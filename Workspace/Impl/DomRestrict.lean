import Workspace.Impl.DomMath

/-!
# Restricting a state value to its domain, in `GI.Lang`

The programs of `Solve` (`Workspace/Impl/Fresh.lean`, `Workspace/Impl/Direct.lean`) first read
the active domain off the state value and restrict the generators and the colorings to it. The
module `domFuns b` (25 functions at base `b`) does this with the library:

* `b`: on the indicator of `D`, the positions of the domain in increasing order
  (`natList (domNat e D)`), by `filter` over `range k` (`domList_spec`);
* `b + 8`: on `[P, k]`, the table of positions `i ↦ posOf P i` (`posTab_spec`), by `findEq`;
* `b + 17`: on `[[P, pos], g]`, the restriction of a permutation `g` of `G` (two `gather`s:
  entry `j` is `pos[g[P[j]]]`, `restrGen_spec`);
* `b + 18`: `gather`, which also restricts a coloring (`gatherColor`);
* `b + 22`: `map` of the restriction over a list of generators (`restrList_spec`).

The mathematics is in `Workspace/Impl/DomMath.lean`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encPerms encGroup gens)
open scoped Pointwise

variable {Ω : Type} {k : ℕ}

/-! ### Lists indexed by positions -/

theorem getD_finRange_map {n : ℕ} (f : Fin n → Val) (i : ℕ) (hi : i < n) (d : Val) :
    ((List.finRange n).map f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  simp [hi]

/-- A list read at the positions of a list `l`: the same as a map over the indices of `l`. -/
theorem map_finRange_getElem {α β : Type*} (l : List α) (F : α → β) :
    (List.finRange l.length).map (fun j => F l[j]) = l.map F := by
  have := List.map_getElem_finRange l
  conv_rhs => rw [← this]
  rw [List.map_map]
  rfl

/-- `encFun` on `Fin s` with `s` the length of the domain list. -/
theorem encFun_domFin (e : Ω ≃ Fin k) (D : Set Ω) (F : Fin k → ℕ) :
    encFun (fun j : Fin (domFin e D).length => F (domFin e D)[j]) =
      natList ((domFin e D).map F) := by
  simp only [encFun, natList]
  rw [List.map_map]
  exact congrArg Val.list (map_finRange_getElem (domFin e D) (fun i => Val.nat (F i)))

theorem natList_domNat_eq (e : Ω ≃ Fin k) (D : Set Ω) (F : ℕ → Val) :
    (domNat e D).map F = (domFin e D).map (fun i : Fin k => F (i : ℕ)) := by
  rw [domNat, List.map_map]; rfl

/-! ### The program -/

/-- On `[dv, i]`: whether `dv[i] = 1`. -/
def domTestF : Expr := .arith .eq (.get (arg 0) (arg 1)) (.nat 1)

/-- On the indicator `dv`: `filter (dv[i] = 1) (range (length dv))`. -/
def domListF (rng filt : ℕ) : Expr := .call filt (mk2 (.var 0) (.call rng (.length (.var 0))))

/-- On `[P, i]`: the position of `i` in `P`. -/
def posF (fe : ℕ) : Expr := .call fe (mk2 (arg 1) (arg 0))

/-- On `[P, k]`: the table `i ↦ posOf P i` for `i < k`. -/
def posTabF (rng mp : ℕ) : Expr := .call mp (mk2 (arg 0) (.call rng (arg 1)))

/-- On `[[P, pos], g]`: `pos ∘ g ∘ P`, the restriction of `g` to the domain. -/
def restrGenF (ga : ℕ) : Expr :=
  .call ga (mk2 (.get (arg 0) (.nat 1)) (.call ga (mk2 (arg 1) (.get (arg 0) (.nat 0)))))

/-- **The restriction module** at base `b` (25 functions). -/
def domFuns (b : ℕ) : List Expr :=
  [domListF (b + 1) (b + 4)] ++ rangeFuns (b + 1) ++ filterFuns (b + 4) (b + 7) ++ [domTestF] ++
    [posTabF (b + 1) (b + 9)] ++ mapFuns (b + 9) (b + 12) ++ [posF (b + 13)] ++
    findEqFuns (b + 13) ++ [restrGenF (b + 18)] ++ gatherFuns (b + 18) ++
    mapFuns (b + 22) (b + 17)

theorem length_domFuns (b : ℕ) : (domFuns b).length = 25 := by
  simp [domFuns, rangeFuns, filterFuns, mapFuns, loopFuns, findEqFuns, findFuns, gatherFuns]

/-- The blocks of the restriction module. -/
structure DomAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (domListF (b + 1) (b + 4))
  range : P.HasAt (b + 1) (rangeFuns (b + 1))
  filter : P.HasAt (b + 4) (filterFuns (b + 4) (b + 7))
  test : P.funs[b + 7]? = some domTestF
  posTab : P.funs[b + 8]? = some (posTabF (b + 1) (b + 9))
  map1 : P.HasAt (b + 9) (mapFuns (b + 9) (b + 12))
  pos : P.funs[b + 12]? = some (posF (b + 13))
  findEq : P.HasAt (b + 13) (findEqFuns (b + 13))
  restrGen : P.funs[b + 17]? = some (restrGenF (b + 18))
  gather : P.HasAt (b + 18) (gatherFuns (b + 18))
  map2 : P.HasAt (b + 22) (mapFuns (b + 22) (b + 17))

theorem domAt_of_hasAt {P : Program} {b : ℕ} (h : P.HasAt b (domFuns b)) : DomAt P b where
  entry := by simpa using h.block 0 (gs := [domListF (b + 1) (b + 4)]) (by rfl) |>.single
  range := h.block 1 (by rfl)
  filter := h.block 4 (by rfl)
  test := by simpa using (h.block 7 (gs := [domTestF]) (by rfl)).single
  posTab := by simpa using (h.block 8 (gs := [posTabF (b + 1) (b + 9)]) (by rfl)).single
  map1 := h.block 9 (by rfl)
  pos := by simpa using (h.block 12 (gs := [posF (b + 13)]) (by rfl)).single
  findEq := h.block 13 (by rfl)
  restrGen := by simpa using (h.block 17 (gs := [restrGenF (b + 18)]) (by rfl)).single
  gather := h.block 18 (by rfl)
  map2 := h.block 22 (by rfl)

/-! ### The positions of the domain -/

/-- The indicator of `D` at a number (`0` beyond `k`). -/
noncomputable def indN (e : Ω ≃ Fin k) (D : Set Ω) (i : ℕ) : ℕ :=
  if h : i < k then indF e D ⟨i, h⟩ else 0

/-- The test of the filter: a number whose indicator is `1`. -/
noncomputable def domQ (e : Ω ≃ Fin k) (D : Set Ω) : Val → Bool
  | .nat i => decide (indN e D i = 1)
  | .list _ => false

theorem domTest_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some domTestF) (e : Ω ≃ Fin k)
    (D : Set Ω) (i : Fin k) :
    FunDet P f (.list [indVal e D, .nat i]) (boolVal (domQ e D (.nat i))) (200 * (k + 1) ^ 2) := by
  have g0 := Det.arg' (P := P) (vs := [indVal e D, .nat i]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [indVal e D, .nat i]) (rest := []) (j := 1) rfl
  have gi := Det.get' g0 g1 (v := .nat (indF e D i)) (by simp)
  have hq : (if indF e D i = 1 then 1 else 0) = (domQ e D (.nat i)).toNat := by
    simp only [domQ, indN, i.isLt, dif_pos]
    split_ifs with h1 <;> simp [h1]
  refine FunDet.intro hf ((Det.arith' (op := .eq) gi (Det.nat 1) (z := (domQ e D (.nat i)).toNat)
    (by simp only [BinOp.eval]; exact hq)).mono ?_)
  have w1 := DomVal.wt_le (domVal_indVal e D)
  have w2 := wt_list2_le (indVal e D) (.nat i)
  have w3 := wt_nat_le i
  have w4 := wt_nat_le (indF e D i)
  have w5 := indF_le_one e D i
  have w6 : (domQ e D (.nat i)).toNat ≤ 1 := Bool.toNat_le _
  have := i.isLt
  have : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

open Classical in
theorem filter_domQ (e : Ω ≃ Fin k) (D : Set Ω) :
    ((List.finRange k).map (fun i : Fin k => Val.nat ((1 : Perm (Fin k)) i))).filter (domQ e D) =
      (domNat e D).map Val.nat := by
  rw [List.filter_map, natList_domNat_eq]
  simp only [Perm.coe_one, id_eq]
  congr 1
  apply List.filter_congr
  intro i _
  simp [domQ, indN, i.isLt, indF]

/-- The cost constant of `domList`. -/
def domListK : ℕ := 10 ^ 6

/-- **The positions of the domain.** -/
theorem domList_spec {P : Program} {b : ℕ} (h : DomAt P b) (e : Ω ≃ Fin k) (D : Set Ω) :
    FunDet P b (indVal e D) (natList (domNat e D)) (domListK * (k + 1) ^ 3) := by
  have hind : indVal e D = .list ((List.finRange k).map fun i => .nat (indF e D i)) := rfl
  have dl := Det.length (Det.var' (P := P) (env := [indVal e D]) (i := 0) (v := indVal e D) rfl)
  rw [hind] at dl
  simp only [List.length_map, List.length_finRange] at dl
  have dr := Det.call dl (range_det h.range k)
  have hfl := filter_spec h.filter (c := indVal e D)
    (xs := (List.finRange k).map (fun i : Fin k => Val.nat ((1 : Perm (Fin k)) i)))
    (q := domQ e D) (B := fun _ => 200 * (k + 1) ^ 2) (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact domTest_det h.test e D i)
  rw [filter_domQ] at hfl
  have w1 := DomVal.wt_le (domVal_indVal e D)
  have w2 := wt_encPerm_le (1 : Perm (Fin k))
  have w3 : (natList (domNat e D)).wt ≤ 5 * (k + 1) ^ 2 := by
    refine (wt_natList_le_sq (B := k) (fun x hx => (domNat_lt hx).le) ?_).trans (by nlinarith)
    rw [length_domNat]; exact length_domFin_le
  have w4 := wt_list2_le (indVal e D) (encPerm (1 : Perm (Fin k)))
  have p23 : (k + 1) ^ 2 ≤ (k + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hk : k * (200 * (k + 1) ^ 2) ≤ 200 * (k + 1) ^ 3 := by
    calc k * (200 * (k + 1) ^ 2) ≤ (k + 1) * (200 * (k + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
      _ = 200 * (k + 1) ^ 3 := by ring
  have hfd : FunDet P (b + 4) (.list [indVal e D, encPerm (1 : Perm (Fin k))])
      (natList (domNat e D)) (40000 * (k + 1) ^ 3) := by
    refine hfl.mono fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
    subst hw
    simp only [List.map_const', List.length_map, List.length_finRange, List.sum_replicate,
      smul_eq_mul] at hc
    have e1 : (Val.list ((List.finRange k).map
        (fun i : Fin k => Val.nat ((1 : Perm (Fin k)) i)))) = encPerm (1 : Perm (Fin k)) := rfl
    rw [e1] at hc
    have hl : loopModK * (k + 1) * ((Val.list [indVal e D, encPerm (1 : Perm (Fin k))]).wt + k +
        (Val.list ((domNat e D).map Val.nat)).wt + 1) ≤ loopModK * (k + 1) * (30 * (k + 1) ^ 2) :=
      Nat.mul_le_mul_left _ (by
        have : (Val.list ((domNat e D).map Val.nat)).wt = (natList (domNat e D)).wt := rfl
        nlinarith)
    have e2 : loopModK * (k + 1) * (30 * (k + 1) ^ 2) = 30000 * (k + 1) ^ 3 := by
      simp only [loopModK]; ring
    omega
  have dv := Det.var' (P := P) (env := [indVal e D]) (i := 0) (v := indVal e D) rfl
  refine FunDet.intro h.entry ((Det.call (Det.mk2 dv dr) hfd).mono ?_)
  simp only [domListK]
  have p13 : k + 1 ≤ (k + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have : (Val.list ((List.finRange k).map fun i => Val.nat (indF e D i))).wt = (indVal e D).wt :=
    rfl
  omega

/-! ### The table of positions -/

/-- The table of positions of the domain: `i ↦ posOf P i`. -/
noncomputable def posVal (e : Ω ≃ Fin k) (D : Set Ω) : Val :=
  encFun fun i : Fin k => posOf (domNat e D) i

theorem domNat_le (e : Ω ≃ Fin k) (D : Set Ω) : ∀ x ∈ domNat e D, x ≤ k :=
  fun _ hx => (domNat_lt hx).le

theorem length_domNat_le (e : Ω ≃ Fin k) (D : Set Ω) : (domNat e D).length ≤ k := by
  rw [length_domNat]; exact length_domFin_le

theorem wt_domNat_le (e : Ω ≃ Fin k) (D : Set Ω) : (natList (domNat e D)).wt ≤ 5 * (k + 1) ^ 2 :=
  (wt_natList_le_sq (domNat_le e D) (length_domNat_le e D)).trans (by nlinarith)

theorem posOf_domNat_le (e : Ω ≃ Fin k) (D : Set Ω) (i : ℕ) : posOf (domNat e D) i ≤ k :=
  (posOf_le _ _).trans (length_domNat_le e D)

theorem wt_posVal_le (e : Ω ≃ Fin k) (D : Set Ω) : (posVal e D).wt ≤ 5 * (k + 1) ^ 2 := by
  have := wt_encFun_le (fun i : Fin k => posOf (domNat e D) i) (B := k)
    fun i => posOf_domNat_le e D i
  rw [posVal]; nlinarith

/-- The cost constant of the table of positions. -/
def posTabK : ℕ := 10 ^ 7

/-- **The table of positions.** -/
theorem posTab_spec {P : Program} {b : ℕ} (h : DomAt P b) (e : Ω ≃ Fin k) (D : Set Ω) :
    FunDet P (b + 8) (.list [natList (domNat e D), .nat k]) (posVal e D) (posTabK * (k + 1) ^ 4) := by
  set c := natList (domNat e D) with hc
  have wc : c.wt ≤ 5 * (k + 1) ^ 2 := wt_domNat_le e D
  have hf : ∀ i : Fin k, FunDet P (b + 12) (.list [c, .nat i])
      (.nat (posOf (domNat e D) i)) (findEqK * (k + 1) ^ 3 + 200 * (k + 1) ^ 2) := by
    intro i
    have g0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 0) rfl
    have g1 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 1) rfl
    have hfe := findEq_spec h.findEq (xs := domNat e D) (j := i) (B := k) (domNat_le e D)
      i.isLt.le (length_domNat_le e D)
    refine FunDet.intro h.pos ((Det.call (Det.mk2 g1 g0) hfe).mono ?_)
    have := wt_list2_le c (.nat i)
    have := wt_list2_le (.nat i) c
    have := wt_nat_le i
    have := wt_nat_le (posOf (domNat e D) i)
    have := posOf_domNat_le e D i
    have := i.isLt
    have : (Val.nat ((domNat e D).findIdx fun x => decide (x = (i : ℕ)))).wt =
      (Val.nat (posOf (domNat e D) i)).wt := rfl
    have : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have ht := tabulate_spec (m := k) h.map1 (c := c) hf
  have g0 := Det.arg' (P := P) (vs := [c, .nat k]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [c, .nat k]) (rest := []) (j := 1) rfl
  have dr := Det.call g1 (range_det h.range k)
  refine FunDet.intro h.posTab ((Det.call (Det.mk2 g0 dr) ht).mono ?_)
  have e1 : (Val.list ((List.finRange k).map fun i : Fin k => Val.nat (posOf (domNat e D) i))) =
    posVal e D := rfl
  have e2 : (encFun fun i : Fin k => (i : ℕ)) = encPerm (1 : Perm (Fin k)) := rfl
  rw [e1, e2] at *
  have w1 := wt_posVal_le e D
  have w2 := wt_encPerm_le (1 : Perm (Fin k))
  have w3 := wt_list2_le c (.nat k)
  have w4 := wt_nat_le k
  have w5 := wt_list2_le c (encPerm (1 : Perm (Fin k)))
  have p12 : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : (k + 1) ^ 2 ≤ (k + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have p34 : (k + 1) ^ 3 ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : mapK * (k + 1) * ((Val.list [c, encPerm (1 : Perm (Fin k))]).wt + (posVal e D).wt + 1)
      ≤ mapK * (k + 1) * (40 * (k + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
  have e3 : mapK * (k + 1) * (40 * (k + 1) ^ 2) = 40000 * (k + 1) ^ 3 := by
    simp only [mapK]; ring
  have hkB : k * (findEqK * (k + 1) ^ 3 + 200 * (k + 1) ^ 2) ≤
      findEqK * (k + 1) ^ 4 + 200 * (k + 1) ^ 3 := by
    have : k * (findEqK * (k + 1) ^ 3 + 200 * (k + 1) ^ 2) ≤
        (k + 1) * (findEqK * (k + 1) ^ 3 + 200 * (k + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
    calc _ ≤ _ := this
      _ = findEqK * (k + 1) ^ 4 + 200 * (k + 1) ^ 3 := by ring
  simp only [posTabK, findEqK] at *
  omega

/-! ### Restricting a permutation -/

/-- The context of the restriction: the positions and the table. -/
noncomputable def domCtx (e : Ω ≃ Fin k) (D : Set Ω) : Val :=
  .list [natList (domNat e D), posVal e D]

theorem wt_domCtx_le (e : Ω ≃ Fin k) (D : Set Ω) : (domCtx e D).wt ≤ 30 * (k + 1) ^ 2 := by
  have := wt_list2_le (natList (domNat e D)) (posVal e D)
  have := wt_domNat_le e D
  have := wt_posVal_le e D
  have : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [domCtx]; omega

/-- The cost constant of the restriction of a permutation. -/
def restrGenK : ℕ := 10 ^ 12

section Gen

variable (e : Ω ≃ Fin k) (G : Subgroup (Perm Ω)) (D : Set Ω) (hD : Invariant G D)

/-- The restricted permutation, entry by entry. -/
theorem encPerm_restrP {g : Perm (Fin k)} (hg : g ∈ groupFin e G) :
    encPerm (restrP e G D hD g) =
      .list ((domFin e D).map fun p => Val.nat (posOf (domNat e D) (g p))) := by
  rw [restrP_of_mem e G D hD hg, encPerm_eq_encFun]
  simp only [encFun]
  rw [← map_finRange_getElem (domFin e D) (fun p => Val.nat (posOf (domNat e D) (g p)))]
  congr 1
  apply List.map_congr_left
  intro j _
  rw [restrK_apply]

/-- **The restriction of a permutation of `G`.** -/
theorem restrGen_spec {P : Program} {b : ℕ} (h : DomAt P b) {g : Perm (Fin k)}
    (hg : g ∈ groupFin e G) :
    FunDet P (b + 17) (.list [domCtx e D, encPerm g]) (encPerm (restrP e G D hD g))
      (restrGenK * (k + 1) ^ 6) := by
  have wA : (Val.list [domCtx e D, encPerm g]).wt ≤ 80 * (k + 1) ^ 2 := by
    have := wt_list2_le (domCtx e D) (encPerm g)
    have := wt_domCtx_le e D
    have := wt_encPerm_le g
    have : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have g0 := Det.arg' (P := P) (vs := [domCtx e D, encPerm g]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [domCtx e D, encPerm g]) (rest := []) (j := 1) rfl
  have gP := Det.get' g0 (Det.nat 0) (v := natList (domNat e D)) rfl
  have gpos := Det.get' g0 (Det.nat 1) (v := posVal e D) rfl
  -- the inner gather: `g ∘ P`
  set L2 : List ℕ := (domFin e D).map fun p => (g p : ℕ) with hL2
  have hin := gather_spec h.gather (L := (List.finRange k).map fun i => Val.nat (g i))
    (is := domNat e D) (fun i hi => by simpa using domNat_lt hi)
  have hin_eq : (Val.list ((domNat e D).map fun i =>
      ((List.finRange k).map fun i => Val.nat (g i)).getD i (.nat 0))) = natList L2 := by
    rw [natList_domNat_eq]
    simp only [natList, hL2, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply]
    rw [getD_finRange_map _ _ p.isLt]
  rw [hin_eq] at hin
  have d1 := Det.call (Det.mk2 g1 gP) hin
  -- the outer gather: `pos ∘ (g ∘ P)`
  have hout := gather_spec h.gather
    (L := (List.finRange k).map fun i : Fin k => Val.nat (posOf (domNat e D) i)) (is := L2)
    (fun i hi => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hi
      simp)
  have hout_eq : (Val.list (L2.map fun i =>
      ((List.finRange k).map fun i : Fin k => Val.nat (posOf (domNat e D) i)).getD i (.nat 0))) =
      encPerm (restrP e G D hD g) := by
    rw [encPerm_restrP e G D hD hg, hL2, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply]
    rw [getD_finRange_map _ _ (g p).isLt]
  rw [hout_eq] at hout
  have d2 := Det.call (Det.mk2 gpos d1) hout
  refine FunDet.intro h.restrGen (d2.mono ?_)
  -- the cost
  have e1 : (Val.list ((List.finRange k).map fun i => Val.nat (g i))) = encPerm g := rfl
  have e2 : (Val.list ((List.finRange k).map fun i : Fin k => Val.nat (posOf (domNat e D) i))) =
    posVal e D := rfl
  rw [e1] at d1 ⊢
  rw [e2]
  have wL2 : (natList L2).wt ≤ 5 * (k + 1) ^ 2 := by
    refine (wt_natList_le_sq (B := k) ?_ ?_).trans (by nlinarith)
    · intro x hx; obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx; exact (g p).isLt.le
    · simp only [hL2, List.length_map]; exact length_domFin_le
  have wR := wt_encPerm_le (restrP e G D hD g)
  have hs : (domFin e D).length ≤ k := length_domFin_le
  have wR' : (encPerm (restrP e G D hD g)).wt ≤ 4 * (k + 1) ^ 2 :=
    wR.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have wg := wt_encPerm_le g
  have wP := wt_domNat_le e D
  have wpos := wt_posVal_le e D
  have a1 := wt_list2_le (encPerm g) (natList (domNat e D))
  have a2 := wt_list2_le (posVal e D) (natList L2)
  have p1 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have b1 : ((Val.list [encPerm g, natList (domNat e D)]).wt + 1) ^ 3 ≤ (30 * (k + 1) ^ 2) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  have b2 : ((Val.list [posVal e D, natList L2]).wt + 1) ^ 3 ≤ (30 * (k + 1) ^ 2) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  have b3 : (30 * (k + 1) ^ 2) ^ 3 = 27000 * (k + 1) ^ 6 := by ring
  have p26 : (k + 1) ^ 2 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have b4 : gatherK * ((Val.list [encPerm g, natList (domNat e D)]).wt + 1) ^ 3 ≤
      gatherK * (27000 * (k + 1) ^ 6) := b3 ▸ Nat.mul_le_mul_left _ b1
  have b5 : gatherK * ((Val.list [posVal e D, natList L2]).wt + 1) ^ 3 ≤
      gatherK * (27000 * (k + 1) ^ 6) := b3 ▸ Nat.mul_le_mul_left _ b2
  simp only [restrGenK, gatherK] at *
  omega

/-- The cost constant of the restriction of a list of generators. -/
def restrListK : ℕ := 10 ^ 13

/-- **The restriction of a list of permutations of `G`.** -/
theorem restrList_spec {P : Program} {b : ℕ} (h : DomAt P b) {hs : List (Perm (Fin k))}
    (hhs : ∀ g ∈ hs, g ∈ groupFin e G) :
    FunDet P (b + 22) (.list [domCtx e D, .list (hs.map encPerm)])
      (.list (hs.map fun g => encPerm (restrP e G D hD g)))
      (restrListK * ((hs.length + 1) * (k + 1)) ^ 7) := by
  have hm := mapList_spec h.map2 hs encPerm (fun g => encPerm (restrP e G D hD g))
    (c := domCtx e D) (fun a _ a' _ he => by rw [encPerm_injective he])
    (fun a ha => restrGen_spec e G D hD h (hhs a ha))
  refine hm.mono ?_
  set T := (hs.length + 1) * (k + 1) with hT
  have hT1 : k + 1 ≤ T := Nat.le_mul_of_pos_left _ (by omega)
  have hT2 : hs.length + 1 ≤ T := Nat.le_mul_of_pos_right _ (by omega)
  have hs' : (domFin e D).length ≤ k := length_domFin_le
  have w1 : (Val.list (hs.map encPerm)).wt ≤ 13 * T ^ 2 := by
    have h1 := wt_list_le (hs.map encPerm)
    have h2 : ((hs.map encPerm).map Val.wt).sum ≤ hs.length * (4 * (k + 1) ^ 2) := by
      have := List.sum_le_card_nsmul ((hs.map encPerm).map Val.wt) (4 * (k + 1) ^ 2) (by
        simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        intro g _; exact wt_encPerm_le g)
      simpa using this
    simp only [List.length_map] at h1
    have : hs.length * (4 * (k + 1) ^ 2) ≤ 4 * T ^ 2 := by
      have : hs.length * (k + 1) ≤ T := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    nlinarith
  have w2 : (Val.list (hs.map fun g => encPerm (restrP e G D hD g))).wt ≤ 13 * T ^ 2 := by
    have h1 := wt_list_le (hs.map fun g => encPerm (restrP e G D hD g))
    have h2 : ((hs.map fun g => encPerm (restrP e G D hD g)).map Val.wt).sum ≤
        hs.length * (4 * (k + 1) ^ 2) := by
      have := List.sum_le_card_nsmul ((hs.map fun g => encPerm (restrP e G D hD g)).map Val.wt)
        (4 * (k + 1) ^ 2) (by
        simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        intro g _
        exact (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)))
      simpa using this
    simp only [List.length_map] at h1
    have : hs.length * (4 * (k + 1) ^ 2) ≤ 4 * T ^ 2 := by
      have : hs.length * (k + 1) ≤ T := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    nlinarith
  have w3 := wt_list2_le (domCtx e D) (.list (hs.map encPerm))
  have w4 := wt_domCtx_le e D
  have p2 : (k + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hT1 2
  have p6 : (k + 1) ^ 6 ≤ T ^ 6 := Nat.pow_le_pow_left hT1 6
  have p37 : T ^ 3 ≤ T ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : hs.length * (restrGenK * (k + 1) ^ 6) ≤ restrGenK * T ^ 7 := by
    calc hs.length * (restrGenK * (k + 1) ^ 6) ≤ T * (restrGenK * T ^ 6) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ p6)
      _ = restrGenK * T ^ 7 := by ring
  have h2 : mapK * (hs.length + 1) * ((Val.list [domCtx e D, .list (hs.map encPerm)]).wt +
      (Val.list (hs.map fun g => encPerm (restrP e G D hD g))).wt + 1) ≤
      mapK * T * (200 * T ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hT2) (by
        have : 1 ≤ T ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega)
  have h3 : mapK * T * (200 * T ^ 2) = 200000 * T ^ 3 := by simp only [mapK]; ring
  simp only [restrListK, restrGenK] at *
  omega

end Gen

end GI.Impl
