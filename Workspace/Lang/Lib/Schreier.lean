/-
Two uses of the orbit program with a transversal (`Workspace.Lang.Lib.OrbitT`).

* **Schreier transversal** (`schreierFuns`, `schreier_spec`): for `G = ⟨gs⟩ ≤ Sym(n)` and a
  point `α`, the orbit `α^G` with an element `t_β ∈ G`, `t_β α = β`, for each orbit point `β`.
  A point `i` is the value `[i]`. The cost is at most `schK * (m + 2n + 20)⁶` for `m`
  generators.
* **Element enumeration of a small group** (`enumFuns`, `enum_spec`): when `|G| ≤ B`, the list of
  all elements of `G`, without repeats, as the orbit of `1` under left multiplication by the
  generators. The cost is at most `enumK * (m + B + 4 (n + 1)² + 20)⁶`.
-/
module

public import Workspace.Lang.Lib.OrbitT

@[expose] public section

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val encPerm encPerms)
open Equiv

variable {n : ℕ}

/-! ### Points -/

/-- The key of a point: `[i]`. -/
def ptKey (i : Fin n) : List ℕ := [(i : ℕ)]

theorem ptKey_injective : Function.Injective (ptKey (n := n)) := fun i j h => by
  simp only [ptKey, List.cons.injEq, and_true] at h; exact Fin.ext h

theorem isAct_pt : IsAct (n := n) (fun g i => g i) :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

/-- The action on points: on `[ac, encPerm g, [i]]`, the value `[g i]`. -/
def ptActF : Expr := mk1 (.get (arg 1) (.get (arg 2) (.nat 0)))

theorem ptAct_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some ptActF) (g : Perm (Fin n))
    (i : Fin n) :
    FunDet P f (.list [.nat 0, encPerm g, natList (ptKey i)]) (natList (ptKey (g i)))
      (1000 * (n + 1) ^ 2) := by
  have d1 := Det.arg' (P := P) (vs := [.nat 0, encPerm g, natList (ptKey i)]) (rest := [])
    (j := 1) rfl
  have d2 := Det.arg' (P := P) (vs := [.nat 0, encPerm g, natList (ptKey i)]) (rest := [])
    (j := 2) rfl
  have di := Det.get' (P := P) d2 (Det.nat 0) (show [Val.nat (i : ℕ)][0]? = some (.nat i) from rfl)
  have dA := Det.mk1 (Det.applyPerm d1 di)
  refine FunDet.intro hf (dA.mono ?_)
  have w1 := wt_list3_le (.nat 0) (encPerm g) (natList (ptKey i))
  have w2 := wt_encPerm_le g
  have w3 : (natList (ptKey i)).wt ≤ 2 * (Val.nat i).wt + 5 := wt_list1_le _
  have w4 := wt_nat_le (i : ℕ)
  have w5 := wt_nat_le (g i : ℕ)
  have w6 := wt_list1_le (.nat (g i))
  have w0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
  have hi := i.isLt
  have hgi := (g i).isLt
  have hN : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

/-- The Schreier transversal program, at base `b` (23 functions). -/
def schreierFuns (b : ℕ) : List Expr := orbTFuns b (b + 22) ++ [ptActF]

/-- The constant of the Schreier transversal. -/
def schK : ℕ := 11000000

/-- **Schreier transversal.** On `[0, [encPerm g | g ∈ gs], [α], n, n]`, the result is the value
of a list `L` of pairs `([β], t_β)`: the points `β` are the orbit of `α` under `G = ⟨gs⟩`,
without repeats, with `t_β ∈ G` and `t_β α = β`, and the first pair is `([α], 1)`. -/
theorem schreier_spec {P : Program} {b : ℕ} (h : P.HasAt b (schreierFuns b))
    (gs : List (Perm (Fin n))) (α : Fin n) :
    FunAll P b (.list [.nat 0, .list (gs.map encPerm), natList (ptKey α), .nat n, .nat n])
      (fun w cost => ∃ L : List (Fin n × Perm (Fin n)), w = encPairs ptKey L ∧
        (L.map Prod.fst).Nodup ∧ (∀ β, β ∈ L.map Prod.fst ↔ ∃ g ∈ genGroup gs, g α = β) ∧
        (∀ p ∈ L, p.2 ∈ genGroup gs ∧ p.2 α = p.1) ∧ L.head? = some (α, 1) ∧
        cost ≤ schK * (gs.length + 2 * n + 20) ^ 6) := by
  have hO := h.left
  have hA : P.funs[b + 22]? = some ptActF := by
    simpa [length_orbTFuns] using h.right.single
  set S := gs.length + 2 * n + 20 with hS
  have hS1 : 1 ≤ S := by omega
  have p2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have H : OrbTHyp P (b + 22) ptKey (fun g i => g i) gs α (.nat 0) S (1000 * S ^ 2) :=
    { isAct := isAct_pt
      key_inj := ptKey_injective
      hn := by omega
      hm := by omega
      hac := by have := wt_nat_le 0; omega
      hkey := fun y _ => by
        have w3 : (natList (ptKey y)).wt ≤ 2 * (Val.nat y).wt + 5 := wt_list1_le _
        have := wt_nat_le (y : ℕ)
        have := y.isLt
        omega
      hfa := fun g _ y _ => (ptAct_spec hA g y).mono (by omega) }
  have hB : (actOrbit (fun g i => g i) gs α).ncard ≤ n := by
    have := Set.ncard_le_card (actOrbit (fun (g : Perm (Fin n)) i => g i) gs α)
    simpa using this
  refine (orbT_spec hO H (by omega) hB).mono fun w cost hw => ?_
  obtain ⟨L, h1, h2, h3, h4, h5, h6⟩ := hw
  refine ⟨L, h1, h2, h3, h4, h5, ?_⟩
  have p6 : S ^ 2 * (1000 * S ^ 2) = 1000 * S ^ 4 := by ring
  have p46 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  simp only [schK, orbTK] at h6 ⊢
  omega

/-! ### Element enumeration -/

/-- The key of a permutation: its list of values. -/
def permKey (σ : Perm (Fin n)) : List ℕ := (List.finRange n).map fun i => (σ i : ℕ)

theorem natList_permKey (σ : Perm (Fin n)) : natList (permKey σ) = encPerm σ := by
  simp [natList, permKey, GI.Cited.encPerm, List.map_map, Function.comp_def]

theorem permKey_injective : Function.Injective (permKey (n := n)) := fun σ τ h =>
  encPerm_injective (by rw [← natList_permKey, ← natList_permKey, h])

theorem isAct_mul : IsAct (n := n) (fun g x => g * x) :=
  ⟨fun x => one_mul x, fun g h x => mul_assoc g h x⟩

theorem actOrbit_mul_one (gs : List (Perm (Fin n))) (σ : Perm (Fin n)) :
    σ ∈ actOrbit (fun g x => g * x) gs 1 ↔ σ ∈ genGroup gs := by
  simp [actOrbit]

/-- The action by left multiplication: on `[ac, encPerm g, encPerm x]`, the value
`encPerm (g * x)`. -/
def permActF (comp : ℕ) : Expr := .call comp (mk2 (arg 1) (arg 2))

theorem permAct_spec {P : Program} {f comp : ℕ} (hf : P.funs[f]? = some (permActF comp))
    (hc : P.HasAt comp (composeFuns comp)) (g x : Perm (Fin n)) :
    FunDet P f (.list [.nat 0, encPerm g, natList (permKey x)]) (natList (permKey (g * x)))
      (40000 * (n + 1) ^ 3) := by
  rw [natList_permKey, natList_permKey]
  have d1 := Det.arg' (P := P) (vs := [.nat 0, encPerm g, encPerm x]) (rest := []) (j := 1) rfl
  have d2 := Det.arg' (P := P) (vs := [.nat 0, encPerm g, encPerm x]) (rest := []) (j := 2) rfl
  refine FunDet.intro hf ((Det.call (Det.mk2 d1 d2) (compose_spec hc g x)).mono ?_)
  have w1 := wt_list3_le (.nat 0) (encPerm g) (encPerm x)
  have w2 := wt_encPerm_le g
  have w3 := wt_encPerm_le x
  have w4 := wt_encPerm_le (g * x)
  have w5 := wt_list2_le (encPerm g) (encPerm x)
  have w0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
  have hN : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  simp only [permK]
  omega

/-- On `[c, [yv, t]]`: the point `yv`. -/
def fstF : Expr := .get (arg 1) (.nat 0)

/-- The entry of the enumeration: on `[gens, B, n]`, run the orbit program on
`[0, gens, encPerm 1, B, n]` and keep the points. -/
def enumEntry (b : ℕ) : Expr :=
  .letE (.call (b + 1) (.snoc (mk4 (.nat 0) (arg 0) (.call (b + 20) (arg 2)) (arg 1)) (arg 2)))
    (.call (b + 24) (mk2 (.nat 0) (.var 1)))

/-- The enumeration program, at base `b` (28 functions). -/
def enumFuns (b : ℕ) : List Expr :=
  [enumEntry b] ++ orbTFuns (b + 1) (b + 23) ++ [permActF (b + 13)] ++ mapFuns (b + 24) (b + 27) ++
    [fstF]

/-- The constant of the enumeration. -/
def enumK : ℕ := 20000000

/-- **Element enumeration of a small group.** When `G = ⟨gs⟩` has at most `B` elements, the
result on `[[encPerm g | g ∈ gs], B, n]` is the list of the elements of `G`, without repeats. -/
theorem enum_spec {P : Program} {b : ℕ} (h : P.HasAt b (enumFuns b))
    (gs : List (Perm (Fin n))) {B : ℕ} (hB : Nat.card (genGroup gs) ≤ B) :
    FunAll P b (.list [.list (gs.map encPerm), .nat B, .nat n])
      (fun w cost => ∃ els : List (Perm (Fin n)), w = .list (els.map encPerm) ∧ els.Nodup ∧
        (∀ σ, σ ∈ els ↔ σ ∈ genGroup gs) ∧
        cost ≤ enumK * (gs.length + B + 4 * (n + 1) ^ 2 + 20) ^ 6) := by
  simp only [enumFuns] at h
  have he : P.funs[b]? = some (enumEntry b) := h.left.left.left.left.single
  have hO : P.HasAt (b + 1) (orbTFuns (b + 1) (b + 23)) := by simpa using h.left.left.left.right
  have hA : P.funs[b + 23]? = some (permActF (b + 13)) := by
    simpa [length_orbTFuns, Nat.add_assoc] using h.left.left.right.single
  have hM : P.HasAt (b + 24) (mapFuns (b + 24) (b + 27)) := by
    simpa [length_orbTFuns, Nat.add_assoc] using h.left.right
  have hF : P.funs[b + 27]? = some fstF := by
    simpa [length_orbTFuns, mapFuns, loopFuns, Nat.add_assoc] using h.right.single
  obtain ⟨-, -, hP, hr⟩ := OrbTAt.pieces hO
  have hc : P.HasAt (b + 13) (composeFuns (b + 13)) := by simpa [Nat.add_assoc] using hP.comp
  have hr' : P.HasAt (b + 20) (rangeFuns (b + 20)) := by simpa [Nat.add_assoc] using hr
  set S := gs.length + B + 4 * (n + 1) ^ 2 + 20 with hS
  have hS1 : 1 ≤ S := by omega
  have hn2 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS1 (by norm_num)
  have p4 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS1 (by norm_num)
  have p5 : S ^ 5 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hn3 : (n + 1) ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have H : OrbTHyp P (b + 23) permKey (fun g x => g * x) gs 1 (.nat 0) S (40000 * S ^ 3) :=
    { isAct := isAct_mul
      key_inj := permKey_injective
      hn := by omega
      hm := by omega
      hac := by have := wt_nat_le 0; omega
      hkey := fun y _ => by rw [natList_permKey]; have := wt_encPerm_le y; omega
      hfa := fun g _ y _ => (permAct_spec hA hc g y).mono (by omega) }
  have hOrb : actOrbit (fun g x => g * x) gs (1 : Perm (Fin n)) = (genGroup gs : Set (Perm (Fin n))) :=
    Set.ext fun σ => actOrbit_mul_one gs σ
  have hB' : (actOrbit (fun g x => g * x) gs (1 : Perm (Fin n))).ncard ≤ B := by
    rw [hOrb, ← Nat.card_coe_set_eq]; exact hB
  have hD := orbT_det hO H (by omega) hB'
  rw [natList_permKey] at hD
  obtain ⟨hg, hmem, -⟩ := orbitPairs_spec isAct_mul gs (1 : Perm (Fin n)) hB'
  obtain ⟨hlen, hwL⟩ := H.wt_pairs (by omega) hB' hg
  set L := orbitPairs (fun g x => g * x) gs (1 : Perm (Fin n)) B with hL
  -- the range
  have hR : FunDet P (b + 20) (.nat n) (encPerm (1 : Perm (Fin n))) (8000 * S ^ 3) := by
    refine (range_spec hr' n).mono fun w c hw => ⟨by rw [hw.1, range_eq_encPerm_one], ?_⟩
    have hc := hw.2
    rw [hw.1, range_eq_encPerm_one] at hc
    have w1 := wt_encPerm_le (1 : Perm (Fin n))
    have w2 := wt_nat_le n
    have h1 : loopModK * (n + 1) * ((Val.nat n).wt + n + (encPerm (1 : Perm (Fin n))).wt + 1) ≤
        loopModK * S * (8 * S ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e : loopModK * S * (8 * S ^ 2) = 8000 * S ^ 3 := by simp only [loopModK]; ring
    omega
  -- the map
  have hMap : FunDet P (b + 24) (.list [.nat 0, encPairs permKey L])
      (.list (L.map fun p => encPerm p.1)) (200000 * S ^ 4) := by
    have hm := map_spec hM (c := .nat 0) (xs := L.map (encPair permKey))
      (R := fun x w => ∀ p, x = encPair permKey p → w = encPerm p.1)
      (B := fun _ => 100 * S ^ 3) (by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        have d1 := Det.arg' (P := P) (vs := [.nat 0, encPair permKey p]) (rest := []) (j := 1) rfl
        have d := Det.get' d1 (Det.nat 0) (show [natList (permKey p.1), encPerm p.2][0]? =
          some (natList (permKey p.1)) from rfl)
        refine FunAll.intro hF (d.post fun c hc => ⟨fun q hq => ?_, ?_⟩)
        · rw [natList_permKey, encPair_injective permKey_injective hq]
        · have w1 := wt_list2_le (.nat 0) (encPair permKey p)
          have w2 := H.wt_pair (hg.2 p hp)
          have w3 : (natList (permKey p.1)).wt < (encPair permKey p).wt :=
            wt_le_wt_list (by simp)
          have w0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
          beta_reduce
          omega)
    refine hm.mono fun w c hw => ?_
    obtain ⟨ws, rfl, hws, hc⟩ := hw
    have e : ws = L.map fun p => encPerm p.1 :=
      forall₂_map_eq (h := hws) fun p _ w hw => hw p rfl
    subst e
    refine ⟨rfl, ?_⟩
    rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
    have w1 := wt_list2_le (.nat 0) (encPairs permKey L)
    have w1' : (Val.list [.nat 0, .list (L.map (encPair permKey))]).wt =
      (Val.list [.nat 0, encPairs permKey L]).wt := rfl
    have w0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    have w2 := wt_list_le_of (L.map fun p => encPerm p.1) (c := 4 * S ^ 2) (by
      simp only [List.mem_map, forall_exists_index, and_imp]
      rintro _ p _ rfl
      exact (wt_encPerm_le p.1).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)))
    rw [List.length_map] at w2
    have e1 : S * (100 * S ^ 3) = 100 * S ^ 4 := by ring
    have e2 : S * (9 * S ^ 2) = 9 * S ^ 3 := by ring
    have e3 : mapK * S * (100 * S ^ 3) = 100000 * S ^ 4 := by simp only [mapK]; ring
    have h1 : L.length * (100 * S ^ 3) ≤ S * (100 * S ^ 3) := Nat.mul_le_mul_right _ (by omega)
    have h2 : L.length * (2 * (4 * S ^ 2) + 1) ≤ S * (9 * S ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : mapK * (L.length + 1) * ((Val.list [.nat 0, .list (L.map (encPair permKey))]).wt +
        (Val.list (L.map fun p => encPerm p.1)).wt + 1) ≤ mapK * S * (100 * S ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hlen) (by omega)
    omega
  -- the entry
  set vs : List Val := [.list (gs.map encPerm), .nat B, .nat n] with hvs
  have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have d2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have dArg := Det.snoc (Det.mk4 (Det.nat 0) d0 (Det.call d2 hR) d1) d2
  have dOrb := Det.call dArg hD
  have dMap := Det.call (Det.mk2 (Det.nat 0) (Det.var' (P := P)
    (env := [.list vs, encPairs permKey L]) (i := 1) rfl)) hMap
  have dAll := Det.letE dOrb dMap
  refine FunAll.intro he (dAll.post fun c hc => ⟨L.map Prod.fst, by simp [List.map_map,
    Function.comp_def], hg.1, fun σ => (hmem σ).trans (actOrbit_mul_one gs σ), ?_⟩)
  clear dAll dMap dOrb dArg d0 d1 d2 hMap hR hD
  have wv := wt_list3_le (.list (gs.map encPerm)) (.nat B) (.nat n)
  have wv' : (Val.list [.list (gs.map encPerm), .nat B, .nat n]).wt = (Val.list vs).wt := rfl
  have wg := H.wt_gens
  have wB := wt_nat_le B
  have wn := wt_nat_le n
  have w1 := H.wt_perm (1 : Perm (Fin n))
  have w0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
  have w4 := wt_list4_le (.nat 0) (.list (gs.map encPerm)) (encPerm (1 : Perm (Fin n))) (.nat B)
  have w5 := wt_list_snoc_le [.nat 0, .list (gs.map encPerm), encPerm (1 : Perm (Fin n)), .nat B]
    (.nat n)
  have w6 := wt_list2_le (.nat 0) (encPairs permKey L)
  have w7 := wt_list_le_of (L.map fun p => encPerm p.1) (c := 4 * S ^ 2) (by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ p _ rfl
    exact (wt_encPerm_le p.1).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)))
  rw [List.length_map] at w7
  have h2 : L.length * (2 * (4 * S ^ 2) + 1) ≤ S * (9 * S ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e2 : S * (9 * S ^ 2) = 9 * S ^ 3 := by ring
  have e5 : S ^ 2 * (40000 * S ^ 3) = 40000 * S ^ 5 := by ring
  simp only [enumK, orbTK] at hc ⊢
  omega

end GI.Lang
