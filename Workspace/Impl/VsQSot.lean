module

public import Workspace.Impl.VsQSotMath
public import Workspace.Impl.Lift
public import Workspace.Lang.Prims.Reduce

@[expose] public section

/-!
# The small orbit transporter (SOT)

Let `H = ⟨gs⟩ ≤ K` act on `Y` through `α` (an action of `K`), with the action available as a
language function `fa` on keys. The program `vsQSotFuns` lists the orbit of `y₀` with a
transversal (`vsQ_orbT_spec`), and then computes generators of the stabilizer of `y₀` in `H`:

1. for each generator `g`, the permutation `ρ g = g ⊕ π(g)` of `Fin (n + m)`, where `π(g)` is the
   permutation of the positions of the orbit list (`vsQRho`);
2. the pointwise stabilizer of the point `n` in `⟨ρ gs⟩` (one primitive call);
3. the first `n` entries of each generator (`gather`), and the reduction to at most `n²`
   generators by the membership filter.

`vsQSot_spec` states the result: the orbit list `L` and a list `ks` of at most `n²` generators of
the stabilizer `vsQStabG`.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

variable {n : ℕ} {Y : Type} {K : Subgroup (Perm (Fin n))} {α : Perm (Fin n) → Y → Y}
  {gs : List (Perm (Fin n))} {y₀ : Y}

/-! ### Mathematics of the encodings -/

theorem vsQ_idxOf_eq [DecidableEq Y] (L : List (Y × Perm (Fin n))) (y : Y) :
    (L.map Prod.fst).idxOf y = L.findIdx (fun q => decide (q.1 = y)) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [List.map_cons, List.idxOf_cons, List.findIdx_cons, ih]
    by_cases h : p.1 = y
    · simp [h]
    · have : (p.1 == y) = false := by simpa using h
      simp [this, h]

theorem vsQ_map_finRange_add {β : Type*} {t G : ℕ} (f : Fin (t + G) → β) :
    (List.finRange (t + G)).map f =
      (List.finRange t).map (fun i => f (Fin.castAdd G i)) ++
        (List.finRange G).map (fun k => f (Fin.natAdd t k)) := by
  rw [← List.ofFn_eq_map, List.ofFn_add, List.ofFn_eq_map, List.ofFn_eq_map]
  rfl

theorem VsQOrbL.length_eq {L : List (Y × Perm (Fin n))} (hL : VsQOrbL α gs y₀ L) :
    L.length = (vsQOrb α gs y₀).ncard := by
  classical
  have e : vsQOrb α gs y₀ = ↑(L.map Prod.fst).toFinset := by
    ext y; simp only [Finset.mem_coe, List.mem_toFinset]; exact (hL.mem y).symm
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL.nodup, List.length_map]

section

variable (hα : VsQPAct K α) (hK : genGroup gs ≤ K) {L : List (Y × Perm (Fin n))}
  (hL : VsQOrbL α gs y₀ L)

/-- The encoding of `ρ h`: the entries of `h`, then the shifted positions `n + π(h) j`. -/
theorem vsQRho_enc (h : genGroup gs) :
    encPerm (vsQRho hα hK hL h) =
      .list ((List.finRange n).map (fun i => .nat ((h : Perm (Fin n)) i)) ++
        (List.finRange L.length).map (fun j => .nat (n + vsQPiF hα hK hL h j))) := by
  unfold encPerm
  rw [vsQ_map_finRange_add]
  congr 2
  · apply List.map_congr_left
    intro i _
    simp [vsQRho, sumToFin]
  · apply List.map_congr_left
    intro j _
    simp [vsQRho, sumToFin, vsQPi_apply]

open Classical in
/-- The shifted positions, as a map over the orbit list. -/
theorem vsQ_pos_map (h : genGroup gs) :
    L.map (fun p => Val.nat (n + vsQPos L (α h p.1))) =
      (List.finRange L.length).map (fun j => .nat (n + vsQPiF hα hK hL h j)) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_finRange]
  rfl

/-- `ρ h` restricted to the first `n` points is `h`. -/
theorem vsQRho_sum (h : genGroup gs) :
    vsQRho hα hK hL h = sumToFin (Perm.sumCongr (h : Perm (Fin n)) (vsQPi hα hK hL h)) := rfl

end

/-! ### The hypotheses -/

/-- The hypotheses of the transporter: an injective key, `⟨gs⟩ ≤ K`, the bound `S` on `n + 1`,
the number of generators plus one, the weight of the context, the weights of the keys of the
orbit and `B + 1`; the orbit has at most `B` points, and the action function `fa` costs at
most `A`. -/
structure VsQSotHyp (P : Program) (fa : ℕ) (K : Subgroup (Perm (Fin n)))
    (α : Perm (Fin n) → Y → Y) (gs : List (Perm (Fin n))) (keyY : Y → List ℕ) (y₀ : Y)
    (ac : Val) (S A B : ℕ) : Prop where
  hk : Function.Injective keyY
  hK : genGroup gs ≤ K
  hn : n + 1 ≤ S
  hm : gs.length + 1 ≤ S
  hac : ac.wt ≤ S
  hkey : ∀ y ∈ vsQOrb α gs y₀, (natList (0 :: keyY y)).wt ≤ S
  hfa : ∀ g ∈ gs, ∀ y ∈ vsQOrb α gs y₀,
    FunDet P fa (.list [ac, encPerm g, natList (0 :: keyY y)]) (natList (0 :: keyY (α g y))) A
  hBS : B + 1 ≤ S
  hB : (vsQOrb α gs y₀).ncard ≤ B

variable {P : Program} {fa : ℕ} {keyY : Y → List ℕ} {ac : Val} {S A B : ℕ}

theorem VsQSotHyp.one_le (H : VsQSotHyp P fa K α gs keyY y₀ ac S A B) : 1 ≤ S := by
  have := H.hn; omega

theorem VsQSotHyp.wt_perm (H : VsQSotHyp P fa K α gs keyY y₀ ac S A B) (t : Perm (Fin n)) :
    (encPerm t).wt ≤ 4 * S ^ 2 :=
  (wt_encPerm_le t).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left H.hn 2))

/-- The weights of the orbit list. -/
theorem VsQSotHyp.wt_pairs (H : VsQSotHyp P fa K α gs keyY y₀ ac S A B)
    {L : List (Y × Perm (Fin n))} (hL : VsQOrbL α gs y₀ L) :
    L.length + 1 ≤ S ∧
      (∀ p ∈ L, (Val.list [natList (0 :: keyY p.1), encPerm p.2]).wt ≤ 16 * S ^ 2) ∧
      (vsQPairs keyY L).wt ≤ 40 * S ^ 3 := by
  have hS := H.one_le
  have hlen : L.length ≤ B := hL.length_eq ▸ H.hB
  have hpw : ∀ p ∈ L, (Val.list [natList (0 :: keyY p.1), encPerm p.2]).wt ≤ 16 * S ^ 2 := by
    intro p hp
    have h1 := wt_list2_le (natList (0 :: keyY p.1)) (encPerm p.2)
    have h2 := H.hkey p.1 ((hL.mem _).1 (List.mem_map_of_mem hp))
    have h3 := H.wt_perm p.2
    have h5 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
    have h6 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS
    omega
  refine ⟨by have := H.hBS; omega, hpw, ?_⟩
  have h1 := wt_list_le_of (L.map fun q => Val.list [natList (0 :: keyY q.1), encPerm q.2])
    (c := 16 * S ^ 2) (by
      simp only [List.mem_map, forall_exists_index, and_imp]
      rintro _ p hp rfl; exact hpw p hp)
  simp only [List.length_map] at h1
  have h2 : L.length * (2 * (16 * S ^ 2) + 1) ≤ S * (33 * S ^ 2) :=
    Nat.mul_le_mul (by have := H.hBS; omega)
      (by have : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS; omega)
  have e : S * (33 * S ^ 2) = 33 * S ^ 3 := by ring
  have h3 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  show (Val.list _).wt ≤ _
  omega

/-! ### The position of an image -/

/-- On `[[ac, Lv, n, g], x]`: `n` plus the position in `Lv` of the image under `g` of the point
of the pair `x`. The search sits at `fd`. -/
def vsQPiE (fa fd : ℕ) : Expr :=
  .arith .add (.get (arg 0) (.nat 2))
    (.call fd (mk2 (.call fa (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 3))
      (.get (arg 1) (.nat 0)))) (.get (arg 0) (.nat 1))))

/-- The cost of one position. -/
def vsQPiCost (S A : ℕ) : ℕ := A + 10 ^ 6 * S ^ 4

set_option maxHeartbeats 1000000 in
open Classical in
theorem vsQPi_spec {f fd eq : ℕ} (hf : P.funs[f]? = some (vsQPiE fa fd))
    (hfd : P.HasAt fd (findFuns fd (fd + 3))) (ht : P.funs[fd + 3]? = some (orbTestF eq))
    (heq : P.HasAt eq (eqNatsFuns eq)) (hα : VsQPAct K α)
    (H : VsQSotHyp P fa K α gs keyY y₀ ac S A B) {L : List (Y × Perm (Fin n))}
    (hL : VsQOrbL α gs y₀ L) {g : Perm (Fin n)} (hg : g ∈ gs) {p : Y × Perm (Fin n)}
    (hp : p ∈ L) :
    FunDet P f (.list [.list [ac, vsQPairs keyY L, .nat n, encPerm g],
        .list [natList (0 :: keyY p.1), encPerm p.2]])
      (.nat (n + vsQPos L (α g p.1))) (vsQPiCost S A) := by
  have hS := H.one_le
  have hk' : Function.Injective (fun y : Y => 0 :: keyY y) := fun a b h => H.hk (List.cons.inj h).2
  have hy : p.1 ∈ vsQOrb α gs y₀ := (hL.mem _).1 (List.mem_map_of_mem hp)
  have hgy : α g p.1 ∈ vsQOrb α gs y₀ :=
    vsQOrb_act hα H.hK (Subgroup.subset_closure hg) hy
  obtain ⟨hlen, hwp, hwL⟩ := H.wt_pairs hL
  set c := Val.list [ac, vsQPairs keyY L, .nat n, encPerm g] with hc
  set x := Val.list [natList (0 :: keyY p.1), encPerm p.2] with hx
  have d0 := Det.arg' (P := P) (vs := [c, x]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [c, x]) (rest := []) (j := 1) rfl
  have dac := Det.get' d0 (Det.nat 0) (show [ac, vsQPairs keyY L, .nat n, encPerm g][0]? = some ac
    from rfl)
  have dL := Det.get' d0 (Det.nat 1) (show [ac, vsQPairs keyY L, .nat n, encPerm g][1]? =
    some (vsQPairs keyY L) from rfl)
  have dn := Det.get' d0 (Det.nat 2) (show [ac, vsQPairs keyY L, .nat n, encPerm g][2]? =
    some (.nat n) from rfl)
  have dg := Det.get' d0 (Det.nat 3) (show [ac, vsQPairs keyY L, .nat n, encPerm g][3]? =
    some (encPerm g) from rfl)
  have dk := Det.get' d1 (Det.nat 0) (show [natList (0 :: keyY p.1), encPerm p.2][0]? =
    some (natList (0 :: keyY p.1)) from rfl)
  have dfa := Det.call (Det.mk3 dac dg dk) (H.hfa g hg p.1 hy)
  -- the search
  have hF := find_spec hfd (c := natList (0 :: keyY (α g p.1))) (xs := L.map (encPair (fun y : Y => 0 :: keyY y)))
    (q := pairTest n (fun y : Y => 0 :: keyY y) (α g p.1)) (B := fun _ => 100000 * S ^ 2) (by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
      have hqo : q.1 ∈ vsQOrb α gs y₀ := (hL.mem _).1 (List.mem_map_of_mem hq)
      have := orbTest_spec ht heq (fun y : Y => 0 :: keyY y) hS (α g p.1) q (H.hkey _ hgy) (H.hkey _ hqo) (hwp q hq)
      rw [pairTest_encPair hk']
      have e : decide (0 :: keyY (α g p.1) = 0 :: keyY q.1) = decide (q.1 = α g p.1) :=
        Bool.decide_congr ⟨fun h => (hk' h).symm, fun h => h ▸ rfl⟩
      rw [e] at this
      exact this)
  have eL : vsQPairs keyY L = .list (L.map (encPair (fun y : Y => 0 :: keyY y))) := rfl
  have hF' : FunAll P fd (.list [natList (0 :: keyY (α g p.1)), vsQPairs keyY L])
      (fun w c => w = .nat (vsQPos L (α g p.1)) ∧ c ≤ 200000 * S ^ 4) := by
    rw [eL]
    refine hF.mono fun w cost hw => ⟨by rw [hw.1, findIdx_map_pairTest hk', vsQPos,
      vsQ_idxOf_eq], ?_⟩
    have hc := hw.2
    rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
    have w1 := wt_list2_le (natList (0 :: keyY (α g p.1))) (vsQPairs keyY L)
    have w2 := H.hkey _ hgy
    have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
    have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
    have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
    have h1 : L.length * (100000 * S ^ 2) ≤ S * (100000 * S ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have e1 : (Val.list [natList (0 :: keyY (α g p.1)), .list (L.map (encPair (fun y : Y => 0 :: keyY y)))]).wt =
      (Val.list [natList (0 :: keyY (α g p.1)), vsQPairs keyY L]).wt := rfl
    rw [e1] at hc
    have h2 : loopModK * (L.length + 1) * ((Val.list [natList (0 :: keyY (α g p.1)),
        vsQPairs keyY L]).wt + 2 * L.length + 3) ≤ loopModK * S * (95 * S ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e2 : S * (100000 * S ^ 2) = 100000 * S ^ 3 := by ring
    have e3 : loopModK * S * (95 * S ^ 3) = 95000 * S ^ 4 := by simp only [loopModK]; ring
    omega
  have dfd := Det.call (Det.mk2 dfa dL) hF'
  have dsum := Det.arith' (op := .add) (z := n + vsQPos L (α g p.1)) dn dfd rfl
  refine FunDet.intro hf (dsum.mono ?_)
  -- the cost
  have wc := wt_list4_le ac (vsQPairs keyY L) (.nat n) (encPerm g)
  have wx := wt_list2_le (natList (0 :: keyY p.1)) (encPerm p.2)
  have wa := wt_list2_le c x
  have w3 := wt_list3_le ac (encPerm g) (natList (0 :: keyY p.1))
  have w4 := wt_list2_le (natList (0 :: keyY (α g p.1))) (vsQPairs keyY L)
  have wn := wt_nat_le n
  have wg := H.wt_perm g
  have wpp := H.wt_perm p.2
  have wk1 := H.hkey _ hy
  have wk2 := H.hkey _ hgy
  have hac := H.hac
  have hn := H.hn
  have hpos : vsQPos L (α g p.1) ≤ L.length := by
    classical
    unfold vsQPos
    exact (List.idxOf_le_length).trans (by simp)
  have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
  have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
  have ex : x.wt = (Val.list [natList (0 :: keyY p.1), encPerm p.2]).wt := rfl
  have ec : c.wt = (Val.list [ac, vsQPairs keyY L, .nat n, encPerm g]).wt := rfl
  have wnat := wt_nat_le (vsQPos L (α g p.1))
  simp only [vsQPiCost]
  omega

/-! ### The permutation `ρ g` of one generator -/

/-- On `[[ac, Lv, n], g]`: the encoding of `ρ g`, the entries of `g` followed by the shifted
positions. Append sits at `ap`, the map of `vsQPiE` at `mp`. -/
def vsQRhoE (ap mp : ℕ) : Expr :=
  .call ap (mk2 (arg 1) (.call mp (mk2 (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
    (.get (arg 0) (.nat 2)) (arg 1)) (.get (arg 0) (.nat 1)))))

/-- The cost of one generator. -/
def vsQRhoCost (S A : ℕ) : ℕ := S * A + 10 ^ 7 * S ^ 5

set_option maxHeartbeats 2000000 in
open Classical in
theorem vsQRho_spec {f ap mp fd eq : ℕ} (hf : P.funs[f]? = some (vsQRhoE ap mp))
    (hap : P.HasAt ap (appendFuns ap)) (hmp : P.HasAt mp (mapFuns mp (mp + 3)))
    (hpi : P.funs[mp + 3]? = some (vsQPiE fa fd))
    (hfd : P.HasAt fd (findFuns fd (fd + 3))) (ht : P.funs[fd + 3]? = some (orbTestF eq))
    (heq : P.HasAt eq (eqNatsFuns eq)) (hα : VsQPAct K α)
    (H : VsQSotHyp P fa K α gs keyY y₀ ac S A B) {L : List (Y × Perm (Fin n))}
    (hL : VsQOrbL α gs y₀ L) {g : Perm (Fin n)} (hg : g ∈ gs) :
    FunDet P f (.list [.list [ac, vsQPairs keyY L, .nat n], encPerm g])
      (encPerm (vsQRho hα H.hK hL ⟨g, Subgroup.subset_closure hg⟩)) (vsQRhoCost S A) := by
  have hS := H.one_le
  obtain ⟨hlen, hwp, hwL⟩ := H.wt_pairs hL
  set c := Val.list [ac, vsQPairs keyY L, .nat n] with hc
  have d0 := Det.arg' (P := P) (vs := [c, encPerm g]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [c, encPerm g]) (rest := []) (j := 1) rfl
  have dac := Det.get' d0 (Det.nat 0) (show [ac, vsQPairs keyY L, .nat n][0]? = some ac from rfl)
  have dL := Det.get' d0 (Det.nat 1) (show [ac, vsQPairs keyY L, .nat n][1]? =
    some (vsQPairs keyY L) from rfl)
  have dn := Det.get' d0 (Det.nat 2) (show [ac, vsQPairs keyY L, .nat n][2]? =
    some (.nat n) from rfl)
  have dc4 := Det.mk4 dac dL dn d1
  -- the positions
  have hinj : ∀ q ∈ L, ∀ q' ∈ L, Val.list [natList (0 :: keyY q.1), encPerm q.2] =
      Val.list [natList (0 :: keyY q'.1), encPerm q'.2] →
      Val.nat (n + vsQPos L (α g q.1)) = Val.nat (n + vsQPos L (α g q'.1)) := by
    intro q _ q' _ he
    simp only [Val.list.injEq, List.cons.injEq, and_true] at he
    rw [H.hk (List.cons.inj (natList_injective he.1)).2]
  have hM := mapList_spec hmp L (fun q => Val.list [natList (0 :: keyY q.1), encPerm q.2])
    (fun q => Val.nat (n + vsQPos L (α g q.1)))
    (c := .list [ac, vsQPairs keyY L, .nat n, encPerm g]) (B := vsQPiCost S A) hinj
    (fun q hq => vsQPi_spec hpi hfd ht heq hα H hL hg hq)
  have dM := Det.call (Det.mk2 dc4 dL) hM
  set gh : genGroup gs := ⟨g, Subgroup.subset_closure hg⟩ with hgh
  have ep : L.map (fun q => Val.nat (n + vsQPos L (α g q.1))) =
      (List.finRange L.length).map (fun j => .nat (n + vsQPiF hα H.hK hL gh j)) :=
    vsQ_pos_map hα H.hK hL gh
  set ys := (List.finRange L.length).map (fun j => Val.nat (n + vsQPiF hα H.hK hL gh j))
    with hys
  set xs := (List.finRange n).map (fun i => Val.nat (g i)) with hxs
  have eg : encPerm g = .list xs := rfl
  rw [ep] at dM
  have hA := append_spec hap xs ys
  have er : encPerm (vsQRho hα H.hK hL gh) = .list (xs ++ ys) := vsQRho_enc hα H.hK hL gh
  have dA := Det.call (Det.mk2 d1 dM) (w := encPerm (vsQRho hα H.hK hL gh))
    (cb := loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
      (encPerm (vsQRho hα H.hK hL gh)).wt + 1)) (by
      rw [eg]
      refine hA.mono fun w cost hw => ⟨by rw [hw.1, er], ?_⟩
      have h2 := hw.2
      rw [hw.1, ← er] at h2
      exact h2)
  refine FunDet.intro hf (dA.mono ?_)
  -- the cost
  have hlenL : L.length ≤ S := by omega
  have hys_len : ys.length = L.length := by simp [hys]
  have wr : (encPerm (vsQRho hα H.hK hL gh)).wt ≤ 16 * S ^ 2 := by
    have := wt_encPerm_le (vsQRho hα H.hK hL gh)
    have h2 : (n + L.length + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by have := H.hn; omega) 2
    have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
    omega
  have wys : (Val.list ys).wt ≤ 13 * S ^ 2 := by
    have h1 := wt_list_le_of ys (c := 2 * S + 2) (by
      intro v hv
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
      have := wt_nat_le (n + (vsQPiF hα H.hK hL gh j : ℕ))
      have := (vsQPiF hα H.hK hL gh j).isLt
      have := H.hn
      omega)
    rw [hys_len] at h1
    have h2 : L.length * (2 * (2 * S + 2) + 1) ≤ S * (4 * S + 5) := Nat.mul_le_mul hlenL (by omega)
    have e : S * (4 * S + 5) = 4 * S ^ 2 + 5 * S := by ring
    have : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have wg := H.wt_perm g
  have wxs : (Val.list xs).wt ≤ 4 * S ^ 2 := eg ▸ wg
  have hac := H.hac
  have hn := H.hn
  have wn := wt_nat_le n
  have wc := wt_list3_le ac (vsQPairs keyY L) (.nat n)
  have wa := wt_list2_le c (encPerm g)
  have wc4 := wt_list4_le ac (vsQPairs keyY L) (.nat n) (encPerm g)
  have wm := wt_list2_le (.list [ac, vsQPairs keyY L, .nat n, encPerm g])
    (.list (L.map fun q => Val.list [natList (0 :: keyY q.1), encPerm q.2]))
  have wap := wt_list2_le (.list xs) (.list ys)
  have wm2 := wt_list2_le (.list [ac, vsQPairs keyY L, .nat n, encPerm g]) (vsQPairs keyY L)
  have wap2 := wt_list2_le (encPerm g) (.list ys)
  have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
  have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
  have p4 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by norm_num)
  have ewL : (Val.list (L.map fun q => Val.list [natList (0 :: keyY q.1), encPerm q.2])).wt =
    (vsQPairs keyY L).wt := rfl
  have k1 : L.length * vsQPiCost S A ≤ S * A + 10 ^ 6 * S ^ 5 := by
    have := Nat.mul_le_mul_right (vsQPiCost S A) hlenL
    have e : S * vsQPiCost S A = S * A + 10 ^ 6 * S ^ 5 := by simp only [vsQPiCost]; ring
    omega
  have k2 : mapK * (L.length + 1) * ((Val.list [Val.list [ac, vsQPairs keyY L, .nat n,
      encPerm g], .list (L.map fun q => Val.list [natList (0 :: keyY q.1), encPerm q.2])]).wt +
      (Val.list ys).wt + 1) ≤ mapK * (S + 1) * (500 * S ^ 3) := by
    apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
    omega
  have e2 : mapK * (S + 1) * (500 * S ^ 3) = 500000 * S ^ 4 + 500000 * S ^ 3 := by
    simp only [mapK]; ring
  have k3 : loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
      (encPerm (vsQRho hα H.hK hL gh)).wt + 1) ≤ loopModK * (S + 1) * (100 * S ^ 2) := by
    apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
    omega
  have e3 : loopModK * (S + 1) * (100 * S ^ 2) = 100000 * S ^ 3 + 100000 * S ^ 2 := by
    simp only [loopModK]; ring
  have eM : (Val.list (L.map fun q => Val.nat (n + vsQPos L (α g q.1)))).wt = (Val.list ys).wt := by
    rw [ep]
  have ec : c.wt = (Val.list [ac, vsQPairs keyY L, .nat n]).wt := rfl
  simp only [vsQRhoCost]
  omega

/-! ### Projecting pairs and reducing -/

theorem reduceCost_mono (h : Membership) (n : ℕ) {m m' : ℕ} (hm : m ≤ m') :
    reduceCost h n m ≤ reduceCost h n m' := by
  unfold reduceCost
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (by omega)) _))

/-- On `[c, x]`: gather `x` at the positions `c`. -/
def vsQSwapE (gt : ℕ) : Expr := .call gt (mk2 (arg 1) (arg 0))

theorem vsQSwap_spec {f gt : ℕ} (hf : P.funs[f]? = some (vsQSwapE gt))
    (hgt : P.HasAt gt (gatherFuns gt)) {n' : ℕ} (a : Perm (Fin n)) (c : Perm (Fin n')) :
    FunDet P f (.list [encPerm (1 : Perm (Fin n)), encPerm (sumToFin (Perm.sumCongr a c))])
      (encPerm a) (gatherK * (40 * (n + n' + 1) ^ 2) ^ 3 + 1000 * (n + n' + 1) ^ 2) := by
  set σ := sumToFin (Perm.sumCongr a c)
  have d0 := Det.arg' (P := P) (vs := [encPerm (1 : Perm (Fin n)), encPerm σ]) (rest := [])
    (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [encPerm (1 : Perm (Fin n)), encPerm σ]) (rest := [])
    (j := 1) rfl
  refine FunDet.intro hf ((Det.call (Det.mk2 d1 d0) (gatherLeft_spec hgt a c)).mono ?_)
  have w1 := wt_list2_le (encPerm (1 : Perm (Fin n))) (encPerm σ)
  have w2 := wt_list2_le (encPerm σ) (encPerm (1 : Perm (Fin n)))
  have w3 := wt_encPerm_le σ
  have h4 : (encPerm (1 : Perm (Fin n))).wt ≤ 4 * (n + n' + 1) ^ 2 :=
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have h5 : (encPerm a).wt ≤ 4 * (n + n' + 1) ^ 2 :=
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have : 1 ≤ (n + n' + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- On `[n, xs]`, `xs` a list of encoded `a ⊕ c`: the reduced group value of the `a`. -/
def vsQProjE (red mg mq rg : ℕ) : Expr :=
  .call red (.call mg (mk2 (arg 0) (.call mq (mk2 (.call rg (arg 0)) (arg 1)))))

set_option maxHeartbeats 2000000 in
theorem vsQProj_spec (hm : Membership) {f red mg mq rg gt jm : ℕ}
    (hf : P.funs[f]? = some (vsQProjE red mg mq rg))
    (hred : P.HasAt red (reduceFuns red jm)) (hj : P.prims[jm]? = some (membershipPrim hm))
    (hmg : P.HasAt mg (mkGroupFuns mg)) (hmq : P.HasAt mq (mapFuns mq (mq + 3)))
    (hsw : P.funs[mq + 3]? = some (vsQSwapE gt)) (hgt : P.HasAt gt (gatherFuns gt))
    (hrg : P.HasAt rg (rangeFuns rg)) {n' : ℕ} (ps : List (Perm (Fin n) × Perm (Fin n')))
    (hps : ps.length ≤ (n + n') ^ 2) :
    FunDet P f (.list [.nat n, .list (ps.map fun p => encPerm (sumToFin (Perm.sumCongr p.1 p.2)))])
      (encGroup (keepList (ps.map Prod.fst)))
      (10 ^ 13 * (n + n' + 1) ^ 9 + reduceCost hm n ((n + n') ^ 2)) := by
  set xs := ps.map fun p => encPerm (sumToFin (Perm.sumCongr p.1 p.2)) with hxs
  have d0 := Det.arg' (P := P) (vs := [.nat n, .list xs]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [.nat n, .list xs]) (rest := []) (j := 1) rfl
  have dr := Det.call d0 (range_det hrg n)
  have hinj : ∀ a ∈ ps, ∀ a' ∈ ps, encPerm (sumToFin (Perm.sumCongr a.1 a.2)) =
      encPerm (sumToFin (Perm.sumCongr a'.1 a'.2)) → encPerm a.1 = encPerm a'.1 := by
    intro a _ a' _ he
    have h1 := sumToFin_injective (encPerm_injective he)
    congr 1
    ext i
    have := congrArg (fun σ : Perm (Fin n ⊕ Fin n') => σ (Sum.inl i)) h1
    simp only [Perm.sumCongr_apply, Sum.map_inl, Sum.inl.injEq] at this
    rw [this]
  have hM := mapList_spec hmq ps (fun p => encPerm (sumToFin (Perm.sumCongr p.1 p.2)))
    (fun p => encPerm p.1) (c := encPerm (1 : Perm (Fin n)))
    (B := gatherK * (40 * (n + n' + 1) ^ 2) ^ 3 + 1000 * (n + n' + 1) ^ 2) hinj
    (fun p _ => vsQSwap_spec hsw hgt p.1 p.2)
  have dM := Det.call (Det.mk2 dr d1) hM
  have eM : ps.map (fun p => encPerm p.1) = (ps.map Prod.fst).map encPerm := by
    rw [List.map_map]; rfl
  rw [eM] at dM
  have dG := Det.call (Det.mk2 d0 dM) (mkGroup_spec hmg (ps.map Prod.fst))
  have dR := Det.call dG (reduce_spec hm hred hj (ps.map Prod.fst))
  refine FunDet.intro hf (dR.mono ?_)
  -- the cost
  have hB : gatherK * (40 * (n + n' + 1) ^ 2) ^ 3 + 1000 * (n + n' + 1) ^ 2 ≤
      6400000000 * (n + n' + 1) ^ 6 + 1000 * (n + n' + 1) ^ 2 := by
    have e : gatherK * (40 * (n + n' + 1) ^ 2) ^ 3 = 6400000000 * (n + n' + 1) ^ 6 := by
      simp only [gatherK]; ring
    omega
  obtain ⟨N, hN⟩ : ∃ N, n + n' + 1 = N := ⟨_, rfl⟩
  rw [hN] at hB
  rw [hN]
  have hnN : n + 1 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have q2 : (n + n') ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hpsN : ps.length ≤ N ^ 2 := hps.trans q2
  have p12 : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right hN1 (by norm_num)
  have p36 : N ^ 3 ≤ N ^ 6 := Nat.pow_le_pow_right hN1 (by norm_num)
  have p68 : N ^ 6 ≤ N ^ 8 := Nat.pow_le_pow_right hN1 (by norm_num)
  have p89 : N ^ 8 ≤ N ^ 9 := Nat.pow_le_pow_right hN1 (by norm_num)
  have hlen : (ps.map Prod.fst).length = ps.length := List.length_map _
  -- weights
  have wxs : (Val.list xs).wt ≤ 52 * N ^ 6 := by
    have := wt_list_encPerms_le (ps.map fun p => sumToFin (Perm.sumCongr p.1 p.2))
    rw [List.map_map] at this
    simp only [List.length_map, hN] at this
    have h2 : ((ps.length + 1) * N) ^ 2 ≤ (2 * N ^ 3) ^ 2 :=
      Nat.pow_le_pow_left (by
        have := Nat.mul_le_mul_right N (show ps.length + 1 ≤ 2 * N ^ 2 by omega)
        have e : 2 * N ^ 2 * N = 2 * N ^ 3 := by ring
        omega) 2
    have e : (2 * N ^ 3) ^ 2 = 4 * N ^ 6 := by ring
    exact this.trans (by simp only [Function.comp_def] at *; omega)
  have wfst : (Val.list ((ps.map Prod.fst).map encPerm)).wt ≤ 52 * N ^ 6 := by
    have := wt_list_encPerms_le (ps.map Prod.fst)
    rw [hlen] at this
    have h2 : ((ps.length + 1) * (n + 1)) ^ 2 ≤ (2 * N ^ 3) ^ 2 :=
      Nat.pow_le_pow_left (by
        have := Nat.mul_le_mul (show ps.length + 1 ≤ 2 * N ^ 2 by omega) (show n + 1 ≤ N by omega)
        have e : 2 * N ^ 2 * N = 2 * N ^ 3 := by ring
        omega) 2
    have e : (2 * N ^ 3) ^ 2 = 4 * N ^ 6 := by ring
    omega
  have wG : (encGroup (ps.map Prod.fst)).wt ≤ 400 * N ^ 6 := by
    have := wt_encGroup_le (ps.map Prod.fst)
    rw [hlen] at this
    have h2 : ((ps.length + 2) * (n + 1)) ^ 2 ≤ (3 * N ^ 3) ^ 2 :=
      Nat.pow_le_pow_left (by
        have := Nat.mul_le_mul (show ps.length + 2 ≤ 3 * N ^ 2 by omega) (show n + 1 ≤ N by omega)
        have e : 3 * N ^ 2 * N = 3 * N ^ 3 := by ring
        omega) 2
    have e : (3 * N ^ 3) ^ 2 = 9 * N ^ 6 := by ring
    omega
  have wK : (encGroup (keepList (ps.map Prod.fst))).wt ≤ 400 * N ^ 6 := by
    have := wt_encGroup_le_sq (length_keepList_le (ps.map Prod.fst))
    have : (n + 1) ^ 6 ≤ N ^ 6 := Nat.pow_le_pow_left (by omega) 6
    omega
  have w1 : (encPerm (1 : Perm (Fin n))).wt ≤ 4 * N ^ 2 :=
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnN _))
  have wn := wt_nat_le n
  have wa := wt_list2_le (.nat n) (.list xs)
  have wb := wt_list2_le (encPerm (1 : Perm (Fin n))) (.list xs)
  have wc := wt_list2_le (.nat n) (.list ((ps.map Prod.fst).map encPerm))
  -- the pieces
  have k1 : ps.length * (gatherK * (40 * N ^ 2) ^ 3 + 1000 * N ^ 2) ≤
      N ^ 2 * (6400000000 * N ^ 6 + 1000 * N ^ 2) := Nat.mul_le_mul hpsN hB
  have e1 : N ^ 2 * (6400000000 * N ^ 6 + 1000 * N ^ 2) =
      6400000000 * N ^ 8 + 1000 * N ^ 4 := by ring
  have exs : (Val.list [encPerm (1 : Perm (Fin n)),
      Val.list (ps.map fun p => encPerm (sumToFin (Perm.sumCongr p.1 p.2)))]).wt =
      (Val.list [encPerm (1 : Perm (Fin n)), .list xs]).wt := rfl
  have p4 : N ^ 4 ≤ N ^ 8 := Nat.pow_le_pow_right hN1 (by norm_num)
  have k2 : mapK * (ps.length + 1) * ((Val.list [encPerm (1 : Perm (Fin n)),
      Val.list (ps.map fun p => encPerm (sumToFin (Perm.sumCongr p.1 p.2)))]).wt +
      (Val.list ((ps.map Prod.fst).map encPerm)).wt + 1) ≤ mapK * (2 * N ^ 2) * (200 * N ^ 6) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : mapK * (2 * N ^ 2) * (200 * N ^ 6) = 400000 * N ^ 8 := by simp only [mapK]; ring
  have k3 : mkGroupK * (((ps.map Prod.fst).length + 2) * (n + 1)) ^ 3 ≤ mkGroupK * (3 * N ^ 3) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
      rw [hlen]
      have := Nat.mul_le_mul (show ps.length + 2 ≤ 3 * N ^ 2 by omega) (show n + 1 ≤ N by omega)
      have e : 3 * N ^ 2 * N = 3 * N ^ 3 := by ring
      omega) 3)
  have e3 : mkGroupK * (3 * N ^ 3) ^ 3 = 2700000 * N ^ 9 := by simp only [mkGroupK]; ring
  have k4 : reduceCost hm n (ps.map Prod.fst).length ≤ reduceCost hm n ((n + n') ^ 2) :=
    reduceCost_mono hm n (by rw [hlen]; exact hps)
  have k5 : 8000 * (n + 1) ^ 3 ≤ 8000 * N ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  omega

/-! ### The graph group -/

/-- The input of the transporter. -/
def vsQSotIn (ac : Val) (gs : List (Perm (Fin n))) (keyY : Y → List ℕ) (y₀ : Y) (B : ℕ) : Val :=
  .list [ac, .list (gs.map encPerm), natList (0 :: keyY y₀), .nat B, .nat n]

/-- On `[inp, Lv]`: the group value of the `ρ g`, `g ∈ gs`, on `Fin (n + |L|)`. -/
def vsQGraphE (mg mr : ℕ) : Expr :=
  .call mg (mk2 (.arith .add (.get (arg 0) (.nat 4)) (.length (arg 1)))
    (.call mr (mk2 (mk3 (.get (arg 0) (.nat 0)) (arg 1) (.get (arg 0) (.nat 4)))
      (.get (arg 0) (.nat 1)))))

/-- The cost of the graph group. -/
def vsQGraphCost (S A : ℕ) : ℕ := S ^ 2 * A + 10 ^ 9 * S ^ 6

theorem vsQ_mem_orb (hα : VsQPAct K α) : y₀ ∈ vsQOrb α gs y₀ :=
  ⟨1, (genGroup gs).one_mem, hα.one y₀⟩

theorem wt_vsQSotIn_le (hα : VsQPAct K α) (H : VsQSotHyp P fa K α gs keyY y₀ ac S A B) :
    (vsQSotIn ac gs keyY y₀ B).wt ≤ 60 * S ^ 4 ∧ (Val.list (gs.map encPerm)).wt ≤ 13 * S ^ 4 := by
  have hS := H.one_le
  have h1 := wt_list_encPerms_le gs
  have h2 : ((gs.length + 1) * (n + 1)) ^ 2 ≤ (S * S) ^ 2 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul H.hm H.hn) 2
  have e : (S * S) ^ 2 = S ^ 4 := by ring
  have hk := H.hkey y₀ (vsQ_mem_orb hα)
  have w := wt_list_le [ac, .list (gs.map encPerm), natList (0 :: keyY y₀), .nat B, .nat n]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w
  have wb := wt_nat_le B
  have wn := wt_nat_le n
  have hac := H.hac
  have hBS := H.hBS
  have hn := H.hn
  have p1 : S ≤ S ^ 4 := Nat.le_self_pow (by norm_num) _
  refine ⟨?_, by omega⟩
  show (Val.list _).wt ≤ _
  omega

set_option maxHeartbeats 2000000 in
theorem vsQGraph_spec {f mg mr ap fd eq : ℕ} (hf : P.funs[f]? = some (vsQGraphE mg mr))
    (hmg : P.HasAt mg (mkGroupFuns mg)) (hmr : P.HasAt mr (mapFuns mr (mr + 3)))
    (hrho : P.funs[mr + 3]? = some (vsQRhoE ap (mr + 4)))
    (hap : P.HasAt ap (appendFuns ap)) (hmp : P.HasAt (mr + 4) (mapFuns (mr + 4) (mr + 7)))
    (hpi : P.funs[mr + 7]? = some (vsQPiE fa fd))
    (hfd : P.HasAt fd (findFuns fd (fd + 3))) (ht : P.funs[fd + 3]? = some (orbTestF eq))
    (heq : P.HasAt eq (eqNatsFuns eq)) (hα : VsQPAct K α)
    (H : VsQSotHyp P fa K α gs keyY y₀ ac S A B) {L : List (Y × Perm (Fin n))}
    (hL : VsQOrbL α gs y₀ L) :
    FunDet P f (.list [vsQSotIn ac gs keyY y₀ B, vsQPairs keyY L])
      (encGroup (vsQDs hα H.hK hL)) (vsQGraphCost S A) := by
  have hS := H.one_le
  obtain ⟨hlen, hwp, hwL⟩ := H.wt_pairs hL
  obtain ⟨wIn, wgs⟩ := wt_vsQSotIn_le hα H
  set inp := vsQSotIn ac gs keyY y₀ B with hinp
  have d0 := Det.arg' (P := P) (vs := [inp, vsQPairs keyY L]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [inp, vsQPairs keyY L]) (rest := []) (j := 1) rfl
  have dn := Det.get' d0 (Det.nat 4) (show [ac, .list (gs.map encPerm), natList (0 :: keyY y₀),
    .nat B, .nat n][4]? = some (.nat n) from rfl)
  have dac := Det.get' d0 (Det.nat 0) (show [ac, .list (gs.map encPerm), natList (0 :: keyY y₀),
    .nat B, .nat n][0]? = some ac from rfl)
  have dgs := Det.get' d0 (Det.nat 1) (show [ac, .list (gs.map encPerm), natList (0 :: keyY y₀),
    .nat B, .nat n][1]? = some (.list (gs.map encPerm)) from rfl)
  have dlen := Det.length (vs := L.map fun q => Val.list [natList (0 :: keyY q.1), encPerm q.2]) d1
  have dsum := Det.arith' (op := .add) (z := n + L.length) dn dlen (by
    simp [GI.Machine.BinOp.eval])
  -- the map over the generators
  have ea : gs.attach.map (fun g => encPerm g.1) = gs.map encPerm := by simp
  have hinj : ∀ g ∈ gs.attach, ∀ g' ∈ gs.attach, encPerm g.1 = encPerm g'.1 →
      encPerm (vsQRho hα H.hK hL ⟨g.1, Subgroup.subset_closure g.2⟩) =
        encPerm (vsQRho hα H.hK hL ⟨g'.1, Subgroup.subset_closure g'.2⟩) := by
    intro g _ g' _ he
    rw [Subtype.ext (encPerm_injective he)]
  have hM := mapList_spec hmr gs.attach (fun g => encPerm g.1)
    (fun g => encPerm (vsQRho hα H.hK hL ⟨g.1, Subgroup.subset_closure g.2⟩))
    (c := .list [ac, vsQPairs keyY L, .nat n]) (B := vsQRhoCost S A) hinj
    (fun g _ => vsQRho_spec hrho hap hmp hpi hfd ht heq hα H hL g.2)
  rw [ea] at hM
  have eo : gs.attach.map (fun g => encPerm (vsQRho hα H.hK hL ⟨g.1, Subgroup.subset_closure g.2⟩))
      = (vsQDs hα H.hK hL).map encPerm := by
    rw [vsQDs, List.map_map]; rfl
  rw [eo] at hM
  have dM := Det.call (Det.mk2 (Det.mk3 dac d1 dn) dgs) hM
  have dG := Det.call (Det.mk2 dsum dM) (mkGroup_spec hmg (vsQDs hα H.hK hL))
  refine FunDet.intro hf (dG.mono ?_)
  -- the cost
  have hlenD : (vsQDs hα H.hK hL).length = gs.length := by simp [vsQDs]
  have hlenA : gs.attach.length = gs.length := List.length_attach
  have hm := H.hm
  have hn := H.hn
  have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
  have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
  have p4 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by norm_num)
  have p5 : S ^ 5 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by norm_num)
  have wD : (Val.list ((vsQDs hα H.hK hL).map encPerm)).wt ≤ 52 * S ^ 4 := by
    have h1 := wt_list_encPerms_le (vsQDs hα H.hK hL)
    rw [hlenD] at h1
    have h2 : ((gs.length + 1) * (n + L.length + 1)) ^ 2 ≤ (S * (2 * S)) ^ 2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul hm (by omega)) 2
    have e : (S * (2 * S)) ^ 2 = 4 * S ^ 4 := by ring
    omega
  have k1 : gs.attach.length * vsQRhoCost S A ≤ S ^ 2 * A + 10 ^ 7 * S ^ 6 := by
    rw [hlenA]
    have := Nat.mul_le_mul_right (vsQRhoCost S A) (show gs.length ≤ S by omega)
    have e : S * vsQRhoCost S A = S ^ 2 * A + 10 ^ 7 * S ^ 6 := by simp only [vsQRhoCost]; ring
    omega
  have hac := H.hac
  have wn := wt_nat_le n
  have wc3 := wt_list3_le ac (vsQPairs keyY L) (.nat n)
  have wm := wt_list2_le (.list [ac, vsQPairs keyY L, .nat n]) (.list (gs.map encPerm))
  have k2 : mapK * (gs.attach.length + 1) * ((Val.list [Val.list [ac, vsQPairs keyY L, .nat n],
      .list (gs.map encPerm)]).wt + (Val.list ((vsQDs hα H.hK hL).map encPerm)).wt + 1) ≤
      mapK * S * (300 * S ^ 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : mapK * S * (300 * S ^ 4) = 300000 * S ^ 5 := by simp only [mapK]; ring
  have k3 : mkGroupK * (((vsQDs hα H.hK hL).length + 2) * (n + L.length + 1)) ^ 3 ≤
      mkGroupK * ((2 * S) * (2 * S)) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) (by omega)) 3)
  have e3 : mkGroupK * ((2 * S) * (2 * S)) ^ 3 = 6400000 * S ^ 6 := by simp only [mkGroupK]; ring
  have wG : (encGroup (vsQDs hα H.hK hL)).wt ≤ 1000 * S ^ 4 := by
    have h1 := wt_encGroup_le (vsQDs hα H.hK hL)
    have h2 : ((((vsQDs hα H.hK hL).length + 2) * (n + L.length + 1))) ^ 2 ≤ ((2 * S) * (2 * S)) ^ 2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) (by omega)) 2
    have e : ((2 * S) * (2 * S)) ^ 2 = 16 * S ^ 4 := by ring
    omega
  have wI := wt_list2_le inp (vsQPairs keyY L)
  have w5 := wt_list2_le (.nat (n + L.length)) (.list ((vsQDs hα H.hK hL).map encPerm))
  have w6 := wt_nat_le (n + L.length)
  have w7 := wt_list3_le ac (vsQPairs keyY L) (.nat n)
  have eLv : (Val.list (L.map fun q => Val.list [natList (0 :: keyY q.1), encPerm q.2])).wt =
    (vsQPairs keyY L).wt := rfl
  have eLl : (L.map fun q => Val.list [natList (0 :: keyY q.1), encPerm q.2]).length = L.length :=
    List.length_map _
  simp only [vsQGraphCost]
  omega

/-! ### The stabilizer -/

theorem vsQ_lift_list (hα : VsQPAct K α) (hK : genGroup gs ≤ K) {L : List (Y × Perm (Fin n))}
    (hL : VsQOrbL α gs y₀ L) {hs : List (Perm (Fin (n + L.length)))}
    (h : ∀ σ ∈ hs, ∃ g : genGroup gs, vsQRho hα hK hL g = σ) :
    ∃ hs' : List (genGroup gs), hs = hs'.map (vsQRho hα hK hL) := by
  induction hs with
  | nil => exact ⟨[], rfl⟩
  | cons σ hs ih =>
    obtain ⟨g, hg⟩ := h σ (by simp)
    obtain ⟨hs', e⟩ := ih fun τ hτ => h τ (by simp [hτ])
    exact ⟨g :: hs', by simp [hg, e]⟩

theorem wt_encGroup_vsQDs (hα : VsQPAct K α) (H : VsQSotHyp P fa K α gs keyY y₀ ac S A B)
    {L : List (Y × Perm (Fin n))} (hL : VsQOrbL α gs y₀ L) :
    (encGroup (vsQDs hα H.hK hL)).wt ≤ 1000 * S ^ 4 := by
  obtain ⟨hlen, -, -⟩ := H.wt_pairs hL
  have hlenD : (vsQDs hα H.hK hL).length = gs.length := by simp [vsQDs]
  have h1 := wt_encGroup_le (vsQDs hα H.hK hL)
  have hm := H.hm
  have hn := H.hn
  have h2 : ((((vsQDs hα H.hK hL).length + 2) * (n + L.length + 1))) ^ 2 ≤ ((2 * S) * (2 * S)) ^ 2 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) (by omega)) 2
  have e : ((2 * S) * (2 * S)) ^ 2 = 16 * S ^ 4 := by ring
  omega

/-- On `[inp, Lv]`: the graph group, its stabilizer of the point `n`, and the reduced
projection. -/
def vsQSot2E (gr jp pj : ℕ) : Expr :=
  .letE (.call gr (.var 0))
    (.letE (.prim jp (mk2 (.var 1) (mk1 (.get (arg 0) (.nat 4)))))
      (.call pj (mk2 (.get (arg 0) (.nat 4)) (.var 2))))

/-- The bound of the stabilizer call. -/
noncomputable def vsQPsB (hps : PointwiseStab) (S : ℕ) : ℕ :=
  (pointwiseStabPrim hps).c * (3000 * S ^ 4 + 2) ^ (pointwiseStabPrim hps).k

/-- The cost of the second stage. -/
noncomputable def vsQSot2Cost (hps : PointwiseStab) (hm : Membership) (n S A : ℕ) : ℕ :=
  S ^ 2 * A + 10 ^ 16 * S ^ 9 + vsQPsB hps S + reduceCost hm n (4 * S ^ 2)

set_option maxHeartbeats 4000000 in
theorem vsQSot2_spec (hps : PointwiseStab) (hm : Membership)
    {f gr jp pj mg mr ap fd eq red mq rg gt jm : ℕ} (hf : P.funs[f]? = some (vsQSot2E gr jp pj))
    (hgr : P.funs[gr]? = some (vsQGraphE mg mr))
    (hmg : P.HasAt mg (mkGroupFuns mg)) (hmr : P.HasAt mr (mapFuns mr (mr + 3)))
    (hrho : P.funs[mr + 3]? = some (vsQRhoE ap (mr + 4)))
    (hap : P.HasAt ap (appendFuns ap)) (hmp : P.HasAt (mr + 4) (mapFuns (mr + 4) (mr + 7)))
    (hpi : P.funs[mr + 7]? = some (vsQPiE fa fd))
    (hfd : P.HasAt fd (findFuns fd (fd + 3))) (ht : P.funs[fd + 3]? = some (orbTestF eq))
    (heq : P.HasAt eq (eqNatsFuns eq))
    (hjp : P.prims[jp]? = some (pointwiseStabPrim hps))
    (hpj : P.funs[pj]? = some (vsQProjE red mg mq rg))
    (hred : P.HasAt red (reduceFuns red jm)) (hj : P.prims[jm]? = some (membershipPrim hm))
    (hmq : P.HasAt mq (mapFuns mq (mq + 3)))
    (hsw : P.funs[mq + 3]? = some (vsQSwapE gt)) (hgt : P.HasAt gt (gatherFuns gt))
    (hrg : P.HasAt rg (rangeFuns rg)) (hα : VsQPAct K α)
    (H : VsQSotHyp P fa K α gs keyY y₀ ac S A B) {L : List (Y × Perm (Fin n))}
    (hL : VsQOrbL α gs y₀ L) :
    FunAll P f (.list [vsQSotIn ac gs keyY y₀ B, vsQPairs keyY L]) (fun w cost =>
      ∃ ks : List (Perm (Fin n)), w = encGroup ks ∧ gens ks = vsQStabG hα H.hK y₀ ∧
        ks.length ≤ n ^ 2 ∧ cost ≤ vsQSot2Cost hps hm n S A) := by
  have hS := H.one_le
  have hpos : 0 < L.length := by
    have := hL.hd
    cases L with
    | nil => simp at this
    | cons _ _ => simp
  obtain ⟨hlen, hwp, hwL⟩ := H.wt_pairs hL
  obtain ⟨wIn, wgs⟩ := wt_vsQSotIn_le hα H
  set inp := vsQSotIn ac gs keyY y₀ B with hinp
  set a := Val.list [inp, vsQPairs keyY L] with ha
  set gv := encGroup (vsQDs hα H.hK hL) with hgv
  have dgv := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl)
    (vsQGraph_spec hgr hmg hmr hrho hap hmp hpi hfd ht heq hα H hL)
  apply FunAll.intro hf
  refine EvalAll.letE dgv fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  -- the stabilizer call
  have dn : Det P [a, gv] (.get (arg 0) (.nat 4)) (.nat n) _ :=
    Det.get' (Det.arg' (P := P) (vs := [inp, vsQPairs keyY L]) (rest := [gv]) (j := 0) rfl)
      (Det.nat 4) (show [ac, .list (gs.map encPerm), natList (0 :: keyY y₀), .nat B, .nat n][4]?
        = some (.nat n) from rfl)
  have dgv' : Det P [a, gv] (.var 1) gv _ := Det.var' (i := 1) rfl
  have darg0 := Det.mk2 dgv' (Det.mk1 dn)
  have darg : Det P [a, gv] (mk2 (.var 1) (mk1 (.get (arg 0) (.nat 4))))
      (.list [gv, encPts [Fin.natAdd n (⟨0, hpos⟩ : Fin L.length)]]) _ := darg0
  have hG : GroupVal (n + L.length) gv (gens (vsQDs hα H.hK hL)) := ⟨_, rfl, rfl⟩
  refine EvalAll.letE (pointwiseStab_call hps hjp darg hG) fun w cb hw => ?_
  obtain ⟨⟨hs, rfl, hslen, hsgen⟩, hcb⟩ := hw
  -- lift the generators
  obtain ⟨hs', ehs⟩ := vsQ_lift_list hα H.hK hL (hs := hs) (fun σ hσ => by
    have : σ ∈ gens hs := Subgroup.subset_closure hσ
    rw [hsgen, vsQ_pstab_mem hα H.hK hL hpos] at this
    obtain ⟨g, -, hg⟩ := this
    exact ⟨g, hg⟩)
  set ps : List (Perm (Fin n) × Perm (Fin L.length)) :=
    hs'.map fun g : genGroup gs => ((g : Perm (Fin n)), vsQPi hα H.hK hL g) with hps_def
  have eps : hs.map encPerm = ps.map fun p => encPerm (sumToFin (Perm.sumCongr p.1 p.2)) := by
    rw [ehs, hps_def, List.map_map, List.map_map]; rfl
  have hpslen : ps.length ≤ (n + L.length) ^ 2 := by
    rw [hps_def, List.length_map]; rw [ehs, List.length_map] at hslen; exact hslen
  have ehs' : ps.map Prod.fst = hs'.map Subtype.val := by rw [hps_def, List.map_map]; rfl
  have hstab : gens (hs'.map Subtype.val) = vsQStabG hα H.hK y₀ :=
    vsQ_stab_gens hα H.hK hL hpos hs' (by rw [← ehs]; exact hsgen)
  set wv := Val.list (hs.map encPerm) with hwv
  have dn2 : Det P [a, gv, wv] (.get (arg 0) (.nat 4)) (.nat n) _ :=
    Det.get' (Det.arg' (P := P) (vs := [inp, vsQPairs keyY L]) (rest := [gv, wv]) (j := 0) rfl)
      (Det.nat 4) (show [ac, .list (gs.map encPerm), natList (0 :: keyY y₀), .nat B, .nat n][4]?
        = some (.nat n) from rfl)
  have dw : Det P [a, gv, wv] (.var 2) wv _ := Det.var' (i := 2) rfl
  have hP := vsQProj_spec hm hpj hred hj hmg hmq hsw hgt hrg ps hpslen
  rw [← eps, ehs'] at hP
  have dP := Det.call (Det.mk2 dn2 dw) hP
  refine EvalAll.mono dP fun w' c' hw' => ⟨_, hw'.1, by rw [gens_keepList, hstab],
    length_keepList_le _, ?_⟩
  have hc' := hw'.2
  have hw1 : w'.wt = (encGroup (keepList (hs'.map Subtype.val))).wt := by rw [hw'.1]
  have ea : a.wt = (Val.list [inp, vsQPairs keyY L]).wt := rfl
  -- the cost
  have hn := H.hn
  have hlenL : n + L.length + 1 ≤ 2 * S := by omega
  have wG := wt_encGroup_vsQDs hα H hL
  have wK : (encGroup (keepList (hs'.map Subtype.val))).wt ≤ 320 * S ^ 6 := by
    have := wt_encGroup_le_sq (length_keepList_le (hs'.map Subtype.val))
    have : (n + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left hn 6
    omega
  have wW : wv.wt ≤ 13 * (2 * S) ^ 6 := by
    have := GensVal.wt_le (n := n + L.length) (v := wv) ⟨hs, rfl, hslen, hsgen⟩
    exact this.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlenL 6))
  have e6 : (2 * S) ^ 6 = 64 * S ^ 6 := by ring
  have wnS : 13 * (n + L.length + 1) ^ 6 ≤ 13 * (2 * S) ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlenL 6)
  have wpts := wt_list1_le (.nat n)
  have wn := wt_nat_le n
  have warg := wt_list2_le gv (.list [.nat n])
  have warg2 := wt_list2_le (.nat n) wv
  have wa := wt_list2_le inp (vsQPairs keyY L)
  have wG' : gv.wt ≤ 1000 * S ^ 4 := wG
  have hbound : (pointwiseStabPrim hps).bound (.list [gv, .list [.nat n]]) ≤ vsQPsB hps S := by
    unfold Prim.bound vsQPsB
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    have := (Val.list [gv, .list [.nat n]]).size_le_wt
    have p : S ≤ S ^ 4 := Nat.le_self_pow (by norm_num) _
    omega
  have e8 : encPts [Fin.natAdd n (⟨0, hpos⟩ : Fin L.length)] = .list [.nat n] := rfl
  rw [e8] at hcb
  have hN9 : 10 ^ 13 * (n + L.length + 1) ^ 9 ≤ 10 ^ 13 * (2 * S) ^ 9 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlenL 9)
  have e9 : (2 * S) ^ 9 = 512 * S ^ 9 := by ring
  have hR : reduceCost hm n ((n + L.length) ^ 2) ≤ reduceCost hm n (4 * S ^ 2) :=
    reduceCost_mono hm n (by
      have : (n + L.length) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
      omega)
  have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
  have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
  have p4 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by norm_num)
  have p5 : S ^ 6 ≤ S ^ 9 := Nat.pow_le_pow_right hS (by norm_num)
  simp only [vsQSot2Cost, vsQGraphCost] at *
  omega

/-! ### The program -/

/-- The entry, on `inp`: the orbit list `Lv`, then `[Lv, stage two on [inp, Lv]]`. -/
def vsQSotE (b s2 : ℕ) : Expr :=
  .letE (.call b (.var 0)) (mk2 (.var 1) (.call s2 (mk2 (.var 0) (.var 1))))

/-- **The transporter**, at base `b` (57 functions), with the action at `fa`, the pointwise
stabilizer primitive at `jp` and the membership primitive at `jm`. The entry is `b + 22`. -/
def vsQSotFuns (b fa jp jm : ℕ) : List Expr :=
  orbTFuns b fa ++
    ([vsQSotE b (b + 23), vsQSot2E (b + 24) jp (b + 25), vsQGraphE (b + 26) (b + 33),
      vsQProjE (b + 52) (b + 26) (b + 44) (b + 19)] ++
    (mkGroupFuns (b + 26) ++ (mapFuns (b + 33) (b + 36) ++ ([vsQRhoE (b + 41) (b + 37)] ++
    (mapFuns (b + 37) (b + 40) ++ ([vsQPiE fa (b + 8)] ++ (appendFuns (b + 41) ++
    (mapFuns (b + 44) (b + 47) ++ ([vsQSwapE (b + 48)] ++ (gatherFuns (b + 48) ++
    reduceFuns (b + 52) jm))))))))))

theorem _root_.GI.Lang.Program.HasAt.split {P : Program} {b : ℕ} {A B : List Expr} (h : P.HasAt b (A ++ B))
    {k : ℕ} (hk : A.length = k) : P.HasAt b A ∧ P.HasAt (b + k) B :=
  ⟨h.left, hk ▸ h.right⟩

/-- The cost of the transporter. -/
noncomputable def vsQSotCost (hps : PointwiseStab) (hm : Membership) (n S A : ℕ) : ℕ :=
  2 * (S ^ 2 * A) + orbTK * S ^ 6 + 10 ^ 17 * S ^ 9 + vsQPsB hps S + reduceCost hm n (4 * S ^ 2)

set_option maxHeartbeats 4000000 in
/-- **The small orbit transporter.** On `vsQSotIn ac gs keyY y₀ B` it returns the orbit list `L`
of `y₀` and a list `ks` of at most `n²` generators of the stabilizer of `y₀` in `⟨gs⟩`. -/
theorem vsQSot_spec [Countable Y] (hps : PointwiseStab) (hm : Membership) {b jp jm : ℕ}
    (h : P.HasAt b (vsQSotFuns b fa jp jm)) (hjp : P.prims[jp]? = some (pointwiseStabPrim hps))
    (hjm : P.prims[jm]? = some (membershipPrim hm)) (hα : VsQPAct K α)
    (H : VsQSotHyp P fa K α gs keyY y₀ ac S A B) :
    FunAll P (b + 22) (vsQSotIn ac gs keyY y₀ B) (fun w cost =>
      ∃ (L : List (Y × Perm (Fin n))) (ks : List (Perm (Fin n))),
        w = .list [vsQPairs keyY L, encGroup ks] ∧ VsQOrbL α gs y₀ L ∧
        gens ks = vsQStabG hα H.hK y₀ ∧ ks.length ≤ n ^ 2 ∧
        cost ≤ vsQSotCost hps hm n S A) := by
  have hS := H.one_le
  obtain ⟨hO, h1⟩ := h.split (length_orbTFuns b fa)
  obtain ⟨hH, h2⟩ := h1.split (k := 4) rfl
  obtain ⟨hmg, h3⟩ := h2.split (k := 7) rfl
  obtain ⟨hmr, h4⟩ := h3.split (k := 3) rfl
  obtain ⟨hrho, h5⟩ := h4.split (k := 1) rfl
  obtain ⟨hmp, h6⟩ := h5.split (k := 3) rfl
  obtain ⟨hpi, h7⟩ := h6.split (k := 1) rfl
  obtain ⟨hap, h8⟩ := h7.split (k := 3) rfl
  obtain ⟨hmq, h9⟩ := h8.split (k := 3) rfl
  obtain ⟨hsw, h10⟩ := h9.split (k := 1) rfl
  obtain ⟨hgt, hred⟩ := h10.split (k := 4) rfl
  have h22 : P.funs[b + 22]? = some (vsQSotE b (b + 23)) := by simpa using hH 0 (by simp)
  have h23 : P.funs[b + 23]? = some (vsQSot2E (b + 24) jp (b + 25)) := by
    simpa [Nat.add_assoc] using hH 1 (by simp)
  have h24 : P.funs[b + 24]? = some (vsQGraphE (b + 26) (b + 33)) := by
    simpa [Nat.add_assoc] using hH 2 (by simp)
  have h25 : P.funs[b + 25]? = some (vsQProjE (b + 52) (b + 26) (b + 44) (b + 19)) := by
    simpa [Nat.add_assoc] using hH 3 (by simp)
  have e1 : b + 22 + 4 = b + 26 := by omega
  have e2 : b + 22 + 4 + 7 = b + 33 := by omega
  have e3 : b + 22 + 4 + 7 + 3 = b + 33 + 3 := by omega
  have e4 : b + 22 + 4 + 7 + 3 + 1 = b + 33 + 4 := by omega
  have e5 : b + 22 + 4 + 7 + 3 + 1 + 3 = b + 33 + 7 := by omega
  have e6 : b + 22 + 4 + 7 + 3 + 1 + 3 + 1 = b + 41 := by omega
  have e7 : b + 22 + 4 + 7 + 3 + 1 + 3 + 1 + 3 = b + 44 := by omega
  have e8 : b + 22 + 4 + 7 + 3 + 1 + 3 + 1 + 3 + 3 = b + 44 + 3 := by omega
  have e9 : b + 22 + 4 + 7 + 3 + 1 + 3 + 1 + 3 + 3 + 1 = b + 48 := by omega
  have e10 : b + 22 + 4 + 7 + 3 + 1 + 3 + 1 + 3 + 3 + 1 + 4 = b + 52 := by omega
  rw [e1] at hmg
  rw [e2] at hmr
  rw [e3] at hrho
  rw [e4] at hmp
  rw [e5] at hpi
  rw [e6] at hap
  rw [e7] at hmq
  rw [e8] at hsw
  rw [e9] at hgt
  rw [e10] at hred
  replace hmr : P.HasAt (b + 33) (mapFuns (b + 33) (b + 33 + 3)) := hmr
  replace hrho : P.funs[b + 33 + 3]? = some (vsQRhoE (b + 41) (b + 33 + 4)) := hrho.single
  replace hmp : P.HasAt (b + 33 + 4) (mapFuns (b + 33 + 4) (b + 33 + 7)) := hmp
  replace hpi : P.funs[b + 33 + 7]? = some (vsQPiE fa (b + 8)) := hpi.single
  replace hmq : P.HasAt (b + 44) (mapFuns (b + 44) (b + 44 + 3)) := hmq
  replace hsw : P.funs[b + 44 + 3]? = some (vsQSwapE (b + 48)) := hsw.single
  have hfd : P.HasAt (b + 8) (findFuns (b + 8) (b + 8 + 3)) := (hO.block 8 (by rfl))
  have ht : P.funs[b + 8 + 3]? = some (orbTestF (b + 16)) := (hO.block 11 (gs := [_]) (by rfl)).single
  have heq : P.HasAt (b + 16) (eqNatsFuns (b + 16)) := hO.block 16 (by rfl)
  have hrg : P.HasAt (b + 19) (rangeFuns (b + 19)) := hO.block 19 (by rfl)
  have horb := vsQ_orbT_spec hO hα H.hK H.hk H.hn H.hm H.hac H.hkey H.hfa H.hBS H.hB
  obtain ⟨wIn, -⟩ := wt_vsQSotIn_le hα H
  set inp := vsQSotIn ac gs keyY y₀ B with hinp
  apply FunAll.intro h22
  refine EvalAll.letE (Ra := fun v c => ∃ L : List (Y × Perm (Fin n)), v = vsQPairs keyY L ∧
      VsQOrbL α gs y₀ L ∧ c ≤ inp.wt + 1 + (S ^ 2 * A + orbTK * S ^ 6) + v.wt + 1)
    (EvalAll.call_funAll (Det.var' (P := P) (env := [inp]) (i := 0) rfl) fun v ca hv => ?_) ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine horb.mono fun w c hw => ?_
    obtain ⟨L, rfl, hnd, hmem, hpr, hhd, hc⟩ := hw
    exact ⟨L, rfl, ⟨hnd, hmem, hpr, hhd⟩, by omega⟩
  rintro v ca ⟨L, rfl, hL, hca⟩
  have d1 : Det P [inp, vsQPairs keyY L] (.var 1) (vsQPairs keyY L) _ := Det.var' (i := 1) rfl
  have d0 : Det P [inp, vsQPairs keyY L] (.var 0) inp _ := Det.var' (i := 0) rfl
  have h2 := vsQSot2_spec hps hm h23 h24 hmg hmr hrho hap hmp hpi hfd ht heq hjp h25 hred hjm
    hmq hsw hgt hrg hα H hL
  have dm := Det.mk2 d0 d1
  refine (EvalAll.mk2_last d1 (EvalAll.call_funAll (Q := fun w c => ∃ ks : List (Perm (Fin n)),
      w = encGroup ks ∧ gens ks = vsQStabG hα H.hK y₀ ∧ ks.length ≤ n ^ 2 ∧
      c ≤ inp.wt + 1 + ((vsQPairs keyY L).wt + 1) + 2 * (Val.list [inp, vsQPairs keyY L]).wt + 7 +
        vsQSot2Cost hps hm n S A + w.wt + 1) dm fun v' ca' hv' => ?_)).mono ?_
  · obtain ⟨rfl, hca'⟩ := hv'
    refine h2.mono fun w c hw => ?_
    obtain ⟨ks, rfl, hks, hkl, hc⟩ := hw
    exact ⟨ks, rfl, hks, hkl, by omega⟩
  rintro w cost ⟨vb, cb, ⟨ks, rfl, hks, hkl, hc2⟩, rfl, hcost⟩
  refine ⟨L, ks, rfl, hL, hks, hkl, ?_⟩
  -- the cost
  obtain ⟨hlen, -, hwL⟩ := H.wt_pairs hL
  have wK : (encGroup ks).wt ≤ 320 * S ^ 6 := by
    have := wt_encGroup_le_sq hkl
    have : (n + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left H.hn 6
    omega
  have w1 := wt_list2_le inp (vsQPairs keyY L)
  have w2 := wt_list2_le (vsQPairs keyY L) (encGroup ks)
  have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
  have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
  have p4 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by norm_num)
  have p5 : S ^ 6 ≤ S ^ 9 := Nat.pow_le_pow_right hS (by norm_num)
  simp only [vsQSotCost, vsQSot2Cost] at *
  omega

end GI.Impl
