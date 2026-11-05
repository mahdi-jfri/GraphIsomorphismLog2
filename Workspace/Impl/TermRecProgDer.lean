module

public import Workspace.Impl.TermRecProgPcs

@[expose] public section

/-!
# T5, the relative derived series

`tmRi_der_spec`: on `[[gens H, gens N], ℓ, gens H]` the loop `b + 63` returns generators of
`A = relDerived H N ℓ`, at most `n²` of them. Each step (`tmRi_derStep_spec`) is one call of
**DerivedSubgroup**, the generators of `N` appended, and the cut to `n²` generators by
**Membership** (`reduce_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

theorem tmRi_gens_append (as bs : List (Perm (Fin n))) : gens (as ++ bs) = gens as ⊔ gens bs := by
  simp only [gens, List.mem_append, Set.setOf_or, Subgroup.closure_union]

theorem tmRi_reduceCost_mono (h : Membership) (n : ℕ) {m m' : ℕ} (hm : m ≤ m') :
    reduceCost h n m ≤ reduceCost h n m' := by
  unfold reduceCost
  gcongr

/-- `append_spec` as a deterministic call. -/
theorem tmRi_append_det {P : Program} {b : ℕ} (h : P.HasAt b (appendFuns b)) (xs ys : List Val) :
    FunDet P b (.list [.list xs, .list ys]) (.list (xs ++ ys))
      (loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
        (Val.list (xs ++ ys)).wt + 1)) :=
  (append_spec h xs ys).mono fun w c hw => ⟨hw.1, by have := hw.2; rw [hw.1] at this; exact this⟩

/-- The cost bound of one step of the derived series. -/
noncomputable def tmRiDerStepC (pder : Prim) (hmem : Membership) (n : ℕ) : ℕ :=
  pder.boundSize (400 * (n + 1) ^ 6) + reduceCost hmem n (2 * n ^ 2) + 10 ^ 9 * (n + 1) ^ 8

/-- **One step of the derived series**: `D ↦ ⟨[D, D], N⟩`. -/
theorem tmRi_derStep_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {σH σN gs : List (Perm (Fin n))}
    (hH : σH.length ≤ n ^ 2) (hN : σN.length ≤ n ^ 2) (hgs : gs.length ≤ n ^ 2) (i : ℕ)
    (hi : i ≤ n ^ 2 + 5) :
    FunAll P (b + 8) (.list [.list [encGroup σH, encGroup σN], .nat i, encGroup gs])
      (fun w cost => (∃ gs', w = encGroup gs' ∧ gens gs' = ⁅gens gs, gens gs⁆ ⊔ gens σN ∧
        gs'.length ≤ n ^ 2) ∧ cost ≤ tmRiDerStepC (derivedSubgroupPrim hder) hmem n) := by
  set c : Val := .list [encGroup σH, encGroup σN] with hc
  set vs : List Val := [c, .nat i, encGroup gs] with hvs
  have hwH := wt_encGroup_le_sq hH
  have hwN := wt_encGroup_le_sq hN
  have hwg := wt_encGroup_le_sq hgs
  have hcw : c.wt ≤ 2 * ((encGroup σH).wt + (encGroup σN).wt) + 6 := wt_list2_le _ _
  have hiw := wt_nat_le i
  have hvw : (Val.list vs).wt ≤ 2 * (c.wt + (Val.nat i).wt + (encGroup gs).wt) + 7 :=
    wt_list3_le _ _ _
  have h1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hn2 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
  have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hvwb : (Val.list vs).wt ≤ 4000 * (n + 1) ^ 6 := by omega
  -- the derived subgroup
  have d2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have hsz : (encGroup gs).size ≤ 400 * (n + 1) ^ 6 :=
    (Val.size_le_wt _).trans (by omega)
  have hbd := (derivedSubgroupPrim hder).bound_le hsz
  refine FunAll.intro hP.derStep (EvalAll.letE (derivedSubgroup_call hder hP.der d2
    ⟨gs, rfl, rfl⟩) fun L cL hL => ?_)
  obtain ⟨⟨hs, rfl, hsl, hsg⟩, hcL⟩ := hL
  -- the append and the reduction
  set env : List Val := [.list vs, .list (hs.map encPerm)] with henv
  have e0 := Det.arg' (P := P) (vs := vs) (rest := [.list (hs.map encPerm)]) (j := 0) rfl
  have e2 := Det.arg' (P := P) (vs := vs) (rest := [.list (hs.map encPerm)]) (j := 2) rfl
  have dn := Det.get' e2 (Det.nat 0) (v := .nat n) rfl
  have dgN := Det.get' (Det.get' e0 (Det.nat 1) (v := encGroup σN) rfl) (Det.nat 1)
    (v := .list ((1 :: σN).map encPerm)) rfl
  have dL := Det.var' (P := P) (env := env) (i := 1) (v := .list (hs.map encPerm)) rfl
  have dapp := Det.call (Det.mk2 dgN dL) (tmRi_append_det hP.app _ _)
  have happ : Val.list (List.map encPerm (1 :: σN) ++ List.map encPerm hs) =
      .list ((1 :: (σN ++ hs)).map encPerm) := by simp
  rw [happ] at dapp
  have dgrp := Det.mk2 dn dapp
  have hgrp : Val.list [.nat n, .list ((1 :: (σN ++ hs)).map encPerm)] = encGroup (σN ++ hs) := by
    simp [encGroup, GI.Cited.encPerms]
  rw [hgrp] at dgrp
  have dred := Det.call dgrp (reduce_spec hmem hP.red hP.mem (σN ++ hs))
  refine (dred.post fun cost hcost => ⟨⟨keepList (σN ++ hs), rfl, ?_, length_keepList_le _⟩, ?_⟩)
  · rw [gens_keepList, tmRi_gens_append, hsg, sup_comm]
  · have hl2 : (σN ++ hs).length ≤ 2 * n ^ 2 := by simp; omega
    have hT : ((σN ++ hs).length + 2) * (n + 1) ≤ 2 * (n + 1) ^ 3 := by
      have e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      have : (σN ++ hs).length + 2 ≤ 2 * (n + 1) ^ 2 := by omega
      calc _ ≤ 2 * (n + 1) ^ 2 * (n + 1) := Nat.mul_le_mul_right _ this
        _ = 2 * (n + 1) ^ 3 := by ring
    have hT2 : (((σN ++ hs).length + 2) * (n + 1)) ^ 2 ≤ 4 * (n + 1) ^ 6 := by
      calc _ ≤ (2 * (n + 1) ^ 3) ^ 2 := Nat.pow_le_pow_left hT 2
        _ = 4 * (n + 1) ^ 6 := by ring
    have hT1 : (((σN ++ hs).length + 1) * (n + 1)) ^ 2 ≤ 4 * (n + 1) ^ 6 :=
      le_trans (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (by omega)) 2) hT2
    have hG2 := wt_encGroup_le (σN ++ hs)
    have hL2 := wt_list_encPerms_le (1 :: (σN ++ hs))
    simp only [List.length_cons] at hL2
    rw [show (σN ++ hs).length + 1 + 1 = (σN ++ hs).length + 2 from rfl] at hL2
    have e2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    have hkw := wt_encGroup_le_sq (length_keepList_le (σN ++ hs))
    have hhs := wt_list_encPerms_le_sq hsl
    have hNl : (Val.list (List.map encPerm (1 :: σN))).wt < (encGroup σN).wt :=
      wt_le_wt_list (vs := [.nat n, _]) (by simp)
    have h2w := wt_list2_le (.list (List.map encPerm (1 :: σN))) (.list (List.map encPerm hs))
    have hnw := wt_nat_le n
    have hn6 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    have hlm : loopModK * ((List.map encPerm hs).length + 1) *
        ((Val.list [Val.list (List.map encPerm (1 :: σN)), Val.list (List.map encPerm hs)]).wt +
          (List.map encPerm hs).length + (Val.list (List.map encPerm (1 :: (σN ++ hs)))).wt + 1) ≤
        10 ^ 6 * (n + 1) ^ 8 := by
      rw [mul_assoc, List.length_map]
      calc _ ≤ loopModK * ((n + 1) ^ 2 * (1000 * (n + 1) ^ 6)) := by
            refine Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
        _ = 10 ^ 6 * (n + 1) ^ 8 := by simp only [loopModK]; ring
    have hrc := tmRi_reduceCost_mono hmem n hl2
    unfold tmRiDerStepC
    omega

/-- The cost bound of the derived series. -/
noncomputable def tmRiDerC (pder : Prim) (hmem : Membership) (n : ℕ) : ℕ :=
  (n ^ 2 + 5) * tmRiDerStepC pder hmem n + 10 ^ 8 * (n + 1) ^ 8

/-- **The relative derived series**: generators of `relDerived H N ℓ`. -/
theorem tmRi_der_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {σH σN : List (Perm (Fin n))}
    (hH : σH.length ≤ n ^ 2) (hN : σN.length ≤ n ^ 2) (ℓ : ℕ) (hℓ : ℓ ≤ n ^ 2 + 5) :
    FunAll P (b + 63) (.list [.list [encGroup σH, encGroup σN], .nat ℓ, encGroup σH])
      (fun w cost => (∃ gs, w = encGroup gs ∧ gens gs = relDerived (gens σH) (gens σN) ℓ ∧
        gs.length ≤ n ^ 2) ∧ cost ≤ tmRiDerC (derivedSubgroupPrim hder) hmem n) := by
  have hit := iter_spec hP.iterDer (c := .list [encGroup σH, encGroup σN]) (k := ℓ)
    (acc0 := encGroup σH)
    (Inv := fun i acc => ∃ gs, acc = encGroup gs ∧ gens gs = relDerived (gens σH) (gens σN) i ∧
      gs.length ≤ n ^ 2)
    (M := 320 * (n + 1) ^ 6) (B := fun _ => tmRiDerStepC (derivedSubgroupPrim hder) hmem n)
    ⟨σH, rfl, rfl, hH⟩ (fun i acc _ ⟨gs, h1, _, h3⟩ => h1 ▸ wt_encGroup_le_sq h3)
    (fun i acc hi ⟨gs, h1, h2, h3⟩ => by
      subst h1
      refine (tmRi_derStep_spec hP hH hN h3 i (by omega)).mono fun w cost hw => ⟨?_, hw.2⟩
      obtain ⟨gs', h1', h2', h3'⟩ := hw.1
      exact ⟨gs', h1', by rw [h2', h2, relDerived_succ], h3'⟩)
  refine hit.mono fun w cost hw => ⟨hw.1, ?_⟩
  have h2 := hw.2
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
  have hwH := wt_encGroup_le_sq hH
  have hwN := wt_encGroup_le_sq hN
  have hcw := wt_list2_le (encGroup σH) (encGroup σN)
  have h3w := wt_list3_le (.list [encGroup σH, encGroup σN]) (.nat ℓ) (encGroup σH)
  have hlw := wt_nat_le ℓ
  have e2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hloop : loopModK * (ℓ + 1) * ((Val.list [.list [encGroup σH, encGroup σN], .nat ℓ,
      encGroup σH]).wt + ℓ + 320 * (n + 1) ^ 6 + 1) ≤ 10 ^ 8 * (n + 1) ^ 8 := by
    rw [mul_assoc]
    calc _ ≤ loopModK * (6 * (n + 1) ^ 2 * (10000 * (n + 1) ^ 6)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
      _ = 6 * 10 ^ 7 * (n + 1) ^ 8 := by simp only [loopModK]; ring
      _ ≤ 10 ^ 8 * (n + 1) ^ 8 := Nat.mul_le_mul_right _ (by norm_num)
  have hst : ℓ * tmRiDerStepC (derivedSubgroupPrim hder) hmem n ≤
      (n ^ 2 + 5) * tmRiDerStepC (derivedSubgroupPrim hder) hmem n := Nat.mul_le_mul_right _ hℓ
  unfold tmRiDerC
  omega

end GI.Impl
