import Workspace.Impl.NClPreSift

/-!
# The lifts of the preimage program

`preLift_spec`: for `m ∈ 1 :: ms`, the function `b + 7` sifts `n'` times from `x = 1` and returns
some `x ∈ D'` that lifts `m` (it maps `n + k` to `n + m k` for all `k`).
`preLifts_spec`: the map of it over `1 :: ms`.
-/

namespace GI.Impl

open GI.Cited GI.Lang Equiv
open GI.Machine (BinOp)

/-- The cost of one lift, for an instance of weight below `Y`. -/
noncomputable def nclLiftCost (h : PointwiseStab) (Y : ℕ) : ℕ :=
  Y * nclSiftCost h Y + 2 * 10 ^ 6 * Y ^ 3

/-- The invariant of the sifting loop. -/
def NclSiftInv (I : PreimageInst) (m : Perm (Fin I.n')) (i : ℕ) (acc : Val) : Prop :=
  ∃ x, acc = .list [encPerm x, encPts (nclDeltaPts (n' := I.n') I.n i)] ∧ x ∈ nclPreD I ∧
    NclAgreeBelow x m i

theorem nclWt_list_nil : (Val.list []).wt ≤ 4 := by
  have := wt_list_le ([] : List Val); simpa using this

set_option maxHeartbeats 1000000 in
/-- **A lift.** -/
theorem preLift_spec {P : Program} {b j : ℕ} {h : PointwiseStab} (hP : PreAt P b j h)
    (I : PreimageInst) {m : Perm (Fin I.n')} (hm : m ∈ 1 :: I.ms) :
    FunAll P (b + 7) (.list [preimageEnc I, encPerm m])
      (fun w c => (∃ x, w = encPerm x ∧ x ∈ nclPreD I ∧ NclLifts x m) ∧
        c ≤ nclLiftCost h ((preimageEnc I).wt + 1)) := by
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = (preimageEnc I).wt + 1 := ⟨_, rfl⟩
  rw [← hYd]
  have hNY : I.n + I.n' + 1 ≤ Y := by have := nclDeg_lt_preimageEnc I; omega
  have y1 : 1 ≤ Y := by omega
  have p2 : (I.n + I.n' + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hNY 2
  have p2' : (I.n' + 1) ^ 2 ≤ Y ^ 2 := (Nat.pow_le_pow_left (by omega) 2).trans p2
  have q12 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right y1 (by omega)
  set A : Val := .list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms] with hA
  have eA : preimageEnc I = A := rfl
  rw [eA]
  set c : Val := .list [A, encPerm m] with hc
  have wA : A.wt + 1 = Y := by rw [hYd, eA]
  have wm := wt_encPerm_le m
  have w1 := wt_encPerm_le (1 : Perm (Fin (I.n + I.n')))
  have wc : c.wt ≤ 2 * Y + 8 * Y ^ 2 + 6 := by
    have := wt_list2_le A (encPerm m); rw [hc]; omega
  -- the argument of the loop
  have dA0 : Det P [c] (arg 0) A (2 * c.wt + 5) :=
    (Det.arg' (vs := [A, encPerm m]) (rest := []) (j := 0) rfl).mono (by rw [hc]; try omega)
  have dK := Det.get' (Det.get' dA0 (Det.nat 2)
      (show [Val.nat I.n, encGroup (nclPreDs I), encGroup I.ms][2]? = some (encGroup I.ms) from rfl))
    (Det.nat 0) (show [Val.nat I.n', .list ((1 :: I.ms).map encPerm)][0]? = some (.nat I.n') from rfl)
  have dOne := Det.get' (Det.get' (Det.get' dA0 (Det.nat 1)
      (show [Val.nat I.n, encGroup (nclPreDs I), encGroup I.ms][1]? =
        some (encGroup (nclPreDs I)) from rfl)) (Det.nat 1)
      (show [Val.nat (I.n + I.n'), .list ((1 :: nclPreDs I).map encPerm)][1]? =
        some (.list ((1 :: nclPreDs I).map encPerm)) from rfl))
    (Det.nat 0) (show ((1 :: nclPreDs I).map encPerm)[0]? =
      some (encPerm (1 : Perm (Fin (I.n + I.n')))) from rfl)
  have dArg := Det.mk3 (Det.var' (P := P) (env := [c]) (i := 0) rfl) dK (Det.mk2 dOne Det.nil)
  -- the loop
  have hE := EvalAll.call_funAll (f := b + 8) (Q := fun w cst => NclSiftInv I m I.n' w ∧
      cst ≤ I.n' * nclSiftCost h Y + 10 ^ 6 * Y ^ 3) dArg fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine (iter_spec hP.iter (c := c) (k := I.n') (acc0 := .list [encPerm (1 : Perm (Fin (I.n + I.n'))), .list []])
      (Inv := NclSiftInv I m) (M := 30 * Y ^ 2) (B := fun _ => nclSiftCost h Y)
      ⟨1, by rw [nclDeltaPts_zero]; rfl, Subgroup.one_mem _, fun _ hj => absurd hj (by omega)⟩
      (fun i acc _ hacc => by
        obtain ⟨x, rfl, -, -⟩ := hacc
        have := wt_list2_le (encPerm x) (encPts (nclDeltaPts (n' := I.n') I.n i))
        have := wt_encPerm_le x
        have := nclWt_encPts_le (nclDeltaPts (n' := I.n') I.n i)
          (le_trans (nclLength_deltaPts (n := I.n) (n' := I.n') (k := i)) (by omega))
        omega)
      (fun i acc hi hacc => by
        obtain ⟨x, rfl, hx, ha⟩ := hacc
        refine (preSift_spec hP I hm hi hx ha).mono fun w cst hw => ⟨hw.1, ?_⟩
        rw [← hYd] at hw; exact hw.2)).mono fun w cb hw => ⟨hw.1, ?_⟩
    have hcb := hw.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcb
    have wn := wt_nat_le I.n'
    have wl := nclWt_list_nil
    have w2 := wt_list2_le (encPerm (1 : Perm (Fin (I.n + I.n')))) (.list [])
    have w3 := wt_list3_le c (.nat I.n') (.list [encPerm (1 : Perm (Fin (I.n + I.n'))), .list []])
    have hw : w.wt ≤ 30 * Y ^ 2 := by
      obtain ⟨x, rfl, -, -⟩ := hw.1
      have := wt_list2_le (encPerm x) (encPts (nclDeltaPts (n' := I.n') I.n I.n'))
      have := wt_encPerm_le x
      have := nclWt_encPts_le (nclDeltaPts (n' := I.n') I.n I.n')
        (le_trans (nclLength_deltaPts (n := I.n) (n' := I.n') (k := I.n')) (by omega))
      omega
    have k1 : loopModK * (I.n' + 1) * ((Val.list [c, .nat I.n', .list [encPerm (1 : Perm (Fin (I.n + I.n'))), .list []]]).wt +
        I.n' + 30 * Y ^ 2 + 1) ≤ (1000 * Y) * (200 * Y ^ 2) :=
      Nat.mul_le_mul (by unfold loopModK; omega) (by omega)
    have e1 : (1000 * Y) * (200 * Y ^ 2) = 200000 * Y ^ 3 := by ring
    have wD : (Val.list [Val.nat (I.n + I.n'), .list ((1 :: nclPreDs I).map encPerm)]).wt < Y := by
      have : (encGroup (nclPreDs I)).wt < A.wt := wt_le_wt_list (by simp)
      exact lt_of_lt_of_le this (by omega)
    have wM : (Val.list [Val.nat I.n', .list ((1 :: I.ms).map encPerm)]).wt < Y := by
      have : (encGroup I.ms).wt < A.wt := wt_le_wt_list (by simp)
      exact lt_of_lt_of_le this (by omega)
    have wL1 : (Val.list ((1 :: nclPreDs I).map encPerm)).wt <
        (Val.list [Val.nat (I.n + I.n'), .list ((1 :: nclPreDs I).map encPerm)]).wt :=
      wt_le_wt_list (by simp)
    have wG1 : (encGroup (nclPreDs I)).wt =
        (Val.list [Val.nat (I.n + I.n'), .list ((1 :: nclPreDs I).map encPerm)]).wt := rfl
    have wG2 : (encGroup I.ms).wt = (Val.list [Val.nat I.n', .list ((1 :: I.ms).map encPerm)]).wt :=
      rfl
    have y23 : Y ^ 2 ≤ Y ^ 3 := q23
    omega
  refine FunAll.intro hP.lift (EvalAll.get hE (Det.nat 0) fun va ca vb cb hra hrb => ?_)
  obtain ⟨⟨x, rfl, hx, ha⟩, hca⟩ := hra
  obtain ⟨rfl, hcb⟩ := hrb
  refine ⟨[encPerm x, encPts (nclDeltaPts (n' := I.n') I.n I.n')], 0, rfl, rfl, by simp,
    ⟨x, rfl, hx, fun k => ha k k.2⟩, ?_⟩
  have := wt_encPerm_le x
  have h1 : I.n' * nclSiftCost h Y ≤ Y * nclSiftCost h Y := Nat.mul_le_mul_right _ (by omega)
  have p2'' : (I.n + I.n' + 1) ^ 2 ≤ Y ^ 3 := p2.trans q23
  show _ ≤ nclLiftCost h Y
  unfold nclLiftCost
  simp only [List.getElem_cons_zero]
  omega

end GI.Impl
