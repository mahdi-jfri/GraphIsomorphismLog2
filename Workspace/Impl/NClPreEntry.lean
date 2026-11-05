module

public import Workspace.Impl.NClPreLift
public import Workspace.Impl.Reduce

@[expose] public section

/-!
# The entry of the preimage program

`preEntry_spec`: on the instance `I`, the program returns at most `n²` generators of the
preimage. It computes the kernel `K = D'_(Δ)` with one pointwise stabilizer call, a lift of each
`m ∈ 1 :: ms` (`preLift_spec`), restricts `1`, the lifts and the generators of `K` to the first
`n` points, and compresses the list with one more pointwise stabilizer call at no points
(`pointwiseStab_nil`). The result is the preimage by `nclPreimage_gens`.
-/

namespace GI.Impl

open GI.Cited GI.Lang Equiv
open GI.Machine (BinOp)

theorem nclRestr_one {n n' : ℕ} : nclRestr (1 : Perm (Fin (n + n'))) = 1 := by
  have := nclRestr_sum (1 : Perm (Fin n)) (1 : Perm (Fin n'))
  rwa [nclSc_one, nclSumToFin_one] at this

/-- Taking the first `n` entries of an element of `D'` gives its restriction. -/
theorem nclTake_encPerm (I : PreimageInst) {y : Perm (Fin (I.n + I.n'))} (hy : y ∈ nclPreD I) :
    ((List.finRange (I.n + I.n')).map fun i => Val.nat (y i)).take I.n =
      (List.finRange I.n).map fun i => Val.nat (nclRestr y i) := by
  obtain ⟨g, h, -, rfl⟩ := nclMem_preD I hy
  rw [nclRestr_sum]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_finRange] at h2
    have e := nclSumToFin_sumCongr_castAdd g h ⟨i, h2⟩
    simp only [List.getElem_take, List.getElem_map, List.getElem_finRange]
    have e' := congrArg (fun p : Fin (I.n + I.n') => (p : ℕ)) e
    simp only [Fin.coe_castAdd] at e'
    simp only [Fin.cast_mk]
    rw [show (⟨i, by omega⟩ : Fin (I.n + I.n')) = Fin.castAdd I.n' ⟨i, h2⟩ from rfl, e']

/-- The lifts, read off from the output of the map. -/
theorem nclLifts_list (I : PreimageInst) {ms' : List (Perm (Fin I.n'))} {ws : List Val}
    (hF : List.Forall₂ (fun x w => ∃ m, x = encPerm m ∧ ∃ z, w = encPerm z ∧ z ∈ nclPreD I ∧
      NclLifts z m) (ms'.map encPerm) ws) :
    ∃ zs : List (Perm (Fin (I.n + I.n'))), ws = zs.map encPerm ∧ zs.length = ms'.length ∧
      (∀ z ∈ zs, z ∈ nclPreD I ∧ ∃ m ∈ ms', NclLifts z m) ∧ ∀ m ∈ ms', ∃ z ∈ zs, NclLifts z m := by
  induction ms' generalizing ws with
  | nil =>
    obtain rfl := List.forall₂_nil_left_iff.mp hF
    exact ⟨[], rfl, rfl, by simp, by simp⟩
  | cons m ms' ih =>
    rcases ws with _ | ⟨w, ws⟩
    · exact absurd hF (by simp)
    rw [List.map_cons] at hF
    obtain ⟨⟨m', em, z, rfl, hz, hl⟩, hF'⟩ := List.forall₂_cons.mp hF
    obtain rfl := encPerm_injective em
    obtain ⟨zs, rfl, hlen, hzs, hcov⟩ := ih hF'
    refine ⟨z :: zs, rfl, by simp [hlen], fun y hy => ?_, fun p hp => ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨hz, _, List.mem_cons_self .., hl⟩
      · obtain ⟨h1, q, hq, h2⟩ := hzs y hy
        exact ⟨h1, q, List.mem_cons_of_mem _ hq, h2⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨z, List.mem_cons_self .., hl⟩
      · obtain ⟨y, hy, h2⟩ := hcov p hp
        exact ⟨y, List.mem_cons_of_mem _ hy, h2⟩

/-- The restrictions, read off from the output of the map. -/
theorem nclRestr_list {N n : ℕ} {ys : List (Perm (Fin N))} {ws : List Val} {r : Perm (Fin N) → Perm (Fin n)}
    (hF : List.Forall₂ (fun x w => ∃ y, x = encPerm y ∧ w = encPerm (r y)) (ys.map encPerm) ws) :
    ws = (ys.map r).map encPerm := by
  induction ys generalizing ws with
  | nil => exact List.forall₂_nil_left_iff.mp hF
  | cons y ys ih =>
    rcases ws with _ | ⟨w, ws⟩
    · exact absurd hF (by simp)
    rw [List.map_cons] at hF
    obtain ⟨⟨y', ey, rfl⟩, hF'⟩ := List.forall₂_cons.mp hF
    obtain rfl := encPerm_injective ey
    rw [ih hF']; rfl

/-- The weight of a list of permutations. -/
theorem nclWt_perms_le {N Y K : ℕ} (L : List (Perm (Fin N))) (hN : N + 1 ≤ Y) (hL : L.length ≤ K) :
    (Val.list (L.map encPerm)).wt ≤ 8 * (K * Y ^ 2) + K + 4 := by
  have h1 := wt_list_le (L.map encPerm)
  have h2 : ((L.map encPerm).map Val.wt).sum ≤ L.length * (4 * Y ^ 2) := by
    have := List.sum_le_card_nsmul ((L.map encPerm).map Val.wt) (4 * Y ^ 2) (by
      intro x hx
      simp only [List.map_map, List.mem_map, Function.comp] at hx
      obtain ⟨p, -, rfl⟩ := hx
      exact (wt_encPerm_le p).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN 2)))
    simpa using this
  have h3 : L.length * (4 * Y ^ 2) ≤ K * (4 * Y ^ 2) := Nat.mul_le_mul_right _ hL
  have e : K * (4 * Y ^ 2) = 4 * (K * Y ^ 2) := by ring
  simp only [List.length_map] at h1
  omega

/-- The cost of the preimage program, for an instance of weight below `Y`. -/
noncomputable def nclPreCost (h : PointwiseStab) (Y : ℕ) : ℕ :=
  Y * nclLiftCost h Y + 2 * ((pointwiseStabPrim h).c * (200 * Y ^ 4) ^ (pointwiseStabPrim h).k) +
    10 ^ 12 * Y ^ 8

/-- `append` with its result fixed. -/
theorem nclAppend_det {P : Program} {b : ℕ} (h : P.HasAt b (appendFuns b)) (xs ys : List Val) :
    FunDet P b (.list [.list xs, .list ys]) (.list (xs ++ ys)) (loopModK * (ys.length + 1) *
      ((Val.list [.list xs, .list ys]).wt + ys.length + (Val.list (xs ++ ys)).wt + 1)) :=
  (append_spec h xs ys).mono fun w c hw => by obtain ⟨rfl, hc⟩ := hw; exact ⟨rfl, hc⟩

set_option maxHeartbeats 4000000 in
/-- **The entry of the preimage program.** -/
theorem preEntry_spec {P : Program} {b j : ℕ} {h : PointwiseStab} (hP : PreAt P b j h)
    (I : PreimageInst) :
    FunAll P b (preimageEnc I) (fun w c => GensVal I.n w (GI.CitedChecks.preimageSubgroup I) ∧
      c ≤ nclPreCost h ((preimageEnc I).wt + 1)) := by
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = (preimageEnc I).wt + 1 := ⟨_, rfl⟩
  rw [← hYd]
  have hNY : I.n + I.n' + 1 ≤ Y := by have := nclDeg_lt_preimageEnc I; omega
  have y1 : 1 ≤ Y := by omega
  have p2 : (I.n + I.n' + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hNY 2
  have q12 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right y1 (by omega)
  have q34 : Y ^ 3 ≤ Y ^ 4 := Nat.pow_le_pow_right y1 (by omega)
  have q46 : Y ^ 4 ≤ Y ^ 6 := Nat.pow_le_pow_right y1 (by omega)
  have q68 : Y ^ 6 ≤ Y ^ 8 := Nat.pow_le_pow_right y1 (by omega)
  have p6 : (I.n + I.n' + 1) ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left hNY 6
  set Dv := encGroup (nclPreDs I) with hDv
  set Mv := encGroup I.ms with hMv
  set A : Val := .list [.nat I.n, Dv, Mv] with hA
  have eA : preimageEnc I = A := rfl
  rw [eA]
  have wA : A.wt + 1 = Y := by rw [hYd, eA]
  have wDv : Dv.wt < A.wt := wt_le_wt_list (by simp [hA])
  have wMv : Mv.wt < A.wt := wt_le_wt_list (by simp [hA])
  have wn := wt_nat_le I.n
  have wN := wt_nat_le (I.n + I.n')
  have hnA : (Val.nat I.n).wt < A.wt := wt_le_wt_list (by simp [hA])
  set xs := (1 :: I.ms).map encPerm with hxs
  have wxs : (Val.list xs).wt < Mv.wt := wt_le_wt_list (by simp [hMv, encGroup, encPerms, hxs])
  have lxs : xs.length < (Val.list xs).wt := length_lt_wt_list xs
  have lx : xs.length = I.ms.length + 1 := by simp [hxs]
  set ds := (1 :: nclPreDs I).map encPerm with hds
  have wds : (Val.list ds).wt < Dv.wt := wt_le_wt_list (by simp [hDv, encGroup, encPerms, hds])
  -- pieces of the input
  have dN : ∀ rest, Det P (A :: rest) (arg 0) (.nat I.n) (2 * A.wt + 5) := fun rest =>
    (Det.arg' (vs := [.nat I.n, Dv, Mv]) (rest := rest) (j := 0) rfl).mono (by rw [hA])
  have dD : ∀ rest, Det P (A :: rest) (arg 1) Dv (2 * A.wt + 6) := fun rest =>
    (Det.arg' (vs := [.nat I.n, Dv, Mv]) (rest := rest) (j := 1) rfl).mono (by rw [hA])
  have dM : ∀ rest, Det P (A :: rest) (arg 2) Mv (2 * A.wt + 7) := fun rest =>
    (Det.arg' (vs := [.nat I.n, Dv, Mv]) (rest := rest) (j := 2) rfl).mono (by rw [hA])
  have dNN : ∀ rest, Det P (A :: rest) (.get (arg 1) (.nat 0)) (.nat (I.n + I.n'))
      (3 * A.wt + 20) := fun rest =>
    (Det.get' (dD rest) (Det.nat 0)
      (show [Val.nat (I.n + I.n'), .list ds][0]? = some (.nat (I.n + I.n')) from rfl)).mono
      (by omega)
  have dOne : ∀ rest, Det P (A :: rest) (.get (.get (arg 1) (.nat 1)) (.nat 0))
      (encPerm (1 : Perm (Fin (I.n + I.n')))) (5 * A.wt + 20) := fun rest =>
    (Det.get' (Det.get' (dD rest) (Det.nat 1)
      (show [Val.nat (I.n + I.n'), .list ds][1]? = some (.list ds) from rfl)) (Det.nat 0)
      (show ds[0]? = some (encPerm (1 : Perm (Fin (I.n + I.n')))) from rfl)).mono (by
        have : (encPerm (1 : Perm (Fin (I.n + I.n')))).wt < (Val.list ds).wt :=
          wt_le_wt_list (by simp [hds])
        omega)
  have dMs : ∀ rest, Det P (A :: rest) (.get (arg 2) (.nat 1)) (.list xs) (4 * A.wt + 20) :=
    fun rest => (Det.get' (dM rest) (Det.nat 1)
      (show [Val.nat I.n', .list xs][1]? = some (.list xs) from rfl)).mono (by omega)
  -- 1. the kernel
  have wP0 : (Val.list [.nat I.n, .nat (I.n + I.n')]).wt ≤ 4 * Y + 6 := by
    have := wt_list2_le (.nat I.n) (.nat (I.n + I.n')); omega
  have dP := Det.call (Det.mk2 (dN []) (dNN [])) (prePts_spec hP.pts I.n I.n')
  have wPts := nclWt_encPts_le (nclDeltaPts (n' := I.n') I.n I.n')
    (le_trans (nclLength_deltaPts (n := I.n) (n' := I.n') (k := I.n')) (by omega))
  have da1 := Det.mk2 (dD []) dP
  have hG : GroupVal (I.n + I.n') Dv (nclPreD I) := ⟨nclPreDs I, rfl, rfl⟩
  refine FunAll.intro hP.entry (EvalAll.letE (pointwiseStab_call h hP.prim da1 hG) fun w1 c1 hw1 => ?_)
  obtain ⟨⟨ks, rfl, hksl, hks⟩, hc1⟩ := hw1
  replace hksl : ks.length ≤ (I.n + I.n') ^ 2 := hksl
  have hksY : ks.length ≤ Y ^ 2 := le_trans hksl (Nat.pow_le_pow_left (by omega) 2)
  have ww1 : (Val.list (ks.map encPerm)).wt ≤ 13 * (I.n + I.n' + 1) ^ 6 :=
    GensVal.wt_le ⟨ks, rfl, hksl, hks⟩
  have hb1 : (pointwiseStabPrim h).bound (.list [Dv, encPts (nclDeltaPts (n' := I.n') I.n I.n')]) ≤
      (pointwiseStabPrim h).c * (200 * Y ^ 4) ^ (pointwiseStabPrim h).k := by
    unfold Prim.bound
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have := (Val.list [Dv, encPts (nclDeltaPts (n' := I.n') I.n I.n')]).size_le_wt
    have := wt_list2_le Dv (encPts (nclDeltaPts (n' := I.n') I.n I.n'))
    omega
  have hC1 : c1 ≤ (pointwiseStabPrim h).c * (200 * Y ^ 4) ^ (pointwiseStabPrim h).k +
      10 ^ 5 * Y ^ 6 := by
    have := wt_list2_le Dv (encPts (nclDeltaPts (n' := I.n') I.n I.n'))
    have k1 : loopModK * (I.n' + 1) * ((Val.list [.nat I.n, .nat (I.n + I.n')]).wt + I.n' +
        5 * (I.n + I.n' + 1) ^ 2 + 1) ≤ (1000 * Y) * (20 * Y ^ 2) :=
      Nat.mul_le_mul (by unfold loopModK; omega) (by omega)
    have e1 : (1000 * Y) * (20 * Y ^ 2) = 20000 * Y ^ 3 := by ring
    have := wt_list2_le (Val.nat I.n) (.nat (I.n + I.n'))
    omega
  -- 2. the lifts
  have da2 := Det.mk2 (Det.var' (P := P) (env := [A, .list (ks.map encPerm)]) (i := 0) rfl)
    (dMs [.list (ks.map encPerm)])
  have hE2 := EvalAll.call_funAll (f := b + 4) (Q := fun w c => ∃ zs : List (Perm (Fin (I.n + I.n'))),
      w = .list (zs.map encPerm) ∧ zs.length = (1 :: I.ms).length ∧
      (∀ z ∈ zs, z ∈ nclPreD I ∧ ∃ m ∈ 1 :: I.ms, NclLifts z m) ∧
      (∀ m ∈ 1 :: I.ms, ∃ z ∈ zs, NclLifts z m) ∧ c ≤ Y * nclLiftCost h Y + 10 ^ 6 * Y ^ 4)
      da2 fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine (map_spec hP.map1 (c := A) (xs := xs) (R := fun x w => ∃ m, x = encPerm m ∧
      ∃ z, w = encPerm z ∧ z ∈ nclPreD I ∧ NclLifts z m) (B := fun _ => nclLiftCost h Y)
      fun x hx => ?_).mono fun w cb hw => ?_
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      refine (preLift_spec hP I hm).mono fun w c hw => ⟨⟨m, rfl, hw.1⟩, ?_⟩
      have := hw.2; rwa [← hYd] at this
    · obtain ⟨ws, rfl, hF, hcb⟩ := hw
      obtain ⟨zs, rfl, hlen, hzs, hcov⟩ := nclLifts_list I hF
      refine ⟨zs, rfl, by simpa using hlen, hzs, hcov, ?_⟩
      have hs : (xs.map fun _ => nclLiftCost h Y).sum = xs.length * nclLiftCost h Y := by simp
      have hl : xs.length * nclLiftCost h Y ≤ Y * nclLiftCost h Y := Nat.mul_le_mul_right _ (by omega)
      have hzl : zs.length ≤ Y := by simp only [List.length_cons] at hlen; omega
      have wz := nclWt_perms_le zs (by omega : I.n + I.n' + 1 ≤ Y) hzl
      have wa := wt_list2_le A (.list xs)
      have k1 : mapK * (xs.length + 1) * ((Val.list [A, .list xs]).wt +
          (Val.list (zs.map encPerm)).wt + 1) ≤ (1000 * Y) * (20 * Y ^ 3) := by
        refine Nat.mul_le_mul (by unfold mapK; omega) ?_
        have : Y * Y ^ 2 = Y ^ 3 := by ring
        omega
      have e1 : (1000 * Y) * (20 * Y ^ 3) = 20000 * Y ^ 4 := by ring
      have hz2 : zs.length ≤ Y := hzl
      have wz' : (Val.list (zs.map encPerm)).wt ≤ 13 * Y ^ 3 := by
        have : Y * Y ^ 2 = Y ^ 3 := by ring
        have : zs.length * Y ^ 2 ≤ Y * Y ^ 2 := Nat.mul_le_mul_right _ hzl
        have := nclWt_perms_le zs (by omega : I.n + I.n' + 1 ≤ Y) (le_refl zs.length)
        omega
      rw [hs] at hcb
      have := wt_list2_le A (.list xs)
      have := wt_list2_le (Val.list (zs.map encPerm)) (.list [])
      omega
  refine EvalAll.letE hE2 fun w2 c2 hw2 => ?_
  obtain ⟨zs, rfl, hlen, hzs, hcov, hc2⟩ := hw2
  have hzl1 : zs.length + 1 ≤ Y := by simp only [List.length_cons] at hlen; omega
  have hzl : zs.length ≤ Y := by omega
  -- 3. the list `1 :: zs ++ ks`
  set e1 := encPerm (1 : Perm (Fin (I.n + I.n'))) with he1
  have dI1 := Det.mk1 (dOne [.list (ks.map encPerm), .list (zs.map encPerm)])
  have dIn := Det.call (Det.mk2 dI1 (Det.var' (P := P) (env := [A, .list (ks.map encPerm),
    .list (zs.map encPerm)]) (i := 2) rfl)) (nclAppend_det hP.app [e1] (zs.map encPerm))
  have dOut3 := Det.call (Det.mk2 dIn (Det.var' (P := P) (env := [A, .list (ks.map encPerm),
    .list (zs.map encPerm)]) (i := 1) rfl))
    (nclAppend_det hP.app ([e1] ++ zs.map encPerm) (ks.map encPerm))
  set ys : List (Perm (Fin (I.n + I.n'))) := (1 :: zs) ++ ks with hys
  have e3 : [e1] ++ zs.map encPerm ++ ks.map encPerm =
      ys.map encPerm := by simp [hys, he1]
  have hyl : ys.length ≤ 3 * Y ^ 2 := by
    have : ys.length = zs.length + 1 + ks.length := by simp [hys]; omega
    omega
  have wys : (Val.list (ys.map encPerm)).wt ≤ 30 * Y ^ 4 := by
    have := nclWt_perms_le ys (by omega : I.n + I.n' + 1 ≤ Y) hyl
    have : Y ^ 2 * Y ^ 2 = Y ^ 4 := by ring
    have : 3 * Y ^ 2 * Y ^ 2 = 3 * Y ^ 4 := by ring
    omega
  have we1 : e1.wt ≤ 4 * Y ^ 2 := (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ p2)
  have wzs := nclWt_perms_le zs (by omega : I.n + I.n' + 1 ≤ Y) hzl
  have w1zs : (Val.list ([e1] ++ zs.map encPerm)).wt ≤ 8 * ((Y + 1) * Y ^ 2) + (Y + 1) + 4 := by
    have := nclWt_perms_le (1 :: zs) (by omega : I.n + I.n' + 1 ≤ Y)
      (show (1 :: zs).length ≤ Y + 1 by simp; omega)
    simpa [he1] using this
  have eY3 : Y * Y ^ 2 = Y ^ 3 := by ring
  have eY3' : (Y + 1) * Y ^ 2 = Y ^ 3 + Y ^ 2 := by ring
  have wl1 := wt_list1_le e1
  have wl2 := wt_list2_le (.list [e1]) (.list (zs.map encPerm))
  have wl3 := wt_list2_le (.list ([e1] ++ zs.map encPerm)) (.list (ks.map encPerm))
  have hksY6 : (Val.list (ks.map encPerm)).wt ≤ 13 * Y ^ 6 := le_trans ww1 (by omega)
  have q36 : Y ^ 3 ≤ Y ^ 6 := q34.trans q46
  have t1 : (Val.list [e1]).wt ≤ 8 * Y ^ 2 + 5 := by omega
  have t2 : (Val.list (zs.map encPerm)).wt ≤ 8 * Y ^ 3 + Y + 4 := by omega
  have t3 : (Val.list [.list [e1], .list (zs.map encPerm)]).wt ≤ 16 * Y ^ 3 + 16 * Y ^ 2 + 2 * Y + 24 := by
    omega
  have t4 : (Val.list ([e1] ++ zs.map encPerm)).wt ≤ 8 * Y ^ 3 + 8 * Y ^ 2 + Y + 5 := by omega
  have k1 : loopModK * ((zs.map encPerm).length + 1) *
      ((Val.list [.list [e1], .list (zs.map encPerm)]).wt + (zs.map encPerm).length +
        (Val.list ([e1] ++ zs.map encPerm)).wt + 1) ≤ (1000 * Y) * (100 * Y ^ 3) :=
    Nat.mul_le_mul (by simp only [List.length_map]; unfold loopModK; omega) (by
      simp only [List.length_map]; omega)
  have k2 : loopModK * ((ks.map encPerm).length + 1) *
      ((Val.list [.list ([e1] ++ zs.map encPerm), .list (ks.map encPerm)]).wt +
        (ks.map encPerm).length + (Val.list ([e1] ++ zs.map encPerm ++ ks.map encPerm)).wt + 1) ≤
      (1000 * (2 * Y ^ 2)) * (100 * Y ^ 6) :=
    Nat.mul_le_mul (by simp only [List.length_map]; unfold loopModK; omega) (by
      simp only [List.length_map]
      have := wys; rw [← e3] at this
      omega)
  have e1' : (1000 * Y) * (100 * Y ^ 3) = 100000 * Y ^ 4 := by ring
  have e2' : (1000 * (2 * Y ^ 2)) * (100 * Y ^ 6) = 200000 * Y ^ 8 := by ring
  have wys' := wys; rw [← e3] at wys'
  have dOut3' := dOut3.mono (c' := 10 ^ 7 * Y ^ 8) (by omega)
  refine EvalAll.letE dOut3' fun w3 c3 hw3 => ?_
  obtain ⟨rfl, hc3⟩ := hw3
  rw [e3]
  -- 4. the restrictions to the first `n` points
  have hysD : ∀ y ∈ ys, y ∈ nclPreD I := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact Subgroup.one_mem _
      · exact (hzs y hy).1
    · have : y ∈ gens ks := Subgroup.subset_closure hy
      rw [hks] at this; exact this.1
  have hLT : linTakeCost (20 * Y ^ 2) ≤ 10 ^ 8 * Y ^ 6 := by
    unfold linTakeCost
    have h1 : (20 * Y ^ 2 + 1) ^ 3 ≤ (21 * Y ^ 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have e : (21 * Y ^ 2) ^ 3 = 9261 * Y ^ 6 := by ring
    omega
  have da4 := Det.mk2 (dN [.list (ks.map encPerm), .list (zs.map encPerm), .list (ys.map encPerm)])
    (Det.var' (P := P) (env := [A, .list (ks.map encPerm), .list (zs.map encPerm),
      .list (ys.map encPerm)]) (i := 3) rfl)
  have hE4 := EvalAll.call_funAll (f := b + 58) (Q := fun w c =>
      w = .list ((ys.map nclRestr).map encPerm) ∧ c ≤ 10 ^ 9 * Y ^ 8) da4 fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine (map_spec hP.map2 (c := .nat I.n) (xs := ys.map encPerm) (R := fun x w => ∃ y : Perm (Fin (I.n + I.n')),
      x = encPerm y ∧ w = encPerm (nclRestr y)) (B := fun _ => linTakeCost (20 * Y ^ 2))
      fun x hx => ?_).mono fun w cb hw => ?_
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      refine FunAll.mono (linTake_spec hP.take ((List.finRange (I.n + I.n')).map
        fun i => Val.nat (y i)) I.n (by simp)) fun w c hw => ⟨⟨y, rfl, ?_⟩, ?_⟩
      · rw [hw.1, nclTake_encPerm I (hysD y hy)]; rfl
      · refine hw.2.trans (linTakeCost_mono ?_)
        have := wt_list2_le (.nat I.n) (encPerm y)
        have := wt_encPerm_le y
        show (Val.list [.nat I.n, encPerm y]).wt ≤ _
        omega
    · obtain ⟨ws, rfl, hF, hcb⟩ := hw
      have ews := nclRestr_list hF
      subst ews
      refine ⟨rfl, ?_⟩
      have hs : ((ys.map encPerm).map fun _ => linTakeCost (20 * Y ^ 2)).sum =
          (ys.map encPerm).length * linTakeCost (20 * Y ^ 2) := by
        rw [List.map_const', List.sum_replicate, smul_eq_mul]
      rw [hs] at hcb
      have l1 : (ys.map encPerm).length * linTakeCost (20 * Y ^ 2) ≤ (3 * Y ^ 2) * (10 ^ 8 * Y ^ 6) :=
        Nat.mul_le_mul (by simpa using hyl) hLT
      have e1 : (3 * Y ^ 2) * (10 ^ 8 * Y ^ 6) = 3 * 10 ^ 8 * Y ^ 8 := by ring
      have wr := nclWt_perms_le (ys.map nclRestr) (by omega : I.n + 1 ≤ Y)
        (show (ys.map nclRestr).length ≤ 3 * Y ^ 2 by simpa using hyl)
      have e4 : 3 * Y ^ 2 * Y ^ 2 = 3 * Y ^ 4 := by ring
      have e4' : 8 * (3 * Y ^ 2 * Y ^ 2) = 24 * Y ^ 4 := by ring
      have w2 := wt_list2_le (.nat I.n) (.list (ys.map encPerm))
      have l2 : mapK * ((ys.map encPerm).length + 1) * ((Val.list [.nat I.n,
          .list (ys.map encPerm)]).wt + (Val.list ((ys.map nclRestr).map encPerm)).wt + 1) ≤
          (1000 * (4 * Y ^ 2)) * (200 * Y ^ 4) :=
        Nat.mul_le_mul (by simp only [List.length_map]; unfold mapK; omega) (by omega)
      have e2 : (1000 * (4 * Y ^ 2)) * (200 * Y ^ 4) = 800000 * Y ^ 6 := by ring
      have := wt_nat_le I.n
      omega
  refine EvalAll.letE hE4 fun w4 c4 hw4 => ?_
  obtain ⟨rfl, hc4⟩ := hw4
  -- 5. the compression
  set gs' := (zs ++ ks).map nclRestr with hgs'
  have e5 : (ys.map nclRestr).map encPerm = (1 :: gs').map encPerm := by
    simp [hys, hgs', nclRestr_one]
  rw [e5]
  have da5 := Det.mk2 (Det.mk2 (dN [.list (ks.map encPerm), .list (zs.map encPerm),
    .list (ys.map encPerm), .list ((1 :: gs').map encPerm)]) (Det.var' (P := P)
      (env := [A, .list (ks.map encPerm), .list (zs.map encPerm),
      .list (ys.map encPerm), .list ((1 :: gs').map encPerm)]) (i := 4) rfl)) Det.nil
  have da5' : Det P [A, .list (ks.map encPerm), .list (zs.map encPerm), .list (ys.map encPerm),
      .list ((1 :: gs').map encPerm)] (mk2 (mk2 (arg 0) (.var 4)) .nil)
      (.list [encGroup gs', encPts ([] : List (Fin I.n))]) _ := da5
  have hmM : ∀ m ∈ 1 :: I.ms, m ∈ nclPreM I := fun m hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure hm
  have hxs' : ∀ x ∈ 1 :: zs, x ∈ nclPreD I ∧ ∃ m ∈ nclPreM I, NclLifts x m := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, fun k => rfl⟩
    · obtain ⟨h1, m, hm, h2⟩ := hzs x hx
      exact ⟨h1, m, hmM m hm, h2⟩
  have hcov' : ∀ m ∈ I.ms, ∃ x ∈ 1 :: zs, NclLifts x m := fun m hm => by
    obtain ⟨z, hz, h2⟩ := hcov m (List.mem_cons_of_mem _ hm)
    exact ⟨z, List.mem_cons_of_mem _ hz, h2⟩
  have hpre := nclPreimage_gens I (1 :: zs) ks hxs' hcov' hks
  rw [show ((1 :: zs) ++ ks).map nclRestr = 1 :: gs' by simp [hgs', nclRestr_one],
    gens_one_cons] at hpre
  refine (pointwiseStab_call h hP.prim da5' ⟨gs', rfl, rfl⟩).mono fun w c hw => ⟨?_, ?_⟩
  · have := hw.1; rwa [pointwiseStab_nil, hpre] at this
  · have hc := hw.2
    have ww := GensVal.wt_le hw.1
    have hgl : gs'.length + 1 ≤ 3 * Y ^ 2 := by
      have : ys.length = zs.length + 1 + ks.length := by simp [hys]; omega
      simp [hgs']; omega
    have wr := nclWt_perms_le (1 :: gs') (by omega : I.n + 1 ≤ Y)
      (show (1 :: gs').length ≤ 3 * Y ^ 2 by simpa using hgl)
    have e4' : 8 * (3 * Y ^ 2 * Y ^ 2) = 24 * Y ^ 4 := by ring
    have wl := nclWt_list_nil
    have wg := wt_list2_le (.nat I.n) (.list ((1 :: gs').map encPerm))
    have eg : (encGroup gs').wt = (Val.list [.nat I.n, .list ((1 :: gs').map encPerm)]).wt := rfl
    have wa := wt_list2_le (encGroup gs') (encPts ([] : List (Fin I.n)))
    have ep : (encPts ([] : List (Fin I.n))).wt = (Val.list []).wt := rfl
    have hb5 : (pointwiseStabPrim h).bound (.list [encGroup gs', encPts ([] : List (Fin I.n))]) ≤
        (pointwiseStabPrim h).c * (200 * Y ^ 4) ^ (pointwiseStabPrim h).k := by
      unfold Prim.bound
      refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
      have := (Val.list [encGroup gs', encPts ([] : List (Fin I.n))]).size_le_wt
      omega
    have wa2 := wt_list2_le (Val.list [.nat I.n, .list ((1 :: gs').map encPerm)]) (.list [])
    have pn6 : (I.n + 1) ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have q48 : Y ^ 4 ≤ Y ^ 8 := q46.trans q68
    have q38 : Y ^ 3 ≤ Y ^ 8 := q34.trans q48
    unfold nclPreCost
    omega

end GI.Impl
