import Workspace.Impl.NClPreProg
import Workspace.Impl.NClEntry

/-!
# The sifting step of the preimage program

`preSift_spec`: one sifting step. On `[[a0, encPerm m], i, [encPerm x, pts]]`, where `a0` is the
instance, `x ∈ D'` agrees with `m` on the first `i` points of `Δ` and `pts` lists these points,
the step returns `[encPerm (x t), pts ++ [n + i]]`. Here `t` is the transversal element that maps
the point `n + i` to `x⁻¹ (n + m i)` in the Schreier transversal of the pointwise stabilizer of
`pts` (`nclSift_step`).
-/

namespace GI.Impl

open GI.Cited GI.Lang Equiv
open GI.Machine (BinOp)

theorem nclEncPerm_get {k : ℕ} (σ : Perm (Fin k)) (i : Fin k) :
    ((List.finRange k).map fun j => Val.nat (σ j))[(i : ℕ)]? = some (.nat (σ i)) := by
  simp

/-- The cost of one sifting step, for an instance of weight below `Y`. -/
noncomputable def nclSiftCost (h : PointwiseStab) (Y : ℕ) : ℕ :=
  10 ^ 17 * Y ^ 12 + (pointwiseStabPrim h).c * (21 * Y ^ 2) ^ (pointwiseStabPrim h).k

theorem nclDeg_lt_preimageEnc (I : PreimageInst) : I.n + I.n' + 1 ≤ (preimageEnc I).wt := by
  have h1 := ncl_deg_lt_wt (nclPreDs I)
  have h2 : (encGroup (nclPreDs I)).wt <
      (Val.list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms]).wt :=
    wt_le_wt_list (by simp)
  have e : (preimageEnc I).wt = (Val.list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms]).wt :=
    rfl
  omega

set_option maxHeartbeats 4000000 in
/-- **One sifting step.** -/
theorem preSift_spec {P : Program} {b j : ℕ} {h : PointwiseStab} (hP : PreAt P b j h)
    (I : PreimageInst) {m : Perm (Fin I.n')} (hm : m ∈ 1 :: I.ms) {i : ℕ} (hi : i < I.n')
    {x : Perm (Fin (I.n + I.n'))} (hx : x ∈ nclPreD I) (ha : NclAgreeBelow x m i) :
    FunAll P (b + 11) (.list [.list [preimageEnc I, encPerm m], .nat i,
        .list [encPerm x, encPts (nclDeltaPts (n' := I.n') I.n i)]])
      (fun w c => (∃ x', w = .list [encPerm x', encPts (nclDeltaPts (n' := I.n') I.n (i + 1))] ∧
        x' ∈ nclPreD I ∧ NclAgreeBelow x' m (i + 1)) ∧
        c ≤ nclSiftCost h ((preimageEnc I).wt + 1)) := by
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = (preimageEnc I).wt + 1 := ⟨_, rfl⟩
  rw [← hYd]
  have hNY : I.n + I.n' + 1 ≤ Y := by have := nclDeg_lt_preimageEnc I; omega
  set k : Fin I.n' := ⟨i, hi⟩ with hk
  set S := nclDeltaPts (n' := I.n') I.n i with hS
  set α : Fin (I.n + I.n') := nclInDelta k with hα
  set β : Fin (I.n + I.n') := x⁻¹ (nclInDelta (m k)) with hβ
  have hαv : (α : ℕ) = I.n + i := nclInDelta_val k
  have hβv : (nclInDelta (n := I.n) (m k) : ℕ) = I.n + (m k : ℕ) := nclInDelta_val (m k)
  have hmk := (m k).2
  -- powers of `Y`
  have y1 : 1 ≤ Y := by omega
  have p2 : (I.n + I.n' + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hNY 2
  have p2' : (I.n' + 1) ^ 2 ≤ Y ^ 2 := (Nat.pow_le_pow_left (by omega) 2).trans p2
  have p3 : (I.n + I.n' + 1) ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left hNY 3
  have p4 : (I.n + I.n' + 1) ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left hNY 4
  have p6 : (I.n + I.n' + 1) ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left hNY 6
  have q12 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right y1 (by omega)
  have q34 : Y ^ 3 ≤ Y ^ 4 := Nat.pow_le_pow_right y1 (by omega)
  have q46 : Y ^ 4 ≤ Y ^ 6 := Nat.pow_le_pow_right y1 (by omega)
  have q612 : Y ^ 6 ≤ Y ^ 12 := Nat.pow_le_pow_right y1 (by omega)
  -- the weight of the input
  set V : List Val := [.list [.list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms], encPerm m],
    .nat i, .list [encPerm x, .list (S.map fun p => Val.nat p.val)]] with hV
  have eIn : Val.list [.list [preimageEnc I, encPerm m], .nat i,
      .list [encPerm x, encPts S]] = Val.list V := by
    rw [hV, nclEncPts_val]; rfl
  rw [eIn]
  have wA : (Val.list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms]).wt + 1 = Y := by
    rw [hYd]; rfl
  have wSl : S.length ≤ I.n + I.n' :=
    le_trans (nclLength_deltaPts (n := I.n) (n' := I.n') (k := i)) (by omega)
  have wS : (Val.list (S.map fun p => Val.nat p.val)).wt ≤ 5 * (I.n + I.n' + 1) ^ 2 := by
    rw [← nclEncPts_val]; exact nclWt_encPts_le S wSl
  have wm := wt_encPerm_le m
  have wx := wt_encPerm_le x
  have wxi := wt_encPerm_le x⁻¹
  have wi := wt_nat_le i
  have hVW : (Val.list V).wt ≤ 100 * Y ^ 2 := by
    have h1 := wt_list3_le (.list [.list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms],
      encPerm m]) (.nat i) (.list [encPerm x, .list (S.map fun p => Val.nat p.val)])
    have h2 := wt_list2_le (.list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms]) (encPerm m)
    have h3 := wt_list2_le (encPerm x) (.list (S.map fun p => Val.nat p.val))
    have e : (Val.list V).wt = (Val.list [.list [.list [.nat I.n, encGroup (nclPreDs I),
      encGroup I.ms], encPerm m], .nat i,
      .list [encPerm x, .list (S.map fun p => Val.nat p.val)]]).wt := rfl
    omega
  -- the pieces of the input, in any environment that starts with it
  have dA0 : ∀ rest, Det P (.list V :: rest) (.get (arg 0) (.nat 0))
      (.list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms]) (300 * Y ^ 2) := fun rest =>
    (Det.get' (Det.arg' (vs := V) (rest := rest) (j := 0) rfl) (Det.nat 0)
      (show [Val.list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms], encPerm m][0]? =
        some (.list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms]) from rfl)).mono (by omega)
  have wn := wt_nat_le I.n
  have wN := wt_nat_le (I.n + I.n')
  have wDv : (encGroup (nclPreDs I)).wt < Y := by
    have : (encGroup (nclPreDs I)).wt <
        (Val.list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms]).wt := wt_le_wt_list (by simp)
    omega
  have dNn : ∀ rest, Det P (.list V :: rest) (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat I.n)
      (400 * Y ^ 2) := fun rest =>
    (Det.get' (dA0 rest) (Det.nat 0)
      (show [Val.nat I.n, encGroup (nclPreDs I), encGroup I.ms][0]? = some (.nat I.n) from rfl)).mono
      (by omega)
  have dDv : ∀ rest, Det P (.list V :: rest) (.get (.get (arg 0) (.nat 0)) (.nat 1))
      (encGroup (nclPreDs I)) (400 * Y ^ 2) := fun rest =>
    (Det.get' (dA0 rest) (Det.nat 1)
      (show [Val.nat I.n, encGroup (nclPreDs I), encGroup I.ms][1]? =
        some (encGroup (nclPreDs I)) from rfl)).mono (by omega)
  have dNN : ∀ rest, Det P (.list V :: rest) (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 0))
      (.nat (I.n + I.n')) (500 * Y ^ 2) := fun rest =>
    (Det.get' (dDv rest) (Det.nat 0)
      (show [Val.nat (I.n + I.n'), .list ((1 :: nclPreDs I).map encPerm)][0]? =
        some (.nat (I.n + I.n')) from rfl)).mono (by omega)
  have dM : ∀ rest, Det P (.list V :: rest) (.get (arg 0) (.nat 1)) (encPerm m) (300 * Y ^ 2) :=
    fun rest => (Det.get' (Det.arg' (vs := V) (rest := rest) (j := 0) rfl) (Det.nat 1)
      (show [Val.list [.nat I.n, encGroup (nclPreDs I), encGroup I.ms], encPerm m][1]? =
        some (encPerm m) from rfl)).mono (by omega)
  have dX : ∀ rest, Det P (.list V :: rest) (.get (arg 2) (.nat 0)) (encPerm x) (300 * Y ^ 2) :=
    fun rest => (Det.get' (Det.arg' (vs := V) (rest := rest) (j := 2) rfl) (Det.nat 0)
      (show [encPerm x, Val.list (S.map fun p => Val.nat p.val)][0]? = some (encPerm x) from rfl)).mono
      (by omega)
  have dS : ∀ rest, Det P (.list V :: rest) (.get (arg 2) (.nat 1))
      (.list (S.map fun p => Val.nat p.val)) (300 * Y ^ 2) :=
    fun rest => (Det.get' (Det.arg' (vs := V) (rest := rest) (j := 2) rfl) (Det.nat 1)
      (show [encPerm x, Val.list (S.map fun p => Val.nat p.val)][1]? =
        some (.list (S.map fun p => Val.nat p.val)) from rfl)).mono (by omega)
  have dI : ∀ rest, Det P (.list V :: rest) (arg 1) (.nat i) (300 * Y ^ 2) :=
    fun rest => (Det.arg' (vs := V) (rest := rest) (j := 1) rfl).mono (by omega)
  -- the step `n + i`
  have dNi : ∀ rest, Det P (.list V :: rest) (.arith .add (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (arg 1)) (.nat (I.n + i)) (800 * Y ^ 2) := fun rest =>
    (nclDet_arith_le (op := BinOp.add) (z := I.n + i) (dNn rest) (dI rest) rfl
      (nclWt_nat_mono (show I.n + i ≤ I.n + I.n' by omega))).mono (by omega)
  -- 1. the pointwise stabilizer of the points
  have da1 := Det.mk2 (dDv []) (dS [])
  rw [← nclEncPts_val] at da1
  have hG : GroupVal (I.n + I.n') (encGroup (nclPreDs I)) (nclPreD I) := ⟨nclPreDs I, rfl, rfl⟩
  refine FunAll.intro hP.sift (EvalAll.letE (pointwiseStab_call h hP.prim da1 hG) fun w1 c1 hw1 => ?_)
  obtain ⟨⟨hs, rfl, hhs, hgen⟩, hc1⟩ := hw1
  replace hhs : hs.length ≤ (I.n + I.n') ^ 2 := hhs
  have ww1 : (Val.list (hs.map encPerm)).wt ≤ 13 * (I.n + I.n' + 1) ^ 6 :=
    GensVal.wt_le ⟨hs, rfl, hhs, hgen⟩
  have hsY : hs.length ≤ Y ^ 2 := le_trans hhs (Nat.pow_le_pow_left (by omega) 2)
  -- 2. the Schreier transversal of the orbit of `α`
  have dAl : Det P [Val.list V, .list (hs.map encPerm)]
      (.arith .add (.get (.get (arg 0) (.nat 0)) (.nat 0)) (arg 1)) (.nat (α : ℕ)) (800 * Y ^ 2) := by
    rw [hαv]; exact dNi _
  have da2 := Det.snoc (Det.mk4 (Det.nat 0) (Det.var' (P := P)
      (env := [Val.list V, .list (hs.map encPerm)]) (i := 1) rfl) (Det.mk1 dAl) (dNN _)) (dNN _)
  have hE2 := EvalAll.call_funAll (f := b + 12) (Q := fun w c => ∃ L : List (Fin (I.n + I.n') ×
      Perm (Fin (I.n + I.n'))), w = encPairs ptKey L ∧ L.length ≤ I.n + I.n' ∧
      (∀ γ, γ ∈ L.map Prod.fst ↔ ∃ g ∈ genGroup hs, g α = γ) ∧
      (∀ p ∈ L, p.2 ∈ genGroup hs ∧ p.2 α = p.1) ∧ c ≤ 2 * 10 ^ 16 * Y ^ 12) da2 fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine (schreier_spec hP.sch hs α).mono fun w cb hw => ?_
    obtain ⟨L, rfl, hnd, hmem, hpr, -, hcb⟩ := hw
    have hL : L.length ≤ I.n + I.n' := by
      have := hnd.length_le_card; simpa using this
    refine ⟨L, rfl, hL, hmem, hpr, ?_⟩
    have wL := nclWt_encPairs_le L hL
    have e2 : (encPairs ptKey L).wt = (Val.list (L.map (encPair ptKey))).wt := rfl
    have w0 := wt_nat_le 0
    have wal : (Val.list [Val.nat (α : ℕ)]).wt ≤ 2 * (α : ℕ) + 9 := by
      have := wt_list1_le (Val.nat (α : ℕ)); have := wt_nat_le (α : ℕ); omega
    have w4 := wt_list4_le (.nat 0) (.list (hs.map encPerm)) (.list [Val.nat (α : ℕ)])
      (.nat (I.n + I.n'))
    have w5 : (Val.list [Val.nat 0, .list (hs.map encPerm), .list [Val.nat (α : ℕ)],
        .nat (I.n + I.n'), .nat (I.n + I.n')]).wt ≤ 100 * Y ^ 6 := by
      have := wt_list_le [Val.nat 0, .list (hs.map encPerm), .list [Val.nat (α : ℕ)],
        .nat (I.n + I.n'), .nat (I.n + I.n')]
      simp at this
      have := α.2
      omega
    have hS6 : (hs.length + 2 * (I.n + I.n') + 20) ^ 6 ≤ (23 * Y ^ 2) ^ 6 :=
      Nat.pow_le_pow_left (by omega) 6
    have hsch : schK * (hs.length + 2 * (I.n + I.n') + 20) ^ 6 ≤ 10 ^ 16 * Y ^ 12 :=
      calc _ ≤ schK * (23 * Y ^ 2) ^ 6 := Nat.mul_le_mul_left _ hS6
        _ = 11000000 * 23 ^ 6 * Y ^ 12 := by rw [show schK = 11000000 from rfl]; ring
        _ ≤ 10 ^ 16 * Y ^ 12 := Nat.mul_le_mul_right _ (by norm_num)
    have hal := α.2
    have e5 : (Val.list ([Val.nat 0, .list (hs.map encPerm), .list [Val.nat (α : ℕ)],
        .nat (I.n + I.n')] ++ [.nat (I.n + I.n')])).wt = (Val.list [Val.nat 0,
        .list (hs.map encPerm), .list [Val.nat (α : ℕ)], .nat (I.n + I.n'),
        .nat (I.n + I.n')]).wt := rfl
    omega
  refine EvalAll.letE hE2 fun w2 c2 hw2 => ?_
  obtain ⟨L, rfl, hL, hmem, hpr, hc2⟩ := hw2
  -- 3. the transversal element of `β = x⁻¹ (n + m i)`
  have hgen' : genGroup hs = pointwiseStab (nclPreD I) S := hgen
  have hβL : ∃ p ∈ L, p.1 = β := by
    obtain ⟨y, hy, hyα⟩ := nclSift_exists I (nclExists_lift I hm) hx (k := k) ha
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp ((hmem β).mpr ⟨y, hgen' ▸ hy, hyα⟩)
    exact ⟨p, hp, hpe⟩
  have dInv := Det.call (dX [.list (hs.map encPerm), encPairs ptKey L]) (inv_spec hP.inv x)
  have dMi := Det.get' (dM [.list (hs.map encPerm), encPairs ptKey L])
    (dI [.list (hs.map encPerm), encPairs ptKey L]) (nclEncPerm_get m k)
  have dIdx := nclDet_arith_le (op := BinOp.add) (z := (nclInDelta (n := I.n) (m k) : ℕ))
    (dNn [.list (hs.map encPerm), encPairs ptKey L]) dMi (by rw [hβv]; rfl)
    (nclWt_nat_mono (show (nclInDelta (n := I.n) (m k) : ℕ) ≤ I.n + I.n' by omega))
  have dB := Det.get' dInv dIdx (nclEncPerm_get x⁻¹ (nclInDelta (m k)))
  have da3 := Det.mk3 dB (Det.var' (P := P)
    (env := [Val.list V, .list (hs.map encPerm), encPairs ptKey L]) (i := 2) rfl) (Det.nat 0)
  have wL := nclWt_encPairs_le L hL
  have eL : (encPairs ptKey L).wt = (Val.list (L.map (encPair ptKey))).wt := rfl
  have hE3 := EvalAll.call_funAll (f := b + 35) (Q := fun w c => (∃ p ∈ L, p.1 = β ∧
      w = encPerm p.2) ∧ c ≤ 10 ^ 9 * Y ^ 6) da3 fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine (preSel_spec hP L β hβL hL).mono fun w cb hw => ⟨hw.1, ?_⟩
    obtain ⟨⟨p, -, -, rfl⟩, hcb⟩ := hw
    have wp := wt_encPerm_le p.2
    have wb := wt_nat_le (β : ℕ)
    have hb := β.2
    have w3 := wt_list3_le (.nat (β : ℕ)) (.list (L.map (encPair ptKey))) (.nat 0)
    have e3 : (Val.list [Val.nat (β : ℕ), encPairs ptKey L, .nat 0]).wt =
      (Val.list [Val.nat (β : ℕ), .list (L.map (encPair ptKey)), .nat 0]).wt := rfl
    have wmk := wt_nat_le (m k : ℕ)
    have wid := wt_nat_le (nclInDelta (n := I.n) (m k) : ℕ)
    have hid := (nclInDelta (n := I.n) (m k)).2
    have p44 : (I.n + I.n' + 1) ^ 4 ≤ Y ^ 6 := p4.trans q46
    have p34 : (I.n + I.n' + 1) ^ 3 ≤ Y ^ 6 := p3.trans (q34.trans q46)
    have p14 : (I.n + I.n' + 1) ^ 2 ≤ Y ^ 6 := p2.trans (q23.trans (q34.trans q46))
    have p11 : (I.n + 1) ^ 4 ≤ Y ^ 6 := (Nat.pow_le_pow_left (by omega) 4).trans p44
    have ewN : (Val.nat (m k : ℕ)).wt ≤ (I.n' + 1) := by omega
    have hinv : invK * (I.n + I.n' + 1) ^ 4 ≤ 100000 * Y ^ 6 := by
      rw [show invK = 100000 from rfl]; omega
    have eb1 : (Val.nat (β : ℕ)).wt = (Val.nat (x⁻¹ (nclInDelta (m k)) : ℕ)).wt := rfl
    have eb2 : (Val.list [Val.nat (β : ℕ), encPairs ptKey L, .nat 0]).wt =
      (Val.list [Val.nat (x⁻¹ (nclInDelta (m k)) : ℕ), encPairs ptKey L, .nat 0]).wt := rfl
    have hc := hca
    have w0 := wt_nat_le 0
    have t1 : (encPairs ptKey L).wt ≤ 100 * Y ^ 6 := by omega
    have t2 : (Val.list [Val.nat (β : ℕ), encPairs ptKey L, Val.nat 0]).wt ≤ 300 * Y ^ 6 := by omega
    have t3 : ca ≤ 200000 * Y ^ 6 := by omega
    have t4 : cb ≤ 10 ^ 6 * Y ^ 6 := by omega
    omega
  refine EvalAll.letE hE3 fun w3 c3 hw3 => ?_
  obtain ⟨⟨p, hp, hpβ, rfl⟩, hc3⟩ := hw3
  -- 4. the result
  have dC := Det.call (Det.mk2 (dX [.list (hs.map encPerm), encPairs ptKey L, encPerm p.2])
    (Det.var' (P := P) (env := [Val.list V, .list (hs.map encPerm), encPairs ptKey L,
      encPerm p.2]) (i := 3) rfl)) (compose_spec hP.comp x p.2)
  have dSn := Det.snoc (dS [.list (hs.map encPerm), encPairs ptKey L, encPerm p.2])
    (dNi [.list (hs.map encPerm), encPairs ptKey L, encPerm p.2])
  rw [← nclEncPts_deltaPts_succ hi] at dSn
  have dOut := Det.mk2 dC dSn
  have ⟨htm, htα⟩ := hpr p hp
  have ht : p.2 ∈ pointwiseStab (nclPreD I) (nclDeltaPts I.n k) := hgen' ▸ htm
  have hst := nclSift_step I hx (k := k) ha ht (by rw [htα, hpβ])
  refine dOut.post fun c hc => ⟨⟨x * p.2, rfl, hst⟩, ?_⟩
  -- the cost
  have wp := wt_encPerm_le p.2
  have wxp := wt_encPerm_le (x * p.2)
  have wS' := nclWt_encPts_le (nclDeltaPts (n' := I.n') I.n (i + 1)) (by
    have := nclLength_deltaPts (n := I.n) (n' := I.n') (k := i + 1); omega)
  have w2 := wt_list2_le (encPerm x) (encPerm p.2)
  have w2' := wt_list2_le (encPerm (x * p.2)) (encPts (nclDeltaPts (n' := I.n') I.n (i + 1)))
  have hb : (pointwiseStabPrim h).bound (.list [encGroup (nclPreDs I), encPts S]) ≤
      (pointwiseStabPrim h).c * (21 * Y ^ 2) ^ (pointwiseStabPrim h).k := by
    unfold Prim.bound
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have := (Val.list [encGroup (nclPreDs I), encPts S]).size_le_wt
    have := wt_list2_le (encGroup (nclPreDs I)) (encPts S)
    have := nclWt_encPts_le S wSl
    omega
  have hc1' := hc1
  have p26 : (I.n + I.n' + 1) ^ 2 ≤ Y ^ 6 := p2.trans (q23.trans (q34.trans q46))
  have p36 : (I.n + I.n' + 1) ^ 3 ≤ Y ^ 6 := p3.trans (q34.trans q46)
  have y212 : Y ^ 2 ≤ Y ^ 12 := q23.trans (q34.trans (q46.trans q612))
  have wSc : (Val.list ((S.map fun p => Val.nat p.val) ++ [Val.nat (I.n + i)])).wt =
      (encPts (nclDeltaPts (n' := I.n') I.n (i + 1))).wt := by
    rw [nclEncPts_deltaPts_succ hi]
  have wda1 : (Val.list [encGroup (nclPreDs I), encPts S]).wt ≤ 2 * Y + 10 * Y ^ 2 + 6 := by
    have := wt_list2_le (encGroup (nclPreDs I)) (encPts S)
    have := nclWt_encPts_le S wSl
    omega
  unfold permK at hc
  unfold nclSiftCost
  omega

end GI.Impl
