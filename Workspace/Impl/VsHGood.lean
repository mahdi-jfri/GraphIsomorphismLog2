import Workspace.Impl.VsHBas
import Workspace.Proved.VsHGoodMath
import Workspace.Proved.VsHDimMath

/-!
# The goodness test

With `q = p^(dim L)`, `Q = q - 1` and the flag `dv = (r ∣ Q)`, an element `ȳ` of the hard `Ȳ`
is good iff `Λ(y^r) ∈ L` and, when `dv`, `Λ(y^Q) = Λ(1)` (`vsH_good_iff`).

* `vsHGoodE`, `vsHGood_spec`: on `[[ctx, r, Q, dv], y]`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- `if` on a known number, with the cost as a sum. -/
theorem Det.vsHIte {P : Program} {env : List Val} {c t e : Expr} {x : ℕ} {v1 v0 : Val}
    {cc ct ce : ℕ} (hc : Det P env c (.nat x) cc) (ht : Det P env t v1 ct)
    (he : Det P env e v0 ce) :
    Det P env (.ite c t e) (if x = 0 then v0 else v1) (cc + ct + ce + v1.wt + v0.wt + 1) :=
  (Det.ite' hc ht he).mono (by
    have := max_le_add_of_nonneg (Nat.zero_le ct) (Nat.zero_le ce)
    have := max_le_add_of_nonneg (Nat.zero_le v1.wt) (Nat.zero_le v0.wt)
    omega)

/-- The value of the goodness test. -/
noncomputable def vsHGB (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow) (r Q : ℕ)
    (dv : Bool) (y : Perm (Fin I.n)) : Bool :=
  vsPInLB I ws' cs rows (y ^ r) && (!dv || decide (vsPLocL I ws' cs (y ^ Q) = vsPLocL I ws' cs 1))

/-- The context of the goodness test. -/
def vsHGc (C : Val) (r Q : ℕ) (dv : Bool) : Val := .list [C, .nat r, .nat Q, boolVal dv]

/-- The identity, read from the context `[[ctx, …], …]`. -/
def vsHOne : Expr := .get (.get (.get (.get (arg 0) (.nat 0)) (.nat 5)) (.nat 1)) (.nat 0)

/-- On `[[ctx, r, Q, dv], y]`: the goodness test. -/
def vsHGoodE (pow inl loc eq : ℕ) : Expr :=
  .letE (.call pow (mk4 (.nat 0) (arg 1) (.get (arg 0) (.nat 1))
      vsHOne))
  (.letE (.call pow (mk4 (.nat 0) (arg 1) (.get (arg 0) (.nat 2))
      vsHOne))
    (.ite (.call inl (mk2 (.get (arg 0) (.nat 0)) (.var 1)))
      (.ite (.get (arg 0) (.nat 3))
        (.call eq (mk2
          (.call loc (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (.get (arg 0) (.nat 0)) (.nat 1))
            (.var 2)))
          (.call loc (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (.get (arg 0) (.nat 0)) (.nat 1))
            vsHOne))))
        (.nat 1))
      (.nat 0)))

/-- The cost of the goodness test. -/
def vsHGoodCost (Cφ N W : ℕ) : ℕ :=
  vsPInLPCost Cφ N W + 2 * vsPLocCost Cφ N + 10 ^ 9 * (N + 1) ^ 9 + 10 ^ 4 * W

set_option maxHeartbeats 8000000 in
theorem vsHGood_spec {P : Program} {f pow inl loc eq phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsHGoodE pow inl loc eq)) (hpow : P.HasAt pow (vsPPowFuns pow))
    (hinl : P.HasAt inl (vsPInLPFuns inl phi))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (heq : P.HasAt eq (vsPEqFuns eq))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {r Q : ℕ} (hr : r ≤ N) (hQ : GI.Machine.len Q ≤ (N + 1) ^ 2)
    (dv : Bool) {y : Perm (Fin I.n)} (hy : y ∈ gens I.gs) :
    FunDet P f (.list [vsHGc (vsPCtx I ws' cs rows hs) r Q dv, encPerm y])
      (boolVal (vsHGB I ws' cs rows r Q dv y)) (vsHGoodCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set cv := [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n] with hcv
  set c2 := [Val.list cv, .nat r, .nat Q, boolVal dv]
  set vs := [Val.list c2, encPerm y]
  have e0 : vsHGc C r Q dv = .list c2 := rfl
  rw [e0]
  have hn := H.n
  -- reading the context
  have rd : ∀ (rest : List Val), (Det P (Val.list vs :: rest) (arg 0) (.list c2)
        (2 * (Val.list vs).wt + 0 + 5)) ∧
      Det P (Val.list vs :: rest) (arg 1) (encPerm y) (2 * (Val.list vs).wt + 1 + 5) :=
    fun rest => ⟨Det.arg' (P := P) (vs := vs) (rest := rest) (j := 0) rfl,
      Det.arg' (P := P) (vs := vs) (rest := rest) (j := 1) rfl⟩
  have rC : ∀ (rest : List Val), ∃ k, Det P (Val.list vs :: rest) (.get (arg 0) (.nat 0)) (.list cv) k ∧
      k ≤ 4 * (Val.list vs).wt + 50 :=
    fun rest => ⟨_, Det.get' (rd rest).1 (Det.nat 0) rfl, by
      have := wt_le_wt_list (show Val.list cv ∈ c2 by simp [c2])
      have := wt_le_wt_list (show Val.list c2 ∈ vs by simp [vs])
      have := wt_nat_le 0
      omega⟩
  have rOne : ∀ (rest : List Val), ∃ k, Det P (Val.list vs :: rest) vsHOne (encPerm (1 : Perm (Fin I.n))) k ∧
      k ≤ 20 * (Val.list vs).wt + 200 := by
    intro rest
    obtain ⟨k, dC, hk⟩ := rC rest
    have d5 := Det.get' dC (Det.nat 5) (show cv[5]? = some (encGroup hs) from rfl)
    have d51 := Det.get' d5 (Det.nat 1)
      (show [Val.nat I.n, Val.list ((1 :: hs).map encPerm)][1]? = some (.list ((1 :: hs).map encPerm)) from rfl)
    have d510 := Det.get' d51 (Det.nat 0)
      (show ((1 :: hs).map encPerm)[0]? = some (encPerm 1) from rfl)
    refine ⟨_, d510, ?_⟩
    have h1 := wt_le_wt_list (show encGroup hs ∈ cv by simp [hcv])
    have h2 := wt_le_wt_list (show Val.list cv ∈ c2 by simp [c2])
    have h3 := wt_le_wt_list (show Val.list c2 ∈ vs by simp [vs])
    have h4 := wt_le_wt_list (show Val.list ((1 :: hs).map encPerm) ∈
      [Val.nat I.n, Val.list ((1 :: hs).map encPerm)] by simp)
    have h5 := wt_le_wt_list (show encPerm (1 : Perm (Fin I.n)) ∈ (1 :: hs).map encPerm by simp)
    have e5 : (encGroup hs).wt = (Val.list [Val.nat I.n, Val.list ((1 :: hs).map encPerm)]).wt := rfl
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 5
    omega
  -- `y^r`
  obtain ⟨k1, o1, hk1⟩ := rOne []
  have gr := Det.get' (rd []).1 (Det.nat 1) (show c2[1]? = some (.nat r) from rfl)
  have dP1 := Det.call (Det.mk4 (Det.nat 0) (rd []).2 gr o1) (vsPPow_spec hpow y 1 r)
  rw [mul_one] at dP1
  -- `y^Q`
  obtain ⟨k2, o2, hk2⟩ := rOne [encPerm (y ^ r)]
  have gQ := Det.get' (rd [encPerm (y ^ r)]).1 (Det.nat 2) (show c2[2]? = some (.nat Q) from rfl)
  have dP2 := Det.call (Det.mk4 (Det.nat 0) (rd [encPerm (y ^ r)]).2 gQ o2) (vsPPow_spec hpow y 1 Q)
  rw [mul_one] at dP2
  -- the tests
  set E2 := [Val.list vs, encPerm (y ^ r), encPerm (y ^ Q)]
  obtain ⟨k3, dC3, hk3⟩ := rC [encPerm (y ^ r), encPerm (y ^ Q)]
  have v1 := Det.var' (P := P) (env := E2) (i := 1) rfl
  have v2 := Det.var' (P := P) (env := E2) (i := 2) rfl
  have dI := Det.call (Det.mk2 dC3 v1) (vsPInLP_spec hinl hphi H (pow_mem hy r))
  have d3 := Det.get' (rd [encPerm (y ^ r), encPerm (y ^ Q)]).1 (Det.nat 3)
    (show c2[3]? = some (boolVal dv) from rfl)
  have dΓ := Det.get' dC3 (Det.nat 0) (show cv[0]? = some (vsQGam I) from rfl)
  have dF := Det.get' dC3 (Det.nat 1) (show cv[1]? = some (vsWFrVal I.p I.d ws' cs) from rfl)
  obtain ⟨k4, o4, hk4⟩ := rOne [encPerm (y ^ r), encPerm (y ^ Q)]
  have dL1 := Det.call (Det.mk3 dΓ dF v2) (vsPLoc_spec hloc hwl hphi H.sz H.gam H.n H.fr (pow_mem hy Q))
  have dL2 := Det.call (Det.mk3 dΓ dF o4) (vsPLoc_spec hloc hwl hphi H.sz H.gam H.n H.fr (one_mem _))
  have hDN : cs.length ≤ N := le_trans (Nat.le_mul_self _) H.dd
  have dE := Det.call (Det.mk2 dL1 dL2) (vsPEq_spec heq H.sz.pN H.dd (vsPLocL_sq (y ^ Q))
    (vsPLocL_sq 1))
  have dIn := Det.vsHIte d3 dE (Det.nat 1)
  have dOut := Det.vsHIte dI dIn (Det.nat 0)
  refine FunDet.intro hf ((Det.letE dP1 (Det.letE dP2 dOut)).post fun c hc => ⟨?_, ?_⟩)
  · unfold vsHGB
    cases vsPInLB I ws' cs rows (y ^ r) <;> cases dv <;>
      cases decide (vsPLocL I ws' cs (y ^ Q) = vsPLocL I ws' cs 1) <;> rfl
  · have wC : (Val.list cv).wt ≤ W := H.cw
    have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hn3 : (I.n + 1) ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have q39 : (N + 1) ^ 3 ≤ (N + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have q79 : (N + 1) ^ 7 ≤ (N + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have q59 : (N + 1) ^ 5 ≤ (N + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have wQ : (Val.nat Q).wt ≤ (N + 1) ^ 2 + 2 := by rw [wt_nat']; omega
    have wr := wt_nat_le r
    have w0 := wt_nat_le 0
    have wy := wt_encPerm_le y
    have w1 := wt_encPerm_le (1 : Perm (Fin I.n))
    have wyr := wt_encPerm_le (y ^ r)
    have wyQ := wt_encPerm_le (y ^ Q)
    have wdv := wt_boolVal_le dv
    have wc2 := wt_list_le c2
    simp only [c2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at wc2
    have ec2 : (Val.list c2).wt = (Val.list [Val.list cv, .nat r, .nat Q, boolVal dv]).wt := rfl
    have q49 : (N + 1) ^ 4 ≤ (N + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have wvs := wt_list2_le (Val.list c2) (encPerm y)
    have evs : (Val.list vs).wt = (Val.list [Val.list c2, encPerm y]).wt := rfl
    have p1 := vsPPowCost_le (n := I.n) (e := r) (k := N) (by have := vsP_bits_le r; omega)
    have hQb : Q.bits.length ≤ (N + 1) ^ 2 := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.2 (GI.Machine.len_le_iff.1 hQ)
    have p2 := vsPPowCost_le (n := I.n) (e := Q) (k := (N + 1) ^ 2) hQb
    have p1' : 10 ^ 6 * (N + 1) ^ 2 * (I.n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 5 := by
      calc 10 ^ 6 * (N + 1) ^ 2 * (I.n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 2 * (N + 1) ^ 3 :=
            Nat.mul_le_mul_left _ hn3
        _ = 10 ^ 6 * (N + 1) ^ 5 := by ring
    have p2' : 10 ^ 6 * ((N + 1) ^ 2 + 1) ^ 2 * (I.n + 1) ^ 3 ≤ 4 * 10 ^ 6 * (N + 1) ^ 7 := by
      have : ((N + 1) ^ 2 + 1) ^ 2 ≤ 4 * (N + 1) ^ 4 := by nlinarith
      calc 10 ^ 6 * ((N + 1) ^ 2 + 1) ^ 2 * (I.n + 1) ^ 3 ≤ 10 ^ 6 * (4 * (N + 1) ^ 4) * (N + 1) ^ 3 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ this) hn3
        _ = 4 * 10 ^ 6 * (N + 1) ^ 7 := by ring
    have l1 := wt_list4_le (.nat 0) (encPerm y) (.nat r) (encPerm (1 : Perm (Fin I.n)))
    have l2 := wt_list4_le (.nat 0) (encPerm y) (.nat Q) (encPerm (1 : Perm (Fin I.n)))
    have l3 := wt_list2_le (Val.list cv) (encPerm (y ^ r))
    have hmΓ := wt_le_wt_list (show vsQGam I ∈ cv by simp [hcv])
    have hmF := wt_le_wt_list (show vsWFrVal I.p I.d ws' cs ∈ cv by simp [hcv])
    have l4 := wt_list3_le (vsQGam I) (vsWFrVal I.p I.d ws' cs) (encPerm (y ^ Q))
    have l5 := wt_list3_le (vsQGam I) (vsWFrVal I.p I.d ws' cs) (encPerm (1 : Perm (Fin I.n)))
    have hsq1 := vsPLocL_sq (I := I) (ws' := ws') (cs := cs) (y ^ Q)
    have hsq2 := vsPLocL_sq (I := I) (ws' := ws') (cs := cs) 1
    have wz1 := wt_vsWVs_le (N := N) (VsWFit.bnd hsq1.1 H.sz.pN hDN) (by rw [hsq1.2]; omega)
    have wz2 := wt_vsWVs_le (N := N) (VsWFit.bnd hsq2.1 H.sz.pN hDN) (by rw [hsq2.2]; omega)
    have l6 := wt_list2_le (vsWVs (vsPLocL I ws' cs (y ^ Q))) (vsWVs (vsPLocL I ws' cs 1))
    have wb1 := wt_boolVal_le (vsPInLB I ws' cs rows (y ^ r))
    have wb2 := wt_boolVal_le (decide (vsPLocL I ws' cs (y ^ Q) = vsPLocL I ws' cs 1))
    have wn1 := wt_nat_le 1
    have wb3 : (if (vsPInLB I ws' cs rows (y ^ r)).toNat = 0 then Val.nat 0 else
        (if dv.toNat = 0 then Val.nat 1 else
          boolVal (decide (vsPLocL I ws' cs (y ^ Q) = vsPLocL I ws' cs 1)))).wt ≤ 3 := by
      split
      · exact w0.trans (by norm_num)
      · split
        · exact wn1.trans (by norm_num)
        · exact wb2
    have wb4 : (if dv.toNat = 0 then Val.nat 1 else
          boolVal (decide (vsPLocL I ws' cs (y ^ Q) = vsPLocL I ws' cs 1))).wt ≤ 3 := by
      split
      · exact wn1.trans (by norm_num)
      · exact wb2
    simp only [vsHGoodCost, vsPLocCost] at *

    omega

/-! ### What the goodness test means -/

section Meaning

variable {s : VsQSt I} [Fact I.p.Prime]

/-- **What the goodness test means.** -/
theorem vsHGB_iff (hs : VsQStOK s) {as : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs)
    {Lb : List (List (List ℕ))} (hLb : ∀ M ∈ Lb, VsFSq I.p (vsQD s) M)
    (hspan : vsFMatSpan I.p (vsQD s) Lb = Subalgebra.toSubmodule
      (vsFAlgOf I.p (vsQD s) (as.map (vsPLocL I s.ws' (vsQCs s)))))
    [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    (hA : ∀ a ∈ vsPBar hs (gens as), ∀ b ∈ vsPBar hs (gens as), a * b = b * a)
    (hdom : vsTDom (vsTAlg (vsPBar hs (gens as)))) {r : ℕ} (hr : r.Prime)
    {y : Perm (Fin I.n)} (hy : y ∈ gens s.hs) :
    vsHGB I s.ws' (vsQCs s) (vsPRows I.p Lb) r (I.p ^ (vsPRows I.p Lb).length - 1)
        (decide (r ∣ I.p ^ (vsPRows I.p Lb).length - 1)) y = true ↔
      vsMGood (vsPBar hs (gens as)) r (vsPRho hs y) := by
  rw [vsH_good_iff hA hdom hr, vsH_finrank_L hs has hLb hspan]
  set Q := I.p ^ (vsPRows I.p Lb).length - 1
  have h1 : vsPInLB I s.ws' (vsQCs s) (vsPRows I.p Lb) (y ^ r) = true ↔
      vsPRho hs y ^ r ∈ vsMScal (vsPBar hs (gens as)) := by
    rw [← vsPRho_pow hs hy, vsPRho_of hs (pow_mem hy r)]
    exact vsPInLB_iff hs has hLb hspan (pow_mem hy r)
  have h2 : vsPLocL I s.ws' (vsQCs s) (y ^ Q) = vsPLocL I s.ws' (vsQCs s) 1 ↔
      vsPRho hs y ^ Q = 1 := by
    rw [vsPLocL_eq_iff hs, ← vsQRho_ext hs (pow_mem hy Q) (one_mem _), ← vsPRho_of hs,
      ← vsPRho_of hs, vsPRho_pow hs hy, vsPRho_one]
  unfold vsHGB
  rw [Bool.and_eq_true, h1, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_iff,
    decide_eq_false_iff_not, h2]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨ha, fun hd => hb.resolve_left (not_not.2 hd)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha, by by_cases hd : r ∣ Q <;> simp_all⟩

end Meaning

end GI.Impl
