import Workspace.Impl.VsBFld0C

/-!
# The case `T = 0`

On `[lc, prep, Lb]`: look for a generator `g` (in `1 :: hs`) with `f(g) ≠ 0`. If there is one,
run `vsB0bE`. Otherwise `f` vanishes on `H`, and the answer is `(1, hs)` when `t = 0` and none
otherwise.

* `vsB0E`, `vsB0_spec`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The list `(1 :: hs)` of encoded generators, from the local context. -/
def vsBHsE : Expr := .get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 1)

/-- The case `T = 0`, on `[lc, prep, Lb]`. -/
def vsB0E (fd c0b eqN : ℕ) : Expr :=
  .letE (.call fd (mk2 (.get (arg 1) (.nat 1)) vsBHsE))
  (.ite (.arith .sub (.length vsBHsE) (.var 1))
    (.call c0b (mk4 (arg 0) (arg 1) (arg 2) (.get vsBHsE (.var 1))))
    (.ite (.call eqN (mk2 (.get (arg 1) (.nat 4)) (.get (.get (arg 1) (.nat 0)) (.nat 3))))
      (mk2 (.nat 0) (mk3 (.nat 1) vsBOneE (.get (.get (arg 0) (.nat 0)) (.nat 1))))
      (mk2 (.nat 0) (mk1 (.nat 0)))))

/-- The layout of the case `T = 0`. -/
structure VsB0At (P : Program) (hm : Membership) (f fd tst c0b m lin eqN tau rng dA red appd bA bB sc sv mI fI
    mF fF sv2 rp mm fl ch sotA cmp phi jp jm : ℕ) : Prop where
  hf0 : P.funs[f]? = some (vsB0E fd c0b eqN)
  hfd : P.HasAt fd (findFuns fd tst)
  htst : P.funs[tst]? = some (vsBTestE (bB + 3) (bB + 4) eqN)
  hb : VsB0bAt P hm c0b m lin eqN tau rng dA red appd bA bB sc sv mI fI mF fF sv2 rp mm fl ch sotA cmp phi jp jm

/-- The cost bound of the case `T = 0`, apart from the input weight. -/
noncomputable def vsB0TCost (hm : Membership) (n S Cφ : ℕ) : ℕ :=
  vsB0Cost hm n S Cφ + 2 * S ^ 2 * (Cφ + 10 ^ 18 * S ^ 6)

open Classical in
/-- The search predicate: an encoded element of `H` with `f ≠ 0`. -/
noncomputable def vsB0Q (s : VsQSt I) (x : Val) : Bool :=
  decide (∃ g ∈ gens s.hs, x = encPerm g ∧ vsBAlpha s g 0 ≠ 0)

theorem vsB0Q_enc {s : VsQSt I} {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    vsB0Q s (encPerm g) = decide (vsBAlpha s g 0 ≠ 0) := by
  unfold vsB0Q
  rw [decide_eq_decide]
  refine ⟨fun ⟨g', _, he, hne⟩ => ?_, fun h => ⟨g, hg, rfl, h⟩⟩
  rw [encPerm_injective he]; exact hne

set_option maxHeartbeats 16000000 in
/-- **The case `T = 0`.** -/
theorem vsB0_spec (hm : Membership) {P : Program}
    {f fd tst c0b m lin eqN tau rng dA red appd bA bB sc sv mI fI mF fF sv2 rp mm fl ch sotA cmp phi jp jm
      Cφ S Tm : ℕ}
    (H : VsB0At P hm f fd tst c0b m lin eqN tau rng dA red appd bA bB sc sv mI fI mF fF sv2 rp mm fl ch sotA cmp
      phi jp jm)
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) (hab : s.Ab) (hD : 1 ≤ vsQD s)
    (hdom : VsBDom s) (hspan : ∀ v, ∃ X ∈ vsBLamA s, X *ᵥ vsBe0 s hD = v)
    {Lb : List (List (List ℕ))}
    (hLb : ∀ X, X ∈ Submodule.span (ZMod I.p) {X | ∃ M ∈ Lb, vsWM I.p (vsQD s) M = X} ↔ X ∈ vsBLamA s)
    (hsq : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M) (hLbl : Lb.length ≤ vsQD s * vsQD s)
    {gsA : List (Perm (Fin I.n))} {LsA : List (List ((Fin (vsQD s) → ZMod I.p) × Perm (Fin I.n)))}
    (hgA : (genGroup gsA : Set (Perm (Fin I.n))) = vsBH1 hs) (hglA : gsA.length ≤ I.n ^ 2 + 2)
    (hlA : LsA.length = (vsBPs I.n).length)
    (hOA : ∀ i (hi : i < LsA.length), VsBOrbL (vsBAp s ((vsBPs I.n).getD i 0))
      (vsBKs (vsBAp s) (vsBe0 s hD) (gens s.hs : Set (Perm (Fin I.n))) ((vsBPs I.n).take i))
      (vsBe0 s hD) LsA[i])
    (hWA : ∀ L ∈ LsA, VsBPW (vsBS2 S) vsQVec L) (chB : Val)
    (hT : ∀ k ∈ vsBH1 hs, vsBAlpha s k 0 = 0) {Wp : ℕ}
    (hWp : (Val.list [vsQLCV s, .list [vsBCtxA s hD, vsBCtxB s,
      .list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))], chB,
      natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))], vsFMatsVal Lb]).wt ≤ Wp) :
    FunAll P f (.list [vsQLCV s, .list [vsBCtxA s hD, vsBCtxB s,
      .list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))], chB,
      natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))], vsFMatsVal Lb])
      (fun w c => ∃ a, w = vsQLeafV a ∧ VsQAnsOK hs.prob a ∧ c ≤ vsB0TCost hm I.n S Cφ + 3 * 10 ^ 4 * S ^ 2 * Wp) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  have hnS := hS.n
  have hpS := hS.p
  set lc := vsQLCV s
  set cA := vsBCtxA s hD
  set cB := vsBCtxB s
  set chA := Val.list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))]
  set t := vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)
  set tV := natList (vsQVec t)
  set pv := Val.list [cA, cB, chA, chB, tV]
  set LbV := vsFMatsVal Lb
  set A := Val.list [lc, pv, LbV]
  set xs := (1 :: s.hs).map encPerm
  have wA : A.wt ≤ Wp := hWp
  have rd : ∀ rest k v, [lc, pv, LbV][k]? = some v → Det P (A :: rest) (arg k) v (2 * A.wt + k + 5) :=
    fun rest k v hv => Det.arg' (vs := [lc, pv, LbV]) (rest := rest) hv
  have wpv : pv.wt < A.wt := wt_le_wt_list (by simp [A])
  have wlc : lc.wt < A.wt := wt_le_wt_list (by simp [A])
  have wLbA : LbV.wt < A.wt := wt_le_wt_list (by simp [A])
  have rp : ∀ rest k v, [cA, cB, chA, chB, tV][k]? = some v →
      Det P (A :: rest) (.get (arg 1) (.nat k)) v (3 * A.wt + 20) := fun rest k v hv => by
    refine (Det.get' (rd rest 1 pv rfl) (Det.nat k) hv).mono ?_
    have hk : k < 5 := by
      by_contra h; push Not at h
      rw [List.getElem?_eq_none (by simp; omega)] at hv; cases hv
    have : v.wt < pv.wt := wt_le_wt_list (List.mem_of_getElem? hv)
    omega
  have wcA : cA.wt < pv.wt := wt_le_wt_list (by simp [pv])
  have wcB : cB.wt < pv.wt := wt_le_wt_list (by simp [pv])
  have wtV : tV.wt < pv.wt := wt_le_wt_list (by simp [pv])
  have wst : (vsQStV I s).wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV])
  have wGs : (encGroup s.hs).wt < (vsQStV I s).wt := wt_le_wt_list (by simp [vsQStV])
  have wgl : (Val.list xs).wt < (encGroup s.hs).wt := wt_le_wt_list (by simp [xs, encGroup, encPerms])
  have ef1 : (Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]).wt =
    (vsQStV I s).wt := rfl
  have eg1 : (Val.list [Val.nat I.n, .list xs]).wt = (encGroup s.hs).wt := rfl
  have := wt_nat_le 0; have := wt_nat_le 1
  have rG : ∀ rest, Det P (A :: rest) (.get (.get (arg 0) (.nat 0)) (.nat 1)) (encGroup s.hs) (4 * A.wt + 40) :=
    fun rest => by
    have d0 := rd rest 0 lc rfl
    have dst := Det.get' d0 (Det.nat 0) (show [vsQStV I s, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat (vsQD s),
      vsFMatsVal (vsQMs s)][0]? = some (vsQStV I s) from rfl)
    have dG := Det.get' dst (Det.nat 1) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
      natList s.y][1]? = some (encGroup s.hs) from rfl)
    refine dG.mono ?_
    omega
  have rX : ∀ rest, Det P (A :: rest) vsBHsE (.list xs) (5 * A.wt + 60) := fun rest => by
    have dGl := Det.get' (rG rest) (Det.nat 1) (show [Val.nat I.n, .list xs][1]? = some (.list xs) from rfl)
    refine dGl.mono ?_
    omega
  have rOne : ∀ rest, Det P (A :: rest) vsBOneE (encPerm 1) (6 * A.wt + 60) := fun rest => by
    have d1 := Det.get' (rX rest) (Det.nat 0) (show xs[0]? = some (encPerm 1) from rfl)
    refine d1.mono ?_
    have w1 : (encPerm (1 : Perm (Fin I.n))).wt < (Val.list xs).wt := wt_le_wt_list (by simp [xs])
    omega
  -- the search
  have hxsl : xs.length ≤ S ^ 2 := by
    have := hs.hsl; have : I.n ^ 2 + 1 ≤ S ^ 2 := by
      have := Nat.pow_le_pow_left hnS 2
      have e : (I.n + 1) ^ 2 = I.n ^ 2 + 2 * I.n + 1 := by ring
      omega
    simp [xs]; omega
  have htst : ∀ x ∈ xs, FunDet P tst (.list [cB, x]) (boolVal (vsB0Q s x)) (Cφ + 10 ^ 17 * S ^ 6) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    have hgg : g ∈ gens s.hs := by
      rcases List.mem_cons.mp hg with rfl | hg
      · exact one_mem _
      · exact Subgroup.subset_closure hg
    rw [vsB0Q_enc hgg]
    exact vsB_test_spec H.htst H.hb.hbB H.hb.heqN hphi hS hs hgg
  have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hSS : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have hs2 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS1
  set i := xs.findIdx (vsB0Q s)
  have hil : i ≤ xs.length := List.findIdx_le_length
  refine FunAll.intro H.hf0 (EvalAll.letE (Ra := fun w c => w = .nat i ∧
      c ≤ S ^ 2 * (Cφ + 2 * 10 ^ 17 * S ^ 6) + 2 * 10 ^ 4 * S ^ 2 * Wp + 10 ^ 5 * S ^ 2)
    (EvalAll.call_funAll (Det.mk2 (rp [] 1 cB rfl) (rX [])) fun v ca hv => ?_) fun v1 c1 hv1 => ?_)
  · obtain ⟨rfl, hca⟩ := hv
    refine (find_spec H.hfd (c := cB) htst).mono fun w c hw => ⟨hw.1, ?_⟩
    obtain ⟨rfl, hc⟩ := hw
    rw [List.map_const', List.sum_replicate, smul_eq_mul] at hc
    have w2 := wt_list2_le cB (.list xs)
    have wi := wt_nat_le i
    have k1 : xs.length * (Cφ + 10 ^ 17 * S ^ 6) ≤ S ^ 2 * (Cφ + 10 ^ 17 * S ^ 6) := Nat.mul_le_mul_right _ hxsl
    have k2 : loopModK * (xs.length + 1) * ((Val.list [cB, .list xs]).wt + 2 * xs.length + 3) ≤
        1000 * (2 * S ^ 2) * (5 * Wp + 2 * S ^ 2 + 3) := by
      simp only [loopModK]
      apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
      omega
    have e1 : 1000 * (2 * S ^ 2) * (5 * Wp + 2 * S ^ 2 + 3) = 10000 * (S ^ 2 * Wp) + 4000 * (S ^ 2 * S ^ 2) +
      6000 * S ^ 2 := by ring
    have e2 : 2 * 10 ^ 4 * S ^ 2 * Wp = 2 * 10 ^ 4 * (S ^ 2 * Wp) := by ring
    have hW1 : Wp ≤ S ^ 2 * Wp := Nat.le_mul_of_pos_left _ hs2
    have hS4 : S ^ 2 * S ^ 2 ≤ S ^ 2 * S ^ 6 := Nat.mul_le_mul_left _ q26
    have e3 : S ^ 2 * (Cφ + 2 * 10 ^ 17 * S ^ 6) = S ^ 2 * Cφ + 2 * 10 ^ 17 * (S ^ 2 * S ^ 6) := by ring
    have e4 : S ^ 2 * (Cφ + 10 ^ 17 * S ^ 6) = S ^ 2 * Cφ + 10 ^ 17 * (S ^ 2 * S ^ 6) := by ring
    have : i ≤ S ^ 2 := by omega
    have ei : (Val.nat (List.findIdx (vsB0Q s) xs)).wt = (Val.nat i).wt := rfl
    clear_value lc cA cB chA t tV pv LbV A xs i
    omega
  obtain ⟨rfl, hc1⟩ := hv1
  set E1 := [A, Val.nat i]
  have hxsS : xs.length ≤ S ^ 2 := hxsl
  have dsub := Det.arith (op := .sub) (Det.length (rX [Val.nat i])) (Det.var' (P := P) (env := E1) (i := 1) rfl)
  simp only [GI.Machine.BinOp.eval] at dsub
  have wleaf : ∀ a : Option (Perm (Fin I.n) × List (Perm (Fin I.n))), (∀ r ∈ a, r.2.length ≤ I.n ^ 2) →
      (vsQLeafV a).wt ≤ 10 ^ 4 * S ^ 6 := fun a ha => vsQLeaf_wt hS ha
  refine EvalAll.ite dsub (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
  obtain ⟨hx1, hcc⟩ := hx
  have hx2 : x = xs.length - i := Val.nat.inj hx1
  have hcc' : cc ≤ 10 * Wp + 10 * S ^ 2 + 100 := by
    have := wt_nat_le i; have := wt_nat_le (xs.length - i)
    clear_value lc cA cB chA t tV pv LbV A xs i
    omega
  clear hcc hx1
  have hW1 : Wp ≤ S ^ 2 * Wp := Nat.le_mul_of_pos_left _ hs2
  have e5 : 3 * 10 ^ 4 * S ^ 2 * Wp = 3 * 10 ^ 4 * (S ^ 2 * Wp) := by ring
  have e6 : 2 * 10 ^ 4 * S ^ 2 * Wp = 2 * 10 ^ 4 * (S ^ 2 * Wp) := by ring
  have e7 : S ^ 2 * (Cφ + 2 * 10 ^ 17 * S ^ 6) ≤ 2 * S ^ 2 * (Cφ + 10 ^ 18 * S ^ 6) := by
    have : Cφ + 2 * 10 ^ 17 * S ^ 6 ≤ 2 * (Cφ + 10 ^ 18 * S ^ 6) := by omega
    calc S ^ 2 * (Cφ + 2 * 10 ^ 17 * S ^ 6) ≤ S ^ 2 * (2 * (Cφ + 10 ^ 18 * S ^ 6)) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have q612 : S ^ 6 ≤ S ^ 2 * S ^ 6 := Nat.le_mul_of_pos_left _ hs2
  have hs6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
  have wni := wt_nat_le i
  have q312 : S ^ 3 ≤ S ^ 12 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q612' : S ^ 6 ≤ S ^ 12 := Nat.pow_le_pow_right hS1 (by norm_num)
  have e8 : 2 * S ^ 2 * (Cφ + 10 ^ 18 * S ^ 6) = 2 * (S ^ 2 * Cφ) + 2 * 10 ^ 18 * (S ^ 2 * S ^ 6) := by ring
  have e9 : S ^ 2 * (Cφ + 2 * 10 ^ 17 * S ^ 6) = S ^ 2 * Cφ + 2 * 10 ^ 17 * (S ^ 2 * S ^ 6) := by ring
  by_cases hi : i < xs.length
  · have hx0 : x ≠ 0 := by omega
    rw [if_neg hx0]
    have hq : vsB0Q s xs[i] = true := List.findIdx_getElem (w := hi)
    obtain ⟨g, hg, hxg, hne⟩ : ∃ g ∈ gens s.hs, xs[i] = encPerm g ∧ vsBAlpha s g 0 ≠ 0 := by
      simpa only [vsB0Q, decide_eq_true_eq] using hq
    have dget := Det.get (rX [Val.nat i]) (Det.var' (P := P) (env := E1) (i := 1) rfl) hi
    rw [hxg] at dget
    have din := Det.mk4 (rd [Val.nat i] 0 lc rfl) (rd [Val.nat i] 1 pv rfl) (rd [Val.nat i] 2 LbV rfl) dget
    have wg := hS.wt_perm g
    have hWp' : (Val.list [lc, pv, LbV, encPerm g]).wt ≤ 2 * Wp + 10 * S ^ 2 + 20 := by
      have := wt_list_le [lc, pv, LbV, encPerm g]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at this
      have := wt_list_le [lc, pv, LbV]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at this
      have := sum_wt_lt_wt_list [lc, pv, LbV]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
      have eA : A.wt = (Val.list [lc, pv, LbV]).wt := rfl
      clear_value lc cA cB chA t tV pv LbV A xs i
      omega
    refine EvalAll.call_funAll din fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (vsB0b_spec hm H.hb hphi hS hs hab hD hdom hspan hLb hsq hLbl hgA hglA hlA hOA hWA chB hT hg hne
      hWp').mono ?_
    rintro w c ⟨a, rfl, ha, hc⟩
    refine ⟨a, rfl, ha, ?_⟩
    have wl := hS.wt_ans (a := a) (by
      rcases a with _ | ⟨h0, ks⟩
      · simp
      · intro r hr; simp at hr; rw [← hr]; exact ha.2.2)
    have wl2 := wt_list2_le (.nat 0) (vsQAnsV a)
    have el : (vsQLeafV a).wt = (Val.list [.nat 0, vsQAnsV a]).wt := rfl
    have w4 := wt_list4_le lc pv LbV (encPerm g)
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2
    unfold vsB0TCost
    clear_value lc cA cB chA t tV pv LbV A xs i
    have t1 : c1 ≤ S ^ 2 * Cφ + 2 * 10 ^ 17 * (S ^ 2 * S ^ 6) + 2 * 10 ^ 4 * (S ^ 2 * Wp) + 10 ^ 5 * S ^ 2 := by
      omega
    have t2 : (vsQLeafV a).wt ≤ 2000 * S ^ 6 := by omega
    have t3 : ca ≤ 100 * Wp + 100 * S ^ 2 := by omega
    have t4 : c ≤ vsB0Cost hm I.n S Cφ + 3000 * Wp + 10 ^ 5 * S ^ 2 := by omega
    omega
  · have hx0 : x = 0 := by omega
    rw [if_pos hx0]
    have hz : ∀ g ∈ s.hs, vsBAlpha s g 0 = 0 := by
      have hall := List.findIdx_eq_length.mp (show xs.findIdx (vsB0Q s) = xs.length by omega)
      intro g hg
      have hq := hall (encPerm g) (List.mem_map_of_mem (List.mem_cons_of_mem _ hg))
      rw [vsB0Q_enc (Subgroup.subset_closure hg)] at hq
      simpa using hq
    have dz := Det.get' (rp [Val.nat i] 0 cA rfl) (Det.nat 3) (show [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s),
      .nat I.p, natList (List.replicate (vsQD s) 0), .nat I.n, natList (vsQVec (vsBe0 s hD))][3]? =
      some (natList (List.replicate (vsQD s) 0)) from rfl)
    have deq := Det.call (Det.mk2 (rp [Val.nat i] 4 tV rfl) dz)
      (eqNats_spec H.hb.heqN (vsQVec t) (List.replicate (vsQD s) 0))
    have wz : (natList (List.replicate (vsQD s) 0)).wt ≤ 20 * S ^ 2 := by
      rw [← vsQVec_zero]; exact (vsB_wt_vecA hS hs _).1
    have wt0 : tV.wt ≤ 20 * S ^ 2 := (vsB_wt_vecA hS hs t).1
    have eT : (natList (vsQVec t)).wt = tV.wt := rfl
    have eT2 : (Val.list [tV, natList (List.replicate (vsQD s) 0)]).wt =
      (Val.list [natList (vsQVec t), natList (List.replicate (vsQD s) 0)]).wt := rfl
    have wT2 := wt_list2_le tV (natList (List.replicate (vsQD s) 0))
    have heqc : loopModK * ((vsQVec t).length + 1) * ((Val.list [natList (vsQVec t),
        natList (List.replicate (vsQD s) 0)]).wt + (vsQVec t).length + 4) ≤ 10 ^ 5 * S ^ 3 := by
      rw [vsQVec_length]
      have w2 := wt_list2_le (natList (vsQVec t)) (natList (List.replicate (vsQD s) 0))
      have h3 : 1000 * (vsQD s + 1) * ((Val.list [natList (vsQVec t), natList (List.replicate (vsQD s) 0)]).wt +
          vsQD s + 4) ≤ 1000 * (S * (100 * S ^ 2)) := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
      have e : 1000 * (S * (100 * S ^ 2)) = 10 ^ 5 * S ^ 3 := by ring
      simp only [loopModK]; omega
    have dG := rG [Val.nat i]
    have d1 := rOne [Val.nat i]
    by_cases ht : t = 0
    · have hd : decide (vsQVec t = List.replicate (vsQD s) 0) = true := by
        rw [ht, vsQVec_zero]; simp
      rw [hd] at deq
      have dout := Det.ite_pos deq (by decide)
        (Det.mk2 (Det.nat (P := P) (env := E1) 0) (Det.mk3 (Det.nat (P := P) (env := E1) 1) d1 dG))
        (e := mk2 (.nat 0) (mk1 (.nat 0)))
      refine dout.post fun c hc => ⟨some (1, s.hs), rfl, vsB0_ans_all hs hz ht, ?_⟩
      have wl := wleaf (some (1, s.hs)) (by intro r hr; simp at hr; rw [← hr]; exact hs.hsl)
      have el : (vsQLeafV (some (1, s.hs))).wt =
        (Val.list [.nat 0, .list [.nat 1, encPerm 1, encGroup s.hs]]).wt := rfl
      have hk1 : (Val.list [.nat 1, encPerm (1 : Perm (Fin I.n)), encGroup s.hs]).wt <
          (vsQLeafV (some (1, s.hs))).wt := by rw [el]; exact wt_le_wt_list (by simp)
      have hb := wt_boolVal_le true
      have w3 := wt_list3_le (.nat 1) (encPerm (1 : Perm (Fin I.n))) (encGroup s.hs)
      have w2 := wt_list2_le (.nat 0) (.list [.nat 1, encPerm (1 : Perm (Fin I.n)), encGroup s.hs])
      have wp1 := hS.wt_perm (1 : Perm (Fin I.n))
      have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 3; have := wt_nat_le 4
      clear_value lc cA cB chA t tV pv LbV A xs i
      have tW : (vsQLeafV (some (1, s.hs))).wt ≤ 10 ^ 4 * S ^ 6 := wl
      have tC : c ≤ 100 * Wp + 10 ^ 6 * S ^ 6 := by omega
      unfold vsB0TCost vsB0Cost
      clear * - hc1 hcc' tW tC e6 e5 e8 e9 hW1 q612 q612' hs2 hs6 q26 el
      omega
    · have hd : decide (vsQVec t = List.replicate (vsQD s) 0) = false :=
        decide_eq_false fun h => ht (vsQVec_injective' (h.trans vsQVec_zero.symm))
      rw [hd] at deq
      have dout := Det.ite_zero deq (Det.mk2 (Det.nat (P := P) (env := E1) 0) (Det.mk1 (Det.nat (P := P) (env := E1) 0)))
        (t := mk2 (.nat 0) (mk3 (.nat 1) vsBOneE (.get (.get (arg 0) (.nat 0)) (.nat 1))))
      refine dout.post fun c hc => ⟨none, rfl, vsB0_ans_none hs hz ht, ?_⟩
      have e : (vsQLeafV (I := I) none).wt = (Val.list [.nat 0, .list [.nat 0]]).wt := rfl
      have := wt_nat_le 0
      have w1 := wt_list1_le (.nat 0)
      have w2 := wt_list2_le (.nat 0) (.list [.nat 0])
      have hb := wt_boolVal_le false
      clear_value lc cA cB chA t tV pv LbV A xs i
      have tW : (vsQLeafV (I := I) none).wt ≤ 2000 * S ^ 6 := by omega
      have tC : c ≤ 100 * Wp + 10 ^ 6 * S ^ 6 := by omega
      unfold vsB0TCost vsB0Cost
      clear * - hc1 hcc' tW tC e6 e5 e8 e9 hW1 q612 q612' hs2 hs6 q26 e
      omega

end GI.Impl
