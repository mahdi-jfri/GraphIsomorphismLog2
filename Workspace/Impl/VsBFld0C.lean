import Workspace.Impl.VsBFld0B

/-!
# The case `T = 0` with a generator `g` that moves `0`

On `[lc, prep, Lb, g]` with `f(g) ≠ 0`: the point `m` with `(Λ(g) - 1) m = f(g)`, then
`u = t + m`. If `u = 0` there is no solution. Otherwise `τ ∈ L` with `τ m = u`, and the
λ-descent looks for `h` with `Λ(h) = τ`. The stabilizer is `H₁`.

* `vsB0bE`, `vsB0b_spec`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

theorem vsB0_u {p D : ℕ} [NeZero p] (t : Fin D → ZMod p) (a : List ℕ) :
    vsWV p D (vsLin p 1 1 (vsQVec t) a) = t + vsWV p D a := by
  funext j
  rw [vsWV_apply, vsF_apply, vsLin_getD _ _ _ _ _ (by rw [vsQVec_length]; exact j.2)]
  simp only [Pi.add_apply, vsWV_apply, vsF_apply, one_mul, Nat.cast_add, ZMod.natCast_mod]
  rw [← vsF_apply, vsF_vsQVec]

section Ans

variable {s : VsQSt I} (hs : VsQStOK s) (hab : s.Ab) (hdom : VsBDom s)
  (hT : ∀ k ∈ vsBH1 hs, vsBAlpha s k 0 = 0)
  {g₀ : Perm (Fin I.n)} (hg₀ : g₀ ∈ gens s.hs) {m : Fin (vsQD s) → ZMod I.p}
  (hm : (vsQLam s g₀ - 1) *ᵥ m = vsBAlpha s g₀ 0) (hne : vsBAlpha s g₀ 0 ≠ 0)
  {τ : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)} (hτ : τ ∈ vsBLamA s)
  (hτm : τ *ᵥ m = vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x) + m)
include hs hab hdom hT hg₀ hm hne hτ hτm

theorem vsB0b_found {gsA : List (Perm (Fin I.n))}
    (hgA : (genGroup gsA : Set (Perm (Fin I.n))) = vsBH1 hs) {prod : Perm (Fin I.n)}
    (hp : prod ∈ gens s.hs) (hpe : vsQLam s prod = τ) :
    VsQAnsOK hs.prob (some (prod, keepList gsA)) := by
  refine ⟨(vsB0_sol_tau hs hab hdom hT hg₀ hm hne hτ hτm).mpr ⟨hp, hpe⟩, ?_, length_keepList_le _⟩
  rw [gens_keepList, ← vsBStab0_eq hs, vsB0_stab hs hab hdom hT hg₀ hm hne]
  exact SetLike.coe_injective hgA

theorem vsB0b_none (hno : ¬ ∃ h ∈ gens s.hs, vsQLam s h = τ) : VsQAnsOK hs.prob none := by
  show vsQSol I _ _ _ _ = ∅
  ext h
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hh
  exact hno ⟨h, ((vsB0_sol_tau hs hab hdom hT hg₀ hm hne hτ hτm).mp hh)⟩

end Ans

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The case `T = 0` with a generator `g` moving `0`, on `[lc, prep, Lb, g]`. -/
def vsB0bE (m lin eqN tau rng dA red appd : ℕ) : Expr :=
  .letE (.call m (mk3 (.get (arg 1) (.nat 0)) (.get (arg 1) (.nat 1)) (arg 3)))
  (.letE (.call lin (.snoc (mk4 (.get (.get (arg 1) (.nat 0)) (.nat 2)) (.nat 1) (.nat 1)
      (.get (arg 1) (.nat 4))) (.var 1)))
  (.ite (.call eqN (mk2 (.var 2) (.get (.get (arg 1) (.nat 0)) (.nat 3))))
    (mk2 (.nat 0) (mk1 (.nat 0)))
    (.letE (.call tau (vsBmk5 (.get (.get (arg 1) (.nat 0)) (.nat 2)) (.get (.get (arg 1) (.nat 0)) (.nat 3))
        (arg 2) (.var 1) (.var 2)))
    (.letE (.call dA (vsBmk5 (.get (arg 1) (.nat 0))
        (.call rng (.arith .add (.arith .sub (.get (.get (arg 1) (.nat 0)) (.nat 4)) (.nat 2)) (.nat 1)))
        (.get (.get (arg 1) (.nat 2)) (.nat 1)) (.var 3) vsBOneE))
    (.ite (.get (.var 4) (.nat 0))
      (mk2 (.nat 0) (mk3 (.nat 1) (.get (.var 4) (.nat 2))
        (.call red (mk2 (.get (.get (arg 1) (.nat 0)) (.nat 4))
          (.call appd (mk2 (mk1 vsBOneE) (.get (.get (arg 1) (.nat 2)) (.nat 0))))))))
      (mk2 (.nat 0) (mk1 (.nat 0))))))))

/-- The layout of the case `T = 0` with a moving generator. -/
structure VsB0bAt (P : Program) (hm : Membership) (f m lin eqN tau rng dA red appd bA bB sc sv mI fI mF fF
    sv2 rp mm fl ch sotA cmp phi jp jm : ℕ) : Prop where
  hf0 : P.funs[f]? = some (vsB0bE m lin eqN tau rng dA red appd)
  hm0 : P.funs[m]? = some (vsB0mE (bA + 4) sc (bB + 3) (bB + 4) sv)
  hbA : P.HasAt bA (vsBAFuns bA phi)
  hbB : P.HasAt bB (vsBBFuns bB phi)
  hsc : P.HasAt sc (vsWSubCFuns sc)
  hsv : P.HasAt sv (vsBSolveFuns sv)
  hlin : P.HasAt lin (vsLinFuns lin)
  heqN : P.HasAt eqN (eqNatsFuns eqN)
  htau : VsB0TAt P tau mI fI mF fF sv2 rp mm fl ch
  hrng : P.HasAt rng (rangeFuns rng)
  hdA : P.HasAt dA (vsBDescFuns dA (bA + 2) (sotA + 8) (bA + 3) cmp)
  hsotA : P.HasAt sotA (vsQSotFuns sotA (bA + 1) jp jm)
  hcmp : P.HasAt cmp (composeFuns cmp)
  hred : P.HasAt red (reduceFuns red jm)
  happd : P.HasAt appd (appendFuns appd)
  hjm : P.prims[jm]? = some (membershipPrim hm)

/-- The cost bound of the case `T = 0`. -/
noncomputable def vsB0Cost (hm : Membership) (n S Cφ : ℕ) : ℕ :=
  vsBDaCost S Cφ + 3 * Cφ + 10 ^ 30 * S ^ 12 + reduceCost hm n (2 * S ^ 2)

set_option maxHeartbeats 16000000 in
/-- **The case `T = 0` with a generator moving `0`.** -/
theorem vsB0b_spec (hm : Membership) {P : Program}
    {f m lin eqN tau rng dA red appd bA bB sc sv mI fI mF fF sv2 rp mm fl ch sotA cmp phi jp jm Cφ S Tm : ℕ}
    (H : VsB0bAt P hm f m lin eqN tau rng dA red appd bA bB sc sv mI fI mF fF sv2 rp mm fl ch sotA cmp
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
    (hT : ∀ k ∈ vsBH1 hs, vsBAlpha s k 0 = 0) {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs)
    (hne : vsBAlpha s g 0 ≠ 0) {Wp : ℕ}
    (hWp : (Val.list [vsQLCV s, .list [vsBCtxA s hD, vsBCtxB s,
      .list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))], chB,
      natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))], vsFMatsVal Lb, encPerm g]).wt ≤ Wp) :
    FunAll P f (.list [vsQLCV s, .list [vsBCtxA s hD, vsBCtxB s,
      .list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))], chB,
      natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))], vsFMatsVal Lb, encPerm g])
      (fun w c => ∃ a, w = vsQLeafV a ∧ VsQAnsOK hs.prob a ∧ c ≤ vsB0Cost hm I.n S Cφ + 1000 * Wp) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  haveI : Fact I.p.Prime := ⟨I.prime⟩
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
  set A := Val.list [lc, pv, LbV, encPerm g]
  have wA : A.wt ≤ Wp := hWp
  have rd : ∀ rest k v, [lc, pv, LbV, encPerm g][k]? = some v → Det P (A :: rest) (arg k) v (2 * A.wt + k + 5) :=
    fun rest k v hv => Det.arg' (vs := [lc, pv, LbV, encPerm g]) (rest := rest) hv
  have wpv : pv.wt < A.wt := wt_le_wt_list (by simp [A])
  have wlc : lc.wt < A.wt := wt_le_wt_list (by simp [A])
  have wLbA : LbV.wt < A.wt := wt_le_wt_list (by simp [A])
  have wgA : (encPerm g).wt < A.wt := wt_le_wt_list (by simp [A])
  have rp : ∀ rest k v, [cA, cB, chA, chB, tV][k]? = some v →
      Det P (A :: rest) (.get (arg 1) (.nat k)) v (3 * A.wt + 20) := fun rest k v hv => by
    refine (Det.get' (rd rest 1 pv rfl) (Det.nat k) hv).mono ?_
    have hk : k < 5 := by
      by_contra h; push Not at h
      rw [List.getElem?_eq_none (by simp; omega)] at hv; cases hv
    have : v.wt < pv.wt := wt_le_wt_list (List.mem_of_getElem? hv)
    omega
  have wcA : cA.wt < pv.wt := wt_le_wt_list (by simp [pv])
  have wchA : chA.wt < pv.wt := wt_le_wt_list (by simp [pv])
  have rA : ∀ rest k v, [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
      natList (List.replicate (vsQD s) 0), .nat I.n, natList (vsQVec (vsBe0 s hD))][k]? = some v →
      Det P (A :: rest) (.get (.get (arg 1) (.nat 0)) (.nat k)) v (4 * A.wt + 40) := fun rest k v hv => by
    refine (Det.get' (rp rest 0 cA rfl) (Det.nat k) hv).mono ?_
    have hk : k < 6 := by
      by_contra h; push Not at h
      rw [List.getElem?_eq_none (by simp; omega)] at hv; cases hv
    have : v.wt < cA.wt := wt_le_wt_list (List.mem_of_getElem? hv)
    omega
  have rH : ∀ rest k v, [Val.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))][k]? = some v →
      Det P (A :: rest) (.get (.get (arg 1) (.nat 2)) (.nat k)) v (4 * A.wt + 40) := fun rest k v hv => by
    refine (Det.get' (rp rest 2 chA rfl) (Det.nat k) hv).mono ?_
    have hk : k < 2 := by
      by_contra h; push Not at h
      rw [List.getElem?_eq_none (by simp; omega)] at hv; cases hv
    have : v.wt < chA.wt := wt_le_wt_list (List.mem_of_getElem? hv)
    omega
  have rOne : ∀ rest, Det P (A :: rest) vsBOneE (encPerm 1) (6 * A.wt + 60) := fun rest => by
    have d0 := rd rest 0 lc rfl
    have dst := Det.get' d0 (Det.nat 0) (show [vsQStV I s, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat (vsQD s),
      vsFMatsVal (vsQMs s)][0]? = some (vsQStV I s) from rfl)
    have dG := Det.get' dst (Det.nat 1) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
      natList s.y][1]? = some (encGroup s.hs) from rfl)
    have dGl := Det.get' dG (Det.nat 1) (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][1]? =
      some (.list ((1 :: s.hs).map encPerm)) from rfl)
    have d1 := Det.get' dGl (Det.nat 0) (show ((1 :: s.hs).map encPerm)[0]? = some (encPerm 1) from rfl)
    refine d1.mono ?_
    have wst : (vsQStV I s).wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV])
    have wGs : (encGroup s.hs).wt < (vsQStV I s).wt := wt_le_wt_list (by simp [vsQStV])
    have wgl : (Val.list ((1 :: s.hs).map encPerm)).wt < (encGroup s.hs).wt :=
      wt_le_wt_list (by simp [encGroup, encPerms])
    have w1 : (encPerm (1 : Perm (Fin I.n))).wt < (Val.list ((1 :: s.hs).map encPerm)).wt :=
      wt_le_wt_list (by simp)
    have ef1 : (Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]).wt =
      (vsQStV I s).wt := rfl
    have eg1 : (Val.list [Val.nat I.n, .list ((1 :: s.hs).map encPerm)]).wt = (encGroup s.hs).wt := rfl
    have := wt_nat_le 0; have := wt_nat_le 1
    omega
  -- the point `m`
  set aL := vsB0a s g
  have hRfit := vsBR_sq (s := s) g
  have hFfit : VsWFit I.p (vsQD s) [vsQVec (vsBAlpha s g 0)] := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact ⟨vsQVec_lt _, vsQVec_length _⟩
  have hsol := vsBSolve_comb I.prime hRfit.1 hFfit (vsB0_m_sp hs hdom hT hg hne)
  have hmv : (vsQLam s g - 1) *ᵥ vsWV I.p (vsQD s) aL = vsBAlpha s g 0 := vsB0_m hs hsol.2.2
  have ham : vsWV I.p (vsQD s) aL ≠ 0 := fun h0 => hne (by rw [← hmv, h0, mulVec_zero])
  have hal : aL.length = (vsQD s) + 1 := by rw [show aL = vsBSolveL I.p (vsBR s g) (vsQVec (vsBAlpha s g 0)) from rfl,
    hsol.2.1, hRfit.2]
  have halp : ∀ y ∈ aL, y < I.p := hsol.1
  have hN2 : (S + 1) ^ 2 ≤ 4 * S ^ 2 := by
    have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
    omega
  have waL : (natList aL).wt ≤ 20 * S ^ 2 := by
    have := wt_natList_le_sq (B := S) (xs := aL) (fun y hy => (halp y hy).le.trans hpS) (by omega)
    omega
  have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q612 : S ^ 6 ≤ S ^ 12 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hs2 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS1
  have hSS : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have da := Det.call (Det.mk3 (rp [] 0 cA rfl) (rp [] 1 cB rfl) (rd [] 3 _ rfl))
    (vsB0m_spec H.hm0 H.hbA H.hbB H.hsc H.hsv hphi hS hs hD hdom hT hg hne)
  have wcB : cB.wt < pv.wt := wt_le_wt_list (by simp [pv])
  have wtV : tV.wt < pv.wt := wt_le_wt_list (by simp [pv])
  refine FunAll.intro H.hf0 (EvalAll.letE da fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  have hc1' : c1 ≤ 2 * Cφ + 10 ^ 17 * S ^ 6 + 30 * Wp + 100 * S ^ 2 + 1000 := by
    have := wt_list3_le cA cB (encPerm g)
    have ea : (natList (vsB0a s g)).wt = (natList aL).wt := rfl
    clear_value aL lc cA cB chA t tV pv LbV A
    omega
  clear hc1
  -- `u = t + m`
  set E1 := [A, natList aL]
  set uL := vsLin I.p 1 1 (vsQVec t) aL
  have du := Det.call (Det.snoc (Det.mk4 (rA [natList aL] 2 _ rfl) (Det.nat 1) (Det.nat 1)
      (rp [natList aL] 4 tV rfl)) (Det.var' (P := P) (env := E1) (i := 1) rfl))
    (vsLin_spec H.hlin (N := S) I.prime.pos (fun x hx => (vsQVec_lt t x hx).le.trans hpS)
      (fun x hx => (halp x hx).le.trans hpS) (by rw [vsQVec_length]; omega) (by omega)
      (by rw [vsQVec_length]; omega) hpS (by omega) (by omega))
  have huL : uL = vsQVec (vsWV I.p (vsQD s) uL) :=
    vsQVec_of (by rw [vsLin_length, vsQVec_length]) (vsLin_lt I.prime.pos _ _)
  have huu : vsWV I.p (vsQD s) uL = t + vsWV I.p (vsQD s) aL := vsB0_u t aL
  have wuL : (natList uL).wt ≤ 20 * S ^ 2 := by
    rw [huL]; exact (vsB_wt_vecA hS hs _).1
  refine EvalAll.letE du fun v2 c2 hv2 => ?_
  obtain ⟨rfl, hc2⟩ := hv2
  have hc2' : c2 ≤ 10 ^ 7 * S ^ 3 + 30 * Wp := by
    have w4 := wt_list_le [Val.nat I.p, .nat 1, .nat 1, tV, natList aL]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at w4
    have w4' := wt_list4_le (.nat I.p) (.nat 1) (.nat 1) tV
    have := wt_nat_le I.p; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 4
    have hN3 : (S + 1) ^ 3 ≤ 8 * S ^ 3 := by
      have h1 : (S + 1) ^ 3 ≤ (2 * S) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      have e : (2 * S) ^ 3 = 8 * S ^ 3 := by ring
      omega
    have ew : (Val.list ([Val.nat I.p, .nat 1, .nat 1, tV] ++ [natList aL])).wt =
      (Val.list [Val.nat I.p, .nat 1, .nat 1, tV, natList aL]).wt := rfl
    have ew2 : (vsLinArg I.p 1 1 (vsQVec t) aL).wt = (Val.list [Val.nat I.p, .nat 1, .nat 1, tV, natList aL]).wt := rfl
    have eu : (natList (vsLin I.p 1 1 (vsQVec t) aL)).wt ≤ 20 * S ^ 2 := wuL
    clear_value aL uL lc cA cB chA t tV pv LbV A
    omega
  clear hc2
  -- the test `u = 0`
  set E2 := [A, natList aL, natList uL]
  have dq := Det.call (Det.mk2 (Det.var' (P := P) (env := E2) (i := 2) rfl)
    (rA [natList aL, natList uL] 3 _ rfl)) (eqNats_spec H.heqN uL (List.replicate (vsQD s) 0))
  refine EvalAll.ite dq (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
  obtain ⟨hx1, hcc⟩ := hx
  have hx2 : x = (decide (uL = List.replicate (vsQD s) 0)).toNat := Val.nat.inj hx1
  have hcc' : cc ≤ 10 ^ 6 * S ^ 3 + 30 * Wp := by
    have w2 := wt_list2_le (natList uL) (natList (List.replicate (vsQD s) 0))
    have wz : (natList (List.replicate (vsQD s) 0)).wt ≤ 20 * S ^ 2 := by
      rw [← vsQVec_zero]; exact (vsB_wt_vecA hS hs _).1
    have hl : uL.length = (vsQD s) := by rw [vsLin_length, vsQVec_length]
    have hb := wt_boolVal_le (decide (uL = List.replicate (vsQD s) 0))
    have h3 : loopModK * (uL.length + 1) * ((Val.list [natList uL, natList (List.replicate (vsQD s) 0)]).wt +
        uL.length + 4) ≤ 10 ^ 3 * (S * (100 * S ^ 2)) := by
      simp only [loopModK]; rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    have e : 10 ^ 3 * (S * (100 * S ^ 2)) = 10 ^ 5 * S ^ 3 := by ring
    clear_value aL uL lc cA cB chA t tV pv LbV A
    omega
  clear hcc hx1
  have wleaf : ∀ a : Option (Perm (Fin I.n) × List (Perm (Fin I.n))), (∀ r ∈ a, r.2.length ≤ I.n ^ 2) →
      (vsQLeafV a).wt ≤ 10 ^ 4 * S ^ 6 := fun a ha => vsQLeaf_wt hS ha
  have wnone := wleaf none (by simp)
  by_cases hu0 : uL = List.replicate (vsQD s) 0
  · have : x = 1 := by simp [hx2, hu0]
    subst this
    simp only [one_ne_zero, if_false]
    refine (Det.mk2 (Det.nat 0) (Det.mk1 (Det.nat 0))).post fun c hc => ⟨none, rfl, ?_, ?_⟩
    · apply vsB0_ans_u0 hs hab hdom hT hg hmv hne
      have : vsWV I.p (vsQD s) uL = 0 := by rw [hu0, ← vsQVec_zero, vsWV_vsQVec]
      rwa [huu] at this
    · have e : (vsQLeafV (I := I) none).wt = (Val.list [.nat 0, .list [.nat 0]]).wt := rfl
      have := wt_nat_le 0
      have w1 := wt_list1_le (.nat 0)
      unfold vsB0Cost
      clear_value aL uL lc cA cB chA t tV pv LbV A
      omega
  have : x = 0 := by simp [hx2, hu0]
  subst this
  simp only [if_true]
  have hu1 : vsWV I.p (vsQD s) uL ≠ 0 := fun h => hu0 (by rw [huL, h, vsQVec_zero])
  -- `τ`
  have hpS2 : I.p ≤ S ^ 2 := hpS.trans (Nat.le_self_pow (by norm_num) _)
  have hDD2 : vsQD s * vsQD s + 1 ≤ S ^ 2 := by
    have h1 : vsQD s + 1 ≤ S := by omega
    have h2 := Nat.mul_le_mul h1 h1
    have e : (vsQD s + 1) * (vsQD s + 1) = vsQD s * vsQD s + 2 * vsQD s + 1 := by ring
    rw [sq]; omega
  have hLl2 : Lb.length + 1 ≤ S ^ 2 := by omega
  have hufit : VsWFit I.p (vsQD s) [uL] := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨vsLin_lt I.prime.pos _ _, by rw [vsLin_length, vsQVec_length]⟩
  have hsp : vsWV I.p (vsQD s) uL ∈ vsWSp I.p (vsQD s) (vsB0Imgs I.p (vsQD s) Lb aL) := by
    rw [show vsB0Imgs I.p (vsQD s) Lb aL = Lb.map fun M => vsFRowMul I.p aL M (vsWZ (vsQD s)) from rfl,
      vsB0_imgs_top hs hdom hD hspan hLb hsq ham]
    exact Submodule.mem_top
  have hIfit : VsWFit I.p (vsQD s) (vsB0Imgs I.p (vsQD s) Lb aL) := fun r hr => by
    obtain ⟨M, -, rfl⟩ := List.mem_map.mp hr
    exact vsFRowMul_fit I.prime.pos aL M _ (List.mem_singleton_self _)
  set τ := vsWM I.p (vsQD s) (vsB0TauL I.p (vsQD s) Lb aL uL)
  have hτ := vsB0_tau hLb hsq aL (vsBSolveL I.p (vsB0Imgs I.p (vsQD s) Lb aL) uL) uL
    (vsBSolve_comb I.prime hIfit hufit hsp).2.2
  have hτm : τ *ᵥ vsWV I.p (vsQD s) aL = t + vsWV I.p (vsQD s) aL := by rw [← huu]; exact hτ.2
  have hτ0 : τ ≠ 0 := fun h0 => hu1 (by rw [← hτ.2]; show τ *ᵥ _ = 0; rw [h0, zero_mulVec])
  obtain ⟨uτ, huτ⟩ := vsB_unit hs hab hdom hτ.1 hτ0
  set E2' := [natList aL, natList uL]
  have dτ := Det.call (Det.vsBmk5 (rA E2' 2 _ rfl) (rA E2' 3 _ rfl) (rd E2' 2 _ rfl)
      (Det.var' (P := P) (env := E2) (i := 1) rfl) (Det.var' (P := P) (env := E2) (i := 2) rfl))
    (vsB0Tau_spec H.htau I.prime (N := S ^ 2) hpS2 hDD2 hsq hLl2 halp (by omega) (by omega) hufit hsp)
  have wτE : (vsQE I.p (vsQD s) 0 τ).wt ≤ 2 * 10 ^ 4 * S ^ 3 := vsB_wt_carA hS hs τ
  have eτE : vsQE I.p (vsQD s) 0 (vsWM I.p (vsQD s) (vsB0TauL I.p (vsQD s) Lb aL uL)) = vsQE I.p (vsQD s) 0 τ := rfl
  rw [eτE] at dτ
  refine EvalAll.letE dτ fun v3 c3 hv3 => ?_
  obtain ⟨rfl, hc3⟩ := hv3
  have hS12 : (S ^ 2 + 1) ^ 6 ≤ 64 * S ^ 12 := by
    have h1 : (S ^ 2 + 1) ^ 6 ≤ (2 * S ^ 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have e : (2 * S ^ 2) ^ 6 = 64 * S ^ 12 := by ring
    omega
  have hc3' : c3 ≤ 10 ^ 14 * S ^ 12 + 40 * Wp := by
    have w5 := wt_list_le [Val.nat I.p, natList (List.replicate (vsQD s) 0), LbV, natList aL, natList uL]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at w5
    have wz : (natList (List.replicate (vsQD s) 0)).wt ≤ 20 * S ^ 2 := by
      rw [← vsQVec_zero]; exact (vsB_wt_vecA hS hs _).1
    have := wt_nat_le I.p; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
    clear_value aL uL lc cA cB chA t tV pv LbV A τ
    omega
  clear hc3
  -- the λ-descent
  set E3 := [A, natList aL, natList uL, vsQE I.p (vsQD s) 0 τ]
  set E3' := [natList aL, natList uL, vsQE I.p (vsQD s) 0 τ]
  have dk := Det.arith (op := .add) (Det.arith (op := .sub) (rA E3' 4 _ rfl) (Det.nat 2)) (Det.nat 1)
  simp only [GI.Machine.BinOp.eval] at dk
  have hk : I.n - 2 + 1 = max I.n 2 - 1 := by omega
  rw [hk] at dk
  have hrange : FunDet P rng (.nat (max I.n 2 - 1)) (natList (vsBPs I.n)) (10 ^ 5 * S ^ 3) := by
    refine (range_spec H.hrng (max I.n 2 - 1)).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
    obtain ⟨rfl, -⟩ := hw
    have wr : (natList (List.range (max I.n 2 - 1))).wt ≤ 5 * (S + 1) ^ 2 :=
      wt_natList_le_sq (fun y hy => (List.mem_range.mp hy).le.trans (by omega)) (by simp; omega)
    have wk := wt_nat_le (max I.n 2 - 1)
    have h2 : (max I.n 2 - 1 + 1) * ((Val.nat (max I.n 2 - 1)).wt + (max I.n 2 - 1) +
        (natList (List.range (max I.n 2 - 1))).wt + 1) ≤ (2 * S) * (30 * S ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (2 * S) * (30 * S ^ 2) = 60 * S ^ 3 := by ring
    simp only [loopModK]
    calc 1000 * (max I.n 2 - 1 + 1) * _ = 1000 * ((max I.n 2 - 1 + 1) * ((Val.nat (max I.n 2 - 1)).wt +
          (max I.n 2 - 1) + (natList (List.range (max I.n 2 - 1))).wt + 1)) := by ring
      _ ≤ _ := by omega
  have drng := Det.call dk hrange
  have din := Det.vsBmk5 (rp E3' 0 cA rfl) drng (rH E3' 1 _ rfl)
    (Det.var' (P := P) (env := E3) (i := 3) rfl) (rOne E3')
  have edin : Val.list [cA, natList (vsBPs I.n), .list (LsA.map (vsQPairs vsQVec)), vsQE I.p (vsQD s) 0 τ,
      encPerm (1 : Perm (Fin I.n))] = vsBDescIn cA (vsBPs I.n) vsQVec LsA (vsBEncU s) uτ := by
    rw [vsBDescIn, vsBEncU, huτ]; rfl
  rw [edin] at din
  have hdA := vsB_descA H.hdA H.hsotA H.hcmp H.hbA hphi hS hs hab hD hdom hlA hOA hWA uτ
  refine EvalAll.letE (Ra := fun w c => VsBDescOut (gens s.hs) (vsBPsi hs) (vsBEncU s) uτ w ∧
      c ≤ vsBDaCost S Cφ + 10 ^ 7 * S ^ 6 + 100 * Wp)
    (EvalAll.call_funAll din fun v ca hv => ?_) fun v4 c4 hv4 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hdA.mono fun w c hw => ⟨hw.1, ?_⟩
    obtain ⟨⟨ok, τm, prod, rfl, hok⟩, hc⟩ := hw
    have hok1 : ok ≤ 1 := by rcases hok with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
    have w3 := wt_list3_le (.nat ok) (vsBEncU s τm) (encPerm prod)
    have := wt_nat_le ok
    have := vsB_wt_carA hS hs ((τm : (vsBMt s)ˣ) : vsBMt s)
    have eE : (vsBEncU s τm).wt = (vsQE I.p (vsQD s) 0 ((τm : (vsBMt s)ˣ) : vsBMt s)).wt := rfl
    have := hS.wt_perm prod
    have w1 := hS.wt_perm 1
    have w5 := wt_list_le [cA, natList (vsBPs I.n), .list (LsA.map (vsQPairs vsQVec)),
      vsQE I.p (vsQD s) 0 τ, encPerm (1 : Perm (Fin I.n))]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at w5
    have wps : (natList (vsBPs I.n)).wt ≤ 5 * (S + 1) ^ 2 :=
      wt_natList_le_sq (xs := vsBPs I.n) (fun y hy => by simp [vsBPs] at hy; omega) (by simp [vsBPs]; omega)
    have wLs : (Val.list (LsA.map (vsQPairs vsQVec))).wt < chA.wt := wt_le_wt_list (by simp [chA])
    have edin2 : (vsBDescIn cA (vsBPs I.n) vsQVec LsA (vsBEncU s) uτ).wt =
        (Val.list [cA, natList (vsBPs I.n), .list (LsA.map (vsQPairs vsQVec)), vsQE I.p (vsQD s) 0 τ,
          encPerm (1 : Perm (Fin I.n))]).wt := by rw [← edin]
    have := wt_nat_le (max I.n 2 - 1); have := wt_nat_le 2; have := wt_nat_le 1; have := wt_nat_le 4
    have := wt_nat_le (I.n - 2); have := wt_nat_le I.n
    clear_value aL uL lc cA cB chA t tV pv LbV A τ
    omega
  obtain ⟨⟨ok, τm, prod, rfl, hok⟩, hc4⟩ := hv4
  set dV := Val.list [.nat ok, vsBEncU s τm, encPerm prod]
  set E4 := [A, natList aL, natList uL, vsQE I.p (vsQD s) 0 τ, dV]
  set E4' := [natList aL, natList uL, vsQE I.p (vsQD s) 0 τ, dV]
  have dok := Det.get' (Det.var' (P := P) (env := E4) (i := 4) rfl) (Det.nat 0)
    (show [Val.nat ok, vsBEncU s τm, encPerm prod][0]? = some (.nat ok) from rfl)
  refine EvalAll.ite dok (fun _ _ h => ⟨_, h.1⟩) fun x cc2 hx => ?_
  obtain ⟨hx1, hcc2⟩ := hx
  have hxo : x = ok := Val.nat.inj hx1
  subst hxo
  have hok1 : x ≤ 1 := by rcases hok with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
  have wdV : dV.wt ≤ 10 ^ 5 * S ^ 3 := by
    have w3 := wt_list3_le (.nat x) (vsBEncU s τm) (encPerm prod)
    have := wt_nat_le x
    have := vsB_wt_carA hS hs ((τm : (vsBMt s)ˣ) : vsBMt s)
    have eE : (vsBEncU s τm).wt = (vsQE I.p (vsQD s) 0 ((τm : (vsBMt s)ˣ) : vsBMt s)).wt := rfl
    have := hS.wt_perm prod
    have edV : dV.wt = (Val.list [.nat x, vsBEncU s τm, encPerm prod]).wt := rfl
    omega
  have hcc2' : cc2 ≤ 10 ^ 6 * S ^ 3 := by
    have := wt_nat_le 0
    have : (Val.nat x).wt ≤ 3 := by have := wt_nat_le x; omega
    have edV : dV.wt = (Val.list [.nat x, vsBEncU s τm, encPerm prod]).wt := rfl
    omega
  clear hcc2
  rcases hok with ⟨rfl, hp, hpe⟩ | ⟨rfl, hno⟩
  · simp only [one_ne_zero, if_false]
    have hpe' : vsQLam s prod = τ := by
      have := congrArg (fun u : vsBU s => ((u : (vsBMt s)ˣ) : vsBMt s)) hpe
      simpa [vsBPsi_val hs hp, huτ] using this
    have hgw := vsB_wt_gens hS hglA
    have w1v : (Val.list [encPerm (1 : Perm (Fin I.n))]).wt ≤ 1000 * S ^ 6 := by
      have := wt_list1_le (encPerm (1 : Perm (Fin I.n))); have := hS.wt_perm (1 : Perm (Fin I.n))
      omega
    have wL1 : (Val.list ([encPerm (1 : Perm (Fin I.n))] ++ gsA.map encPerm)).wt ≤ 500 * S ^ 6 := by
      have := vsB_wt_gens' hS (gs := 1 :: gsA) (by simp; omega)
      exact this
    have kap : FunDet P appd (.list [.list [encPerm (1 : Perm (Fin I.n))], .list (gsA.map encPerm)])
        (.list ([encPerm (1 : Perm (Fin I.n))] ++ gsA.map encPerm)) (10 ^ 8 * S ^ 8) := by
      refine (append_spec H.happd [encPerm (1 : Perm (Fin I.n))] (gsA.map encPerm)).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
      obtain ⟨rfl, -⟩ := hw
      have w2 := wt_list2_le (.list [encPerm (1 : Perm (Fin I.n))]) (.list (gsA.map encPerm))
      have hyl : (gsA.map encPerm).length + 1 ≤ 4 * S ^ 2 := by
        simp; have : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega
      have h4 : ((gsA.map encPerm).length + 1) * ((Val.list [.list [encPerm (1 : Perm (Fin I.n))],
          .list (gsA.map encPerm)]).wt + (gsA.map encPerm).length +
          (Val.list ([encPerm (1 : Perm (Fin I.n))] ++ gsA.map encPerm)).wt + 1) ≤
          (4 * S ^ 2) * (10 ^ 4 * S ^ 6) := Nat.mul_le_mul hyl (by omega)
      have e : (4 * S ^ 2) * (10 ^ 4 * S ^ 6) = 4 * 10 ^ 4 * S ^ 8 := by ring
      simp only [loopModK]
      calc 1000 * ((gsA.map encPerm).length + 1) * _ = 1000 * (((gsA.map encPerm).length + 1) *
            ((Val.list [.list [encPerm (1 : Perm (Fin I.n))], .list (gsA.map encPerm)]).wt +
            (gsA.map encPerm).length + (Val.list ([encPerm (1 : Perm (Fin I.n))] ++ gsA.map encPerm)).wt + 1)) := by
              ring
        _ ≤ _ := by omega
    have dap := Det.call (Det.mk2 (Det.mk1 (rOne E4')) (rH E4' 0 _ rfl)) kap
    have dG0 := Det.mk2 (rA E4' 4 _ rfl) dap
    have eG : Val.list [.nat I.n, .list ([encPerm (1 : Perm (Fin I.n))] ++ gsA.map encPerm)] = encGroup gsA := by
      simp [encGroup, encPerms]
    rw [eG] at dG0
    have dred := Det.call dG0 (reduce_spec hm H.hred H.hjm gsA)
    have dprod := Det.get' (Det.var' (P := P) (env := E4) (i := 4) rfl) (Det.nat 2)
      (show [Val.nat 1, vsBEncU s τm, encPerm prod][2]? = some (encPerm prod) from rfl)
    have dout := Det.mk2 (Det.nat (P := P) (env := E4) 0) (Det.mk3 (Det.nat (P := P) (env := E4) 1) dprod dred)
    refine dout.post fun c hc => ⟨some (prod, keepList gsA), rfl,
      vsB0b_found hs hab hdom hT hg hmv hne (show τ ∈ vsBLamA s from hτ.1) hτm hgA hp hpe', ?_⟩
    have wl := wleaf (some (prod, keepList gsA)) (by intro r hr; simp at hr; rw [← hr]; exact length_keepList_le _)
    have el : (vsQLeafV (some (prod, keepList gsA))).wt =
      (Val.list [.nat 0, .list [.nat 1, encPerm prod, encGroup (keepList gsA)]]).wt := rfl
    have hred := reduceCost_mono hm I.n (show gsA.length ≤ 2 * S ^ 2 by
      have : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega)
    have wG : (encGroup gsA).wt ≤ 2000 * S ^ 6 := by
      have := wt_list2_le (.nat I.n) (.list ([encPerm (1 : Perm (Fin I.n))] ++ gsA.map encPerm))
      rw [eG] at this; have := wt_nat_le I.n; omega
    have w3 := wt_list3_le (.nat 1) (encPerm prod) (encGroup (keepList gsA))
    have w2 := wt_list2_le (.nat 0) (.list [.nat 1, encPerm prod, encGroup (keepList gsA)])
    have w2' := wt_list2_le (.nat I.n) (.list ([encPerm (1 : Perm (Fin I.n))] ++ gsA.map encPerm))
    have w2'' := wt_list2_le (.list [encPerm (1 : Perm (Fin I.n))]) (.list (gsA.map encPerm))
    have wgs : (Val.list (gsA.map encPerm)).wt < chA.wt := wt_le_wt_list (by simp [chA])
    have := hS.wt_perm prod; have := wt_nat_le I.n
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 4
    have edV : dV.wt = (Val.list [.nat 1, vsBEncU s τm, encPerm prod]).wt := rfl
    have hk1 : (Val.list [.nat 1, encPerm prod, encGroup (keepList gsA)]).wt <
        (vsQLeafV (some (prod, keepList gsA))).wt := by rw [el]; exact wt_le_wt_list (by simp)
    have hk2 : (encGroup (keepList gsA)).wt < (Val.list [.nat 1, encPerm prod, encGroup (keepList gsA)]).wt :=
      wt_le_wt_list (by simp)
    have q812 : S ^ 8 ≤ S ^ 12 := Nat.pow_le_pow_right hS1 (by norm_num)
    have q312 : S ^ 3 ≤ S ^ 12 := Nat.pow_le_pow_right hS1 (by norm_num)
    have hDa := vsBDaCost
    unfold vsB0Cost
    clear_value aL uL lc cA cB chA t tV pv LbV A τ dV
    omega
  · simp only [if_true]
    have hno' : ¬ ∃ h ∈ gens s.hs, vsQLam s h = τ := by
      rintro ⟨h, hh, he⟩
      exact hno ⟨h, hh, Subtype.ext (Units.ext (by rw [vsBPsi_val hs hh, huτ, he]; try rfl))⟩
    refine (Det.mk2 (Det.nat 0) (Det.mk1 (Det.nat 0))).post fun c hc => ⟨none, rfl,
      vsB0b_none hs hab hdom hT hg hmv hne (show τ ∈ vsBLamA s from hτ.1) hτm hno', ?_⟩
    have e : (vsQLeafV (I := I) none).wt = (Val.list [.nat 0, .list [.nat 0]]).wt := rfl
    have := wt_nat_le 0
    have w1 := wt_list1_le (.nat 0)
    have q312 : S ^ 3 ≤ S ^ 12 := Nat.pow_le_pow_right hS1 (by norm_num)
    unfold vsB0Cost
    clear_value aL uL lc cA cB chA t tV pv LbV A τ dV
    omega

end GI.Impl
