module

public import Workspace.Impl.FreshPrep
public import Workspace.Impl.Floor
public import Workspace.Impl.Weights

@[expose] public section

/-!
# A fresh phase of `Solve`

Algorithm 5, `Solve` with `N₀ < |dom|`: start a fresh phase on the domain. In the recursion
this is `Run.fresh`: one `Continue` child on the fresh state `S' = S.freshOn (freshHier G' M)`
on the type `S.dom`, where `G' = G|_dom` and `M` is the size of a largest orbit of `G'`. Its
answer `A'` is lifted back to `S.liftAnswer A'`.

The step function `freshBody prep cont lift` on a state value `v`:

1. `p := prepF v` (`prep_spec`): a short generating list `gs₀` of `G`, the domain positions,
   `s = |dom|`, and a canonical value `v'` of `S'`.
2. `u' := Continue v'`, by the induction hypothesis: `S'` meets the invariant
   (`good_fresh`) and is smaller in the measure (`mlt_fresh`).
3. The lift of `u'` (`lift_spec`) on `[[k, s, domCtx, gs₀], u']`.

Cited tasks: **PointwiseStab** (in `prepF`, to cut generating lists), **Preimage** and
**NormalizedFactor** (in the lift).

Cost: `prepF` and the lift cost at most `prepCost (X)` and `liftCost (X)` with `X = wt v + 1`,
and the rest of the body at most `10⁷ X⁶`. The step needs `freshCost X ≤ Ks X^ds` for all
`X ≥ 1` (`Iface.FreshK`). The `Continue` call costs at most the total cost of its run, which is
the child cost of `Run.fresh`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens PointwiseStab Preimage NormalizedFactor)

/-- The body of a fresh phase on a state value `v`. -/
def freshBody (prep cont lift : ℕ) : Expr :=
  .letE (.call prep (.var 0))
  (.letE (.call cont (.get (.var 1) (.nat 3)))
  (.call lift (mk2 (mk4 (arg 0) (.get (.var 1) (.nat 2)) (.get (.var 1) (.nat 1))
    (.get (.var 1) (.nat 0))) (.var 2))))

/-- The cost of a fresh phase besides the `Continue` call, in `X = wt v + 1`. -/
def freshCost (pst pp pf : Prim) (X : ℕ) : ℕ :=
  prepCost pst X + liftCost pp pf X + 10 ^ 7 * X ^ 6

theorem liftCost_mono (pp pf : Prim) {a b : ℕ} (h : a ≤ b) : liftCost pp pf a ≤ liftCost pp pf b := by
  unfold liftCost
  have h1 : (a + 1) ^ 21 ≤ (b + 1) ^ 21 := Nat.pow_le_pow_left (by omega) _
  have h2 : (a + 1) ^ 6 ≤ (b + 1) ^ 6 := Nat.pow_le_pow_left (by omega) _
  have h3 : (10 ^ 6 * (a + 1) ^ 6 + 2) ^ pp.k ≤ (10 ^ 6 * (b + 1) ^ 6 + 2) ^ pp.k :=
    Nat.pow_le_pow_left (by omega) _
  have h4 : (10 ^ 6 * (a + 1) ^ 6 + 2) ^ pf.k ≤ (10 ^ 6 * (b + 1) ^ 6 + 2) ^ pf.k :=
    Nat.pow_le_pow_left (by omega) _
  have := Nat.mul_le_mul_left liftK h1
  have := Nat.mul_le_mul_left pp.c h3
  have := Nat.mul_le_mul_left pf.c h4
  omega

theorem ansW_le_pow (k : ℕ) : ansW k ≤ 400 * (k + 1) ^ 6 := by
  unfold ansW groupW
  have h1 : (k ^ 2 + 2) * (k + 1) ≤ 2 * (k + 1) ^ 3 := measure_le_of_sq le_rfl
  have h2 : ((k ^ 2 + 2) * (k + 1)) ^ 2 ≤ 4 * (k + 1) ^ 6 := by
    have := Nat.pow_le_pow_left h1 2
    have e : (2 * (k + 1) ^ 3) ^ 2 = 4 * (k + 1) ^ 6 := by ring
    omega
  have h3 : (k + 1) ^ 2 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : 1 ≤ (k + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  omega

/-- Where the pieces of a fresh phase sit. -/
structure FreshAt (P : Program) (F : Funs) (f prep red dom col hier ap rep lo cnt ob jst lift jpre
    jfac : ℕ) : Prop where
  entry : P.funs[f]? = some (freshBody prep F.cont lift)
  prepAt : PrepAt P prep red dom col hier ap rep lo cnt ob jst
  liftAt : LiftAt P lift dom jpre jfac

theorem pow6_le {X : ℕ} (hX : 1 ≤ X) (a p : ℕ) :
    (a * X ^ 6 + 2) ^ p ≤ (a + 2) ^ p * X ^ (6 * p) := by
  have h1 : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ hX
  have h2 : a * X ^ 6 + 2 ≤ (a + 2) * X ^ 6 := by nlinarith
  calc (a * X ^ 6 + 2) ^ p ≤ ((a + 2) * X ^ 6) ^ p := Nat.pow_le_pow_left h2 p
    _ = (a + 2) ^ p * X ^ (6 * p) := by rw [mul_pow, ← pow_mul]

/-- A constant for `Ks` that covers a fresh phase (`freshK_of`). -/
def freshConst (pst pp pf : Prim) : ℕ :=
  10 ^ 22 + 2 * (pst.c * (10 ^ 6 + 2) ^ pst.k) + liftK * 2 ^ 21 +
    pp.c * (64 * 10 ^ 6 + 2) ^ pp.k + pf.c * (64 * 10 ^ 6 + 2) ^ pf.k + 10 ^ 7

/-- **Sufficient constants for a fresh phase**: `Ks ≥ freshConst` and `ds` at least `21` and at
least six times the exponents of the three cited tasks. -/
theorem freshCost_le (pst pp pf : Prim) {d : ℕ} (hd : 21 ≤ d) (h1 : 6 * pst.k ≤ d)
    (h2 : 6 * pp.k ≤ d) (h3 : 6 * pf.k ≤ d) {X : ℕ} (hX : 1 ≤ X) :
    freshCost pst pp pf X ≤ freshConst pst pp pf * X ^ d := by
  have pw : ∀ m, m ≤ d → X ^ m ≤ X ^ d := fun m hm => Nat.pow_le_pow_right hX hm
  have q1 := pow6_le hX (10 ^ 6) pst.k
  have q2 : 10 ^ 6 * (X + 1) ^ 6 + 2 ≤ (64 * 10 ^ 6) * X ^ 6 + 2 := by
    have : (X + 1) ^ 6 ≤ (2 * X) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have e : (2 * X) ^ 6 = 64 * X ^ 6 := by ring
    omega
  have q3 : (10 ^ 6 * (X + 1) ^ 6 + 2) ^ pp.k ≤ (64 * 10 ^ 6 + 2) ^ pp.k * X ^ (6 * pp.k) :=
    (Nat.pow_le_pow_left q2 _).trans (pow6_le hX _ _)
  have q4 : (10 ^ 6 * (X + 1) ^ 6 + 2) ^ pf.k ≤ (64 * 10 ^ 6 + 2) ^ pf.k * X ^ (6 * pf.k) :=
    (Nat.pow_le_pow_left q2 _).trans (pow6_le hX _ _)
  have q5 : (X + 1) ^ 21 ≤ 2 ^ 21 * X ^ 21 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) 21
  have r1 := Nat.mul_le_mul_left pst.c (q1.trans (Nat.mul_le_mul_left _ (pw _ h1)))
  have r3 := Nat.mul_le_mul_left pp.c (q3.trans (Nat.mul_le_mul_left _ (pw _ h2)))
  have r4 := Nat.mul_le_mul_left pf.c (q4.trans (Nat.mul_le_mul_left _ (pw _ h3)))
  have r5 := Nat.mul_le_mul_left liftK (q5.trans (Nat.mul_le_mul_left _ (pw _ hd)))
  have r6 := pw 21 hd
  have r7 := pw 6 (by omega)
  unfold freshCost prepCost liftCost freshConst
  have e1 : ∀ a b : ℕ, a * (b * X ^ d) = a * b * X ^ d := fun a b => by ring
  rw [e1] at r1 r3 r4 r5
  have e2 : (10 ^ 22 + 2 * (pst.c * (10 ^ 6 + 2) ^ pst.k) + liftK * 2 ^ 21 +
      pp.c * (64 * 10 ^ 6 + 2) ^ pp.k + pf.c * (64 * 10 ^ 6 + 2) ^ pf.k + 10 ^ 7) * X ^ d =
      10 ^ 22 * X ^ d + 2 * (pst.c * (10 ^ 6 + 2) ^ pst.k * X ^ d) + liftK * 2 ^ 21 * X ^ d +
      pp.c * (64 * 10 ^ 6 + 2) ^ pp.k * X ^ d + pf.c * (64 * 10 ^ 6 + 2) ^ pf.k * X ^ d +
      10 ^ 7 * X ^ d := by ring
  rw [e2]
  have := Nat.mul_le_mul_left (10 ^ 22) r6
  have := Nat.mul_le_mul_left (10 ^ 7) r7
  omega

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

/-- The constants of `Solve` cover a fresh phase. -/
def FreshK (pst pp pf : Prim) : Prop := ∀ X : ℕ, 1 ≤ X → freshCost pst pp pf X ≤ I.Ks * X ^ I.ds

/-- `FreshK` from explicit constants (`freshCost_le`). -/
theorem freshK_of {pst pp pf : Prim} (hK : freshConst pst pp pf ≤ I.Ks) (hd : 21 ≤ I.ds)
    (h1 : 6 * pst.k ≤ I.ds) (h2 : 6 * pp.k ≤ I.ds) (h3 : 6 * pf.k ≤ I.ds) :
    I.FreshK pst pp pf := fun _ hX =>
  (freshCost_le pst pp pf hd h1 h2 h3 hX).trans (Nat.mul_le_mul_right _ hK)

/-- **A fresh phase meets its specification.** -/
theorem freshSpec (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    {f prep red dom col hier ap rep lo cnt ob jst lift jpre jfac : ℕ}
    (h : FreshAt Pg F f prep red dom col hier ap rep lo cnt ob jst lift jpre jfac)
    (hjs : Pg.prims[jst]? = some (pointwiseStabPrim hst))
    (hjp : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hjf : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (hK : I.FreshK (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac)) :
    I.FreshSpec Pg F f := by
  intro Ω C S k e c hc v hv hg hP ih
  have hsv : StateVal e c v S := hv
  have hP' : P₀.N₀ < S.size := hP
  have hsz : 0 < S.size := by omega
  have hkv := StateVal.k_le_wt hsv
  obtain ⟨gv, dv, xv, yv, hv0, rv, -, -, -, -, -, -, hveq⟩ := id hsv
  set vs := [Val.nat k, gv, dv, xv, yv, hv0, rv, boolVal S.floor, .nat S.h, .nat S.N] with hvs
  subst hveq
  refine FunAll.intro h.entry ?_
  -- 1. the fresh value
  have d0 := Det.var' (P := Pg) (env := [Val.list vs]) (i := 0) rfl
  refine EvalAll.letE (EvalAll.call_spec d0 (prep_spec hst h.prepAt hjs e c S hsz hsv)) ?_
  rintro w1 c1 ⟨cb1, ⟨⟨gs₀, hsF, labF, a, hgs₀, hl₀, hmax, hcan, rfl, hw1⟩, hcb1⟩, hc1⟩
  haveI : Finite S.dom := Finite.of_equiv _ (domEquiv e S.dom).symm
  have m3 : (Val.nat (domFin e S.dom).length).wt < (Val.list [encGroup gs₀, domCtx e S.dom,
      .nat (domFin e S.dom).length, freshVal (domFin e S.dom).length (encGroup hsF)
        (natList (cmpCodes e c S S.x)) (natList (cmpCodes e c S S.y))
        (fhierVal (encFun labF) (Nat.card (orb S.domGroup a)))]).wt := wt_le_wt_list (by simp)
  have m4 : (freshVal (domFin e S.dom).length (encGroup hsF)
        (natList (cmpCodes e c S S.x)) (natList (cmpCodes e c S S.y))
        (fhierVal (encFun labF) (Nat.card (orb S.domGroup a)))).wt < (Val.list [encGroup gs₀,
      domCtx e S.dom, .nat (domFin e S.dom).length, freshVal (domFin e S.dom).length (encGroup hsF)
        (natList (cmpCodes e c S S.x)) (natList (cmpCodes e c S S.y))
        (fhierVal (encFun labF) (Nat.card (orb S.domGroup a)))]).wt := wt_le_wt_list (by simp)
  have m1 : (encGroup gs₀).wt < (Val.list [encGroup gs₀, domCtx e S.dom,
      .nat (domFin e S.dom).length, freshVal (domFin e S.dom).length (encGroup hsF)
        (natList (cmpCodes e c S S.x)) (natList (cmpCodes e c S S.y))
        (fhierVal (encFun labF) (Nat.card (orb S.domGroup a)))]).wt := wt_le_wt_list (by simp)
  have m2 : (domCtx e S.dom).wt < (Val.list [encGroup gs₀, domCtx e S.dom,
      .nat (domFin e S.dom).length, freshVal (domFin e S.dom).length (encGroup hsF)
        (natList (cmpCodes e c S S.x)) (natList (cmpCodes e c S S.y))
        (fhierVal (encFun labF) (Nat.card (orb S.domGroup a)))]).wt := wt_le_wt_list (by simp)
  have hs_k : (domFin e S.dom).length ≤ k := length_domFin_le
  obtain ⟨hT, hH⟩ := freshHier_of_largest S.domGroup a hmax
  have hgood := good_fresh S hP' hT hH
  have hcall := ih .cont _ hgood (mlt_fresh S _) _ (domEquiv e S.dom) (freshCode e c S)
    (freshCode_injective e c S hc) _ hcan
  -- 2. the `Continue` call
  refine EvalAll.letE (EvalAll.call_spec (Det.get' (Det.var' (i := 1) rfl) (Det.nat 3)
    (vs := [encGroup gs₀, domCtx e S.dom, _, _]) rfl) hcall) ?_
  rintro u' c2 ⟨cb2, ⟨A', L', r, hL', hA', hcb2⟩, hc2⟩
  have hL'' : L' = none := hL'
  subst hL''
  -- 3. the lift
  have hA'sub : A' ⊆ (restrictHom S.G S.dom S.dom_inv).range := by
    rw [r.exact]
    intro g hg
    exact hg.1
  have hlift := lift_spec hpre hfac h.liftAt h.prepAt.domAt hjp hjf e S hgs₀ hl₀ hA' hA'sub
  refine (EvalAll.call_spec (Det.mk2 (Det.mk4 (Det.arg' (vs := vs) (j := 0) rfl)
    (Det.get' (Det.var' (i := 1) rfl) (Det.nat 2) (vs := [encGroup gs₀, domCtx e S.dom, _, _])
      rfl)
    (Det.get' (Det.var' (i := 1) rfl) (Det.nat 1) (vs := [encGroup gs₀, domCtx e S.dom, _, _])
      rfl)
    (Det.get' (Det.var' (i := 1) rfl) (Det.nat 0) (vs := [encGroup gs₀, domCtx e S.dom, _, _])
      rfl)) (Det.var' (i := 2) rfl)) hlift).mono ?_
  rintro w c3 ⟨cb3, ⟨hAns, hcb3⟩, hc3⟩
  refine ⟨S.liftAnswer A', none, Run.fresh hP' (S.freshOn_freshOf hT hH) r, rfl, by simp [Run.kind],
    hAns, ?_⟩
  have hown : I.own .solve (Run.fresh hP' (S.freshOn_freshOf hT hH) r) (Val.list vs) =
      (I.Ks : ℝ) * (((Val.list vs).wt : ℝ) + 1) ^ I.ds := by simp [own]
  have hch : I.childCost (Run.fresh hP' (S.freshOn_freshOf hT hH) r) = r.total I.work := by
    simp [childCost, Run.children, charge]
  rw [hown, hch]
  simp only [excess, reduceCtorEq, if_false, add_zero] at hcb2
  -- the weights
  set X := (Val.list vs).wt + 1 with hX
  have hkX : k + 1 ≤ X := by omega
  have k6 : (k + 1) ^ 6 ≤ X ^ 6 := Nat.pow_le_pow_left hkX 6
  have hX1 : 1 ≤ X := by omega
  have p16 : X ≤ X ^ 6 := Nat.le_self_pow (by norm_num) _
  have wu := hA'.wt_le
  have wu' : ansW (domFin e S.dom).length ≤ 400 * (k + 1) ^ 6 :=
    (ansW_le_pow _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6))
  have ww := hAns.wt_le
  have ww' := ansW_le_pow k
  have wctx := wt_liftCtx_le e S.dom hl₀
  have wl2 := wt_list2_le (liftCtx e S.dom gs₀) u'
  have hlc := liftCost_mono (preimagePrim hpre) (normalizedFactorPrim hfac) (show k ≤ X by omega)
  have eL : (Val.list [Val.nat k, Val.nat (domFin e S.dom).length, domCtx e S.dom,
    encGroup gs₀]).wt = (liftCtx e S.dom gs₀).wt := rfl
  have eL2 : (Val.list [Val.list [Val.nat k, Val.nat (domFin e S.dom).length, domCtx e S.dom,
    encGroup gs₀], u']).wt = (Val.list [liftCtx e S.dom gs₀, u']).wt := rfl
  have hnat : c1 + (c2 + c3 + w.wt + 1) + w.wt + 1 ≤ freshCost (pointwiseStabPrim hst)
      (preimagePrim hpre) (normalizedFactorPrim hfac) X + cb2 := by
    unfold freshCost
    omega
  have hKX : ((freshCost (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac)
      X : ℕ) : ℝ) ≤ (I.Ks : ℝ) * (((Val.list vs).wt : ℝ) + 1) ^ I.ds := by
    have := hK X hX1
    have e2 : ((X : ℕ) : ℝ) = ((Val.list vs).wt : ℝ) + 1 := by rw [hX]; push_cast; ring
    rw [← e2]
    exact_mod_cast this
  have hnat' : ((c1 + (c2 + c3 + w.wt + 1) + w.wt + 1 : ℕ) : ℝ) ≤
      ((freshCost (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac) X : ℕ) : ℝ)
        + (cb2 : ℝ) := by exact_mod_cast hnat
  push_cast at hnat' ⊢
  linarith

end Iface

/-- **A fresh phase with the concrete interface** `Rest.iface`: its constants cover the fresh
phase when `solveK ≥ freshConst` and `solveD` is at least `21` and six times the exponents of
the three cited tasks. -/
theorem Rest.freshK (R : Rest) {pst pp pf : Prim} (hK : freshConst pst pp pf ≤ R.solveK)
    (hd : 21 ≤ R.solveD) (h1 : 6 * pst.k ≤ R.solveD) (h2 : 6 * pp.k ≤ R.solveD)
    (h3 : 6 * pf.k ≤ R.solveD) : R.iface.FreshK pst pp pf :=
  R.iface.freshK_of (hK.trans (Nat.le_add_left _ _)) (hd.trans (le_max_right _ _))
    (h1.trans (le_max_right _ _)) (h2.trans (le_max_right _ _)) (h3.trans (le_max_right _ _))

end GI.Impl
