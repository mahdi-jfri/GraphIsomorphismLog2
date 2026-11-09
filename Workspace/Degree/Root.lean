module

public import Workspace.Degree.RootBound
public import Workspace.Degree.RootProg

@[expose] public section

/-!
# The root

`DegCode Pg D` collects the code that the recursion needs in the program `Pg` for the degree `D`:
the four new functions with their placements, for every root bound `Nm`, the general solver, and the
root (`RootCode`). `degree_root` is the string theorem of the paper at the root: on a state value of
a state of `Γ̂_D` on `k` positions, the root returns a canonical answer at cost at most
`exp(c log(k + 2) log(D + 2)) K (wt v + 1)^m`, with constants that do not depend on `Pg` or `D`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm Real
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership GroupOrder MinimalBlocks)

/-- **The code of the root.** -/
structure RootCode (Pg : Program) (D : ℕ) (hst : PointwiseStab) (hpre : Preimage)
    (hfac : NormalizedFactor) where
  f : ℕ
  fs : ℕ
  rf : ℕ
  contD : ℕ
  dE : Expr
  prep : ℕ
  red : ℕ
  dom : ℕ
  col : ℕ
  hier : ℕ
  ap : ℕ
  rep : ℕ
  lo : ℕ
  cnt : ℕ
  ob : ℕ
  jst : ℕ
  lift : ℕ
  jpre : ℕ
  jfac : ℕ
  htop : Pg.funs[f]? = some (rootTopBody fs rf P₀.N₀ dE)
  hdE : ∀ env, Det Pg env dE (.nat D) (D + 3)
  hrf : Pg.funs[rf]? = some (rootFreshBody prep contD lift dE)
  hp : PrepAt Pg prep red dom col hier ap rep lo cnt ob jst
  hjs : Pg.prims[jst]? = some (pointwiseStabPrim hst)
  hl : LiftAt Pg lift dom jpre jfac
  hjp : Pg.prims[jpre]? = some (preimagePrim hpre)
  hjf : Pg.prims[jfac]? = some (normalizedFactorPrim hfac)

/-- The context of the recursion for the root bound `Nm`. -/
def DCtx (Pg : Program) (I : Iface) (contD transD giantD D Nm : ℕ) : Ctx :=
  ⟨Pg, I, contD, transD, giantD, D, Nm⟩

/-- **The code of the recursion** in `Pg` for the degree `D`. -/
structure DegCode (Pg : Program) (D : ℕ) (hst : PointwiseStab) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder) (h : JohnsonRecognition)
    (hp : Preimage) (hm : Membership) (c₁ c₂ : ℝ) (Xw : ℕ → ℕ) (a : ℝ) (Kg dg : ℕ) where
  I : Iface
  contD : ℕ
  transD : ℕ
  giantD : ℕ
  F₀ : Funs
  F : Funs
  fs : ℕ
  cd : ∀ Nm, ContCode (DCtx Pg I contD transD giantD D Nm) F
  rc : ∀ Nm, ResetCode (DCtx Pg I contD transD giantD D Nm) (cd Nm).frs hst hpre hfac
  ht : ∀ Nm, TransCode (DCtx Pg I contD transD giantD D Nm) F hmb hO h hp hst hm
  gc : ∀ Nm, GiantCode (DCtx Pg I contD transD giantD D Nm) F₀ F hpre hfac hm (abKrC hst) Xw
  solver : GenSolverAt Pg fs a Kg dg
  hf₁ : ∀ Nm, (cd Nm).fs = fs
  hf₂ : ∀ Nm, (ht Nm).fs = fs
  hf₃ : ∀ Nm, (gc Nm).fs = fs
  hE : ∀ Nm, (ht Nm).E = caseE c₁ c₂ P₀.q₀
  hlab : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (lv : Val)
    (L : SuppliedLabels S), LabValStd e S lv L → I.LabVal e S lv L
  hlabW : ∀ k N, labWStd k N ≤ I.labW k N
  root : RootCode Pg D hst hpre hfac
  root_fs : root.fs = fs
  root_cont : root.contD = contD

/-- The cost of the root in raw form. -/
noncomputable def rootRaw (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    (cr a : ℝ) (Kg dg D k W : ℕ) : ℝ :=
  exp (cr * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) +
    (rootOwn (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac) (W + 1) D : ℕ) +
    (exp (a * Real.log ((k : ℝ) + 2) * (Real.log ((P₀.N₀ : ℝ) + 2) + Real.log ((D : ℝ) + 2))) +
      Kg * ((W : ℝ) + 1) ^ dg) +
    ((20 * (W + P₀.N₀ + D + 20) + 3 * (ansW k + 1) : ℕ) : ℝ)

/-- The solver bound in a root that calls the solver. -/
theorem solver_le_root {a : ℝ} (ha : 0 ≤ a) {s k D : ℕ} (hs : s ≤ k) (hk : ¬ (P₀.N₀ < k ∧ D < k)) :
    exp (a * Real.log ((s : ℝ) + 2) ^ 2) ≤
      exp (a * Real.log ((k : ℝ) + 2) * (Real.log ((P₀.N₀ : ℝ) + 2) + Real.log ((D : ℝ) + 2))) := by
  refine exp_le_exp.2 ?_
  have hs' : (s : ℝ) ≤ k := by exact_mod_cast hs
  have l0 : 0 ≤ Real.log ((s : ℝ) + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    linarith)
  have l1 : Real.log ((s : ℝ) + 2) ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have lN : 0 ≤ Real.log ((P₀.N₀ : ℝ) + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ P₀.N₀ := Nat.cast_nonneg _
    linarith)
  have lD : 0 ≤ Real.log ((D : ℝ) + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    linarith)
  have l2 : Real.log ((s : ℝ) + 2) ≤ Real.log ((P₀.N₀ : ℝ) + 2) + Real.log ((D : ℝ) + 2) := by
    rcases not_and_or.1 hk with h | h
    · have : (s : ℝ) ≤ P₀.N₀ := by exact_mod_cast hs.trans (not_lt.1 h)
      have := Real.log_le_log (by positivity) (by linarith : (s : ℝ) + 2 ≤ (P₀.N₀ : ℝ) + 2)
      linarith
    · have : (s : ℝ) ≤ D := by exact_mod_cast hs.trans (not_lt.1 h)
      have := Real.log_le_log (by positivity) (by linarith : (s : ℝ) + 2 ≤ (D : ℝ) + 2)
      linarith
  have := mul_le_mul l1 l2 l0 (by linarith)
  have e : a * Real.log ((s : ℝ) + 2) ^ 2 = a * (Real.log ((s : ℝ) + 2) * Real.log ((s : ℝ) + 2)) := by
    ring
  rw [e, mul_assoc]
  exact mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left l2 l0) (by nlinarith)) ha

/-- **The root, in raw form.** -/
theorem degree_root_raw (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    (hmb : MinimalBlocks) (hO : GroupOrder) (h : JohnsonRecognition) (hp : Preimage)
    (hm : Membership) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hA : AltAt c₁ c₂ P₀.q₀)
    (Kg dg : ℕ) {a : ℝ} (ha : 0 ≤ a) {Xw : ℕ → ℕ} (hXw : PBU fun _ W _ => Xw W) :
    ∃ cr : ℝ, 0 ≤ cr ∧ ∀ (Pg : Program) (D : ℕ)
      (dc : DegCode Pg D hst hpre hfac hmb hO h hp hm c₁ c₂ Xw a Kg dg), 6 ≤ D →
      ∀ {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
        Function.Injective c → GammaHat D S.G → S.size = k → ∀ v : Val, StateVal e c v S →
        FunAll Pg dc.root.f v fun u cost => AnsC e u S.answer ∧
          (cost : ℝ) ≤ rootRaw hst hpre hfac cr a Kg dg D k v.wt := by
  obtain ⟨ks, Cm, em, hka, -, hcb⟩ := calls_bound hst hpre hfac hmb hO h hp hm hc₁ hc₂ hA Kg dg ha hXw
  obtain ⟨cr, hcr, hrb⟩ := root_bound ks Cm em Kg dg
  refine ⟨cr, hcr, fun Pg D dc hD6 {Ω C} _ S k e c hc hG hSk v hsv => ?_⟩
  obtain ⟨gv, dv, xv, yv, hvIn, rv, -, -, -, -, -, -, hveq⟩ := id hsv
  have hkv := StateVal.k_le_wt hsv
  have hsk : S.size ≤ k := hSk.le
  set Bnd := rootRaw hst hpre hfac cr a Kg dg D k v.wt - ((20 * (v.wt + P₀.N₀ + D + 20) +
    3 * (ansW k + 1) : ℕ) : ℝ) with hBnd
  have hroot := rootTop_spec dc.root.htop dc.root.hdE (k := k)
    (vs := [.nat k, gv, dv, xv, yv, hvIn, rv, boolVal S.floor, .nat S.h, .nat S.N]) rfl
    (Post := fun u cost => AnsC e u S.answer ∧ (cost : ℝ) ≤ Bnd) ?_ ?_
  · rw [← hveq] at hroot
    refine hroot.mono fun u cost ⟨c₀, ⟨hA', hc₀⟩, hcost⟩ => ⟨hA', ?_⟩
    have hu := hA'.wt_le
    have h1 : (cost : ℝ) ≤ (c₀ : ℝ) + ((20 * (v.wt + P₀.N₀ + D + 20) + 3 * (ansW k + 1) : ℕ) : ℝ) := by
      have : cost ≤ c₀ + (20 * (v.wt + P₀.N₀ + D + 20) + 3 * (ansW k + 1)) := by
        omega
      exact_mod_cast this
    rw [hBnd] at hc₀
    linarith
  · -- the fresh phase
    intro hN hDk
    rw [← hveq]
    have hfr := rootFresh_spec hst hpre hfac (b := exp (cr * Real.log ((k : ℝ) + 2) *
      Real.log ((D : ℝ) + 2))) dc.root.hrf dc.root.hdE dc.root.hp dc.root.hjs dc.root.hl
      dc.root.hjp dc.root.hjf e c S hsv (by omega) ?_
    · refine hfr.mono fun u cost ⟨hA', hc'⟩ => ⟨hA', ?_⟩
      rw [hBnd]
      unfold rootRaw
      have e1 := exp_pos (a * Real.log ((k : ℝ) + 2) * (Real.log ((P₀.N₀ : ℝ) + 2) +
        Real.log ((D : ℝ) + 2)))
      have e2 : (0 : ℝ) ≤ Kg * ((v.wt : ℝ) + 1) ^ dg := by positivity
      linarith
    · intro x hmax val hcan
      set X := DCtx Pg dc.I dc.contD dc.transD dc.giantD D k
      have hspec := hcb X dc.F₀ dc.F dc.fs (dc.cd k) (dc.rc k) (dc.ht k) (dc.gc k) dc.solver
        (dc.hf₁ k) (dc.hf₂ k) (dc.hf₃ k) (dc.hE k) hD6 hDk.le dc.hlab dc.hlabW
        ⟨S.dom, C, rootState S D x, false⟩
        ⟨rootState_dGood S D x hG hmax (by omega) hsk,
          (rootState_dGood S D x hG hmax (by omega) hsk).good⟩
        _ (domEquiv e S.dom) (freshCode e c S) (freshCode_injective e c S hc) val
        ⟨hcan, fun h => by cases h⟩
      have hb := hrb S x D k hD6 hDk.le hsk
      rw [hka] at hb
      rw [dc.root_cont]
      exact hspec.mono fun u cost ⟨hA', hc'⟩ => ⟨hA', hc'.trans hb⟩
  · -- the general solver
    intro hk
    rw [← hveq, dc.root_fs]
    refine (dc.solver S k e c hc v hsv).mono fun u cost ⟨hA', hc'⟩ => ⟨hA', ?_⟩
    rw [hBnd]
    unfold rootRaw
    have e1 := solver_le_root ha hsk hk
    have e2 := exp_pos (cr * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2))
    have e3 : (0 : ℝ) ≤ ((rootOwn (pointwiseStabPrim hst) (preimagePrim hpre)
      (normalizedFactorPrim hfac) (v.wt + 1) D : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith

/-- The polynomial part of the root. -/
noncomputable def rootPol (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    (Kg dg k W : ℕ) : ℕ :=
  prepCost (pointwiseStabPrim hst) (W + 1) +
    liftCost (preimagePrim hpre) (normalizedFactorPrim hfac) (W + 1) +
    10 ^ 4 * (resetY (W + 1) + 100) + Kg * (W + 1) ^ dg + 20 * (W + P₀.N₀ + 20) + 3 * (ansW k + 1)

theorem rootPol_pbu (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor) (Kg dg : ℕ) :
    PBU fun k W _ => rootPol hst hpre hfac Kg dg k W := by
  unfold rootPol prepCost liftCost resetY ansW groupW
  norm_poly

/-- **The final shape** of the bound at the root. -/
theorem rootRaw_le (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    {cr a : ℝ} (hcr : 0 ≤ cr) (ha : 0 ≤ a) (Kg dg : ℕ) :
    ∃ (C : ℝ) (K m : ℕ), 0 ≤ C ∧ ∀ D k W : ℕ, 6 ≤ D → k ≤ W →
      rootRaw hst hpre hfac cr a Kg dg D k W ≤
        exp (C * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) * K * ((W : ℝ) + 1) ^ m := by
  obtain ⟨Cp, mp, hpol⟩ := rootPol_pbu hst hpre hfac Kg dg
  set lN := Real.log ((P₀.N₀ : ℝ) + 2)
  have hlN : 0 ≤ lN := Real.log_nonneg (by
    have : (0 : ℝ) ≤ P₀.N₀ := Nat.cast_nonneg _
    linarith)
  refine ⟨cr + a * (lN / 2 + 1) + 2, 10 ^ 5 + 2 + Cp * 2 ^ mp, mp, by positivity,
    fun D k W hD hkW => ?_⟩
  set x := Real.log ((k : ℝ) + 2)
  set y := Real.log ((D : ℝ) + 2)
  have hy : 2 ≤ y := two_le_log_add_two hD
  have hx : 1 / 2 ≤ x := by
    have : Real.log 2 ≤ x := Real.log_le_log (by norm_num) (by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith)
    have := log_two_gt_half
    linarith
  set t := x * y with ht
  have ht1 : 1 ≤ t := by nlinarith
  set C := cr + a * (lN / 2 + 1) + 2
  have hCt : 0 ≤ C * t := by positivity
  have eC : ∀ b : ℝ, b * x * y = b * t := fun b => by simp only [t]; ring
  -- the exponential terms
  have ht0 : 0 ≤ t := by linarith
  have hCe : C * t = cr * t + a * (lN / 2) * t + a * t + 2 * t := by simp only [C]; ring
  have hat : 0 ≤ a * (lN / 2) * t := by positivity
  have hat' : 0 ≤ a * t := by positivity
  have hcrt : 0 ≤ cr * t := by positivity
  have E1 : exp (cr * x * y) ≤ exp (C * t) := by
    rw [eC]; exact exp_le_exp.2 (by linarith)
  have E2 : exp (a * x * (lN + y)) ≤ exp (C * t) := by
    refine exp_le_exp.2 ?_
    have h1 : x * lN ≤ lN / 2 * t := by
      have hx0 : 0 ≤ x := by linarith
      have := mul_nonneg (mul_nonneg hx0 hlN) (by linarith : (0 : ℝ) ≤ y - 2)
      have e : lN / 2 * t - x * lN = x * lN * (y - 2) / 2 := by simp only [t]; ring
      linarith
    have h2 : a * x * (lN + y) = a * (x * lN) + a * t := by simp only [t]; ring
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 ha
    have e : a * (lN / 2 * t) = a * (lN / 2) * t := by ring
    linarith
  have E3 : (D : ℝ) ≤ exp (C * t) := by
    have h1 : (D : ℝ) + 2 = exp y := (Real.exp_log (by positivity)).symm
    have hyt : y ≤ 2 * t := by
      have := mul_le_mul_of_nonneg_right hx (by linarith : (0 : ℝ) ≤ y)
      simp only [t]; linarith
    have h2 : exp y ≤ exp (C * t) := exp_le_exp.2 (by linarith)
    linarith
  have E4 : (1 : ℝ) ≤ exp (C * t) := Real.one_le_exp hCt
  -- the polynomial terms
  have P1 : rootOwn (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac) (W + 1) D +
      (20 * (W + P₀.N₀ + D + 20) + 3 * (ansW k + 1)) + Kg * (W + 1) ^ dg ≤
      rootPol hst hpre hfac Kg dg k W + 10 ^ 4 * D + 20 * D := by
    unfold rootOwn rootPol
    ring_nf
    omega
  have P2 : rootPol hst hpre hfac Kg dg k W ≤ Cp * 2 ^ mp * (W + 1) ^ mp := by
    have h := hpol k W 0
    unfold PB at h
    have h2 : W + 0 + k + 2 ≤ 2 * (W + 1) := by omega
    calc rootPol hst hpre hfac Kg dg k W ≤ Cp * (W + 0 + k + 2) ^ mp := h
      _ ≤ Cp * (2 * (W + 1)) ^ mp := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 mp)
      _ = Cp * 2 ^ mp * (W + 1) ^ mp := by rw [mul_pow]; ring
  have P3 : ((rootOwn (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac)
      (W + 1) D : ℕ) : ℝ) + ((20 * (W + P₀.N₀ + D + 20) + 3 * (ansW k + 1) : ℕ) : ℝ) +
      (Kg : ℝ) * ((W : ℝ) + 1) ^ dg ≤ (Cp * 2 ^ mp : ℕ) * ((W : ℝ) + 1) ^ mp + (10 ^ 4 + 20) * D := by
    have := P1.trans (Nat.add_le_add_right (Nat.add_le_add_right P2 _) _)
    have h' : ((rootOwn (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac)
        (W + 1) D + (20 * (W + P₀.N₀ + D + 20) + 3 * (ansW k + 1)) + Kg * (W + 1) ^ dg : ℕ) : ℝ) ≤
        ((Cp * 2 ^ mp * (W + 1) ^ mp + 10 ^ 4 * D + 20 * D : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h' ⊢
    linarith
  have hW1 : (1 : ℝ) ≤ ((W : ℝ) + 1) ^ mp := one_le_pow₀ (by
    have : (0 : ℝ) ≤ W := Nat.cast_nonneg _
    linarith)
  unfold rootRaw
  rw [show cr * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2) = cr * x * y from rfl,
    show a * Real.log ((k : ℝ) + 2) * (Real.log ((P₀.N₀ : ℝ) + 2) + Real.log ((D : ℝ) + 2)) =
      a * x * (lN + y) from rfl,
    show C * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2) = C * t by rw [ht]; ring]
  have hK : ((10 ^ 5 + 2 + Cp * 2 ^ mp : ℕ) : ℝ) = 10 ^ 5 + 2 + ((Cp * 2 ^ mp : ℕ) : ℝ) := by
    push_cast; ring
  rw [hK]
  have hP0 : (0 : ℝ) ≤ ((Cp * 2 ^ mp : ℕ) : ℝ) := Nat.cast_nonneg _
  have f1 : ((Cp * 2 ^ mp : ℕ) : ℝ) * ((W : ℝ) + 1) ^ mp ≤
      exp (C * t) * ((Cp * 2 ^ mp : ℕ) : ℝ) * ((W : ℝ) + 1) ^ mp := by
    have := mul_le_mul_of_nonneg_right E4 (mul_nonneg hP0 (by positivity : (0 : ℝ) ≤ ((W : ℝ) + 1) ^ mp))
    linarith
  have f2 : exp (C * t) * (10 ^ 5 + 2) ≤ exp (C * t) * (10 ^ 5 + 2) * ((W : ℝ) + 1) ^ mp := by
    have := exp_pos (C * t)
    nlinarith
  nlinarith

/-- **The string theorem of the paper at the root.** -/
theorem degree_root (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    (hmb : MinimalBlocks) (hO : GroupOrder) (h : JohnsonRecognition) (hp : Preimage)
    (hm : Membership) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hA : AltAt c₁ c₂ P₀.q₀)
    (Kg dg : ℕ) {a : ℝ} (ha : 0 ≤ a) {Xw : ℕ → ℕ} (hXw : PBU fun _ W _ => Xw W) :
    ∃ (C : ℝ) (K m : ℕ), 0 ≤ C ∧ ∀ (Pg : Program) (D : ℕ)
      (dc : DegCode Pg D hst hpre hfac hmb hO h hp hm c₁ c₂ Xw a Kg dg), 6 ≤ D →
      ∀ {Ω C' : Type} [Finite Ω] (S : State Ω C') (k : ℕ) (e : Ω ≃ Fin k) (c : C' → ℕ),
        Function.Injective c → GammaHat D S.G → S.size = k → ∀ v : Val, StateVal e c v S →
        FunAll Pg dc.root.f v fun u cost => AnsC e u S.answer ∧
          (cost : ℝ) ≤ exp (C * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) * K *
            ((v.wt : ℝ) + 1) ^ m := by
  obtain ⟨cr, hcr, hraw⟩ := degree_root_raw hst hpre hfac hmb hO h hp hm hc₁ hc₂ hA Kg dg ha hXw
  obtain ⟨C, K, m, hC, hle⟩ := rootRaw_le hst hpre hfac hcr ha Kg dg
  refine ⟨C, K, m, hC, fun Pg D dc hD {Ω C'} _ S k e c hc hG hSk v hsv => ?_⟩
  have hkv := StateVal.k_le_wt hsv
  exact (hraw Pg D dc hD S k e c hc hG hSk v hsv).mono fun u cost ⟨hA', hc'⟩ =>
    ⟨hA', hc'.trans (hle D k v.wt hD (by omega))⟩

end GI.Degree
