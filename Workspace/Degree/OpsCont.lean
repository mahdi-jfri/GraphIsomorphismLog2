module

public import Workspace.Degree.ContD
public import Workspace.Degree.OrbitD
public import Workspace.Degree.ResetProg
public import Workspace.Degree.Spine
public import Workspace.Degree.Children

@[expose] public section

/-!
# The operations of `contD`

The three operations of `Ops` (`Degree/Spine.lean`) that `contD` runs itself: the general solver
on a small state, the orbit chain, and the reset.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm Real
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor)

variable {Ω C : Type}

namespace Ctx

variable (X : Ctx)

/-- The bound on the weight of a state value along the recursion. -/
def W₀ : ℕ := 10 ^ 4 * (X.Nm + 2) ^ 6

variable {X}

theorem wt_le_W₀ {k : ℕ} {S : State Ω C} {e : Ω ≃ Fin k} {c : C → ℕ} {v : Val}
    (hS : DGood X.D X.Nm S) (hv : Canon e c v S) : v.wt ≤ X.W₀ := by
  have h3 := hv.wt_le_poly
  have h4 : (S.N + 2) ^ 6 ≤ (X.Nm + 2) ^ 6 := Nat.pow_le_pow_left (by have := hS.N_le; omega) 6
  unfold W₀
  omega

theorem k_le_Nm {k : ℕ} {S : State Ω C} {e : Ω ≃ Fin k} {c : C → ℕ} {v : Val}
    (hS : DGood X.D X.Nm S) (hv : Canon e c v S) : k ≤ X.Nm :=
  hv.fits.trans hS.N_le

/-- A call on a child below `μ`, from the bound `B`. -/
theorem below_call {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} {B : Child → ℝ} (hB : X.Below μ B)
    {k : ℕ} {e : Ω ≃ Fin k} {cc : C → ℕ} (hcc : Function.Injective cc) {T : State Ω C}
    (hd : DGood X.D X.Nm T) (hg : GI.Algorithm.Good P₀ .cont T) (hlt : MLt (measure P₀ .cont T) μ) {val : Val}
    (hv : Canon e cc val T) :
    FunAll X.Pg X.contD val (ChildPost (fun T => B ⟨Ω, C, T, false⟩) T e) :=
  hB ⟨Ω, C, T, false⟩ ⟨hd, hg⟩ hlt k e cc hcc val ⟨hv, fun h => by cases h⟩

end Ctx

/-- The code of `contD`. -/
structure ContCode (X : Ctx) (F : Funs) where
  hF : F.cont = X.contD
  bs : ℕ
  brho : ℕ
  g : ℕ
  blog : ℕ
  bl : ℕ
  bm : ℕ
  fs : ℕ
  forb : ℕ
  frs : ℕ
  hcont : X.Pg.funs[X.contD]? = some (contE bs brho bl bm P₀.N₀ fs forb frs)
  hbs : X.Pg.HasAt bs (sizeFuns bs)
  hbr : X.Pg.HasAt brho (foldlFuns brho g)
  hg : X.Pg.funs[g]? = some (rhoStep blog)
  hl : X.Pg.HasAt blog (log2Funs blog)
  hlo : X.Pg.HasAt bl (loFuns bl)
  hmax : X.Pg.HasAt bm (maxFuns bm)
  /-- The orbit chain. -/
  obl : ℕ
  obs : ℕ
  obg : ℕ
  obc : ℕ
  horb : X.Pg.funs[forb]? = some (orbitBody F obl obs obg obc)
  holo : X.Pg.HasAt obl (loFuns obl)
  hosp : X.Pg.HasAt obs (splitFuns obs)
  hoga : X.Pg.HasAt obg (gatherFuns obg)
  hoco : X.Pg.HasAt obc (composeFuns obc)

variable {X : Ctx} {ks : Cst} {K₁ : ℝ} {F : Funs}

/-- The own cost of `contD` at a call, including the weight of the answer. -/
noncomputable def contPart (k N W : ℕ) : ℕ := contOwn P₀.N₀ k N W + 8 * (ansW k + 2)

/-- **The general solver on a small state.** -/
theorem ops_base (cd : ContCode X F) {a : ℝ} {Kg dg : ℕ}
    (hgs : ∀ {Ω C : Type} (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
      Function.Injective c → ∀ v : Val, StateVal e c v S →
        FunAll X.Pg cd.fs v fun u cost => AnsC e u S.answer ∧
          (cost : ℝ) ≤ Real.exp (a * Real.log ((S.size : ℝ) + 2) ^ 2) + Kg * ((v.wt : ℝ) + 1) ^ dg)
    (hK : ∀ k N W, k ≤ X.Nm → N ≤ X.Nm → W ≤ X.W₀ →
      (contPart k N W : ℝ) + Kg * ((W : ℝ) + 1) ^ dg ≤ K₁)
    (T : State Ω C) (hd : DGood X.D X.Nm T) (hs : Ctx.IsSmall T) :
    X.Runs X.contD .cont T (measure P₀ .cont T)
      (K₁ + exp (a * Real.log ((T.size : ℝ) + 2) ^ 2)) (· = []) := by
  intro B _ k e cc hcc v hv
  have hcan : Canon e cc v T := hv.1
  refine (contD_spec cd.hcont cd.hbs cd.hbr cd.hg cd.hl cd.hlo cd.hmax hcan
    (fun _ => hgs T k e cc hcc v hcan.stateVal) (fun h => absurd hs h)
    (fun h => absurd hs h)).mono ?_
  rintro u cost ⟨c₀, ⟨ha, hc⟩, hle⟩
  refine ⟨ha, [], rfl, ?_⟩
  simp only [List.map_nil, List.sum_nil, add_zero]
  have hk := hK k T.N v.wt (Ctx.k_le_Nm hd hcan) hd.N_le (Ctx.wt_le_W₀ hd hcan)
  have hu := ha.wt_le
  have h2 : cost ≤ c₀ + contPart k T.N v.wt := by unfold contPart; omega
  have h3 : (cost : ℝ) ≤ c₀ + contPart k T.N v.wt := by exact_mod_cast h2
  linarith

/-- The first child of the orbit chain. -/
theorem first_facts {T : State Ω C} (hd : DGood X.D X.Nm T) (hnt : ¬ T.Transitive) {D₁ : Set Ω}
    (hD₁ : T.LargestOrbit D₁) :
    let T₁ := firstChild T hD₁
    DGood X.D X.Nm T₁ ∧ MLt (measure P₀ .cont T₁) (measure P₀ .cont T) ∧
      T₁.dres.Le T.dres ∧ 1 ≤ T₁.size ∧ T₁.size < T.size := by
  intro T₁
  have hfin : Finite Ω := hd.finite
  have hG : T₁.G = T.G := State.inherit_G _ _ _ _ _ _
  have hdom : T₁.dom = D₁ := State.inherit_dom _ _ _ _ _ _
  have hh : T₁.hier = T.hier := State.inherit_hier _ _ _ _ _ _
  have hN : T₁.N = T.N := State.inherit_N _ _ _ _ _ _
  have hlt : T₁.size < T.size := LargestOrbit.size_lt hnt hD₁ hdom
  obtain ⟨h1, h2⟩ := first_parts T hD₁
  have hb : T₁.rows = none ∧ T₁.floor = false ∧ T₁.h = 2 := by
    by_cases hc : T.ColsSplit D₁
    · obtain ⟨a, b, c⟩ := h1 hc
      exact ⟨a.trans hd.rows, b.trans hd.floor, c.trans hd.h⟩
    · exact h2 hc
  have hinv : T₁.HierInv := by
    show HierInv T₁.G T₁.dom T₁.hier
    rw [hG, hdom, hh]
    exact HierInv.mono hd.hier le_rfl hD₁.subset
  have hsz := hd.size_le
  refine ⟨hd.child hN (by omega) hG.le hinv hb.1 hb.2.1 hb.2.2 (by rw [hh]; exact hd.caps), ?_, ?_,
    ?_, hlt⟩
  · rw [mlt_iff]
    simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false,
      false_or]
    omega
  · exact le_child hG.le (hdom ▸ hD₁.subset) (by rw [hh]) (by rw [hh])
  · obtain ⟨x, hx⟩ := hD₁.nonempty
    have : Nonempty T₁.dom := ⟨⟨x, hdom ▸ hx⟩⟩
    exact Nat.card_pos

/-- The second child of the orbit chain. -/
theorem second_facts {T : State Ω C} (hd : DGood X.D X.Nm T) (hnt : ¬ T.Transitive) {D₁ : Set Ω}
    (hD₁ : T.LargestOrbit D₁) (t : Perm Ω) :
    let T₂ := secondChild T hD₁ t
    DGood X.D X.Nm T₂ ∧ MLt (measure P₀ .cont T₂) (measure P₀ .cont T) ∧
      T₂.dres.Le T.dres ∧ 1 ≤ T₂.size ∧ T₂.size < T.size ∧
      (firstChild T hD₁).size + T₂.size ≤ T.size := by
  intro T₂
  have hfin : Finite Ω := hd.finite
  have hG : T₂.G ≤ T.G := autGroup_le _ _ hD₁.invariant _
  have hdom : T₂.dom = T.dom \ D₁ := rfl
  have hh : T₂.hier = T.hier := rfl
  have hN : T₂.N = T.N := rfl
  have hs := orbitChain_sizes (S₁ := firstChild T hD₁) (S₂ := T₂) hnt hD₁
    (State.inherit_dom _ _ _ _ _ _) rfl
  have hinv : T₂.HierInv := by
    show HierInv T₂.G T₂.dom T₂.hier
    exact HierInv.mono hd.hier hG Set.diff_subset
  have hsz := hd.size_le
  have hb : T₂.rows = none ∧ T₂.floor = false ∧ T₂.h = 2 := ⟨rfl, rfl, rfl⟩
  obtain ⟨hs1, hs2, hs3⟩ := hs
  refine ⟨hd.child hN (by omega) hG hinv hb.1 hb.2.1 hb.2.2 (by rw [hh]; exact hd.caps), ?_, ?_,
    hs3, by omega, hs1.le⟩
  · rw [mlt_iff]
    simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false,
      false_or]
    omega
  · exact le_child hG Set.diff_subset (by rw [hh]) (by rw [hh])

theorem size_pos_of_not_small {T : State Ω C} (hs : ¬ Ctx.IsSmall T) : T.dom.Nonempty := by
  have h1 : 0 < T.size := by
    unfold Ctx.IsSmall at hs
    omega
  obtain ⟨⟨x⟩, -⟩ := Nat.card_pos_iff.1 h1
  exact ⟨x.1, x.2⟩

/-- **The orbit chain.** -/
theorem ops_orbit (cd : ContCode X F)
    (hK : ∀ k N W, k ≤ X.Nm → N ≤ X.Nm → W ≤ X.W₀ →
      (contPart k N W : ℝ) + (orbK * (X.W₀ + ansW k + 1) ^ 15 : ℕ) ≤ K₁)
    (T : State Ω C) (hd : DGood X.D X.Nm T) (hs : ¬ Ctx.IsSmall T) (hnt : ¬ T.Transitive) :
    X.Runs X.contD .cont T (measure P₀ .cont T) K₁ (Ctx.OrbitShape T) := by
  intro B hB k e cc hcc v hv
  have hcan : Canon e cc v T := hv.1
  have hfin : Finite Ω := hd.finite
  have hne := size_pos_of_not_small hs
  have hgood : ∀ {T' : State Ω C}, DGood X.D X.Nm T' → GI.Algorithm.Good P₀ .cont T' := fun h => h.good
  have horb := orbit_specD (Pg := X.Pg) cd.horb cd.holo cd.hosp cd.hoga cd.hoco
    (fun T' => B ⟨Ω, C, T', false⟩) e cc hcan hne hnt
    (fun D₁ hD₁ val hval => by
      obtain ⟨h1, h2, -⟩ := first_facts hd hnt hD₁
      rw [cd.hF]
      exact Ctx.below_call hB hcc h1 h1.good h2 hval)
    (fun D₁ hD₁ t val hval => by
      obtain ⟨h1, h2, -⟩ := second_facts hd hnt hD₁ t
      rw [cd.hF]
      exact Ctx.below_call hB hcc h1 h1.good h2 hval)
  refine (contD_spec cd.hcont cd.hbs cd.hbr cd.hg cd.hl cd.hlo cd.hmax hcan
    (fun h => absurd h hs) (fun _ _ => horb) (fun _ h => absurd h hnt)).mono ?_
  rintro u cost ⟨c₀, ⟨ha, D₁, hD₁, L, hL, hc⟩, hle⟩
  refine ⟨ha, L.map fun T' => ⟨Ω, C, T', false⟩, ?_, ?_⟩
  · obtain ⟨f1, f2, f3, f4, f5⟩ := first_facts hd hnt hD₁
    rcases hL with rfl | ⟨t, rfl⟩
    · refine ⟨by simp, ?_, ?_⟩
      · have e : (firstChild T hD₁).dres.s = (firstChild T hD₁).size := rfl
        simpa [Child.res, e] using f5.le
      · intro c hc'
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc'
        subst hc'
        exact ⟨rfl, f3, f4, f5⟩
    · obtain ⟨s1, s2, s3, s4, s5, s6⟩ := second_facts hd hnt hD₁ t
      refine ⟨by simp, ?_, ?_⟩
      · have e : (firstChild T hD₁).dres.s = (firstChild T hD₁).size := rfl
        have e' : (secondChild T hD₁ t).dres.s = (secondChild T hD₁ t).size := rfl
        simpa [Child.res, e, e'] using s6
      · intro c hc'
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | rfl
        · exact ⟨rfl, f3, f4, f5⟩
        · exact ⟨rfl, s3, s4, s5⟩
  · rw [List.map_map]
    have hk := hK k T.N v.wt (Ctx.k_le_Nm hd hcan) hd.N_le (Ctx.wt_le_W₀ hd hcan)
    have hu := ha.wt_le
    have h2 : cost ≤ c₀ + contPart k T.N v.wt := by unfold contPart; omega
    have h3 : (cost : ℝ) ≤ c₀ + contPart k T.N v.wt := by exact_mod_cast h2
    have h4 : stateW k T ≤ X.W₀ := by
      have e1 := stateW_le_of_small hcan.fits hcan.small'
      have e2 : (T.N + 2) ^ 6 ≤ (X.Nm + 2) ^ 6 :=
        Nat.pow_le_pow_left (by have := hd.N_le; omega) 6
      unfold Ctx.W₀
      omega
    have h5 : orbK * (stateW k T + ansW k + 1) ^ 15 ≤ orbK * (X.W₀ + ansW k + 1) ^ 15 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 15)
    have h6 : ((orbK * (stateW k T + ansW k + 1) ^ 15 : ℕ) : ℝ) ≤
        ((orbK * (X.W₀ + ansW k + 1) ^ 15 : ℕ) : ℝ) := by exact_mod_cast h5
    change (cost : ℝ) ≤ K₁ + (L.map fun T' => B ⟨Ω, C, T', false⟩).sum
    linarith

/-- The code of the reset. -/
structure ResetCode (X : Ctx) (frs : ℕ) (hst : PointwiseStab) (hpre : Preimage)
    (hfac : NormalizedFactor) where
  prep : ℕ
  mh : ℕ
  mi : ℕ
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
  hb : X.Pg.funs[frs]? = some (resetBody prep mh X.transD lift)
  hp : PrepAt X.Pg prep red dom col hier ap rep lo cnt ob jst
  hjs : X.Pg.prims[jst]? = some (pointwiseStabPrim hst)
  hm : X.Pg.HasAt mh (mapFuns mh mi)
  hi : X.Pg.funs[mi]? = some (resetIntBody (dom + 18) (dom + 9))
  hl : LiftAt X.Pg lift dom jpre jfac
  hjp : X.Pg.prims[jpre]? = some (preimagePrim hpre)
  hjf : X.Pg.prims[jfac]? = some (normalizedFactorPrim hfac)

/-- **The reset.** -/
theorem ops_reset {hst : PointwiseStab} {hpre : Preimage} {hfac : NormalizedFactor}
    (cd : ContCode X F) (rc : ResetCode X cd.frs hst hpre hfac)
    (hK : ∀ k N W, k ≤ X.Nm → N ≤ X.Nm → W ≤ X.W₀ →
      (contPart k N W : ℝ) + (resetOwn (pointwiseStabPrim hst) (preimagePrim hpre)
        (normalizedFactorPrim hfac) (W + 1) : ℕ) ≤ K₁)
    (T : State Ω C) (hd : DGood X.D X.Nm T) (hs : ¬ Ctx.IsSmall T) (ht : T.Transitive) :
    ∃ (Ω' C' : Type) (R : State Ω' C'), DGood X.D X.Nm R ∧ R.Transitive ∧ Ctx.Ready R ∧
      R.size = T.size ∧ R.dres.Le T.dres ∧
      (∀ μ, MLt μ (measure P₀ .cont R) → MLt μ (measure P₀ .cont T)) ∧
      ∀ b : ℝ, (∀ (k : ℕ) (e : Ω' ≃ Fin k) (cc : C' → ℕ), Function.Injective cc → ∀ v : Val,
          X.In .cont e cc v R → FunAll X.Pg X.transD v fun u cost =>
            AnsC e u R.answer ∧ (cost : ℝ) ≤ b) →
        ∀ (k : ℕ) (e : Ω ≃ Fin k) (cc : C → ℕ), Function.Injective cc → ∀ v : Val,
          X.In .cont e cc v T → FunAll X.Pg X.contD v fun u cost =>
            AnsC e u T.answer ∧ (cost : ℝ) ≤ K₁ + b := by
  have hfin : Finite Ω := hd.finite
  have hs' : max P₀.N₀ (rhoNat T.hier) < T.size := not_le.1 hs
  have hN : P₀.N₀ < T.size := (le_max_left _ _).trans_lt hs'
  have hρ : rhoNat T.hier < T.size := (le_max_right _ _).trans_lt hs'
  have h2 : 2 ≤ T.size := by have := one_le_N₀; omega
  refine ⟨T.dom, C, resetState T, resetState_dGood T hd hN, resetState_transitive T ht,
    (resetState_size T).symm, resetState_size T, resetState_res_le T,
    fun μ h => resetState_measure T hd ht h, fun b hyp k e cc hcc v hv => ?_⟩
  have hcan : Canon e cc v T := hv.1
  have hr := reset_spec hst hpre hfac rc.hb rc.hp rc.hjs rc.hm rc.hi rc.hl rc.hjp rc.hjf e cc T hcan
    h2 hρ.le (b := b) (fun val hval =>
      hyp _ (domEquiv e T.dom) (freshCode e cc T) (freshCode_injective e cc T hcc) val
        ⟨hval, fun h => by cases h⟩)
  refine (contD_spec cd.hcont cd.hbs cd.hbr cd.hg cd.hl cd.hlo cd.hmax hcan
    (fun h => absurd h hs) (fun _ h => absurd ht h) (fun _ _ => hr)).mono ?_
  rintro u cost ⟨c₀, ⟨ha, hc⟩, hle⟩
  refine ⟨ha, ?_⟩
  have hk := hK k T.N v.wt (Ctx.k_le_Nm hd hcan) hd.N_le (Ctx.wt_le_W₀ hd hcan)
  have hu := ha.wt_le
  have h3 : cost ≤ c₀ + contPart k T.N v.wt := by unfold contPart; omega
  have h4 : (cost : ℝ) ≤ c₀ + contPart k T.N v.wt := by exact_mod_cast h3
  linarith

end GI.Degree
