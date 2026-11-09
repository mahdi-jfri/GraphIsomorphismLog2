module

public import Workspace.Degree.AggD
public import Workspace.Degree.RoundShape
public import Workspace.Degree.OpsCont
public import Workspace.Paper.ScriptCalls

@[expose] public section

/-!
# The operation of `giantD`

`ops_giant` proves the field `giant` of `Ops` (`Degree/Spine.lean`). `giantD` is the round of the
general algorithm (`aggBodyE`), whose specification `as_agg_specD` is the named statement `GiantAt`.
The calls of the round are paid by `giantJ`: a `Continue` call by the bound `B` of the spine, and a
call of the general solver by its own cost. The second kind is part of the own work of the node.
There are at most `N^a` calls (`calls_count'`), and each is on at most `q² ≤ D²` points.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm Real
open GI.Cited (Val Preimage NormalizedFactor Membership)

/-- **The statement of `as_agg_specD`** at the function `f`, for every cost of the calls. -/
def GiantAt (I : Iface) (Pg : Program) (F₀ F : Funs) (hpre : Preimage) (hfac : NormalizedFactor)
    (hm : Membership) (krC Xw : ℕ → ℕ) (f : ℕ) : Prop :=
  ∀ (J : CostT) {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {sv lv : Val}
    {L : SuppliedLabels S}, AsCall I Pg F₀ e c S sv lv L →
    DIH Pg F J (RoundP P₀ S L.q) (measure P₀ .giant S) →
    (∀ (Ag : Aggregation P₀ S L.toGiantLabels), Ag.sel.val = L.sel.val →
      ∀ (o : LcOver L.q) (ov), ov ∈ Ag.script.evalExact.overs → ov.2 = L.toGiantLabels.lift o.2.1 →
      ∀ (τ : Perm Ω) (val : Val), Canon e c val (lcChild S o.2.1 τ L.sel (abCap L.toGiantLabels)) →
      FunAll Pg F.cont val (ChildPost (fun T => J .cont T)
        (lcChild S o.2.1 τ L.sel (abCap L.toGiantLabels)) e)) →
    FunAll Pg f (.list [sv, lv]) fun u cost => AnsC e u S.answer ∧
      ∃ (Ag : Aggregation P₀ S L.toGiantLabels) (os : List (LcOver L.q)) (cs : List Child),
        haveI : Finite Ω := Finite.of_equiv _ e.symm
        Ag.sel.val = L.sel.val ∧ cs.length = os.length ∧
        List.Forall₂ (fun o ov => ov.2 = L.toGiantLabels.lift o.2.1) os Ag.script.evalExact.overs ∧
        (∀ c' ∈ cs, ∃ o ∈ os, ∃ τ : Perm Ω, c' =
          ⟨Ω, C, lcChild S o.2.1 τ L.sel (abCap L.toGiantLabels), false⟩) ∧
        (cost : ℝ) ≤ asOwn hpre hfac hm krC Xw k (I.inW .giant S) + Ag.script.cost J +
          (cs.map fun c' => J .cont c'.T).sum

/-- The costs of the calls of a round: `B` for `Continue`, the cost of the general solver for
`Solve`. -/
noncomputable def giantJ (a : ℝ) (Kg dg : ℕ) (B : Child → ℝ) : CostT := fun {Ω C} m T =>
  match m with
  | .solve => exp (a * Real.log ((T.size : ℝ) + 2) ^ 2) +
      Kg * (((10 ^ 4 * (T.N + 2) ^ 6 : ℕ) : ℝ) + 1) ^ dg
  | .cont => B ⟨Ω, C, T, false⟩
  | .giant => 0

/-- The cost of one call of the general solver in a round, on at most `D²` points. -/
noncomputable def solveB (a : ℝ) (Kg dg D : ℕ) : ℝ :=
  exp (a * Real.log (((D ^ 2 : ℕ) : ℝ) + 2) ^ 2) +
    Kg * (((10 ^ 4 * (D ^ 2 + 2) ^ 6 : ℕ) : ℝ) + 1) ^ dg

theorem solveB_nn (a : ℝ) (Kg dg D : ℕ) : 0 ≤ solveB a Kg dg D := by
  unfold solveB
  positivity

/-- **The cost of a script** with calls of the two kinds. -/
theorem Script.cost_le {α : Type} {p : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop} (J : CostT)
    (B : Child → ℝ) {Bs : ℝ} (hBs : 0 ≤ Bs)
    (hp : ∀ {Ω' C' : Type} (m : Mode) (T : State Ω' C'), p m T →
      (m = .solve ∧ J .solve T ≤ Bs) ∨ (m = .cont ∧ J .cont T = B ⟨Ω', C', T, false⟩)) :
    ∀ s : Script α, s.CallsExact p → s.cost J ≤ s.numCalls * Bs + (s.children.map B).sum
  | .done _, _ => by simp [Script.cost, Script.numCalls, Script.children]
  | .ask m T k, h => by
    have ih := Script.cost_le J B hBs hp (k T.answer) h.2
    simp only [Script.cost, Script.numCalls, Script.children, List.map_append, List.sum_append]
    push_cast
    rcases hp m T h.1 with ⟨rfl, hJ⟩ | ⟨rfl, hJ⟩
    · simp only [reduceCtorEq, if_false, List.map_nil, List.sum_nil, zero_add]
      nlinarith
    · simp only [if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [hJ]
      nlinarith

theorem forall₂_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab hl, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_mem hl h
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- The code of `giantD`. -/
structure GiantCode (X : Ctx) (F₀ F : Funs) (hpre : Preimage) (hfac : NormalizedFactor)
    (hm : Membership) (krC Xw : ℕ → ℕ) where
  hcont : F.cont = X.contD
  fs : ℕ
  hsolve : F.solve = fs
  spec : GiantAt X.I X.Pg F₀ F hpre hfac hm krC Xw X.giantD
  ih : ∀ {Ω C : Type} (S : State Ω C), X.I.IH X.Pg F₀ .giant S
  labW_le : ∀ k N, X.I.labW k N ≤ labWStd k N

/-- The bound on the weight of the input of a round. -/
def Ctx.WG (X : Ctx) : ℕ := 2 * (X.W₀ + labWStd X.Nm X.Nm) + 6

/-- **The polynomial bounds of a round.** -/
structure GiantBudget (X : Ctx) (hpre : Preimage) (hfac : NormalizedFactor) (hm : Membership)
    (krC Xw : ℕ → ℕ) (a : ℝ) (Kg dg : ℕ) (K₂ : ℝ) : Prop where
  own : ∀ k W, k ≤ X.Nm → W ≤ X.WG → (asOwn hpre hfac hm krC Xw k W : ℝ) ≤ K₂
  calls : ∀ N : ℕ, N ≤ X.Nm → (N : ℝ) ^ P₀.a * solveB a Kg dg X.D ≤ K₂

variable {X : Ctx} {ks : Cst}

set_option maxHeartbeats 2000000 in
/-- **The field `giant` of `Ops`.** -/
theorem ops_giant {F₀ F : Funs} {hpre : Preimage} {hfac : NormalizedFactor} {hm : Membership}
    {krC Xw : ℕ → ℕ} (gc : GiantCode X F₀ F hpre hfac hm krC Xw) {Kg dg : ℕ} {K₂ : ℝ}
    (hb : GiantBudget X hpre hfac hm krC Xw ks.a Kg dg K₂)
    (hgs : ∀ {Ω C : Type} (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
      Function.Injective c → ∀ v : Val, StateVal e c v S →
        FunAll X.Pg gc.fs v fun u cost => AnsC e u S.answer ∧
          (cost : ℝ) ≤ exp (ks.a * Real.log ((S.size : ℝ) + 2) ^ 2) + Kg * ((v.wt : ℝ) + 1) ^ dg)
    (hc₀ : ks.c₀ = cZero) (hδ : ks.δ = GI.Paper.cBeta P₀.β)
    (hCm : ks.Cm = 4 * (P₀.κ.factorial : ℝ) + 11) (ham : ks.am = 2 * (P₀.κ : ℝ)) (hCo : ks.Co = 2)
    (hao : ks.ao = (P₀.κ : ℝ) + 1) {Ω C : Type} (T : State Ω C) (hd : DGood X.D X.Nm T)
    (hg : Good P₀ .giant T) :
    X.Runs X.giantD .giant T (measure P₀ .giant T) (K₂ + K₂)
      (fun cs => ∃ lq : ℝ, 1 ≤ lq ∧ X.GiantShape ks T lq cs) := by
  intro B hB k e cc hcc v hv
  have hfin : Finite Ω := hd.finite
  obtain ⟨sv, lv, L, rfl, hcan, hlab, hq₀, hlw, hLN⟩ := hv.2 rfl
  obtain ⟨hNgt, hsN, htr, hγ, hinv, -⟩ := id hg
  have hqN : (L.q : ℝ) ≤ (T.N : ℝ) ^ P₀.α := le_rpow_of_pow_lt hLN
  have hN1 : (1 : ℝ) ≤ T.N := by
    have : 1 ≤ T.N := by have := one_le_N₀; omega
    exact_mod_cast this
  have h2 : 2 ≤ T.size := by
    have h1 : (1 : ℝ) ≤ (T.N : ℝ) ^ P₀.γ := Real.one_le_rpow hN1 (by norm_num [P₀])
    have : (1 : ℝ) < T.size := lt_of_le_of_lt h1 hγ
    have : 1 < T.size := by exact_mod_cast this
    omega
  have hnot : ¬ RowCase P₀.α T L.toGiantLabels := fun h => absurd hqN (not_le.2 h.1)
  have hcall : AsCall X.I X.Pg F₀ e cc T sv lv L :=
    ⟨hcc, hcan, hlab, hq₀, hlw, hg, gc.ih T, hnot⟩
  have hkN : k ≤ X.Nm := Ctx.k_le_Nm hd hcan
  have hih : DIH X.Pg F (giantJ ks.a Kg dg B) (RoundP P₀ T L.q) (measure P₀ .giant T) := by
    intro m Ω' C' T' hm hg' hlt hPr k' e' c' hc' arg hcan'
    rcases hm with rfl | rfl
    · show FunAll X.Pg F.solve arg _
      rw [gc.hsolve]
      refine (hgs T' k' e' c' hc' arg hcan'.stateVal).mono fun u c₁ ⟨ha, hc⟩ => ⟨ha, ?_⟩
      have hw : arg.wt ≤ 10 ^ 4 * (T'.N + 2) ^ 6 := hcan'.wt_le_poly
      have hw' : ((arg.wt : ℝ) + 1) ^ dg ≤ (((10 ^ 4 * (T'.N + 2) ^ 6 : ℕ) : ℝ) + 1) ^ dg :=
        pow_le_pow_left₀ (by positivity) (by
          have : (arg.wt : ℝ) ≤ ((10 ^ 4 * (T'.N + 2) ^ 6 : ℕ) : ℝ) := by exact_mod_cast hw
          linarith) dg
      have hK : (0 : ℝ) ≤ Kg := Nat.cast_nonneg Kg
      show (c₁ : ℝ) ≤ exp (ks.a * Real.log ((T'.size : ℝ) + 2) ^ 2) +
        Kg * (((10 ^ 4 * (T'.N + 2) ^ 6 : ℕ) : ℝ) + 1) ^ dg
      exact hc.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hw' hK))
    · obtain ⟨-, hlt', hmlt⟩ := localChild_of_call (X := X) hc₀ hd hg h2 hPr.1 (hPr.2 hqN)
      show FunAll X.Pg F.cont arg _
      rw [gc.hcont]
      exact hB ⟨Ω', C', T', false⟩ hlt' hmlt k' e' c' hc' arg ⟨hcan', fun h => by cases h⟩
  have hlcih : ∀ (Ag : Aggregation P₀ T L.toGiantLabels), Ag.sel.val = L.sel.val →
      ∀ (o : LcOver L.q) (ov), ov ∈ Ag.script.evalExact.overs →
      ov.2 = L.toGiantLabels.lift o.2.1 →
      ∀ (τ : Perm Ω) (val : Val), Canon e cc val (lcChild T o.2.1 τ L.sel (abCap L.toGiantLabels)) →
      FunAll X.Pg F.cont val (ChildPost (fun T' => (giantJ ks.a Kg dg B) .cont T')
        (lcChild T o.2.1 τ L.sel (abCap L.toGiantLabels)) e) := by
    intro Ag hsel o ov hov h2' τ val hval
    rcases ov with ⟨σ, E⟩
    simp only at h2'
    subst h2'
    have hH : lcHier T L.sel (abCap L.toGiantLabels) = Ag.newHier (σ, L.toGiantLabels.lift o.2.1) := by
      rw [← hsel]
      exact lcHier_eq_newHier T Ag _
    have hle : (σ, L.toGiantLabels.lift o.2.1).2 ≤ T.G := L.toGiantLabels.lift_le o.2.1
    have hT : lcChild T o.2.1 τ L.sel (abCap L.toGiantLabels) =
        T.restrict (σ, L.toGiantLabels.lift o.2.1).2 hle T.x (T.y ∘ τ)
          (Ag.newHier (σ, L.toGiantLabels.lift o.2.1)) := by
      unfold lcChild
      rw [hH]
    rw [hT] at hval ⊢
    obtain ⟨-, f2, f3⟩ := over_facts (X := X) (ks := ks) hδ hd hg hq₀ Ag hsel hov hle (T.y ∘ τ)
    rw [gc.hcont]
    exact Ctx.below_call hB hcc f2.1 f2.2 f3 hval
  refine (gc.spec (giantJ ks.a Kg dg B) hcall hih hlcih).mono ?_
  rintro u cost ⟨ha, Ag, os, cs, hsel, hlen, hF, hcs, hcost⟩
  have hos : ∀ c ∈ cs, Ctx.OverChild ks T (Real.log L.q) c ∧ X.Good c ∧
      MLt (measure P₀ c.mode c.T) (measure P₀ .giant T) := by
    intro c hc
    obtain ⟨o, ho, τ, rfl⟩ := hcs c hc
    obtain ⟨ov, hov, h2'⟩ := forall₂_mem hF ho
    rcases ov with ⟨σ, E⟩
    simp only at h2'
    subst h2'
    have hH : lcHier T L.sel (abCap L.toGiantLabels) = Ag.newHier (σ, L.toGiantLabels.lift o.2.1) := by
      rw [← hsel]
      exact lcHier_eq_newHier T Ag _
    have hle : (σ, L.toGiantLabels.lift o.2.1).2 ≤ T.G := L.toGiantLabels.lift_le o.2.1
    have hT : lcChild T o.2.1 τ L.sel (abCap L.toGiantLabels) =
        T.restrict (σ, L.toGiantLabels.lift o.2.1).2 hle T.x (T.y ∘ τ)
          (Ag.newHier (σ, L.toGiantLabels.lift o.2.1)) := by
      unfold lcChild
      rw [hH]
    rw [hT]
    exact over_facts (X := X) (ks := ks) hδ hd hg hq₀ Ag hsel hov hle (T.y ∘ τ)
  have hlen' : cs.length ≤ Ag.script.evalExact.overs.length := by
    rw [hlen, hF.length_eq]
  obtain ⟨hshape, -⟩ := giantShape_of_round (X := X) hc₀ hδ hCm ham hCo hao hd hg h2 hLN hq₀ Ag hsel
    cs hos hlen'
  refine ⟨ha, Ag.script.children ++ [] ++ cs, ⟨Real.log L.q, ?_, hshape⟩, ?_⟩
  · have hq : (3 : ℝ) ≤ L.q := by
      have : 3 ≤ L.q := by have : P₀.q₀ = 2064 := rfl; omega
      exact_mod_cast this
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  · have hqD : L.q ≤ X.D := Ag.sel_cap.trans (hd.caps _ (List.getElem_mem _))
    have hq2 : L.q ^ 2 ≤ X.D ^ 2 := Nat.pow_le_pow_left hqD 2
    have hBs := solveB_nn ks.a Kg dg X.D
    have hcalls := Script.CallsExact.and Ag.calls (Ag.script_roundCalls hqN)
    have hc2 := Script.cost_le (giantJ ks.a Kg dg B) B hBs (fun m T' h => by
      obtain ⟨-, hr⟩ := h
      rcases hr with ⟨rfl, hs, hN⟩ | ⟨rfl, -⟩
      · refine Or.inl ⟨rfl, ?_⟩
        show exp (ks.a * Real.log ((T'.size : ℝ) + 2) ^ 2) +
            Kg * (((10 ^ 4 * (T'.N + 2) ^ 6 : ℕ) : ℝ) + 1) ^ dg ≤ solveB ks.a Kg dg X.D
        unfold solveB
        have hs' : (T'.size : ℝ) ≤ ((X.D ^ 2 : ℕ) : ℝ) := by exact_mod_cast hs.trans hq2
        have hl1 : 0 ≤ Real.log ((T'.size : ℝ) + 2) := Real.log_nonneg (by
          have : (0 : ℝ) ≤ T'.size := Nat.cast_nonneg _
          linarith)
        have hl2 : Real.log ((T'.size : ℝ) + 2) ≤ Real.log (((X.D ^ 2 : ℕ) : ℝ) + 2) :=
          Real.log_le_log (by positivity) (by linarith)
        have hsq : Real.log ((T'.size : ℝ) + 2) ^ 2 ≤ Real.log (((X.D ^ 2 : ℕ) : ℝ) + 2) ^ 2 :=
          pow_le_pow_left₀ hl1 hl2 2
        have he := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hsq ks.a_nn)
        have hN' : 10 ^ 4 * (T'.N + 2) ^ 6 ≤ 10 ^ 4 * (X.D ^ 2 + 2) ^ 6 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)
        have hN'' : (((10 ^ 4 * (T'.N + 2) ^ 6 : ℕ) : ℝ) + 1) ^ dg ≤
            (((10 ^ 4 * (X.D ^ 2 + 2) ^ 6 : ℕ) : ℝ) + 1) ^ dg :=
          pow_le_pow_left₀ (by positivity) (by
            have : ((10 ^ 4 * (T'.N + 2) ^ 6 : ℕ) : ℝ) ≤ ((10 ^ 4 * (X.D ^ 2 + 2) ^ 6 : ℕ) : ℝ) := by
              exact_mod_cast hN'
            linarith) dg
        have hK : (0 : ℝ) ≤ Kg := Nat.cast_nonneg Kg
        exact add_le_add he (mul_le_mul_of_nonneg_left hN'' hK)
      · exact Or.inr ⟨rfl, rfl⟩) Ag.script hcalls
    have hn := Ag.calls_count'
    have hcall := hb.calls T.N hd.N_le
    have hWG : X.I.inW .giant T ≤ X.WG := by
      have hk : Nat.card Ω = k := by rw [Nat.card_congr e, Nat.card_fin]
      have hfit : Nat.card Ω ≤ T.N := hk ▸ hcan.fits
      have e1 := stateW_le_of_small hfit hcan.small'
      have e2 : (T.N + 2) ^ 6 ≤ (X.Nm + 2) ^ 6 := Nat.pow_le_pow_left (by have := hd.N_le; omega) 6
      have e3 := gc.labW_le (Nat.card Ω) T.N
      have e4 : labWStd (Nat.card Ω) T.N ≤ labWStd X.Nm X.Nm := by
        have := hd.N_le
        have : (Nat.card Ω + 1) ^ 4 ≤ (X.Nm + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
        unfold labWStd
        omega
      show 2 * (stateW (Nat.card Ω) T + X.I.labW (Nat.card Ω) T.N) + 6 ≤ X.WG
      unfold Ctx.WG Ctx.W₀
      omega
    have hown := hb.own k _ hkN hWG
    have hmul : (Ag.script.numCalls : ℝ) * solveB ks.a Kg dg X.D ≤
        (T.N : ℝ) ^ P₀.a * solveB ks.a Kg dg X.D := mul_le_mul_of_nonneg_right hn hBs
    have hcs' : (cs.map fun c' => giantJ ks.a Kg dg B .cont c'.T) = cs.map B := by
      refine List.map_congr_left fun c' hc' => ?_
      obtain ⟨o, -, τ, rfl⟩ := hcs c' hc'
      rfl
    rw [hcs'] at hcost
    simp only [List.map_append, List.map_nil, List.sum_append, List.sum_nil, add_zero]
    linarith

end GI.Degree
