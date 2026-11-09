module

public import Workspace.Degree.Children
public import Workspace.Algorithm.Existence

@[expose] public section

/-!
# The shape of a round

`giantShape_of_round` puts the calls of a round into the form `GiantShape` of
`Workspace/Degree/Spine.lean`, with the invariant and a drop of the measure for each child. The
continuations on overcosets may have any coloring `y` (`over_facts`), since the program may pick
another representative of an overcoset than the script.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly Equiv Equiv.Perm Real

variable {Ω C : Type}

/-- **A continuation of a round on an overcoset**, with any coloring `y`: it lowers `Q`, and it has
the invariant. -/
theorem over_facts {X : Ctx} {ks : Cst} (hδ : ks.δ = GI.Paper.cBeta P₀.β) {S : State Ω C}
    (hd : DGood X.D X.Nm S) (hg : Good P₀ .giant S) {L : SuppliedLabels S} (hq₀ : P₀.q₀ < L.q)
    (I : Aggregation P₀ S L.toGiantLabels) (hsel : I.sel.val = L.sel.val)
    {ov : Perm Ω × Subgroup (Perm Ω)} (hov : ov ∈ I.script.evalExact.overs) (hle : ov.2 ≤ S.G)
    (y : Ω → C) :
    let T := S.restrict ov.2 hle S.x y (I.newHier ov)
    Ctx.OverChild ks S (Real.log L.q) ⟨Ω, C, T, false⟩ ∧ X.Good ⟨Ω, C, T, false⟩ ∧
      MLt (measure P₀ .cont T) (measure P₀ .giant S) := by
  intro T
  have hTdef : T = S.restrict ov.2 hle S.x y (I.newHier ov) := rfl
  haveI := hd.finite
  obtain ⟨hNgt, hsN, htr, -, hinv, -⟩ := id hg
  have hq0 : 3 ≤ L.q := by
    have : P₀.q₀ = 2064 := rfl
    omega
  have hcu := I.capUpdate _ hov
  have hk := I.overs_keep _ hov
  have hG : T.G ≤ S.G := hle
  have hr : (T).rows = none := by
    rw [hTdef, State.restrict_rows_of _ _ _ _ _ _ hk]
    exact hd.rows
  have hf : (T).floor = false := by
    rw [hTdef, State.restrict_floor_of _ _ _ _ _ _ hk]
    exact hd.floor
  have hh : (T).h = 2 := by
    rw [hTdef, State.restrict_h_of _ _ _ _ _ _ hk]
    exact hd.h
  have hinvj : (T).HierInv := I.child_hierInv hsel hinv hov
  refine ⟨overChild_of_capUpdate hδ hq0 hG subset_rfl hcu, ⟨?_, ⟨hNgt, hsN, hinvj⟩⟩, ?_⟩
  · exact hd.child rfl hsN hG hinvj hr hf hh (caps_of_capUpdate hcu hd.caps)
  · have hρ : rhoNat (T).hier = rhoNat S.hier := by
      have h1 : (rhoNat (T).hier : ℝ) = rhoNat S.hier := by
        rw [rhoNat_cast, rhoNat_cast]
        exact hcu.rho_eq
      exact_mod_cast h1
    have hσ : (T).sigma P₀.κ ≤ S.sigma P₀.κ :=
      State.sigma_le_of P₀_terminating.κ_five hG le_rfl
    have hc' := hcu.capSum_lt P₀_terminating.β_lt (by omega)
    have htrj := trInd_le (T)
    have h1 : (T).size = S.size := rfl
    have hNj : (T).N = S.N := rfl
    have h3 : flInd (T) = flInd S := by simp only [flInd, hf, hd.floor]
    have htrS : trInd S = 1 := trInd_of S htr
    have hρ' : rhoNat (I.newHier (ov)) = rhoNat S.hier := hρ
    change MLt (GI.Algorithm.measure P₀ .cont (T)) _
    rw [mlt_iff]
    simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
    have h4 : (T).h = S.h := hh.trans hd.h.symm
    have h5 : capSum (T).hier = capSum (I.newHier (ov)) :=
      rfl
    omega

/-- **A round has the shape of the spine.** All charged calls go in the first list of `GiantShape`,
so the mass bound of the round bounds them, and the second list is empty. -/
theorem giantShape_of_round {X : Ctx} {ks : Cst} (hc₀ : ks.c₀ = cZero)
    (hδ : ks.δ = GI.Paper.cBeta P₀.β) (hCm : ks.Cm = 4 * (P₀.κ.factorial : ℝ) + 11)
    (ham : ks.am = 2 * (P₀.κ : ℝ)) (hCo : ks.Co = 2) (hao : ks.ao = (P₀.κ : ℝ) + 1)
    {S : State Ω C} (hd : DGood X.D X.Nm S) (hg : Good P₀ .giant S) (h2 : 2 ≤ S.size)
    {L : SuppliedLabels S} (hLN : L.q ^ 5 < S.N ^ 2) (hq₀ : P₀.q₀ < L.q)
    (I : Aggregation P₀ S L.toGiantLabels) (hsel : I.sel.val = L.sel.val) (os : List Child)
    (hos : ∀ c ∈ os, Ctx.OverChild ks S (Real.log L.q) c ∧ X.Good c ∧
      MLt (measure P₀ c.mode c.T) (measure P₀ .giant S))
    (hlen : os.length ≤ I.script.evalExact.overs.length) :
    haveI := hd.finite
    X.GiantShape ks S (Real.log L.q) (I.script.children ++ [] ++ os) ∧
      ∀ c ∈ I.script.children ++ os, X.Good c ∧
        MLt (measure P₀ c.mode c.T) (measure P₀ .giant S) := by
  haveI := hd.finite
  have hS := hg
  obtain ⟨hNgt, hsN, htr, -, hinv, -⟩ := id hS
  have hqD : L.q ≤ X.D := I.sel_cap.trans (hd.caps _ (List.getElem_mem _))
  have hq0 : 3 ≤ L.q := by
    have : P₀.q₀ = 2064 := rfl
    omega
  have hqN : (L.q : ℝ) ≤ (S.N : ℝ) ^ P₀.α := le_rpow_of_pow_lt hLN
  have hcalls := Script.CallsExact.and I.calls (I.script_roundCalls hqN)
  have hmem := Script.mem_children (p := fun {Ω' C'} m T => AggCall P₀ S m T ∧ RoundCall L.q m T)
    hcalls
  have hlocal : ∀ c ∈ I.script.children, Ctx.LocalChild ks S c ∧ X.Good c ∧
      MLt (measure P₀ c.mode c.T) (measure P₀ .giant S) := by
    rintro ⟨Ω', C', T, gt⟩ hc
    obtain ⟨hgt, ha, hr⟩ := hmem _ hc
    obtain rfl : gt = false := hgt
    exact localChild_of_call hc₀ hd hS h2 ha hr
  refine ⟨⟨I.script.children, [], os, rfl, fun c hc => (hlocal c hc).1, ?_,
    by simp, ?_, fun c hc => (hos c hc).1, ?_⟩, ?_⟩
  · exact massOK_of_round I hCm ham (by omega) (by omega) hqD
  · simp only [Ctx.MassOK, List.map_nil, List.sum_nil]
    have := ks.Cm_nn
    have h3 : 0 ≤ S.dres.sz := by unfold Res.sz; positivity
    positivity
  · have hlen : os.length ≤ 2 * L.q ^ I.ℓ := hlen.trans I.overs_length_le
    have h3 : (os.length : ℝ) ≤ 2 * (L.q : ℝ) ^ I.ℓ := by exact_mod_cast hlen
    have hq3 : (0 : ℝ) < L.q := by
      have : (3 : ℝ) ≤ L.q := by exact_mod_cast hq0
      linarith
    have e := Real.exp_nat_mul (Real.log L.q) I.ℓ
    rw [Real.exp_log hq3] at e
    rw [hCo, hao]
    refine h3.trans (le_of_eq ?_)
    rw [← e]
    congr 2
    change ((P₀.κ + 1 : ℕ) : ℝ) * _ = _
    push_cast
    ring
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact (hlocal c hc).2
    · exact (hos c hc).2

end GI.Degree
