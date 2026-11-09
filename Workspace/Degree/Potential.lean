module

public import Workspace.Assembly.Params
public import Workspace.Degree.Weight

@[expose] public section

/-!
# The resources of a state

The weight of `Workspace/Degree/Weight.lean` reads four numbers of a state. The first is its size.
The second is the potential term: the largest value of `log(|v^G| + 2) + σ(v, G)`
over the points of the domain. It is a sup over points, not `log(s + 2) + sup σ`, because
`ChargedCall` gives its two alternatives one point at a time. The others are `ρ` and `Q`.

On a transitive state the two forms agree, and that is all the operations use. A child has a
smaller value because each of its points does.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly Equiv

variable {Ω C : Type}

/-- The value of one point in the potential: `log(|v^G| + 2) + σ(v, G)`. -/
noncomputable def pointValue (G : Subgroup (Perm Ω)) (v : Ω) : ℝ :=
  Real.log (((orb G v).ncard : ℝ) + 2) + (GI.sigma P₀.κ v G : ℝ)

/-- The term `ψ`. -/
noncomputable def _root_.GI.Algorithm.State.psi (S : State Ω C) : ℝ := ⨆ v : S.dom, pointValue S.G v

/-- The resources of a state. -/
noncomputable def _root_.GI.Algorithm.State.dres (S : State Ω C) : Res :=
  ⟨S.size, S.psi, (rhoNat S.hier : ℝ), State.hierQ S.hier⟩

theorem pointValue_nonneg (G : Subgroup (Perm Ω)) (v : Ω) : 0 ≤ pointValue G v := by
  unfold pointValue
  have : (0 : ℝ) ≤ Real.log (((orb G v).ncard : ℝ) + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ ((orb G v).ncard : ℝ) := Nat.cast_nonneg _
    linarith)
  positivity

theorem _root_.GI.Algorithm.State.psi_nonneg (S : State Ω C) : 0 ≤ S.psi :=
  Real.iSup_nonneg fun v => pointValue_nonneg S.G v

theorem hierQ_nonneg (l : List (Interval Ω)) : 0 ≤ State.hierQ l := by
  unfold State.hierQ
  refine List.sum_nonneg ?_
  intro x hx
  obtain ⟨I, -, rfl⟩ := List.mem_map.1 hx
  exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

/-- The resources of every state are nonnegative. -/
theorem _root_.GI.Algorithm.State.dres_ok (S : State Ω C) : S.dres.OK :=
  ⟨S.psi_nonneg, Nat.cast_nonneg _, hierQ_nonneg _⟩

theorem _root_.GI.Algorithm.State.point_le_psi [Finite Ω] (S : State Ω C) {v : Ω} (hv : v ∈ S.dom) :
    pointValue S.G v ≤ S.psi := by
  have hb : BddAbove (Set.range fun w : S.dom => pointValue S.G w) :=
    (Set.finite_range _).bddAbove
  exact le_ciSup hb (⟨v, hv⟩ : S.dom)

/-- `ψ` is at most any bound on the points, which is how `ψ` of a child is bounded. -/
theorem _root_.GI.Algorithm.State.psi_le {S : State Ω C} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ v ∈ S.dom, pointValue S.G v ≤ b) : S.psi ≤ b :=
  Real.iSup_le (fun v => h v v.2) hb

theorem exists_mem_dom [Finite Ω] {S : State Ω C} (h : 1 ≤ S.size) : ∃ v, v ∈ S.dom := by
  have h1 : 0 < Nat.card S.dom := h
  obtain ⟨⟨v, hv⟩⟩ := (Nat.card_pos_iff.1 h1).1
  exact ⟨v, hv⟩

theorem one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- A state with a nonempty domain has `ψ ≥ 1`. -/
theorem _root_.GI.Algorithm.State.one_le_psi [Finite Ω] {S : State Ω C} (h : 1 ≤ S.size) : 1 ≤ S.psi := by
  obtain ⟨v, hv⟩ := exists_mem_dom h
  refine le_trans ?_ (S.point_le_psi hv)
  have hm : v ∈ orb S.G v := ⟨1, S.G.one_mem, rfl⟩
  have hc : 1 ≤ (orb S.G v).ncard := by
    have hf : (orb S.G v).Finite := Set.toFinite _
    exact Nat.succ_le_of_lt ((Set.ncard_pos hf).2 ⟨v, hm⟩)
  have hc' : (1 : ℝ) ≤ ((orb S.G v).ncard : ℝ) := by exact_mod_cast hc
  have h3 : Real.log 3 ≤ Real.log (((orb S.G v).ncard : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have := one_le_log_three
  unfold pointValue
  have : (0 : ℝ) ≤ (GI.sigma P₀.κ v S.G : ℝ) := Nat.cast_nonneg _
  linarith

/-- On a transitive state with a nonempty domain, `ψ ≥ log(s + 2)`. -/
theorem _root_.GI.Algorithm.State.log_le_psi [Finite Ω] {S : State Ω C} (ht : S.Transitive) (h : 1 ≤ S.size) :
    Real.log ((S.size : ℝ) + 2) ≤ S.psi := by
  obtain ⟨v, hv⟩ := exists_mem_dom h
  refine le_trans ?_ (S.point_le_psi hv)
  have hsub : S.dom ⊆ orb S.G v := fun w hw => ht v hv w hw
  have hc : S.size ≤ (orb S.G v).ncard := by
    unfold State.size
    rw [Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hc' : (S.size : ℝ) ≤ ((orb S.G v).ncard : ℝ) := by exact_mod_cast hc
  have hs : (0 : ℝ) ≤ S.size := Nat.cast_nonneg _
  have h3 : Real.log ((S.size : ℝ) + 2) ≤ Real.log (((orb S.G v).ncard : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  unfold pointValue
  have : (0 : ℝ) ≤ (GI.sigma P₀.κ v S.G : ℝ) := Nat.cast_nonneg _
  linarith

end GI.Degree
