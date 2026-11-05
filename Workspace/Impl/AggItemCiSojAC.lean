module

public import Workspace.Impl.AggItemCiSojAut
public import Workspace.Impl.GenEnum

@[expose] public section

/-!
# The subgroup encoded by a nonempty canonical rectangle answer

Every physical rectangle query has the same source coloring and group. Its
canonical coset therefore encodes precisely that source automorphism subgroup.
This justifies projecting all returned generators through the stored parent map.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Rectangle Equiv Equiv.Perm
open GI.Cited (gens encPerm)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-- A full canonical answer has its representative in the exact answer and its
subgroup equal to the full source automorphism group. -/
theorem itcs_answer_coset (e : Ω ≃ Fin k) (T : State Ω C)
    {x : Perm (Fin k)} {gs : List (Perm (Fin k))}
    (h : toFin e '' T.answer = x • (gens gs : Set (Perm (Fin k)))) :
    ∃ g : Perm Ω, g ∈ T.answer ∧ toFin e g = x ∧
      gens gs = groupFin e (autGroup T.G T.dom T.dom_inv T.x) := by
  have hx : x ∈ toFin e '' T.answer := by
    rw [h]
    exact ⟨1, (gens gs).one_mem, by simp⟩
  obtain ⟨g, hg, hgx⟩ := hx
  refine ⟨g, hg, hgx, ?_⟩
  have hc : toFin e '' T.answer =
      x • (groupFin e (autGroup T.G T.dom T.dom_inv T.x) : Set (Perm (Fin k))) := by
    change toFin e '' answer T.G T.dom T.x T.y = _
    rw [answer_eq_smul_aut T.dom_inv hg, image_toFin_smul, hgx]
    rfl
  have he : x • (gens gs : Set (Perm (Fin k))) =
      x • (groupFin e (autGroup T.G T.dom T.dom_inv T.x) : Set (Perm (Fin k))) := h.symm.trans hc
  apply SetLike.coe_injective
  have he' := congrArg (fun A : Set (Perm (Fin k)) => x⁻¹ • A) he
  simpa only [smul_smul, inv_mul_cancel, one_smul] using he'

variable {S : State Ω C} {L : GiantLabels S} {W R : Finset (Fin L.q)}

/-- The source physical subgroup is independent of the target matrix and twist. -/
noncomputable def itcsPhysicalAut (rep : RectRep P₀ S L W R) (M : W → R → Bool) :
    Subgroup (Perm Ω) := autGroup rep.H rep.Δ rep.Δ_inv (rep.colors M)

/-- In particular all canonical rectangle generators lie in the parent group. -/
theorem itcs_answer_gens_parent (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    (M N : W → R → Bool) (t : permitted W R)
    {x : Perm (Fin k)} {gs : List (Perm (Fin k))}
    (h : toFin e '' (rep.state M N t).answer = x • (gens gs : Set (Perm (Fin k)))) :
    gens gs = groupFin e (itcsPhysicalAut rep M) ∧
      ∀ a ∈ gens gs, ∃ g : Perm Ω, g ∈ S.G ∧ toFin e g = a := by
  obtain ⟨g, hg, hgx, he⟩ := itcs_answer_coset e (rep.state M N t) h
  change gens gs = groupFin e (itcsPhysicalAut rep M) at he
  refine ⟨he, ?_⟩
  intro a ha
  rw [he] at ha
  obtain ⟨g', hg', hga⟩ := ha
  exact ⟨g', rep.le hg'.1, hga⟩

end GI.Impl
