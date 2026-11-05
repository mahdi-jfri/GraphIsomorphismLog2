module

public import Workspace.Impl.AggItemCiSojCC
public import Workspace.Impl.AggItemCiSojLeft

@[expose] public section

/-!
# Full-label overcosets from the complete rectangle answers

Representative differences recover all matrix automorphisms. Adding the even
permutations fixing the left side gives precisely the model's full `leftGroup`.
The program may use its canonical answer representative: it lies in the same
full overcoset as the representative selected by the model's reader.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Rectangle Equiv Equiv.Perm
open GI.Cited (gens)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- The projected complete answers generate the exact full-label item group. -/
theorem itcs_full_answer_gens (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    (M N : W → R → Bool) (rr : permitted W R → Option rep.H)
    (hr : ∀ t ∈ itcsTwists rep, match rr t with
      | none => (rep.state M N t).answer = ∅
      | some g => g.val ∈ (rep.state M N t).answer)
    (gs : List (Perm (Fin k))) (hgs : gens gs = groupFin e (itcsPhysicalAut rep M))
    {p₀ : permitted W R} (h₀ : p₀ ∈ itcsCosetReps rep rr) :
    gens (itcsLeftGens W R (itcsDiffGens p₀ (itcsCosetReps rep rr)
      ((itcsLiftGens e rep M gs hgs).map (itcsRepMap rep)))) =
        (leftGroup M).map (alternatingGroup (Fin L.q)).subtype := by
  apply itcs_left_gens
  exact itcs_coset_generators rep M N rr hr _ (itcs_projected_gens e rep M gs hgs) h₀

/-- Any actual physical answer representative gives the same overcoset as the
model's reader, with the exact model group. -/
theorem itcs_answer_ovAt (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q)) (t : permitted W R) (g : rep.H)
    (hg : g.val ∈ (rep.state M N t).answer) {σ : alternatingGroup (Fin L.q)}
    (hread : (rep.query M N a₀ t).read (rep.state M N t).answer = some σ)
    (ms : List (Perm (Fin L.q))) :
    asOvAt L (a₀ * (t * itcsRepMap rep g).val, leftGroup M, ms)
      (AuxItem.liftOver L (leftGroup M) σ) := by
  have hσ := rep.query_sound M N a₀ t hread
  have htr := RectRep.transports_twist (rep.transports_of_mem hg).2
  have hp : MatrixTransports M N (t * itcsRepMap rep g) := htr
  have hm := (leftOvercoset_coset hσ (t * itcsRepMap rep g).val).1 (mem_leftOvercoset hp)
  apply it_ovAt_of_mem L _ ms
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using hm

/-- An empty physical answer makes the model's query reader return `none`. -/
theorem itcs_query_read_none (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q)) (t : permitted W R)
    (hempty : (rep.state M N t).answer = ∅) :
    (rep.query M N a₀ t).read (rep.state M N t).answer = none := by
  classical
  simp only [RectRep.query, hempty, Set.mem_empty_iff_false, false_and,
    exists_false, ↓reduceDIte]

/-- A nonempty canonical answer forces a model reader representative as well. -/
theorem itcs_query_read_some (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q)) (t : permitted W R) (g : rep.H)
    (hg : g.val ∈ (rep.state M N t).answer) :
    ∃ σ, (rep.query M N a₀ t).read (rep.state M N t).answer = some σ := by
  classical
  have hex : ∃ h, h ∈ (rep.state M N t).answer ∧ h ∈ S.G := ⟨g.val, hg, rep.le g.property⟩
  simp only [RectRep.query, dif_pos hex]
  exact ⟨_, rfl⟩

end GI.Impl
