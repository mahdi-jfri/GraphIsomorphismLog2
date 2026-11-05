module

public import Workspace.GraphReduction
public import Mathlib.Data.Fintype.Perm

@[expose] public section

/-! A finite exhaustive reference solver, with correctness proofs. It is NOT the paper's
algorithm and is NOT claimed to have quasipolynomial running time. -/
namespace GI

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

instance (x y : V → C) (p : Equiv.Perm V) : Decidable (Transports x y p) :=
  inferInstanceAs (Decidable (∀ v, y (p v) = x v))

def allTransporters (x y : V → C) : Finset (Equiv.Perm V) :=
  Finset.univ.filter (Transports x y)

@[simp] theorem mem_allTransporters (x y : V → C) (p : Equiv.Perm V) :
    p ∈ allTransporters x y ↔ Transports x y p := by
  simp [allTransporters]

def isomorphic (x y : V → C) : Bool := decide (allTransporters x y).Nonempty

theorem isomorphic_correct (x y : V → C) :
    isomorphic x y = true ↔ ∃ p, Transports x y p := by
  simp [isomorphic, Finset.Nonempty]

theorem reference_candidate_count :
    (Finset.univ : Finset (Equiv.Perm V)).card = (Fintype.card V).factorial := by
  simp [Fintype.card_perm]

/-- Listing all automorphisms supplies a (possibly very large) complete generating set. -/
theorem exhaustive_generators_complete (x : V → C) :
    Subgroup.closure (↑(allTransporters x x) : Set (Equiv.Perm V)) =
      automorphisms ⊤ x := by
  have h : (↑(allTransporters x x) : Set (Equiv.Perm V)) =
      (automorphisms ⊤ x : Set (Equiv.Perm V)) := by
    ext p
    simp [automorphisms]
  rw [h, Subgroup.closure_eq]

end GI
