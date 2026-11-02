import Workspace.Algorithm.State

/-!
# The query children of an aggregation round

The certificate calls (`CheckNewWindow`), the lockstep comparisons, the kernel calls of the
auxiliary items and the rectangle queries are inherited calls on a new core. Section 6 sets their
bookkeeping: "An independent certificate or rectangle child that may lose the carrier clears its
row record and floor mode, and sets `h=2` against its already established physical or symmetry
decrease."

Whether such a child keeps the carrier (`CounterInv` and `CarrierOK` for the new core) is a
statement about alternating sections of a subgroup, which a program cannot test with the cited
algorithms. So these children always clear the record (`State.queryChild`): every such child
*may* lose the carrier, as far as the algorithm knows. The paper's analysis charges these calls
to their physical or symmetry decrease (`ChargedCall`), not to the bookkeeping.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

namespace State

variable {Ω C : Type}

/-- **A query child**: a new core `(G', D', x', y')` with colors of any type, the hierarchy and
phase size of `S`, no row record, floor mode off and `h = 2`. -/
def queryChild {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C') : State Ω C' :=
  ⟨G', D', hD', x', y', S.hier, none, false, 2, le_rfl, S.N, CounterInv.reset _ _ _ _,
    CarrierOK.none _ _ _⟩

variable {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
  (hD' : Invariant G' D') (x' y' : Ω → C')

@[simp] theorem queryChild_G : (S.queryChild G' D' hD' x' y').G = G' := rfl
@[simp] theorem queryChild_dom : (S.queryChild G' D' hD' x' y').dom = D' := rfl
@[simp] theorem queryChild_x : (S.queryChild G' D' hD' x' y').x = x' := rfl
@[simp] theorem queryChild_y : (S.queryChild G' D' hD' x' y').y = y' := rfl
@[simp] theorem queryChild_hier : (S.queryChild G' D' hD' x' y').hier = S.hier := rfl
@[simp] theorem queryChild_N : (S.queryChild G' D' hD' x' y').N = S.N := rfl
@[simp] theorem queryChild_rows : (S.queryChild G' D' hD' x' y').rows = none := rfl
@[simp] theorem queryChild_floor : (S.queryChild G' D' hD' x' y').floor = false := rfl
@[simp] theorem queryChild_h : (S.queryChild G' D' hD' x' y').h = 2 := rfl

theorem queryChild_answer :
    (S.queryChild G' D' hD' x' y').answer = GI.Algorithm.answer G' D' x' y' := rfl

theorem queryChild_inst : (S.queryChild G' D' hD' x' y').Inst G' D' x' y' :=
  ⟨rfl, rfl, rfl, rfl⟩

end State

end GI.Algorithm
