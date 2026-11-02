import Workspace.Lang.Prims.LinMembership

namespace GI.Impl
open GI.Cited GI.Lang

/-- Constructive membership called on the function input. -/
def linMembershipF (j : ℕ) : Expr := primF j

noncomputable def linMembershipCost (h : ConstructiveMembership) (I : MemberInst) : ℕ :=
  (linMembershipPrim h).bound (memberInput I) + (memberInput I).wt +
    linMembershipWt (linMembershipDegree h) I + 2

/-- On a known member, the output contains a checked SLP, not the negative answer. -/
theorem linMembership_member_spec (h : ConstructiveMembership) {P : Program} {f j : ℕ}
    (hf : P.funs[f]? = some (linMembershipF j))
    (hj : P.prims[j]? = some (linMembershipPrim h)) (I : MemberInst) (hx : I.x ∈ gens I.gs) :
    FunAll P f (memberInput I) (fun w cost =>
      (∃ prog : List SlpInstr, w = .list [.nat 1, .list (prog.map encSlpInstr)] ∧
        prog.length ≤ (memberInput I).cells.length ^ linMembershipDegree h ∧
        SlpReaches I.gs prog I.x) ∧ cost ≤ linMembershipCost h I) := by
  refine (FunAll.prim_spec hf hj (linMembershipPrim_spec h I hx)).mono fun w cost hw => ?_
  exact ⟨hw.1, by have := linMembershipOut_wt hw.1; unfold linMembershipCost; omega⟩

end GI.Impl
