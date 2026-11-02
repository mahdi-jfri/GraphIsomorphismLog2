import Workspace.Lang.Prims.LinNormal
import Workspace.Impl.LinSlp

/-! The constructive-membership task, including the cost of writing its SLP.
The bound on program length alone is insufficient: the instruction indices must
also be bounded. Validity supplies that bound. -/
namespace GI.Lang
open GI.Cited GI.Impl

noncomputable def linMembershipDegree (h : ConstructiveMembership) : ℕ := h.choose
noncomputable def linMembershipPrim (h : ConstructiveMembership) : Prim :=
  Prim.ofHyp _ _ h.choose_spec

/-- The output of constructive membership on a member: a checked straight-line program. -/
def linMembershipOut (d : ℕ) (I : MemberInst) (v : Val) : Prop :=
  ∃ prog : List SlpInstr, v = .list [.nat 1, .list (prog.map encSlpInstr)] ∧
    prog.length ≤ (memberInput I).cells.length ^ d ∧ SlpReaches I.gs prog I.x

/-- Every encoded instruction has weight linear in a bound on its indices. -/
theorem linSlpInstr_wt {B : ℕ} {ins : SlpInstr} (h : linSlpRefs B ins) :
    (encSlpInstr ins).wt ≤ 100 * (B + 1) := by
  cases ins with
  | gen i =>
    have := wt_list2_le (.nat 0) (.nat i)
    have := wt_nat_le i
    have : (Val.nat 0).wt = 2 := by decide
    simp only [linSlpRefs] at h
    change (Val.list [.nat 0, .nat i]).wt ≤ _
    omega
  | inv j =>
    have := wt_list2_le (.nat 1) (.nat j)
    have := wt_nat_le j
    have : (Val.nat 1).wt = 3 := by decide
    simp only [linSlpRefs] at h
    change (Val.list [.nat 1, .nat j]).wt ≤ _
    omega
  | mul j k =>
    have := wt_list3_le (.nat 2) (.nat j) (.nat k)
    have := wt_nat_le j
    have := wt_nat_le k
    have : (Val.nat 2).wt = 4 := by decide
    simp only [linSlpRefs] at h
    change (Val.list [.nat 2, .nat j, .nat k]).wt ≤ _
    omega

/-- Polynomial in the input length for each uniform task exponent d. -/
def linMembershipWt (d : ℕ) (I : MemberInst) : ℕ :=
  400 * (((memberInput I).cells.length ^ d) + 1) *
    (I.gs.length + (memberInput I).cells.length ^ d + 2) + 100

theorem linMembershipOut_wt {d : ℕ} {I : MemberInst} {v : Val}
    (hv : linMembershipOut d I v) : v.wt ≤ linMembershipWt d I := by
  obtain ⟨prog, rfl, hl, es, he, _⟩ := hv
  have hgen : linSlpEntries I.gs prog [] = some es := by
    rwa [linSlpEntries_perm]
  have hr := (linSlpEntries_refs prog [] es hgen).2
  have hi : ∀ v ∈ prog.map encSlpInstr,
      v.wt ≤ 100 * (I.gs.length + (memberInput I).cells.length ^ d + 2) := by
    intro v hv
    obtain ⟨ins, hins, rfl⟩ := List.mem_map.mp hv
    apply linSlpInstr_wt
    exact linSlpRefs_mono (by simp only [List.length_nil]; omega) (hr ins hins)
  have hb := linWtList hi
  have ho := wt_list2_le (.nat 1) (.list (prog.map encSlpInstr))
  have : (Val.nat 1).wt = 3 := by decide
  simp only [List.length_map] at hb
  unfold linMembershipWt
  nlinarith [Nat.mul_le_mul_right
    (100 * (I.gs.length + (memberInput I).cells.length ^ d + 2)) hl]

/-- The primitive on a known member `I.x ∈ ⟨I.gs⟩`, the promise of the task. -/
theorem linMembershipPrim_spec (h : ConstructiveMembership) (I : MemberInst)
    (hx : I.x ∈ gens I.gs) :
    PrimSpec (linMembershipPrim h) (memberInput I)
      (linMembershipOut (linMembershipDegree h) I) := by
  obtain ⟨n, gs, x⟩ := I
  apply Prim.ofHyp_spec h.choose_spec ⟨n, gs, x, hx⟩
  rintro ⟨n', gs', x', hx'⟩ hy
  simp only [knownMemberInput, Val.list.injEq, List.cons.injEq, and_true] at hy
  obtain rfl := encGroup_deg hy.1
  obtain rfl := encGroup_injective hy.1
  obtain rfl := encPerm_injective hy.2
  rfl

end GI.Lang
