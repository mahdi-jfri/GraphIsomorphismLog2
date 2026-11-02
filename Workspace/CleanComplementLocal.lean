import Workspace.Compat
import Workspace.CleanCompletionTransfer

/-! From actual localized lifts to the clean block cycles used in A.17.
The existence of the localized lifts (LG2) remains an explicit input. -/
namespace GI
variable {I V : Type*} [DecidableEq I]

/-- A lift with no action inside blocks fixed by its top permutation. -/
structure LocalizedBlockLift (label : V → I) (p : Equiv.Perm I) (g : Equiv.Perm V) : Prop where
  action : ∀ x, label (g x) = p (label x)
  fixes : ∀ x, p (label x) = label x → g x = x

omit [DecidableEq I] in
theorem block_action_inverse (label : V → I) (p : Equiv.Perm I) (g : Equiv.Perm V)
    (ha : ∀ x, label (g x) = p (label x)) (x : V) :
    label (g.symm x) = p.symm (label x) := by
  apply p.injective
  rw [← ha, g.apply_symm_apply, p.apply_symm_apply]

omit [DecidableEq I] in
theorem LocalizedBlockLift.moves_iff {label : V → I} {p : Equiv.Perm I}
    {g : Equiv.Perm V} (hg : LocalizedBlockLift label p g) (x : V) :
    g x ≠ x ↔ p (label x) ≠ label x := by
  constructor
  · exact fun h he => h (hg.fixes x he)
  · intro h he
    exact h ((hg.action x).symm.trans (congrArg label he))

/-- Concrete individual clean-cycle data, before choosing any coordinates. -/
structure CleanBlockCycle (label : V → I) (a b c : I) (s : Equiv.Perm V) : Prop where
  action : ∀ x, label (s x) = cleanCycle a b c (label x)
  returns : ∀ x, s (s (s x)) = x
  fixes : ∀ x, label x ≠ a → label x ≠ b → label x ≠ c → s x = x

omit [DecidableEq I] in
theorem top_pair_separated (p q : Equiv.Perm I) (a : I)
    (hmeet : ∀ i, (p i ≠ i ∧ q i ≠ i) ↔ i = a) : LocalSeparated p q := by
  have ha := (hmeet a).mpr rfl
  constructor
  · intro i hi hpi
    have hi' := (hmeet i).mp hi
    have hp := (hmeet (p i)).mp hpi
    subst i
    exact ha.1 hp
  · intro i hi hqi
    have hi' := (hmeet i).mp hi
    have hq := (hmeet (q i)).mp hqi
    subst i
    exact ha.2 hq

theorem top_local_commutator (p q : Equiv.Perm I) (a : I)
    (hmeet : ∀ i, (p i ≠ i ∧ q i ≠ i) ↔ i = a) :
    rightLocalCommutator p q = cleanCycle a (q a) (p a) := by
  have he := local_commutator_cycle_product p q (top_pair_separated p q a hmeet)
    [a] (by simp) (fun i => by simpa [localIntersection] using (hmeet i).symm)
  simpa [localThreeCycle, cleanCycle] using he

omit [DecidableEq I] in
theorem localized_intersection {label : V → I} {p q : Equiv.Perm I}
    {g h : Equiv.Perm V} (hg : LocalizedBlockLift label p g)
    (hh : LocalizedBlockLift label q h) (a : I)
    (hmeet : ∀ i, (p i ≠ i ∧ q i ≠ i) ↔ i = a) (x : V) :
    localIntersection g h x ↔ label x = a := by
  rw [localIntersection, hg.moves_iff, hh.moves_iff, hmeet]

omit [DecidableEq I] in
theorem localized_separated {label : V → I} {p q : Equiv.Perm I}
    {g h : Equiv.Perm V} (hg : LocalizedBlockLift label p g)
    (hh : LocalizedBlockLift label q h) (a : I)
    (hmeet : ∀ i, (p i ≠ i ∧ q i ≠ i) ↔ i = a) : LocalSeparated g h := by
  have ha := (hmeet a).mpr rfl
  constructor
  · intro x hx hy
    have hx' := (localized_intersection hg hh a hmeet x).mp hx
    have hy' := (localized_intersection hg hh a hmeet (g x)).mp hy
    rw [hg.action, hx'] at hy'
    exact ha.1 hy'
  · intro x hx hy
    have hx' := (localized_intersection hg hh a hmeet x).mp hx
    have hy' := (localized_intersection hg hh a hmeet (h x)).mp hy
    rw [hh.action, hx'] at hy'
    exact ha.2 hy'

/-- A.16 supplies all clean-cycle fields from the actual two localized lifts. -/
theorem cleanBlockCycle_of_localized {label : V → I} {p q : Equiv.Perm I}
    {g h : Equiv.Perm V} (hg : LocalizedBlockLift label p g)
    (hh : LocalizedBlockLift label q h) (a : I)
    (hmeet : ∀ i, (p i ≠ i ∧ q i ≠ i) ↔ i = a) :
    CleanBlockCycle label a (q a) (p a) (rightLocalCommutator g h) where
  action := by
    intro x
    change label (h (g (h.symm (g.symm x)))) = _
    rw [hh.action, hg.action, block_action_inverse label q h hh.action,
      block_action_inverse label p g hg.action]
    change rightLocalCommutator p q (label x) = _
    rw [top_local_commutator p q a hmeet]
  returns := local_commutator_return g h (localized_separated hg hh a hmeet)
  fixes := by
    intro x hxa hxb hxc
    apply local_commutator_outside
    · intro hx
      exact hxa ((localized_intersection hg hh a hmeet x).mp hx)
    · intro hx
      have he := (localized_intersection hg hh a hmeet (g.symm x)).mp hx
      have ht := hg.action (g.symm x)
      rw [g.apply_symm_apply, he] at ht
      exact hxc ht
    · intro hx
      have he := (localized_intersection hg hh a hmeet (h.symm x)).mp hx
      have ht := hh.action (h.symm x)
      rw [h.apply_symm_apply, he] at ht
      exact hxb ht

theorem local_commutator_mem (G : Subgroup (Equiv.Perm V))
    {g h : Equiv.Perm V} (hg : g ∈ G) (hh : h ∈ G) : rightLocalCommutator g h ∈ G :=
  G.mul_mem (G.mul_mem (G.mul_mem hh hg) (G.inv_mem hh)) (G.inv_mem hg)

theorem cleanCycle_conjugate (t : Equiv.Perm I) (a b c : I) :
    cleanCycle (t a) (t b) (t c) = t * cleanCycle a b c * t⁻¹ := by
  rw [cleanCycle, Equiv.swap_apply_apply t a c, Equiv.swap_apply_apply t a b]
  simp [cleanCycle, mul_assoc]

theorem CleanBlockCycle.conjugate {label : V → I} {a b c : I} {s : Equiv.Perm V}
    (hc : CleanBlockCycle label a b c s) (r : Equiv.Perm V) (t : Equiv.Perm I)
    (hr : ∀ x, label (r x) = t (label x)) :
    CleanBlockCycle label (t a) (t b) (t c) (r * s * r⁻¹) where
  action := by
    intro x
    change label (r (s (r.symm x))) = _
    rw [hr, hc.action, block_action_inverse label t r hr, cleanCycle_conjugate]
    rfl
  returns := by
    intro x
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_apply_self]
    change r (s (s (s (r.symm x)))) = x
    rw [hc.returns, r.apply_symm_apply]
  fixes := by
    intro x hxa hxb hxc
    have ht : label x = t (label (r.symm x)) := by simpa using hr (r.symm x)
    have ha : label (r.symm x) ≠ a := fun he => hxa (ht.trans (congrArg t he))
    have hb : label (r.symm x) ≠ b := fun he => hxb (ht.trans (congrArg t he))
    have hc' : label (r.symm x) ≠ c := fun he => hxc (ht.trans (congrArg t he))
    change r (s (r.symm x)) = x
    rw [hc.fixes _ ha hb hc', r.apply_symm_apply]

end GI
