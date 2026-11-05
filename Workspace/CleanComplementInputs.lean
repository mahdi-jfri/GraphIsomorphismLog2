module

public import Workspace.CleanComplementEven

@[expose] public section

/-! Exact LG2-style input obligations and their connection to the constructed
clean complements. This file does not assert that the logarithmic threshold
implies localization. -/
namespace GI
variable {I V : Type*} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Equiv.Perm V)} (A : CleanBlockAction G I)

/-- LG2 for a specified block set: every supported even top permutation has
a lift fixing all vertices in the other blocks pointwise. -/
def LocalLiftAvailable (T : Set I) : Prop :=
  ∀ p : alternatingGroup I, (∀ i, i ∉ T → p.val i = i) →
    ∃ g : G, A.top g = p ∧ ∀ x, A.label x ∉ T → g.val x = x

theorem localized_of_pointwise_fixing (T : Set I) (g : G) (p : alternatingGroup I)
    (htop : A.top g = p) (hsupport : ∀ i, p.val i ≠ i ↔ i ∈ T)
    (hfix : ∀ x, A.label x ∉ T → g.val x = x) :
    LocalizedBlockLift A.label (A.top g).val g.val where
  action := A.action g
  fixes := by
    intro x hx
    apply hfix x
    intro hmem
    apply (hsupport (A.label x)).mpr hmem
    simpa only [htop] using hx

theorem localized_pair_of_LG2 (T U : Set I) (hT : LocalLiftAvailable A T)
    (hU : LocalLiftAvailable A U) (p q : alternatingGroup I) (a : I)
    (hp : ∀ i, p.val i ≠ i ↔ i ∈ T) (hq : ∀ i, q.val i ≠ i ↔ i ∈ U)
    (hmeet : ∀ i, (i ∈ T ∧ i ∈ U) ↔ i = a) :
    ∃ d : LocalizedBlockPair A, d.center = a := by
  classical
  obtain ⟨g, hgp, hgfix⟩ := hT p (fun i hi => by
    by_contra hn
    exact hi ((hp i).mp hn))
  obtain ⟨h, hhq, hhfix⟩ := hU q (fun i hi => by
    by_contra hn
    exact hi ((hq i).mp hn))
  refine ⟨{
    g := g
    h := h
    center := a
    left := localized_of_pointwise_fixing A T g p hgp hp hgfix
    right := localized_of_pointwise_fixing A U h q hhq hq hhfix
    meet := ?_ }, rfl⟩
  intro i
  rw [hgp, hhq, hp, hq]
  exact hmeet i

end GI

namespace GI.CleanEvenConstruction
variable {I B W : Type*} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Equiv.Perm ((B × I) ⊕ W))}
variable (A : CleanBlockAction G (Option I))

theorem extraLift_of_LG2 (T : Set (Option I)) (hT : LocalLiftAvailable A T)
    (p : alternatingGroup (Option I)) (a b c : I)
    (hp : ∀ i, p.val i ≠ i ↔ i ∈ T) (hsend : p.val (some a) = none)
    (hb : some b ∉ T) (hc : some c ∉ T) : Nonempty (ExtraLift A a b c) := by
  classical
  obtain ⟨h, htop, hfix⟩ := hT p (fun i hi => by
    by_contra hn
    exact hi ((hp i).mp hn))
  refine ⟨{
    h := h
    localized := localized_of_pointwise_fixing A T h p htop hp hfix
    sends := by simpa only [htop] using hsend
    fixes_b := ?_
    fixes_c := ?_ }⟩
  · rw [htop]
    by_contra hn
    exact hb ((hp (some b)).mp hn)
  · rw [htop]
    by_contra hn
    exact hc ((hp (some c)).mp hn)

end GI.CleanEvenConstruction
