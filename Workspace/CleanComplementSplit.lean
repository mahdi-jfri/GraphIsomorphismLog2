module

public import Workspace.CleanCompletionCoordinates
public import Mathlib.GroupTheory.Complement

@[expose] public section

/-! A pure alternating subgroup contained in the supplied block group is an
actual complement to the kernel of that supplied action. -/
namespace GI
variable {I V B : Type*} [Fintype I] [DecidableEq I]

structure CleanBlockAction (G : Subgroup (Equiv.Perm V)) (I : Type*) [Fintype I]
    [DecidableEq I] where
  label : V → I
  label_surjective : Function.Surjective label
  top : G →* alternatingGroup I
  top_surjective : Function.Surjective top
  action : ∀ (g : G) (x : V), label (g.val x) = (top g).val (label x)

def coordinatePureLift (e : B × I ≃ V) : Equiv.Perm I →* Equiv.Perm V :=
  (relabelPerm e).toMonoidHom.comp cleanPureHom

omit [Fintype I] [DecidableEq I] in
theorem coordinatePureLift_apply (e : B × I ≃ V) (p : Equiv.Perm I) (b : B) (i : I) :
    coordinatePureLift e p (e (b, i)) = e (b, p i) := by
  change e (cleanPureHom p (e.symm (e (b, i)))) = _
  rw [e.symm_apply_apply]
  rfl

namespace CleanBlockAction
variable {G : Subgroup (Equiv.Perm V)} (A : CleanBlockAction G I)

/-- The section is built from the actual pure permutations already shown to lie in G. -/
def cleanSection (e : B × I ≃ V)
    (hmem : ∀ p : alternatingGroup I, coordinatePureLift e p.val ∈ G) :
    alternatingGroup I →* G where
  toFun p := ⟨coordinatePureLift e p.val, hmem p⟩
  map_one' := by apply Subtype.ext; exact (coordinatePureLift e).map_one
  map_mul' p q := by apply Subtype.ext; exact (coordinatePureLift e).map_mul p.val q.val

theorem top_cleanSection (e : B × I ≃ V) (base : B)
    (hcoord : ∀ b i, A.label (e (b, i)) = i)
    (hmem : ∀ p : alternatingGroup I, coordinatePureLift e p.val ∈ G)
    (p : alternatingGroup I) : A.top (cleanSection e hmem p) = p := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have h := A.action (cleanSection e hmem p) (e (base, i))
  change A.label (coordinatePureLift e p.val (e (base, i))) =
    (A.top (cleanSection e hmem p)).val (A.label (e (base, i))) at h
  rw [coordinatePureLift_apply, hcoord, hcoord] at h
  exact h.symm

theorem cleanSection_injective (e : B × I ≃ V) (base : B)
    (hcoord : ∀ b i, A.label (e (b, i)) = i)
    (hmem : ∀ p : alternatingGroup I, coordinatePureLift e p.val ∈ G) :
    Function.Injective (cleanSection e hmem) := by
  intro p q hpq
  have ht := congrArg A.top hpq
  simpa only [A.top_cleanSection e base hcoord hmem] using ht

theorem kernel_inf_cleanRange (e : B × I ≃ V) (base : B)
    (hcoord : ∀ b i, A.label (e (b, i)) = i)
    (hmem : ∀ p : alternatingGroup I, coordinatePureLift e p.val ∈ G) :
    A.top.ker ⊓ (cleanSection e hmem).range = ⊥ := by
  apply le_antisymm
  · intro g hg
    obtain ⟨p, rfl⟩ := hg.2
    have hp : p = 1 := (A.top_cleanSection e base hcoord hmem p).symm.trans hg.1
    simp [hp]
  · exact bot_le

theorem kernel_mul_cleanRange (e : B × I ≃ V) (base : B)
    (hcoord : ∀ b i, A.label (e (b, i)) = i)
    (hmem : ∀ p : alternatingGroup I, coordinatePureLift e p.val ∈ G) (g : G) :
    ∃ k ∈ A.top.ker, ∃ r ∈ (cleanSection e hmem).range, k * r = g := by
  let r := cleanSection e hmem (A.top g)
  refine ⟨g * r⁻¹, ?_, r, ⟨A.top g, rfl⟩, ?_⟩
  · change A.top (g * r⁻¹) = 1
    rw [map_mul, map_inv, A.top_cleanSection e base hcoord hmem]
    simp
  · simp [mul_assoc]

theorem cleanRange_isComplement (e : B × I ≃ V) (base : B)
    (hcoord : ∀ b i, A.label (e (b, i)) = i)
    (hmem : ∀ p : alternatingGroup I, coordinatePureLift e p.val ∈ G) :
    A.top.ker.IsComplement' (cleanSection e hmem).range := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · exact disjoint_iff.mpr (A.kernel_inf_cleanRange e base hcoord hmem)
  · apply Set.eq_univ_iff_forall.mpr
    intro g
    obtain ⟨k, hk, r, hr, he⟩ := A.kernel_mul_cleanRange e base hcoord hmem g
    exact Set.mem_mul.mpr ⟨k, hk, r, hr, he⟩

noncomputable def cleanRangeEquiv (e : B × I ≃ V) (base : B)
    (hcoord : ∀ b i, A.label (e (b, i)) = i)
    (hmem : ∀ p : alternatingGroup I, coordinatePureLift e p.val ∈ G) :
    alternatingGroup I ≃* (cleanSection e hmem).range :=
  MonoidHom.ofInjective (A.cleanSection_injective e base hcoord hmem)

theorem cleanRange_ambient (e : B × I ≃ V)
    (hmem : ∀ p : alternatingGroup I, coordinatePureLift e p.val ∈ G) :
    (cleanSection e hmem).range.map G.subtype =
      (alternatingGroup I).map (coordinatePureLift e) := by
  ext x
  constructor
  · rintro ⟨g, ⟨p, rfl⟩, rfl⟩
    exact ⟨p.val, p.property, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨cleanSection e hmem ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, rfl⟩

end CleanBlockAction
end GI
