import Workspace.StabilizerImage

namespace GI.StabilizerQuotient.KernelQuotient

variable {G Q V W : Type*} [Group G] [Group Q] [MulAction G V] [MulAction Q W]
variable {φ : G →* Q}

theorem preimage_orbit_iff (f : KernelQuotient φ V W) (onto : Function.Surjective φ)
    (P : Subgroup Q) (x y : V) :
    (∃ g : G, φ g ∈ P ∧ g • x = y) ↔ ∃ p : P, (p : Q) • f.map x = f.map y := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨φ g, hg⟩, (f.equivariant g x).symm⟩
  · rintro ⟨p, hp⟩
    obtain ⟨g, hg⟩ := onto p.val
    have heq : f.map (g • x) = f.map y := by rw [f.equivariant, hg, hp]
    obtain ⟨k, hk, hky⟩ := (f.kernel_fibers _ _).mp heq
    refine ⟨k * g, ?_, ?_⟩
    · simpa only [map_mul, hk, one_mul, hg] using p.property
    · simpa only [mul_smul] using hky

/-- An ideal orbit pulls back to one actual physical orbit, since its fibers
are precisely the kernel orbits. -/
theorem preimage_eq_orbit (f : KernelQuotient φ V W) (onto : Function.Surjective φ)
    (P : Subgroup Q) (S : Set W)
    (preserved : ∀ p : P, ∀ w ∈ S, (p : Q) • w ∈ S)
    (transitive : ∀ w ∈ S, ∀ z ∈ S, ∃ p : P, (p : Q) • w = z)
    (x : V) (hx : f.map x ∈ S) :
    {y : V | f.map y ∈ S} = MulAction.orbit (P.comap φ) x := by
  ext y
  constructor
  · intro hy
    obtain ⟨g, hg, hgy⟩ := (f.preimage_orbit_iff onto P x y).mpr
      (transitive _ hx _ hy)
    exact ⟨⟨g, hg⟩, hgy⟩
  · rintro ⟨g, rfl⟩
    change f.map ((g : G) • x) ∈ S
    rw [f.equivariant]
    exact preserved ⟨φ g, g.property⟩ _ hx

def restrictedMap (f : KernelQuotient φ V W) (S : Set W) :
    {x : V // f.map x ∈ S} → S := fun x => ⟨f.map x, x.property⟩

theorem restrictedMap_surjective (f : KernelQuotient φ V W) (S : Set W) :
    Function.Surjective (f.restrictedMap S) := by
  rintro ⟨w, hw⟩
  obtain ⟨x, hx⟩ := f.onto w
  exact ⟨⟨x, hx.symm ▸ hw⟩, Subtype.ext hx⟩

variable [Fintype V] [Fintype W]

theorem card_factorization (f : KernelQuotient φ V W) (w : W) :
    Nat.card V = Nat.card W * Nat.card {x : V // f.map x = w} := by
  classical
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv f.map)
  rw [Fintype.card_sigma] at h
  have hc : ∀ z : W, Fintype.card {x : V // f.map x = z} =
      Fintype.card {x : V // f.map x = w} := by
    intro z
    simpa only [← Nat.card_eq_fintype_card] using f.equal_fibers z w
  simp_rw [hc] at h
  simpa using h.symm

theorem subset_count (f : KernelQuotient φ V W) (S : Set W) (w : W) :
    Nat.card {x : V // f.map x ∈ S} = Nat.card S * Nat.card {x : V // f.map x = w} := by
  classical
  have h := Fintype.card_congr (GI.fiberSubsetEquiv f.map S)
  rw [Fintype.card_sigma] at h
  have hc : ∀ z : S, Fintype.card {x : V // f.map x = z.val} =
      Fintype.card {x : V // f.map x = w} := by
    intro z
    simpa only [← Nat.card_eq_fintype_card] using f.equal_fibers z.val w
  simp_rw [hc] at h
  simpa using h

/-- Integer form of the exact physical fraction, without dividing by a
possibly empty cardinality. -/
theorem subset_fraction (f : KernelQuotient φ V W) (S : Set W) (w : W) :
    Nat.card {x : V // f.map x ∈ S} * Nat.card W = Nat.card S * Nat.card V := by
  rw [f.subset_count S w, f.card_factorization w]
  ac_rfl

end GI.StabilizerQuotient.KernelQuotient
