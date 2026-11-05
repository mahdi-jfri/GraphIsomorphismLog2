module

public import Workspace.KernelQuotientFacts

@[expose] public section

namespace GI.StabilizerQuotient.KernelQuotient

variable {G Q V W : Type*} [Group G] [Group Q] [MulAction G V] [MulAction Q W]
variable {φ : G →* Q}

theorem orbitRel_iff (f : KernelQuotient φ V W) (x y : V) :
    MulAction.orbitRel φ.ker V x y ↔ f.map x = f.map y := by
  change (∃ k : φ.ker, (k : G) • y = x) ↔ _
  constructor
  · rintro ⟨k, hk⟩
    exact ((f.kernel_fibers y x).mpr ⟨k, k.property, hk⟩).symm
  · intro h
    obtain ⟨k, hk, hxy⟩ := (f.kernel_fibers y x).mp h.symm
    exact ⟨⟨k, hk⟩, hxy⟩

noncomputable def orbitEquiv (f : KernelQuotient φ V W) :
    Quotient (MulAction.orbitRel φ.ker V) ≃ W := by
  let q : Quotient (MulAction.orbitRel φ.ker V) → W :=
    Quotient.lift f.map (fun x y hxy => (f.orbitRel_iff x y).mp hxy)
  apply Equiv.ofBijective q
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        intro h
        exact Quotient.sound ((f.orbitRel_iff x y).mpr h)
  · intro w
    obtain ⟨x, rfl⟩ := f.onto w
    exact ⟨Quotient.mk _ x, rfl⟩

theorem orbitEquiv_apply (f : KernelQuotient φ V W) (x : V) :
    f.orbitEquiv (Quotient.mk _ x) = f.map x := rfl

theorem orbitEquiv_equivariant (f : KernelQuotient φ V W) (g : G) (x : V) :
    f.orbitEquiv (Quotient.mk _ (g • x)) = φ g • f.orbitEquiv (Quotient.mk _ x) :=
  f.equivariant g x

end GI.StabilizerQuotient.KernelQuotient
