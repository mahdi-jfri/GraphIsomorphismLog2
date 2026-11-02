import Workspace.Impl.LinObjectFrameMath

namespace GI.Impl

noncomputable def linObjectFrameRep {G V W : Type*} [Group G] [AddCommGroup V] [AddCommGroup W]
    (E : V ≃+ W) (ρ : G →* (V ≃+ V)) : G →* (W ≃+ W) where
  toFun g := (E.symm.trans (ρ g)).trans E
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

@[simp] theorem linObjectFrameRep_image {G V W : Type*} [Group G] [AddCommGroup V] [AddCommGroup W]
    (E : V ≃+ W) (ρ : G →* (V ≃+ V)) (g : G) (v : V) :
    linObjectFrameRep E ρ g (E v) = E (ρ g v) := by
  simp [linObjectFrameRep]

theorem linObjectFrameRep_cocycle {G V W : Type*} [Group G] [AddCommGroup V] [AddCommGroup W]
    (E : V ≃+ W) (ρ : G →* (V ≃+ V)) (c : G → V)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (g h : G) :
    E (c (g * h)) = linObjectFrameRep E ρ g (E (c h)) + E (c g) := by
  rw [hc,map_add,linObjectFrameRep_image]

end GI.Impl
