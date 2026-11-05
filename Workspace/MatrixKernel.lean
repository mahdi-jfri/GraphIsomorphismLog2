module

public import Workspace.SemiregularTwins
public import Workspace.Transport

@[expose] public section

namespace GI.Matrix

variable {L R : Type*}

def automorphisms (M : L → R → Bool) : Subgroup (Equiv.Perm L × Equiv.Perm R) where
  carrier := {p | ∀ x y, M (p.1 x) (p.2 y) = M x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro p q hp hq x y
    exact (hp (q.1 x) (q.2 y)).trans (hq x y)
  inv_mem' := by
    intro p hp x y
    simpa using (hp (p.1⁻¹ x) (p.2⁻¹ y)).symm

def rowPermutations (M : L → R → Bool) : Subgroup (Equiv.Perm L) where
  carrier := {p | ∀ x, M (p x) = M x}
  one_mem' := fun _ => rfl
  mul_mem' := fun hp hq x => (hp _).trans (hq x)
  inv_mem' := by
    intro p hp x
    simpa using (hp (p⁻¹ x)).symm

def left (M : L → R → Bool) : automorphisms M →* Equiv.Perm L :=
  (MonoidHom.fst _ _).comp (automorphisms M).subtype

def right (M : L → R → Bool) : automorphisms M →* Equiv.Perm R :=
  (MonoidHom.snd _ _).comp (automorphisms M).subtype

def rowLift (M : L → R → Bool) : rowPermutations M →* automorphisms M where
  toFun g := ⟨(g.val, 1), fun x y => congrFun (g.property x) y⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The kernel of the right action is exactly the row permutations which
move vertices only within classes having identical rows. -/
theorem right_kernel_left_image (M : L → R → Bool) :
    (right M).ker.map (left M) = rowPermutations M := by
  ext p
  constructor
  · rintro ⟨g, hg, rfl⟩
    change g.val.2 = 1 at hg
    intro x
    funext y
    simpa [left, hg] using g.property x y
  · intro hp
    exact ⟨rowLift M ⟨p, hp⟩, rfl, rfl⟩

variable [Fintype L] [Fintype R]

theorem row_mem_twins (M : L → R → Bool) (g : rowPermutations M) (x z : L) :
    g.val z ∈ Semiregular.twins M x ↔ z ∈ Semiregular.twins M x := by
  simp only [Semiregular.twins, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show M (g.val z) = M z from g.property z]

def twinAction (M : L → R → Bool) (x : L) :
    rowPermutations M →* Equiv.Perm (Semiregular.twins M x) where
  toFun g :=
    { toFun z := ⟨g.val z, (row_mem_twins M g x z).mpr z.property⟩
      invFun z := ⟨g.val⁻¹ z, (row_mem_twins M g⁻¹ x z).mpr z.property⟩
      left_inv z := by apply Subtype.ext; exact g.val.symm_apply_apply z
      right_inv z := by apply Subtype.ext; exact g.val.apply_symm_apply z }
  map_one' := by ext z; rfl
  map_mul' _ _ := by ext z; rfl

def twinProduct (M : L → R → Bool) :
    rowPermutations M →* (∀ x : L, Equiv.Perm (Semiregular.twins M x)) where
  toFun g x := twinAction M x g
  map_one' := by funext x; exact map_one (twinAction M x)
  map_mul' g h := by funext x; exact map_mul (twinAction M x) g h

/-- The actual right-action kernel embeds in a product of permutation groups
whose degrees are precisely the left twin-class sizes. -/
theorem twinProduct_injective (M : L → R → Bool) : Function.Injective (twinProduct M) := by
  intro g h heq
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hx : x ∈ Semiregular.twins M x := by simp [Semiregular.twins]
  exact congrArg (fun p => (p ⟨x, hx⟩).val) (congrFun heq x)

end GI.Matrix
