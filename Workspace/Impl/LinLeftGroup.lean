import Workspace.Impl.LinActionEmbedding
import Workspace.Impl.LinObjectColor

/-! A right translate preserves the left stabilizer of a set. Thus an object
can be relabeled by its numeric color and its underlying coset subgroup. -/
namespace GI.Impl
open GI.Multicoset
variable {G : Type*} [Group G]

def linLeftGroup (C : Set G) : Subgroup G where
  carrier := {g | ∀ x, g * x ∈ C ↔ x ∈ C}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh x
    simpa only [mul_assoc] using (hg (h * x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have hh := hg (g⁻¹ * x)
    simpa only [mul_inv_cancel_left] using hh.symm

private theorem linRightSet_mem (C : Set G) (h x : G) :
    x ∈ (fun c => c * h) '' C ↔ x * h⁻¹ ∈ C := by
  constructor
  · rintro ⟨c, hc, rfl⟩; simpa using hc
  · intro hx; exact ⟨x * h⁻¹, hx, by simp⟩

theorem linLeftGroup_right (C : Set G) (h : G) :
    linLeftGroup ((fun c => c * h) '' C) = linLeftGroup C := by
  ext g
  constructor
  · intro hg x
    have hh := hg (x * h)
    simpa only [linRightSet_mem, mul_assoc, mul_inv_cancel, mul_one] using hh
  · intro hg x
    have hh := hg (x * h⁻¹)
    simpa only [linRightSet_mem, mul_assoc] using hh

theorem linLeftGroup_coset (L : Subgroup G) (h : G) :
    linLeftGroup ((fun l => l * h) '' (L : Set G)) = L := by
  ext g
  constructor
  · intro hg
    have hh := (hg h).mpr (show h ∈ (fun l => l * h) '' (L : Set G) from ⟨1, L.one_mem, by simp⟩)
    obtain ⟨l, hl, he⟩ := hh
    have he' : l = g := mul_right_cancel he
    simpa only [he'] using hl
  · intro hg x
    simp only [linRightSet_mem]
    constructor
    · intro hx
      have hh := L.mul_mem (L.inv_mem hg) hx
      simpa [mul_assoc] using hh
    · intro hx
      simpa [mul_assoc] using L.mul_mem hg hx

/-- Refining by the left subgroup is a globally injective equivariant map,
including outside the finite list of currently occurring objects. -/
def linObjectRefine : linActEmbedding (G := G) (Ω := CObj ℕ G) (Ψ := CObj (ℕ × Subgroup G) G) where
  toFun o := ⟨(o.tag, linLeftGroup o.coset), o.coset⟩
  injective := by
    intro o o' h
    apply CObj.ext
    · exact congrArg (fun x : CObj (ℕ × Subgroup G) G => x.tag.1) h
    · exact congrArg (fun x : CObj (ℕ × Subgroup G) G => x.coset) h
  act o g := by
    apply CObj.ext
    · simp only [cobj_act_tag, cobj_act_coset, linLeftGroup_right]
    · rfl

@[simp] theorem linObjectRefine_apply {n : ℕ} (o : TmRiO n) :
    (linObjectRefine (G := Equiv.Perm (Fin n))).toFun (tmRiObj o) =
      ⟨(o.1, GI.Cited.gens o.2.1), (tmRiObj o).coset⟩ := by
  change (⟨(o.1, linLeftGroup ((fun l => l * o.2.2) '' (GI.Cited.gens o.2.1 : Set _))),
    (fun l => l * o.2.2) '' (GI.Cited.gens o.2.1 : Set _)⟩ : CObj (ℕ × Subgroup (Equiv.Perm (Fin n))) _) = _
  rw [linLeftGroup_coset]
  rfl

end GI.Impl
