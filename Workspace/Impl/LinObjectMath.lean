import Workspace.Impl.TermRecProgTest

/-! Normalizing the paper's orbit colors. The glue contract allows two subgroup
lists under one color. Refining that color by the subgroup preserves transport. -/
namespace GI.Impl
open GI.Cited GI.Multicoset Equiv

variable {G : Type*} [Group G]

/-- A nonempty right coset determines its underlying left subgroup. -/
theorem linCosetLeftGroup_eq {L M : Subgroup G} {h k : G}
    (he : (fun l => l * h) '' (L : Set G) = (fun m => m * k) '' (M : Set G)) : L = M := by
  have hdiff (K : Subgroup G) (t x y : G)
      (hx : x ∈ (fun l => l * t) '' (K : Set G))
      (hy : y ∈ (fun l => l * t) '' (K : Set G)) : x * y⁻¹ ∈ K := by
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    simpa [mul_inv_rev, mul_assoc] using K.mul_mem ha (K.inv_mem hb)
  apply le_antisymm
  · intro l hl
    have hh : h ∈ (fun m => m * k) '' (M : Set G) := by
      rw [← he]; exact ⟨1, L.one_mem, by simp⟩
    have hlh : l * h ∈ (fun m => m * k) '' (M : Set G) := he ▸ ⟨l, hl, rfl⟩
    simpa using hdiff M k (l * h) h hlh hh
  · intro m hm
    have hk : k ∈ (fun l => l * h) '' (L : Set G) := by
      rw [he]; exact ⟨1, M.one_mem, by simp⟩
    have hmk : m * k ∈ (fun l => l * h) '' (L : Set G) := he.symm ▸ ⟨m, hm, rfl⟩
    simpa using hdiff L h (m * k) k hmk hk

/-- The equality test for unrestricted subgroup lists in TermGlueObjSpec. -/
theorem linObject_eq_iff {n : ℕ} (o o' : TmRiO n) :
    tmRiObj o = tmRiObj o' ↔ o.1 = o'.1 ∧ gens o.2.1 = gens o'.2.1 ∧
      o.2.2 * o'.2.2⁻¹ ∈ gens o.2.1 := by
  obtain ⟨c, ls, h⟩ := o
  obtain ⟨c', ms, k⟩ := o'
  constructor
  · intro he
    have ht := congrArg CObj.tag he
    have hs := congrArg CObj.coset he
    have hL := linCosetLeftGroup_eq hs
    refine ⟨ht, hL, ?_⟩
    have hh : h ∈ (tmRiObj (c, ls, h)).coset := ⟨1, (gens ls).one_mem, by simp⟩
    rw [he] at hh
    obtain ⟨m, hm, heq⟩ := hh
    rw [← hL] at hm
    simpa [← heq] using hm
  · rintro ⟨rfl, hL, hhk⟩
    have hh := (cobj_eq_iff (L := fun _ : ℕ => gens ls) (c := c) (c' := c) (h := h) (k := k)).mpr ⟨rfl, hhk⟩
    simpa only [tmRiObj, tmGlObj, cobj, hL] using hh

@[simp] theorem linObject_act {n : ℕ} (o : TmRiO n) (g : Perm (Fin n)) :
    tmRiObj o ↼ g = tmRiObj (o.1, o.2.1, o.2.2 * g) := by
  apply CObj.ext
  · rfl
  · simp only [tmRiObj, tmGlObj, cobj_act_coset, Set.image_image]
    simp only [mul_assoc]

/-- Replace generators by their compressed list and refine the color. -/
noncomputable def linObjectNorm {n : ℕ} (χ : TmRiO n → ℕ) (o : TmRiO n) : TmRiO n :=
  (χ o, GI.Lang.keepList o.2.1, o.2.2)

/-- The refined color condition is exactly what is needed for point transport.
It holds for first-index labels of (old color, generated subgroup). -/
theorem linObjectNorm_transport {n : ℕ} (χ : TmRiO n → ℕ) (o o' : TmRiO n)
    (hχ : χ o = χ o' ↔ o.1 = o'.1 ∧ gens o.2.1 = gens o'.2.1) (g : Perm (Fin n)) :
    tmRiObj (linObjectNorm χ o) ↼ g = tmRiObj (linObjectNorm χ o') ↔ tmRiObj o ↼ g = tmRiObj o' := by
  rw [linObject_act, linObject_act, linObject_eq_iff, linObject_eq_iff]
  simp only [linObjectNorm, GI.Lang.gens_keepList]
  rw [hχ]
  tauto

end GI.Impl
