import Workspace.DiagonalCarrier

/-!
# The cap of a colored partition

Section A.3, "Case 1 and balanced colored partitions": "Color ideal points by their orbit
lengths and, for a length `ℓ ≥ 2`, partition its color class into the actual `π(F_x)`-orbits.
… Its full allowed group is a subgroup of `Sym(ℓ) wr Sym(r)`. Therefore the full
colored-partition group has hereditary alternating-section width at most `q/2`, by the
extension and subgroup properties of that width."

A colored partition of a finite set `V` is a block map `blk : V → Finset V` (the block of each
point) and a color map `col : V → ℕ`, constant on blocks. `Perm V` acts on colored partitions by
relabeling. `colPart_cap`: if every block has at most `s` points and every color has at most
`s` blocks, the stabilizer has alternating-section width at most `s`. The kernel of the action
on the blocks acts inside the blocks, and the image permutes the blocks of each color.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

/-- **A colored partition** of `V`: the block of each point and the color of each point. -/
@[ext] structure ColPart (V : Type*) where
  blk : V → Finset V
  col : V → ℕ

namespace ColPart

variable {V : Type*}

/-- Relabeling of a colored partition by a permutation `σ`. -/
instance [DecidableEq V] : MulAction (Perm V) (ColPart V) where
  smul σ z := ⟨fun a => (z.blk (σ⁻¹ a)).map σ.toEmbedding, fun a => z.col (σ⁻¹ a)⟩
  one_smul z := by
    ext a b
    · change b ∈ (z.blk ((1 : Perm V)⁻¹ a)).map (1 : Perm V).toEmbedding ↔ b ∈ z.blk a
      simp
    · rfl
  mul_smul σ τ z := by
    ext a b
    · change b ∈ (z.blk ((σ * τ)⁻¹ a)).map (σ * τ).toEmbedding ↔
        b ∈ ((z.blk (τ⁻¹ (σ⁻¹ a))).map τ.toEmbedding).map σ.toEmbedding
      simp only [Finset.map_map, mul_inv_rev, Perm.mul_apply]
      rfl
    · rfl

@[simp] theorem smul_blk [DecidableEq V] (σ : Perm V) (z : ColPart V) (a : V) :
    (σ • z).blk a = (z.blk (σ⁻¹ a)).map σ.toEmbedding := rfl

@[simp] theorem smul_col [DecidableEq V] (σ : Perm V) (z : ColPart V) (a : V) :
    (σ • z).col a = z.col (σ⁻¹ a) := rfl

/-- `σ` fixes a colored partition exactly when it maps blocks to blocks and keeps colors. -/
theorem smul_eq_self_iff [DecidableEq V] (σ : Perm V) (z : ColPart V) :
    σ • z = z ↔ ∀ a, z.blk (σ a) = (z.blk a).map σ.toEmbedding ∧ z.col (σ a) = z.col a := by
  constructor
  · intro h a
    have h1 := congrArg (fun w : ColPart V => w.blk (σ a)) h
    have h2 := congrArg (fun w : ColPart V => w.col (σ a)) h
    simp only [smul_blk, smul_col, Perm.inv_apply_self] at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  · intro h
    ext a b
    · simp only [smul_blk]
      rw [← (h (σ⁻¹ a)).1, Perm.apply_inv_self]
    · simp only [smul_col]
      rw [← (h (σ⁻¹ a)).2, Perm.apply_inv_self]

end ColPart

open GI.SectionCaps

/-- **The cap of a colored partition.** Let `z` be a colored partition of `V`: every point lies
in its block and the color is constant on blocks. If every block has at most `s` points and every color has at most `s` blocks, every
group `H` that fixes `z` has alternating-section width at most `s`. -/
theorem colPart_cap {V : Type*} [Fintype V] [DecidableEq V] (z : ColPart V)
    (hmem : ∀ a, a ∈ z.blk a)
    (hcol : ∀ a b, b ∈ z.blk a → z.col b = z.col a) {s : ℕ}
    (hsize : ∀ a, (z.blk a).card ≤ s)
    (hcount : ∀ c : ℕ, ((Finset.univ.filter fun a => z.col a = c).image z.blk).card ≤ s)
    (H : Subgroup (Perm V)) (hH : ∀ σ ∈ H, σ • z = z) : Cap H s := by
  classical
  have hfix : ∀ σ ∈ H, ∀ a, z.blk (σ a) = (z.blk a).map σ.toEmbedding ∧
      z.col (σ a) = z.col a := fun σ hσ => (ColPart.smul_eq_self_iff σ z).1 (hH σ hσ)
  -- the blocks
  let X := {B : Finset V // ∃ a, z.blk a = B}
  have hmapX : ∀ σ ∈ H, ∀ B : X, ∃ a, z.blk a = B.val.map σ.toEmbedding := by
    rintro σ hσ ⟨B, a, rfl⟩
    exact ⟨σ a, (hfix σ hσ a).1⟩
  let act : H →* Perm X :=
    { toFun := fun σ =>
        { toFun := fun B => ⟨B.val.map (σ : Perm V).toEmbedding, hmapX σ σ.2 B⟩
          invFun := fun B => ⟨B.val.map (σ⁻¹ : Perm V).toEmbedding, hmapX _ (H.inv_mem σ.2) B⟩
          left_inv := fun B => by
            apply Subtype.ext
            simp [Finset.map_map]
          right_inv := fun B => by
            apply Subtype.ext
            simp [Finset.map_map] }
      map_one' := by ext B b; simp
      map_mul' := fun σ τ => by
        refine Equiv.ext fun B => Subtype.ext ?_
        change B.val.map ((σ * τ : H) : Perm V).toEmbedding =
          (B.val.map (τ : Perm V).toEmbedding).map (σ : Perm V).toEmbedding
        rw [Finset.map_map]
        rfl }
  -- the kernel acts inside the blocks
  have kernel : Cap act.ker s := by
    let ρ : act.ker →* Perm V := H.subtype.comp act.ker.subtype
    have faithful : Function.Injective ρ := fun a b h => Subtype.ext (Subtype.ext h)
    refine GI.Carrier.cap_of_fixed_labels ρ faithful z.blk ?_ ?_
    · intro g a
      have hg : act g.val = 1 := g.property
      have h1 := congrArg (fun p : Perm X => (p ⟨z.blk a, a, rfl⟩).val) hg
      simp only [Perm.one_apply] at h1
      change z.blk ((g.val : Perm V) a) = z.blk a
      rw [(hfix _ g.val.2 a).1]
      exact h1
    · intro B
      rw [Nat.card_eq_fintype_card]
      by_cases hB : ∃ a, z.blk a = B
      · obtain ⟨a, rfl⟩ := hB
        calc Fintype.card {x // z.blk x = z.blk a}
            ≤ (z.blk a).card := by
              rw [← Fintype.card_coe]
              refine Fintype.card_le_of_injective
                (fun x => ⟨x.val, by have h := hmem x.val; rwa [x.property] at h⟩) ?_
              intro x y h
              apply Subtype.ext
              have h' := congrArg (fun w : {v // v ∈ z.blk a} => w.val) h
              simpa using h'
          _ ≤ s := hsize a
      · have : IsEmpty {x // z.blk x = B} := ⟨fun x => hB ⟨x.val, x.property⟩⟩
        rw [Fintype.card_eq_zero]
        exact Nat.zero_le _
  -- the image permutes the blocks of each color
  let colX : X → {c // c ∈ Finset.univ.image z.col} := fun B =>
    ⟨z.col B.2.choose, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have colX_spec : ∀ (B : X) a, z.blk a = B.val → (colX B).val = z.col a := by
    intro B a ha
    have h := B.2.choose_spec
    have hm : a ∈ z.blk B.2.choose := by rw [h, ← ha]; exact hmem a
    exact (hcol _ _ hm).symm
  have image : Cap act.range s := by
    refine GI.Carrier.cap_of_fixed_labels act.range.subtype Subtype.val_injective colX ?_ ?_
    · rintro ⟨r, σ, rfl⟩ B
      obtain ⟨a, ha⟩ := B.2
      change colX (act σ B) = colX B
      apply Subtype.ext
      rw [colX_spec B a ha, colX_spec (act σ B) ((σ : Perm V) a)]
      · exact (hfix _ σ.2 a).2
      · change z.blk ((σ : Perm V) a) = B.val.map (σ : Perm V).toEmbedding
        rw [(hfix _ σ.2 a).1, ha]
    · intro c
      rw [Nat.card_eq_fintype_card]
      refine le_trans ?_ (hcount c.val)
      rw [← Fintype.card_coe]
      refine Fintype.card_le_of_injective (fun B => ⟨B.val.val, ?_⟩) ?_
      swap
      · intro B C h
        apply Subtype.ext; apply Subtype.ext
        have h' := congrArg (fun w : {B // B ∈ (Finset.univ.filter fun a => z.col a = c.val).image z.blk} => w.val) h
        simpa using h'
      obtain ⟨a, ha⟩ := B.val.2
      rw [Finset.mem_image]
      refine ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ha⟩
      rw [← colX_spec B.val a ha]
      exact congrArg Subtype.val B.property
  have h := extension act.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict]; exact kernel) image
  intro U k hk q onto
  have := h U k hk q onto
  omega

end GI.Algorithm
