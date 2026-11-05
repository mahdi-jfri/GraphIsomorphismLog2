module

public import Workspace.RectangleSides
public import Workspace.MatrixCaps

@[expose] public section

/-!
# The left overcoset of a rectangle answer and its cap

Lemma 5.1 and the paragraph "The returned parent cap" after Lemma A.28: the
permitted matrix transporter is projected to the left side `W`, extended by
arbitrary permutations of `Γ \ W`, and cut down to even permutations. The result
is `leftOvercoset M N`, a subset of `Alt Γ`. Its group is `leftGroup M`.

* every permitted matrix transporter lies in `leftOvercoset M N`;
* `leftOvercoset M N` is a left coset of `leftGroup M` once it is nonempty;
* `leftGroup M` has alternating-section width at most
  `max (max b |R|) (|Γ| - |W|)` when every left twin class has size at most `b`.
-/

namespace GI.SectionCaps

/-- A cap may be raised. -/
theorem mono {G : Type*} [Group G] {b c : ℕ} (bound : Cap G b) (hbc : b ≤ c) : Cap G c :=
  fun U k hk q onto => (bound U k hk q onto).trans hbc

end GI.SectionCaps

namespace GI.Rectangle

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α] {W R : Finset α}

/-- The side permutations of `h` transport the matrix `M` to `N`. -/
def MatrixTransports (M N : W → R → Bool) (h : permitted W R) : Prop :=
  ∀ a b, N ((sideAction h).1 a) ((sideAction h).2 b) = M a b

/-- The left projection of the permitted matrix transporter, extended by arbitrary
permutations of `Γ \ W`, with alternating parity imposed. -/
def leftOvercoset (M N : W → R → Bool) : Set (alternatingGroup α) :=
  {g | ∃ h : permitted W R, MatrixTransports M N h ∧
    ∀ a ∈ W, (g : Perm α) a = ((h : alternatingGroup α) : Perm α) a}

theorem matrixTransports_mul {M N P : W → R → Bool} {h k : permitted W R}
    (hk : MatrixTransports N P k) (hh : MatrixTransports M N h) :
    MatrixTransports M P (k * h) := by
  intro a b
  rw [map_mul]
  exact (hk _ _).trans (hh a b)

theorem matrixTransports_inv {M N : W → R → Bool} {h : permitted W R}
    (hh : MatrixTransports M N h) : MatrixTransports N M h⁻¹ := by
  intro a b
  have e := hh ((sideAction h⁻¹).1 a) ((sideAction h⁻¹).2 b)
  have e1 : (sideAction h).1 ((sideAction h⁻¹).1 a) = a := by
    rw [← Perm.mul_apply, ← Prod.fst_mul, ← map_mul, mul_inv_cancel, map_one]; rfl
  have e2 : (sideAction h).2 ((sideAction h⁻¹).2 b) = b := by
    rw [← Perm.mul_apply, ← Prod.snd_mul, ← map_mul, mul_inv_cancel, map_one]; rfl
  rw [e1, e2] at e
  exact e.symm

theorem matrixTransports_one (M : W → R → Bool) : MatrixTransports M M 1 := by
  intro a b
  rw [map_one]
  rfl

/-- The group of the overcoset: left parts of permitted matrix automorphisms. -/
def leftGroup (M : W → R → Bool) : Subgroup (alternatingGroup α) where
  carrier := leftOvercoset M M
  one_mem' := ⟨1, matrixTransports_one M, fun _ _ => rfl⟩
  mul_mem' := by
    rintro g g' ⟨h, hh, hg⟩ ⟨h', hh', hg'⟩
    refine ⟨h * h', matrixTransports_mul hh hh', fun a ha => ?_⟩
    have hmem : ((h' : alternatingGroup α) : Perm α) a ∈ W :=
      (left_mem_iff W R h' a).mpr ha
    change (g : Perm α) ((g' : Perm α) a) =
      ((h : alternatingGroup α) : Perm α) (((h' : alternatingGroup α) : Perm α) a)
    rw [hg' a ha, hg _ hmem]
  inv_mem' := by
    rintro g ⟨h, hh, hg⟩
    refine ⟨h⁻¹, matrixTransports_inv hh, fun a ha => ?_⟩
    have hmem : (((h : alternatingGroup α) : Perm α))⁻¹ a ∈ W :=
      (left_mem_iff W R h⁻¹ a).mpr ha
    change (g : Perm α)⁻¹ a = ((h : Perm α))⁻¹ a
    apply (g : Perm α).injective
    rw [Perm.apply_inv_self, hg _ hmem]
    rw [Perm.apply_inv_self]

theorem mem_leftGroup_iff (M : W → R → Bool) (g : alternatingGroup α) :
    g ∈ leftGroup M ↔ g ∈ leftOvercoset M M := Iff.rfl

/-- Every permitted matrix transporter lies in the overcoset. -/
theorem mem_leftOvercoset {M N : W → R → Bool} {h : permitted W R}
    (hh : MatrixTransports M N h) : (h : alternatingGroup α) ∈ leftOvercoset M N :=
  ⟨h, hh, fun _ _ => rfl⟩

/-- A nonempty overcoset is a left coset of its group. -/
theorem leftOvercoset_coset {M N : W → R → Bool} {g₀ : alternatingGroup α}
    (h₀ : g₀ ∈ leftOvercoset M N) (g : alternatingGroup α) :
    g ∈ leftOvercoset M N ↔ g₀⁻¹ * g ∈ leftGroup M := by
  obtain ⟨k, hk, hg₀⟩ := h₀
  -- On `W`, `g₀⁻¹` agrees with `k⁻¹`, since `g₀` and `k` agree on `W` and map it onto `W`.
  have inv_agree : ∀ a ∈ W, ((g₀ : Perm α))⁻¹ a = ((k : Perm α))⁻¹ a := by
    intro a ha
    have hmem : (((k : alternatingGroup α) : Perm α))⁻¹ a ∈ W :=
      (left_mem_iff W R k⁻¹ a).mpr ha
    apply (g₀ : Perm α).injective
    rw [Perm.apply_inv_self, hg₀ _ hmem]
    rw [Perm.apply_inv_self]
  constructor
  · rintro ⟨h, hh, hg⟩
    refine ⟨k⁻¹ * h, matrixTransports_mul (matrixTransports_inv hk) hh, fun a ha => ?_⟩
    have hmem : ((h : alternatingGroup α) : Perm α) a ∈ W := (left_mem_iff W R h a).mpr ha
    change ((g₀ : Perm α))⁻¹ ((g : Perm α) a) = ((k : Perm α))⁻¹ ((h : Perm α) a)
    rw [hg a ha]
    exact inv_agree _ hmem
  · rintro ⟨h, hh, hg⟩
    refine ⟨k * h, matrixTransports_mul hk hh, fun a ha => ?_⟩
    have hmem : ((h : alternatingGroup α) : Perm α) a ∈ W := (left_mem_iff W R h a).mpr ha
    have e := hg a ha
    change ((g₀ : Perm α))⁻¹ ((g : Perm α) a) = (h : Perm α) a at e
    change (g : Perm α) a = (k : Perm α) ((h : Perm α) a)
    rw [← hg₀ _ hmem, ← e, Perm.apply_inv_self]

/-! ### The cap -/

theorem leftGroup_maps (M : W → R → Bool) (g : leftGroup M) (a : α) :
    ((g : alternatingGroup α) : Perm α) a ∈ W ↔ a ∈ W := by
  obtain ⟨h, _, hg⟩ := g.property
  constructor
  · intro ha
    by_contra hna
    -- `g a = g a'` with `a' = h⁻¹ (g a) ∈ W`.
    have hmem : (((h : alternatingGroup α) : Perm α))⁻¹ ((g : Perm α) a) ∈ W :=
      (left_mem_iff W R h⁻¹ _).mpr ha
    have e := hg _ hmem
    change (g : Perm α) ((h : Perm α)⁻¹ ((g : Perm α) a)) =
      (h : Perm α) ((h : Perm α)⁻¹ ((g : Perm α) a)) at e
    rw [Perm.apply_inv_self] at e
    have := (g : Perm α).injective e
    exact hna (this ▸ hmem)
  · intro ha
    rw [hg a ha]
    exact (left_mem_iff W R h a).mpr ha

/-- Restriction of an element of `leftGroup M` to `W`. -/
def restrictLeft (M : W → R → Bool) (g : leftGroup M) : Perm W :=
  ((g : alternatingGroup α) : Perm α).subtypePerm (fun a => leftGroup_maps M g a)

theorem restrictLeft_mem (M : W → R → Bool) (g : leftGroup M) :
    restrictLeft M g ∈ (Matrix.left M).range := by
  obtain ⟨h, hh, hg⟩ := g.property
  refine ⟨⟨sideAction h, fun a b => hh a b⟩, ?_⟩
  ext a
  change ((h : alternatingGroup α) : Perm α) a = ((g : alternatingGroup α) : Perm α) a
  exact (hg a a.property).symm

/-- The restriction to `W`, as a homomorphism into the left projection of the
matrix automorphism group. -/
def leftRestriction (M : W → R → Bool) : leftGroup M →* (Matrix.left M).range where
  toFun g := ⟨restrictLeft M g, restrictLeft_mem M g⟩
  map_one' := by ext a; rfl
  map_mul' _ _ := by ext a; rfl

theorem outside_maps (M : W → R → Bool) (g : leftGroup M) (a : α) :
    ((g : alternatingGroup α) : Perm α) a ∉ W ↔ a ∉ W :=
  not_congr (leftGroup_maps M g a)

/-- The kernel of the restriction acts faithfully on `Γ \ W`. -/
def kernelOutside (M : W → R → Bool) :
    (leftRestriction M).ker →* Perm {a : α // a ∉ W} where
  toFun g := ((g.val : alternatingGroup α) : Perm α).subtypePerm
    (fun a => outside_maps M g.val a)
  map_one' := by ext a; rfl
  map_mul' _ _ := by ext a; rfl

theorem kernelOutside_injective (M : W → R → Bool) :
    Function.Injective (kernelOutside M) := by
  intro g g' e
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  ext a
  by_cases ha : a ∈ W
  · have h1 : restrictLeft M g.val ⟨a, ha⟩ = ⟨a, ha⟩ := by
      have := congrArg Subtype.val g.property
      exact congrArg (fun p : Perm W => p ⟨a, ha⟩) this
    have h2 : restrictLeft M g'.val ⟨a, ha⟩ = ⟨a, ha⟩ := by
      have := congrArg Subtype.val g'.property
      exact congrArg (fun p : Perm W => p ⟨a, ha⟩) this
    have e1 := congrArg Subtype.val h1
    have e2 := congrArg Subtype.val h2
    exact e1.trans e2.symm
  · have := congrArg (fun p : Perm {a : α // a ∉ W} => (p ⟨a, ha⟩ : α)) e
    exact this

theorem card_outside : Fintype.card {a : α // a ∉ W} = Fintype.card α - W.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_coe]

/-- The overcoset group has alternating-section width at most
`max (q - |W|) (max b |R|)`, where `b` bounds the left twin classes. -/
theorem leftGroup_cap (M : W → R → Bool) (b : ℕ)
    (sizes : ∀ x, (Semiregular.twins M x).card ≤ b) :
    SectionCaps.Cap (leftGroup M) (max (Fintype.card α - W.card) (max b R.card)) := by
  have hker : SectionCaps.Cap (leftRestriction M).ker (Fintype.card α - W.card) := by
    have h := SectionCaps.of_injective (kernelOutside M) (kernelOutside_injective M)
      (SectionCaps.permutations (V := {a : α // a ∉ W}))
    rwa [card_outside] at h
  have himage : SectionCaps.Cap (Matrix.left M).range (max b R.card) := by
    have h := SectionCaps.of_surjective _ (QuotientImage.range_surjective (Matrix.left M))
      (Matrix.matrix_cap M b sizes)
    simpa only [Fintype.card_coe] using h
  exact SectionCaps.extension (leftRestriction M) hker himage

end GI.Rectangle
