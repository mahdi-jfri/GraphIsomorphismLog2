module

public import Workspace.Impl.TermRecMath

@[expose] public section

/-!
# One level of Theorem A.20 with the choices of the program (T5, mathematics)

`TermRecMath.lean` proves one level of the recursion for any choice of point and point
transporters, with the class representative of `MulticosetSolvable.classRep` (a
`Classical.epsilon` choice). The program of `TermRecProg*.lean` makes its own choices, and this
file proves the level with them.

* **The pairwise step, seen from the target.** The program fixes a point `x` of the target
  piece `T` and tries every `y ∈ S`, with `x^{τ_y} = y`. Then
  `Iso_H(S, T) = ⋃_y τ_y⁻¹ Iso_{H_x}(S^{τ_y⁻¹}, T)` (`tmRi_pair_eq`). This is the paper's step
  for `Iso_H(T, S)` ("fix `x ∈ S_i`, try every `y ∈ T_j`"), inverted: `Iso_H(S, T) =
  Iso_H(T, S)⁻¹` (`tmRi_mem_iso_inv`). The pieces are multiplied on the left, the form in which
  the program combines cosets (`GI.Lang.combine`). The recursive calls meet their
  preconditions by `tmRec_pair_fix` with `S` and `T` exchanged.
* **Profiles with the first representative.** The program takes as representative of the class
  of a piece `S` the first piece `ρ S` of its list with `Iso_H(ρ S, S) ≠ ∅`, and as color its
  position. `TmRiRep` lists what is used of this choice; `tmRiHat_act`, `tmRiHat_fix`,
  `tmRiHat_conf` are `hat_act`, `hat_fix`, `hat_conf` of `MulticosetSolvable` for it, and
  `tmRi_glue_pre`, `tmRi_prof_empty` are `tmRec_glue_pre`, `tmRec_prof_empty`.
* `tmRi_iso_coset`: a transporter is empty or a left coset, the form `combine` needs.
-/

namespace GI.Impl

open GI.Multicoset Equiv
open GI.Cited (gens)
open scoped Pointwise

variable {G : Type} [Group G]

/-! ### Transporters and inverses -/

section Inv

variable {Ω : Type} [RAct G Ω]

theorem tmRi_mem_iso_inv {H : Subgroup G} {X Y : Ω} {h : G} :
    h ∈ Iso H X Y ↔ h⁻¹ ∈ Iso H Y X := by
  constructor
  · exact iso_inv
  · intro hh; simpa using iso_inv hh

/-- **A transporter is empty or a left coset**: `Iso_H(X, Y) = t Aut_H(Y)` for `t` in it. -/
theorem tmRi_iso_coset (H : Subgroup G) (X Y : Ω) :
    Iso H X Y = ∅ ∨ ∃ (c : G) (K : Subgroup G), Iso H X Y = c • (K : Set G) := by
  rcases (Iso H X Y).eq_empty_or_nonempty with he | ⟨t, ht⟩
  · exact Or.inl he
  refine Or.inr ⟨t, Aut H Y, ?_⟩
  ext h
  simp only [Set.mem_smul_set, SetLike.mem_coe, smul_eq_mul]
  constructor
  · intro hh
    refine ⟨t⁻¹ * h, ⟨H.mul_mem (H.inv_mem ht.1) hh.1, ?_⟩, by group⟩
    rw [← ht.2, act_act, mul_inv_cancel_left, hh.2, ht.2]
  · rintro ⟨k, hk, rfl⟩
    exact iso_comp ht (show k ∈ Iso H Y Y from hk)

/-- **The pairwise step from the target.** For `x ∈ T` and, for every `y ∈ S` that is an
`H`-image of `x`, a chosen `τ_y ∈ H` with `x^{τ_y} = y`:
`Iso_H(S, T) = ⋃_y τ_y⁻¹ Iso_{H_x}(S^{τ_y⁻¹}, T)`. -/
theorem tmRi_pair_eq {H : Subgroup G} {S T : Multiset Ω} {x : Ω} (hx : x ∈ T) (τ : Ω → G)
    (hτ : ∀ y ∈ S, (∃ t ∈ H, x ↼ t = y) → τ y ∈ H ∧ x ↼ τ y = y) (h : G) :
    h ∈ Iso H S T ↔ ∃ y ∈ S, (∃ t ∈ H, x ↼ t = y) ∧
      ∃ k ∈ Iso (Aut H x) (S ↼ (τ y)⁻¹) T, h = (τ y)⁻¹ * k := by
  rw [tmRi_mem_iso_inv, tmRec_pair_eq hx τ hτ h⁻¹]
  constructor
  · rintro ⟨y, hy, hyH, k, hk, he⟩
    refine ⟨y, hy, hyH, k⁻¹, iso_inv hk, ?_⟩
    rw [← mul_inv_rev, ← he, inv_inv]
  · rintro ⟨y, hy, hyH, k, hk, rfl⟩
    exact ⟨y, hy, hyH, k⁻¹, iso_inv hk, by group⟩

end Inv

/-! ### Profiles with a chosen representative -/

section Prof

open Classical

variable {Ω : Type} [RAct G Ω] {H A : Subgroup G}

/-- The profile of a piece `S` with representative `rep S` and color `col S`: the coset object
`A · Iso_H(rep S, S)`. -/
def tmRiProf (H A : Subgroup G) (col : Multiset Ω → ℕ) (rep : Multiset Ω → Multiset Ω)
    (S : Multiset Ω) : CObj ℕ G :=
  ⟨col S, {z | ∃ a ∈ A, ∃ g ∈ Iso H (rep S) S, z = a * g}⟩

/-- What is used of the choice of representatives and colors on the pieces `P`: the
representative lies in the class, it depends only on the class, and two pieces have the same
color exactly when they lie in one class. -/
structure TmRiRep (H : Subgroup G) (P : Finset (Multiset Ω)) (col : Multiset Ω → ℕ)
    (rep : Multiset Ω → Multiset Ω) : Prop where
  nonempty : ∀ S ∈ P, (Iso H (rep S) S).Nonempty
  rep_eq : ∀ S ∈ P, ∀ S' ∈ P, (Iso H S S').Nonempty → rep S = rep S'
  col_iff : ∀ S ∈ P, ∀ S' ∈ P, col S = col S' ↔ (Iso H S S').Nonempty

variable {P : Finset (Multiset Ω)} {col : Multiset Ω → ℕ} {rep : Multiset Ω → Multiset Ω}

theorem tmRiProf_act (hr : TmRiRep H P col rep) {S : Multiset Ω} (hS : S ∈ P) {h : G}
    (hh : h ∈ H) (hSh : S ↼ h ∈ P) : tmRiProf H A col rep (S ↼ h) = tmRiProf H A col rep S ↼ h := by
  have hne : (Iso H S (S ↼ h)).Nonempty := ⟨h, hh, rfl⟩
  have hrep : rep S = rep (S ↼ h) := hr.rep_eq S hS _ hSh hne
  apply CObj.ext
  · exact ((hr.col_iff S hS _ hSh).2 hne).symm
  · rw [cobj_act_coset]
    simp only [tmRiProf, ← hrep]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, g, hg, rfl⟩
      refine ⟨a * (g * h⁻¹), ⟨a, ha, g * h⁻¹, ?_, rfl⟩, by group⟩
      have := (mem_iso_shift hh).mp hg
      simpa using this
    · rintro ⟨_, ⟨a, ha, g, hg, rfl⟩, rfl⟩
      exact ⟨a, ha, g * h, iso_comp hg ⟨hh, rfl⟩, by group⟩

theorem tmRiProf_fix (hAn : Normalizes H A) (S : Multiset Ω) {a : G} (ha : a ∈ A) :
    tmRiProf H A col rep S ↼ a = tmRiProf H A col rep S := by
  apply CObj.ext
  · rfl
  · rw [cobj_act_coset]
    simp only [tmRiProf]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨a', ha', g, hg, rfl⟩, rfl⟩
      exact ⟨a' * (g * a * g⁻¹), A.mul_mem ha' (hAn g hg.1 a ha), g, hg, by group⟩
    · rintro ⟨a', ha', g, hg, rfl⟩
      refine ⟨a' * (g * a⁻¹ * g⁻¹) * g, ⟨a' * (g * a⁻¹ * g⁻¹),
        A.mul_mem ha' (hAn g hg.1 _ (A.inv_mem ha)), g, hg, rfl⟩, by group⟩

theorem tmRiProf_eq (hr : TmRiRep H P col rep) (hAn : Normalizes H A) {S T : Multiset Ω}
    (hS : S ∈ P) (hT : T ∈ P) {τ : G}
    (he : tmRiProf H A col rep S ↼ τ = tmRiProf H A col rep T) : ∃ c ∈ A, S ↼ τ = T ↼ c := by
  have hcol : col S = col T := congrArg CObj.tag he
  have hrep : rep S = rep T := hr.rep_eq S hS T hT ((hr.col_iff S hS T hT).1 hcol)
  obtain ⟨i, hi⟩ := hr.nonempty S hS
  have hmem : i * τ ∈ (tmRiProf H A col rep S ↼ τ).coset := by
    rw [cobj_act_coset]
    exact ⟨i, ⟨1, A.one_mem, i, hi, by simp⟩, rfl⟩
  rw [he] at hmem
  obtain ⟨a, ha, j, hj, hij⟩ := hmem
  rw [← hrep] at hj
  refine ⟨j⁻¹ * a * j, hAn.inv hj.1 ha, ?_⟩
  rw [← hi.2, act_act, hij, ← hj.2, act_act]
  congr 1; group

/-- The multiset of profiles of `U`. -/
noncomputable def tmRiHat (H A : Subgroup G) (col : Multiset Ω → ℕ)
    (rep : Multiset Ω → Multiset Ω) (U : Multiset Ω) : Multiset (CObj ℕ G) :=
  (pieces A U).val.map (tmRiProf H A col rep)

theorem tmRiHat_act (hr : TmRiRep H P col rep) (hAn : Normalizes H A) {U : Multiset Ω}
    (hU : pieces A U ⊆ P) {h : G} (hh : h ∈ H) (hUh : pieces A (U ↼ h) ⊆ P) :
    tmRiHat H A col rep U ↼ h = tmRiHat H A col rep (U ↼ h) := by
  unfold tmRiHat
  rw [multiset_act_def, Multiset.map_map, pieces_act hAn hh,
    Finset.image_val_of_injOn (fun x _ y _ hxy => act_injective h hxy), Multiset.map_map]
  apply Multiset.map_congr rfl
  intro S hS
  have hS' : S ∈ pieces A U := hS
  simp only [Function.comp_apply]
  refine (tmRiProf_act hr (hU hS') hh (hUh ?_)).symm
  rw [pieces_act hAn hh]
  exact Finset.mem_image_of_mem _ hS'

theorem tmRiHat_fix (hAn : Normalizes H A) (U : Multiset Ω) :
    Fixes A (tmRiHat H A col rep U) := by
  intro a ha o ho
  obtain ⟨S, -, rfl⟩ := Multiset.mem_map.mp ho
  exact tmRiProf_fix hAn S ha

/-- Equal profile multisets give configurations. -/
theorem tmRiHat_conf (hr : TmRiRep H P col rep) (hAn : Normalizes H A) {U V : Multiset Ω}
    (hU : pieces A U ⊆ P) (hV : pieces A V ⊆ P) {τ : G} (hτ : τ ∈ H)
    (he : tmRiHat H A col rep U ↼ τ = tmRiHat H A col rep V) : Conf A V (U ↼ τ) := by
  have hfwd : ∀ S ∈ pieces A U, ∃ T ∈ pieces A V, ∃ c ∈ A, S ↼ τ = T ↼ c := by
    intro S hS
    have hm : tmRiProf H A col rep S ↼ τ ∈ tmRiHat H A col rep V := by
      rw [← he]; exact act_mem_act τ (Multiset.mem_map_of_mem _ hS)
    obtain ⟨T, hT, hTe⟩ := Multiset.mem_map.mp hm
    exact ⟨T, hT, tmRiProf_eq hr hAn (hU hS) (hV hT) hTe.symm⟩
  have hbwd : ∀ T ∈ pieces A V, ∃ S ∈ pieces A U, ∃ c ∈ A, S ↼ τ = T ↼ c := by
    intro T hT
    have hm : tmRiProf H A col rep T ∈ tmRiHat H A col rep U ↼ τ := by
      rw [he]; exact Multiset.mem_map_of_mem _ hT
    rw [mem_act] at hm
    obtain ⟨S, hS, hSe⟩ := Multiset.mem_map.mp hm
    refine ⟨S, hS, tmRiProf_eq hr hAn (hU hS) (hV hT) ?_⟩
    rw [hSe, act_inv_act]
  apply conf_of_parts
  · intro z hz
    rw [mem_act] at hz
    have hS : partAt A U {z ↼ τ⁻¹} ∈ pieces A U := mem_pieces.mpr ⟨_, hz, rfl⟩
    obtain ⟨T, hT, c, hc, hSc⟩ := hfwd _ hS
    have hzS : z ∈ partAt A U {z ↼ τ⁻¹} ↼ τ := by
      rw [mem_act]; exact mem_piece_iff.mpr ⟨hz, sameOrb_refl A _⟩
    rw [hSc, mem_act] at hzS
    exact ⟨z ↼ c⁻¹, Multiset.mem_of_le (piece_le hT) hzS, ⟨c, hc, by simp⟩⟩
  · intro T hT
    obtain ⟨S, hS, c, hc, hSc⟩ := hbwd T hT
    refine ⟨c, hc, ?_⟩
    obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero (piece_ne_zero hT)
    have hcong : partAt A (U ↼ τ) T = partAt A (U ↼ τ) (S ↼ τ) := by
      apply partAt_congr (t₀ := t)
      · intro s hs; exact piece_sameOrb hT ht hs
      · intro s hs
        rw [hSc, mem_act] at hs
        exact (piece_sameOrb hT ht hs).trans ⟨c, hc, by simp⟩
      · exact piece_ne_zero hT
      · exact act_ne_zero (piece_ne_zero hS) τ
    rw [hcong, partAt_act hAn hτ, partAt_piece hS, hSc]

/-- Transporters of `U` and `V` carry the profiles. -/
theorem tmRiHat_carry (hr : TmRiRep H P col rep) (hAn : Normalizes H A) {U V : Multiset Ω}
    (hU : pieces A U ⊆ P) (hV : pieces A V ⊆ P) {h : G} (hh : h ∈ Iso H U V) :
    h ∈ Iso H (tmRiHat H A col rep U) (tmRiHat H A col rep V) := by
  refine ⟨hh.1, ?_⟩
  rw [tmRiHat_act hr hAn hU hh.1 (by rw [hh.2]; exact hV), hh.2]

/-- **The glue's preconditions hold** when the profile call returns the coset `B τ`
(`TermGlueObjSpec`, P1–P5 and `A ≤ B`). -/
theorem tmRi_glue_pre (hr : TmRiRep H P col rep) (hAH : A ≤ H) (hAn : Normalizes H A)
    {X Y : Multiset Ω} (hXP : pieces A X ⊆ P) (hYP : pieces A Y ⊆ P) {B : Subgroup G} {τ : G}
    (hiso : Iso H (tmRiHat H A col rep X) (tmRiHat H A col rep Y) = tmGlCoset B τ) :
    A ≤ B ∧ (∀ g ∈ B, Conf A X (X ↼ g)) ∧ (∀ g ∈ B, Conf A Y (X ↼ (g * τ))) ∧
      (∀ g ∈ B, Conf A Y (Y ↼ (τ⁻¹ * g * τ))) ∧ (∀ h ∈ Iso H X Y, h * τ⁻¹ ∈ B) ∧
      Aut H X ≤ B := by
  have hτ : τ ∈ Iso H (tmRiHat H A col rep X) (tmRiHat H A col rep Y) := by
    rw [hiso]; exact ⟨1, B.one_mem, one_mul τ⟩
  have hB : ∀ g, g ∈ B ↔ g * τ ∈ Iso H (tmRiHat H A col rep X) (tmRiHat H A col rep Y) := by
    intro g
    rw [hiso]
    constructor
    · intro hg; exact ⟨g, hg, rfl⟩
    · rintro ⟨b, hb, he⟩
      rwa [mul_right_cancel he] at hb
  have hautB : ∀ g, g ∈ Aut H (tmRiHat H A col rep X) ↔ g ∈ B := by
    intro g
    rw [hB, mem_iso_iff_of_mem hτ, mul_inv_cancel_right]
  have hBH : ∀ g ∈ B, g ∈ H := fun g hg => aut_le H _ ((hautB g).2 hg)
  have hτH : τ ∈ H := hτ.1
  refine ⟨fun a ha => (hautB a).1 ⟨hAH ha, (tmRiHat_fix hAn X).act_eq ha⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hg' := (hautB g).2 hg
    exact tmRiHat_conf hr hAn hXP hXP hg'.1 hg'.2
  · intro g hg
    have hg' := (hB g).1 hg
    exact tmRiHat_conf hr hAn hXP hYP hg'.1 hg'.2
  · intro g hg
    have hg' := (hB g).1 hg
    have hH : τ⁻¹ * g * τ ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hτH) (hBH g hg)) hτH
    refine tmRiHat_conf hr hAn hYP hYP hH ?_
    rw [← hτ.2, act_act, show τ * (τ⁻¹ * g * τ) = g * τ by group]
    exact hg'.2.trans hτ.2.symm
  · intro h hh
    rw [hB, inv_mul_cancel_right]
    exact tmRiHat_carry hr hAn hXP hYP hh
  · intro g hg
    exact (hautB g).1 (tmRiHat_carry hr hAn hXP hXP hg)

/-- **An empty profile transporter means an empty transporter.** -/
theorem tmRi_prof_empty (hr : TmRiRep H P col rep) (hAn : Normalizes H A) {X Y : Multiset Ω}
    (hXP : pieces A X ⊆ P) (hYP : pieces A Y ⊆ P)
    (he : Iso H (tmRiHat H A col rep X) (tmRiHat H A col rep Y) = ∅) : Iso H X Y = ∅ := by
  ext h
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hh
  have := tmRiHat_carry hr hAn hXP hYP hh
  rw [he] at this
  exact this

end Prof

end GI.Impl
