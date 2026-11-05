module

public import Workspace.Impl.TermGlue

@[expose] public section

/-!
# One level of the recursion of Theorem A.20, in the form a program computes it (T5, mathematics)

`MulticosetSolvable.proc` makes its choices with `Classical.choose` and keeps the class
representatives of the profiles as colors (`CObj (Multiset Ω) G`). A program makes other choices
and uses numbers as colors. This file proves that the level is still correct with any choices:

* `tmRec_rl_iso`: renaming colors by a map injective on the colors that occur does not change
  transporters. So profiles may carry the number of their class representative as color.
* `tmRec_pair_eq`: the pairwise step with any chosen source point `x ∈ S` and any chosen point
  transporters `τ_y` ("fix `x ∈ S_i`, try every `y ∈ T_j`, and choose a point transporter")
  returns `Iso_H(S, T)`. `tmRec_pair_fix`: its recursive calls meet the preconditions (the
  kernel `A ∩ H_x` fixes both aligned subconfigurations).
* `tmRec_prof_obj`: the profile `A · Iso_H(r, S)` is the coset object `⟨σA ++ σr⟩ t` for
  generators `σr` of `Aut_H(r)` and any `t ∈ Iso_H(r, S)`.
* `tmRec_glue_pre`: when the profile call returns `B τ`, the preconditions P1–P5 of
  `TermGlueObjSpec` hold; `tmRec_prof_empty`: when it returns nothing, `Iso_H(X, Y) = ∅`.
-/

namespace GI.Impl

open GI.Multicoset Equiv
open GI.Cited (gens)

variable {G : Type} [Group G]

/-! ### Renaming colors -/

section Relabel

variable {κ κ' : Type}

/-- Rename the color of a coset object. -/
def tmRecRl (f : κ → κ') (o : CObj κ G) : CObj κ' G := ⟨f o.tag, o.coset⟩

theorem tmRecRl_act (f : κ → κ') (o : CObj κ G) (g : G) :
    tmRecRl f o ↼ g = tmRecRl f (o ↼ g) := rfl

theorem tmRecRl_map_act (f : κ → κ') (X : Multiset (CObj κ G)) (g : G) :
    X.map (tmRecRl f) ↼ g = (X ↼ g).map (tmRecRl f) := by
  rw [multiset_act_def, multiset_act_def, Multiset.map_map, Multiset.map_map]
  rfl

omit [Group G] in
/-- Renaming back with a left inverse on the colors that occur. -/
private theorem tmRec_rl_back {f : κ → κ'} {T : Set κ} (hf : Set.InjOn f T) [Nonempty κ]
    {X : Multiset (CObj κ G)} (hX : ∀ o ∈ X, o.tag ∈ T) :
    (X.map (tmRecRl f)).map (tmRecRl (Function.invFunOn f T)) = X := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id X]
  refine Multiset.map_congr rfl fun o ho => ?_
  simp only [Function.comp_apply, tmRecRl, id]
  exact CObj.ext (hf.leftInvOn_invFunOn (hX o ho)) rfl

/-- **Renaming colors keeps transporters**, when the renaming is injective on the colors of
both multisets. -/
theorem tmRec_rl_act_iff {f : κ → κ'} {T : Set κ} (hf : Set.InjOn f T)
    {X Y : Multiset (CObj κ G)} (hX : ∀ o ∈ X, o.tag ∈ T) (hY : ∀ o ∈ Y, o.tag ∈ T) (g : G) :
    X.map (tmRecRl f) ↼ g = Y.map (tmRecRl f) ↔ X ↼ g = Y := by
  constructor
  · intro h
    rw [tmRecRl_map_act] at h
    by_cases hne : Nonempty κ
    swap
    · have h0 : ∀ Z : Multiset (CObj κ G), Z = 0 := fun Z => by
        by_contra hZ
        obtain ⟨o, -⟩ := Multiset.exists_mem_of_ne_zero hZ
        exact hne ⟨o.tag⟩
      rw [h0 (X ↼ g), h0 Y]
    have hXg : ∀ o ∈ X ↼ g, o.tag ∈ T := by
      intro o ho
      rw [mem_act] at ho
      exact (hX _ ho : (o ↼ g⁻¹).tag ∈ T)
    rw [← tmRec_rl_back hf hXg, ← tmRec_rl_back hf hY, h]
  · intro h
    rw [tmRecRl_map_act, h]

theorem tmRec_rl_iso {f : κ → κ'} {T : Set κ} (hf : Set.InjOn f T)
    {X Y : Multiset (CObj κ G)} (hX : ∀ o ∈ X, o.tag ∈ T) (hY : ∀ o ∈ Y, o.tag ∈ T)
    (H : Subgroup G) : Iso H (X.map (tmRecRl f)) (Y.map (tmRecRl f)) = Iso H X Y := by
  ext h
  simp only [mem_iso]
  exact and_congr_right fun _ => tmRec_rl_act_iff hf hX hY h

end Relabel

/-! ### The pairwise step with any choices -/

section Pair

variable {Ω : Type} [RAct G Ω]

/-- **The pairwise step with any chosen point and point transporters.** For `x ∈ S` and, for
every `y ∈ T` that is an `H`-image of `x`, a chosen `τ_y ∈ H` with `x^{τ_y} = y`:
`Iso_H(S, T) = ⋃_y Iso_{H_x}(S, T^{τ_y⁻¹}) τ_y`. -/
theorem tmRec_pair_eq {H : Subgroup G} {S T : Multiset Ω} {x : Ω} (hx : x ∈ S) (τ : Ω → G)
    (hτ : ∀ y ∈ T, (∃ t ∈ H, x ↼ t = y) → τ y ∈ H ∧ x ↼ τ y = y) (h : G) :
    h ∈ Iso H S T ↔ ∃ y ∈ T, (∃ t ∈ H, x ↼ t = y) ∧
      ∃ k ∈ Iso (Aut H x) S (T ↼ (τ y)⁻¹), h = k * τ y := by
  constructor
  · rintro ⟨hh, he⟩
    have hy : x ↼ h ∈ T := by rw [← he]; exact act_mem_act h hx
    obtain ⟨hτH, hτx⟩ := hτ _ hy ⟨h, hh, rfl⟩
    refine ⟨x ↼ h, hy, ⟨h, hh, rfl⟩, h * (τ (x ↼ h))⁻¹, ⟨⟨H.mul_mem hh (H.inv_mem hτH), ?_⟩, ?_⟩,
      by group⟩
    · rw [← act_act, act_eq_iff, inv_inv]; exact hτx.symm
    · rw [← act_act, he]
  · rintro ⟨y, hy, hyH, k, ⟨hkx, hkS⟩, rfl⟩
    obtain ⟨hτH, -⟩ := hτ y hy hyH
    refine ⟨H.mul_mem (aut_le H x hkx) hτH, ?_⟩
    rw [← act_act, hkS, act_inv_act]

open scoped commutatorElement in
/-- **The recursive calls of the pairwise step meet their preconditions**: the kernel
`A ∩ H_x` fixes `S` and the aligned target `T^{τ⁻¹}` ("This kernel fixes the whole orbit"). -/
theorem tmRec_pair_fix {H N A : Subgroup G} (hNn : Normalizes H N) (hAH : A ≤ H)
    (hAn : Normalizes H A) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ N)
    {S T : Multiset Ω} (hS : ∀ s ∈ S, ∀ s' ∈ S, SameOrb A s s')
    (hT : ∀ t ∈ T, ∀ t' ∈ T, SameOrb A t t') (hNS : Fixes N S) {x : Ω} (hx : x ∈ S)
    {τ : G} (hτH : τ ∈ H) (hy : x ↼ τ ∈ T) :
    Fixes (A ⊓ Aut H x) S ∧ Fixes (A ⊓ Aut H x) (T ↼ τ⁻¹) := by
  have hfixorb : ∀ z, SameOrb A x z → ∀ c ∈ A ⊓ Aut H x, z ↼ c = z := by
    rintro z ⟨a, ha, rfl⟩ c ⟨hcA, hcx⟩
    refine abelian_stabilizer_fixes_orbit (N := N) ?_ ?_ hcA hcx.2 ha
    · intro a ha b hb
      simpa [commutatorElement_def] using hcomm a ha b hb
    · intro a' ha' n hn
      exact fixes_point_act (fun n hn => hNS n hn x hx) hNn (hAH ha') n hn
  refine ⟨fun c hc s hs => hfixorb s (hS x hx s hs) c hc, ?_⟩
  intro c hc z hz
  refine hfixorb z ?_ c hc
  rw [mem_act] at hz
  have h1 : SameOrb A (x ↼ τ) (z ↼ τ⁻¹⁻¹) := hT _ hy _ hz
  rw [inv_inv] at h1
  exact (sameOrb_act_iff hAn hτH).mp h1

end Pair

/-! ### Profiles as coset objects with number colors -/

section Prof

variable {Ω' : Type} [RAct G Ω']

/-- **The profile coset `A · Iso_H(r, S)` is the coset `(A ⊔ Aut_H(r)) t`** for any
`t ∈ Iso_H(r, S)` ("`H_{P_i} = A Aut_H(S_i)`, `Trans_H(P_i, P_j) = A Iso_H(S_i, S_j)`"). -/
theorem tmRec_prof_coset {H A : Subgroup G} (hAn : Normalizes H A) {r S : Ω'} {t : G}
    (ht : t ∈ Iso H r S) :
    {z | ∃ a ∈ A, ∃ g ∈ Iso H r S, z = a * g} =
      (fun l => l * t) '' ((A ⊔ Aut H r : Subgroup G) : Set G) := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, g, hg, rfl⟩
    refine ⟨a * (g * t⁻¹), Subgroup.mul_mem_sup ha ?_, by group⟩
    exact (mem_iso_iff_of_mem ht).mp hg
  · rintro ⟨l, hl, rfl⟩
    rw [Subgroup.sup_eq_closure] at hl
    have hn : Normalizes (Aut H r) A := hAn.mono (aut_le H r)
    obtain ⟨k, hk, a, ha, rfl⟩ := closure_mem_mul hn (Γ := (A : Set G) ∪ Aut H r) (by
      rintro γ (hγ | hγ)
      · exact ⟨1, (Aut H r).one_mem, γ, hγ, by group⟩
      · exact ⟨γ, hγ, 1, A.one_mem, by group⟩) l hl
    refine ⟨k * a * k⁻¹, hn k hk a ha, k * t, ?_, by group⟩
    exact (mem_iso_iff_of_mem ht).mpr (by simpa using hk)

end Prof

/-! ### The preconditions of the glue -/

section Glue

variable {Ω : Type} [RAct G Ω] {H A : Subgroup G} {P : Finset (Multiset Ω)}
  {pairf : Multiset Ω → Multiset Ω → Set G}

/-- The profiles of `U` with number colors `f`. -/
noncomputable def tmRecHat (A : Subgroup G) (P : Finset (Multiset Ω))
    (pairf : Multiset Ω → Multiset Ω → Set G) (f : Multiset Ω → ℕ) (U : Multiset Ω) :
    Multiset (CObj ℕ G) :=
  (hat A P pairf U).map (tmRecRl f)

private theorem hat_tags (hpair : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T) {U : Multiset Ω}
    (hU : pieces A U ⊆ P) : ∀ o ∈ hat A P pairf U, o.tag ∈ (P : Set (Multiset Ω)) := by
  intro o ho
  obtain ⟨S, hS, rfl⟩ := Multiset.mem_map.mp ho
  exact (classRep_spec hpair (hU hS)).1

/-- With number colors injective on the pieces, the profile transporter is unchanged. -/
theorem tmRecHat_iso (hpair : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T) {f : Multiset Ω → ℕ}
    (hf : Set.InjOn f P) {U V : Multiset Ω} (hU : pieces A U ⊆ P) (hV : pieces A V ⊆ P)
    (K : Subgroup G) :
    Iso K (tmRecHat A P pairf f U) (tmRecHat A P pairf f V) = Iso K (hat A P pairf U) (hat A P pairf V) :=
  tmRec_rl_iso hf (hat_tags hpair hU) (hat_tags hpair hV) K

/-- **The glue's preconditions hold** when the profile call returns the coset `B τ`
(`TermGlueObjSpec`, P1–P5 and `A ≤ B`). -/
theorem tmRec_glue_pre (hpair : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T) (hAH : A ≤ H)
    (hAn : Normalizes H A) {f : Multiset Ω → ℕ} (hf : Set.InjOn f P) {X Y : Multiset Ω}
    (hXP : pieces A X ⊆ P) (hYP : pieces A Y ⊆ P) {B : Subgroup G} {τ : G}
    (hiso : Iso H (tmRecHat A P pairf f X) (tmRecHat A P pairf f Y) = tmGlCoset B τ) :
    A ≤ B ∧ (∀ g ∈ B, Conf A X (X ↼ g)) ∧ (∀ g ∈ B, Conf A Y (X ↼ (g * τ))) ∧
      (∀ g ∈ B, Conf A Y (Y ↼ (τ⁻¹ * g * τ))) ∧ (∀ h ∈ Iso H X Y, h * τ⁻¹ ∈ B) ∧
      Aut H X ≤ B := by
  rw [tmRecHat_iso hpair hf hXP hYP] at hiso
  have hτ : τ ∈ Iso H (hat A P pairf X) (hat A P pairf Y) := by
    rw [hiso]; exact ⟨1, B.one_mem, one_mul τ⟩
  have hB : ∀ g, g ∈ B ↔ g * τ ∈ Iso H (hat A P pairf X) (hat A P pairf Y) := by
    intro g
    rw [hiso]
    constructor
    · intro hg; exact ⟨g, hg, rfl⟩
    · rintro ⟨b, hb, he⟩
      rwa [mul_right_cancel he] at hb
  have hautB : ∀ g, g ∈ Aut H (hat A P pairf X) ↔ g ∈ B := by
    intro g
    rw [hB, mem_iso_iff_of_mem hτ, mul_inv_cancel_right]
  have hBH : ∀ g ∈ B, g ∈ H := fun g hg => aut_le H _ ((hautB g).2 hg)
  have hτH : τ ∈ H := hτ.1
  -- transporters of `X` and `Y` carry the profiles
  have hcarry : ∀ {U V : Multiset Ω}, pieces A U ⊆ P → pieces A V ⊆ P → ∀ h ∈ Iso H U V,
      h ∈ Iso H (hat A P pairf U) (hat A P pairf V) := by
    intro U V hU hV h ⟨hh, he⟩
    refine ⟨hh, ?_⟩
    rw [hat_act hpair hAn hU hh (by rw [he]; exact hV), he]
  refine ⟨fun a ha => (hautB a).1 ⟨hAH ha, (hat_fix hpair hAn hXP).act_eq ha⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hg' := (hautB g).2 hg
    exact hat_conf hpair hAn hXP hXP hg'.1 hg'.2
  · intro g hg
    have hg' := (hB g).1 hg
    exact hat_conf hpair hAn hXP hYP hg'.1 hg'.2
  · intro g hg
    have hg' := (hB g).1 hg
    have hH : τ⁻¹ * g * τ ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hτH) (hBH g hg)) hτH
    refine hat_conf hpair hAn hYP hYP hH ?_
    rw [← hτ.2, act_act, show τ * (τ⁻¹ * g * τ) = g * τ by group]
    exact hg'.2.trans hτ.2.symm
  · intro h hh
    rw [hB, inv_mul_cancel_right]
    exact hcarry hXP hYP h hh
  · intro g hg
    exact (hautB g).1 (hcarry hXP hXP g hg)

/-- **An empty profile transporter means an empty transporter.** -/
theorem tmRec_prof_empty (hpair : ∀ S ∈ P, ∀ T ∈ P, pairf S T = Iso H S T)
    (hAn : Normalizes H A) {f : Multiset Ω → ℕ} (hf : Set.InjOn f P) {X Y : Multiset Ω}
    (hXP : pieces A X ⊆ P) (hYP : pieces A Y ⊆ P)
    (he : Iso H (tmRecHat A P pairf f X) (tmRecHat A P pairf f Y) = ∅) : Iso H X Y = ∅ := by
  rw [tmRecHat_iso hpair hf hXP hYP] at he
  ext h
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hh, hxy⟩
  have : h ∈ Iso H (hat A P pairf X) (hat A P pairf Y) := by
    refine ⟨hh, ?_⟩
    rw [hat_act hpair hAn hXP hh (by rw [hxy]; exact hYP), hxy]
  rw [he] at this
  exact this

end Glue

end GI.Impl
