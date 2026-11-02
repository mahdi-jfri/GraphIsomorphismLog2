import Mathlib

/-!
# Linear groups: invariant subspaces and restriction

Basic notions for the order bound on solvable linear groups.

`K` is a field and `V` a `K`-vector space. A linear group is a subgroup `H` of the unit group of
`Module.End K V`. A subspace `W` is `H`-invariant if every element of `H` maps `W` into `W`.
`H` is *irreducible* if `0` and `V` are the only invariant subspaces, and *completely
reducible* if every invariant subspace has an invariant complement.

The main results:
* `GI.Proved.palfy_card_le_split`: if `V = W ⊕ W'` with both parts invariant, then `|H|` is at
  most the product of the orders of the restrictions of `H` to `W` and `W'`.
* `GI.Proved.palfy_clifford`: a normal subgroup of an irreducible group is completely
  reducible (Clifford).
-/

namespace GI.Proved

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

instance palfy_finite_end [Finite V] : Finite (Module.End K V) :=
  Finite.of_injective (fun f : Module.End K V => (f : V → V)) DFunLike.coe_injective

instance palfy_finite_units [Finite V] : Finite (Module.End K V)ˣ :=
  Finite.of_injective (fun u : (Module.End K V)ˣ => (u : Module.End K V)) Units.val_injective

/-- `W` is invariant under every element of `H`. -/
def palfyInv (H : Subgroup (Module.End K V)ˣ) (W : Submodule K V) : Prop :=
  ∀ h ∈ H, ∀ v ∈ W, (h : Module.End K V) v ∈ W

/-- `H` is irreducible: the only invariant subspaces are `0` and `V`. -/
def palfyIrr (H : Subgroup (Module.End K V)ˣ) : Prop :=
  ∀ W : Submodule K V, palfyInv H W → W = ⊥ ∨ W = ⊤

/-- `H` is completely reducible: every invariant subspace has an invariant complement. -/
def palfyCR (H : Subgroup (Module.End K V)ˣ) : Prop :=
  ∀ W : Submodule K V, palfyInv H W → ∃ W' : Submodule K V, palfyInv H W' ∧ IsCompl W W'

theorem palfyCR_of_irr {H : Subgroup (Module.End K V)ˣ} (h : palfyIrr H) : palfyCR H := by
  intro W hW
  rcases h W hW with rfl | rfl
  · exact ⟨⊤, fun _ _ _ _ => Submodule.mem_top, isCompl_bot_top⟩
  · exact ⟨⊥, fun _ _ v hv => by rw [(Submodule.mem_bot K).mp hv, map_zero]; exact zero_mem _,
      isCompl_top_bot⟩

/-- An invariant subspace is mapped into itself also by inverses. -/
theorem palfyInv.inv {H : Subgroup (Module.End K V)ˣ} {W : Submodule K V} (hW : palfyInv H W)
    {h : (Module.End K V)ˣ} (hh : h ∈ H) {v : V} (hv : v ∈ W) :
    ((h⁻¹ : (Module.End K V)ˣ) : Module.End K V) v ∈ W :=
  hW _ (H.inv_mem hh) v hv

/-- The restriction of `H` to an invariant subspace. -/
noncomputable def palfyRes (H : Subgroup (Module.End K V)ˣ) (W : Submodule K V)
    (hW : palfyInv H W) : H →* (Module.End K W)ˣ where
  toFun h :=
    { val := (h.1 : Module.End K V).restrict (fun v hv => hW h.1 h.2 v hv)
      inv := ((h.1⁻¹ : (Module.End K V)ˣ) : Module.End K V).restrict
        (fun v hv => hW.inv h.2 hv)
      val_inv := by
        ext v
        change ((h.1 * h.1⁻¹ : (Module.End K V)ˣ) : Module.End K V) v = v
        simp
      inv_val := by
        ext v
        change ((h.1⁻¹ * h.1 : (Module.End K V)ˣ) : Module.End K V) v = v
        simp }
  map_one' := by
    ext v
    simp [LinearMap.restrict_apply]
  map_mul' a b := by
    ext v
    simp [LinearMap.restrict_apply, Module.End.mul_apply]

theorem palfyRes_apply (H : Subgroup (Module.End K V)ˣ) (W : Submodule K V)
    (hW : palfyInv H W) (h : H) (w : W) :
    ((((palfyRes H W hW h : (Module.End K W)ˣ) : Module.End K W) w : W) : V) =
      (h.1 : Module.End K V) w := rfl

/-- The restricted group, as a subgroup of `GL(W)`. -/
noncomputable def palfyResGrp (H : Subgroup (Module.End K V)ˣ) (W : Submodule K V)
    (hW : palfyInv H W) : Subgroup (Module.End K W)ˣ :=
  (palfyRes H W hW).range

theorem palfyResGrp_solvable (H : Subgroup (Module.End K V)ˣ) [IsSolvable H] (W : Submodule K V)
    (hW : palfyInv H W) : IsSolvable (palfyResGrp H W hW) :=
  solvable_of_surjective (palfyRes H W hW).rangeRestrict_surjective

/-- A subspace of `W` invariant under the restricted group, viewed in `V`, is `H`-invariant. -/
theorem palfyInv_map {H : Subgroup (Module.End K V)ˣ} {W : Submodule K V} (hW : palfyInv H W)
    {U : Submodule K W} (hU : palfyInv (palfyResGrp H W hW) U) :
    palfyInv H (U.map W.subtype) := by
  rintro h hh _ ⟨u, hu, rfl⟩
  refine ⟨_, hU _ ⟨⟨h, hh⟩, rfl⟩ u hu, ?_⟩
  rfl

/-- An `H`-invariant subspace of `V` gives an invariant subspace of `W` by pulling back. -/
theorem palfyInv_comap {H : Subgroup (Module.End K V)ˣ} {W : Submodule K V} (hW : palfyInv H W)
    {U : Submodule K V} (hU : palfyInv H U) :
    palfyInv (palfyResGrp H W hW) (U.comap W.subtype) := by
  rintro _ ⟨h, rfl⟩ u hu
  exact hU h.1 h.2 _ hu

/-- The restriction of a completely reducible group to an invariant subspace is completely
reducible. -/
theorem palfyCR_res {H : Subgroup (Module.End K V)ˣ} (hH : palfyCR H) {W : Submodule K V}
    (hW : palfyInv H W) : palfyCR (palfyResGrp H W hW) := by
  intro U hU
  obtain ⟨X, hX, hc⟩ := hH _ (palfyInv_map hW hU)
  have hXW : palfyInv H (X ⊓ W) := fun h hh v hv => ⟨hX h hh v hv.1, hW h hh v hv.2⟩
  refine ⟨X.comap W.subtype, palfyInv_comap hW hX, ?_⟩
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro u ⟨hu1, hu2⟩
    have : (u : V) ∈ U.map W.subtype ⊓ X := ⟨⟨u, hu1, rfl⟩, hu2⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at this
    exact (Submodule.mem_bot K).mpr (Subtype.ext this)
  · rw [codisjoint_iff, eq_top_iff]
    rintro ⟨w, hw⟩ -
    have hw' : w ∈ U.map W.subtype ⊔ X := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw'
    obtain ⟨u, hu, rfl⟩ := ha
    have hbW : b ∈ W := by
      have : b = w - u := by rw [← hab]; simp
      rw [this]
      exact W.sub_mem hw u.2
    have : (⟨w, hw⟩ : W) = u + ⟨b, hbW⟩ := Subtype.ext (by simp [← hab])
    rw [this]
    exact Submodule.add_mem_sup hu (show (⟨b, hbW⟩ : W) ∈ X.comap W.subtype from hb)

/-- **Splitting.** If `V = W ⊕ W'` with both parts invariant, then `H` embeds in the product of
its restrictions, and `|V| = |W| |W'|`. -/
theorem palfy_card_le_split [Finite V] {H : Subgroup (Module.End K V)ˣ} {W W' : Submodule K V}
    (hW : palfyInv H W) (hW' : palfyInv H W') (hc : IsCompl W W') :
    Nat.card H ≤ Nat.card (palfyResGrp H W hW) * Nat.card (palfyResGrp H W' hW') ∧
      Nat.card V = Nat.card W * Nat.card W' := by
  constructor
  · rw [← Nat.card_prod]
    apply Nat.card_le_card_of_injective
      (fun h => ((⟨_, h, rfl⟩ : palfyResGrp H W hW), (⟨_, h, rfl⟩ : palfyResGrp H W' hW')))
    intro a b hab
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    have e1 := congrArg (fun u : (Module.End K W)ˣ => (((u : Module.End K W) ⟨x, hx⟩ : W) : V)) h1
    have e2 := congrArg (fun u : (Module.End K W')ˣ => (((u : Module.End K W') ⟨y, hy⟩ : W') : V)) h2
    simp only [palfyRes_apply] at e1 e2
    rw [map_add, map_add, e1, e2]
  · rw [← Nat.card_prod]
    exact Nat.card_congr (Submodule.prodEquivOfIsCompl W W' hc).toEquiv.symm

/-- `C` is normalized by `H`. -/
def palfyNormal (C H : Subgroup (Module.End K V)ˣ) : Prop :=
  C ≤ H ∧ ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C

/-- The image of a `C`-invariant subspace under an element of `H` is `C`-invariant. -/
theorem palfyInv_map_conj {C H : Subgroup (Module.End K V)ˣ} (hCH : palfyNormal C H)
    {U : Submodule K V} (hU : palfyInv C U) {h : (Module.End K V)ˣ} (hh : h ∈ H) :
    palfyInv C (U.map (h : Module.End K V)) := by
  rintro c hc _ ⟨u, hu, rfl⟩
  refine ⟨((h⁻¹ * c * h : (Module.End K V)ˣ) : Module.End K V) u, hU _ ?_ u hu, ?_⟩
  · have := hCH.2 _ (H.inv_mem hh) c hc
    simpa using this
  · change ((h * (h⁻¹ * c * h) : (Module.End K V)ˣ) : Module.End K V) u = _
    simp [mul_assoc]

/-- **Clifford.** A subgroup normalized by an irreducible group is completely reducible. -/
theorem palfy_clifford [Finite V] {C H : Subgroup (Module.End K V)ˣ} (hH : palfyIrr H)
    (hCH : palfyNormal C H) : palfyCR C := by
  intro W hW
  have hbot : palfyInv C ⊥ := fun _ _ v hv => by
    rw [(Submodule.mem_bot K).mp hv, map_zero]; exact zero_mem _
  obtain ⟨X, ⟨hX, hWX⟩, hXmax⟩ := (wellFounded_gt (α := Submodule K V)).has_min
    {X | palfyInv C X ∧ Disjoint W X} ⟨⊥, hbot, disjoint_bot_right⟩
  refine ⟨X, hX, hWX, ?_⟩
  rw [codisjoint_iff]
  by_contra hT
  by_cases hV : (⊥ : Submodule K V) = ⊤
  · apply hT
    rw [eq_top_iff, ← hV]
    exact bot_le
  have htop : palfyInv C ⊤ := fun _ _ _ _ => Submodule.mem_top
  obtain ⟨U, ⟨hU, hU0⟩, hUmin⟩ := (wellFounded_lt (α := Submodule K V)).has_min
    {U | palfyInv C U ∧ U ≠ ⊥} ⟨⊤, htop, fun h => hV h.symm⟩
  -- some conjugate of `U` is not inside `W ⊔ X`
  have hex : ∃ h ∈ H, ¬ U.map (h : Module.End K V) ≤ W ⊔ X := by
    by_contra hall
    push Not at hall
    let Y := Submodule.span K {v | ∃ h ∈ H, ∃ u ∈ U, (h : Module.End K V) u = v}
    have hY : palfyInv H Y := by
      intro g hg v hv
      have : Y.map (g : Module.End K V) ≤ Y := by
        rw [Submodule.map_span_le]
        rintro _ ⟨h, hh, u, hu, rfl⟩
        apply Submodule.subset_span
        refine ⟨g * h, H.mul_mem hg hh, u, hu, rfl⟩
      exact this ⟨v, hv, rfl⟩
    rcases hH Y hY with h0 | h0
    · apply hU0
      rw [eq_bot_iff]
      intro u hu
      have : u ∈ Y := Submodule.subset_span ⟨1, H.one_mem, u, hu, rfl⟩
      rwa [h0] at this
    · apply hT
      rw [eq_top_iff, ← h0, Submodule.span_le]
      rintro _ ⟨h, hh, u, hu, rfl⟩
      exact hall h hh ⟨u, hu, rfl⟩
  obtain ⟨h, hh, hS⟩ := hex
  set S := U.map (h : Module.End K V)
  have hSC : palfyInv C S := palfyInv_map_conj hCH hU hh
  -- `S` is a minimal `C`-invariant subspace, so it meets `W ⊔ X` trivially
  have hdis : Disjoint (W ⊔ X) S := by
    rw [disjoint_iff]
    by_contra hne
    have hI : palfyInv C ((W ⊔ X) ⊓ S) := fun c hc v hv =>
      ⟨Submodule.mem_sup.mpr (by
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv.1
        exact ⟨_, hW c hc a ha, _, hX c hc b hb, by rw [← map_add, hab]⟩), hSC c hc v hv.2⟩
    have hpre : palfyInv C (((W ⊔ X) ⊓ S).map
        ((h⁻¹ : (Module.End K V)ˣ) : Module.End K V)) :=
      palfyInv_map_conj hCH hI (H.inv_mem hh)
    have hle : ((W ⊔ X) ⊓ S).map ((h⁻¹ : (Module.End K V)ˣ) : Module.End K V) ≤ U := by
      rintro _ ⟨v, ⟨-, u, hu, rfl⟩, rfl⟩
      change ((h⁻¹ * h : (Module.End K V)ˣ) : Module.End K V) u ∈ U
      simpa using hu
    have hne' : ((W ⊔ X) ⊓ S).map ((h⁻¹ : (Module.End K V)ˣ) : Module.End K V) ≠ ⊥ := by
      intro h0
      apply hne
      rw [eq_bot_iff]
      intro v hv
      have : ((h⁻¹ : (Module.End K V)ˣ) : Module.End K V) v = 0 := by
        have : ((h⁻¹ : (Module.End K V)ˣ) : Module.End K V) v ∈
          ((W ⊔ X) ⊓ S).map ((h⁻¹ : (Module.End K V)ˣ) : Module.End K V) := ⟨v, hv, rfl⟩
        rwa [h0, Submodule.mem_bot] at this
      have hv' : v = (h : Module.End K V) (((h⁻¹ : (Module.End K V)ˣ) : Module.End K V) v) := by
        change v = ((h * h⁻¹ : (Module.End K V)ˣ) : Module.End K V) v
        simp
      rw [Submodule.mem_bot, hv', this, map_zero]
    have heq := eq_of_le_of_not_lt hle (hUmin _ ⟨hpre, hne'⟩)
    apply hS
    intro v hv
    have hv' : v ∈ (W ⊔ X) ⊓ S := by
      obtain ⟨u, hu, rfl⟩ := hv
      rw [← heq] at hu
      obtain ⟨w, hw, rfl⟩ := hu
      change ((h * h⁻¹ : (Module.End K V)ˣ) : Module.End K V) w ∈ _
      simpa using hw
    exact hv'.1
  have hX' : palfyInv C (X ⊔ S) := fun c hc v hv => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (hX c hc a ha) (hSC c hc b hb)
  have hWX' : Disjoint W (X ⊔ S) := hWX.disjoint_sup_right_of_disjoint_sup_left hdis
  apply hXmax (X ⊔ S) ⟨hX', hWX'⟩
  refine lt_of_le_of_ne le_sup_left ?_
  intro hXS
  apply hS
  rw [hXS]
  exact le_sup_right.trans le_sup_right

end GI.Proved
