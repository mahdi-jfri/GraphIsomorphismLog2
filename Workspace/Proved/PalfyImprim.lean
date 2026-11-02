import Workspace.Proved.PalfyRing
import Workspace.Proved.SolvOrder

/-!
# The imprimitive step

Let `H` be an irreducible solvable linear group on `V` over a finite field `K` with `q`
elements, and let `R` be a commutative algebra normalized by `H` that has an idempotent other
than `0` and `1`. Let `e_1, …, e_t` be the minimal idempotents of `R`, so `t ≥ 2`, and let
`W_i = e_i V`. Assume the bound `24 q^6 |G|^3 ≤ |W|^E` for every smaller space `W` and every
solvable completely reducible `G ≤ GL(W)`. Then `24 q^6 |H|^3 ≤ |V|^E`
(`GI.Proved.palfy_imprimitive`).

*Proof.* `H` permutes the `e_i` by conjugation. Let `S` be the image in `Sym(t)` and `L` the
kernel. Dixon's bound gives `|S|^3 ≤ 24^{t-1}`. The stabilizer `H_i` of `e_i` maps `W_i` into
itself, and its restriction `G_i` to `W_i` is irreducible: for a `G_i`-invariant `U ⊆ W_i`, the
span `Y` of all `h U` with `h ∈ H` is `H`-invariant, and `e_i Y = U` because `e_i h U = 0` when
`h e_i h⁻¹ ≠ e_i`. Since `∑ e_i = 1`, the group `L` embeds in `∏ G_i`, and `∏ |W_i| ≤ |V|`
because the `e_i` are orthogonal. So
`24 q^6 |H|^3 ≤ 24 q^6 · 24^{t-1} ∏ |G_i|^3 ≤ ∏ 24 q^6 |G_i|^3 ≤ ∏ |W_i|^E ≤ |V|^E`.
-/

namespace GI.Proved

/-- The induction hypothesis over a fixed field: the bound holds below size `n`. -/
def PalfyIH (K : Type) [Field K] (E n : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module K W] [Finite W] [Nontrivial W], Nat.card W < n →
    ∀ G : Subgroup (Module.End K W)ˣ, IsSolvable G → palfyCR G →
      24 * Nat.card K ^ 6 * Nat.card G ^ 3 ≤ Nat.card W ^ E

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/-- The elements of `H` that commute with `e`. -/
def palfyStab (H : Subgroup (Module.End K V)ˣ) (e : Module.End K V) :
    Subgroup (Module.End K V)ˣ where
  carrier := {h | h ∈ H ∧ (h : Module.End K V) * e = e * (h : Module.End K V)}
  mul_mem' := by
    rintro a b ⟨ha, hae⟩ ⟨hb, hbe⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    simp only [Units.val_mul]
    rw [mul_assoc, hbe, ← mul_assoc, hae, mul_assoc]
  one_mem' := ⟨H.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, hae⟩
    refine ⟨H.inv_mem ha, ?_⟩
    have h1 : ((a⁻¹ : (Module.End K V)ˣ) : Module.End K V) * (a : Module.End K V) = 1 :=
      Units.inv_mul a
    have h2 : (a : Module.End K V) * ((a⁻¹ : (Module.End K V)ˣ) : Module.End K V) = 1 :=
      Units.mul_inv a
    set a' := ((a⁻¹ : (Module.End K V)ˣ) : Module.End K V)
    calc a' * e = a' * e * ((a : Module.End K V) * a') := by rw [h2, mul_one]
      _ = a' * (e * (a : Module.End K V)) * a' := by simp only [mul_assoc]
      _ = a' * ((a : Module.End K V) * e) * a' := by rw [hae]
      _ = (a' * (a : Module.End K V)) * e * a' := by simp only [mul_assoc]
      _ = e * a' := by rw [h1, one_mul]

theorem palfyStab_le (H : Subgroup (Module.End K V)ˣ) (e : Module.End K V) :
    palfyStab H e ≤ H := fun _ h => h.1

/-- The stabilizer of `e` maps `e V` into itself. -/
theorem palfyStab_inv (H : Subgroup (Module.End K V)ˣ) (e : Module.End K V) :
    palfyInv (palfyStab H e) (LinearMap.range e) := by
  rintro h ⟨-, he⟩ _ ⟨v, rfl⟩
  refine ⟨(h : Module.End K V) v, ?_⟩
  change (e * (h : Module.End K V)) v = ((h : Module.End K V) * e) v
  rw [he]

theorem palfy_conj_eq_iff (h : (Module.End K V)ˣ) (e : Module.End K V) :
    (h : Module.End K V) * e * ((h⁻¹ : (Module.End K V)ˣ) : Module.End K V) = e ↔
      (h : Module.End K V) * e = e * (h : Module.End K V) := by
  constructor
  · intro h1
    calc (h : Module.End K V) * e
        = (h : Module.End K V) * e * (((h⁻¹ : (Module.End K V)ˣ) : Module.End K V) *
          (h : Module.End K V)) := by rw [Units.inv_mul, mul_one]
      _ = e * (h : Module.End K V) := by rw [← mul_assoc, h1]
  · intro h1
    rw [h1, mul_assoc, Units.mul_inv, mul_one]

section

variable [Finite V] {H : Subgroup (Module.End K V)ˣ} {R : Subalgebra K (Module.End K V)}

/-- The restriction of the stabilizer of a minimal idempotent `e` to `e V` is irreducible. -/
theorem palfy_stab_irr (hH : palfyIrr H) (hR : PalfyAlg H R) {e : Module.End K V}
    (he : e ∈ palfyMinIdem R) :
    palfyIrr (palfyResGrp (palfyStab H e) _ (palfyStab_inv H e)) := by
  intro U hU
  set U' := U.map (LinearMap.range e).subtype
  have hU' : palfyInv (palfyStab H e) U' := palfyInv_map _ hU
  have heW : ∀ w ∈ LinearMap.range e, e w = w := by
    rintro _ ⟨v, rfl⟩
    rw [← Module.End.mul_apply, he.2.1.eq]
  have hU'W : U' ≤ LinearMap.range e := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  let Y := Submodule.span K {v | ∃ h ∈ H, ∃ u ∈ U', (h : Module.End K V) u = v}
  have hY : palfyInv H Y := by
    intro g hg v hv
    have : Y.map (g : Module.End K V) ≤ Y := by
      rw [Submodule.map_span_le]
      rintro _ ⟨h, hh, u, hu, rfl⟩
      exact Submodule.subset_span ⟨g * h, H.mul_mem hg hh, u, hu, rfl⟩
    exact this ⟨v, hv, rfl⟩
  have heY : ∀ y ∈ Y, e y ∈ U' := by
    intro y hy
    have : Y ≤ U'.comap e := by
      rw [Submodule.span_le]
      rintro _ ⟨h, hh, u, hu, rfl⟩
      change e ((h : Module.End K V) u) ∈ U'
      by_cases hs : (h : Module.End K V) * e = e * (h : Module.End K V)
      · rw [← Module.End.mul_apply, ← hs, Module.End.mul_apply, heW u (hU'W hu)]
        exact hU' h ⟨hh, hs⟩ u hu
      · have hne : (h : Module.End K V) * e * ((h⁻¹ : (Module.End K V)ˣ) : Module.End K V) ≠ e :=
          fun h1 => hs ((palfy_conj_eq_iff h e).mp h1)
        have h0 := palfy_minIdem_mul hR he (palfy_minIdem_conj hR hh he) hne.symm
        have : e ((h : Module.End K V) u) = (e * ((h : Module.End K V) * e *
            ((h⁻¹ : (Module.End K V)ˣ) : Module.End K V))) ((h : Module.End K V) u) := by
          simp only [Module.End.mul_apply]
          congr 1
          change _ = (h : Module.End K V) (e ((((h⁻¹ * h : (Module.End K V)ˣ)) :
            Module.End K V) u))
          rw [inv_mul_cancel, Units.val_one, Module.End.one_apply, heW u (hU'W hu)]
        rw [this, h0]
        exact zero_mem _
    exact this hy
  rcases hH Y hY with h0 | h0
  · left
    rw [eq_bot_iff]
    intro u hu
    have : (u : V) ∈ Y := Submodule.subset_span ⟨1, H.one_mem, u, ⟨u, hu, rfl⟩, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    exact (Submodule.mem_bot K).mpr (Subtype.ext this)
  · right
    rw [eq_top_iff]
    intro u _
    have h1 := heY u (by rw [h0]; exact Submodule.mem_top)
    rw [heW u u.2] at h1
    obtain ⟨u', hu', hu'u⟩ := h1
    rw [← Subtype.ext hu'u]
    exact hu'

/-- `H` permutes the minimal idempotents. -/
noncomputable def palfyPermHom (hR : PalfyAlg H R) :
    H →* Equiv.Perm {e // e ∈ (palfy_minIdem_finite R).toFinset} where
  toFun h :=
    { toFun := fun e => ⟨((h : (Module.End K V)ˣ) : Module.End K V) * e * (((h : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V),
        (Set.Finite.mem_toFinset _).mpr (palfy_minIdem_conj hR h.2
          ((Set.Finite.mem_toFinset _).mp e.2))⟩
      invFun := fun e => ⟨(((h : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V) * e * ((h : (Module.End K V)ˣ) : Module.End K V),
        (Set.Finite.mem_toFinset _).mpr (by
          have := palfy_minIdem_conj hR (H.inv_mem h.2) ((Set.Finite.mem_toFinset _).mp e.2)
          rwa [inv_inv] at this)⟩
      left_inv := fun e => by
        apply Subtype.ext
        change (((h : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V) * (((h : (Module.End K V)ˣ) : Module.End K V) * e *
          (((h : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V)) * ((h : (Module.End K V)ˣ) : Module.End K V) = e
        have h1 : (((h : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V) * ((h : (Module.End K V)ˣ) : Module.End K V) = 1 :=
          Units.inv_mul (h : (Module.End K V)ˣ)
        simp only [← mul_assoc, h1, one_mul]
        rw [mul_assoc, h1, mul_one]
      right_inv := fun e => by
        apply Subtype.ext
        change ((h : (Module.End K V)ˣ) : Module.End K V) * ((((h : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V) * e *
          ((h : (Module.End K V)ˣ) : Module.End K V)) * (((h : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V) = e
        have h1 : ((h : (Module.End K V)ˣ) : Module.End K V) * (((h : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V) = 1 :=
          Units.mul_inv (h : (Module.End K V)ˣ)
        simp only [← mul_assoc, h1, one_mul]
        rw [mul_assoc, h1, mul_one] }
  map_one' := by
    ext e
    simp
  map_mul' a b := by
    ext e
    simp [mul_assoc]

theorem palfyPermHom_ker (hR : PalfyAlg H R) {h : H} (hk : h ∈ (palfyPermHom hR).ker)
    {e : Module.End K V} (he : e ∈ palfyMinIdem R) : (h : (Module.End K V)ˣ) ∈ palfyStab H e := by
  refine ⟨h.2, (palfy_conj_eq_iff (h : (Module.End K V)ˣ) e).mp ?_⟩
  have := congrArg Subtype.val
    (Equiv.ext_iff.mp ((palfyPermHom hR).mem_ker.mp hk) ⟨e, (Set.Finite.mem_toFinset _).mpr he⟩)
  exact this

/-- The sizes of the pieces `e V` multiply to at most `|V|`. -/
theorem palfy_prod_card_le (hR : PalfyAlg H R) :
    ∏ e : {e // e ∈ (palfy_minIdem_finite R).toFinset}, Nat.card (LinearMap.range e.1) ≤
      Nat.card V := by
  classical
  rw [← Nat.card_pi]
  apply Nat.card_le_card_of_injective
    (fun f : (∀ e : {e // e ∈ (palfy_minIdem_finite R).toFinset}, LinearMap.range e.1) =>
      ∑ e, (f e : V))
  intro f g hfg
  funext e'
  have key : ∀ f : (∀ e : {e // e ∈ (palfy_minIdem_finite R).toFinset}, LinearMap.range e.1),
      e'.1 (∑ e, (f e : V)) = f e' := by
    intro f
    rw [map_sum, Finset.sum_eq_single e']
    · obtain ⟨v, hv⟩ := (f e').2
      rw [← hv, ← Module.End.mul_apply,
        ((Set.Finite.mem_toFinset _).mp e'.2).2.1.eq]
    · intro b _ hb
      obtain ⟨v, hv⟩ := (f b).2
      rw [← hv, ← Module.End.mul_apply, palfy_minIdem_mul hR ((Set.Finite.mem_toFinset _).mp e'.2)
        ((Set.Finite.mem_toFinset _).mp b.2) (fun h => hb (Subtype.ext h).symm)]
      rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  apply Subtype.ext
  rw [← key f, ← key g]
  exact congrArg e'.1 hfg

end

/-- **The imprimitive step.** -/
theorem palfy_imprimitive [Finite K] [Finite V] [Nontrivial V] {E : ℕ} (ih : PalfyIH K E (Nat.card V))
    {H : Subgroup (Module.End K V)ˣ} [IsSolvable H] (hH : palfyIrr H)
    {R : Subalgebra K (Module.End K V)} (hR : PalfyAlg H R) {f : Module.End K V} (hfR : f ∈ R)
    (hf : IsIdempotentElem f) (hf0 : f ≠ 0) (hf1 : f ≠ 1) :
    24 * Nat.card K ^ 6 * Nat.card H ^ 3 ≤ Nat.card V ^ E := by
  classical
  set P := (palfy_minIdem_finite R).toFinset
  set T := {e // e ∈ P}
  have hP : ∀ e : T, e.1 ∈ palfyMinIdem R := fun e => (Set.Finite.mem_toFinset _).mp e.2
  have ht : 2 ≤ Fintype.card T := by
    rw [Fintype.card_coe]; exact palfy_minIdem_two_le hR hfR hf hf0 hf1
  -- the pieces
  let G : (e : T) → Subgroup (Module.End K (LinearMap.range e.1))ˣ := fun e =>
    palfyResGrp (palfyStab H e.1) _ (palfyStab_inv H e.1)
  have hGsolv : ∀ e : T, IsSolvable (G e) := by
    intro e
    haveI : IsSolvable (palfyStab H e.1) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective (palfyStab_le H e.1))
    exact palfyResGrp_solvable _ _ _
  have hWne : ∀ e : T, Nontrivial (LinearMap.range e.1) := by
    intro e
    rw [Submodule.nontrivial_iff_ne_bot]
    intro h0
    apply (hP e).2.2.1
    ext v
    have : e.1 v ∈ LinearMap.range e.1 := ⟨v, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    exact this
  have hWlt : ∀ e : T, Nat.card (LinearMap.range e.1) < Nat.card V := by
    intro e
    obtain ⟨e', he'⟩ : ∃ e' : T, e' ≠ e := by
      by_contra hall
      push Not at hall
      have : Fintype.card T ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => (hall a).trans (hall b).symm)
      omega
    haveI := hWne e'
    obtain ⟨⟨w, hw⟩, hw0⟩ := exists_ne (0 : LinearMap.range e'.1)
    have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
    have hwe : w ∉ LinearMap.range e.1 := by
      rintro ⟨v, rfl⟩
      obtain ⟨u, hu⟩ := hw
      apply hw0'
      have h1 : e.1 (e.1 v) = e.1 v := by rw [← Module.End.mul_apply, (hP e).2.1.eq]
      rw [← h1, ← hu, ← Module.End.mul_apply,
        palfy_minIdem_mul hR (hP e) (hP e') (fun h => he' (Subtype.ext h).symm)]
      rfl
    have := Nat.card_le_card_of_injective _ (Subtype.val_injective (p := (· ∈ LinearMap.range e.1)))
    rcases this.lt_or_eq with h | h
    · exact h
    · exfalso
      have hsurj := (Function.Injective.bijective_of_nat_card_le
        (Subtype.val_injective (p := (· ∈ LinearMap.range e.1))) h.ge).2
      obtain ⟨x, hx⟩ := hsurj w
      exact hwe (hx ▸ x.2)
  have hGbound : ∀ e : T, 24 * Nat.card K ^ 6 * Nat.card (G e) ^ 3 ≤
      Nat.card (LinearMap.range e.1) ^ E := by
    intro e
    haveI := hWne e
    exact ih _ (hWlt e) (G e) (hGsolv e) (palfyCR_of_irr (palfy_stab_irr hH hR (hP e)))
  -- the permutation part
  set φ := palfyPermHom hR
  haveI : IsSolvable φ.range := solvable_of_surjective φ.rangeRestrict_surjective
  have hS : Nat.card φ.range ^ 3 ≤ 24 ^ (Fintype.card T - 1) := by
    have := solvOrder_bound (α := T) (by rw [Nat.card_eq_fintype_card]; omega) φ.range
      inferInstance
    rwa [Nat.card_eq_fintype_card (α := T)] at this
  -- the kernel
  have hL : Nat.card φ.ker ≤ ∏ e : T, Nat.card (G e) := by
    rw [← Nat.card_pi]
    apply Nat.card_le_card_of_injective (fun k : φ.ker => fun e : T =>
      (⟨palfyRes (palfyStab H e.1) _ (palfyStab_inv H e.1)
        ⟨(k : H), palfyPermHom_ker hR k.2 (hP e)⟩, ⟨_, rfl⟩⟩ : G e))
    intro a b hab
    apply Subtype.ext; apply Subtype.ext; apply Units.ext; apply LinearMap.ext
    intro v
    have hv : v = ∑ e : T, e.1 v := by
      have := palfy_minIdem_sum hR
      have h1 : v = (1 : Module.End K V) v := rfl
      conv_lhs => rw [h1, ← this]
      rw [LinearMap.sum_apply]
      exact (Finset.sum_coe_sort P (fun e : Module.End K V => e v)).symm
    rw [hv, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro e _
    have h1 := congrArg (fun F => ((((F e : (Module.End K (LinearMap.range e.1))ˣ) :
      Module.End K (LinearMap.range e.1)) ⟨e.1 v, v, rfl⟩ : LinearMap.range e.1) : V)) hab
    simpa only [palfyRes_apply] using h1
  -- numerics
  have hcard : Nat.card H = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hprodW := palfy_prod_card_le hR
  set t := Fintype.card T
  set c := 24 * Nat.card K ^ 6
  have hc24 : 24 ≤ c := Nat.le_mul_of_pos_right 24 (pow_pos Nat.card_pos 6)
  calc 24 * Nat.card K ^ 6 * Nat.card H ^ 3
      = c * Nat.card φ.range ^ 3 * Nat.card φ.ker ^ 3 := by rw [hcard]; ring
    _ ≤ c * 24 ^ (t - 1) * (∏ e : T, Nat.card (G e)) ^ 3 := by gcongr
    _ ≤ c * c ^ (t - 1) * (∏ e : T, Nat.card (G e)) ^ 3 := by gcongr
    _ = ∏ e : T, (c * Nat.card (G e) ^ 3) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Finset.prod_pow,
        ← pow_succ']
      congr 2
      omega
    _ ≤ ∏ e : T, Nat.card (LinearMap.range e.1) ^ E := Finset.prod_le_prod' (fun e _ => hGbound e)
    _ = (∏ e : T, Nat.card (LinearMap.range e.1)) ^ E := Finset.prod_pow _ _ _
    _ ≤ Nat.card V ^ E := Nat.pow_le_pow_left hprodW E

end GI.Proved
