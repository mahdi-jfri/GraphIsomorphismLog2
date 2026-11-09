module

public import Workspace.Degree.OrderBound
public import Workspace.Proved.PalfyField

/-!
# The imprimitive and field steps for groups in the class

These are `GI.Proved.palfy_imprimitive` and `GI.Proved.palfy_field_step`, with `Γ̂_D` in place of
solvable. The constant `24` becomes `D³`, because the permutation group on the `t` pieces has order
at most `D^(t-1)` by `GI.Degree.card_le_pow`, where the solvable case used Dixon's bound. The rest
of the proofs is the same.
-/

@[expose] public section

namespace GI.Degree

open GI.Proved

/-- The induction hypothesis over a fixed field: the bound holds below size `n`. -/
def DegIH (D : ℕ) (K : Type) [Field K] (E n : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module K W] [Finite W] [Nontrivial W], Nat.card W < n →
    ∀ G : Subgroup (Module.End K W)ˣ, GammaHat D G → palfyCR G →
      D ^ 3 * Nat.card K ^ 6 * Nat.card G ^ 3 ≤ Nat.card W ^ E

/-- The induction hypothesis over larger fields, for spaces of size exactly `n`. -/
def DegIH2 (D E n m : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [Finite L] (W : Type) [AddCommGroup W] [Module L W] [Finite W]
    [Nontrivial W], Nat.card W = n → m < Nat.card L →
    ∀ G : Subgroup (Module.End L W)ˣ, GammaHat D G → palfyCR G →
      D ^ 3 * Nat.card L ^ 6 * Nat.card G ^ 3 ≤ Nat.card W ^ E

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/-- **The imprimitive step.** -/
theorem deg_imprimitive [Finite K] [Finite V] [Nontrivial V] {D E : ℕ} (hD : 6 ≤ D)
    (ih : DegIH D K E (Nat.card V))
    {H : Subgroup (Module.End K V)ˣ} (hcl : GammaHat D H) (hH : palfyIrr H)
    {R : Subalgebra K (Module.End K V)} (hR : PalfyAlg H R) {f : Module.End K V} (hfR : f ∈ R)
    (hf : IsIdempotentElem f) (hf0 : f ≠ 0) (hf1 : f ≠ 1) :
    D ^ 3 * Nat.card K ^ 6 * Nat.card H ^ 3 ≤ Nat.card V ^ E := by
  classical
  set P := (palfy_minIdem_finite R).toFinset
  set T := {e // e ∈ P}
  have hP : ∀ e : T, e.1 ∈ palfyMinIdem R := fun e => (Set.Finite.mem_toFinset _).mp e.2
  have ht : 2 ≤ Fintype.card T := by
    rw [Fintype.card_coe]; exact palfy_minIdem_two_le hR hfR hf hf0 hf1
  -- the pieces
  let G : (e : T) → Subgroup (Module.End K (LinearMap.range e.1))ˣ := fun e =>
    palfyResGrp (palfyStab H e.1) _ (palfyStab_inv H e.1)
  have hGcl : ∀ e : T, GammaHat D (G e) := by
    intro e
    have h1 : GammaHat D (palfyStab H e.1) :=
      hcl.of_injective (Subgroup.inclusion (palfyStab_le H e.1))
        (Subgroup.inclusion_injective _)
    exact h1.of_surjective _ (palfyRes _ _ _).rangeRestrict_surjective
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
  have hGbound : ∀ e : T, D ^ 3 * Nat.card K ^ 6 * Nat.card (G e) ^ 3 ≤
      Nat.card (LinearMap.range e.1) ^ E := by
    intro e
    haveI := hWne e
    exact ih _ (hWlt e) (G e) (hGcl e) (palfyCR_of_irr (palfy_stab_irr hH hR (hP e)))
  -- the permutation part
  set φ := palfyPermHom hR
  have hS : Nat.card φ.range ^ 3 ≤ (D ^ 3) ^ (Fintype.card T - 1) := by
    have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
    have := card_le_pow hD φ.range (hcl.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
    rw [Nat.card_eq_fintype_card (α := T)] at this
    calc _ ≤ (D ^ (Fintype.card T - 1)) ^ 3 := Nat.pow_le_pow_left this 3
      _ = _ := by ring
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
  set c := D ^ 3 * Nat.card K ^ 6
  have hc24 : D ^ 3 ≤ c := Nat.le_mul_of_pos_right _ (pow_pos Nat.card_pos 6)
  calc D ^ 3 * Nat.card K ^ 6 * Nat.card H ^ 3
      = c * Nat.card φ.range ^ 3 * Nat.card φ.ker ^ 3 := by rw [hcard]; ring
    _ ≤ c * (D ^ 3) ^ (t - 1) * (∏ e : T, Nat.card (G e)) ^ 3 := by gcongr
    _ ≤ c * c ^ (t - 1) * (∏ e : T, Nat.card (G e)) ^ 3 := by gcongr
    _ = ∏ e : T, (c * Nat.card (G e) ^ 3) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Finset.prod_pow,
        ← pow_succ']
      congr 2
      omega
    _ ≤ ∏ e : T, Nat.card (LinearMap.range e.1) ^ E := Finset.prod_le_prod' (fun e _ => hGbound e)
    _ = (∏ e : T, Nat.card (LinearMap.range e.1)) ^ E := Finset.prod_pow _ _ _
    _ ≤ Nat.card V ^ E := Nat.pow_le_pow_left hprodW E

/-- **The field step.** -/
theorem deg_field_step [Finite K] [Finite V] [Nontrivial V] {D E : ℕ}
    (ih : DegIH2 D E (Nat.card V) (Nat.card K))
    {H A : Subgroup (Module.End K V)ˣ} (hcl : GammaHat D H) (hH : palfyIrr H)
    (hAH : palfyNormal A H) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hF : IsField (palfyAdj A)) (hne : palfyAdj A ≠ ⊥) :
    D ^ 3 * Nat.card K ^ 6 * Nat.card H ^ 3 ≤ Nat.card V ^ E := by
  classical
  have hKR := palfy_card_adj hne
  have hK2 : 1 < Nat.card K := Finite.one_lt_card
  letI := palfyFld A hF
  letI := palfyMod A hF
  set C := palfyCent H A
  have hcR : ∀ c ∈ C, ∀ r ∈ (palfyAdj A), (c : Module.End K V) * r = r * (c : Module.End K V) := by
    intro c hc
    apply palfyAdj_comm_of
    intro a ha
    exact congrArg Units.val (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 a ha).symm
  let ψ : C →* (Module.End (palfyAdj A) V)ˣ :=
    { toFun := fun c =>
        { val := palfyLin A hF ((c : (Module.End K V)ˣ) : Module.End K V) (hcR c c.2)
          inv := palfyLin A hF (((c⁻¹ : C) : (Module.End K V)ˣ) : Module.End K V) (hcR _ (C.inv_mem c.2))
          val_inv := LinearMap.ext fun v => by
            change ((c * c⁻¹ : (Module.End K V)ˣ) : Module.End K V) v = v
            simp
          inv_val := LinearMap.ext fun v => by
            change ((c⁻¹ * c : (Module.End K V)ˣ) : Module.End K V) v = v
            simp }
      map_one' := Units.ext (LinearMap.ext fun v => rfl)
      map_mul' := fun a b => Units.ext (LinearMap.ext fun v => rfl) }
  have hψ : ∀ c : C, ∀ v : V, (((ψ c : (Module.End (palfyAdj A) V)ˣ) : Module.End (palfyAdj A) V) v) =
      ((c : (Module.End K V)ˣ) : Module.End K V) v := fun _ _ => rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext; apply Units.ext; apply LinearMap.ext
    intro v
    rw [← hψ, ← hψ, hab]
  have hCcard : Nat.card C = Nat.card ψ.range :=
    Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv
  have hCcl : GammaHat D C := hcl.of_injective (Subgroup.inclusion (inf_le_left : C ≤ H))
    (Subgroup.inclusion_injective _)
  have hRcl : GammaHat D ψ.range := hCcl.of_surjective _ ψ.rangeRestrict_surjective
  have hAC : ∀ a ∈ A, a ∈ C := by
    intro a ha
    refine Subgroup.mem_inf.mpr ⟨hAH.1 ha, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro b hb
    exact hAc b hb a ha
  have hCR : palfyCR ψ.range := by
    intro W hW
    let WK : Submodule K V :=
      { carrier := W
        add_mem' := W.add_mem
        zero_mem' := W.zero_mem
        smul_mem' := fun k v hv => by
          have : (⟨algebraMap K (Module.End K V) k, (palfyAdj A).algebraMap_mem k⟩ : (palfyAdj A)) • v ∈ W :=
            W.smul_mem _ hv
          exact (Module.algebraMap_end_apply K K V k v) ▸ this }
    have hWK : palfyInv C WK := by
      intro c hc v hv
      exact hW _ ⟨⟨c, hc⟩, rfl⟩ v hv
    obtain ⟨X, hX, hc⟩ := palfy_clifford hH (palfyCent_normal hAH) WK hWK
    have hXA : palfyInv A X := fun a ha => hX a (hAC a ha)
    let XR : Submodule (palfyAdj A) V :=
      { carrier := X
        add_mem' := X.add_mem
        zero_mem' := X.zero_mem
        smul_mem' := fun r v hv => palfyAdj_inv hXA r r.2 v hv }
    refine ⟨XR, ?_, ?_, ?_⟩
    · rintro _ ⟨c, rfl⟩ v hv
      exact hX c c.2 v hv
    · rw [disjoint_iff, eq_bot_iff]
      intro v hv
      have : v ∈ WK ⊓ X := hv
      rw [hc.inf_eq_bot, Submodule.mem_bot] at this
      exact (Submodule.mem_bot (palfyAdj A)).mpr this
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have : v ∈ WK ⊔ X := by rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp this
      exact Submodule.add_mem_sup (S := W) (T := XR) hy hz
  have hKlt : Nat.card K < Nat.card (palfyAdj A) := by nlinarith
  have hbound := ih (palfyAdj A) V rfl hKlt ψ.range hRcl hCR
  -- `A` is cyclic
  let f : A →* (palfyAdj A) :=
    { toFun := fun a => ⟨((a : (Module.End K V)ˣ) : Module.End K V), palfyAdj_mem a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hfinj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Units.ext (congrArg Subtype.val hab))
  haveI : IsCyclic A := isCyclic_of_injective_ringHom f hfinj
  obtain ⟨a0, ha0⟩ := IsCyclic.exists_generator (α := A)
  have hfib := solv_card_le_mul_of_fibers H C inf_le_left
    (fun h : H => (⟨(h : (Module.End K V)ˣ) * a0 * (h : (Module.End K V)ˣ)⁻¹,
      hAH.2 h h.2 a0 a0.2⟩ : A)) (by
      intro x y hxy
      have hxy' := congrArg Subtype.val hxy
      simp only at hxy'
      refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem x.2) y.2,
        Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro a ha
      obtain ⟨n, hn⟩ := ha0 ⟨a, ha⟩
      have hcomm : Commute ((x : (Module.End K V)ˣ)⁻¹ * y) (a0 : (Module.End K V)ˣ) := by
        change _ * _ = _ * _
        calc (x : (Module.End K V)ˣ)⁻¹ * y * a0
            = (x : (Module.End K V)ˣ)⁻¹ * (y * a0 * (y : (Module.End K V)ˣ)⁻¹) * y := by group
          _ = (x : (Module.End K V)ˣ)⁻¹ * (x * a0 * (x : (Module.End K V)ˣ)⁻¹) * y := by
            rw [hxy']
          _ = a0 * ((x : (Module.End K V)ˣ)⁻¹ * y) := by group
      have := (hcomm.zpow_right n).eq
      have hn' : (a0 : (Module.End K V)ˣ) ^ n = a := by
        have := congrArg Subtype.val hn
        simpa using this
      rw [hn'] at this
      exact this.symm)
  have hAR : Nat.card A ≤ Nat.card (palfyAdj A) := Nat.card_le_card_of_injective f hfinj
  rw [hCcard] at hfib
  calc D ^ 3 * Nat.card K ^ 6 * Nat.card H ^ 3
      ≤ D ^ 3 * Nat.card K ^ 6 * (Nat.card A * Nat.card ψ.range) ^ 3 := by gcongr
    _ = D ^ 3 * (Nat.card K ^ 2) ^ 3 * Nat.card A ^ 3 * Nat.card ψ.range ^ 3 := by ring
    _ ≤ D ^ 3 * Nat.card (palfyAdj A) ^ 3 * Nat.card (palfyAdj A) ^ 3 * Nat.card ψ.range ^ 3 := by
      gcongr
    _ = D ^ 3 * Nat.card (palfyAdj A) ^ 6 * Nat.card ψ.range ^ 3 := by ring
    _ ≤ Nat.card V ^ E := hbound

end GI.Degree
