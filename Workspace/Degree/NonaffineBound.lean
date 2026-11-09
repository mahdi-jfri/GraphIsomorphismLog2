module

public import Workspace.Degree.AlmostSimpleBound
public import Workspace.Degree.OrderBound
public import Maroti.Reduction.Step1
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Primitive groups with a nonabelian minimal normal subgroup

Let `G ∈ Γ̂_D` be primitive of degree `n`, and let `N ≅ T^r` be a nonabelian minimal normal subgroup.
Write `K ≤ Sym(r)` for the group that `G` induces on the `r` factors. By GNS Lemma 2.2, `|K| ≤ D^(r-1)`.
We follow Step 1 of Maróti's proof with this bound in place of `r!`. There are two cases.

* `|T|^r ≤ n²`. This covers the regular, diagonal and twisted wreath types. Here
  `|G| ≤ n |K| |Aut T|^r`, for any transitive normal `N` (`card_le_mul_card_mulAut`).
* `G` embeds in `H wr K` in the product action on `Δ^r`, with `H` primitive and almost simple.
  This includes the case `r = 1`. Then `almostSimple_alternatives` applies to `H`.
-/

@[expose] public section

namespace GI.Degree

open Equiv MulAction CFSG.Holt.General.AltRecPrim Maroti Maroti.SimpleFactors

variable {α : Type} {G : Subgroup (Perm α)} {N : Subgroup G} (F : SimpleFactors N)

theorem card_S_pow [Finite α] {i₀ : Fin F.r} :
    Nat.card (∀ i : Fin F.r, MulAut (F.S i)) = Nat.card (MulAut (F.S i₀)) ^ F.r := by
  simp only [Nat.card_pi]
  have hcongr : ∀ i : Fin F.r, Nat.card (MulAut (F.S i)) = Nat.card (MulAut (F.S i₀)) := by
    intro i
    obtain ⟨e⟩ := nonempty_mulEquiv_S F i i₀
    exact Nat.card_congr (MulAut.congr e).toEquiv
  simp [hcongr]

/-- An element of the kernel on the factors that induces the identity on each factor centralizes
`N`. -/
theorem mem_centralizer_of_kerToPiAut (hN : N.Normal) {g : (coordPermHom F hN).ker}
    (hg : kerToPiAut F hN g = 1) : (g : G) ∈ Subgroup.centralizer (N : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hgn : (g : G) * n * (g : G)⁻¹ ∈ N := hN.conj_mem n hn g
  have hproj : ∀ i : Fin F.r, F.proj i ⟨(g : G) * n * (g : G)⁻¹, hgn⟩ = F.proj i ⟨n, hn⟩ := by
    intro i
    apply Subtype.ext
    have hmap : (F.S i).map (MulAut.conj (g : G)).toMonoidHom = F.S i := by
      have h1 : coordPermHom F hN g i = i := by
        rw [MonoidHom.mem_ker.mp g.2, Perm.one_apply]
      rw [map_conj_eq_coordPermHom F hN, h1]
    rw [F.proj_conj hmap ⟨n, hn⟩ hgn]
    have hgi := congrArg (fun φ : ∀ j, MulAut (F.S j) => (φ i (F.proj i ⟨n, hn⟩) : G)) hg
    exact hgi
  have heq : (⟨(g : G) * n * (g : G)⁻¹, hgn⟩ : N) = ⟨n, hn⟩ := by
    rw [← mul_inv_eq_one]
    apply F.eq_one_of_forall_proj_eq_one
    intro i
    rw [map_mul, map_inv, hproj i, mul_inv_cancel]
  have hval : (g : G) * n * (g : G)⁻¹ = n := congrArg Subtype.val heq
  calc n * (g : G) = ((g : G) * n * (g : G)⁻¹) * g := by rw [hval]
    _ = (g : G) * n := by group

/-- For transitive `N`, `|G| ≤ n |K| |Aut T|^r`. A point stabilizer has image in `K`, and its
kernel acts faithfully on `N` by conjugation, since `N` is transitive. -/
theorem card_le_mul_card_mulAut [Finite α] [IsPreprimitive G α] (hN : N.Normal) (hNne : N ≠ ⊥)
    (ω : α) (i₀ : Fin F.r) :
    Nat.card G ≤ Nat.card α * (Nat.card (coordPermHom F hN).range *
      Nat.card (MulAut (F.S i₀)) ^ F.r) := by
  have htr : IsPretransitive (N.map G.subtype) α := by
    have := hN
    exact isPretransitive_of_normal_subgroup hNne
  let St := stabilizer G ω
  let φ : St →* Perm (Fin F.r) := (coordPermHom F hN).comp St.subtype
  have hSt : Nat.card St = Nat.card φ.range * Nat.card φ.ker := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker, mul_comm]
  have hle : φ.range ≤ (coordPermHom F hN).range := by
    rintro _ ⟨g, rfl⟩
    exact ⟨g.1, rfl⟩
  have h1 : Nat.card φ.range ≤ Nat.card (coordPermHom F hN).range :=
    Subgroup.card_le_of_le hle
  let ι : φ.ker → (coordPermHom F hN).ker := fun g => ⟨g.1.1, g.2⟩
  have hinj : Function.Injective fun g : φ.ker => kerToPiAut F hN (ι g) := by
    intro g g' hgg
    have hk : kerToPiAut F hN (ι g * (ι g')⁻¹) = 1 := by
      rw [map_mul, map_inv]
      simp only at hgg
      rw [hgg, mul_inv_cancel]
    have hcen := mem_centralizer_of_kerToPiAut F hN hk
    have hfix : ((ι g * (ι g')⁻¹ : (coordPermHom F hN).ker) : G) ∈ St := by
      change (g.1.1 * (g'.1.1)⁻¹ : G) ∈ St
      exact mul_mem g.1.2 (inv_mem g'.1.2)
    have h1g : ((ι g * (ι g')⁻¹ : (coordPermHom F hN).ker) : G) = 1 := by
      apply Subtype.ext
      apply eq_one_of_commute_transitive (N := N.map G.subtype) (ω := ω)
        (mem_stabilizer_iff.mp hfix)
      rintro _ ⟨m, hm, rfl⟩
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hcen m hm).symm)
    have h2g : (g.1.1 : G) = g'.1.1 := by
      have : (g.1.1 * (g'.1.1)⁻¹ : G) = 1 := h1g
      exact mul_inv_eq_one.1 this
    exact Subtype.ext (Subtype.ext h2g)
  have h2 : Nat.card φ.ker ≤ Nat.card (MulAut (F.S i₀)) ^ F.r :=
    (Nat.card_le_card_of_injective _ hinj).trans (card_S_pow F).le
  have hmul : Nat.card St * Nat.card α = Nat.card G := by
    rw [← index_stabilizer_of_transitive G ω, Subgroup.card_mul_index]
  calc Nat.card G = Nat.card α * Nat.card St := by rw [← hmul, mul_comm]
    _ ≤ _ := by
      rw [hSt]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)

/-- In the product case, `|G| ≤ |K| |H|^r`. This is Maróti's bound with `|K|` for `r!`. -/
theorem card_le_range_mul_card_H_pow [Finite α] [IsPreprimitive G α] [Nontrivial α]
    (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) (i₀ : Fin F.r) :
    Nat.card G ≤ Nat.card (coordPermHom F hN).range * Nat.card (H F hN ω hR i₀) ^ F.r := by
  let K := (coordPermHom F hN).ker
  have hker : Nat.card K ≤ Nat.card (H F hN ω hR i₀) ^ F.r := by
    have hinj := Nat.card_le_card_of_injective (kerToPiH F hN ω hR) (kerToPiH_injective F hN ω hR)
    have hpi : Nat.card (∀ i : Fin F.r, H F hN ω hR i) = Nat.card (H F hN ω hR i₀) ^ F.r := by
      simp only [Nat.card_pi]
      have hcongr : ∀ i : Fin F.r, Nat.card (H F hN ω hR i) = Nat.card (H F hN ω hR i₀) :=
        fun i => card_H_eq F hN ω hR i i₀
      simp [hcongr]
    exact hinj.trans hpi.le
  calc Nat.card G = K.index * Nat.card K := by rw [mul_comm, K.card_mul_index]
    _ ≤ _ := by
      rw [Subgroup.index_ker]
      exact Nat.mul_le_mul_left _ hker

/-- The constant of `nonaffine_alternatives`. -/
noncomputable def nonC₁ : ℝ := 2 + asC₁

theorem nonC₁_nonneg : 0 ≤ nonC₁ := by
  have := asC₁_nonneg
  unfold nonC₁
  linarith

theorem one_le_log_of_four_le {t : ℕ} (ht : 4 ≤ t) : 1 ≤ Real.log t := by
  have h1 : Real.log (4 : ℕ) ≤ Real.log t :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  have h2 : Real.log (4 : ℕ) = 2 * Real.log 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

section Main

variable [Finite α] [IsPreprimitive G α] [Nontrivial α]

theorem card_range_le {D : ℕ} (hD : 6 ≤ D) (hG : GammaHat D G) (hN : N.Normal) :
    Nat.card (coordPermHom F hN).range ≤ D ^ (F.r - 1) := by
  have hne : Nonempty (Fin F.r) := ⟨⟨0, F.one_le⟩⟩
  have := card_le_pow hD (coordPermHom F hN).range (hG.of_surjective
    (coordPermHom F hN).rangeRestrict (coordPermHom F hN).rangeRestrict_surjective)
  simpa [Nat.card_eq_fintype_card] using this

/-- The case `|T|^r ≤ n²`. -/
theorem log_card_of_small_socle {D : ℕ} (hD : 6 ≤ D) (hG : GammaHat D G) (hN : N.Normal)
    (hNne : N ≠ ⊥) (i₀ : Fin F.r) (hsm : Nat.card (F.S i₀) ^ F.r ≤ Nat.card α ^ 2) :
    Real.log (Nat.card G) ≤ (2 * Real.log D + 5) * Real.log (Nat.card α) := by
  obtain ⟨ω⟩ : Nonempty α := inferInstance
  have hNS := isNonabelianSimple_S F i₀
  have : IsSimpleGroup (F.S i₀) := hNS.1
  have hc := card_le_mul_card_mulAut F hN hNne ω i₀
  have hk := card_range_le F hD hG hN
  have hA := autBound hNS.2
  set t := Nat.card (F.S i₀) with ht
  have ht32 : 32 ≤ t := thirty_two_le_card_of_isNonabelianSimple _ hNS
  have hlogt : 1 ≤ Real.log t := one_le_log_of_four_le (by omega)
  set n := Nat.card α with hn
  have hn2 : 2 ≤ n := Finite.one_lt_card
  set x := Real.log n with hx
  have hx0 : 0 ≤ x := Real.log_natCast_nonneg n
  set L := Real.log D with hL
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg D
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hr1 : 1 ≤ F.r := F.one_le
  have hrt : (F.r : ℝ) * Real.log t ≤ 2 * x := by
    have h3 : ((t : ℝ) ^ F.r) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hsm
    have h4 := Real.log_le_log (by positivity) h3
    rwa [Real.log_pow, Real.log_pow] at h4
  have hr : (F.r : ℝ) ≤ 2 * x := by
    have hr0 : (0 : ℝ) ≤ F.r := by positivity
    nlinarith
  have hbound : Nat.card G ≤ n * (D ^ (F.r - 1) * (t ^ 2) ^ F.r) :=
    hc.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul hk (Nat.pow_le_pow_left hA _)))
  have hlog : Real.log (Nat.card G) ≤
      x + (F.r - 1 : ℕ) * L + F.r * (2 * Real.log t) := by
    have h3 : (Nat.card G : ℝ) ≤ n * ((D : ℝ) ^ (F.r - 1) * ((t : ℝ) ^ 2) ^ F.r) := by
      exact_mod_cast hbound
    have h4 := Real.log_le_log (by exact_mod_cast Nat.card_pos) h3
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have ht0 : (t : ℝ) ≠ 0 := by positivity
    rw [Real.log_mul hn0 (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow] at h4
    push_cast at h4 ⊢
    linarith
  have hr' : ((F.r - 1 : ℕ) : ℝ) ≤ 2 * x := by
    have : ((F.r - 1 : ℕ) : ℝ) ≤ F.r := by exact_mod_cast Nat.sub_le _ _
    linarith
  have h5 : ((F.r - 1 : ℕ) : ℝ) * L ≤ 2 * x * L := mul_le_mul_of_nonneg_right hr' hL0
  nlinarith

/-- The product case. Here `G ≤ H wr K` on `Δ^r`, and `H` obeys a bound of the form `B log |Δ|`. -/
theorem log_card_of_product {D : ℕ} (hD : 6 ≤ D) (hG : GammaHat D G) (hN : N.Normal) (ω : α)
    (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) (i₀ : Fin F.r) {B : ℝ}
    (hB : Real.log (Nat.card (H F hN ω hR i₀)) ≤ B * Real.log (Nat.card (Δ F ω i₀))) :
    Real.log (Nat.card G) ≤ (Real.log D + B) * Real.log (Nat.card α) := by
  have hc := card_le_range_mul_card_H_pow F hN ω hR i₀
  have hk := card_range_le F hD hG hN
  have hn : Nat.card α = Nat.card (Δ F ω i₀) ^ F.r := by
    rw [card_α_eq_pow_card_Δ F hN ω hR, card_Δ_eq F hN ω hR ⟨0, F.one_le⟩ i₀]
  have hδ : 5 ≤ Nat.card (Δ F ω i₀) := five_le_card_Δ F ω hR i₀
  set δ := Nat.card (Δ F ω i₀) with hδ'
  have hlogδ : 1 ≤ Real.log δ := one_le_log_of_four_le (by omega)
  have hx : Real.log (Nat.card α) = F.r * Real.log δ := by
    rw [hn]
    push_cast
    rw [Real.log_pow]
  have hL0 : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hbound : Nat.card G ≤ D ^ (F.r - 1) * Nat.card (H F hN ω hR i₀) ^ F.r :=
    hc.trans (Nat.mul_le_mul_right _ hk)
  have hH0 : (0 : ℝ) < Nat.card (H F hN ω hR i₀) := by
    have : Finite (Δ F ω i₀) := inferInstance
    exact_mod_cast Nat.card_pos
  have hlog : Real.log (Nat.card G) ≤
      (F.r - 1 : ℕ) * Real.log D + F.r * Real.log (Nat.card (H F hN ω hR i₀)) := by
    have h3 : (Nat.card G : ℝ) ≤
        (D : ℝ) ^ (F.r - 1) * (Nat.card (H F hN ω hR i₀) : ℝ) ^ F.r := by
      exact_mod_cast hbound
    have h4 := Real.log_le_log (by exact_mod_cast Nat.card_pos) h3
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h4
  have hr0 : (0 : ℝ) ≤ F.r := by positivity
  have hr' : ((F.r - 1 : ℕ) : ℝ) ≤ F.r := by exact_mod_cast Nat.sub_le _ _
  have h5 : ((F.r - 1 : ℕ) : ℝ) * Real.log D ≤ F.r * Real.log δ * Real.log D := by
    refine mul_le_mul_of_nonneg_right (hr'.trans ?_) hL0
    nlinarith
  have h6 : (F.r : ℝ) * Real.log (Nat.card (H F hN ω hR i₀)) ≤ F.r * (B * Real.log δ) :=
    mul_le_mul_of_nonneg_left hB hr0
  rw [hx]
  nlinarith

/-- **The nonaffine case.** A primitive group in `Γ̂_D` with a nonabelian minimal normal subgroup
has `log |G| ≤ O(log D log n)`, or it is a Johnson product. -/
theorem nonaffine_alternatives (F : SimpleFactors N) {D : ℕ} (hD : 6 ≤ D) (hG : GammaHat D G)
    (hN : N.Normal) (hNne : N ≠ ⊥) :
    IsWreathType G ∨
      Real.log (Nat.card G) ≤ (nonC₁ * Real.log D + 17) * Real.log (Nat.card α) := by
  obtain ⟨ω⟩ : Nonempty α := inferInstance
  have hL0 : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hx0 : 0 ≤ Real.log (Nat.card α) := Real.log_natCast_nonneg _
  have hasC := asC₁_nonneg
  let i₀ : Fin F.r := ⟨0, F.one_le⟩
  have hemb : ∀ i, EmbedsInSym D (F.S i) := fun i => by
    have := F.isSimpleGroup i
    exact gammaHat_simple_iff.1 (hG.subgroup (F.S i))
  -- The bound for small socle implies the claimed bound.
  have hsmall : Nat.card (F.S i₀) ^ F.r ≤ Nat.card α ^ 2 →
      Real.log (Nat.card G) ≤ (nonC₁ * Real.log D + 17) * Real.log (Nat.card α) := fun hsm => by
    refine (log_card_of_small_socle F hD hG hN hNne i₀ hsm).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hx0
    unfold nonC₁
    nlinarith
  have hreg : stabilizer N ω = ⊥ → Nat.card (F.S i₀) ^ F.r ≤ Nat.card α ^ 2 := fun h => by
    have htr : IsPretransitive N α := isPretransitive_of_normal_ne_bot hNne
    have hmul := (stabilizer N ω).card_mul_index
    rw [index_stabilizer_of_transitive N ω, h, Subgroup.card_bot, one_mul, card_N_eq F] at hmul
    rw [hmul]
    exact Nat.le_self_pow (by norm_num) _
  by_cases hC : Subgroup.centralizer (N : Set G) = ⊥
  · by_cases hr : F.r = 1
    · have has := isAlmostSimpleWith_of_r_eq_one hN F hr hC
      rcases almostSimple_alternatives hD G has (hemb _) with h | h
      · exact Or.inl h.isWreathType
      · refine Or.inr (h.trans (mul_le_mul_of_nonneg_right ?_ hx0))
        unfold nonC₁
        nlinarith
    · have hr2 : 2 ≤ F.r := by
        have := F.one_le
        omega
      by_cases hK : stabilizer N ω = ⊥
      · exact Or.inr (hsmall (hreg hK))
      · have htr : IsPretransitive N α := isPretransitive_of_normal_ne_bot hNne
        rcases forall_map_proj_eq_top_or_ne_top F hN ω with htop | hne
        · refine Or.inr (hsmall ?_)
          have hidx := index_stabilizer_of_transitive N ω
          have hKne : stabilizer N ω ≠ ⊤ := by
            intro h
            rw [h, Subgroup.index_top] at hidx
            have : 2 ≤ Nat.card α := Finite.one_lt_card
            omega
          have hKcard := card_stabilizer_le_pow_half F hN ω htop hKne
          have hmul := (stabilizer N ω).card_mul_index
          rw [hidx, card_N_eq F] at hmul
          set t := Nat.card (F.S i₀)
          have ht : 0 < t := Nat.card_pos
          have hge : t ^ ((F.r + 1) / 2) ≤ Nat.card α := by
            have hsplit : t ^ F.r = t ^ (F.r / 2) * t ^ ((F.r + 1) / 2) := by
              rw [← pow_add]
              congr 1
              omega
            have h3 : t ^ (F.r / 2) * t ^ ((F.r + 1) / 2) ≤ t ^ (F.r / 2) * Nat.card α := by
              rw [← hsplit, ← hmul]
              exact Nat.mul_le_mul_right _ hKcard
            exact Nat.le_of_mul_le_mul_left h3 (by positivity)
          calc t ^ F.r ≤ t ^ (((F.r + 1) / 2) * 2) := Nat.pow_le_pow_right ht (by omega)
            _ = (t ^ ((F.r + 1) / 2)) ^ 2 := pow_mul _ _ _
            _ ≤ _ := Nat.pow_le_pow_left hge 2
        · have hprim : IsPreprimitive (H F hN ω hne i₀) (Δ F ω i₀) :=
            isPreprimitive_H F hN ω hne i₀
          have has : IsAlmostSimpleWith (H F hN ω hne i₀) (F.S i₀) :=
            isAlmostSimpleWith_H F hN ω hne hK i₀
          rcases almostSimple_alternatives hD (H F hN ω hne i₀) has (hemb i₀) with h | h
          · exact Or.inl (isWreathType_of_isSubsetActionType_H F hN ω hne h)
          · refine Or.inr ((log_card_of_product F hD hG hN ω hne i₀ h).trans ?_)
            refine mul_le_mul_of_nonneg_right ?_ hx0
            unfold nonC₁
            nlinarith
  · refine Or.inr (hsmall (hreg ?_))
    -- The centralizer of `N` is a nontrivial normal subgroup, so it is transitive.
    let C : Subgroup G := Subgroup.centralizer (N : Set G)
    have hCnorm : C.Normal := by
      refine ⟨fun c hc g => Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
      have hn' : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
      have hc' := Subgroup.mem_centralizer_iff.mp hc (g⁻¹ * n * g) hn'
      calc n * (g * c * g⁻¹) = g * ((g⁻¹ * n * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * n * g)) * g⁻¹ := by rw [hc']
        _ = (g * c * g⁻¹) * n := by group
    have : IsPretransitive (C.map G.subtype) α := isPretransitive_of_normal_subgroup hC
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply Subtype.ext
    apply eq_one_of_commute_transitive (N := C.map G.subtype) (ω := ω)
      (mem_stabilizer_iff.mp hn)
    rintro _ ⟨c, hc, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc n.1 n.2)

end Main

end GI.Degree
