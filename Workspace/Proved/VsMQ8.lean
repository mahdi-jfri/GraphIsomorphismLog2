module

public import Workspace.Proved.VsMHardB

@[expose] public section

/-!
# The `Q₈` case (**M7**, LM Proposition 5.11)

Here `r = 2` and the maximal good isotropic `E` is `0`. Then every good element of `Y` lies in
`S`, and `|Ȳ| ≤ 4` by M6. Two non-commuting `x, y ∈ Y` give four distinct classes
`1, x, y, xy` modulo `S`, so these are all of `Ȳ` (`vsM_cover`).

* `vsM_q8Cent`. An element `c` of `C ≤ C(A)` is fixed by the pair `(c x c⁻¹, c y c⁻¹)` up to
  `C(Y)`. Both entries lie in `Y`, have the squares `x²`, `y²`, and do not commute. In each
  class there are at most two elements with a given square (they differ by `ζ = -1`), and the
  two classes differ and are not `S`. This gives at most `3 · 2 · 2 · 2 = 24` pairs.
* `vsM_q8Two`. For `y ∈ Y`, `y' ∈ Y'` outside `S`, neither `y` nor `y'` is good, so `y² y'²`
  is a square `μ²` in `S` (the quadratic character is multiplicative). Then `t = y y' μ⁻¹` has
  `t² = 1`, and `z ∈ Y` with `⁅z, y⁆ = ζ` shifts it. `VsMSplitHyp.pieces` with `k = 1` gives two
  pieces. Elements of `H` fixing the classes of `y` and `y'` move `t` only by a scalar. They
  have index at most `|Ȳ| · |Ȳ'| ≤ 16`, so the stabilizer has index at most `4 · 16 ≤ 72`.
-/

namespace GI.Proved

open Module
open scoped commutatorElement

/-- **Pigeonhole for cosets.** If `|P : P ∩ W| ≤ n` and `g_0, …, g_{n-1} ∈ P` lie in distinct
cosets of `W`, then every `y ∈ P` lies in one of these cosets. -/
theorem vsM_cover {G : Type*} [Group G] (W P : Subgroup G) (g : ℕ → G) (n : ℕ)
    (h0 : W.relIndex P ≠ 0) (hn : W.relIndex P ≤ n) (hg : ∀ i < n, g i ∈ P)
    (hd : ∀ i j, i < j → j < n → (g i)⁻¹ * g j ∉ W) {y : G} (hy : y ∈ P) :
    ∃ i < n, (g i)⁻¹ * y ∈ W := by
  classical
  by_contra hne
  push Not at hne
  haveI : Finite (P ⧸ W.subgroupOf P) := Nat.finite_of_card_ne_zero h0
  let f : Fin (n + 1) → P ⧸ W.subgroupOf P := fun i =>
    if hi : (i : ℕ) < n then ((⟨g i, hg i hi⟩ : P) : P ⧸ W.subgroupOf P)
    else ((⟨y, hy⟩ : P) : P ⧸ W.subgroupOf P)
  have key : ∀ i j : Fin (n + 1), (i : ℕ) < j → f i ≠ f j := by
    intro i j hij hf
    have hj1 := j.isLt
    have hi : (i : ℕ) < n := by omega
    simp only [f, dif_pos hi] at hf
    by_cases hj : (j : ℕ) < n
    · rw [dif_pos hj, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hf
      exact hd i j hij hj (by simpa using hf)
    · rw [dif_neg hj, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hf
      exact hne i hi (by simpa using hf)
  have hinj : Function.Injective f := by
    intro i j hf
    rcases lt_trichotomy (i : ℕ) j with hlt | heq | hgt
    · exact absurd hf (key i j hlt)
    · exact Fin.ext heq
    · exact absurd hf.symm (key j i hgt)
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  unfold Subgroup.relIndex Subgroup.index at hn
  omega

variable {p : ℕ} [hp : Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

local notation "𝔼" => End (ZMod p) V

/-- The units that normalize `S` and fix each element of `T` modulo `S`. -/
def vsMFix (S : Subgroup (End (ZMod p) V)ˣ) (T : Set (End (ZMod p) V)ˣ) :
    Subgroup (End (ZMod p) V)ˣ where
  carrier := {g | (∀ s ∈ S, g * s * g⁻¹ ∈ S ∧ g⁻¹ * s * g ∈ S) ∧
    ∀ z ∈ T, z⁻¹ * (g * z * g⁻¹) ∈ S ∧ z⁻¹ * (g⁻¹ * z * g) ∈ S}
  mul_mem' := by
    rintro g g' ⟨hgS, hgY⟩ ⟨hg'S, hg'Y⟩
    refine ⟨fun s hs => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩⟩
    · have : g * g' * s * (g * g')⁻¹ = g * (g' * s * g'⁻¹) * g⁻¹ := by group
      rw [this]; exact (hgS _ (hg'S s hs).1).1
    · have : (g * g')⁻¹ * s * (g * g') = g'⁻¹ * (g⁻¹ * s * g) * g' := by group
      rw [this]; exact (hg'S _ (hgS s hs).2).2
    · have : z⁻¹ * (g * g' * z * (g * g')⁻¹) =
          (z⁻¹ * (g * z * g⁻¹)) * (g * (z⁻¹ * (g' * z * g'⁻¹)) * g⁻¹) := by group
      rw [this]; exact S.mul_mem (hgY z hz).1 (hgS _ (hg'Y z hz).1).1
    · have : z⁻¹ * ((g * g')⁻¹ * z * (g * g')) =
          (z⁻¹ * (g'⁻¹ * z * g')) * (g'⁻¹ * (z⁻¹ * (g⁻¹ * z * g)) * g') := by group
      rw [this]; exact S.mul_mem (hg'Y z hz).2 (hg'S _ (hgY z hz).2).2
  one_mem' := ⟨fun s hs => by simpa using hs, fun z _ => by simp [S.one_mem]⟩
  inv_mem' := by
    rintro g ⟨hgS, hgY⟩
    refine ⟨fun s hs => ?_, fun z hz => ?_⟩
    · rw [inv_inv]; exact ⟨(hgS s hs).2, (hgS s hs).1⟩
    · rw [inv_inv]; exact ⟨(hgY z hz).2, (hgY z hz).1⟩

/-- If `g, g'` normalize `S` and move `z` to the same class modulo `S`, then `g⁻¹ g'` fixes
`z` modulo `S`. -/
theorem vsM_fix_of {H S : Subgroup 𝔼ˣ} (hS : VsMNorm H S) {g g' z : 𝔼ˣ} (hg : g ∈ H)
    (hg' : g' ∈ H) (hz : (g * z * g⁻¹)⁻¹ * (g' * z * g'⁻¹) ∈ S) :
    z⁻¹ * ((g⁻¹ * g') * z * (g⁻¹ * g')⁻¹) ∈ S ∧
      z⁻¹ * ((g⁻¹ * g')⁻¹ * z * (g⁻¹ * g')) ∈ S := by
  have hu : g⁻¹ * g' ∈ H := H.mul_mem (H.inv_mem hg) hg'
  have h1 : z⁻¹ * ((g⁻¹ * g') * z * (g⁻¹ * g')⁻¹) ∈ S := by
    have e1 : z⁻¹ * ((g⁻¹ * g') * z * (g⁻¹ * g')⁻¹) =
        g⁻¹ * ((g * z * g⁻¹)⁻¹ * (g' * z * g'⁻¹)) * g⁻¹⁻¹ := by group
    rw [e1]
    exact hS _ (H.inv_mem hg) _ hz
  refine ⟨h1, ?_⟩
  have e2 : z⁻¹ * ((g⁻¹ * g')⁻¹ * z * (g⁻¹ * g')) =
      (g⁻¹ * g')⁻¹ * (z⁻¹ * ((g⁻¹ * g') * z * (g⁻¹ * g')⁻¹))⁻¹ * (g⁻¹ * g')⁻¹⁻¹ := by group
  rw [e2]
  exact hS _ (H.inv_mem hu) _ (S.inv_mem h1)

section Q8

variable [FiniteDimensional (ZMod p) V] [Nontrivial V] {H A Y : Subgroup (End (ZMod p) V)ˣ}
  {e : Fin 0 → (End (ZMod p) V)ˣ}

omit [FiniteDimensional (ZMod p) V] [Nontrivial V] in
/-- With `E = 0`, every good element of `Y` lies in `S`. -/
theorem vsM_good_scal (he : VsMIso A Y 2 e) {y : 𝔼ˣ} (hy : y ∈ Y) (hg : vsMGood A 2 y) :
    y ∈ vsMScal A := by
  have := he.2.2.2.2 y hy hg (fun i => i.elim0)
  rwa [Set.range_eq_empty, Subgroup.closure_empty, bot_sup_eq] at this

/-- Two elements of `Y` in the same class modulo `S` with the same square differ by `1`
or by `ζ`. -/
theorem VsMHard.sq_eq (h : VsMHard H A Y 2) {ζ : 𝔼ˣ} (hζ : ζ ∈ vsMScal A) (hζ1 : ζ ≠ 1)
    (hζr : ζ ^ 2 = 1) {u u' : 𝔼ˣ} (hu : u ∈ Y) (huu : u⁻¹ * u' ∈ vsMScal A)
    (hsq : u' ^ 2 = u ^ 2) : u' = u ∨ u' = u * ζ := by
  have hu' : u' = u * (u⁻¹ * u') := by rw [mul_inv_cancel_left]
  have hs2 : (u⁻¹ * u') ^ 2 = 1 := by
    have e1 : u' ^ 2 = u ^ 2 * (u⁻¹ * u') ^ 2 := by
      conv_lhs => rw [hu']
      exact (h.commute hu huu).symm.mul_pow 2
    rw [hsq] at e1
    exact (mul_eq_left.1 e1.symm)
  obtain ⟨j, hj, hsj⟩ := vsM_dlog A 2 ζ _ h.hA h.dom h.prime hζ hζ1 hζr huu hs2
  interval_cases j
  · left; rw [hu', hsj, pow_zero, mul_one]
  · right; rw [hu', hsj, pow_one]

/-- An element of `S` of order dividing `2` that is not `1` is `ζ`. -/
theorem VsMHard.eq_zeta (h : VsMHard H A Y 2) {ζ : 𝔼ˣ} (hζ : ζ ∈ vsMScal A) (hζ1 : ζ ≠ 1)
    (hζr : ζ ^ 2 = 1) {c : 𝔼ˣ} (hc : c ∈ vsMScal A) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) :
    c = ζ := by
  obtain ⟨j, hj, hcj⟩ := vsM_dlog A 2 ζ c h.hA h.dom h.prime hζ hζ1 hζr hc hc2
  interval_cases j
  · exact absurd (hcj.trans (pow_zero ζ)) hc1
  · rw [hcj, pow_one]

/-- **M7, first part** (LM Proposition 5.11). -/
theorem vsM_q8Cent : VsMQ8CentStmt p V := by
  intro H A Y C e h he hCH hCA
  classical
  haveI : Finite 𝔼 := Module.finite_of_finite (ZMod p)
  obtain ⟨ζ, hζ, hζ1, hζr⟩ := h.exists_zeta
  obtain ⟨x, hx, y, hy, hxy⟩ := h.nab
  -- the four classes `1, x, y, xy`
  let g : ℕ → 𝔼ˣ := fun i => if i = 1 then x else if i = 2 then y else if i = 3 then x * y else 1
  have hgY : ∀ i < 4, g i ∈ Y := by
    intro i _
    simp only [g]
    split_ifs
    exacts [hx, hy, Y.mul_mem hx hy, Y.one_mem]
  have hnS : ∀ w : 𝔼ˣ, (w * x = x * w → w * y = y * w → x * y = y * x) → w ∉ vsMScal A :=
    fun w hw hwS => hxy (hw (h.scal_comm hx hwS).symm (h.scal_comm hy hwS).symm)
  have hd : ∀ i j, i < j → j < 4 → (g i)⁻¹ * g j ∉ vsMScal A := by
    intro i j hij hj
    interval_cases j <;> interval_cases i <;> simp only [g] <;> norm_num <;> apply hnS <;>
      intro h1 h2
    · exact h2
    · exact h1.symm
    · calc x * y = x * (x * (x⁻¹ * y)) := by group
        _ = x * (x⁻¹ * y * x) := by rw [h1]
        _ = y * x := by group
    · calc x * y = (x * y * y) * y⁻¹ := by group
        _ = (y * (x * y)) * y⁻¹ := by rw [h2]
        _ = y * x := by group
    · exact h1.symm
    · calc x * y = y * (y⁻¹ * (x * y) * y) * y⁻¹ := by group
        _ = y * (y * (y⁻¹ * (x * y))) * y⁻¹ := by rw [h2]
        _ = y * x := by group
  have hn : (vsMScal A).relIndex Y ≤ 4 := by simpa using h.index_le he
  have hcover : ∀ z ∈ Y, ∃ i < 4, (g i)⁻¹ * z ∈ vsMScal A := fun z hz =>
    vsM_cover (vsMScal A) Y g 4 Subgroup.index_ne_zero_of_finite hn hgY hd hz
  -- an element of `C` commuting with `x` and `y` centralizes `Y`
  have hcen : ∀ c ∈ C, c * x = x * c → c * y = y * c →
      c ∈ Subgroup.centralizer (Y : Set 𝔼ˣ) := by
    intro c hc hcx hcy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨i, -, hi⟩ := hcover z hz
    have hcg : Commute c (g i) := by
      simp only [g]
      split_ifs
      exacts [hcx, hcy, Commute.mul_right hcx hcy, Commute.one_right c]
    have hcs : Commute c ((g i)⁻¹ * z) := vsM_comm_scal (hCA hc) hi
    have hz' : z = g i * ((g i)⁻¹ * z) := by rw [mul_inv_cancel_left]
    rw [hz']
    exact ((hcg.mul_right hcs).eq).symm
  -- representatives of the elements of a class with a given square
  let ρ : ℕ → 𝔼ˣ → 𝔼ˣ := fun i a =>
    if hex : ∃ u ∈ Y, (g i)⁻¹ * u ∈ vsMScal A ∧ u ^ 2 = a then hex.choose else 1
  have hrep : ∀ u ∈ Y, u ∉ vsMScal A → ∃ i < 4, i ≠ 0 ∧ (g i)⁻¹ * u ∈ vsMScal A ∧
      ∃ ε < 2, u = ρ i (u ^ 2) * ζ ^ ε := by
    intro u hu huS
    obtain ⟨i, hi, hiu⟩ := hcover u hu
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply huS
      simpa [g] using hiu
    have hex : ∃ w ∈ Y, (g i)⁻¹ * w ∈ vsMScal A ∧ w ^ 2 = u ^ 2 := ⟨u, hu, hiu, rfl⟩
    obtain ⟨hwY, hwS, hw2⟩ := hex.choose_spec
    have hρ : ρ i (u ^ 2) = hex.choose := dif_pos hex
    have hww : (hex.choose)⁻¹ * u ∈ vsMScal A := by
      have := (vsMScal A).mul_mem ((vsMScal A).inv_mem hwS) hiu
      rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at this
    refine ⟨i, hi, hi0, hiu, ?_⟩
    rcases h.sq_eq hζ hζ1 hζr hwY hww hw2.symm with h1 | h1
    · exact ⟨0, by norm_num, by rw [hρ, pow_zero, mul_one]; exact h1⟩
    · exact ⟨1, by norm_num, by rw [hρ, pow_one]; exact h1⟩
  let I : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    ((Finset.range 4 ×ˢ Finset.range 4) ×ˢ (Finset.range 2 ×ˢ Finset.range 2)).filter
      (fun q => q.1.1 ≠ 0 ∧ q.1.2 ≠ 0 ∧ q.1.1 ≠ q.1.2)
  have hI : I.card = 24 := by decide
  let F : (ℕ × ℕ) × (ℕ × ℕ) → 𝔼ˣ × 𝔼ˣ := fun q =>
    (ρ q.1.1 (x ^ 2) * ζ ^ q.2.1, ρ q.1.2 (y ^ 2) * ζ ^ q.2.2)
  have hmap : ∀ c ∈ C, (c * x * c⁻¹, c * y * c⁻¹) ∈ F '' (I : Set _) := by
    intro c hc
    have hu : c * x * c⁻¹ ∈ Y := h.norm c (hCH hc) x hx
    have hv : c * y * c⁻¹ ∈ Y := h.norm c (hCH hc) y hy
    have hsq : ∀ w ∈ Y, (c * w * c⁻¹) ^ 2 = w ^ 2 := by
      intro w hw
      rw [conj_pow, vsM_comm_scal (hCA hc) (h.pow w hw), mul_inv_cancel_right]
    have huv : (c * x * c⁻¹) * (c * y * c⁻¹) ≠ (c * y * c⁻¹) * (c * x * c⁻¹) := by
      intro e1
      apply hxy
      calc x * y = c⁻¹ * ((c * x * c⁻¹) * (c * y * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * y * c⁻¹) * (c * x * c⁻¹)) * c := by rw [e1]
        _ = y * x := by group
    have huS : c * x * c⁻¹ ∉ vsMScal A := fun hS => huv (h.scal_comm hv hS).symm
    have hvS : c * y * c⁻¹ ∉ vsMScal A := fun hS => huv (h.scal_comm hu hS)
    obtain ⟨i, hi, hi0, hiu, ε, hε, hue⟩ := hrep _ hu huS
    obtain ⟨j, hj, hj0, hjv, δ, hδ, hve⟩ := hrep _ hv hvS
    have hij : i ≠ j := by
      rintro rfl
      apply huv
      have hs : (c * x * c⁻¹)⁻¹ * (c * y * c⁻¹) ∈ vsMScal A := by
        have := (vsMScal A).mul_mem ((vsMScal A).inv_mem hiu) hjv
        rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at this
      have hc : Commute (c * x * c⁻¹) ((c * x * c⁻¹) * ((c * x * c⁻¹)⁻¹ * (c * y * c⁻¹))) :=
        (Commute.refl _).mul_right (h.commute hu hs).symm
      rw [mul_inv_cancel_left] at hc
      exact hc.eq
    refine ⟨((i, j), (ε, δ)), ?_, ?_⟩
    · simp only [I, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨⟨hi, hj⟩, hε, hδ⟩, hi0, hj0, hij⟩
    · simp only [F]
      rw [← hsq x hx, ← hsq y hy, ← hue, ← hve]
  have hfib : ∀ c ∈ C, ∀ c' ∈ C, (c * x * c⁻¹, c * y * c⁻¹) = (c' * x * c'⁻¹, c' * y * c'⁻¹) →
      c⁻¹ * c' ∈ Subgroup.centralizer (Y : Set 𝔼ˣ) := by
    intro c hc c' hc' e1
    obtain ⟨e2, e3⟩ := Prod.mk.inj e1
    have hcomm : ∀ w : 𝔼ˣ, c * w * c⁻¹ = c' * w * c'⁻¹ → c⁻¹ * c' * w = w * (c⁻¹ * c') := by
      intro w ew
      calc c⁻¹ * c' * w = c⁻¹ * (c' * w * c'⁻¹) * c' := by group
        _ = c⁻¹ * (c * w * c⁻¹) * c' := by rw [ew]
        _ = w * (c⁻¹ * c') := by group
    exact hcen _ (C.mul_mem (C.inv_mem hc) hc') (hcomm x e2) (hcomm y e3)
  have hb := vsM_relIndex_le (Subgroup.centralizer (Y : Set 𝔼ˣ)) C
    (fun c => (c * x * c⁻¹, c * y * c⁻¹)) (F '' (I : Set _)) ((Finset.finite_toSet I).image F)
    hmap hfib
  calc _ ≤ (F '' (I : Set _)).ncard := hb
    _ ≤ (I : Set ((ℕ × ℕ) × (ℕ × ℕ))).ncard := Set.ncard_image_le (Finset.finite_toSet I)
    _ = 24 := by rw [Set.ncard_coe_finset, hI]

/-- An element of `Y` outside `S` has quadratic character `ζ` on its square: `y²` is not a
square in `S`. -/
theorem VsMHard.chi_sq (h : VsMHard H A Y 2) (he : VsMIso A Y 2 e) {ζ : 𝔼ˣ}
    (hζ : ζ ∈ vsMScal A) (hζ1 : ζ ≠ 1) (hζr : ζ ^ 2 = 1) {y : 𝔼ˣ} (hy : y ∈ Y)
    (hyS : y ∉ vsMScal A) : (y ^ 2) ^ (Nat.card (vsMScal A) / 2) = ζ := by
  have hdvd := h.card_dvd hζ hζ1 hζr
  refine h.eq_zeta hζ hζ1 hζr (pow_mem (h.pow y hy) _) (vsM_chi_r hdvd (h.pow y hy)) ?_
  intro h1
  exact hyS (vsM_good_scal he hy ((h.good_iff hdvd hy).2 h1))

/-- **M7, second part** (LM Proposition 5.11). -/
theorem vsM_q8Two : VsMQ8TwoStmt p V := by
  intro H A Y Y' e y y' h he h' he' hY'Y hy hyS hy' hy'S
  classical
  haveI : Finite 𝔼 := Module.finite_of_finite (ZMod p)
  obtain ⟨ζ, hζ, hζ1, hζr⟩ := h.exists_zeta
  have hdvd := h.card_dvd hζ hζ1 hζr
  have hyy' : y * y' = y' * y := Subgroup.mem_centralizer_iff.1 (hY'Y hy') y hy
  have hyA := h.cent hy
  have hy'A := h'.cent hy'
  -- `y² y'²` is a square `μ²` in `S`
  obtain ⟨μ, hμ, hμ2⟩ : ∃ μ ∈ vsMScal A, y ^ 2 * y' ^ 2 = μ ^ 2 := by
    have hm : y ^ 2 * y' ^ 2 ∈ vsMScal A := mul_mem (h.pow y hy) (h'.pow y' hy')
    obtain ⟨l, hl, hl2⟩ := ((vsM_good_test A h.hA h.dom).2 2 _ h.prime hdvd hm).2 (by
      rw [vsM_chi_mul h.hA (h.pow y hy) (h'.pow y' hy'), h.chi_sq he hζ hζ1 hζr hy hyS,
        h'.chi_sq he' hζ hζ1 hζr hy' hy'S, ← pow_two, hζr])
    exact ⟨l, hl, hl2⟩
  obtain ⟨t, ht⟩ : ∃ t : 𝔼ˣ, t = y * y' * μ⁻¹ := ⟨_, rfl⟩
  have hμA : μ⁻¹ ∈ Subgroup.centralizer (A : Set 𝔼ˣ) :=
    Subgroup.inv_mem _ (vsM_scal_le_centralizer h.hA hμ)
  have hsplit : VsMSplitHyp A 2 ζ (fun _ : Fin 1 => t) :=
    { hA := h.hA, hdom := h.dom, hr := h.prime, hζ := hζ, hζ1 := hζ1, hζr := hζr
      htA := fun _ => by
        rw [ht]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyA hy'A) hμA
      htt := fun _ _ => rfl
      htr := fun _ => by
        have c1 : Commute (y * y') μ⁻¹ :=
          vsM_comm_scal (Subgroup.mul_mem _ hyA hy'A) (inv_mem hμ)
        rw [ht, c1.mul_pow, (show Commute y y' from hyy').mul_pow, hμ2, inv_pow,
          mul_inv_cancel] }
  have hEq : vsMAlgE A ![y * y'] = vsMAlgE A (fun _ : Fin 1 => t) := by
    apply le_antisymm
    · refine Algebra.adjoin_le ?_
      rintro _ (hx | ⟨i, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inl hx)
      · show (((![y * y'] : Fin 1 → 𝔼ˣ) i : 𝔼ˣ) : 𝔼) ∈ vsMAlgE A (fun _ : Fin 1 => t)
        have : (((![y * y'] : Fin 1 → 𝔼ˣ) i : 𝔼ˣ) : 𝔼) = (t : 𝔼) * (μ : 𝔼) := by
          rw [← Units.val_mul, ht, inv_mul_cancel_right, Subsingleton.elim i 0,
            Matrix.cons_val_zero]
        rw [this]
        exact mul_mem (hsplit.t_mem 0) (hsplit.L_le hμ.1)
    · refine Algebra.adjoin_le ?_
      rintro _ (hx | ⟨i, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inl hx)
      · show ((t : 𝔼ˣ) : 𝔼) ∈ vsMAlgE A ![y * y']
        rw [ht, Units.val_mul]
        refine mul_mem (Algebra.subset_adjoin (Or.inr ⟨0, ?_⟩))
          (Algebra.adjoin_mono Set.subset_union_left hμ.2)
        simp
  -- the shift `z`
  obtain ⟨z, hz, hzy⟩ : ∃ z ∈ Y, ⁅z, y⁆ = ζ := by
    have hnc : ¬ ∀ w ∈ Y, y * w = w * y := fun hc => hyS (h.central hy hc)
    push Not at hnc
    obtain ⟨z, hz, hzy⟩ := hnc
    refine ⟨z, hz, h.eq_zeta hζ hζ1 hζr (h.comm z hz y hy) (h.comm_pow hz hy) ?_⟩
    intro h1
    exact hzy (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have hst : ∀ i j : Fin 1, (fun _ : Fin 1 => z) i * (fun _ : Fin 1 => t) j *
      ((fun _ : Fin 1 => z) i)⁻¹ = if j = i then ζ * (fun _ : Fin 1 => t) j
        else (fun _ : Fin 1 => t) j := by
    intro i j
    rw [if_pos (Subsingleton.elim j i)]
    have e1 : z * y' * z⁻¹ = y' := by
      rw [Subgroup.mem_centralizer_iff.1 (hY'Y hy') z hz, mul_inv_cancel_right]
    have e2 : z * μ⁻¹ * z⁻¹ = μ⁻¹ := by
      rw [h.scal_comm hz (inv_mem hμ), mul_inv_cancel_right]
    show z * t * z⁻¹ = ζ * t
    calc z * t * z⁻¹ = ⁅z, y⁆ * (y * (z * y' * z⁻¹) * (z * μ⁻¹ * z⁻¹)) := by
          rw [ht, commutatorElement_def]; group
      _ = ζ * t := by rw [hzy, e1, e2, ht, mul_assoc y]
  rw [hEq]
  obtain ⟨π, hπ⟩ := hsplit.idem
  refine ⟨hsplit.reduced hπ, @fun ι f hfB hf hspan => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hsplit.pieces (fun _ => z) (fun _ => h.cent hz) hst f hfB hf hspan
  rw [pow_one] at h1
  refine ⟨h1, h2, ?_⟩
  -- the elements of `H` fixing the classes of `y` and `y'`
  have hS := vsM_scal_norm h.abn
  have hK := h3 (H ⊓ vsMFix (vsMScal A) {y, y'}) (fun g hg => by
    refine ⟨fun _ => ?_, (hg.2.1 ζ hζ).1⟩
    have ha := (hg.2.2 y (Set.mem_insert y _)).1
    have hb := (hg.2.2 y' (Set.mem_insert_of_mem y rfl)).1
    have hc := (hg.2.1 _ (inv_mem hμ)).1
    have hw : y'⁻¹ * (g * y' * g⁻¹) * (g * μ⁻¹ * g⁻¹) * μ ∈ vsMScal A :=
      mul_mem (mul_mem hb hc) hμ
    have e1 : ⁅g, t⁆ = y * (y⁻¹ * (g * y * g⁻¹) * (y' * (y'⁻¹ * (g * y' * g⁻¹) *
        (g * μ⁻¹ * g⁻¹) * μ) * y'⁻¹)) * y⁻¹ := by
      rw [ht, commutatorElement_def]; group
    rw [e1, h'.scal_comm hy' hw, mul_inv_cancel_right, h.scal_comm hy (mul_mem ha hw),
      mul_inv_cancel_right]
    exact mul_mem ha hw)
  have hKH : (H ⊓ vsMFix (vsMScal A) {y, y'}).relIndex H ≤ 16 := by
    rw [Subgroup.inf_relIndex_left]
    let fy : 𝔼ˣ → Y ⧸ (vsMScal A).subgroupOf Y := fun g =>
      if hg : g * y * g⁻¹ ∈ Y then ((⟨_, hg⟩ : Y) : Y ⧸ (vsMScal A).subgroupOf Y)
      else ((1 : Y) : Y ⧸ (vsMScal A).subgroupOf Y)
    let fy' : 𝔼ˣ → Y' ⧸ (vsMScal A).subgroupOf Y' := fun g =>
      if hg : g * y' * g⁻¹ ∈ Y' then ((⟨_, hg⟩ : Y') : Y' ⧸ (vsMScal A).subgroupOf Y')
      else ((1 : Y') : Y' ⧸ (vsMScal A).subgroupOf Y')
    have hb := vsM_relIndex_le (vsMFix (vsMScal A) {y, y'}) H (fun g => (fy g, fy' g))
      Set.univ Set.finite_univ (fun _ _ => Set.mem_univ _) (by
        intro g hg g' hg' e0
        obtain ⟨e2, e3⟩ := Prod.mk.inj e0
        simp only [fy, dif_pos (h.norm g hg y hy), dif_pos (h.norm g' hg' y hy)] at e2
        simp only [fy', dif_pos (h'.norm g hg y' hy'), dif_pos (h'.norm g' hg' y' hy')] at e3
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at e2 e3
        refine ⟨fun s hs => ⟨?_, ?_⟩, fun w hw => ?_⟩
        · exact hS _ (H.mul_mem (H.inv_mem hg) hg') s hs
        · have := hS _ (H.inv_mem (H.mul_mem (H.inv_mem hg) hg')) s hs
          rwa [inv_inv] at this
        · rcases hw with rfl | hw
          · exact vsM_fix_of hS hg hg' (by simpa using e2)
          · rw [Set.mem_singleton_iff] at hw
            subst hw
            exact vsM_fix_of hS hg hg' (by simpa using e3))
    rw [Set.ncard_univ, Nat.card_prod] at hb
    have hy4 : (vsMScal A).relIndex Y ≤ 4 := by simpa using h.index_le he
    have hy'4 : (vsMScal A).relIndex Y' ≤ 4 := by simpa using h'.index_le he'
    calc _ ≤ _ := hb
      _ ≤ 4 * 4 := Nat.mul_le_mul hy4 hy'4
  have hne : (vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1) ⊓
      (H ⊓ vsMFix (vsMScal A) {y, y'})).relIndex H ≠ 0 := Subgroup.index_ne_zero_of_finite
  calc (vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1)).relIndex H
      ≤ (vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1) ⊓
          (H ⊓ vsMFix (vsMScal A) {y, y'})).relIndex H :=
        Subgroup.relIndex_le_of_le_left inf_le_left hne
    _ = (vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1)).relIndex
          ((H ⊓ vsMFix (vsMScal A) {y, y'}) ⊓ H) *
          (H ⊓ vsMFix (vsMScal A) {y, y'}).relIndex H :=
        (Subgroup.relIndex_inf_mul_relIndex _ _ _).symm
    _ = (vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1)).relIndex
          (H ⊓ vsMFix (vsMScal A) {y, y'}) * (H ⊓ vsMFix (vsMScal A) {y, y'}).relIndex H := by
        rw [inf_eq_left.2 inf_le_left]
    _ ≤ (2 ^ 1 * 2) * 16 := Nat.mul_le_mul hK hKH
    _ ≤ 72 := by norm_num

end Q8

end GI.Proved
