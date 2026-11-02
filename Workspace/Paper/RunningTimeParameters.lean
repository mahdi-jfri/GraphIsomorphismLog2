import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Section 7.5: choice of parameters

The conditions (i) to (iv) of Section 7.5 of the paper, the
claim that they can be met, the claim that the example values meet them, and the
margins of the last paragraph. The base size `N₀` is in
`Workspace/Paper/RunningTimeBaseSize.lean`.
-/

namespace GI.Paper

open Real

/-! ## Named quantities of Section 7.2 and 7.5 -/

/-- `c_θ = (1/2) log(1/θ)` (Section 7.2). -/
noncomputable def cTheta (θ : ℝ) : ℝ := 1 / 2 * Real.log (1 / θ)

/-- `c_β = log(1/β)` (equation `eq:main-cap-payment`). -/
noncomputable def cBeta (β : ℝ) : ℝ := Real.log (1 / β)

/-- `x₀ = log 8`, the value of `x = log(s+2)` at `s = 6` (item (iv)). -/
noncomputable def xZero : ℝ := Real.log 8

/-- `H_* = 2B + log(8J)` (item (iv)). -/
noncomputable def hStar (B : ℝ) (J : ℕ) : ℝ := 2 * B + Real.log (8 * J)

/-- The constants of item (iv) of Section 7.5, together with the facts from items (i)
and (iii) that the charging argument of Section 7.2 uses. Each field is quoted from
Section 7.5 unless marked otherwise. -/
structure ChargingConstants where
  /-- the fixed exponent of Section 7.2 -/
  a : ℝ
  /-- the phase-threshold exponent of equation `eq:scale-constraints` -/
  γ : ℝ
  /-- the test size `κ` -/
  κ : ℝ
  θ : ℝ
  β : ℝ
  /-- the bounded ideal cutoff of item (i) -/
  q₀ : ℝ
  /-- the bound on the number of child classes at a node -/
  J : ℕ
  /-- the parity multiplicity of a row construction -/
  b₀ : ℝ
  A : ℝ
  B : ℝ
  D : ℕ
  /-- item (iv): "Fix `a ≥ 1`". -/
  one_le_a : 1 ≤ a
  /-- item (ii): `2α < γ < 1`, so `0 < γ < 1`. -/
  γ_pos : 0 < γ
  γ_lt_one : γ < 1
  /-- item (i): `κ` is a positive test size. -/
  κ_pos : 0 < κ
  /-- item (iii): "Choose `θ < 1` above `1/2`". -/
  half_lt_θ : 1 / 2 < θ
  θ_lt_one : θ < 1
  /-- item (iii): `max{1/2, …} < β < 1`. -/
  half_lt_β : 1 / 2 < β
  β_lt_one : β < 1
  /-- item (i): "so that `βq₀ ≥ 2`". -/
  two_le_βq₀ : 2 ≤ β * q₀
  /-- item (iv): `J` is an upper bound on a number of classes; a class exists. -/
  one_le_J : 1 ≤ J
  /-- item (iv): `b₀` bounds a multiplicity, so it is at least one. -/
  one_le_b₀ : 1 ≤ b₀
  /-- item (iv): `B ≥ log(8 J b₀)`. -/
  B_ge : Real.log (8 * J * b₀) ≤ B
  /-- equation `eq:main-constant-domain`, first half. -/
  A_domain : a / γ + hStar B J / xZero ≤ A * cTheta θ
  /-- equation `eq:main-constant-domain`, second half. -/
  A_symmetry : a / γ + hStar B J / xZero ≤ A * κ
  /-- equation `eq:main-constant-cap`. -/
  A_cap : a + hStar B J / Real.log q₀ ≤ A * cBeta β
  /-- equation `eq:main-constant-enum`. -/
  A_enum : a + (a / γ) / Real.log 2 + hStar B J / (xZero * Real.log 2) ≤ A / 3
  /-- equation `eq:main-constant-product`. -/
  A_product : 4 + a / γ + hStar B J / xZero ≤ A
  /-- item (iv): "an integer `D ≥ 3`". -/
  three_le_D : 3 ≤ D
  /-- item (iv): "with `D > a/γ + 2`". -/
  D_gt : a / γ + 2 < D

namespace ChargingConstants

variable (C : ChargingConstants)

/-- `a_* = a/γ` (equation `eq:main-phase-active`). -/
noncomputable def aStar : ℝ := C.a / C.γ

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem xZero_pos : 0 < xZero := Real.log_pos (by norm_num)

theorem a_pos : 0 < C.a := by linarith [C.one_le_a]

theorem aStar_nonneg : 0 ≤ C.aStar := div_nonneg C.a_pos.le C.γ_pos.le

theorem log8J_pos : 0 < Real.log (8 * C.J) := by
  apply Real.log_pos
  have : (1 : ℝ) ≤ C.J := by exact_mod_cast C.one_le_J
  linarith

theorem B_nonneg : 0 ≤ C.B := by
  have h : 0 ≤ Real.log (8 * C.J * C.b₀) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ C.J := by exact_mod_cast C.one_le_J
    nlinarith [C.one_le_b₀]
  linarith [C.B_ge]

theorem hStar_nonneg : 0 ≤ hStar C.B C.J := by
  unfold hStar; linarith [C.B_nonneg, C.log8J_pos]

theorem cTheta_pos : 0 < cTheta C.θ := by
  unfold cTheta
  apply mul_pos (by norm_num) (Real.log_pos _)
  rw [lt_div_iff₀ (by linarith [C.half_lt_θ])]; linarith [C.θ_lt_one]

theorem cBeta_pos : 0 < cBeta C.β := by
  unfold cBeta
  apply Real.log_pos
  rw [lt_div_iff₀ (by linarith [C.half_lt_β])]; linarith [C.β_lt_one]

theorem one_lt_q₀ : 1 < C.q₀ := by
  have := C.two_le_βq₀; nlinarith [C.β_lt_one, C.half_lt_β]

theorem A_nonneg : 0 ≤ C.A := by
  have h1 : 0 ≤ hStar C.B C.J / xZero := div_nonneg C.hStar_nonneg xZero_pos.le
  linarith [C.A_product, C.aStar_nonneg, show C.aStar = C.a / C.γ from rfl]

/-! ## The margins of the last paragraph of Section 7.5

Each lemma says that a row of the table of Section 7.2 leaves the margin
`H_* - 2B = log(8J)` after its logarithmic multiplicity is paid. -/

/-- Physical row: "the physical and symmetry rows of the table have logarithmic
multiplicity at most `a_* x`, and (main-constant-domain) leaves a margin at least
`H_* - 2B = log(8J)`". -/
theorem margin_domain {x : ℝ} (hx : xZero ≤ x) :
    C.aStar * x + Real.log (8 * C.J) ≤ C.A * cTheta C.θ * x - 2 * C.B := by
  have h := mul_le_mul_of_nonneg_right C.A_domain (xZero_pos.le.trans hx)
  have hH : hStar C.B C.J ≤ hStar C.B C.J / xZero * x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ xZero_pos]
    exact mul_le_mul_of_nonneg_left hx C.hStar_nonneg
  unfold hStar at hH h
  unfold aStar
  nlinarith

/-- Symmetry row, by the second half of (main-constant-domain). -/
theorem margin_symmetry {x : ℝ} (hx : xZero ≤ x) :
    C.aStar * x + Real.log (8 * C.J) ≤ C.A * C.κ * x - 2 * C.B := by
  have h := mul_le_mul_of_nonneg_right C.A_symmetry (xZero_pos.le.trans hx)
  have hH : hStar C.B C.J ≤ hStar C.B C.J / xZero * x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ xZero_pos]
    exact mul_le_mul_of_nonneg_left hx C.hStar_nonneg
  unfold hStar at hH h
  unfold aStar
  nlinarith

/-- Cap row: "The cap row has logarithmic multiplicity at most `a log q` and the same
margin by (main-constant-cap)", for `q ≥ q₀`. -/
theorem margin_cap {q : ℝ} (hq : C.q₀ ≤ q) :
    C.a * Real.log q + Real.log (8 * C.J) ≤ C.A * cBeta C.β * Real.log q - 2 * C.B := by
  have hl0 : 0 < Real.log C.q₀ := Real.log_pos C.one_lt_q₀
  have hlq : Real.log C.q₀ ≤ Real.log q := Real.log_le_log (by linarith [C.one_lt_q₀]) hq
  have h := mul_le_mul_of_nonneg_right C.A_cap (hl0.le.trans hlq)
  have hH : hStar C.B C.J ≤ hStar C.B C.J / Real.log C.q₀ * Real.log q := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl0]
    exact mul_le_mul_of_nonneg_left hlq C.hStar_nonneg
  unfold hStar at hH h
  nlinarith

/-- Enumeration row, the display "For enumeration use `log 2 ≤ log d ≤ x`". -/
theorem margin_enum_display {x ℓ : ℝ} (hx : xZero ≤ x) (hℓ2 : Real.log 2 ≤ ℓ)
    (hℓx : ℓ ≤ x) :
    C.a * ℓ ^ 2 + C.aStar * x + hStar C.B C.J ≤
      (C.a + C.aStar / Real.log 2 + hStar C.B C.J / (xZero * Real.log 2)) * x * ℓ := by
  have hl2 := log_two_pos'
  have hx0 : 0 < x := xZero_pos.trans_le hx
  have hℓ0 : 0 < ℓ := hl2.trans_le hℓ2
  have h1 : C.a * ℓ ^ 2 ≤ C.a * x * ℓ := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hℓx hℓ0.le) C.a_pos.le
    nlinarith
  have h2 : C.aStar * x ≤ C.aStar / Real.log 2 * x * ℓ := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hl2]
    have := mul_le_mul_of_nonneg_left hℓ2 (mul_nonneg C.aStar_nonneg hx0.le)
    nlinarith
  have h3 : hStar C.B C.J ≤ hStar C.B C.J / (xZero * Real.log 2) * x * ℓ := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (mul_pos xZero_pos hl2)]
    have := mul_le_mul hx hℓ2 hl2.le hx0.le
    have := mul_le_mul_of_nonneg_left this C.hStar_nonneg
    nlinarith
  nlinarith

/-- Enumeration row: (main-constant-enum) gives the margin after subtracting `2B`. -/
theorem margin_enum {x ℓ : ℝ} (hx : xZero ≤ x) (hℓ2 : Real.log 2 ≤ ℓ) (hℓx : ℓ ≤ x) :
    C.a * ℓ ^ 2 + C.aStar * x + Real.log (8 * C.J) ≤ C.A / 3 * x * ℓ - 2 * C.B := by
  have h := C.margin_enum_display hx hℓ2 hℓx
  have h2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right C.A_enum (xZero_pos.le.trans hx))
    (log_two_pos'.le.trans hℓ2)
  unfold hStar at h h2
  unfold aStar at h ⊢
  linarith

/-- Product row, the display "For a product exponent `r ≥ 2`, use …", given the bound
`log(2^r r!) ≤ 4(r-1)x` of `GI.Paper.main_product_index_bound`. -/
theorem margin_product_display {x L r : ℝ} (hx : xZero ≤ x) (hr : 2 ≤ r)
    (hL : L ≤ 4 * (r - 1) * x) :
    L + C.aStar * x + hStar C.B C.J ≤ (4 + C.aStar + hStar C.B C.J / xZero) * (r - 1) * x := by
  have hx0 : 0 < x := xZero_pos.trans_le hx
  have h1 : C.aStar * x ≤ C.aStar * (r - 1) * x := by
    have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ r - 1)
      (mul_nonneg C.aStar_nonneg hx0.le)
    nlinarith
  have h2 : hStar C.B C.J ≤ hStar C.B C.J / xZero * (r - 1) * x := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ xZero_pos]
    have := mul_le_mul (by linarith : (1 : ℝ) ≤ r - 1) hx xZero_pos.le (by linarith)
    have := mul_le_mul_of_nonneg_left this C.hStar_nonneg
    nlinarith
  nlinarith

/-- Product row: (main-constant-product) pays this row as well. -/
theorem margin_product {x L r : ℝ} (hx : xZero ≤ x) (hr : 2 ≤ r)
    (hL : L ≤ 4 * (r - 1) * x) :
    L + C.aStar * x + Real.log (8 * C.J) ≤ C.A * (r - 1) * x - 2 * C.B := by
  have h := C.margin_product_display hx hr hL
  have h2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right C.A_product (by linarith : (0 : ℝ) ≤ r - 1))
    (xZero_pos.le.trans hx)
  unfold hStar at h h2
  unfold aStar at h ⊢
  linarith

/-- Last row: "`b₀ e^{-B} ≤ 1/(8J)`". -/
theorem margin_row : C.b₀ * Real.exp (-C.B) ≤ 1 / (8 * C.J) := by
  have hJ : (0 : ℝ) < 8 * C.J := by
    have : (1 : ℝ) ≤ C.J := by exact_mod_cast C.one_le_J
    linarith
  have hb : 0 < C.b₀ := by linarith [C.one_le_b₀]
  have h := Real.exp_le_exp.mpr C.B_ge
  rw [Real.exp_log (by positivity)] at h
  rw [Real.exp_neg, le_div_iff₀ hJ]
  have he := Real.exp_pos C.B
  calc C.b₀ * (Real.exp C.B)⁻¹ * (8 * C.J) = (8 * C.J * C.b₀) / Real.exp C.B := by
        field_simp
    _ ≤ 1 := by rw [div_le_one he]; exact h

end ChargingConstants

/-! ## Items (ii) and (iii) -/

/-- Item (ii): `1/3 < α < 1/2` and `2α < γ < 1` imply `1-α < γ` and `1-2α < α`. -/
theorem sec_parameters_item_ii {α γ : ℝ} (hα : 1 / 3 < α) (_hα' : α < 1 / 2)
    (hγ : 2 * α < γ) (_hγ' : γ < 1) : 1 - α < γ ∧ 1 - 2 * α < α := by
  constructor <;> linarith

/-- Item (iii) can be met: for `0 < δ ≤ 1/4` and `2/3 < η < 1` there are `β` and
`θ < 1` above `1/2` and `2η(1-η)`, and a cutoff `q₀` with
`2η(1-η)q/(q-1) ≤ θ` for every `q ≥ q₀`. -/
theorem sec_parameters_item_iii {δ η : ℝ} (hδ : 0 < δ) (_hδ' : δ ≤ 1 / 4)
    (hη : 2 / 3 < η) (hη' : η < 1) :
    ∃ β θ q₀ : ℝ, max (max (1 / 2) (1 - δ)) (max (1 - η * δ) η) < β ∧ β < 1 ∧
      1 / 2 < θ ∧ 2 * η * (1 - η) < θ ∧ θ < 1 ∧ 1 < q₀ ∧
      ∀ q : ℝ, q₀ ≤ q → 2 * η * (1 - η) * q / (q - 1) ≤ θ := by
  set m := max (max (1 / 2) (1 - δ)) (max (1 - η * δ) η)
  have hm : m < 1 := by
    simp only [m, max_lt_iff]
    refine ⟨⟨by norm_num, by linarith⟩, by nlinarith, hη'⟩
  -- `2η(1-η) < 1/2 < 3/4`, since `η(1-η) ≤ 1/4`.
  have hp : 2 * η * (1 - η) ≤ 1 / 2 := by nlinarith [sq_nonneg (η - 1 / 2)]
  refine ⟨(m + 1) / 2, 3 / 4, 3, by linarith, by linarith, by norm_num, by linarith,
    by norm_num, by norm_num, ?_⟩
  intro q hq
  rw [div_le_iff₀ (by linarith)]
  have hp0 : 0 ≤ 2 * η * (1 - η) := by nlinarith
  nlinarith

/-- Item (iv) can be met: for any `a ≥ 1`, `0 < γ < 1`, `κ > 0`, `θ, β ∈ (1/2,1)`,
`βq₀ ≥ 2`, `J ≥ 1`, `b₀ ≥ 1`, there are `A`, `B`, `D` that complete them to
`ChargingConstants`. -/
theorem sec_parameters_item_iv {a γ κ θ β q₀ b₀ : ℝ} {J : ℕ} (ha : 1 ≤ a) (hγ : 0 < γ)
    (hγ1 : γ < 1) (hκ : 0 < κ) (hθ : 1 / 2 < θ) (hθ1 : θ < 1) (hβ : 1 / 2 < β)
    (hβ1 : β < 1) (hq : 2 ≤ β * q₀) (hJ : 1 ≤ J) (hb : 1 ≤ b₀) :
    ∃ C : ChargingConstants, C.a = a ∧ C.γ = γ ∧ C.κ = κ ∧ C.θ = θ ∧ C.β = β ∧
      C.q₀ = q₀ ∧ C.J = J ∧ C.b₀ = b₀ := by
  set B := Real.log (8 * J * b₀)
  set H := hStar B J
  have cθ : 0 < cTheta θ := by
    unfold cTheta
    apply mul_pos (by norm_num) (Real.log_pos _)
    rw [lt_div_iff₀ (by linarith)]; linarith
  have cβ : 0 < cBeta β := by
    unfold cBeta
    apply Real.log_pos
    rw [lt_div_iff₀ (by linarith)]; linarith
  -- One `A` above each of the five lower bounds.
  set A := |a / γ + H / xZero| / cTheta θ + |a / γ + H / xZero| / κ +
    |a + H / Real.log q₀| / cBeta β +
    3 * |a + a / γ / Real.log 2 + H / (xZero * Real.log 2)| + |4 + a / γ + H / xZero|
  have hA1 : 0 ≤ |a / γ + H / xZero| / cTheta θ := div_nonneg (abs_nonneg _) cθ.le
  have hA2 : 0 ≤ |a / γ + H / xZero| / κ := div_nonneg (abs_nonneg _) hκ.le
  have hA3 : 0 ≤ |a + H / Real.log q₀| / cBeta β := div_nonneg (abs_nonneg _) cβ.le
  have hA4 : 0 ≤ 3 * |a + a / γ / Real.log 2 + H / (xZero * Real.log 2)| := by positivity
  have hA5 : 0 ≤ |4 + a / γ + H / xZero| := abs_nonneg _
  have key : ∀ {u c : ℝ}, 0 < c → |u| / c ≤ A → u ≤ A * c := by
    intro u c hc h
    have := (div_le_iff₀ hc).mp h
    linarith [le_abs_self u]
  obtain ⟨D, hD⟩ := exists_nat_gt (a / γ + 2)
  let C : ChargingConstants :=
    { a := a, γ := γ, κ := κ, θ := θ, β := β, q₀ := q₀, J := J, b₀ := b₀, A := A,
      B := B, D := max D 3, one_le_a := ha, γ_pos := hγ, γ_lt_one := hγ1, κ_pos := hκ,
      half_lt_θ := hθ, θ_lt_one := hθ1, half_lt_β := hβ, β_lt_one := hβ1,
      two_le_βq₀ := hq, one_le_J := hJ, one_le_b₀ := hb, B_ge := le_rfl,
      A_domain := key cθ (by linarith), A_symmetry := key hκ (by linarith),
      A_cap := key cβ (by linarith),
      A_enum := by
        have := le_abs_self (a + a / γ / Real.log 2 + H / (xZero * Real.log 2)); linarith
      A_product := by have := le_abs_self (4 + a / γ + H / xZero); linarith
      three_le_D := le_max_right _ _
      D_gt := by
        calc a / γ + 2 < D := hD
          _ ≤ ((max D 3 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _ }
  exact ⟨C, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The example values -/

/-- The example of Section 7.5: `κ = 64`, `δ = 1/4`, `η = 3/4`, `β = 9/10`,
`θ = 3/4`, `α = 2/5`, `γ = 9/10` satisfy items (ii) and (iii), including the
displayed checks `2α = 4/5 < γ`, `1-α = 3/5 < γ`, `1-2α = 1/5 < α`,
`1-ηδ = 13/16 < β`, `2η(1-η) = 3/8 < θ`; the cutoff condition
`2η(1-η)q/(q-1) ≤ θ` holds for every `q ≥ 2`; and the cutoff
`q₀ = 4κ+2 = 258` of item (i) satisfies `βq₀ ≥ 2`. -/
theorem sec_parameters_example :
    let κ : ℝ := 64; let δ : ℝ := 1 / 4; let η : ℝ := 3 / 4; let β : ℝ := 9 / 10
    let θ : ℝ := 3 / 4; let α : ℝ := 2 / 5; let γ : ℝ := 9 / 10
    -- item (ii)
    (1 / 3 < α ∧ α < 1 / 2 ∧ 2 * α < γ ∧ γ < 1) ∧
    (2 * α = 4 / 5 ∧ 1 - α = 3 / 5 ∧ 1 - α < γ ∧ 1 - 2 * α = 1 / 5 ∧ 1 - 2 * α < α) ∧
    -- item (iii)
    (0 < δ ∧ δ ≤ 1 / 4 ∧ 2 / 3 < η ∧ η < 1) ∧
    (max (max (1 / 2) (1 - δ)) (max (1 - η * δ) η) < β ∧ β < 1) ∧
    (1 - η * δ = 13 / 16 ∧ 2 * η * (1 - η) = 3 / 8) ∧
    (1 / 2 < θ ∧ 2 * η * (1 - η) < θ ∧ θ < 1) ∧
    (∀ q : ℝ, 2 ≤ q → 2 * η * (1 - η) * q / (q - 1) ≤ θ) ∧
    -- item (i) with `q₀ = 4κ+2`
    (2 ≤ β * (4 * κ + 2)) ∧
    -- the constants of Section 7.2 are positive
    (0 < cTheta θ ∧ 0 < cBeta β) := by
  intro κ δ η β θ α γ
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, by norm_num, by norm_num, ?_, by norm_num,
    ?_⟩
  · simp only [β, δ, η]; norm_num
  · intro q hq
    rw [div_le_iff₀ (by linarith)]
    simp only [η, θ]; nlinarith
  · constructor
    · unfold cTheta; simp only [θ]
      exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
    · unfold cBeta; simp only [β]; exact Real.log_pos (by norm_num)

/-- The example values complete to constants of item (iv): with `κ = 64`, `θ = 3/4`,
`β = 9/10`, `γ = 9/10`, `q₀ = 258`, `J = 8` and any `a ≥ 1`, `b₀ ≥ 1`. -/
theorem sec_parameters_example_constants {a b₀ : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b₀) :
    ∃ C : ChargingConstants, C.a = a ∧ C.γ = 9 / 10 ∧ C.κ = 64 ∧ C.θ = 3 / 4 ∧
      C.β = 9 / 10 ∧ C.q₀ = 258 ∧ C.J = 8 ∧ C.b₀ = b₀ :=
  sec_parameters_item_iv ha (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb

end GI.Paper
