module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# The weight of the recursion, and why it closes

This file has only real inequalities. It proves that one choice of the constant `A` pays every
operation of Sections 8.5 and 8.6 of the paper. The states of the recursion enter through their
resources (`Res`): the domain size `s`, and the numbers `ψ`, `ρ`, `Q`. See
`Workspace/Degree/Potential.lean` for the resources of a state.

The weight is `W(r) = sz³ exp(A ((ψ + ρ) L + Q))`, with `sz = max(1, s)`. So the exponent of the
size is `3`, as in the paper, and `W ≥ 1` on every state, also on one with an empty domain. The
bound to prove is `T ≤ K W`.

Each operation is a statement that a sum of costs of children and the node's own work is at most
`K W(r)`:

* `base_closes` and `baseRho_closes`: the general solver on a small state;
* `orbit_closes`: the orbit chain, paid by `s³ ≥ s₁³ + s₂³ + 6`;
* `enum_closes`: enumeration of a primitive quotient of degree `b`;
* `product_closes`: normalization of a product, paid by `ρ`;
* `norm_closes`: the single-factor normalization, with at most two children;
* `giant_closes`: a giant step, at cost at most `K W / 4`;
* `root_W_le`: the bound `W = exp(O(x L))` at the root, where `x = log(n + 2)`.

`exists_A` gives one `A` for all of them. The own work is at most `K`, or `K (1 + I)` at a node with
`I` branches, so `K` pays both the polynomial work and the configuration oracle.
-/

namespace GI.Degree

open Real

/-- The resources of a state, as the weight reads them. -/
structure Res where
  /-- The size of the active domain. -/
  s : ℕ
  /-- The largest of `log(|v^G| + 2) + σ(v)` over the domain. -/
  psi : ℝ
  /-- The hierarchy measure `ρ`. -/
  rho : ℝ
  /-- The cap sum `Q`. -/
  Q : ℝ

namespace Res

/-- `max(1, s)`. -/
noncomputable def sz (r : Res) : ℝ := max 1 (r.s : ℝ)

/-- `Ψ = A ((ψ + ρ) L + Q)`. -/
noncomputable def pot (A L : ℝ) (r : Res) : ℝ := A * ((r.psi + r.rho) * L + r.Q)

/-- `W = sz³ exp Ψ`. -/
noncomputable def W (A L : ℝ) (r : Res) : ℝ := r.sz ^ 3 * exp (r.pot A L)

/-- The resources are nonnegative. -/
structure OK (r : Res) : Prop where
  psi : 0 ≤ r.psi
  rho : 0 ≤ r.rho
  Q : 0 ≤ r.Q

/-- `c` has at most the resources of `r`. -/
structure Le (c r : Res) : Prop where
  s : c.s ≤ r.s
  psi : c.psi ≤ r.psi
  rho : c.rho ≤ r.rho
  Q : c.Q ≤ r.Q

theorem one_le_sz (r : Res) : 1 ≤ r.sz := le_max_left _ _

theorem sz_pos (r : Res) : 0 < r.sz := lt_of_lt_of_le one_pos r.one_le_sz

theorem sz_eq {r : Res} (h : 1 ≤ r.s) : r.sz = r.s := by
  unfold sz; exact max_eq_right (by exact_mod_cast h)

theorem sz_mono {c r : Res} (h : c.s ≤ r.s) : c.sz ≤ r.sz := by
  unfold sz
  exact max_le_max le_rfl (by exact_mod_cast h)

theorem W_pos (A L : ℝ) (r : Res) : 0 < r.W A L := by
  unfold W; have := r.sz_pos; positivity

theorem exp_le_W (A L : ℝ) (r : Res) : exp (r.pot A L) ≤ r.W A L := by
  unfold W
  have h : 1 ≤ r.sz ^ 3 := one_le_pow₀ r.one_le_sz
  nlinarith [exp_pos (r.pot A L)]

theorem pot_mono {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) {c r : Res} (h : c.Le r) :
    c.pot A L ≤ r.pot A L := by
  unfold pot
  have := mul_le_mul_of_nonneg_right (add_le_add h.psi h.rho) hL
  exact mul_le_mul_of_nonneg_left (add_le_add this h.Q) hA

theorem W_mono {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) {c r : Res} (h : c.Le r) :
    c.W A L ≤ r.W A L := by
  unfold W
  have h1 : c.sz ^ 3 ≤ r.sz ^ 3 := pow_le_pow_left₀ c.sz_pos.le (sz_mono h.s) 3
  have h2 := exp_le_exp.2 (pot_mono hA hL h)
  exact mul_le_mul h1 h2 (exp_pos _).le (by have := r.sz_pos; positivity)

/-- A child whose potential is lower by `t`: its weight is its `sz³` times `exp(Ψ - t)`. -/
theorem W_le_of_drop {A L t : ℝ} {c r : Res} (h : c.pot A L + t ≤ r.pot A L) :
    c.W A L ≤ c.sz ^ 3 * exp (r.pot A L - t) := by
  unfold W
  have h1 := exp_le_exp.2 (show c.pot A L ≤ r.pot A L - t by linarith)
  exact mul_le_mul_of_nonneg_left h1 (by have := c.sz_pos; positivity)

/-- A child with a domain no larger than the parent's, and potential lower by `t`. -/
theorem W_le_exp_mul {A L t : ℝ} {c r : Res} (hs : c.s ≤ r.s) (h : c.pot A L + t ≤ r.pot A L) :
    c.W A L ≤ exp (-t) * r.W A L := by
  refine (W_le_of_drop h).trans ?_
  have h1 : c.sz ^ 3 ≤ r.sz ^ 3 := pow_le_pow_left₀ c.sz_pos.le (sz_mono hs) 3
  unfold W
  rw [sub_eq_add_neg, exp_add]
  have h2 : 0 < exp (r.pot A L) * exp (-t) := by positivity
  nlinarith

/-- The potential drop from drops of the resources. -/
theorem pot_add_le {A L a b e : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) {c r : Res} (h1 : c.psi + a ≤ r.psi)
    (h2 : c.rho + b ≤ r.rho) (h3 : c.Q + e ≤ r.Q) :
    c.pot A L + A * ((a + b) * L + e) ≤ r.pot A L := by
  unfold pot
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hA
  have := mul_le_mul_of_nonneg_right (add_le_add h1 h2) hL
  nlinarith

/-- The drop of a list of children with total mass at most `M` times the parent's: their
weights sum to at most `M exp(-t) W(r)`. -/
theorem sum_W_le {A L t M : ℝ} {r : Res} (cs : List Res)
    (hd : ∀ c ∈ cs, c.pot A L + t ≤ r.pot A L)
    (hm : (cs.map fun c => c.sz ^ 3).sum ≤ M * r.sz ^ 3) :
    (cs.map fun c => c.W A L).sum ≤ M * exp (-t) * r.W A L := by
  have h1 : (cs.map fun c => c.W A L).sum ≤
      (cs.map fun c => c.sz ^ 3 * exp (r.pot A L - t)).sum :=
    List.sum_le_sum fun c hc => W_le_of_drop (hd c hc)
  rw [List.sum_map_mul_right] at h1
  refine h1.trans ?_
  have h2 := mul_le_mul_of_nonneg_right hm (exp_pos (r.pot A L - t)).le
  refine h2.trans (le_of_eq ?_)
  unfold W
  rw [sub_eq_add_neg, exp_add]
  ring

/-- The mass of `n` children, each with a domain no larger than the parent's. -/
theorem mass_le_length {r : Res} (cs : List Res) (hs : ∀ c ∈ cs, c.s ≤ r.s) :
    (cs.map fun c => c.sz ^ 3).sum ≤ (cs.length : ℝ) * r.sz ^ 3 := by
  have := List.sum_le_length_nsmul (cs.map fun c => c.sz ^ 3) (r.sz ^ 3) (by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    exact pow_le_pow_left₀ c.sz_pos.le (sz_mono (hs c hc)) 3)
  simpa using this

theorem psi_mul_le_pot {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) {r : Res} (h : r.OK) :
    A * (r.psi * L) ≤ r.pot A L := by
  unfold pot
  refine mul_le_mul_of_nonneg_left ?_ hA
  nlinarith [h.rho, h.Q, mul_nonneg h.rho hL]

theorem rho_mul_le_pot {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) {r : Res} (h : r.OK) :
    A * (r.rho * L) ≤ r.pot A L := by
  unfold pot
  refine mul_le_mul_of_nonneg_left ?_ hA
  nlinarith [h.psi, h.Q, mul_nonneg h.psi hL]

end Res

/-! ### Small facts about reals -/

theorem small_const {C y : ℝ} (hC : 0 ≤ C) (h : 31 + C ≤ y) : C * exp (-y) ≤ 1 / 32 := by
  have h1 : (1 + 31) * (1 + C) ≤ exp y := by
    have e1 := add_one_le_exp (31 : ℝ)
    have e2 := add_one_le_exp C
    have e3 := exp_le_exp.2 h
    have e4 : exp (31 + C) = exp 31 * exp C := exp_add _ _
    have : (31 + 1) * (C + 1) ≤ exp 31 * exp C :=
      mul_le_mul e1 e2 (by linarith) (exp_pos _).le
    nlinarith
  rw [exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (exp_pos _) (by norm_num)]
  nlinarith

theorem exp_neg_le_quarter {y : ℝ} (h : 3 ≤ y) : exp (-y) ≤ 1 / 4 := by
  have := add_one_le_exp y
  rw [exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- `log²(s + 2) ≤ 8 s` for `s ≥ 1`. -/
theorem log_sq_le (s : ℕ) (hs : 1 ≤ s) : Real.log ((s : ℝ) + 2) ^ 2 ≤ 8 * s := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  set t : ℝ := (s : ℝ) + 2 with ht
  set u : ℝ := √t with hu
  have ht0 : 0 ≤ t := by linarith
  have hu1 : 1 ≤ u := by
    rw [hu, Real.one_le_sqrt]; linarith
  have huu : u ^ 2 = t := Real.sq_sqrt ht0
  have hy : Real.log t = 2 * Real.log u := by
    rw [hu, Real.log_sqrt ht0]; ring
  have hlu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hl0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  rw [hy]
  nlinarith

/-- A size with `s² ≤ D⁵` has `log(s + 2) ≤ 3 log(D + 2)`. -/
theorem log_le_of_sq_le {s D : ℕ} (h : s ^ 2 ≤ D ^ 5) (hD : 1 ≤ D) :
    Real.log ((s : ℝ) + 2) ≤ 3 * Real.log ((D : ℝ) + 2) := by
  have h3 : s ≤ D ^ 3 := by
    by_contra hc
    push Not at hc
    have h1 : (D ^ 3 + 1) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hc 2
    have h2 : D ^ 5 ≤ D ^ 6 := Nat.pow_le_pow_right hD (by norm_num)
    have h3 : (D ^ 3 + 1) ^ 2 = D ^ 6 + 2 * D ^ 3 + 1 := by ring
    omega
  have h4 : s + 2 ≤ (D + 2) ^ 3 := by nlinarith [Nat.zero_le D, Nat.pow_le_pow_left (Nat.le_add_right D 2) 3]
  have h5 : (s : ℝ) + 2 ≤ ((D : ℝ) + 2) ^ 3 := by exact_mod_cast h4
  have hs0 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
  have := Real.log_le_log hs0 h5
  rwa [Real.log_pow] at this

/-! ### The operations -/

namespace Res

variable {A L K : ℝ} {r : Res}

theorem one_le_exp_pot (hA : 0 ≤ A) (hL : 0 ≤ L) (h : r.OK) : 1 ≤ exp (r.pot A L) := by
  refine one_le_exp ?_
  have h1 := psi_mul_le_pot hA hL h
  have h2 : 0 ≤ A * (r.psi * L) := mul_nonneg hA (mul_nonneg h.psi hL)
  linarith

theorem one_le_W (hA : 0 ≤ A) (hL : 0 ≤ L) (h : r.OK) : 1 ≤ r.W A L :=
  (one_le_exp_pot hA hL h).trans (exp_le_W A L r)

/-- **The general solver on a state with `s ≤ ρ`.** Its cost `exp(a log²(s + 2))` is paid by `ρ` in
the weight, and the rest of its cost by `K`. -/
theorem baseRho_closes {a : ℝ} (ha : 0 ≤ a) (hA : 4 * a + 1 ≤ A) (hL : 2 ≤ L) (hK : 1 ≤ K)
    (hok : r.OK) (hs : 1 ≤ r.s) (hρ : (r.s : ℝ) ≤ r.rho) :
    exp (a * Real.log ((r.s : ℝ) + 2) ^ 2) + K / 2 ≤ K * r.W A L := by
  have hA0 : 0 ≤ A := by linarith
  have hs' : (1 : ℝ) ≤ r.s := by exact_mod_cast hs
  have h1 := log_sq_le r.s hs
  have h2 := rho_mul_le_pot hA0 (by linarith : (0 : ℝ) ≤ L) hok
  have h3 : a * Real.log ((r.s : ℝ) + 2) ^ 2 + 1 ≤ r.pot A L := by
    have hρ0 : 0 ≤ r.rho := hok.rho
    have h4 : a * Real.log ((r.s : ℝ) + 2) ^ 2 ≤ a * (8 * r.rho) := by
      have : Real.log ((r.s : ℝ) + 2) ^ 2 ≤ 8 * r.rho := by linarith
      exact mul_le_mul_of_nonneg_left this ha
    have h5 : (4 * a + 1) * (r.rho * 2) ≤ A * (r.rho * L) :=
      mul_le_mul hA (mul_le_mul_of_nonneg_left hL hρ0) (by positivity) hA0
    have h6 : 1 ≤ r.rho := hs'.trans hρ
    nlinarith
  have h6 : exp (a * Real.log ((r.s : ℝ) + 2) ^ 2) * 2 ≤ exp (r.pot A L) := by
    have := exp_le_exp.2 h3
    rw [exp_add] at this
    have e1 := add_one_le_exp (1 : ℝ)
    have e0 := exp_pos (a * Real.log ((r.s : ℝ) + 2) ^ 2)
    nlinarith
  have h7 := exp_le_W A L r
  have h8 := one_le_W hA0 (by linarith : (0 : ℝ) ≤ L) hok
  nlinarith

/-- **The orbit chain.** Two children on disjoint nonempty parts of the domain, with no more
resources. The node's own work is paid by `s³ ≥ s₁³ + s₂³ + 6`. -/
theorem orbit_closes (hA : 0 ≤ A) (hL : 0 ≤ L) (hK : 0 ≤ K) (hok : r.OK) {c₁ c₂ : Res}
    (h₁ : c₁.Le r) (h₂ : c₂.Le r) (h1 : 1 ≤ c₁.s) (h2 : 1 ≤ c₂.s) (hs : c₁.s + c₂.s ≤ r.s) :
    K + K * c₁.W A L + K * c₂.W A L ≤ K * r.W A L := by
  have hE := one_le_exp_pot hA hL hok
  have hr1 : 1 ≤ r.s := by omega
  have ha : (1 : ℝ) ≤ c₁.s := by exact_mod_cast h1
  have hb : (1 : ℝ) ≤ c₂.s := by exact_mod_cast h2
  have hab : (c₁.s : ℝ) + c₂.s ≤ r.s := by exact_mod_cast hs
  have hp₁ := exp_le_exp.2 (pot_mono hA hL h₁)
  have hp₂ := exp_le_exp.2 (pot_mono hA hL h₂)
  have hW₁ : c₁.W A L ≤ (c₁.s : ℝ) ^ 3 * exp (r.pot A L) := by
    unfold W; rw [sz_eq h1]
    exact mul_le_mul_of_nonneg_left hp₁ (by positivity)
  have hW₂ : c₂.W A L ≤ (c₂.s : ℝ) ^ 3 * exp (r.pot A L) := by
    unfold W; rw [sz_eq h2]
    exact mul_le_mul_of_nonneg_left hp₂ (by positivity)
  have hW : r.W A L = (r.s : ℝ) ^ 3 * exp (r.pot A L) := by unfold W; rw [sz_eq hr1]
  have hcube : (c₁.s : ℝ) ^ 3 + (c₂.s : ℝ) ^ 3 + 1 ≤ (r.s : ℝ) ^ 3 := by
    have h3 : ((c₁.s : ℝ) + c₂.s) ^ 3 ≤ (r.s : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hab 3
    nlinarith [mul_pos (lt_of_lt_of_le one_pos ha) (lt_of_lt_of_le one_pos hb)]
  have h4 : c₁.W A L + c₂.W A L + 1 ≤ r.W A L := by
    rw [hW]
    have := mul_le_mul_of_nonneg_right hcube (exp_pos (r.pot A L)).le
    nlinarith
  nlinarith

/-- **The orbit chain, when the first child is empty and there is no second call.** The own work
is paid by `s³ ≥ s₁³ + 1`, and it needs `s₁ < s`. -/
theorem orbit_closes₁ (hA : 0 ≤ A) (hL : 0 ≤ L) (hK : 0 ≤ K) (hok : r.OK) {c : Res} (h : c.Le r)
    (hc : c.s < r.s) (hc1 : 1 ≤ c.s) : K + K * c.W A L ≤ K * r.W A L := by
  have hE := one_le_exp_pot hA hL hok
  have ha : (1 : ℝ) ≤ c.s := by exact_mod_cast hc1
  have hab : (c.s : ℝ) + 1 ≤ r.s := by exact_mod_cast hc
  have hW₁ : c.W A L ≤ (c.s : ℝ) ^ 3 * exp (r.pot A L) := by
    unfold W; rw [sz_eq hc1]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (pot_mono hA hL h)) (by positivity)
  have hW : r.W A L = (r.s : ℝ) ^ 3 * exp (r.pot A L) := by
    unfold W; rw [sz_eq (by omega)]
  have hcube : (c.s : ℝ) ^ 3 + 1 ≤ (r.s : ℝ) ^ 3 := by
    have h3 : ((c.s : ℝ) + 1) ^ 3 ≤ (r.s : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hab 3
    nlinarith [sq_nonneg (c.s : ℝ)]
  have h4 : c.W A L + 1 ≤ r.W A L := by
    rw [hW]
    have := mul_le_mul_of_nonneg_right hcube (exp_pos (r.pot A L)).le
    nlinarith
  nlinarith

/-- **Enumeration of a primitive quotient.** At most `I ≤ exp(cE L log b)` children, whose `ψ` is
lower by `(log b)/3`, and own work at most `K (1 + I)`. The term `ψ ≥ log b` pays for the branches. -/
theorem enum_closes {lb I cE : ℝ} (hK : 0 ≤ K) (hL : 2 ≤ L) (hlb : 1 / 2 ≤ lb) (hψ : lb ≤ r.psi)
    (hok : r.OK) (hcE : 0 ≤ cE) (hA : 3 * cE + 18 ≤ A) (hI1 : 1 ≤ I)
    (hI : I ≤ exp (cE * L * lb)) (cs : List Res) (hn : (cs.length : ℝ) ≤ I)
    (hc : ∀ c ∈ cs, c.s ≤ r.s ∧ c.psi + lb / 3 ≤ r.psi ∧ c.rho ≤ r.rho ∧ c.Q ≤ r.Q) :
    K * (1 + I) + K * (cs.map fun c => c.W A L).sum ≤ K * r.W A L := by
  have hA0 : 0 ≤ A := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hLb : 1 ≤ L * lb := by nlinarith
  set t := A * ((lb / 3 + 0) * L + 0) with ht
  have hd : ∀ c ∈ cs, c.pot A L + t ≤ r.pot A L := fun c hc' => by
    obtain ⟨-, h1, h2, h3⟩ := hc c hc'
    exact pot_add_le hA0 hL0 h1 (by linarith) (by linarith)
  have hsum := sum_W_le (M := (cs.length : ℝ)) cs hd
    (mass_le_length cs fun c hc' => (hc c hc').1)
  have hWpos := r.W_pos A L
  set Y := exp (cE * L * lb) with hY
  have hX : 3 ≤ t - cE * L * lb := by
    have : t = A / 3 * (L * lb) := by rw [ht]; ring
    rw [this]
    nlinarith
  have h1 : (cs.length : ℝ) * exp (-t) ≤ 1 / 4 := by
    have e : Y * exp (-t) = exp (-(t - cE * L * lb)) := by
      rw [hY, ← exp_add]; congr 1; ring
    have h2 : (cs.length : ℝ) * exp (-t) ≤ Y * exp (-t) :=
      mul_le_mul_of_nonneg_right (hn.trans hI) (exp_pos _).le
    rw [e] at h2
    exact h2.trans (exp_neg_le_quarter hX)
  have h2 : (cs.map fun c => c.W A L).sum ≤ 1 / 4 * r.W A L :=
    hsum.trans (mul_le_mul_of_nonneg_right h1 hWpos.le)
  have h3 : 2 * (1 + I) ≤ r.W A L := by
    have hp := psi_mul_le_pot hA0 hL0 hok
    have h4 : A * (L * lb) ≤ r.pot A L :=
      le_trans (mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_right hψ hL0]) hA0) hp
    have h5 : cE * L * lb + 3 ≤ A * (L * lb) := by nlinarith
    have h6 := exp_le_exp.2 (h5.trans h4)
    rw [exp_add] at h6
    have e3 := add_one_le_exp (3 : ℝ)
    have hY0 : 0 < Y := exp_pos _
    have h7 := exp_le_W A L r
    nlinarith
  nlinarith

/-- **Normalization of a product with `r₁ + 1` coordinates.** At most `I ≤ exp(cP r₁ L)` children,
whose `ρ` is lower by `r₁`, and own work at most `K (1 + I)`. The term `ρ ≥ r₁` pays for the
branches. -/
theorem product_closes {r₁ I cP : ℝ} (hK : 0 ≤ K) (hL : 2 ≤ L) (hr₁ : 1 ≤ r₁) (hρ : r₁ ≤ r.rho)
    (hok : r.OK) (hcP : 0 ≤ cP) (hA : cP + 5 ≤ A) (hI1 : 1 ≤ I) (hI : I ≤ exp (cP * r₁ * L))
    (cs : List Res)
    (hn : (cs.length : ℝ) ≤ I)
    (hc : ∀ c ∈ cs, c.s ≤ r.s ∧ c.psi ≤ r.psi ∧ c.rho + r₁ ≤ r.rho ∧ c.Q ≤ r.Q) :
    K * (1 + I) + K * (cs.map fun c => c.W A L).sum ≤ K * r.W A L := by
  have hA0 : 0 ≤ A := by linarith
  have hL0 : 0 ≤ L := by linarith
  set t := A * ((0 + r₁) * L + 0) with ht
  have hd : ∀ c ∈ cs, c.pot A L + t ≤ r.pot A L := fun c hc' => by
    obtain ⟨-, h1, h2, h3⟩ := hc c hc'
    exact pot_add_le hA0 hL0 (by linarith) h2 (by linarith)
  have hsum := sum_W_le (M := (cs.length : ℝ)) cs hd
    (mass_le_length cs fun c hc' => (hc c hc').1)
  have hWpos := r.W_pos A L
  set Y := exp (cP * r₁ * L) with hY
  have hrL : 2 ≤ r₁ * L := by nlinarith
  have htt : t = A * (r₁ * L) := by rw [ht]; ring
  have hX : 3 ≤ t - cP * r₁ * L := by rw [htt]; nlinarith
  have h1 : (cs.length : ℝ) * exp (-t) ≤ 1 / 4 := by
    have e : Y * exp (-t) = exp (-(t - cP * r₁ * L)) := by
      rw [hY, ← exp_add]; congr 1; ring
    have h2 : (cs.length : ℝ) * exp (-t) ≤ Y * exp (-t) :=
      mul_le_mul_of_nonneg_right (hn.trans hI) (exp_pos _).le
    rw [e] at h2
    exact h2.trans (exp_neg_le_quarter hX)
  have h2 : (cs.map fun c => c.W A L).sum ≤ 1 / 4 * r.W A L :=
    hsum.trans (mul_le_mul_of_nonneg_right h1 hWpos.le)
  have h3 : 2 * (1 + I) ≤ r.W A L := by
    have hp := rho_mul_le_pot hA0 hL0 hok
    have h4 : A * (r₁ * L) ≤ r.pot A L :=
      le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρ hL0) hA0) hp
    have h5 : cP * r₁ * L + 3 ≤ A * (r₁ * L) := by nlinarith
    have h6 := exp_le_exp.2 (h5.trans h4)
    rw [exp_add] at h6
    have e3 := add_one_le_exp (3 : ℝ)
    have hY0 : 0 < Y := exp_pos _
    have h7 := exp_le_W A L r
    nlinarith
  nlinarith

/-- `exp(Ψ)` is large at a state with `ψ ≥ 1`. -/
theorem nine_le_W (hA : 4 ≤ A) (hL : 2 ≤ L) (hok : r.OK) (hψ : 1 ≤ r.psi) : 9 ≤ r.W A L := by
  have h1 := psi_mul_le_pot (by linarith : (0 : ℝ) ≤ A) (by linarith : (0 : ℝ) ≤ L) hok
  have h2 : 8 ≤ A * (r.psi * L) := by
    have : 2 ≤ r.psi * L := by nlinarith
    nlinarith
  have h3 := add_one_le_exp (r.pot A L)
  have h4 := exp_le_W A L r
  linarith

/-- **The single-factor normalization.** At most two children. A child in `GiantStep` has no
more resources, and it costs at most `K W / 4`. A child in `Continue` is on orbits of at most
half the domain, so its `ψ` is lower by `c₀`. The second component of a pair says which kind the
child is. -/
theorem norm_closes {c₀ : ℝ} (hK : 0 ≤ K) (hL : 2 ≤ L) (hA : 4 ≤ A) (hc₀ : 3 ≤ A * c₀)
    (hok : r.OK) (hψ : 1 ≤ r.psi) (cs : List (Res × Bool)) (hn : cs.length ≤ 2)
    (hc : ∀ p ∈ cs, p.1.s ≤ r.s ∧ p.1.rho ≤ r.rho ∧ p.1.Q ≤ r.Q ∧
      (if p.2 then p.1.psi ≤ r.psi else p.1.psi + c₀ ≤ r.psi)) :
    K + (cs.map fun p => (if p.2 then 1 / 4 else 1) * (K * p.1.W A L)).sum ≤ K * r.W A L := by
  have hA0 : 0 ≤ A := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hb : ∀ p ∈ cs, (if p.2 then (1 : ℝ) / 4 else 1) * (K * p.1.W A L) ≤ K * r.W A L / 4 := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hc p hp
    by_cases hg : p.2 = true
    · rw [if_pos hg] at h4 ⊢
      have := W_mono hA0 hL0 (show p.1.Le r from ⟨h1, h4, h2, h3⟩)
      have := mul_le_mul_of_nonneg_left this hK
      linarith
    · rw [if_neg hg] at h4 ⊢
      have hd : p.1.pot A L + A * ((c₀ + 0) * L + 0) ≤ r.pot A L :=
        pot_add_le hA0 hL0 h4 (by linarith) (by linarith)
      have h5 := W_le_exp_mul h1 hd
      have h6 : 3 ≤ A * ((c₀ + 0) * L + 0) := by nlinarith
      have h7 := exp_neg_le_quarter h6
      have h8 := r.W_pos A L
      have h9 : p.1.W A L ≤ 1 / 4 * r.W A L :=
        h5.trans (mul_le_mul_of_nonneg_right h7 h8.le)
      have := mul_le_mul_of_nonneg_left h9 hK
      linarith
  have hsum := List.sum_le_length_nsmul
    (cs.map fun p => (if p.2 then (1 : ℝ) / 4 else 1) * (K * p.1.W A L)) (K * r.W A L / 4) (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact hb p hp)
  have hn' : ((cs.length : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hn
  simp only [List.length_map, nsmul_eq_mul] at hsum
  have h9 := nine_le_W hA hL hok hψ
  have h10 : (cs.length : ℝ) * (K * r.W A L / 4) ≤ 2 * (K * r.W A L / 4) :=
    mul_le_mul_of_nonneg_right hn' (by positivity)
  nlinarith

/-- **A giant step.** Three lists of children: charged calls and halving calls, whose `ψ` is lower
by `c₀`, with total mass at most `Cm exp(am L)` times the parent's; and continuations on overcosets,
at most `Co exp(ao lq)` of them, whose `Q` is lower by `δ lq`. The own work is at most `K`, and
this covers the oracle. The total is at most `K W / 4`. -/
theorem giant_closes {c₀ δ lq Cm am Co ao : ℝ} (hK : 0 ≤ K) (hL : 2 ≤ L) (hA : 4 ≤ A)
    (hCm : 0 ≤ Cm) (hCo : 0 ≤ Co) (hc₀ : am + 16 + Cm ≤ A * c₀) (hδ : ao + 31 + Co ≤ A * δ)
    (hlq : 1 ≤ lq) (hok : r.OK) (hψ : 1 ≤ r.psi) (ch hv ov : List Res)
    (hch : ∀ c ∈ ch, c.psi + c₀ ≤ r.psi ∧ c.rho ≤ r.rho ∧ c.Q ≤ r.Q)
    (hmc : (ch.map fun c => c.sz ^ 3).sum ≤ Cm * exp (am * L) * r.sz ^ 3)
    (hhv : ∀ c ∈ hv, c.psi + c₀ ≤ r.psi ∧ c.rho ≤ r.rho ∧ c.Q ≤ r.Q)
    (hmh : (hv.map fun c => c.sz ^ 3).sum ≤ Cm * exp (am * L) * r.sz ^ 3)
    (hov : ∀ c ∈ ov, c.s ≤ r.s ∧ c.psi ≤ r.psi ∧ c.rho ≤ r.rho ∧ c.Q + δ * lq ≤ r.Q)
    (hno : (ov.length : ℝ) ≤ Co * exp (ao * lq)) :
    K + K * (ch.map fun c => c.W A L).sum + K * (hv.map fun c => c.W A L).sum +
      K * (ov.map fun c => c.W A L).sum ≤ K * r.W A L / 4 := by
  have hA0 : 0 ≤ A := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hWpos := r.W_pos A L
  set t := A * ((c₀ + 0) * L + 0) with ht
  have htt : t = A * c₀ * L := by rw [ht]; ring
  have hsm : Cm * exp (am * L) * exp (-t) ≤ 1 / 32 := by
    have e : exp (am * L) * exp (-t) = exp (-((A * c₀ - am) * L)) := by
      rw [← exp_add, htt]; congr 1; ring
    rw [mul_assoc, e]
    refine small_const hCm ?_
    nlinarith
  have hdc : ∀ c ∈ ch, c.pot A L + t ≤ r.pot A L := fun c hc' => by
    obtain ⟨h1, h2, h3⟩ := hch c hc'
    exact pot_add_le hA0 hL0 h1 (by linarith) (by linarith)
  have hdh : ∀ c ∈ hv, c.pot A L + t ≤ r.pot A L := fun c hc' => by
    obtain ⟨h1, h2, h3⟩ := hhv c hc'
    exact pot_add_le hA0 hL0 h1 (by linarith) (by linarith)
  have hchs := sum_W_le ch hdc hmc
  have hhvs := sum_W_le hv hdh hmh
  have h1 := hchs.trans (mul_le_mul_of_nonneg_right hsm hWpos.le)
  have h2 := hhvs.trans (mul_le_mul_of_nonneg_right hsm hWpos.le)
  set t' := A * ((0 + 0) * L + δ * lq) with ht'
  have htt' : t' = A * δ * lq := by rw [ht']; ring
  have hdo : ∀ c ∈ ov, c.pot A L + t' ≤ r.pot A L := fun c hc' => by
    obtain ⟨-, h1, h2, h3⟩ := hov c hc'
    exact pot_add_le hA0 hL0 (by linarith) (by linarith) h3
  have hovs := sum_W_le (M := (ov.length : ℝ)) ov hdo
    (mass_le_length ov fun c hc' => (hov c hc').1)
  have hso : (ov.length : ℝ) * exp (-t') ≤ 1 / 32 := by
    have e : exp (ao * lq) * exp (-t') = exp (-((A * δ - ao) * lq)) := by
      rw [← exp_add, htt']; congr 1; ring
    have h3 := mul_le_mul_of_nonneg_right hno (exp_pos (-t')).le
    rw [mul_assoc, e] at h3
    refine h3.trans (small_const hCo ?_)
    nlinarith
  have h3 := hovs.trans (mul_le_mul_of_nonneg_right hso hWpos.le)
  have h9 := nine_le_W hA hL hok hψ
  have h4 : 1 + 3 / 32 * r.W A L ≤ r.W A L / 4 := by linarith
  have h5 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) hK
  have h6 := mul_le_mul_of_nonneg_left h4 hK
  nlinarith

/-- **The root bound.** With `x = log(n + 2)`: if `s ≤ exp x`, `ψ + ρ = O(x)` and `Q = O(x L)`, the
weight of the root is `exp(O(x L))`. -/
theorem root_W_le {x Cp Cq : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L) (hx : 0 ≤ x) (hs : r.sz ≤ exp x)
    (hp : r.psi + r.rho ≤ Cp * x) (hq : r.Q ≤ Cq * x * L) :
    r.W A L ≤ exp ((3 + A * (Cp + Cq)) * x * L) := by
  have h1 : r.sz ^ 3 ≤ exp (3 * x) := by
    have := pow_le_pow_left₀ r.sz_pos.le hs 3
    rwa [← exp_nat_mul, Nat.cast_ofNat] at this
  have h2 : r.pot A L ≤ A * (Cp + Cq) * x * L := by
    unfold pot
    have h3 := mul_le_mul_of_nonneg_right hp (by linarith : (0 : ℝ) ≤ L)
    have h4 := mul_le_mul_of_nonneg_left (add_le_add h3 hq) hA
    nlinarith
  have h3 : 3 * x + r.pot A L ≤ (3 + A * (Cp + Cq)) * x * L := by nlinarith
  unfold W
  calc r.sz ^ 3 * exp (r.pot A L) ≤ exp (3 * x) * exp (r.pot A L) :=
        mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ = exp (3 * x + r.pot A L) := (exp_add _ _).symm
    _ ≤ _ := exp_le_exp.2 h3

end Res

/-! ### One constant for all operations -/

/-- The conditions on `A`. Here `a` is the exponent of the general solver, `cE` that of the
primitive enumeration, `Cm, am` bound the mass of the local calls, `Co, ao` the number of
continuations, and `c₀`, `δ` are the drops of `ψ` and of `Q`. -/
structure ACond (a cE cP Cm am Co ao c₀ δ A : ℝ) : Prop where
  four : 4 ≤ A
  five : 5 ≤ A
  prod : cP + 5 ≤ A
  base : 4 * a + 1 ≤ A
  enum : 3 * cE + 18 ≤ A
  norm : 3 ≤ A * c₀
  mass : am + 16 + Cm ≤ A * c₀
  over : ao + 31 + Co ≤ A * δ

/-- **One `A` works for all operations.** -/
theorem exists_A {a cE cP Cm am Co ao c₀ δ : ℝ} (hcP : 0 ≤ cP) (hc₀ : 0 < c₀) (hδ : 0 < δ) :
    ∃ A, ACond a cE cP Cm am Co ao c₀ δ A := by
  refine ⟨max (cP + 5) (max (4 * a + 1) (max (3 * cE + 18) (max (3 / c₀) (max ((am + 16 + Cm) / c₀)
    ((ao + 31 + Co) / δ))))), ?_⟩
  set A := max (cP + 5) (max (4 * a + 1) (max (3 * cE + 18) (max (3 / c₀) (max ((am + 16 + Cm) / c₀)
    ((ao + 31 + Co) / δ))))) with hA
  have hp : cP + 5 ≤ A := le_max_left _ _
  have h5 : 5 ≤ A := by linarith
  have h1 : 4 * a + 1 ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : 3 * cE + 18 ≤ A := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h3 : 3 / c₀ ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have h4 : (am + 16 + Cm) / c₀ ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  have h6 : (ao + 31 + Co) / δ ≤ A :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  exact ⟨by linarith, h5, hp, h1, h2, (div_le_iff₀ hc₀).1 h3, (div_le_iff₀ hc₀).1 h4,
    (div_le_iff₀ hδ).1 h6⟩

end GI.Degree
