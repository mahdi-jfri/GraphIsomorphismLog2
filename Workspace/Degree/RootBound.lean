module

public import Workspace.Degree.Calls
public import Workspace.Degree.Interface
public import Workspace.Paper.RootBounds
public import Workspace.Degree.RootState

@[expose] public section

/-!
# The bound at the root

With `x = log(k + 2)` and `y = log(D + 2)`, where `6 ≤ D ≤ k`, every term of the bound of
`calls_bound` at the root is at most `exp(c x y)`. A function with this property is `ExpB`. Sums,
products and constants keep it. The terms are: the polynomial `M` in `k`, the cost `solveB` of a
solver call on at most `D²` points, `exp(9 a L²)` with `L = y + 2 ≤ 2 y`, and the weight `W` of the
root state, by `root_W_le`. On the root state `ψ ≤ (1 + Cσ) x` by Theorem A.9
(`GI.Paper.sigma_le_log`), `ρ ≤ 4 x`, and `Q ≤ x L`, since the one interval has ratio at most `s`
and cap at most `D`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm Real

/-- `f D k ≥ 0` is at most `exp(c log(k + 2) log(D + 2))` for `6 ≤ D ≤ k`. -/
def ExpB (f : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ D k : ℕ, 6 ≤ D → D ≤ k →
    0 ≤ f D k ∧ f D k ≤ exp (c * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2))

theorem two_le_log_add_two {D : ℕ} (hD : 6 ≤ D) : 2 ≤ Real.log ((D : ℝ) + 2) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h1 := Real.exp_one_lt_d9
  have h2 : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 : (6 : ℝ) ≤ D := by exact_mod_cast hD
  have h4 : 0 < exp 1 := exp_pos 1
  nlinarith

theorem log_le_log_k {D k : ℕ} (h : D ≤ k) : Real.log ((D : ℝ) + 2) ≤ Real.log ((k : ℝ) + 2) := by
  have : (D : ℝ) ≤ k := by exact_mod_cast h
  exact Real.log_le_log (by positivity) (by linarith)

/-- The facts on `x` and `y` that every step uses. -/
theorem xy_facts {D k : ℕ} (hD : 6 ≤ D) (h : D ≤ k) :
    2 ≤ Real.log ((D : ℝ) + 2) ∧ 2 ≤ Real.log ((k : ℝ) + 2) ∧
      4 ≤ Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2) := by
  have hy := two_le_log_add_two hD
  have hx := hy.trans (log_le_log_k h)
  exact ⟨hy, hx, by nlinarith⟩

namespace ExpB

variable {f g : ℕ → ℕ → ℝ}

theorem mono (hf : ExpB f) (h : ∀ D k, 6 ≤ D → D ≤ k → 0 ≤ g D k ∧ g D k ≤ f D k) : ExpB g := by
  obtain ⟨c, hc, hf⟩ := hf
  exact ⟨c, hc, fun D k hD hk => ⟨(h D k hD hk).1, (h D k hD hk).2.trans (hf D k hD hk).2⟩⟩

theorem const {a : ℝ} (ha : 0 ≤ a) : ExpB fun _ _ => a := by
  refine ⟨Real.log (a + 1), Real.log_nonneg (by linarith), fun D k hD hk => ⟨ha, ?_⟩⟩
  obtain ⟨-, -, ht⟩ := xy_facts hD hk
  have h1 : a ≤ exp (Real.log (a + 1)) := by rw [Real.exp_log (by linarith)]; linarith
  refine h1.trans (exp_le_exp.2 ?_)
  have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ a + 1)
  rw [mul_assoc]
  nlinarith

theorem add (hf : ExpB f) (hg : ExpB g) : ExpB fun D k => f D k + g D k := by
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨c', hc', hg⟩ := hg
  refine ⟨c + c' + 1, by linarith, fun D k hD hk => ?_⟩
  obtain ⟨-, -, ht⟩ := xy_facts hD hk
  obtain ⟨h1, h2⟩ := hf D k hD hk
  obtain ⟨h3, h4⟩ := hg D k hD hk
  set t := Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)
  have e : ∀ b : ℝ, b * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2) = b * t := fun b => by
    simp only [t]; ring
  rw [e] at h2 h4 ⊢
  refine ⟨by linarith, ?_⟩
  have g1 : exp (c * t) ≤ exp ((c + c') * t) := exp_le_exp.2 (by nlinarith)
  have g2 : exp (c' * t) ≤ exp ((c + c') * t) := exp_le_exp.2 (by nlinarith)
  have g3 : (2 : ℝ) ≤ exp t := by
    have := Real.add_one_le_exp t
    linarith
  have g4 : exp ((c + c' + 1) * t) = exp ((c + c') * t) * exp t := by
    rw [← Real.exp_add]; ring_nf
  have g5 := exp_pos ((c + c') * t)
  rw [g4]
  nlinarith

theorem mul (hf : ExpB f) (hg : ExpB g) : ExpB fun D k => f D k * g D k := by
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨c', hc', hg⟩ := hg
  refine ⟨c + c', by linarith, fun D k hD hk => ?_⟩
  obtain ⟨h1, h2⟩ := hf D k hD hk
  obtain ⟨h3, h4⟩ := hg D k hD hk
  refine ⟨mul_nonneg h1 h3, ?_⟩
  have : exp ((c + c') * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) =
      exp (c * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) *
        exp (c' * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]
  exact mul_le_mul h2 h4 h3 (exp_pos _).le

/-- `exp(c x y)` itself. -/
theorem exp_xy {c : ℝ} (hc : 0 ≤ c) :
    ExpB fun D k => exp (c * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) :=
  ⟨c, hc, fun _ _ _ _ => ⟨(exp_pos _).le, le_rfl⟩⟩

/-- `exp(c y²)`, since `y ≤ x`. -/
theorem exp_yy {c : ℝ} (hc : 0 ≤ c) :
    ExpB fun D _ => exp (c * Real.log ((D : ℝ) + 2) ^ 2) := by
  refine (exp_xy hc).mono fun D k hD hk => ⟨(exp_pos _).le, exp_le_exp.2 ?_⟩
  obtain ⟨hy, -, -⟩ := xy_facts hD hk
  have := log_le_log_k hk
  have h2 : 0 ≤ c * Real.log ((D : ℝ) + 2) := by positivity
  nlinarith

/-- `(k + 2)^e`. -/
theorem pow_k (e : ℕ) : ExpB fun _ k => ((k : ℝ) + 2) ^ e := by
  refine (exp_xy (Nat.cast_nonneg e)).mono fun D k hD hk => ⟨by positivity, ?_⟩
  obtain ⟨hy, hx, -⟩ := xy_facts hD hk
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
  refine exp_le_exp.2 ?_
  have h0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have := mul_nonneg h0 (by linarith : (0 : ℝ) ≤ Real.log ((k : ℝ) + 2))
  nlinarith

end ExpB

theorem expB_budM (Cm em : ℕ) : ExpB fun _ k => (budM Cm em k : ℝ) := by
  refine ((ExpB.const (Nat.cast_nonneg Cm)).mul (ExpB.pow_k em)).mono fun D k _ _ => ?_
  unfold budM
  push_cast
  exact ⟨by positivity, le_rfl⟩

theorem expB_solveB {a : ℝ} (ha : 0 ≤ a) (Kg dg : ℕ) : ExpB fun D _ => solveB a Kg dg D := by
  have h1 := ExpB.exp_yy (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ha)
  have h2 := (ExpB.const (by positivity : (0 : ℝ) ≤ Kg * (10 ^ 5 : ℝ) ^ dg)).mul (ExpB.pow_k (12 * dg))
  refine (h1.add h2).mono fun D k hD hk => ⟨solveB_nn a Kg dg D, ?_⟩
  unfold solveB
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hDk : (D : ℝ) ≤ k := by exact_mod_cast hk
  have e1 : Real.log (((D ^ 2 : ℕ) : ℝ) + 2) ≤ 2 * Real.log ((D : ℝ) + 2) := by
    rw [← Real.log_rpow (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    push_cast
    rw [show ((D : ℝ) + 2) ^ (2 : ℝ) = ((D : ℝ) + 2) ^ (2 : ℕ) from Real.rpow_natCast _ 2]
    nlinarith
  have e2 : 0 ≤ Real.log (((D ^ 2 : ℕ) : ℝ) + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ ((D ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith)
  have e3 : exp (a * Real.log (((D ^ 2 : ℕ) : ℝ) + 2) ^ 2) ≤
      exp (4 * a * Real.log ((D : ℝ) + 2) ^ 2) := by
    refine exp_le_exp.2 ?_
    have := pow_le_pow_left₀ e2 e1 2
    nlinarith
  have e4 : (((10 ^ 4 * (D ^ 2 + 2) ^ 6 : ℕ) : ℝ) + 1) ≤ 10 ^ 5 * ((k : ℝ) + 2) ^ 12 := by
    push_cast
    have f1 : (D : ℝ) ^ 2 + 2 ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith
    have f2 := pow_le_pow_left₀ (by positivity) f1 6
    have f3 : (1 : ℝ) ≤ ((k : ℝ) + 2) ^ 12 := one_le_pow₀ (by linarith)
    rw [← pow_mul] at f2
    norm_num at f2 ⊢
    linarith
  have e5 : (((10 ^ 4 * (D ^ 2 + 2) ^ 6 : ℕ) : ℝ) + 1) ^ dg ≤
      (10 ^ 5 : ℝ) ^ dg * ((k : ℝ) + 2) ^ (12 * dg) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) e4 dg
  have e6 := mul_le_mul_of_nonneg_left e5 (Nat.cast_nonneg Kg : (0 : ℝ) ≤ Kg)
  have e7 : (Kg : ℝ) * ((10 ^ 5 : ℝ) ^ dg * ((k : ℝ) + 2) ^ (12 * dg)) =
      (Kg : ℝ) * (10 ^ 5 : ℝ) ^ dg * ((k : ℝ) + 2) ^ (12 * dg) := by ring
  linarith

/-- The constant `K` of the spine, at the root. -/
theorem expB_K (ks : Cst) (Cm em Kg dg : ℕ) :
    ExpB fun D k => ks.K (ownK Cm em ks.a Kg dg D k) (logD D) := by
  have ha := ks.a_nn
  have h1 : ExpB fun D k => ownK Cm em ks.a Kg dg D k := by
    have := ((ExpB.const (by norm_num : (0 : ℝ) ≤ 16)).mul (expB_budM Cm em)).mul
      ((ExpB.const zero_le_one).add (expB_solveB ha Kg dg))
    refine this.mono fun D k _ _ => ?_
    unfold ownK
    have := solveB_nn ks.a Kg dg D
    exact ⟨by positivity, le_rfl⟩
  have h2 := ExpB.exp_yy (mul_nonneg (by norm_num : (0 : ℝ) ≤ 36) ha)
  have hc : (0 : ℝ) ≤ 2 * exp (ks.a * Real.log ((P₀.N₀ : ℝ) + 2) ^ 2) := by positivity
  have := ((((ExpB.const (by norm_num : (0 : ℝ) ≤ 4)).mul h1).add (ExpB.const hc)).add
    ((ExpB.const (by norm_num : (0 : ℝ) ≤ 2)).mul h2)).add (ExpB.const (by norm_num : (0 : ℝ) ≤ 2))
  refine this.mono fun D k hD hk => ?_
  obtain ⟨hy, -, -⟩ := xy_facts hD hk
  obtain ⟨h0, -⟩ := (h1.choose_spec.2 D k hD hk)
  unfold Cst.K
  refine ⟨by positivity, ?_⟩
  have e1 : logD D ^ 2 ≤ 4 * Real.log ((D : ℝ) + 2) ^ 2 := by unfold logD; nlinarith
  have e2 : exp (9 * ks.a * logD D ^ 2) ≤ exp (36 * ks.a * Real.log ((D : ℝ) + 2) ^ 2) :=
    exp_le_exp.2 (by nlinarith)
  linarith

theorem log_two_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  have h : exp (1 / 2) * exp (1 / 2) = exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [exp_pos (1 / 2 : ℝ)]

theorem towerRank_toNat_le' (r : ℕ) : (GI.towerRank r).toNat ≤ 2 * Nat.log 2 r := by
  unfold GI.towerRank
  split_ifs <;> omega

/-- `ρ` of the root hierarchy is at most `4 log(s + 2)`. -/
theorem rho_root_le {Ω C : Type} [Finite Ω] (S : State Ω C) (D : ℕ) (a : S.dom) :
    ((rhoNat (rootHier S D a) : ℕ) : ℝ) ≤ 4 * Real.log ((S.size : ℝ) + 2) := by
  have hl0 : 0 ≤ Real.log ((S.size : ℝ) + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ S.size := Nat.cast_nonneg _
    linarith)
  set M := Nat.card (orb S.domGroup a)
  have hM : M ≤ S.size := Finite.card_subtype_le (fun x => x ∈ orb S.domGroup a)
  unfold rootHier freshHier
  by_cases h1 : M = 1
  · simp only [M] at h1
    simp [h1, rhoNat]
    positivity
  · simp only [M] at h1
    simp only [h1, ite_false, orbitHier, List.map_cons, List.map_nil, rhoNat, clampIv,
      List.sum_cons, List.sum_nil, add_zero]
    have h2 : ((GI.towerRank M).toNat : ℝ) ≤ 2 * (Nat.log 2 M : ℝ) := by
      have := towerRank_toNat_le' M
      exact_mod_cast this
    have h3 : ((Nat.log 2 M : ℕ) : ℝ) ≤ Real.logb 2 M := by exact_mod_cast Real.natLog_le_logb M 2
    have h4 : Real.logb 2 M ≤ 2 * Real.log ((S.size : ℝ) + 2) := by
      rcases Nat.eq_zero_or_pos M with h0 | h0
      · rw [h0]; simp; positivity
      · rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
        have hMr : (M : ℝ) ≤ (S.size : ℝ) + 2 := by
          have : (M : ℝ) ≤ S.size := by exact_mod_cast hM
          linarith
        have := Real.log_le_log (by exact_mod_cast h0) hMr
        have := log_two_gt_half
        nlinarith
    linarith

/-- **The weight of the root state.** -/
theorem expB_rootW {A : ℝ} (hA : 0 ≤ A) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {Ω C : Type} [Finite Ω] (S : State Ω C) (a : S.dom) (D k : ℕ),
      6 ≤ D → D ≤ k → S.size ≤ k →
      (rootState S D a).dres.W A (logD D) ≤
        exp (c * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) := by
  obtain ⟨Cs, hCs, hσ⟩ := GI.Paper.sigma_le_log
  refine ⟨2 * (3 + A * (1 + Cs + 4 + 1)), by positivity, fun {Ω C} _ S a D k hD hk hSk => ?_⟩
  obtain ⟨hyD, hxk, -⟩ := xy_facts hD hk
  set R := rootState S D a
  have hRs : R.size = S.size := rootState_size S D a
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hSk' : (S.size : ℝ) ≤ k := by exact_mod_cast hSk
  have hlk : Real.log ((S.size : ℝ) + 2) ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hs : R.dres.sz ≤ exp (Real.log ((k : ℝ) + 2)) := by
    rw [Real.exp_log (by positivity)]
    have : R.dres.s = S.size := hRs
    unfold Res.sz
    rw [this]
    exact max_le (by linarith) (by linarith)
  have hpsi : R.dres.psi + R.dres.rho ≤ (1 + Cs + 4) * Real.log ((k : ℝ) + 2) := by
    have hrho : R.dres.rho ≤ 4 * Real.log ((k : ℝ) + 2) :=
      (rho_root_le S D a).trans (by linarith)
    have hp : R.psi ≤ (1 + Cs) * Real.log ((k : ℝ) + 2) := by
      refine R.psi_le (by nlinarith) fun v _ => ?_
      unfold pointValue
      have : Fintype S.dom := Fintype.ofFinite _
      have hcard : Fintype.card S.dom = S.size := by
        rw [← Nat.card_eq_fintype_card]; rfl
      have e1 : ((orb R.G v).ncard : ℝ) ≤ S.size := by
        have := Set.ncard_le_card (orb R.G v)
        have h2 : Nat.card S.dom = S.size := rfl
        rw [h2] at this
        exact_mod_cast this
      have e2 : Real.log (((orb R.G v).ncard : ℝ) + 2) ≤ Real.log ((k : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have e3 := hσ P₀.κ (by norm_num [P₀]) S.dom R.G v
      rw [hcard] at e3
      have e4 : Real.log (S.size : ℝ) ≤ Real.log ((k : ℝ) + 2) := by
        rcases Nat.eq_zero_or_pos S.size with h0 | h0
        · rw [h0]; simp; positivity
        · exact Real.log_le_log (by exact_mod_cast h0) (by linarith)
      have e5 := mul_le_mul_of_nonneg_left e4 hCs
      linarith
    have : R.dres.psi = R.psi := rfl
    linarith
  have hq : R.dres.Q ≤ 1 * Real.log ((k : ℝ) + 2) * logD D := by
    show State.hierQ (rootHier S D a) ≤ _
    unfold rootHier freshHier
    by_cases h1 : Nat.card (orb S.domGroup a) = 1
    · simp only [h1, ite_true, List.map_nil, State.hierQ, List.sum_nil]
      have := logD_ge D
      positivity
    · simp only [h1, ite_false, orbitHier, List.map_cons, List.map_nil, State.hierQ, clampIv,
        List.sum_cons, List.sum_nil, add_zero]
      set M := Nat.card (orb S.domGroup a)
      have hM : M ≤ S.size := Finite.card_subtype_le (fun x => x ∈ orb S.domGroup a)
      have hMr : (M : ℝ) ≤ (k : ℝ) + 2 := by
        have : (M : ℝ) ≤ S.size := by exact_mod_cast hM
        linarith
      have f1 : Real.log (M : ℝ) ≤ Real.log ((k : ℝ) + 2) := by
        rcases Nat.eq_zero_or_pos M with h0 | h0
        · rw [h0]; simp; positivity
        · exact Real.log_le_log (by exact_mod_cast h0) hMr
      have f0 : 0 ≤ Real.log (M : ℝ) := Real.log_natCast_nonneg M
      have f2 : Real.log ((max (min M D) 2 : ℕ) : ℝ) ≤ logD D := by
        have g1 : ((max (min M D) 2 : ℕ) : ℝ) ≤ (D : ℝ) + 2 := by
          have : max (min M D) 2 ≤ D + 2 := max_le (by omega) (by omega)
          exact_mod_cast this
        have g2 := Real.log_le_log (by
          have : 0 < max (min M D) 2 := by omega
          exact_mod_cast this) g1
        unfold logD
        linarith
      have f3 : 0 ≤ Real.log ((max (min M D) 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
      have := mul_le_mul f1 f2 f3 (by linarith)
      linarith
  have h := Res.root_W_le hA (by have := logD_ge D; linarith) (by linarith) hs hpsi hq
  refine h.trans (exp_le_exp.2 ?_)
  have hL : logD D ≤ 2 * Real.log ((D : ℝ) + 2) := by unfold logD; linarith
  have hc : 0 ≤ (3 + A * (1 + Cs + 4 + 1)) * Real.log ((k : ℝ) + 2) := by positivity
  have := mul_le_mul_of_nonneg_left hL hc
  nlinarith

/-- **The bound at the root.** -/
theorem root_bound (ks : Cst) (Cm em Kg dg : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {Ω C : Type} [Finite Ω] (S : State Ω C) (a : S.dom) (D k : ℕ),
      6 ≤ D → D ≤ k → S.size ≤ k →
      ks.bound (ks.K (ownK Cm em ks.a Kg dg D k) (logD D)) (logD D)
          ⟨S.dom, C, rootState S D a, false⟩ ≤
        exp (c * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) := by
  obtain ⟨c₁, hc₁, h₁⟩ := expB_K ks Cm em Kg dg
  obtain ⟨c₂, hc₂, h₂⟩ := expB_rootW ks.A_nn
  refine ⟨c₁ + c₂, by linarith, fun {Ω C} _ S a D k hD hk hSk => ?_⟩
  obtain ⟨hK0, hK⟩ := h₁ D k hD hk
  have hW := h₂ S a D k hD hk hSk
  have hW0 := (rootState S D a).dres.W_pos ks.A (logD D)
  show ks.K _ _ * (rootState S D a).dres.W ks.A (logD D) ≤ _
  have : exp ((c₁ + c₂) * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) =
      exp (c₁ * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) *
        exp (c₂ * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]
  exact mul_le_mul hK hW hW0.le (exp_pos _).le

end GI.Degree
