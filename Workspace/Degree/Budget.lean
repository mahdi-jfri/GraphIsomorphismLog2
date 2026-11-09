module

public import Workspace.Degree.OpsAll
public import Workspace.Impl.GenNormPoly
public import Workspace.Assembly.GenReq
public import Workspace.Impl.AggSpecReq

@[expose] public section

/-!
# The budgets

`budgets` gives one polynomial `M n = C (n + 2)^e` that pays the own work of every node, for all
`D ≤ n`, where `n` is the root's bound `Nm` for `N`. The constants depend on the primitives only.
A round also pays its calls to the general solver, by the factor `1 + solveB` (`GiantBudget`).

The tool is `pbu_le`: a uniformly polynomial `f k W B` is at most `C (n + 2)^e (B + 1)^p` when
`k ≤ n` and `W` is at most a polynomial in `n`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm Real
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership GroupOrder MinimalBlocks)

/-- `f` is at most a polynomial in `n`. -/
def PolyN (f : ℕ → ℕ) : Prop := ∃ C e : ℕ, ∀ n, f n ≤ C * (n + 2) ^ e

theorem PolyN.of_pbu {f : ℕ → ℕ} (h : PBU fun n _ _ => f n) : PolyN f := by
  obtain ⟨C, D, h⟩ := h
  exact ⟨C, D, fun n => by simpa [PB] using h n 0 0⟩

/-- **The bound of a uniformly polynomial function** on `k ≤ n` and `W ≤ G n`. -/
theorem pbu_le {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) {G : ℕ → ℕ} (hG : PolyN G) :
    ∃ C e p : ℕ, ∀ n k W B, k ≤ n → W ≤ G n → f k W B ≤ C * (n + 2) ^ e * (B + 1) ^ p := by
  obtain ⟨C, D, hf⟩ := hf
  obtain ⟨Cg, eg, hG⟩ := hG
  refine ⟨C * (Cg + 1) ^ D, (eg + 1) * D, D, fun n k W B hk hW => ?_⟩
  have h1 := hf k W B
  unfold PB at h1
  have hn1 : 1 ≤ n + 2 := by omega
  have hpow : (n + 2) ≤ (n + 2) ^ (eg + 1) := Nat.le_self_pow (by omega) _
  have hpow' : (n + 2) ^ eg ≤ (n + 2) ^ (eg + 1) := Nat.pow_le_pow_right hn1 (by omega)
  have h2 : W + B + k + 2 ≤ (Cg + 1) * (n + 2) ^ (eg + 1) * (B + 1) := by
    have := hG n
    have e1 : Cg * (n + 2) ^ eg ≤ Cg * (n + 2) ^ (eg + 1) := Nat.mul_le_mul_left _ hpow'
    nlinarith
  calc f k W B ≤ C * (W + B + k + 2) ^ D := h1
    _ ≤ C * ((Cg + 1) * (n + 2) ^ (eg + 1) * (B + 1)) ^ D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 D)
    _ = C * (Cg + 1) ^ D * (n + 2) ^ ((eg + 1) * D) * (B + 1) ^ D := by
        rw [mul_pow, mul_pow, ← pow_mul]; ring

/-- A smaller bound inside a larger one. -/
theorem dom_le {C C' e e' p p' n B : ℕ} (hC : C ≤ C') (he : e ≤ e') (hp : p ≤ p') :
    C * (n + 2) ^ e * (B + 1) ^ p ≤ C' * (n + 2) ^ e' * (B + 1) ^ p' := by
  have h1 : (n + 2) ^ e ≤ (n + 2) ^ e' := Nat.pow_le_pow_right (by omega) he
  have h2 : (B + 1) ^ p ≤ (B + 1) ^ p' := Nat.pow_le_pow_right (by omega) hp
  exact Nat.mul_le_mul (Nat.mul_le_mul hC h1) h2

theorem polyN_W₀ : PolyN fun n => 10 ^ 4 * (n + 2) ^ 6 := ⟨10 ^ 4, 6, fun _ => le_rfl⟩

/-- The weight bound of a branch input, as a function of `n`. -/
noncomputable def wbN (hmb : MinimalBlocks) (n : ℕ) : ℕ :=
  30 * (10 ^ 4 * (n + 2) ^ 6 + gsX hmb (10 ^ 4 * (n + 2) ^ 6) + gsWc n + n ^ 2 + 10) + 100

theorem wb_eq (X : Ctx) (hmb : MinimalBlocks) : X.WB hmb = wbN hmb X.Nm := rfl

theorem polyN_wb (hmb : MinimalBlocks) : PolyN (wbN hmb) := by
  refine PolyN.of_pbu ?_
  have h1 : PBU fun n _ _ => gsX hmb (10 ^ 4 * (n + 2) ^ 6) :=
    normPoly_subst (gsX_poly hmb) PBU.k (by norm_poly) PBU.B
  have h2 : PBU fun n _ _ => gsWc n := by unfold gsWc; norm_poly
  unfold wbN
  exact PBU.addc (PBU.smul 30 (PBU.addc (PBU.add (PBU.add (PBU.add (by norm_poly) h1) h2)
    (by norm_poly)) 10)) 100

/-- The weight bound of a round input, as a function of `n`. -/
def wgN (n : ℕ) : ℕ := 2 * (10 ^ 4 * (n + 2) ^ 6 + labWStd n n) + 6

theorem polyN_wg : PolyN wgN := by
  refine PolyN.of_pbu ?_
  unfold wgN labWStd
  norm_poly

theorem le_M {C e p n B Cm em : ℕ} (hB : B ≤ n) (hC : C ≤ Cm) (he : e + p ≤ em) :
    C * (n + 2) ^ e * (B + 1) ^ p ≤ Cm * (n + 2) ^ em := by
  have h1 : (B + 1) ^ p ≤ (n + 2) ^ p := Nat.pow_le_pow_left (by omega) p
  have h2 : (n + 2) ^ e * (n + 2) ^ p ≤ (n + 2) ^ em := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) he
  calc C * (n + 2) ^ e * (B + 1) ^ p ≤ C * (n + 2) ^ e * (n + 2) ^ p := Nat.mul_le_mul_left _ h1
    _ = C * ((n + 2) ^ e * (n + 2) ^ p) := by ring
    _ ≤ Cm * (n + 2) ^ em := Nat.mul_le_mul hC h2

/-- The polynomial of the budgets. -/
def budM (Cm em n : ℕ) : ℕ := Cm * (n + 2) ^ em

set_option maxHeartbeats 4000000 in
/-- **The budgets.** One polynomial `M = budM Cm em Nm` pays the own work of every node, for all
`D ≤ Nm`. -/
theorem budgets (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    (hmb : MinimalBlocks) (hO : GroupOrder) (h : JohnsonRecognition) (hp : Preimage)
    (hm : Membership) (E Kg dg : ℕ) {Xw : ℕ → ℕ} (hXw : PBU fun _ W _ => Xw W) :
    ∃ Cm em p : ℕ, 1 ≤ p ∧ 1 ≤ Cm ∧ ∀ X : Ctx, X.D ≤ X.Nm →
      ContBudget X hst hpre hfac Kg dg (4 * (budM Cm em X.Nm : ℝ)) ∧
      TransBudget X hmb hO h hp hst hm E Kg dg p (4 * (budM Cm em X.Nm : ℝ)) ∧
      ∀ a : ℝ, GiantBudget X hpre hfac hm (abKrC hst) Xw a Kg dg
        (4 * (budM Cm em X.Nm : ℝ) * (1 + solveB a Kg dg X.D)) := by
  -- the bounds of the parts
  have wb := polyN_wb hmb
  obtain ⟨C1, e1, p1, b1⟩ := pbu_le (enumCost_poly hp hm) wb
  have hpr : PBU fun k W B => 2 * prodCost hp hm k W B + 2 * W + 4 * k ^ 2 + 200 :=
    PBU.addc (PBU.add (PBU.add (PBU.smul 2 (prodCost_poly hp hm)) (PBU.smul 2 PBU.W))
      (by norm_poly)) 200
  obtain ⟨C2, e2, p2, b2⟩ := pbu_le hpr wb
  obtain ⟨C3, e3, b3⟩ : PolyN fun n => (groupOrderPrim hO).c *
      (10 ^ 4 * (n + 2) ^ 6 + 2) ^ (groupOrderPrim hO).k := PolyN.of_pbu (by norm_poly)
  obtain ⟨C4, e4, p4, b4⟩ := pbu_le (G := fun n => n) (f := fun k _ _ => (groupOrderPrim hO).c *
      (groupW k + 2) ^ (groupOrderPrim hO).k) (by unfold groupW; norm_poly) ⟨1, 1, fun n => by
        simp⟩
  obtain ⟨C5, e5, p5, b5⟩ := pbu_le (normStepCost_poly hp hst hm) wb
  obtain ⟨C6, e6, p6, b6⟩ := pbu_le (G := fun n => 10 ^ 4 * (n + 2) ^ 6)
    (f := fun _ W _ => Kg * (W + 1) ^ dg) (by norm_poly) polyN_W₀
  obtain ⟨C7, e7, p7, b7⟩ := pbu_le (f := fun k W B => gateOwn W k B) (by unfold gateOwn; norm_poly)
    wb
  obtain ⟨C8, e8, p8, b8⟩ := pbu_le (f := fun k W _ => 3 * (ansW k + 1) + (100 * W + 100 + ansW k))
    (by unfold ansW groupW; norm_poly) wb
  obtain ⟨C9, e9, p9, b9⟩ := pbu_le (G := fun n => 10 ^ 4 * (n + 2) ^ 6)
    (f := fun k W B => transOwn hmb hO h E B k W + 8 * (ansW k + 2))
    (by unfold transOwn degTestC gsX gsWc ansW groupW; norm_poly) polyN_W₀
  obtain ⟨C10, e10, p10, b10⟩ := pbu_le (G := fun n => 10 ^ 4 * (n + 2) ^ 6)
    (f := fun k W B => contPart k B W + Kg * (W + 1) ^ dg)
    (by unfold contPart contOwn rhoC rhoStepC ansW groupW; norm_poly) polyN_W₀
  obtain ⟨C11, e11, p11, b11⟩ := pbu_le (G := fun n => n)
    (f := fun k W _ => orbK * (10 ^ 4 * (k + 2) ^ 6 + ansW W + 1) ^ 15)
    (by unfold ansW groupW; norm_poly) ⟨1, 1, fun n => by simp⟩
  obtain ⟨C12, e12, p12, b12⟩ := pbu_le (G := fun n => 10 ^ 4 * (n + 2) ^ 6)
    (f := fun k W B => contPart k B W + resetOwn (pointwiseStabPrim hst) (preimagePrim hpre)
      (normalizedFactorPrim hfac) (W + 1))
    (by unfold contPart contOwn rhoC rhoStepC ansW groupW resetOwn prepCost liftCost resetY intC
        norm_poly) polyN_W₀
  obtain ⟨C13, e13, p13, b13⟩ := pbu_le (asOwn_poly hst hpre hfac hm hXw) polyN_wg
  -- one polynomial for all
  obtain ⟨Cm, hCm⟩ : ∃ Cm, Cm = 1 + C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 +
    C12 + C13 := ⟨_, rfl⟩
  obtain ⟨em, hem⟩ : ∃ em, em = 36000 + (e1 + p1) + (e2 + p2) + e3 + (e4 + p4) + (e5 + p5) +
    (e6 + p6) + (e7 + p7) + (e8 + p8) + (e9 + p9) + (e10 + p10) + (e11 + p11) + (e12 + p12) +
    (e13 + p13) := ⟨_, rfl⟩
  obtain ⟨p, hp'⟩ : ∃ p, p = 1 + p1 + p2 := ⟨_, rfl⟩
  refine ⟨Cm, em, p, by omega, by omega, fun X hDn => ?_⟩
  set n := X.Nm with hn
  have hW₀ : X.W₀ = 10 ^ 4 * (n + 2) ^ 6 := rfl
  have hWB : X.WB hmb = wbN hmb n := rfl
  have hWG : X.WG = wgN n := rfl
  have hM0 : 0 ≤ (budM Cm em n : ℝ) := Nat.cast_nonneg _
  -- a bound without `B`
  have fin0 : ∀ {C e q B : ℕ}, B ≤ n → C ≤ Cm → e + q ≤ em →
      C * (n + 2) ^ e * (B + 1) ^ q ≤ budM Cm em n := fun hB hC he => le_M hB hC he
  refine ⟨⟨?_, ?_, ?_⟩, ⟨by positivity, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun a => ⟨?_, ?_⟩⟩
  -- `contD`
  · intro k N W hk hN hW
    have h1 := b10 n k W N hk hW
    have h2 := fin0 (C := C10) (e := e10) (q := p10) hN (by omega) (by omega)
    have h3 : contPart k N W + Kg * (W + 1) ^ dg ≤ 4 * budM Cm em n := by
      have := h1.trans h2; omega
    exact_mod_cast h3
  · intro k N W hk hN hW
    have h1 := b10 n k W N hk hW
    have h2 := fin0 (C := C10) (e := e10) (q := p10) hN (by omega) (by omega)
    have h3 := b11 n n k 0 le_rfl hk
    have h4 := fin0 (C := C11) (e := e11) (q := p11) (Nat.zero_le n) (by omega) (by omega)
    have h5 : contPart k N W + orbK * (X.W₀ + ansW k + 1) ^ 15 ≤ 4 * budM Cm em n := by
      rw [hW₀]
      have := h1.trans h2
      have := h3.trans h4
      omega
    exact_mod_cast h5
  · intro k N W hk hN hW
    have h1 := b12 n k W N hk hW
    have h2 := fin0 (C := C12) (e := e12) (q := p12) hN (by omega) (by omega)
    have h3 : contPart k N W + resetOwn (pointwiseStabPrim hst) (preimagePrim hpre)
        (normalizedFactorPrim hfac) (W + 1) ≤ 4 * budM Cm em n := by
      have := h1.trans h2; omega
    exact_mod_cast h3
  -- `transD`
  · intro k W B hk hW
    have h1 := b1 n k W B hk (hWB ▸ hW)
    have h2 : C1 * (n + 2) ^ e1 * (B + 1) ^ p1 ≤ Cm * (n + 2) ^ em * (B + 1) ^ p :=
      dom_le (by omega) (by omega) (by omega)
    have h3 : enumCost hp hm k W B ≤ 4 * budM Cm em n * (B + 1) ^ p := by
      have : enumCost hp hm k W B ≤ budM Cm em n * (B + 1) ^ p := h1.trans h2
      have h4 : budM Cm em n * (B + 1) ^ p ≤ 4 * budM Cm em n * (B + 1) ^ p :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    exact_mod_cast h3
  · intro k W B gv Kv hk hW hgv hKv
    have h1 := b2 n k W B hk (hWB ▸ hW)
    have h2 : C2 * (n + 2) ^ e2 * (B + 1) ^ p2 ≤ budM Cm em n * (B + 1) ^ p :=
      dom_le (by omega) (by omega) (by omega)
    have g1 := mb_bound_le (groupOrderPrim hO) (hgv.trans hW₀.le)
    have g2 : (groupOrderPrim hO).c * (10 ^ 4 * (n + 2) ^ 6 + 2) ^ (groupOrderPrim hO).k ≤
        budM Cm em n := by
      have := fin0 (C := C3) (e := e3) (q := 0) (Nat.zero_le n) (by omega) (by omega)
      simp only [pow_zero, mul_one] at this
      exact (b3 n).trans this
    have g3 := mb_bound_le (groupOrderPrim hO) hKv
    have g4 := (b4 n k 0 0 hk (Nat.zero_le _)).trans
      (fin0 (C := C4) (e := e4) (q := p4) (Nat.zero_le n) (by omega) (by omega))
    have hB1 : 1 ≤ (B + 1) ^ p := Nat.one_le_pow _ _ (by omega)
    have h3 : prodCostD hO hp hm k W B gv Kv ≤ 4 * budM Cm em n * (B + 1) ^ p := by
      have h5 := h1.trans h2
      have hb1 : budM Cm em n ≤ budM Cm em n * (B + 1) ^ p := Nat.le_mul_of_pos_right _ hB1
      have hb4 : 4 * budM Cm em n * (B + 1) ^ p = 4 * (budM Cm em n * (B + 1) ^ p) := by ring
      have hb5 : 4 * budM Cm em n = 4 * budM Cm em n := rfl
      unfold prodCostD
      rw [hb4]
      omega
    exact_mod_cast h3
  · intro n' m W hn' hm' hW
    have h1 := b5 n n' W m hn' (hWB ▸ hW)
    have h2 := fin0 (C := C5) (e := e5) (q := p5) (hm'.trans hDn) (by omega) (by omega)
    have h3 : normStepCost hp hst hm n' m W ≤ 4 * budM Cm em n := by
      have := h1.trans h2; omega
    exact_mod_cast h3
  · intro W hW
    have h1 := b6 n 0 W 0 (Nat.zero_le _) (hW₀ ▸ hW)
    have h2 := fin0 (C := C6) (e := e6) (q := p6) (Nat.zero_le n) (by omega) (by omega)
    have h3 : Kg * (W + 1) ^ dg ≤ 4 * budM Cm em n := by
      have := h1.trans h2; omega
    have h4 : ((Kg * (W + 1) ^ dg : ℕ) : ℝ) ≤ ((4 * budM Cm em n : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at h4
    exact h4
  · intro k W N m hk hW hN hm'
    have h1 := b7 n N W m hN (hWB ▸ hW)
    have h2 := fin0 (C := C7) (e := e7) (q := p7) (hm'.trans hDn) (by omega) (by omega)
    have h3 := b8 n k W 0 hk (hWB ▸ hW)
    have h4 := fin0 (C := C8) (e := e8) (q := p8) (Nat.zero_le n) (by omega) (by omega)
    have h5 : gateOwn W N m + 3 * (ansW k + 1) ≤ 4 * budM Cm em n := by
      have := h1.trans h2
      have := h3.trans h4
      omega
    exact_mod_cast h5
  · intro k W hk hW
    have h3 := b8 n k W 0 hk (hWB ▸ hW)
    have h4 := fin0 (C := C8) (e := e8) (q := p8) (Nat.zero_le n) (by omega) (by omega)
    have h5 : 100 * W + 100 + ansW k ≤ 4 * budM Cm em n := by
      have := h3.trans h4
      omega
    exact_mod_cast h5
  · intro k W hk hW
    have h1 := b9 n k W X.D hk (hW₀ ▸ hW)
    have h2 := fin0 (C := C9) (e := e9) (q := p9) hDn (by omega) (by omega)
    have h3 : transOwn hmb hO h E X.D k W + 8 * (ansW k + 2) ≤ 4 * budM Cm em n := by
      have := h1.trans h2; omega
    exact_mod_cast h3
  -- `giantD`
  · intro k W hk hW
    have h1 := b13 n k W 0 hk (hWG ▸ hW)
    have h2 := fin0 (C := C13) (e := e13) (q := p13) (Nat.zero_le n) (by omega) (by omega)
    have h3 : asOwn hpre hfac hm (abKrC hst) Xw k W ≤ 4 * budM Cm em n := by
      have := h1.trans h2; omega
    have h4 : ((asOwn hpre hfac hm (abKrC hst) Xw k W : ℕ) : ℝ) ≤ ((4 * budM Cm em n : ℕ) : ℝ) := by
      exact_mod_cast h3
    have hs := solveB_nn a Kg dg X.D
    push_cast at h4
    generalize solveB a Kg dg X.D = y at hs ⊢
    generalize (budM Cm em n : ℝ) = M at h4 hM0 ⊢
    generalize ((asOwn hpre hfac hm (abKrC hst) Xw k W : ℕ) : ℝ) = A at h4 ⊢
    nlinarith
  · intro N hN
    have ha : P₀.a = ((36000 : ℕ) : ℝ) := by norm_num [P₀]
    rw [ha, Real.rpow_natCast]
    have h1 : N ^ 36000 ≤ budM Cm em n := by
      have e1 : N ^ 36000 ≤ (n + 2) ^ 36000 := Nat.pow_le_pow_left (by omega) _
      have e2 : (n + 2) ^ 36000 ≤ (n + 2) ^ em := Nat.pow_le_pow_right (by omega) (by omega)
      have e3 : (n + 2) ^ em ≤ Cm * (n + 2) ^ em := Nat.le_mul_of_pos_left _ (by omega)
      exact e1.trans (e2.trans e3)
    have h2 : (N : ℝ) ^ 36000 ≤ (budM Cm em n : ℝ) := by
      have := Nat.cast_le (α := ℝ) |>.mpr h1
      rwa [Nat.cast_pow] at this
    have hs := solveB_nn a Kg dg X.D
    have e1 := mul_le_mul_of_nonneg_right h2 hs
    have e2 := mul_nonneg hM0 hs
    have e3 : (budM Cm em n : ℝ) * solveB a Kg dg X.D ≤
        4 * (budM Cm em n : ℝ) * (1 + solveB a Kg dg X.D) := by
      have : 4 * (budM Cm em n : ℝ) * (1 + solveB a Kg dg X.D) =
          4 * (budM Cm em n : ℝ) + 4 * ((budM Cm em n : ℝ) * solveB a Kg dg X.D) := by ring
      rw [this]; linarith
    exact e1.trans e3

end GI.Degree
