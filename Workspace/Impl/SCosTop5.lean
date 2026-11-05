module

public import Workspace.Impl.SCosTop4

@[expose] public section

/-!
# The top level, part 5 (the entry and the bridge)

`scos_top_spec`: given a solver of the problems of the recursion (function `0`) at cost
`F n`, the entry `scosTopF` (function `12`) solves `SolvableCosetIntersectionTask` at cost
`F n + scosOwnT hps X`, `X` the weight of the input. The own cost is a polynomial in `X`
(`scosOwnT_le`). `scos_solvableCosetIntersection_of` turns this into the cited statement
`GI.Cited.SolvableCosetIntersection` when `F` is polynomial, by
`polyTimeAt_ofVal_of_lang_cells`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

/-- **The own cost of the entry**, on an input of weight `X`: the steps before and after the
recursion, with the two calls of the pointwise stabilizer. -/
noncomputable def scosOwnT (hps : PointwiseStab) (X : ℕ) : ℕ :=
  10 ^ 19 * (X + 1) ^ 14 + (pointwiseStabPrim hps).boundSize (10 ^ 14 * (X + 1) ^ 6) +
    pstabK * (10 ^ 14 * (X + 1) ^ 6) ^ 9 +
    (pointwiseStabPrim hps).boundSize (10 ^ 16 * (X + 1) ^ 14)

/-- The exponent of `scosOwnT_le`. -/
noncomputable def scosTopD (hps : PointwiseStab) : ℕ := 54 + 14 * (pointwiseStabPrim hps).k

/-- The constant of `scosOwnT_le`. -/
noncomputable def scosTopK (hps : PointwiseStab) : ℕ :=
  10 ^ 19 + (pointwiseStabPrim hps).c * (10 ^ 14 + 2) ^ (pointwiseStabPrim hps).k +
    pstabK * (10 ^ 14) ^ 9 + (pointwiseStabPrim hps).c * (10 ^ 16 + 2) ^ (pointwiseStabPrim hps).k

theorem scosTop_boundSize_le (p : Prim) (A E Y : ℕ) (hY : 1 ≤ Y) :
    p.boundSize (A * Y ^ E) ≤ p.c * (A + 2) ^ p.k * Y ^ (E * p.k) := by
  unfold Prim.boundSize
  have h1 : 1 ≤ Y ^ E := Nat.one_le_pow _ _ hY
  have h2 : A * Y ^ E + 2 ≤ (A + 2) * Y ^ E := by rw [Nat.add_mul]; omega
  calc p.c * (A * Y ^ E + 2) ^ p.k ≤ p.c * ((A + 2) * Y ^ E) ^ p.k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
    _ = p.c * (A + 2) ^ p.k * Y ^ (E * p.k) := by rw [mul_pow, ← pow_mul]; ring

theorem scosTop_sum4 {a b c d A B C D Z : ℕ} (ha : a ≤ A * Z) (hb : b ≤ B * Z) (hc : c ≤ C * Z)
    (hd : d ≤ D * Z) : a + b + c + d ≤ (A + B + C + D) * Z := by
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
  omega

/-- **The own cost is polynomial.** -/
theorem scosOwnT_le (hps : PointwiseStab) (X : ℕ) :
    scosOwnT hps X ≤ scosTopK hps * (X + 1) ^ scosTopD hps := by
  have hY : 1 ≤ X + 1 := by omega
  have mono : ∀ {E : ℕ}, E ≤ scosTopD hps → (X + 1) ^ E ≤ (X + 1) ^ scosTopD hps :=
    fun h => Nat.pow_le_pow_right hY h
  have a1 := (scosTop_boundSize_le (pointwiseStabPrim hps) (10 ^ 14) 6 (X + 1) hY).trans
    (Nat.mul_le_mul_left _ (mono (E := 6 * (pointwiseStabPrim hps).k)
      (by unfold scosTopD; omega)))
  have a2 := (scosTop_boundSize_le (pointwiseStabPrim hps) (10 ^ 16) 14 (X + 1) hY).trans
    (Nat.mul_le_mul_left _ (mono (E := 14 * (pointwiseStabPrim hps).k)
      (by unfold scosTopD; omega)))
  have a0 : 10 ^ 19 * (X + 1) ^ 14 ≤ 10 ^ 19 * (X + 1) ^ scosTopD hps :=
    Nat.mul_le_mul_left _ (mono (by unfold scosTopD; omega))
  have a3 : pstabK * (10 ^ 14 * (X + 1) ^ 6) ^ 9 ≤
      pstabK * (10 ^ 14) ^ 9 * (X + 1) ^ scosTopD hps := by
    have e : pstabK * (10 ^ 14 * (X + 1) ^ 6) ^ 9 = pstabK * (10 ^ 14) ^ 9 * (X + 1) ^ 54 := by
      rw [mul_pow, ← pow_mul]; ring
    rw [e]
    exact Nat.mul_le_mul_left _ (mono (by unfold scosTopD; omega))
  unfold scosOwnT scosTopK
  exact scosTop_sum4 a0 a1 a3 a2

section Main

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

/-- `P` for short. -/
local notation "𝒫" => scosProgram c hps hpre hmb

/-- **The entry solves the task**, given a solver of the problems of the recursion at cost
`F n`. -/
theorem scos_top_spec {F : ℕ → ℕ}
    (hsolve : ∀ (n : ℕ) (v : Val) (𝒢 : Subgroup (ScosPair n)) (x : ScosPair n)
      (Φ : Finset (Fin n)),
      ScosProb n v 𝒢 x Φ → FunAll (𝒫) 0 v (fun w c' => ScosAns n w x 𝒢 Φ ∧ c' ≤ F n))
    (I : SolvCosetInst) :
    FunAll (𝒫) 12 (.list [encGroup I.gs, encGroup I.hs, encPerm I.x]) (fun w cost =>
      scosTopCorrect I.gs I.hs I.x w ∧
        cost ≤ F I.n + scosOwnT hps (Val.list [encGroup I.gs, encGroup I.hs, encPerm I.x]).wt) := by
  obtain ⟨n, gs, hsolv, hs, x⟩ := I
  dsimp only
  have hw := scosTopW_of gs hs x
  obtain ⟨X, hX⟩ : ∃ X, (Val.list [encGroup gs, encGroup hs, encPerm x]).wt = X := ⟨_, rfl⟩
  rw [hX] at hw ⊢
  have hn := hw.n_lt
  have d1 := scosTop_d1 (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs hs x hw hX
  have d2 := scosTop_d2 (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs hs x hw
  have d3 := scosTop_d3 (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs hs x hw hX
  have d4 := scosTop_d4 (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs hs x hw hX
  have wd4 := d4.wt_lt
  apply FunAll.intro (scos_top (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
  unfold scosTopF
  refine EvalAll.letE d1 fun v1 k1 h1 => ?_
  obtain ⟨rfl, hk1⟩ := h1
  refine EvalAll.letE d2 fun v2 k2 h2 => ?_
  obtain ⟨rfl, hk2⟩ := h2
  refine EvalAll.letE d3 fun v3 k3 h3 => ?_
  obtain ⟨rfl, hk3⟩ := h3
  -- The normalization: a group value of `G × H` of weight at most `scosW n`.
  have c4 : EvalAll (𝒫) [Val.list [encGroup gs, encGroup hs, encPerm x], .nat n,
      encPerm (1 : Perm (Fin n)), scosTopLv gs hs]
      (.call 117 (mk2 (mk2 (.arith .add (.var 1) (.var 1)) (.var 3)) .nil))
      (fun w c => GroupVal (n + n) w (((gens gs).prod (gens hs)).map nintSum) ∧
        w.wt ≤ scosW n ∧ c ≤ 10 ^ 14 * (X + 1) ^ 6 +
          (pointwiseStabPrim hps).boundSize (10 ^ 14 * (X + 1) ^ 6) +
          pstabK * (10 ^ 14 * (X + 1) ^ 6) ^ 9 + scosW n + 1) := by
    refine EvalAll.call_funAll d4 fun v ca h => ?_
    obtain ⟨rfl, hca⟩ := h
    refine (pstab_spec hps (scos_pstab (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
      (scos_prim0 (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
      (G := gens (scosTopGens gs hs)) ⟨_, rfl, rfl⟩ []).mono fun w c hw' => ?_
    obtain ⟨hG, hwt, hc⟩ := hw'
    rw [nint_pointwiseStab_nil, scosTop_gens] at hG
    have hwt' : w.wt ≤ scosW n := hwt
    refine ⟨hG, hwt', ?_⟩
    have b1 : (pointwiseStabPrim hps).bound
        (.list [encGroup (scosTopGens gs hs), encPts ([] : List (Fin (n + n)))]) ≤
        (pointwiseStabPrim hps).boundSize (10 ^ 14 * (X + 1) ^ 6) :=
      Prim.bound_le _ (by
        have := (Val.list [encGroup (scosTopGens gs hs),
          encPts ([] : List (Fin (n + n)))]).size_le_wt
        omega)
    have b2 : pstabK * (Val.list [encGroup (scosTopGens gs hs),
        encPts ([] : List (Fin (n + n)))]).wt ^ 9 ≤ pstabK * (10 ^ 14 * (X + 1) ^ 6) ^ 9 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left wd4.le 9)
    omega
  refine EvalAll.letE c4 fun gv k4 h4 => ?_
  obtain ⟨hG4, hgw, hk4⟩ := h4
  have d5 := scosTop_d5 (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs hs x hw hX gv
  refine EvalAll.letE d5 fun v5 k5 h5 => ?_
  obtain ⟨rfl, hk5⟩ := h5
  -- The problem of `G × H`, the pair `(x⁻¹, 1)` and all points.
  have hprob : ScosProb n (.list [gv, encPerm (nintSum (x⁻¹, 1)), scosInd Finset.univ])
      ((gens gs).prod (gens hs)) (x⁻¹, 1) Finset.univ :=
    ⟨⟨gv, rfl, hG4, hgw⟩, scosInv_univ _, by rw [scosTop_fst]; exact hsolv⟩
  have d6 := scosTop_d6 (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs hs x hw gv hgw
  have c6 : EvalAll (𝒫) [Val.list [encGroup gs, encGroup hs, encPerm x], .nat n,
      encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv, encPerm (nintSum (x⁻¹, 1))]
      (.call 0 (mk3 (.var 4) (.var 5)
        (.call 265 (mk2 (.var 1) (.call 72 (.arith .add (.var 1) (.var 1)))))))
      (fun w c => ScosAns n w (x⁻¹, 1) ((gens gs).prod (gens hs)) Finset.univ ∧
        c ≤ 10 ^ 8 * (X + 1) ^ 6 + F n + w.wt + 1) :=
    EvalAll.call_funAll d6 fun v ca h => by
      obtain ⟨rfl, hca⟩ := h
      exact (hsolve n _ _ _ _ hprob).mono fun w c hw' => ⟨hw'.1, by omega⟩
  refine EvalAll.letE c6 fun w k6 h6 => ?_
  obtain ⟨hans, hk6⟩ := h6
  have hww := scosTop_ans_wt hn hans
  refine (scosTop_tail (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs hs x hw gv w
    hans).mono fun v cv hv => ⟨hv.1, ?_⟩
  obtain ⟨-, hvw, hcv⟩ := hv
  have hW := scosW_le_X hn
  have q1 : 1 ≤ (X + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have q2 : (X + 1) ^ 6 ≤ (X + 1) ^ 14 := nint_pow_mono (by omega) (by norm_num)
  have q3 : X + 1 ≤ (X + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have q4 : (X + 1) ^ 3 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
  have q5 : (X + 1) ^ 4 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
  unfold scosTopTailT at hcv
  unfold scosOwnT
  omega

/-- The cost of the entry as one polynomial in the weight of the input. -/
theorem scosTop_cost_poly {F : ℕ → ℕ} {K D : ℕ}
    (hF : ∀ n, F n ≤ K * (n + 1) ^ D)
    (hsolve : ∀ (n : ℕ) (v : Val) (𝒢 : Subgroup (ScosPair n)) (x : ScosPair n)
      (Φ : Finset (Fin n)),
      ScosProb n v 𝒢 x Φ → FunAll (𝒫) 0 v (fun w c' => ScosAns n w x 𝒢 Φ ∧ c' ≤ F n))
    (I : SolvCosetInst) :
    FunAll (𝒫) 12 (.list [encGroup I.gs, encGroup I.hs, encPerm I.x]) (fun v cost =>
      scosTopCorrect I.gs I.hs I.x v ∧ cost ≤ (K + scosTopK hps) *
        ((Val.list [encGroup I.gs, encGroup I.hs, encPerm I.x]).wt + 1) ^ (D + scosTopD hps)) := by
  refine (scos_top_spec hsolve I).mono fun v cost h => ⟨h.1, ?_⟩
  have hn := (scosTopW_of I.gs I.hs I.x).n_lt
  have h1 := hF I.n
  have h2 := scosOwnT_le hps (Val.list [encGroup I.gs, encGroup I.hs, encPerm I.x]).wt
  have h3 := h.2
  generalize (Val.list [encGroup I.gs, encGroup I.hs, encPerm I.x]).wt = X at *
  have hY : 1 ≤ X + 1 := by omega
  have p1 : (I.n + 1) ^ D ≤ (X + 1) ^ (D + scosTopD hps) :=
    (Nat.pow_le_pow_left (by omega) D).trans (Nat.pow_le_pow_right hY (by omega))
  have p2 : (X + 1) ^ scosTopD hps ≤ (X + 1) ^ (D + scosTopD hps) :=
    Nat.pow_le_pow_right hY (by omega)
  have m1 := Nat.mul_le_mul_left K p1
  have m2 := Nat.mul_le_mul_left (scosTopK hps) p2
  rw [Nat.add_mul]
  omega

/-- **Solvable coset intersection**, from a polynomial-time solver of the recursion. -/
theorem scos_solvableCosetIntersection_of {F : ℕ → ℕ} {K D : ℕ}
    (hF : ∀ n, F n ≤ K * (n + 1) ^ D)
    (hsolve : ∀ (n : ℕ) (v : Val) (𝒢 : Subgroup (ScosPair n)) (x : ScosPair n)
      (Φ : Finset (Fin n)),
      ScosProb n v 𝒢 x Φ → FunAll (𝒫) 0 v (fun w c' => ScosAns n w x 𝒢 Φ ∧ c' ≤ F n)) :
    SolvableCosetIntersection := by
  have h := polyTimeAt_ofVal_of_lang_cells
    (enc := fun I : SolvCosetInst => Val.list [encGroup I.gs, encGroup I.hs, encPerm I.x])
    (Correct := fun I v => scosTopCorrect I.gs I.hs I.x v)
    (𝒫) 12 (K + scosTopK hps) (D + scosTopD hps) 1 1
    (fun I => nint_cells_bound (nint_cells_list (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact nint_cells_group _
      · exact nint_cells_group _
      · exact nint_cells_perm _))) (fun I => scosTop_cost_poly hF hsolve I)
  exact h

end Main

end GI.Impl
