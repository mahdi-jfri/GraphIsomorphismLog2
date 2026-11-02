import Workspace.Impl.SCosBase6

/-!
# The base case `Φ = {α}` (function 4)

`scos_base_spec`: on a problem `v` with `Φ = {α}`, every run of `scosBaseF` returns a correct
answer at cost at most `scosOwnB hps n`, a polynomial in `n` (`scosOwnB_le`).

The body is a chain of seven steps (`Impl/SCosBase2.lean` to `SCosBase6.lean`). All costs are
bounded through `M = 10⁵ (n + 1)⁶`, which bounds the weight of the input and of the answer, and
`S = 10¹⁶ M⁶`, which bounds the cost and the weight of the Schreier transversal.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The weight bound `M` of the base case. -/
def scosBaseM (n : ℕ) : ℕ := 10 ^ 5 * (n + 1) ^ 6

/-- **The own cost of the base case.** -/
noncomputable def scosOwnB (hps : PointwiseStab) (n : ℕ) : ℕ :=
  10 ^ 6 * scosBaseS (scosBaseM n) ^ 2 + (pointwiseStabPrim hps).boundSize (30 * scosBaseM n)

/-- `(n + n + 1)^k ≤ 2^k (n + 1)^k`. -/
theorem scosBase_pow_le (k : ℕ) : (n + n + 1) ^ k ≤ 2 ^ k * (n + 1) ^ k := by
  rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) k

/-- The weight facts of `M`. -/
theorem scosBaseM_facts (n : ℕ) :
    n + n + 1 ≤ scosBaseM n ∧ 320 * (n + n + 1) ^ 6 ≤ scosBaseM n ∧
      2 * (4 * (n + n + 1) ^ 2 + 320 * (n + n + 1) ^ 6) + 6 ≤ scosBaseM n ∧
      2 * (320 * (n + n + 1) ^ 6 + 4 * (n + n + 1) ^ 2 + ((n + n) * 7 + 4)) + 7 ≤
        scosBaseM n := by
  have h6 := scosBase_pow_le (n := n) 6
  have h2 := scosBase_pow_le (n := n) 2
  have q1 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have q2 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  unfold scosBaseM
  norm_num at h6 h2
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The input weighs at most `M`. -/
theorem scosBase_wtV (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n)
    (hg : (encGroup gs).wt ≤ scosW n) : (scosBaseV gs x a).wt ≤ scosBaseM n := by
  have w1 := wt_list3_le (encGroup gs) (encPerm (nintSum x)) (scosInd ({a} : Finset (Fin n)))
  have w2 := wt_encPerm_le (nintSum x)
  have w3 : (scosInd ({a} : Finset (Fin n))).wt ≤ (n + n) * (2 * 1 + 5) + 4 :=
    wt_encFun_le _ (indF_le_one _ _)
  have := (scosBaseM_facts n).2.2.2
  unfold scosW at hg
  have e : (scosBaseV gs x a).wt = (Val.list [encGroup gs, encPerm (nintSum x),
    scosInd ({a} : Finset (Fin n))]).wt := rfl
  omega

/-- An answer weighs at most `M`. -/
theorem scosBase_ans_wt {w : Val} {x : ScosPair n} {𝒢 : Subgroup (ScosPair n)}
    {Φ : Finset (Fin n)} (h : ScosAns n w x 𝒢 Φ) : w.wt ≤ scosBaseM n := by
  have hf := (scosBaseM_facts n).2.2.1
  rcases h with ⟨rfl, -⟩ | ⟨z, -, lv, rfl, -, hlv⟩
  · have : (Val.list []).wt ≤ 4 := (wt_list_le []).trans (by simp)
    omega
  · have w1 := wt_list2_le (encPerm (nintSum z)) lv
    have w2 := wt_encPerm_le (nintSum z)
    unfold scosW at hlv
    omega

/-- The facts of `S`. -/
theorem scosBaseS_facts (M : ℕ) (hM : 1 ≤ M) :
    M ≤ scosBaseS M ∧ M ^ 2 ≤ scosBaseS M ∧ M ^ 3 ≤ scosBaseS M ∧ M ^ 4 ≤ scosBaseS M ∧
      scosBaseS M ≤ scosBaseS M ^ 2 ∧ pstabK * (30 * M) ^ 9 ≤ scosBaseS M ^ 2 := by
  have p1 : M ≤ M ^ 6 := Nat.le_self_pow (by norm_num) M
  have p2 : M ^ 2 ≤ M ^ 6 := Nat.pow_le_pow_right hM (by norm_num)
  have p3 : M ^ 3 ≤ M ^ 6 := Nat.pow_le_pow_right hM (by norm_num)
  have p4 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right hM (by norm_num)
  have p9 : M ^ 9 ≤ M ^ 12 := Nat.pow_le_pow_right hM (by norm_num)
  have e1 : scosBaseS M ^ 2 = 10 ^ 32 * M ^ 12 := by unfold scosBaseS; ring
  have e2 : pstabK * (30 * M) ^ 9 = 19683000000000000000 * M ^ 9 := by
    simp only [pstabK]; ring
  have hS1 : 1 ≤ scosBaseS M := by
    unfold scosBaseS; have := Nat.one_le_pow 6 M hM; omega
  refine ⟨?_, ?_, ?_, ?_, Nat.le_self_pow (by norm_num) _, ?_⟩
  · unfold scosBaseS; omega
  · unfold scosBaseS; omega
  · unfold scosBaseS; omega
  · unfold scosBaseS; omega
  · rw [e1, e2]; omega

/-- The final sum of the costs. -/
theorem scosBase_total {M S k1 k2 k3 k4 k5 k6 k7 ww bS : ℕ} (hMS : M ≤ S) (hM3 : M ^ 3 ≤ S)
    (hM4 : M ^ 4 ≤ S) (hSS : S ≤ S ^ 2) (hP : pstabK * (30 * M) ^ 9 ≤ S ^ 2) (hM1 : 1 ≤ M)
    (h1 : k1 ≤ 200000 * M ^ 3) (h2 : k2 ≤ 30 * M) (h3 : k3 ≤ 10 * M) (h4 : k4 ≤ 300000 * M ^ 4)
    (h5 : k5 ≤ S) (h6 : k6 ≤ 100000 * S ^ 2)
    (h7 : k7 ≤ 200000 * S + (bS + pstabK * (30 * M) ^ 9 + 100 * M)) (hw : ww ≤ M) :
    k1 + (k2 + (k3 + (k4 + (k5 + (k6 + k7 + ww + 1) + ww + 1) + ww + 1) + ww + 1) + ww + 1) +
      ww + 1 ≤ 10 ^ 6 * S ^ 2 + bS := by
  omega

section Main

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-- **The base case** (function 4, `Φ = {α}`): a correct answer at cost at most
`scosOwnB hps n`. -/
theorem scos_base_spec {v : Val} {𝒢 : Subgroup (ScosPair n)} {x : ScosPair n}
    {Φ : Finset (Fin n)} (hv : ScosProb n v 𝒢 x Φ) (h1 : Φ.card = 1) :
    FunAll (𝒫) 4 v (fun w cost => ScosAns n w x 𝒢 Φ ∧ cost ≤ scosOwnB hps n) := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
  have hinv := hv.inv
  obtain ⟨gv, rfl, ⟨gs, rfl, hgs⟩, hgw⟩ := hv.val
  obtain ⟨hN, hW6, -, -⟩ := scosBaseM_facts n
  have hM := scosBase_wtV gs x a hgw
  have hM1 : 1 ≤ scosBaseM n := by omega
  obtain ⟨hMS, hM2, hM3, hM4, hSS, hP⟩ := scosBaseS_facts (scosBaseM n) hM1
  unfold scosOwnB
  apply FunAll.intro scos_base
  refine EvalAll.letE (scosBase_d1 gs x a hM hN) fun v1 k1 h1 => ?_
  obtain ⟨rfl, hk1⟩ := h1
  refine EvalAll.letE (scosBase_d2 gs x a hM hN) fun v2 k2 h2 => ?_
  obtain ⟨rfl, hk2⟩ := h2
  refine EvalAll.letE (scosBase_d3 gs x a hN) fun v3 k3 h3 => ?_
  obtain ⟨rfl, hk3⟩ := h3
  refine EvalAll.letE (scosBase_d4 gs x a hM hN) fun v4 k4 h4 => ?_
  obtain ⟨rfl, hk4⟩ := h4
  refine EvalAll.letE (scosBase_e5 gs x a hM hN) fun v5 k5 h5 => ?_
  obtain ⟨L, rfl, -, hL2, hL3, hk5, hLw⟩ := h5
  refine EvalAll.letE (scosBase_d6 gs x a L hN hLw hM2) fun v6 k6 h6 => ?_
  obtain ⟨rfl, hk6⟩ := h6
  refine (scosBase_e7 gs x a hinv hgs L hL2 hL3 hM hN hW6 hLw hM3).mono fun w k7 hw => ?_
  obtain ⟨hans, hk7⟩ := hw
  refine ⟨hans, ?_⟩
  have hww := scosBase_ans_wt hans
  unfold scosBaseT7 scosBaseP at hk7
  exact scosBase_total hMS hM3 hM4 hSS hP hM1 hk1 hk2 hk3 hk4 hk5 hk6 hk7 hww

end Main

/-- **The own cost is a polynomial**: `scosOwnB hps n ≤ K (n + 1)^D` with `K` and `D` depending
only on the constants `c`, `k` of the pointwise-stabilizer primitive. -/
theorem scosOwnB_le (hps : PointwiseStab) (n : ℕ) :
    scosOwnB hps n ≤ (10 ^ 6 * (10 ^ 16 * (10 ^ 5) ^ 6) ^ 2 +
      (pointwiseStabPrim hps).c * (3000002 : ℕ) ^ (pointwiseStabPrim hps).k) *
      (n + 1) ^ (72 + 6 * (pointwiseStabPrim hps).k) := by
  set pc := (pointwiseStabPrim hps).c
  set pk := (pointwiseStabPrim hps).k
  have hY : 1 ≤ n + 1 := by omega
  -- the first term
  have e1 : 10 ^ 6 * scosBaseS (scosBaseM n) ^ 2 =
      10 ^ 6 * (10 ^ 16 * (10 ^ 5) ^ 6) ^ 2 * (n + 1) ^ 72 := by
    unfold scosBaseS scosBaseM; ring
  have t1 : (n + 1) ^ 72 ≤ (n + 1) ^ (72 + 6 * pk) := Nat.pow_le_pow_right hY (by omega)
  -- the second term
  have hb : 30 * scosBaseM n + 2 ≤ 3000002 * (n + 1) ^ 6 := by
    have := Nat.one_le_pow 6 (n + 1) hY
    unfold scosBaseM; omega
  have t2 : (pointwiseStabPrim hps).boundSize (30 * scosBaseM n) ≤
      pc * (3000002 : ℕ) ^ pk * (n + 1) ^ (72 + 6 * pk) := by
    unfold Prim.boundSize
    calc pc * (30 * scosBaseM n + 2) ^ pk ≤ pc * (3000002 * (n + 1) ^ 6) ^ pk :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
      _ = pc * 3000002 ^ pk * (n + 1) ^ (6 * pk) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ pc * 3000002 ^ pk * (n + 1) ^ (72 + 6 * pk) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY (by omega))
  unfold scosOwnB
  rw [e1, add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ t1) t2

end GI.Impl
