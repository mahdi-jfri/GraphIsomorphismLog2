import Workspace.Lang.Lib.Loop
import Workspace.Machine.Len

/-!
# Steps 4–5 of `camProg`: reading `m` and `k`

The program reads `m` from the order `t = m!/2` of one simple factor, and `k` from the size
`s = binom(m, k)` of one of its orbits. Both are searches of the same shape: walk `j = j₀, j₀ + 1,
…` along an increasing sequence `a j` and stop at the first `j` with `a j = t`.

`advFuns b f` (three functions) is this walk. Its argument is `[c, t, K, [j₀, a j₀]]`; for `K`
rounds it replaces `[j, v]` by `[j + 1, f [c, j, v]]` while `v < t`, and keeps it otherwise
(`adv_spec`). The user function `f` computes `a (j + 1)` from `a j`. Since every value before the
stop is below `t`, the numbers stay small.

* `camMFuns`: on `[t, n]`, the least `m ≥ 2` with `m!/2 = t` (`a j = j!/2`, `a (j+1) = a j (j+1)`).
* `camKFuns`: on `[m, s]`, the least `k` with `binom(m, k) = s` (`a (j+1) = a j (m - j)/(j + 1)`).
-/

namespace GI.Lang

open GI.Machine (BinOp len len_mono len_mul_le len_le_self)
open GI.Cited (Val)

/-! ### The walk -/

/-- The step on `[[c, t, K, acc0], i, [j, v]]`: `[j + 1, f [c, j, v]]` if `v < t`, else `[j, v]`. -/
def advStep (f : ℕ) : Expr :=
  .ite (.arith .lt (.get (arg 2) (.nat 1)) (.get (arg 0) (.nat 1)))
    (mk2 (.arith .add (.get (arg 2) (.nat 0)) (.nat 1))
      (.call f (mk3 (.get (arg 0) (.nat 0)) (.get (arg 2) (.nat 0)) (.get (arg 2) (.nat 1)))))
    (arg 2)

/-- The walk, at base `b` (three functions), with step function `f`. -/
def advFuns (b f : ℕ) : List Expr :=
  loopFuns b (.get (.var 0) (.nat 2)) (.get (.var 0) (.nat 3)) (advStep f)

/-- The accumulator after `i` rounds. -/
def advAcc (a : ℕ → ℕ) (j0 js i : ℕ) : Val := .list [.nat (min (j0 + i) js), .nat (a (min (j0 + i) js))]

theorem wt_nat_mono {x y : ℕ} (h : x ≤ y) : (Val.nat x).wt ≤ (Val.nat y).wt := by
  rw [wt_nat, wt_nat]; have := len_mono h; omega

/-- One round of the walk. -/
theorem advStep_det {P : Program} {f : ℕ} {c : Val} {t K j0 js B : ℕ} {a : ℕ → ℕ}
    (hj : j0 ≤ js) (ht : a js = t) (hlt : ∀ j, j0 ≤ j → j < js → a j < t)
    (hf : ∀ j, j0 ≤ j → j < js → FunDet P f (.list [c, .nat j, .nat (a j)]) (.nat (a (j + 1))) B)
    (i : ℕ) :
    Det P [.list [.list [c, .nat t, .nat K, advAcc a j0 js 0], .nat i, advAcc a j0 js i]]
      (advStep f) (advAcc a j0 js (i + 1))
      (B + 100 * ((Val.list [.list [c, .nat t, .nat K, advAcc a j0 js 0], .nat i,
        advAcc a j0 js i]).wt + 2 * (Val.nat js).wt + 2 * (Val.nat t).wt + 10)) := by
  set A := Val.list [c, .nat t, .nat K, advAcc a j0 js 0] with hA
  set j := min (j0 + i) js with hjdef
  set Z := Val.list [A, .nat i, advAcc a j0 js i] with hZ
  have hacc : advAcc a j0 js i = .list [.nat j, .nat (a j)] := rfl
  have dAc := Det.arg' (P := P) (vs := [A, .nat i, advAcc a j0 js i]) (rest := []) (j := 2) rfl
  have dA := Det.arg' (P := P) (vs := [A, .nat i, advAcc a j0 js i]) (rest := []) (j := 0) rfl
  rw [hacc] at dAc
  have dJ := Det.get' dAc (Det.nat 0) (show [Val.nat j, .nat (a j)][0]? = some (.nat j) from rfl)
  have dV := Det.get' dAc (Det.nat 1) (show [Val.nat j, .nat (a j)][1]? = some (.nat (a j)) from rfl)
  have dT := Det.get' dA (Det.nat 1)
    (show [c, Val.nat t, .nat K, advAcc a j0 js 0][1]? = some (.nat t) from rfl)
  have dC := Det.get' dA (Det.nat 0)
    (show [c, Val.nat t, .nat K, advAcc a j0 js 0][0]? = some c from rfl)
  have dTest := Det.arith (op := .lt) dV dT
  have hwZ : (advAcc a j0 js i).wt < Z.wt := wt_le_wt_list (by simp)
  have hwA : A.wt < Z.wt := wt_le_wt_list (by simp)
  have hwc : c.wt < A.wt := wt_le_wt_list (by simp)
  have hwt : (Val.nat t).wt < A.wt := wt_le_wt_list (by simp)
  have hjv : (Val.list [Val.nat j, .nat (a j)]).wt = (advAcc a j0 js i).wt := rfl
  have wj : (Val.nat j).wt < (advAcc a j0 js i).wt := by
    rw [← hjv]; exact wt_le_wt_list (by simp)
  have wv : (Val.nat (a j)).wt < (advAcc a j0 js i).wt := by
    rw [← hjv]; exact wt_le_wt_list (by simp)
  have wlt : ∀ y z, (Val.nat (BinOp.eval .lt y z)).wt ≤ 3 := fun y z => by
    simp only [BinOp.eval]; split <;> decide
  have w1 := wlt (a j) t
  have hz1 : (Val.list [A, .nat i, .list [.nat j, .nat (a j)]]).wt = Z.wt := rfl
  have hz2 : (Val.list [A, .nat i, advAcc a j0 js i]).wt = Z.wt := rfl
  have hn1 : (Val.nat 1).wt = 3 := by rw [wt_nat]; rfl
  have hn0 : (Val.nat 0).wt = 2 := by rw [wt_nat]; rfl
  by_cases hjs : j < js
  · -- `a j < t`: advance
    have hj0 : j0 ≤ j := by omega
    have hji : j = j0 + i := by omega
    have hv := hlt j hj0 hjs
    have hnext : advAcc a j0 js (i + 1) = .list [.nat (j + 1), .nat (a (j + 1))] := by
      simp only [advAcc]
      have : min (j0 + (i + 1)) js = j + 1 := by omega
      rw [this]
    have hx : BinOp.eval .lt (a j) t = 1 := by simp [BinOp.eval, hv]
    rw [hx] at dTest
    have dCall := Det.call (Det.mk3 dC dJ dV) (hf j hj0 hjs)
    have dAdd := Det.arith (op := .add) dJ (Det.nat 1)
    rw [show BinOp.eval .add j 1 = j + 1 from rfl] at dAdd
    have dNew := Det.mk2 dAdd dCall
    rw [hnext]
    refine (Det.ite_pos dTest one_ne_zero dNew).mono ?_
    have hw3 := wt_list3_le c (.nat j) (.nat (a j))
    have hw2 := wt_list2_le (.nat (j + 1)) (.nat (a (j + 1)))
    have hj1 : (Val.nat (j + 1)).wt ≤ (Val.nat js).wt := wt_nat_mono hjs
    have haj : a (j + 1) ≤ t := by
      rcases Nat.lt_or_ge (j + 1) js with h1 | h1
      · exact (hlt _ (by omega) h1).le
      · rw [show j + 1 = js by omega, ht]
    have ha1 : (Val.nat (a (j + 1))).wt ≤ (Val.nat t).wt := wt_nat_mono haj
    have hjn := wt_nat_le j
    have hj1n := wt_nat_le (j + 1)
    clear dCall dNew dTest dC dT dV dJ dA dAc
    omega
  · -- `j = js`: keep
    have hjj : j = js := by omega
    have hnext : advAcc a j0 js (i + 1) = advAcc a j0 js i := by
      simp only [advAcc]
      have h1 : min (j0 + (i + 1)) js = js := by omega
      have h2 : min (j0 + i) js = js := by omega
      rw [h1, h2]
    have hx : BinOp.eval .lt (a j) t = 0 := by simp [BinOp.eval, hjj, ht]
    rw [hx] at dTest
    have dAc' := Det.arg' (P := P) (vs := [A, .nat i, advAcc a j0 js i]) (rest := []) (j := 2) rfl
    rw [hnext]
    refine (Det.ite_zero dTest dAc').mono ?_
    clear dTest dC dT dV dJ dA dAc dAc'
    omega

/-- The weight of an accumulator. -/
theorem wt_advAcc_le {a : ℕ → ℕ} {j0 js t : ℕ} (ht : a js = t) (hlt : ∀ j, j0 ≤ j → j < js → a j < t)
    (hj : j0 ≤ js) (i : ℕ) :
    (advAcc a j0 js i).wt ≤ 2 * ((Val.nat js).wt + (Val.nat t).wt) + 6 := by
  have h1 : min (j0 + i) js ≤ js := min_le_right _ _
  have h2 : a (min (j0 + i) js) ≤ t := by
    rcases Nat.lt_or_ge (min (j0 + i) js) js with h | h
    · exact (hlt _ (by omega) h).le
    · rw [show min (j0 + i) js = js by omega, ht]
  have := wt_list2_le (.nat (min (j0 + i) js)) (.nat (a (min (j0 + i) js)))
  have := wt_nat_mono h1
  have := wt_nat_mono h2
  simp only [advAcc]
  omega

/-- **The walk.** After `K ≥ js - j₀` rounds from `[j₀, a j₀]`, the accumulator is `[js, t]`. -/
theorem adv_spec {P : Program} {b f : ℕ} (h : P.HasAt b (advFuns b f)) {c : Val}
    {t K j0 js B : ℕ} {a : ℕ → ℕ}
    (hj : j0 ≤ js) (hK : js ≤ j0 + K) (ht : a js = t) (hlt : ∀ j, j0 ≤ j → j < js → a j < t)
    (hf : ∀ j, j0 ≤ j → j < js → FunDet P f (.list [c, .nat j, .nat (a j)]) (.nat (a (j + 1))) B) :
    FunDet P b (.list [c, .nat t, .nat K, .list [.nat j0, .nat (a j0)]]) (.list [.nat js, .nat t])
      ((K + 1) * (B + 2000 * ((Val.list [c, .nat t, .nat K, .list [.nat j0, .nat (a j0)]]).wt +
        K + 2 * (Val.nat js).wt + 2 * (Val.nat t).wt + 12))) := by
  have h0 : advAcc a j0 js 0 = .list [.nat j0, .nat (a j0)] := by
    simp only [advAcc, Nat.add_zero, min_eq_left hj]
  rw [← h0]
  set A := Val.list [c, .nat t, .nat K, advAcc a j0 js 0] with hA
  have hk : Det P [A] (.get (.var 0) (.nat 2)) (.nat K) _ :=
    Det.get' (Det.var' (P := P) (env := [A]) (i := 0) rfl) (Det.nat 2) rfl
  have hacc : Det P [A] (.get (.var 0) (.nat 3)) (advAcc a j0 js 0) _ :=
    Det.get' (Det.var' (P := P) (env := [A]) (i := 0) rfl) (Det.nat 3) rfl
  have hwK : (Val.nat K).wt < A.wt := wt_le_wt_list (by simp)
  have hwa0 : (advAcc a j0 js 0).wt < A.wt := wt_le_wt_list (by simp)
  have hKw := wt_nat_le K
  have hAo : (Val.list [c, .nat t, .nat K, advAcc a j0 js 0]).wt = A.wt := rfl
  set M := 2 * ((Val.nat js).wt + (Val.nat t).wt) + 6 with hM
  refine (loopBdd_spec h hk hacc ?_ (M := M) (Inv := fun i acc => acc = advAcc a j0 js i)
    (D := fun _ => B + 100 * (2 * (A.wt + K + M) + 11 + 2 * (Val.nat js).wt +
      2 * (Val.nat t).wt + 10)) rfl
    (fun i acc _ h => h ▸ wt_advAcc_le ht hlt hj i) ?_).mono ?_
  · omega
  · rintro i acc hi rfl
    refine (advStep_det hj ht hlt hf i).post fun cc hc => ⟨rfl, ?_⟩
    have h1 := wt_stepArg_le (Val.list [c, .nat t, .nat K, advAcc a j0 js 0]) i (advAcc a j0 js i)
    have h2 := wt_advAcc_le ht hlt hj i
    have : i ≤ K := hi.le
    beta_reduce
    clear_value M A
    clear hk hacc h hf
    omega
  · rintro w cc ⟨rfl, hc⟩
    refine ⟨?_, hc.trans ?_⟩
    · simp only [advAcc, ht, show min (j0 + K) js = js by omega]
    · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, loopModK]
      set X := A.wt + K + 2 * (Val.nat js).wt + 2 * (Val.nat t).wt + 12 with hX
      have hD : B + 100 * (2 * (A.wt + K + M) + 11 + 2 * (Val.nat js).wt +
          2 * (Val.nat t).wt + 10) ≤ B + 600 * X := by omega
      have e2 := Nat.mul_le_mul_left K hD
      have e3 : 1000 * (K + 1) * (A.wt + K + M + 1) ≤ 1000 * (K + 1) * X :=
        Nat.mul_le_mul_left _ (by omega)
      have e4 : K * (B + 600 * X) = K * B + 600 * (K * X) := by ring
      have e5 : 1000 * (K + 1) * X = 1000 * (K * X) + 1000 * X := by ring
      have e6 : (K + 1) * (B + 2000 * X) = K * B + B + 2000 * (K * X) + 2000 * X := by ring
      rw [e6]
      rw [e4] at e2
      rw [e5] at e3
      clear_value X M A
      clear hk hacc h hf
      generalize K * X = KX at *
      generalize K * B = KB at *
      generalize K * (B + 100 * (2 * (A.wt + K + M) + 11 + 2 * (Val.nat js).wt +
          2 * (Val.nat t).wt + 10)) = KD at *
      clear hc e5 e6 hD
      generalize 1000 * (K + 1) * (A.wt + K + M + 1) = Q at *
      omega

/-! ### Strictly increasing sequences -/

theorem cam_lt_of_step {a : ℕ → ℕ} {j0 js : ℕ} (h : ∀ j, j0 ≤ j → j < js → a j < a (j + 1)) :
    ∀ j, j0 ≤ j → j < js → a j < a js := by
  induction js with
  | zero => intro j _ hj; omega
  | succ js ih =>
    intro j hj0 hj
    have hs := h js (by omega) (by omega)
    rcases Nat.lt_or_ge j js with hlt | hge
    · exact (ih (fun i h1 h2 => h i h1 (by omega)) j hj0 hlt).trans hs
    · rw [show j = js by omega]; exact hs

/-! ### `m` from `m!/2` -/

/-- The step of the factorial walk: on `[c, j, v]`, `v (j + 1)`. -/
def camMStep : Expr := .arith .mul (arg 2) (.arith .add (arg 1) (.nat 1))

/-- The entry: on `[t, n]`, the walk from `[2, 1]` for `n` rounds, then its first entry. -/
def camMEntry (adv : ℕ) : Expr :=
  .get (.call adv (mk4 (.nat 0) (arg 0) (arg 1) (mk2 (.nat 2) (.nat 1)))) (.nat 0)

/-- **Reading `m`**, at base `b` (five functions). -/
def camMFuns (b : ℕ) : List Expr := [camMEntry (b + 1)] ++ advFuns (b + 1) (b + 4) ++ [camMStep]

theorem cam_half_fact_succ {j : ℕ} (hj : 2 ≤ j) : (j + 1).factorial / 2 = j.factorial / 2 * (j + 1) := by
  obtain ⟨q, hq⟩ := Nat.dvd_factorial (by norm_num : 0 < 2) hj
  rw [Nat.factorial_succ, hq]
  have e : (j + 1) * (2 * q) = 2 * (q * (j + 1)) := by ring
  rw [e, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]

theorem cam_half_fact_lt {j : ℕ} (hj : 2 ≤ j) : j.factorial / 2 < (j + 1).factorial / 2 := by
  rw [cam_half_fact_succ hj]
  have : 0 < j.factorial / 2 := by
    have := Nat.self_le_factorial j
    have : 2 ≤ j.factorial := le_trans hj this
    omega
  calc j.factorial / 2 = j.factorial / 2 * 1 := by ring
    _ < j.factorial / 2 * (j + 1) := Nat.mul_lt_mul_of_pos_left (by omega) this

theorem wt_nat_mul_le (x y : ℕ) : (Val.nat (x * y)).wt ≤ (Val.nat x).wt + (Val.nat y).wt := by
  rw [wt_nat, wt_nat, wt_nat]; have := len_mul_le x y; omega

theorem camMStep_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some camMStep) (c : Val) (j v : ℕ) :
    FunDet P f (.list [c, .nat j, .nat v]) (.nat (v * (j + 1)))
      (10 * ((Val.list [c, .nat j, .nat v]).wt + 10)) := by
  have dV := Det.arg' (P := P) (vs := [c, .nat j, .nat v]) (rest := []) (j := 2) rfl
  have dJ := Det.arg' (P := P) (vs := [c, .nat j, .nat v]) (rest := []) (j := 1) rfl
  have dA := Det.arith (op := .add) dJ (Det.nat 1)
  rw [show BinOp.eval .add j 1 = j + 1 from rfl] at dA
  have dM := Det.arith (op := .mul) dV dA
  rw [show BinOp.eval .mul v (j + 1) = v * (j + 1) from rfl] at dM
  refine FunDet.intro hf (dM.mono ?_)
  have h1 := wt_nat_mul_le v (j + 1)
  have hj : (Val.nat j).wt < (Val.list [c, .nat j, .nat v]).wt := wt_le_wt_list (by simp)
  have hv : (Val.nat v).wt < (Val.list [c, .nat j, .nat v]).wt := wt_le_wt_list (by simp)
  have h2 : (Val.nat (j + 1)).wt ≤ (Val.nat j).wt + 1 := by
    rw [wt_nat, wt_nat]; have := GI.Machine.len_succ_le j; omega
  have h3 : (Val.nat 1).wt = 3 := by rw [wt_nat]; rfl
  omega

/-- The constant of the two searches. -/
def camSearchK : ℕ := 100000

/-- **Reading `m` from `m!/2`.** On `[m!/2, n]` with `2 ≤ m ≤ n + 2`, the result is `m`. -/
theorem camM_spec {P : Program} {b : ℕ} (h : P.HasAt b (camMFuns b)) {m n : ℕ} (hm : 2 ≤ m)
    (hmn : m ≤ n + 2) :
    FunDet P b (.list [.nat (m.factorial / 2), .nat n]) (.nat m)
      (camSearchK * ((Val.list [.nat (m.factorial / 2), .nat n]).wt + n + 10) ^ 2) := by
  simp only [camMFuns] at h
  have hentry : P.funs[b]? = some (camMEntry (b + 1)) := h.left.left.single
  have hadv : P.HasAt (b + 1) (advFuns (b + 1) (b + 4)) := h.left.right
  have hstep : P.funs[b + 4]? = some camMStep := by
    have := h.right.single; simpa [advFuns, loopFuns, Nat.add_assoc] using this
  obtain ⟨t, htd⟩ : ∃ t, m.factorial / 2 = t := ⟨_, rfl⟩
  rw [htd]
  have hsum := sum_wt_lt_wt_list [.nat t, .nat n]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  set x := Val.list [.nat t, .nat n] with hx
  have hlt0 := cam_lt_of_step (a := fun j => j.factorial / 2) (j0 := 2) (js := m)
    (fun j hj _ => cam_half_fact_lt hj)
  have hlt : ∀ j, 2 ≤ j → j < m → j.factorial / 2 < t := by
    intro j h1 h2
    have := hlt0 j h1 h2
    beta_reduce at this
    omega
  have hle : ∀ j, 2 ≤ j → j < m → (j + 1).factorial / 2 ≤ t := by
    intro j hj hjm
    rcases Nat.lt_or_ge (j + 1) m with h1 | h1
    · exact (hlt _ (by omega) h1).le
    · rw [show j + 1 = m by omega, htd]
  have hwt : (Val.nat t).wt < x.wt := wt_le_wt_list (by simp)
  have hwn : (Val.nat n).wt < x.wt := wt_le_wt_list (by simp)
  set B := 10 * (2 * ((Val.nat 0).wt + (Val.nat (n + 2)).wt + (Val.nat t).wt) + 17) with hB
  have hf : ∀ j, 2 ≤ j → j < m → FunDet P (b + 4)
      (.list [.nat 0, .nat j, .nat (j.factorial / 2)]) (.nat ((j + 1).factorial / 2)) B := by
    intro j hj hjm
    rw [cam_half_fact_succ hj]
    refine (camMStep_det hstep _ j _).mono ?_
    have := wt_list3_le (.nat 0) (.nat j) (.nat (j.factorial / 2))
    have := wt_nat_mono (show j ≤ n + 2 by omega)
    have := wt_nat_mono (hlt j hj hjm).le
    omega
  have hw := adv_spec (c := .nat 0) (t := t) (K := n) (a := fun j => j.factorial / 2) hadv hm
    (by omega) htd hlt hf
  have h21 : (Nat.factorial 2) / 2 = 1 := by simp [Nat.factorial]
  beta_reduce at hw
  rw [h21] at hw
  have dX := Det.var' (P := P) (env := [x]) (i := 0) rfl
  have d0 := Det.get' dX (Det.nat 0) (show [Val.nat t, .nat n][0]? = some (.nat t) from rfl)
  have d1 := Det.get' dX (Det.nat 1) (show [Val.nat t, .nat n][1]? = some (.nat n) from rfl)
  have dArg := Det.mk4 (Det.nat (P := P) (env := [x]) 0) d0 d1 (Det.mk2 (Det.nat 2) (Det.nat 1))
  have dCall := Det.call dArg hw
  have dRes := Det.get' dCall (Det.nat 0) (show [Val.nat m, .nat t][0]? = some (.nat m) from rfl)
  refine FunDet.intro hentry (dRes.mono ?_)
  clear dRes dCall dArg d0 d1 dX hw hf h hentry hadv hstep h21 hlt0 hlt hle htd
  have w4 := wt_list4_le (.nat 0) (.nat t) (.nat n) (.list [.nat 2, .nat 1])
  have w21 := wt_list2_le (.nat 2) (.nat 1)
  have w2l := wt_list2_le (.nat m) (.nat t)
  have wm := wt_nat_mono hmn
  have wn2 : (Val.nat (n + 2)).wt ≤ (Val.nat n).wt + 3 := by
    rw [wt_nat, wt_nat]; have := GI.Machine.len_add_le n 2
    have : len 2 = 2 := rfl
    have : len n ≤ max (len n) (len 2) := le_max_left _ _
    have : max (len n) (len 2) ≤ len n + 2 := max_le (by omega) (by omega)
    omega
  have hc0 : (Val.nat 0).wt = 2 := by rw [wt_nat]; rfl
  have hc1 : (Val.nat 1).wt = 3 := by rw [wt_nat]; rfl
  have hc2 : (Val.nat 2).wt = 4 := by rw [wt_nat]; rfl
  have hg2 : 2 ≤ (Val.nat t).wt := by rw [wt_nat]; omega
  have hh2 : 2 ≤ (Val.nat n).wt := by rw [wt_nat]; omega
  have hxw := x.two_le_size
  have hxs := x.size_le_wt
  set Y := x.wt + n + 10 with hY
  set Z := (Val.list [Val.nat 0, Val.nat t, Val.nat n, Val.list [Val.nat 2, Val.nat 1]]).wt
  have hZ : Z ≤ 4 * Y := by omega
  have hX : Z + n + 2 * (Val.nat m).wt + 2 * (Val.nat t).wt + 12 ≤ 10 * Y := by omega
  have hBY : B ≤ 40 * Y := by omega
  have e1 : (n + 1) * (B + 2000 * (Z + n + 2 * (Val.nat m).wt + 2 * (Val.nat t).wt + 12)) ≤
      Y * (40 * Y + 2000 * (10 * Y)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e2 : Y * (40 * Y + 2000 * (10 * Y)) = 20040 * Y ^ 2 := by ring
  have hYY : 10 * Y ≤ Y ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right Y (by omega)
  simp only [camSearchK]
  rw [e2] at e1
  clear_value Y Z B x
  generalize Y ^ 2 = Q at *
  obtain ⟨R, hR⟩ : ∃ R, (n + 1) * (B + 2000 * (Z + n + 2 * (Val.nat m).wt + 2 * (Val.nat t).wt + 12))
    = R := ⟨_, rfl⟩
  rw [hR] at e1 ⊢
  omega

/-! ### `k` from `binom(m, k)` -/

/-- The step of the binomial walk: on `[m, j, v]`, `v (m - j) / (j + 1)`. -/
def camKStep : Expr :=
  .arith .div (.arith .mul (arg 2) (.arith .sub (arg 0) (arg 1))) (.arith .add (arg 1) (.nat 1))

/-- The entry: on `[m, s]`, the walk from `[0, 1]` for `m` rounds, then its first entry. -/
def camKEntry (adv : ℕ) : Expr :=
  .get (.call adv (mk4 (arg 0) (arg 1) (arg 0) (mk2 (.nat 0) (.nat 1)))) (.nat 0)

/-- **Reading `k`**, at base `b` (five functions). -/
def camKFuns (b : ℕ) : List Expr := [camKEntry (b + 1)] ++ advFuns (b + 1) (b + 4) ++ [camKStep]

theorem cam_choose_succ (m j : ℕ) : m.choose (j + 1) = m.choose j * (m - j) / (j + 1) := by
  rw [← Nat.choose_succ_right_eq, Nat.mul_div_cancel _ (by omega)]

theorem cam_choose_lt {m j : ℕ} (hj : 2 * j + 2 < m + 1) : m.choose j < m.choose (j + 1) := by
  have e := Nat.choose_succ_right_eq m j
  have hpos : 0 < m.choose j := Nat.choose_pos (by omega)
  by_contra hc
  have h1 : m.choose (j + 1) * (j + 1) ≤ m.choose j * (j + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : m.choose j * (j + 1) < m.choose j * (m - j) := Nat.mul_lt_mul_of_pos_left (by omega) hpos
  omega

theorem camKStep_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some camKStep) (m j v : ℕ) :
    FunDet P f (.list [.nat m, .nat j, .nat v]) (.nat (v * (m - j) / (j + 1)))
      (20 * ((Val.list [.nat m, .nat j, .nat v]).wt + (Val.nat (v * (m - j))).wt + 10)) := by
  have dV := Det.arg' (P := P) (vs := [.nat m, .nat j, .nat v]) (rest := []) (j := 2) rfl
  have dJ := Det.arg' (P := P) (vs := [.nat m, .nat j, .nat v]) (rest := []) (j := 1) rfl
  have dM := Det.arg' (P := P) (vs := [.nat m, .nat j, .nat v]) (rest := []) (j := 0) rfl
  have dS := Det.arith (op := .sub) dM dJ
  rw [show BinOp.eval .sub m j = m - j from rfl] at dS
  have dP := Det.arith (op := .mul) dV dS
  rw [show BinOp.eval .mul v (m - j) = v * (m - j) from rfl] at dP
  have dA := Det.arith (op := .add) dJ (Det.nat 1)
  rw [show BinOp.eval .add j 1 = j + 1 from rfl] at dA
  have dD := Det.arith (op := .div) dP dA
  rw [show BinOp.eval .div (v * (m - j)) (j + 1) = v * (m - j) / (j + 1) from rfl] at dD
  refine FunDet.intro hf (dD.mono ?_)
  have hj : (Val.nat j).wt < (Val.list [.nat m, .nat j, .nat v]).wt := wt_le_wt_list (by simp)
  have hm : (Val.nat m).wt < (Val.list [.nat m, .nat j, .nat v]).wt := wt_le_wt_list (by simp)
  have h2 : (Val.nat (j + 1)).wt ≤ (Val.nat j).wt + 1 := by
    rw [wt_nat, wt_nat]; have := GI.Machine.len_succ_le j; omega
  have h3 : (Val.nat 1).wt = 3 := by rw [wt_nat]; rfl
  have h4 := wt_nat_mono (Nat.sub_le m j)
  have h5 := wt_nat_mono (Nat.div_le_self (v * (m - j)) (j + 1))
  omega

/-- **Reading `k` from `binom(m, k)`.** On `[m, binom(m, k)]` with `2k < m`, the result is `k`. -/
theorem camK_spec {P : Program} {b : ℕ} (h : P.HasAt b (camKFuns b)) {m k : ℕ} (hk : 2 * k < m) :
    FunDet P b (.list [.nat m, .nat (m.choose k)]) (.nat k)
      (camSearchK * ((Val.list [.nat m, .nat (m.choose k)]).wt + m + 10) ^ 2) := by
  simp only [camKFuns] at h
  have hentry : P.funs[b]? = some (camKEntry (b + 1)) := h.left.left.single
  have hadv : P.HasAt (b + 1) (advFuns (b + 1) (b + 4)) := h.left.right
  have hstep : P.funs[b + 4]? = some camKStep := by
    have := h.right.single; simpa [advFuns, loopFuns, Nat.add_assoc] using this
  set s := m.choose k with hsd
  have hsum := sum_wt_lt_wt_list [.nat m, .nat s]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  set x := Val.list [.nat m, .nat s] with hx
  have hlt : ∀ j, 0 ≤ j → j < k → m.choose j < s :=
    cam_lt_of_step (a := fun j => m.choose j) (fun j _ hj => cam_choose_lt (by omega))
  have hwm : (Val.nat m).wt < x.wt := wt_le_wt_list (by simp)
  have hws : (Val.nat s).wt < x.wt := wt_le_wt_list (by simp)
  set B := 20 * (2 * (2 * (Val.nat m).wt + (Val.nat s).wt) + 7 + (Val.nat m).wt + (Val.nat s).wt
    + 10) with hB
  have hf : ∀ j, 0 ≤ j → j < k → FunDet P (b + 4)
      (.list [.nat m, .nat j, .nat (m.choose j)]) (.nat (m.choose (j + 1))) B := by
    intro j _ hjk
    rw [cam_choose_succ]
    refine (camKStep_det hstep m j _).mono ?_
    have := wt_list3_le (.nat m) (.nat j) (.nat (m.choose j))
    have := wt_nat_mono (show j ≤ m by omega)
    have := wt_nat_mono (hlt j (by omega) hjk).le
    have := wt_nat_mul_le (m.choose j) (m - j)
    have := wt_nat_mono (Nat.sub_le m j)
    omega
  have hw := adv_spec (c := .nat m) (t := s) (K := m) (a := fun j => m.choose j) hadv
    (Nat.zero_le k) (by omega) rfl hlt hf
  simp only [Nat.choose_zero_right] at hw
  have dX := Det.var' (P := P) (env := [x]) (i := 0) rfl
  have d0 := Det.get' dX (Det.nat 0) (show [Val.nat m, .nat s][0]? = some (.nat m) from rfl)
  have d1 := Det.get' dX (Det.nat 1) (show [Val.nat m, .nat s][1]? = some (.nat s) from rfl)
  have dArg := Det.mk4 d0 d1 d0 (Det.mk2 (Det.nat (P := P) (env := [x]) 0) (Det.nat 1))
  have dCall := Det.call dArg hw
  have dRes := Det.get' dCall (Det.nat 0) (show [Val.nat k, .nat s][0]? = some (.nat k) from rfl)
  refine FunDet.intro hentry (dRes.mono ?_)
  clear dRes dCall dArg d0 d1 dX hw hf h hentry hadv hstep
  have w4 := wt_list4_le (.nat m) (.nat s) (.nat m) (.list [.nat 0, .nat 1])
  have w21 := wt_list2_le (.nat 0) (.nat 1)
  have w2l := wt_list2_le (.nat k) (.nat s)
  have wk := wt_nat_mono (show k ≤ m by omega)
  have hc0 : (Val.nat 0).wt = 2 := by rw [wt_nat]; rfl
  have hc1 : (Val.nat 1).wt = 3 := by rw [wt_nat]; rfl
  have hxw := x.two_le_size
  have hxs := x.size_le_wt
  have hmw := wt_nat_le m
  have hg2 : 2 ≤ (Val.nat s).wt := by rw [wt_nat]; omega
  have hh2 : 2 ≤ (Val.nat m).wt := by rw [wt_nat]; omega
  set Y := x.wt + m + 10 with hY
  set Z := (Val.list [Val.nat m, Val.nat s, Val.nat m, Val.list [Val.nat 0, Val.nat 1]]).wt
  have hZ : Z ≤ 5 * Y := by omega
  have hX : Z + m + 2 * (Val.nat k).wt + 2 * (Val.nat s).wt + 12 ≤ 12 * Y := by omega
  have hBY : B ≤ 200 * Y := by omega
  have e1 : (m + 1) * (B + 2000 * (Z + m + 2 * (Val.nat k).wt + 2 * (Val.nat s).wt + 12)) ≤
      Y * (200 * Y + 2000 * (12 * Y)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e2 : Y * (200 * Y + 2000 * (12 * Y)) = 24200 * Y ^ 2 := by ring
  have hYY : 10 * Y ≤ Y ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right Y (by omega)
  simp only [camSearchK]
  rw [e2] at e1
  clear_value Y Z B s x
  generalize Y ^ 2 = Q at *
  generalize (m + 1) * (B + 2000 * (Z + m + 2 * (Val.nat k).wt + 2 * (Val.nat s).wt + 12)) = R at *
  omega

end GI.Lang
