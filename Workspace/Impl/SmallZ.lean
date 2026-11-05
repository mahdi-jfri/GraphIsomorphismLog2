module

public import Workspace.Lang.Lib.Loop
public import Workspace.Machine.Len
public import Workspace.Assembly.Params

@[expose] public section

/-!
# The integer small test as a program

The dispatcher of `Continue` enumerates a primitive quotient whose order passes the integer
small test `PrimitiveQuotient.SmallZ b`: `|ρ(G)| ≤ d^(b ⌊log₂ d⌋)`
(`Workspace/Algorithm/Dispatch.lean`). The real test `|ρ(G)| ≤ exp(a (log d)²)` cannot be decided
exactly, and the integer test implies it for `b = ⌊a log 2⌋` (`small_of_smallZ`).

`smallZFuns b B` (seven functions) decides the integer test with exponent `B` on `[ord, d]`:
it returns `1` when `ord ≤ d^(B ⌊log₂ d⌋)` and `0` otherwise (`smallZ_spec`). It works in two
loops, so that no number exceeds `(ord + 1) max(d, 1)`:

* `log2Funs`: `d` rounds of doubling from `[0, 1]`, which stop at `[⌊log₂ d⌋, 2^⌊log₂ d⌋]`;
* `powFuns`: `e = B ⌊log₂ d⌋` rounds of `t ↦ min(t d, ord + 1)` from `1`, which give
  `min(d^e, ord + 1)`.

Then `ord ≤ d^e` exactly when `ord < min(d^e, ord + 1) + 1`. The cost is at most
`smallZK X²` with `X = wt [ord, d] + B d + B + d + 10` (`smallZ_spec`). No cited result is used.
-/

namespace GI.Lang

open GI.Machine (BinOp len len_mono len_mul_le len_le_self)
open GI.Cited (Val)

/-! ### The arithmetic facts -/

/-- One doubling step: below `⌊log₂ d⌋` the next power of two is at most `d`, and at
`⌊log₂ d⌋` it is above `d`. -/
theorem log2_step_lt (d c : ℕ) (hc : c < Nat.log 2 d) : 2 * 2 ^ c ≤ d := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hc
  calc 2 * 2 ^ c = 2 ^ (c + 1) := by ring
    _ ≤ 2 ^ Nat.log 2 d := Nat.pow_le_pow_right (by norm_num) hc
    _ ≤ d := Nat.pow_log_le_self 2 hd

theorem log2_step_eq (d : ℕ) : d < 2 * 2 ^ Nat.log 2 d := by
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) d
  calc d < 2 ^ (Nat.log 2 d + 1) := this
    _ = 2 * 2 ^ Nat.log 2 d := by ring

/-- One step of the capped power: `min(min(x, y) d, y) = min(x d, y)` for `y ≥ 0`. -/
theorem min_mul_min (x y d : ℕ) : min (min x y * d) y = min (x * d) y := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rcases le_total x y with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h]
      have h1 : y ≤ y * d := Nat.le_mul_of_pos_right y hd
      have h2 : y ≤ x * d := le_trans h1 (Nat.mul_le_mul_right d h)
      rw [min_eq_right h1, min_eq_right h2]

/-- The final test: `ord ≤ x` exactly when `ord < min(x, ord + 1) + 1`. -/
theorem le_iff_lt_min (ord x : ℕ) : ord ≤ x ↔ ord < min x (ord + 1) + 1 := by
  constructor
  · intro h
    have : ord ≤ min x (ord + 1) := le_min h (Nat.le_succ ord)
    omega
  · intro h
    rcases le_total x (ord + 1) with h' | h'
    · rw [min_eq_left h'] at h; omega
    · omega

/-! ### `⌊log₂ d⌋` by doubling -/

/-- The doubling step on `[d, i, [c, p]]`: `[c, p]` if `d < 2p`, else `[c + 1, 2p]`. -/
def log2Step : Expr :=
  .ite (.arith .lt (arg 0) (.arith .mul (.nat 2) (.get (arg 2) (.nat 1))))
    (arg 2)
    (mk2 (.arith .add (.get (arg 2) (.nat 0)) (.nat 1))
      (.arith .mul (.nat 2) (.get (arg 2) (.nat 1))))

/-- `⌊log₂ d⌋`, at base `b` (three functions): on `d`, the list `[⌊log₂ d⌋, 2^⌊log₂ d⌋]`. It runs
`d + 4` rounds; the rounds after `⌊log₂ d⌋` change nothing. -/
def log2Funs (b : ℕ) : List Expr :=
  loopFuns b (.arith .add (.var 0) (.nat 4)) (mk2 (.nat 0) (.nat 1)) log2Step

/-- The value of the doubling loop after `i` rounds. -/
def log2Acc (d i : ℕ) : Val := .list [.nat (min i (Nat.log 2 d)), .nat (2 ^ min i (Nat.log 2 d))]

/-- The entries of the doubling loop are at most `d` and `max(d, 1)`. -/
theorem log2Acc_le (d i : ℕ) : min i (Nat.log 2 d) ≤ d ∧ 2 ^ min i (Nat.log 2 d) ≤ max d 1 := by
  refine ⟨(min_le_right _ _).trans (Nat.log_le_self 2 d), ?_⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · calc 2 ^ min i (Nat.log 2 d) ≤ 2 ^ Nat.log 2 d :=
          Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)
      _ ≤ d := Nat.pow_log_le_self 2 (by omega)
      _ ≤ max d 1 := le_max_left _ _

theorem len_max_one_le (d : ℕ) : len (max d 1) ≤ len d + 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [max_eq_left hd]; omega

theorem wt_log2Acc_le (d i : ℕ) : (log2Acc d i).wt ≤ 4 * (Val.nat d).wt + 20 := by
  obtain ⟨h1, h2⟩ := log2Acc_le d i
  have := wt_list2_le (.nat (min i (Nat.log 2 d))) (.nat (2 ^ min i (Nat.log 2 d)))
  have l1 := len_mono h1
  have l2 := len_mono h2
  have l3 := len_max_one_le d
  simp only [log2Acc, wt_nat] at *
  omega

/-- One round of the doubling loop. -/
theorem log2Step_det {P : Program} (d i : ℕ) :
    Det P [.list [.nat d, .nat i, log2Acc d i]] log2Step (log2Acc d (i + 1))
      (40 * ((Val.list [.nat d, .nat i, log2Acc d i]).wt + 20)) := by
  set L := Nat.log 2 d
  set c := min i L with hc
  set A := Val.list [.nat d, .nat i, log2Acc d i] with hA
  have hacc : log2Acc d i = .list [.nat c, .nat (2 ^ c)] := rfl
  have dA := Det.arg' (P := P) (vs := [.nat d, .nat i, log2Acc d i]) (rest := []) (j := 2) rfl
  have dD := Det.arg' (P := P) (vs := [.nat d, .nat i, log2Acc d i]) (rest := []) (j := 0) rfl
  rw [hacc] at dA
  have dP := Det.get' dA (Det.nat 1) (show [Val.nat c, .nat (2 ^ c)][1]? = some (.nat (2 ^ c)) from rfl)
  have dC := Det.get' dA (Det.nat 0) (show [Val.nat c, .nat (2 ^ c)][0]? = some (.nat c) from rfl)
  have d2P := Det.arith (op := .mul) (Det.nat (P := P) (env := [A]) 2) dP
  have dT := Det.arith (op := .lt) dD d2P
  have dNew := Det.mk2 (Det.arith (op := .add) dC (Det.nat 1)) d2P
  -- the weights
  have hwA : (log2Acc d i).wt < A.wt := wt_le_wt_list (by simp)
  have hwD : (Val.nat d).wt < A.wt := wt_le_wt_list (by simp)
  have hb : c ≤ d ∧ 2 ^ c ≤ max d 1 := log2Acc_le d i
  have hwn := wt_log2Acc_le d (i + 1)
  have l2 : len (2 * 2 ^ c) ≤ len d + 3 := by
    have := len_mul_le 2 (2 ^ c)
    have := len_mono hb.2
    have := len_max_one_le d
    have : len 2 = 2 := rfl
    omega
  have lc1 : len (c + 1) ≤ len d + 2 := by
    have := GI.Machine.len_add_le c 1
    have := len_mono hb.1
    have : len 1 = 1 := rfl
    omega
  have hlist := wt_list2_le (Val.nat (c + 1)) (.nat (2 * 2 ^ c))
  have hev : ∀ x y, BinOp.eval .mul x y = x * y := fun _ _ => rfl
  have hel : ∀ x y, BinOp.eval .lt x y = if x < y then 1 else 0 := fun _ _ => rfl
  have hea : ∀ x y, BinOp.eval .add x y = x + y := fun _ _ => rfl
  simp only [hev, hel, hea, wt_nat] at d2P dT dNew hlist
  have wc := wt_nat c
  have w2 := wt_nat (2 ^ c)
  have hwacc : (log2Acc d i).wt = (Val.list [.nat c, .nat (2 ^ c)]).wt := by rw [hacc]
  have hl0 : len c ≤ len d := len_mono hb.1
  have hl1 : len (2 ^ c) ≤ len d + 1 := (len_mono hb.2).trans (len_max_one_le d)
  have wdd := wt_nat d
  have hq : (Val.list [Val.nat d, Val.nat i, Val.list [Val.nat c, Val.nat (2 ^ c)]]).wt = A.wt := by
    rw [hA, hacc]
  have hp : (Val.list [Val.nat d, Val.nat i, log2Acc d i]).wt = A.wt := rfl
  have hl0' : len 0 = 0 := rfl
  have hl1' : len 1 = 1 := rfl
  have hl2' : len 2 = 2 := rfl
  by_cases hcl : c < L
  · -- `2^(c+1) ≤ d`: double
    have h2 := log2_step_lt d c hcl
    have hlt : ¬ d < 2 * 2 ^ c := by omega
    have hci : c = i := by rw [hc]; exact min_eq_left (by omega)
    have hnext : log2Acc d (i + 1) = .list [.nat (c + 1), .nat (2 * 2 ^ c)] := by
      simp only [log2Acc]
      have : min (i + 1) L = c + 1 := by rw [← hci]; exact min_eq_left (by omega)
      rw [this, pow_succ, mul_comm (2 ^ c) 2]
    rw [if_neg hlt] at dT
    rw [hnext]
    refine (Det.ite_zero dT dNew).mono ?_
    rw [hnext] at hwn
    simp only [wt_nat] at *
    omega
  · -- `c = ⌊log₂ d⌋`: `d < 2^(c+1)`, keep
    have hcL : c = L := by have : c ≤ L := min_le_right _ _; omega
    have h2 : d < 2 * 2 ^ c := hcL ▸ log2_step_eq d
    have hnext : log2Acc d (i + 1) = log2Acc d i := by
      simp only [log2Acc]
      have h1 : min (i + 1) L = L := min_eq_right (by have : min i L = L := hcL.symm ▸ hc.symm; omega)
      have h2 : min i L = L := hc ▸ hcL
      rw [h1, h2]
    rw [if_pos h2] at dT
    rw [hnext]
    have dA' := Det.arg' (P := P) (vs := [.nat d, .nat i, log2Acc d i]) (rest := []) (j := 2) rfl
    refine (Det.ite_pos dT one_ne_zero dA').mono ?_
    simp only [wt_nat] at *
    omega

/-- After `d + 4` rounds the doubling loop holds `[⌊log₂ d⌋, 2^⌊log₂ d⌋]`. -/
theorem log2Acc_final (d : ℕ) :
    log2Acc d (d + 4) = .list [.nat (Nat.log 2 d), .nat (2 ^ Nat.log 2 d)] := by
  have : min (d + 4) (Nat.log 2 d) = Nat.log 2 d :=
    min_eq_right ((Nat.log_le_self 2 d).trans (by omega))
  simp only [log2Acc, this]

/-- **`⌊log₂ d⌋` by doubling.** -/
theorem log2_spec {P : Program} {b : ℕ} (h : P.HasAt b (log2Funs b)) (d : ℕ) :
    FunDet P b (.nat d) (.list [.nat (Nat.log 2 d), .nat (2 ^ Nat.log 2 d)])
      (2000 * (d + 4) + loopModK * (d + 5) * (5 * (Val.nat d).wt + d + 25)) := by
  have wd := wt_nat d
  have hk : Det P [.nat d] (.arith .add (.var 0) (.nat 4)) (.nat (d + 4)) _ :=
    Det.arith' (op := .add) (Det.var' (P := P) (env := [.nat d]) (i := 0) rfl) (Det.nat 4) rfl
  have h0 := Det.mk2 (P := P) (env := [.nat d]) (Det.nat 0) (Det.nat 1)
  have w01 := wt_list2_le (Val.nat 0) (.nat 1)
  have l4 := wt_nat_le (d + 4)
  have hl0 : len 0 = 0 := rfl
  have hl1 : len 1 = 1 := rfl
  refine (loopBdd_spec h hk h0 ?_ (M := 4 * (Val.nat d).wt + 20)
    (Inv := fun i acc => acc = log2Acc d i) (D := fun _ => 2000) rfl
    (fun i acc _ h => h ▸ wt_log2Acc_le d i) ?_).mono ?_
  · simp only [wt_nat] at w01 wd ⊢
    omega
  · rintro i acc hi rfl
    refine (log2Step_det d i).post fun c hc => ⟨rfl, ?_⟩
    have := wt_stepArg_le (.nat d) i (log2Acc d i)
    have := wt_log2Acc_le d i
    clear h hk h0 w01 l4 hl0 hl1
    beta_reduce
    generalize (Val.list [Val.nat d, Val.nat i, log2Acc d i]).wt = X at *
    generalize (log2Acc d i).wt = Y at *
    generalize (Val.nat d).wt = Z at *
    clear wd
    linarith
  · rintro w c ⟨rfl, hc⟩
    refine ⟨log2Acc_final d, hc.trans ?_⟩
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have : (Val.nat d).wt + (d + 4) + (4 * (Val.nat d).wt + 20) + 1 = 5 * (Val.nat d).wt + d + 25 := by
      ring
    rw [this, mul_comm (d + 4) 2000]

/-! ### The capped power -/

/-- The step of the capped power on `[[ord, d, e], i, t]`: `min(t d, ord + 1)`. -/
def powStep : Expr :=
  .letE (.arith .mul (arg 2) (.get (arg 0) (.nat 1)))
    (.ite (.arith .lt (.get (arg 0) (.nat 0)) (.var 1))
      (.arith .add (.get (arg 0) (.nat 0)) (.nat 1)) (.var 1))

/-- The capped power, at base `b` (three functions): on `[ord, d, e]`, `min(d^e, ord + 1)`. -/
def powFuns (b : ℕ) : List Expr := loopFuns b (.get (.var 0) (.nat 2)) (.nat 1) powStep

/-- One round of the capped power. -/
theorem powStep_det {P : Program} (ord d e i : ℕ) :
    Det P [.list [.list [.nat ord, .nat d, .nat e], .nat i, .nat (min (d ^ i) (ord + 1))]] powStep
      (.nat (min (d ^ (i + 1)) (ord + 1)))
      (40 * ((Val.list [.list [.nat ord, .nat d, .nat e], .nat i,
        .nat (min (d ^ i) (ord + 1))]).wt + 20)) := by
  set t0 := min (d ^ i) (ord + 1)
  set a := Val.list [.nat ord, .nat d, .nat e]
  set A := Val.list [a, .nat i, .nat t0] with hA
  have dT := Det.arg' (P := P) (vs := [a, .nat i, .nat t0]) (rest := []) (j := 2) rfl
  have dA := Det.arg' (P := P) (vs := [a, .nat i, .nat t0]) (rest := []) (j := 0) rfl
  have dD := Det.get' dA (Det.nat 1) (show [Val.nat ord, .nat d, .nat e][1]? = some (.nat d) from rfl)
  have dM := Det.arith (op := .mul) dT dD
  have hev : BinOp.eval .mul t0 d = t0 * d := rfl
  rw [hev] at dM
  -- inside the `let`
  have dA' := Det.arg' (P := P) (vs := [a, .nat i, .nat t0]) (rest := [.nat (t0 * d)]) (j := 0) rfl
  have dO := Det.get' dA' (Det.nat 0) (show [Val.nat ord, .nat d, .nat e][0]? = some (.nat ord) from rfl)
  have dV := Det.var' (P := P) (env := [A, .nat (t0 * d)]) (i := 1) rfl
  have dTest := Det.arith (op := .lt) dO dV
  have dAdd := Det.arith (op := .add) dO (Det.nat 1)
  have hval : (if BinOp.eval .lt ord (t0 * d) = 0 then Val.nat (t0 * d)
      else Val.nat (BinOp.eval .add ord 1)) = .nat (min (d ^ (i + 1)) (ord + 1)) := by
    have h : min (t0 * d) (ord + 1) = min (d ^ (i + 1)) (ord + 1) := by
      rw [pow_succ]; exact min_mul_min _ _ _
    rw [← h]
    by_cases hlt : ord < t0 * d
    · simp only [BinOp.eval, hlt, ↓reduceIte, one_ne_zero,
        min_eq_right (by omega : ord + 1 ≤ t0 * d)]
    · simp only [BinOp.eval, hlt, ↓reduceIte,
        min_eq_left (by omega : t0 * d ≤ ord + 1)]
  have dIte := Det.ite' dTest dAdd dV
  rw [hval] at dIte
  refine (Det.letE dM dIte).mono ?_
  -- the weights
  have hwa : a.wt < A.wt := wt_le_wt_list (by simp)
  have hwt : (Val.nat t0).wt < A.wt := wt_le_wt_list (by simp)
  have hwo : (Val.nat ord).wt < a.wt := wt_le_wt_list (by simp)
  have hwd : (Val.nat d).wt < a.wt := wt_le_wt_list (by simp)
  rw [wt_nat] at hwt hwo hwd
  have ht0 : t0 ≤ ord + 1 := min_le_right _ _
  have l1 := len_mul_le t0 d
  have l3 := GI.Machine.len_add_le ord 1
  have l4 := len_mono (min_le_right (d ^ (i + 1)) (ord + 1))
  have hl1 : len 1 = 1 := rfl
  have lif : len (if ord < t0 * d then 1 else 0) ≤ 1 := by split <;> decide
  have wmax : ∀ x y : ℕ, max x y ≤ x + y := fun x y => max_le (by omega) (by omega)
  have m1 := wmax (len (ord + 1) + 2) (len (t0 * d) + 2)
  have m2 := wmax (len (ord + 1) + 2) (len (t0 * d) + 2 + 1)
  have m3 := wmax (len ord) (len 1)
  have hAw : (Val.list [a, Val.nat i, Val.nat t0]).wt = A.wt := rfl
  simp only [wt_nat, BinOp.eval, hAw]
  generalize A.wt = X at *
  generalize a.wt = Y at *
  omega

/-- **The capped power**: `min(d^e, ord + 1)`. -/
theorem pow_spec {P : Program} {b : ℕ} (h : P.HasAt b (powFuns b)) (ord d e : ℕ) :
    FunDet P b (.list [.nat ord, .nat d, .nat e]) (.nat (min (d ^ e) (ord + 1)))
      (2000 * e + loopModK * (e + 1) *
        ((Val.list [.nat ord, .nat d, .nat e]).wt + e + (len (ord + 1) + 2) + 1)) := by
  set a := Val.list [.nat ord, .nat d, .nat e] with ha
  have hk : Det P [a] (.get (.var 0) (.nat 2)) (.nat e) _ :=
    Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 2)
      (show [Val.nat ord, .nat d, .nat e][2]? = some (.nat e) from rfl)
  have h0 := Det.nat (P := P) (env := [a]) 1
  have hwe : (Val.nat e).wt < a.wt := wt_le_wt_list (by simp)
  have le := wt_nat_le e
  have ha2 := a.two_le_size
  have ha3 := a.size_le_wt
  refine (loopBdd_spec h hk h0 ?_ (M := len (ord + 1) + 2)
    (Inv := fun i acc => acc = .nat (min (d ^ i) (ord + 1))) (D := fun _ => 2000)
    (by simp) (fun i acc _ h => by
      rw [h, wt_nat]; exact Nat.add_le_add_right (len_mono (min_le_right _ _)) 2) ?_).mono ?_
  · show a.wt + 1 + (2 + 3) + (Val.nat e).wt + 1 + (1 + 3) ≤ 10 * (a.wt + e + 1)
    omega
  · rintro i acc hi rfl
    refine (powStep_det ord d e i).post fun c hc => ⟨rfl, ?_⟩
    have h1 := wt_stepArg_le a i (.nat (min (d ^ i) (ord + 1)))
    have h2 : (Val.nat (min (d ^ i) (ord + 1))).wt ≤ len (ord + 1) + 2 := by
      rw [wt_nat]; exact Nat.add_le_add_right (len_mono (min_le_right _ _)) 2
    clear h hk h0
    beta_reduce
    generalize (Val.list [a, .nat i, .nat (min (d ^ i) (ord + 1))]).wt = X at *
    generalize (Val.nat (min (d ^ i) (ord + 1))).wt = Y at *
    generalize a.wt = Z at *
    linarith
  · rintro w c ⟨rfl, hc⟩
    refine ⟨rfl, hc.trans ?_⟩
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm e 2000, le_refl]

/-! ### The test -/

/-- The body of the test on `[ord, d]`: `L := ⌊log₂ d⌋`, `m := min(d^(B L), ord + 1)`, and
`ord < m + 1`. -/
def smallZBody (b B : ℕ) : Expr :=
  .letE (.call (b + 1) (.get (.var 0) (.nat 1)))
    (.letE (.call (b + 4) (mk3 (.get (.var 0) (.nat 0)) (.get (.var 0) (.nat 1))
        (.arith .mul (.nat B) (.get (.var 1) (.nat 0)))))
      (.arith .lt (.get (.var 0) (.nat 0)) (.arith .add (.var 2) (.nat 1))))

/-- **The integer small test**, at base `b` (seven functions), with exponent `B`. -/
def smallZFuns (b B : ℕ) : List Expr := [smallZBody b B] ++ log2Funs (b + 1) ++ powFuns (b + 4)

/-- The constant of the test. -/
def smallZK : ℕ := 100000

/-- **The integer small test.** On `[ord, d]` it returns `1` if `ord ≤ d^(B ⌊log₂ d⌋)` and `0`
otherwise, at cost at most `smallZK X²` with `X = wt [ord, d] + B d + B + d + 10`. -/
theorem smallZ_spec {P : Program} {b B : ℕ} (h : P.HasAt b (smallZFuns b B)) (ord d : ℕ) :
    FunDet P b (.list [.nat ord, .nat d]) (boolVal (decide (ord ≤ d ^ (B * Nat.log 2 d))))
      (smallZK * ((Val.list [.nat ord, .nat d]).wt + B * d + B + d + 10) ^ 2) := by
  simp only [smallZFuns] at h
  have hbody : P.funs[b]? = some (smallZBody b B) := h.left.left.single
  have hlog : P.HasAt (b + 1) (log2Funs (b + 1)) := h.left.right
  have hpow : P.HasAt (b + 4) (powFuns (b + 4)) := by
    have := h.right; simpa [log2Funs, loopFuns, Nat.add_assoc] using this
  set x := Val.list [.nat ord, .nat d] with hx
  obtain ⟨L, hLd⟩ : ∃ L, Nat.log 2 d = L := ⟨_, rfl⟩
  rw [hLd]
  set m := min (d ^ (B * L)) (ord + 1)
  have dX := Det.var' (P := P) (env := [x]) (i := 0) rfl
  have dDd := Det.get' dX (Det.nat 1) (show [Val.nat ord, .nat d][1]? = some (.nat d) from rfl)
  have dLog := Det.call dDd (log2_spec hlog d)
  rw [hLd] at dLog
  -- second `let`
  have dX2 := Det.var' (P := P) (env := [x, .list [.nat L, .nat (2 ^ L)]]) (i := 0) rfl
  have dO2 := Det.get' dX2 (Det.nat 0) (show [Val.nat ord, .nat d][0]? = some (.nat ord) from rfl)
  have dD2 := Det.get' dX2 (Det.nat 1) (show [Val.nat ord, .nat d][1]? = some (.nat d) from rfl)
  have dLg := Det.var' (P := P) (env := [x, .list [.nat L, .nat (2 ^ L)]]) (i := 1) rfl
  have dL := Det.get' dLg (Det.nat 0) (show [Val.nat L, .nat (2 ^ L)][0]? = some (.nat L) from rfl)
  have dE := Det.arith' (op := .mul) (Det.nat B) dL rfl
  have dArg := Det.mk3 dO2 dD2 dE
  have dPow := Det.call dArg (pow_spec hpow ord d (B * L))
  -- the test
  have dX3 := Det.var' (P := P) (env := [x, .list [.nat L, .nat (2 ^ L)], .nat m]) (i := 0) rfl
  have dO3 := Det.get' dX3 (Det.nat 0) (show [Val.nat ord, .nat d][0]? = some (.nat ord) from rfl)
  have dM := Det.var' (P := P) (env := [x, .list [.nat L, .nat (2 ^ L)], .nat m]) (i := 2) rfl
  have dT := Det.arith (op := .lt) dO3 (Det.arith (op := .add) dM (Det.nat 1))
  have hval : Val.nat (BinOp.eval .lt ord (BinOp.eval .add m 1)) =
      boolVal (decide (ord ≤ d ^ (B * L))) := by
    change Val.nat (if ord < m + 1 then 1 else 0) =
      Val.nat (decide (ord ≤ d ^ (B * L))).toNat
    by_cases hle : ord ≤ d ^ (B * L)
    · rw [if_pos ((le_iff_lt_min ord _).1 hle), decide_eq_true hle]; rfl
    · rw [if_neg (fun h' => hle ((le_iff_lt_min ord _).2 h')), decide_eq_false hle]; rfl
  rw [← hval]
  refine FunDet.intro hbody ((Det.letE dLog (Det.letE dPow dT)).mono ?_)
  -- the weights
  clear h hbody hlog hpow dX dDd dLog dX2 dO2 dD2 dLg dL dE dArg dPow dX3 dO3 dM dT hval
  have hm1 : m ≤ ord + 1 := min_le_right _ _
  clear_value m
  have hW := x.two_le_size
  have hW' := x.size_le_wt
  have hwd : (Val.nat d).wt < x.wt := wt_le_wt_list (by simp)
  have hwo : (Val.nat ord).wt < x.wt := wt_le_wt_list (by simp)
  have hL : L ≤ d := hLd ▸ Nat.log_le_self 2 d
  have heB : B * L ≤ B * d := Nat.mul_le_mul_left B hL
  have hlg : (Val.list [Val.nat L, Val.nat (2 ^ L)]).wt ≤ 4 * (Val.nat d).wt + 20 := by
    have := wt_log2Acc_le d (d + 4); rwa [log2Acc_final, hLd] at this
  have hwL := wt_nat_le L
  have hw3 := wt_list3_le (Val.nat ord) (Val.nat d) (Val.nat (B * L))
  have hwe := wt_nat_le (B * L)
  have lo1 := GI.Machine.len_add_le ord 1
  have lm := len_mono hm1
  have lm1 := len_mono (show m + 1 ≤ ord + 2 by omega)
  have lo2 := GI.Machine.len_add_le ord 2
  have hl1 : len 1 = 1 := rfl
  have hl2 : len 2 = 2 := rfl
  have wlt : ∀ y z, (Val.nat (BinOp.eval .lt y z)).wt ≤ 3 := fun y z => by
    simp only [BinOp.eval]; split <;> decide
  have w1 := wlt ord (BinOp.eval .add m 1)
  have hmax := le_max_left (len ord) (len 1)
  have hmax2 : max (len ord) (len 1) ≤ len ord + 1 := max_le (by omega) (by omega)
  have hmax3 : max (len ord) (len 2) ≤ len ord + 2 := max_le (by omega) (by omega)
  have lmm := len_mono (min_le_right (d ^ (B * L)) (ord + 1))
  simp only [BinOp.eval, wt_nat] at hwd hwo hwL hwe w1 hw3 hlg ⊢
  generalize B * L = E at *
  generalize B * d = F at *
  -- the two loops
  set X := x.wt + F + B + d + 10 with hX
  clear_value X
  have hlogc : 1000 * (d + 5) * (5 * (len d + 2) + d + 25) ≤ 5000 * X ^ 2 := by
    have h1 : d + 5 ≤ X := by omega
    have h2 : 5 * (len d + 2) + d + 25 ≤ 5 * X := by omega
    calc 1000 * (d + 5) * (5 * (len d + 2) + d + 25) ≤ 1000 * X * (5 * X) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ = 5000 * X ^ 2 := by ring
  have hpowc : 1000 * (E + 1) * ((Val.list [Val.nat ord, Val.nat d, Val.nat E]).wt + E +
      (len (ord + 1) + 2) + 1) ≤ 6000 * X ^ 2 := by
    have h1 : E + 1 ≤ X := by omega
    have h2 : (Val.list [Val.nat ord, Val.nat d, Val.nat E]).wt + E +
        (len (ord + 1) + 2) + 1 ≤ 6 * X := by omega
    calc _ ≤ 1000 * X * (6 * X) := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ = 6000 * X ^ 2 := by ring
  have hX10 : 10 ≤ X := by omega
  have hXX : 10 * X ≤ X ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right X hX10
  simp only [loopModK, smallZK] at *
  generalize X ^ 2 = Y at *
  generalize (Val.list [Val.nat ord, Val.nat d, Val.nat E]).wt = Z at *
  obtain ⟨P1, hP1⟩ : ∃ P1, 1000 * (d + 5) * (5 * (len d + 2) + d + 25) = P1 := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P2, 1000 * (E + 1) * (Z + E + (len (ord + 1) + 2) + 1) = P2 := ⟨_, rfl⟩
  rw [hP1] at hlogc ⊢
  rw [hP2] at hpowc ⊢
  clear hP1 hP2
  omega

open Classical in
/-- **The integer small test of a primitive quotient at `P₀`**: on `[|ρ(G)|, d]`, the test with
exponent `24953 = P₀.smallExp` returns `1` exactly when the quotient passes `SmallZ`. -/
theorem smallZ_spec_P₀ {P : Program} {b : ℕ} (h : P.HasAt b (smallZFuns b 24953))
    {Ω C : Type} {S : GI.Algorithm.State Ω C} (Q : GI.Algorithm.PrimitiveQuotient S) :
    FunDet P b (.list [.nat (Nat.card Q.ρ.range), .nat Q.d])
      (boolVal (decide (Q.SmallZ GI.Assembly.P₀.smallExp)))
      (smallZK * ((Val.list [.nat (Nat.card Q.ρ.range), .nat Q.d]).wt + 24953 * Q.d + 24953 +
        Q.d + 10) ^ 2) := by
  have := smallZ_spec h (Nat.card Q.ρ.range) Q.d
  have e : decide (Q.SmallZ GI.Assembly.P₀.smallExp) =
      decide (Nat.card Q.ρ.range ≤ Q.d ^ (24953 * Nat.log 2 Q.d)) := by
    simp only [GI.Algorithm.PrimitiveQuotient.SmallZ, GI.Assembly.P₀_smallExp]
  rw [e]
  exact this

end GI.Lang
