/-
Helper statements for the graph isomorphism wrapper program, with weakest-precondition proofs.

We define four small building blocks and prove their specifications:
* `findN`: recovers `n` from cell 0, which holds `2 * n * n`.
* `writeNatBits`: writes `natBits v` at `regPos` and advances `regPos`.
* `writeMapBits`: writes `mapBits f` for a map stored at `regBase`.
* `writeGensBits`: writes the list of generators stored at `regR + 2 + regN`.

Every block keeps all memory cells below its initial write pointer `regPos`, so writing output
bits after the program's output never overwrites data that still has to be read.
-/
module

public import Workspace.Turing.Wrap.Bits
public import Workspace.Machine.Loops

@[expose] public section

namespace GI.Turing

open GI.Machine GI.Statement

/-! ### Registers of the wrapper -/

abbrev regL : ℕ := 0
abbrev regN : ℕ := 1
abbrev regR : ℕ := 2
abbrev regK : ℕ := 3
abbrev regB : ℕ := 4
abbrev regPos : ℕ := 5
abbrev regT : ℕ := 6
abbrev regI : ℕ := 7
abbrev regV : ℕ := 8
abbrev regBase : ℕ := 9

/-! ### Recovering `n` from `2 * n * n` -/

/-- Count `m` up from 0 while `2 * m * m < mem 0`, placing `n` in `regN`. -/
def findN : Stmt :=
  .assign regL (.load (.const 0)) ;;
  .assign regN (.const 0) ;;
  .loop (.lt (2 * .reg regN * .reg regN) (.reg regL))
    (.assign regN (.reg regN + 1))

/-- If cell 0 holds `2 * n * n`, then `findN` keeps memory, sets `regN` to `n`, and costs at most
`(n + 1) * (25 * len (2 * n * n + 2) + 15)`. -/
theorem wp_findN {p : Program} {st : State} {n : ℕ} (h0 : st.mem 0 = 2 * n * n) :
    WP p findN st (fun o st' c =>
      o = .normal ∧ st'.mem = st.mem ∧ st'.regs regN = n ∧
      c ≤ (n + 1) * (25 * len (2 * n * n + 2) + 15)) := by
  set M := 2 * n * n + 2 with hM
  set L := len M with hL
  refine WP.seq' (fun st₁ c₁ => st₁.mem = st.mem ∧ st₁.regs regL = 2 * n * n ∧
      c₁ ≤ 6 * L + 3) ?_ ?_
  · refine WP.assign_le (M := M) (by simp [h0, hM]) fun c hc => ?_
    refine ⟨rfl, rfl, by simp [h0], ?_⟩
    simp only [Expr.size_load, Expr.size_const] at hc; omega
  rintro st₁ c₁ ⟨hmem₁, hL₁, hc₁⟩
  refine WP.seq' (fun st₂ c₂ => st₂.mem = st.mem ∧ st₂.regs regL = 2 * n * n ∧
      st₂.regs regN = 0 ∧ c₂ = 2) ?_ ?_
  · apply WP.assign
    refine ⟨rfl, hmem₁, by simp [regL, regN, hL₁], by simp, by simp [len_zero]⟩
  rintro st₂ c₂ ⟨hmem₂, hL₂, hN₂, rfl⟩
  let I : State → ℕ → Prop := fun st' a =>
    ∃ m ≤ n, st'.mem = st.mem ∧ st'.regs regL = 2 * n * n ∧ st'.regs regN = m ∧
      a ≤ m * (25 * L + 15)
  refine WP.loop (Q := fun o st' c =>
      o = .normal ∧ st'.mem = st.mem ∧ st'.regs regN = n ∧
      c₁ + (2 + c + 1) + 1 ≤ (n + 1) * (25 * L + 15))
    I (fun st' => n - st'.regs regN) ⟨0, Nat.zero_le n, hmem₂, hL₂, hN₂, by simp⟩ ?_ ?_
  · rintro st' a ⟨m, hmn, hmem', hL', hN', ha⟩ htest
    have hlt : 2 * m * m < 2 * n * n := by
      simp only [Expr.lt, Expr.mul_eq, Expr.ofNat_eq, evalExpr_bin, evalExpr_const, evalExpr_reg,
        BinOp.eval_lt, BinOp.eval_mul, hL', hN'] at htest
      by_contra h; simp [h] at htest
    have hm_lt : m < n := by
      by_contra h
      have : m = n := by omega
      subst this; omega
    have htest_le : (evalExpr st' (.lt (2 * .reg regN * .reg regN) (.reg regL))).2 ≤
        14 * L + 7 := by
      have hv : (Expr.lt (2 * .reg regN * .reg regN) (.reg regL)).ValsLe st' M := by
        have h1 : m ≤ n * n := le_trans hm_lt.le (Nat.le_mul_self n)
        have h2 : 2 * m * m ≤ 2 * n * n := by nlinarith
        have h3 : 2 * n * n = 2 * (n * n) := by ring
        simp [Expr.lt, hL', hN', hM]; omega
      have hcost := Expr.cost_le hv
      have hsize : (Expr.lt (2 * .reg regN * .reg regN) (.reg regL)).size = 7 := rfl
      rw [hsize] at hcost
      omega
    refine WP.assign_le (M := M) (by
        have h1 : m ≤ n * n := le_trans hm_lt.le (Nat.le_mul_self n)
        have h2 : 2 * n * n = 2 * (n * n) := by ring
        simp [hN', hM]; omega) fun c hc => ?_
    simp only [Expr.add_eq, Expr.ofNat_eq, Expr.size_bin, Expr.size_reg, Expr.size_const] at hc
    refine ⟨⟨m + 1, hm_lt, hmem', by simp [regL, regN, hL'], by simp [hN'], ?_⟩,
      by simp [hN']; omega⟩
    rw [Nat.succ_mul]
    omega
  · rintro st' a ⟨m, hmn, hmem', hL', hN', ha⟩ htest
    have hge : ¬ (2 * m * m < 2 * n * n) := by
      simp only [Expr.lt, Expr.mul_eq, Expr.ofNat_eq, evalExpr_bin, evalExpr_const, evalExpr_reg,
        BinOp.eval_lt, BinOp.eval_mul, hL', hN'] at htest
      intro h; simp [h] at htest
    have hmn_eq : m = n := by
      by_contra h
      have hlt : m < n := by omega
      have : 2 * m * m < 2 * n * n := by nlinarith
      exact hge this
    subst hmn_eq
    have htest_le : (evalExpr st' (.lt (2 * .reg regN * .reg regN) (.reg regL))).2 ≤
        14 * L + 7 := by
      have hv : (Expr.lt (2 * .reg regN * .reg regN) (.reg regL)).ValsLe st' M := by
        have h1 : m ≤ m * m := Nat.le_mul_self m
        have h2 : 2 * m * m = 2 * (m * m) := by ring
        simp [Expr.lt, hL', hN', hM]; omega
      have hcost := Expr.cost_le hv
      have hsize : (Expr.lt (2 * .reg regN * .reg regN) (.reg regL)).size = 7 := rfl
      rw [hsize] at hcost
      omega
    refine ⟨rfl, hmem', hN', ?_⟩
    rw [Nat.succ_mul]
    omega

/-! ### Writing `natBits v` -/

/-- The loop of `writeNatBits`: writes `natDigitsBits v` at `regPos`. -/
def writeNatBitsLoop : Stmt :=
  .loop (.reg regV) (
    .store (.reg regPos) (.const 1) ;;
    .store (.reg regPos + 1) (.reg regV % 2) ;;
    .assign regPos (.reg regPos + 2) ;;
    .assign regV (.reg regV / 2)
  )

/-- Write `natBits v` (with `v = regV`) starting at `regPos`, and advance `regPos`. -/
def writeNatBits : Stmt :=
  writeNatBitsLoop ;;
  .store (.reg regPos) (.const 0) ;;
  .assign regPos (.reg regPos + 1)

@[simp] theorem writes_writeNatBitsLoop (r : ℕ) :
    writeNatBitsLoop.Writes r ↔ r = regPos ∨ r = regV := by
  simp [writeNatBitsLoop, Stmt.Writes]

@[simp] theorem writes_writeNatBits (r : ℕ) :
    writeNatBits.Writes r ↔ r = regPos ∨ r = regV := by
  simp [writeNatBits, Stmt.Writes]; tauto

/-- Specification of `writeNatBitsLoop`, proved by strong induction on `v`. -/
theorem wp_writeNatBitsLoop {p : Program} {M : ℕ} :
    ∀ (v : ℕ) (st : State),
      st.regs regV = v →
      st.regs regPos + 2 * len v + 1 ≤ M →
      v + 2 ≤ M →
      WP p writeNatBitsLoop st (fun o st' c =>
        o = .normal ∧
        st'.regs regPos = st.regs regPos + 2 * len v ∧
        st'.regs regV = 0 ∧
        (∀ r, r ≠ regPos → r ≠ regV → st'.regs r = st.regs r) ∧
        BitsAt st'.mem (st.regs regPos) (natDigitsBits v) ∧
        (∀ x < st.regs regPos, st'.mem x = st.mem x) ∧
        c ≤ len v * (40 * (len M + 1)) + 2) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro st hv hposM hvM
    set pos := st.regs regPos with hpos
    set L := len M with hL
    rcases Nat.eq_zero_or_pos v with rfl | hvpos
    · refine WP.intro (Runs.loop_exit (by simp [hv])) ?_
      refine ⟨rfl, by simp [len_zero, ← hpos], hv, fun _ _ _ => rfl, BitsAt.nil _ _,
        fun _ _ => rfl, ?_⟩
      simp [hv, len_zero]
    · have hlen_step : len (v / 2) + 1 = len v := len_div_two_add_one_of_pos hvpos
      -- Step 1: run one iteration of the loop body.
      have hbody : WP p (
          .store (.reg regPos) (.const 1) ;;
          .store (.reg regPos + 1) (.reg regV % 2) ;;
          .assign regPos (.reg regPos + 2) ;;
          .assign regV (.reg regV / 2)) st (fun o st₁ c₁ =>
            o = .normal ∧
            st₁.regs regPos = pos + 2 ∧
            st₁.regs regV = v / 2 ∧
            (∀ r, r ≠ regPos → r ≠ regV → st₁.regs r = st.regs r) ∧
            st₁.mem pos = 1 ∧
            st₁.mem (pos + 1) = v % 2 ∧
            (∀ x < pos, st₁.mem x = st.mem x) ∧
            c₁ ≤ 36 * L + 21) := by
        refine WP.seq' (fun st₁ c₁ =>
            st₁.regs = st.regs ∧
            st₁.mem = Function.update st.mem pos 1 ∧
            c₁ ≤ 6 * L + 3) ?_ ?_
        · refine WP.store_le (M := M) (by simp [← hpos]; omega) (by simp; omega)
            (by simp [← hpos]; omega) (by simp; omega) fun c hc => ?_
          simp only [Expr.size_reg, Expr.size_const] at hc
          exact ⟨rfl, rfl, by simp [← hpos], by omega⟩
        rintro st₁ c₁ ⟨hr₁, hm₁, hc₁⟩
        refine WP.seq' (fun st₂ c₂ =>
            st₂.regs = st.regs ∧
            st₂.mem = Function.update st₁.mem (pos + 1) (v % 2) ∧
            c₂ ≤ 14 * L + 7) ?_ ?_
        · refine WP.store_le (M := M) (by simp [hr₁, ← hpos]; omega)
            (by simp [hr₁, hv]; omega)
            (by simp [hr₁, ← hpos]; omega)
            (by simp [hr₁, hv]; exact le_trans (Nat.mod_le v 2) (by omega)) fun c hc => ?_
          simp only [Expr.add_eq, Expr.mod_eq, Expr.ofNat_eq, Expr.size_bin, Expr.size_reg,
            Expr.size_const] at hc
          exact ⟨rfl, hr₁, by simp [hr₁, ← hpos, hv], by omega⟩
        rintro st₂ c₂ ⟨hr₂, hm₂, hc₂⟩
        refine WP.seq' (fun st₃ c₃ =>
            st₃.mem = st₂.mem ∧
            st₃.regs = Function.update st.regs regPos (pos + 2) ∧
            c₃ ≤ 8 * L + 4) ?_ ?_
        · refine WP.assign_le (M := M) (by simp [hr₂, ← hpos]; omega) fun c hc => ?_
          simp only [Expr.add_eq, Expr.ofNat_eq, Expr.size_bin, Expr.size_reg,
            Expr.size_const] at hc
          exact ⟨rfl, rfl, by simp [hr₂, ← hpos], by omega⟩
        rintro st₃ c₃ ⟨hm₃, hr₃, hc₃⟩
        refine WP.assign_le (M := M) (by simp [hr₃, regPos, regV, hv]; omega) fun c₄ hc₄ => ?_
        simp only [Expr.div_eq, Expr.ofNat_eq, Expr.size_bin, Expr.size_reg,
          Expr.size_const] at hc₄
        refine ⟨rfl, by simp [hr₃, regPos, regV], by simp [hr₃, regPos, regV, hv],
          fun r h1 h2 => by simp [hr₃, Function.update_of_ne h1, Function.update_of_ne h2],
          ?_, ?_, ?_, by omega⟩
        · rw [hm₃, hm₂, Function.update_of_ne (by omega), hm₁, Function.update_self]
        · rw [hm₃, hm₂, Function.update_self]
        · intro x hx
          rw [hm₃, hm₂, Function.update_of_ne (by omega), hm₁, Function.update_of_ne (by omega)]
      -- Step 2: combine one iteration with the induction hypothesis on `v / 2`.
      obtain ⟨_, st₁, c₁, hrun₁, rfl, hpos₁, hv₁, hregs₁, hm1_0, hm1_1, hbelow₁, hc₁⟩ := hbody
      have hrec := ih (v / 2) (Nat.div_lt_self hvpos (by norm_num)) st₁ hv₁
        (by rw [hpos₁]; omega) (by have := Nat.div_le_self v 2; omega)
      obtain ⟨_, st₂, c₂, hrun₂, rfl, hpos₂, hv₂, hregs₂, hbits₂, hbelow₂, hc₂⟩ := hrec
      refine WP.intro (Runs.loop_step (by simp [hv]; omega) hrun₁ hrun₂) ?_
      refine ⟨rfl, by rw [hpos₂, hpos₁]; omega, hv₂,
        fun r h1 h2 => (hregs₂ r h1 h2).trans (hregs₁ r h1 h2), ?_, ?_, ?_⟩
      · rw [natDigitsBits_pos hvpos]
        refine BitsAt.cons ?_ (BitsAt.cons ?_ ?_)
        · rw [hbelow₂ pos (by omega), hm1_0]; decide
        · rw [hbelow₂ (pos + 1) (by omega), hm1_1]
        · simpa [hpos₁, Nat.add_assoc] using hbits₂
      · intro x hx
        rw [hbelow₂ x (by omega), hbelow₁ x hx]
      · have hlv : len v ≤ L := len_mono (by omega)
        simp only [evalExpr_reg, hv]
        rw [← hlen_step, Nat.succ_mul]
        omega

/-- Specification of `writeNatBits`: writes `natBits v` at `regPos`, advances `regPos` by
`(natBits v).length`, keeps cells below `regPos`, and costs at most
`(len v + 1) * (40 * (len M + 1))`. -/
theorem wp_writeNatBits {p : Program} {M v : ℕ} {st : State}
    (hv : st.regs regV = v)
    (hposM : st.regs regPos + (natBits v).length + 1 ≤ M)
    (hvM : v + 2 ≤ M) :
    WP p writeNatBits st (fun o st' c =>
      o = .normal ∧
      st'.regs regPos = st.regs regPos + (natBits v).length ∧
      (∀ r, r ≠ regPos → r ≠ regV → st'.regs r = st.regs r) ∧
      BitsAt st'.mem (st.regs regPos) (natBits v) ∧
      (∀ x < st.regs regPos, st'.mem x = st.mem x) ∧
      c ≤ (len v + 1) * (40 * (len M + 1))) := by
  set pos := st.regs regPos with hpos
  set L := len M with hL
  have hlen : (natBits v).length = 2 * len v + 1 := natBits_length v
  refine WP.seq' (fun st₁ c₁ =>
      st₁.regs regPos = pos + 2 * len v ∧
      (∀ r, r ≠ regPos → r ≠ regV → st₁.regs r = st.regs r) ∧
      BitsAt st₁.mem pos (natDigitsBits v) ∧
      (∀ x < pos, st₁.mem x = st.mem x) ∧
      c₁ ≤ len v * (40 * (L + 1)) + 2) ?_ ?_
  · exact (wp_writeNatBitsLoop v st hv (by omega) hvM).mono
      fun o st₁ c₁ ⟨ho, hp, _, hr, hb, hbel, hc⟩ => ⟨ho, hp, hr, hb, hbel, hc⟩
  rintro st₁ c₁ ⟨hpos₁, hregs₁, hbits₁, hbelow₁, hc₁⟩
  refine WP.seq' (fun st₂ c₂ =>
      st₂.regs = st₁.regs ∧
      st₂.mem = Function.update st₁.mem (pos + 2 * len v) 0 ∧
      c₂ ≤ 6 * L + 3) ?_ ?_
  · refine WP.store_le (M := M) (by simp [hpos₁]; omega) (by simp)
      (by simp [hpos₁]; omega) (by simp) fun c hc => ?_
    simp only [Expr.size_reg, Expr.size_const] at hc
    exact ⟨rfl, rfl, by simp [hpos₁], by omega⟩
  rintro st₂ c₂ ⟨hr₂, hm₂, hc₂⟩
  refine WP.assign_le (M := M) (by simp [hr₂, hpos₁]; omega) fun c₃ hc₃ => ?_
  simp only [Expr.add_eq, Expr.ofNat_eq, Expr.size_bin, Expr.size_reg, Expr.size_const] at hc₃
  refine ⟨rfl, by simp [hr₂, hpos₁, hlen]; omega,
    fun r h1 h2 => by simp [hr₂, Function.update_of_ne h1, hregs₁ r h1 h2], ?_, ?_, ?_⟩
  · rw [natBits_eq]
    refine BitsAt.append ?_ ?_
    · refine hbits₁.congr fun x hx₁ hx₂ => ?_
      rw [hm₂, Function.update_of_ne (by rw [natDigitsBits_length] at hx₂; omega)]
    · refine BitsAt.singleton ?_
      rw [natDigitsBits_length, hm₂, Function.update_self]
      decide
  · intro x hx
    rw [hm₂, Function.update_of_ne (by omega), hbelow₁ x hx]
  · rw [Nat.succ_mul]
    omega

/-! ### Writing `mapBits f` -/

/-- Write `mapBits f` for a map stored at `regBase .. regBase + regN - 1`. -/
def writeMapBits : Stmt :=
  Stmt.forUp regI regN (
    .assign regV (.load (.reg regBase + .reg regI)) ;;
    writeNatBits
  )

@[simp] theorem writes_writeMapBits (r : ℕ) :
    writeMapBits.Writes r ↔ r = regI ∨ r = regV ∨ r = regPos := by
  simp [writeMapBits, Stmt.Writes]; tauto

/-- The first `k` entries of `mapBits f`. -/
def prefixMapBits {n : ℕ} (f : Fin n → Fin n) (k : ℕ) : List Bool :=
  ((List.finRange n).take k).flatMap fun i => natBits (f i)

theorem prefixMapBits_zero {n : ℕ} (f : Fin n → Fin n) : prefixMapBits f 0 = [] := by
  simp [prefixMapBits]

theorem prefixMapBits_succ {n : ℕ} (f : Fin n → Fin n) {k : ℕ} (hk : k < n) :
    prefixMapBits f (k + 1) = prefixMapBits f k ++ natBits (f ⟨k, hk⟩) := by
  unfold prefixMapBits
  have htake : (List.finRange n).take (k + 1) = (List.finRange n).take k ++ [⟨k, hk⟩] := by
    rw [List.take_add_one]
    have hget : (List.finRange n)[k]? = some ⟨k, hk⟩ := by
      rw [List.getElem?_eq_getElem (by simp [hk]), List.getElem_finRange]
      rfl
    simp [hget]
  rw [htake, List.flatMap_append, List.flatMap_singleton]

theorem prefixMapBits_self {n : ℕ} (f : Fin n → Fin n) : prefixMapBits f n = mapBits f := by
  unfold prefixMapBits mapBits
  rw [List.take_of_length_le (by simp)]

theorem prefixMapBits_length_le {n : ℕ} (f : Fin n → Fin n) (k : ℕ) :
    (prefixMapBits f k).length ≤ (mapBits f).length := by
  unfold prefixMapBits mapBits
  have hsplit := List.take_append_drop k (List.finRange n)
  conv_rhs => rw [← hsplit, List.flatMap_append, List.length_append]
  omega

/-- Specification of `writeMapBits`: writes `mapBits f` at `regPos`, advances `regPos` by
`(mapBits f).length`, keeps cells below `regPos`, and preserves all registers other than `regI`,
`regV`, `regPos`. -/
theorem wp_writeMapBits {p : Program} {n base M : ℕ} {f : Fin n → Fin n} {st : State}
    (hN : st.regs regN = n) (hBase : st.regs regBase = base)
    (hdisj : base + n ≤ st.regs regPos)
    (hmap : ∀ i : Fin n, st.mem (base + i) = f i)
    (hM : st.regs regPos + (mapBits f).length + n + 2 ≤ M) :
    WP p writeMapBits st (fun o st' c =>
      o = .normal ∧
      st'.regs regPos = st.regs regPos + (mapBits f).length ∧
      (∀ r, r ≠ regI → r ≠ regV → r ≠ regPos → st'.regs r = st.regs r) ∧
      BitsAt st'.mem (st.regs regPos) (mapBits f) ∧
      (∀ x < st.regs regPos, st'.mem x = st.mem x) ∧
      c ≤ (n + 1) * (len n + 3) * (50 * (len M + 1))) := by
  set pos₀ := st.regs regPos with hpos₀
  set L := len M with hL
  let I : ℕ → State → Prop := fun k st' =>
    st'.regs regPos = pos₀ + (prefixMapBits f k).length ∧
    (∀ r, r ≠ regI → r ≠ regV → r ≠ regPos → st'.regs r = st.regs r) ∧
    BitsAt st'.mem pos₀ (prefixMapBits f k) ∧
    (∀ x < pos₀, st'.mem x = st.mem x)
  have hlnM : len n ≤ L := len_mono (by omega)
  refine WP.forUp_const (i := regI) (n := regN) (by decide)
    (by simp [Stmt.Writes, regI, regV, regPos])
    (by simp [Stmt.Writes, regN, regV, regPos])
    I ((len n + 2) * (40 * (L + 1))) ?_ ?_ ?_ ?_
  · rintro k st' v ⟨hp, hr, hb, hbel⟩
    exact ⟨by simp [regPos, regI, hp],
      fun r h1 h2 h3 => by simp [Function.update_of_ne h1, hr r h1 h2 h3], hb, hbel⟩
  · exact ⟨by simp [prefixMapBits_zero, ← hpos₀], fun _ _ _ _ => rfl,
      by rw [prefixMapBits_zero]; exact BitsAt.nil _ _, fun _ _ => rfl⟩
  · rintro k st' hk ⟨hp, hr, hb, hbel⟩ hi hn
    rw [hN] at hk hn
    have hbase' : st'.regs regBase = base := by
      rw [hr regBase (by decide) (by decide) (by decide), hBase]
    have hval : st'.mem (base + k) = f ⟨k, hk⟩ := by
      rw [hbel (base + k) (by omega)]
      exact hmap ⟨k, hk⟩
    have hfv_lt : (f ⟨k, hk⟩ : ℕ) < n := (f ⟨k, hk⟩).isLt
    refine WP.seq' (fun st₁ c₁ =>
        st₁.mem = st'.mem ∧
        st₁.regs regV = f ⟨k, hk⟩ ∧
        st₁.regs regPos = pos₀ + (prefixMapBits f k).length ∧
        (∀ r, r ≠ regI → r ≠ regV → r ≠ regPos → st₁.regs r = st.regs r) ∧
        c₁ ≤ 10 * L + 5) ?_ ?_
    · refine WP.assign_le (M := M) (by
          simp [hbase', hi, hval]; omega) fun c hc => ?_
      simp only [Expr.add_eq, Expr.size_load, Expr.size_bin, Expr.size_reg] at hc
      refine ⟨rfl, rfl, by simp [hbase', hi, hval],
        by simp [regPos, regV, hp],
        fun r h1 h2 h3 => by simp [Function.update_of_ne h2, hr r h1 h2 h3],
        by omega⟩
    rintro st₁ c₁ ⟨hm₁, hv₁, hpos₁, hregs₁, hc₁⟩
    have hsucc := prefixMapBits_succ f hk
    have hlen_next : (prefixMapBits f k).length + (natBits (f ⟨k, hk⟩)).length ≤
        (mapBits f).length := by
      have hle := prefixMapBits_length_le f (k + 1)
      rw [hsucc, List.length_append] at hle
      exact hle
    refine (wp_writeNatBits (p := p) (M := M) hv₁ (by omega) (by omega)).mono ?_
    rintro o st₂ c₂ ⟨rfl, hpos₂, hregs₂, hbits₂, hbelow₂, hc₂⟩
    refine ⟨rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hpos₂, hpos₁, hsucc, List.length_append]; omega
    · intro r h1 h2 h3
      exact (hregs₂ r h3 h2).trans (hregs₁ r h1 h2 h3)
    · rw [hsucc]
      refine BitsAt.append ?_ ?_
      · refine (hm₁ ▸ hb).congr fun x hx₁ hx₂ => hbelow₂ x (by omega)
      · rwa [hpos₁] at hbits₂
    · intro x hx
      rw [hbelow₂ x (by omega), hm₁, hbel x hx]
    · rw [← hL] at hc₂
      have hlf : len (f ⟨k, hk⟩ : ℕ) ≤ len n := len_mono hfv_lt.le
      have hmul : (len (f ⟨k, hk⟩ : ℕ) + 1) * (40 * (L + 1)) ≤ (len n + 1) * (40 * (L + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      have hsucc_mul : (len n + 2) * (40 * (L + 1)) =
          (len n + 1) * (40 * (L + 1)) + 40 * (L + 1) := by ring
      omega
  · rintro st' c ⟨hp, hr, hb, hbel⟩ _ _ hc
    rw [hN, prefixMapBits_self] at hp hb
    rw [hN] at hc
    refine ⟨rfl, hp, hr, hb, hbel, ?_⟩
    have h1 : (len n + 2) * (40 * (L + 1)) + 11 + 6 * len n ≤ (len n + 3) * (50 * (L + 1)) := by
      have : (len n + 3) * (50 * (L + 1)) =
          (len n + 2) * (40 * (L + 1)) + 10 * (len n + 2) * (L + 1) + 50 * (L + 1) := by ring
      nlinarith
    have h2 : 7 + 4 * len n ≤ (len n + 3) * (50 * (L + 1)) := by nlinarith
    have h3 : n * ((len n + 2) * (40 * (L + 1)) + 11 + 6 * len n) ≤
        n * ((len n + 3) * (50 * (L + 1))) := Nat.mul_le_mul_left n h1
    have h4 : (n + 1) * (len n + 3) * (50 * (L + 1)) =
        n * ((len n + 3) * (50 * (L + 1))) + (len n + 3) * (50 * (L + 1)) := by ring
    omega

/-! ### Writing the generators list -/

/-- Write `gens.flatMap (fun g => true :: mapBits g)` from memory starting at `regR + 2 + regN`. -/
def writeGensBits : Stmt :=
  Stmt.forUp regT regK (
    .store (.reg regPos) (.const 1) ;;
    .assign regPos (.reg regPos + 1) ;;
    .assign regBase (.reg regR + 2 + .reg regN + .reg regN * .reg regT) ;;
    writeMapBits
  )

/-- The first `j` generators encoded as bits. -/
def prefixGensBits {n : ℕ} (gens : List (Equiv.Perm (Fin n))) (j : ℕ) : List Bool :=
  (gens.take j).flatMap fun g => true :: mapBits (fun i => g i)

theorem prefixGensBits_zero {n : ℕ} (gens : List (Equiv.Perm (Fin n))) :
    prefixGensBits gens 0 = [] := by
  simp [prefixGensBits]

theorem prefixGensBits_succ {n : ℕ} (gens : List (Equiv.Perm (Fin n))) {j : ℕ}
    (hj : j < gens.length) :
    prefixGensBits gens (j + 1) =
      prefixGensBits gens j ++ (true :: mapBits (fun i => gens.get ⟨j, hj⟩ i)) := by
  unfold prefixGensBits
  have htake : gens.take (j + 1) = gens.take j ++ [gens.get ⟨j, hj⟩] := by
    rw [List.take_add_one]
    have hget : gens[j]? = some (gens.get ⟨j, hj⟩) := by
      rw [List.getElem?_eq_getElem hj]; rfl
    simp [hget]
  rw [htake, List.flatMap_append, List.flatMap_singleton]

theorem prefixGensBits_self {n : ℕ} (gens : List (Equiv.Perm (Fin n))) :
    prefixGensBits gens gens.length = gens.flatMap fun g => true :: mapBits (fun i => g i) := by
  simp [prefixGensBits]

theorem prefixGensBits_length_le {n : ℕ} (gens : List (Equiv.Perm (Fin n))) (j : ℕ) :
    (prefixGensBits gens j).length ≤
      (gens.flatMap fun g => true :: mapBits (fun i => g i)).length := by
  unfold prefixGensBits
  have hsplit := List.take_append_drop j gens
  conv_rhs => rw [← hsplit, List.flatMap_append, List.length_append]
  omega

/-- Specification of `writeGensBits`. -/
theorem wp_writeGensBits {p : Program} {n r M : ℕ} {gens : List (Equiv.Perm (Fin n))}
    {st : State}
    (hN : st.regs regN = n) (hR : st.regs regR = r) (hK : st.regs regK = gens.length)
    (hdisj : r + 2 + n + n * gens.length ≤ st.regs regPos)
    (hgens : ∀ (t : Fin gens.length) (i : Fin n), st.mem (r + 2 + n + n * t + i) = gens.get t i)
    (hM : st.regs regPos + (gens.flatMap fun g => true :: mapBits (fun i => g i)).length +
      n + gens.length + 2 ≤ M) :
    WP p writeGensBits st (fun o st' c =>
      o = .normal ∧
      st'.regs regPos =
        st.regs regPos + (gens.flatMap fun g => true :: mapBits (fun i => g i)).length ∧
      st'.regs regB = st.regs regB ∧
      BitsAt st'.mem (st.regs regPos)
        (gens.flatMap fun g => true :: mapBits (fun i => g i)) ∧
      (∀ x < st.regs regPos, st'.mem x = st.mem x) ∧
      c ≤ (gens.length + 1) * ((n + 2) * (len n + 4) * (50 * (len M + 1)))) := by
  set pos₀ := st.regs regPos with hpos₀
  set L := len M with hL
  set fullBits := gens.flatMap fun g => true :: mapBits (fun i => g i) with hfull
  have hlnM : len n ≤ L := len_mono (by omega)
  have hlkM : len gens.length ≤ L := len_mono (by omega)
  let I : ℕ → State → Prop := fun j st' =>
    st'.regs regPos = pos₀ + (prefixGensBits gens j).length ∧
    st'.regs regN = n ∧
    st'.regs regR = r ∧
    st'.regs regB = st.regs regB ∧
    BitsAt st'.mem pos₀ (prefixGensBits gens j) ∧
    (∀ x < pos₀, st'.mem x = st.mem x)
  refine WP.forUp_const (i := regT) (n := regK) (by decide)
    (by simp [Stmt.Writes, regT, regPos, regBase, regI, regV])
    (by simp [Stmt.Writes, regK, regPos, regBase, regI, regV])
    I ((n + 1) * (len n + 3) * (50 * (L + 1)) + 40 * (L + 1)) ?_ ?_ ?_ ?_
  · rintro j st' v ⟨hp, hn', hr', hb', hbits, hbel⟩
    exact ⟨by simp [regPos, regT, hp], by simp [regN, regT, hn'],
      by simp [regR, regT, hr'], by simp [regB, regT, hb'], hbits, hbel⟩
  · exact ⟨by simp [prefixGensBits_zero, ← hpos₀], hN, hR, rfl,
      by rw [prefixGensBits_zero]; exact BitsAt.nil _ _, fun _ _ => rfl⟩
  · rintro j st' hj ⟨hp, hn', hr', hb', hbits, hbel⟩ ht hk'
    rw [hK] at hj hk'
    have hsucc := prefixGensBits_succ gens hj
    have hlen_next : (prefixGensBits gens j).length +
        (1 + (mapBits (fun i => gens.get ⟨j, hj⟩ i)).length) ≤ fullBits.length := by
      have hle := prefixGensBits_length_le gens (j + 1)
      rw [← hfull, hsucc, List.length_append, List.length_cons] at hle
      omega
    have hbase_le : r + 2 + n + n * j + n ≤ pos₀ := by
      have hmul : n * j + n ≤ n * gens.length := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left n hj
      omega
    -- Step 1: store `1` at `regPos`.
    refine WP.seq' (fun st₁ c₁ =>
        st₁.regs = st'.regs ∧
        st₁.mem = Function.update st'.mem (pos₀ + (prefixGensBits gens j).length) 1 ∧
        c₁ ≤ 6 * L + 3) ?_ ?_
    · refine WP.store_le (M := M) (by simp [hp]; omega) (by simp; omega)
        (by simp [hp]; omega) (by simp; omega) fun c hc => ?_
      simp only [Expr.size_reg, Expr.size_const] at hc
      exact ⟨rfl, rfl, by simp [hp], by omega⟩
    rintro st₁ c₁ ⟨hr₁, hm₁, hc₁⟩
    -- Step 2: increment `regPos`.
    refine WP.seq' (fun st₂ c₂ =>
        st₂.mem = st₁.mem ∧
        st₂.regs = Function.update st'.regs regPos (pos₀ + (prefixGensBits gens j).length + 1) ∧
        c₂ ≤ 8 * L + 4) ?_ ?_
    · refine WP.assign_le (M := M) (by simp [hr₁, hp]; omega) fun c hc => ?_
      simp only [Expr.add_eq, Expr.ofNat_eq, Expr.size_bin, Expr.size_reg, Expr.size_const] at hc
      exact ⟨rfl, rfl, by simp [hr₁, hp], by omega⟩
    rintro st₂ c₂ ⟨hm₂, hr₂, hc₂⟩
    -- Step 3: set `regBase := r + 2 + n + n * j`.
    refine WP.seq' (fun st₃ c₃ =>
        st₃.mem = st₁.mem ∧
        st₃.regs regPos = pos₀ + (prefixGensBits gens j).length + 1 ∧
        st₃.regs regBase = r + 2 + n + n * j ∧
        st₃.regs regN = n ∧
        st₃.regs regR = r ∧
        st₃.regs regB = st.regs regB ∧
        c₃ ≤ 20 * L + 10) ?_ ?_
    · refine WP.assign_le (M := M) (by
          simp [hr₂, regR, regN, regT, regPos, hr', hn', ht]; omega) fun c hc => ?_
      simp only [Expr.add_eq, Expr.mul_eq, Expr.ofNat_eq, Expr.size_bin, Expr.size_reg,
        Expr.size_const] at hc
      refine ⟨rfl, hm₂,
        by simp [hr₂, regBase, regPos],
        by simp [hr₂, regR, regN, regT, regPos, hr', hn', ht],
        by simp [hr₂, regBase, regPos, regN, hn'],
        by simp [hr₂, regBase, regPos, regR, hr'],
        by simp [hr₂, regBase, regPos, regB, hb'],
        by omega⟩
    rintro st₃ c₃ ⟨hm₃, hpos₃, hbase₃, hn₃, hr₃, hb₃, hc₃⟩
    -- Step 4: run `writeMapBits`.
    have hmap₃ : ∀ i : Fin n, st₃.mem ((r + 2 + n + n * j) + i) = gens.get ⟨j, hj⟩ i := by
      intro i
      rw [hm₃, hm₁, Function.update_of_ne (by omega), hbel _ (by omega)]
      exact hgens ⟨j, hj⟩ i
    refine (wp_writeMapBits (p := p) (M := M) (f := fun i => gens.get ⟨j, hj⟩ i)
        hn₃ hbase₃ (by omega) hmap₃ (by omega)).mono ?_
    rintro o st₄ c₄ ⟨rfl, hpos₄, hregs₄, hbits₄, hbelow₄, hc₄⟩
    refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hpos₄, hpos₃, hsucc, List.length_append, List.length_cons]; omega
    · rw [hregs₄ regN (by decide) (by decide) (by decide), hn₃]
    · rw [hregs₄ regR (by decide) (by decide) (by decide), hr₃]
    · rw [hregs₄ regB (by decide) (by decide) (by decide), hb₃]
    · rw [hsucc]
      refine BitsAt.append ?_ (BitsAt.cons ?_ ?_)
      · refine hbits.congr fun x hx₁ hx₂ => ?_
        rw [hbelow₄ x (by omega), hm₃, hm₁, Function.update_of_ne (by omega)]
      · rw [hbelow₄ (pos₀ + (prefixGensBits gens j).length) (by omega), hm₃, hm₁,
          Function.update_self]
        decide
      · simpa [hpos₃, Nat.add_assoc] using hbits₄
    · intro x hx
      rw [hbelow₄ x (by omega), hm₃, hm₁, Function.update_of_ne (by omega), hbel x hx]
    · rw [← hL] at hc₄; omega
  · rintro st' c ⟨hp, _, _, hb', hbits, hbel⟩ _ _ hc
    rw [hK, prefixGensBits_self] at hp hbits
    rw [hK] at hc
    refine ⟨rfl, hp, hb', hbits, hbel, ?_⟩
    set W := (n + 1) * (len n + 3) * (50 * (L + 1))
    set W' := (n + 2) * (len n + 4) * (50 * (L + 1))
    have hW_diff : W + 40 * (L + 1) + 11 + 6 * len gens.length ≤ W' := by
      have : W' = W + (n + 1) * (50 * (L + 1)) + (len n + 4) * (50 * (L + 1)) := by
        dsimp only [W, W']; ring
      nlinarith
    have htail : 7 + 4 * len gens.length ≤ W' := by
      have : 50 * (L + 1) ≤ W' := by
        dsimp only [W']
        exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
      omega
    have hmul : gens.length * (W + 40 * (L + 1) + 11 + 6 * len gens.length) ≤
        gens.length * W' := Nat.mul_le_mul_left _ hW_diff
    rw [Nat.succ_mul]
    omega

end GI.Turing
