/-
The wrapper program `GI.Turing.wrap` and its correctness and cost bound.

Given a program `p` of the log-cost machine, `wrap p` puts a new procedure 0 in front of `p`
(shifted by 1). Procedure 0 recovers `n` from cell 0 (`2 * n * n`), stores `n` into cell 0 so
that memory is an `InputLayout`, calls procedure 1 (`p`), and serializes the output of `p` into
`answerBits` starting after the output of `p`. When `n ≤ 1`, it writes no generators, since the
empty list generates `autGroup G`.

The main theorem `GI.Turing.wrap_run` shows that whenever `p` finishes with a correct output at
cost `T`, `wrap p` finishes on `rawInput (inputBits G H)` with `rawOutput` equal to
`answerBits a` for a correct answer `a`, and both its cost and the output length are at most
`20000 * (T + n + 2) ^ 8`.
-/
module

public import Workspace.Turing.Wrap.WriteBits
public import Workspace.Turing.Wrap.Changed

@[expose] public section

namespace GI.Turing

open GI.Machine GI.Statement

/-! ### The wrapper program -/

/-- Compute `regK`, `regB`, `regPos`, write the leading `1` at `B + 1`, and set `regBase` to
`r + 1`. -/
def writeHeader : Stmt :=
  .cond (.lt (.const 1) (.reg regN))
    (.assign regK (.load (.reg regR + 1 + .reg regN)))
    (.assign regK (.const 0)) ;;
  .assign regB (.reg regR + 2 + .reg regN + .reg regN * .reg regK) ;;
  .assign regPos (.reg regB + 1) ;;
  .store (.reg regPos) (.const 1) ;;
  .assign regPos (.reg regPos + 1) ;;
  .assign regBase (.reg regR + 1)

/-- Write the trailing `0`, store the bit count into cell `B`, and return `B`. -/
def writeFooter : Stmt :=
  .store (.reg regPos) (.const 0) ;;
  .assign regPos (.reg regPos + 1) ;;
  .store (.reg regB) (.reg regPos - (.reg regB + 1)) ;;
  .ret (.reg regB)

/-- Serialize the output of `p` at `regR` into `answerBits` at a fresh address `B`, store the
number of bits at `B`, and return `B`. -/
def writeOutput : Stmt :=
  .cond (.load (.reg regR))
    (writeHeader ;; writeMapBits ;; writeGensBits ;; writeFooter)
    (.assign regB (.reg regR + 1) ;;
     .store (.reg regB + 1) (.const 0) ;;
     .store (.reg regB) (.const 1) ;;
     .ret (.reg regB))

/-- Procedure 0 of `wrap p`. -/
def wrapMain : Stmt :=
  findN ;;
  .store (.const 0) (.reg regN) ;;
  .call regR 1 [] ;;
  writeOutput

/-- The wrapper program: procedure 0 reads the input bits, runs `p`, and writes the output bits. -/
def wrap (p : Program) : Program :=
  ⟨wrapMain :: p.shifted 1⟩

/-- `wrap p` embeds `p` at offset 1. -/
theorem embeds_wrap (p : Program) : Embeds (wrap p) p 1 :=
  Embeds.of_append (A := [wrapMain]) (B := []) (by simp [wrap])

/-! ### Correctness of `writeHeader`, `writeFooter`, and `writeOutput` -/

/-- Specification of `writeHeader`. -/
private theorem wp_writeHeader {p : Program} {n r k M : ℕ} {st : State}
    (hN : st.regs regN = n) (hR : st.regs regR = r)
    (hK_big : 1 < n → st.mem (r + 1 + n) = k)
    (hK_small : n ≤ 1 → k = 0)
    (hM : r + 2 + n + n * k + n + k + 4 ≤ M) :
    let B := r + 2 + n + n * k
    WP p writeHeader st (fun o st' c =>
      o = .normal ∧
      st'.mem = Function.update st.mem (B + 1) 1 ∧
      st'.regs regN = n ∧ st'.regs regR = r ∧ st'.regs regK = k ∧
      st'.regs regB = B ∧ st'.regs regPos = B + 2 ∧ st'.regs regBase = r + 1 ∧
      c ≤ 80 * (len M + 1)) := by
  intro B
  set L := len M with hL
  -- Step 1: set `regK := k`.
  refine WP.seq' (fun st₁ c₁ =>
      st₁.mem = st.mem ∧
      st₁.regs regN = n ∧ st₁.regs regR = r ∧ st₁.regs regK = k ∧
      c₁ ≤ 20 * L + 11) ?_ ?_
  · have hcond_cost : (evalExpr st (.lt (.const 1) (.reg regN))).2 ≤ 6 * L + 3 := by
      have hv : (Expr.lt (.const 1) (.reg regN)).ValsLe st M := by
        simp [Expr.lt, hN]; omega
      have hc := Expr.cost_le hv
      have hsize : (Expr.lt (.const 1) (.reg regN)).size = 3 := rfl
      rw [hsize] at hc
      omega
    by_cases hn1 : 1 < n
    · refine WP.cond_true (by simp [Expr.lt, hN, hn1]) ?_
      refine WP.assign_le (M := M) (by simp [hR, hN, hK_big hn1]; omega) fun c hc => ?_
      have hsize : (Expr.load (.reg regR + 1 + .reg regN)).size = 6 := rfl
      rw [hsize] at hc
      refine ⟨rfl, rfl, by simp [regN, regK, hN], by simp [regR, regK, hR],
        by simp [hR, hN, hK_big hn1], by omega⟩
    · have hk0 : k = 0 := hK_small (by omega)
      refine WP.cond_false (by simp [Expr.lt, hN, hn1]) ?_
      refine WP.assign_le (M := M) (by simp) fun c hc => ?_
      have hsize : (Expr.const 0).size = 1 := rfl
      rw [hsize] at hc
      refine ⟨rfl, rfl, by simp [regN, regK, hN], by simp [regR, regK, hR],
        by simp [hk0], by omega⟩
  rintro st₁ c₁ ⟨hm₁, hN₁, hR₁, hK₁, hc₁⟩
  -- Step 2: `regB := B`.
  refine WP.seq' (fun st₂ c₂ =>
      st₂.mem = st.mem ∧
      st₂.regs regN = n ∧ st₂.regs regR = r ∧ st₂.regs regK = k ∧
      st₂.regs regB = B ∧ c₂ ≤ 20 * L + 10) ?_ ?_
  · refine WP.assign_le (M := M) (by simp [hR₁, hN₁, hK₁]; omega) fun c hc => ?_
    have hsize : (Expr.reg regR + 2 + .reg regN + .reg regN * .reg regK).size = 9 := rfl
    rw [hsize] at hc
    refine ⟨rfl, hm₁, by simp [regN, regB, hN₁], by simp [regR, regB, hR₁],
      by simp [regK, regB, hK₁], by simp [hR₁, hN₁, hK₁, B], by omega⟩
  rintro st₂ c₂ ⟨hm₂, hN₂, hR₂, hK₂, hB₂, hc₂⟩
  -- Step 3: `regPos := B + 1`.
  refine WP.seq' (fun st₃ c₃ =>
      st₃.mem = st.mem ∧
      st₃.regs regN = n ∧ st₃.regs regR = r ∧ st₃.regs regK = k ∧
      st₃.regs regB = B ∧ st₃.regs regPos = B + 1 ∧ c₃ ≤ 8 * L + 4) ?_ ?_
  · refine WP.assign_le (M := M) (by simp [hB₂]; omega) fun c hc => ?_
    have hsize : (Expr.reg regB + 1).size = 3 := rfl
    rw [hsize] at hc
    refine ⟨rfl, hm₂, by simp [regN, regPos, hN₂], by simp [regR, regPos, hR₂],
      by simp [regK, regPos, hK₂], by simp [regB, regPos, hB₂], by simp [hB₂], by omega⟩
  rintro st₃ c₃ ⟨hm₃, hN₃, hR₃, hK₃, hB₃, hPos₃, hc₃⟩
  -- Step 4: store `1` at `B + 1`.
  refine WP.seq' (fun st₄ c₄ =>
      st₄.regs = st₃.regs ∧
      st₄.mem = Function.update st.mem (B + 1) 1 ∧ c₄ ≤ 6 * L + 3) ?_ ?_
  · refine WP.store_le (M := M) (by simp [hPos₃]; omega) (by simp; omega)
      (by simp [hPos₃]; omega) (by simp; omega) fun c hc => ?_
    simp only [Expr.size_reg, Expr.size_const] at hc
    exact ⟨rfl, rfl, by simp [hm₃, hPos₃], by omega⟩
  rintro st₄ c₄ ⟨hr₄, hm₄, hc₄⟩
  -- Step 5: `regPos := B + 2`.
  refine WP.seq' (fun st₅ c₅ =>
      st₅.mem = st₄.mem ∧
      st₅.regs regN = n ∧ st₅.regs regR = r ∧ st₅.regs regK = k ∧
      st₅.regs regB = B ∧ st₅.regs regPos = B + 2 ∧ c₅ ≤ 8 * L + 4) ?_ ?_
  · refine WP.assign_le (M := M) (by simp [hr₄, hPos₃]; omega) fun c hc => ?_
    have hsize : (Expr.reg regPos + 1).size = 3 := rfl
    rw [hsize] at hc
    refine ⟨rfl, rfl, by simp [hr₄, regN, regPos, hN₃], by simp [hr₄, regR, regPos, hR₃],
      by simp [hr₄, regK, regPos, hK₃], by simp [hr₄, regB, regPos, hB₃],
      by simp [hr₄, hPos₃], by omega⟩
  rintro st₅ c₅ ⟨hm₅, hN₅, hR₅, hK₅, hB₅, hPos₅, hc₅⟩
  -- Step 6: `regBase := r + 1`.
  refine WP.assign_le (M := M) (by simp [hR₅]; omega) fun c₆ hc₆ => ?_
  have hsize : (Expr.reg regR + 1).size = 3 := rfl
  rw [hsize] at hc₆
  refine ⟨rfl, hm₅.trans hm₄, by simp [regN, regBase, hN₅], by simp [regR, regBase, hR₅],
    by simp [regK, regBase, hK₅], by simp [regB, regBase, hB₅],
    by simp [regPos, regBase, hPos₅], by simp [hR₅], by omega⟩

/-- Specification of `writeFooter`. -/
private theorem wp_writeFooter {p : Program} {B M : ℕ} {bs : List Bool} {st : State}
    (hB : st.regs regB = B) (hPos : st.regs regPos = B + 1 + bs.length)
    (hbits : BitsAt st.mem (B + 1) bs) (hM : B + bs.length + 2 ≤ M) :
    WP p writeFooter st (fun o st' c =>
      o = .returned B ∧
      rawOutput st'.mem B = bs ++ [false] ∧
      st'.mem B = bs.length + 1 ∧
      c ≤ 40 * (len M + 1)) := by
  set L := len M with hL
  -- Step 1: store terminating `0` at `B + 1 + bs.length`.
  refine WP.seq' (fun st₁ c₁ =>
      st₁.regs = st.regs ∧
      BitsAt st₁.mem (B + 1) (bs ++ [false]) ∧
      c₁ ≤ 6 * L + 3) ?_ ?_
  · refine WP.store_le (M := M) (by simp [hPos]; omega) (by simp)
      (by simp [hPos]; omega) (by simp) fun c hc => ?_
    simp only [Expr.size_reg, Expr.size_const] at hc
    refine ⟨rfl, rfl, ?_, by omega⟩
    refine BitsAt.append ?_ ?_
    · refine hbits.congr fun x hx₁ hx₂ => ?_
      dsimp only
      rw [show (evalExpr st (.reg regPos)).1 = B + 1 + bs.length by simp [hPos],
        Function.update_of_ne (by omega)]
    · refine BitsAt.singleton ?_
      simp [hPos]
  rintro st₁ c₁ ⟨hr₁, hbits₁, hc₁⟩
  -- Step 2: `regPos := B + 1 + bs.length + 1`.
  refine WP.seq' (fun st₂ c₂ =>
      st₂.mem = st₁.mem ∧
      st₂.regs regB = B ∧ st₂.regs regPos = B + 1 + bs.length + 1 ∧ c₂ ≤ 8 * L + 4) ?_ ?_
  · refine WP.assign_le (M := M) (by simp [hr₁, hPos]; omega) fun c hc => ?_
    have hsize : (Expr.reg regPos + 1).size = 3 := rfl
    rw [hsize] at hc
    refine ⟨rfl, rfl, by simp [hr₁, regB, regPos, hB], by simp [hr₁, hPos], by omega⟩
  rintro st₂ c₂ ⟨hm₂, hB₂, hPos₂, hc₂⟩
  -- Step 3: store `bs.length + 1` into cell `B`.
  refine WP.seq' (fun st₃ c₃ =>
      st₃.regs = st₂.regs ∧
      st₃.mem B = bs.length + 1 ∧
      BitsAt st₃.mem (B + 1) (bs ++ [false]) ∧
      c₃ ≤ 14 * L + 7) ?_ ?_
  · refine WP.store_le (M := M) (by simp [hB₂]; omega)
      (by simp [hPos₂, hB₂]; omega)
      (by simp [hB₂]; omega)
      (by simp [hPos₂, hB₂]; omega) fun c hc => ?_
    have hsize : (Expr.reg regPos - (.reg regB + 1)).size = 5 := rfl
    simp only [Expr.size_reg, hsize] at hc
    refine ⟨rfl, rfl, by simp [hB₂, hPos₂]; omega, ?_, by omega⟩
    refine (hm₂ ▸ hbits₁).congr fun x hx₁ _ => ?_
    dsimp only
    rw [show (evalExpr st₂ (.reg regB)).1 = B by simp [hB₂],
      Function.update_of_ne (by omega)]
  rintro st₃ c₃ ⟨hr₃, hmB₃, hbits₃, hc₃⟩
  -- Step 4: return `B`.
  refine WP.ret_le (M := M) (by simp [hr₃, hB₂]; omega) fun c₄ hc₄ => ?_
  simp only [Expr.size_reg] at hc₄
  have hret : (evalExpr st₃ (.reg regB)).1 = B := by simp [hr₃, hB₂]
  rw [hret]
  refine ⟨rfl, ?_, hmB₃, by omega⟩
  refine rawOutput_eq_of_bitsAt ?_ hbits₃
  simpa using hmB₃

/-- The negative branch of `writeOutput` (when `mem r = 0`). -/
private theorem wp_writeOutput_false {p : Program} {n r : ℕ} {G H : SimpleGraph (Fin n)}
    {st : State} (hR : st.regs regR = r) (hm0 : st.mem r = 0) :
    WP p writeOutput st (fun o st' c =>
      o = .returned (r + 1) ∧
      rawOutput st'.mem (r + 1) = answerBits (G := G) (H := H) none ∧
      st'.mem (r + 1) = 1 ∧
      c ≤ 50 * (len (r + 2) + 1)) := by
  set M := r + 2 with hM
  set L := len M with hL
  have htest_val : (evalExpr st (.load (.reg regR))).1 = 0 := by simp [hR, hm0]
  have htest_cost : (evalExpr st (.load (.reg regR))).2 ≤ 4 * L + 2 := by
    have hv : (Expr.load (.reg regR)).ValsLe st M := by simp [hR, hm0, hM]
    have hc := Expr.cost_le hv
    simp only [Expr.size_load, Expr.size_reg] at hc
    omega
  refine WP.cond_false htest_val ?_
  refine WP.seq' (fun st₁ c₁ =>
      st₁.mem = st.mem ∧ st₁.regs regB = r + 1 ∧ c₁ ≤ 8 * L + 4) ?_ ?_
  · refine WP.assign_le (M := M) (by simp [hR, hM]) fun c hc => ?_
    have hsize : (Expr.reg regR + 1).size = 3 := rfl
    rw [hsize] at hc
    exact ⟨rfl, rfl, by simp [hR], by omega⟩
  rintro st₁ c₁ ⟨_, hB₁, hc₁⟩
  refine WP.seq' (fun st₂ c₂ =>
      st₂.regs = st₁.regs ∧ st₂.mem (r + 2) = 0 ∧ c₂ ≤ 10 * L + 5) ?_ ?_
  · refine WP.store_le (M := M) (by simp [hB₁, hM]) (by simp)
      (by simp [hB₁, hM]) (by simp) fun c hc => ?_
    have hsize : (Expr.reg regB + 1).size = 3 := rfl
    simp only [hsize, Expr.size_const] at hc
    exact ⟨rfl, rfl, by simp [hB₁], by omega⟩
  rintro st₂ c₂ ⟨hr₂, hm₂, hc₂⟩
  refine WP.seq' (fun st₃ c₃ =>
      st₃.regs = st₁.regs ∧ st₃.mem (r + 1) = 1 ∧ st₃.mem (r + 2) = 0 ∧ c₃ ≤ 6 * L + 3) ?_ ?_
  · refine WP.store_le (M := M) (by simp [hr₂, hB₁, hM]) (by simp [hM])
      (by simp [hr₂, hB₁, hM]) (by simp [hM]) fun c hc => ?_
    simp only [Expr.size_reg, Expr.size_const] at hc
    refine ⟨rfl, hr₂, by simp [hr₂, hB₁], ?_, by omega⟩
    dsimp only
    rw [show (evalExpr st₂ (.reg regB)).1 = r + 1 by simp [hr₂, hB₁],
      Function.update_of_ne (by omega)]
    exact hm₂
  rintro st₃ c₃ ⟨hr₃, hm₃1, hm₃2, hc₃⟩
  refine WP.ret_le (M := M) (by simp [hr₃, hB₁, hM]) fun c₄ hc₄ => ?_
  simp only [Expr.size_reg] at hc₄
  have hret : (evalExpr st₃ (.reg regB)).1 = r + 1 := by simp [hr₃, hB₁]
  rw [hret]
  refine ⟨rfl, ?_, hm₃1, by omega⟩
  refine rawOutput_eq_of_bitsAt hm₃1 (BitsAt.singleton ?_)
  rw [show r + 1 + 1 = r + 2 by omega, hm₃2]
  decide

/-- The positive branch of `writeOutput` (when `mem r = 1`). -/
private theorem wp_writeOutput_true {p : Program} {n r : ℕ} {G H : SimpleGraph (Fin n)}
    {σ : G ≃g H} {gens : List (Equiv.Perm (Fin n))} {st : State}
    (hN : st.regs regN = n) (hR : st.regs regR = r) (hm1 : st.mem r = 1)
    (hσ : ∀ i : Fin n, st.mem (r + 1 + i) = σ i)
    (hK_big : 1 < n → st.mem (r + 1 + n) = gens.length)
    (hK_small : n ≤ 1 → gens = [])
    (hgens : ∀ (t : Fin gens.length) (i : Fin n),
      st.mem (r + 2 + n + n * t + i) = gens.get t i) :
    let B := r + 2 + n + n * gens.length
    let Lbits := (answerBits (some (σ, gens))).length
    let M := B + Lbits + n + gens.length + 4
    WP p writeOutput st (fun o st' c =>
      o = .returned B ∧
      rawOutput st'.mem B = answerBits (some (σ, gens)) ∧
      st'.mem B = Lbits ∧
      c ≤ (gens.length + 3) * ((n + 2) * (len n + 4) * (50 * (len M + 1)))) := by
  intro B Lbits M
  set L := len M with hL
  set mapB := mapBits (fun i => σ i) with hmapB
  set genB := gens.flatMap fun g => true :: mapBits (fun i => g i) with hgenB
  have hLbits_eq : Lbits = 2 + mapB.length + genB.length := by
    simp only [Lbits, answerBits, hmapB, hgenB, List.length_append, List.length_cons,
      List.length_nil]
    omega
  have htest_val : (evalExpr st (.load (.reg regR))).1 ≠ 0 := by simp [hR, hm1]
  have htest_cost : (evalExpr st (.load (.reg regR))).2 ≤ 4 * L + 2 := by
    have hv : (Expr.load (.reg regR)).ValsLe st M := by simp [hR, hm1, M, B]; omega
    have hc := Expr.cost_le hv
    simp only [Expr.size_load, Expr.size_reg] at hc
    omega
  refine WP.cond_true htest_val ?_
  -- Step 1: `writeHeader`.
  refine WP.seq' (fun st₁ c₁ =>
      st₁.mem = Function.update st.mem (B + 1) 1 ∧
      st₁.regs regN = n ∧ st₁.regs regR = r ∧ st₁.regs regK = gens.length ∧
      st₁.regs regB = B ∧ st₁.regs regPos = B + 2 ∧ st₁.regs regBase = r + 1 ∧
      c₁ ≤ 80 * (L + 1)) ?_ ?_
  · exact (wp_writeHeader (p := p) (M := M) hN hR hK_big
      (fun hn => by simp [hK_small hn]) (by dsimp only [M, B]; omega))
  rintro st₁ c₁ ⟨hm₁, hN₁, hR₁, hK₁, hB₁, hPos₁, hBase₁, hc₁⟩
  -- Step 2: `writeMapBits` for `σ`.
  have hmap₁ : ∀ i : Fin n, st₁.mem (r + 1 + i) = σ i := by
    intro i
    rw [hm₁, Function.update_of_ne (by have := i.isLt; omega)]
    exact hσ i
  refine WP.seq' (fun st₂ c₂ =>
      st₂.regs regN = n ∧ st₂.regs regR = r ∧ st₂.regs regK = gens.length ∧
      st₂.regs regB = B ∧ st₂.regs regPos = B + 2 + mapB.length ∧
      BitsAt st₂.mem (B + 1) (true :: mapB) ∧
      (∀ x < B + 1, st₂.mem x = st.mem x) ∧
      c₂ ≤ (n + 1) * (len n + 3) * (50 * (L + 1))) ?_ ?_
  · refine (wp_writeMapBits (p := p) (M := M) (f := fun i => σ i)
        hN₁ hBase₁ (by omega) hmap₁ (by rw [hPos₁, ← hmapB]; omega)).mono ?_
    rintro o st₂ c₂ ⟨rfl, hPos₂, hregs₂, hbits₂, hbelow₂, hc₂⟩
    refine ⟨rfl,
      by rw [hregs₂ regN (by decide) (by decide) (by decide), hN₁],
      by rw [hregs₂ regR (by decide) (by decide) (by decide), hR₁],
      by rw [hregs₂ regK (by decide) (by decide) (by decide), hK₁],
      by rw [hregs₂ regB (by decide) (by decide) (by decide), hB₁],
      by rw [hPos₂, hPos₁], ?_, ?_, hc₂⟩
    · refine BitsAt.cons ?_ (by simpa [hPos₁] using hbits₂)
      rw [hbelow₂ (B + 1) (by omega), hm₁, Function.update_self]
      decide
    · intro x hx
      rw [hbelow₂ x (by omega), hm₁, Function.update_of_ne (by omega)]
  rintro st₂ c₂ ⟨hN₂, hR₂, hK₂, hB₂, hPos₂, hbits₂, hbelow₂, hc₂⟩
  -- Step 3: `writeGensBits` for `gens`.
  have hgens₂ : ∀ (t : Fin gens.length) (i : Fin n),
      st₂.mem (r + 2 + n + n * t + i) = gens.get t i := by
    intro t i
    have hlt := permsAt_cell_lt t i
    rw [hbelow₂ _ (by omega)]
    exact hgens t i
  refine WP.seq' (fun st₃ c₃ =>
      st₃.regs regB = B ∧ st₃.regs regPos = B + 1 + (true :: mapB ++ genB).length ∧
      BitsAt st₃.mem (B + 1) (true :: mapB ++ genB) ∧
      c₃ ≤ (gens.length + 1) * ((n + 2) * (len n + 4) * (50 * (L + 1)))) ?_ ?_
  · refine (wp_writeGensBits (p := p) (M := M) hN₂ hR₂ hK₂ (by omega) hgens₂
        (by rw [hPos₂, ← hgenB]; omega)).mono ?_
    rintro o st₃ c₃ ⟨rfl, hPos₃, hB₃, hbits₃, hbelow₃, hc₃⟩
    refine ⟨rfl, hB₃.trans hB₂, ?_, ?_, hc₃⟩
    · rw [hPos₃, hPos₂, ← hgenB]
      simp only [List.length_cons, List.length_append]
      omega
    · rw [List.cons_append]
      have hbits₃' : BitsAt st₃.mem ((B + 1) + (true :: mapB).length) genB := by
        rw [show (B + 1) + (true :: mapB).length = B + 2 + mapB.length by simp; omega]
        rwa [hPos₂, ← hgenB] at hbits₃
      exact BitsAt.append
        (hbits₂.congr fun x hx₁ hx₂ => hbelow₃ x (by simp at hx₂; omega)) hbits₃'
  rintro st₃ c₃ ⟨hB₃, hPos₃, hbits₃, hc₃⟩
  -- Step 4: `writeFooter`.
  have hMfoot : B + (true :: mapB ++ genB).length + 2 ≤ M := by
    simp only [List.length_cons, List.length_append, M]; omega
  refine (wp_writeFooter (p := p) (M := M) hB₃ hPos₃ hbits₃ hMfoot).mono ?_
  rintro o st₄ c₄ ⟨rfl, hraw₄, hmB₄, hc₄⟩
  have hlen_ans : (true :: mapB ++ genB).length + 1 = Lbits := by
    simp only [List.length_cons, List.length_append]; omega
  refine ⟨rfl, hraw₄, hmB₄.trans hlen_ans, ?_⟩
  set W := (n + 2) * (len n + 4) * (50 * (L + 1))
  have hW_ge : 400 * (L + 1) ≤ W := by
    have h1 : 2 * 4 ≤ (n + 2) * (len n + 4) := Nat.mul_le_mul (by omega) (by omega)
    have h2 := Nat.mul_le_mul_right (50 * (L + 1)) h1
    dsimp only [W]; omega
  have hmap_le : (n + 1) * (len n + 3) * (50 * (L + 1)) ≤ W :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  have htot : (gens.length + 3) * W = (gens.length + 1) * W + W + W := by ring
  omega

/-! ### Arithmetic helpers and full run of `wrap p` -/

/-- Pure arithmetic bound for the positive branch of `wrap_run`. -/
private theorem wrap_pos_cost_bound {T n r k Lbits c₁ c₂ c₄ : ℕ}
    (hlen_r : len r ≤ T)
    (hk : k ≤ T + 2 * n * n + 1)
    (hLbits : Lbits ≤ 2 + (k + 1) * (1 + n * (2 * len n + 1)))
    (hc₁ : c₁ ≤ 90 * (T + n + 2) ^ 3)
    (hc₂ : c₂ ≤ 12 * (T + n + 2))
    (hc₄ : c₄ ≤ (k + 3) * ((n + 2) * (len n + 4) *
      (50 * (len (r + 2 + n + n * k + Lbits + n + k + 4) + 1)))) :
    c₁ + (c₂ + (T + c₄ + 1) + 1) + 1 + 1 ≤ 20000 * (T + n + 2) ^ 8 ∧
    Lbits ≤ 20000 * (T + n + 2) ^ 8 := by
  set U := T + n + 2
  have hU2 : 2 ≤ U := by omega
  have hU12 : U ≤ U ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left U (by omega)
  have hU23 : U ^ 2 ≤ U ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hU34 : U ^ 3 ≤ U ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hU48 : U ^ 4 ≤ U ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hU24 : U ^ 2 ≤ U ^ 4 := le_trans hU23 hU34
  have hU14 : U ≤ U ^ 4 := le_trans hU12 hU24
  have hU2_ge4 : 4 ≤ U ^ 2 := by
    have : 2 ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left hU2 2
    omega
  have hln : len n ≤ U := le_trans (len_le_self n) (by omega)
  have hnn : n * n ≤ U ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h2nn : 2 * n * n = 2 * (n * n) := by ring
  have hk_le : k ≤ 3 * U ^ 2 := by omega
  have hLbits_le : Lbits ≤ 18 * U ^ 4 := by
    have h2 : k + 1 ≤ 4 * U ^ 2 := by omega
    have h3a : n * (2 * len n + 1) ≤ U * (2 * U + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3b : U * (2 * U + 1) = 2 * U ^ 2 + U := by ring
    have h3 : 1 + n * (2 * len n + 1) ≤ 4 * U ^ 2 := by omega
    have h4 : (k + 1) * (1 + n * (2 * len n + 1)) ≤ (4 * U ^ 2) * (4 * U ^ 2) :=
      Nat.mul_le_mul h2 h3
    have h5 : (4 * U ^ 2) * (4 * U ^ 2) = 16 * U ^ 4 := by ring
    omega
  have hlenM_le : len (r + 2 + n + n * k + Lbits + n + k + 4) + 1 ≤ 31 * U ^ 4 := by
    set X := 2 + n + n * k + Lbits + n + k + 4
    have hM_eq : r + 2 + n + n * k + Lbits + n + k + 4 = r + X := by dsimp only [X]; omega
    have hlen1 : len (r + X) ≤ len r + len X + 1 := len_add_le_add r X
    have hlenX : len X ≤ X := len_le_self X
    have hnk : n * k ≤ 3 * U ^ 3 := by
      have h1 := Nat.mul_le_mul (show n ≤ U by omega) hk_le
      have h2 : U * (3 * U ^ 2) = 3 * U ^ 3 := by ring
      omega
    have hX_le : X ≤ 28 * U ^ 4 := by dsimp only [X]; omega
    rw [hM_eq]
    omega
  have hc4_le : c₄ ≤ 18600 * U ^ 8 := by
    have h1 : k + 3 ≤ 4 * U ^ 2 := by omega
    have h2 : n + 2 ≤ U := by omega
    have h3 : len n + 4 ≤ 3 * U := by omega
    have h4 : 50 * (len (r + 2 + n + n * k + Lbits + n + k + 4) + 1) ≤ 1550 * U ^ 4 := by omega
    have hp1 : (n + 2) * (len n + 4) ≤ U * (3 * U) := Nat.mul_le_mul h2 h3
    have hp2 : (n + 2) * (len n + 4) *
        (50 * (len (r + 2 + n + n * k + Lbits + n + k + 4) + 1)) ≤
        (U * (3 * U)) * (1550 * U ^ 4) := Nat.mul_le_mul hp1 h4
    have hp3 : (k + 3) * ((n + 2) * (len n + 4) *
        (50 * (len (r + 2 + n + n * k + Lbits + n + k + 4) + 1))) ≤
        (4 * U ^ 2) * ((U * (3 * U)) * (1550 * U ^ 4)) := Nat.mul_le_mul h1 hp2
    have heq : (4 * U ^ 2) * ((U * (3 * U)) * (1550 * U ^ 4)) = 18600 * U ^ 8 := by ring
    omega
  have hU38 : U ^ 3 ≤ U ^ 8 := le_trans hU34 hU48
  have hU18 : U ≤ U ^ 8 := le_trans hU14 hU48
  exact ⟨by omega, by omega⟩

/-- If `p` finishes on the `InputLayout` of `G` and `H` with a correct output at cost `T`, then
`wrap p` finishes on `rawInput (inputBits G H)` with `rawOutput` equal to `answerBits a` for a
correct answer `a`, and both its cost and the output length are at most `20000 * (T + n + 2) ^ 8`.
-/
theorem wrap_run {p : Program} {n : ℕ} {G H : SimpleGraph (Fin n)}
    {fuel r T : ℕ} {mem' : ℕ → ℕ}
    (hrun : run p (Function.update (rawInput (inputBits G H)) 0 n) fuel = some (mem', r, T))
    (hout : CorrectOutput G H mem' r) :
    ∃ fuel' mem_w B T_w, ∃ a : Answer G H,
      run (wrap p) (rawInput (inputBits G H)) fuel' = some (mem_w, B, T_w) ∧
      IsCorrectAnswer G H a ∧
      rawOutput mem_w B = answerBits a ∧
      T_w ≤ 20000 * (T + n + 2) ^ 8 ∧
      mem_w B ≤ 20000 * (T + n + 2) ^ 8 := by
  set U := T + n + 2 with hU
  have hU2 : 2 ≤ U := by omega
  have hU12 : U ≤ U ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left U (by omega)
  have hU23 : U ^ 2 ≤ U ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hU38 : U ^ 3 ≤ U ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hU18 : U ≤ U ^ 8 := le_trans (le_trans hU12 hU23) hU38
  have hU2_ge4 : 4 ≤ U ^ 2 := by
    have : 2 ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left hU2 2
    omega
  -- Unpack the run of `p` and embed it in `wrap p` at offset 1.
  obtain ⟨body, o_p, st_p, c_p, hbody, hr_p, hmem_p, hret_p, hT_eq, hlen_r, _⟩ := run_spec hrun
  have hemb : Embeds (wrap p) p 1 := embeds_wrap p
  have hbody1 : (wrap p).procs[1]? = some (body.shift 1) := hemb 0 body hbody
  have hr_p1 : Runs (wrap p) (body.shift 1)
      { mem := Function.update (rawInput (inputBits G H)) 0 n, regs := fun _ => 0 }
      o_p st_p c_p := hr_p.shift hemb
  -- Run `wrapMain` from the initial state of `run (wrap p)`.
  let st0 : State := { mem := rawInput (inputBits G H), regs := fun _ => 0 }
  have h0 : st0.mem 0 = 2 * n * n := by
    simp [st0, rawInput, inputBits_length]
  have hmain : WP (wrap p) wrapMain st0 (fun o st_f c =>
      ∃ B, ∃ a : Answer G H,
        o = .returned B ∧ IsCorrectAnswer G H a ∧
        rawOutput st_f.mem B = answerBits a ∧
        c + 1 ≤ 20000 * U ^ 8 ∧ st_f.mem B ≤ 20000 * U ^ 8) := by
    -- Step 1: `findN`.
    refine WP.seq' (fun st₁ c₁ =>
        st₁.mem = rawInput (inputBits G H) ∧ st₁.regs regN = n ∧ c₁ ≤ 90 * U ^ 3) ?_ ?_
    · refine (wp_findN (p := wrap p) h0).mono ?_
      rintro o st₁ c₁ ⟨rfl, hm₁, hN₁, hc₁⟩
      refine ⟨rfl, hm₁, hN₁, ?_⟩
      have hlen2 : len (2 * n * n + 2) ≤ 3 * U ^ 2 := by
        have h1 : len (2 * n * n + 2) ≤ 2 * n * n + 2 := len_le_self _
        have h2 : n * n ≤ U ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
        have h3 : 2 * n * n = 2 * (n * n) := by ring
        omega
      have h1 : 25 * len (2 * n * n + 2) + 15 ≤ 90 * U ^ 2 := by omega
      have h2 : (n + 1) * (25 * len (2 * n * n + 2) + 15) ≤ U * (90 * U ^ 2) :=
        Nat.mul_le_mul (by omega) h1
      have h3 : U * (90 * U ^ 2) = 90 * U ^ 3 := by ring
      omega
    rintro st₁ c₁ ⟨hm₁, hN₁, hc₁⟩
    -- Step 2: `.store (.const 0) (.reg regN)`.
    refine WP.seq' (fun st₂ c₂ =>
        st₂.mem = Function.update (rawInput (inputBits G H)) 0 n ∧
        st₂.regs regN = n ∧ c₂ ≤ 12 * U) ?_ ?_
    · refine WP.store_le (M := n) (by simp) (by simp [hN₁]) (by simp) (by simp [hN₁])
        fun c hc => ?_
      simp only [Expr.size_const, Expr.size_reg] at hc
      have hln : len n ≤ n := len_le_self n
      exact ⟨rfl, by simp [hm₁, hN₁], hN₁, by omega⟩
    rintro st₂ c₂ ⟨hm₂, hN₂, hc₂⟩
    -- Step 3: `.call regR 1 []`.
    refine WP.seq' (fun st₃ c₃ =>
        st₃.mem = mem' ∧ st₃.regs regN = n ∧ st₃.regs regR = r ∧ c₃ = T) ?_ ?_
    · refine WP.call hbody1 ?_
      have hargs0 : (fun i => (evalArgs st₂ []).1.getD i 0) = (fun _ => 0) := by
        funext i; simp
      rw [hm₂, hargs0]
      refine WP.intro hr_p1 ?_
      refine ⟨rfl, hmem_p, by simp [regN, regR, hN₂], by simp [hret_p], ?_⟩
      simp [hT_eq]
    rintro st₃ c₃ ⟨hm₃, hN₃, hR₃, hc₃⟩
    -- Step 4: `writeOutput`.
    rcases hout with ⟨hm0, hempty⟩ | ⟨hm1, σ, hσ, gens₀, hglen₀, hgens₀, hclos₀⟩
    · -- Case `mem' r = 0`: not isomorphic.
      refine (wp_writeOutput_false (p := wrap p) (G := G) (H := H) hR₃ (hm₃ ▸ hm0)).mono ?_
      rintro o st₄ c₄ ⟨rfl, hraw, hmB, hc₄⟩
      refine ⟨r + 1, none, rfl, hempty, hraw, ?_, ?_⟩
      · have hlr2 : len (r + 2) + 1 ≤ 2 * U := by
          have h1 : len (r + 2) ≤ len r + len 2 + 1 := len_add_le_add r 2
          have h2 : len 2 = 2 := by decide
          omega
        omega
      · omega
    · -- Case `mem' r = 1`: isomorphic.
      -- Use `gens₀` when `2 ≤ n` and `[]` when `n ≤ 1`.
      obtain ⟨gens, hK_big, hK_small, hgens_mem, hclos, hgens_le⟩ :
          ∃ gens : List (Equiv.Perm (Fin n)),
            (1 < n → st₃.mem (r + 1 + n) = gens.length) ∧
            (n ≤ 1 → gens = []) ∧
            (∀ (t : Fin gens.length) (i : Fin n),
              st₃.mem (r + 2 + n + n * t + i) = gens.get t i) ∧
            Subgroup.closure {g | g ∈ gens} = autGroup G ∧
            gens.length ≤ T + 2 * n * n + 1 := by
        by_cases hn : 1 < n
        · exact ⟨gens₀, fun _ => by rw [hm₃, hglen₀], fun h => absurd hn (by omega),
            fun t i => by rw [hm₃]; exact hgens₀ t i, hclos₀,
            run_gens_length_le (by omega) (inputLayout_update_rawInput G H) hrun gens₀ hgens₀⟩
        · exact ⟨[], fun h => absurd h hn, fun _ => rfl,
            fun t => absurd t.isLt (Nat.not_lt_zero _),
            autGroup_closure_nil_of_le_one G (by omega), Nat.zero_le _⟩
      refine (wp_writeOutput_true (p := wrap p) hN₃ hR₃ (hm₃ ▸ hm1) (fun i => hm₃ ▸ hσ i)
        hK_big hK_small hgens_mem).mono ?_
      rintro o st₄ c₄ ⟨rfl, hraw, hmB, hc₄⟩
      have hbound := wrap_pos_cost_bound hlen_r hgens_le (answerBits_some_length_le σ gens)
        hc₁ hc₂ hc₄
      refine ⟨r + 2 + n + n * gens.length, some (σ, gens), rfl, hclos, hraw, ?_, ?_⟩
      · rw [hc₃]; exact hbound.1
      · rw [hmB]; exact hbound.2
  -- Convert `WP (wrap p) wrapMain` into `run (wrap p)`.
  obtain ⟨o, st_f, c, hr, B, a, rfl, hcorr, hraw, hc, hmB⟩ := hmain
  have hcall : Runs (wrap p) (.call 0 0 []) st0 .normal
      { mem := st_f.mem, regs := Function.update st0.regs 0 B } (0 + c + 1) :=
    Runs.call (st := st0) (f := 0) (r := 0) (args := []) (body := wrapMain) rfl
      (by simpa [st0] using hr)
  obtain ⟨fuel', hfuel'⟩ := hcall
  refine ⟨fuel', st_f.mem, B, c + 1, a, ?_, hcorr, hraw, hc, hmB⟩
  unfold run
  simp only [Nat.zero_add] at hfuel'
  rw [hfuel']
  simp

end GI.Turing
