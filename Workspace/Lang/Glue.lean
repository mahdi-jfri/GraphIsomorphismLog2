/-
The glue to the main statement: a `GI.Lang` program that computes a correct answer from the
input value, at a language cost of at most `exp (C * log (n + 2) ^ 2)`, gives
`GI.Statement.GraphIsomorphismInQuasipolynomialTime` (`glue`).

The machine program is `glueProgram P f`. Its procedure 0, `mainBody f`:
1. writes the input value `inputVal G H` right after the input, at `N = 2 * n * n + 1`
   (`buildInput`);
2. calls user function `f` on it, with the heap pointer just after it;
3. copies the cells of the answer `[c₀, …, c_{k-1}]` to the cells right after the answer value,
   and returns their address.
-/
module

public import Workspace.Lang.CorrectMain
public import Workspace.Lang.Encode
public import Workspace.Machine.LoopRules

@[expose] public section

set_option linter.unusedSimpArgs false

namespace GI.Lang

open GI.Machine (Stmt Outcome State WP len len_mono Embeds storeCost evalExpr evalArgs)
open GI.Cited (Val ValAt)
open GI.Statement (InputLayout CorrectOutput)

variable {n : ℕ}

/-! ### Lists of numbers -/

theorem valsAt_map_nat_iff {mem : ℕ → ℕ} {b : ℕ} {l : List ℕ} :
    ValsAt mem b (l.map .nat) ↔
      ∀ i (hi : i < l.length), mem (b + 2 * i) = 0 ∧ mem (b + 2 * i + 1) = l[i] := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, ValsAt.cons_iff, ValAt.nat_iff, size_nat, ih]
    constructor
    · rintro ⟨⟨h0, h1⟩, h⟩ i hi
      rcases i with _ | i
      · simpa using ⟨h0, h1⟩
      · have := h i (by simpa using hi)
        simp only [List.getElem_cons_succ]
        rw [show b + 2 * (i + 1) = b + 2 + 2 * i by ring]; exact this
    · intro h
      have h0 := h 0 (by simp)
      refine ⟨⟨by simpa using h0.1, by simpa [List.getElem_cons] using h0.2⟩,
        fun i hi => ?_⟩
      have := h (i + 1) (by simpa using hi)
      rw [show b + 2 * (i + 1) = b + 2 + 2 * i by ring] at this
      simpa using this

theorem length_cellsList_map_nat (l : List ℕ) :
    (Val.cellsList (l.map .nat)).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]; omega

/-! ### Writing the input value -/

/-- Register 2 gets `N = 2 * n * n + 1`, and the three header cells of a list of `N` numbers
go to `N, N + 1, N + 2`. -/
def header : Stmt :=
  .assign 2 (.bin .add (.bin .mul (.bin .mul (.const 2) (.load (.const 0))) (.load (.const 0)))
    (.const 1)) ;;
  .store (.reg 2) (.const 1) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 2) ;;
  .store (.bin .add (.reg 2) (.const 2)) (.bin .mul (.const 2) (.reg 2))

theorem wp_header {q : GI.Machine.Program} {mem : ℕ → ℕ} (h0 : mem 0 = n) :
    WP q header ⟨mem, fun _ => 0⟩ (fun o st c => o = .normal ∧
      st.regs = Function.update (fun _ => 0) 2 (2 * n * n + 1) ∧
      st.mem (2 * n * n + 1) = 1 ∧ st.mem (2 * n * n + 1 + 1) = 2 * n * n + 1 ∧
      st.mem (2 * n * n + 1 + 2) = 2 * (2 * n * n + 1) ∧
      (∀ a < 2 * n * n + 1, st.mem a = mem a) ∧
      c ≤ 100 * (len (2 * n * n + 1) + 1)) := by
  obtain ⟨N, hN⟩ : ∃ N, 2 * n * n + 1 = N := ⟨_, rfl⟩
  rw [hN]
  unfold header
  apply seq_assign
  apply seq_store
  apply seq_store
  apply WP.store
  simp only [machine_simps, h0, hN, Function.update_apply, if_true]
  refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · intro a ha
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · have l1 : len n ≤ len N := len_mono (by nlinarith)
    have l2 : len (2 * n) ≤ len N := len_mono (by nlinarith)
    have l3 : len (2 * n * n) ≤ len N := len_mono (by omega)
    have l4 := GI.Machine.len_add_le N 1
    have l5 := GI.Machine.len_add_le N 2
    have l6 := GI.Machine.len_mul_le 2 N
    simp only [show len 2 = 2 from rfl, GI.Machine.len_one, GI.Machine.len_zero] at *
    omega

/-- Every input cell is at most `n + 1`: cell 0 holds `n`, and the other cells hold 0 or 1. -/
theorem inputLayout_le {G H : SimpleGraph (Fin n)} {mem : ℕ → ℕ} (h : InputLayout G H mem)
    (a : ℕ) : mem a ≤ n + 1 := by
  classical
  by_cases ha0 : a = 0
  · rw [ha0, h.size]; omega
  by_cases hbig : 2 * n * n < a
  · rw [h.rest a hbig]; omega
  have h2 : 2 * n * n = n * n + n * n := by ring
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; omega
    · exact hn
  have decompose : ∀ b, b < n * n → ∃ i j : Fin n, b = n * i + j := by
    intro b hb
    refine ⟨⟨b / n, (Nat.div_lt_iff_lt_mul hn).mpr (by rwa [Nat.mul_comm] at hb)⟩,
      ⟨b % n, Nat.mod_lt b hn⟩, ?_⟩
    exact (Nat.div_add_mod b n).symm
  by_cases hleft : a ≤ n * n
  · obtain ⟨i, j, hij⟩ := decompose (a - 1) (by omega)
    rw [show a = 1 + n * i + j by omega, h.left]
    split_ifs <;> omega
  · obtain ⟨i, j, hij⟩ := decompose (a - 1 - n * n) (by omega)
    rw [show a = 1 + n * n + n * i + j by omega, h.right]
    split_ifs <;> omega

/-- The two loops that write the entries of the input value: first the tags 0, then the
numbers, read from the input cells. -/
def fillInput : Stmt :=
  Stmt.forUp 3 2 (.store (.bin .add (.bin .add (.reg 2) (.const 3))
    (.bin .mul (.const 2) (.reg 3))) (.const 0)) ;;
  Stmt.forUp 3 2 (.store (.bin .add (.bin .add (.reg 2) (.const 4))
    (.bin .mul (.const 2) (.reg 3))) (.load (.reg 3)))

theorem wp_fillInput {q : GI.Machine.Program} {st : State} {mem : ℕ → ℕ} {N : ℕ}
    (h2 : st.regs 2 = N) (hval : ∀ a < N, mem a ≤ N + 1)
    (hlow : ∀ a < N, st.mem a = mem a) :
    WP q fillInput st (fun o st' c => o = .normal ∧ st'.regs = Function.update st.regs 3 N ∧
      ValsAt st'.mem (N + 3) (((List.range N).map mem).map .nat) ∧
      (∀ a, a < N + 3 → st'.mem a = st.mem a) ∧
      c ≤ N * (60 * (len (3 * N + 4) + 1)) + 20 * (len N + 1)) := by
  have l1 : len N ≤ len (3 * N + 4) := len_mono (by omega)
  unfold fillInput
  refine WP.seq' (fun st₁ c => st₁.regs = Function.update st.regs 3 N ∧
      (∀ k < N, st₁.mem (N + 3 + 2 * k) = 0) ∧
      (∀ x, (∀ k < N, x ≠ N + 3 + 2 * k) → st₁.mem x = st.mem x) ∧
      c ≤ N * (20 * (len (3 * N + 4) + 1) + 11 + 6 * len N) + 7 + 4 * len N) ?_ ?_
  · refine WP.forUp_store (by omega) (fun k => N + 3 + 2 * k) (fun _ => 0)
      (20 * (len (3 * N + 4) + 1)) (fun j k _ _ h => by beta_reduce at h; omega) ?_ ?_
    · intro k st' hk hr _
      rw [h2] at hk
      have hk2 : st'.regs 2 = N := by rw [hr]; simp [h2]
      have hk3 : st'.regs 3 = k := by rw [hr]; simp
      refine ⟨by simp [machine_simps, hk2, hk3], by simp, ?_⟩
      have a1 : len k ≤ len (3 * N + 4) := len_mono (by omega)
      have a2 : len (2 * k) ≤ len (3 * N + 4) := len_mono (by omega)
      have a3 : len (N + 3) ≤ len (3 * N + 4) := len_mono (by omega)
      have a4 : len (N + 3 + 2 * k) ≤ len (3 * N + 4) := len_mono (by omega)
      simp only [storeCost, machine_simps, hk2, hk3, show len 2 = 2 from rfl,
        show len 3 = 2 from rfl, GI.Machine.len_zero]
      omega
    · intro mem' c hw hr hc
      rw [h2] at hw hc
      refine ⟨rfl, by simp [h2], hw, fun x hx => hr x (by rw [h2]; exact hx), hc⟩
  rintro st₁ c₁ ⟨r1, w1, o1, k1⟩
  have e12 : st₁.regs 2 = N := by rw [r1]; simp [h2]
  refine WP.forUp_store (by omega) (fun k => N + 4 + 2 * k) mem
      (20 * (len (3 * N + 4) + 1)) (fun j k _ _ h => by beta_reduce at h; omega) ?_ ?_
  · intro k st' hk hr hm
    rw [e12] at hk
    have hk2 : st'.regs 2 = N := by rw [hr]; simp [e12]
    have hk3 : st'.regs 3 = k := by rw [hr]; simp
    have hmk : st'.mem k = mem k := by
      rw [hm k (fun j _ => by beta_reduce; omega), o1 k (fun j _ => by omega), hlow k hk]
    refine ⟨by simp [machine_simps, hk2, hk3], by simp [machine_simps, hk3, hmk], ?_⟩
    have a1 : len k ≤ len (3 * N + 4) := len_mono (by omega)
    have a2 : len (2 * k) ≤ len (3 * N + 4) := len_mono (by omega)
    have a3 : len (N + 4) ≤ len (3 * N + 4) := len_mono (by omega)
    have a4 : len (N + 4 + 2 * k) ≤ len (3 * N + 4) := len_mono (by omega)
    have a5 : len (mem k) ≤ len (3 * N + 4) := len_mono (by have := hval k hk; omega)
    simp only [storeCost, machine_simps, hk2, hk3, hmk, show len 2 = 2 from rfl,
      show len 4 = 3 from rfl]
    omega
  · intro mem' c hw hr hc
    rw [e12] at hw hc
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · show Function.update st₁.regs 3 (st₁.regs 2) = _
      rw [e12, r1, Function.update_idem]
    · show ValsAt mem' _ _
      rw [valsAt_map_nat_iff]
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      refine ⟨?_, ?_⟩
      · rw [hr _ (fun k _ => by beta_reduce; omega)]
        simpa [Nat.add_assoc] using w1 i hi
      · have := hw i hi
        simp only [List.getElem_map, List.getElem_range]
        rw [show N + 3 + 2 * i + 1 = N + 4 + 2 * i by omega]
        exact this
    · intro a ha
      show mem' a = _
      rw [hr a (fun k _ => by beta_reduce; omega), o1 a (fun k _ => by omega)]
    · have hL : 3 ≤ len (3 * N + 4) := by
        have := len_mono (show 4 ≤ 3 * N + 4 by omega)
        simpa [show len 4 = 3 from rfl] using this
      have m1 : N * (20 * (len (3 * N + 4) + 1) + 11 + 6 * len N) ≤
          N * (30 * (len (3 * N + 4) + 1)) := Nat.mul_le_mul_left _ (by omega)
      have e : N * (60 * (len (3 * N + 4) + 1)) = 2 * (N * (30 * (len (3 * N + 4) + 1))) := by
        ring
      omega

/-! ### Writing the answer -/

/-- Register 5 holds the address of the answer value, a list of numbers, and register 4 the
address after it. Copy the numbers to the cells from register 4 on. -/
def writeAnswer : Stmt :=
  .assign 6 (.load (.bin .add (.reg 5) (.const 1))) ;;
  Stmt.forUp 3 6 (.store (.bin .add (.reg 4) (.reg 3))
    (.load (.bin .add (.bin .add (.reg 5) (.const 4)) (.bin .mul (.const 2) (.reg 3)))))

theorem wp_writeAnswer {q : GI.Machine.Program} {st : State} {A R : ℕ} {cells : List ℕ}
    (h4 : st.regs 4 = R) (h5 : st.regs 5 = A)
    (hval : ValAt st.mem A (.list (cells.map .nat)))
    (hR : A + (Val.list (cells.map .nat)).size ≤ R) :
    WP q writeAnswer st (fun o st' c => o = .normal ∧
      (∀ j (hj : j < cells.length), st'.mem (R + j) = cells[j]) ∧ st'.regs 4 = R ∧
      c ≤ (cells.length + 1) *
        (60 * (len (R + cells.length + 2 ^ (Val.list (cells.map .nat)).wt) + 1))) := by
  obtain ⟨v, hv⟩ : ∃ v, Val.list (cells.map .nat) = v := ⟨_, rfl⟩
  rw [hv] at hval hR ⊢
  have hl := ValAt.list_iff.mp (hv ▸ hval)
  simp only [List.length_map] at hl
  have hent := valsAt_map_nat_iff.mp hl.2.2.2
  have hsz : v.size = 2 * cells.length + 3 := by
    rw [← hv, size_list, length_cellsList_map_nat]
  obtain ⟨M, hM⟩ : ∃ M, R + cells.length + 2 ^ v.wt = M := ⟨_, rfl⟩
  rw [hM]
  -- Every cell of the answer value is below `2 ^ v.wt`.
  have hcell : ∀ i < v.size, st.mem (A + i) < 2 ^ v.wt :=
    fun i hi => Val.lt_two_pow_wt (hval.mem_cells hi)
  generalize 2 ^ v.wt = B at hcell hM
  unfold writeAnswer
  apply seq_assign
  have hk : (evalExpr st (.load (.bin .add (.reg 5) (.const 1)))).1 = cells.length := by
    simp [machine_simps, h5, hl.2.1]
  have hk' : (evalExpr st (.load (.bin .add (.reg 5) (.const 1)))).2 ≤ 10 * (len M + 1) := by
    have a1 : len A ≤ len M := len_mono (by omega)
    have a2 : len (A + 1) ≤ len M := len_mono (by omega)
    have a3 : len cells.length ≤ len M := len_mono (by omega)
    simp [machine_simps, h5, hl.2.1, GI.Machine.len_one]
    omega
  generalize (evalExpr st (.load (.bin .add (.reg 5) (.const 1)))).2 = c₀ at hk' ⊢
  rw [hk]
  refine WP.forUp_store (by omega) (fun j => R + j) (fun j => cells.getD j 0)
    (40 * (len M + 1)) (fun j k _ _ h => by beta_reduce at h; omega) ?_ ?_
  · intro j st' hj hr hm
    simp only [Function.update_apply, if_true] at hj
    have hj4 : st'.regs 4 = R := by rw [hr]; simp [h4]
    have hj5 : st'.regs 5 = A := by rw [hr]; simp [h5]
    have hj3 : st'.regs 3 = j := by rw [hr]; simp
    have hread : st'.mem (A + 4 + 2 * j) = cells[j] := by
      rw [hm _ (fun i _ => by beta_reduce; omega), show A + 4 + 2 * j = A + 3 + 2 * j + 1 by omega]
      exact (hent j hj).2
    have hlt : cells[j] < B := by
      rw [← hread, hm _ (fun i _ => by beta_reduce; omega),
        show A + 4 + 2 * j = A + (2 * j + 4) by omega]
      exact hcell _ (by omega)
    refine ⟨by simp [machine_simps, hj4, hj3], ?_, ?_⟩
    · simp [machine_simps, hj5, hj3, hread, List.getElem?_eq_getElem hj]
    · have a1 : len A ≤ len M := len_mono (by omega)
      have a2 : len (A + 4) ≤ len M := len_mono (by omega)
      have a3 : len j ≤ len M := len_mono (by omega)
      have a4 : len (2 * j) ≤ len M := len_mono (by omega)
      have a5 : len (A + 4 + 2 * j) ≤ len M := len_mono (by omega)
      have a6 : len R ≤ len M := len_mono (by omega)
      have a7 : len (R + j) ≤ len M := len_mono (by omega)
      have a8 : len cells[j] ≤ len M := len_mono (by omega)
      simp only [storeCost, machine_simps, hj4, hj5, hj3, hread, show len 2 = 2 from rfl,
        show len 4 = 3 from rfl]
      omega
  · intro mem' c hw _ hc
    simp only [Function.update_apply, if_true] at hw hc
    refine ⟨rfl, fun j hj => ?_, by simp [h4], ?_⟩
    · have := hw j hj
      simp only [List.getD_eq_getElem _ _ hj] at this
      exact this
    · have a3 : len cells.length ≤ len M := len_mono (by omega)
      have m1 : cells.length * (40 * (len M + 1) + 11 + 6 * len cells.length) ≤
          cells.length * (60 * (len M + 1)) := Nat.mul_le_mul_left _ (by omega)
      have e : (cells.length + 1) * (60 * (len M + 1)) =
          cells.length * (60 * (len M + 1)) + 60 * (len M + 1) := by ring
      omega

/-! ### The whole program -/

/-- The address just after the input value: `N + 3 + 2 * N`, with `N` in register 2. -/
def hpExpr : MExpr :=
  .bin .add (.bin .add (.reg 2) (.const 3)) (.bin .mul (.const 2) (.reg 2))

/-- Procedure 0 of the glue program. -/
def mainBody (f : ℕ) : Stmt :=
  header ;; fillInput ;; .call 4 (2 + f) [hpExpr, .const 0, .reg 2] ;; .assign 5 hpExpr ;;
  writeAnswer ;; .ret (.reg 4)

/-- The glue program: `mainBody f`, then the compiled program at offset 1. -/
def glueProgram (P : Program) (f : ℕ) : GI.Machine.Program :=
  ⟨mainBody f :: (compile P).shifted 1⟩

theorem glue_embeds (P : Program) (f : ℕ) : Embeds (glueProgram P f) (compile P) 1 :=
  Embeds.of_append (A := [mainBody f]) (B := []) (by simp [glueProgram])

theorem glue_proc {P : Program} {f : ℕ} {body : Expr} (hf : P.funs[f]? = some body) :
    (glueProgram P f).procs[2 + f]? = some ((funBody (primOff P) body).shift 1) := by
  have := glue_embeds P f (1 + f) _ (compile_fun hf)
  rwa [show 1 + f + 1 = 2 + f by omega] at this

/-- **The machine part of the glue.** If every evaluation of user function `f` on the input
value gives a correct answer at a language cost satisfying `Q`, the glue program finishes on
the input memory with a correct output, at a cost of at most
`1000 * (cost + 4 * (2 * n * n + 1) + 10) ^ (P.degree + 2)` for a language cost `cost`
satisfying `Q`. -/
theorem glue_run {P : Program} {f : ℕ} {body : Expr} (hf : P.funs[f]? = some body)
    {G H : SimpleGraph (Fin n)} {mem : ℕ → ℕ} (hm : InputLayout G H mem) {Q : ℕ → Prop}
    (h : EvalAll P [inputVal G H] body (fun w c => AnswerOK G H w ∧ Q c)) :
    ∃ fuel mem' r cost, GI.Machine.run (glueProgram P f) mem fuel = some (mem', r, cost) ∧
      CorrectOutput G H mem' r ∧ ∃ lc, Q lc ∧
        cost ≤ 1000 * (lc + 4 * (2 * n * n + 1) + 10) ^ (P.degree + 2) := by
  have hle := inputLayout_le hm
  obtain rfl := inputMem_eq hm
  obtain ⟨N, hN⟩ : ∃ N, 2 * n * n + 1 = N := ⟨_, rfl⟩
  rw [hN]
  refine GI.Machine.exists_run_of_wp (Q := fun mem' r cost => CorrectOutput G H mem' r ∧
    ∃ lc, Q lc ∧ cost ≤ 1000 * (lc + 4 * N + 10) ^ (P.degree + 2)) rfl ?_
  unfold mainBody
  -- The header.
  refine WP.seq' _ (wp_header (inputMem_layout G H).size) ?_
  rintro st₁ c₁ ⟨r1, m1N, m1N1, m1N2, m1low, k1⟩
  rw [hN] at r1 m1N m1N1 m1N2 m1low k1
  have e12 : st₁.regs 2 = N := by rw [r1]; simp
  -- The entries of the input value.
  have hnN : n ≤ N := by rw [← hN]; nlinarith
  refine WP.seq' _ (wp_fillInput (mem := inputMem G H) e12 (fun a _ => by
    have := hle a; omega) m1low) ?_
  rintro st₂ c₂ ⟨r2, v2, m2, k2⟩
  have e22 : st₂.regs 2 = N := by rw [r2]; simp [e12]
  have hval : ValAt st₂.mem N (inputVal G H) := by
    rw [inputVal, ValAt.list_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [m2 _ (by omega), m1N]
    · rw [m2 _ (by omega), m1N1]; simp [inputCells, hN]
    · rw [m2 _ (by omega), m1N2, length_cellsList_map_nat]; simp [inputCells, hN]
    · simpa [inputCells, hN] using v2
  have hsz : (inputVal G H).size = 2 * N + 3 := by
    rw [inputVal, size_list, length_cellsList_map_nat]; simp [inputCells, hN]
  -- The call of user function `f`.
  apply WP.seq
  apply WP.call (glue_proc hf)
  refine (WP.shift (glue_embeds P f) (wp_funBody_eval h (hp := N + 3 + 2 * N)
    (st := { mem := st₂.mem, regs := fun i => (evalArgs st₂ [hpExpr, .const 0, .reg 2]).1.getD i 0 })
    ?_ ?_ ?_)).mono ?_
  · simp [machine_simps, hpExpr, e22]
  · simpa [machine_simps, e22] using hval
  · simp [machine_simps, e22, hsz]; omega
  rintro o st' c ⟨w, lc, ⟨⟨hok, hQ⟩, -⟩, rfl, vw, mw, hwt, kc⟩
  obtain ⟨cells, rfl, hcells⟩ := hok
  simp only [Outcome.retVal_returned]
  -- The address of the answer value.
  apply seq_assign
  obtain ⟨R, hR⟩ : ∃ R, N + 3 + 2 * N + (Val.list (cells.map .nat)).size = R := ⟨_, rfl⟩
  rw [hR]
  have h5 : (evalExpr ⟨st'.mem, Function.update st₂.regs 4 R⟩ hpExpr).1 = N + 3 + 2 * N := by
    simp [machine_simps, hpExpr, e22]
  have hc5 : (evalExpr ⟨st'.mem, Function.update st₂.regs 4 R⟩ hpExpr).2 ≤ 20 * (N + 1) := by
    have a1 := GI.Machine.len_le_self N
    have a2 := GI.Machine.len_le_self (N + 3)
    have a3 := GI.Machine.len_le_self (2 * N)
    simp [machine_simps, hpExpr, e22, show len 3 = 2 from rfl, show len 2 = 2 from rfl]
    omega
  generalize (evalExpr ⟨st'.mem, Function.update st₂.regs 4 R⟩ hpExpr).2 = c₅ at hc5 ⊢
  rw [h5]
  -- Writing the answer.
  refine WP.seq' _ (wp_writeAnswer (A := N + 3 + 2 * N)
    (R := R) ?_ ?_ vw (by omega)) ?_
  · simp
  · simp
  rintro st₆ c₆ ⟨w6, r6, k6⟩
  apply WP.ret
  simp only [machine_simps, r6, Outcome.retVal_returned]
  refine ⟨hcells _ _ w6, lc, hQ, ?_⟩
  -- The cost: every part is at most a constant times `Z ^ E`.
  obtain ⟨Z, hZ⟩ : ∃ Z, lc + 4 * N + 10 = Z := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, P.degree + 2 = E := ⟨_, rfl⟩
  rw [hZ, hE]
  rw [hE] at kc
  have hE3 : 3 ≤ E := by rw [← hE]; simp [Program.degree]
  have hZ1 : 1 ≤ Z := by omega
  have hZZ : Z ≤ Z * Z := Nat.le_mul_of_pos_left _ (by omega)
  have hZE : Z * Z ≤ Z ^ E := by
    rw [← pow_two]; exact Nat.pow_le_pow_right hZ1 (by omega)
  have hsl : (Val.list (cells.map .nat)).size = 2 * cells.length + 3 := by
    rw [size_list, length_cellsList_map_nat]
  have hsw := (Val.list (cells.map .nat)).size_le_wt
  have lN := GI.Machine.len_le_self N
  have lR := GI.Machine.len_le_self R
  have l34 : len (3 * N + 4) ≤ 3 * N + 4 := GI.Machine.len_le_self _
  have t2 : N * (60 * (len (3 * N + 4) + 1)) ≤ 60 * (Z * Z) := by
    calc N * (60 * (len (3 * N + 4) + 1)) ≤ Z * (60 * Z) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 60 * (Z * Z) := by ring
  have t3 : (evalExpr st₂ hpExpr).2 ≤ 20 * (N + 1) := by
    have a2 := GI.Machine.len_le_self (N + 3)
    have a3 := GI.Machine.len_le_self (2 * N)
    simp [machine_simps, hpExpr, e22, show len 3 = 2 from rfl, show len 2 = 2 from rfl]
    omega
  have t4 : c ≤ 403 * Z ^ E := by
    have := GI.Machine.len_le_self (N + 3 + 2 * N)
    exact kc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have t6 : c₆ ≤ 240 * (Z * Z) := by
    have l1 := len_add_two_pow (R + cells.length) (Val.list (cells.map .nat)).wt
    have l2 := GI.Machine.len_le_self (R + cells.length)
    calc c₆ ≤ (cells.length + 1) *
          (60 * (len (R + cells.length + 2 ^ (Val.list (cells.map .nat)).wt) + 1)) := k6
      _ ≤ Z * (240 * Z) := Nat.mul_le_mul (by omega) (by omega)
      _ = 240 * (Z * Z) := by ring
  simp only [e22, GI.Machine.len_zero]
  omega

/-! ### The bound -/

/-- A polynomial in a quasipolynomial bound and in `n` is again a quasipolynomial bound. -/
theorem quasi_absorb (A E : ℕ) (C : ℝ) : ∃ C' : ℝ, ∀ (n lc : ℕ),
    (lc : ℝ) ≤ Real.exp (C * Real.log (n + 2) ^ 2) →
    ((A * (lc + 4 * (2 * n * n + 1) + 10) ^ E : ℕ) : ℝ) ≤
      Real.exp (C' * Real.log (n + 2) ^ 2) := by
  have hl₀ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨l₀, hl⟩ : ∃ l₀, Real.log 2 = l₀ := ⟨_, rfl⟩
  rw [hl] at hl₀
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, |C| + 2 / l₀ = C₀ := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, ((A : ℝ) + 1) * 15 ^ E = K₀ := ⟨_, rfl⟩
  have hK1 : 1 ≤ K₀ := by
    rw [← hK₀]
    have : (1 : ℝ) ≤ 15 ^ E := one_le_pow₀ (by norm_num)
    nlinarith [(Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  refine ⟨E * C₀ + Real.log K₀ / l₀ ^ 2, fun n lc hlc => ?_⟩
  obtain ⟨L, hL⟩ : ∃ L, Real.log (n + 2) = L := ⟨_, rfl⟩
  rw [hL] at hlc ⊢
  have hLl : l₀ ≤ L := by
    rw [← hl, ← hL]
    exact Real.log_le_log (by norm_num) (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  have hL0 : 0 < L := lt_of_lt_of_le hl₀ hLl
  have hC₀0 : 0 ≤ C₀ := by rw [← hC₀]; positivity
  -- The two parts of the base are at most `exp (C₀ * L ^ 2)`.
  have h1 : (lc : ℝ) ≤ Real.exp (C₀ * L ^ 2) := by
    refine hlc.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (sq_nonneg L)))
    rw [← hC₀]
    have := le_abs_self C
    have : 0 ≤ 2 / l₀ := by positivity
    linarith
  have h2 : ((n : ℝ) + 2) ^ 2 ≤ Real.exp (C₀ * L ^ 2) := by
    have e : ((n : ℝ) + 2) ^ 2 = Real.exp (2 * L) := by
      rw [show 2 * L = L + L by ring, Real.exp_add, ← hL,
        Real.exp_log (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)]
      ring
    rw [e]
    refine Real.exp_le_exp.mpr ?_
    have h3 : 2 * L ≤ 2 / l₀ * L ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl₀]
      nlinarith
    rw [← hC₀]
    have : 0 ≤ |C| * L ^ 2 := by positivity
    nlinarith
  have hM : 1 ≤ Real.exp (C₀ * L ^ 2) := Real.one_le_exp (by positivity)
  have hbase : ((lc + 4 * (2 * n * n + 1) + 10 : ℕ) : ℝ) ≤ 15 * Real.exp (C₀ * L ^ 2) := by
    push_cast
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  -- Now raise to the power `E` and absorb the constant.
  have hpow : ((A * (lc + 4 * (2 * n * n + 1) + 10) ^ E : ℕ) : ℝ) ≤
      K₀ * Real.exp (E * C₀ * L ^ 2) := by
    rw [← hK₀, show (E : ℝ) * C₀ * L ^ 2 = E * (C₀ * L ^ 2) by ring, Real.exp_nat_mul]
    push_cast
    have hb0 : (0 : ℝ) ≤ (lc : ℝ) + 4 * (2 * n * n + 1) + 10 := by positivity
    have hb := hbase
    push_cast at hb
    calc (A : ℝ) * ((lc : ℝ) + 4 * (2 * n * n + 1) + 10) ^ E
        ≤ ((A : ℝ) + 1) * (15 * Real.exp (C₀ * L ^ 2)) ^ E :=
          mul_le_mul (by linarith) (pow_le_pow_left₀ hb0 hb E) (by positivity) (by positivity)
      _ = ((A : ℝ) + 1) * 15 ^ E * Real.exp (C₀ * L ^ 2) ^ E := by ring
  have hK : K₀ ≤ Real.exp (Real.log K₀ / l₀ ^ 2 * L ^ 2) := by
    calc K₀ = Real.exp (Real.log K₀) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (Real.log K₀ / l₀ ^ 2 * L ^ 2) := by
        refine Real.exp_le_exp.mpr ?_
        have hlog : 0 ≤ Real.log K₀ := Real.log_nonneg hK1
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : l₀ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hl₀.le hLl 2
        nlinarith
  calc ((A * (lc + 4 * (2 * n * n + 1) + 10) ^ E : ℕ) : ℝ)
      ≤ K₀ * Real.exp (E * C₀ * L ^ 2) := hpow
    _ ≤ Real.exp (Real.log K₀ / l₀ ^ 2 * L ^ 2) * Real.exp (E * C₀ * L ^ 2) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
    _ = Real.exp ((E * C₀ + Real.log K₀ / l₀ ^ 2) * L ^ 2) := by
        rw [← Real.exp_add]; ring_nf

/-- **The glue.** Let `body` be user function `f` of a `GI.Lang` program `P`. Suppose that for
all graphs `G` and `H` on `Fin n`, every evaluation of `body` on the input value `inputVal G H`
gives a correct answer (`AnswerOK`), at a language cost of at most
`exp (C * log (n + 2) ^ 2)`. Then graph isomorphism is in quasipolynomial time. -/
theorem glue (P : Program) (f : ℕ) (body : Expr) (hf : P.funs[f]? = some body) (C : ℝ)
    (h : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)), EvalAll P [inputVal G H] body
      (fun w cost => AnswerOK G H w ∧ (cost : ℝ) ≤ Real.exp (C * Real.log (n + 2) ^ 2))) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  obtain ⟨C', hC'⟩ := quasi_absorb 1000 (P.degree + 2) C
  refine ⟨glueProgram P f, C', fun n G H mem hm => ?_⟩
  obtain ⟨fuel, mem', r, cost, hrun, hout, lc, hlc, hcost⟩ :=
    glue_run hf hm (Q := fun c => (c : ℝ) ≤ Real.exp (C * Real.log (n + 2) ^ 2)) (h n G H)
  refine ⟨fuel, mem', r, cost, hrun, hout, ?_⟩
  calc (cost : ℝ) ≤ ((1000 * (lc + 4 * (2 * n * n + 1) + 10) ^ (P.degree + 2) : ℕ) : ℝ) := by
        exact_mod_cast hcost
    _ ≤ Real.exp (C' * Real.log (n + 2) ^ 2) := hC' n lc hlc

end GI.Lang
