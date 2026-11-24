/-
Single-step simulation of stack machine instructions by the Turing machine `tm P`.

The relation `Rel P c cfg` links a stack machine configuration `c` to a Turing machine
configuration `cfg`: the Turing machine is at label `(clampPc P.length c.pc, .start)`, every
return address on `c.rs` is at most `P.length`, each stack holds the encoded contents of the
corresponding stack in `c`, `outBuf` holds `c.out.reverse`, and `out`, `scr0`, `scr1` are empty.
The internal state `cfg.var` is unconstrained because every instruction initializes any field it
uses before reading it.

The main theorem `step_sim` shows that one stack machine step of cost `s` from a related
configuration is matched by at most `(P.length + 4) * s` steps of `tm P`, ending in a related
configuration.
-/
module

public import Workspace.Turing.TM.Passes

@[expose] public section

namespace GI.Turing.TM

open GI.Machine (len)
open _root_.Turing (initList)
open _root_.Turing.TM2 (stepAux)
open Function (update)

/-- Simulation relation between a stack-machine configuration `c` and a Turing-machine
configuration `cfg` of `tm P`. -/
structure Rel (P : SM.Program) (c : SM.Config) (cfg : (tm P).Cfg) : Prop where
  rs_le : ∀ r ∈ c.rs, r ≤ P.length
  label : cfg.l = some (clampPc P.length c.pc, .start)
  stk_inp : cfg.stk .inp = c.inp
  stk_out : cfg.stk .out = []
  stk_outBuf : cfg.stk .outBuf = c.out.reverse
  stk_ret : cfg.stk .ret = encRetStack c.rs
  stk_scr0 : cfg.stk .scr0 = []
  stk_scr1 : cfg.stk .scr1 = []
  stk_num : ∀ s : SM.Stk, cfg.stk (.num s) = encStack (c.stk s)

theorem rel_init (P : SM.Program) (x : List Bool) :
    Rel P (SM.init x) (initList (tm P) x) where
  rs_le _ h := by cases h
  label := by
    simp [initList, tm, SM.init, clampPc]
  stk_inp := by simp [initList_stk, SM.init]
  stk_out := by simp [initList_stk]
  stk_outBuf := by simp [initList_stk, SM.init]
  stk_ret := by simp [initList_stk, SM.init, encRetStack]
  stk_scr0 := by simp [initList_stk]
  stk_scr1 := by simp [initList_stk]
  stk_num s := by simp [initList_stk, SM.init, encStack]

private theorem num_ne_scr0 (s : SM.Stk) : K.num s ≠ K.scr0 := by intro h; cases h
private theorem scr0_ne_num (s : SM.Stk) : K.scr0 ≠ K.num s := by intro h; cases h
private theorem num_ne_scr1 (s : SM.Stk) : K.num s ≠ K.scr1 := by intro h; cases h
private theorem scr1_ne_num (s : SM.Stk) : K.scr1 ≠ K.num s := by intro h; cases h
private theorem num_ne_inp (s : SM.Stk) : K.num s ≠ K.inp := by intro h; cases h
private theorem outBuf_ne_num (s : SM.Stk) : K.outBuf ≠ K.num s := by intro h; cases h

private theorem one_le_mul_cost (N n : ℕ) : 1 ≤ (N + 4) * (1 + n) :=
  Nat.le_trans (by omega : 1 ≤ N + 4) (Nat.le_mul_of_pos_right _ (by omega))

private theorem tmProg_at {P : SM.Program} {pc : ℕ} {i : SM.Instr} (hi : P[pc]? = some i)
    (μ : Micro) :
    tmProg P (clampPc P.length pc, μ) = instrStmt P.length (clampPc P.length pc) i μ := by
  have hlt : pc < P.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hi
    cases hi
  have hval : (clampPc P.length pc).val = pc := by
    simp only [clampPc, Nat.min_eq_left (Nat.le_of_lt hlt)]
  have hget : P[pc] = i := by
    rw [List.getElem?_eq_getElem hlt] at hi
    exact Option.some.inj hi
  simp only [tmProg, hval, hlt, ↓reduceDIte, hget]

private theorem clampPc_val_of_lt {N n : ℕ} (h : n < N) : (clampPc N n).val = n :=
  Nat.min_eq_left (Nat.le_of_lt h)

private theorem clampPc_succ_eq {N n : ℕ} (h : n < N) :
    clampPc N ((clampPc N n).val + 1) = clampPc N (n + 1) := by
  rw [clampPc_val_of_lt h]

private theorem pc_lt_of_getElem? {P : SM.Program} {pc : ℕ} {i : SM.Instr} (hi : P[pc]? = some i) :
    pc < P.length := by
  by_contra h
  rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hi
  cases hi

private theorem tm_step_cfg {P : SM.Program} {cfg : (tm P).Cfg} {lbl : Lab P.length}
    (hl : cfg.l = some lbl) :
    (tm P).step cfg = some (stepAux (tmProg P lbl) cfg.var cfg.stk) := by
  rcases cfg with ⟨l, v, S⟩
  dsimp only at hl
  subst hl
  rfl

private theorem step_push {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s : SM.Stk} {k cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.push s k))
    (he : SM.exec1 c (.push s k) = some (c', cost)) :
    ∃ cfg' t, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' t ∧ t ≤ (P.length + 4) * cost := by
  simp only [SM.exec1, Option.some.injEq, Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩
  have hlt := pc_lt_of_getElem? hi
  have hstep : (tm P).step cfg =
      some ⟨some (clampPc P.length (c.pc + 1), .start), cfg.var,
        update cfg.stk (.num s) (encNat k ++ cfg.stk (.num s))⟩ := by
    rw [tm_step_cfg hrel.label, tmProg_at hi .start]
    simp only [instrStmt, stepAux_pushList, stepAux, clampPc_succ_eq hlt]
    rfl
  refine ⟨_, 1, ?_, ReachesIn.single hstep, one_le_mul_cost P.length (len k)⟩
  refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne, hrel.stk_inp]
  · simp [Function.update_of_ne, hrel.stk_out]
  · simp [Function.update_of_ne, hrel.stk_outBuf]
  · simp [Function.update_of_ne, hrel.stk_ret]
  · simp [Function.update_of_ne, hrel.stk_scr0]
  · simp [Function.update_of_ne, hrel.stk_scr1]
  · intro t
    by_cases hts : t = s
    · subst hts; simp [hrel.stk_num, encStack_cons]
    · simp [Function.update_of_ne, hts, hrel.stk_num]

private theorem step_pop {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s : SM.Stk} {cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.pop s))
    (he : SM.exec1 c (.pop s) = some (c', cost)) :
    ∃ cfg' t, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' t ∧ t ≤ (P.length + 4) * cost := by
  simp only [SM.exec1] at he
  cases hstk : c.stk s with
  | nil => rw [hstk] at he; cases he
  | cons v r =>
    rw [hstk] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    have hlt := pc_lt_of_getElem? hi
    let pc := clampPc P.length c.pc
    have hstep1 : (tm P).step cfg = some ⟨some (pc, .popLoop), cfg.var, cfg.stk⟩ := by
      rw [tm_step_cfg hrel.label, tmProg_at hi .start]; rfl
    have hloop := reachesIn_popLoop (P := P) (s := .num s) (self := (pc, .popLoop))
      (exitStmt := .goto (fun _ => (clampPc P.length (pc.val + 1), .start)))
      (tmProg_at hi .popLoop) (bits v) (encStack r) cfg.var cfg.stk
      (by rw [hrel.stk_num s, hstk, encStack_cons, encNat])
    simp only [stepAux, pc, clampPc_succ_eq hlt] at hloop
    have hrun := ReachesIn.step_head hstep1 hloop
    refine ⟨_, (bits v).length + 1 + 1, ?_, hrun, ?_⟩
    · refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne, hrel.stk_inp]
      · simp [Function.update_of_ne, hrel.stk_out]
      · simp [Function.update_of_ne, hrel.stk_outBuf]
      · simp [Function.update_of_ne, hrel.stk_ret]
      · simp [Function.update_of_ne, hrel.stk_scr0]
      · simp [Function.update_of_ne, hrel.stk_scr1]
      · intro t
        by_cases hts : t = s
        · subst hts; simp
        · simp [Function.update_of_ne, hts, hrel.stk_num]
    · rw [bits_length]
      have h2 : 2 * (1 + len v) ≤ (P.length + 4) * (1 + len v) :=
        Nat.mul_le_mul_right _ (by omega)
      omega

private theorem step_copy {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s t : SM.Stk} {cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.copy s t))
    (he : SM.exec1 c (.copy s t) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1] at he
  cases hstk : c.stk s with
  | nil => rw [hstk] at he; cases he
  | cons v r =>
    rw [hstk] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    have hlt := pc_lt_of_getElem? hi
    let pc := clampPc P.length c.pc
    have hstep1 : (tm P).step cfg = some ⟨some (pc, .copyPop), cfg.var, cfg.stk⟩ := by
      rw [tm_step_cfg hrel.label, tmProg_at hi .start]; rfl
    obtain ⟨v₁, hpop⟩ := reachesIn_copyPop (P := P) (s := .num s) (num_ne_scr0 s) (num_ne_scr1 s)
      (self := (pc, .copyPop)) (next := (pc, .copyRestore0)) (tmProg_at hi .copyPop)
      (bits v) (encStack r) [] [] cfg.var cfg.stk
      (by rw [hrel.stk_num s, hstk, encStack_cons, encNat]) hrel.stk_scr0 hrel.stk_scr1
    simp only [List.append_nil] at hpop
    let S₁ := update (update (update cfg.stk (.num s) (false :: encStack r)) .scr0 (bits v).reverse)
      .scr1 (bits v).reverse
    obtain ⟨v₂, hres0⟩ := reachesIn_restoreLoop (P := P) (scr := .scr0) (tgt := .num s)
      (scr0_ne_num s) (self := (pc, .copyRestore0))
      (exitStmt := .push (.num t) (fun _ => false) (.goto (fun _ => (pc, .copyRestore1))))
      (tmProg_at hi .copyRestore0) (bits v).reverse v₁ S₁
      (by simp [S₁, Function.update_of_ne])
    simp only [stepAux] at hres0
    let S₂0 := update (update S₁ .scr0 []) (.num s) (pushDigits (bits v).reverse (S₁ (.num s)))
    have hS₂0_eq : S₂0 = update cfg.stk .scr1 (bits v).reverse := by
      ext k
      have hS₁s : S₁ (.num s) = false :: encStack r := by
        simp [S₁, Function.update_of_ne]
      by_cases hk : k = .num s
      · subst hk
        simp only [S₂0, Function.update_self, hS₁s, pushDigits_reverse_false,
          Function.update_of_ne (num_ne_scr1 s), hrel.stk_num s, hstk, encStack_cons, encNat]
      · simp only [S₂0, Function.update_of_ne hk]
        by_cases hk0 : k = .scr0
        · subst hk0
          simp [Function.update_self, Function.update_of_ne, hrel.stk_scr0]
        · simp only [Function.update_of_ne hk0, S₁]
          by_cases hk1 : k = .scr1
          · subst hk1; simp
          · simp [Function.update_of_ne hk1, Function.update_of_ne hk0, Function.update_of_ne hk]
    change ReachesIn (tm P) ⟨some (pc, .copyRestore0), v₁, S₁⟩
      ⟨some (pc, .copyRestore1), v₂, update S₂0 (.num t) (false :: S₂0 (.num t))⟩ _ at hres0
    rw [hS₂0_eq] at hres0
    let S₂ := update (update cfg.stk .scr1 (bits v).reverse) (.num t)
      (false :: (update cfg.stk .scr1 (bits v).reverse) (.num t))
    obtain ⟨v₃, hres1⟩ := reachesIn_restoreLoop (P := P) (scr := .scr1) (tgt := .num t)
      (scr1_ne_num t) (self := (pc, .copyRestore1))
      (exitStmt := .goto (fun _ => (clampPc P.length (pc.val + 1), .start)))
      (tmProg_at hi .copyRestore1) (bits v).reverse v₂ S₂
      (by simp [S₂, Function.update_of_ne])
    simp only [stepAux, pc, clampPc_succ_eq hlt] at hres1
    have hrun := (ReachesIn.step_head hstep1 hpop).trans (hres0.trans hres1)
    let S₃ := update (update S₂ .scr1 []) (.num t) (pushDigits (bits v).reverse (S₂ (.num t)))
    have hS₃_eq : S₃ = update cfg.stk (.num t) (encNat v ++ cfg.stk (.num t)) := by
      have hS₂t : S₂ (.num t) = false :: cfg.stk (.num t) := by
        simp [S₂, Function.update_of_ne]
      ext k
      by_cases hkt : k = .num t
      · subst hkt
        simp only [S₃, Function.update_self, hS₂t, pushDigits_reverse_false, encNat]
      · simp only [S₃, Function.update_of_ne hkt]
        by_cases hk1 : k = .scr1
        · subst hk1; simp [hrel.stk_scr1]
        · simp [S₂, Function.update_of_ne hk1, Function.update_of_ne hkt]
    change ReachesIn (tm P) cfg ⟨some (clampPc P.length (c.pc + 1), .start), v₃, S₃⟩ _ at hrun
    rw [hS₃_eq] at hrun
    refine ⟨_, _, ?_, hrun, ?_⟩
    · refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne, hrel.stk_inp]
      · simp [Function.update_of_ne, hrel.stk_out]
      · simp [Function.update_of_ne, hrel.stk_outBuf]
      · simp [Function.update_of_ne, hrel.stk_ret]
      · simp [Function.update_of_ne, hrel.stk_scr0]
      · simp [Function.update_of_ne, hrel.stk_scr1]
      · intro u
        by_cases hut : u = t
        · subst hut; simp [hrel.stk_num, encStack_cons]
        · simp [Function.update_of_ne, hut, hrel.stk_num]
    · simp only [List.length_reverse, bits_length]
      have h4 : 4 * (1 + len v) ≤ (P.length + 4) * (1 + len v) :=
        Nat.mul_le_mul_right _ (by omega)
      omega

private theorem step_move {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s t : SM.Stk} {cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.move s t))
    (he : SM.exec1 c (.move s t) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1] at he
  cases hstk : c.stk s with
  | nil => rw [hstk] at he; cases he
  | cons v r =>
    rw [hstk] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    have hlt := pc_lt_of_getElem? hi
    let pc := clampPc P.length c.pc
    have hstep1 : (tm P).step cfg = some ⟨some (pc, .movePop), cfg.var, cfg.stk⟩ := by
      rw [tm_step_cfg hrel.label, tmProg_at hi .start]; rfl
    obtain ⟨v₁, hpop⟩ := reachesIn_movePop (P := P) (s := .num s) (t := .num t)
      (num_ne_scr0 s) (num_ne_scr0 t) (self := (pc, .movePop)) (next := (pc, .moveRestore))
      (tmProg_at hi .movePop) (bits v) (encStack r) [] cfg.var cfg.stk
      (by rw [hrel.stk_num s, hstk, encStack_cons, encNat]) hrel.stk_scr0
    simp only [List.append_nil] at hpop
    let S₁' := update (update cfg.stk (.num s) (encStack r)) .scr0 (bits v).reverse
    let S₁ := update S₁' (.num t) (false :: S₁' (.num t))
    obtain ⟨v₂, hres⟩ := reachesIn_restoreLoop (P := P) (scr := .scr0) (tgt := .num t)
      (scr0_ne_num t) (self := (pc, .moveRestore))
      (exitStmt := .goto (fun _ => (clampPc P.length (pc.val + 1), .start)))
      (tmProg_at hi .moveRestore) (bits v).reverse v₁ S₁
      (by simp [S₁, S₁', Function.update_of_ne])
    simp only [stepAux, pc, clampPc_succ_eq hlt] at hres
    have hrun := (ReachesIn.step_head hstep1 hpop).trans hres
    refine ⟨_, _, ?_, hrun, ?_⟩
    · refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [S₁, S₁', Function.update_of_ne, hrel.stk_inp]
      · simp [S₁, S₁', Function.update_of_ne, hrel.stk_out]
      · simp [S₁, S₁', Function.update_of_ne, hrel.stk_outBuf]
      · simp [S₁, S₁', Function.update_of_ne, hrel.stk_ret]
      · simp [Function.update_of_ne]
      · simp [S₁, S₁', Function.update_of_ne, hrel.stk_scr1]
      · intro u
        by_cases hut : u = t
        · subst hut
          have hS₁t : S₁ (.num u) = false :: S₁' (.num u) := by simp [S₁]
          simp only [Function.update_self, hS₁t, pushDigits_reverse_false, encStack_cons, encNat]
          congr 1
          by_cases hus : u = s
          · subst hus; simp [S₁', Function.update_of_ne]
          · simp [S₁', Function.update_of_ne, hus, hrel.stk_num]
        · simp only [Function.update_of_ne (show K.num u ≠ K.num t by intro h; exact hut (K.num.inj h)),
            Function.update_of_ne (num_ne_scr0 u), S₁, Function.update_of_ne hut]
          by_cases hus : u = s
          · subst hus; simp [S₁', Function.update_of_ne]
          · simp [S₁', Function.update_of_ne, hus, hrel.stk_num]
    · simp only [List.length_reverse, bits_length]
      have h3 : 3 * (1 + len v) ≤ (P.length + 4) * (1 + len v) :=
        Nat.mul_le_mul_right _ (by omega)
      omega

private theorem step_add {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s t : SM.Stk} {cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.add s t))
    (he : SM.exec1 c (.add s t) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1] at he
  by_cases hst : s = t
  · simp [hst] at he
  · simp only [hst, ↓reduceIte] at he
    cases hs : c.stk s with
    | nil => rw [hs] at he; cases he
    | cons a rs =>
      cases ht : c.stk t with
      | nil => rw [hs, ht] at he; cases he
      | cons b rt =>
        rw [hs, ht] at he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        have hlt := pc_lt_of_getElem? hi
        let pc := clampPc P.length c.pc
        have hkst : K.num s ≠ K.num t := fun h => hst (K.num.inj h)
        have hstep1 : (tm P).step cfg =
            some ⟨some (pc, .addLoop), { cfg.var with carry := false }, cfg.stk⟩ := by
          rw [tm_step_cfg hrel.label, tmProg_at hi .start]; rfl
        obtain ⟨v₁, hadd⟩ := reachesIn_addLoop (P := P) (s := .num s) (t := .num t)
          hkst (num_ne_scr0 s) (num_ne_scr0 t) (self := (pc, .addLoop)) (next := (pc, .moveRestore))
          (tmProg_at hi .addLoop) (bits a) (bits b) (encStack rs) (encStack rt) []
          { cfg.var with carry := false } cfg.stk
          (by rw [hrel.stk_num s, hs, encStack_cons, encNat])
          (by rw [hrel.stk_num t, ht, encStack_cons, encNat]) hrel.stk_scr0
        simp only [List.append_nil] at hadd
        have haddBits : addBitsRaw (bits a) (bits b) false = bits (a + b) := addBitsRaw_bits a b
        change ReachesIn (tm P) ⟨some (pc, .addLoop), { cfg.var with carry := false }, cfg.stk⟩
          ⟨some (pc, .moveRestore), v₁,
            update (update (update cfg.stk (.num s) (false :: encStack rs)) (.num t) (encStack rt))
              .scr0 ((addBitsRaw (bits a) (bits b) false).reverse)⟩ _ at hadd
        rw [haddBits] at hadd
        let S₁ := update (update (update cfg.stk (.num s) (false :: encStack rs)) (.num t) (encStack rt))
          .scr0 (bits (a + b)).reverse
        obtain ⟨v₂, hres⟩ := reachesIn_restoreLoop (P := P) (scr := .scr0) (tgt := .num s)
          (scr0_ne_num s) (self := (pc, .moveRestore))
          (exitStmt := .goto (fun _ => (clampPc P.length (pc.val + 1), .start)))
          (tmProg_at hi .moveRestore) (bits (a + b)).reverse v₁ S₁ (Function.update_self K.scr0 _ _)
        simp only [stepAux, pc, clampPc_succ_eq hlt] at hres
        have hrun := (ReachesIn.step_head hstep1 hadd).trans hres
        refine ⟨_, _, ?_, hrun, ?_⟩
        · refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [S₁, Function.update_of_ne, hrel.stk_inp]
          · simp [S₁, Function.update_of_ne, hrel.stk_out]
          · simp [S₁, Function.update_of_ne, hrel.stk_outBuf]
          · simp [S₁, Function.update_of_ne, hrel.stk_ret]
          · simp [Function.update_of_ne]
          · simp [S₁, Function.update_of_ne, hrel.stk_scr1]
          · intro u
            by_cases hus : u = s
            · subst hus
              have hS₁s : S₁ (.num u) = false :: encStack rs := by
                simp [S₁, Function.update_of_ne, hkst]
              simp only [Function.update_self, hS₁s, pushDigits_reverse_false, encStack_cons,
                encNat]
            · simp only [Function.update_of_ne (show K.num u ≠ K.num s by intro h; exact hus (K.num.inj h)),
                Function.update_of_ne (num_ne_scr0 u), Function.update_of_ne hus]
              by_cases hut : u = t
              · subst hut; simp [S₁, Function.update_of_ne]
              · simp [S₁, Function.update_of_ne, hus, hut, hrel.stk_num]
        · have hlen := addBitsRaw_length_le (bits a) (bits b) false
          rw [haddBits] at hlen
          simp only [List.length_reverse, bits_length] at hlen ⊢
          have h4 : 4 * (1 + len a + len b) ≤ (P.length + 4) * (1 + len a + len b) :=
            Nat.mul_le_mul_right _ (by omega)
          omega

private theorem step_sub {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s t : SM.Stk} {cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.sub s t))
    (he : SM.exec1 c (.sub s t) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1] at he
  by_cases hst : s = t
  · simp [hst] at he
  · simp only [hst, ↓reduceIte] at he
    cases hs : c.stk s with
    | nil => rw [hs] at he; cases he
    | cons a rs =>
      cases ht : c.stk t with
      | nil => rw [hs, ht] at he; cases he
      | cons b rt =>
        rw [hs, ht] at he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        have hlt := pc_lt_of_getElem? hi
        let pc := clampPc P.length c.pc
        have hkst : K.num s ≠ K.num t := fun h => hst (K.num.inj h)
        have hstep1 : (tm P).step cfg =
            some ⟨some (pc, .subLoop), { cfg.var with carry := false }, cfg.stk⟩ := by
          rw [tm_step_cfg hrel.label, tmProg_at hi .start]; rfl
        obtain ⟨v₁, hsub⟩ := reachesIn_subLoop (P := P) (s := .num s) (t := .num t)
          hkst (num_ne_scr0 s) (num_ne_scr0 t) (self := (pc, .subLoop))
          (onBorrow := (pc, .drainScr0)) (onNoBorrow := (pc, .stripZeros))
          (tmProg_at hi .subLoop) (bits a) (bits b) (encStack rs) (encStack rt) []
          { cfg.var with carry := false } cfg.stk
          (by rw [hrel.stk_num s, hs, encStack_cons, encNat])
          (by rw [hrel.stk_num t, ht, encStack_cons, encNat]) hrel.stk_scr0
        simp only [List.append_nil] at hsub
        let subRes := subBitsRaw (bits a) (bits b) false
        let S₁ := update (update (update cfg.stk (.num s) (false :: encStack rs)) (.num t) (encStack rt))
          .scr0 subRes.1.reverse
        have hsubLen : subRes.1.length = max (bits a).length (bits b).length :=
          subBitsRaw_length (bits a) (bits b) false
        cases hbr : subRes.2 with
        | true =>
          have hab0 : a - b = 0 := subBitsRaw_borrow_true a b hbr
          change ReachesIn (tm P) ⟨some (pc, .subLoop), { cfg.var with carry := false }, cfg.stk⟩
            ⟨some (if subRes.2 then (pc, .drainScr0) else (pc, .stripZeros)), v₁, S₁⟩ _ at hsub
          rw [hbr] at hsub
          simp only [↓reduceIte] at hsub
          have hdrain := reachesIn_drainLoop (P := P) (k := .scr0) (self := (pc, .drainScr0))
            (exitStmt := .goto (fun _ => (clampPc P.length (pc.val + 1), .start)))
            (tmProg_at hi .drainScr0) subRes.1.reverse v₁ S₁ (Function.update_self K.scr0 _ _)
          simp only [stepAux, pc, clampPc_succ_eq hlt] at hdrain
          have hrun := (ReachesIn.step_head hstep1 hsub).trans hdrain
          refine ⟨_, _, ?_, hrun, ?_⟩
          · refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [S₁, Function.update_of_ne, hrel.stk_inp]
            · simp [S₁, Function.update_of_ne, hrel.stk_out]
            · simp [S₁, Function.update_of_ne, hrel.stk_outBuf]
            · simp [S₁, Function.update_of_ne, hrel.stk_ret]
            · simp
            · simp [S₁, Function.update_of_ne, hrel.stk_scr1]
            · intro u
              by_cases hus : u = s
              · subst hus
                simp only [Function.update_self, S₁, Function.update_of_ne (num_ne_scr0 u),
                  Function.update_of_ne hkst, hab0, encStack_cons, encNat_zero, List.singleton_append]
              · simp only [Function.update_of_ne hus, S₁, Function.update_of_ne (num_ne_scr0 u)]
                by_cases hut : u = t
                · subst hut; simp
                · simp [Function.update_of_ne, hus, hut, hrel.stk_num]
          · simp only [List.length_reverse, hsubLen, bits_length]
            have h4 : 4 * (1 + len a + len b) ≤ (P.length + 4) * (1 + len a + len b) :=
              Nat.mul_le_mul_right _ (by omega)
            omega
        | false =>
          have hstripEq : stripLeadingFalse subRes.1.reverse = (bits (a - b)).reverse :=
            subBitsRaw_borrow_false a b hbr
          change ReachesIn (tm P) ⟨some (pc, .subLoop), { cfg.var with carry := false }, cfg.stk⟩
            ⟨some (if subRes.2 then (pc, .drainScr0) else (pc, .stripZeros)), v₁, S₁⟩ _ at hsub
          rw [hbr] at hsub
          simp only [Bool.false_eq_true, ↓reduceIte] at hsub
          obtain ⟨v₂, hstrip⟩ := reachesIn_stripZeros (P := P) (self := (pc, .stripZeros))
            (next := (pc, .moveRestore)) (tmProg_at hi .stripZeros) subRes.1.reverse v₁ S₁
            (Function.update_self K.scr0 _ _)
          let S₂ := update S₁ .scr0 (bits (a - b)).reverse
          rw [hstripEq] at hstrip
          obtain ⟨v₃, hres⟩ := reachesIn_restoreLoop (P := P) (scr := .scr0) (tgt := .num s)
            (scr0_ne_num s) (self := (pc, .moveRestore))
            (exitStmt := .goto (fun _ => (clampPc P.length (pc.val + 1), .start)))
            (tmProg_at hi .moveRestore) (bits (a - b)).reverse v₂ S₂
            (Function.update_self K.scr0 _ _)
          simp only [stepAux, pc, clampPc_succ_eq hlt] at hres
          have hrun := (ReachesIn.step_head hstep1 hsub).trans (hstrip.trans hres)
          refine ⟨_, _, ?_, hrun, ?_⟩
          · refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [S₂, S₁, Function.update_of_ne, hrel.stk_inp]
            · simp [S₂, S₁, Function.update_of_ne, hrel.stk_out]
            · simp [S₂, S₁, Function.update_of_ne, hrel.stk_outBuf]
            · simp [S₂, S₁, Function.update_of_ne, hrel.stk_ret]
            · simp [Function.update_of_ne]
            · simp [S₂, S₁, Function.update_of_ne, hrel.stk_scr1]
            · intro u
              by_cases hus : u = s
              · subst hus
                have hS₂s : S₂ (.num u) = false :: encStack rs := by
                  simp [S₂, S₁, Function.update_of_ne, hkst]
                simp only [Function.update_self, hS₂s, pushDigits_reverse_false,
                  encStack_cons, encNat]
              · simp only [Function.update_of_ne (show K.num u ≠ K.num s by intro h; exact hus (K.num.inj h)),
                  Function.update_of_ne (num_ne_scr0 u), Function.update_of_ne hus, S₂]
                by_cases hut : u = t
                · subst hut; simp [S₁, Function.update_of_ne]
                · simp [S₁, Function.update_of_ne, hus, hut, hrel.stk_num]
          · have hsum := stripLeadingFalse_length_add subRes.1.reverse
            rw [hstripEq, List.length_reverse, List.length_reverse, hsubLen] at hsum
            simp only [List.length_reverse, bits_length] at hsum ⊢
            have h4 : 4 * (1 + len a + len b) ≤ (P.length + 4) * (1 + len a + len b) :=
              Nat.mul_le_mul_right _ (by omega)
            omega

private theorem step_double {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s : SM.Stk} {cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.double s))
    (he : SM.exec1 c (.double s) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1] at he
  cases hstk : c.stk s with
  | nil => rw [hstk] at he; cases he
  | cons v r =>
    rw [hstk] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    have hlt := pc_lt_of_getElem? hi
    have hstks : cfg.stk (.num s) = encNat v ++ encStack r := by
      rw [hrel.stk_num s, hstk, encStack_cons]
    by_cases hv : v = 0
    · subst hv
      have hstep : (tm P).step cfg =
          some ⟨some (clampPc P.length (c.pc + 1), .start), { cfg.var with flag := false }, cfg.stk⟩ := by
        rw [tm_step_cfg hrel.label, tmProg_at hi .start]
        simp only [instrStmt, stepAux, hstks, encNat_zero, List.singleton_append, List.head?_cons,
          clampPc_succ_eq hlt]
        rfl
      refine ⟨_, 1, ?_, ReachesIn.single hstep, one_le_mul_cost P.length (len 0)⟩
      refine ⟨hrel.rs_le, rfl, hrel.stk_inp, hrel.stk_out, hrel.stk_outBuf, hrel.stk_ret,
        hrel.stk_scr0, hrel.stk_scr1, ?_⟩
      intro u
      by_cases hus : u = s
      · subst hus; simpa [hstk] using hrel.stk_num u
      · simp [Function.update_of_ne, hus, hrel.stk_num]
    · cases hb : bits v with
      | nil => exact absurd (bits_eq_nil_iff.mp hb) hv
      | cons d ds =>
        have hstep : (tm P).step cfg =
            some ⟨some (clampPc P.length (c.pc + 1), .start), { cfg.var with flag := true },
              update cfg.stk (.num s) ([true, false] ++ cfg.stk (.num s))⟩ := by
          rw [tm_step_cfg hrel.label, tmProg_at hi .start]
          simp only [instrStmt, stepAux, hstks, encNat, hb, encDigits, List.cons_append,
            List.head?_cons, stepAux_pushList, clampPc_succ_eq hlt]
          rfl
        refine ⟨_, 1, ?_, ReachesIn.single hstep, one_le_mul_cost P.length (len v)⟩
        refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [Function.update_of_ne, hrel.stk_inp]
        · simp [Function.update_of_ne, hrel.stk_out]
        · simp [Function.update_of_ne, hrel.stk_outBuf]
        · simp [Function.update_of_ne, hrel.stk_ret]
        · simp [Function.update_of_ne, hrel.stk_scr0]
        · simp [Function.update_of_ne, hrel.stk_scr1]
        · intro u
          by_cases hus : u = s
          · subst hus
            simp only [Function.update_self, hstks, encStack_cons, encNat_double hv,
              List.cons_append, List.nil_append]
          · simp [Function.update_of_ne, hus, hrel.stk_num]

private theorem step_half {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s : SM.Stk} {cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.half s))
    (he : SM.exec1 c (.half s) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1] at he
  cases hstk : c.stk s with
  | nil => rw [hstk] at he; cases he
  | cons v r =>
    rw [hstk] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    have hlt := pc_lt_of_getElem? hi
    have hstks : cfg.stk (.num s) = encNat v ++ encStack r := by
      rw [hrel.stk_num s, hstk, encStack_cons]
    cases hb : bits v with
    | nil =>
      have hv0 : v = 0 := bits_eq_nil_iff.mp hb
      subst hv0
      have hstep : (tm P).step cfg =
          some ⟨some (clampPc P.length (c.pc + 1), .start), { cfg.var with flag := false }, cfg.stk⟩ := by
        rw [tm_step_cfg hrel.label, tmProg_at hi .start]
        simp only [instrStmt, stepAux, hstks, encNat_zero, List.singleton_append, List.head?_cons,
          clampPc_succ_eq hlt]
        rfl
      refine ⟨_, 1, ?_, ReachesIn.single hstep, one_le_mul_cost P.length (len 0)⟩
      refine ⟨hrel.rs_le, rfl, hrel.stk_inp, hrel.stk_out, hrel.stk_outBuf, hrel.stk_ret,
        hrel.stk_scr0, hrel.stk_scr1, ?_⟩
      intro u
      by_cases hus : u = s
      · subst hus; simpa [hstk] using hrel.stk_num u
      · simp [Function.update_of_ne, hus, hrel.stk_num]
    | cons d ds =>
      have hhalf : bits (v / 2) = ds := by rw [bits_half, hb]; rfl
      have hstep : (tm P).step cfg =
          some ⟨some (clampPc P.length (c.pc + 1), .start), { cfg.var with flag := true },
            update cfg.stk (.num s) (encDigits ds ++ encStack r)⟩ := by
        rw [tm_step_cfg hrel.label, tmProg_at hi .start]
        simp only [instrStmt, stepAux, hstks, encNat, hb, encDigits, List.cons_append,
          List.head?_cons, List.tail_cons, Function.update_self, Function.update_idem,
          clampPc_succ_eq hlt]
        rfl
      refine ⟨_, 1, ?_, ReachesIn.single hstep, one_le_mul_cost P.length (len v)⟩
      refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne, hrel.stk_inp]
      · simp [Function.update_of_ne, hrel.stk_out]
      · simp [Function.update_of_ne, hrel.stk_outBuf]
      · simp [Function.update_of_ne, hrel.stk_ret]
      · simp [Function.update_of_ne, hrel.stk_scr0]
      · simp [Function.update_of_ne, hrel.stk_scr1]
      · intro u
        by_cases hus : u = s
        · subst hus; simp [encStack_cons, encNat, hhalf]
        · simp [Function.update_of_ne, hus, hrel.stk_num]

private theorem step_parity {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s : SM.Stk} {cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.parity s))
    (he : SM.exec1 c (.parity s) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1] at he
  cases hstk : c.stk s with
  | nil => rw [hstk] at he; cases he
  | cons v r =>
    rw [hstk] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    have hlt := pc_lt_of_getElem? hi
    let pc := clampPc P.length c.pc
    have hstks : cfg.stk (.num s) = encNat v ++ encStack r := by
      rw [hrel.stk_num s, hstk, encStack_cons]
    cases hb : bits v with
    | nil =>
      have hv0 : v = 0 := bits_eq_nil_iff.mp hb
      subst hv0
      have hstep : (tm P).step cfg =
          some ⟨some (clampPc P.length (c.pc + 1), .start), { cfg.var with flag := false },
            update cfg.stk (.num s) (false :: encStack r)⟩ := by
        rw [tm_step_cfg hrel.label, tmProg_at hi .start]
        simp only [instrStmt, stepAux, hstks, encNat_zero, List.singleton_append, List.head?_cons,
          List.tail_cons, Function.update_self, Function.update_idem, clampPc_succ_eq hlt]
        rfl
      refine ⟨_, 1, ?_, ReachesIn.single hstep, one_le_mul_cost P.length (len 0)⟩
      refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne, hrel.stk_inp]
      · simp [Function.update_of_ne, hrel.stk_out]
      · simp [Function.update_of_ne, hrel.stk_outBuf]
      · simp [Function.update_of_ne, hrel.stk_ret]
      · simp [Function.update_of_ne, hrel.stk_scr0]
      · simp [Function.update_of_ne, hrel.stk_scr1]
      · intro u
        by_cases hus : u = s
        · subst hus; simp [encStack_cons, encNat_zero]
        · simp [Function.update_of_ne, hus, hrel.stk_num]
    | cons d ds =>
      have hmod := mod_two_of_bits hb
      have hstep1 : (tm P).step cfg =
          some ⟨some (pc, .parityLoop), { cfg.var with flag := true, bit := d },
            update cfg.stk (.num s) (encDigits ds ++ encStack r)⟩ := by
        rw [tm_step_cfg hrel.label, tmProg_at hi .start]
        simp only [instrStmt, stepAux, hstks, encNat, hb, encDigits, List.cons_append,
          List.head?_cons, List.tail_cons, Function.update_self, Function.update_idem]
        rfl
      have hloop := reachesIn_popLoop (P := P) (s := .num s) (self := (pc, .parityLoop))
        (exitStmt := .branch (fun v => v.bit)
          (pushList (.num s) [true, true, false] (.goto (fun _ => (clampPc P.length (pc.val + 1), .start))))
          (pushList (.num s) [false] (.goto (fun _ => (clampPc P.length (pc.val + 1), .start)))))
        (tmProg_at hi .parityLoop) ds (encStack r) { cfg.var with flag := true, bit := d }
        (update cfg.stk (.num s) (encDigits ds ++ encStack r)) (Function.update_self _ _ _)
      simp only [Function.update_idem, stepAux, stepAux_pushList, pc, clampPc_succ_eq hlt] at hloop
      have hrun := ReachesIn.step_head hstep1 hloop
      have hlen : ds.length + 1 = len v := by
        have := bits_length v; rw [hb, List.length_cons] at this; exact this
      cases d with
      | true =>
        simp only [Bool.cond_true, Function.update_self] at hrun
        refine ⟨_, _, ?_, hrun, ?_⟩
        · refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [Function.update_of_ne, hrel.stk_inp]
          · simp [Function.update_of_ne, hrel.stk_out]
          · simp [Function.update_of_ne, hrel.stk_outBuf]
          · simp [Function.update_of_ne, hrel.stk_ret]
          · simp [Function.update_of_ne, hrel.stk_scr0]
          · simp [Function.update_of_ne, hrel.stk_scr1]
          · intro u
            by_cases hus : u = s
            · subst hus; simp [hmod, encStack_cons, encNat_one]
            · simp [Function.update_of_ne, hus, hrel.stk_num]
        · have h1 : 1 * (1 + len v) ≤ (P.length + 4) * (1 + len v) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
      | false =>
        simp only [Bool.cond_false, Function.update_self] at hrun
        refine ⟨_, _, ?_, hrun, ?_⟩
        · refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [Function.update_of_ne, hrel.stk_inp]
          · simp [Function.update_of_ne, hrel.stk_out]
          · simp [Function.update_of_ne, hrel.stk_outBuf]
          · simp [Function.update_of_ne, hrel.stk_ret]
          · simp [Function.update_of_ne, hrel.stk_scr0]
          · simp [Function.update_of_ne, hrel.stk_scr1]
          · intro u
            by_cases hus : u = s
            · subst hus; simp [hmod, encStack_cons, encNat_zero]
            · simp [Function.update_of_ne, hus, hrel.stk_num]
        · have h1 : 1 * (1 + len v) ≤ (P.length + 4) * (1 + len v) :=
            Nat.mul_le_mul_right _ (by omega)
          omega

private theorem step_jz {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s : SM.Stk} {l cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.jz s l))
    (he : SM.exec1 c (.jz s l) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1] at he
  cases hstk : c.stk s with
  | nil => rw [hstk] at he; cases he
  | cons v r =>
    rw [hstk] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    have hlt := pc_lt_of_getElem? hi
    let pc := clampPc P.length c.pc
    have hstks : cfg.stk (.num s) = encNat v ++ encStack r := by
      rw [hrel.stk_num s, hstk, encStack_cons]
    cases hb : bits v with
    | nil =>
      have hv0 : v = 0 := bits_eq_nil_iff.mp hb
      subst hv0
      have hstep : (tm P).step cfg =
          some ⟨some (clampPc P.length l, .start), { cfg.var with flag := false },
            update cfg.stk (.num s) (encStack r)⟩ := by
        rw [tm_step_cfg hrel.label, tmProg_at hi .start]
        simp only [instrStmt, stepAux, hstks, encNat_zero, List.singleton_append, List.head?_cons,
          List.tail_cons]
        rfl
      refine ⟨_, 1, ?_, ReachesIn.single hstep, one_le_mul_cost P.length (len 0)⟩
      refine ⟨hrel.rs_le, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne, hrel.stk_inp]
      · simp [Function.update_of_ne, hrel.stk_out]
      · simp [Function.update_of_ne, hrel.stk_outBuf]
      · simp [Function.update_of_ne, hrel.stk_ret]
      · simp [Function.update_of_ne, hrel.stk_scr0]
      · simp [Function.update_of_ne, hrel.stk_scr1]
      · intro u
        by_cases hus : u = s
        · subst hus; simp
        · simp [Function.update_of_ne, hus, hrel.stk_num]
    | cons d ds =>
      have hvne : v ≠ 0 := by intro hv; subst hv; rw [bits_zero] at hb; cases hb
      have hstep1 : (tm P).step cfg =
          some ⟨some (pc, .popLoop), { cfg.var with flag := true },
            update cfg.stk (.num s) (encDigits ds ++ encStack r)⟩ := by
        rw [tm_step_cfg hrel.label, tmProg_at hi .start]
        simp only [instrStmt, stepAux, hstks, encNat, hb, encDigits, List.cons_append,
          List.head?_cons, List.tail_cons, Function.update_self, Function.update_idem]
        rfl
      have hloop := reachesIn_popLoop (P := P) (s := .num s) (self := (pc, .popLoop))
        (exitStmt := .goto (fun _ => (clampPc P.length (pc.val + 1), .start)))
        (tmProg_at hi .popLoop) ds (encStack r) { cfg.var with flag := true }
        (update cfg.stk (.num s) (encDigits ds ++ encStack r)) (Function.update_self _ _ _)
      simp only [Function.update_idem, stepAux, pc, clampPc_succ_eq hlt] at hloop
      have hrun := ReachesIn.step_head hstep1 hloop
      have hlen : ds.length + 1 = len v := by
        have := bits_length v; rw [hb, List.length_cons] at this; exact this
      refine ⟨_, _, ?_, hrun, ?_⟩
      · refine ⟨hrel.rs_le, by simp [hvne], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [Function.update_of_ne, hrel.stk_inp]
        · simp [Function.update_of_ne, hrel.stk_out]
        · simp [Function.update_of_ne, hrel.stk_outBuf]
        · simp [Function.update_of_ne, hrel.stk_ret]
        · simp [Function.update_of_ne, hrel.stk_scr0]
        · simp [Function.update_of_ne, hrel.stk_scr1]
        · intro u
          by_cases hus : u = s
          · subst hus; simp
          · simp [Function.update_of_ne, hus, hrel.stk_num]
      · have h1 : 1 * (1 + len v) ≤ (P.length + 4) * (1 + len v) :=
          Nat.mul_le_mul_right _ (by omega)
        omega

private theorem step_jmp {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {l cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.jmp l))
    (he : SM.exec1 c (.jmp l) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1, Option.some.injEq, Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩
  have hstep : (tm P).step cfg = some ⟨some (clampPc P.length l, .start), cfg.var, cfg.stk⟩ := by
    rw [tm_step_cfg hrel.label, tmProg_at hi .start]; rfl
  refine ⟨_, 1, ?_, ReachesIn.single hstep, by omega⟩
  exact ⟨hrel.rs_le, rfl, hrel.stk_inp, hrel.stk_out, hrel.stk_outBuf, hrel.stk_ret,
    hrel.stk_scr0, hrel.stk_scr1, hrel.stk_num⟩

private theorem step_jnil {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s : SM.Stk} {l cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.jnil s l))
    (he : SM.exec1 c (.jnil s l) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1, Option.some.injEq, Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩
  have hlt := pc_lt_of_getElem? hi
  cases hstk : c.stk s with
  | nil =>
    have hstep : (tm P).step cfg =
        some ⟨some (clampPc P.length l, .start), { cfg.var with flag := true }, cfg.stk⟩ := by
      rw [tm_step_cfg hrel.label, tmProg_at hi .start]
      simp only [instrStmt, stepAux, hrel.stk_num s, hstk, encStack_nil, List.head?_nil,
        Option.isNone_none, Bool.cond_true]
      rfl
    refine ⟨_, 1, ?_, ReachesIn.single hstep, by omega⟩
    exact ⟨hrel.rs_le, by simp, hrel.stk_inp, hrel.stk_out, hrel.stk_outBuf,
      hrel.stk_ret, hrel.stk_scr0, hrel.stk_scr1, hrel.stk_num⟩
  | cons v r =>
    have hne : cfg.stk (.num s) ≠ [] := by
      rw [hrel.stk_num s, hstk]
      intro h; cases encStack_eq_nil_iff.mp h
    cases hcons : cfg.stk (.num s) with
    | nil => exact absurd hcons hne
    | cons b bs =>
      have hstep : (tm P).step cfg =
          some ⟨some (clampPc P.length (c.pc + 1), .start), { cfg.var with flag := false }, cfg.stk⟩ := by
        rw [tm_step_cfg hrel.label, tmProg_at hi .start]
        simp only [instrStmt, stepAux, hcons, List.head?_cons, Option.isNone_some, Bool.cond_false,
          clampPc_succ_eq hlt]
        rfl
      refine ⟨_, 1, ?_, ReachesIn.single hstep, by omega⟩
      exact ⟨hrel.rs_le, by simp, hrel.stk_inp, hrel.stk_out, hrel.stk_outBuf,
        hrel.stk_ret, hrel.stk_scr0, hrel.stk_scr1, hrel.stk_num⟩

private theorem step_call {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {l cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.call l))
    (he : SM.exec1 c (.call l) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1, Option.some.injEq, Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩
  have hlt := pc_lt_of_getElem? hi
  have hstep : (tm P).step cfg =
      some ⟨some (clampPc P.length l, .start), cfg.var,
        update cfg.stk .ret (encRet (c.pc + 1) ++ cfg.stk .ret)⟩ := by
    rw [tm_step_cfg hrel.label, tmProg_at hi .start]
    simp only [instrStmt, stepAux_pushList, stepAux, clampPc_val_of_lt hlt]
    rfl
  refine ⟨_, 1, ?_, ReachesIn.single hstep, by omega⟩
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · omega
    · exact hrel.rs_le r hr
  · simp [Function.update_of_ne, hrel.stk_inp]
  · simp [Function.update_of_ne, hrel.stk_out]
  · simp [Function.update_of_ne, hrel.stk_outBuf]
  · simp [hrel.stk_ret, encRetStack_cons]
  · simp [Function.update_of_ne, hrel.stk_scr0]
  · simp [Function.update_of_ne, hrel.stk_scr1]
  · intro u; simp [Function.update_of_ne, hrel.stk_num]

private theorem step_ret {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some .ret)
    (he : SM.exec1 c .ret = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1] at he
  cases hrs : c.rs with
  | nil => rw [hrs] at he; cases he
  | cons r rs =>
    rw [hrs] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    let pc := clampPc P.length c.pc
    have hrle : r ≤ P.length := hrel.rs_le r (by simp [hrs])
    let v₀ : State P.length := { cfg.var with addr := ⟨0, Nat.zero_lt_succ P.length⟩ }
    have hstep1 : (tm P).step cfg = some ⟨some (pc, .retLoop), v₀, cfg.stk⟩ := by
      rw [tm_step_cfg hrel.label, tmProg_at hi .start]; rfl
    obtain ⟨v', hloop⟩ := reachesIn_retLoop (P := P) (self := (pc, .retLoop))
      (tmProg_at hi .retLoop) r (encRetStack rs) v₀ cfg.stk
      (by rw [hrel.stk_ret, hrs, encRetStack_cons]) (by simp [v₀]; exact hrle)
    have hfin : (⟨v₀.addr.val + r, Nat.lt_succ_of_le (by simp [v₀]; exact hrle)⟩ : Fin (P.length + 1)) =
        clampPc P.length r := by
      ext; simp [v₀, clampPc, Nat.min_eq_left hrle]
    rw [hfin] at hloop
    have hrun := ReachesIn.step_head hstep1 hloop
    refine ⟨_, _, ?_, hrun, by omega⟩
    refine ⟨fun x hx => hrel.rs_le x (by simp [hrs, hx]), rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Function.update_of_ne, hrel.stk_inp]
    · simp [Function.update_of_ne, hrel.stk_out]
    · simp [Function.update_of_ne, hrel.stk_outBuf]
    · simp
    · simp [Function.update_of_ne, hrel.stk_scr0]
    · simp [Function.update_of_ne, hrel.stk_scr1]
    · intro u; simp [Function.update_of_ne, hrel.stk_num]

private theorem step_read {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s : SM.Stk} {cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.read s))
    (he : SM.exec1 c (.read s) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1] at he
  have hlt := pc_lt_of_getElem? hi
  cases hinp : c.inp with
  | nil =>
    rw [hinp] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    have hstep : (tm P).step cfg =
        some ⟨some (clampPc P.length (c.pc + 1), .start),
          { cfg.var with flag := false, bit := false },
          update (update cfg.stk .inp []) (.num s) (encNat 2 ++ cfg.stk (.num s))⟩ := by
      rw [tm_step_cfg hrel.label, tmProg_at hi .start]
      simp only [instrStmt, stepAux, hrel.stk_inp, hinp, List.head?_nil, List.tail_nil,
        Bool.cond_false, stepAux_pushList, Function.update_of_ne (num_ne_inp s),
        clampPc_succ_eq hlt]
      rfl
    refine ⟨_, 1, ?_, ReachesIn.single hstep, by omega⟩
    refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Function.update_of_ne]
    · simp [Function.update_of_ne, hrel.stk_out]
    · simp [Function.update_of_ne, hrel.stk_outBuf]
    · simp [Function.update_of_ne, hrel.stk_ret]
    · simp [Function.update_of_ne, hrel.stk_scr0]
    · simp [Function.update_of_ne, hrel.stk_scr1]
    · intro u
      by_cases hus : u = s
      · subst hus; simp [hrel.stk_num, encStack_cons]
      · simp [Function.update_of_ne, hus, hrel.stk_num]
  | cons b x =>
    rw [hinp] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    cases b with
    | true =>
      have hstep : (tm P).step cfg =
          some ⟨some (clampPc P.length (c.pc + 1), .start),
            { cfg.var with flag := true, bit := true },
            update (update cfg.stk .inp x) (.num s) (encNat 1 ++ cfg.stk (.num s))⟩ := by
        rw [tm_step_cfg hrel.label, tmProg_at hi .start]
        simp only [instrStmt, stepAux, hrel.stk_inp, hinp, List.head?_cons, List.tail_cons,
          Bool.cond_true, stepAux_pushList, Function.update_of_ne (num_ne_inp s),
          clampPc_succ_eq hlt]
        rfl
      refine ⟨_, 1, ?_, ReachesIn.single hstep, by omega⟩
      refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne]
      · simp [Function.update_of_ne, hrel.stk_out]
      · simp [Function.update_of_ne, hrel.stk_outBuf]
      · simp [Function.update_of_ne, hrel.stk_ret]
      · simp [Function.update_of_ne, hrel.stk_scr0]
      · simp [Function.update_of_ne, hrel.stk_scr1]
      · intro u
        by_cases hus : u = s
        · subst hus; simp [hrel.stk_num, encStack_cons]
        · simp [Function.update_of_ne, hus, hrel.stk_num]
    | false =>
      have hstep : (tm P).step cfg =
          some ⟨some (clampPc P.length (c.pc + 1), .start),
            { cfg.var with flag := true, bit := false },
            update (update cfg.stk .inp x) (.num s) (encNat 0 ++ cfg.stk (.num s))⟩ := by
        rw [tm_step_cfg hrel.label, tmProg_at hi .start]
        simp only [instrStmt, stepAux, hrel.stk_inp, hinp, List.head?_cons, List.tail_cons,
          Bool.cond_true, Bool.cond_false, stepAux_pushList,
          Function.update_of_ne (num_ne_inp s), clampPc_succ_eq hlt]
        rfl
      refine ⟨_, 1, ?_, ReachesIn.single hstep, by omega⟩
      refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne]
      · simp [Function.update_of_ne, hrel.stk_out]
      · simp [Function.update_of_ne, hrel.stk_outBuf]
      · simp [Function.update_of_ne, hrel.stk_ret]
      · simp [Function.update_of_ne, hrel.stk_scr0]
      · simp [Function.update_of_ne, hrel.stk_scr1]
      · intro u
        by_cases hus : u = s
        · subst hus; simp [hrel.stk_num, encStack_cons]
        · simp [Function.update_of_ne, hus, hrel.stk_num]

private theorem step_write {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg}
    {s : SM.Stk} {cost : ℕ}
    (hrel : Rel P c cfg) (hi : P[c.pc]? = some (.write s))
    (he : SM.exec1 c (.write s) = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.exec1] at he
  cases hstk : c.stk s with
  | nil => rw [hstk] at he; cases he
  | cons v r =>
    rw [hstk] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    have hlt := pc_lt_of_getElem? hi
    let pc := clampPc P.length c.pc
    have hstks : cfg.stk (.num s) = encNat v ++ encStack r := by
      rw [hrel.stk_num s, hstk, encStack_cons]
    cases hb : bits v with
    | nil =>
      have hv0 : v = 0 := bits_eq_nil_iff.mp hb
      subst hv0
      have hstep : (tm P).step cfg =
          some ⟨some (clampPc P.length (c.pc + 1), .start), { cfg.var with flag := false },
            update (update cfg.stk (.num s) (encStack r)) .outBuf (false :: cfg.stk .outBuf)⟩ := by
        rw [tm_step_cfg hrel.label, tmProg_at hi .start]
        simp only [instrStmt, stepAux, hstks, encNat_zero, List.singleton_append, List.head?_cons,
          List.tail_cons, Function.update_of_ne (outBuf_ne_num s), clampPc_succ_eq hlt]
        rfl
      refine ⟨_, 1, ?_, ReachesIn.single hstep, one_le_mul_cost P.length (len 0)⟩
      refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne, hrel.stk_inp]
      · simp [Function.update_of_ne, hrel.stk_out]
      · simp [hrel.stk_outBuf]
      · simp [Function.update_of_ne, hrel.stk_ret]
      · simp [Function.update_of_ne, hrel.stk_scr0]
      · simp [Function.update_of_ne, hrel.stk_scr1]
      · intro u
        by_cases hus : u = s
        · subst hus; simp [Function.update_of_ne]
        · simp [Function.update_of_ne, hus, hrel.stk_num]
    | cons d ds =>
      have hvne : v ≠ 0 := by intro hv; subst hv; rw [bits_zero] at hb; cases hb
      let S₁ := update (update cfg.stk (.num s) (encDigits ds ++ encStack r)) .outBuf
        (true :: cfg.stk .outBuf)
      have hstep1 : (tm P).step cfg = some ⟨some (pc, .popLoop), { cfg.var with flag := true }, S₁⟩ := by
        rw [tm_step_cfg hrel.label, tmProg_at hi .start]
        simp only [instrStmt, stepAux, hstks, encNat, hb, encDigits, List.cons_append,
          List.head?_cons, List.tail_cons, Function.update_self, Function.update_idem,
          Function.update_of_ne (outBuf_ne_num s), S₁]
        rfl
      have hloop := reachesIn_popLoop (P := P) (s := .num s) (self := (pc, .popLoop))
        (exitStmt := .goto (fun _ => (clampPc P.length (pc.val + 1), .start)))
        (tmProg_at hi .popLoop) ds (encStack r) { cfg.var with flag := true } S₁
        (by simp [S₁, Function.update_of_ne])
      simp only [stepAux, pc, clampPc_succ_eq hlt] at hloop
      have hrun := ReachesIn.step_head hstep1 hloop
      have hlen : ds.length + 1 = len v := by
        have := bits_length v; rw [hb, List.length_cons] at this; exact this
      refine ⟨_, _, ?_, hrun, ?_⟩
      · refine ⟨hrel.rs_le, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [S₁, Function.update_of_ne, hrel.stk_inp]
        · simp [S₁, Function.update_of_ne, hrel.stk_out]
        · simp [S₁, Function.update_of_ne, hrel.stk_outBuf, hvne]
        · simp [S₁, Function.update_of_ne, hrel.stk_ret]
        · simp [S₁, Function.update_of_ne, hrel.stk_scr0]
        · simp [S₁, Function.update_of_ne, hrel.stk_scr1]
        · intro u
          by_cases hus : u = s
          · subst hus; simp
          · simp [S₁, Function.update_of_ne, hus, hrel.stk_num]
      · have h1 : 1 * (1 + len v) ≤ (P.length + 4) * (1 + len v) :=
          Nat.mul_le_mul_right _ (by omega)
        omega

/-- One step of the stack machine program `P` of cost `cost` is simulated by at most
`(P.length + 4) * cost` steps of `tm P`, preserving the simulation relation `Rel P`. -/
theorem step_sim {P : SM.Program} {c c' : SM.Config} {cfg : (tm P).Cfg} {cost : ℕ}
    (hrel : Rel P c cfg) (hstep : SM.step P c = some (c', cost)) :
    ∃ cfg' steps, Rel P c' cfg' ∧ ReachesIn (tm P) cfg cfg' steps ∧
      steps ≤ (P.length + 4) * cost := by
  simp only [SM.step] at hstep
  cases hi : P[c.pc]? with
  | none => rw [hi] at hstep; cases hstep
  | some i =>
    rw [hi] at hstep
    cases i with
    | push s k => exact step_push hrel hi hstep
    | pop s => exact step_pop hrel hi hstep
    | copy s t => exact step_copy hrel hi hstep
    | move s t => exact step_move hrel hi hstep
    | add s t => exact step_add hrel hi hstep
    | sub s t => exact step_sub hrel hi hstep
    | double s => exact step_double hrel hi hstep
    | half s => exact step_half hrel hi hstep
    | parity s => exact step_parity hrel hi hstep
    | jz s l => exact step_jz hrel hi hstep
    | jmp l => exact step_jmp hrel hi hstep
    | jnil s l => exact step_jnil hrel hi hstep
    | call l => exact step_call hrel hi hstep
    | ret => exact step_ret hrel hi hstep
    | read s => exact step_read hrel hi hstep
    | write s => exact step_write hrel hi hstep
    | halt => simp [SM.exec1] at hstep

end GI.Turing.TM
