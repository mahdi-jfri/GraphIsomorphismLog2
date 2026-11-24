/-
Basic lemmas for the stack machine (`Workspace.Turing.SM`) and small reusable gadgets used by the
log-cost RAM compiler.

We fix two additional stacks besides `E` and `Mem`: `R` (stack 2) for the current procedure's
registers, and `F` (stack 3) for saved caller register frames. We prove single-instruction run
lemmas under `CodeAt`, properties of `Keeps`, `memOf`, and `listSize`, and four small code gadgets:
emptying `R`, saving `R` onto `F`, restoring `R` from `F`, and building `R` from argument values
on `E`.
-/
module

public import Workspace.Turing.Interface
public import Workspace.Machine.Len

@[expose] public section

namespace GI.Turing.Core

open GI.Machine (len)
open GI.Turing (E Mem memOf listSize Keeps)
open GI.Turing.SM

/-! ### Stacks -/

/-- The stack holding the current procedure's register file as `(reg, val)` pairs. -/
abbrev R : Stk := 2

/-- The stack holding saved caller register frames. -/
abbrev F : Stk := 3

theorem E_ne_Mem : E ≠ Mem := by decide
theorem E_ne_R : E ≠ R := by decide
theorem E_ne_F : E ≠ F := by decide
theorem Mem_ne_R : Mem ≠ R := by decide
theorem Mem_ne_F : Mem ≠ F := by decide
theorem R_ne_F : R ≠ F := by decide

/-! ### Properties of `Keeps` -/

theorem keeps_refl (ss : List Stk) (c : Config) : Keeps ss c c :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem keeps_trans {ss : List Stk} {c₁ c₂ c₃ : Config}
    (h₁ : Keeps ss c₁ c₂) (h₂ : Keeps ss c₂ c₃) : Keeps ss c₁ c₃ :=
  ⟨fun t ht => (h₂.1 t ht).trans (h₁.1 t ht),
    h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem keeps_mono {ss₁ ss₂ : List Stk} {c c' : Config}
    (hsub : ∀ t, t ∈ ss₁ → t ∈ ss₂) (h : Keeps ss₁ c c') : Keeps ss₂ c c' :=
  ⟨fun t ht => h.1 t (fun ht₁ => ht (hsub t ht₁)), h.2.1, h.2.2.1, h.2.2.2⟩

theorem keeps_stk_eq {ss : List Stk} {c c' : Config} (h : Keeps ss c c')
    {t : Stk} (ht : t ∉ ss) : c'.stk t = c.stk t :=
  h.1 t ht

/-! ### Properties of `memOf` and `listSize` -/

theorem memOf_nil : memOf [] = fun _ => 0 := rfl

theorem memOf_cons_cons (a v : ℕ) (rest : List ℕ) :
    memOf (a :: v :: rest) = Function.update (memOf rest) a v := by
  funext x
  simp only [memOf, Function.update_apply]
  by_cases h : x = a
  · subst h; simp
  · simp [h, Ne.symm h]

@[simp] theorem listSize_nil : listSize [] = 0 := rfl

@[simp] theorem listSize_cons (v : ℕ) (rest : List ℕ) :
    listSize (v :: rest) = len v + 1 + listSize rest := rfl

theorem listSize_append (l₁ l₂ : List ℕ) :
    listSize (l₁ ++ l₂) = listSize l₁ + listSize l₂ := by
  simp [listSize, List.map_append, List.sum_append]

/-! ### Single-instruction run lemmas -/

theorem steps_push {P : Program} {a : ℕ} {cfg : Config} {s : Stk} {k : ℕ}
    (hc : P[a]? = some (.push s k)) (hpc : cfg.pc = a) :
    ∃ cfg', Steps P cfg cfg' (1 + len k) ∧ cfg'.pc = a + 1 ∧
      cfg'.stk s = k :: cfg.stk s ∧ Keeps [s] cfg cfg' := by
  refine ⟨{ cfg with pc := a + 1, stk := Function.update cfg.stk s (k :: cfg.stk s) }, ?_,
    rfl, ?_, ?_⟩
  · apply Steps.single
    rw [step_eq (hpc ▸ hc)]
    simp [exec1, hpc]
  · simp
  · refine ⟨fun t ht => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at ht
    exact Function.update_of_ne ht _ _

theorem steps_pop {P : Program} {a : ℕ} {cfg : Config} {s : Stk} {v : ℕ} {rest : List ℕ}
    (hc : P[a]? = some (.pop s)) (hpc : cfg.pc = a) (hs : cfg.stk s = v :: rest) :
    ∃ cfg', Steps P cfg cfg' (1 + len v) ∧ cfg'.pc = a + 1 ∧
      cfg'.stk s = rest ∧ Keeps [s] cfg cfg' := by
  refine ⟨{ cfg with pc := a + 1, stk := Function.update cfg.stk s rest }, ?_, rfl, ?_, ?_⟩
  · apply Steps.single
    rw [step_eq (hpc ▸ hc)]
    simp [exec1, hs, hpc]
  · simp
  · refine ⟨fun t ht => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at ht
    exact Function.update_of_ne ht _ _

theorem steps_move {P : Program} {a : ℕ} {cfg : Config} {s t : Stk} {v : ℕ} {rest : List ℕ}
    (hne : s ≠ t) (hc : P[a]? = some (.move s t)) (hpc : cfg.pc = a)
    (hs : cfg.stk s = v :: rest) :
    ∃ cfg', Steps P cfg cfg' (1 + len v) ∧ cfg'.pc = a + 1 ∧
      cfg'.stk s = rest ∧ cfg'.stk t = v :: cfg.stk t ∧ Keeps [s, t] cfg cfg' := by
  let st1 := Function.update cfg.stk s rest
  let st2 := Function.update st1 t (v :: st1 t)
  refine ⟨{ cfg with pc := a + 1, stk := st2 }, ?_, rfl, ?_, ?_, ?_⟩
  · apply Steps.single
    rw [step_eq (hpc ▸ hc)]
    simp [exec1, hs, hpc, st1, st2]
  · simp only [st2, st1, Function.update_of_ne hne, Function.update_self]
  · simp only [st2, st1, Function.update_self, Function.update_of_ne hne.symm]
  · refine ⟨fun u hu => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    simp only [st2, st1, Function.update_of_ne hu.2, Function.update_of_ne hu.1]

theorem steps_jz {P : Program} {a l : ℕ} {cfg : Config} {s : Stk} {v : ℕ} {rest : List ℕ}
    (hc : P[a]? = some (.jz s l)) (hpc : cfg.pc = a) (hs : cfg.stk s = v :: rest) :
    ∃ cfg', Steps P cfg cfg' (1 + len v) ∧
      cfg'.pc = (if v = 0 then l else a + 1) ∧
      cfg'.stk s = rest ∧ Keeps [s] cfg cfg' := by
  refine ⟨{ cfg with pc := if v = 0 then l else a + 1, stk := Function.update cfg.stk s rest },
    ?_, rfl, ?_, ?_⟩
  · apply Steps.single
    rw [step_eq (hpc ▸ hc)]
    simp [exec1, hs, hpc]
  · simp
  · refine ⟨fun t ht => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at ht
    exact Function.update_of_ne ht _ _

theorem steps_jmp {P : Program} {a l : ℕ} {cfg : Config}
    (hc : P[a]? = some (.jmp l)) (hpc : cfg.pc = a) :
    ∃ cfg', Steps P cfg cfg' 1 ∧ cfg'.pc = l ∧ Keeps [] cfg cfg' := by
  refine ⟨{ cfg with pc := l }, ?_, rfl, keeps_refl [] cfg⟩
  apply Steps.single
  rw [step_eq (hpc ▸ hc)]
  rfl

theorem steps_jnil {P : Program} {a l : ℕ} {cfg : Config} {s : Stk}
    (hc : P[a]? = some (.jnil s l)) (hpc : cfg.pc = a) :
    ∃ cfg', Steps P cfg cfg' 1 ∧
      cfg'.pc = (if cfg.stk s = [] then l else a + 1) ∧ Keeps [] cfg cfg' := by
  refine ⟨{ cfg with pc := if cfg.stk s = [] then l else a + 1 }, ?_, rfl, keeps_refl [] cfg⟩
  apply Steps.single
  rw [step_eq (hpc ▸ hc)]
  simp [exec1, hpc]

theorem steps_call {P : Program} {a l : ℕ} {cfg : Config}
    (hc : P[a]? = some (.call l)) (hpc : cfg.pc = a) :
    ∃ cfg', Steps P cfg cfg' 1 ∧ cfg'.pc = l ∧
      cfg'.rs = (a + 1) :: cfg.rs ∧
      (∀ t, cfg'.stk t = cfg.stk t) ∧ cfg'.inp = cfg.inp ∧ cfg'.out = cfg.out := by
  refine ⟨{ cfg with pc := l, rs := (a + 1) :: cfg.rs }, ?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  apply Steps.single
  rw [step_eq (hpc ▸ hc)]
  simp [exec1, hpc]

theorem steps_ret {P : Program} {a r : ℕ} {rs : List ℕ} {cfg : Config}
    (hc : P[a]? = some .ret) (hpc : cfg.pc = a) (hrs : cfg.rs = r :: rs) :
    ∃ cfg', Steps P cfg cfg' 1 ∧ cfg'.pc = r ∧ cfg'.rs = rs ∧
      (∀ t, cfg'.stk t = cfg.stk t) ∧ cfg'.inp = cfg.inp ∧ cfg'.out = cfg.out := by
  refine ⟨{ cfg with pc := r, rs := rs }, ?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  apply Steps.single
  rw [step_eq (hpc ▸ hc)]
  simp [exec1, hrs]

/-! ### Gadget 1: emptying `R` -/

/-- Code placed at `a` that empties stack `R`. -/
def emptyR (a : ℕ) : List Instr :=
  [.jnil R (a + 3), .pop R, .jmp a]

@[simp] theorem emptyR_length (a : ℕ) : (emptyR a).length = 3 := rfl

/-- `emptyR a` empties `R`, keeps all other stacks, and costs at most `3 * listSize (cfg.stk R) + 1`. -/
theorem steps_emptyR {P : Program} {a : ℕ} {cfg : Config}
    (hc : CodeAt P a (emptyR a)) (hpc : cfg.pc = a) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + 3 ∧ cfg'.stk R = [] ∧
      Keeps [R] cfg cfg' ∧ S ≤ 3 * listSize (cfg.stk R) + 1 := by
  generalize hr : cfg.stk R = r
  induction r generalizing cfg with
  | nil =>
    have h0 : P[a]? = some (.jnil R (a + 3)) := hc.cons
    obtain ⟨c1, hs1, hpc1, hk1⟩ := steps_jnil h0 hpc
    simp only [hr, ↓reduceIte] at hpc1
    exact ⟨c1, 1, hs1, hpc1, by rw [keeps_stk_eq hk1 (by simp), hr],
      keeps_mono (by simp) hk1, by simp⟩
  | cons v rest ih =>
    have h0 : P[a]? = some (.jnil R (a + 3)) := hc.cons
    have h1 : P[a + 1]? = some (.pop R) := hc.tail.cons
    have h2 : P[a + 2]? = some (.jmp a) := by
      simpa [Nat.add_assoc] using hc.tail.tail.cons
    obtain ⟨c1, hs1, hpc1, hk1⟩ := steps_jnil h0 hpc
    simp only [hr, List.cons_ne_nil, ↓reduceIte] at hpc1
    have hR1 : c1.stk R = v :: rest := by rw [keeps_stk_eq hk1 (by simp), hr]
    obtain ⟨c2, hs2, hpc2, hR2, hk2⟩ := steps_pop h1 hpc1 hR1
    obtain ⟨c3, hs3, hpc3, hk3⟩ := steps_jmp h2 (by omega)
    have hR3 : c3.stk R = rest := by rw [keeps_stk_eq hk3 (by simp), hR2]
    obtain ⟨c4, S4, hs4, hpc4, hR4, hk4, hcost4⟩ := ih hpc3 hR3
    refine ⟨c4, 1 + (1 + len v) + 1 + S4,
      ((hs1.trans hs2).trans hs3).trans hs4, hpc4, hR4, ?_, ?_⟩
    · exact keeps_trans (keeps_trans (keeps_mono (by simp) hk1) hk2)
        (keeps_trans (keeps_mono (by simp) hk3) hk4)
    · simp only [listSize_cons]; omega

/-! ### Gadgets 2 and 3: saving `R` onto `F` and restoring `R` from `F` -/

/-- Encoding of a saved frame on `F`: each element of `r` is pushed onto `acc` followed by tag `1`. -/
def pushFrame : List ℕ → List ℕ → List ℕ
  | [], acc => acc
  | v :: r, acc => pushFrame r (1 :: v :: acc)

/-- Code placed at `a` that moves `R` onto `F` with a `0` sentinel below and `1` tags above each
entry. -/
def saveR (a : ℕ) : List Instr :=
  [.push F 0, .jnil R (a + 5), .move R F, .push F 1, .jmp (a + 1)]

@[simp] theorem saveR_length (a : ℕ) : (saveR a).length = 5 := rfl

/-- The loop body of `saveR`, starting at `a + 1`. -/
private theorem steps_saveRLoop {P : Program} {a : ℕ} {cfg : Config} {r : List ℕ}
    (h1 : P[a + 1]? = some (.jnil R (a + 5)))
    (h2 : P[a + 2]? = some (.move R F))
    (h3 : P[a + 3]? = some (.push F 1))
    (h4 : P[a + 4]? = some (.jmp (a + 1)))
    (hpc : cfg.pc = a + 1) (hr : cfg.stk R = r) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + 5 ∧
      cfg'.stk R = [] ∧ cfg'.stk F = pushFrame r (cfg.stk F) ∧
      Keeps [R, F] cfg cfg' ∧ S ≤ 5 * listSize r + 1 := by
  induction r generalizing cfg with
  | nil =>
    obtain ⟨c1, hs1, hpc1, hk1⟩ := steps_jnil h1 hpc
    simp only [hr, ↓reduceIte] at hpc1
    exact ⟨c1, 1, hs1, hpc1, by rw [keeps_stk_eq hk1 (by simp), hr],
      by rw [keeps_stk_eq hk1 (by simp)]; rfl, keeps_mono (by simp) hk1, by simp⟩
  | cons v rest ih =>
    obtain ⟨c1, hs1, hpc1, hk1⟩ := steps_jnil h1 hpc
    simp only [hr, List.cons_ne_nil, ↓reduceIte] at hpc1
    have hR1 : c1.stk R = v :: rest := by rw [keeps_stk_eq hk1 (by simp), hr]
    have hF1 : c1.stk F = cfg.stk F := keeps_stk_eq hk1 (by simp)
    obtain ⟨c2, hs2, hpc2, hR2, hF2, hk2⟩ := steps_move R_ne_F h2 (by omega) hR1
    obtain ⟨c3, hs3, hpc3, hF3, hk3⟩ := steps_push h3 (by omega)
    obtain ⟨c4, hs4, hpc4, hk4⟩ := steps_jmp h4 (by omega)
    have hR4 : c4.stk R = rest := by
      rw [keeps_stk_eq hk4 (by simp), keeps_stk_eq hk3 (by simp [R_ne_F]), hR2]
    have hF4 : c4.stk F = 1 :: v :: cfg.stk F := by
      rw [keeps_stk_eq hk4 (by simp), hF3, hF2, hF1]
    obtain ⟨c5, S5, hs5, hpc5, hR5, hF5, hk5, hcost5⟩ := ih hpc4 hR4
    refine ⟨c5, 1 + (1 + len v) + (1 + len 1) + 1 + S5,
      (((hs1.trans hs2).trans hs3).trans hs4).trans hs5, hpc5, hR5, ?_, ?_, ?_⟩
    · rw [hF5, hF4]; rfl
    · exact keeps_trans
        (keeps_trans (keeps_trans (keeps_mono (by simp) hk1) hk2)
          (keeps_mono (by intro t ht; simp at ht ⊢; right; exact ht) hk3))
        (keeps_trans (keeps_mono (by simp) hk4) hk5)
    · simp only [listSize_cons, GI.Machine.len_one]; omega

/-- `saveR a` empties `R` and pushes `pushFrame (cfg.stk R) (0 :: cfg.stk F)` onto `F`. -/
theorem steps_saveR {P : Program} {a : ℕ} {cfg : Config}
    (hc : CodeAt P a (saveR a)) (hpc : cfg.pc = a) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + 5 ∧
      cfg'.stk R = [] ∧ cfg'.stk F = pushFrame (cfg.stk R) (0 :: cfg.stk F) ∧
      Keeps [R, F] cfg cfg' ∧ S ≤ 5 * listSize (cfg.stk R) + 2 := by
  have h0 : P[a]? = some (.push F 0) := hc.cons
  have h1 : P[a + 1]? = some (.jnil R (a + 5)) := hc.tail.cons
  have h2 : P[a + 2]? = some (.move R F) := by simpa [Nat.add_assoc] using hc.tail.tail.cons
  have h3 : P[a + 3]? = some (.push F 1) := by simpa [Nat.add_assoc] using hc.tail.tail.tail.cons
  have h4 : P[a + 4]? = some (.jmp (a + 1)) := by
    simpa [Nat.add_assoc] using hc.tail.tail.tail.tail.cons
  obtain ⟨c1, hs1, hpc1, hF1, hk1⟩ := steps_push h0 hpc
  have hR1 : c1.stk R = cfg.stk R := keeps_stk_eq hk1 (by simp [R_ne_F])
  obtain ⟨c2, S2, hs2, hpc2, hR2, hF2, hk2, hcost2⟩ := steps_saveRLoop h1 h2 h3 h4 hpc1 hR1
  refine ⟨c2, (1 + len 0) + S2, hs1.trans hs2, hpc2, hR2, ?_, ?_, ?_⟩
  · rw [hF2, hF1]
  · exact keeps_trans (keeps_mono (by intro t ht; simp at ht ⊢; right; exact ht) hk1) hk2
  · simp only [GI.Machine.len_zero]; omega

/-- Code placed at `a` that restores a saved frame from `F` back onto `R`. -/
def restoreR (a : ℕ) : List Instr :=
  [.jz F (a + 3), .move F R, .jmp a]

@[simp] theorem restoreR_length (a : ℕ) : (restoreR a).length = 3 := rfl

/-- Unwinding `pushFrame r tail` from `F` onto `R`, returning to `pc = a`. -/
private theorem steps_restoreRLoop {P : Program} {a : ℕ} {cfg : Config} {r tail : List ℕ}
    (h0 : P[a]? = some (.jz F (a + 3)))
    (h1 : P[a + 1]? = some (.move F R))
    (h2 : P[a + 2]? = some (.jmp a))
    (hpc : cfg.pc = a) (hF : cfg.stk F = pushFrame r tail) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a ∧
      cfg'.stk R = r ++ cfg.stk R ∧ cfg'.stk F = tail ∧
      Keeps [R, F] cfg cfg' ∧ S ≤ 4 * listSize r := by
  induction r generalizing cfg tail with
  | nil =>
    exact ⟨cfg, 0, Steps.refl cfg, hpc, rfl, hF, keeps_refl _ cfg, Nat.zero_le _⟩
  | cons v rest ih =>
    obtain ⟨c1, S1, hs1, hpc1, hR1, hF1, hk1, hcost1⟩ :=
      ih (tail := 1 :: v :: tail) hpc hF
    obtain ⟨c2, hs2, hpc2, hF2, hk2⟩ := steps_jz h0 hpc1 hF1
    simp only [Nat.one_ne_zero, ↓reduceIte] at hpc2
    have hR2 : c2.stk R = rest ++ cfg.stk R := by
      rw [keeps_stk_eq hk2 (by simp [R_ne_F]), hR1]
    obtain ⟨c3, hs3, hpc3, hF3, hR3, hk3⟩ := steps_move R_ne_F.symm h1 hpc2 hF2
    obtain ⟨c4, hs4, hpc4, hk4⟩ := steps_jmp h2 (by omega)
    refine ⟨c4, S1 + (1 + len 1) + (1 + len v) + 1,
      ((hs1.trans hs2).trans hs3).trans hs4, hpc4, ?_, ?_, ?_, ?_⟩
    · rw [keeps_stk_eq hk4 (by simp), hR3, hR2]; rfl
    · rw [keeps_stk_eq hk4 (by simp), hF3]
    · exact keeps_trans
        (keeps_trans hk1 (keeps_mono (by intro t ht; simp at ht ⊢; right; exact ht) hk2))
        (keeps_trans (keeps_mono (by intro t ht; simp at ht ⊢; tauto) hk3)
          (keeps_mono (by simp) hk4))
    · simp only [listSize_cons, GI.Machine.len_one]; omega

/-- `restoreR a` restores `r` from `F` onto an empty `R` and pops the `0` sentinel from `F`. -/
theorem steps_restoreR {P : Program} {a : ℕ} {cfg : Config} {r tail : List ℕ}
    (hc : CodeAt P a (restoreR a)) (hpc : cfg.pc = a)
    (hR : cfg.stk R = []) (hF : cfg.stk F = pushFrame r (0 :: tail)) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + 3 ∧
      cfg'.stk R = r ∧ cfg'.stk F = tail ∧
      Keeps [R, F] cfg cfg' ∧ S ≤ 4 * listSize r + 1 := by
  have h0 : P[a]? = some (.jz F (a + 3)) := hc.cons
  have h1 : P[a + 1]? = some (.move F R) := hc.tail.cons
  have h2 : P[a + 2]? = some (.jmp a) := by simpa [Nat.add_assoc] using hc.tail.tail.cons
  obtain ⟨c1, S1, hs1, hpc1, hR1, hF1, hk1, hcost1⟩ := steps_restoreRLoop h0 h1 h2 hpc hF
  obtain ⟨c2, hs2, hpc2, hF2, hk2⟩ := steps_jz h0 hpc1 hF1
  simp only [↓reduceIte] at hpc2
  refine ⟨c2, S1 + (1 + len 0), hs1.trans hs2, hpc2, ?_, hF2, ?_, ?_⟩
  · rw [keeps_stk_eq hk2 (by simp [R_ne_F]), hR1, hR, List.append_nil]
  · exact keeps_trans hk1 (keeps_mono (by intro t ht; simp at ht ⊢; right; exact ht) hk2)
  · simp only [GI.Machine.len_zero]; omega

/-! ### Gadget 4: building `R` from argument values on `E` -/

/-- Code that pops `n` values `v₀, …, v_{n-1}` from `E` and pushes `(k + i, v_i)` onto `R`. -/
def buildRFrom : ℕ → ℕ → List Instr
  | _, 0 => []
  | k, n + 1 => [.move E R, .push R k] ++ buildRFrom (k + 1) n

@[simp] theorem buildRFrom_length (k n : ℕ) : (buildRFrom k n).length = 2 * n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [buildRFrom, ih]; omega

/-- `buildRFrom k vs.length` pops `vs` from `E`, puts `vs[i]` at register `k + i` in `R`, and
adds `∑ i, (len (k + i) + 1 + len vs[i] + 1)` to both the cost and `listSize (cfg.stk R)`. -/
theorem steps_buildRFrom {P : Program} {a k M : ℕ} {cfg : Config} {vs rest : List ℕ}
    (hc : CodeAt P a (buildRFrom k vs.length)) (hpc : cfg.pc = a)
    (hE : cfg.stk E = vs ++ rest) (hM : k + vs.length ≤ M) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + 2 * vs.length ∧
      cfg'.stk E = rest ∧
      (∀ x, memOf (cfg'.stk R) x =
        if k ≤ x ∧ x < k + vs.length then vs.getD (x - k) 0 else memOf (cfg.stk R) x) ∧
      Keeps [E, R] cfg cfg' ∧
      listSize (cfg'.stk R) ≤ listSize (cfg.stk R) +
        (len M + 1) * vs.length + listSize vs ∧
      S ≤ (len M + 1) * vs.length + listSize vs := by
  induction vs generalizing a k cfg with
  | nil =>
    refine ⟨cfg, 0, Steps.refl cfg, by simpa using hpc, hE, ?_, keeps_refl _ cfg, by simp, by simp⟩
    intro x; simp
  | cons v vs ih =>
    have h0 : P[a]? = some (.move E R) := hc.cons
    have h1 : P[a + 1]? = some (.push R k) := hc.tail.cons
    have hc_rest : CodeAt P (a + 2) (buildRFrom (k + 1) vs.length) := by
      simpa [Nat.add_assoc] using hc.tail.tail
    obtain ⟨c1, hs1, hpc1, hE1, hR1, hk1⟩ := steps_move E_ne_R h0 hpc hE
    obtain ⟨c2, hs2, hpc2, hR2, hk2⟩ := steps_push h1 hpc1
    have hE2 : c2.stk E = vs ++ rest := by rw [keeps_stk_eq hk2 (by simp [E_ne_R]), hE1]; rfl
    obtain ⟨c3, S3, hs3, hpc3, hE3, hmem3, hk3, hsize3, hcost3⟩ :=
      ih hc_rest (by omega) hE2 (by simp at hM; omega)
    have hlenk : len k ≤ len M := GI.Machine.len_mono (by simp at hM; omega)
    refine ⟨c3, (1 + len v) + (1 + len k) + S3, (hs1.trans hs2).trans hs3, ?_, hE3, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro x
      rw [hmem3 x]
      by_cases hkx : k + 1 ≤ x ∧ x < k + 1 + vs.length
      · have hkx' : k ≤ x ∧ x < k + (v :: vs).length := by simp; omega
        simp only [hkx, hkx']
        have hsub : x - k = (x - (k + 1)) + 1 := by omega
        rw [hsub]
        rfl
      · simp only [hkx, ↓reduceIte, hR2, hR1, memOf_cons_cons, Function.update_apply]
        by_cases hx : x = k
        · have hkx' : k ≤ k ∧ k < k + (v :: vs).length := by simp
          simp only [hx, ↓reduceIte, hkx', Nat.sub_self]
          rfl
        · have hnot : ¬ (k ≤ x ∧ x < k + (v :: vs).length) := by simp at hkx ⊢; omega
          simp only [hx, hnot, ↓reduceIte]
    · exact keeps_trans
        (keeps_trans hk1 (keeps_mono (by intro t ht; simp at ht ⊢; right; exact ht) hk2)) hk3
    · have hsz2 : listSize (c2.stk R) = len k + 1 + (len v + 1 + listSize (cfg.stk R)) := by
        rw [hR2, hR1]; simp [listSize_cons]
      simp only [List.length_cons, listSize_cons, Nat.mul_succ] at hsize3 ⊢
      omega
    · simp only [List.length_cons, listSize_cons, Nat.mul_succ] at hcost3 ⊢
      omega

/-- Special case of `steps_buildRFrom` starting from `k = 0` and empty `R`. -/
theorem steps_buildR {P : Program} {a M : ℕ} {cfg : Config} {vs rest : List ℕ}
    (hc : CodeAt P a (buildRFrom 0 vs.length)) (hpc : cfg.pc = a)
    (hE : cfg.stk E = vs ++ rest) (hR : cfg.stk R = []) (hM : vs.length ≤ M) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + 2 * vs.length ∧
      cfg'.stk E = rest ∧
      memOf (cfg'.stk R) = (fun i => vs.getD i 0) ∧
      Keeps [E, R] cfg cfg' ∧
      listSize (cfg'.stk R) ≤ (len M + 1) * vs.length + listSize vs ∧
      S ≤ (len M + 1) * vs.length + listSize vs := by
  obtain ⟨c', S, hs, hpc', hE', hmem', hk', hsz', hcost'⟩ :=
    steps_buildRFrom (k := 0) (M := M) hc hpc hE (by omega)
  refine ⟨c', S, hs, hpc', hE', ?_, hk', ?_, hcost'⟩
  · funext x
    rw [hmem' x, hR, memOf_nil]
    by_cases hx : x < vs.length
    · simp [hx]
    · simp only [Nat.zero_le, true_and, Nat.zero_add, hx, ↓reduceIte]
      exact (List.getD_eq_default vs 0 (Nat.le_of_not_lt hx)).symm
  · rw [hR, listSize_nil, Nat.zero_add] at hsz'
    exact hsz'

end GI.Turing.Core
