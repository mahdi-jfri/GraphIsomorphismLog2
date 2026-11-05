/-
Correctness and cost of the compiler of `Workspace.Lang.Compile`.

`Spec P K D ctx t env s Q` says that the machine code `s`, run in `compile P` from any state
whose context registers `ctx` hold the environment `env` below the heap pointer, ends normally
with a result `v` and a language cost `cost` such that `Q v cost`, and `Done` holds: `v` is stored
at the old heap pointer, the heap pointer moved just past it, the memory below the old heap
pointer and the registers `2, …, t - 1` are unchanged, and the machine cost is at most
`Bnd K D hp cost = K * cost ^ 2 * (len hp + cost + 1) ^ D`.

This file proves one lemma per construct of the language. `Workspace.Lang.CorrectMain` puts them
together by induction on `EvalAll`.
-/
module

public import Workspace.Lang.CompileFacts

@[expose] public section

set_option linter.unusedSimpArgs false

namespace GI.Lang

open GI.Machine (Stmt Outcome State WP Runs len copyBody evalExpr evalArgs Embeds
  len_mono len_le_iff lt_two_pow_len len_succ_le len_zero len_one len_add_le BinOp)
open GI.Cited (Val ValAt)

/-- What compiled code keeps: the memory below the starting heap pointer, and the registers
`2, …, t - 1`. -/
structure Frame (t : ℕ) (st st' : State) : Prop where
  mem : ∀ a < st.regs 0, st'.mem a = st.mem a
  regs : ∀ r, 2 ≤ r → r < t → st'.regs r = st.regs r

theorem Frame.refl (t : ℕ) (st : State) : Frame t st st := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem Frame.trans {t t' : ℕ} {st st₁ st₂ : State} (h₁ : Frame t st st₁) (h₂ : Frame t' st₁ st₂)
    (ht : t ≤ t') (hp : st.regs 0 ≤ st₁.regs 0) : Frame t st st₂ :=
  ⟨fun a ha => by rw [h₂.mem a (by omega), h₁.mem a ha],
   fun r h2 hr => by rw [h₂.regs r h2 (by omega), h₁.regs r h2 hr]⟩

/-- The result of compiled code started in state `st`: value `v` of language cost `cost`, final
state `st'`, machine cost `c`. -/
structure Done (K D t : ℕ) (st : State) (v : Val) (cost : ℕ) (st' : State) (c : ℕ) : Prop where
  wt : v.wt + 1 ≤ cost
  val : ValAt st'.mem (st.regs 0) v
  hp : st'.regs 0 = st.regs 0 + v.size
  frame : Frame t st st'
  cost_le : c ≤ Bnd K D (st.regs 0) cost

theorem Done.base {K D t : ℕ} {st st' : State} {v : Val} {cost c : ℕ}
    (d : Done K D t st v cost st' c) {h : ℕ} (hh : st.regs 0 = h) :
    ValAt st'.mem h v ∧ st'.regs 0 = h + v.size ∧ (∀ a < h, st'.mem a = st.mem a) ∧
      c ≤ Bnd K D h cost := by
  subst hh; exact ⟨d.val, d.hp, d.frame.mem, d.cost_le⟩

/-- The contract of compiled code. -/
def Spec (P : Program) (K D : ℕ) (ctx : List ℕ) (t : ℕ) (env : List Val) (s : Stmt)
    (Q : Val → ℕ → Prop) : Prop :=
  ∀ st : State, EnvAt st ctx env → WP (compile P) s st (fun o st' c =>
    o = .normal ∧ ∃ v cost, Q v cost ∧ Done K D t st v cost st' c)

/-- The hypotheses on the constants. -/
structure Consts (P : Program) (K D : ℕ) : Prop where
  K_ge : 400 ≤ K
  D_ge : 1 ≤ D
  prim_k : ∀ p ∈ P.prims, p.k + 1 ≤ D

/-! ### Small facts -/

theorem len_add_two_pow (h w : ℕ) : len (h + 2 ^ w) ≤ len h + w + 2 := by
  have := len_add_le h (2 ^ w)
  have h2 : len (2 ^ w) = w + 1 := GI.Machine.len_two_pow w
  omega

theorem size_lt_two_pow_wt (v : Val) : v.size < 2 ^ v.wt :=
  lt_of_le_of_lt v.size_le_wt Nat.lt_two_pow_self

/-- The allowance for the own work of a step: `s * cost * Y` with `s` the step's own charge,
`cost` the total language cost, and `Y = len h + cost + 1`. -/
theorem W_ge {s c Y : ℕ} (hs : 1 ≤ s) (hc : 1 ≤ c) :
    Y ≤ s * c * Y ∧ s * Y ≤ s * c * Y ∧ c * Y ≤ s * c * Y := by
  refine ⟨?_, ?_, ?_⟩
  · have : 1 ≤ s * c := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc Y = 1 * Y := by ring
      _ ≤ s * c * Y := Nat.mul_le_mul_right _ this
  · calc s * Y = s * 1 * Y := by ring
      _ ≤ s * c * Y := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hc)
  · calc c * Y = 1 * c * Y := by ring
      _ ≤ s * c * Y := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hs)

/-- A leaf step: overhead at most `A * (s * s * Y)`. -/
theorem bnd_leaf {K D h s o A : ℕ} (hA : A ≤ K) (hD : 1 ≤ D)
    (ho : o ≤ A * (s * s * (len h + s + 1))) : o ≤ Bnd K D h s := by
  have := overhead_le (s := s) (c := s) (Y := len h + s + 1) (e := 1) hA hD (by omega)
  unfold Bnd
  rw [pow_one] at this
  have h2 : K * s * s * (len h + s + 1) ^ D = K * s ^ 2 * (len h + s + 1) ^ D := by ring
  have h3 : A * (s * s * (len h + s + 1)) = A * s * s * (len h + s + 1) := by ring
  omega

/-- One subcomputation. -/
theorem bnd_one {K D h h₁ c₁ s m₁ o A : ℕ} (hA : A ≤ K) (hD : 1 ≤ D)
    (hm₁ : m₁ ≤ Bnd K D h₁ c₁) (hh₁ : len h₁ ≤ len h + s)
    (ho : o ≤ A * (s * (c₁ + s) * (len h + (c₁ + s) + 1))) : m₁ + o ≤ Bnd K D h (c₁ + s) := by
  have := bnd_combine (h := h) (h₂ := h) (c₂ := 0) (m₂ := 0) (s := s) (o := o) (K := K) (D := D)
    hm₁ (by simp [Bnd]) (by omega) (by omega) ?_
  · simpa using this
  have := overhead_le (s := s) (c := c₁ + s) (Y := len h + (c₁ + s) + 1) (e := 1) hA hD
    (by omega)
  rw [pow_one] at this
  have h3 : A * (s * (c₁ + s) * (len h + (c₁ + s) + 1)) =
    A * s * (c₁ + s) * (len h + (c₁ + s) + 1) := by ring
  simp only [Nat.add_zero] at this ⊢
  omega

/-- Two subcomputations. -/
theorem bnd_two {K D h h₁ h₂ c₁ c₂ s m₁ m₂ o A : ℕ} (hA : A ≤ K) (hD : 1 ≤ D)
    (hm₁ : m₁ ≤ Bnd K D h₁ c₁) (hm₂ : m₂ ≤ Bnd K D h₂ c₂)
    (hh₁ : len h₁ + c₁ ≤ len h + c₁ + c₂ + s) (hh₂ : len h₂ + c₂ ≤ len h + c₁ + c₂ + s)
    (ho : o ≤ A * (s * (c₁ + c₂ + s) * (len h + (c₁ + c₂ + s) + 1))) :
    m₁ + m₂ + o ≤ Bnd K D h (c₁ + c₂ + s) := by
  refine bnd_combine hm₁ hm₂ hh₁ hh₂ ?_
  have := overhead_le (s := s) (c := c₁ + c₂ + s) (Y := len h + (c₁ + c₂ + s) + 1) (e := 1) hA
    hD (by omega)
  rw [pow_one] at this
  have h3 : A * (s * (c₁ + c₂ + s) * (len h + (c₁ + c₂ + s) + 1)) =
    A * s * (c₁ + c₂ + s) * (len h + (c₁ + c₂ + s) + 1) := by ring
  omega

theorem bnd_one' {K D h h₁ c₁ s m₁ T A : ℕ} (hA : A ≤ K) (hD : 1 ≤ D)
    (hm₁ : m₁ ≤ Bnd K D h₁ c₁) (hh₁ : len h₁ ≤ len h + s)
    (ho : T - m₁ ≤ A * (s * (c₁ + s) * (len h + (c₁ + s) + 1))) : T ≤ Bnd K D h (c₁ + s) := by
  have := bnd_one hA hD hm₁ hh₁ ho
  omega

theorem bnd_two' {K D h h₁ h₂ c₁ c₂ s m₁ m₂ T A : ℕ} (hA : A ≤ K) (hD : 1 ≤ D)
    (hm₁ : m₁ ≤ Bnd K D h₁ c₁) (hm₂ : m₂ ≤ Bnd K D h₂ c₂)
    (hh₁ : len h₁ + c₁ ≤ len h + c₁ + c₂ + s) (hh₂ : len h₂ + c₂ ≤ len h + c₁ + c₂ + s)
    (ho : T - m₁ - m₂ ≤ A * (s * (c₁ + c₂ + s) * (len h + (c₁ + c₂ + s) + 1))) :
    T ≤ Bnd K D h (c₁ + c₂ + s) := by
  have := bnd_two hA hD hm₁ hm₂ hh₁ hh₂ ho
  omega

/-- One subcomputation, with an overhead of a higher power of `Y`. -/
theorem bnd_one_pow' {K D h h₁ c₁ s m₁ T A e : ℕ} (hA : A ≤ K) (he : e ≤ D)
    (hm₁ : m₁ ≤ Bnd K D h₁ c₁) (hh₁ : len h₁ ≤ len h + s)
    (ho : T - m₁ ≤ A * (s * (c₁ + s) * (len h + (c₁ + s) + 1) ^ e)) :
    T ≤ Bnd K D h (c₁ + s) := by
  have := bnd_combine (h := h) (h₂ := h) (c₂ := 0) (m₂ := 0) (s := s) (o := T - m₁) (K := K)
    (D := D) hm₁ (by simp [Bnd]) (by omega) (by omega) ?_
  · simp only [Nat.add_zero] at this; omega
  have := overhead_le (s := s) (c := c₁ + s) (Y := len h + (c₁ + s) + 1) hA he (by omega)
  have h3 : A * (s * (c₁ + s) * (len h + (c₁ + s) + 1) ^ e) =
    A * s * (c₁ + s) * (len h + (c₁ + s) + 1) ^ e := by ring
  simp only [Nat.add_zero] at this ⊢
  omega

/-- The bound of a primitive at base `b` splits into the language charge and a power of the
length of `b`. -/
theorem prim_cost_split (c k a b : ℕ) :
    c * (a + b + 2) ^ k ≤ c * (a + 2) ^ k * (b + 1) ^ k := by
  rw [Nat.mul_assoc, ← Nat.mul_pow]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by nlinarith) _)

/-- The environment stays in place while the context registers and the memory below the heap
pointer do not change. -/
theorem EnvAt.of_frame {st st' : State} {ctx : List ℕ} {env : List Val} {t : ℕ}
    (h : EnvAt st ctx env) (hctx : CtxOK ctx t) (hf : Frame t st st')
    (hp : st.regs 0 ≤ st'.regs 0) : EnvAt st' ctx env :=
  h.mono (fun r hr => hf.regs r (hctx r hr).1 (hctx r hr).2) hf.mem hp

/-- A value stays in place while its cells do not change. -/
theorem _root_.GI.Cited.ValAt.of_below {mem mem' : ℕ → ℕ} {b : ℕ} {v : Val} (h : ValAt mem b v) {top : ℕ}
    (hle : b + v.size ≤ top) (hm : ∀ a < top, mem' a = mem a) : ValAt mem' b v :=
  h.congr fun x _ hx => hm x (by omega)

theorem Frame.mono_t {t t' : ℕ} {st st' : State} (h : Frame t st st') (ht : t' ≤ t) :
    Frame t' st st' := ⟨h.mem, fun r h2 hr => h.regs r h2 (by omega)⟩

/-- After the assignment `t := hp`, the frame of `t` holds. -/
theorem frame_update {st : State} {t r : ℕ} (v : ℕ) (hr : t ≤ r) :
    Frame t st { st with regs := Function.update st.regs r v } :=
  ⟨fun _ _ => rfl, fun r' _ hr' => by
    simp only [Function.update_apply]; rw [if_neg (by omega)]⟩

/-- Writing register 0 or 1 keeps the frame. -/
theorem frame_update_low {st : State} {t r : ℕ} (v : ℕ) (hr : r < 2) :
    Frame t st { st with regs := Function.update st.regs r v } :=
  ⟨fun _ _ => rfl, fun r' h2 _ => by
    simp only [Function.update_apply]; rw [if_neg (by omega)]⟩

/-! ### Sequencing -/

theorem seq_assign {q : GI.Machine.Program} {r : ℕ} {e : MExpr} {u : Stmt} {st : State}
    {Q' : Outcome → State → ℕ → Prop}
    (h : WP q u { st with regs := Function.update st.regs r (evalExpr st e).1 }
      (fun o st'' c' => Q' o st'' ((evalExpr st e).2 + 1 + c' + 1))) :
    WP q (.assign r e ;; u) st Q' :=
  WP.seq (WP.assign h)

theorem seq_store {q : GI.Machine.Program} {a e : MExpr} {u : Stmt} {st : State}
    {Q' : Outcome → State → ℕ → Prop}
    (h : WP q u { st with mem := Function.update st.mem (evalExpr st a).1 (evalExpr st e).1 }
      (fun o st'' c' => Q' o st'' ((evalExpr st a).2 + (evalExpr st e).2 + 1 +
        len (evalExpr st a).1 + len (evalExpr st e).1 + c' + 1))) :
    WP q (.store a e ;; u) st Q' :=
  WP.seq (WP.store h)

theorem seq_sub {P : Program} {K D : ℕ} {ctx' : List ℕ} {t' : ℕ} {env' : List Val} {s u : Stmt}
    {R : Val → ℕ → Prop} {st : State} {Q' : Outcome → State → ℕ → Prop}
    (hs : Spec P K D ctx' t' env' s R) (henv : EnvAt st ctx' env')
    (hk : ∀ v cost st' c, R v cost → Done K D t' st v cost st' c →
      WP (compile P) u st' (fun o st'' c' => Q' o st'' (c + c' + 1))) :
    WP (compile P) (s ;; u) st Q' := by
  refine WP.seq' (fun st' c => ∃ v cost, R v cost ∧ Done K D t' st v cost st' c)
    ((hs st henv).mono ?_) ?_
  · rintro o st' c ⟨ho, v, cost, hr, hd⟩; exact ⟨ho, v, cost, hr, hd⟩
  · rintro st' c ⟨v, cost, hr, hd⟩; exact hk v cost st' c hr hd

/-! ### Walking through a list -/

theorem cellsList_take_succ (vs : List Val) (k : ℕ) (hk : k < vs.length) :
    (Val.cellsList (vs.take (k + 1))).length =
      (Val.cellsList (vs.take k)).length + vs[k].size := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, cellsList_append, cellsList_cons, cellsList_nil,
    List.append_nil, List.length_append, size_eq_length]

theorem cellsList_take_le (vs : List Val) (k : ℕ) :
    (Val.cellsList (vs.take k)).length ≤ (Val.cellsList vs).length := by
  conv_rhs => rw [← List.take_append_drop k vs]
  rw [cellsList_append, List.length_append]
  omega

/-- The loop of `get`: starting with register `a` at the first entry of the values `vs` stored at
`b`, and register `n` holding `x ≤ vs.length`, the loop moves register `a` past `x` entries. -/
theorem wp_skipLoop {q : GI.Machine.Program} {st : State} {i n a s : ℕ} (hia : i ≠ a)
    (his : i ≠ s) (hna : n ≠ a) (hns : n ≠ s) (hin : i ≠ n) (has : a ≠ s) {vs : List Val} {b x : ℕ}
    (hvs : ValsAt st.mem b vs) (hx : x ≤ vs.length) (hn : st.regs n = x) (ha : st.regs a = b) :
    WP q (Stmt.forUp i n (skipStep a s)) st (fun o st' c => o = .normal ∧ st'.mem = st.mem ∧
      st'.regs a = b + (Val.cellsList (vs.take x)).length ∧
      (∀ r, r ≠ i → r ≠ a → r ≠ s → st'.regs r = st.regs r) ∧
      c ≤ x * (40 * (len (b + (Val.cellsList vs).length) + 1) + 11 + 6 * len x) + 7 + 4 * len x) := by
  have hwa : ¬ (skipStep a s).Writes i := by
    simp only [skipStep, sizeInto, GI.Machine.Stmt.Writes]; omega
  have hwn : ¬ (skipStep a s).Writes n := by
    simp only [skipStep, sizeInto, GI.Machine.Stmt.Writes]; omega
  set M := b + (Val.cellsList vs).length
  let I : ℕ → State → Prop := fun k st' => st'.mem = st.mem ∧
    st'.regs a = b + (Val.cellsList (vs.take k)).length ∧
    (∀ r, r ≠ i → r ≠ a → r ≠ s → st'.regs r = st.regs r)
  refine GI.Machine.WP.forUp_const hin hwa hwn I (40 * (len M + 1)) ?_ ?_ ?_ ?_
  · rintro k st' v ⟨h1, h2, h3⟩
    refine ⟨h1, by simp [Function.update_apply, Ne.symm hia, h2], fun r r1 r2 r3 => ?_⟩
    simp [Function.update_apply, r1, h3 r r1 r2 r3]
  · exact ⟨rfl, by simp [ha], fun _ _ _ _ => rfl⟩
  · rintro k st' hk ⟨h1, h2, h3⟩ _ _
    rw [hn] at hk
    have hk' : k < vs.length := by omega
    have hv := hvs.get k hk'
    rw [← h1, ← h2] at hv
    have hle := cellsList_take_le vs (k + 1)
    rw [cellsList_take_succ vs k hk'] at hle
    refine WP.seq' (fun st'' c => st'' = { st' with regs := Function.update st'.regs s vs[k].size } ∧
      c ≤ 20 * (len (st'.regs a + vs[k].size) + 1)) ?_ ?_
    · exact (wp_sizeInto hv).mono fun o st'' c ⟨h4, h5, h6⟩ => ⟨h4, h5, h6⟩
    rintro st'' c ⟨rfl, hc⟩
    apply WP.assign
    refine ⟨rfl, ⟨h1, ?_, fun r r1 r2 r3 => ?_⟩, ?_⟩
    · simp [machine_simps, has, h2, cellsList_take_succ vs k hk', Nat.add_assoc]
    · simp [Function.update_apply, r2, r3, h3 r r1 r2 r3]
    · have l1 : len (st'.regs a + vs[k].size) ≤ len M := len_mono (by rw [h2]; omega)
      have l2 : len (st'.regs a) ≤ len M := len_mono (by rw [h2]; omega)
      have l3 : len vs[k].size ≤ len M := len_mono (by rw [h2] at *; omega)
      simp only [machine_simps, has, if_false, if_true, Function.update_apply] at hc ⊢
      omega
  · rintro st' c ⟨h1, h2, h3⟩ hi _ hc
    rw [hn] at h2 hc
    refine ⟨rfl, h1, h2, fun r r1 r2 r3 => ?_, hc⟩
    by_cases hr : r = i
    · exact absurd hr r1
    · exact h3 r r1 r2 r3

/-! ### Leaves -/

section Cases

variable {P : Program} {K D : ℕ} (hc : Consts P K D) {ctx : List ℕ} {t : ℕ} {env : List Val}
  {Q : Val → ℕ → Prop}

include hc

theorem spec_nat (k : ℕ) (hq : Q (.nat k) ((Val.nat k).wt + 1)) :
    Spec P K D ctx t env (compE (primOff P) ctx t (.nat k)) Q := by
  intro st _
  have hK := hc.K_ge
  have hD := hc.D_ge
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  simp only [compE]
  refine WP.seq' (fun st₁ c => st₁ = { st with mem := Function.update st.mem h 0 } ∧
    c ≤ 4 * len h + 4) ?_ ?_
  · apply WP.store; refine ⟨rfl, by simp [machine_simps, hh], ?_⟩
    simp [machine_simps, len_zero, hh]; omega
  rintro st₁ c₁ ⟨rfl, hc₁⟩
  refine WP.seq' (fun st₂ c =>
    st₂ = { st with mem := Function.update (Function.update st.mem h 0) (h + 1) k } ∧
    c ≤ 4 * len (h + 1) + 2 * len k + 8) ?_ ?_
  · apply WP.store; refine ⟨rfl, by simp [machine_simps, hh], ?_⟩
    simp only [machine_simps, hh, len_one]
    have := len_mono (show h ≤ h + 1 by omega)
    omega
  rintro st₂ c₂ ⟨rfl, hc₂⟩
  apply WP.assign
  refine ⟨rfl, .nat k, _, hq, ⟨le_rfl, ?_, ?_, ?_, ?_⟩⟩
  · rw [ValAt.nat_iff]; simp [Function.update_apply, hh]
  · simp [machine_simps, hh]
  · refine ⟨fun a ha => ?_, fun r h2 _ => ?_⟩
    · simp only [Function.update_apply, hh]; rw [if_neg (by omega), if_neg (by omega)]
    · simp only [Function.update_apply]; rw [if_neg (by omega)]
  · rw [wt_nat]
    refine bnd_leaf (A := 20) (by omega) hD ?_
    have h1 := len_add_le' h 1
    have h2 := len_add_le' h 2
    have hW := (W_ge (s := len k + 2 + 1) (c := len k + 2 + 1) (Y := len h + (len k + 2 + 1) + 1)
      (by omega) (by omega)).1
    simp only [machine_simps, hh, show len 2 = 2 from rfl] at *
    omega

theorem spec_var {i : ℕ} (hctx : CtxOK ctx t) (hi : i < env.length)
    (hq : Q env[i] (env[i].wt + 1)) :
    Spec P K D ctx t env (compE (primOff P) ctx t (.var i)) Q := by
  intro st henv
  have hK := hc.K_ge
  have hD := hc.D_ge
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  obtain ⟨hv, hle, hmem⟩ := henv.get hi
  simp only [compE]
  generalize ctx.getD i 0 = r at *
  generalize env[i] = v at *
  obtain ⟨a, ha⟩ : ∃ a, st.regs r = a := ⟨_, rfl⟩
  rw [ha] at hv hle
  rw [hh] at hle
  have hr2 := hctx r hmem
  refine WP.seq' (fun st₁ c => st₁ = { st with regs := Function.update st.regs t v.size } ∧
      c ≤ 20 * (len (a + v.size) + 1)) ?_ ?_
  · refine (wp_sizeInto (r := t) (a := r) (v := v) (by rw [ha]; exact hv)).mono ?_
    rintro o st' c ⟨rfl, h1, h2⟩; rw [ha] at h2; exact ⟨rfl, h1, h2⟩
  rintro st₁ c₁ ⟨rfl, hc₁⟩
  have hrt : r ≠ t := by omega
  have ht0 : t ≠ 0 := by omega
  have hsz := size_lt_two_pow_wt v
  refine WP.seq' (fun st₂ c => st₂.mem = st₂.mem ∧ ValAt st₂.mem h v ∧
      (∀ x, x < h ∨ h + v.size ≤ x → st₂.mem x = st.mem x) ∧
      st₂.regs = Function.update (Function.update st.regs t v.size) 1 0 ∧
      c ≤ (6 + 2 * len a + 2 * len h + 2 * len v.size) + 30 * (v.size + 1) * (len (h + 2 ^ v.wt) + 1) + 1)
    ?_ ?_
  · refine (wp_copyVal (P := P) (st := { st with regs := Function.update st.regs t v.size })
      (s := a) (d := h) (M := h + 2 ^ v.wt) (v := v) hv ?_ ?_ ?_ (Or.inr hle)
      (by omega) (by omega) (by omega)).mono ?_
    · simp [Function.update_apply, hrt, ha]
    · simp [Function.update_apply, ht0.symm, hh]
    · simp [Function.update_apply]
    · rintro o st' c ⟨rfl, a1, a2, a3, a4⟩
      refine ⟨rfl, rfl, a1, a2, a3, ?_⟩
      simp only [machine_simps, Function.update_apply, hrt, ht0.symm, if_false, ha, hh,
        if_true] at a4
      omega
  rintro st₂ c₂ ⟨-, hv₂, hm₂, hr₂, hc₂⟩
  apply WP.assign
  have e0 : st₂.regs 0 = h := by rw [hr₂]; simp [Function.update_apply, ht0.symm, hh]
  have et : st₂.regs t = v.size := by rw [hr₂]; simp [Function.update_apply, ht0.symm]; omega
  refine ⟨rfl, v, _, hq, ⟨le_rfl, ?_, ?_, ?_, ?_⟩⟩
  · rw [hh]; exact hv₂
  · simp [machine_simps, e0, et, hh]
  · refine ⟨fun x hx => ?_, fun r' h2 hr' => ?_⟩
    · exact hm₂ x (Or.inl (by omega))
    · simp only [Function.update_apply, hr₂]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [hh]
    refine bnd_leaf (A := 300) (by omega) hD ?_
    have hM := len_add_two_pow h v.wt
    have h1 : len a ≤ len h := len_mono (by omega)
    have h2 : len (a + v.size) ≤ len h := len_mono (by omega)
    have h3 : len v.size ≤ v.wt := le_trans (len_mono v.size_le_wt) (GI.Machine.len_le_self _)
    have h4 : len (h + v.size) ≤ len h + v.wt := le_trans (len_add_le' _ _) (by
      have := v.size_le_wt; omega)
    have h5 : v.size + 1 ≤ v.wt + 1 := by have := v.size_le_wt; omega
    simp only [machine_simps, e0, et]
    obtain ⟨hW1, hW2, -⟩ := W_ge (s := v.wt + 1) (c := v.wt + 1) (Y := len h + (v.wt + 1) + 1)
      (by omega) (by omega)
    have : 30 * (v.size + 1) * (len (h + 2 ^ v.wt) + 1) ≤
        60 * ((v.wt + 1) * (len h + (v.wt + 1) + 1)) := by
      calc 30 * (v.size + 1) * (len (h + 2 ^ v.wt) + 1)
          ≤ 30 * (v.wt + 1) * (2 * (len h + (v.wt + 1) + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ h5) (by omega)
        _ = 60 * ((v.wt + 1) * (len h + (v.wt + 1) + 1)) := by ring
    omega

theorem spec_arith {op : BinOp} {a b : Expr} {Ra Rb : Val → ℕ → Prop} (hctx : CtxOK ctx t)
    (ht : 2 ≤ t)
    (ha : Spec P K D ctx (t + 1) env (compE (primOff P) ctx (t + 1) a) Ra)
    (hb : Spec P K D ctx (t + 1) env (compE (primOff P) ctx (t + 1) b) Rb)
    (hq : ∀ va ca vb cb, Ra va ca → Rb vb cb → ∃ x y, va = .nat x ∧ vb = .nat y ∧
      Q (.nat (op.eval x y)) (ca + cb + (Val.nat (op.eval x y)).wt + 1)) :
    Spec P K D ctx t env (compE (primOff P) ctx t (.arith op a b)) Q := by
  intro st henv
  have hK := hc.K_ge
  have hD := hc.D_ge
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  have ht0 : t ≠ 0 := by omega
  simp only [compE]
  apply seq_assign
  simp only [machine_simps, hh]
  have f₁ := frame_update (st := st) h (le_refl t)
  have h₁0 : ({ st with regs := Function.update st.regs t h } : State).regs 0 = h := by
    simp [Function.update_apply, ht0.symm, hh]
  refine seq_sub (ha) (henv.of_frame hctx f₁ (by rw [h₁0, hh]))
    fun va ca st₂ c₂ hRa da => ?_
  obtain ⟨va2, e20, m21, k2⟩ := da.base h₁0
  have f₂ := f₁.trans da.frame (by omega) (by rw [h₁0, hh])
  refine seq_sub hb (henv.of_frame hctx (f₂.mono_t (by omega)) (by rw [e20, hh]; omega))
    fun vb cb st₃ c₃ hRb db => ?_
  obtain ⟨x, y, rfl, rfl, hQ⟩ := hq _ _ _ _ hRa hRb
  simp only [size_nat] at e20
  obtain ⟨vb3, e30, m32, k3⟩ := db.base e20
  simp only [size_nat] at e30
  replace e30 : st₃.regs 0 = h + 4 := by omega
  have e3t : st₃.regs t = h := by
    rw [db.frame.regs t ht (by omega), da.frame.regs t ht (by omega)]; simp
  have vx := ValAt.nat_iff.mp (va2.of_below (top := h + 2) (by simp) fun a ha' => m32 a ha')
  have vy := ValAt.nat_iff.mp vb3
  apply seq_store
  simp only [machine_simps, e3t, e30, vx.2, vy.2, show h + 2 + 1 = h + 3 by omega]
  apply WP.assign
  set z := op.eval x y
  refine ⟨rfl, .nat z, _, hQ, ⟨by omega, ?_, ?_, ?_, ?_⟩⟩
  · rw [hh, ValAt.nat_iff]
    simp only [Function.update_apply]
    rw [if_neg (by omega)]
    exact ⟨vx.1, by simp⟩
  · simp [machine_simps, e3t, hh]
  · refine ⟨fun a ha' => ?_, fun r h2 hr => ?_⟩
    · simp only [Function.update_apply, hh] at ha' ⊢
      rw [if_neg (by omega), m32 a (by omega), m21 a ha']
    · simp only [Function.update_apply]
      rw [if_neg (by omega), db.frame.regs r h2 (by omega), da.frame.regs r h2 (by omega)]
      simp [Function.update_apply]; omega
  · rw [hh, show ca + cb + (Val.nat z).wt + 1 = ca + cb + ((Val.nat z).wt + 1) by ring]
    refine bnd_two' (A := 100) (by omega) hD k2 k3 ?_ ?_ ?_
    · omega
    · have := len_add_le' h 2; have := da.wt; rw [wt_nat] at this; omega
    have wa := da.wt; have wb := db.wt
    rw [wt_nat] at wa wb ⊢
    have l1 := len_add_le' h 1
    have l3 := len_add_le' h 3
    have l2 := len_add_le' h 2
    obtain ⟨hW1, -, -⟩ := W_ge (s := len z + 2 + 1) (c := ca + cb + (len z + 2 + 1))
      (Y := len h + (ca + cb + (len z + 2 + 1)) + 1) (by omega) (by omega)
    simp only [machine_simps, e3t, e30, vx.2, vy.2, show h + 2 + 1 = h + 3 by omega,
      show len 2 = 2 from rfl, show len 3 = 2 from rfl, len_one]
    omega

omit hc in
/-- The common start of a compound construct: save the heap pointer in register `t` and run
the code of the first subexpression with first free register `t + 1`. -/
theorem seq_prelude {a : Expr} {Ra : Val → ℕ → Prop} {u : Stmt} {Q' : Outcome → State → ℕ → Prop}
    (hctx : CtxOK ctx t) (ht : 2 ≤ t)
    (ha : Spec P K D ctx (t + 1) env (compE (primOff P) ctx (t + 1) a) Ra)
    {st : State} (henv : EnvAt st ctx env)
    (hk : ∀ va ca st₂ c₂, Ra va ca → va.wt + 1 ≤ ca → ValAt st₂.mem (st.regs 0) va →
      st₂.regs 0 = st.regs 0 + va.size → Frame t st st₂ → st₂.regs t = st.regs 0 →
      c₂ ≤ Bnd K D (st.regs 0) ca →
      WP (compile P) u st₂ (fun o st'' c' => Q' o st'' (1 + len (st.regs 0) + 1 + (c₂ + c' + 1) + 1))) :
    WP (compile P) (.assign t (.reg 0) ;; compE (primOff P) ctx (t + 1) a ;; u) st Q' := by
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  have ht0 : t ≠ 0 := by omega
  apply seq_assign
  simp only [machine_simps, hh]
  have f₁ := frame_update (st := st) h (le_refl t)
  have h₁0 : ({ st with regs := Function.update st.regs t h } : State).regs 0 = h := by
    simp [Function.update_apply, ht0.symm, hh]
  refine seq_sub (ha) (henv.of_frame hctx f₁ (by rw [h₁0, hh]))
    fun va ca st₂ c₂ hRa da => ?_
  obtain ⟨va2, e20, m21, k2⟩ := da.base h₁0
  have f₂ := f₁.trans da.frame (by omega) (by rw [h₁0, hh])
  have e2t : st₂.regs t = h := by rw [da.frame.regs t ht (by omega)]; simp
  have := hk va ca st₂ c₂ hRa da.wt (by rw [hh]; exact va2) (by rw [hh]; exact e20)
    (f₂.mono_t le_rfl) (by rw [hh]; exact e2t) (by rw [hh]; exact k2)
  rw [hh] at this
  exact this

theorem spec_nil (hq : Q (.list []) ((Val.list []).wt + 1)) :
    Spec P K D ctx t env (compE (primOff P) ctx t .nil) Q := by
  intro st _
  have hK := hc.K_ge
  have hD := hc.D_ge
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  simp only [compE]
  apply seq_store; apply seq_store; apply seq_store
  apply WP.assign
  have hw : (Val.list []).wt = 4 := by simp [Val.wt, cellWt, len_zero]
  refine ⟨rfl, .list [], _, hq, ⟨le_rfl, ?_, ?_, ?_, ?_⟩⟩
  · rw [ValAt.list_iff]
    simp [machine_simps, hh, Function.update_apply, len_zero]
  · simp [machine_simps, hh, size_list]
  · refine ⟨fun a ha => ?_, fun r h2 _ => ?_⟩
    · simp only [machine_simps, Function.update_apply, hh] at ha ⊢
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · simp only [Function.update_apply]; rw [if_neg (by omega)]
  · rw [hw]
    refine bnd_leaf (A := 30) (by omega) hD ?_
    have h1 := len_add_le' h 1
    have h2 := len_add_le' h 2
    have h3 := len_add_le' h 3
    have hW := (W_ge (s := 4 + 1) (c := 4 + 1) (Y := len h + (4 + 1) + 1) (by omega) (by omega)).1
    simp only [machine_simps, hh, show len 2 = 2 from rfl, show len 3 = 2 from rfl, len_one,
      len_zero] at *
    omega

theorem spec_length {l : Expr} {Ra : Val → ℕ → Prop} (hctx : CtxOK ctx t) (ht : 2 ≤ t)
    (ha : Spec P K D ctx (t + 1) env (compE (primOff P) ctx (t + 1) l) Ra)
    (hq : ∀ va ca, Ra va ca → ∃ vs, va = .list vs ∧
      Q (.nat vs.length) (ca + (Val.nat vs.length).wt + 1)) :
    Spec P K D ctx t env (compE (primOff P) ctx t (.length l)) Q := by
  intro st henv
  have hK := hc.K_ge
  have hD := hc.D_ge
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  simp only [compE]
  refine seq_prelude hctx ht ha henv fun va ca st₂ c₂ hRa hwa va2 e20 f₂ e2t k2 => ?_
  obtain ⟨vs, rfl, hQ⟩ := hq _ _ hRa
  rw [hh] at va2 e20 e2t k2
  have vl := ValAt.list_iff.mp va2
  apply seq_store
  simp only [machine_simps, e2t]
  apply WP.assign
  refine ⟨rfl, .nat vs.length, _, hQ, ⟨by omega, ?_, ?_, ?_, ?_⟩⟩
  · rw [hh, ValAt.nat_iff]
    refine ⟨by simp, ?_⟩
    simp only [Function.update_apply, show h + 1 ≠ h by omega, if_false]
    exact vl.2.1
  · simp [machine_simps, e2t, hh]
  · refine ⟨fun a ha' => ?_, fun r h2 hr => ?_⟩
    · simp only [Function.update_apply, hh] at ha' ⊢
      rw [if_neg (by omega), f₂.mem a (by omega)]
    · simp only [Function.update_apply]
      rw [if_neg (by omega), f₂.regs r h2 hr]
  · rw [hh, show ca + (Val.nat vs.length).wt + 1 = ca + ((Val.nat vs.length).wt + 1) by ring]
    refine bnd_one' (A := 100) (by omega) hD k2 (by omega) ?_
    rw [wt_list] at hwa
    rw [wt_nat]
    have l2 := len_add_le' h 2
    obtain ⟨hW1, -, -⟩ := W_ge (s := len vs.length + 2 + 1) (c := ca + (len vs.length + 2 + 1))
      (Y := len h + (ca + (len vs.length + 2 + 1)) + 1) (by omega) (by omega)
    simp only [machine_simps, e2t, show len 2 = 2 from rfl, len_zero]
    omega

theorem spec_isNat {e : Expr} {Ra : Val → ℕ → Prop} (hctx : CtxOK ctx t) (ht : 2 ≤ t)
    (ha : Spec P K D ctx (t + 1) env (compE (primOff P) ctx (t + 1) e) Ra)
    (hq : ∀ va ca, Ra va ca → Q (.nat va.isNatNum) (ca + (Val.nat va.isNatNum).wt + 1)) :
    Spec P K D ctx t env (compE (primOff P) ctx t (.isNat e)) Q := by
  intro st henv
  have hK := hc.K_ge
  have hD := hc.D_ge
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  simp only [compE]
  refine seq_prelude hctx ht ha henv fun va ca st₂ c₂ hRa hwa va2 e20 f₂ e2t k2 => ?_
  have hQ := hq _ _ hRa
  rw [hh] at va2 e20 e2t k2
  have htag : st₂.mem h = 1 - va.isNatNum ∧ va.isNatNum ≤ 1 := by
    cases va with
    | nat n => simp [(ValAt.nat_iff.mp va2).1, Val.isNatNum]
    | list vs => simp [(ValAt.list_iff.mp va2).1, Val.isNatNum]
  apply seq_store
  simp only [machine_simps, e2t, htag.1]
  apply seq_store
  simp only [machine_simps, Function.update_apply, e2t]
  apply WP.assign
  have hsz := va.two_le_size
  refine ⟨rfl, .nat va.isNatNum, _, hQ, ⟨by omega, ?_, ?_, ?_, ?_⟩⟩
  · rw [hh, ValAt.nat_iff]
    simp only [Function.update_apply]
    simp only [if_true, if_neg (show h + 1 ≠ h by omega), true_and]
    omega
  · simp [machine_simps, e2t, hh]
  · refine ⟨fun a ha' => ?_, fun r h2 hr => ?_⟩
    · simp only [Function.update_apply, hh] at ha' ⊢
      rw [if_neg (by omega), if_neg (by omega), f₂.mem a (by omega)]
    · simp only [Function.update_apply]
      rw [if_neg (by omega), f₂.regs r h2 hr]
  · rw [hh, show ca + (Val.nat va.isNatNum).wt + 1 = ca + ((Val.nat va.isNatNum).wt + 1) by ring]
    refine bnd_one' (A := 100) (by omega) hD k2 (by omega) ?_
    rw [wt_nat] at hQ ⊢
    have l2 := len_add_le' h 2
    have l1 := len_add_le' h 1
    have hl : len (1 - va.isNatNum) ≤ 1 := GI.Machine.len_le_one_iff.mpr (by omega)
    have hl' : len va.isNatNum ≤ 1 := GI.Machine.len_le_one_iff.mpr htag.2
    have hl'' : len (1 - (1 - va.isNatNum)) ≤ 1 := GI.Machine.len_le_one_iff.mpr (by omega)
    obtain ⟨hW1, -, -⟩ := W_ge (s := len va.isNatNum + 2 + 1) (c := ca + (len va.isNatNum + 2 + 1))
      (Y := len h + (ca + (len va.isNatNum + 2 + 1)) + 1) (by omega) (by omega)
    simp only [machine_simps, e2t, htag.1, show len 2 = 2 from rfl, len_zero, len_one,
      Function.update_apply, if_true]
    omega

theorem spec_snoc {l e : Expr} {Ra Rb : Val → ℕ → Prop} (hctx : CtxOK ctx t) (ht : 2 ≤ t)
    (ha : Spec P K D ctx (t + 1) env (compE (primOff P) ctx (t + 1) l) Ra)
    (hb : Spec P K D ctx (t + 2) env (compE (primOff P) ctx (t + 2) e) Rb)
    (hq : ∀ va ca vb cb, Ra va ca → Rb vb cb → ∃ vs, va = .list vs ∧
      Q (.list (vs ++ [vb])) (ca + cb + (Val.list (vs ++ [vb])).wt + 1)) :
    Spec P K D ctx t env (compE (primOff P) ctx t (.snoc l e)) Q := by
  intro st henv
  have hK := hc.K_ge
  have hD := hc.D_ge
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  simp only [compE]
  refine seq_prelude hctx ht ha henv fun va ca st₂ c₂ hRa hwa va2 e20 f₂ e2t k2 => ?_
  rw [hh] at va2 e20 e2t k2
  apply seq_assign
  simp only [machine_simps, e20]
  have f₃ := frame_update (st := st₂) (h + va.size) (le_refl (t + 1))
  have h30 : ({ st₂ with regs := Function.update st₂.regs (t + 1) (h + va.size) } : State).regs 0 =
      h + va.size := by simp [Function.update_apply, e20]
  have f₂₃ := f₂.trans f₃ (by omega) (by rw [hh, e20]; omega)
  refine seq_sub hb (henv.of_frame hctx (f₂₃.mono_t le_rfl) (by rw [h30, hh]; omega))
    fun vb cb st₄ c₄ hRb db => ?_
  obtain ⟨vs, rfl, hQ⟩ := hq _ _ _ _ hRa hRb
  obtain ⟨vb4, e40, m43, k4⟩ := db.base h30
  have e4t : st₄.regs t = h := by
    rw [db.frame.regs t ht (by omega)]; simp [Function.update_apply, e2t]
  have e4t1 : st₄.regs (t + 1) = h + (Val.list vs).size := by
    rw [db.frame.regs (t + 1) (by omega) (by omega)]; simp
  have vl := ValAt.list_iff.mp (va2.of_below (mem' := st₄.mem) (top := h + (Val.list vs).size)
    le_rfl fun a ha' => by rw [m43 a ha'])
  have hS := size_list vs
  apply seq_store
  simp only [machine_simps, e4t, vl.2.1]
  apply WP.store
  have hsub : h + (Val.list vs).size + vb.size - (h + (Val.list vs).size) = vb.size := by omega
  have hm : ∀ x, x ≠ h + 1 → x ≠ h + 2 → Function.update (Function.update
      st₄.mem (h + 1) (vs.length + 1)) (h + 2) ((Val.cellsList vs).length + vb.size) x =
      st₄.mem x := by
    intro x h1 h2; simp only [Function.update_apply]; rw [if_neg h2, if_neg h1]
  have e1 : (evalExpr { st₄ with mem := Function.update st₄.mem (h + 1) (vs.length + 1) }
      (.bin .add (.reg t) (.const 2))).1 = h + 2 := by simp [machine_simps, e4t]
  have e2 : (evalExpr { st₄ with mem := Function.update st₄.mem (h + 1) (vs.length + 1) }
      (.bin .add (.load (.bin .add (.reg t) (.const 2))) (.bin .sub (.reg 0) (.reg (t + 1))))).1 =
      (Val.cellsList vs).length + vb.size := by
    simp only [machine_simps, e4t, e4t1, e40, show h + 2 ≠ h + 1 by omega, if_false, vl.2.2.1,
      hsub]
  rw [e1, e2]
  refine ⟨rfl, .list (vs ++ [vb]), _, hQ, ⟨by omega, ?_, ?_, ?_, ?_⟩⟩
  · rw [hh, ValAt.list_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (hm h (by omega) (by omega)).trans vl.1
    · simp only [Function.update_apply, show h + 1 ≠ h + 2 by omega, if_false, if_true]; simp
    · simp only [Function.update_apply, if_true]; simp [size_eq_length]
    · rw [ValsAt.append_iff, ValsAt.cons_iff]
      refine ⟨vl.2.2.2.congr fun x hx _ => hm x (by omega) (by omega), ?_, by simp⟩
      rw [show h + 3 + (Val.cellsList vs).length = h + (Val.list vs).size by omega]
      exact vb4.congr fun x hx _ => hm x (by omega) (by omega)
  · rw [hh, e40, size_list, size_list]; simp [size_eq_length]; omega
  · refine ⟨fun a ha' => ?_, fun r h2 hr => ?_⟩
    · simp only [Function.update_apply, hh] at ha' ⊢
      rw [if_neg (by omega), if_neg (by omega), m43 a (by omega), f₂.mem a (by rw [hh]; omega)]
    · rw [db.frame.regs r h2 (by omega)]
      simp only [Function.update_apply]
      rw [if_neg (by omega), f₂.regs r h2 hr]
  · rw [hh, show ca + cb + (Val.list (vs ++ [vb])).wt + 1 =
      ca + cb + ((Val.list (vs ++ [vb])).wt + 1) by ring]
    refine bnd_two' (A := 100) (by omega) hD k2 k4 ?_ ?_ ?_
    · omega
    · have := len_add_le' h (Val.list vs).size
      have := (Val.list vs).size_le_wt
      omega
    have wa := hwa; rw [wt_list] at wa
    have wb := db.wt
    have hsw := (Val.list vs).size_le_wt
    have hsb := vb.size_le_wt
    have l1 := len_add_le' h 1
    have l2 := len_add_le' h 2
    have l3 := len_add_le' h ((Val.list vs).size + vb.size)
    have l4 := len_add_le' h (Val.list vs).size
    have l5 := len_succ_le vs.length
    have l6 := len_add_le' (Val.cellsList vs).length vb.size
    have l7 : len vb.size ≤ vb.size := GI.Machine.len_le_self _
    have l8 : len (h + (Val.list vs).size + vb.size) ≤ len h + (Val.list vs).size + vb.size := by
      have := len_add_le' h ((Val.list vs).size + vb.size); rw [← Nat.add_assoc] at this; omega
    obtain ⟨hW1, -, -⟩ := W_ge (s := (Val.list (vs ++ [vb])).wt + 1)
      (c := ca + cb + ((Val.list (vs ++ [vb])).wt + 1))
      (Y := len h + (ca + cb + ((Val.list (vs ++ [vb])).wt + 1)) + 1) (by omega) (by omega)
    simp only [machine_simps, Function.update_apply, e4t, e4t1, e40, vl.2.1, vl.2.2.1,
      show h + 2 ≠ h + 1 by omega, if_false, show len 2 = 2 from rfl, len_one, hsub]
    omega

theorem spec_ite {c th el : Expr} {Rc : Val → ℕ → Prop} (hctx : CtxOK ctx t) (ht : 2 ≤ t)
    (hcs : Spec P K D ctx (t + 1) env (compE (primOff P) ctx (t + 1) c) Rc)
    (hn : ∀ vc cc, Rc vc cc → ∃ x, vc = .nat x)
    (hbs : ∀ x cc, Rc (.nat x) cc → Spec P K D ctx (t + 1) env
      (compE (primOff P) ctx (t + 1) (if x = 0 then el else th))
      (fun w cb => Q w (cc + cb + w.wt + 1))) :
    Spec P K D ctx t env (compE (primOff P) ctx t (.ite c th el)) Q := by
  intro st henv
  have hK := hc.K_ge
  have hD := hc.D_ge
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  simp only [compE]
  refine seq_prelude hctx ht hcs henv fun va ca st₂ c₂ hRa hwa va2 e20 f₂ e2t k2 => ?_
  rw [hh] at va2 e20 e2t k2
  obtain ⟨x, rfl⟩ := hn _ _ hRa
  have vx := ValAt.nat_iff.mp va2
  apply seq_assign
  simp only [machine_simps, e2t]
  apply WP.cond
  have f₃ := f₂.trans (frame_update_low (st := st₂) (t := t) h (show 0 < 2 by omega)) le_rfl
    (by rw [hh, e20]; omega)
  have h30 : ({ st₂ with regs := Function.update st₂.regs 0 h } : State).regs 0 = h := by simp
  have hcode : (if (evalExpr { st₂ with regs := Function.update st₂.regs 0 h }
      (.load (.bin .add (.reg t) (.const 1)))).1 = 0 then compE (primOff P) ctx (t + 1) el
      else compE (primOff P) ctx (t + 1) th) =
      compE (primOff P) ctx (t + 1) (if x = 0 then el else th) := by
    simp only [machine_simps, Function.update_apply, show t ≠ 0 by omega, if_false, e2t, vx.2]
    split <;> rfl
  rw [hcode]
  refine ((hbs x ca hRa) _ (henv.of_frame hctx f₃ (by rw [h30, hh]))).mono ?_
  rintro o st₄ c₄ ⟨rfl, w, cb, hQ, db⟩
  obtain ⟨vb4, e40, m43, k4⟩ := db.base h30
  refine ⟨rfl, w, _, hQ, ⟨by have := db.wt; omega, by rw [hh]; exact vb4, by rw [hh, e40],
    ?_, ?_⟩⟩
  · refine ⟨fun a ha' => ?_, fun r h2 hr => ?_⟩
    · rw [hh] at ha'
      rw [m43 a ha']; exact f₃.mem a (by rw [hh]; exact ha')
    · rw [db.frame.regs r h2 (by omega)]; exact f₃.regs r h2 hr
  · rw [hh, show ca + cb + w.wt + 1 = ca + cb + (w.wt + 1) by ring]
    refine bnd_two' (A := 100) (by omega) hD k2 k4 (by omega) (by omega) ?_
    have wa := hwa; rw [wt_nat] at wa
    obtain ⟨hW1, -, -⟩ := W_ge (s := w.wt + 1) (c := ca + cb + (w.wt + 1))
      (Y := len h + (ca + cb + (w.wt + 1)) + 1) (by omega) (by omega)
    have l1 := len_add_le' h 1
    simp only [machine_simps, Function.update_apply, show t ≠ 0 by omega, if_false, e2t, vx.2,
      len_one]
    omega

theorem spec_letE {e body : Expr} {Ra : Val → ℕ → Prop} (hctx : CtxOK ctx t) (ht : 2 ≤ t)
    (ha : Spec P K D ctx (t + 1) env (compE (primOff P) ctx (t + 1) e) Ra)
    (hbs : ∀ v ca, Ra v ca → Spec P K D (ctx ++ [t]) (t + 2) (env ++ [v])
      (compE (primOff P) (ctx ++ [t]) (t + 2) body) (fun w cb => Q w (ca + cb + w.wt + 1))) :
    Spec P K D ctx t env (compE (primOff P) ctx t (.letE e body)) Q := by
  intro st henv
  have hK := hc.K_ge
  have hD := hc.D_ge
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  simp only [compE]
  refine seq_prelude hctx ht ha henv fun va ca st₂ c₂ hRa hwa va2 e20 f₂ e2t k2 => ?_
  rw [hh] at va2 e20 e2t k2
  obtain ⟨p₁, hp₁⟩ : ∃ p, h + va.size = p := ⟨_, rfl⟩
  rw [hp₁] at e20
  apply seq_assign
  simp only [machine_simps, e20]
  have f₃ := frame_update (st := st₂) p₁ (le_refl (t + 1))
  have h30 : ({ st₂ with regs := Function.update st₂.regs (t + 1) p₁ } : State).regs 0 = p₁ := by
    simp [Function.update_apply, e20]
  have f₂₃ := f₂.trans f₃ (by omega) (by rw [hh, e20]; omega)
  have henv₃ : EnvAt { st₂ with regs := Function.update st₂.regs (t + 1) p₁ } (ctx ++ [t])
      (env ++ [va]) := by
    refine (henv.of_frame hctx f₂₃ (by rw [h30, hh]; omega)).snoc ?_ ?_
    · simp only [Function.update_apply, show t ≠ t + 1 by omega, if_false, e2t]; exact va2
    · rw [h30]; simp only [Function.update_apply, show t ≠ t + 1 by omega, if_false, e2t]; omega
  have hctx' : CtxOK (ctx ++ [t]) (t + 2) := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · have := hctx r hr; omega
    · simp at hr; omega
  refine seq_sub (hbs va ca hRa) henv₃ fun w cb st₄ c₄ hQ db => ?_
  obtain ⟨vb4, e40, m43, k4⟩ := db.base h30
  have e4t : st₄.regs t = h := by
    rw [db.frame.regs t ht (by omega)]; simp [Function.update_apply, e2t]
  have e4t1 : st₄.regs (t + 1) = p₁ := by
    rw [db.frame.regs (t + 1) (by omega) (by omega)]; simp
  have hsz := size_lt_two_pow_wt w
  have hsub : p₁ + w.size - p₁ = w.size := by omega
  have hsa := va.size_le_wt
  refine WP.seq' (fun st₅ c => ValAt st₅.mem h w ∧
      (∀ x, x < h ∨ h + w.size ≤ x → st₅.mem x = st₄.mem x) ∧
      st₅.regs = Function.update st₄.regs 1 0 ∧
      c ≤ (10 + 4 * len p₁ + len h + 2 * len (p₁ + w.size) + len w.size) +
        30 * (w.size + 1) * (len (p₁ + 2 ^ w.wt) + 1) + 1) ?_ ?_
  · refine (wp_copyVal (P := P) (st := st₄) (s := p₁) (d := h) (M := p₁ + 2 ^ w.wt) (v := w) vb4
      ?_ ?_ ?_ (Or.inl (by omega)) (by omega) (by omega) (by omega)).mono ?_
    · simp [e4t1]
    · simp [e4t]
    · simp [machine_simps, e40, e4t1, hsub]
    · rintro o st' c ⟨rfl, a1, a2, a3, a4⟩
      refine ⟨rfl, a1, a2, a3, ?_⟩
      simp only [machine_simps, e4t, e4t1, e40, hsub] at a4
      omega
  rintro st₅ c₅ ⟨vw5, m54, r54, k5⟩
  apply WP.assign
  have e50 : st₅.regs 0 = p₁ + w.size := by rw [r54]; simp [Function.update_apply, e40]
  have e5t : st₅.regs t = h := by rw [r54]; simp [Function.update_apply, show t ≠ 1 by omega, e4t]
  have e5t1 : st₅.regs (t + 1) = p₁ := by
    rw [r54]; simp [Function.update_apply, show t ≠ 0 by omega, e4t1]
  refine ⟨rfl, w, _, hQ, ⟨by have := db.wt; omega, by rw [hh]; exact vw5, ?_, ?_, ?_⟩⟩
  · simp [machine_simps, e50, e5t, e5t1, hh, hsub]
  · refine ⟨fun a ha' => ?_, fun r h2 hr => ?_⟩
    · rw [hh] at ha'
      simp only
      rw [m54 a (Or.inl ha'), m43 a (by omega)]
      exact f₂₃.mem a (by rw [hh]; exact ha')
    · simp only [Function.update_apply]
      rw [if_neg (by omega), r54]
      simp only [Function.update_apply]
      rw [if_neg (by omega), db.frame.regs r h2 (by omega)]
      exact f₂₃.regs r h2 hr
  · rw [hh, show ca + cb + w.wt + 1 = ca + cb + (w.wt + 1) by ring]
    refine bnd_two' (A := 200) (by omega) hD k2 k4 (by omega) ?_ ?_
    · have := len_add_le' h va.size
      rw [hp₁] at this
      have := va.size_le_wt
      omega
    have wa := hwa
    have wb := db.wt
    have hsa := va.size_le_wt
    have hsw := w.size_le_wt
    have l1 := len_add_le' h va.size
    rw [hp₁] at l1
    have l2 := len_add_le' p₁ w.size
    have l3 : len w.size ≤ w.size := GI.Machine.len_le_self _
    have l4 := len_add_two_pow p₁ w.wt
    have l5 := len_add_le' h w.size
    obtain ⟨hW1, hW2, -⟩ := W_ge (s := w.wt + 1) (c := ca + cb + (w.wt + 1))
      (Y := len h + (ca + cb + (w.wt + 1)) + 1) (by omega) (by omega)
    have hcopy : 30 * (w.size + 1) * (len (p₁ + 2 ^ w.wt) + 1) ≤
        90 * ((w.wt + 1) * (len h + (ca + cb + (w.wt + 1)) + 1)) := by
      calc 30 * (w.size + 1) * (len (p₁ + 2 ^ w.wt) + 1)
          ≤ 30 * (w.wt + 1) * (3 * (len h + (ca + cb + (w.wt + 1)) + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
        _ ≤ 90 * ((w.wt + 1) * (len h + (ca + cb + (w.wt + 1)) + 1)) := by ring_nf; omega
    simp only [machine_simps, e50, e5t, e5t1, e4t, e40, hsub]
    omega

omit hc in
/-- The procedure of a user function, run on an argument `va` stored at `b`, with heap pointer
`p₁` just after it. It returns the new heap pointer. -/
theorem wp_funBody {body : Expr} {va : Val} {Q' : Val → ℕ → Prop}
    (hbs : Spec P K D [2] 3 [va] (compE (primOff P) [2] 3 body) Q')
    {stc : State} {b p₁ : ℕ} (hc0 : stc.regs 0 = p₁) (hc2 : stc.regs 2 = b)
    (hval : ValAt stc.mem b va) (hle : b + va.size ≤ p₁) :
    WP (compile P) (funBody (primOff P) body) stc (fun o st' c => ∃ w cb c', Q' w cb ∧
      o = .returned (p₁ + w.size) ∧ ValAt st'.mem p₁ w ∧ (∀ a < p₁, st'.mem a = stc.mem a) ∧
      c = c' + (1 + len (p₁ + w.size) + 1) + 1 ∧ c' ≤ Bnd K D p₁ cb ∧ w.wt + 1 ≤ cb) := by
  have henv : EnvAt stc [2] [va] := .cons ⟨by rw [hc2]; exact hval, by rw [hc2, hc0]; exact hle⟩ .nil
  refine seq_sub hbs henv fun w cb st₄ c₄ hQ db => ?_
  obtain ⟨vb4, e40, m43, k4⟩ := db.base hc0
  apply WP.ret
  refine ⟨w, cb, c₄, hQ, by simp [e40], vb4, m43, by simp [e40], k4, db.wt⟩

theorem spec_call {f : ℕ} {a body : Expr} {Ra : Val → ℕ → Prop} (hctx : CtxOK ctx t)
    (ht : 2 ≤ t) (hf : P.funs[f]? = some body)
    (ha : Spec P K D ctx (t + 1) env (compE (primOff P) ctx (t + 1) a) Ra)
    (hbs : ∀ v ca, Ra v ca → Spec P K D [2] 3 [v] (compE (primOff P) [2] 3 body)
      (fun w cb => Q w (ca + cb + w.wt + 1))) :
    Spec P K D ctx t env (compE (primOff P) ctx t (.call f a)) Q := by
  intro st henv
  have hK := hc.K_ge
  have hD := hc.D_ge
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  simp only [compE]
  refine seq_prelude hctx ht ha henv fun va ca st₂ c₂ hRa hwa va2 e20 f₂ e2t k2 => ?_
  rw [hh] at va2 e20 e2t k2
  obtain ⟨p₁, hp₁⟩ : ∃ p, h + va.size = p := ⟨_, rfl⟩
  rw [hp₁] at e20
  apply WP.seq
  apply WP.call (compile_fun hf)
  refine (wp_funBody (hbs va ca hRa) (b := h) (p₁ := p₁)
    (stc := { mem := st₂.mem, regs := fun i => (evalArgs st₂ [.reg 0, 0, .reg t]).1.getD i 0 })
    ?_ ?_ va2 (by omega)).mono ?_
  · simp [machine_simps, e20]
  · simp [machine_simps, e2t]
  rintro o st' c ⟨w, cb, c', hQ, rfl, vw, mw, rfl, k4, hwb⟩
  simp only [Outcome.retVal_returned]
  -- After the call: register `t + 1` holds the final heap pointer of the callee.
  have e30 : (Function.update st₂.regs (t + 1) (p₁ + w.size)) 0 = p₁ := by
    simp [Function.update_apply, e20]
  have e3t : (Function.update st₂.regs (t + 1) (p₁ + w.size)) t = h := by
    simp [Function.update_apply, e2t]
  have e3t1 : (Function.update st₂.regs (t + 1) (p₁ + w.size)) (t + 1) = p₁ + w.size := by simp
  have hsz := size_lt_two_pow_wt w
  have hsub : p₁ + w.size - p₁ = w.size := by omega
  have hsa := va.size_le_wt
  refine WP.seq' (fun st₅ c => ValAt st₅.mem h w ∧
      (∀ x, x < h ∨ h + w.size ≤ x → st₅.mem x = st'.mem x) ∧
      st₅.regs = Function.update (Function.update st₂.regs (t + 1) (p₁ + w.size)) 1 0 ∧
      c ≤ (10 + 4 * len p₁ + len h + 2 * len (p₁ + w.size) + len w.size) +
        30 * (w.size + 1) * (len (p₁ + 2 ^ w.wt) + 1) + 1) ?_ ?_
  · refine (wp_copyVal (P := P)
      (st := { mem := st'.mem, regs := Function.update st₂.regs (t + 1) (p₁ + w.size) })
      (s := p₁) (d := h) (M := p₁ + 2 ^ w.wt) (v := w) vw
      ?_ ?_ ?_ (Or.inl (by omega)) (by omega) (by omega) (by omega)).mono ?_
    · simp [machine_simps, e20]
    · simp [machine_simps, e2t]
    · simp [machine_simps, e20]
    · rintro o st'' c ⟨rfl, a1, a2, a3, a4⟩
      refine ⟨rfl, a1, a2, a3, ?_⟩
      have n1 : (0 = t + 1) = False := by simp
      have n2 : (t = t + 1) = False := by simp
      simp only [machine_simps, n1, n2, if_false, e20, e2t, hsub, len_zero] at a4
      omega
  rintro st₅ c₅ ⟨vw5, m5, r5, k5⟩
  apply WP.assign
  have e50 : st₅.regs 0 = p₁ := by rw [r5]; simp [Function.update_apply, e20]
  have e5t : st₅.regs t = h := by
    rw [r5]; simp [Function.update_apply, show t ≠ 1 by omega, e2t]
  have e5t1 : st₅.regs (t + 1) = p₁ + w.size := by
    rw [r5]; simp [Function.update_apply, show t ≠ 0 by omega]
  refine ⟨rfl, w, _, hQ, ⟨by omega, by rw [hh]; exact vw5, ?_, ?_, ?_⟩⟩
  · simp [machine_simps, e50, e5t, e5t1, hh, hsub]
  · refine ⟨fun a ha' => ?_, fun r h2 hr => ?_⟩
    · rw [hh] at ha'
      simp only
      rw [m5 a (Or.inl ha'), mw a (by omega)]
      exact f₂.mem a (by rw [hh]; exact ha')
    · simp only [Function.update_apply]
      rw [if_neg (by omega), r5]
      simp only [Function.update_apply]
      rw [if_neg (by omega), if_neg (by omega)]
      exact f₂.regs r h2 hr
  · rw [hh, show ca + cb + w.wt + 1 = ca + cb + (w.wt + 1) by ring]
    refine bnd_two' (A := 200) (by omega) hD k2 k4 (by omega) ?_ ?_
    · have := len_add_le' h va.size
      rw [hp₁] at this
      omega
    have l1 := len_add_le' h va.size
    rw [hp₁] at l1
    have hsw := w.size_le_wt
    have l2 := len_add_le' p₁ w.size
    have l3 : len w.size ≤ w.size := GI.Machine.len_le_self _
    have l4 := len_add_two_pow p₁ w.wt
    have l5 := len_add_le' h w.size
    obtain ⟨hW1, hW2, -⟩ := W_ge (s := w.wt + 1) (c := ca + cb + (w.wt + 1))
      (Y := len h + (ca + cb + (w.wt + 1)) + 1) (by omega) (by omega)
    have hcopy : 30 * (w.size + 1) * (len (p₁ + 2 ^ w.wt) + 1) ≤
        90 * ((w.wt + 1) * (len h + (ca + cb + (w.wt + 1)) + 1)) := by
      calc 30 * (w.size + 1) * (len (p₁ + 2 ^ w.wt) + 1)
          ≤ 30 * (w.wt + 1) * (3 * (len h + (ca + cb + (w.wt + 1)) + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
        _ ≤ 90 * ((w.wt + 1) * (len h + (ca + cb + (w.wt + 1)) + 1)) := by ring_nf; omega
    simp only [machine_simps, e50, e5t, e5t1, e20, e2t, hsub, len_zero]
    omega

theorem spec_prim {j : ℕ} {a : Expr} {p : Prim} {Ra : Val → ℕ → Prop} (hctx : CtxOK ctx t)
    (ht : 2 ≤ t) (hj : P.prims[j]? = some p)
    (ha : Spec P K D ctx (t + 1) env (compE (primOff P) ctx (t + 1) a) Ra)
    (hq : ∀ v ca, Ra v ca → p.Pre v ∧ ∀ w, p.Post v w → Q w (ca + p.bound v + w.wt + 1)) :
    Spec P K D ctx t env (compE (primOff P) ctx t (.prim j a)) Q := by
  intro st henv
  have hK := hc.K_ge
  have hD := hc.D_ge
  have hkD : p.k + 1 ≤ D := hc.prim_k p (List.mem_of_getElem? hj)
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  simp only [compE]
  refine seq_prelude hctx ht ha henv fun va ca st₂ c₂ hRa hwa va2 e20 f₂ e2t k2 => ?_
  rw [hh] at va2 e20 e2t k2
  obtain ⟨hpre, hpost⟩ := hq va ca hRa
  have hcall := GI.Machine.PolyTimeWith.wp_call p.spec (compile_embeds_prim hj) (st := st₂)
    (r := t + 1) (e := .reg t) (x := ⟨va, hpre⟩)
    (by simpa [primTask, GI.Cited.Task.ofVal, e2t] using va2)
  simp only [machine_simps, e2t] at hcall
  refine WP.seq' (fun st₃ c₃ => GI.Machine.CallPost (primTask p.Pre p.Post) p.c p.k ⟨va, hpre⟩
    h (t + 1) (1 + len h) st₂ .normal st₃ c₃) (hcall.mono fun o st' c hp => ⟨hp.normal,
      hp.normal ▸ hp⟩) ?_
  rintro st₃ c₃ hp
  obtain ⟨w, hw, hPost⟩ := hp.output
  have hQ := hpost w hPost
  obtain ⟨r, hr⟩ : ∃ r, st₃.regs (t + 1) = r := ⟨_, rfl⟩
  rw [hr] at hw
  have hge : h ≤ r := hr ▸ hp.ge
  have hlr : len r ≤ c₃ := hr ▸ hp.len_le
  have hc3 : c₃ ≤ p.c * (va.size + len h + 2) ^ p.k + (1 + len h) := hp.cost_le
  have e3t : st₃.regs t = h := by rw [hp.regs t (by omega), e2t]
  refine WP.seq' (fun st₄ c => st₄ = { st₃ with regs := Function.update st₃.regs (t + 2) w.size } ∧
      c ≤ 20 * (len (r + w.size) + 1)) ?_ ?_
  · refine (wp_sizeInto (r := t + 2) (a := t + 1) (v := w) (by rw [hr]; exact hw)).mono ?_
    rintro o st' c ⟨rfl, h1, h2⟩; rw [hr] at h2; exact ⟨rfl, h1, h2⟩
  rintro st₄ c₄ ⟨rfl, hc₄⟩
  have hsz := size_lt_two_pow_wt w
  refine WP.seq' (fun st₅ c => ValAt st₅.mem h w ∧
      (∀ x, x < h ∨ h + w.size ≤ x → st₅.mem x = st₃.mem x) ∧
      st₅.regs = Function.update (Function.update st₃.regs (t + 2) w.size) 1 0 ∧
      c ≤ (3 + len r + len h + len w.size) + 30 * (w.size + 1) * (len (r + 2 ^ w.wt) + 1) + 1)
    ?_ ?_
  · refine (wp_copyVal (P := P) (st := { st₃ with regs := Function.update st₃.regs (t + 2) w.size })
      (s := r) (d := h) (M := r + 2 ^ w.wt) (v := w) hw ?_ ?_ ?_ (Or.inl hge) (by omega) (by omega)
      (by omega)).mono ?_
    · simp [machine_simps, hr]
    · simp [machine_simps, e3t]
    · simp [machine_simps]
    · rintro o st' c ⟨rfl, a1, a2, a3, a4⟩
      refine ⟨rfl, a1, a2, a3, ?_⟩
      have n1 : (t + 1 = t + 2) = False := by simp
      have n2 : (t = t + 2) = False := by simp
      simp only [machine_simps, n1, n2, if_false, hr, e3t, if_true] at a4
      omega
  rintro st₅ c₅ ⟨vw5, m5, r5, k5⟩
  apply WP.assign
  have e5t : st₅.regs t = h := by
    rw [r5]; simp [Function.update_apply, show t ≠ 1 by omega, e3t]
  have e5t2 : st₅.regs (t + 2) = w.size := by
    rw [r5]; simp [Function.update_apply]
  refine ⟨rfl, w, _, hQ, ⟨by omega, by rw [hh]; exact vw5, ?_, ?_, ?_⟩⟩
  · simp [machine_simps, e5t, e5t2, hh]
  · refine ⟨fun x hx => ?_, fun r' h2 hr' => ?_⟩
    · rw [hh] at hx
      simp only
      rw [m5 x (Or.inl hx), hp.below x hx]
      exact f₂.mem x (by rw [hh]; exact hx)
    · simp only [Function.update_apply]
      rw [if_neg (by omega), r5]
      simp only [Function.update_apply]
      rw [if_neg (by omega), if_neg (by omega), hp.regs r' (by omega)]
      exact f₂.regs r' h2 hr'
  · rw [hh, show ca + p.bound va + w.wt + 1 = ca + (p.bound va + w.wt + 1) by ring]
    refine bnd_one_pow' (A := 300) (e := p.k + 1) (by omega) hkD k2 (by omega) ?_
    -- Names for the quantities of the bound.
    obtain ⟨B, hB⟩ : ∃ B, p.bound va = B := ⟨_, rfl⟩
    rw [hB]
    have hsplit : p.c * (va.size + len h + 2) ^ p.k ≤ B * (len h + 1) ^ p.k := by
      rw [← hB]; exact prim_cost_split _ _ _ _
    obtain ⟨Y, hY⟩ : ∃ Y, len h + (ca + (B + w.wt + 1)) + 1 = Y := ⟨_, rfl⟩
    obtain ⟨Z, hZ⟩ : ∃ Z, Y ^ (p.k + 1) = Z := ⟨_, rfl⟩
    rw [hY, hZ]
    have hY1 : 1 ≤ Y := by omega
    have hYZ : Y ≤ Z := by
      rw [← hZ]
      calc Y = Y ^ 1 := (pow_one Y).symm
        _ ≤ Y ^ (p.k + 1) := Nat.pow_le_pow_right hY1 (by omega)
    have hpowZ : (len h + 1) ^ p.k ≤ Z := by
      rw [← hZ]
      calc (len h + 1) ^ p.k ≤ Y ^ p.k := Nat.pow_le_pow_left (by omega) _
        _ ≤ Y ^ (p.k + 1) := Nat.pow_le_pow_right hY1 (by omega)
    obtain ⟨s, hs⟩ : ∃ s, B + w.wt + 1 = s := ⟨_, rfl⟩
    rw [hs]
    have hs1 : 1 ≤ s := by omega
    have hBZ : B * (len h + 1) ^ p.k ≤ s * Z :=
      Nat.mul_le_mul (by omega) hpowZ
    have hZ1 : 1 ≤ Z := le_trans hY1 hYZ
    have hsZ : Z ≤ s * Z := Nat.le_mul_of_pos_left _ (by omega)
    have hW : s * Z ≤ s * (ca + s) * Z :=
      calc s * Z = s * 1 * Z := by ring
        _ ≤ s * (ca + s) * Z := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have hc3' : c₃ ≤ 2 * (s * Z) := by
      have : len h + 1 ≤ Y := by omega
      omega
    have hsw := w.size_le_wt
    have l1 := len_add_le' r w.size
    have l2 := len_add_two_pow r w.wt
    have l3 : len w.size ≤ w.size := GI.Machine.len_le_self _
    have l4 := len_add_le' h w.size
    have hlenM : len (r + 2 ^ w.wt) + 1 ≤ 5 * (s * Z) := by omega
    have hcopy : 30 * (w.size + 1) * (len (r + 2 ^ w.wt) + 1) ≤ 150 * (s * (ca + s) * Z) := by
      calc 30 * (w.size + 1) * (len (r + 2 ^ w.wt) + 1)
          ≤ 30 * s * (5 * (s * Z)) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hlenM
        _ = 150 * (s * s * Z) := by ring
        _ ≤ 150 * (s * (ca + s) * Z) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    simp only [machine_simps, e5t, e5t2]
    omega

theorem spec_get {l i : Expr} {Ra Rb : Val → ℕ → Prop} (hctx : CtxOK ctx t) (ht : 2 ≤ t)
    (ha : Spec P K D ctx (t + 1) env (compE (primOff P) ctx (t + 1) l) Ra)
    (hb : Spec P K D ctx (t + 1) env (compE (primOff P) ctx (t + 1) i) Rb)
    (hq : ∀ va ca vb cb, Ra va ca → Rb vb cb → ∃ vs x, va = .list vs ∧ vb = .nat x ∧
        ∃ hx : x < vs.length, Q vs[x] (ca + cb + vs[x].wt + 1)) :
    Spec P K D ctx t env (compE (primOff P) ctx t (.get l i)) Q := by
  intro st henv
  have hK := hc.K_ge
  have hD := hc.D_ge
  obtain ⟨h, hh⟩ : ∃ h, st.regs 0 = h := ⟨_, rfl⟩
  simp only [compE]
  refine seq_prelude hctx ht ha henv fun va ca st₂ c₂ hRa hwa va2 e20 f₂ e2t k2 => ?_
  rw [hh] at va2 e20 e2t k2
  obtain ⟨p₁, hp₁⟩ : ∃ p, h + va.size = p := ⟨_, rfl⟩
  rw [hp₁] at e20
  refine seq_sub hb (henv.of_frame hctx (f₂.mono_t (by omega)) (by rw [e20, hh]; omega))
    fun vb cb st₃ c₃ hRb db => ?_
  obtain ⟨vs, x, rfl, rfl, hx, hQ⟩ := hq _ _ _ _ hRa hRb
  obtain ⟨vb3, e30, m32, k3⟩ := db.base e20
  simp only [size_nat] at e30
  have e3t : st₃.regs t = h := by rw [db.frame.regs t ht (by omega), e2t]
  have vl := ValAt.list_iff.mp (va2.of_below (mem' := st₃.mem) (top := p₁) (by omega)
    fun a ha' => m32 a ha')
  have vx := ValAt.nat_iff.mp vb3
  -- Facts on sizes.
  have hsl := size_list vs
  have hwl := (Val.list vs).size_le_wt
  have hlc := length_le_cellsList vs
  have htake := cellsList_take_le vs (x + 1)
  rw [cellsList_take_succ vs x hx] at htake
  have hsx := vs[x].size_le_wt
  have hsz := size_lt_two_pow_wt vs[x]
  have hwb := db.wt
  rw [wt_nat] at hwb
  -- The two assignments before the loop.
  apply seq_assign
  have hv1 : (evalExpr st₃ (.load (.reg 0 - 1))).1 = x := by
    simp [machine_simps, e30, show p₁ + 2 - 1 = p₁ + 1 by omega, vx.2]
  have hc1 : (evalExpr st₃ (.load (.reg 0 - 1))).2 ≤ 8 + 3 * len (p₁ + 2) + len x := by
    have := len_mono (show p₁ + 1 ≤ p₁ + 2 by omega)
    simp [machine_simps, e30, show p₁ + 2 - 1 = p₁ + 1 by omega, vx.2, len_one]
    omega
  generalize (evalExpr st₃ (.load (.reg 0 - 1))).2 = c₄ at hc1 ⊢
  rw [hv1]
  apply seq_assign
  have hv2 : (evalExpr { st₃ with regs := Function.update st₃.regs (t + 1) x }
      (.reg t + 3)).1 = h + 3 := by
    simp [machine_simps, e3t]
  have hc2 : (evalExpr { st₃ with regs := Function.update st₃.regs (t + 1) x }
      (.reg t + 3)).2 ≤ 8 + 2 * len (h + 3) := by
    have := len_mono (show h ≤ h + 3 by omega)
    simp [machine_simps, e3t, show len 3 = 2 from rfl]
    omega
  generalize (evalExpr { st₃ with regs := Function.update st₃.regs (t + 1) x }
      (.reg t + 3)).2 = c₅ at hc2 ⊢
  rw [hv2]
  -- The loop.
  obtain ⟨L, hL⟩ : ∃ L, (Val.cellsList (vs.take x)).length = L := ⟨_, rfl⟩
  rw [hL] at htake
  refine WP.seq' (fun st₆ c => st₆.mem = st₃.mem ∧ st₆.regs (t + 2) = h + 3 + L ∧
      (∀ r, r ≠ t + 3 → r ≠ t + 2 → r ≠ t + 4 → st₆.regs r =
        Function.update (Function.update st₃.regs (t + 1) x) (t + 2) (h + 3) r) ∧
      c ≤ x * (40 * (len (h + 3 + (Val.cellsList vs).length) + 1) + 11 + 6 * len x) + 7 +
        4 * len x) ?_ ?_
  · refine (wp_skipLoop (vs := vs) (b := h + 3) (x := x) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by simpa using vl.2.2.2) hx.le (by simp) (by simp)).mono ?_
    rintro o st' c ⟨rfl, a1, a2, a3, a4⟩
    exact ⟨rfl, a1, by rw [a2, hL], a3, a4⟩
  rintro st₆ c₆ ⟨m6, e6a, r6, k6⟩
  have e6t : st₆.regs t = h := by
    rw [r6 t (by omega) (by omega) (by omega)]; simp [Function.update_apply, e3t]
  have hvx : ValAt st₆.mem (st₆.regs (t + 2)) vs[x] := by
    rw [m6, e6a, ← hL]; exact vl.2.2.2.get x hx
  refine WP.seq' (fun st₇ c => st₇ = { st₆ with regs := Function.update st₆.regs (t + 4) vs[x].size } ∧
      c ≤ 20 * (len (h + 3 + L + vs[x].size) + 1)) ?_ ?_
  · refine (wp_sizeInto hvx).mono ?_
    rintro o st' c ⟨rfl, a1, a2⟩; rw [e6a] at a2; exact ⟨rfl, a1, a2⟩
  rintro st₇ c₇ ⟨rfl, k7⟩
  refine WP.seq' (fun st₈ c => ValAt st₈.mem h vs[x] ∧
      (∀ y, y < h ∨ h + vs[x].size ≤ y → st₈.mem y = st₆.mem y) ∧
      st₈.regs = Function.update (Function.update st₆.regs (t + 4) vs[x].size) 1 0 ∧
      c ≤ (3 + len (h + 3 + L) + len h + len vs[x].size) +
        30 * (vs[x].size + 1) * (len (p₁ + 2 ^ vs[x].wt) + 1) + 1) ?_ ?_
  · refine (wp_copyVal (P := P) (st := ⟨st₆.mem, Function.update st₆.regs (t + 4) vs[x].size⟩)
      (s := h + 3 + L) (d := h) (M := p₁ + 2 ^ vs[x].wt) (v := vs[x])
      (by rw [← e6a]; exact hvx) ?_ ?_ ?_ (Or.inl (by omega)) (by omega) (by omega)
      (by omega)).mono ?_
    · simp [machine_simps, e6a]
    · simp [machine_simps, e6t]
    · simp [machine_simps]
    · rintro o st' c ⟨rfl, a1, a2, a3, a4⟩
      refine ⟨rfl, a1, a2, a3, ?_⟩
      have n1 : (t + 2 = t + 4) = False := by simp
      have n2 : (t = t + 4) = False := by simp
      simp only [machine_simps, n1, n2, if_false, if_true, e6a, e6t] at a4
      omega
  rintro st₈ c₈ ⟨vw8, m8, r8, k8⟩
  apply WP.assign
  have e8t : st₈.regs t = h := by
    rw [r8]; simp [Function.update_apply, show t ≠ 1 by omega, e6t]
  have e8t4 : st₈.regs (t + 4) = vs[x].size := by
    rw [r8]; simp [Function.update_apply]
  refine ⟨rfl, vs[x], _, hQ, ⟨by omega, by rw [hh]; exact vw8, ?_, ?_, ?_⟩⟩
  · simp [machine_simps, e8t, e8t4, hh]
  · refine ⟨fun y hy => ?_, fun r h2 hr => ?_⟩
    · rw [hh] at hy
      simp only
      rw [m8 y (Or.inl hy), m6, m32 y (by omega)]
      exact f₂.mem y (by rw [hh]; exact hy)
    · simp only [Function.update_apply]
      rw [if_neg (by omega), r8]
      simp only [Function.update_apply]
      rw [if_neg (by omega), if_neg (by omega), r6 r (by omega) (by omega) (by omega)]
      simp only [Function.update_apply]
      rw [if_neg (by omega), if_neg (by omega), db.frame.regs r h2 (by omega)]
      exact f₂.regs r h2 hr
  · rw [hh, show ca + cb + vs[x].wt + 1 = ca + cb + (vs[x].wt + 1) by ring]
    refine bnd_two' (A := 300) (by omega) hD k2 k3 (by omega) ?_ ?_
    · have := len_add_le' h (Val.list vs).size
      rw [hp₁] at this
      omega
    obtain ⟨s, hs⟩ : ∃ s, vs[x].wt + 1 = s := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y, len h + (ca + cb + s) + 1 = Y := ⟨_, rfl⟩
    rw [hs, hY]
    obtain ⟨hW1, hW2, hW3⟩ := W_ge (s := s) (c := ca + cb + s) (Y := Y) (by omega) (by omega)
    have l1 := len_add_le' h (Val.list vs).size
    rw [hp₁] at l1
    have l2 := len_add_le' h (3 + (Val.cellsList vs).length)
    have l3 := len_add_le' h (3 + L + vs[x].size)
    have l4 := len_add_two_pow p₁ vs[x].wt
    have l5 := len_add_le' h vs[x].size
    have l6 : len x ≤ x := GI.Machine.len_le_self _
    have l7 : len vs[x].size ≤ vs[x].size := GI.Machine.len_le_self _
    have l8 := len_add_le' h (3 + L)
    have l9 := len_add_le' p₁ 2
    simp only [← Nat.add_assoc] at l2 l3 l8
    have hloop : x * (40 * (len (h + 3 + (Val.cellsList vs).length) + 1) + 11 + 6 * len x) ≤
        57 * ((ca + cb + s) * Y) := by
      calc x * (40 * (len (h + 3 + (Val.cellsList vs).length) + 1) + 11 + 6 * len x)
          ≤ (ca + cb + s) * (57 * Y) := Nat.mul_le_mul (by omega) (by omega)
        _ = 57 * ((ca + cb + s) * Y) := by ring
    have hcopy : 30 * (vs[x].size + 1) * (len (p₁ + 2 ^ vs[x].wt) + 1) ≤ 90 * (s * Y) := by
      calc 30 * (vs[x].size + 1) * (len (p₁ + 2 ^ vs[x].wt) + 1)
          ≤ 30 * s * (3 * Y) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
        _ = 90 * (s * Y) := by ring
    have l10 := len_add_le' h 3
    have t1 : c₄ ≤ 20 * Y := by omega
    have t2 : c₅ ≤ 20 * Y := by omega
    have t3 : c₆ ≤ 70 * (s * (ca + cb + s) * Y) := by omega
    have t4 : c₇ ≤ 40 * Y := by omega
    have t5 : c₈ ≤ 100 * (s * (ca + cb + s) * Y) := by omega
    simp only [machine_simps, e8t, e8t4]
    rw [Nat.sub_le_iff_le_add, Nat.sub_le_iff_le_add]
    omega

end Cases

end GI.Lang
