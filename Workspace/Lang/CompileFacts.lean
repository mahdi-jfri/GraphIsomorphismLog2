/-
Facts used by the correctness proof of the compiler (`Workspace.Lang.Correct`).

* Where the procedures of `compile P` are (`compile_copy`, `compile_fun`, `compile_embeds_prim`).
* `wp_sizeInto`: reading the size of a stored value.
* `wp_copyCall`, `wp_copyVal`: copying cells, and copying a stored value.
* `EnvAt`: the environment values are stored at the addresses in the context registers, below
  the heap pointer.
* Cost arithmetic: `len_add_le'`, `bnd_combine`, `overhead_le`.
-/
module

public import Workspace.Lang.Compile

@[expose] public section

namespace GI.Lang

open GI.Machine (Stmt Outcome State WP Runs len copyBody evalExpr evalArgs Embeds wp_copy
  len_mono len_le_iff lt_two_pow_len len_succ_le len_zero len_one)
open GI.Cited (Val ValAt)

/-! ### Lengths -/

theorem len_add_le' (x y : ℕ) : len (x + y) ≤ len x + y := by
  induction y with
  | zero => simp
  | succ y ih => have := len_succ_le (x + y); rw [← Nat.add_assoc]; omega

theorem len_le_of_le {x y : ℕ} (h : x ≤ y) : len x ≤ len y := len_mono h

/-- A number below `2 ^ k` has length at most `k`. -/
theorem len_le_of_lt_two_pow {x k : ℕ} (h : x < 2 ^ k) : len x ≤ k := len_le_iff.mpr h

/-! ### The procedures of the compiled program -/

theorem length_primsCode (off : ℕ) (ps : List Prim) :
    (primsCode off ps).length = (ps.map fun p => p.prog.procs.length).sum := by
  induction ps generalizing off with
  | nil => rfl
  | cons p ps ih => simp [primsCode, ih, GI.Machine.Program.shifted]

theorem primsCode_append (off : ℕ) (ps qs : List Prim) :
    primsCode off (ps ++ qs) =
      primsCode off ps ++ primsCode (off + (ps.map fun p => p.prog.procs.length).sum) qs := by
  induction ps generalizing off with
  | nil => simp [primsCode]
  | cons p ps ih => simp [primsCode, ih, Nat.add_assoc]

theorem compile_copy (P : Program) : (compile P).procs[0]? = some copyBody := rfl

theorem compile_fun {P : Program} {f : ℕ} {body : Expr} (hf : P.funs[f]? = some body) :
    (compile P).procs[1 + f]? = some (funBody (primOff P) body) := by
  have hlt : f < P.funs.length := (List.getElem?_eq_some_iff.mp hf).1
  simp only [compile]
  rw [List.getElem?_append_left (by simp; omega), Nat.add_comm, List.getElem?_cons_succ]
  simp [hf]

theorem compile_embeds_prim {P : Program} {j : ℕ} {p : Prim} (hj : P.prims[j]? = some p) :
    Embeds (compile P) p.prog (primOff P j) := by
  have hlt : j < P.prims.length := (List.getElem?_eq_some_iff.mp hj).1
  have hp : P.prims[j] = p := (List.getElem?_eq_some_iff.mp hj).2
  have hsplit : P.prims = P.prims.take j ++ p :: P.prims.drop (j + 1) := by
    rw [← hp]; simp
  set A := copyBody :: P.funs.map (funBody (primOff P)) ++
    primsCode (1 + P.funs.length) (P.prims.take j)
  have hA : A.length = primOff P j := by
    simp [A, primOff, length_primsCode]; omega
  rw [← hA]
  refine Embeds.of_append (B := primsCode (primOff P j + p.prog.procs.length)
    (P.prims.drop (j + 1))) ?_
  have : (compile P).procs = copyBody :: P.funs.map (funBody (primOff P)) ++
      primsCode (1 + P.funs.length) P.prims := rfl
  rw [this]
  conv_lhs => rw [hsplit]
  rw [primsCode_append]
  have e1 : (copyBody :: (P.funs.map (funBody (primOff P)) ++
      primsCode (1 + P.funs.length) (P.prims.take j))).length = primOff P j := by
    simp [primOff, length_primsCode]; omega
  simp only [primsCode, A, List.cons_append, List.append_assoc, e1]
  rfl

/-! ### Reading the size of a value -/

theorem wp_sizeInto {q : GI.Machine.Program} {st : State} {r a : ℕ} {v : Val}
    (h : ValAt st.mem (st.regs a) v) :
    WP q (sizeInto r a) st (fun o st' c => o = .normal ∧
      st' = { st with regs := Function.update st.regs r v.size } ∧
      c ≤ 20 * (len (st.regs a + v.size) + 1)) := by
  have hl1 : len (st.regs a) ≤ len (st.regs a + v.size) := len_mono (by omega)
  have hl2 : len (st.regs a + 2) ≤ len (st.regs a + v.size) := len_mono (by
    have := v.two_le_size; omega)
  cases v with
  | nat n =>
    rw [ValAt.nat_iff] at h
    apply GI.Machine.WP.cond
    simp only [GI.Machine.evalExpr_load, GI.Machine.evalExpr_reg, h.1, if_true]
    apply GI.Machine.WP.assign
    refine ⟨rfl, by simp, ?_⟩
    simp only [machine_simps, len_zero, show len 2 = 2 from rfl]
    simp only [size_nat] at hl1 hl2 ⊢
    omega
  | list vs =>
    rw [ValAt.list_iff] at h
    apply GI.Machine.WP.cond
    simp only [GI.Machine.evalExpr_load, GI.Machine.evalExpr_reg, h.1, one_ne_zero, if_false]
    apply GI.Machine.WP.assign
    refine ⟨rfl, ?_, ?_⟩
    · simp only [machine_simps, h.2.2.1, size_list]
    · have h3 : len ((Val.cellsList vs).length) ≤ len (st.regs a + (Val.list vs).size) :=
        len_mono (by rw [size_list]; omega)
      have h4 : len ((Val.cellsList vs).length + 3) ≤ len (st.regs a + (Val.list vs).size) :=
        len_mono (by rw [size_list]; omega)
      simp only [machine_simps, h.2.2.1, len_one, show len 2 = 2 from rfl,
        show len 3 = 2 from rfl]
      omega

/-! ### Copying -/

theorem compile_copy' (P : Program) : (compile P).procs[0]? = some copyBody := rfl

/-- One call of the copy procedure: `L` cells from `s` to `d`, where `d ≤ s` or the two blocks do
not overlap. All addresses and copied values are at most `M`. -/
theorem wp_copyCall {P : Program} {st : State} {e₁ e₂ e₃ : MExpr} {s d L M : ℕ}
    (h1 : (evalExpr st e₁).1 = s) (h2 : (evalExpr st e₂).1 = d) (h3 : (evalExpr st e₃).1 = L)
    (hdisj : d ≤ s ∨ s + L ≤ d) (hM : s + L ≤ M) (hM' : d + L ≤ M)
    (hv : ∀ i < L, st.mem (s + i) ≤ M) :
    WP (compile P) (copyCall e₁ e₂ e₃) st (fun o st' c => o = .normal ∧
      (∀ i < L, st'.mem (d + i) = st.mem (s + i)) ∧
      (∀ x, x < d ∨ d + L ≤ x → st'.mem x = st.mem x) ∧
      st'.regs = Function.update st.regs 1 0 ∧
      c ≤ (evalArgs st [e₁, e₂, e₃]).2 + 30 * (L + 1) * (len M + 1) + 1) := by
  apply GI.Machine.WP.call (compile_copy P)
  refine (wp_copy (p := compile P) (M := M) (src := s) (dst := d) (L := L)
    (st := { mem := st.mem, regs := fun i => (evalArgs st [e₁, e₂, e₃]).1.getD i 0 })
    ?_ ?_ ?_ hdisj hM hM' hv).mono ?_
  · simp [h1]
  · simp [h2]
  · simp [h3]
  · rintro o st' c ⟨rfl, a1, a2, -, a4⟩
    exact ⟨rfl, a1, a2, rfl, by omega⟩

/-- Copying a stored value. -/
theorem wp_copyVal {P : Program} {st : State} {e₁ e₂ e₃ : MExpr} {s d M : ℕ} {v : Val}
    (hval : ValAt st.mem s v)
    (h1 : (evalExpr st e₁).1 = s) (h2 : (evalExpr st e₂).1 = d)
    (h3 : (evalExpr st e₃).1 = v.size)
    (hdisj : d ≤ s ∨ s + v.size ≤ d) (hM : s + v.size ≤ M) (hM' : d + v.size ≤ M)
    (hv : 2 ^ v.wt ≤ M) :
    WP (compile P) (copyCall e₁ e₂ e₃) st (fun o st' c => o = .normal ∧
      ValAt st'.mem d v ∧
      (∀ x, x < d ∨ d + v.size ≤ x → st'.mem x = st.mem x) ∧
      st'.regs = Function.update st.regs 1 0 ∧
      c ≤ (evalArgs st [e₁, e₂, e₃]).2 + 30 * (v.size + 1) * (len M + 1) + 1) := by
  refine (wp_copyCall h1 h2 h3 hdisj hM hM' ?_).mono ?_
  · intro i hi
    have := Val.lt_two_pow_wt (hval.mem_cells hi)
    omega
  · rintro o st' c ⟨rfl, a1, a2, a3, a4⟩
    refine ⟨rfl, fun i hi => ?_, a2, a3, a4⟩
    rw [a1 i hi]; exact hval i hi

/-! ### Environments -/

/-- The environment `env` is stored at the addresses in the registers `ctx`, each value below the
heap pointer. -/
def EnvAt (st : State) (ctx : List ℕ) (env : List Val) : Prop :=
  List.Forall₂ (fun r v => ValAt st.mem (st.regs r) v ∧ st.regs r + v.size ≤ st.regs 0) ctx env

/-- The context registers lie between 2 and `t - 1`. -/
def CtxOK (ctx : List ℕ) (t : ℕ) : Prop := ∀ r ∈ ctx, 2 ≤ r ∧ r < t

theorem CtxOK.mono {ctx : List ℕ} {t t' : ℕ} (h : CtxOK ctx t) (ht : t ≤ t') : CtxOK ctx t' :=
  fun r hr => ⟨(h r hr).1, by have := (h r hr).2; omega⟩

theorem EnvAt.mono {st st' : State} {ctx : List ℕ} {env : List Val} (h : EnvAt st ctx env)
    (hr : ∀ r ∈ ctx, st'.regs r = st.regs r) (hm : ∀ a < st.regs 0, st'.mem a = st.mem a)
    (hp : st.regs 0 ≤ st'.regs 0) : EnvAt st' ctx env := by
  unfold EnvAt at *
  induction h with
  | nil => exact .nil
  | @cons r v ctx env hrv _ ih =>
    refine .cons ⟨?_, ?_⟩ (ih (fun r' hr' => hr r' (by simp [hr'])))
    · rw [hr r (by simp)]
      exact hrv.1.congr fun x _ hx => hm x (by omega)
    · rw [hr r (by simp)]; omega

theorem EnvAt.get {st : State} {ctx : List ℕ} {env : List Val} (h : EnvAt st ctx env) {i : ℕ}
    (hi : i < env.length) :
    ValAt st.mem (st.regs (ctx.getD i 0)) env[i] ∧
      st.regs (ctx.getD i 0) + env[i].size ≤ st.regs 0 ∧ ctx.getD i 0 ∈ ctx := by
  unfold EnvAt at h
  induction h generalizing i with
  | nil => simp at hi
  | @cons r v ctx env hrv _ ih =>
    cases i with
    | zero => simpa using hrv
    | succ i =>
      obtain ⟨a, b, c⟩ := ih (by simpa using hi)
      simp only [List.getD_cons_succ, List.getElem_cons_succ]
      exact ⟨a, b, List.mem_cons_of_mem _ c⟩

theorem EnvAt.snoc {st : State} {ctx : List ℕ} {env : List Val} (h : EnvAt st ctx env)
    {t : ℕ} {v : Val} (hv : ValAt st.mem (st.regs t) v) (hle : st.regs t + v.size ≤ st.regs 0) :
    EnvAt st (ctx ++ [t]) (env ++ [v]) :=
  List.rel_append h (.cons ⟨hv, hle⟩ .nil)

theorem EnvAt.length {st : State} {ctx : List ℕ} {env : List Val} (h : EnvAt st ctx env) :
    ctx.length = env.length := List.Forall₂.length_eq h

/-! ### Cost arithmetic -/

/-- The bound on the machine cost of compiled code that starts with heap pointer `h` and has
language cost `c`. -/
def Bnd (K D h c : ℕ) : ℕ := K * c ^ 2 * (len h + c + 1) ^ D

/-- Two subcomputations of costs `c₁, c₂` and overhead `o`, for a step with own charge `s`. -/
theorem bnd_combine {K D h h₁ h₂ c₁ c₂ s m₁ m₂ o : ℕ}
    (hm₁ : m₁ ≤ Bnd K D h₁ c₁) (hm₂ : m₂ ≤ Bnd K D h₂ c₂)
    (hh₁ : len h₁ + c₁ ≤ len h + c₁ + c₂ + s) (hh₂ : len h₂ + c₂ ≤ len h + c₁ + c₂ + s)
    (ho : o ≤ K * s * (c₁ + c₂ + s) * (len h + (c₁ + c₂ + s) + 1) ^ D) :
    m₁ + m₂ + o ≤ Bnd K D h (c₁ + c₂ + s) := by
  unfold Bnd at *
  set Y := len h + (c₁ + c₂ + s) + 1
  have e₁ : (len h₁ + c₁ + 1) ^ D ≤ Y ^ D := Nat.pow_le_pow_left (by omega) _
  have e₂ : (len h₂ + c₂ + 1) ^ D ≤ Y ^ D := Nat.pow_le_pow_left (by omega) _
  set Z := Y ^ D
  have f₁ : m₁ ≤ K * c₁ ^ 2 * Z :=
    le_trans hm₁ (Nat.mul_le_mul_left _ e₁)
  have f₂ : m₂ ≤ K * c₂ ^ 2 * Z :=
    le_trans hm₂ (Nat.mul_le_mul_left _ e₂)
  have key : c₁ ^ 2 + c₂ ^ 2 + s * (c₁ + c₂ + s) ≤ (c₁ + c₂ + s) ^ 2 := by nlinarith
  have : K * c₁ ^ 2 * Z + K * c₂ ^ 2 * Z + K * s * (c₁ + c₂ + s) * Z ≤
      K * (c₁ + c₂ + s) ^ 2 * Z := by
    have := Nat.mul_le_mul_left (K * Z) key
    nlinarith
  omega

/-- An overhead of `A * s * c * Y ^ e`, with `A ≤ K` and `e ≤ D`, fits the bound. -/
theorem overhead_le {K D A s c Y e : ℕ} (hA : A ≤ K) (he : e ≤ D) (hY : 1 ≤ Y) :
    A * s * c * Y ^ e ≤ K * s * c * Y ^ D := by
  have : Y ^ e ≤ Y ^ D := Nat.pow_le_pow_right hY he
  have h1 : A * s * c ≤ K * s * c := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hA)
  exact Nat.mul_le_mul h1 this

end GI.Lang
