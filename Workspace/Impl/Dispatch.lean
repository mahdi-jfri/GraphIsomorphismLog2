module

public import Workspace.Impl.Skeleton

@[expose] public section

/-!
# One step specification per case

The body of the function of a procedure (`Solve`, `Continue`, `GiantStep`) is a dispatcher
(`modeBody sel fs`): a selector function `sel` reads the input value and returns the number `j`
of the case that applies, and the body calls the step function `fs[j]` of that case on the same
input. This is the structure of Algorithms 4 and 5: each procedure is a list of guarded cases.

* `CasePred`: the guard of a case, a predicate on the state and the input value.
* `Iface.SelSpec m Ps sel`: on every input of a call of `m`, `sel` returns a case `j` whose
  guard `Ps[j]` holds, at cost at most `selB` (`Ks (wt v + 1)^ds` for `Solve`, `selW m S`
  otherwise).
* `Iface.StepSpec m P κs f`: **the step specification of a case.** On every input of a call of
  `m` whose state has the invariant and satisfies the guard `P`, under the induction hypothesis
  (`IH`: the recursive functions meet their specifications on smaller calls), every evaluation
  of `f` returns a canonical answer `AnsC e u A` of an actual run `r : Run P₀ m S A` that starts
  with one of the constructors `κs`, at a cost of at most

  `own m r v + childCost r`,

  where `own` is the work of the case (`W r.node`, or `Ks (wt v + 1)^ds` for `Solve`) and
  `childCost r` is the sum, over the children of `r` (`Run.children`: inherited calls, fresh
  calls and script calls), of the child's total cost and its setup `charge`. So the step
  computes the children's values (canonical ones, so that the setup is bounded by the child's
  state), calls the recursive functions on them through the function table, and combines their
  answers as the constructor combines the `A`s; the data of the constructor (the largest
  orbit, the `DispatchStep`, the `Normalization`, the `RowTerminal`, the `Aggregation`, …) is
  what the step computes, and the proof of the specification exhibits it.
* `Iface.modeOK_of_dispatch`: a selector and step specifications for all cases give `ModeOK`.

The cases of the three procedures, with their guards and constructors, are in
`Workspace/Impl/Cases.lean`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val)
open scoped Pointwise

/-- The guard of a case: a predicate on the state and the input value. -/
structure CasePred where
  P : ∀ {Ω C : Type} {k : ℕ}, (Ω ≃ Fin k) → State Ω C → Val → Prop

/-- The `if` chain of a dispatcher, in the environment `[v, j]`: call `fs[j]` on `v`. -/
def switchE : ℕ → List ℕ → Expr
  | _, [] => .nil
  | _, [f] => .call f (.var 0)
  | j, f :: g :: fs => .ite (.arith .eq (.var 1) (.nat j)) (.call f (.var 0)) (switchE (j + 1) (g :: fs))

/-- **The body of a dispatcher**: `let j := sel v in fs[j] v`. -/
def modeBody (sel : ℕ) (fs : List ℕ) : Expr := .letE (.call sel (.var 0)) (switchE 0 fs)

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

/-- The children of a run, each with its total cost and its setup charge. -/
noncomputable def childCost {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P₀ m S L A) : ℝ :=
  (r.children.map fun nd => nd.run.total I.work + I.charge nd).sum

/-- The work of the case at the root of `r`. -/
noncomputable def own (m : Mode) {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P₀ m S L A) (v : Val) : ℝ :=
  if m = .solve then (I.Ks : ℝ) * ((v.wt : ℝ) + 1) ^ I.ds else max 0 (I.W r.node)

/-- The cost bound of the selector. -/
noncomputable def selB (m : Mode) {Ω C : Type} (S : State Ω C) (v : Val) : ℝ :=
  if m = .solve then (I.Ks : ℝ) * ((v.wt : ℝ) + 1) ^ I.ds else max 0 (I.selW m S)

/-- **The step specification of a case** (see the module docstring). -/
def StepSpec (m : Mode) (Pc : CasePred) (κs : List CallKind) (f : ℕ) : Prop :=
  ∀ {Ω C : Type} (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ), Function.Injective c →
    ∀ v : Val, I.InVal m e c v S → Good P₀ m S → Pc.P e S v → I.IH Pg F m S →
      FunAll Pg f v (fun u cost => ∃ (A : Set (Perm Ω)) (L : Option (SuppliedLabels S))
        (r : Run P₀ m S L A), I.LabOf m e v S L ∧ r.kind ∈ κs ∧
        AnsC e u A ∧ (cost : ℝ) ≤ I.own m r v + I.childCost r)

/-- **The specification of a selector**: it returns the number of a case whose guard holds. -/
def SelSpec (m : Mode) (Ps : List CasePred) (sel : ℕ) : Prop :=
  ∀ {Ω C : Type} (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ), Function.Injective c →
    ∀ v : Val, I.InVal m e c v S → Good P₀ m S →
      FunAll Pg sel v (fun i cost => ∃ (j : ℕ) (hj : j < Ps.length), i = .nat j ∧
        Ps[j].P e S v ∧ (cost : ℝ) ≤ I.selB m S v)

/-- The total cost of a run is the work of its root without the setups, plus the cost of its
children with their setups. -/
theorem total_eq {m : Mode} {Ω C : Type} {S : State Ω C} {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} (r : Run P₀ m S L A) (hfit : m = .solve ∨ (Nat.card Ω ≤ S.N ∧ Small S)) :
    r.total I.work = I.base r.node + I.childCost r := by
  rw [Run.total_eq, childCost, List.sum_map_add]
  have hf : Fits r.node := hfit
  simp only [work, if_pos hf]
  have : r.node.run.children = r.children := rfl
  rw [this]
  ring

end Iface

/-! ### The `if` chain -/

theorem wt_bool_le (p : Prop) [Decidable p] : (Val.nat (if p then 1 else 0)).wt ≤ 3 := by
  split_ifs <;> simp [wt_nat, GI.Machine.len_zero]

/-- **The `if` chain calls `fs[t]`.** In the environment `[v, i]` with `i = j₀ + t`, every
evaluation of `switchE j₀ fs` is a call of `fs[t]` on `v`, and costs at most the cost of that
call plus `wt v + 2 + wt u + (t + 1) (2 i + 13 + wt u)`. -/
theorem switch_spec {Pg : Program} {v : Val} {Q : Val → ℕ → Prop} :
    ∀ (fs : List ℕ) (j₀ t i : ℕ) (ht : t < fs.length), i = j₀ + t → FunAll Pg fs[t] v Q →
      EvalAll Pg [v, .nat i] (switchE j₀ fs) (fun u c => ∃ cf, Q u cf ∧
        c ≤ cf + v.wt + 2 + u.wt + (t + 1) * (2 * i + 13 + u.wt))
  | [], _, _, _, ht, _, _ => absurd ht (by simp)
  | [f], j₀, t, i, ht, hi, hf => by
    have ht0 : t = 0 := by simp at ht; omega
    subst ht0
    simp only [List.getElem_cons_zero] at hf
    refine EvalAll.call_funAll (Det.var' (P := Pg) (env := [v, .nat i]) (i := 0) rfl)
      fun v' ca h => ?_
    obtain ⟨rfl, hca⟩ := h
    exact hf.mono fun u cf hq => ⟨cf, hq, by omega⟩
  | f :: g :: fs, j₀, t, i, ht, hi, hf => by
    have htest : Det Pg [v, .nat i] (.arith .eq (.var 1) (.nat j₀))
        (.nat (if i = j₀ then 1 else 0)) (i + j₀ + 12) := by
      have h1 := Det.var' (P := Pg) (env := [v, .nat i]) (i := 1) (v := .nat i) rfl
      have h2 := Det.arith (op := .eq) h1 (Det.nat (P := Pg) (env := [v, .nat i]) j₀)
      refine h2.mono ?_
      have := wt_nat_le i
      have := wt_bool_le (i = j₀)
      simp only [GI.Machine.BinOp.eval] at *
      omega
    refine EvalAll.ite htest (fun _ _ h => ⟨_, h.1⟩) fun x cc h => ?_
    obtain ⟨hx, hcc⟩ := h
    cases t with
    | zero =>
      have hij : i = j₀ := by omega
      have hx1 : x = 1 := by simp [hij] at hx; omega
      subst hx1
      simp only [one_ne_zero, if_false]
      simp only [List.getElem_cons_zero] at hf
      refine EvalAll.call_funAll (Det.var' (P := Pg) (env := [v, .nat i]) (i := 0) rfl)
        fun v' ca h => ?_
      obtain ⟨rfl, hca⟩ := h
      exact hf.mono fun u cf hq => ⟨cf, hq, by omega⟩
    | succ t =>
      have hij : i ≠ j₀ := by omega
      have hx0 : x = 0 := by simp [hij] at hx; omega
      subst hx0
      simp only [if_true]
      simp only [List.getElem_cons_succ] at hf
      refine (switch_spec (g :: fs) (j₀ + 1) t i (by simp at ht ⊢; omega) (by omega) hf).mono ?_
      rintro u cb ⟨cf, hq, hcb⟩
      refine ⟨cf, hq, ?_⟩
      have : (t + 1 + 1) * (2 * i + 13 + u.wt) = (t + 1) * (2 * i + 13 + u.wt) +
          (2 * i + 13 + u.wt) := by ring
      omega

/-! ### The dispatcher -/

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

theorem one_le_pow_add {x : ℝ} (hx : 0 ≤ x) (d : ℕ) : 1 ≤ (x + 1) ^ d :=
  one_le_pow₀ (by linarith)

theorem pow_le_pow_d {x : ℝ} (hx : 0 ≤ x) {a b : ℕ} (h : a ≤ b) : (x + 1) ^ a ≤ (x + 1) ^ b :=
  pow_le_pow_right₀ (by linarith) h

/-- **A dispatcher meets `ModeOK`** if its selector and the step functions of all cases meet
their specifications (at most eight cases). -/
theorem modeOK_of_dispatch {m : Mode} {sel : ℕ} {fs : List ℕ} {Ps : List CasePred}
    (hbody : Pg.funs[F.get m]? = some (modeBody sel fs)) (hlen : fs.length = Ps.length)
    (h8 : fs.length ≤ 8) (hsel : I.SelSpec Pg m Ps sel)
    (hstep : ∀ (j : ℕ) (hj : j < fs.length), ∃ κs : List CallKind,
      I.StepSpec Pg F m (Ps[j]'(hlen ▸ hj)) κs fs[j]) : I.ModeOK Pg F m := by
  intro Ω C S hg ih k e c hc v hv
  refine FunAll.intro hbody ?_
  unfold modeBody
  refine EvalAll.letE (Ra := fun iv ci => ∃ (j : ℕ) (hj : j < Ps.length), iv = .nat j ∧
      Ps[j].P e S v ∧ (ci : ℝ) ≤ v.wt + 1 + I.selB m S v + j + 3) ?_ ?_
  · refine EvalAll.call_funAll (Det.var' (P := Pg) (env := [v]) (i := 0) rfl) fun v' ca h => ?_
    obtain ⟨hv', hca⟩ := h
    rw [hv']
    refine (hsel S k e c hc v hv hg).mono fun iv cs ⟨j, hj, hiv, hP, hcs⟩ => ?_
    subst hiv
    refine ⟨j, hj, rfl, hP, ?_⟩
    have hjw := wt_nat_le j
    have hca' : (ca : ℝ) ≤ v.wt + 1 := by exact_mod_cast hca
    have hjw' : ((Val.nat j).wt : ℝ) ≤ j + 2 := by exact_mod_cast hjw
    push_cast
    linarith
  rintro iv ci ⟨j, hj, rfl, hP, hci⟩
  have hjf : j < fs.length := hlen ▸ hj
  obtain ⟨κs, hs⟩ := hstep j hjf
  have hf := hs S k e c hc v hv hg hP ih
  refine (switch_spec fs 0 j j hjf (by omega) hf).mono ?_
  rintro u cb ⟨cf, ⟨A, L, r, hL, -, hA, hcf⟩, hcb⟩
  refine ⟨A, L, r, hL, hA, ?_⟩
  -- The cost: the selector, the `if` chain and the case.
  have hj8 : j < 8 := by omega
  have hu := hA.wt_le
  rw [← card_eq e] at hu
  have hchain : (cb : ℝ) ≤ cf + v.wt + 2 + u.wt + 8 * (27 + u.wt) := by
    have h1 : (j + 1) * (2 * j + 13 + u.wt) ≤ 8 * (27 + u.wt) :=
      Nat.mul_le_mul (by omega) (by omega)
    have : cb ≤ cf + v.wt + 2 + u.wt + 8 * (27 + u.wt) := by omega
    exact_mod_cast this
  have hjr : (j : ℝ) ≤ 8 := by exact_mod_cast hj8.le
  have hkey : ((ci + cb + u.wt + 1 : ℕ) : ℝ) ≤
      I.selB m S v + I.own m r v + I.childCost r + 2 * v.wt + 10 * (ansW (Nat.card Ω) : ℝ) + 240 := by
    push_cast
    have : (u.wt : ℝ) ≤ ansW (Nat.card Ω) := by exact_mod_cast hu
    linarith
  have hfit : m = .solve ∨ (Nat.card Ω ≤ S.N ∧ Small S) := by
    cases m with
    | solve => exact Or.inl rfl
    | cont => exact Or.inr ⟨(card_eq e).trans_le (show Canon e c v S from hv).fits,
        (show Canon e c v S from hv).small'⟩
    | giant =>
      obtain ⟨sv, lv, L, -, hsv, -⟩ := hv
      exact Or.inr ⟨(card_eq e).trans_le hsv.fits, hsv.small'⟩
  rw [I.total_eq r hfit]
  refine hkey.trans ?_
  have hx : (0 : ℝ) ≤ v.wt := Nat.cast_nonneg _
  have hcc := I.childCost r
  cases m with
  | solve =>
    simp only [selB, own, base, excess, Run.node, if_true]
    -- `k ≤ wt v`, so `ansW k ≤ 1000 (wt v + 1)^6`.
    have hk : Nat.card Ω ≤ v.wt := by rw [card_eq e]; exact StateVal.k_le_wt hv
    have ha : (ansW (Nat.card Ω) : ℝ) ≤ 1000 * ((v.wt : ℝ) + 1) ^ 6 := by
      have h1 := ansW_le (Nat.card Ω)
      have h2 : (Nat.card Ω + 1) ^ 6 ≤ (v.wt + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      have : ansW (Nat.card Ω) ≤ 1000 * (v.wt + 1) ^ 6 := by omega
      exact_mod_cast this
    have h6 := pow_le_pow_d hx (le_max_right I.ds 6)
    have hds := pow_le_pow_d hx (le_max_left I.ds 6)
    have h1 : (v.wt : ℝ) + 1 ≤ ((v.wt : ℝ) + 1) ^ I.d₀ := by
      calc (v.wt : ℝ) + 1 = ((v.wt : ℝ) + 1) ^ 1 := (pow_one _).symm
        _ ≤ ((v.wt : ℝ) + 1) ^ I.d₀ := pow_le_pow_d hx I.one_le_d₀
    have hKs : (0 : ℝ) ≤ I.Ks := Nat.cast_nonneg _
    have hd0 : I.d₀ = max I.ds 6 := rfl
    rw [← hd0] at h6 hds
    have : (I.Ks : ℝ) * ((v.wt : ℝ) + 1) ^ I.ds ≤ (I.Ks : ℝ) * ((v.wt : ℝ) + 1) ^ I.d₀ :=
      mul_le_mul_of_nonneg_left hds hKs
    have hK0 : (I.K₀ : ℝ) = 2 * I.Ks + 20000 := by simp [K₀]
    rw [hK0]
    nlinarith
  | cont =>
    have hw := InVal.wt_le (by simp) hv
    simp only [selB, own, base, excess, ovh, Run.node, reduceCtorEq, if_false]
    have : (v.wt : ℝ) ≤ I.inW .cont S := by exact_mod_cast hw
    have : (0 : ℝ) ≤ ansW (Nat.card Ω) := Nat.cast_nonneg _
    linarith
  | giant =>
    have hw := InVal.wt_le (by simp) hv
    simp only [selB, own, base, excess, ovh, Run.node, reduceCtorEq, if_false]
    have : (v.wt : ℝ) ≤ I.inW .giant S := by exact_mod_cast hw
    have : (0 : ℝ) ≤ ansW (Nat.card Ω) := Nat.cast_nonneg _
    linarith

end Iface

end GI.Impl
