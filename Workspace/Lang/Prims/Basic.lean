/-
**Cited algorithms as primitives: the general part.**

A cited algorithm is a hypothesis `h : ∃ prog, PolyTimeAt (Task.ofVal enc Correct) prog` (the
form of every `GI.Cited.X` of `Workspace/Cited/Algo*.lean`). `Prim.ofHyp enc Correct h` is the
primitive of `GI.Lang` that runs the program of `h` (`Prim.ofCited` with the program and
constants chosen from `h`). No hypothesis becomes an axiom here: every primitive takes its
hypothesis as an argument.

* `PrimSpec p v Out`: on the value `v`, primitive `p` may be called (`p.Pre v`) and every result
  `w` satisfies `Out w`. The specification lemmas of the wrappers have this form, with `Out`
  stated about mathematical objects (`Workspace.Lang.Prims.Repr`).
* `Prim.ofHyp_spec`: if the encoding is injective, the result on `enc x` is correct for `x`.
* `EvalAll.prim_spec`, `FunAll.prim_spec`: a call of a primitive with a `PrimSpec`, in a program
  that holds the primitive at index `j`. The language cost of the call is the cost of the
  argument, plus `p.bound v = p.c * (v.size + 2) ^ p.k`, plus the weight of the result plus one.
  `EvalAll.prim_spec_le` replaces the weight of the result by a bound `W` on it.
* `Program.PrimsAt P b ps`: the primitives `ps` sit in `P` at indices `b, b + 1, …`, the
  counterpart of `Program.HasAt` for functions.
-/
import Workspace.Lang.Prims.Repr

namespace GI.Lang

open GI.Cited (Val PolyTimeAt)

/-- The primitive of a cited algorithm, given by its hypothesis. The program and the constants
of the bound are those that `h` provides. -/
noncomputable def Prim.ofHyp {α : Type} (enc : α → Val) (Correct : α → Val → Prop)
    (h : ∃ prog, PolyTimeAt (GI.Cited.Task.ofVal enc Correct) prog) : Prim :=
  Prim.ofCited enc Correct h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec

/-- A primitive meets a specification on a value: it may be called on `v`, and every result
satisfies `Out`. -/
def PrimSpec (p : Prim) (v : Val) (Out : Val → Prop) : Prop :=
  p.Pre v ∧ ∀ w, p.Post v w → Out w

theorem PrimSpec.mono {p : Prim} {v : Val} {Out Out' : Val → Prop} (h : PrimSpec p v Out)
    (hO : ∀ w, Out w → Out' w) : PrimSpec p v Out' :=
  ⟨h.1, fun w hw => hO w (h.2 w hw)⟩

/-- **The primitive of a cited algorithm is correct**: on the encoding of an instance `x`, if
no other instance has the same encoding, every result is a correct output for `x`. -/
theorem Prim.ofHyp_spec {α : Type} {enc : α → Val} {Correct : α → Val → Prop}
    (h : ∃ prog, PolyTimeAt (GI.Cited.Task.ofVal enc Correct) prog) (x : α)
    (hinj : ∀ y, enc y = enc x → y = x) :
    PrimSpec (Prim.ofHyp enc Correct h) (enc x) (Correct x) := by
  refine ⟨⟨x, rfl⟩, fun w hw => ?_⟩
  obtain ⟨y, hy, hc⟩ := hw
  rw [hinj y hy] at hc
  exact hc

theorem Prim.ofHyp_bound {α : Type} {enc : α → Val} {Correct : α → Val → Prop}
    (h : ∃ prog, PolyTimeAt (GI.Cited.Task.ofVal enc Correct) prog) (v : Val) :
    (Prim.ofHyp enc Correct h).bound v =
      h.choose_spec.choose * (v.size + 2) ^ h.choose_spec.choose_spec.choose := rfl

/-- **A call of a primitive with a specification.** The argument evaluates to `v` at cost at
most `ca`; the call returns some `w` with `Out w`, at cost at most `ca + p.bound v + w.wt + 1`. -/
theorem EvalAll.prim_spec {P : Program} {env : List Val} {j : ℕ} {p : Prim} {a : Expr}
    {v : Val} {ca : ℕ} {Out : Val → Prop} (hj : P.prims[j]? = some p) (ha : Det P env a v ca)
    (hs : PrimSpec p v Out) :
    EvalAll P env (.prim j a) (fun w c => Out w ∧ c ≤ ca + p.bound v + w.wt + 1) :=
  EvalAll.prim hj ha fun v' ca' h => by
    obtain ⟨rfl, hca⟩ := h
    exact ⟨hs.1, fun w hw => ⟨hs.2 w hw, by omega⟩⟩

/-- **A call of a primitive whose results have bounded weight.** If every result `w` with
`Out w` weighs at most `W`, the cost of the call is at most `ca + p.bound v + W + 1`, a bound
that does not depend on which result comes back. The tasks bound the size of their outputs, so
every primitive of `Workspace.Lang.Prims` has such a `W`, a polynomial in the degree. -/
theorem EvalAll.prim_spec_le {P : Program} {env : List Val} {j : ℕ} {p : Prim} {a : Expr}
    {v : Val} {ca W : ℕ} {Out : Val → Prop} (hj : P.prims[j]? = some p) (ha : Det P env a v ca)
    (hs : PrimSpec p v Out) (hW : ∀ w, Out w → w.wt ≤ W) :
    EvalAll P env (.prim j a) (fun w c => Out w ∧ c ≤ ca + p.bound v + W + 1) :=
  (EvalAll.prim_spec hj ha hs).mono fun w c h => ⟨h.1, by have := hW w h.1; omega⟩

/-- A function whose body is a call of primitive `j` on its argument. -/
def primF (j : ℕ) : Expr := .prim j (.var 0)

/-- **A function that calls a primitive.** -/
theorem FunAll.prim_spec {P : Program} {f j : ℕ} {p : Prim} (hf : P.funs[f]? = some (primF j))
    (hj : P.prims[j]? = some p) {v : Val} {Out : Val → Prop} (hs : PrimSpec p v Out) :
    FunAll P f v (fun w c => Out w ∧ c ≤ p.bound v + v.wt + w.wt + 2) :=
  FunAll.intro hf ((EvalAll.prim_spec hj (Det.var' (env := [v]) (i := 0) rfl) hs).mono
    fun _ _ h => ⟨h.1, by omega⟩)

/-- A call of a primitive whose result is determined. -/
theorem Det.prim_spec {P : Program} {env : List Val} {j : ℕ} {p : Prim} {a : Expr}
    {v w : Val} {ca : ℕ} (hj : P.prims[j]? = some p) (ha : Det P env a v ca)
    (hs : PrimSpec p v (· = w)) : Det P env (.prim j a) w (ca + p.bound v + w.wt + 1) :=
  Det.prim hj ha hs.1 hs.2

/-! ### Primitives at known indices -/

/-- The primitives `ps` sit in `P` at indices `b, b + 1, …`. -/
def Program.PrimsAt (P : Program) (b : ℕ) (ps : List Prim) : Prop :=
  ∀ j (h : j < ps.length), P.prims[b + j]? = some ps[j]

theorem Program.primsAt_append (fs : List Expr) (A ps B : List Prim) :
    (Program.mk fs (A ++ ps ++ B)).PrimsAt A.length ps := by
  intro j h
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left h, List.getElem?_eq_getElem h]

theorem Program.PrimsAt.get {P : Program} {b : ℕ} {ps : List Prim} (h : P.PrimsAt b ps) {j : ℕ}
    (hj : j < ps.length) : P.prims[b + j]? = some ps[j] := h j hj

theorem Program.PrimsAt.left {P : Program} {b : ℕ} {A B : List Prim} (h : P.PrimsAt b (A ++ B)) :
    P.PrimsAt b A := fun j hj => by
  have := h j (by simp; omega)
  rwa [List.getElem_append_left hj] at this

theorem Program.PrimsAt.right {P : Program} {b : ℕ} {A B : List Prim} (h : P.PrimsAt b (A ++ B)) :
    P.PrimsAt (b + A.length) B := fun j hj => by
  have := h (A.length + j) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.add_assoc] using this

theorem Program.PrimsAt.single {P : Program} {b : ℕ} {p : Prim} (h : P.PrimsAt b [p]) :
    P.prims[b]? = some p := by simpa using h 0 (by simp)

theorem Program.PrimsAt.of_sub {P P' : Program} (hs : P.Sub P') {b : ℕ} {ps : List Prim}
    (h : P.PrimsAt b ps) : P'.PrimsAt b ps := fun j hj => hs.prims_eq (h j hj)

theorem Program.HasAt.of_sub {P P' : Program} (hs : P.Sub P') {b : ℕ} {fs : List Expr}
    (h : P.HasAt b fs) : P'.HasAt b fs := fun j hj => hs.funs_eq (h j hj)

end GI.Lang
