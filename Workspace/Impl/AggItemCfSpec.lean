import Workspace.Impl.AggItemStepSpec
import Workspace.Impl.AggRectSpec

/-!
# Cases 2b and 3: the contracts of the two stages

Cases 2b and 3 of the aggregation (Section A.3) end with an object read off the canonical
structures `X` (source string, source tuple `src`) and `Y` (target string, branch tuple `b`):
`outPair hK X Y` (`Workspace/Algorithm/AuxOut.lean`). The item of the branch is then
`cfgOutItem O ch oX oY` (`Workspace/Algorithm/AuxCases.lean`): the overcoset of a colored
partition, the configuration query of Lemma A.12, or the first-rectangle item of Lemma 5.1.

The programs of these cases have two stages, and this file fixes their contracts.

1. **The object stage** (`ItCfObjSpec`): from the data of the structures as the items phase holds
   them (the group `X.grp` by generators, the refined tuple colors `X.col`, the tuple `X.tup`) it
   computes
   * the orbital coloring `orbColOut H t` of Case 2b, the input of the binary joint refinement
     (one `KaryRefinement 2` call per branch, made by the case program, not by this stage);
   * from the refined binary coloring, the object `orbitalOut R H t` of Case 2b;
   * the object `designOut col t` of Case 3.
   The objects are given by their values `itCfOutV` (below).
2. **The item stage** (`ItCfItemSpec`): from the values of the two objects and the round data
   `K.v`, the item script of `cfgOutItem (RectOracle.ofReps rep) soj oX oY`, one call at a time,
   as the branch step of a case does (`ItSBrPost`). Its own choices are the first-rectangle
   choices `soj` and the rectangle representations `rep`, so it narrows a set of such pairs
   (`ItCfCh`). The certificate search (`RcCertSpec`) and the representation program
   (`RcRepSpec`) are its inputs.

The case program (`AggItemCfCase.lean`) composes the two stages with the binary refinement call.

## The value of an object

* `none`: `[0]`;
* a colored partition `z`: `[1, rows, cols]`, with `rows` the indicator lists of the blocks
  `z.blk a` (by `a`) and `cols = encFun z.col`;
* a pair configuration `X` with source vertex `x₀`: `[2, rcCertIn X x₀]`, that is
  `[2, [col table, X.j, x₀]]`, the input of the certificate search (`RcCertSpec`).

The value fixes the object (`itCfOutV_injective`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)

variable {Ω C : Type} {k q : ℕ}

/-! ### The value of an object -/

/-- The indicator lists of the blocks of a colored partition, by point. -/
def itCfBlkV (z : ColPart (Fin q)) : Val :=
  .list ((List.finRange q).map fun a => encFun fun b => if b ∈ z.blk a then 1 else 0)

/-- **The value of an object** of Cases 2b and 3. -/
def itCfOutV : CfgOut q → Val
  | .none => .list [.nat 0]
  | .part z => .list [.nat 1, itCfBlkV z, encFun z.col]
  | .pair X x₀ => .list [.nat 2, rcCertIn X x₀]

theorem itCf_map_finRange {α : Type} {f g : Fin q → α}
    (h : (List.finRange q).map f = (List.finRange q).map g) : f = g :=
  funext fun a => List.map_inj_left.1 h a (List.mem_finRange a)

theorem itCfBlkV_blk {z z' : ColPart (Fin q)} (h : itCfBlkV z = itCfBlkV z') :
    z.blk = z'.blk := by
  simp only [itCfBlkV, Val.list.injEq] at h
  funext a
  have h2 := encFun_injective (congrFun (itCf_map_finRange h) a)
  ext b
  have := congrFun h2 b
  by_cases h3 : b ∈ z.blk a <;> by_cases h4 : b ∈ z'.blk a <;> simp_all

/-- **The value fixes the object.** -/
theorem itCfOutV_injective : Function.Injective (itCfOutV (q := q)) := by
  intro o o' h
  cases o with
  | none => cases o' <;> simp_all [itCfOutV]
  | part z =>
    cases o' with
    | none => simp [itCfOutV] at h
    | pair X x₀ => simp [itCfOutV] at h
    | part z' =>
      simp only [itCfOutV, Val.list.injEq, List.cons.injEq, and_true, true_and] at h
      rw [ColPart.ext (itCfBlkV_blk h.1) (encFun_injective h.2)]
  | pair X x₀ =>
    cases o' with
    | none => simp [itCfOutV] at h
    | part z' => simp [itCfOutV] at h
    | pair X' x₀' =>
      simp only [itCfOutV, rcCertIn, rcColVal, Val.list.injEq, List.cons.injEq, and_true,
        true_and, Val.nat.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hcol : X.col = X'.col := by
        funext a
        exact encFun_injective (congrFun (itCf_map_finRange h1) a)
      have hX : X = X' := PairCfg.ext hcol h2
      have hx : x₀ = x₀' := Fin.ext h3
      rw [hX, hx]

/-! ### The object stage -/

/-- The bound shape of a stage: `C (M + 1)^D` of the input weight `M`. -/
def itCfB (C D M : ℕ) : ℕ := C * (M + 1) ^ D

/-- **The input of the orbital coloring**: `[q, H, t]`, the group by generators. -/
def itCfColIn (hs : List (Perm (Fin q))) {ℓ : ℕ} (t : Fin ℓ → Fin q) : Val :=
  .list [.nat q, encGroup hs, stTv t]

/-- **The input of the object of Case 2b**: `[q, H, t, R c]`, with `R c` the refined binary
coloring of the orbital coloring `c = orbColOut H t`. -/
def itCfOrbIn (hs : List (Perm (Fin q))) {ℓ : ℕ} (t : Fin ℓ → Fin q)
    (r : (Fin 2 → Fin q) → ℕ) : Val :=
  .list [.nat q, encGroup hs, stTv t, encKColoring r]

/-- **The input of the object of Case 3**: `[q, κ, col, t]`. -/
def itCfDesIn {κ : ℕ} (col : (Fin κ → Fin q) → ℕ) {ℓ : ℕ} (t : Fin ℓ → Fin q) : Val :=
  .list [.nat q, .nat κ, encKColoring col, stTv t]

/-- **The contract of the object stage**, three programs with the bound `itCfB Co Do`:
* `fcol` on `[q, H, t]` returns the orbital coloring `orbColOut H t` of Case 2b (the
  maximal degree of transitivity of `H` on its dominant orbit, the anchors, the orbital of the
  next pair, and the binary coloring of `C = Φ \ anchors` and of the orbital);
* `forb` on `[q, H, t, R (orbColOut H t)]` returns the object `orbitalOut R H t` of Case 2b, for
  every refiner `R` (the program sees `R` only through this coloring);
* `fdes` on `[q, κ, col, t]` returns the object `designOut col t` of Case 3.
Each costs at most `itCfB Co Do` of its input weight. -/
structure ItCfObjSpec (Pg : Program) (fcol forb fdes Co Do : ℕ) : Prop where
  col : ∀ {q ℓ : ℕ} (hs : List (Perm (Fin q))) (t : Fin ℓ → Fin q),
    FunAll Pg fcol (itCfColIn hs t) fun w cost =>
      w = encKColoring (orbColOut (gens hs) t) ∧ cost ≤ itCfB Co Do (itCfColIn hs t).wt
  orb : ∀ {q ℓ : ℕ} (hs : List (Perm (Fin q))) (t : Fin ℓ → Fin q) (R : Refiner2 q),
    FunAll Pg forb (itCfOrbIn hs t (R (orbColOut (gens hs) t))) fun w cost =>
      w = itCfOutV (orbitalOut R (gens hs) t) ∧
        cost ≤ itCfB Co Do (itCfOrbIn hs t (R (orbColOut (gens hs) t))).wt
  des : ∀ {q κ ℓ : ℕ} (col : (Fin κ → Fin q) → ℕ) (t : Fin ℓ → Fin q),
    FunAll Pg fdes (itCfDesIn col t) fun w cost =>
      w = itCfOutV (designOut col t) ∧ cost ≤ itCfB Co Do (itCfDesIn col t).wt

/-! ### The item stage -/

/-- **The choices of the item stage**: the first-rectangle choices and the rectangle
representations of a round. -/
abbrev ItCfCh {Ω C : Type} (S : State Ω C) (L : GiantLabels S) : Type :=
  SojChoice × (∀ W R : Finset (Fin L.q), RectConds P₀ S L W R → RectRep P₀ S L W R)

/-- **The item script of the configuration branch** for the choices `ch` (the round's
`cfg` item with `soj := ch.1`, `rep := ch.2`). The finiteness of `Ω` comes from `e`. -/
noncomputable def itCfSb (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (oX oY : CfgOut L.q) (ch : ItCfCh S L) : Script (Branches Ω) :=
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  (cfgOutItem (RectOracle.ofReps ch.2) ch.1 oX oY).script

/-- All colors of an object are at most `B`. -/
def itCfColsLe : CfgOut q → ℕ → Prop
  | .none, _ => True
  | .part z, B => ∀ a, z.col a ≤ B
  | .pair X _, B => (∀ a b, X.col a b ≤ B) ∧ X.j ≤ B

/-- **The objects of a branch**: some round of the base set has these objects in the branch
of `b`, and their colors are below `2 q^κ` (as the object stage provides: the cached binary
colors are below `2q²` in Case 2b, the colors of `K.d`, `K.d'` below `2q^κ` in Case 3). -/
def ItCfObjOf {S : State Ω C} {L : SuppliedLabels S} (K : ItSCtx k S L)
    (b : Fin (P₀.κ + 1) → Fin L.q) (oX oY : CfgOut L.q) : Prop :=
  ∃ Ag ∈ itSBase K, Ag.out (Ag.strX Ag.src) (Ag.strY b) = (oX, oY) ∧
    itCfColsLe oX (2 * L.q ^ P₀.κ) ∧ itCfColsLe oY (2 * L.q ^ P₀.κ)

/-- **The relations of the item stage**: `Ki` between branches (the item's kept value stands
for a set of choices), `Ri` inside the branch of `b` with objects `oX`, `oY` (the item state
stands for a set of choices `E`, with continuations `sb ch` and at most `f` more calls). -/
structure ItCfIRel : Type 1 where
  Ki : ∀ {Ω C : Type} {k : ℕ}, (Ω ≃ Fin k) → (C → ℕ) → (S : State Ω C) →
    (L : SuppliedLabels S) → ItSCtx k S L → Val → Set (ItCfCh S L.toGiantLabels) → Prop
  Ri : ∀ {Ω C : Type} {k : ℕ}, (Ω ≃ Fin k) → (C → ℕ) → (S : State Ω C) →
    (L : SuppliedLabels S) → ItSCtx k S L → (Fin (P₀.κ + 1) → Fin L.q) → CfgOut L.q →
    CfgOut L.q → Val → Set (ItCfCh S L.toGiantLabels) →
    (ItCfCh S L.toGiantLabels → Script (Branches Ω)) → ℕ → Prop

/-- **What one item step returns**, as `ItSBrPost` for the choice sets of the item stage:
* `[0, [⟨pieces⟩, ⟨overcosets⟩, wI']]`: the script of every choice of `E' ⊆ E` is finished with
  the result `r`, the lists stand for `r`, and `wI'` is a kept value of `E'`;
* `[1, code, arg, kst]`: the choices of a nonempty `E' ⊆ E` ask the same call, and `[kst, u]`
  stands for `E'` and their continuations, for every canonical answer `u`. -/
def ItCfIPost (R : ItCfIRel) (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
    (L : SuppliedLabels S) (K : ItSCtx k S L) (b : Fin (P₀.κ + 1) → Fin L.q)
    (oX oY : CfgOut L.q) (E : Set (ItCfCh S L.toGiantLabels))
    (sb : ItCfCh S L.toGiantLabels → Script (Branches Ω)) (f B : ℕ) (w : Val) : Prop :=
  (∃ (r : Branches Ω) (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver L.q)) (wI : Val)
      (E' : Set (ItCfCh S L.toGiantLabels)),
    w = .list [.nat 0, .list [.list (pcs.map encPiece),
      .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2), wI]] ∧
    E' ⊆ E ∧ (∀ ch ∈ E', sb ch = .done r) ∧ R.Ki e c S L K wI E' ∧
    ItSOut e L.toGiantLabels r pcs os ∧ (itSOutV pcs os).wt ≤ B) ∨
  (0 < f ∧ ∃ (m : Mode) (Ω' C' : Type) (T : State Ω' C') (k' : ℕ) (e' : Ω' ≃ Fin k')
    (c' : C' → ℕ) (arg kst : Val) (E' : Set (ItCfCh S L.toGiantLabels))
    (kk : ItCfCh S L.toGiantLabels → Set (Perm Ω') → Script (Branches Ω)),
    E' ⊆ E ∧ E'.Nonempty ∧ Function.Injective c' ∧ (m = .solve ∨ m = .cont) ∧
    w = .list [.nat 1, .nat (modeCode m), arg, kst] ∧ Canon e' c' arg T ∧ Good P₀ m T ∧
    MLt (measure P₀ m T) (measure P₀ .giant S) ∧ (∀ ch ∈ E', sb ch = .ask m T (kk ch)) ∧
    ∀ u, AnsC e' u T.answer → R.Ri e c S L K b oX oY (.list [kst, u]) E'
      (fun ch => kk ch T.answer) (f - 1))

variable (I : Iface) (Pg : Program)

/-- **What the item stage must do at a context `K`**, with init at `fi`, start at `fs`, step at
`fk` and the bound `B` (on cost, weights and calls per branch):
* `init`: on `K.v` the init program returns a kept value for some set of choices;
* `ne`, `wtK`: a kept value stands for a nonempty set and weighs at most `B`;
* `start`: on `[K.v, stTv b, ⟨oX⟩, ⟨oY⟩, wI]`, for the objects of the branch of `b`, the start
  program returns what `ItCfIPost` asks for the scripts `itCfSb e oX oY`, with at most `B` calls;
* `wtR`: an item state weighs at most `B`;
* `step`: on an item state the step program returns what `ItCfIPost` asks. -/
structure ItCfItemAt (R : ItCfIRel) (fi fs fk : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
    (L : SuppliedLabels S) (K : ItSCtx k S L) (B : ℕ) : Prop where
  init : FunAll Pg fi K.v (fun w cost => ∃ E, R.Ki e c S L K w E ∧ cost ≤ B)
  ne : ∀ w E, R.Ki e c S L K w E → E.Nonempty
  wtK : ∀ w E, R.Ki e c S L K w E → w.wt ≤ B
  start : ∀ b oX oY w E, ItCfObjOf K b oX oY → R.Ki e c S L K w E →
    FunAll Pg fs (.list [K.v, stTv b, itCfOutV oX, itCfOutV oY, w]) (fun w' cost =>
      cost ≤ B ∧ ItCfIPost R e c S L K b oX oY E (itCfSb e oX oY) B B w')
  wtR : ∀ b oX oY ist E sb f, R.Ri e c S L K b oX oY ist E sb f → ist.wt ≤ B
  step : ∀ b oX oY ist E sb f, R.Ri e c S L K b oX oY ist E sb f →
    FunAll Pg fk ist (fun w cost => cost ≤ B ∧ ItCfIPost R e c S L K b oX oY E sb f B w)

/-- **The contract of the item stage** at `fi` (init), `fs` (start) and `fk` (step), with the
bound `Xt` of the input weight: there are relations such that at every context of a call in
Case 2b or 3, the programs meet `ItCfItemAt` with the bound `Xt (inW .giant S)`. -/
def ItCfItemSpec (F : Funs) (fi fs fk : ℕ) (Xt : ℕ → ℕ) : Prop :=
  ∃ R : ItCfIRel, ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
    (sv lv : Val) (L : SuppliedLabels S), AsCall I Pg F e c S sv lv L →
    ∀ K : ItSCtx k S L, K.OK e c → (K.case = .twoB ∨ K.case = .three) →
      ItCfItemAt Pg R fi fs fk e c S L K (Xt (I.inW .giant S))

end GI.Impl
