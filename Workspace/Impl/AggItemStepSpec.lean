import Workspace.Impl.AggItemStr
import Workspace.Impl.AggItemUpd
import Workspace.Impl.AggItemRun

/-!
# The item programs of the three cases: their contracts

The items of a round run in three parts:

1. the structure step `it_str_spec`: from the start state `st` it computes `v = [st, [d, d'],
   code, src]`, which fixes the joint refinement `J` at the class colorings, the case and the
   source tuple;
2. the start of the case: an *init* program of the case computes, once per round, a value
   `cache₀` that the case keeps from branch to branch (for example `τ₀` and `t` of Case 2a, or
   the recorded choices of Cases 2b and 3);
3. for each branch tuple `b`, in the order `stTs q (κ + 1)`, the case's *branch step* runs the
   item script `(Ag.items b).script`, one call at a time, like the step function of a script
   runner (`Iface.StepPostC`).

This file fixes what the step function of `itemsScript` needs from parts 2 and 3. A case program
states its own invariants, as two relations (`ItSCaseRel`):
* `Kc K w D`: between branches, the kept value `w` stands for the nonempty set `D` of candidate
  rounds (rounds that agree with all the choices made so far);
* `Rb K b bst D sb f`: inside the branch of `b`, the branch state `bst` stands for the rounds `D`,
  where `sb Ag` is what is left of the item script of `Ag` at `b`, and at most `f` more calls are
  made in this branch.

`ItSCaseAt` lists what these relations must satisfy; `ItSCaseOK` is the contract of a case's
programs at their indices `f0` (init) and `fb` (branch step), with a bound `Xc` on cost, weight and
calls, as a function of the input weight `W₀ = inW .giant S`.

The context `K : ItSCtx k S L` collects the data fixed before the branches: the candidate set and
the round `Ag₀` of the hand-over, the parts of the start state, the refined colors `d`, `d'`, and
the joint refinement `J`. Its value `K.v` is the output of the structure step. `itSBase K` is the
set of rounds that agree with the structure step: the branch order, the class numbers, the
`κ`-ary values of the joint refinement and the source tuple. Every round `itUpd (itRound Ag₀ J')
…` with `J'` equal to `J` at arity `κ` lies in it (`itSBase_upd`), so a case may choose `halv`,
`soj`, `rep` and the binary values of `hK` freely.

The hand-over `ItHand` does not bound the lengths of the lists of graph pairs, so it does not
bound the weight of the start state by the input weight. `ItHandB` adds these bounds (they hold
for the output of the comparison phase, `itS_asCompOK_of_runB`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)

variable {Ω C : Type} {k : ℕ}

/-! ### The hand-over with length bounds -/

/-- **The hand-over of the items with length bounds**: `ItHand`, and the three lists of graph
pairs of the start state have at most `(k + q)²` entries. -/
def ItHandB (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (L : SuppliedLabels S)
    (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (st : Val) : Prop :=
  Cs ⊆ asRounds L ∧ ∃ Ag₀ ∈ Cs,
    (∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag.compScript = Ag₀.compScript →
      Ag ∈ Cs) ∧
    ∃ (sv : Val) (ps fx fy : List (Perm (Fin k) × Perm (Fin L.q))) (O : TestTupleOrder L.q P₀.κ),
      st = itSt sv k L.q ps fx fy O.tuples (itCr Ag₀.fin S Ag₀.πd P₀.κ) ∧
      Canon e c sv S ∧ PairGens e L.toGiantLabels S.G ps ∧
      PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.x) fx ∧
      PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.y) fy ∧
      ps.length ≤ (k + L.q) ^ 2 ∧ fx.length ≤ (k + L.q) ^ 2 ∧ fy.length ≤ (k + L.q) ^ 2

theorem ItHandB.itHand {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S}
    {Cs : Set (Aggregation P₀ S L.toGiantLabels)} {st : Val} (h : ItHandB e c S L Cs st) :
    ItHand e c S L Cs st := by
  obtain ⟨hsub, Ag₀, h0, hcl, sv, ps, fx, fy, O, hst, hcan, hps, hfx, hfy, -⟩ := h
  exact ⟨hsub, Ag₀, h0, hcl, sv, ps, fx, fy, O, hst, hcan, hps, hfx, hfy⟩

/-! ### The context of the branches -/

/-- **The data fixed before the branches.** -/
structure ItSCtx (k : ℕ) {Ω C : Type} (S : State Ω C) (L : SuppliedLabels S) where
  /-- The candidate set of the hand-over. -/
  Cs : Set (Aggregation P₀ S L.toGiantLabels)
  /-- The round of the hand-over. -/
  Ag₀ : Aggregation P₀ S L.toGiantLabels
  /-- The canonical value of the state. -/
  sv : Val
  /-- Graph pairs of `G`, of the lift of `F_x` and of the lift of `F_y`. -/
  ps : List (Perm (Fin k) × Perm (Fin L.q))
  fx : List (Perm (Fin k) × Perm (Fin L.q))
  fy : List (Perm (Fin k) × Perm (Fin L.q))
  /-- The order of the test tuples of the comparison phase. -/
  O : TestTupleOrder L.q P₀.κ
  /-- The refined colors of the two strings. -/
  d : (Fin P₀.κ → Fin L.q) → ℕ
  d' : (Fin P₀.κ → Fin L.q) → ℕ
  /-- The joint refinement that takes the value `(d, d')` at the class colorings. -/
  J : JointFn

namespace ItSCtx

variable {S : State Ω C} {L : SuppliedLabels S} (K : ItSCtx k S L)

/-- The start state of the items. -/
noncomputable def st : Val :=
  itSt K.sv k L.q K.ps K.fx K.fy K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)

/-- The case of the round. -/
noncomputable def case : AggCase := aggCase (itX0 K.Ag₀ K.J).grp

/-- **The output of the structure step**: `[st, [d, d'], code, src]`. -/
noncomputable def v : Val :=
  .list [K.st, .list [encKColoring K.d, encKColoring K.d'], .nat (AggCase.code K.case),
    natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))]

/-- **The facts of the context.** -/
structure OK (e : Ω ≃ Fin k) (c : C → ℕ) : Prop where
  sub : K.Cs ⊆ asRounds L
  mem : K.Ag₀ ∈ K.Cs
  cl : ∀ Ag ∈ asRounds L, Ag.certScript = K.Ag₀.certScript →
    Ag.compScript = K.Ag₀.compScript → Ag ∈ K.Cs
  can : Canon e c K.sv S
  hps : PairGens e L.toGiantLabels S.G K.ps
  hfx : PairGens e L.toGiantLabels (itCertLift K.Ag₀.fin S K.Ag₀.πd P₀.κ S.x) K.fx
  hfy : PairGens e L.toGiantLabels (itCertLift K.Ag₀.fin S K.Ag₀.πd P₀.κ S.y) K.fy
  lps : K.ps.length ≤ (k + L.q) ^ 2
  lfx : K.fx.length ≤ (k + L.q) ^ 2
  lfy : K.fy.length ≤ (k + L.q) ^ 2
  dlt : ∀ x, K.d x < 2 * L.q ^ P₀.κ
  dlt' : ∀ x, K.d' x < 2 * L.q ^ P₀.κ
  hJ : haveI := K.Ag₀.fin
    letI : Fintype S.dom := Fintype.ofFinite _
    letI : DecidableEq S.dom := Classical.decEq _
    ∃ h : JointOK (tcol S K.Ag₀.πd P₀.κ (itNum K.Ag₀) (dstr S S.x))
        (tcol S K.Ag₀.πd P₀.κ (itNum K.Ag₀) (dstr S S.y)) K.d K.d',
      K.J = stSetJ K.Ag₀.hK L.q P₀.κ _ _ K.d K.d' h

end ItSCtx

/-- The branch tuples, in the program's order. -/
noncomputable def itSTups (q : ℕ) : List (Fin (P₀.κ + 1) → Fin q) := stTs q (P₀.κ + 1)

theorem itSTups_nodup (q : ℕ) : (itSTups q).Nodup := by
  unfold itSTups stTs
  exact (List.nodup_finRange _).map finFunctionFinEquiv.symm.injective

theorem mem_itSTups {q : ℕ} (b : Fin (P₀.κ + 1) → Fin q) : b ∈ itSTups q := mem_stTs b

/-- **The rounds that agree with the structure step**: candidates of the hand-over, with the
branch order `itSTups q`, the class numbers `itNum Ag₀`, the `κ`-ary values of `J` and the source
tuple `itSrc Ag₀ J`. -/
def itSBase {S : State Ω C} {L : SuppliedLabels S} (K : ItSCtx k S L) :
    Set (Aggregation P₀ S L.toGiantLabels) :=
  {Ag | Ag ∈ K.Cs ∧ Ag.tuples = itSTups L.q ∧ Ag.num = itNum K.Ag₀ ∧
    Ag.hK L.q P₀.κ = K.J L.q P₀.κ ∧ Ag.src = itSrc K.Ag₀ K.J}

section Base

variable {S : State Ω C} {L : SuppliedLabels S}

/-- The structure of `x` depends on the joint refinement only through its `κ`-ary values. -/
theorem itX0_congr (Ag : Aggregation P₀ S L.toGiantLabels) {J J' : JointFn}
    (h : J' L.q P₀.κ = J L.q P₀.κ) : itX0 Ag J' = itX0 Ag J := by
  unfold itX0 structX canon rcol
  rw [h]

/-- The source tuple depends on the joint refinement only through its `κ`-ary values. -/
theorem itSrc_congr (Ag : Aggregation P₀ S L.toGiantLabels) {J J' : JointFn}
    (h : J' L.q P₀.κ = J L.q P₀.κ) : itSrc Ag J' = itSrc Ag J := by
  rw [itSrc_eq_of, itSrc_eq_of, itX0_congr Ag h]

/-- **The free rounds lie in the base set**: `Ag₀` with a joint refinement that agrees with `J` at
arity `κ`, the program's branch order, and any halving choices, first-rectangle choices and
rectangle representations. -/
theorem itSBase_upd {e : Ω ≃ Fin k} {c : C → ℕ} {K : ItSCtx k S L} (hK : K.OK e c)
    {J' : JointFn} (hJ' : J' L.q P₀.κ = K.J L.q P₀.κ) (hv : HalvingChoice S L.toGiantLabels)
    (sj : SojChoice)
    (rp : ∀ W R : Finset (Fin L.q), RectConds P₀ S L.toGiantLabels W R →
      RectRep P₀ S L.toGiantLabels W R) :
    itUpd (itRound K.Ag₀ J') (itSTups L.q) (itSTups_nodup L.q) mem_itSTups hv sj rp ∈ itSBase K :=
  ⟨it_upd_mem hK.sub hK.mem hK.cl J' _ _ _ hv sj rp, rfl, rfl, hJ', itSrc_congr K.Ag₀ hJ'⟩

/-- The base set is not empty. -/
theorem itSBase_nonempty {e : Ω ≃ Fin k} {c : C → ℕ} {K : ItSCtx k S L} (hK : K.OK e c) :
    (itSBase K).Nonempty :=
  ⟨_, itSBase_upd hK rfl (HalvingChoice.default S L.toGiantLabels) SojChoice.default
    K.Ag₀.rep⟩

theorem itSBase_sub {K : ItSCtx k S L} : itSBase K ⊆ K.Cs := fun _ h => h.1

end Base

/-! ### The outputs -/

/-- **The program's pieces and overcosets stand for a branch output** `r`: as in `AsItemsOK`. -/
def ItSOut {S : State Ω C} (e : Ω ≃ Fin k) (L : GiantLabels S) (r : Branches Ω)
    (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver L.q)) : Prop :=
  List.Forall₂ (asOvAt L) os r.overs ∧ pcs.length = r.pieces.length ∧
    (∀ i (h1 : i < pcs.length) (h2 : i < r.pieces.length), ceSet pcs[i] = toFin e '' r.pieces[i]) ∧
    ∀ o ∈ os, gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype

/-- The value of pieces and overcosets: `[⟨pieces⟩, ⟨overcosets⟩]`. -/
def itSOutV {q : ℕ} (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver q)) : Val :=
  .list [.list (pcs.map encPiece), .list (os.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2)]

/-! ### The contracts of a case -/

/-- **The relations of a case program**: `Kc` between branches, `Rb` inside a branch. -/
structure ItSCaseRel : Type 1 where
  Kc : ∀ {Ω C : Type} {k : ℕ}, (Ω ≃ Fin k) → (C → ℕ) → (S : State Ω C) →
    (L : SuppliedLabels S) → ItSCtx k S L → Val → Set (Aggregation P₀ S L.toGiantLabels) → Prop
  Rb : ∀ {Ω C : Type} {k : ℕ}, (Ω ≃ Fin k) → (C → ℕ) → (S : State Ω C) →
    (L : SuppliedLabels S) → ItSCtx k S L → (Fin (P₀.κ + 1) → Fin L.q) → Val →
    Set (Aggregation P₀ S L.toGiantLabels) →
    (Aggregation P₀ S L.toGiantLabels → Script (Branches Ω)) → ℕ → Prop

/-- **What one branch step returns** (as `Iface.StepPostC`, for the item script of one branch):
* `[0, [⟨pieces⟩, ⟨overcosets⟩, w']]`: the item script of every round of a subset `D'` is
  finished with the same result `r`, the program's lists stand for `r` (`ItSOut`), and the new
  kept value `w'` stands for `D'`;
* `[1, code, arg, kst]`: the rounds of a nonempty subset `D'` ask the same call (a canonical value
  `arg` of a state `T` that is good and below the round in the measure), and for every canonical
  answer `u` of the exact answer, `[kst, u]` stands for `D'` with their continuations, with one
  call fewer. -/
def ItSBrPost (R : ItSCaseRel) (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (L : SuppliedLabels S)
    (K : ItSCtx k S L) (b : Fin (P₀.κ + 1) → Fin L.q) (D : Set (Aggregation P₀ S L.toGiantLabels))
    (sb : Aggregation P₀ S L.toGiantLabels → Script (Branches Ω)) (f B : ℕ) (w : Val) : Prop :=
  (∃ (r : Branches Ω) (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver L.q)) (w' : Val)
      (D' : Set (Aggregation P₀ S L.toGiantLabels)),
    w = .list [.nat 0, .list [.list (pcs.map encPiece),
      .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2), w']] ∧
    D' ⊆ D ∧ (∀ Ag ∈ D', sb Ag = .done r) ∧ R.Kc e c S L K w' D' ∧
    ItSOut e L.toGiantLabels r pcs os ∧ (itSOutV pcs os).wt ≤ B) ∨
  (0 < f ∧ ∃ (m : Mode) (Ω' C' : Type) (T : State Ω' C') (k' : ℕ) (e' : Ω' ≃ Fin k')
    (c' : C' → ℕ) (arg kst : Val) (D' : Set (Aggregation P₀ S L.toGiantLabels))
    (kk : Aggregation P₀ S L.toGiantLabels → Set (Perm Ω') → Script (Branches Ω)),
    D' ⊆ D ∧ D'.Nonempty ∧ Function.Injective c' ∧ (m = .solve ∨ m = .cont) ∧
    w = .list [.nat 1, .nat (modeCode m), arg, kst] ∧ Canon e' c' arg T ∧ Good P₀ m T ∧
    MLt (measure P₀ m T) (measure P₀ .giant S) ∧ (∀ Ag ∈ D', sb Ag = .ask m T (kk Ag)) ∧
    ∀ u, AnsC e' u T.answer → R.Rb e c S L K b (.list [kst, u]) D' (fun Ag => kk Ag T.answer)
      (f - 1))

variable (I : Iface) (Pg : Program)

/-- **What a case program must do at a context `K`**, with init at `f0`, branch step at `fb`,
and the bound `B` (on cost, weights and calls per branch):
* `init`: on `K.v` the init program returns a kept value for a subset of `itSBase K`;
* `ne`, `wtK`: a kept value stands for a nonempty set and weighs at most `B`;
* `start`: at the start of the branch of `b`, `[K.v, stTv b, w]` stands for the item scripts of
  the rounds of `w`, with at most `B` calls;
* `wtR`: a branch state weighs at most `B`;
* `step`: the branch step returns what `ItSBrPost` asks, at cost at most `B`. -/
structure ItSCaseAt (R : ItSCaseRel) (f0 fb : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
    (L : SuppliedLabels S) (K : ItSCtx k S L) (B : ℕ) : Prop where
  init : FunAll Pg f0 K.v (fun w cost => ∃ D, D ⊆ itSBase K ∧ R.Kc e c S L K w D ∧ cost ≤ B)
  ne : ∀ w D, R.Kc e c S L K w D → D.Nonempty
  wtK : ∀ w D, R.Kc e c S L K w D → w.wt ≤ B
  start : ∀ b w D, R.Kc e c S L K w D →
    R.Rb e c S L K b (.list [K.v, stTv b, w]) D (fun Ag => (Ag.items b).script) B
  wtR : ∀ b bst D sb f, R.Rb e c S L K b bst D sb f → bst.wt ≤ B
  step : ∀ b bst D sb f, R.Rb e c S L K b bst D sb f →
    FunAll Pg fb bst (fun w cost => cost ≤ B ∧ ItSBrPost R e c S L K b D sb f B w)

/-- **The contract of a case program** at `f0` (init) and `fb` (branch step), for the cases
`cs`, with the bound `Xc` of the input weight: there are relations `R` such that at every context
of a call whose case is in `cs`, the programs meet `ItSCaseAt` with the bound
`Xc (inW .giant S)`. -/
def ItSCaseOK (F : Funs) (cs : AggCase → Prop) (f0 fb : ℕ) (Xc : ℕ → ℕ) : Prop :=
  ∃ R : ItSCaseRel, ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
    (sv lv : Val) (L : SuppliedLabels S), AsCall I Pg F e c S sv lv L →
    ∀ K : ItSCtx k S L, K.OK e c → cs K.case →
      ItSCaseAt Pg R f0 fb e c S L K (Xc (I.inW .giant S))

/-- The relations of a case with the call bound relaxed: `Rb` at any `f' ≤ f`. -/
def ItSCaseRel.relax (R : ItSCaseRel) : ItSCaseRel where
  Kc := R.Kc
  Rb e c S L K b bst D sb f := ∃ f' ≤ f, R.Rb e c S L K b bst D sb f'

/-- **A case contract for a larger bound.** -/
theorem ItSCaseOK.mono {F : Funs} {cs : AggCase → Prop} {f0 fb : ℕ} {Xc Xc' : ℕ → ℕ}
    (h : ItSCaseOK I Pg F cs f0 fb Xc) (hX : ∀ W, Xc W ≤ Xc' W) :
    ItSCaseOK I Pg F cs f0 fb Xc' := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R.relax, fun e c S sv lv L hc K hK hcs => ?_⟩
  have h := hR e c S sv lv L hc K hK hcs
  have hB := hX (I.inW .giant S)
  refine ⟨h.init.mono fun w c ⟨D, h1, h2, h3⟩ => ⟨D, h1, h2, h3.trans hB⟩, h.ne,
    fun w D hw => (h.wtK w D hw).trans hB, fun b w D hw => ⟨_, hB, h.start b w D hw⟩,
    fun b bst D sb f ⟨f', _, hb⟩ => (h.wtR b bst D sb f' hb).trans hB,
    fun b bst D sb f ⟨f', hf', hb⟩ => ?_⟩
  refine (h.step b bst D sb f' hb).mono fun w cost ⟨hc, hp⟩ => ⟨hc.trans hB, ?_⟩
  rcases hp with ⟨r, pcs, os, w', D', h1, h2, h3, h4, h5, h6⟩ |
    ⟨hf0, m, Ω', C', T, k', e', c', arg, kst, D', kk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · exact Or.inl ⟨r, pcs, os, w', D', h1, h2, h3, h4, h5, h6.trans hB⟩
  · exact Or.inr ⟨by omega, m, Ω', C', T, k', e', c', arg, kst, D', kk, h1, h2, h3, h4, h5, h6, h7,
      h8, h9, fun u hu => ⟨f' - 1, by omega, h10 u hu⟩⟩

end GI.Impl
