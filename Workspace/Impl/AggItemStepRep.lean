module

public import Workspace.Impl.AggItemStepWt
public import Workspace.Impl.AggCertLoop

@[expose] public section

/-!
# The walk through the items, and the relation of the step function

The script of the items of a round is `Ag.itemsScript`: the item scripts of the branch tuples in
the order `Ag.tuples`, then the concatenation of their results. The step function of the items
walks through it one branch at a time. This file names the remaining script at each point
(`itSW`), and the relation `itSRep` between the program state and the candidate scripts.

* `itSW Ag rs bs`: the item scripts of the tuples `bs`, after the branches with results `rs`.
  `itSW_start`: the whole script; `itSW_nil`: at the end, `done (concat rs)`; `itSW_cons`: the
  first branch, then the others.
* `ItSOut` of a concatenation: `itSOut_append`.

The program state is `[H, u]`, with `H = [tag, K.v, tv, j, acc, x]`:
* `tag = 0`, between branches: `j` branches are finished, `acc` lists their pieces and overcosets,
  `x` is the case's kept value, `u = 0`;
* `tag = 1`, inside the branch of the tuple number `j - 1`: `x` is the case's branch state;
* `tag = 3`, after a call inside that branch: `x` is what the case kept for the answer, and `u`
  is the answer.

`itSRep` says this, with the measure `3 (n - j) + tag'` (`tag' = 1, 2, 3`) of the walk, where
`n = q^(κ+1)` is the number of branches.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)

variable {Ω C : Type} {k : ℕ}

/-! ### The walk -/

section Walk

variable {S : State Ω C} {L : GiantLabels S}

/-- **The remaining script of the items**: the item scripts of the tuples `bs`, after branches
with results `rs`. -/
noncomputable def itSW (Ag : Aggregation P₀ S L) (rs : List (Branches Ω))
    (bs : List (Fin (P₀.κ + 1) → Fin L.q)) : Script (Branches Ω) :=
  (Script.seqList (bs.map fun b => (Ag.items b).script)).bind fun l =>
    Script.done (Branches.concat (rs ++ l))

theorem itSW_start (Ag : Aggregation P₀ S L) : Ag.itemsScript = itSW Ag [] Ag.tuples := by
  unfold Aggregation.itemsScript itSW
  rfl

theorem itSW_nil (Ag : Aggregation P₀ S L) (rs : List (Branches Ω)) :
    itSW Ag rs [] = Script.done (Branches.concat rs) := by
  show Script.done (Branches.concat (rs ++ [])) = _
  rw [List.append_nil]

theorem itSW_cons (Ag : Aggregation P₀ S L) (rs : List (Branches Ω))
    (b : Fin (P₀.κ + 1) → Fin L.q) (bs : List (Fin (P₀.κ + 1) → Fin L.q)) :
    itSW Ag rs (b :: bs) = (Ag.items b).script.bind fun r => itSW Ag (rs ++ [r]) bs := by
  show (Script.seqList ((Ag.items b).script :: bs.map fun b => (Ag.items b).script)).bind
    (fun l => Script.done (Branches.concat (rs ++ l))) = _
  rw [scr_seqList_cons]
  refine scr_bind_congr _ fun r => ?_
  unfold itSW
  refine scr_bind_congr _ fun l => ?_
  rw [List.append_assoc, List.singleton_append]

end Walk

/-! ### Concatenated outputs -/

theorem itS_concat_append (rs : List (Branches Ω)) (r : Branches Ω) :
    Branches.concat (rs ++ [r]) =
      ⟨(Branches.concat rs).pieces ++ r.pieces, (Branches.concat rs).overs ++ r.overs⟩ := by
  simp [Branches.concat, List.flatMap_append]

/-- **The outputs of two parts, concatenated.** -/
theorem itSOut_append {S : State Ω C} {e : Ω ≃ Fin k} {L : GiantLabels S}
    {rs : List (Branches Ω)} {r : Branches Ω} {pcs pcs' : List (Perm (Fin k) × Acc k)}
    {os os' : List (LcOver L.q)} (h : ItSOut e L (Branches.concat rs) pcs os)
    (h' : ItSOut e L r pcs' os') :
    ItSOut e L (Branches.concat (rs ++ [r])) (pcs ++ pcs') (os ++ os') := by
  rw [itS_concat_append]
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  refine ⟨List.rel_append h1 h1', by simp [h2, h2'], fun i hi1 hi2 => ?_, fun o ho => ?_⟩
  · by_cases hi : i < pcs.length
    · rw [List.getElem_append_left hi, List.getElem_append_left (by omega)]
      exact h3 i hi (by omega)
    · simp only [List.length_append] at hi1 hi2
      rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      convert h3' (i - pcs.length) (by omega) (by omega) using 3
      rw [h2]
  · rcases List.mem_append.1 ho with ho | ho
    · exact h4 o ho
    · exact h4' o ho

theorem itSOut_nil {S : State Ω C} (e : Ω ≃ Fin k) (L : GiantLabels S) :
    ItSOut e L (Branches.concat []) [] [] :=
  ⟨List.Forall₂.nil, rfl, fun i h => absurd h (by simp), fun o h => absurd h (by simp)⟩

/-! ### The program state -/

/-- The value of the branch tuples in the program's order. -/
noncomputable def itSTv (q : ℕ) : Val := .list ((itSTups q).map stTv)

/-- **The head of a program state**: `[tag, G, tv, j, acc, x]`. -/
noncomputable def itSH {q : ℕ} (tag : ℕ) (G : Val) (j : ℕ) (pcs : List (Perm (Fin k) × Acc k))
    (os : List (LcOver q)) (x : Val) : Val :=
  .list [.nat tag, G, itSTv q, .nat j, itSOutV pcs os, x]

/-- **The accumulated lists are small**: their entries weigh at most `B` and there are at most
`j B` of them. -/
def ItSAcc {q : ℕ} (B j : ℕ) (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver q)) : Prop :=
  (∀ v ∈ pcs.map encPiece, v.wt ≤ B) ∧
    (∀ v ∈ os.map (fun o => lcOv (o.1 : Perm (Fin q)) o.2.2), v.wt ≤ B) ∧
    pcs.length ≤ j * B ∧ os.length ≤ j * B

/-- **What the final output stands for**: as in `AsItemsOK`. -/
def ItSFin {S : State Ω C} (e : Ω ≃ Fin k) (L : GiantLabels S) (a : Branches Ω) (out : Val) :
    Prop :=
  ∃ (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver L.q)),
    out = itSOutV pcs os ∧ ItSOut e L a pcs os

section Rep

variable {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- **The relation of the step function** at the context `K`, for the case relations `R` and the
bound `B` of the case: the program state `st` of measure `m` stands for the candidate scripts
`Ss`, with at most `f` more calls. -/
def itSRep (R : ItSCaseRel) (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (L : SuppliedLabels S)
    (K : ItSCtx k S L) (B : ℕ) (m : ℕ) (st : Val) (Ss : Set (Script (Branches Ω))) (f : ℕ) :
    Prop :=
  (∃ (j : ℕ) (rs : List (Branches Ω)) (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver L.q))
      (w : Val) (D : Set (Aggregation P₀ S L.toGiantLabels)),
    st = .list [itSH 0 K.v j pcs os w, .nat 0] ∧ j ≤ (itSTups L.q).length ∧
    R.Kc e c S L K w D ∧ D ⊆ itSBase K ∧
    Ss = (fun Ag => itSW Ag rs ((itSTups L.q).drop j)) '' D ∧
    ItSOut e L.toGiantLabels (Branches.concat rs) pcs os ∧ ItSAcc B j pcs os ∧
    ((itSTups L.q).length - j) * B ≤ f ∧ m = 3 * ((itSTups L.q).length - j) + 1) ∨
  (∃ (j : ℕ) (b : Fin (P₀.κ + 1) → Fin L.q) (rs : List (Branches Ω))
      (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver L.q)) (bst : Val)
      (D : Set (Aggregation P₀ S L.toGiantLabels))
      (sb : Aggregation P₀ S L.toGiantLabels → Script (Branches Ω)) (fb : ℕ),
    st = .list [itSH 1 K.v (j + 1) pcs os bst, .nat 0] ∧ (itSTups L.q)[j]? = some b ∧
    R.Rb e c S L K b bst D sb fb ∧ D ⊆ itSBase K ∧
    Ss = (fun Ag => (sb Ag).bind fun r => itSW Ag (rs ++ [r]) ((itSTups L.q).drop (j + 1))) '' D ∧
    ItSOut e L.toGiantLabels (Branches.concat rs) pcs os ∧ ItSAcc B j pcs os ∧
    fb + ((itSTups L.q).length - (j + 1)) * B ≤ f ∧
    m = 3 * ((itSTups L.q).length - (j + 1)) + 2) ∨
  (∃ (j : ℕ) (b : Fin (P₀.κ + 1) → Fin L.q) (rs : List (Branches Ω))
      (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver L.q)) (kst u : Val)
      (D : Set (Aggregation P₀ S L.toGiantLabels))
      (sb : Aggregation P₀ S L.toGiantLabels → Script (Branches Ω)) (fb : ℕ),
    st = .list [itSH 3 K.v (j + 1) pcs os kst, u] ∧ (itSTups L.q)[j]? = some b ∧
    R.Rb e c S L K b (.list [kst, u]) D sb fb ∧ D ⊆ itSBase K ∧
    Ss = (fun Ag => (sb Ag).bind fun r => itSW Ag (rs ++ [r]) ((itSTups L.q).drop (j + 1))) '' D ∧
    ItSOut e L.toGiantLabels (Branches.concat rs) pcs os ∧ ItSAcc B j pcs os ∧
    fb + ((itSTups L.q).length - (j + 1)) * B ≤ f ∧
    m = 3 * ((itSTups L.q).length - (j + 1)) + 3)

end Rep

end GI.Impl
