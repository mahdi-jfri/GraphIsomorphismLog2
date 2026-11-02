import Workspace.Impl.AggCertWalk
import Workspace.Impl.AggCacheProg
import Workspace.Impl.AggInc
import Workspace.Impl.AggTup
import Workspace.Impl.AggPTProg

/-!
# The program states of the certificate phase

The step function of the certificate phase keeps its data in one value. This file fixes the
layout of that value and says what it stands for: a position of the walk (`CpPos`,
`AggCertWalk.lean`) and a record of the coset representatives chosen so far.

## Layout

A program state is `[kst, u]`: `u` is the answer of the last window call (or anything, at the
start of a round), and

`kst = [par, Ts, s, res, cache, p0, px, t, ps, os, inner, T, lz, lx, logs]`

* `par`: the parent data, fixed for the whole phase;
* `Ts`: the test sets still to come after the current one, each as `[indT T, label points]`;
* `s`: the string (`0` for `x`, `1` for `y`); `t`: the round;
* `res`: the graph forms of the final groups of the finished test sets (`[x-pairs, y-pairs]`);
* `cache`: the cache of coset representatives (`ckEntV`, `AggCacheProg.lean`);
* `p0`: the graph form of the lift of `P_T` (to restart with `y`); `px`: the final group of `x`;
* `ps`: the graph form of the lift of the current group `A_t`; `os`: the domain points outside
  the current window `W_t`;
* `T` (entry 11): the current test set, as `[indT T, label points]`;
* `inner`: `[]` at the start of a round; inside a round `[reps, gens, gv, dv, inc, a]`: the
  representatives still to come, the generators collected so far (`stageGens`), the group
  value of the lifted kernel, the window indicator, the increment and the representative whose
  answer `u` is;
* `lz` (entry 12): the stage log of the current string: for each finished round `j < t`, the
  graph form of the lift of `A_j` and the domain positions of the increment `V_j`;
* `lx` (entry 13): during the loop of `y`, the complete stage log of `x`;
* `logs` (entry 14): the logs `[T, x-stages, y-stages]` of the finished test sets.

The logs are what the comparison phase reads (`CmHand`, `AggCmpHand.lean`): the stages are
known only through the window calls of this phase.

## What a program state stands for

* `CacheOK'`: the cache stands for a record, and every representative is a position permutation
  of an element of `G` (needed to make the window call).
* `CpRoundInv σ acc T rec`: the data of the start of a round.
* `CpWinInv`: inside a round, after the window call of `a`, with its answer `u`.
* `CpRep par Bw M₀ NT m st Ss f`: the program state `st` stands for the candidate set `Ss` at a
  position of measure `m ≤ f`. This is the relation of `stepOKC_of_move`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)
open scoped Pointwise

/-! ### Values -/

section Values

variable {k q : ℕ}

/-- A graph form: pairs `(a, π a)`. -/
abbrev GPairs (k q : ℕ) := List (Perm (Fin k) × Perm (Fin q))

/-- The value of a graph form. -/
def gpV (ps : GPairs k q) : Val := .list (ps.map pairV)

/-- The value of a test set: its indicator and its label points `k + c`, `c ∈ T`. -/
noncomputable def tsV (k : ℕ) (T : Finset (Fin q)) : Val :=
  .list [indT T, natList (ptsKey (labPts k (tlist T)))]

/-- The value of the result of one test set. -/
def resV (r : GPairs k q × GPairs k q) : Val := .list [gpV r.1, gpV r.2]

/-- One stage of a log: the graph form of the lift of `A_j` and the positions of `V_j`. -/
abbrev CpStgD (k q : ℕ) := GPairs k q × List (Fin (k + q))

/-- The value `[⟨pairs⟩, ⟨positions⟩]` of one stage (the same as `cmStgV`). -/
def cpSgV (d : CpStgD k q) : Val := .list [gpV d.1, encPts d.2]

/-- The value `[tsV T, ⟨x-stages⟩, ⟨y-stages⟩]` of the log of a test set (the same as `cmLogV`). -/
noncomputable def cpLogV (l : Finset (Fin q) × List (CpStgD k q) × List (CpStgD k q)) : Val :=
  .list [tsV k l.1, .list (l.2.1.map cpSgV), .list (l.2.2.map cpSgV)]

/-- **The data of a program state** outside a round. -/
structure CpSt (k q : ℕ) where
  Ts : List (Finset (Fin q))
  s : Bool
  res : List (GPairs k q × GPairs k q)
  cache : List (CacheEntry k q)
  p0 : GPairs k q
  px : GPairs k q
  t : ℕ
  ps : GPairs k q
  osP : List (Fin (k + q))
  /-- The current test set. -/
  T : Finset (Fin q)
  /-- The stage log of the current string. -/
  lz : List (CpStgD k q)
  /-- The stage log of `x` (during the loop of `y`). -/
  lx : List (CpStgD k q)
  /-- The logs of the finished test sets. -/
  logs : List (Finset (Fin q) × List (CpStgD k q) × List (CpStgD k q))

/-- The value `kst` of a program state. -/
noncomputable def CpSt.val (par : Val) (σ : CpSt k q) (inner : Val) : Val :=
  .list [par, .list (σ.Ts.map (tsV k)), boolVal σ.s, .list (σ.res.map resV),
    .list (σ.cache.map ckEntV), gpV σ.p0, gpV σ.px, .nat σ.t, gpV σ.ps, encPts σ.osP, inner,
    tsV k σ.T, .list (σ.lz.map cpSgV), .list (σ.lx.map cpSgV), .list (σ.logs.map cpLogV)]

/-- The value `inner` inside a round. -/
def cpInnerV (as gs hs : List (Perm (Fin k))) (dv : Val) (incP : List (Fin (k + q)))
    (a : Perm (Fin k)) : Val :=
  .list [.list (as.map encPerm), .list (gs.map encPerm), encGroup hs, dv, encPts incP, encPerm a]

/-- **Length bounds on the data of a program state**, which bound its weight
(`AggCertWt.lean`): graph forms have at most `(k + q)²` pairs (the outputs of the cited
primitives), cached representative lists at most `D` entries. -/
def CpLen (D : ℕ) (σ : CpSt k q) : Prop :=
  σ.t ≤ k ∧ σ.osP.length ≤ k ∧ σ.p0.length ≤ (k + q) ^ 2 ∧ σ.px.length ≤ (k + q) ^ 2 ∧
    σ.ps.length ≤ (k + q) ^ 2 ∧
    (∀ r ∈ σ.res, r.1.length ≤ (k + q) ^ 2 ∧ r.2.length ≤ (k + q) ^ 2) ∧
    ∀ ent ∈ σ.cache, ent.1.length ≤ (k + q) ^ 2 ∧ ent.2.1.length ≤ (k + q) ^ 2 ∧
      ent.2.2.length ≤ D

/-- Length bounds on one stage. -/
def CpSgLen (d : CpStgD k q) : Prop := d.1.length ≤ (k + q) ^ 2 ∧ d.2.length ≤ k

/-- Length bounds on one stage log: at most `k` stages. -/
def CpLgLen (l : List (CpStgD k q)) : Prop := l.length ≤ k ∧ ∀ d ∈ l, CpSgLen d

/-- **Length bounds on the logs**, which bound their weight: one log for each finished test set,
and at most `k` stages in each stage log. -/
structure CpLogLen (σ : CpSt k q) : Prop where
  logs_len : σ.logs.length = σ.res.length
  lz : CpLgLen σ.lz
  lx : CpLgLen σ.lx
  logs : ∀ l ∈ σ.logs, CpLgLen l.2.1 ∧ CpLgLen l.2.2

/-- **Length bounds on the data inside a round**: at most `D` representatives in the round
(those still to come, `as`, the current one, and those done), each done one with at most
`k² + 1` collected generators; at most `k²` generators of the kernel; the window indicator is a
`0/1` list; at most `k` points in the increment. -/
def CpInLen (k q D : ℕ) (inner : Val) : Prop :=
  ∃ (as gs hs : List (Perm (Fin k))) (f : Fin k → ℕ) (incP : List (Fin (k + q)))
    (a : Perm (Fin k)), inner = cpInnerV as gs hs (encFun f) incP a ∧
    gs.length + (as.length + 1) * (k ^ 2 + 1) ≤ D * (k ^ 2 + 1) ∧ hs.length ≤ k ^ 2 ∧
    (∀ i, f i ≤ 1) ∧ incP.length ≤ k

end Values

/-! ### The invariants -/

section Inv

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] (e : Ω ≃ Fin k) {S : State Ω C} [Fintype S.dom]
  {L : GiantLabels S} (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- **A good cache**: it stands for a record (`CacheOK`), and every representative is the
position permutation of an element of `G`. -/
def CacheOK' (c : List (CacheEntry k L.q))
    (rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))) : Prop :=
  CacheOK e S L c rec ∧ ∀ ent ∈ c, ∀ a ∈ ent.2.2, (toFin e).symm a ∈ S.G

/-- The string of a position, on `Ω`. -/
abbrev cpZ (S : State Ω C) (s : Bool) : Ω → C := cpStr S.x S.y s

omit [DecidableEq Ω] [Fintype S.dom] in
theorem cpStr_dstr (s : Bool) :
    cpStr (dstr S S.x) (dstr S S.y) s = dstr S (cpZ S s) := by
  cases s <;> rfl

/-- **Stage `j` of the string `z` for the test set `T`** (the same as `CmStg`): `d.1` is a graph
form of the lift of `A_j` with at most `(k + q)²` pairs, and `d.2` lists the positions of the
increment `V_j` once each. -/
def CpStg (T : Finset (Fin L.q)) (z : Ω → C) (j : ℕ) (d : CpStgD k L.q) : Prop :=
  PairGens e L (S.liftGroup (grp (cpPhi S πd T) (dstr S z) j)) d.1 ∧
    d.1.length ≤ (k + L.q) ^ 2 ∧
    ∃ incl : List S.dom, incl.Nodup ∧
      (∀ v, v ∈ incl ↔ v ∈ inc (cpPhi S πd T) (dstr S z) j) ∧ d.2 = incl.map (domPos e L.q)

/-- **The log of the string `z` for `T`** (the same as `CmStgs`): one stage for each round
`j < n`, in order. -/
def CpStgs (T : Finset (Fin L.q)) (z : Ω → C) (l : List (CpStgD k L.q)) : Prop :=
  l.length = Fintype.card S.dom ∧ ∀ j (h : j < l.length), CpStg e πd T z j l[j]

/-- **The data at the start of a round**, for the position
`round acc T σ.Ts σ.s σ.t` and the record `rec`. -/
structure CpRoundInv (σ : CpSt k L.q) (acc : List (StagePair S)) (T : Finset (Fin L.q))
    (rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))) :
    Prop where
  card : T.card = P₀.κ
  cardTs : ∀ T' ∈ σ.Ts, T'.card = P₀.κ
  t_le : σ.t ≤ Fintype.card S.dom
  res : List.Forall₂ (fun (r : StagePair S) (p : GPairs k L.q × GPairs k L.q) =>
    PairGens e L (S.liftGroup r.1.1) p.1 ∧ PairGens e L (S.liftGroup r.2.1) p.2) acc σ.res
  cache : CacheOK' e σ.cache rec
  p0 : PairGens e L (S.liftGroup (Pgrp S.domGroup πd T)) σ.p0
  px : σ.s = true →
    PairGens e L (S.liftGroup (grp (cpPhi S πd T) (dstr S S.x) (Fintype.card S.dom))) σ.px
  ps : PairGens e L (S.liftGroup (grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t)) σ.ps
  os : ∃ os : List S.dom, os.Nodup ∧
    (∀ v, v ∈ os ↔ v ∉ win (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t) ∧
    σ.osP = os.map (domPos e L.q)
  /-- The test sets: those done, the current one and those to come, in the order of a
  `TestSetOrder`. -/
  ord : ∃ O : TestSetOrder L.q P₀.κ, σ.logs.map Prod.fst ++ T :: σ.Ts = O.sets
  /-- The log of the current string: the rounds `0, …, t - 1`. -/
  lz_len : σ.lz.length = σ.t
  lz : ∀ j (h : j < σ.lz.length), CpStg e πd T (cpZ S σ.s) j σ.lz[j]
  lx : σ.s = true → CpStgs e πd T S.x σ.lx
  logs : ∀ l ∈ σ.logs, CpStgs e πd l.1 S.x l.2.1 ∧ CpStgs e πd l.1 S.y l.2.2
  loglen : CpLogLen σ
  /-- The results of the finished test sets are the final stages of their logs' test sets. -/
  resLog : List.Forall₂ (fun (l : Finset (Fin L.q) × List (CpStgD k L.q) × List (CpStgD k L.q))
    (p : GPairs k L.q × GPairs k L.q) =>
      PairGens e L (S.liftGroup (grp (cpPhi S πd l.1) (dstr S S.x) (Fintype.card S.dom))) p.1 ∧
      PairGens e L (S.liftGroup (grp (cpPhi S πd l.1) (dstr S S.y) (Fintype.card S.dom))) p.2)
    σ.logs σ.res

/-- The window call of the representative `τ` in round `t` of the string `s`. -/
noncomputable abbrev cpCall (T : Finset (Fin L.q)) (s : Bool) (t : ℕ) (τ : Perm S.dom) :
    State Ω (Option C) :=
  windowCall S (kernelIn (cpPhi S πd T) (grp (cpPhi S πd T) (dstr S (cpZ S s)) t))
    (inc (cpPhi S πd T) (dstr S (cpZ S s)) t) (cpInv S (cpPhi S πd T) (dstr S (cpZ S s)) t)
    (dstr S (cpZ S s)) τ

/-- **The data inside a round**, after the window call of `a`, with its answer `u`: the
representatives `dn` before `a` have been called (with answers `o`), those of `as` are still
to come. The position is `win acc T σ.Ts σ.s σ.t τs acc'`. -/
def CpWinInv (σ : CpSt k L.q) (acc : List (StagePair S)) (T : Finset (Fin L.q))
    (rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom)))
    (inner u : Val) (τs : List (Perm S.dom)) (acc' : List (Set (Perm S.dom))) : Prop :=
  CpRoundInv e πd σ acc T rec ∧ σ.t < Fintype.card S.dom ∧
    inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t ≠ ∅ ∧
    ∃ (dn : List (Perm (Fin k) × Option (Perm (Fin k) × List (Perm (Fin k)))))
      (a : Perm (Fin k)) (as hs : List (Perm (Fin k))) (dv : Val) (incl : List S.dom),
      inner = cpInnerV as (stageGens dn) hs dv (incl.map (domPos e L.q)) a ∧
      ((grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t,
        kernelIn (cpPhi S πd T) (grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t)),
        (dn.map Prod.fst ++ a :: as).map (domOfPos e S)) ∈ rec ∧
      (∀ b ∈ dn.map Prod.fst ++ a :: as, (toFin e).symm b ∈ S.G) ∧
      τs = as.map (domOfPos e S) ∧
      (∀ p ∈ dn, AnsSet e p.2 (cpCall πd T σ.s σ.t (domOfPos e S p.1)).answer) ∧
      acc' = cpAcc S (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t
        ((dn.map Prod.fst ++ [a]).map (domOfPos e S)) ∧
      AnsC e u (cpCall πd T σ.s σ.t (domOfPos e S a)).answer ∧
      GroupValC k (encGroup hs)
        (groupFin e (S.liftGroup (kernelIn (cpPhi S πd T)
          (grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t)))) ∧
      DomVal e dv (Subtype.val '' (inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t : Set S.dom)) ∧
      incl.Nodup ∧ ∀ v, v ∈ incl ↔ v ∈ inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t

/-- **What a program state stands for.** `par` is the parent value, `Bw` bounds the weights of
program states, `M₀` bounds the measure plus the cache length, `NT` the number of test sets,
and `D` the number of representatives in one round. -/
def CpRep (par : Val) (D Bw M₀ NT : ℕ) (m : ℕ) (st : Val)
    (Ss : Set (Script (List (StagePair S)))) (f : ℕ) : Prop :=
  ∃ (pos : CpPos S L.q) (σ : CpSt k L.q)
    (rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))),
    m = cpMeas (Fintype.card S.dom) D pos ∧ m ≤ f ∧ st.wt ≤ Bw ∧
    σ.cache.length + m ≤ M₀ ∧ σ.res.length + σ.Ts.length + 1 ≤ NT ∧ CpLen D σ ∧
    Ss = (fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R pos) '' Cands rec ∧
    match pos with
    | .fin _ => False
    | .round acc T Ts s t => T = σ.T ∧ Ts = σ.Ts ∧ s = σ.s ∧ t = σ.t ∧
        CpRoundInv e πd σ acc T rec ∧ ∃ u, st = .list [σ.val par (.list []), u]
    | .win acc T Ts s t τs acc' => T = σ.T ∧ Ts = σ.Ts ∧ s = σ.s ∧ t = σ.t ∧
        ∃ inner u, st = .list [σ.val par inner, u] ∧ CpWinInv e πd σ acc T rec inner u τs acc' ∧
          CpInLen k L.q D inner

end Inv

end GI.Impl
