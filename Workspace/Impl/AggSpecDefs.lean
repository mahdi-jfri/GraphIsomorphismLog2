module

public import Workspace.Impl.AggSpecExec
public import Workspace.Impl.AggSpecChild

@[expose] public section

/-!
# The aggregation round as a sequence of phases: the contracts

The program of an aggregation round (`aggBodyE`, `Workspace/Impl/AggSpecBody.lean`) runs, on the
input `[sv, lv]` of a `GiantStep` call:

1. **reading** (`AsReadOK`): the program state of the certificate phase and the context of
   `LiftAndContinue` (`lcCtx`: the state value, the graph pairs `[g, π g]`, the selected interval,
   the new cap `⌊βq⌋`);
2. **the certificate phase** (`AsCertOK`): a run of `Ag.certScript` (Algorithm 2, Lemma 4.1);
3. **the comparison phase** (`AsCompOK`): a run of `Ag.compScript`;
4. **the items** (`AsItemsOK`): the canonical structures (class numbers, source tuple, the
   joint refinement; this includes the case test of each branch) and a run of `Ag.itemsScript`
   (Algorithm `alg:auxiliary`), whose output lists the pieces and the overcosets;
5. **`LiftAndContinue`** on the overcosets (`AsLcAt`, met by `lcMap_spec`);
6. **`CombineExact`** (`AsCeAt`, met by `ce_spec`).

The round's choices (`Aggregation` fields such as `reps`, `pick`, `num`, `src`, `halv`) are made
by the program as it goes, so no single round `Ag` is fixed at the start. Each phase works on a
*set* `Cs` of candidate rounds (as `Iface.run_specC` does inside a phase): it returns a run of the
part of the script of one candidate `Ag ∈ Cs`, and hands to the next phase the candidates whose
part of the script is the same as that of `Ag`. At the start the set is `asRounds L`: all rounds
with the selected interval and the constituent of the supplied labels. What a phase hands to the
next is a relation between the program state and the candidate set; these relations are the
fields of `AsHand`, fixed by the programs of the phases.

Every phase costs at most `X W₀` besides the calls of its run, and returns a value of weight at
most `X W₀`, where `W₀ = inW .giant S` bounds the weight of the input of the call.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm gens Preimage NormalizedFactor Membership)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-- **The rounds that fit the supplied labels**: the selected interval and the constituent are
those of the labels (`hsel`, `hcon` of `Run.aggregate`). -/
def asRounds {S : State Ω C} (L : SuppliedLabels S) : Set (Aggregation P₀ S L.toGiantLabels) :=
  {Ag | Ag.sel.val = L.sel.val ∧ Ag.con = L.con}

/-- **A call of the aggregation round**: the facts that the step specification gives about the
input `[sv, lv]` of a `GiantStep` call in the aggregation case. -/
structure AsCall (I : Iface) (Pg : Program) (F : Funs) (e : Ω ≃ Fin k) (c : C → ℕ)
    (S : State Ω C) (sv lv : Val) (L : SuppliedLabels S) : Prop where
  inj : Function.Injective c
  can : Canon e c sv S
  lab : I.LabVal e S lv L
  q₀ : P₀.q₀ < L.q
  lw : lv.wt ≤ I.labW k S.N
  good : Good P₀ .giant S
  ih : I.IH Pg F .giant S
  hnot : ¬ RowCase P₀.α S L.toGiantLabels

/-- **The hand-over relations between the phases.** `cert e c S L Cs st`: the program state `st`
of the certificate phase stands for the candidate set `Cs`; `comp` and `items` are the same for
the comparison phase and the items. -/
structure AsHand : Type 1 where
  cert : ∀ {Ω C : Type} {k : ℕ}, (Ω ≃ Fin k) → (C → ℕ) → (S : State Ω C) →
    (L : SuppliedLabels S) → Set (Aggregation P₀ S L.toGiantLabels) → Val → Prop
  comp : ∀ {Ω C : Type} {k : ℕ}, (Ω ≃ Fin k) → (C → ℕ) → (S : State Ω C) →
    (L : SuppliedLabels S) → Set (Aggregation P₀ S L.toGiantLabels) → Val → Prop
  items : ∀ {Ω C : Type} {k : ℕ}, (Ω ≃ Fin k) → (C → ℕ) → (S : State Ω C) →
    (L : SuppliedLabels S) → Set (Aggregation P₀ S L.toGiantLabels) → Val → Prop

variable (I : Iface) (Pg : Program) (F : Funs)

/-- **Reading the input** at `fr`: on `[sv, lv]` it returns `[st, ctx]`, where `st` is a program
state of the certificate phase for all rounds of the labels, and `ctx` is the context of
`LiftAndContinue` with graph pairs `ps` of `G` (`PairGens`), the selected interval and the cap
`⌊βq⌋`. -/
def AsReadOK (H : AsHand) (X : ℕ → ℕ) (fr : ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (sv lv : Val)
    (L : SuppliedLabels S), AsCall I Pg F e c S sv lv L →
    FunAll Pg fr (.list [sv, lv]) (fun w cost => ∃ (st : Val)
      (ps : List (Perm (Fin k) × Perm (Fin L.q))),
      w = .list [st, lcCtx sv k L.q ps L.sel (abCap L.toGiantLabels)] ∧
      PairGens e L.toGiantLabels S.G ps ∧ H.cert e c S L (asRounds L) st ∧
      cost ≤ X (I.inW .giant S) ∧ w.wt ≤ X (I.inW .giant S))

/-- **The certificate phase** at `fc`: from a program state of a candidate set `Cs`, a run of the
certificate script of one candidate `Ag`, and a program state of the comparison phase for the
candidates with the same certificate script. -/
def AsCertOK (H : AsHand) (X : ℕ → ℕ) (fc : ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (sv lv : Val)
    (L : SuppliedLabels S), AsCall I Pg F e c S sv lv L →
    ∀ (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (st : Val), H.cert e c S L Cs st →
    FunAll Pg fc st (fun w cost => ∃ Ag ∈ Cs, ∃ (a : List (StagePair S))
      (ex : Exec P₀ Ag.certScript a),
      H.comp e c S L {Ag' | Ag' ∈ Cs ∧ Ag'.certScript = Ag.certScript} w ∧
      (cost : ℝ) ≤ X (I.inW .giant S) + I.execCost ex ∧ w.wt ≤ X (I.inW .giant S))

/-- **The comparison phase** at `fm`: from a program state of a candidate set `Cs`, a run of the
comparison script of one candidate `Ag`, and a program state of the items for the candidates
with the same comparison script. -/
def AsCompOK (H : AsHand) (X : ℕ → ℕ) (fm : ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (sv lv : Val)
    (L : SuppliedLabels S), AsCall I Pg F e c S sv lv L →
    ∀ (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (st : Val), H.comp e c S L Cs st →
    FunAll Pg fm st (fun w cost => ∃ Ag ∈ Cs, ∃ (a : List Bool) (ex : Exec P₀ Ag.compScript a),
      H.items e c S L {Ag' | Ag' ∈ Cs ∧ Ag'.compScript = Ag.compScript} w ∧
      (cost : ℝ) ≤ X (I.inW .giant S) + I.execCost ex ∧ w.wt ≤ X (I.inW .giant S))

/-- **The program's overcoset `o = (σ, E₀, ms)` stands for the overcoset `ov` of the script**:
the groups agree, `ov.2 = π⁻¹(E₀)`, and the program's representative `L.rep σ` lies in the coset
`ov.1 • ov.2`. The paper fixes the coset of an overcoset, not its representative (`Run.aggregate`
takes any `τ_j ∈ ρ_j • H_j`), while the model picks the representatives of some items by a
classical choice. -/
def asOvAt {S : State Ω C} (L : GiantLabels S) (o : LcOver L.q)
    (ov : Perm Ω × Subgroup (Perm Ω)) : Prop :=
  ov.2 = L.lift o.2.1 ∧ L.rep o.1 ∈ ov.1 • (ov.2 : Set (Perm Ω))

/-- **The items** at `fi` (the canonical structures, the case of each branch, and the items'
script): from a program state of a candidate set `Cs`, a run of the items' script of one
candidate `Ag` with result `⟨pieces, ovs⟩`, where each overcoset of `ovs` has the group and the
coset of the corresponding entry of the program's list `os` (`asOvAt`), returned as
`[⟨pieces as combine pieces⟩, ⟨overcosets [σ, generators of E₀]⟩]`. -/
def AsItemsOK (H : AsHand) (X : ℕ → ℕ) (fi : ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (sv lv : Val)
    (L : SuppliedLabels S), AsCall I Pg F e c S sv lv L →
    ∀ (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (st : Val), H.items e c S L Cs st →
    FunAll Pg fi st (fun w cost => ∃ Ag ∈ Cs, ∃ (pieces : List (Set (Perm Ω)))
      (os : List (LcOver L.q)) (ovs : List (Perm Ω × Subgroup (Perm Ω)))
      (pcs : List (Perm (Fin k) × Acc k)) (ex : Exec P₀ Ag.itemsScript ⟨pieces, ovs⟩),
      List.Forall₂ (asOvAt L.toGiantLabels) os ovs ∧
      w = .list [.list (pcs.map encPiece), .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)] ∧
      pcs.length = pieces.length ∧
      (∀ i (h1 : i < pcs.length) (h2 : i < pieces.length), ceSet pcs[i] = toFin e '' pieces[i]) ∧
      (∀ o ∈ os, gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype) ∧
      (cost : ℝ) ≤ X (I.inW .giant S) + I.execCost ex ∧ w.wt ≤ X (I.inW .giant S))

/-- **`LiftAndContinue`** at `blc`: the conclusion of `lcMap_spec`, for a canonical state value. -/
def AsLcAt (hpre : Preimage) (hfac : NormalizedFactor) (blc : ℕ) (krC : ℕ → ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {sv : Val} {S : State Ω C},
    Canon e c sv S → ∀ {L : GiantLabels S} (_ : L.Constituent)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))}, PairGens e L S.G ps →
    ∀ {sel : ℕ}, sel < S.hier.length → ∀ (cap : ℕ) (os : List (LcOver L.q)),
    (∀ o ∈ os, gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype) →
    (∀ o ∈ os, ∀ (τ : Perm Ω) val, Canon e c val (lcChild S o.2.1 τ sel cap) →
      FunAll Pg F.cont val (I.Post .cont (lcChild S o.2.1 τ sel cap) e val)) →
    FunAll Pg blc (.list [lcCtx sv k L.q ps sel cap,
        .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)])
      (fun w cost => ∃ ws : List Val, w = .list ws ∧ ws.length = os.length ∧
        (∀ i (hi : i < os.length) (hw : i < ws.length), ∃ a u, ws[i] = .list [encPerm a, u] ∧
          (toFin e).symm a ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)) ∧
          AnsC e u (lcChild S os[i].2.1 ((toFin e).symm a) sel cap).answer) ∧
        ∃ cs : ℕ → ℕ, (∀ i (hi : i < os.length), ∃ τ ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)),
          ∃ (A : Set (Perm Ω)) (r : Run P₀ .cont (lcChild S os[i].2.1 τ sel cap) none A),
            (cs i : ℝ) ≤ r.total I.work) ∧
        cost ≤ os.length * lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC
            (2 * (Val.list [lcCtx sv k L.q ps sel cap,
              .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)]).wt + 6) +
          ∑ i ∈ Finset.range os.length, cs i +
          mapQK * (os.length + 1) *
            ((Val.list [lcCtx sv k L.q ps sel cap,
              .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)]).wt + w.wt + 1))

/-- `lcMap_spec` meets `AsLcAt`. -/
theorem asLcAt_of (hpre : Preimage) (hfac : NormalizedFactor)
    {b f bpre jpre bkr blift sb sp jfac bg bh bset : ℕ} {krC : ℕ → ℕ}
    (hb : Pg.HasAt b (mapFuns b f))
    (hf : Pg.funs[f]? = some (lcChildF F bpre bkr blift bg bh))
    (hbpre : Pg.HasAt bpre (graphPreFuns bpre jpre))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hkr : LcKrOK Pg bkr krC) (hkrm : Monotone krC)
    (hlift : Pg.funs[blift]? = some (liftLabF sb sp jfac)) (hsb : ShiftAt Pg sb)
    (hsp : Pg.HasAt sp (pSplitFuns sp))
    (hjfac : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (hga : Pg.HasAt bg (gatherFuns bg))
    (hbh : Pg.funs[bh]? = some (lcHierF bset)) (hset : Pg.HasAt bset (setFuns bset)) :
    AsLcAt I Pg F hpre hfac b krC := by
  intro Ω C k e c sv S hcan L con ps hps sel hsel cap os hos hcall
  obtain ⟨gv, dv, xv, yv, hv, rv, -, -, -, -, -, -, rfl⟩ := hcan.val
  exact lcMap_spec I hpre hfac hb hf hbpre hjpre hkr hkrm hlift hsb hsp hjfac hga hbh hset hcan
    con hps hsel cap os hos hcall

/-- **`CombineExact`** at `bce`: the conclusion of `ce_spec`. -/
def AsCeAt (hm : Membership) (bce : ℕ) : Prop :=
  ∀ (k : ℕ) (pcs cps : List (Perm (Fin k) × Acc k)),
    (unionSet (pcs ++ cps) = ∅ ∨ ∃ (c : Perm (Fin k)) (H : Subgroup (Perm (Fin k))),
      unionSet (pcs ++ cps) = c • (H : Set _)) →
    FunAll Pg bce (.list [.list (pcs.map encPiece), .list (cps.map encPiece)]) (fun u cost =>
      CosetC k u (unionSet (pcs ++ cps)) ∧
        cost ≤ ceCost hm k (Val.list [.list (pcs.map encPiece), .list (cps.map encPiece)]).wt)

/-- `ce_spec` meets `AsCeAt`. -/
theorem asCeAt_of (hm : Membership) {f bapp bc g comp inv app bn jm : ℕ}
    (hf : Pg.funs[f]? = some (ceF bapp bc bn)) (hap : Pg.HasAt bapp (appendFuns bapp))
    (hbc : Pg.HasAt bc (foldlFuns bc g)) (hg : Pg.funs[g]? = some (combStep comp inv app))
    (hcomp : Pg.HasAt comp (composeFuns comp)) (hinv : Pg.HasAt inv (invFuns inv))
    (happ : Pg.HasAt app (appendFuns app))
    (hbn : Pg.HasAt bn (cosetNFFuns bn jm)) (hjm : Pg.prims[jm]? = some (membershipPrim hm)) :
    AsCeAt Pg hm f :=
  fun _ pcs cps hU => ce_spec hm hf hap hbc hg hcomp hinv happ hbn hjm pcs cps hU

/-! ### The cost of the round -/

/-- The largest value of `f` up to `n`. It is monotone in `n` even when `f` is not. -/
def asMax (f : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range (n + 1)).sup f

theorem le_asMax (f : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) : f m ≤ asMax f n :=
  Finset.le_sup (f := f) (Finset.mem_range.2 (by omega))

/-- The weight bound of one continuation piece `[encPerm a, u]`. -/
def asEW (k : ℕ) : ℕ := 2 * (4 * (k + 1) ^ 2 + ansW k) + 6

/-- The weight bound of the input of `LiftAndContinue`, for phase values of weight `Y`. -/
def asWl (Y : ℕ) : ℕ := 2 * (Y + Y) + 6

/-- The weight bound of the output of `LiftAndContinue`. -/
def asWw (k Y : ℕ) : ℕ := Y * (2 * asEW k + 1) + 4

/-- The weight bound of the input of `CombineExact`. -/
def asWc (k Y : ℕ) : ℕ := 2 * (Y + asWw k Y) + 6

/-- **The own work of the round** on `k` positions with input weight bound `W₀`, for phases
bounded by `X`: the reading, the four phases without their calls, `LiftAndContinue` without its
continuations, `CombineExact` and the overhead of the body. -/
noncomputable def asOwn (hpre : Preimage) (hfac : NormalizedFactor) (hm : Membership)
    (krC X : ℕ → ℕ) (k W₀ : ℕ) : ℕ :=
  100 * (W₀ + X W₀ + asWl (X W₀) + asWw k (X W₀) + asWc k (X W₀) + ansW k + 10) +
    X W₀ * asMax (lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC) (2 * asWl (X W₀) + 6) +
    mapQK * (X W₀ + 1) * (asWl (X W₀) + asWw k (X W₀) + 1) +
    asMax (ceCost hm k) (asWc k (X W₀))

end GI.Impl
