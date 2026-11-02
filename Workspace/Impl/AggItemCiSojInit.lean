import Workspace.Impl.AggItemCiSojChoice

/-!
# Initializing the fixed first-rectangle choices

The kept value is empty. Its relation fixes one certificate function, the explicit
alignment and imprimitive-pair functions, and one representation function supplied
by `RcRepSpec` for this round. The functions need not be materialized at init:
their encoded values are computed by their programs at each later call.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- The same representation function is used at every rectangle of this context. -/
def itcsRepFnOK (Pg : Program) (fr : ℕ) (Br : ℕ → ℕ) (e : Ω ≃ Fin k)
    (K : ItSCtx k S L)
    (rf : ∀ W R : Finset (Fin L.q), RectConds P₀ S L.toGiantLabels W R →
      RectRep P₀ S L.toGiantLabels W R) : Prop :=
  ∀ (W R : Finset (Fin L.q)) (h : RectConds P₀ S L.toGiantLabels W R),
    FunAll Pg fr (rcRepIn K.sv L.q K.ps W R) fun w cost =>
      ∃ hs : List (Perm (Fin k) × Perm (Fin L.q)),
        w = rcRepVal e (rf W R h) hs ∧ PairGens e L.toGiantLabels (rf W R h).H hs ∧
          hs.length ≤ k ^ 2 ∧ cost ≤ Br (rcRepIn K.sv L.q K.ps W R).wt ∧
          w.wt ≤ Br (rcRepIn K.sv L.q K.ps W R).wt

/-- The kept relation fixes all first-rectangle choice functions for the round. -/
def itcsKeep (Pg : Program) (fr : ℕ) (Br : ℕ → ℕ) (cf : RcCertFn)
    (e : Ω ≃ Fin k) (_c : C → ℕ) (K : ItSCtx k S L) (w : Val)
    (E : Set (ItCfCh S L.toGiantLabels)) : Prop :=
  w = .list [] ∧ ∃ rf, itcsRepFnOK Pg fr Br e K rf ∧ E = {(itcsChoices cf, rf)}

/-- Every kept value represents a nonempty, fixed choice set. -/
theorem itcs_keep_ne {Pg : Program} {fr : ℕ} {Br : ℕ → ℕ} {cf : RcCertFn}
    {e : Ω ≃ Fin k} {c : C → ℕ} {K : ItSCtx k S L} {w : Val}
    {E : Set (ItCfCh S L.toGiantLabels)} (h : itcsKeep Pg fr Br cf e c K w E) : E.Nonempty := by
  obtain ⟨-, rf, -, rfl⟩ := h
  exact Set.singleton_nonempty _

/-- The empty kept value has constant weight. -/
theorem itcs_keep_weight {Pg : Program} {fr : ℕ} {Br : ℕ → ℕ} {cf : RcCertFn}
    {e : Ω ≃ Fin k} {c : C → ℕ} {K : ItSCtx k S L} {w : Val}
    {E : Set (ItCfCh S L.toGiantLabels)} (h : itcsKeep Pg fr Br cf e c K w E) : w.wt ≤ 4 := by
  rw [h.1, wt_list_nil]

/-- The actual init program returns the empty kept value in constant cost. All
representation-contract preconditions are supplied by the calling context. -/
theorem itcs_init {Pg : Program} {fi fr : ℕ} {Br : ℕ → ℕ} (cf : RcCertFn)
    (hfi : Pg.funs[fi]? = some Expr.nil) (hr : RcRepSpec Pg fr Br)
    (e : Ω ≃ Fin k) (c : C → ℕ) (K : ItSCtx k S L) (hinj : Function.Injective c)
    (hK : K.OK e c) :
    FunAll Pg fi K.v (fun w cost =>
      ∃ E, itcsKeep Pg fr Br cf e c K w E ∧ cost ≤ 5) := by
  obtain ⟨rf, hrf⟩ := itcs_rep_call hK hinj hr
  have hn : FunDet Pg fi K.v (.list []) 5 :=
    StDC.funDet hfi (StDC.nil (W := 4) (by omega)) (by omega)
  exact FunAll.mono hn fun w cost ⟨hw, hc⟩ =>
    ⟨{(itcsChoices cf, rf)}, ⟨hw, rf, hrf, rfl⟩, hc⟩

end GI.Impl
