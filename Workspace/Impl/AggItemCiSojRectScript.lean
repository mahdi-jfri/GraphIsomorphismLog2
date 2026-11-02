import Workspace.Impl.AggItemCiSojQueryPost
import Workspace.Impl.AggItemCiSojGuard

/-! # Exact model dispatch from the source certificate to the ordered queries -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Rectangle GI.CoherentEntrance Equiv Equiv.Perm

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

open Classical in
/-- The literal five clauses tested by the model's rectangle branch. -/
def itcsRectGuard (X Y : PairCfg L.q) (y₀ : Fin L.q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) : Prop :=
  let W' := Y.fiber.filter fun a => Y.col y₀ a = (certVals X i₀ cert).1
  let R' := Y.fiber.filter fun a => Y.col y₀ a = (certVals X i₀ cert).2.1
  (rectW X i₀ cert).card = W'.card ∧ (rectR X i₀ cert).card = R'.card ∧
    3 ≤ (rectW X i₀ cert).card ∧ Disjoint (rectW X i₀ cert) (rectR X i₀ cert) ∧ Disjoint W' R'

/-- On primitive, unbalanced source data, the fixed certificate is the model's
next branch. Its existence is supplied by `itcs_cert_exists`. -/
theorem itcs_cert_script (O : RectOracle P₀ S L) (ch : SojChoice)
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q) (hx : x₀ ∈ X.fiber)
    (hp : PrimitiveColorCuts X.coloring false)
    (hb : ¬ ∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤ etaB*X.fiber.card)
    (hc : Nonempty (RectangleCertificate X.coloring false (X.idx hx) etaB)) :
    (sojItem O ch X Y x₀ y₀).script =
      (rectItem O ch X Y y₀ (X.idx hx) (ch.cert X (X.idx hx) hc)).script := by
  classical
  simp only [sojItem,dif_pos hx,if_pos hp,if_neg hb,dif_pos hc]

/-- A failed literal rectangle guard finishes the item with no overcosets. -/
theorem itcs_rect_skip (O : RectOracle P₀ S L) (ch : SojChoice)
    (X Y : PairCfg L.q) (y₀ : Fin L.q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB)
    (hg : ¬ itcsRectGuard X Y y₀ i₀ cert) :
    (rectItem O ch X Y y₀ i₀ cert).script = Script.done ⟨[],[]⟩ := by
  classical
  simp only [itcsRectGuard] at hg
  simp only [rectItem,dif_neg hg,AuxItem.script]

/-- A successful literal guard selects the fixed even alignment and exactly the
model's rectangle queries. -/
theorem itcs_rect_query_script (O : RectOracle P₀ S L) (ch : SojChoice)
    (X Y : PairCfg L.q) (y₀ : Fin L.q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB)
    (hg : itcsRectGuard X Y y₀ i₀ cert) :
    let W := rectW X i₀ cert
    let R := rectR X i₀ cert
    let W' := Y.fiber.filter fun a => Y.col y₀ a = (certVals X i₀ cert).1
    let R' := Y.fiber.filter fun a => Y.col y₀ a = (certVals X i₀ cert).2.1
    let a₀ := (ch.align W R W' R' hg.2.2.2.1 hg.2.2.2.2 hg.1 hg.2.1 hg.2.2.1).1
    let M := rectM X i₀ cert
    let N := fun (w : W) (r : R) => decide (Y.col (a₀.val w.val) (a₀.val r.val) = (certVals X i₀ cert).2.2)
    (rectItem O ch X Y y₀ i₀ cert).script =
      (AuxItem.query (O.queries W R M N a₀) (leftGroup M)).script := by
  classical
  dsimp only
  simp only [itcsRectGuard] at hg
  simp only [rectItem,dif_pos hg]

/-- The cited representation function gives exactly the two-or-fewer ordered
queries. The proof of `RectConds` is used at the oracle call itself. -/
theorem itcs_rect_oracle_script [Finite Ω]
    (rf : ∀ W R : Finset (Fin L.q), RectConds P₀ S L W R → RectRep P₀ S L W R)
    (W R : Finset (Fin L.q)) (hc : RectConds P₀ S L W R)
    (M N : W → R → Bool) (a₀ : alternatingGroup (Fin L.q)) :
    (AuxItem.query ((RectOracle.ofReps rf).queries W R M N a₀) (leftGroup M)).script =
      itcsQuerySeq (rf W R hc) M N a₀ (itcsTwists (rf W R hc)) [] := by
  classical
  simp only [RectOracle.ofReps,dif_pos hc]
  exact itcs_query_seq_item _ M N a₀

end GI.Impl
