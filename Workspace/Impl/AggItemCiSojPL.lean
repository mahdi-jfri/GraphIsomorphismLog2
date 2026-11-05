module

public import Workspace.Impl.AggItemCiSojPW

@[expose] public section

/-! # The computed matrix colors are exactly the model's query colors -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle GI.CoherentEntrance GI.PairRefinement Equiv Equiv.Perm

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- A matrix entry read from the original pair-color table. -/
def itcsMatrix (X : PairCfg L.q) (v : ℕ) : W→R→Bool :=
  fun w r=>decide (X.col w.val r.val=v)

/-- Raw certificate edge colors read precisely the source certificate matrix. -/
theorem itcs_source_matrix (X : PairCfg L.q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) :
    rectM X i₀ cert = itcsMatrix X (certVals X i₀ cert).2.2 := by
  funext w r
  exact rectM_apply X i₀ cert w r

/-- The source pullback through the identity permutation is the model's source string. -/
theorem itcs_source_pull (rep : RectRep P₀ S L W R) (X : PairCfg L.q) (v : ℕ) :
    rep.colors (itcsMatrix X v) =
      fun a=>(rep.cell a).map fun c=>decide (X.col ((1:Perm (Fin L.q)) c.1.val)
        ((1:Perm (Fin L.q)) c.2.val)=v) := by
  funext a
  rfl

/-- Twisting the aligned target matrix reads the target table through `a₀*t`,
which is exactly the permutation computed by the pullback program. -/
theorem itcs_target_pull (rep : RectRep P₀ S L W R) (Y : PairCfg L.q) (v : ℕ)
    (a₀ : Perm (Fin L.q)) (t : permitted W R) :
    rep.colors (RectRep.twistMat t (fun w r=>decide (Y.col (a₀ w.val) (a₀ r.val)=v))) =
      fun a=>(rep.cell a).map fun c=>decide (Y.col ((a₀*t.val.val) c.1.val)
        ((a₀*t.val.val) c.2.val)=v) := by
  funext a
  cases he : rep.cell a <;> simp only [RectRep.colors,he,Option.map_none,Option.map_some] <;> rfl

end GI.Impl
