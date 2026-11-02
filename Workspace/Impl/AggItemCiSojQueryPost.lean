import Workspace.Impl.AggItemCiSojSeq
import Workspace.Impl.AggItemCiSojQuery
import Workspace.Impl.AggItemCiSojSpec

/-! # Returning the next exact rectangle query to the aggregation interface -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}
  {W R : Finset (Fin L.q)}

/-- The ordered model query satisfies every recursive-call clause of the item
postcondition: its canonical encoding, injective color code, inherited goodness,
and measure decrease are supplied by the rectangle proofs at this call. -/
theorem itcs_query_post (Rel : ItCfIRel) (e : Ω ≃ Fin k) (c : C → ℕ) (K : ItSCtx k S L)
    (b : Fin (P₀.κ+1) → Fin L.q) (oX oY : CfgOut L.q)
    (E : Set (ItCfCh S L.toGiantLabels))
    (sb : ItCfCh S L.toGiantLabels → Script (Branches Ω)) (f B : ℕ)
    (rep : RectRep P₀ S L.toGiantLabels W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q)) (t : permitted W R) (ts : List (permitted W R))
    (prev : List (Option (alternatingGroup (Fin L.q))))
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hier kst : Val)
    (hK : K.OK e c) (hgood : Good P₀ .giant S) (h3 : 3 ≤ W.card) (hR : R.Nonempty)
    (hhs : PairGens e L.toGiantLabels rep.H hs) (hlen : hs.length ≤ k^2)
    (hhier : HierValC e hier S.hier) (hf : 0 < f) (hE : E.Nonempty)
    (hscript : ∀ ch ∈ E, sb ch = itcsQuerySeq rep M N a₀ (t::ts) prev)
    (hrel : ∀ u, AnsC e u (rep.state M N t).answer →
      Rel.Ri e c S L K b oX oY (.list [kst,u]) E
        (fun _ => itcsQuerySeq rep M N a₀ ts (prev++[(rep.query M N a₀ t).read (rep.state M N t).answer]))
        (f-1)) :
    ItCfIPost Rel e c S L K b oX oY E sb f B
      (.list [.nat 1,.nat 1,itcsQVal e rep M N t hs hier,kst]) := by
  letI : Finite Ω := Finite.of_equiv _ e.symm
  have hcall := itcs_query_call rep M N a₀ t hgood
  have hcan := itcs_query_canon e rep M N t hK.can hhier hhs hlen (itcs_query_k e rep h3 hR)
  refine Or.inr ⟨hf,.cont,Ω,Option Bool,rep.state M N t,k,e,itcsQCode,
    itcsQVal e rep M N t hs hier,kst,E,
    (fun _ A => itcsQuerySeq rep M N a₀ ts (prev++[(rep.query M N a₀ t).read A])),
    subset_rfl,hE,itcs_qcode_inj,Or.inr rfl,rfl,hcan,hcall.1,hcall.2,?_,hrel⟩
  intro ch hch
  exact (hscript ch hch).trans (itcs_query_seq_cons rep M N a₀ t ts prev)

end GI.Impl
