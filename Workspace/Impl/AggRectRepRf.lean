module

public import Workspace.Impl.AggRectRepKq
public import Workspace.Impl.AggGraph

@[expose] public section

/-!
# The representation function of the pair cases

The representation that the program computes, as one function of the rectangle (`rcRRep`). It
follows `rectRepOf` (`Workspace/Algorithm/AuxPairRect.lean`): by the support classification
(Corollary A.25) the kernel orbits are indexed by ordered pairs, by unordered pairs, or by
single labels.

* Ordered pairs: Lemma A.27 on the quotient of Lemma A.26 transported from the increasing order
  of the two fixed points of `π(G_x)` at a base point `x` (`rcRKqO`).
* Unordered pairs: Lemma A.27 on the quotient (it is fixed by `f(x) = D`).
* Single labels: a supplied representation `nat` (the diagonal carrier of Lemma A.30).

The data that the program reads off it:

* the group `H = π⁻¹(P)` is generated, in graph form, by the pairs of `G` whose label part lies
  in `P` (`rcR_pairGens_H`), which is what the cited **Preimage** task returns on the graph
  group with the generators of `P` (`rcR_closure_gens`);
* the cell code of a position `g x` is `rcRCode W R uno (π g d₁) (π g d₂)`, for the support
  `D = {d₁ < d₂}` at `x` and `uno` true for unordered pairs (`rcR_code_ord`, `rcR_code_uno`);
  off the domain it is `0`.
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle

/-! ### The cell code of a pair of labels -/

/-- The code of the cell above the pair `(c, d)`: `1 + c q + d` when `c ∈ W`, `d ∈ R`; for
unordered pairs also `1 + d q + c` when `d ∈ W`, `c ∈ R`; else `0`. -/
def rcRCode {q : ℕ} (W R : Finset (Fin q)) (uno : Bool) (c d : Fin q) : ℕ :=
  if c ∈ W ∧ d ∈ R then 1 + (c : ℕ) * q + d
  else if uno = true ∧ d ∈ W ∧ c ∈ R then 1 + (d : ℕ) * q + c else 0

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}

section Cells

variable {W R : Finset (Fin L.q)} (hd : Disjoint W R)

/-- Ordered pairs: the code of the cell of a position with `f(v) = (c, d)`. -/
theorem rcR_code_ord (f : GI.StabilizerQuotient.KernelQuotient πd S.dom
    (GI.Pairs.OrderedPair (Fin L.q))) {v : Ω} (hv : v ∈ S.dom) {c d : Fin L.q} (hcd : c ≠ d)
    (hf : f.map ⟨v, hv⟩ = ⟨(c, d), hcd⟩) :
    rcCellCode (pairCell f (orderedEmbedding hd) v) = rcRCode W R false c d := by
  unfold rcRCode
  by_cases h : c ∈ W ∧ d ∈ R
  · rw [if_pos h]
    have : pairCell f (orderedEmbedding hd) v = some (⟨c, h.1⟩, ⟨d, h.2⟩) := by
      rw [pairCell_eq_some f _ hv, hf]; rfl
    rw [this]; rfl
  · rw [if_neg h, if_neg (by simp)]
    have : pairCell f (orderedEmbedding hd) v = none := by
      rw [pairCell_eq_none f _ hv, hf]
      rintro ⟨⟨w, r⟩, hwr⟩
      have h1 : (w.1, r.1) = (c, d) := congrArg (fun z : GI.Pairs.OrderedPair (Fin L.q) => z.1) hwr
      rw [Prod.mk.injEq] at h1
      exact h ⟨h1.1 ▸ w.2, h1.2 ▸ r.2⟩
    rw [this]; rfl

/-- Unordered pairs: the code of the cell of a position with `f(v) = {c, d}`. -/
theorem rcR_code_uno (f : GI.StabilizerQuotient.KernelQuotient πd S.dom
    (GI.Johnson.SubsetVertex (Fin L.q) 2)) {v : Ω} (hv : v ∈ S.dom) {c d : Fin L.q}
    (hcd : c ≠ d) (hf : f.map ⟨v, hv⟩ = GI.Pairs.unorderedOfOrdered ⟨(c, d), hcd⟩) :
    rcCellCode (pairCell f (unorderedEmbedding hd) v) = rcRCode W R true c d := by
  unfold rcRCode
  by_cases h : c ∈ W ∧ d ∈ R
  · rw [if_pos h]
    have : pairCell f (unorderedEmbedding hd) v = some (⟨c, h.1⟩, ⟨d, h.2⟩) := by
      rw [pairCell_eq_some f _ hv, hf]; rfl
    rw [this]; rfl
  rw [if_neg h]
  by_cases h' : d ∈ W ∧ c ∈ R
  · rw [if_pos ⟨rfl, h'⟩]
    have : pairCell f (unorderedEmbedding hd) v = some (⟨d, h'.1⟩, ⟨c, h'.2⟩) := by
      rw [pairCell_eq_some f _ hv, hf]
      apply Subtype.ext
      exact Finset.pair_comm c d
    rw [this]; rfl
  · rw [if_neg (by simp [h'])]
    have : pairCell f (unorderedEmbedding hd) v = none := by
      rw [pairCell_eq_none f _ hv, hf]
      rintro ⟨⟨w, r⟩, hwr⟩
      have h1 := congrArg (fun z : GI.Johnson.SubsetVertex (Fin L.q) 2 => (z.1 : Set (Fin L.q)))
        hwr
      simp only [unorderedEmbedding, orderedEmbedding, GI.Pairs.unorderedOfOrdered,
        Function.Embedding.coeFn_mk, Finset.coe_pair] at h1
      rcases Set.pair_eq_pair_iff.1 h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exact h ⟨by rw [← h2]; exact w.2, by rw [← h3]; exact r.2⟩
      · exact h' ⟨by rw [← h2]; exact w.2, by rw [← h3]; exact r.2⟩
    rw [this]; rfl

/-- Off the domain the cell code is `0`. -/
theorem rcR_code_off {Ξ : Type} [MulAction (alternatingGroup (Fin L.q)) Ξ]
    (f : GI.StabilizerQuotient.KernelQuotient πd S.dom Ξ) (emb : W × R ↪ Ξ) {v : Ω}
    (hv : v ∉ S.dom) : rcCellCode (pairCell f emb v) = 0 := by
  unfold pairCell; rw [dif_neg hv]; rfl

end Cells

/-! ### The group `H` in graph form -/

section Group

variable {k : ℕ} (e : Ω ≃ Fin k)

/-- **The graph of `H = π⁻¹(P)`** is the part of the graph of `G` whose label part lies in `P`. -/
theorem rcR_graph_lift (E : Subgroup (alternatingGroup (Fin L.q))) :
    graphOf e L (L.lift E) =
      graphOf e L S.G ⊓ (E.map (alternatingGroup (Fin L.q)).subtype).comap (MonoidHom.snd _ _) := by
  ext p
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_snd]
  rw [mem_graphOf, mem_graphOf]
  constructor
  · rintro ⟨g, hg, hl, h1, h2⟩
    obtain ⟨hg', hE⟩ := L.mem_lift.1 hl
    exact ⟨⟨g, hg, hg, h1, h2⟩, ⟨_, hE, h2⟩⟩
  · rintro ⟨⟨g, hg, -, h1, h2⟩, ⟨s, hs, hs2⟩⟩
    refine ⟨g, hg, L.mem_lift.2 ⟨hg, ?_⟩, h1, h2⟩
    have : L.π ⟨g, hg⟩ = s := Subtype.ext (h2.trans hs2.symm)
    rw [this]; exact hs

/-- **Graph pairs of `H = π⁻¹(P)`** from the preimage output: pairs that generate the part of the
group of `ps` (graph pairs of `G`) whose label part lies in `⟨ms⟩ = P`. -/
theorem rcR_pairGens_H {E : Subgroup (alternatingGroup (Fin L.q))}
    {ps qs : List (Perm (Fin k) × Perm (Fin L.q))} {ms : List (Perm (Fin L.q))}
    (hps : PairGens e L S.G ps) (hms : GI.Cited.gens ms = E.map (alternatingGroup (Fin L.q)).subtype)
    (hqs : Subgroup.closure {p | p ∈ qs} =
      Subgroup.closure {p | p ∈ ps} ⊓ (GI.Cited.gens ms).comap (MonoidHom.snd _ _)) :
    PairGens e L (L.lift E) qs := by
  unfold PairGens
  rw [hqs, hps, hms, rcR_graph_lift]

/-- The generators of `P` lie in the label part of the graph of `G` (the precondition of the
preimage call). -/
theorem rcR_gens_in_graph {ps : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L S.G ps) {m : Perm (Fin L.q)} (hm : m ∈ alternatingGroup (Fin L.q)) :
    ∃ p ∈ Subgroup.closure {p | p ∈ ps}, MonoidHom.snd _ _ p = m := by
  obtain ⟨g, hg⟩ := L.π_surj ⟨m, hm⟩
  refine ⟨gpair e L g, ?_, ?_⟩
  · rw [hps, mem_graphOf]
    exact ⟨g.1, g.2, g.2, rfl, rfl⟩
  · show ((L.π g : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) = m
    rw [hg]

end Group

/-! ### The representation function -/

section Rep

variable [Finite Ω] (I : AggregationData P₀ S L)

/-- The kernel-orbit quotient on ordered pairs used by the program: the quotient of Lemma A.26
transported from the increasing order at `x`. -/
noncomputable def rcRQo {x : Ω} (hx : x ∈ S.dom)
    (ho : Nonempty (KernelQuotient I.πd S.dom (GI.Pairs.OrderedPair (Fin L.q)))) :
    KernelQuotient I.πd S.dom (GI.Pairs.OrderedPair (Fin L.q)) :=
  rcRKqO I.πd_spec I.htr (by have := I.q_ten; omega) ho.some hx

open Classical in
/-- **The representation function** of the program, for the base point `x` and a representation
`nat` for single labels (`rectRepOf` with the quotient `rcRQo` for ordered pairs). -/
noncomputable def rcRRep {x : Ω} (hx : x ∈ S.dom)
    (nat : ∀ W R : Finset (Fin L.q), RectConds P₀ S L W R → RectRep P₀ S L W R)
    (W R : Finset (Fin L.q)) (hc : RectConds P₀ S L W R) : RectRep P₀ S L W R :=
  if ho : Nonempty (KernelQuotient I.πd S.dom (GI.Pairs.OrderedPair (Fin L.q))) then
    RectRep.ordered I.πd_spec I.θ_half (rcRQo I hx ho) hc
  else if hu : Nonempty (KernelQuotient I.πd S.dom (GI.Johnson.SubsetVertex (Fin L.q) 2)) then
    RectRep.unordered I.πd_spec I.θ_half hu.some hc
  else nat W R hc

end Rep

end GI.Impl
