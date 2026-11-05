module

public import Workspace.Proved.VsQSplit1

@[expose] public section

/-!
# A split by a chain of local subspaces

A strictly decreasing chain `⊤ > V_1 > … > V_k > ⊥` of local subspaces with steps of equal
dimension, each fixed by `C = ⟨cs⟩`, gives the split of case 2: the lows are the lifts of the
`V_i` and then `W'`.

* `vsQTLows`: the lows from local bases `Qs` of `V_1, …, V_k`.
* `vsQ_splitC`: the split is correct.
-/

open Matrix

namespace GI.Proved

open GI.Impl GI.Cited Equiv

variable {I : VecStabInst}

/-- The lows of a chain of local subspaces given by bases. -/
noncomputable def vsQTLows (s : VsQSt I) (Qs : List (List (List ℕ))) : List (List (List ℕ)) :=
  Qs.map (fun Q => vsWBas I.p (vsWLift I.p I.d s.ws' (vsQCs s) Q)) ++ [s.ws']

/-- The local chain, with `⊤` in front and `⊥` at the end. -/
noncomputable def vsQTLoc (s : VsQSt I) (Qs : List (List (List ℕ))) :
    List (Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :=
  (⊤ :: Qs.map (vsWSp I.p (vsQD s))) ++ [⊥]

section

variable {s : VsQSt I} (hs : VsQStOK s)
include hs

theorem vsQTLows_sp (Qs : List (List (List ℕ))) :
    (s.ws :: vsQTLows s Qs).map (vsQSp I) = (vsQTLoc s Qs).map (vsQLift s) := by
  simp only [vsQTLows, vsQTLoc, List.map_cons, List.map_append, List.map_map, List.cons_append, List.map_nil]
  rw [vsQLift_top hs, vsQLift_bot hs]
  congr 1
  congr 1
  refine List.map_congr_left fun Q _ => ?_
  exact vsQ_bas_lift_sp hs Q

/-- **A split by a chain of local subspaces.** -/
theorem vsQ_splitC {E Tm : ℕ} {ts cs : List (Perm (Fin I.n))} {Qs : List (List (List ℕ))} {e : ℕ}
    (hQ : ∀ Q ∈ Qs, VsWFit I.p (vsQD s) Q)
    (hch : (vsQTLoc s Qs).IsChain fun a b => b < a)
    (hdim : ∀ x ∈ List.zipWith (fun (a b : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) =>
        Module.finrank (ZMod I.p) a - Module.finrank (ZMod I.p) b)
      (vsQTLoc s Qs) (vsQTLoc s Qs).tail, x = e)
    (hk : 1 ≤ Qs.length)
    (hcsl : cs.length ≤ I.n ^ 2) (hcle : gens cs ≤ gens s.hs)
    (htmem : ∀ t ∈ ts, t ∈ gens s.hs) (hcov : ∀ h ∈ gens s.hs, ∃ t ∈ ts, t⁻¹ * h ∈ gens cs)
    (htl : ts.length ≤ Tm)
    (hinv : ∀ c ∈ gens cs, ∀ Q ∈ Qs, ∀ a ∈ vsWSp I.p (vsQD s) Q, vsQLam s c *ᵥ a ∈ vsWSp I.p (vsQD s) Q)
    (hnab : ¬ s.Ab) (hts : ts.length ≤ (Qs.length + 2) ^ E) :
    VsQSplitOK s E Tm ts cs (vsQTLows s Qs) := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  have hsp := vsQTLows_sp hs Qs
  have hlen : (vsQTLows s Qs).length = Qs.length + 1 := by simp [vsQTLows]
  refine ⟨hcsl, hcle, htmem, hcov, htl, ?_, by simp [vsQTLows], ?_, ?_, ?_, Or.inr (Or.inl ⟨hnab, ?_, ?_, ?_⟩)⟩
  · -- the chain
    show List.IsChain (fun a b => vsQSp I b < vsQSp I a) (s.ws :: vsQTLows s Qs)
    rw [← List.isChain_map (vsQSp I) (R := fun A B => B < A), hsp, List.isChain_map]
    exact hch.imp fun a b h => vsQLift_lt hs h
  · simp [vsQTLows]
  · intro u hu
    simp only [vsQTLows, List.mem_append, List.mem_map, List.mem_singleton] at hu
    rcases hu with ⟨Q, hQm, rfl⟩ | rfl
    · have hfit := vsWBas_fit I.prime.pos (vsWLift_fit I.prime.pos hs.fit' (vsQCs s) Q)
      refine ⟨hfit, ?_⟩
      rw [vsWBas_length I.prime (vsWLift_fit I.prime.pos hs.fit' (vsQCs s) Q)]
      exact (Submodule.finrank_le _).trans (by simp)
    · exact ⟨hs.fit', hs.wl'⟩
  · intro u hu
    simp only [vsQTLows, List.mem_append, List.mem_map, List.mem_singleton] at hu
    rcases hu with ⟨Q, hQm, rfl⟩ | rfl
    · rw [vsQ_bas_lift_sp hs Q]
      exact vsQLift_inv hs hcle (fun c hc a ha => hinv c hc Q hQm a ha)
    · exact hs.prob.invW'.mono hcle
  · rw [hlen]; omega
  · -- equal steps
    refine ⟨e, fun x hx => ?_⟩
    have e1 : vsQDims I (s.ws :: vsQTLows s Qs) =
        List.zipWith (fun (a b : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) =>
        Module.finrank (ZMod I.p) a - Module.finrank (ZMod I.p) b)
          (vsQTLoc s Qs) (vsQTLoc s Qs).tail := by
      have e2 : vsQDims I (s.ws :: vsQTLows s Qs) = List.zipWith
          (fun (A B : Submodule (ZMod I.p) (VsQV I)) => Module.finrank (ZMod I.p) A - Module.finrank (ZMod I.p) B)
          ((s.ws :: vsQTLows s Qs).map (vsQSp I)) ((s.ws :: vsQTLows s Qs).map (vsQSp I)).tail := by
        rw [vsQDims, ← List.map_tail, List.zipWith_map]
        rfl
      rw [e2, hsp, ← List.map_tail, List.zipWith_map]
      congr 1
      funext a b
      rw [vsQLift_finrank hs, vsQLift_finrank hs]
      omega
    rw [e1] at hx
    exact hdim x hx
  · rw [hlen]; exact hts

end

end GI.Proved
