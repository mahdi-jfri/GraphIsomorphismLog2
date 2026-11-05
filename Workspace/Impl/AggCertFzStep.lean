module

public import Workspace.Impl.AggCertFzOut

@[expose] public section

/-!
# The graph forms of the certificate groups: one test set

`cp_fz_step`: the step `cpFzStepE` of the loop over the test sets keeps the invariant `CpFzInv`.
After `i` test sets, the list of pairs is a list of positions of elements of `G` whose first parts
generate `cpFzGrp … i`: the lift of `G_(dom)` and of the full certificates of the full test sets
among the first `i`.

The step reads the final group `pz` of the string from the results and the log from the logs, and
computes the points outside the final window (`cp_fz_out`). It then tests whether `T` is full:
`imgCardDet` with no fixed points gives `|φ_T(A_final)|`, and `T` is full when this is
`|Alt(T)| = D` (`cp_isFull_iff`). Only then does it compute the graph form of `K(T)`
(`cp_bud_stabP`, `cp_pairGens_full`) and append it.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

section Bud

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) {Pg : Program}

/-- **The graph form of a pointwise stabilizer, within the budget**, for any points. -/
theorem cp_bud_stabP {k q b jp : ℕ} (hb : Pg.HasAt b (graphStabFuns b jp))
    (hj : Pg.prims[jp]? = some (pointwiseStabPrim hst)) {ps : GPairs k q}
    (hpl : ps.length ≤ (k + q) ^ 2) {X : List (Fin (k + q))} (hX : X.length ≤ k + q) {W : ℕ}
    (hW : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W) :
    CpFB Pg b (.list [.list [.nat k, .nat q], gpV ps, encPts X]) W (cpG hst hpre hm W)
      (fun w => ∃ qs : GPairs k q, w = gpV qs ∧ qs.length ≤ (k + q) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓ fixPts k q X) := by
  have h := graphStabP_spec hst hb hj ps X
  obtain ⟨f1, f2, -, f24, f46, -, -, -, f9, -⟩ := cp_pow_facts k q
  have w6 : (k + q + 1) ^ 6 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  refine FunAll.mono h ?_
  rintro w cw ⟨ns, rfl, hl, hcl, hc⟩
  refine ⟨⟨ns, rfl, hl, hcl⟩, ?_, ?_⟩
  · have := cp_wt_gp (k := k) (q := q) hl
    unfold gpV at this
    omega
  · have h1 := stabBound_le hst ps X 0 0
    set M := imgM k q ps X 0 0 with hM
    have hMW : 2 * M ≤ W := by
      have : M ≤ 22 * (k + q + 1) ^ 2 := by rw [hM]; unfold imgM; omega
      omega
    have h4 : (2 * M) ^ 4 ≤ W ^ 4 := Nat.pow_le_pow_left hMW 4
    have e4 : (2 * M) ^ 4 = 16 * M ^ 4 := by ring
    have h2 := boundSize_mono (pointwiseStabPrim hst) (B := 200 * M ^ 4) (B' := 100 * W ^ 4)
      (by omega)
    have hs : stabPM k q ps X ≤ W + 1 := by unfold stabPM; omega
    have h3 : graphStabK * stabPM k q ps X ^ 8 ≤ graphStabK * (W + 1) ^ 8 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 8)
    have h5 := cp_poly_le (W := W) (K := graphStabK) (d := 8) (by simp [graphStabK])
      (by norm_num) (by omega)
    unfold cpG
    omega

/-- **The order of the image, within the budget.** -/
theorem cp_bud_card {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
    {L : GiantLabels S} {πd : S.domGroup →* alternatingGroup (Fin L.q)} {b jp : ℕ}
    (hb : Pg.HasAt b (imgCardFuns b jp)) (hj : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
    {T : Finset (Fin L.q)} {A : Subgroup (Perm S.dom)} (hA : A ≤ Pgrp S.domGroup πd T)
    {ps : GPairs k L.q} (hps : PairGens e L (S.liftGroup A) ps)
    (hpl : ps.length ≤ (k + L.q) ^ 2) {D : ℕ} (hD : Nat.card (alternatingGroup T) ≤ D) {W : ℕ}
    (hW : 10 ^ 10 * (k + L.q + 1) ^ 12 + D ≤ W) :
    FunDet Pg b (.list [.list [.nat k, .nat L.q], gpV ps, .list [],
      natList (ptsKey (labPts k (tlist T))), .nat D])
      (.nat (cardFix (phiT S.domGroup πd T) A ∅)) (cpG hst hpre hm W) := by
  have hT : T.card ≤ L.q := (Finset.card_le_univ T).trans (by simp)
  have hM : imgM k L.q ps ([] : List (Fin (k + L.q))) D T.card ≤ 2 * W := by
    obtain ⟨f1, f2, -, -, -, -, -, -, f9, -⟩ := cp_pow_facts k L.q
    have : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
    unfold imgM; simp only [List.length_nil]; omega
  refine (imgCardDet πd hst hb hj hπ hA hps (U := ∅) (X := [])
    (fun j => by simp) hD hM).mono ?_
  have h1 := cardCost_mono hst (show 2 * W ≤ 2 * W from le_rfl)
  have h2 := cpG_card hst hpre hm (W := W)
  have h3 : cardCost hst (2 * W) ≤ (2 * W + 2) * cardCost hst (2 * W) :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

end Bud

/-! ### The input of the program -/

section In

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] (e : Ω ≃ Fin k) (S : State Ω C) [Fintype S.dom]
  (L : GiantLabels S) (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- One of two things: the first for `s = 0`, the second otherwise. -/
def cpSel {α : Type} (s : ℕ) (a b : α) : α := if s = 0 then a else b

/-- **The output of the runner**, as the program reads it: the results and the logs of `CpOut`. -/
structure CpFzIn (res : List (GPairs k L.q × GPairs k L.q))
    (logs : List (Finset (Fin L.q) × List (CpStgD k L.q) × List (CpStgD k L.q))) : Prop where
  rel : List.Forall₂ (fun (l : Finset (Fin L.q) × List (CpStgD k L.q) × List (CpStgD k L.q))
      (p : GPairs k L.q × GPairs k L.q) =>
        PairGens e L (S.liftGroup (grp (cpPhi S πd l.1) (dstr S S.x) (Fintype.card S.dom))) p.1 ∧
        PairGens e L (S.liftGroup (grp (cpPhi S πd l.1) (dstr S S.y) (Fintype.card S.dom))) p.2)
      logs res
  lens : ∀ r ∈ res, r.1.length ≤ (k + L.q) ^ 2 ∧ r.2.length ≤ (k + L.q) ^ 2
  stgs : ∀ l ∈ logs, CpStgs e πd l.1 S.x l.2.1 ∧ CpStgs e πd l.1 S.y l.2.2
  lglen : ∀ l ∈ logs, CpLgLen l.2.1 ∧ CpLgLen l.2.2
  ord : ∃ O : TestSetOrder L.q P₀.κ, logs.map Prod.fst = O.sets

/-- The value of the output of the runner. -/
noncomputable def cpOutV {q : ℕ} (res : List (GPairs k q × GPairs k q))
    (logs : List (Finset (Fin q) × List (CpStgD k q) × List (CpStgD k q))) : Val :=
  .list [.list (res.map resV), .list (logs.map cpLogV)]

/-- **The invariant of the loop over the test sets.** -/
def CpFzInv (logs : List (Finset (Fin L.q) × List (CpStgD k L.q) × List (CpStgD k L.q)))
    (z : Ω → C) (i : ℕ) (acc : Val) : Prop :=
  ∃ qs : GPairs k L.q, acc = gpV qs ∧ qs.length ≤ (i + 1) * (k + L.q) ^ 2 ∧
    (∀ p ∈ qs, ∃ g ∈ S.G, toFin e g = p.1) ∧
    gens (qs.map Prod.fst) = cpFzGrp (e := e) πd (logs.map Prod.fst) z i

theorem CpFzIn.length {res : List (GPairs k L.q × GPairs k L.q)}
    {logs : List (Finset (Fin L.q) × List (CpStgD k L.q) × List (CpStgD k L.q))}
    (h : CpFzIn e S L πd res logs) : res.length = logs.length :=
  h.rel.length_eq.symm

end In

end GI.Impl
