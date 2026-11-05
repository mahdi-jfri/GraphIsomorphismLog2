module

public import Workspace.Impl.AggSpecDefs

@[expose] public section

/-!
# The run of a round when the overcosets are known up to coset

The items return a run `Exec P₀ Ag.itemsScript ⟨pieces, ovs⟩` and their own list `os` of
overcoset values, related entrywise by `asOvAt` (`AsItemsOK`): the group of `ovs[i]` is
`π⁻¹(E₀)` of `os[i]`, and the program's representative `L.rep σ` lies in the coset of `ovs[i]`.
The model fixes some representatives by a classical choice, so the program cannot return them.
The paper fixes only the coset (`Run.aggregate` takes any `τ_j ∈ ρ_j • H_j`), so this is enough.

This file restates the three facts that `as_agg_spec` uses about the overcosets for such a pair
`(os, ovs)`:
* `it_ov_coset`: the coset of `os[i]` is the coset of `ovs[i]`;
* `it_child_good_mlt`: a continuation on an overcoset of `os` is an allowed call
  (as `as_child_good_mlt`; it uses only the group of the overcoset);
* `it_run`, `it_union`: the run of the round and the union of the pieces (as `ab_run`,
  `ab_union`, with `ovs` in place of `os.map abOv`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-- **The two cosets agree**: if `o` stands for `ov`, then `L.rep σ • π⁻¹(E₀) = ov.1 • ov.2`. -/
theorem it_ov_coset {S : State Ω C} {L : GiantLabels S} {o : LcOver L.q}
    {ov : Perm Ω × Subgroup (Perm Ω)} (h : asOvAt L o ov) :
    L.rep o.1 • (L.lift o.2.1 : Set (Perm Ω)) = ov.1 • (ov.2 : Set (Perm Ω)) := by
  obtain ⟨h2, x, hx, hxe⟩ := h
  rw [← h2, ← hxe]
  simp only [smul_eq_mul]
  rw [mul_smul, leftCoset_mem_leftCoset _ hx]

/-- The entries of two lists related by `asOvAt`. -/
theorem it_forall₂_get {S : State Ω C} {L : GiantLabels S} {os : List (LcOver L.q)}
    {ovs : List (Perm Ω × Subgroup (Perm Ω))} (h : List.Forall₂ (asOvAt L) os ovs) :
    os.length = ovs.length ∧ ∀ i (h1 : i < os.length) (h2 : i < ovs.length),
      asOvAt L os[i] ovs[i] := by
  obtain ⟨hl, hg⟩ := List.forall₂_iff_get.1 h
  exact ⟨hl, fun i h1 h2 => hg i h1 h2⟩

/-- Every entry of `os` stands for an entry of `ovs`. -/
theorem it_forall₂_mem {S : State Ω C} {L : GiantLabels S} {os : List (LcOver L.q)}
    {ovs : List (Perm Ω × Subgroup (Perm Ω))} (h : List.Forall₂ (asOvAt L) os ovs)
    {o : LcOver L.q} (ho : o ∈ os) : ∃ ov ∈ ovs, asOvAt L o ov := by
  obtain ⟨hl, hg⟩ := it_forall₂_get h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
  exact ⟨ovs[i], List.getElem_mem (by omega), hg i hi (by omega)⟩

/-- **A continuation of the round may be made** (as `as_child_good_mlt`), for an overcoset `ov`
of the round's exact result whose group is `π⁻¹(E₀)`. The representative of `ov` is not used:
the child's group is `π⁻¹(E₀)` and the new hierarchy `newHier` does not depend on the
overcoset. -/
theorem it_child_good_mlt [Finite Ω] {S : State Ω C} (hgood : Good P₀ .giant S)
    (L : SuppliedLabels S) (hq₀ : P₀.q₀ ≤ L.q) (Ag : Aggregation P₀ S L.toGiantLabels)
    (hsel : Ag.sel.val = L.sel.val) (o : LcOver L.q) (ov : Perm Ω × Subgroup (Perm Ω))
    (hov : ov ∈ Ag.script.evalExact.overs) (h2 : ov.2 = L.lift o.2.1) (τ : Perm Ω) :
    Good P₀ .cont (lcChild S o.2.1 τ L.sel (abCap L.toGiantLabels)) ∧
      MLt (measure P₀ .cont (lcChild S o.2.1 τ L.sel (abCap L.toGiantLabels)))
        (measure P₀ .giant S) := by
  obtain ⟨hN, hsN, htr, hth, hhi, -⟩ := hgood
  have hP := P₀_terminating
  have hκ := hP.κ_five
  have htr1 := trInd_of S htr
  set child := lcChild S o.2.1 τ L.sel (abCap L.toGiantLabels) with hchild
  have hhier : child.hier = Ag.newHier ov := by
    rw [hchild, lcChild_hier, ← hsel]
    exact lcHier_eq_newHier S Ag _
  have hinv : child.HierInv := by
    show HierInv child.G child.dom child.hier
    rw [hhier]
    have h := Ag.child_hierInv hsel hhi hov
    rw [h2] at h
    exact h
  refine ⟨⟨hN, hsN, hinv⟩, ?_⟩
  have hcu := Ag.capUpdate ov hov
  have hσ : child.sigma P₀.κ ≤ S.sigma P₀.κ :=
    State.sigma_le_of hκ (L.toGiantLabels.lift_le o.2.1) le_rfl
  have hρ : rhoNat child.hier = rhoNat S.hier := by
    rw [hhier]
    have h1 : (rhoNat (Ag.newHier ov) : ℝ) = rhoNat S.hier := by
      rw [rhoNat_cast, rhoNat_cast]; exact hcu.rho_eq
    exact_mod_cast h1
  have hc := hcu.capSum_lt hP.β_lt (Nat.lt_of_lt_of_le hP.q₀_pos hq₀)
  have htrj := trInd_le child
  rw [mlt_iff]
  simp only [Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
  have h1 : child.size = S.size := rfl
  have hk := lc_keep S L.con o.2.1 L.sel (abCap L.toGiantLabels)
  have hfl : child.floor = S.floor := State.restrict_floor_of _ _ _ _ _ _ hk
  have h3 : flInd child = flInd S := by simp only [flInd, hfl]
  have h4 : child.h = S.h := State.restrict_h_of _ _ _ _ _ _ hk
  have h5 : capSum child.hier = capSum (Ag.newHier ov) := by rw [hhier]
  have hNc : child.N = S.N := rfl
  omega

/-- **The run of the round** (as `ab_run`), with the overcosets `ovs` of the script related to the
program's list `os` by `asOvAt`. The run takes, for the `j`-th overcoset, a `τ_j` in the coset of
`os[j]`, which is the coset of `ovs[j]` (`it_ov_coset`). -/
theorem it_run (I : Iface) {S : State Ω C}
    (hs : (S.N : ℝ) ^ P₀.γ < S.size) (htr : S.Transitive)
    (L : SuppliedLabels S) (hnot : ¬ RowCase P₀.α S L.toGiantLabels) (hq₀ : P₀.q₀ ≤ L.q)
    (Ag : Aggregation P₀ S L.toGiantLabels) (hsel : Ag.sel.val = L.sel.val) (hcon : Ag.con = L.con)
    (pieces : List (Set (Perm Ω))) (os : List (LcOver L.q))
    (ovs : List (Perm Ω × Subgroup (Perm Ω))) (hR : List.Forall₂ (asOvAt L.toGiantLabels) os ovs)
    (ex : Exec P₀ Ag.script ⟨pieces, ovs⟩) (cs : ℕ → ℕ)
    (hrun : ∀ i (hi : i < os.length),
      ∃ τ ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)), ∃ (A : Set (Perm Ω))
        (r : Run P₀ .cont (lcChild S os[i].2.1 τ Ag.sel (abCap L.toGiantLabels)) none A),
          (cs i : ℝ) ≤ r.total I.work) :
    ∃ (A : Set (Perm Ω)) (r : Run P₀ .giant S (some L) A), r.kind = .aggregate ∧
      I.execCost ex + ∑ i ∈ Finset.range os.length, (cs i : ℝ) ≤ I.childCost r := by
  choose τ hτ A r hcs using hrun
  obtain ⟨hl, hg⟩ := it_forall₂_get hR
  let b : Branches Ω := ⟨pieces, ovs⟩
  have hlen : b.overs.length = os.length := hl.symm
  let τ' : Fin b.overs.length → Perm Ω := fun j => τ j (by have := j.2; omega)
  have hτ' : ∀ j, τ' j ∈ (b.overs.get j).1 • ((b.overs.get j).2 : Set (Perm Ω)) := fun j => by
    have h := hτ j (by have := j.2; omega)
    rw [it_ov_coset (hg j _ j.2)] at h
    exact h
  let child : Fin b.overs.length → State Ω C := fun j =>
    lcChild S (os[(j : ℕ)]'(by have := j.2; omega)).2.1 (τ' j) Ag.sel (abCap L.toGiantLabels)
  have hchild : ∀ j, (child j).Inst (b.overs.get j).2 S.dom S.x (S.y ∘ τ' j) := fun j => by
    have h := (hg j (by have := j.2; omega) j.2).1
    show (child j).Inst ovs[(j : ℕ)].2 S.dom S.x (S.y ∘ τ' j)
    rw [h]; exact lcChild_inst S _ _ _ _
  have hhier : ∀ j, (child j).hier = Ag.newHier (b.overs.get j) := fun j => by
    rw [lcChild_hier]; exact lcHier_eq_newHier S Ag _
  have hbk : ∀ j, (child j).book = S.book := fun j => by
    exact lcChild_book S Ag.con _ _ _ _
  let A' : Fin b.overs.length → Set (Perm Ω) := fun j => A j (by have := j.2; omega)
  let r' : ∀ j, Run P₀ .cont (child j) none (A' j) := fun j => r j (by have := j.2; omega)
  refine ⟨_, Run.aggregate hs htr L hnot hq₀ Ag hsel hcon b ex τ' hτ' child hchild
    (fun j => lcChild_N S _ _ _ _) hhier hbk A' r', rfl, ?_⟩
  rw [Iface.childCost_aggregate]
  refine add_le_add le_rfl ?_
  rw [List.sum_ofFn, ← Fin.sum_univ_eq_sum_range (fun i => (cs i : ℝ)) os.length]
  rw [← Fin.sum_congr' (fun i => (cs i : ℝ)) hlen]
  exact Finset.sum_le_sum fun j _ => hcs j _

/-- **The pieces of the round cover the parent answer** (as `ab_union`), with the overcosets
`ovs` of the script related to the program's list `os` by `asOvAt`. -/
theorem it_union (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S} {P : Params}
    (Ag : Aggregation P S L) (pieces : List (Set (Perm Ω))) (os : List (LcOver L.q))
    (ovs : List (Perm Ω × Subgroup (Perm Ω))) (hR : List.Forall₂ (asOvAt L) os ovs)
    (ex : Exec P Ag.script ⟨pieces, ovs⟩) (cap : ℕ)
    (pcs : List (Perm (Fin k) × Acc k)) (hl : pcs.length = pieces.length)
    (hp : ∀ i (h1 : i < pcs.length) (h2 : i < pieces.length), ceSet pcs[i] = toFin e '' pieces[i])
    (cps : List (Perm (Fin k) × Acc k)) (hcl : cps.length = os.length)
    (hc : ∀ i (h1 : i < cps.length) (h2 : i < os.length),
      (toFin e).symm cps[i].1 ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)) ∧
      ceSet cps[i] = toFin e '' ((toFin e).symm cps[i].1 •
        (lcChild S os[i].2.1 ((toFin e).symm cps[i].1) Ag.sel cap).answer)) :
    unionSet (pcs ++ cps) = toFin e '' S.answer := by
  obtain ⟨hol, hg⟩ := it_forall₂_get hR
  let b : Branches Ω := ⟨pieces, ovs⟩
  have hcov : Branches.Covers S b := by
    have h := Ag.covers
    rwa [← ex.exact] at h
  have hlen : b.overs.length = os.length := hol.symm
  let τ : Fin b.overs.length → Perm Ω := fun j => (toFin e).symm (cps[(j : ℕ)]'(by
    have := j.2; omega)).1
  let child : Fin b.overs.length → State Ω C := fun j =>
    lcChild S (os[(j : ℕ)]'(by have := j.2; omega)).2.1 (τ j) Ag.sel cap
  have hτ : ∀ j, τ j ∈ (b.overs.get j).1 • ((b.overs.get j).2 : Set (Perm Ω)) := fun j => by
    have h := (hc j (by have := j.2; omega) (by have := j.2; omega)).1
    rw [it_ov_coset (hg j _ j.2)] at h
    exact h
  have hchild : ∀ j, (child j).Inst (b.overs.get j).2 S.dom S.x (S.y ∘ τ j) := fun j => by
    have h := (hg j (by have := j.2; omega) j.2).1
    show (child j).Inst ovs[(j : ℕ)].2 S.dom S.x (S.y ∘ τ j)
    rw [h]; exact lcChild_inst S _ _ _ _
  have hans := step_aggregate b hcov τ hτ child hchild (fun j => (child j).answer) fun _ => rfl
  rw [← hans]
  exact ce_union e pieces pcs hl hp τ (fun j => (child j).answer) cps (by omega)
    fun j h => (hc j h (by have := j.2; omega)).2

end GI.Impl
