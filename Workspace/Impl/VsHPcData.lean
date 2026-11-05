module

public import Workspace.Impl.VsHPcList
public import Workspace.Proved.VsHChainMath

@[expose] public section

/-!
# The data of a pieces split

From `VsMPiecesOut H̄ (𝔽_p[A ∪ ρ gs]) m bound`, the pieces `Ps = vsFEigL p D Fx` computed from the
stored local matrices of `as ++ gs` are `m` independent nonzero subspaces of equal dimension that
span everything, and the orbit of the tuple of pieces under `⟨hs⟩` has at most `bound` points
(`vsH_split_data`).
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-- The pieces of `𝔽_p[Λ(L)]`. -/
noncomputable def vsHPs (s : VsQSt I) (L : List (Perm (Fin I.n))) : List (List (List ℕ)) :=
  vsFEigL I.p (vsQD s) (vsHFx s L)

theorem vsHFx_sq (L : List (Perm (Fin I.n))) : ∀ x ∈ vsHFx s L, VsWSq I.p (vsQD s) x := by
  intro x hx
  unfold vsHFx at hx
  simp only [vsFFixL, List.mem_map] at hx
  obtain ⟨a, -, rfl⟩ := hx
  exact vsWMC_sq I.prime.pos _ a

/-- The algebra `𝔽_p[A ∪ ρ gs]` is commutative when the generators commute. -/
theorem vsH_algE_comm (hs : VsQStOK s) {as gs : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs)
    (hgs : ∀ g ∈ gs, g ∈ gens s.hs)
    (hc : ∀ x ∈ as ++ gs, ∀ y ∈ as ++ gs, vsPRho hs x * vsPRho hs y = vsPRho hs y * vsPRho hs x) :
    ∀ x ∈ vsMAlgE (vsPBar hs (gens as)) (vsHEf hs gs),
      ∀ y ∈ vsMAlgE (vsPBar hs (gens as)) (vsHEf hs gs), Commute x y := by
  have hL : ∀ x ∈ as ++ gs, x ∈ gens s.hs := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact has (Subgroup.subset_closure hx)
    · exact hgs x hx
  rw [vsH_algE_eq hs has hgs]
  have hG : ∀ u ∈ vsPBar hs (gens (as ++ gs)), ∀ v ∈ vsPBar hs (gens (as ++ gs)), u * v = v * u := by
    rw [vsPBar_gens hs hL]
    refine vsH_closure_comm ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hc x hx y hy
  intro x hx y hy
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb => ?_
  obtain ⟨v, hv, rfl⟩ := hb
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun a ha => ?_).symm
  obtain ⟨u, hu, rfl⟩ := ha
  show Commute (v : Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) u
  unfold Commute SemiconjBy; rw [← Units.val_mul, ← Units.val_mul, hG v hv u hu]

/-- **The data of a pieces split.** -/
theorem vsH_split_data (hs : VsQStOK s) {as gs : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs)
    (hgs : ∀ g ∈ gs, g ∈ gens s.hs)
    (hc : ∀ x ∈ as ++ gs, ∀ y ∈ as ++ gs, vsPRho hs x * vsPRho hs y = vsPRho hs y * vsPRho hs x)
    {m bound : ℕ}
    (hP : VsMPiecesOut (vsPBar hs (gens s.hs)) (vsMAlgE (vsPBar hs (gens as)) (vsHEf hs gs)) m bound) :
    let Ps := vsHPs s (as ++ gs)
    (∀ P ∈ Ps, VsWFit I.p (vsQD s) P) ∧ Ps.length = m ∧
      (iSupIndep fun i : Fin Ps.length => vsWSp I.p (vsQD s) Ps[i]) ∧
      (∃ e, 0 < e ∧ ∀ i : Fin Ps.length, finrank (ZMod I.p) (vsWSp I.p (vsQD s) Ps[i]) = e) ∧
      (⨆ i : Fin Ps.length, vsWSp I.p (vsQD s) Ps[i]) = ⊤ ∧
      (vsQOrb (vsQTAct s) s.hs (Ps.map (vsWSp I.p (vsQD s)))).ncard ≤ bound := by
  intro Ps
  have hFx := vsHFx_sq (s := s) (as ++ gs)
  obtain ⟨hfB, hfp, hfs⟩ := vsH_fix_family hs has hgs hc
  have hB := vsH_algE_comm hs has hgs hc
  obtain ⟨a, hinj, ha, hsurj, hlen⟩ := vsH_pieces hFx _ hB hfB hfp
  set f := fun i : Fin (vsHFx s (as ++ gs)).length => vsWLin I.p (vsQD s) (vsHFx s (as ++ gs))[i]
  obtain ⟨hcount, hdim, hstab⟩ := hP.2 f hfB hfp hfs
  have hfit : ∀ P ∈ Ps, VsWFit I.p (vsQD s) P := fun P hP' =>
    ((vsFEigL_pieces I.prime _ hFx).1 P hP').1
  have hind0 := vsFEig_indep _ hB f hfB hfp
  have hindP : iSupIndep fun i : Fin Ps.length => vsWSp I.p (vsQD s) Ps[i] := by
    have e : (fun i : Fin Ps.length => vsWSp I.p (vsQD s) Ps[i]) = fun i => vsFEig f (a i) :=
      funext fun i => (ha i).1
    rw [e]
    show iSupIndep ((fun b => vsFEig f b) ∘ a)
    exact iSupIndep.comp hind0 hinj
  refine ⟨hfit, hlen.trans hcount, hindP, ?_, ?_, ?_⟩
  · by_cases h0 : Ps.length = 0
    · exact ⟨1, one_pos, fun i => absurd i.2 (by omega)⟩
    · have hi0 : 0 < Ps.length := Nat.pos_of_ne_zero h0
      have e0 : vsWSp I.p (vsQD s) Ps[0] = vsFEig f (a ⟨0, hi0⟩) := (ha ⟨0, hi0⟩).1
      refine ⟨finrank (ZMod I.p) (vsWSp I.p (vsQD s) Ps[0]), ?_, fun i => ?_⟩
      · rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero, e0]
        exact (ha ⟨0, hi0⟩).2
      · have h1 := congrArg (fun U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p) =>
          finrank (ZMod I.p) U) (ha i).1
        have h2 := congrArg (fun U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p) =>
          finrank (ZMod I.p) U) e0
        exact h1.trans ((hdim (a i) (a ⟨0, hi0⟩) (ha i).2 (ha ⟨0, hi0⟩).2).trans h2.symm)
  · rw [eq_top_iff, ← vsFEig_iSup _ hB f hfB hfp]
    refine iSup_le fun b => ?_
    by_cases hb : vsFEig f b = ⊥
    · rw [hb]; exact bot_le
    · obtain ⟨i, rfl⟩ := hsurj b hb
      rw [← (ha i).1]
      exact le_iSup (fun i : Fin Ps.length => vsWSp I.p (vsQD s) Ps[i]) i
  · refine (vsH_tup_orbit hs (X := fun b : {b // vsFEig f b ≠ ⊥} => vsFEig f b.1)
      fun U hU => ?_).trans hstab
    obtain ⟨P, hP', rfl⟩ := List.mem_map.1 hU
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hP'
    exact ⟨⟨a ⟨i, hi⟩, (ha ⟨i, hi⟩).2⟩, (ha ⟨i, hi⟩).1⟩

end GI.Impl
