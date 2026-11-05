module

public import Workspace.Impl.AggPairs
public import Workspace.Lang.Prims.Ops

@[expose] public section

/-!
# Cited calls on graph groups

A subgroup `A ≤ G` in graph form is passed around as the group value `encGroup (qs.map encPair)`
of the encoded pairs (`GraphGV`). This file runs the cited tasks on such values.

* `exists_pairs_of_gens`: a generating list returned for a subgroup of encoded pairs consists of
  encoded pairs, and the pairs generate that subgroup. This is how outputs of the tasks are read
  back in graph form.
* `graphStab_spec`: **PointwiseStab** on the graph group (the existing module `pstabFuns`) gives
  the graph form of `A ∩ Fix(X)`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens sumToFin pointwiseStab PointwiseStab)

variable {k q : ℕ}

/-- **Reading back a generating list.** If a list `hs` generates the image of a subgroup `H` of
pairs, then `hs` is a list of encoded pairs `qs`, and `qs` generates `H`. -/
theorem exists_pairs_of_gens {H : Subgroup (Perm (Fin k) × Perm (Fin q))}
    {hs : List (Perm (Fin (k + q)))} (h : gens hs = H.map (encPairHom k q)) :
    ∃ qs : List (Perm (Fin k) × Perm (Fin q)), hs = qs.map encPair ∧
      Subgroup.closure {p | p ∈ qs} = H := by
  have hmem : ∀ x ∈ hs, ∃ p, encPair p = x := by
    intro x hx
    have : x ∈ gens hs := Subgroup.subset_closure hx
    rw [h, Subgroup.mem_map] at this
    obtain ⟨p, -, hp⟩ := this
    exact ⟨p, hp⟩
  have key : ∀ l : List (Perm (Fin (k + q))), (∀ x ∈ l, ∃ p, encPair p = x) →
      ∃ qs : List (Perm (Fin k) × Perm (Fin q)), l = qs.map encPair := by
    intro l hl
    induction l with
    | nil => exact ⟨[], rfl⟩
    | cons x l ih =>
      obtain ⟨p, hp⟩ := hl x (by simp)
      obtain ⟨qs, hqs⟩ := ih fun y hy => hl y (by simp [hy])
      exact ⟨p :: qs, by simp [hp, hqs]⟩
  obtain ⟨qs, rfl⟩ := key hs hmem
  exact ⟨qs, rfl, closure_of_gens_encPair h⟩

variable {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- **A graph group value**: the group value of encoded pairs that generate the graph of `A`. -/
def GraphGV (e : Ω ≃ Fin k) (L : GiantLabels S) (A : Subgroup (Perm Ω)) (v : Val) : Prop :=
  ∃ qs : List (Perm (Fin k) × Perm (Fin L.q)), v = encGroup (qs.map encPair) ∧ PairGens e L A qs

theorem GraphGV.groupVal {A : Subgroup (Perm Ω)} {v : Val} (h : GraphGV e L A v) :
    ∃ qs : List (Perm (Fin k) × Perm (Fin L.q)), PairGens e L A qs ∧
      GroupVal (k + L.q) v (gens (qs.map encPair)) := by
  obtain ⟨qs, rfl, hq⟩ := h
  exact ⟨qs, hq, qs.map encPair, rfl, rfl⟩

/-- **The pointwise stabilizer of positions, in graph form** (`pstabFuns`, cited task
**PointwiseStab**). -/
theorem graphStab_spec (h : PointwiseStab) {P : Program} {b jp : ℕ}
    (hb : P.HasAt b (pstabFuns b jp)) (hj : P.prims[jp]? = some (pointwiseStabPrim h))
    {A : Subgroup (Perm Ω)} {gv : Val} (hA : GraphGV e L A gv) (X : List (Fin k)) :
    FunAll P b (.list [gv, encPts (leftPts (q := L.q) X)]) (fun w c =>
      GraphGV e L (A ⊓ fixPos (e := e) X) w ∧ w.wt ≤ 320 * (k + L.q + 1) ^ 6 ∧
      c ≤ (pointwiseStabPrim h).bound (.list [gv, encPts (leftPts (q := L.q) X)]) +
        pstabK * (Val.list [gv, encPts (leftPts (q := L.q) X)]).wt ^ 9) := by
  obtain ⟨ps, hps, hG⟩ := hA.groupVal
  refine FunAll.mono (pstab_spec h hb hj hG (leftPts X)) fun w c hw => ?_
  obtain ⟨⟨hs, rfl, hgen⟩, hW, hc⟩ := hw
  refine ⟨?_, hW, hc⟩
  have hsub : pointwiseStab (gens (ps.map encPair)) (leftPts X) =
      (Subgroup.closure {p | p ∈ ps} ⊓ (fixPos (e := Equiv.refl (Fin k)) X).comap
        ((toFin (Equiv.refl (Fin k))).toMonoidHom.comp (MonoidHom.fst _ _))).map
          (encPairHom k L.q) := by
    have hrefl : ∀ a : Perm (Fin k), toFin (Equiv.refl (Fin k)) a = a := fun a => by
      ext i; simp [toFin, Equiv.permCongrHom]
    ext x
    rw [mem_pointwiseStab_pairs]
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_comap]
    constructor
    · rintro ⟨p, hp, hX, rfl⟩
      refine ⟨p, ⟨hp, fun i hi => ?_⟩, rfl⟩
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MonoidHom.coe_fst, hrefl]
      exact hX i hi
    · rintro ⟨p, ⟨hp, hX⟩, rfl⟩
      refine ⟨p, hp, fun i hi => ?_, rfl⟩
      have := hX i hi
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MonoidHom.coe_fst, hrefl] at this
      exact this
  obtain ⟨qs, rfl, -⟩ := exists_pairs_of_gens (hgen.trans hsub)
  exact ⟨qs, rfl, pairGens_fixPos hps X hgen⟩

end GI.Impl
