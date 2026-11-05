module

public import Workspace.Proved.VsPStep4Math
public import Workspace.Impl.VsPCtxP

@[expose] public section

/-!
# The dimension of `L` is the number of echelon rows

`dim 𝔽_p[Ā] = |vsPRows p Lb|` (`vsH_finrank_L`): the rows are an echelon basis of the flattened
`Lb`, which spans the transposed algebra (`hspan`).
-/

open Matrix

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ}

/-- The flattening to `Fin (D * D)`. -/
noncomputable def vsHFlat (p D : ℕ) : Matrix (Fin D) (Fin D) (ZMod p) →ₗ[ZMod p] (Fin (D * D) → ZMod p) :=
  (vsWR p (D * D)).comp (vsPFlat p D)

theorem vsHFlat_inj (D : ℕ) : Function.Injective (vsHFlat p D) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro M hM
  ext i j
  have hD : 0 < D := Nat.pos_of_ne_zero fun h => by subst h; exact i.elim0
  have hk : (i : ℕ) * D + j < D * D := by
    have := i.2; have := j.2; nlinarith
  have := congrFun hM ⟨(i : ℕ) * D + j, hk⟩
  simp only [vsHFlat, LinearMap.comp_apply, vsWR_apply, vsPFlat, LinearMap.coe_mk, AddHom.coe_mk,
    dif_pos hk, Pi.zero_apply] at this
  have e1 : ((i : ℕ) * D + j) / D = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt j.2, zero_add]
  have e2 : ((i : ℕ) * D + j) % D = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]
  simp only [e1, e2] at this
  simpa using this

theorem vsH_finrank_map_inj {K M M' : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup M'] [Module K M'] (f : M →ₗ[K] M') (hf : Function.Injective f)
    (X : Submodule K M) : finrank K (X.map f) = finrank K X :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf X)).symm

variable [hp : Fact p.Prime]

/-- `dim span(Lb) = |rows|`. -/
theorem vsH_finrank_span {D : ℕ} {Lb : List (List (List ℕ))} (hLb : ∀ M ∈ Lb, VsFSq p D M) :
    finrank (ZMod p) (vsFMatSpan p D Lb) = (vsPRows p Lb).length := by
  have hfit : VsWFit p (D * D) (Lb.map List.flatten) := by
    intro u hu
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hu
    exact ⟨vsFA_flatten_lt fun r hr => ((hLb M hM).rows r hr).1,
      by rw [vsFA_flatten_length fun r hr => ((hLb M hM).rows r hr).2, (hLb M hM).len]⟩
  rw [← vsH_finrank_map_inj _ (vsHFlat_inj (p := p) D)]
  have hmap : (vsFMatSpan p D Lb).map (vsHFlat p D) = vsWSp p (D * D) (Lb.map List.flatten) := by
    rw [vsFMatSpan, Submodule.map_span, vsWSp]
    congr 1
    ext v
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_map]
    constructor
    · rintro ⟨_, ⟨M, hM, rfl⟩, rfl⟩
      refine ⟨M.flatten, ⟨M, hM, rfl⟩, ?_⟩
      simp only [vsHFlat, LinearMap.comp_apply, vsPFlat_matrix (hLb M hM), vsWV]
    · rintro ⟨_, ⟨M, hM, rfl⟩, rfl⟩
      refine ⟨vsFMatrix p D M, ⟨M, hM, rfl⟩, ?_⟩
      simp only [vsHFlat, LinearMap.comp_apply, vsPFlat_matrix (hLb M hM), vsWV]
  rw [hmap, ← vsWBas_span hp.out hfit, vsWSp]
  have hind := vsWBas_indep hp.out hfit
  have hset : {v | ∃ u ∈ vsWBas p (Lb.map List.flatten), vsWV p (D * D) u = v} =
      Set.range fun i : Fin (vsWBas p (Lb.map List.flatten)).length =>
        vsWV p (D * D) (vsWBas p (Lb.map List.flatten))[i] := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, List.getElem_mem i.2, rfl⟩
  rw [hset, finrank_span_eq_card hind, Fintype.card_fin]
  simp [vsWBas, vsPRows]

variable {I : VecStabInst} {s : VsQSt I}

/-- **`dim L = |rows|`.** -/
theorem vsH_finrank_L [Fact I.p.Prime] (hs : VsQStOK s) {as : List (Perm (Fin I.n))}
    (has : gens as ≤ gens s.hs) {Lb : List (List (List ℕ))}
    (hLb : ∀ M ∈ Lb, VsFSq I.p (vsQD s) M)
    (hspan : vsFMatSpan I.p (vsQD s) Lb = Subalgebra.toSubmodule
      (vsFAlgOf I.p (vsQD s) (as.map (vsPLocL I s.ws' (vsQCs s))))) :
    finrank (ZMod I.p) (vsTAlg (vsPBar hs (gens as))) = (vsPRows I.p Lb).length := by
  rw [← vsH_finrank_span hLb, hspan]
  set B := Algebra.adjoin (ZMod I.p) {X | ∃ a ∈ as, vsQLam s a = X}
  -- `vsTAlg Ā` is the image of `B` under `toLin'`
  have h1 : Subalgebra.toSubmodule (vsTAlg (vsPBar hs (gens as))) =
      (Subalgebra.toSubmodule B).map
        (Matrix.toLin' : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p) ≃ₗ[ZMod I.p] _).toLinearMap := by
    ext X
    simp only [Subalgebra.mem_toSubmodule, Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · intro hX
      refine ⟨LinearMap.toMatrix' X, ?_, Matrix.toLin'_toMatrix' X⟩
      rw [← vsP_mem_vsTAlg_iff hs has, Matrix.toLin'_toMatrix']
      exact hX
    · rintro ⟨M, hM, rfl⟩
      exact (vsP_mem_vsTAlg_iff hs has M).2 hM
  -- the transposed algebra
  have h2 : Subalgebra.toSubmodule (vsFAlgOf I.p (vsQD s) (as.map (vsPLocL I s.ws' (vsQCs s)))) =
      (Subalgebra.toSubmodule B).map
        ((Matrix.transposeLinearEquiv (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p) (ZMod I.p)).toLinearMap) := by
    have hset : {X | ∃ g ∈ as.map (vsPLocL I s.ws' (vsQCs s)), vsFMatrix I.p (vsQD s) g = X} =
        Matrix.transpose '' {X | ∃ a ∈ as, vsQLam s a = X} := by
      ext X
      simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_image]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨vsQLam s a, ⟨a, ha, rfl⟩, (vsFMatrix_loc a).symm⟩
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨_, ⟨a, ha, rfl⟩, vsFMatrix_loc a⟩
    ext X
    simp only [Subalgebra.mem_toSubmodule, Submodule.mem_map, LinearEquiv.coe_coe,
      Matrix.transposeLinearEquiv_apply]
    rw [vsFAlgOf, hset]
    constructor
    · intro hX
      refine ⟨Xᵀ, ?_, Matrix.transpose_transpose X⟩
      rw [← vsP_adjoin_transpose, Matrix.transpose_transpose]; exact hX
    · rintro ⟨M, hM, rfl⟩
      exact vsP_adjoin_transpose.2 hM
  have e1 : finrank (ZMod I.p) (vsTAlg (vsPBar hs (gens as))) =
      finrank (ZMod I.p) (Subalgebra.toSubmodule (vsTAlg (vsPBar hs (gens as)))) := rfl
  rw [e1, h1, h2, vsH_finrank_map_inj _ (Matrix.toLin' : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p) ≃ₗ[ZMod I.p] _).injective,
    vsH_finrank_map_inj _ (Matrix.transposeLinearEquiv (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)
      (ZMod I.p)).injective]

end GI.Proved
