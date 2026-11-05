module

public import Workspace.Impl.VsWAlgDefs
public import Workspace.Proved.VsWLinMath
public import Workspace.Proved.VsFAlgSpanMath
public import Workspace.Proved.VsFAlgPiece

@[expose] public section

/-!
# The Frobenius map on a span of matrices

Let `Bm` be a list of stored `D × D` matrices, with matrices `M_i = vsWM p D Bm_i` that commute.
On their span, `x ↦ x ^ p` is linear: `(∑ c_i M_i) ^ p = ∑ c_i M_i ^ p`, because `c ^ p = c` in
`ZMod p`. So `x ^ p = 0` and `x ^ p = x` are linear conditions on the coefficients `c`, and the
relations among the flattened `M_i ^ p` (or `M_i ^ p - M_i`) give spanning lists.

* `vsWMC_matrix`: the stored combination `vsWMC p D Bm a` is `∑ a_i M_i`.
* `vsFNilL_span`: `x` is in the span of `vsFNilL p D Bm` iff `x` is in the span of `Bm` and
  `x ^ p = 0`.
* `vsFFixL_span`: the same with `x ^ p = x`.
* `vsFAnnL_span`: `vsFAnnL p D Ys` spans the common kernel of the `Ys`.
* `vsFAnnL_nil`: with `Ys = vsFNilL p D Bm`, this is `vsFAnn B` for the algebra `B` of linear
  maps of the span of `Bm` (only this last result and the two span results are used later).
-/

namespace GI.Proved

open GI.Impl

variable {p : ℕ}

/-! ### Combinations of matrices -/

/-- The combination `c ↦ ∑_{i < n} c_i M_i` of the matrices of the list. -/
noncomputable def vsWPhi (p D : ℕ) (Bm : List (List (List ℕ))) :
    (ℕ → ZMod p) →ₗ[ZMod p] Matrix (Fin D) (Fin D) (ZMod p) :=
  ∑ i ∈ Finset.range Bm.length,
    (LinearMap.proj i : (ℕ → ZMod p) →ₗ[ZMod p] ZMod p).smulRight (vsWM p D (Bm.getD i []))

theorem vsWPhi_apply (D : ℕ) (Bm : List (List (List ℕ))) (c : ℕ → ZMod p) :
    vsWPhi p D Bm c = ∑ i ∈ Finset.range Bm.length, c i • vsWM p D (Bm.getD i []) := by
  simp [vsWPhi, LinearMap.sum_apply]

theorem vsWMC_matrix {D : ℕ} {Bm : List (List (List ℕ))} (hB : ∀ M ∈ Bm, VsWSq p D M)
    (a : List ℕ) : vsWM p D (vsWMC p D Bm a) = vsWPhi p D Bm (vsF p a) := by
  rw [vsWPhi_apply]
  ext r j
  have hj : (vsWMC p D Bm a).getD j [] = vsFRowMul p a (Bm.map fun M => M.getD j []) (vsWZ D) := by
    rw [List.getD_eq_getElem _ _ (by simp [vsWMC])]; simp [vsWMC]
  have hrows : ∀ row ∈ Bm.map (fun M => M.getD j []), row.length ≤ (vsWZ D).length := by
    intro row hrow
    simp only [List.mem_map] at hrow
    obtain ⟨M, hM, rfl⟩ := hrow
    rw [show (vsWZ D).length = D by simp [vsWZ]]
    by_cases h : (j : ℕ) < M.length
    · rw [List.getD_eq_getElem _ _ h]; exact ((hB M hM).1 _ (List.getElem_mem h)).2.le
    · rw [List.getD_eq_default _ _ (by omega)]; simp
  simp only [vsWM, Matrix.transpose_apply, vsFMatrix, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hj, vsFMat_rowMul p a _ _ hrows, vsWZ_vsF, zero_add, Finset.sum_apply, List.length_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have e : (Bm.map fun M => M.getD j []).getD i [] = (Bm.getD i []).getD j [] := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
      List.getD_eq_getElem _ _ hi']
  rw [e]
  rfl

/-- The span of the matrices of a list is the range of `vsWPhi`. -/
theorem vsWPhi_range {D : ℕ} (Bm : List (List (List ℕ))) (x : Matrix (Fin D) (Fin D) (ZMod p)) :
    x ∈ Submodule.span (ZMod p) {X | ∃ M ∈ Bm, vsWM p D M = X} ↔ ∃ c, vsWPhi p D Bm c = x := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨M, hM, rfl⟩ := hX
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hM
      refine ⟨fun j => if j = i then 1 else 0, ?_⟩
      rw [vsWPhi_apply]
      simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_range, hi, if_true]
      rw [List.getD_eq_getElem _ _ hi]
    | zero => exact ⟨0, map_zero _⟩
    | add X Y _ _ hX hY =>
      obtain ⟨c, rfl⟩ := hX
      obtain ⟨e, rfl⟩ := hY
      exact ⟨c + e, map_add _ _ _⟩
    | smul k X _ hX =>
      obtain ⟨c, rfl⟩ := hX
      exact ⟨k • c, map_smul _ _ _⟩
  · rintro ⟨c, rfl⟩
    rw [vsWPhi_apply]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨_, by rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]; exact List.getElem_mem _, rfl⟩

/-! ### The Frobenius map on combinations -/

/-- For commuting `M_i`, `(∑ c_i M_i) ^ p = ∑ c_i M_i ^ p`. -/
theorem vsW_frob_sum [hp : Fact p.Prime] {A : Type*} [Ring A] [Algebra (ZMod p) A] (s : Finset ℕ)
    (M : ℕ → A) (hC : ∀ i ∈ s, ∀ j ∈ s, Commute (M i) (M j)) (c : ℕ → ZMod p) :
    (∑ i ∈ s, c i • M i) ^ p = ∑ i ∈ s, c i • M i ^ p := by
  induction s using Finset.induction_on with
  | empty => simp [zero_pow hp.out.ne_zero]
  | insert a s ha ih =>
    have hC' : ∀ i ∈ s, ∀ j ∈ s, Commute (M i) (M j) := fun i hi j hj =>
      hC i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hcomm : Commute (c a • M a) (∑ i ∈ s, c i • M i) :=
      Commute.sum_right _ _ _ fun i hi =>
        ((hC a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)).smul_left _).smul_right _
    rw [Finset.sum_insert ha, Finset.sum_insert ha, vsFA_add_pow hcomm, vsFA_smul_pow, ih hC']

/-- The unflattening is injective on vectors supported below `D * D`. -/
theorem vsWUnf_eq_zero {D : ℕ} {f : ℕ → ZMod p} (hf : f ∈ vsWSupp p (D * D))
    (h : vsFAUnflat p D f = 0) : f = 0 := by
  funext k
  by_cases hk : k < D * D
  · have hD : 0 < D := by
      rcases Nat.eq_zero_or_pos D with h0 | h0
      · simp [h0] at hk
      · exact h0
    have h1 : k / D < D := Nat.div_lt_of_lt_mul hk
    have h2 : k % D < D := Nat.mod_lt _ hD
    have := congrFun (congrFun h ⟨k / D, h1⟩) ⟨k % D, h2⟩
    change f (k / D * D + k % D) = 0 at this
    rwa [Nat.div_add_mod'] at this
  · exact hf k (by omega)

/-- **Relations among flattened matrices.** If the flattened `g M` stands for the matrix
`(G M)ᵀ`, then a coefficient vector `c` (supported below `n`) is in the span of the relations
among the `g M_i` iff `∑ c_i G M_i = 0`. -/
theorem vsW_rel_iff (hp : p.Prime) {D : ℕ} {Bm : List (List (List ℕ))} (g : List (List ℕ) → List ℕ)
    (hfit : VsWFit p (D * D) (Bm.map g)) (G : List (List ℕ) → Matrix (Fin D) (Fin D) (ZMod p))
    (hG : ∀ M ∈ Bm, vsFAUnflat p D (vsF p (g M)) = (G M).transpose) {c : ℕ → ZMod p}
    (hc : ∀ j, Bm.length ≤ j → c j = 0) :
    c ∈ vsWSpN p (vsWKer p (Bm.map g)) ↔
      ∑ i ∈ Finset.range Bm.length, c i • G (Bm.getD i []) = 0 := by
  have hc' : ∀ j, (Bm.map g).length ≤ j → c j = 0 := by simpa using hc
  rw [vsWSpN_eq_span_list, vsWKer, ← vsUnitPairs_ker hp hfit hc']
  have hsupp := vsWSum_supp (d := D * D) (xs := Bm.map g) (fun x hx => (hfit x hx).2.le) c
  have hU : vsFAUnflat p D (vsComb p (Bm.map g) c) =
      (∑ i ∈ Finset.range Bm.length, c i • G (Bm.getD i [])).transpose := by
    rw [vsComb, map_sum, Matrix.transpose_sum, List.length_map]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [map_smul, Matrix.transpose_smul, List.getD_eq_getElem _ _ (by simpa using hi'),
      List.getElem_map, List.getD_eq_getElem _ _ hi', hG _ (List.getElem_mem hi')]
  constructor
  · intro h0
    rw [h0, map_zero] at hU
    exact Matrix.transpose_eq_zero.mp hU.symm
  · intro h0
    rw [h0, Matrix.transpose_zero] at hU
    exact vsWUnf_eq_zero hsupp hU

/-- The span of the combinations given by the relations among the flattened `g M_i`. -/
theorem vsW_relSpan (hp : p.Prime) {D : ℕ} {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, VsWSq p D M) (g : List (List ℕ) → List ℕ) (hfit : VsWFit p (D * D) (Bm.map g))
    (G : List (List ℕ) → Matrix (Fin D) (Fin D) (ZMod p))
    (hG : ∀ M ∈ Bm, vsFAUnflat p D (vsF p (g M)) = (G M).transpose)
    (x : Matrix (Fin D) (Fin D) (ZMod p)) :
    x ∈ Submodule.span (ZMod p) {X | ∃ y ∈ (vsWKer p (Bm.map g)).map (vsWMC p D Bm),
      vsWM p D y = X} ↔
      ∃ c : ℕ → ZMod p, vsWPhi p D Bm c = x ∧
        ∑ i ∈ Finset.range Bm.length, c i • G (Bm.getD i []) = 0 := by
  have hset : {X | ∃ y ∈ (vsWKer p (Bm.map g)).map (vsWMC p D Bm), vsWM p D y = X} =
      vsWPhi p D Bm '' {f | ∃ a ∈ vsWKer p (Bm.map g), vsF p a = f} := by
    ext X
    simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, (vsWMC_matrix hB a).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, vsWMC_matrix hB a⟩
  have hKfit := vsWKer_fit hp.one_lt hfit
  have hsupp : vsWSpN p (vsWKer p (Bm.map g)) ≤ vsWSupp p Bm.length := by
    have := vsWSpN_le_supp (p := p) (d := (Bm.map g).length) (us := vsWKer p (Bm.map g))
      (fun t ht => (hKfit t ht).2.le)
    simpa using this
  rw [hset, Submodule.span_image]
  change x ∈ (vsWSpN p (vsWKer p (Bm.map g))).map (vsWPhi p D Bm) ↔ _
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, rfl, (vsW_rel_iff hp g hfit G hG (hsupp hc)).mp hc⟩
  · rintro ⟨c, rfl, h0⟩
    set c' : ℕ → ZMod p := fun j => if j < Bm.length then c j else 0
    have hsum : ∀ (Y : ℕ → Matrix (Fin D) (Fin D) (ZMod p)),
        ∑ i ∈ Finset.range Bm.length, c' i • Y i = ∑ i ∈ Finset.range Bm.length, c i • Y i :=
      fun Y => Finset.sum_congr rfl fun i hi => by simp [c', Finset.mem_range.mp hi]
    have hc' : ∀ j, Bm.length ≤ j → c' j = 0 := fun j hj => by simp [c', show ¬ j < Bm.length by omega]
    refine ⟨c', (vsW_rel_iff hp g hfit G hG hc').mpr (by rw [hsum]; exact h0), ?_⟩
    rw [vsWPhi_apply, vsWPhi_apply, hsum]

/-! ### The kernel and the fixed points of the Frobenius map -/

theorem vsWSq_vsFSq {D : ℕ} {M : List (List ℕ)} (h : VsWSq p D M) : VsFSq p D M := ⟨h.2, h.1⟩

theorem vsWPowFlat_fit (hp : 0 < p) {D : ℕ} {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, VsWSq p D M) : VsWFit p (D * D) (Bm.map (vsWPowFlat p D)) := by
  intro f hf
  simp only [List.mem_map] at hf
  obtain ⟨M, hM, rfl⟩ := hf
  have hsq := vsFMatPowL_sq hp (vsWSq_vsFSq (hB M hM)) (z := vsWZ D)
    (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]) (p - 1)
  exact ⟨vsFA_flatten_lt (fun r hr => (hsq.rows r hr).1),
    by rw [vsWPowFlat, vsFA_flatten_length (fun r hr => (hsq.rows r hr).2), hsq.len]⟩

theorem vsWPowFlat_unf (hp : 0 < p) {D : ℕ} {M : List (List ℕ)} (hM : VsWSq p D M) :
    vsFAUnflat p D (vsF p (vsWPowFlat p D M)) = (vsWM p D M ^ p).transpose := by
  have hz : ∀ y ∈ vsWZ D, y < p := fun y hy => by simp [vsWZ] at hy; omega
  have hzl : (vsWZ D).length = D := by simp [vsWZ]
  rw [vsWPowFlat, vsFAUnflat_flatten (vsFMatPowL_sq hp (vsWSq_vsFSq hM) hz hzl (p - 1)),
    vsFMatPow_matrix hp (vsWSq_vsFSq hM) hz hzl (vsWZ_vsF D), vsWM, Matrix.transpose_pow,
    Matrix.transpose_transpose]

/-- The commuting hypothesis for the matrices of a list. -/
def VsWComm (p D : ℕ) (Bm : List (List (List ℕ))) : Prop :=
  ∀ M ∈ Bm, ∀ M' ∈ Bm, Commute (vsWM p D M) (vsWM p D M')

theorem vsWPhi_pow [Fact p.Prime] {D : ℕ} {Bm : List (List (List ℕ))} (hC : VsWComm p D Bm)
    (c : ℕ → ZMod p) :
    vsWPhi p D Bm c ^ p = ∑ i ∈ Finset.range Bm.length, c i • vsWM p D (Bm.getD i []) ^ p := by
  rw [vsWPhi_apply]
  refine vsW_frob_sum _ _ (fun i hi j hj => hC _ ?_ _ ?_) c
  · rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]; exact List.getElem_mem _
  · rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hj)]; exact List.getElem_mem _

/-- **The kernel of the Frobenius map.** For commuting matrices, `x` is in the span of
`vsFNilL p D Bm` iff `x` is in the span of `Bm` and `x ^ p = 0`. -/
theorem vsFNilL_span (hp : p.Prime) {D : ℕ} {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, VsWSq p D M) (hC : VsWComm p D Bm) (x : Matrix (Fin D) (Fin D) (ZMod p)) :
    x ∈ Submodule.span (ZMod p) {X | ∃ y ∈ vsFNilL p D Bm, vsWM p D y = X} ↔
      x ∈ Submodule.span (ZMod p) {X | ∃ M ∈ Bm, vsWM p D M = X} ∧ x ^ p = 0 := by
  haveI := Fact.mk hp
  rw [vsFNilL, vsW_relSpan hp hB _ (vsWPowFlat_fit hp.pos hB) (fun M => vsWM p D M ^ p)
    (fun M hM => vsWPowFlat_unf hp.pos (hB M hM)), vsWPhi_range]
  constructor
  · rintro ⟨c, rfl, h0⟩
    exact ⟨⟨c, rfl⟩, by rw [vsWPhi_pow hC]; exact h0⟩
  · rintro ⟨⟨c, rfl⟩, h0⟩
    exact ⟨c, rfl, by rw [← vsWPhi_pow hC]; exact h0⟩

theorem vsWFixFlat_fit (hp : 0 < p) {D : ℕ} {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, VsWSq p D M) : VsWFit p (D * D) (Bm.map (vsWFixFlat p D)) := by
  intro f hf
  simp only [List.mem_map] at hf
  obtain ⟨M, hM, rfl⟩ := hf
  have hP := vsWPowFlat_fit hp hB (vsWPowFlat p D M) (List.mem_map_of_mem hM)
  exact ⟨vsLin_lt hp _ _, by rw [vsWFixFlat, vsLin_length, hP.2]⟩

theorem vsWFixFlat_unf (hp : 0 < p) {D : ℕ} {M : List (List ℕ)} (hM : VsWSq p D M) :
    vsFAUnflat p D (vsF p (vsWFixFlat p D M)) = (vsWM p D M ^ p - vsWM p D M).transpose := by
  have hP := vsWPowFlat_fit hp (Bm := [M]) (fun M' hM' => by
    rw [List.mem_singleton] at hM'; subst hM'; exact hM) (vsWPowFlat p D M) (by simp)
  have hl : M.flatten.length ≤ (vsWPowFlat p D M).length := by
    rw [vsFA_flatten_length (fun r hr => ((hM.1 r hr).2)), hM.2, hP.2]
  rw [vsWFixFlat, vsF_vsLin _ _ _ hl, map_add, map_smul, map_smul, vsWPowFlat_unf hp hM,
    vsFAUnflat_flatten (vsWSq_vsFSq hM), Matrix.transpose_sub, vsWM, Matrix.transpose_transpose]
  have h1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp, ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [h1, Nat.cast_one, one_smul, neg_one_smul, sub_eq_add_neg]

/-- **The fixed points of the Frobenius map.** For commuting matrices, `x` is in the span of
`vsFFixL p D Bm` iff `x` is in the span of `Bm` and `x ^ p = x`. -/
theorem vsFFixL_span (hp : p.Prime) {D : ℕ} {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, VsWSq p D M) (hC : VsWComm p D Bm) (x : Matrix (Fin D) (Fin D) (ZMod p)) :
    x ∈ Submodule.span (ZMod p) {X | ∃ y ∈ vsFFixL p D Bm, vsWM p D y = X} ↔
      x ∈ Submodule.span (ZMod p) {X | ∃ M ∈ Bm, vsWM p D M = X} ∧ x ^ p = x := by
  haveI := Fact.mk hp
  rw [vsFFixL, vsW_relSpan hp hB _ (vsWFixFlat_fit hp.pos hB)
    (fun M => vsWM p D M ^ p - vsWM p D M) (fun M hM => vsWFixFlat_unf hp.pos (hB M hM)),
    vsWPhi_range]
  have key : ∀ c, ∑ i ∈ Finset.range Bm.length, c i • (vsWM p D (Bm.getD i []) ^ p -
      vsWM p D (Bm.getD i [])) = vsWPhi p D Bm c ^ p - vsWPhi p D Bm c := by
    intro c
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [vsWPhi_pow hC, vsWPhi_apply]
  constructor
  · rintro ⟨c, rfl, h0⟩
    exact ⟨⟨c, rfl⟩, sub_eq_zero.mp (by rw [← key]; exact h0)⟩
  · rintro ⟨⟨c, rfl⟩, h0⟩
    exact ⟨c, rfl, by rw [key, h0, sub_self]⟩

/-! ### Common kernels -/

theorem vsWId_fit (hp : 1 < p) (D : ℕ) : VsWFit p D (vsWId D) := by
  intro u hu
  simp only [vsWId, List.mem_map, List.mem_range] at hu
  obtain ⟨i, -, rfl⟩ := hu
  exact ⟨fun y hy => lt_of_le_of_lt (vsUnit_le_one D i y hy) hp, vsUnit_length D i⟩

theorem vsWV_unit {D i : ℕ} (hi : i < D) :
    vsWV p D (vsUnit D i) = fun j => if (⟨i, hi⟩ : Fin D) = j then 1 else 0 := by
  funext j
  rw [vsWV_apply, vsF_apply, List.getD_eq_getElem _ _ (by rw [vsUnit_length]; exact j.2)]
  simp only [vsUnit, List.getElem_map, List.getElem_range, Fin.ext_iff]
  by_cases h : (j : ℕ) = i
  · simp [h]
  · simp [h, Ne.symm h]

/-- The identity list spans everything. -/
theorem vsWId_span (D : ℕ) : vsWSp p D (vsWId D) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  rw [pi_eq_sum_univ v]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨vsUnit D i, by simp only [vsWId, List.mem_map, List.mem_range]; exact ⟨i, i.2, rfl⟩,
    vsWV_unit i.2⟩

theorem vsWCut_fold_span (hp : p.Prime) {D : ℕ} :
    ∀ (Ys : List (List (List ℕ))) (us : List (List ℕ)), (∀ y ∈ Ys, VsWSq p D y) → VsWFit p D us →
      vsWSp p D (Ys.foldl (vsWCut p D) us) =
        vsWSp p D us ⊓ ⨅ (y) (_ : y ∈ Ys), LinearMap.ker (vsWLin p D y)
  | [], us, _, _ => by simp
  | y :: Ys, us, hY, hu => by
    rw [List.foldl_cons, vsWCut_fold_span hp Ys _ (fun y' hy' => hY y' (List.mem_cons_of_mem _ hy'))
      (vsWCut_fit hp.pos), vsWCut_span hp hu (hY y (List.mem_cons_self ..))]
    ext v
    simp only [Submodule.mem_inf, Submodule.mem_iInf, List.mem_cons, forall_eq_or_imp]
    tauto

/-- **The common kernel.** -/
theorem vsFAnnL_span (hp : p.Prime) {D : ℕ} {Ys : List (List (List ℕ))}
    (hY : ∀ y ∈ Ys, VsWSq p D y) :
    vsWSp p D (vsFAnnL p D Ys) = ⨅ (y) (_ : y ∈ Ys), LinearMap.ker (vsWLin p D y) := by
  rw [vsFAnnL, vsWCut_fold_span hp Ys _ hY (vsWId_fit hp.one_lt D), vsWId_span, top_inf_eq]

theorem vsWMC_sq (hp : 0 < p) {D : ℕ} (Bm : List (List (List ℕ))) (a : List ℕ) :
    VsWSq p D (vsWMC p D Bm a) := by
  refine ⟨fun r hr => ?_, by simp [vsWMC]⟩
  simp only [vsWMC, List.mem_map, List.mem_range] at hr
  obtain ⟨i, -, rfl⟩ := hr
  refine ⟨?_, ?_⟩
  · rw [vsFRowMul]
    exact vsFMulAcc_foldl_lt hp _ _ (fun y hy => by simp [vsWZ] at hy; omega)
  · rw [vsFRowMul, vsFMulAcc_foldl_length]
    simp [vsWZ]

theorem vsWLin_eq (D : ℕ) (y : List (List ℕ)) :
    vsWLin p D y = Matrix.toLinAlgEquiv' (vsWM p D y) := LinearMap.ext fun _ => rfl

/-- **The bridge to `vsFAnn`.** Let `B` be the algebra of the linear maps of the span of `Bm`
(commuting matrices). Then `vsFAnnL` of `vsFNilL` spans `vsFAnn B`. -/
theorem vsFAnnL_nil (hp : p.Prime) {D : ℕ} {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, VsWSq p D M) (hC : VsWComm p D Bm)
    (B : Subalgebra (ZMod p) (Module.End (ZMod p) (Fin D → ZMod p)))
    (hBm : ∀ f, f ∈ B ↔ ∃ x ∈ Submodule.span (ZMod p) {X | ∃ M ∈ Bm, vsWM p D M = X},
      Matrix.toLinAlgEquiv' x = f) :
    haveI := Fact.mk hp
    vsWSp p D (vsFAnnL p D (vsFNilL p D Bm)) = vsFAnn B := by
  haveI := Fact.mk hp
  have hY : ∀ y ∈ vsFNilL p D Bm, VsWSq p D y := fun y hy => by
    simp only [vsFNilL, List.mem_map] at hy
    obtain ⟨a, -, rfl⟩ := hy
    exact vsWMC_sq hp.pos Bm a
  rw [vsFAnnL_span hp hY]
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, mem_vsFAnn]
  constructor
  · intro h f hf hfp
    obtain ⟨x, hx, rfl⟩ := (hBm f).mp hf
    have hxp : x ^ p = 0 := Matrix.toLinAlgEquiv'.injective (by rw [map_pow, hfp, map_zero])
    have hN := (vsFNilL_span hp hB hC x).mpr ⟨hx, hxp⟩
    -- every element of the span of the `vsWM y` kills `v`
    let L : Matrix (Fin D) (Fin D) (ZMod p) →ₗ[ZMod p] (Fin D → ZMod p) :=
      (LinearMap.applyₗ v).comp Matrix.toLinAlgEquiv'.toLinearMap
    have hle : Submodule.span (ZMod p) {X | ∃ y ∈ vsFNilL p D Bm, vsWM p D y = X} ≤
        LinearMap.ker L := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨y, hy, rfl⟩
      have := h y hy
      rw [vsWLin_eq] at this
      exact this
    exact hle hN
  · intro h y hy
    have hN : vsWM p D y ∈ Submodule.span (ZMod p) {X | ∃ y ∈ vsFNilL p D Bm, vsWM p D y = X} :=
      Submodule.subset_span ⟨y, hy, rfl⟩
    obtain ⟨hx, hxp⟩ := (vsFNilL_span hp hB hC _).mp hN
    rw [vsWLin_eq]
    exact h _ ((hBm _).mpr ⟨_, hx, rfl⟩) (by rw [← map_pow, hxp, map_zero])

end GI.Proved
