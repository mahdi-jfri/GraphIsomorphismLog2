module

public import Workspace.Impl.VsPCtx
public import Workspace.Proved.VsQLoc
public import Workspace.Proved.VsFAlgSpanMath
public import Workspace.Proved.VsMBasic

@[expose] public section

/-!
# What the membership test means

The test `vsPInLB` sifts the flattened local matrix of `g` through the echelon rows of the
flattened basis `Lb`. Here we show:

* `vsPSift_iff`: the sifted vector is zero iff `vsFMatrix (loc g)` lies in `vsFMatSpan Lb`.
* `vsP_adjoin_transpose`: transposing maps `𝔽_p[S]` onto `𝔽_p[Sᵀ]`.
-/

open Matrix

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ}

/-- Flattening a matrix into a vector indexed by `ℕ` (row-major, zero beyond `D²`). -/
def vsPFlat (p D : ℕ) : Matrix (Fin D) (Fin D) (ZMod p) →ₗ[ZMod p] (ℕ → ZMod p) where
  toFun M := fun k => if h : k < D * D then
    M ⟨k / D, Nat.div_lt_of_lt_mul h⟩ ⟨k % D, Nat.mod_lt _ (by
      rcases Nat.eq_zero_or_pos D with h0 | h0
      · subst h0; simp at h
      · exact h0)⟩ else 0
  map_add' M N := by funext k; by_cases h : k < D * D <;> simp [h]
  map_smul' c M := by funext k; by_cases h : k < D * D <;> simp [h]

theorem vsPFlat_matrix {D : ℕ} {A : List (List ℕ)} (hA : VsFSq p D A) :
    vsPFlat p D (vsFMatrix p D A) = vsF p A.flatten := by
  have hr : ∀ r ∈ A, r.length = D := fun r hr => (hA.rows r hr).2
  funext k
  simp only [vsPFlat, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with h
  · have hD : 0 < D := by rcases Nat.eq_zero_or_pos D with h0 | h0 <;> [simp [h0] at h; exact h0]
    have hk : k = k / D * D + k % D := (Nat.div_add_mod' k D).symm
    have e : vsF p A.flatten k = vsF p A.flatten (k / D * D + k % D) := by
      conv_lhs => rw [hk]
    rw [e, vsF_apply, vsFA_flatten_getD hr _ _ (Nat.mod_lt _ hD)]
    simp only [vsFMatrix, vsF_apply]
  · rw [vsF_apply, List.getD_eq_default]
    · simp
    · rw [vsFA_flatten_length hr, hA.len]; omega

/-- A list of numbers below `p` reads as `0` iff it is the zero list. -/
theorem vsP_zero_iff {x : List ℕ} (hx : ∀ y ∈ x, y < p) :
    x = vsWZ x.length ↔ vsF p x = 0 := by
  constructor
  · intro h
    rw [h]
    funext i
    simp [vsF_apply, vsWZ, List.getD_eq_getElem?_getD]
  · intro h
    apply List.ext_getElem (by simp [vsWZ])
    intro i h1 h2
    have := congrFun h i
    rw [vsF_apply, List.getD_eq_getElem _ _ h1] at this
    have hlt := hx _ (List.getElem_mem h1)
    have h0 : x[i] = 0 := by
      have hd := (ZMod.natCast_eq_zero_iff _ _).1 this
      exact Nat.eq_zero_of_dvd_of_lt hd hlt
    simp [vsWZ, h0]

/-- **The membership test, on lists.** -/
theorem vsPSift_iff (hp : p.Prime) {D : ℕ} {Lb : List (List (List ℕ))}
    (hLb : ∀ M ∈ Lb, VsFSq p D M) {A : List (List ℕ)} (hA : VsFSq p D A) :
    (vsSift p (vsWRows p (Lb.map List.flatten)) (A.flatten, [])).1 = vsWZ (D * D) ↔
      vsFMatrix p D A ∈ vsFMatSpan p D Lb := by
  have hp0 := hp.pos
  have hfl : ∀ M, VsFSq p D M → (∀ y ∈ M.flatten, y < p) ∧ M.flatten.length = D * D :=
    fun M hM => ⟨vsFA_flatten_lt fun r hr => (hM.rows r hr).1, by
      rw [vsFA_flatten_length fun r hr => (hM.rows r hr).2, hM.len]⟩
  have hfit : VsWFit p (D * D) (Lb.map List.flatten) := by
    intro u hu
    obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hu
    exact hfl M (hLb M hM)
  have hI := vsInsertAll_inv hp (vsWPairs_fit hfit)
  have hR := vsWRows_inv hp hfit
  set rows := vsWRows p (Lb.map List.flatten)
  have hb : VsBelow p (A.flatten, ([] : List ℕ)) := (hfl A hA).1
  have hsh : VsShort (A.flatten, ([] : List ℕ)) rows := by
    intro r hr
    have := hI.len r hr
    exact ⟨by rw [(hfl A hA).2]; exact this.1.le, by simp only [List.length_nil]; exact this.2.le⟩
  have hlen : (vsSift p rows (A.flatten, [])).1.length = D * D := by
    rw [(vsSift_length p rows _).1, (hfl A hA).2]
  have hbel : ∀ y ∈ (vsSift p rows (A.flatten, [])).1, y < p :=
    (vsSift_fits hp0 rows (N := D * D + p) ⟨(hfl A hA).1, by simp,
      by rw [(hfl A hA).2]; omega, by simp⟩).hx
  rw [← hlen, vsP_zero_iff hbel, vsSift_eq_zero_iff hp0 hR.1 hb hsh, hR.2.2]
  -- the span of flattened vectors and the span of matrices
  constructor
  · intro h
    have := Submodule.apply_mem_span_image_of_mem_span (vsFAUnflat p D) h
    rw [vsFAUnflat_flatten hA] at this
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hu
    exact Submodule.subset_span ⟨M, hM, (vsFAUnflat_flatten (hLb M hM)).symm⟩
  · intro h
    have := Submodule.apply_mem_span_image_of_mem_span (vsPFlat p D) h
    rw [vsPFlat_matrix hA] at this
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨X, ⟨M, hM, rfl⟩, rfl⟩
    rw [vsPFlat_matrix (hLb M hM)]
    exact Submodule.subset_span ⟨M.flatten, List.mem_map_of_mem hM, rfl⟩

/-! ### Transposition and subalgebras -/

theorem vsP_transpose_mem {D : ℕ} {S : Set (Matrix (Fin D) (Fin D) (ZMod p))}
    {X : Matrix (Fin D) (Fin D) (ZMod p)} (hX : X ∈ Algebra.adjoin (ZMod p) S) :
    Xᵀ ∈ Algebra.adjoin (ZMod p) (Matrix.transpose '' S) := by
  induction hX using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  | algebraMap r =>
    rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_transpose]
    exact (Algebra.adjoin (ZMod p) _).algebraMap_mem r
  | add x y _ _ hx hy => rw [Matrix.transpose_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [Matrix.transpose_mul]; exact mul_mem hy hx

/-- **Transposing maps `𝔽_p[S]` onto `𝔽_p[Sᵀ]`.** -/
theorem vsP_adjoin_transpose {D : ℕ} {S : Set (Matrix (Fin D) (Fin D) (ZMod p))}
    {X : Matrix (Fin D) (Fin D) (ZMod p)} :
    Xᵀ ∈ Algebra.adjoin (ZMod p) (Matrix.transpose '' S) ↔ X ∈ Algebra.adjoin (ZMod p) S := by
  refine ⟨fun h => ?_, vsP_transpose_mem⟩
  have := vsP_transpose_mem h
  rwa [Matrix.transpose_transpose, Set.image_image, Set.image_congr (g := id)
    (fun x _ => Matrix.transpose_transpose x), Set.image_id] at this

/-- A subalgebra of matrices contains the inverses of its invertible elements. -/
theorem vsP_inv_mem {D : ℕ} [Fact p.Prime] (B : Subalgebra (ZMod p) (Matrix (Fin D) (Fin D) (ZMod p)))
    {M N : Matrix (Fin D) (Fin D) (ZMod p)} (hM : M ∈ B) (hMN : M * N = 1) : N ∈ B := by
  have hNM : N * M = 1 := mul_eq_one_comm.1 hMN
  let f : B →ₗ[ZMod p] B := LinearMap.mulLeft (ZMod p) (⟨M, hM⟩ : B)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg (fun z : B => N * (z : Matrix (Fin D) (Fin D) (ZMod p))) hab
    simpa [f, ← mul_assoc, hNM] using h
  obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective.1 hf) 1
  have h1 : M * (b : Matrix (Fin D) (Fin D) (ZMod p)) = 1 := congrArg Subtype.val hb
  have h2 : N = b := by
    calc N = N * (M * (b : Matrix (Fin D) (Fin D) (ZMod p))) := by rw [h1, mul_one]
      _ = b := by rw [← mul_assoc, hNM, one_mul]
  rw [h2]
  exact b.2

/-! ### The local images of permutation groups -/

variable {I : VecStabInst} {s : VsQSt I}

/-- The local image of a permutation group `K` (through `vsQRho`). -/
noncomputable def vsPBar (hs : VsQStOK s) (K : Subgroup (Equiv.Perm (Fin I.n))) :
    Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ :=
  (K.subgroupOf (gens s.hs)).map (vsQRho hs)

theorem vsQLam_inv (hs : VsQStOK s) {g : Equiv.Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    vsQLam s g * vsQLam s g⁻¹ = 1 := by
  rw [← vsQLam_mul hs hg (inv_mem hg), mul_inv_cancel, vsQLam_one hs]

/-- The local matrices of `⟨as⟩` lie in the algebra generated by those of `as`. -/
theorem vsQLam_mem_adjoin (hs : VsQStOK s) {as : List (Equiv.Perm (Fin I.n))}
    (has : gens as ≤ gens s.hs) {h : Equiv.Perm (Fin I.n)} (hh : h ∈ gens as) :
    vsQLam s h ∈ Algebra.adjoin (ZMod I.p) {X | ∃ a ∈ as, vsQLam s a = X} := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  set B := Algebra.adjoin (ZMod I.p) {X | ∃ a ∈ as, vsQLam s a = X}
  have key : ∀ h ∈ gens as, vsQLam s h ∈ B := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, by simpa using hx, rfl⟩
    | one => rw [vsQLam_one hs]; exact B.one_mem
    | mul x y hx hy ihx ihy =>
      rw [vsQLam_mul hs (has hx) (has hy)]; exact mul_mem ihx ihy
    | inv x hx ihx => exact vsP_inv_mem B ihx (vsQLam_inv hs (has hx))
  exact key h hh

/-- **`vsTAlg` of a local image**, as the image of an algebra of matrices. -/
theorem vsP_mem_vsTAlg_iff [Fact I.p.Prime] (hs : VsQStOK s) {as : List (Equiv.Perm (Fin I.n))}
    (has : gens as ≤ gens s.hs) (M : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) :
    Matrix.toLin' M ∈ vsTAlg (vsPBar hs (gens as)) ↔
      M ∈ Algebra.adjoin (ZMod I.p) {X | ∃ a ∈ as, vsQLam s a = X} := by
  set B := Algebra.adjoin (ZMod I.p) {X | ∃ a ∈ as, vsQLam s a = X}
  have hEq : vsTAlg (vsPBar hs (gens as)) = B.map Matrix.toLinAlgEquiv'.toAlgHom := by
    apply le_antisymm
    · refine Algebra.adjoin_le ?_
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨⟨h, hh⟩, hh', rfl⟩ := Subgroup.mem_map.1 hu
      rw [Subgroup.mem_subgroupOf] at hh'
      refine ⟨vsQLam s h, vsQLam_mem_adjoin hs has hh', ?_⟩
      apply LinearMap.ext; intro a
      rw [vsQRho_apply hs]
      simp [Matrix.toLinAlgEquiv'_apply]
    · rw [AlgHom.map_adjoin]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have hag : a ∈ gens s.hs := has (Subgroup.subset_closure (by simpa using ha))
      refine Algebra.subset_adjoin ⟨vsQRho hs ⟨a, hag⟩, ?_, ?_⟩
      · exact Subgroup.mem_map.2 ⟨⟨a, hag⟩, by
          rw [Subgroup.mem_subgroupOf]; exact Subgroup.subset_closure (by simpa using ha), rfl⟩
      · apply LinearMap.ext; intro v
        rw [vsQRho_apply hs]
        simp [Matrix.toLinAlgEquiv'_apply]
  rw [hEq]
  constructor
  · rintro ⟨N, hN, he⟩
    have : N = M := Matrix.toLin'.injective (by exact he)
    rw [← this]; exact hN
  · intro hM
    exact ⟨M, hM, rfl⟩

theorem vsQRho_eq_toLin' (hs : VsQStOK s) {g : Equiv.Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    ((vsQRho hs ⟨g, hg⟩ : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) :
      Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) = Matrix.toLin' (vsQLam s g) := by
  apply LinearMap.ext; intro a
  rw [vsQRho_apply hs, Matrix.toLin'_apply]

theorem vsFMatrix_loc (g : Equiv.Perm (Fin I.n)) :
    vsFMatrix I.p (vsQD s) (vsPLocL I s.ws' (vsQCs s) g) = (vsQLam s g)ᵀ := by
  rw [vsQLam, vsWM, Matrix.transpose_transpose]; rfl

/-- **What the membership test means.** With `Lb` spanning `𝔽_p[Λ(as)]` (as `vsFAlgSpan`
computes it), the test on `g` holds iff `Λ(g)` lies in the scalars `S` of `Ā`. -/
theorem vsPInLB_iff [Fact I.p.Prime] (hs : VsQStOK s) {as : List (Equiv.Perm (Fin I.n))}
    (has : gens as ≤ gens s.hs) {Lb : List (List (List ℕ))}
    (hLb : ∀ M ∈ Lb, VsFSq I.p (vsQD s) M)
    (hspan : vsFMatSpan I.p (vsQD s) Lb = Subalgebra.toSubmodule
      (vsFAlgOf I.p (vsQD s) (as.map (vsPLocL I s.ws' (vsQCs s)))))
    {g : Equiv.Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    vsPInLB I s.ws' (vsQCs s) (vsWRows I.p (Lb.map List.flatten)) g = true ↔
      vsQRho hs ⟨g, hg⟩ ∈ vsMScal (vsPBar hs (gens as)) := by
  have hA : VsFSq I.p (vsQD s) (vsPLocL I s.ws' (vsQCs s) g) := by
    have := vsPLocL_sq (I := I) (ws' := s.ws') (cs := vsQCs s) g
    exact ⟨this.2, fun a ha => this.1 a ha⟩
  have hset : {X | ∃ M ∈ as.map (vsPLocL I s.ws' (vsQCs s)), vsFMatrix I.p (vsQD s) M = X} =
      Matrix.transpose '' {X | ∃ a ∈ as, vsQLam s a = X} := by
    ext X
    simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨vsQLam s a, ⟨a, ha, rfl⟩, (vsFMatrix_loc a).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, vsFMatrix_loc a⟩
  unfold vsPInLB
  rw [decide_eq_true_iff, vsPSift_iff I.prime hLb hA, hspan, Subalgebra.mem_toSubmodule, vsFAlgOf,
    hset, vsFMatrix_loc, vsP_adjoin_transpose, ← vsP_mem_vsTAlg_iff hs has,
    ← vsQRho_eq_toLin' hs hg, ← vsM_mem_scal_iff]

end GI.Proved
