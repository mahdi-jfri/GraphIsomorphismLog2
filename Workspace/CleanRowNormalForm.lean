import Workspace.CleanRowQuotients
import Workspace.Paper.RowNormalFormDefs

/-! Theorem A.18 for a clean complement, stated with the paper's groups in `G`.

The coordinate-level work is in `RowTransfers` (LG3), `RowNormalForm`,
`RowZeroSum`, `RowQuotients`, `RowSemidirect` and `CleanRowQuotients`.
Here `H = K[B_{i0}]` is `cleanLocalGroup G c.coordinates i0`, the kernel in clean coordinates is
the subdirect subgroup `K' = c.normalRows h5 i0 ≤ H^m`, and the paper's
`N` and `N*` are `rowKernelImage K' i i0` ("the projection to one coordinate of
the kernel fixing another coordinate") and `rowSingleKernel K' i0` ("the
projection of the subgroup supported on one coordinate"). -/

open scoped commutatorElement

namespace GI.PureComplement

open Equiv GI.Paper

variable {I V : Type*} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Perm V)} {A : CleanBlockAction G I} (c : PureComplement A)
variable (h5 : 5 ≤ Fintype.card I) (i0 : I)

theorem cleanLocalGroup_eq : cleanLocalGroup G c.coordinates i0 = c.localGroup i0 := rfl

theorem mem_normalRows_iff (y : I → cleanLocalGroup G c.coordinates i0) :
    y ∈ c.normalRows h5 i0 ↔ cleanLift c.coordinates (cleanLocalGroup G c.coordinates i0) y ∈ G := by
  constructor
  · rintro ⟨x, rfl⟩
    exact x.property
  · intro hy
    exact ⟨⟨fun r => (y r).val, hy⟩, rfl⟩

theorem cleanLift_injective (H : Subgroup (Perm c.Fiber)) :
    Function.Injective (cleanLift c.coordinates H) := by
  intro x y hxy
  have h := c.rowMap_injective hxy
  funext r
  exact Subtype.ext (congrFun h r)

theorem top_cleanLift (y : I → cleanLocalGroup G c.coordinates i0) (hy : cleanLift c.coordinates _ y ∈ G) :
    A.top ⟨cleanLift c.coordinates _ y, hy⟩ = 1 :=
  c.row_top_one ⟨fun r => (y r).val, hy⟩

include h5 in
theorem exists_cleanLift_of_ker (g : G) (hg : A.top g = 1) :
    ∃ y : I → cleanLocalGroup G c.coordinates i0, cleanLift c.coordinates _ y = g.val := by
  obtain ⟨x, hx⟩ := c.kernelEmbedding_surjective ⟨g, hg⟩
  refine ⟨packRows c.rowKernel c.rowKernel_invariant (Nat.le_trans (by decide) h5) i0 x, ?_⟩
  exact congrArg (fun z : A.top.ker => z.val.val) hx

theorem normalRowsEquiv_inl (x : c.normalRows h5 i0) :
    ((c.normalRowsEquiv h5 i0) (SemidirectProduct.inl x)).val =
      cleanLift c.coordinates _ x.val := by
  set e1 := commonRowEquiv c.rowKernel c.rowKernel_invariant (Nat.le_trans (by decide) h5) i0
  have hy : packRows c.rowKernel c.rowKernel_invariant (Nat.le_trans (by decide) h5) i0
      (e1.symm x) = x.val := congrArg Subtype.val (e1.apply_symm_apply x)
  change c.rowMap (e1.symm x).val * (c.sectionHom 1).val = _
  rw [map_one, Subgroup.coe_one, mul_one]
  change c.rowMap (e1.symm x).val = c.rowMap (fun r => (x.val r).val)
  congr 1
  funext r
  exact congrArg (fun z => (z r).val) hy

theorem normalRowsEquiv_inr (p : alternatingGroup I) :
    (c.normalRowsEquiv h5 i0) (SemidirectProduct.inr p) = c.sectionHom p := by
  set e1 := commonRowEquiv c.rowKernel c.rowKernel_invariant (Nat.le_trans (by decide) h5) i0
  apply Subtype.ext
  change c.rowMap (e1.symm 1).val * (c.sectionHom p).val = _
  rw [map_one, Subgroup.coe_one, map_one, one_mul]

variable {i : I} (hij : i ≠ i0)

/-- The paper's `N`. -/
def rowN : Subgroup (cleanLocalGroup G c.coordinates i0) := rowKernelImage (c.normalRows h5 i0) i i0

/-- The paper's `N*`. -/
def rowNstar : Subgroup (cleanLocalGroup G c.coordinates i0) := rowSingleKernel (c.normalRows h5 i0) i0

instance rowN_normal : (c.rowN h5 i0 (i := i)).Normal :=
  row_kernel_normal _ (c.normalRows_subdirect h5 i0) i i0

instance rowNstar_normal : (c.rowNstar h5 i0).Normal :=
  row_single_normal _ (c.normalRows_subdirect h5 i0) i0

/-- The map `θ : G → H/N`; on `K` it reads off one coordinate. -/
noncomputable def theta : G →* cleanLocalGroup G c.coordinates i0 ⧸ c.rowN h5 i0 (i := i) :=
  c.actualDiagonalHom h5 i0 hij

theorem theta_cleanLift (g : G) (y : I → cleanLocalGroup G c.coordinates i0)
    (hy : cleanLift c.coordinates _ y = g.val) (r : I) :
    c.theta h5 i0 hij g = (y r : cleanLocalGroup G c.coordinates i0 ⧸ c.rowN h5 i0 (i := i)) := by
  have hmem : y ∈ c.normalRows h5 i0 := (c.mem_normalRows_iff h5 i0 y).mpr (hy ▸ g.property)
  have he : c.normalRowsEquiv h5 i0 (SemidirectProduct.inl ⟨y, hmem⟩) = g :=
    Subtype.ext ((c.normalRowsEquiv_inl h5 i0 ⟨y, hmem⟩).trans hy)
  have hθ : c.theta h5 i0 hij g = (y i0 : cleanLocalGroup G c.coordinates i0 ⧸ c.rowN h5 i0 (i := i)) := by
    change rowSemidirectHom _ (c.normalRows_invariant h5 i0) (c.normalRows_subdirect h5 i0) h5 hij
      ((c.normalRowsEquiv h5 i0).symm g) = _
    rw [← he, MulEquiv.symm_apply_apply]
    rfl
  rw [hθ]
  exact row_diagonal_quotient _ (c.normalRows_invariant h5 i0) h5 hij y hmem i0 r

theorem theta_section (p : alternatingGroup I) : c.theta h5 i0 hij (c.sectionHom p) = 1 := by
  have h : c.theta h5 i0 hij (c.sectionHom p) = rowSemidirectHom _ (c.normalRows_invariant h5 i0)
      (c.normalRows_subdirect h5 i0) h5 hij ((c.normalRowsEquiv h5 i0).symm (c.sectionHom p)) :=
    rfl
  rw [h, ← c.normalRowsEquiv_inr h5 i0 p, MulEquiv.symm_apply_apply]
  rfl

theorem mem_rowNormalM_iff (g : G) :
    g ∈ rowNormalM G A.top.ker c.coordinates i0 (c.rowN h5 i0 (i := i)) ↔
      A.top g = 1 ∧ ∃ x : I → cleanLocalGroup G c.coordinates i0, (∀ r, x r ∈ c.rowN h5 i0 (i := i)) ∧
        cleanLift c.coordinates _ x = g.val := by
  constructor
  · rintro ⟨hg, x, hx, hxg⟩
    exact ⟨hg, x, hx, hxg⟩
  · rintro ⟨hg, x, hx, hxg⟩
    exact ⟨hg, x, hx, hxg⟩

/-- On `K`, the kernel of `θ` is `M`: by (LG3) and the diagonal property, one
coordinate in `N` puts every coordinate in `N`. -/
theorem theta_eq_one_iff (g : G) (hg : A.top g = 1) :
    c.theta h5 i0 hij g = 1 ↔ g ∈ rowNormalM G A.top.ker c.coordinates i0 (c.rowN h5 i0 (i := i)) := by
  obtain ⟨y, hy⟩ := c.exists_cleanLift_of_ker h5 i0 g hg
  rw [c.theta_cleanLift h5 i0 hij g y hy i0, QuotientGroup.eq_one_iff, c.mem_rowNormalM_iff]
  constructor
  · intro hyN
    have hmem : y ∈ c.normalRows h5 i0 := (c.mem_normalRows_iff h5 i0 y).mpr (hy ▸ g.property)
    have hM := (row_coordinate_in_kernel_iff _ (c.normalRows_invariant h5 i0) h5 hij
      ⟨y, hmem⟩).mp hyN
    exact ⟨hg, y, hM.2, hy⟩
  · rintro ⟨_, x, hx, hxg⟩
    have hxy : x = y := c.cleanLift_injective _ (hxg.trans hy.symm)
    rw [← hxy]
    exact hx i0

/-- Pairwise commuting values make the order of a product irrelevant. -/
theorem prod_rowOrdering_eq {Q : Type*} [Group Q] (q : I → Q)
    (hc : ∀ r r', Commute (q r) (q r')) :
    ((rowOrdering i0).map q).prod = (Finset.univ.toList.map q).prod := by
  have hperm : List.Perm (rowOrdering i0) (Finset.univ : Finset I).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq (row_ordering_nodup i0) (Finset.nodup_toList _)
    ext r
    simp [row_ordering_mem]
  apply (hperm.map q).prod_eq'
  rw [List.pairwise_map]
  exact List.Pairwise.imp_of_mem (R := fun _ _ => True) (fun _ _ _ => hc _ _)
    (List.pairwise_of_forall (fun _ _ => trivial))

include hij in
theorem isRowNormalForm :
    IsRowNormalForm G A.top.ker c.coordinates i0 c.sectionHom (c.rowN h5 i0 (i := i))
      (c.rowNstar h5 i0) := by
  classical
  have h4 : 4 ≤ Fintype.card I := by omega
  set K' := c.normalRows h5 i0
  have hinv := c.normalRows_invariant h5 i0
  have hsub := c.normalRows_subdirect h5 i0
  -- `K` is normal, and `M = K ∩ ker θ`.
  have hMeq : rowNormalM G A.top.ker c.coordinates i0 (c.rowN h5 i0 (i := i)) =
      A.top.ker ⊓ (c.theta h5 i0 hij).ker := by
    ext g
    constructor
    · intro hg
      exact ⟨hg.1, (c.theta_eq_one_iff h5 i0 hij g hg.1).mpr hg⟩
    · rintro ⟨hg, hθ⟩
      exact (c.theta_eq_one_iff h5 i0 hij g hg).mp hθ
  -- Every `g` is `k s(p)` with `k ∈ K`.
  have hdecomp : ∀ g : G, ∃ k : G, ∃ p, A.top k = 1 ∧ g = k * c.sectionHom p := by
    intro g
    refine ⟨g * (c.sectionHom (A.top g))⁻¹, A.top g, ?_, by simp⟩
    rw [map_mul, map_inv, c.top_section, mul_inv_cancel]
  have hθker : (c.theta h5 i0 hij).ker =
      rowNormalM G A.top.ker c.coordinates i0 (c.rowN h5 i0 (i := i)) ⊔ c.sectionHom.range := by
    apply le_antisymm
    · intro g hg
      obtain ⟨k, p, hk, rfl⟩ := hdecomp g
      have hθk : c.theta h5 i0 hij k = 1 := by
        have h := hg
        change c.theta h5 i0 hij (k * c.sectionHom _) = 1 at h
        rwa [map_mul, c.theta_section, mul_one] at h
      apply Subgroup.mul_mem
      · exact (le_sup_left : _ ≤ _ ⊔ c.sectionHom.range)
          ((c.theta_eq_one_iff h5 i0 hij k hk).mp hθk)
      · exact (le_sup_right : _ ≤ rowNormalM G A.top.ker c.coordinates i0 _ ⊔ _) ⟨_, rfl⟩
    · apply sup_le
      · intro g hg
        exact (c.theta_eq_one_iff h5 i0 hij g hg.1).mpr hg
      · rintro _ ⟨p, rfl⟩
        exact c.theta_section h5 i0 hij p
  refine
    { nstar_le := row_single_le_kernel K' hij
      abelian := ?_
      mstar_le_G := ?_
      m_le := inf_le_left
      m_normal := by rw [hMeq]; infer_instance
      mstar_le_m := ?_
      mstar_normal := ?_
      zero_sum := ?_
      diagonal := ?_
      mr_normal := by rw [← hθker]; infer_instance }
  · -- `[N, N] ≤ N*`: commutators of transfers on `(1,2)` and `(1,3)`.
    intro a ha b hb
    have hc := row_kernel_commutator_le_single K' hinv h5 hij
      (Subgroup.commutator_mem_commutator ha hb)
    rwa [commutatorElement_def] at hc
  · -- `(N*)^m ≤ K`.
    rintro _ ⟨x, hx, rfl⟩
    exact (c.mem_normalRows_iff h5 i0 x).mp (row_single_power_le K' hinv h4 hij x hx)
  · rintro g ⟨x, hx, hxg⟩
    have hG : cleanLift c.coordinates _ x ∈ G := hxg ▸ g.property
    have htop : A.top g = 1 := by
      have h := c.top_cleanLift i0 x hG
      have hge : (⟨cleanLift c.coordinates _ x, hG⟩ : G) = g := Subtype.ext hxg
      rwa [hge] at h
    exact ⟨htop, x, fun r => row_single_le_kernel K' hij (hx r), hxg⟩
  · -- `M* ◁ M`, since `N* ◁ H`.
    constructor
    rintro n ⟨x, hx, hxn⟩ m
    obtain ⟨_, y, _, hym⟩ := m.property
    refine ⟨y * x * y⁻¹, fun r => ?_, ?_⟩
    · exact (inferInstance : (c.rowNstar h5 i0).Normal).conj_mem (x r) (hx r) (y r)
    · rw [map_mul, map_mul, map_inv, hym, hxn]
      rfl
  · -- `M/M*` is the zero-sum subgroup.
    let lift := cleanLift c.coordinates (cleanLocalGroup G c.coordinates i0)
    let L := MonoidHom.ofInjective (c.cleanLift_injective (cleanLocalGroup G c.coordinates i0))
    let M := rowNormalM G A.top.ker c.coordinates i0 (c.rowN h5 i0 (i := i))
    let incl : M →* lift.range :=
      { toFun := fun g => ⟨g.val.val, by
          obtain ⟨_, x, _, hx⟩ := g.property
          exact ⟨x, hx⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    let ψ : M →* (I → cleanLocalGroup G c.coordinates i0 ⧸ c.rowNstar h5 i0) :=
      (MonoidHom.compLeft (QuotientGroup.mk' (c.rowNstar h5 i0)) I).comp
        (L.symm.toMonoidHom.comp incl)
    have hψ : ∀ (g : M) (x : I → cleanLocalGroup G c.coordinates i0), lift x = g.val.val →
        ψ g = fun r => (x r : cleanLocalGroup G c.coordinates i0 ⧸ c.rowNstar h5 i0) := by
      intro g x hx
      have hL : L.symm (incl g) = x := by
        rw [MulEquiv.symm_apply_eq]
        exact Subtype.ext hx.symm
      funext r
      change (QuotientGroup.mk ((L.symm (incl g)) r) : cleanLocalGroup G c.coordinates i0 ⧸ c.rowNstar h5 i0) = _
      rw [hL]
    -- The values of `ψ` commute, because `N/N*` is abelian.
    have hcomm : ∀ q : I → cleanLocalGroup G c.coordinates i0 ⧸ c.rowNstar h5 i0,
        (∀ r, q r ∈ (c.rowN h5 i0 (i := i)).map (QuotientGroup.mk' (c.rowNstar h5 i0))) →
        ∀ r r', Commute (q r) (q r') := by
      intro q hq r r'
      obtain ⟨a, ha, hqa⟩ := hq r
      obtain ⟨b, hb, hqb⟩ := hq r'
      rw [← hqa, ← hqb]
      exact row_kernel_quotient_commute K' hinv hsub h5 hij ha hb
    refine ⟨ψ, hψ, ?_, ?_⟩
    · ext g
      obtain ⟨_, x, hxN, hx⟩ := g.property
      rw [MonoidHom.mem_ker, hψ g x hx, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        refine ⟨x, fun r => ?_, hx⟩
        have := congrFun h1 r
        exact (QuotientGroup.eq_one_iff _).mp this
      · rintro ⟨x', hx', hx'g⟩
        have hxx : x' = x := c.cleanLift_injective _ (hx'g.trans hx.symm)
        subst hxx
        funext r
        exact (QuotientGroup.eq_one_iff _).mpr (hx' r)
    · ext q
      constructor
      · rintro ⟨g, rfl⟩
        obtain ⟨_, x, hxN, hx⟩ := g.property
        rw [hψ g x hx]
        have hmem : x ∈ K' := (c.mem_normalRows_iff h5 i0 x).mpr (hx ▸ g.val.property)
        have hzero := (row_membership_iff_zero_product K' hinv hsub h5 hij x hxN).mp hmem
        have hq : ∀ r, (x r : cleanLocalGroup G c.coordinates i0 ⧸ c.rowNstar h5 i0) ∈
            (c.rowN h5 i0 (i := i)).map (QuotientGroup.mk' (c.rowNstar h5 i0)) :=
          fun r => ⟨x r, hxN r, rfl⟩
        refine ⟨hq, ?_⟩
        rw [← prod_rowOrdering_eq i0 _ (hcomm _ hq)]
        exact hzero
      · rintro ⟨hq, hzero⟩
        have hlift : ∀ r, ∃ n : cleanLocalGroup G c.coordinates i0, n ∈ c.rowN h5 i0 (i := i) ∧
            (n : cleanLocalGroup G c.coordinates i0 ⧸ c.rowNstar h5 i0) = q r := hq
        choose x hxN hxq using hlift
        have hprod : ((rowOrdering i0).map
            (fun r => (x r : cleanLocalGroup G c.coordinates i0 ⧸ c.rowNstar h5 i0))).prod = 1 := by
          have hq' : (fun r => (x r : cleanLocalGroup G c.coordinates i0 ⧸ c.rowNstar h5 i0)) = q := funext hxq
          rw [hq', prod_rowOrdering_eq i0 _ (hcomm _ hq)]
          exact hzero
        have hmem := (row_membership_iff_zero_product K' hinv hsub h5 hij x hxN).mpr hprod
        have hG := (c.mem_normalRows_iff h5 i0 x).mp hmem
        let g : M := ⟨⟨lift x, hG⟩, c.top_cleanLift i0 x hG, x, hxN, rfl⟩
        refine ⟨g, ?_⟩
        rw [hψ g x rfl]
        exact funext hxq
  · -- `K/M` is the diagonal `H/N`, and `G/(MR) ≅ H/N`.
    refine ⟨c.theta h5 i0 hij, fun g x r hx => c.theta_cleanLift h5 i0 hij g x hx r, ?_, ?_, hθker⟩
    · intro z
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
      obtain ⟨y, hy, hyh⟩ := hsub i0 h
      have hG := (c.mem_normalRows_iff h5 i0 y).mp hy
      refine ⟨⟨⟨cleanLift c.coordinates _ y, hG⟩, c.top_cleanLift i0 y hG⟩, ?_⟩
      change c.theta h5 i0 hij ⟨cleanLift c.coordinates _ y, hG⟩ = _
      rw [c.theta_cleanLift h5 i0 hij _ y rfl i0, hyh]
    · ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact c.theta_eq_one_iff h5 i0 hij g.val g.property

end GI.PureComplement
