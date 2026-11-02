import Workspace.CleanRowKernel

/-! The common local group H and the subdirect row subgroup are extracted from
the actual clean-coordinate kernel, rather than supplied as hypotheses. -/
namespace GI
variable {I H : Type*} [Fintype I] [DecidableEq I] [Group H]

theorem even_perm_maps_point (hcard : 4 ≤ Fintype.card I) (a b : I) :
    ∃ s : Equiv.Perm I, s ∈ alternatingGroup I ∧ s a = b := by
  letI : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a', ha'⟩ := exists_ne a
  obtain ⟨b', hb'⟩ := exists_ne b
  obtain ⟨s, hs, hsa, _⟩ := even_perm_maps_pair hcard (Ne.symm ha') (Ne.symm hb')
  exact ⟨s, hs, hsa⟩

def commonRowGroup (K : Subgroup (I → H)) (i : I) : Subgroup H := K.map (rowEval i)

theorem coordinate_mem_common (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 4 ≤ Fintype.card I) (i j : I) (x : I → H) (hx : x ∈ K) :
    x j ∈ commonRowGroup K i := by
  obtain ⟨s, hs, hsi⟩ := even_perm_maps_point hcard i j
  refine ⟨rowPermute s x, hinv s hs x hx, ?_⟩
  change x (s i) = x j
  rw [hsi]

def packRows (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 4 ≤ Fintype.card I) (i : I) : K →* (I → commonRowGroup K i) where
  toFun x j := ⟨x.val j, coordinate_mem_common K hinv hcard i j x.val x.property⟩
  map_one' := by funext j; apply Subtype.ext; rfl
  map_mul' x y := by funext j; apply Subtype.ext; rfl

theorem packRows_injective (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 4 ≤ Fintype.card I) (i : I) : Function.Injective (packRows K hinv hcard i) := by
  intro x y hxy
  apply Subtype.ext
  funext j
  exact congrArg (fun z : I → commonRowGroup K i => (z j).val) hxy

def commonRowKernel (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 4 ≤ Fintype.card I) (i : I) : Subgroup (I → commonRowGroup K i) :=
  (packRows K hinv hcard i).range

noncomputable def commonRowEquiv (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 4 ≤ Fintype.card I) (i : I) : K ≃* commonRowKernel K hinv hcard i :=
  MonoidHom.ofInjective (packRows_injective K hinv hcard i)

theorem commonRowKernel_invariant (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 4 ≤ Fintype.card I) (i : I) : RowAltInvariant (commonRowKernel K hinv hcard i) := by
  intro s hs z hz
  obtain ⟨x, rfl⟩ := hz
  refine ⟨⟨rowPermute s x.val, hinv s hs x.val x.property⟩, ?_⟩
  funext j
  rfl

theorem commonRowKernel_subdirect (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 4 ≤ Fintype.card I) (i : I) : RowSubdirect (commonRowKernel K hinv hcard i) := by
  intro j n
  obtain ⟨x, hx, hxi⟩ := n.property
  obtain ⟨s, hs, hsj⟩ := even_perm_maps_point hcard j i
  let y : K := ⟨rowPermute s x, hinv s hs x hx⟩
  refine ⟨packRows K hinv hcard i y, ⟨y, rfl⟩, ?_⟩
  apply Subtype.ext
  change x (s j) = n.val
  rw [hsj]
  exact hxi

namespace PureComplement
variable {V : Type*} {G : Subgroup (Equiv.Perm V)} {A : CleanBlockAction G I}
variable (c : PureComplement A) (hcard : 4 ≤ Fintype.card I) (i : I)

abbrev localGroup := commonRowGroup c.rowKernel i

def commonRows : Subgroup (I → c.localGroup i) :=
  commonRowKernel c.rowKernel c.rowKernel_invariant hcard i

theorem commonRows_invariant : RowAltInvariant (c.commonRows hcard i) :=
  commonRowKernel_invariant c.rowKernel c.rowKernel_invariant hcard i

theorem commonRows_subdirect : RowSubdirect (c.commonRows hcard i) :=
  commonRowKernel_subdirect c.rowKernel c.rowKernel_invariant hcard i

noncomputable def commonRowsKernelEquiv : c.commonRows hcard i ≃* A.top.ker :=
  (commonRowEquiv c.rowKernel c.rowKernel_invariant hcard i).symm.trans c.kernelEquiv

end PureComplement
end GI
