module

public import Workspace.Impl.LinAbelianCoordinates

@[expose] public section

/-!
# The coordinate vector of one element of `A = N / N*` (mathematics)

Let `ns` generate `N*` and `as` generate `N`, with `N*` normal in `N` and `N / N*` abelian.
Fix the coordinate map of `LinPermCertificate.lean`: the `i`-th unit vector goes to the class of
`as[i]`. For an element `x` of `N`, constructive membership in `⟨ns ++ as⟩` gives a straight-line
program reaching `x`. Interpreting the same program on the vectors `0, …, 0` (for `ns`) and the
unit vectors (for `as`) gives an integer vector `z`. Since the generator images match, the class
of `x` is the image of `z` (`tmJV_class`). This is the only result of this file used later.
-/

namespace GI.Impl
open GI.Cited GI.Lang
open scoped IsMulCommutative

/-- The assigned vectors match the generator images: `ns` goes to zero, `as[i]` to the `i`-th
unit vector. -/
theorem tmJV_images {n : ℕ} (ns as : List (Equiv.Perm (Fin n))) (hle : gens ns ≤ gens as)
    [((gens ns).subgroupOf (gens as)).Normal]
    [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))] :
    ((ns ++ as).map (linIntoSubgroup (gens as))).map
        (QuotientGroup.mk' ((gens ns).subgroupOf (gens as))) =
      ((linPrefixVectors as.length ns.length as.length).map Multiplicative.ofAdd).map
        (linCoordHom (fun i : Fin as.length =>
          QuotientGroup.mk' ((gens ns).subgroupOf (gens as)) (linIntoSubgroup (gens as) as[i.val]))) := by
  let A := gens as
  let N := (gens ns).subgroupOf A
  let π := QuotientGroup.mk' N
  let v : Fin as.length → A ⧸ N := fun i => π (linIntoSubgroup A as[i.val])
  let q := linCoordHom v
  have hns : ∀ y ∈ ns, π (linIntoSubgroup A y) = 1 := by
    intro y hy
    apply (QuotientGroup.eq_one_iff _).mpr
    change A.subtype (linIntoSubgroup A y) ∈ gens ns
    rw [linIntoSubgroup_val A y (hle (Subgroup.subset_closure hy))]
    exact Subgroup.subset_closure hy
  have hn : (ns.map (linIntoSubgroup A)).map π = List.replicate ns.length 1 := by
    rw [List.map_map]
    simpa [Function.comp_def] using List.map_eq_replicate_iff.mpr (fun y hy => hns y hy)
  have ht : (List.finRange as.length).take as.length = List.finRange as.length := by
    simp
  rw [List.map_append, List.map_append, hn]
  simp only [linPrefixVectors, ht, List.map_append, List.map_replicate, List.map_map,
    Function.comp_def]
  congr 1
  · exact (congrArg (List.replicate ns.length) (map_one q)).symm
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp

/-- **The class of one element.** A straight-line program reaching `x` from `ns ++ as`, run on
the zero vectors for `ns` and the unit vectors for `as`, gives a vector `z` whose image under
the coordinate map is the class of `x`. -/
theorem tmJV_class {n : ℕ} (ns as : List (Equiv.Perm (Fin n))) (hle : gens ns ≤ gens as)
    [((gens ns).subgroupOf (gens as)).Normal]
    [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]
    (x : Equiv.Perm (Fin n)) (hx : x ∈ gens as) (prog : List SlpInstr)
    (hp : SlpReaches (ns ++ as) prog x) (z : Fin as.length → ℤ)
    (hz : linExponentValue (linPrefixVectors as.length ns.length as.length) prog = some z) :
    Additive.ofMul (QuotientGroup.mk' ((gens ns).subgroupOf (gens as)) ⟨x, hx⟩) =
      linCoordMap (fun i : Fin as.length =>
        QuotientGroup.mk' ((gens ns).subgroupOf (gens as)) (linIntoSubgroup (gens as) as[i.val])) z := by
  let A := gens as
  have hall : ∀ y ∈ ns ++ as, y ∈ A := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hle (Subgroup.subset_closure hy)
    · exact Subgroup.subset_closure hy
  have hpval : linSlpValue (ns ++ as) prog = some x := by
    obtain ⟨es, he, hlast⟩ := hp
    simp only [linSlpValue, linSlpEntries_perm, he, Option.map_some, hlast]
  have hpA : linSlpValue ((ns ++ as).map (linIntoSubgroup A)) prog = some (⟨x, hx⟩ : A) := by
    apply Option.map_injective A.subtype_injective
    rw [← linSlpValue_map, linIntoSubgroup_map A _ hall, hpval]
    rfl
  have hh := linExponent_relation _ _ _ _ (tmJV_images ns as hle) prog _ hpA z hz
  rw [← hh]
  rfl

/-- The hypotheses `gens ns ≤ gens as` and "all commutators of `gens as` lie in `gens ns`" give
the normality instance used in the statements here. -/
theorem tmJV_normal {n : ℕ} (ns as : List (Equiv.Perm (Fin n)))
    (hc : ∀ x ∈ gens as, ∀ y ∈ gens as, x * y * x⁻¹ * y⁻¹ ∈ gens ns) :
    ((gens ns).subgroupOf (gens as)).Normal := by
  have hh := linChain_normal ((gens ns).subgroupOf (gens as)) (as.map (linIntoSubgroup (gens as)))
    (fun x y => hc x x.property y y.property) 0
  simpa only [linChain_zero] using hh

/-- The same hypotheses make the quotient commutative. -/
theorem tmJV_comm {n : ℕ} (ns as : List (Equiv.Perm (Fin n)))
    (hc : ∀ x ∈ gens as, ∀ y ∈ gens as, x * y * x⁻¹ * y⁻¹ ∈ gens ns) :
    letI := tmJV_normal ns as hc
    IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as)) :=
  letI := tmJV_normal ns as hc
  linQuotient_comm _ (fun x y => hc x x.property y y.property)

end GI.Impl
