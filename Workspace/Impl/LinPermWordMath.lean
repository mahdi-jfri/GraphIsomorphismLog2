import Workspace.Impl.LinCoordinates

/-! The ordered word used to lift an integer vector. Its image in an
abelian quotient is the specified integer-coordinate sum. -/
namespace GI.Impl
open scoped BigOperators

def linGroupWordPrefix {G : Type*} [Group G] {t : ℕ} (a : Fin t → G)
    (z : Fin t → ℤ) (i : ℕ) : G :=
  (((List.finRange t).take i).map fun j => a j ^ z j).reverse.prod

def linGroupWord {G : Type*} [Group G] {t : ℕ} (a : Fin t → G) (z : Fin t → ℤ) : G :=
  linGroupWordPrefix a z t

@[simp] theorem linGroupWordPrefix_zero {G : Type*} [Group G] {t : ℕ}
    (a : Fin t → G) (z : Fin t → ℤ) : linGroupWordPrefix a z 0 = 1 := rfl

theorem linGroupWordPrefix_succ {G : Type*} [Group G] {t : ℕ}
    (a : Fin t → G) (z : Fin t → ℤ) (i : Fin t) :
    linGroupWordPrefix a z (i.val + 1) = a i ^ z i * linGroupWordPrefix a z i.val := by
  have he : (List.finRange t).take (i.val + 1) = (List.finRange t).take i.val ++ [i] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using i.isLt)]
    simp
  simp [linGroupWordPrefix, he, List.reverse_append]

theorem linGroupWord_mem {G : Type*} [Group G] {t : ℕ} (A : Subgroup G)
    (a : Fin t → G) (ha : ∀ i, a i ∈ A) (z : Fin t → ℤ) : linGroupWord a z ∈ A := by
  apply A.list_prod_mem
  intro g hg
  simp only [linGroupWord, linGroupWordPrefix, List.take_length,
    List.length_finRange, List.mem_reverse, List.mem_map] at hg
  obtain ⟨i, _, rfl⟩ := hg
  exact A.zpow_mem (ha i) _

theorem linGroupWord_map {G H : Type*} [Group G] [Group H] {t : ℕ}
    (π : G →* H) (a : Fin t → G) (z : Fin t → ℤ) :
    π (linGroupWord a z) = linGroupWord (fun i => π (a i)) z := by
  simp [linGroupWord, linGroupWordPrefix, map_list_prod, List.map_reverse,
    List.map_map, Function.comp_def]

theorem linGroupWord_image {G Q : Type*} [Group G] [CommGroup Q] {t : ℕ}
    (π : G →* Q) (a : Fin t → G) (z : Fin t → ℤ) :
    π (linGroupWord a z) = linCoordHom (fun i => π (a i)) (Multiplicative.ofAdd z) := by
  have ht : (List.finRange t).take t = List.finRange t := List.take_of_length_le (by simp)
  simp only [linGroupWord, linGroupWordPrefix, ht,
    map_list_prod, List.map_reverse, List.map_map, Function.comp_def, map_zpow,
    List.prod_reverse, List.prod_ofFn, ← List.ofFn_eq_map]
  simp [linCoordHom, linCoordMap, LinearMap.sum_apply, toMul_sum, toMul_zsmul,
    ← List.ofFn_eq_map, List.prod_ofFn, Function.comp_def]

end GI.Impl
