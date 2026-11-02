import Workspace.Impl.GenNormChild

/-!
# Reading the point action from a single Cameron factor

A Cameron identification lists every `k`-subset of `m` points. Two different points have
different incidence columns when `0 < k < m`. To recover the image of a point under a block
permutation, search the points for the matching incidence column. This searches `m` points
and `d` blocks per point. It never searches the permutations of `m` points.
-/

namespace GI.Impl

open GI.Algorithm Equiv Equiv.Perm

/-- A `k`-set can separate any two different points. -/
theorem normIncidence_separates {m k : ℕ} (hk : 0 < k) (hkm : k < m)
    {i j : Fin m} (hij : i ≠ j) :
    ∃ A : Product.KSet m k, i ∈ A.1 ∧ j ∉ A.1 := by
  classical
  let U := (Finset.univ.erase i).erase j
  have hU : k - 1 ≤ U.card := by
    have hcard : U.card = m - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    omega
  obtain ⟨T, hT, hc⟩ := Finset.exists_subset_card_eq hU
  have hi : i ∉ T := by
    intro h
    have := hT h
    simp [U] at this
  have hj : j ∉ T := by
    intro h
    have := hT h
    simp [U] at this
  refine ⟨⟨insert i T, by rw [Finset.card_insert_of_notMem hi, hc]; omega⟩,
    Finset.mem_insert_self _ _, ?_⟩
  simpa [Finset.mem_insert, hij.symm] using hj

variable {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S)
variable {m k : ℕ} (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))

/-- Distinct points have distinct incidence columns in the table returned by Cameron
recognition. Surjectivity of the identification is used to read every `k`-subset. -/
theorem normIncidence_injective {i j : Fin m}
    (h : ∀ b : Fin Q.d, i ∈ (e b 0).1 ↔ j ∈ (e b 0).1) : i = j := by
  by_contra hij
  obtain ⟨A, hi, hj⟩ := normIncidence_separates (Q.k_bounds e).1 (Q.k_bounds e).2 hij
  have hb := h (e.symm fun _ => A)
  simp only [Equiv.apply_symm_apply] at hb
  exact hj (hb.mp hi)

/-- A block permutation induced by `a` sends incidence column `i` to column `a i`. -/
theorem normIncidence_image {x : Perm (Fin Q.d)} {a : Perm (Fin m)}
    (ha : Product.IsProd e x 1 fun _ => a) (i : Fin m) (b : Fin Q.d) :
    i ∈ (e b 0).1 ↔ a i ∈ (e (x b) 0).1 := by
  have hb := congrArg Subtype.val (congrFun (ha b) 0)
  simp only [Perm.one_apply] at hb
  rw [hb]
  change i ∈ (e b 0).1 ↔ a i ∈ (e b 0).1.map a.toEmbedding
  simp

/-- The incidence test identifies exactly one point image. -/
theorem normIncidence_image_iff {x : Perm (Fin Q.d)} {a : Perm (Fin m)}
    (ha : Product.IsProd e x 1 fun _ => a) (i j : Fin m) :
    (∀ b : Fin Q.d, i ∈ (e b 0).1 ↔ j ∈ (e (x b) 0).1) ↔ j = a i := by
  constructor
  · intro h
    apply normIncidence_injective Q e
    intro b
    have h1 := h (x⁻¹ b)
    have h2 := normIncidence_image Q e ha i (x⁻¹ b)
    simp only [Perm.apply_inv_self] at h1 h2
    exact h1.symm.trans h2
  · rintro rfl
    exact normIncidence_image Q e ha i

/-- The points passing the incidence test. The loops have lengths `m` and `d`. -/
def normPointCandidates (x : Perm (Fin Q.d)) (i : Fin m) : List (Fin m) :=
  (List.finRange m).filter fun j =>
    (List.finRange Q.d).all fun b => decide (i ∈ (e b 0).1 ↔ j ∈ (e (x b) 0).1)

/-- The candidate list consists of the actual point image alone. -/
theorem normPointCandidates_eq {x : Perm (Fin Q.d)} {a : Perm (Fin m)}
    (ha : Product.IsProd e x 1 fun _ => a) (i : Fin m) :
    normPointCandidates Q e x i = [a i] := by
  have hpred : ∀ j : Fin m,
      ((List.finRange Q.d).all fun b =>
        decide (i ∈ (e b 0).1 ↔ j ∈ (e (x b) 0).1)) = decide (j = a i) := by
    intro j
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
    exact normIncidence_image_iff Q e ha i j
  simp only [normPointCandidates, hpred, List.filter_eq]
  simp

/-- Read the first candidate, with the input point as an unused fallback. This definition
uses finite loops and no choice of a permutation. -/
def normPointImage (x : Perm (Fin Q.d)) (i : Fin m) : Fin m :=
  (normPointCandidates Q e x i).getD 0 i

/-- Incidence recovery computes the homomorphism used by the model, despite its definition
by classical choice. -/
theorem normPointImage_eq (hS : Q.ProductStructure m k 1 e) (x : Q.ρ.range) (i : Fin m) :
    normPointImage Q e x.1 i = Q.permHom e hS x i := by
  rw [normPointImage, normPointCandidates_eq Q e (Q.permOf_spec e hS x)]
  rfl

end GI.Impl
