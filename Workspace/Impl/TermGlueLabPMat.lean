module

public import Workspace.Impl.TermGlueLabPCSum
public import Workspace.Impl.TermGlueLabPE
public import Workspace.Impl.TermGlueLabPCall

@[expose] public section

/-!
# The matrices of the linear part in the coordinates `E`

Step 5 of the label program. The coordinates `E` of `A/B(x)` send the class with
coordinate vector `z` (over the generators `a_i` of `N`) to `z V mod d` (`tmGLPE_g`). Let `U` be
the inverse of `V` and let the rows of `C` be coordinate vectors of `h⁻¹ a_j h`. Then the map
`E ∘ κ_h ∘ E⁻¹` sends `e_j` to row `j` of `U C V`, reduced mod `d`. In the contract's convention
(entry `(i, j)` is coordinate `i` of the image of `e_j`) its matrix is the transpose of `U C V`,
with row `i` reduced mod `d_i` (`tmGLP_mat`). The offsets are vectors `z V mod d`
(`tmGLP_vecZ`).

* `tmGLP_coord_class`: a coordinate vector computed by `linElementCoordinates` gives the class
  of the element (`linElementCoordinates_map`);
* `tmGLP_κ_g`: `κ_h` in coordinates is `z ↦ z C`;
* `tmGLP_mat`: the matrix of any additive map that is `κ_h` read through `E`.
-/

namespace GI.Impl

open GI.Multicoset GI.Cited Equiv Matrix

section Mat

variable {P : Type*} [Group P] {Ω : Type} [RAct P Ω] {q : ℕ}
variable {N : Subgroup P} {A : Type*} [CommGroup A] {φ : N →* A} {x : Fin q → Ω}

/-- **`κ_h` in coordinates.** If row `j` of `C` has the class of `h⁻¹ a_j h`, then `κ_h` sends
the class with coordinates `z` to the class with coordinates `z C`. -/
theorem tmGLP_κ_g {H : Subgroup P} {hn : Normalizes H N} {hker : TmGLKer N H φ} {t : ℕ}
    {a : Fin t → P} (ha : ∀ i, a i ∈ N) {h : P} (hD : h ∈ Aut H (types N x))
    {C : Matrix (Fin t) (Fin t) ℤ}
    (hC : ∀ j, tmGLPg N φ x a (C j) = Additive.ofMul (tmGLc N φ x (h⁻¹ * a j * h)))
    (z : Fin t → ℤ) :
    tmGLκ hn hker h (Additive.toMul (tmGLPg N φ x a z)) =
      Additive.toMul (tmGLPg N φ x a (Matrix.vecMul z C)) := by
  have e1 : tmGLPg N φ x a z = ∑ j, z j • Additive.ofMul (tmGLc N φ x (a j)) := by
    simp [tmGLPg, linCoordMap]
  have e2 : Matrix.vecMul z C = ∑ j, z j • C j := by
    funext i
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
  rw [e2, map_sum, e1, toMul_sum, map_prod]
  simp only [map_zsmul, toMul_zsmul, map_zpow, toMul_ofMul, hC]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [tmGLκ_c hker hD (ha j)]
  rfl

/-- The rows of `U` are sent to the basis vectors when `U V = 1`. -/
theorem tmGLP_map_row {t : ℕ} {U V D : Matrix (Fin t) (Fin t) ℤ} (hUV : U * V = 1) (j : Fin t) :
    tmGLQMap V D (U j) = Pi.single j 1 := by
  funext i
  have e : Matrix.vecMul (U j) V i = (U * V) j i := rfl
  change ((Matrix.vecMul (U j) V i : ℤ) : ZMod (tmGLQMod D i)) = _
  rw [e, hUV]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne' hij, Pi.single_eq_of_ne hij]

/-- The reduced value of an integer in `ZMod (D i i)`. -/
theorem tmGLP_val_cast {t : ℕ} {D : Matrix (Fin t) (Fin t) ℤ} (hpos : ∀ i, 0 < D i i) (i : Fin t)
    (k : ℤ) : (((k : ZMod (tmGLQMod D i))).val : ℤ) = k % D i i := by
  have hd : 0 < tmGLQMod D i := tmGLQMod_pos hpos i
  haveI : NeZero (tmGLQMod D i) := ⟨hd.ne'⟩
  rw [ZMod.val_intCast]
  congr 1
  simp only [tmGLQMod]
  exact Int.toNat_of_nonneg (hpos i).le

/-- **The offset vectors**: the reduced coordinates of `z V mod d`. -/
theorem tmGLP_vecZ {t : ℕ} {V D : Matrix (Fin t) (Fin t) ℤ} (hpos : ∀ i, 0 < D i i)
    (z : Fin t → ℤ) : tmGLVecZ (tmGLQMap V D z) = fun i => Matrix.vecMul z V i % D i i := by
  funext i
  exact tmGLP_val_cast hpos i _

/-- **The matrix of the linear part.** Let `E` be coordinates with `E(g z) = z V mod d`, let
`U V = 1`, and let `f` act on classes in coordinates as `z ↦ z C`. Then every additive map `F`
that is `f` read through `E` has matrix `(i, j) ↦ (U C V)_{j i} mod d_i`. -/
theorem tmGLP_mat {t : ℕ} {a : Fin t → P} {U V D C : Matrix (Fin t) (Fin t) ℤ}
    (hpos : ∀ i, 0 < D i i) (hUV : U * V = 1)
    (E : Additive (tmGLV N φ x) ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ z, E (tmGLPg N φ x a z) = tmGLQMap V D z)
    (f : tmGLV N φ x →* tmGLV N φ x)
    (hf : ∀ z, f (Additive.toMul (tmGLPg N φ x a z)) =
      Additive.toMul (tmGLPg N φ x a (Matrix.vecMul z C)))
    (F : tmGLVec (tmGLQMod D) →+ tmGLVec (tmGLQMod D))
    (hF : ∀ w, F (E w) = E (Additive.ofMul (f (Additive.toMul w)))) :
    tmGLMat (tmGLQMod D) F = fun i j => (U * C * V) j i % D i i := by
  funext i j
  have h1 : F (Pi.single j 1) = tmGLQMap V D (Matrix.vecMul (U j) C) := by
    rw [← tmGLP_map_row (D := D) hUV j, ← hE, hF, hf, ← hE]
    rfl
  have h2 : Matrix.vecMul (Matrix.vecMul (U j) C) V i = (U * C * V) j i := by
    rw [Matrix.vecMul_vecMul]
    rw [Matrix.mul_assoc]
    rfl
  simp only [tmGLMat, h1]
  rw [← h2]
  exact tmGLP_val_cast hpos i _

end Mat

/-! ### Coordinates from `linElementCoordinates` -/

section Coord

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {q : ℕ}
variable {N : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] {φ : N →* A} {x : Fin q → Ω}

/-- **A computed coordinate vector gives the class.** -/
theorem tmGLP_coord_class {σN : List (Perm (Fin n))} (hN : gens σN = N) {y : Perm (Fin n)}
    (hy : y ∈ gens σN) {z : Fin σN.length → ℤ} (hz : TmGLPCoordOf σN y z) :
    tmGLPg N φ x (fun i => σN[i.val]) z = Additive.ofMul (tmGLc N φ x y) := by
  obtain ⟨prog, hp, he⟩ := hz
  let π : gens σN →* tmGLV N φ x :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hN.le)
  have hπ : ∀ w (hw : w ∈ gens σN), π ⟨w, hw⟩ = tmGLc N φ x w := by
    intro w hw
    simp only [π, tmGLc, dif_pos (hN ▸ hw)]
    rfl
  have hm := linElementCoordinates_map σN π y hy prog z hp he
  have hv : (fun i : Fin σN.length => π (linIntoSubgroup (gens σN) σN[i.val])) =
      fun i => tmGLc N φ x σN[i.val] := by
    funext i
    have hi : σN[i.val] ∈ gens σN := Subgroup.subset_closure (List.getElem_mem _)
    rw [show linIntoSubgroup (gens σN) σN[i.val] = ⟨σN[i.val], hi⟩ from by
      simp [linIntoSubgroup, dif_pos hi]]
    exact hπ _ hi
  rw [hv, hπ y hy] at hm
  exact congrArg Additive.ofMul hm

end Coord

end GI.Impl
