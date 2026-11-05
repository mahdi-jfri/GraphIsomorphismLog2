module

public import Workspace.Impl.LinModMatrix
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-! Finite abelian coordinates after Smith reduction. Matrices record the
images of the coordinate generators, with entries reduced in their target
coordinate. This representation permits reduction after every SLP product. -/
namespace GI.Impl
open scoped BigOperators

abbrev linFiniteVec {d : ℕ} (m : Fin d → ℕ) := ∀ i, ZMod (m i)

noncomputable def linFiniteBasis {d : ℕ} (m : Fin d → ℕ) (j : Fin d) : linFiniteVec m :=
  Pi.single j 1

theorem linFiniteDecompose {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (x : linFiniteVec m) :
    ∑ j, (x j).val • linFiniteBasis m j = x := by
  classical
  funext i
  haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single i]
  · simp [linFiniteBasis, nsmul_eq_mul]
  · intro j hj hji
    simp [linFiniteBasis, Pi.single_eq_of_ne (Ne.symm hji)]
  · simp

noncomputable def linFiniteMatrix {d : ℕ} (m : Fin d → ℕ)
    (f : linFiniteVec m →+ linFiniteVec m) (i j : Fin d) : ℕ :=
  (f (linFiniteBasis m j) i).val

/-- Every homomorphism is determined by its reduced generator images. -/
theorem linFiniteMatrix_apply {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (f : linFiniteVec m →+ linFiniteVec m) (x : linFiniteVec m) (i : Fin d) :
    f x i = ((∑ j, linFiniteMatrix m f i j * (x j).val : ℕ) : ZMod (m i)) := by
  classical
  haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
  calc
    f x i = (f (∑ j, (x j).val • linFiniteBasis m j)) i := by rw [linFiniteDecompose m hm x]
    _ = ∑ j, (x j).val • f (linFiniteBasis m j) i := by
      simp only [map_sum, map_nsmul, Finset.sum_apply, Pi.smul_apply]
    _ = ((∑ j, linFiniteMatrix m f i j * (x j).val : ℕ) : ZMod (m i)) := by
      simp only [Nat.cast_sum, Nat.cast_mul, linFiniteMatrix, ZMod.natCast_zmod_val, nsmul_eq_mul]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- Taking the canonical residue after each matrix application preserves its
value in the represented finite abelian group. -/
theorem linFiniteMatrix_val {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (f : linFiniteVec m →+ linFiniteVec m) (x : linFiniteVec m) (i : Fin d) :
    (f x i).val = (∑ j, linFiniteMatrix m f i j * (x j).val) % m i := by
  rw [linFiniteMatrix_apply m hm f x i, ZMod.val_natCast]

/-- Each column respects the order of its source cyclic factor. -/
theorem linFiniteBasis_order {d : ℕ} (m : Fin d → ℕ) (j : Fin d) :
    m j • linFiniteBasis m j = 0 := by
  classical
  funext i
  by_cases h : i = j
  · subst i
    simp [linFiniteBasis, nsmul_eq_mul, ZMod.natCast_self]
  · simp [linFiniteBasis, Pi.single_eq_of_ne h]

theorem linFiniteMatrix_compatible {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (f : linFiniteVec m →+ linFiniteVec m) (i j : Fin d) :
    m i ∣ linFiniteMatrix m f i j * m j := by
  haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
  have hh := congrFun (congrArg f (linFiniteBasis_order m j)) i
  rw [map_nsmul, map_zero] at hh
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa only [Nat.cast_mul, linFiniteMatrix, ZMod.natCast_zmod_val, nsmul_eq_mul,
    Pi.smul_apply, Pi.zero_apply, mul_comm] using hh

/-- The reduced product formula used after every SLP multiplication. -/
theorem linFiniteMatrix_comp {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (f g : linFiniteVec m →+ linFiniteVec m) (i j : Fin d) :
    linFiniteMatrix m (f.comp g) i j =
      (∑ k, linFiniteMatrix m f i k * linFiniteMatrix m g k j) % m i := by
  exact linFiniteMatrix_val m hm f (g (linFiniteBasis m j)) i

theorem linFiniteMatrix_lt {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (f : linFiniteVec m →+ linFiniteVec m) (i j : Fin d) : linFiniteMatrix m f i j < m i := by
  haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
  exact ZMod.val_lt _

/-- Reducing the full affine offset after composition also preserves it. -/
theorem linFiniteAffine_comp {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (f : linFiniteVec m →+ linFiniteVec m) (u v : linFiniteVec m) (i : Fin d) :
    (f v i + u i).val =
      ((∑ j, linFiniteMatrix m f i j * (v j).val) + (u i).val) % m i := by
  haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
  rw [linFiniteMatrix_apply m hm f v i]
  have he : (u i) = ((u i).val : ZMod (m i)) := (ZMod.natCast_zmod_val (u i)).symm
  conv_lhs => rw [he]
  rw [← Nat.cast_add, ZMod.val_natCast]

end GI.Impl
