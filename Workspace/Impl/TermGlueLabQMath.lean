module

public import Workspace.Impl.LinSmith
public import Workspace.Impl.LinHermite
public import Workspace.Impl.LinPresentation
public import Workspace.Impl.TermGlueLabAff

@[expose] public section

/-!
# The quotient of `ℤ^c` by integer relations, in finite abelian coordinates

Step 5 of the label program (proof of Theorem A.23, through the finite abelian
coordinates of the proof of Theorem A.20: "Integer Hermite and Smith normal forms, including
their transformation matrices, have polynomial bit complexity").

Let `M` be an integer matrix with `r` rows and `c ≤ r` columns, of full column rank. Its rows
are relations, and `Q = ℤ^c / ⟨rows of M⟩` (`linRelations M`). The normal-form route is:

1. Hermite: `U M = H` with `U` unimodular. The top `c × c` block `H_b` of `H` is upper
   triangular with positive diagonal, and the other rows are zero, so `H_b` has the same row
   lattice as `M`.
2. Smith of `H_b`: `U' H_b V = D` with `U', V` unimodular and `D` diagonal with positive
   diagonal entries `d_i`.
3. Then `x ↦ ((x V)_i mod d_i)_i` is onto `∏_i ℤ/d_i`, with kernel the row lattice of `M`.

`tmGLQ_rel_iff` is step 3 as a test, and `tmGLQOutEquiv` is the resulting isomorphism
`Q ≃+ ∏_i ℤ/d_i`. It is general: nothing here is special to the label step, so the object glue
can use the same program.
-/

namespace GI.Impl

open Matrix GI.Cited

variable {r c : ℕ}

/-- **The relation test after Hermite and Smith.** `x` lies in the row lattice of `M` exactly
when `d_i` divides `(x V)_i` for every `i`. -/
theorem tmGLQ_rel_iff (hcr : c ≤ r) (M H : Matrix (Fin r) (Fin c) ℤ)
    (U : Matrix (Fin r) (Fin r) ℤ) (hU : IsUnit U.det) (hUM : U * M = H)
    (hH : IsHermiteForm H) (U' V D : Matrix (Fin c) (Fin c) ℤ) (hU' : IsUnit U'.det)
    (hV : IsUnit V.det) (hS : U' * linHermiteBlock hcr H * V = D) (hD : IsSmithForm D)
    (x : Fin c → ℤ) :
    (∃ z, Matrix.vecMul z M = x) ↔ ∀ i, D i i ∣ (Matrix.vecMul x V) i := by
  rw [← linSmithRelation (linHermiteBlock hcr H) U' V D hU' hV hS hD x]
  constructor
  · intro hz
    obtain ⟨y, hy⟩ := (linRowEquation_iff M U hU x).mp hz
    rw [hUM, linTopRows hcr H hH] at hy
    exact ⟨_, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨Matrix.vecMul (linPad y) U, linRowLift hUM (by rw [linPadEquation hcr H hH, hy])⟩

/-- The diagonal entries are positive: `D = U' H_b V` and `H_b` is nonsingular. -/
theorem tmGLQ_diag_pos (hcr : c ≤ r) (H : Matrix (Fin r) (Fin c) ℤ) (hH : IsHermiteForm H)
    (U' V D : Matrix (Fin c) (Fin c) ℤ) (hU' : IsUnit U'.det) (hV : IsUnit V.det)
    (hS : U' * linHermiteBlock hcr H * V = D) (hD : IsSmithForm D) (i : Fin c) :
    0 < D i i := by
  refine linSmithDiagonal_pos D hD ?_ i
  rw [← hS, Matrix.det_mul, Matrix.det_mul]
  refine mul_ne_zero (mul_ne_zero hU'.ne_zero (linHermiteBlock_det_ne hcr H hH)) hV.ne_zero

/-! ### The coordinate map -/

/-- The moduli `d_i` as natural numbers. -/
def tmGLQMod (D : Matrix (Fin c) (Fin c) ℤ) : Fin c → ℕ := fun i => (D i i).toNat

/-- **The coordinate map** `x ↦ ((x V)_i mod d_i)_i`. -/
def tmGLQMap (V D : Matrix (Fin c) (Fin c) ℤ) : (Fin c → ℤ) →+ tmGLVec (tmGLQMod D) where
  toFun x i := ((Matrix.vecMul x V) i : ZMod (tmGLQMod D i))
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp [Matrix.add_vecMul]

theorem tmGLQMap_apply (V D : Matrix (Fin c) (Fin c) ℤ) (x : Fin c → ℤ) (i : Fin c) :
    tmGLQMap V D x i = ((Matrix.vecMul x V) i : ZMod (tmGLQMod D i)) := rfl

/-- The coordinate map is onto, since `V` is invertible over `ℤ`. -/
theorem tmGLQMap_surj (V D : Matrix (Fin c) (Fin c) ℤ) (hV : IsUnit V.det)
    (hpos : ∀ i, 0 < D i i) : Function.Surjective (tmGLQMap V D) := by
  intro y
  refine ⟨Matrix.vecMul (fun i => ((y i).val : ℤ)) V⁻¹, ?_⟩
  funext i
  rw [tmGLQMap_apply, Matrix.vecMul_vecMul, V.nonsing_inv_mul hV, Matrix.vecMul_one]
  haveI : NeZero (tmGLQMod D i) := ⟨by simp [tmGLQMod, hpos i]⟩
  show (((y i).val : ℤ) : ZMod (tmGLQMod D i)) = y i
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-! ### The output of the quotient program -/

/-- **What the quotient program returns** on a relation matrix `M` with `c` columns:
`[d, V]` with `d` the positive moduli and `V` unimodular, such that `x` is a relation exactly
when `d_i ∣ (x V)_i` for all `i`. -/
def TmGLQOut {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℤ) (out : GI.Cited.Val) : Prop :=
  ∃ V D : Matrix (Fin c) (Fin c) ℤ,
    out = .list [GI.Lang.linVecVal (fun i => D i i), encIntMatrix V] ∧ IsUnit V.det ∧
    (∀ i, 0 < D i i) ∧ ∀ x, (∃ z, Matrix.vecMul z M = x) ↔ ∀ i, D i i ∣ (Matrix.vecMul x V) i

/-- The kernel of the coordinate map, from the output facts alone. -/
theorem TmGLQOut.ker {M : Matrix (Fin r) (Fin c) ℤ} {V D : Matrix (Fin c) (Fin c) ℤ}
    (hpos : ∀ i, 0 < D i i) (hrel : ∀ x, (∃ z, Matrix.vecMul z M = x) ↔ ∀ i, D i i ∣ (Matrix.vecMul x V) i) :
    (tmGLQMap V D).ker = (linRelations M).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, linRelations, LinearMap.mem_range]
  have hx : (∃ z, M.vecMulLinear z = x) ↔ ∃ z, Matrix.vecMul z M = x := Iff.rfl
  rw [hx, hrel x]
  constructor
  · intro h i
    have hi := congrFun h i
    rw [tmGLQMap_apply] at hi
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hi
    simpa [tmGLQMod, Int.toNat_of_nonneg (hpos i).le] using hd
  · intro h
    funext i
    rw [tmGLQMap_apply]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
    simpa [tmGLQMod, Int.toNat_of_nonneg (hpos i).le] using h i

/-- **The isomorphism from the output facts**: `ℤ^c / ⟨rows of M⟩ ≃+ ∏_i ℤ/d_i`. -/
noncomputable def tmGLQOutEquiv {M : Matrix (Fin r) (Fin c) ℤ} {V D : Matrix (Fin c) (Fin c) ℤ}
    (hV : IsUnit V.det) (hpos : ∀ i, 0 < D i i)
    (hrel : ∀ x, (∃ z, Matrix.vecMul z M = x) ↔ ∀ i, D i i ∣ (Matrix.vecMul x V) i) :
    ((Fin c → ℤ) ⧸ (linRelations M).toAddSubgroup) ≃+ tmGLVec (tmGLQMod D) :=
  (QuotientAddGroup.quotientAddEquivOfEq (TmGLQOut.ker hpos hrel).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (tmGLQMap_surj V D hV hpos))

theorem tmGLQOutEquiv_mk {M : Matrix (Fin r) (Fin c) ℤ} {V D : Matrix (Fin c) (Fin c) ℤ}
    (hV : IsUnit V.det) (hpos : ∀ i, 0 < D i i)
    (hrel : ∀ x, (∃ z, Matrix.vecMul z M = x) ↔ ∀ i, D i i ∣ (Matrix.vecMul x V) i) (x : Fin c → ℤ) :
    tmGLQOutEquiv hV hpos hrel (QuotientAddGroup.mk x) = tmGLQMap V D x := rfl

/-- The moduli as integers are the diagonal entries. -/
theorem tmGLQMod_cast {D : Matrix (Fin c) (Fin c) ℤ} (hpos : ∀ i, 0 < D i i) (i : Fin c) :
    ((tmGLQMod D i : ℕ) : ℤ) = D i i := by
  simp [tmGLQMod, Int.toNat_of_nonneg (hpos i).le]

end GI.Impl
