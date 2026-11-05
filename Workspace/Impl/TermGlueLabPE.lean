module

public import Workspace.Impl.TermGlueLabPCoord

@[expose] public section

/-!
# The coordinates `E` of the label torsor

Step 5 of the label program. From the coordinate map `tmGLPg` onto `A/B(x)`
(onto by `tmGLPg_surj`, kernel the row lattice of `[M; Z]` by `tmGLP_ker`) and the output
`[d, V]` of the quotient program on `[M; Z]`:

* `tmGLPE`: `A/B(x) ≃+ ∏_i ℤ/d_i`, with `tmGLPE_g`: the class `Σ z_i [a_i]` goes to
  `((z V)_i mod d_i)_i`;
* `tmGLPEo`: `A/B(x) × ℤˣ ≃+ ∏_i ℤ/d'_i` with `d' = (2, d)` (`Fin.cons`), the orientation
  coordinate in front through `ℤˣ ≅ ℤ/2` (`tmGLPUnits`).

These are the maps `E` of `tmGL_contract_trans'` and `tmGL_contract_trans`.
-/

namespace GI.Impl

open GI.Multicoset GI.Cited Equiv Matrix

section E

variable {P : Type*} [Group P] {Ω : Type} [RAct P Ω] {q : ℕ}
variable {N : Subgroup P} {A : Type*} [CommGroup A] {φ : N →* A} {x : Fin q → Ω}
variable {t s : ℕ} {a : Fin t → P} (ha : ∀ i, a i ∈ N) (hgen : N ≤ Subgroup.closure (Set.range a))
  {M : Matrix (Fin t) (Fin t) ℤ}
  (hM : ∀ z, linCoordMap (fun i => phiT N φ (a i)) z = 0 ↔ ∃ y, Matrix.vecMul y M = z)
  {Z : Matrix (Fin s) (Fin t) ℤ}
  (hB : labelGroup N φ x = Subgroup.closure (Set.range fun j =>
      Additive.toMul (linCoordMap (fun i => phiT N φ (a i)) (Z j))))
  {V D : Matrix (Fin t) (Fin t) ℤ} (hV : IsUnit V.det) (hpos : ∀ i, 0 < D i i)
  (hrel : ∀ w, (∃ y, Matrix.vecMul y (tmGLQStack M Z) = w) ↔ ∀ i, D i i ∣ (Matrix.vecMul w V) i)

include ha hM hB in
theorem tmGLPg_ker_eq :
    (tmGLPg N φ x a).ker = (linRelations (tmGLQStack M Z)).toAddSubgroup := by
  ext z
  rw [AddMonoidHom.mem_ker, tmGLP_ker ha M hM Z hB z, Submodule.mem_toAddSubgroup, linRelations,
    LinearMap.mem_range]
  rfl

/-- **The coordinates of `A/B(x)`.** -/
noncomputable def tmGLPE : Additive (tmGLV N φ x) ≃+ tmGLVec (tmGLQMod D) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective _ (tmGLPg_surj (φ := φ) (x := x) ha hgen)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (tmGLPg_ker_eq ha hM hB)).trans
      (tmGLQOutEquiv hV hpos hrel))

/-- **`E` on a class with known coordinates.** -/
theorem tmGLPE_g (z : Fin t → ℤ) :
    tmGLPE ha hgen hM hB hV hpos hrel (tmGLPg N φ x a z) = tmGLQMap V D z := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (tmGLPg_surj (φ := φ) (x := x) ha hgen)).symm (tmGLPg N φ x a z) =
      QuotientAddGroup.mk z := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [tmGLPE, AddEquiv.trans_apply, h]
  rfl

end E

/-! ### The orientation coordinate -/

/-- `ℤˣ ≅ ℤ/2`. -/
def tmGLPUnits : Additive ℤˣ ≃+ ZMod 2 where
  toFun u := if Additive.toMul u = 1 then 0 else 1
  invFun z := if z = 0 then Additive.ofMul 1 else Additive.ofMul (-1)
  left_inv u := by
    rcases Int.units_eq_one_or (Additive.toMul u) with h | h
    · have : u = Additive.ofMul 1 := by rw [← h]; rfl
      subst this; rfl
    · have : u = Additive.ofMul (-1) := by rw [← h]; rfl
      subst this; decide
  right_inv z := by
    fin_cases z <;> rfl
  map_add' u v := by
    rcases Int.units_eq_one_or (Additive.toMul u) with hu | hu <;>
    rcases Int.units_eq_one_or (Additive.toMul v) with hv | hv
    all_goals
      have eu : u = Additive.ofMul (Additive.toMul u) := rfl
      have ev : v = Additive.ofMul (Additive.toMul v) := rfl
      rw [hu] at eu
      rw [hv] at ev
      subst eu ev
      decide

/-- The coordinates with one more coordinate `ℤ/k` in front. -/
def tmGLPCons {d : ℕ} (k : ℕ) (m : Fin d → ℕ) :
    ZMod k × tmGLVec m ≃+ tmGLVec (Fin.cons k m : Fin (d + 1) → ℕ) where
  toFun p := fun i => Fin.cases (motive := fun i => ZMod ((Fin.cons k m : Fin (d + 1) → ℕ) i))
    (ZMod.ringEquivCongr (Fin.cons_zero (α := fun _ => ℕ) k m).symm p.1)
    (fun j => ZMod.ringEquivCongr (Fin.cons_succ (α := fun _ => ℕ) k m j).symm (p.2 j)) i
  invFun v := (ZMod.ringEquivCongr (Fin.cons_zero (α := fun _ => ℕ) k m) (v 0),
    fun j => ZMod.ringEquivCongr (Fin.cons_succ (α := fun _ => ℕ) k m j) (v j.succ))
  left_inv p := by
    ext
    · simp [ZMod.ringEquivCongr_ringEquivCongr_apply]
    · simp [ZMod.ringEquivCongr_ringEquivCongr_apply]
  right_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [ZMod.ringEquivCongr_ringEquivCongr_apply]
    · simp [ZMod.ringEquivCongr_ringEquivCongr_apply]
  map_add' p p' := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [map_add]
    · simp [map_add]

/-- `Additive (X × Y) ≃+ Additive X × Additive Y`. -/
def tmGLPAddProd (X Y : Type*) [Mul X] [Mul Y] : Additive (X × Y) ≃+ Additive X × Additive Y where
  toFun p := (Additive.ofMul (Additive.toMul p).1, Additive.ofMul (Additive.toMul p).2)
  invFun p := Additive.ofMul (Additive.toMul p.1, Additive.toMul p.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

section Eo

variable {P : Type*} [Group P] {Ω : Type} [RAct P Ω] {q : ℕ}
variable {N : Subgroup P} {A : Type*} [CommGroup A] {φ : N →* A} {x : Fin q → Ω}
variable {t s : ℕ} {a : Fin t → P} (ha : ∀ i, a i ∈ N) (hgen : N ≤ Subgroup.closure (Set.range a))
  {M : Matrix (Fin t) (Fin t) ℤ}
  (hM : ∀ z, linCoordMap (fun i => phiT N φ (a i)) z = 0 ↔ ∃ y, Matrix.vecMul y M = z)
  {Z : Matrix (Fin s) (Fin t) ℤ}
  (hB : labelGroup N φ x = Subgroup.closure (Set.range fun j =>
      Additive.toMul (linCoordMap (fun i => phiT N φ (a i)) (Z j))))
  {V D : Matrix (Fin t) (Fin t) ℤ} (hV : IsUnit V.det) (hpos : ∀ i, 0 < D i i)
  (hrel : ∀ w, (∃ y, Matrix.vecMul y (tmGLQStack M Z) = w) ↔ ∀ i, D i i ∣ (Matrix.vecMul w V) i)

/-- **The coordinates of `A/B(x) × C₂`**, the orientation coordinate in front. -/
noncomputable def tmGLPEo : Additive (tmGLV N φ x × ℤˣ) ≃+
    tmGLVec (Fin.cons 2 (tmGLQMod D) : Fin (t + 1) → ℕ) :=
  (tmGLPAddProd _ _).trans (AddEquiv.prodComm.trans ((AddEquiv.prodCongr tmGLPUnits
    (tmGLPE ha hgen hM hB hV hpos hrel)).trans (tmGLPCons 2 (tmGLQMod D))))

end Eo

end GI.Impl
