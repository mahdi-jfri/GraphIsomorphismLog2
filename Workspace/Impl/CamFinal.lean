import Workspace.Impl.CamMain
import Workspace.Impl.CamCells
import Workspace.Lang.Bridge

/-!
# Cameron recognition from Johnson identification

`cameronRecognition_of_johnson`: the cited algorithms for the group order, chief series,
centralizers in quotients and Johnson identification, together with Maróti's theorem, give a
polynomial-time algorithm for `CameronRecognitionTask`. The program is `camFuns` with the four
cited algorithms as primitives (`camProgram`). Its cost on input `x = encGroup gs` is at most
`camMainCost (wt x + 1)` (`camMain_spec`), and this is at most `camK · (wt x + 1) ^ camD`
(`cam_main_cost_poly`).
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

/-- A cited bound at the size `camPB X`, as a monomial in `X`. -/
theorem cam_boundSize_poly (p : Prim) {X : ℕ} (hX : 1 ≤ X) :
    p.boundSize (camPB X) ≤ p.c * (10 ^ 12 + 2) ^ p.k * X ^ (12 * p.k) := by
  unfold Prim.boundSize camPB
  have h1 : 1 ≤ X ^ 12 := Nat.one_le_pow _ _ hX
  have h2 : 10 ^ 12 * X ^ 12 + 2 ≤ (10 ^ 12 + 2) * X ^ 12 := by
    rw [Nat.add_mul]; omega
  calc p.c * (10 ^ 12 * X ^ 12 + 2) ^ p.k ≤ p.c * ((10 ^ 12 + 2) * X ^ 12) ^ p.k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
    _ = p.c * (10 ^ 12 + 2) ^ p.k * X ^ (12 * p.k) := by rw [mul_pow, ← pow_mul]; ring

/-- The constant factor of a cited bound. -/
def camPC (p : Prim) : ℕ := p.c * (10 ^ 12 + 2) ^ p.k

section Poly

variable (ho : GroupOrder) (hc : ChiefSeriesAlgo) (hqc : QuotientCentralizer)
  (hj : JohnsonIdentification)

/-- The degree of the cost. -/
noncomputable def camD : ℕ :=
  12 * ((groupOrderPrim ho).k + (chiefSeriesPrim hc).k + (quotientCentralizerPrim hqc).k +
    (johnsonPrim hj).k) + 183

/-- The constant of the cost. -/
noncomputable def camK : ℕ :=
  11 * (camPC (groupOrderPrim ho) + camPC (chiefSeriesPrim hc) +
    camPC (quotientCentralizerPrim hqc) + camPC (johnsonPrim hj)) +
    10 * camFacK * 4000 ^ 30 + 10 ^ 10

/-- The four cited bounds, times `X`, are at most a monomial of degree `camD`. -/
theorem cam_S4_poly {X : ℕ} (hX : 1 ≤ X) :
    X * camS4 ho hc hqc hj X ≤ (camPC (groupOrderPrim ho) + camPC (chiefSeriesPrim hc) +
      camPC (quotientCentralizerPrim hqc) + camPC (johnsonPrim hj)) * X ^ camD ho hc hqc hj := by
  have hmono : ∀ p : Prim, 12 * p.k + 1 ≤ camD ho hc hqc hj →
      X * p.boundSize (camPB X) ≤ camPC p * X ^ camD ho hc hqc hj := by
    intro p hp
    have h1 := Nat.mul_le_mul_left X (cam_boundSize_poly p hX)
    have h2 : X ^ (12 * p.k + 1) ≤ X ^ camD ho hc hqc hj := Nat.pow_le_pow_right hX hp
    calc X * p.boundSize (camPB X) ≤ X * (p.c * (10 ^ 12 + 2) ^ p.k * X ^ (12 * p.k)) := h1
      _ = camPC p * X ^ (12 * p.k + 1) := by unfold camPC; ring
      _ ≤ camPC p * X ^ camD ho hc hqc hj := Nat.mul_le_mul_left _ h2
  have a1 := hmono (groupOrderPrim ho) (by unfold camD; omega)
  have a2 := hmono (chiefSeriesPrim hc) (by unfold camD; omega)
  have a3 := hmono (quotientCentralizerPrim hqc) (by unfold camD; omega)
  have a4 := hmono (johnsonPrim hj) (by unfold camD; omega)
  unfold camS4
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.add_mul]
  omega

theorem cam_poly_arith {A B U V W Z Y : ℕ} (hA : A ≤ Z) (hB : B ≤ Z) (hU : U ≤ V) (hW : W ≤ Y) :
    10 * A + 10 * U + B + W ≤ 11 * Z + 10 * V + Y := by omega

/-- **The cost is polynomial.** -/
theorem cam_main_cost_poly {X : ℕ} (hX : 1 ≤ X) :
    camMainCost ho hc hqc hj X ≤ camK ho hc hqc hj * X ^ camD ho hc hqc hj := by
  have hS := cam_S4_poly ho hc hqc hj hX
  have hS' : camS4 ho hc hqc hj X ≤ X * camS4 ho hc hqc hj X := Nat.le_mul_of_pos_left _ hX
  have h182 : X ^ 182 ≤ X ^ camD ho hc hqc hj := Nat.pow_le_pow_right hX (by unfold camD; omega)
  have h4 : X ^ 4 ≤ X ^ camD ho hc hqc hj := Nat.pow_le_pow_right hX (by unfold camD; omega)
  have k1 := Nat.mul_le_mul_left (camFacK * 4000 ^ 30) h182
  have k2 := Nat.mul_le_mul_left (10 ^ 10) h4
  set S := camPC (groupOrderPrim ho) + camPC (chiefSeriesPrim hc) +
    camPC (quotientCentralizerPrim hqc) + camPC (johnsonPrim hj)
  set Y := X ^ camD ho hc hqc hj
  have e1 : camMainCost ho hc hqc hj X = 10 * (X * camS4 ho hc hqc hj X) +
      10 * (camFacK * 4000 ^ 30 * X ^ 182) + camS4 ho hc hqc hj X + 10 ^ 10 * X ^ 4 := by
    unfold camMainCost camTailCost; ring
  have e2 : camK ho hc hqc hj * Y = 11 * (S * Y) + 10 * (camFacK * 4000 ^ 30 * Y) +
      10 ^ 10 * Y := by
    unfold camK; ring
  rw [e1, e2]
  exact cam_poly_arith hS (hS'.trans hS) k1 k2

end Poly

/-- **The program.** The functions `camFuns` at base `0`, and the four cited algorithms as
primitives `0, 1, 2, 3`. -/
noncomputable def camProgram (ho : GroupOrder) (hc : ChiefSeriesAlgo) (hqc : QuotientCentralizer)
    (hj : JohnsonIdentification) : Program :=
  ⟨camFuns 0 0 1 2 3, [groupOrderPrim ho, chiefSeriesPrim hc, quotientCentralizerPrim hqc,
    johnsonPrim hj]⟩

theorem camProgram_at (ho : GroupOrder) (hc : ChiefSeriesAlgo) (hqc : QuotientCentralizer)
    (hj : JohnsonIdentification) : CamAt (camProgram ho hc hqc hj) 0 0 1 2 3 ho hc hqc hj := by
  refine camAt_of ?_ rfl rfl rfl rfl
  have h := Program.hasAt_append [] (camFuns 0 0 1 2 3) []
    [groupOrderPrim ho, chiefSeriesPrim hc, quotientCentralizerPrim hqc, johnsonPrim hj]
  simp only [List.nil_append, List.append_nil, List.length_nil] at h
  exact h

/-- **Cameron recognition from Johnson identification.** -/
theorem cameronRecognition_of_johnson (hMa : MarotiPrimitive) (hj : JohnsonIdentification)
    (ho : GroupOrder) (hc : ChiefSeriesAlgo) (hqc : QuotientCentralizer) :
    CameronRecognition := by
  refine polyTimeAt_ofVal_of_lang_cells (camProgram ho hc hqc hj) 0 (camK ho hc hqc hj)
    (camD ho hc hqc hj) 1 1 (fun I => cam_encGroup_cells I.gs) fun I => ?_
  refine (camMain_spec hMa (camProgram_at ho hc hqc hj) I.gs I.le_n I.primitive).mono
    fun v c h => ⟨h.1, h.2.trans (cam_main_cost_poly ho hc hqc hj (by omega))⟩

end GI.Impl
