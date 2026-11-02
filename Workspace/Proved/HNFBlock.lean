import Workspace.Proved.HNFMod
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# The transform from one more Hermite form

Let `A'` be a square nonsingular integer matrix and `d ≠ 0` with `d ℤ^r` in its row lattice. We
want its Hermite form `H'` together with the unimodular `U'` with `U' A' = H'`, keeping all
numbers small.

Take `K > 0` and the `2r × 2r` matrix `M = [[A', I], [0, K I]]` (`hnfBig`). Its row lattice is
`Λ = {(y A', y + K z)}`, and it contains `|d| K ℤ^{2r}` (`hnfBig_single_mem`). So the modular
algorithm (`hnfModMat_spec`) computes its Hermite form `HM` with modulus `|d| K`.

* The last `r` rows of `HM` vanish on the first `r` columns, so they are `(0, K z)` because
  `A'` is nonsingular. Their diagonal entries are exactly `K` (`hnfBig_diag`): they are positive
  multiples of `K`, and they divide `K` because `(0, K e_t)` lies in `Λ` and `HM` is triangular
  (`hnf_tri_coeff`).
* A first-block row of `HM` is `(y A', y + K z)`. So its first block `H'` is `y A'`, and its second
  block `X` is `y` mod `K`, with entries in `[0, K)`.

So `y` is the symmetric residue of `X` mod `K` as soon as `2 |y| < K`. Cramer's rule gives
`|y| ≤ r · max |adj A'|`, because the entries of `H'` are at most `|det H'| = |det A'|`.
-/

namespace GI.Proved

open Matrix GI.Cited

variable {r : ℕ}

/-! ### Vectors on two blocks -/

/-- The vector `(u, v)` with `u, v : ℤ^r`. -/
def hnfJoin (u v : Fin r → ℤ) : Fin (r + r) → ℤ :=
  fun j => if h : (j : ℕ) < r then u ⟨j, h⟩ else v ⟨j - r, by omega⟩

@[simp] theorem hnfJoin_castAdd (u v : Fin r → ℤ) (j : Fin r) :
    hnfJoin u v (Fin.castAdd r j) = u j := by
  simp [hnfJoin]

@[simp] theorem hnfJoin_natAdd (u v : Fin r → ℤ) (j : Fin r) :
    hnfJoin u v (Fin.natAdd r j) = v j := by
  simp [hnfJoin]

theorem hnfJoin_sum {ι : Type*} (S : Finset ι) (a : ι → ℤ) (u v : ι → Fin r → ℤ) :
    ∑ i ∈ S, a i • hnfJoin (u i) (v i) = hnfJoin (∑ i ∈ S, a i • u i) (∑ i ∈ S, a i • v i) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hnfJoin]
  split_ifs <;> simp

theorem hnfJoin_add (u v u' v' : Fin r → ℤ) :
    hnfJoin u v + hnfJoin u' v' = hnfJoin (u + u') (v + v') := by
  funext j; simp only [hnfJoin, Pi.add_apply]; split_ifs <;> rfl

theorem hnfJoin_eq_iff {u v u' v' : Fin r → ℤ} : hnfJoin u v = hnfJoin u' v' ↔ u = u' ∧ v = v' := by
  constructor
  · intro h
    refine ⟨funext fun j => ?_, funext fun j => ?_⟩
    · have := congrFun h (Fin.castAdd r j); rwa [hnfJoin_castAdd, hnfJoin_castAdd] at this
    · have := congrFun h (Fin.natAdd r j); rwa [hnfJoin_natAdd, hnfJoin_natAdd] at this
  · rintro ⟨rfl, rfl⟩; rfl

/-! ### The big matrix -/

/-- `M = [[A', I], [0, K I]]`. -/
def hnfBig (A' : Matrix (Fin r) (Fin r) ℤ) (K : ℤ) : Matrix (Fin (r + r)) (Fin (r + r)) ℤ :=
  fun i j => if hi : (i : ℕ) < r then
      (if hj : (j : ℕ) < r then A' ⟨i, hi⟩ ⟨j, hj⟩ else if (j : ℕ) - r = i then 1 else 0)
    else (if (j : ℕ) < r then 0 else if (j : ℕ) - r = (i : ℕ) - r then K else 0)

theorem hnfBig_top (A' : Matrix (Fin r) (Fin r) ℤ) (K : ℤ) (i : Fin r) :
    hnfBig A' K (Fin.castAdd r i) = hnfJoin (A' i) (Pi.single i 1) := by
  funext j
  simp only [hnfBig, hnfJoin, Fin.val_castAdd, i.isLt, dite_true]
  split_ifs with h1 h2 h2
  · rfl
  · simp [Pi.single_apply, Fin.ext_iff, h2]
  · have : ((⟨(j : ℕ) - r, by omega⟩ : Fin r) ≠ i) := fun e => h2 (by rw [← e])
    simp [this]

theorem hnfBig_bot (A' : Matrix (Fin r) (Fin r) ℤ) (K : ℤ) (t : Fin r) :
    hnfBig A' K (Fin.natAdd r t) = hnfJoin 0 (Pi.single t K) := by
  funext j
  simp only [hnfBig, hnfJoin, Fin.val_natAdd, show ¬ r + (t : ℕ) < r by omega, dite_false,
    Nat.add_sub_cancel_left]
  split_ifs with h1 h2
  · rfl
  · simp [Pi.single_apply, Fin.ext_iff, h2]
  · have : ((⟨(j : ℕ) - r, by omega⟩ : Fin r) ≠ t) := fun e => h2 (by rw [← e])
    simp [this]

/-- The row lattice of `M` is `{(y A', y + K z)}`. -/
theorem hnfBig_mem_iff (A' : Matrix (Fin r) (Fin r) ℤ) (K : ℤ) (v : Fin (r + r) → ℤ) :
    v ∈ Submodule.span ℤ (Set.range (hnfBig A' K)) ↔
      ∃ y z : Fin r → ℤ, v = hnfJoin (y ᵥ* A') (y + K • z) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨fun i => w (Fin.castAdd r i), fun t => w (Fin.natAdd r t), ?_⟩
    rw [Fin.sum_univ_add]
    simp only [hnfBig_top, hnfBig_bot]
    rw [hnfJoin_sum, hnfJoin_sum, hnfJoin_add]
    congr 1
    · funext j; simp [vecMul, dotProduct, Finset.sum_apply, mul_comm]
    · funext j; simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  · rintro ⟨y, z, rfl⟩
    refine ⟨fun i => if h : (i : ℕ) < r then y ⟨i, h⟩ else z ⟨i - r, by omega⟩, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.val_castAdd, Fin.is_lt, dite_true, Fin.val_natAdd,
      show ∀ t : Fin r, ¬ (r + (t : ℕ) < r) from fun t => by omega, dite_false,
      Nat.add_sub_cancel_left, Fin.eta, hnfBig_top, hnfBig_bot]
    rw [hnfJoin_sum, hnfJoin_sum, hnfJoin_add]
    congr 1
    · funext j; simp [vecMul, dotProduct, Finset.sum_apply, mul_comm]
    · funext j; simp [Finset.sum_apply, Pi.single_apply, mul_comm]

/-- **`|d| K ℤ^{2r}` lies in the row lattice of `M`.** -/
theorem hnfBig_single_mem {A' : Matrix (Fin r) (Fin r) ℤ} {d K : ℤ}
    (hA : ∀ j, Pi.single j d ∈ Submodule.span ℤ (Set.range A')) (j : Fin (r + r)) :
    Pi.single j (|d| * K) ∈ Submodule.span ℤ (Set.range (hnfBig A' K)) := by
  have key : Pi.single j (d * K) ∈ Submodule.span ℤ (Set.range (hnfBig A' K)) := by
    rw [hnfBig_mem_iff]
    by_cases hj : (j : ℕ) < r
    · obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hA ⟨j, hj⟩)
      refine ⟨K • w, -w, ?_⟩
      have hw' : w ᵥ* A' = Pi.single ⟨j, hj⟩ d := by
        rw [← hw]; funext l; simp [vecMul, dotProduct, Finset.sum_apply, mul_comm]
      rw [smul_vecMul, hw']
      funext l
      simp only [hnfJoin]
      split_ifs with hl
      · by_cases e : l = j
        · subst e; simp [mul_comm]
        · have : (⟨l, hl⟩ : Fin r) ≠ ⟨j, hj⟩ := fun e' => e (Fin.ext (by simpa using e'))
          simp [e, this]
      · have : l ≠ j := fun e => hl (e ▸ hj)
        simp [this]
    · refine ⟨0, Pi.single ⟨j - r, by omega⟩ d, ?_⟩
      funext l
      simp only [zero_vecMul, zero_add, hnfJoin]
      split_ifs with hl
      · have : l ≠ j := fun e => hj (e ▸ hl)
        simp [this]
      · by_cases e : l = j
        · subst e; simp [mul_comm]
        · have : (⟨(l : ℕ) - r, by omega⟩ : Fin r) ≠ ⟨j - r, by omega⟩ := fun e' =>
            e (Fin.ext (by simp at e'; omega))
          simp [e, this]
  have h := Submodule.smul_mem _ d.sign key
  rwa [← Pi.single_smul, smul_eq_mul, ← mul_assoc, Int.sign_mul_self_eq_abs] at h

/-! ### Triangular bases -/

/-- In a triangular basis with positive diagonal, a combination that vanishes on the first `p`
columns has zero coefficients on the first `p` rows. -/
theorem hnf_tri_coeff {N : ℕ} {H : Matrix (Fin N) (Fin N) ℤ} (hH : IsHermiteForm H)
    (w : Fin N → ℤ) (p : ℕ) (hv : ∀ l : Fin N, (l : ℕ) < p → (w ᵥ* H) l = 0) :
    ∀ t : Fin N, (t : ℕ) < p → w t = 0 := by
  intro t
  obtain ⟨tv, ht⟩ := t
  induction tv using Nat.strong_induction_on with
  | _ tv ih =>
  intro hp
  have h0 := hv ⟨tv, ht⟩ hp
  rw [vecMul, dotProduct, Finset.sum_eq_single ⟨tv, ht⟩] at h0
  · exact (mul_eq_zero.mp h0).resolve_right (hH.2.1 _ _ rfl).ne'
  · intro b _ hb
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hb) with hlt | hgt
    · have := ih b hlt b.isLt (show (b : ℕ) < p from lt_trans hlt hp)
      simp [this]
    · rw [hH.1 b ⟨tv, ht⟩ hgt]; simp
  · simp

/-! ### The blocks of the Hermite form of `M` -/

/-- The hypotheses: `A'` nonsingular, `d ≠ 0` with `d ℤ^r` in its row lattice, `K > 0`. -/
structure HnfSq (A' : Matrix (Fin r) (Fin r) ℤ) (d K : ℤ) : Prop where
  det_ne : A'.det ≠ 0
  d_ne : d ≠ 0
  single : ∀ j, Pi.single j d ∈ Submodule.span ℤ (Set.range A')
  K_pos : 0 < K

/-- The Hermite form of `M`, computed with modulus `|d| K`. -/
def hnfBigH (A' : Matrix (Fin r) (Fin r) ℤ) (d K : ℤ) : Matrix (Fin (r + r)) (Fin (r + r)) ℤ :=
  hnfModMat (|d| * K) (hnfBig A' K)

/-- Its first block: the Hermite form `H'` of `A'`. -/
def hnfHp (A' : Matrix (Fin r) (Fin r) ℤ) (d K : ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j => hnfBigH A' d K (Fin.castAdd r i) (Fin.castAdd r j)

/-- Its top right block: the transform mod `K`. -/
def hnfX (A' : Matrix (Fin r) (Fin r) ℤ) (d K : ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j => hnfBigH A' d K (Fin.castAdd r i) (Fin.natAdd r j)

/-- The symmetric residue of `x ∈ [0, K)`. -/
def hnfLift (K x : ℤ) : ℤ := if 2 * x < K then x else x - K

/-- The transform `U'`. -/
def hnfUp (A' : Matrix (Fin r) (Fin r) ℤ) (d K : ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j => hnfLift K (hnfX A' d K i j)

theorem hnf_vecMul_eq_zero {A' : Matrix (Fin r) (Fin r) ℤ} (h : A'.det ≠ 0) {y : Fin r → ℤ}
    (hy : y ᵥ* A' = 0) : y = 0 := by
  by_contra hne
  exact h (exists_vecMul_eq_zero_iff.mp ⟨y, hne, hy⟩)

section Blocks

variable {A' : Matrix (Fin r) (Fin r) ℤ} {d K : ℤ}

theorem hnfBigH_spec (h : HnfSq A' d K) :
    IsHermiteForm (hnfBigH A' d K) ∧
      Submodule.span ℤ (Set.range (hnfBigH A' d K)) =
        Submodule.span ℤ (Set.range (hnfBig A' K)) ∧
      ∀ i j, 0 ≤ hnfBigH A' d K i j ∧ hnfBigH A' d K i j ≤ |d| * K :=
  hnfModMat_spec (mul_pos (abs_pos.mpr h.d_ne) h.K_pos) _ (hnfBig_single_mem h.single)

theorem hnfBigH_row (h : HnfSq A' d K) (i : Fin (r + r)) :
    ∃ y z : Fin r → ℤ, hnfBigH A' d K i = hnfJoin (y ᵥ* A') (y + K • z) := by
  rw [← hnfBig_mem_iff, ← (hnfBigH_spec h).2.1]
  exact Submodule.subset_span (Set.mem_range_self i)

/-- The last `r` rows are `(0, K z)`. -/
theorem hnfBigH_bot (h : HnfSq A' d K) (t : Fin r) :
    ∃ z : Fin r → ℤ, hnfBigH A' d K (Fin.natAdd r t) = hnfJoin 0 (K • z) := by
  obtain ⟨y, z, hyz⟩ := hnfBigH_row h (Fin.natAdd r t)
  have hy : y ᵥ* A' = 0 := by
    funext j
    have := congrFun hyz (Fin.castAdd r j)
    rw [hnfJoin_castAdd, (hnfBigH_spec h).1.1 _ _ (by simp; omega)] at this
    exact this.symm
  have hy0 := hnf_vecMul_eq_zero h.det_ne hy
  exact ⟨z, by rw [hyz, hy, hy0, zero_add]⟩

/-- **The diagonal of the last block is `K`.** -/
theorem hnfBig_diag (h : HnfSq A' d K) (t : Fin r) :
    hnfBigH A' d K (Fin.natAdd r t) (Fin.natAdd r t) = K := by
  have hH := (hnfBigH_spec h).1
  have hpos : 0 < hnfBigH A' d K (Fin.natAdd r t) (Fin.natAdd r t) := hH.2.1 _ _ rfl
  apply le_antisymm
  · -- it divides `K`
    have hmem : hnfJoin 0 (Pi.single t K) ∈ Submodule.span ℤ (Set.range (hnfBigH A' d K)) := by
      rw [(hnfBigH_spec h).2.1, ← hnfBig_bot]
      exact Submodule.subset_span (Set.mem_range_self _)
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
    have hw' : w ᵥ* hnfBigH A' d K = hnfJoin 0 (Pi.single t K) := by
      rw [← hw]; funext l; simp [vecMul, dotProduct, Finset.sum_apply, mul_comm]
    have hz := hnf_tri_coeff hH w (r + t) (fun l hl => by
      rw [hw']
      simp only [hnfJoin]
      split_ifs with h1
      · rfl
      · have : (⟨(l : ℕ) - r, by omega⟩ : Fin r) ≠ t := fun e => by
          have := congrArg Fin.val e; simp at this; omega
        simp [this])
    have hK := congrFun hw' (Fin.natAdd r t)
    rw [hnfJoin_natAdd, Pi.single_eq_same, vecMul, dotProduct,
      Finset.sum_eq_single (Fin.natAdd r t)] at hK
    · have hdvd : hnfBigH A' d K (Fin.natAdd r t) (Fin.natAdd r t) ∣ K := Dvd.intro_left _ hK
      exact Int.le_of_dvd h.K_pos hdvd
    · intro b _ hb
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hb) with hlt | hgt
      · rw [hz b hlt]; simp
      · rw [hH.1 _ _ hgt]; simp
    · simp
  · -- it is a positive multiple of `K`
    obtain ⟨z, hz⟩ := hnfBigH_bot h t
    rw [hz, hnfJoin_natAdd, Pi.smul_apply, smul_eq_mul] at hpos ⊢
    have : 0 < z t := pos_of_mul_pos_right hpos h.K_pos.le
    nlinarith

/-- The first `r` rows: `H'_i = y A'` and `X_i = y + K z`, with `X` in `[0, K)`. -/
theorem hnfBigH_top (h : HnfSq A' d K) (i : Fin r) :
    ∃ y z : Fin r → ℤ, (fun j => hnfHp A' d K i j) = y ᵥ* A' ∧
      (fun j => hnfX A' d K i j) = y + K • z := by
  obtain ⟨y, z, hyz⟩ := hnfBigH_row h (Fin.castAdd r i)
  refine ⟨y, z, funext fun j => ?_, funext fun j => ?_⟩
  · simp only [hnfHp, hyz, hnfJoin_castAdd]
  · simp only [hnfX, hyz, hnfJoin_natAdd]

theorem hnfX_range (h : HnfSq A' d K) (i j : Fin r) : 0 ≤ hnfX A' d K i j ∧ hnfX A' d K i j < K := by
  have := (hnfBigH_spec h).1.2.2 (Fin.castAdd r i) (Fin.natAdd r j) (Fin.natAdd r j)
    (by simp; omega) rfl
  rw [hnfBig_diag h] at this
  exact this

end Blocks

/-- The symmetric residue recovers a small number from its residue. -/
theorem hnfLift_eq {K x y z : ℤ} (hx : 0 ≤ x ∧ x < K) (hxy : x = y + K * z) (hy : 2 * |y| < K) :
    hnfLift K x = y := by
  have h1 : -K < 2 * y := by have := neg_abs_le y; linarith
  have h2 : 2 * y < K := by have := le_abs_self y; linarith
  have hz1 : z ≤ 1 := by
    by_contra hc
    have : K * 2 ≤ K * z := mul_le_mul_of_nonneg_left (by omega) (by linarith)
    linarith
  have hz0 : 0 ≤ z := by
    by_contra hc
    have : K * z ≤ K * (-1) := mul_le_mul_of_nonneg_left (by omega) (by linarith)
    linarith
  interval_cases z
  · simp only [mul_zero, add_zero] at hxy
    subst hxy
    simp [hnfLift, h2]
  · simp only [mul_one] at hxy
    subst hxy
    simp only [hnfLift]
    rw [if_neg (by linarith)]
    ring

/-! ### The transform -/

section Transform

variable {A' : Matrix (Fin r) (Fin r) ℤ} {d K : ℤ}

/-- The exact transform: row `i` is the `y` with `y A' = H'_i`. -/
noncomputable def hnfY (h : HnfSq A' d K) : Matrix (Fin r) (Fin r) ℤ :=
  fun i => (hnfBigH_top h i).choose

theorem hnfY_mul (h : HnfSq A' d K) : hnfY h * A' = hnfHp A' d K := by
  ext i j
  have := congrFun (hnfBigH_top h i).choose_spec.choose_spec.1 j
  simp only [vecMul, dotProduct] at this
  rw [this, Matrix.mul_apply]
  rfl

theorem hnf_mul_eq_zero (hA : A'.det ≠ 0) {X : Matrix (Fin r) (Fin r) ℤ} (hX : X * A' = 0) :
    X = 0 := by
  ext i j
  have hrow : X i ᵥ* A' = 0 := by
    funext l
    have := congrFun (congrFun hX i) l
    simpa [Matrix.mul_apply, vecMul, dotProduct] using this
  rw [hnf_vecMul_eq_zero hA hrow]
  rfl

/-- `A' = V H'` for an integer `V`: the rows of `A'` lie in the lattice of `H'`. -/
theorem hnf_exists_V (h : HnfSq A' d K) : ∃ V : Matrix (Fin r) (Fin r) ℤ, V * hnfHp A' d K = A' := by
  have hH := (hnfBigH_spec h).1
  have : ∀ i, ∃ v : Fin r → ℤ, v ᵥ* hnfHp A' d K = A' i := by
    intro i
    have hmem : hnfJoin (A' i) (Pi.single i 1) ∈ Submodule.span ℤ (Set.range (hnfBigH A' d K)) := by
      rw [(hnfBigH_spec h).2.1, ← hnfBig_top]
      exact Submodule.subset_span (Set.mem_range_self _)
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
    refine ⟨fun t => w (Fin.castAdd r t), funext fun j => ?_⟩
    have := congrFun hw (Fin.castAdd r j)
    rw [hnfJoin_castAdd, Finset.sum_apply, Fin.sum_univ_add] at this
    rw [← this]
    simp only [vecMul, dotProduct, hnfHp, Pi.smul_apply, smul_eq_mul]
    have h0 : ∀ t : Fin r, hnfBigH A' d K (t.addNat r) (Fin.castAdd r j) = 0 :=
      fun t => hH.1 _ _ (by simp; omega)
    simp [h0]
  choose V hV using this
  exact ⟨V, by
    ext i j
    have := congrFun (hV i) j
    simpa [Matrix.mul_apply, vecMul, dotProduct] using this⟩

theorem hnfY_unit (h : HnfSq A' d K) : IsUnit (hnfY h).det := by
  obtain ⟨V, hV⟩ := hnf_exists_V h
  have h1 : (V * hnfY h - 1) * A' = 0 := by
    rw [sub_mul, Matrix.mul_assoc, hnfY_mul, hV, Matrix.one_mul, sub_self]
  have h2 : V * hnfY h = 1 := sub_eq_zero.mp (hnf_mul_eq_zero h.det_ne h1)
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_one] at h3
  exact isUnit_iff_exists_inv.mpr ⟨V.det, by rw [mul_comm]; exact h3⟩

theorem hnfHp_herm (h : HnfSq A' d K) : IsHermiteForm (hnfHp A' d K) := by
  have hH := (hnfBigH_spec h).1
  refine ⟨fun i j hij => hH.1 _ _ (by simpa using hij), fun i j hij => hH.2.1 _ _ (by simpa using hij),
    fun i j i' hij hi' => hH.2.2 _ _ _ (by simpa using hij) (by simpa using hi')⟩

/-- The entries of `H'` are at most `|det A'|`. -/
theorem hnfHp_le (h : HnfSq A' d K) (i j : Fin r) :
    0 ≤ hnfHp A' d K i j ∧ hnfHp A' d K i j ≤ |A'.det| := by
  have hH := hnfHp_herm h
  have hdet : (hnfHp A' d K).det = (hnfY h).det * A'.det := by rw [← hnfY_mul h, Matrix.det_mul]
  have habs : |(hnfHp A' d K).det| = |A'.det| := by
    rw [hdet, abs_mul, Int.isUnit_iff_abs_eq.mp (hnfY_unit h), one_mul]
  have hne : (hnfHp A' d K).det ≠ 0 := by
    rw [hdet]; exact mul_ne_zero (hnfY_unit h).ne_zero h.det_ne
  have htri : (hnfHp A' d K).det = ∏ t, hnfHp A' d K t t :=
    Matrix.det_of_upperTriangular (fun a b hab => hH.1 a b hab)
  have hdiag : ∀ t, hnfHp A' d K t t ≤ |A'.det| := by
    intro t
    have hdvd : hnfHp A' d K t t ∣ (hnfHp A' d K).det :=
      htri ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ t)
    have := Int.natAbs_le_of_dvd_ne_zero hdvd hne
    have hpos := hH.2.1 t t rfl
    rw [← habs]
    zify at this
    rwa [abs_of_pos hpos] at this
  rcases lt_trichotomy (j : ℕ) i with hji | hji | hji
  · rw [hH.1 i j hji]; exact ⟨le_rfl, abs_nonneg _⟩
  · rw [show i = j from (Fin.ext hji).symm]; exact ⟨(hH.2.1 j j rfl).le, hdiag j⟩
  · have := hH.2.2 i j j hji rfl
    exact ⟨this.1, this.2.le.trans (hdiag j)⟩

/-- **Cramer's rule bound:** `|U'| ≤ r · max |adj A'|`. -/
theorem hnfY_abs_le (h : HnfSq A' d K) {Q : ℤ} (hQ : ∀ i j, |A'.adjugate i j| ≤ Q) (i j : Fin r) :
    |hnfY h i j| ≤ r * Q := by
  have hY : hnfY h * (A' * A'.adjugate) = hnfHp A' d K * A'.adjugate := by
    rw [← Matrix.mul_assoc, hnfY_mul]
  rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at hY
  have he := congrFun (congrFun hY i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at he
  have hdpos : 0 < |A'.det| := abs_pos.mpr h.det_ne
  have hsum : |A'.det| * |hnfY h i j| ≤ |A'.det| * (r * Q) := by
    rw [← abs_mul, he]
    calc |∑ t, hnfHp A' d K i t * A'.adjugate t j| ≤ ∑ t, |hnfHp A' d K i t * A'.adjugate t j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin r, |A'.det| * Q := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [abs_mul]
          have h1 := hnfHp_le h i t
          exact mul_le_mul (by rw [abs_of_nonneg h1.1]; exact h1.2) (hQ t j) (abs_nonneg _)
            (abs_nonneg _)
      _ = |A'.det| * (r * Q) := by simp [Finset.sum_const]; ring
  exact le_of_mul_le_mul_left hsum hdpos

theorem hnfUp_eq (h : HnfSq A' d K) {Q : ℤ} (hQ : ∀ i j, |A'.adjugate i j| ≤ Q)
    (hK : 2 * (r * Q) < K) : hnfUp A' d K = hnfY h := by
  ext i j
  obtain ⟨z, -, hz⟩ := (hnfBigH_top h i).choose_spec
  have hx := congrFun hz j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx
  have hb : |hnfY h i j| ≤ r * Q := hnfY_abs_le h hQ i j
  exact hnfLift_eq (hnfX_range h i j) hx (by linarith)

/-- **The square case.** `U' A' = H'`, `U'` is unimodular, `H'` is in Hermite form, and the
entries are bounded. -/
theorem hnfSquare_spec (h : HnfSq A' d K) {Q : ℤ} (hQ : ∀ i j, |A'.adjugate i j| ≤ Q)
    (hK : 2 * (r * Q) < K) :
    hnfUp A' d K * A' = hnfHp A' d K ∧ IsUnit (hnfUp A' d K).det ∧ IsHermiteForm (hnfHp A' d K) ∧
      (∀ i j, |hnfUp A' d K i j| < K) ∧
      ∀ i j, 0 ≤ hnfHp A' d K i j ∧ hnfHp A' d K i j ≤ |d| * K := by
  rw [hnfUp_eq h hQ hK]
  refine ⟨hnfY_mul h, hnfY_unit h, hnfHp_herm h, fun i j => ?_, fun i j => ?_⟩
  · have := hnfY_abs_le h hQ i j
    have hQ0 : 0 ≤ Q := (abs_nonneg _).trans (hQ i j)
    nlinarith [Nat.cast_nonneg (α := ℤ) r]
  · exact (hnfBigH_spec h).2.2 _ _

end Transform

/-- Entries of the adjugate are at most `r! T^r` when the entries are at most `T ≥ 1`. -/
theorem hnf_adjugate_le {A' : Matrix (Fin r) (Fin r) ℤ} {T : ℤ} (hT1 : 1 ≤ T)
    (hT : ∀ i j, |A' i j| ≤ T) (i j : Fin r) :
    |A'.adjugate i j| ≤ r.factorial * T ^ r := by
  rw [adjugate_apply]
  have h := Matrix.det_le (A := A'.updateRow j (Pi.single i 1)) (abv := AbsoluteValue.abs)
    (x := T) (fun a b => by
      simp only [updateRow_apply]
      split_ifs
      · simp only [Pi.single_apply]; split_ifs <;> simp [hT1, (zero_le_one.trans hT1)]
      · exact hT a b)
  simpa [Fintype.card_fin, nsmul_eq_mul] using h

end GI.Proved
