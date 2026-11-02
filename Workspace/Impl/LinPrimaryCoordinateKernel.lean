import Workspace.Impl.LinPrimaryCoordinates
import Workspace.Impl.LinPrimaryLayers

/-! The explicit divided coordinates have exactly the next primary layer as
kernel. This identifies the field test with the paper's filtration step. -/
namespace GI.Impl

/-- Vanishing of the layer digit is exactly membership in the next fiber. -/
theorem linPrimaryCoord_zero_iff {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (x : linFiniteVec (linPrimaryOrders p ν)) (hx : linPrimaryFiber p ν j x) :
    linPrimaryCoord p ν j x = 0 ↔ linPrimaryFiber p ν (j + 1) x := by
  constructor
  · intro hzero i
    have hz := congrFun hzero i
    have hd : p ∣ (x i).val / p ^ j := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hh := Nat.mul_dvd_mul_left (p ^ j) hd
    rw [Nat.mul_div_cancel' (hx i)] at hh
    simpa only [pow_succ] using hh
  · intro hnext
    funext i
    obtain ⟨a, ha⟩ := hnext i
    change (((x i).val / p ^ j : ℕ) : ZMod p) = 0
    rw [ha, pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos hp)]
    simp

/-- Integer and natural powers give the same scalar action. -/
theorem linPrimaryPowerScalar {V : Type*} [AddCommGroup V] (p j : ℕ) (x : V) :
    (p ^ j : ℤ) • x = (p ^ j : ℕ) • x := by
  rw [← Nat.cast_pow, natCast_zsmul]

/-- The coordinate fiber is precisely p^j V in the finite-primary group. -/
theorem linPrimaryFiber_powerLayer {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (x : linFiniteVec (linPrimaryOrders p ν)) :
    linPrimaryFiber p ν j x ↔ x ∈ linPowerLayer p j := by
  rw [linPowerLayer_mem]
  constructor
  · intro hx
    let y : linFiniteVec (linPrimaryOrders p ν) := fun i => ((x i).val / p ^ j : ℕ)
    refine ⟨y, ?_⟩
    rw [linPrimaryPowerScalar]
    funext i
    haveI : NeZero (linPrimaryOrders p ν i) := ⟨Nat.ne_of_gt (Nat.pow_pos hp)⟩
    change (p ^ j : ℕ) • (y i) = x i
    dsimp only [y]
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (hx i), ZMod.natCast_zmod_val]
  · rintro ⟨y, rfl⟩
    rw [linPrimaryPowerScalar]
    intro i
    haveI : NeZero (linPrimaryOrders p ν i) := ⟨Nat.ne_of_gt (Nat.pow_pos hp)⟩
    have hv : (((p ^ j : ℕ) • y) i).val = (p ^ j * (y i).val) % p ^ ν i := by
      change (((p ^ j : ℕ) • y i)).val = _
      conv_lhs => rw [nsmul_eq_mul, ← ZMod.natCast_zmod_val (y i), ← Nat.cast_mul, ZMod.val_natCast]
      rfl
    rw [hv]
    by_cases hji : j ≤ ν i
    · exact (Nat.dvd_mod_iff (Nat.pow_dvd_pow p hji)).mpr (dvd_mul_right _ _)
    · have hd : p ^ ν i ∣ p ^ j * (y i).val :=
        dvd_mul_of_dvd_left (Nat.pow_dvd_pow p (by omega)) _
      rw [Nat.mod_eq_zero_of_dvd hd]
      exact dvd_zero _

/-- The kernel characterization in the paper's subgroup notation. -/
theorem linPrimaryCoord_next_layer {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (x : linFiniteVec (linPrimaryOrders p ν)) (hx : x ∈ linPowerLayer p j) :
    linPrimaryCoord p ν j x = 0 ↔ x ∈ linPowerLayer p (j + 1) := by
  rw [← linPrimaryFiber_powerLayer p hp ν (j + 1)]
  exact linPrimaryCoord_zero_iff p hp ν j x ((linPrimaryFiber_powerLayer p hp ν j x).mpr hx)

/-- At the largest cyclic exponent, the remaining fiber is zero. -/
theorem linPrimaryFiber_terminal {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (J : ℕ)
    (hJ : ∀ i, ν i ≤ J) (x : linFiniteVec (linPrimaryOrders p ν))
    (hx : linPrimaryFiber p ν J x) : x = 0 := by
  funext i
  haveI : NeZero (linPrimaryOrders p ν i) := ⟨Nat.ne_of_gt (Nat.pow_pos hp)⟩
  have hv := ZMod.val_lt (x i)
  have hlt : (x i).val < p ^ J := hv.trans_le (Nat.pow_le_pow_right hp (hJ i))
  have hz : (x i).val = 0 := Nat.eq_zero_of_dvd_of_lt (hx i) hlt
  exact ZMod.val_injective _ (by simpa using hz)

end GI.Impl
