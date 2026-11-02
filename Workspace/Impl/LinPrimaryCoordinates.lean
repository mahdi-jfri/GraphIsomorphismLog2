import Workspace.Impl.LinPrimaryFieldMatrix
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Computable coordinates on a primary layer. They divide the canonical
integer coordinates by p^j and reduce modulo p. -/
namespace GI.Impl
open scoped BigOperators

theorem linPrimaryDivModCast (p ν j : ℕ) (hj : j < ν) (a : ℕ) :
    (((a % p ^ ν) / p ^ j : ℕ) : ZMod p) = ((a / p ^ j : ℕ) : ZMod p) := by
  have he : p ^ ν = p ^ j * p ^ (ν - j) := by rw [← pow_add]; congr 1; omega
  rw [he, Nat.mod_mul_right_div_self]
  exact linNatModCast (dvd_pow_self p (by omega : ν - j ≠ 0)) _

def linPrimaryFiber {d : ℕ} (p : ℕ) (ν : Fin d → ℕ) (j : ℕ)
    (x : linFiniteVec (linPrimaryOrders p ν)) : Prop := ∀ i, p ^ j ∣ (x i).val

noncomputable def linPrimaryCoord {d : ℕ} (p : ℕ) (ν : Fin d → ℕ) (j : ℕ)
    (x : linFiniteVec (linPrimaryOrders p ν)) : Fin d → ZMod p :=
  fun i => ((x i).val / p ^ j : ℕ)

/-- An inactive primary coordinate has no remaining layer digit. -/
theorem linPrimaryCoord_inactive {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (x : linFiniteVec (linPrimaryOrders p ν)) (i : Fin d) (hi : ¬j < ν i) :
    linPrimaryCoord p ν j x i = 0 := by
  haveI : NeZero (linPrimaryOrders p ν i) := ⟨Nat.ne_of_gt (Nat.pow_pos hp)⟩
  have hv := ZMod.val_lt (x i)
  have hpow : p ^ ν i ≤ p ^ j := Nat.pow_le_pow_right hp (by omega)
  have hlt : (x i).val < p ^ j := hv.trans_le hpow
  simp only [linPrimaryCoord, Nat.div_eq_of_lt hlt, Nat.cast_zero]

/-- Full affine evaluation and layer evaluation commute on the current fiber. -/
theorem linPrimaryCoord_affine {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν))
    (x u : linFiniteVec (linPrimaryOrders p ν))
    (hx : linPrimaryFiber p ν j x) (hu : linPrimaryFiber p ν j u) :
    linPrimaryCoord p ν j (f x + u) =
      (linPrimaryFieldMatrix p ν j f).mulVec (linPrimaryCoord p ν j x) + linPrimaryCoord p ν j u := by
  classical
  have hm : ∀ i, 0 < linPrimaryOrders p ν i := fun i => Nat.pow_pos hp
  funext i
  by_cases hi : j < ν i
  · have hs : (∑ k, (linFiniteMatrix (linPrimaryOrders p ν) f i k : ZMod p) *
          linPrimaryCoord p ν j x k) =
        (linPrimaryFieldMatrix p ν j f).mulVec (linPrimaryCoord p ν j x) i := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : j < ν k
      · simp only [linPrimaryFieldMatrix, linActiveMatrix, hi, hk, if_pos]
      · rw [linPrimaryCoord_inactive p hp ν j x k hk]
        simp
    change (((f x i + u i).val / p ^ j : ℕ) : ZMod p) = _
    rw [linFiniteAffine_comp (linPrimaryOrders p ν) hm f u x i]
    change ((((∑ k, linFiniteMatrix (linPrimaryOrders p ν) f i k * (x k).val) + (u i).val) % p ^ ν i /
      p ^ j : ℕ) : ZMod p) = _
    rw [linPrimaryDivModCast p (ν i) j hi]
    rw [Nat.add_div_of_dvd_left (hu i), Nat.sum_div (fun k _ => dvd_mul_of_dvd_right (hx k) _)]
    simp only [Nat.cast_add, Nat.cast_sum]
    change (∑ k, ((linFiniteMatrix (linPrimaryOrders p ν) f i k * (x k).val / p ^ j : ℕ) : ZMod p)) +
      linPrimaryCoord p ν j u i = _
    simp only [Pi.add_apply]
    rw [← hs]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.mul_div_assoc _ (hx k), Nat.cast_mul]
    rfl
  · have hx0 := linPrimaryCoord_inactive p hp ν j x i hi
    have hu0 := linPrimaryCoord_inactive p hp ν j u i hi
    have hf0 := linPrimaryCoord_inactive p hp ν j (f x + u) i hi
    have hrow (k : Fin d) : linPrimaryFieldMatrix p ν j f i k =
        (1 : Matrix (Fin d) (Fin d) (ZMod p)) i k := by
      simp [linPrimaryFieldMatrix, linActiveMatrix, hi, Matrix.one_apply]
    have hr : (linPrimaryFieldMatrix p ν j f).mulVec (linPrimaryCoord p ν j x) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, hrow]
      change (1 : Matrix (Fin d) (Fin d) (ZMod p)).mulVec (linPrimaryCoord p ν j x) i = 0
      rw [Matrix.one_mulVec, hx0]
    change _ = (linPrimaryFieldMatrix p ν j f).mulVec (linPrimaryCoord p ν j x) i + linPrimaryCoord p ν j u i
    rw [hf0, hr, hu0, add_zero]

/-- Reducing a full cocycle after restriction to a primary fiber gives the
cocycle required by the homogeneous field program. -/
theorem linPrimaryCoord_cocycle {G : Type*} [Group G] {d : ℕ}
    (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (ρ : G →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : G → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g)
    (hmem : ∀ g, linPrimaryFiber p ν j (c g)) (g h : G) :
    linPrimaryCoord p ν j (c (g * h)) =
      (linPrimaryFieldRep p hp ν j ρ g).val.mulVec (linPrimaryCoord p ν j (c h)) +
        linPrimaryCoord p ν j (c g) := by
  rw [hc]
  exact linPrimaryCoord_affine p hp ν j (ρ g).toAddMonoidHom (c h) (c g) (hmem h) (hmem g)

end GI.Impl
