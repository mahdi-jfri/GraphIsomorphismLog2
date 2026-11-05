module

public import Workspace.Impl.LinPrimeSplit
public import Workspace.Impl.LinFiniteAction

@[expose] public section

/-! The full primary action and its explicit generator matrices are obtained
by reducing the retained finite-abelian coordinates. -/
namespace GI.Impl

variable {G : Type*} [Group G] {d p : ℕ} {m : Fin d → ℕ}

noncomputable def linPrimeAction (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) :
    G →* (linFiniteVec (linPrimaryOrders p D.exponent) ≃+ linFiniteVec (linPrimaryOrders p D.exponent)) :=
  linDescendRep (linPrimeProjection D) (linPrimeProjection_surjective D) ρ
    (fun g x hx => linPrimeProjection_preserved D hm (ρ g).toAddMonoidHom x hx)

@[simp] theorem linPrimeAction_image (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (g : G) (x : linFiniteVec m) :
    linPrimeAction D hm ρ g (linPrimeProjection D x) = linPrimeProjection D (ρ g x) := by
  unfold linPrimeAction
  exact linDescendRep_image _ _ _ _ _ _

theorem linPrimeAction_cocycle (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (g h : G) :
    linPrimeProjection D (c (g * h)) =
      linPrimeAction D hm ρ g (linPrimeProjection D (c h)) + linPrimeProjection D (c g) := by
  rw [hc, map_add, linPrimeAction_image]

set_option maxHeartbeats 1000000 in
theorem linPrimeAction_matrix (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (g : G) (i j : Fin d) :
    linFiniteMatrix (linPrimaryOrders p D.exponent) (linPrimeAction D hm ρ g).toAddMonoidHom i j =
      linFiniteMatrix m (ρ g).toAddMonoidHom i j % linPrimaryOrders p D.exponent i := by
  have he := linPrimeAction_image D hm ρ g (linFiniteBasis m j)
  change linPrimeAction D hm ρ g
    (linFiniteProjection m (linPrimaryOrders p D.exponent) (linPrimeSplit_dvd D) (linFiniteBasis m j)) = _ at he
  rw [linFiniteProjection_basis] at he
  change ((linPrimeAction D hm ρ g) (linFiniteBasis (linPrimaryOrders p D.exponent) j) i).val = _
  rw [he]
  change ((linFiniteProjection m (linPrimaryOrders p D.exponent) (linPrimeSplit_dvd D)
    ((ρ g) (linFiniteBasis m j))) i).val = _
  rw [linFiniteProjection_val m (linPrimaryOrders p D.exponent) (linPrimeSplit_dvd D) hm _ i,
    ZMod.val_natCast]
  rfl

theorem linPrimeAction_intMatrix (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (g : G) (i j : Fin d) :
    linFiniteIntMatrix (linPrimaryOrders p D.exponent)
        (linPrimeAction D hm ρ g).toAddMonoidHom i j =
      linFiniteIntMatrix m (ρ g).toAddMonoidHom i j %
        (linPrimaryOrders p D.exponent i : ℤ) := by
  simpa only [linFiniteIntMatrix, Int.natCast_mod] using
    congrArg (fun x : ℕ => (x : ℤ)) (linPrimeAction_matrix D hm ρ g i j)

theorem linPrimeProjection_int (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i)
    (x : linFiniteVec m) (i : Fin d) :
    ((linPrimeProjection D x i).val : ℤ) =
      ((x i).val : ℤ) % (linPrimaryOrders p D.exponent i : ℤ) := by
  change (((linFiniteProjection m (linPrimaryOrders p D.exponent)
    (linPrimeSplit_dvd D) x) i).val : ℤ) = _
  rw [linFiniteProjection_val _ _ _ hm, ZMod.val_natCast, Int.natCast_mod]

theorem linPrimeAction_homogeneous (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m) (g : G) :
    linFiniteActionMatrix (linPrimaryOrders p D.exponent) (linPrimeAction D hm ρ)
        (fun h => linPrimeProjection D (c h)) g =
      fun i j => linFiniteActionMatrix m ρ c g i j %
        linFiniteModuli (linPrimaryOrders p D.exponent) i := by
  funext i j
  induction i using Fin.lastCases with
  | last => simp [linFiniteActionMatrix, linFiniteHomogeneous, linAffineMatrix,
      linFiniteModuli, linExtend]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [linFiniteActionMatrix, linFiniteHomogeneous, linAffineMatrix,
        linFiniteModuli, linFiniteActionLinear] using linPrimeProjection_int D hm (c g) i
    | cast j => simpa [linFiniteActionMatrix, linFiniteHomogeneous, linAffineMatrix,
        linFiniteModuli, linFiniteActionLinear] using linPrimeAction_intMatrix D hm ρ g i j

end GI.Impl
