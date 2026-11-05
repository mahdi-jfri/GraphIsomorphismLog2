module

public import Workspace.Impl.LinAffineCallerCost

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linAffineCaller_source_bounds {n d : ℕ} (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (v w : linFiniteVec m) :
    let W := (tmGLAffIn gs m ρ c v w).wt
    n ≤ W ∧ d ≤ W ∧ gs.length ≤ W ∧ (linVecVal (fun i => (m i : ℤ))).wt < W := by
  rw [linTmGLAffIn_eq]
  let a := Val.list [encGroup gs, linVecVal (fun i => (m i : ℤ)),
    .list ((linActionGens gs).map (linPlainAffineVal m ρ c)),
    linVecVal (fun i => ((v i).val : ℤ)), linVecVal (fun i => ((w i).val : ℤ))]
  let W := a.wt
  have wg : (encGroup gs).wt < W := wt_le_wt_list (by simp [a, W])
  have wo : (linVecVal (fun i => (m i : ℤ))).wt < W := wt_le_wt_list (by simp [a, W])
  have wl : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt := wt_le_wt_list (by simp [encGroup])
  have hn : n ≤ W := by
    have hh := S_le_wt_encGroup gs
    have hm : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => encInt (m i : ℤ))
    simp only [List.length_map, List.length_finRange] at hh
    change d < (linVecVal (fun i => (m i : ℤ))).wt at hh
    omega
  have hg : gs.length ≤ W := by
    have hh := length_lt_wt_list ((1 :: gs).map encPerm)
    simp only [List.length_map, List.length_cons] at hh
    omega
  exact ⟨hn, hd, hg, wo⟩

theorem linAffineCallerContext_spec {P : Program} {b n d : ℕ}
    (h : linRecenterContextAt P b) (gs : List (Equiv.Perm (Fin n))) (hgs : gs ≠ [])
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g) (v w : linFiniteVec m) :
    let a := tmGLAffIn gs m ρ c v w
    FunDet P b a (linActionContext gs m ρ (linFiniteRecenter ρ c w)) (linRecenterContextCost a.wt) := by
  cases gs with
  | nil => exact (hgs rfl).elim
  | cons g xs =>
    let cover := gens (g :: xs)
    let k := linIntoSubgroup cover g
    let ks := xs.map (linIntoSubgroup cover)
    have hs := linRecenterContext_spec h m hm ρ c hc (encGroup (g :: xs))
      (linVecVal (fun i => ((v i).val : ℤ))) w k ks
    simpa only [linTmGLAffIn_eq, linActionContext, linGroupSlpTable, linActionGens,
      List.map_cons] using hs

theorem linAffineCallerDifference_spec {P : Program} {b n d : ℕ}
    (h : linFiniteDifferenceAt P b) (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (v w : linFiniteVec m) :
    let a := tmGLAffIn gs m ρ c v w
    FunDet P b (.list [linVecVal (fun i => (m i : ℤ)),
      linVecVal (fun i => ((v i).val : ℤ)), linVecVal (fun i => ((w i).val : ℤ))])
      (linFiniteIntVecVal m (v - w)) (linAffineCallerDiffBudget a.wt) := by
  let a := tmGLAffIn gs m ρ c v w
  have ha := linTmGLAffIn_eq gs m ρ c v w
  have wo : (linVecVal (fun i => (m i : ℤ))).wt < a.wt := by
    dsimp only [a]
    rw [ha]
    exact wt_le_wt_list (by simp)
  have wv : (linVecVal (fun i => ((v i).val : ℤ))).wt < a.wt := by
    dsimp only [a]
    rw [ha]
    exact wt_le_wt_list (by simp)
  have ww : (linVecVal (fun i => ((w i).val : ℤ))).wt < a.wt := by
    dsimp only [a]
    rw [ha]
    exact wt_le_wt_list (by simp)

  have hh := wt_list3_le (linVecVal (fun i => (m i : ℤ)))
    (linVecVal (fun i => ((v i).val : ℤ))) (linVecVal (fun i => ((w i).val : ℤ)))
  have hb : (Val.list [linVecVal (fun i => (m i : ℤ)),
      linVecVal (fun i => ((v i).val : ℤ)), linVecVal (fun i => ((w i).val : ℤ))]).wt ≤
      100 * (a.wt + 1) := by omega
  exact (linFiniteDifference_spec h m hm v w).mono (linFiniteDifferenceCost_mono hb)

end GI.Impl
