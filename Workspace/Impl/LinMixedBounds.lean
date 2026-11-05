module

public import Workspace.Impl.LinMixedLoop

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linMixedLoop_source_bounds {n d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : gens gs → linFiniteVec m) (x : linFiniteVec m) (r : Equiv.Perm (Fin n)) :
    let W := (linMixedLoopInputVal gs m ρ c x r).wt
    n ≤ W ∧ d ≤ W ∧ (linVecVal (fun i => (m i : ℤ))).wt ≤ W := by
  let ctx := linActionContext gs m ρ c
  let a := linMixedLoopInputVal gs m ρ c x r
  let W := a.wt
  have wc : ctx.wt < W := wt_le_wt_list (by simp [W, a, ctx, linMixedLoopInputVal])
  have wg : (encGroup gs).wt < ctx.wt := wt_le_wt_list (by simp [ctx, linActionContext])
  have wm : (linVecVal (fun i => (m i : ℤ))).wt < W :=
    wt_le_wt_list (by simp [W, a, linMixedLoopInputVal])
  have hn : n ≤ W := by
    have hh := S_le_wt_encGroup gs
    have hlo : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (Nat.le_succ n).trans (hlo.trans (hh.trans (wg.le.trans wc.le)))
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => encInt (m i : ℤ))
    simp only [List.length_map, List.length_finRange] at hh
    change d < (linVecVal (fun i => (m i : ℤ))).wt at hh
    omega
  exact ⟨hn, hd, wm.le⟩

theorem linMixedLoopInv_wt {n d W : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (hn : n ≤ W) (hd : d ≤ W)
    (hwm : (linVecVal (fun i => (m i : ℤ))).wt ≤ W)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (x : linFiniteVec m) (acc0 : Equiv.Perm (Fin n)) (j : ℕ) (a : Val)
    (ha : linMixedLoopInv gs m hm ρ c x acc0 j a) : a.wt ≤ linPrimaryAccumulatorWeight W := by
  rcases ha with ⟨rfl, _⟩ | ⟨ks, hle, r, rfl, hlen, _⟩
  · exact linPrimaryAccumulatorWeight_ge W
  · exact linPrimaryAccumulator_wt ks hlen hn hd m hm hwm _ _ _ _

def linMixedIterationWeight (W : ℕ) : ℕ := 100 * (linPrimaryAccumulatorWeight W + W + 10)

theorem linMixedPassInput_wt {n d W : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hlen : gs.length ≤ n ^ 2) (hn : n ≤ W) (hd : d ≤ W)
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (hwm : (linVecVal (fun i => (m i : ℤ))).wt ≤ W)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (x : linFiniteVec m) (r : Equiv.Perm (Fin n)) (p : ℕ) (hp : p ≤ W) :
    (linPrimePrepareInputVal gs m ρ c x r p).wt ≤ linMixedIterationWeight W := by
  have ha := linPrimaryAccumulator_wt gs hlen hn hd m hm hwm ρ c x r
  have hc : (linActionContext gs m ρ c).wt ≤ linPrimaryAccumulatorWeight W :=
    (wt_le_wt_list (by simp)).le.trans ha
  have hx : (linFinitePointVal m x).wt ≤ linPrimaryAccumulatorWeight W :=
    (wt_le_wt_list (by simp)).le.trans ha
  have hr : (encPerm r).wt ≤ linPrimaryAccumulatorWeight W :=
    (wt_le_wt_list (by simp)).le.trans ha
  have wp := (wt_nat_le p).trans (Nat.add_le_add_right hp 2)
  have hh := wt_list_le [linActionContext gs m ρ c, linFinitePointVal m x, encPerm r,
    .nat p, linVecVal (fun i => (m i : ℤ))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hh
  change (Val.list [linActionContext gs m ρ c, linFinitePointVal m x, encPerm r,
    .nat p, linVecVal (fun i => (m i : ℤ))]).wt ≤ _
  unfold linMixedIterationWeight
  omega

theorem linMixedIterationWeight_poly : PBU (fun _ W _ => linMixedIterationWeight W) :=
  PBU.smul 100 (PBU.addc (PBU.add linPrimaryAccumulatorWeight_poly PBU.W) 10)

end GI.Impl
