import Workspace.Impl.LinPrimaryBounds

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linPrimaryLoopInputVal {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (ν : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν)) (x : linFiniteVec (linPrimaryOrders p ν))
    (r : Equiv.Perm (Fin n)) : Val :=
  .list [linActionContext gs (linPrimaryOrders p ν) ρ c,
    linFinitePointVal (linPrimaryOrders p ν) x, encPerm r, .nat p, encFun ν]

theorem linFiniteOrders_wt_le_moduli {d : ℕ} (m : Fin d → ℕ) :
    (linVecVal (fun i => (m i : ℤ))).wt ≤ (linVecVal (linFiniteModuli m)).wt := by
  change (Val.list ((List.finRange d).map fun i => encInt (m i : ℤ))).wt ≤
    (Val.list ((List.finRange (d + 1)).map fun i => encInt (linFiniteModuli m i))).wt
  unfold linFiniteModuli
  rw [linExtend_value]
  exact wt_list_mono ⟨[encInt 0], rfl⟩

theorem linPrimaryLoop_source_bounds {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hp : p.Prime) (ν : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν)) (x : linFiniteVec (linPrimaryOrders p ν))
    (r : Equiv.Perm (Fin n)) :
    let W := (linPrimaryLoopInputVal gs ν ρ c x r).wt
    n ≤ W ∧ d ≤ W ∧ (linVecVal (fun i => (linPrimaryOrders p ν i : ℤ))).wt ≤ W ∧
      linPrimaryHeight ν ≤ W ∧ ∀ i, ν i ≤ W := by
  let m := linPrimaryOrders p ν
  let ctx := linActionContext gs m ρ c
  let a := linPrimaryLoopInputVal gs ν ρ c x r
  let W := a.wt
  let ident := linFiniteAffineVal m ρ c 1
  have wc : ctx.wt < W := wt_le_wt_list (by simp [W, a, ctx, m, linPrimaryLoopInputVal])
  have wg : (encGroup gs).wt < ctx.wt := wt_le_wt_list (by simp [ctx, linActionContext])
  have wi : ident.wt < ctx.wt := wt_le_wt_list (by simp [ctx, ident, linActionContext])
  have wm : (linVecVal (linFiniteModuli m)).wt < ident.wt :=
    wt_le_wt_list (by simp [ident, linFiniteAffineVal])
  have wν : (encFun ν).wt < W := wt_le_wt_list (by simp [W, a, linPrimaryLoopInputVal])
  have hn : n ≤ W := by
    have hh := S_le_wt_encGroup gs
    have hlo : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (Nat.le_succ n).trans (hlo.trans (hh.trans (wg.le.trans wc.le)))
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => Val.nat (ν i))
    simp only [List.length_map, List.length_finRange] at hh
    change d < (encFun ν).wt at hh
    omega
  have hmW : (linVecVal (linFiniteModuli m)).wt ≤ W := wm.le.trans (wi.le.trans wc.le)
  exact ⟨hn, hd, (linFiniteOrders_wt_le_moduli m).trans hmW,
    (linPrimaryHeight_le hp ν).trans hmW,
    fun i => (linPrimaryExponent_moduli_lt hp ν i).le.trans hmW⟩

end GI.Impl
