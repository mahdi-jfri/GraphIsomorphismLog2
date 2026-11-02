import Workspace.Impl.LinMapEncoded

/-! Map deterministic computations over action records. Distinct cover elements
may have the same record, so their encoding need not be injective. -/
namespace GI.Impl
open GI.Lang GI.Cited

theorem linFunDet_output_eq {P : Program} {f : ℕ} {v x y : Val} {cx cy : ℕ}
    (hx : FunDet P f v x cx) (hy : FunDet P f v y cy) : x = y := by
  obtain ⟨bx, hbx, hx⟩ := hx
  obtain ⟨by', hby, hy⟩ := hy
  have he := Option.some.inj (hbx.symm.trans hby)
  subst by'
  obtain ⟨w, c, hw, hpost⟩ := hx.exists_eval
  exact hpost.1.symm.trans (hy.sound hw).1

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linMapSource_spec {α : Type} {P : Program} {b f : ℕ}
    (hp : P.HasAt b (mapFuns b f)) (enc : α → Val)
    (out : α → Val) (c : Val) (xs : List α) (B : ℕ)
    (hf : ∀ x ∈ xs, FunDet P f (.list [c, enc x]) (out x) B) :
    FunDet P b (.list [c, .list (xs.map enc)]) (.list (xs.map out))
      (linMapBudget (Val.list [c, .list (xs.map enc)]).wt B) := by
  let W := (Val.list [c, .list (xs.map enc)]).wt
  have hh : ∀ v ∈ xs.map enc, FunAll P f (.list [c, v])
      (fun w cost => (∀ x ∈ xs, v = enc x → w = out x) ∧ cost ≤ B) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    refine FunAll.mono (hf x hx) fun w cost hw => ⟨?_, hw.2⟩
    intro y hy heq
    have hsame : out x = out y := by
      have hx' := hf x hx
      have hy' := hf y hy
      rw [heq] at hx'
      exact linFunDet_output_eq hx' hy'
    exact hw.1.trans hsame
  have hm := map_spec hp hh
  have wl : xs.length ≤ W := by
    have hh := length_lt_wt_list (xs.map enc)
    have ww : (Val.list (xs.map enc)).wt < W := wt_le_wt_list (by simp [W])
    simp only [List.length_map] at hh
    omega
  have wo : (Val.list (xs.map out)).wt ≤ 2 * (W * B) + W + 4 := by
    have hh := linWtList (vs := xs.map out) (B := B) (by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact (hf x hx).wt_lt.le)
    simp only [List.length_map] at hh
    nlinarith [Nat.mul_le_mul_right B wl]
  refine hm.mono fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have heq : ws = xs.map out := forall₂_map_eq (h := hws) (fun x hx w hw => hw x hx rfl)
  subst ws
  refine ⟨rfl, ?_⟩
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at hc
  unfold linMapBudget
  have hh := Nat.mul_le_mul_right B wl
  dsimp only [W] at *
  simp only [mapK] at *
  nlinarith

end GI.Impl
