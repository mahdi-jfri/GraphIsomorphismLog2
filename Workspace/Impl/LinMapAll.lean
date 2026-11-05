module

public import Workspace.Impl.LinMapEncoded

@[expose] public section

/-! A uniform map bound for cited subroutines whose output generators
need not be uniquely chosen. The relation is indexed by the source data. -/
namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 1000000 in
theorem linMapAll_spec {α : Type} {P : Program} {b f : ℕ}
    (hp : P.HasAt b (mapFuns b f)) (enc : α → Val) (he : Function.Injective enc)
    (R : α → Val → Prop) (c : Val) (xs : List α) (B : ℕ)
    (hf : ∀ x ∈ xs, FunAll P f (.list [c, enc x]) (fun w cost => R x w ∧ cost ≤ B)) :
    FunAll P b (.list [c, .list (xs.map enc)]) (fun w cost =>
      (∃ ws, w = .list ws ∧ List.Forall₂ R xs ws) ∧
        cost ≤ linMapBudget (Val.list [c, .list (xs.map enc)]).wt B) := by
  let W := (Val.list [c, .list (xs.map enc)]).wt
  have hs : ∀ v ∈ xs.map enc, FunAll P f (.list [c, v]) (fun w cost =>
      (∃ x, v = enc x ∧ R x w ∧ w.wt ≤ B) ∧ cost ≤ B) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact (hf x hx).wt_lt.mono fun w cost hw =>
      ⟨⟨x, rfl, hw.1.1, hw.2.le.trans hw.1.2⟩, hw.1.2⟩
  refine (map_spec hp hs).mono ?_
  intro w cost hw
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  rw [List.forall₂_map_left_iff] at hws
  have hr : List.Forall₂ (fun x w => R x w ∧ w.wt ≤ B) xs ws := hws.imp (by
    intro x w hw
    obtain ⟨y, hy, hr, hb⟩ := hw
    obtain rfl := he hy
    exact ⟨hr, hb⟩)
  have hwB : ∀ w ∈ ws, w.wt ≤ B := by
    clear hf hs hws hc
    induction hr with
    | nil => simp
    | cons h _ ih => simpa using And.intro h.2 ih
  have wl : xs.length ≤ W := by
    have hh := length_lt_wt_list (xs.map enc)
    have hw : (Val.list (xs.map enc)).wt < W := wt_le_wt_list (by simp [W])
    simp only [List.length_map] at hh
    omega
  have wo := linWtList (vs := ws) hwB
  rw [← hr.length_eq] at wo
  refine ⟨⟨ws, rfl, hr.imp (fun _ _ h => h.1)⟩, ?_⟩
  simp only [List.map_const', List.length_map, List.sum_replicate, smul_eq_mul] at hc
  have hm := Nat.mul_le_mul_right B wl
  dsimp only [W] at *
  unfold linMapBudget
  simp only [mapK] at hc
  nlinarith

end GI.Impl
