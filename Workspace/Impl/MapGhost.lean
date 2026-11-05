module

public import Workspace.Lang.Lib.List

@[expose] public section

/-!
# Map with costs known only through a property

`map_spec` asks for a fixed cost bound `B x` for each entry. When `f` calls a recursive procedure,
the cost of a call is only known to be at most the total cost of *some* run of the callee (the
specification of a call is existential). `mapQ_spec` handles this: the cost of the call on
entry `i` is at most `B i + cb` for some `cb` with a property `Q i cb`, and the map then costs at
most `∑ (B i + cs i)` plus an overhead, for some numbers `cs i` with `Q i (cs i)`. The consumer
picks, for each `i`, the run behind `cs i`.

The proof follows the trace of the loop (`LoopPost`): each step appends one entry, so the
accumulators grow and the last one bounds them all.
-/

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

/-- The overhead constant of `mapQ_spec`. -/
def mapQK : ℕ := 2000

/-- **Map with costs known through a property.** -/
theorem mapQ_spec {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val}
    {xs : List Val} {R : ℕ → Val → Prop} {Q : ℕ → ℕ → Prop} {B : ℕ → ℕ}
    (hf : ∀ i (hi : i < xs.length), FunAll P f (.list [c, xs[i]])
      (fun w cost => R i w ∧ ∃ cb, Q i cb ∧ cost ≤ B i + cb)) :
    FunAll P b (.list [c, .list xs]) (fun w cost => ∃ ws, w = .list ws ∧ ws.length = xs.length ∧
      (∀ i (hi : i < ws.length), R i ws[i]) ∧ ∃ cs : ℕ → ℕ, (∀ i, i < xs.length → Q i (cs i)) ∧
      cost ≤ ∑ i ∈ Finset.range xs.length, (B i + cs i) +
        mapQK * (xs.length + 1) * ((Val.list [c, .list xs]).wt + w.wt + 1)) := by
  set a := Val.list [c, .list xs] with ha
  have hk : Det P [a] (.length (.get (.var 0) (.nat 1))) (.nat xs.length) _ :=
    Det.length (Det.get' (Det.var' rfl) (Det.nat 1) rfl)
  have hca : c.wt < a.wt := wt_le_wt_list (by simp)
  have hxa : (Val.list xs).wt < a.wt := wt_le_wt_list (by simp)
  have hnx := length_lt_wt_list xs
  refine (loopFuns_spec h hk Det.nil
    (Inv := fun i acc => ∃ ws, acc = .list ws ∧ ws.length = i ∧ ∀ j (hj : j < ws.length), R j ws[j])
    (Step := fun i acc acc' cb => (∃ ws w, acc = .list ws ∧ acc' = .list (ws ++ [w])) ∧
      ∃ cs, Q i cs ∧ cb ≤ B i + cs + 100 * (a.wt + 1) + 100 * acc'.wt)
    ⟨[], rfl, rfl, fun j hj => absurd hj (by simp)⟩ ?_).mono ?_
  · rintro i acc hi ⟨ws, rfl, hlen, hR⟩
    have hx : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
    have hxi : xs[i].wt < (Val.list xs).wt := wt_getElem_lt xs i hi
    have hc := Det.get' (P := P) (Det.arg' (rest := []) (vs := [a, .nat i, .list ws]) (j := 0) rfl)
      (Det.nat 0) (show [c, Val.list xs][0]? = some c from rfl)
    have hxv := Det.get' (P := P) (Det.get' (Det.arg' (rest := []) (vs := [a, .nat i, .list ws])
      (j := 0) rfl) (Det.nat 1) (show [c, Val.list xs][1]? = some (.list xs) from rfl))
      (Det.arg' (rest := []) (vs := [a, .nat i, .list ws]) (j := 1) rfl) hx
    obtain ⟨CA, hCA, hCAle⟩ : ∃ CA, Det P [.list [a, .nat i, .list ws]]
        (mk2 (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1)))
        (.list [c, xs[i]]) CA ∧ CA ≤ 8 * (Val.list [a, .nat i, .list ws]).wt + 3 * a.wt +
          2 * (Val.list [c, xs[i]]).wt + 40 := ⟨_, Det.mk2 hc hxv, by omega⟩
    have hcall := EvalAll.call_funAll (f := f) hCA
      (Q := fun w cw => R i w ∧ ∃ cs, Q i cs ∧ cw ≤ CA + B i + cs + w.wt + 1) fun v ca hv => by
        obtain ⟨rfl, hca⟩ := hv
        exact (hf i hi).mono fun w cb hw => by
          obtain ⟨hR, cs, hQ, hcb⟩ := hw
          exact ⟨hR, cs, hQ, by omega⟩
    refine (EvalAll.snoc_det (Det.arg' (rest := []) (vs := [a, .nat i, .list ws]) (j := 2) rfl)
      hcall).mono ?_
    rintro v cv ⟨w, cw, ⟨hRw, cs, hQ, hcw⟩, rfl, hcv⟩
    have hw : w.wt < (Val.list (ws ++ [w])).wt := wt_le_wt_list (by simp)
    have hW := wt_list3_le a (.nat i) (.list ws)
    have := wt_nat_le i
    have hcx := wt_list2_le c xs[i]
    have hpre := wt_list_mono (show ws <+: ws ++ [w] from List.prefix_append _ _)
    have hwsl : ws.length < (Val.list ws).wt := length_lt_wt_list ws
    refine ⟨⟨ws ++ [w], rfl, by simp [hlen], fun j hj => ?_⟩, ⟨ws, w, rfl, rfl⟩, cs, hQ, ?_⟩
    · simp only [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [List.getElem_append_left hj]; exact hR j hj
      · rw [List.getElem_append_right (le_refl _)]
        simpa [hlen] using hRw
    · omega
  · rintro w cost ⟨cl, ⟨accs, costs, ha0, hak, hinv, hstep, hcost⟩, hc⟩
    obtain ⟨ws, rfl, hlen, hR⟩ := hak ▸ hinv xs.length (Nat.zero_le _) le_rfl
    -- the accumulators grow
    have hmono : ∀ d i, i + d = xs.length → (accs i).wt ≤ (Val.list ws).wt := by
      intro d
      induction d with
      | zero => intro i hi; rw [show i = xs.length by omega, hak]
      | succ d ih =>
        intro i hi
        obtain ⟨⟨us, u, h1, h2⟩, -⟩ := hstep i (Nat.zero_le _) (by omega)
        have := ih (i + 1) (by omega)
        rw [h1]; rw [h2] at this
        exact (wt_list_mono (List.prefix_append us [u])).trans this
    have hM : ∀ i, 0 ≤ i → i ≤ xs.length → (accs i).wt ≤ (Val.list ws).wt :=
      fun i _ hi => hmono (xs.length - i) i (by omega)
    have h1 := hcost _ hM
    choose! cs hcs using fun i (hi : i < xs.length) => (hstep i (Nat.zero_le _) hi).2
    refine ⟨ws, rfl, hlen, hR, cs, fun i hi => (hcs i hi).1, ?_⟩
    have h2 : ∑ i ∈ Finset.Ico 0 xs.length, costs i ≤ ∑ i ∈ Finset.range xs.length,
        (B i + cs i + (100 * (a.wt + 1) + 100 * (Val.list ws).wt)) := by
      rw [← Finset.range_eq_Ico]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      have := (hcs i hi').2
      have := hM (i + 1) (Nat.zero_le _) hi'
      omega
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
    have h4 := wt_list4_le a (.nat xs.length) (.nat 0) (.list [])
    have := wt_nat_le xs.length
    have := wt_nat_le 0
    simp only [wt_list_nil] at h4
    have hb : xs.length * (100 * (a.wt + 1) + 100 * (Val.list ws).wt) +
        loopK * (xs.length - 0 + 1) * (a.wt + xs.length + (Val.list ws).wt + 1) +
        (4 * (2 * (a.wt + xs.length + 2 + 4) + 8) + a.wt + (Val.list ws).wt + 100 * a.wt + 100) ≤
        mapQK * (xs.length + 1) * (a.wt + (Val.list ws).wt + 1) := by
      simp only [loopK, mapQK, Nat.sub_zero]
      nlinarith
    have hj : (Val.list [c, .list xs]).wt = a.wt := rfl
    rw [hj]
    omega

end GI.Lang
