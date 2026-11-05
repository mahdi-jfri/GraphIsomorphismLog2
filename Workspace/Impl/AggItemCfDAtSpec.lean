module

public import Workspace.Impl.AggItemCfDPrograms

@[expose] public section

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited

/-- The design object at a prefix, with a bound in the full input weight. -/
theorem itCfD_at_spec {P : Program} {I : ItCfDIdx} (h : ItCfDOk P I)
    {dl tl : List ℕ} {q κ : ℕ} (hc : ItCfDCtx dl tl q κ) (m : ℕ) {N : ℕ}
    (hN : (Val.list [stDA dl tl q κ, .nat m]).wt ≤ N) :
    FunDet P I.atf (.list [stDA dl tl q κ, .nat m]) (itCfDAt dl tl q κ m)
      (10 ^ 50 * (N + 1) ^ 8) := by
  set V := stDV dl tl q κ m
  have hVl : V.length = q := stDV_length dl tl q κ m
  have wA : (stDA dl tl q κ).wt < (Val.list [stDA dl tl q κ, .nat m]).wt :=
    wt_le_wt_list (by simp)
  have hq : q ≤ N := by have := hc.le_wt.2.2; omega
  have hk : κ ≤ N := by have := hc.le_wt.2.1; omega
  have hp2 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hp12 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have wV : (natList V).wt ≤ 20 * (N + 1) ^ 2 := by
    have hw := hc.wt_stDV m
    have hh := Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left
      (show 2 * (stDA dl tl q κ).wt + 1 ≤ 2 * (N + 1) by omega) 2)
    have he : 5 * (2 * (N + 1)) ^ 2 = 20 * (N + 1) ^ 2 := by ring
    exact hw.trans (hh.trans_eq he)
  have wVB : (natList V).wt ≤ 100 * (N + 1) ^ 2 := by omega
  have hqB : q ≤ 100 * (N + 1) ^ 2 := by omega
  have wq := wt_nat_le q
  have wrange : (natList (List.range q)).wt ≤ 5 * (N + 1) ^ 2 := by
    have hw := wt_natList_le_sq (xs := List.range q) (B := q)
      (fun x hx => (List.mem_range.1 hx).le) (by simp)
    exact hw.trans (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left (by omega) 2))
  have wctx : (Val.list [natList V, .nat q]).wt ≤ 50 * (N + 1) ^ 2 := by
    have := wt_list2_le (natList V) (.nat q); omega
  have wsearch : (Val.list [.list [natList V, .nat q], natList (List.range q)]).wt ≤
      200 * (N + 1) ^ 2 := by
    have := wt_list2_le (.list [natList V, .nat q]) (natList (List.range q)); omega
  have hpred := fun i hi => itCfD_dom_spec h.dv h.dvv h.cb wVB hVl hqB (z := i) hi
  have hfind := st_find_det h.fd (c := .list [natList V, .nat q]) (n := q)
    (t := stDDom V q) hpred wsearch (by omega)
  have hany := st_any_det h.ad (c := .list [natList V, .nat q]) (n := q)
    (t := stDDom V q) hpred wsearch (by omega)
  have hsearchB := itCfD_search_budget hq
  have hfindB : FunDet P I.fd
      (.list [.list [natList V, .nat q], natList (List.range q)]) (.nat (stDZ V q))
      (itCfDAtBudget N) := hfind.mono hsearchB
  have hanyB := hany.mono hsearchB
  have hvm0 := itCfD_v_spec h.vm h.vmap h.rb h.vf h.cf h.hor hc m hN
  have hvmB : FunDet P I.vm (.list [stDA dl tl q κ, .nat m]) (natList V) (itCfDAtBudget N) :=
    hvm0.mono (itCfD_cost_mono N (b := 10 ^ 40) (by norm_num [stDVMK, itCfDAtBudget]) (by norm_num))
  have hrangeB := (st_range_det h.rb q).mono
    ((Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left (show q + 1 ≤ N + 1 by omega) 3)).trans
      (itCfD_cost_mono N (b := 10 ^ 40) (by norm_num [itCfDAtBudget]) (by norm_num : 3 ≤ (8 : ℕ))))
  have hblocks := itCfD_blocks_spec h.bl h.bm h.rb h.br h.brm h.bce V q hVl wVB hqB
  have hblocksB := hblocks.mono (itCfD_read_budget N)
  have htable := itCfD_table_spec h.tb h.tm h.rb h.tr h.trm h.tce h.cf h.hor hc m hN
  have htableB := htable.mono (itCfD_cost_mono N (b := 10 ^ 40) (by norm_num [itCfDAtBudget]) (by norm_num : 4 ≤ (8 : ℕ)))
  have hp18 : N + 1 ≤ (N + 1) ^ 8 := Nat.le_self_pow (by norm_num) _
  have hp08 : 1 ≤ (N + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hNB : N ≤ itCfDAtBudget N := by unfold itCfDAtBudget; omega
  have hall := itCfD_at_calls h.atf dl tl q κ m hc.len_tl (hN.trans hNB)
    (hq.trans hNB) (hk.trans hNB) hvmB hrangeB hanyB hfindB hblocksB htableB
  exact hall.mono (by unfold itCfDAtBudget; omega)

end GI.Impl
