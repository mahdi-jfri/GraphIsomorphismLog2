import Workspace.Impl.TermRepsCost

/-!
# T3: `Iface.TermRepsSpec` from `TermRadSpec` and Membership

`Iface.tm_termRepsSpec` proves the hypothesis `TermRepsSpec` of the split over the radical
cosets (`TermSplit.lean`) from the radical preimage `TermRadSpec` (T2), the cited
**Membership** task and the cited bounds of [GMP] (for `[H : R] ≤ m^{2 log₂ m}`, Corollary A.22).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Membership)

namespace Iface

variable (Pg : Program)

/-- **T3.** The program `tmRpEntryF` meets `TermRepsSpec`. -/
theorem tm_termRepsSpec (hm : Membership) (hAb : GI.Cited.GMPAbelianFactors)
    (hOut : GI.Cited.GMPOutBound) (hTr : GI.Cited.GMPTransitiveNonabelian)
    {f fi mk grad rg wh st fb gt ab pt jm comp inv : ℕ}
    (h : TmRpAt Pg hm f fi mk grad rg wh st fb gt ab pt jm comp inv) {K D : ℕ}
    (hrad : TermRadSpec Pg K D grad) : TermRepsSpec Pg (tmRpA hm K D) f := by
  intro Ω C _ S k e c hc sv lv L hsv hlv hq0 hgood hrow label hnat hq m h0 E hP σH σN σS hH hNg hS
    htr hlH hlN hlS hcard hsN hN hqα us vs hus hvs
  set F := RowForm.ofPure hnat hq E hP ⟨0, h0⟩ with hF
  set T := F.rowTerminal P₀ htr hcard hsN hN hqα with hT
  set tin := Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
    encFun (rowLab e L.con.blocks)] with htin
  set V := Val.list [tin, .list us, .list vs] with hV
  have hNH : gens σN ≤ gens σH := by rw [hH, hNg]; exact F.Nb_le
  have hnorm : GI.Multicoset.Normalizes (gens σH) (gens σN) := by
    rw [hH, hNg]; exact F.normalizes
  have hRad : GI.Multicoset.radicalPreimage (gens σH) (gens σN) = tmRad T := by
    rw [hH, hNg]; rfl
  have hHb : gens σH = T.Hb := hH
  have hq1 : 0 < L.q := by omega
  refine FunAll.intro h.entry ?_
  unfold tmRpEntryF
  have dt := Det.get' (Det.var' (P := Pg) (env := [V]) (i := 0) (v := V) rfl) (Det.nat 0)
    (show [tin, Val.list us, Val.list vs][0]? = some tin from rfl)
  refine (EvalAll.call_spec dt (tmRpInner_spec e S E hm h hrad sv lv
    (encFun (rowLab e L.con.blocks)) hq1 σH σN σS hNH hnorm).wt_lt).mono ?_
  rintro w cost ⟨cb, ⟨⟨reps, rfl, ⟨j, hinv, hj⟩, hcb⟩, hwc⟩, hcost⟩
  have hfin : (∀ x ∈ gens σH, ∃ r ∈ reps, ∃ y ∈ GI.Multicoset.radicalPreimage (gens σH) (gens σN),
      x = y * r) ∧ reps.length = ((GI.Multicoset.radicalPreimage (gens σH)
        (gens σN)).subgroupOf (gens σH)).index := tmRp_final rfl hinv hj
  rw [hRad, hHb] at hfin hcb
  rw [hHb] at hinv
  refine ⟨reps, rfl, hinv.sub, fun x hx => ?_, hfin.2, ?_⟩
  · obtain ⟨r, hr, y, hy, rfl⟩ := hfin.1 x hx
    exact ⟨r, hr, y, hy, rfl⟩
  -- the cost
  have hVY : V.wt + 1 ≤ tmVB S.N := tm_wtV_le hsv hlv E hq1 hlH hlN hlS hus hvs
  have wtin : tin.wt < V.wt := wt_le_wt_list (by simp)
  have hidx : ((((tmRad T).subgroupOf T.Hb).index : ℕ) : ℝ) ≤ expLogSq 3 S.N := by
    refine (tm_index_le hAb hOut hTr T).trans ?_
    have hB : Fintype.card T.B ≤ S.N := by
      have h1 : Fintype.card T.B = m := by
        change Fintype.card (Fin m) = m
        exact Fintype.card_fin m
      have h2 : m ≤ m * L.q := Nat.le_mul_of_pos_right _ (by omega)
      rw [Fintype.card_fin] at hcard
      omega
    exact tm_rpow_le_expLogSq hB
  have hmain := tmRp_cost_le hm K D hidx (X := tin.wt + 1) (W := V.wt) (by omega) (by omega)
    (by omega)
  refine le_trans ?_ hmain
  have hnat : cost ≤ 2 * tmRpCost hm K D ((tmRad T).subgroupOf T.Hb).index (tin.wt + 1) +
      3 * V.wt + 20 := by
    have e1 : (Val.list [tin, Val.list us, Val.list vs]).wt = V.wt := rfl
    have hcb' : cb ≤ tmRpCost hm K D ((tmRad T).subgroupOf T.Hb).index (tin.wt + 1) := hcb
    omega
  exact_mod_cast hnat

end Iface

end GI.Impl
