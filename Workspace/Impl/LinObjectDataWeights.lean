module

public import Workspace.Impl.LinObjectDataCost

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectDataLocalArg_wt (a m ns ts groups : Val) (W P A R : ℕ)
    (ha : a.wt ≤ W) (hm : m.wt ≤ A) (hn : ns.wt ≤ R) (ht : ts.wt ≤ R) (hg : groups.wt ≤ P) :
    (Val.list [.list [a, m, ns, ts], groups]).wt ≤ 100 * (W + P + A + 2 * R + 1) ^ 2 := by
  have hx := wt_list4_le a m ns ts
  have hy := wt_list2_le (.list [a, m, ns, ts]) groups
  have hs : W + P + A + 2 * R + 1 ≤ (W + P + A + 2 * R + 1) ^ 2 :=
    Nat.le_self_pow (by decide) _
  omega

theorem linObjectDataNormalArg_wt (rs ts rows : Val) (W R L : ℕ)
    (hr : rs.wt ≤ R) (ht : ts.wt ≤ R) (hl : rows.wt ≤ L) :
    (Val.list [rs, ts, rows]).wt ≤ 100 * (W + L + 2 * R + 1) ^ 2 := by
  have hx := wt_list3_le rs ts rows
  have hs : W + L + 2 * R + 1 ≤ (W + L + 2 * R + 1) ^ 2 := Nat.le_self_pow (by decide) _
  omega

set_option maxHeartbeats 500000 in
/-- Scalar accounting for the seven calls in the presentation collector. -/
theorem linObjectDataTail_cost
    (W S PB AB RB LB WB VB n t N cn ct cl cr ci cw cv cost : ℕ)
    (a m idsN idsT idsR groups pv lv win wn vn ctx r2 r4 r5 nw : ℕ)
    (hS : (W + 1) ^ 2 = S) (hn : n * n ≤ S) (hN : N ≤ S + 1) (ht : t ≤ W)
    (ha : a ≤ W) (hm : m ≤ AB) (hnw : nw ≤ W)
    (widN : idsN ≤ RB) (widT : idsT ≤ RB) (widR : idsR ≤ RB)
    (wg : groups ≤ PB) (wp : pv ≤ PB) (wl : lv ≤ LB)
    (wwn : wn ≤ WB) (wvn : vn ≤ VB)
    (wctx : ctx ≤ 2 * (a + m + idsN + idsT) + 8)
    (wwin : win ≤ 2 * (idsR + idsT + lv) + 7)
    (hcn : cn ≤ 2 * W + 0 + 5 + (0 + 3) + nw + 1 +
      (2 * W + 0 + 5 + (0 + 3) + nw + 1) + n * n + 3 + (1 + 3) + N + 3 + RB + idsN + 1)
    (hct : ct ≤ m + 1 + t + 3 + RB + idsT + 1)
    (hcr : cr ≤ m + 1 + t + 3 + (idsN + 1 + N + 3) + (t + N) + 3 + RB + idsR + 1)
    (hci : ci ≤ idsR + 1 + (idsT + 1) + (lv + 1) + 3 * win + 8)
    (hcl : cl ≤ 2 * W + 0 + 5 + (m + 1) + (idsN + 1) + (idsT + 1) +
      4 * ctx + 9 + (pv + 1 + (1 + 3) + groups + 1) +
      2 * r2 + 7 + 2 * LB + 1)
    (hcw : cw ≤ win + 1 + 2 * WB + 1) (hcv : cv ≤ win + 1 + 2 * VB + 1)
    (hcost : cost ≤ pv + 1 + (m + 1) + (win + 1) + (wn + 1) +
      4 * r4 + 9 + (vn + 1) + r5 + 1)
    (hlocal : r2 ≤ 2 * (ctx + groups) + 6)
    (hret4 : r4 ≤ 2 * (pv + m + win + wn) + 8)
    (hret5 : r5 ≤ 2 * (pv + m + win + wn + vn) + 9) :
    cn + (ct + (cl + (cr + (ci + (cw + (cv + cost + r5 + 1) +
      r5 + 1) + r5 + 1) +
      r5 + 1) + r5 + 1) +
      r5 + 1) + r5 + 1 ≤
      1000000 * (S + W + PB + AB + RB + LB + WB + VB + 1) := by
  let T := S + W + PB + AB + RB + LB + WB + VB + 1
  have hT : 1 ≤ T := by
    clear * - T
    omega
  have hctx : ctx ≤ 20 * T := by
    clear * - T wctx ha hm widN widT
    omega
  have hwin : win ≤ 20 * T := by
    clear * - T wwin widR widT wl
    omega
  have hl : r2 ≤ 50 * T := by
    clear * - T hlocal hctx wg
    omega
  have hr4 : r4 ≤ 50 * T := by
    clear * - T hret4 wp hm hwin wwn
    omega
  have hr5 : r5 ≤ 60 * T := by
    clear * - T hret5 wp hm hwin wwn wvn
    omega
  have bn : cn ≤ 1000 * T := by
    clear * - T hcn hn hN hnw widN
    omega
  have bt : ct ≤ 1000 * T := by
    clear * - T hct hm ht widT
    omega
  have bl : cl ≤ 1000 * T := by
    clear * - T hcl hm widN widT hctx wp wg hl
    omega
  have br : cr ≤ 1000 * T := by
    clear * - T hcr hm ht widN hN widR
    omega
  have bi : ci ≤ 1000 * T := by
    clear * - T hci widR widT wl hwin
    omega
  have bw : cw ≤ 1000 * T := by
    clear * - T hcw hwin
    omega
  have bv : cv ≤ 1000 * T := by
    clear * - T hcv hwin
    omega
  have bc : cost ≤ 1000 * T := by
    clear * - T hcost wp hm hwin wwn wvn hr4 hr5
    omega
  change _ ≤ 1000000 * T
  clear * - T hT bn bt bl br bi bw bv bc hr5
  omega

end GI.Impl
