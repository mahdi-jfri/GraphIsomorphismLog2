import Workspace.Impl.AggItemCiSojTab
import Workspace.Impl.AggItemCfObW

/-!
# Weight bounds for the component-table program

Every constructed table is explicit and polynomial in the label count and the
input palette bound. The budget below includes the raw color table, both index
ranges, all `q²` permutation tables, and the final component labels.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms)

/-- Weight of a five-entry value. -/
theorem itcs_wt_list5 (a b c d e : Val) :
    (Val.list [a, b, c, d, e]).wt ≤ 2 * a.wt + 2 * b.wt + 2 * c.wt +
      2 * d.wt + 2 * e.wt + 9 := by
  have h := wt_list_le [a, b, c, d, e]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil] at h
  omega

private theorem itcs_nested5 {a b c d e r : Val} {C B q Q : ℕ}
    (ha : a.wt ≤ C) (hb : b.wt ≤ B + 2) (hc : c.wt ≤ B + 2)
    (hd : d.wt ≤ q + 2) (he : e.wt ≤ q + 2) (hr : r.wt ≤ 4 * Q) :
    (Val.list [.list [a, b, c, d, e], r]).wt ≤ 4 * C + 8 * B + 8 * q + 8 * Q + 56 := by
  have h1 := itcs_wt_list5 a b c d e
  have h2 := wt_list2_le (.list [a, b, c, d, e]) r
  omega

private theorem itcs_nested2 {a b r : Val} {q Q : ℕ}
    (ha : a.wt ≤ q + 2) (hb : b.wt ≤ q + 2) (hr : r.wt ≤ 4 * Q) :
    (Val.list [.list [a, b], r]).wt ≤ 8 * q + 8 * Q + 34 := by
  have h1 := wt_list2_le a b
  have h2 := wt_list2_le (.list [a, b]) r
  omega

/-- A polynomial weight budget for the whole component-table computation. -/
def itcsCompW (q B : ℕ) : ℕ :=
  100 * (itCfObjB q B + (q * q + 1) ^ 2 + itcsGenW q + B + q + 10)

set_option maxHeartbeats 400000 in
/-- All table-construction weight obligations follow from the explicit palette bound. -/
theorem itcs_comp_weights {q B : ℕ} (X : PairCfg q) (x₀ : Fin q) (v : ℕ)
    (hcol : itCfColsLe (.pair X x₀) B) (hv : v ≤ B) :
    itcsCompBounds X v (itcsCompW q B) := by
  have hc : (rcColVal X).wt ≤ itCfObjB q B :=
    (st_wt_mem (by simp : rcColVal X ∈ [rcColVal X, .nat X.j, .nat x₀])).trans
      ((st_wt_mem (by simp : rcCertIn X x₀ ∈ [.nat 2, rcCertIn X x₀])).trans
        (itCfOutV_wt_le hcol))
  have hj : (Val.nat X.j).wt ≤ B + 2 := (wt_nat_le _).trans (by have := hcol.2; omega)
  have hvw : (Val.nat v).wt ≤ B + 2 := (wt_nat_le _).trans (by omega)
  have hqn : (Val.nat q).wt ≤ q + 2 := wt_nat_le q
  have hs : q ≤ q * q := Nat.le_mul_self q
  have hq2 : (q + 1) ^ 2 ≤ (q * q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hsq : q * q + 1 ≤ (q * q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hr : (natList (List.range q)).wt ≤ 4 * (q * q + 1) ^ 2 :=
    (wt_range_le q).trans (Nat.mul_le_mul_left 4 hq2)
  have hrr : (natList (List.range (q * q))).wt ≤ 4 * (q * q + 1) ^ 2 := wt_range_le _
  have hper : ∀ p : Perm (Fin q), (encPerm p).wt ≤ 4 * (q * q + 1) ^ 2 :=
    fun p => (wt_encPerm_le p).trans (Nat.mul_le_mul_left 4 hq2)
  have budget : 10 * itCfObjB q B + 50 * (q * q + 1) ^ 2 + 10 * itcsGenW q +
      20 * B + 20 * q + 100 ≤ itcsCompW q B := by
    unfold itcsCompW
    omega
  have hd : (itcsCompData X v).wt ≤
      2 * itCfObjB q B + 4 * B + 2 * q + 8 * (q * q + 1) ^ 2 + 21 := by
    have h := itcs_wt_list5 (rcColVal X) (.nat X.j) (.nat v) (.nat q) (natList (List.range q))
    change (Val.list [rcColVal X, .nat X.j, .nat v, .nat q, natList (List.range q)]).wt ≤ _
    omega
  have hg := itcs_gen_weight X v
  refine ⟨?_, by omega, by omega, by omega, ?_, ?_, ?_, ?_, fun p => by have := hper p; omega,
    by omega, ?_, ?_, by omega, by omega⟩
  · have h := wt_list_le [rcColVal X, .nat X.j, .nat v, .nat q]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil] at h
    omega
  · have h := wt_list2_le (itcsCompData X v) (natList (List.range (q * q)))
    omega
  · intro t
    have h := wt_list2_le (itcsCompData X v) (.nat t)
    have ht := wt_nat_le (t : ℕ)
    have hlt := t.isLt
    omega
  · intro a b
    have ha := wt_nat_le (a : ℕ)
    have hb := wt_nat_le (b : ℕ)
    have hqa := a.isLt
    have hqb := b.isLt
    have h := itcs_nested5 (q := q) hc hj hvw ((wt_nat_le (a : ℕ)).trans (by omega))
      ((wt_nat_le (b : ℕ)).trans (by omega)) hr
    clear hcol hv hd hg hrr hper hq2 hsq hs hqn ha hb hqa hqb
    omega
  · intro a b
    have hqa := a.isLt
    have hqb := b.isLt
    have h := itcs_nested2 (q := q) ((wt_nat_le (a : ℕ)).trans (by omega))
      ((wt_nat_le (b : ℕ)).trans (by omega)) hr
    clear hcol hv hc hj hvw hd hg hrr hper hq2 hsq hs hqn hqa hqb
    omega
  · have h := wt_list2_le (.nat q) (.list ((itcsSqEdges X v).map encPerm))
    change (Val.list [.nat q, .list ((itcsSqEdges X v).map encPerm)]).wt ≤ _
    omega
  · have hl := it_encFun_wt (itcsLab X v) (fun a => (itcs_lab_lt X v a).le)
    omega

end GI.Impl
