import Workspace.Impl.AggItemCiSojCT

/-!
# Counting the component at the fixed source vertex

The component program gives least-component labels. The existing block-size
program counts labels equal to the source vertex's label. This returns exactly
the component size used by both tests in `AggItemCiSojOne`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

/-- On `[table,j,v,q,x₀]`, the size of the color-`v` component at `x₀`. -/
def itcsSizeF (comp sz : ℕ) : Expr :=
  .call sz (mk2 (.call comp (mk4 (arg 0) (arg 1) (arg 2) (arg 3))) (arg 4))

/-- Cost of one component-size test. -/
def itcsSizeC (q B : ℕ) : ℕ :=
  30 * (itcsCompW q B + 1) + itcsCompTotal q B + (countK + 1000) * (q + 1) ^ 3

/-- The component-size program with all weights and library preconditions discharged. -/
theorem itcs_size_prog {q B : ℕ} {Pg : Program} {Ii : itcsCompIdx} {f : ℕ}
    (hi : itcsCompOk Pg Ii) (hf : Pg.funs[f]? = some (itcsSizeF Ii.f Ii.c1.sz))
    (X : PairCfg q) (x₀ : Fin q) (v : ℕ) (hcol : itCfColsLe (.pair X x₀) B) (hv : v ≤ B) :
    FunDet Pg f (.list [rcColVal X, .nat X.j, .nat v, .nat q, .nat x₀])
      (.nat (itpSz (itcsLab X v) x₀)) (itcsSizeC q B) := by
  have hw := itcs_comp_weights X x₀ v hcol hv
  have hc : (rcColVal X).wt ≤ itCfObjB q B :=
    (st_wt_mem (by simp : rcColVal X ∈ [rcColVal X, .nat X.j, .nat x₀])).trans
      ((st_wt_mem (by simp : rcCertIn X x₀ ∈ [.nat 2, rcCertIn X x₀])).trans
        (itCfOutV_wt_le hcol))
  have hj := wt_nat_le X.j
  have hvw := wt_nat_le v
  have hqn := wt_nat_le q
  have hxn := wt_nat_le (x₀ : ℕ)
  have hxq := x₀.isLt
  have hjB := hcol.2
  have budget : 10 * itCfObjB q B + 50 * (q * q + 1) ^ 2 + 10 * itcsGenW q +
      20 * B + 20 * q + 100 ≤ itcsCompW q B := by unfold itcsCompW; omega
  have hin : (Val.list [rcColVal X, .nat X.j, .nat v, .nat q, .nat x₀]).wt ≤ itcsCompW q B := by
    have hh := itcs_wt_list5 (rcColVal X) (.nat X.j) (.nat v) (.nat q) (.nat x₀)
    omega
  have hqp : (q + 1) ^ 2 ≤ (q * q + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.le_mul_self q) 1) 2
  have hl := it_encFun_wt (itcsLab X v) (fun a => (itcs_lab_lt X v a).le)
  have hszarg : (Val.list [encFun (itcsLab X v), .nat x₀]).wt ≤ itcsCompW q B := by
    have hh := wt_list2_le (encFun (itcsLab X v)) (.nat x₀)
    have hhl := hl.trans (Nat.mul_le_mul_left 5 hqp)
    omega
  have hsz : itpSz (itcsLab X v) x₀ ≤ q := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have hout : (Val.nat (itpSz (itcsLab X v) x₀)).wt ≤ itcsCompW q B :=
    (wt_nat_le _).trans (by have := hw.qle; omega)
  let vs : List Val := [rcColVal X, .nat X.j, .nat v, .nat q, .nat x₀]
  have get {i : ℕ} {w : Val} (he : vs[i]? = some w) (hiw : i + 2 ≤ itcsCompW q B) :
      StDC Pg [.list vs] (arg i) w 3 0 (itcsCompW q B) :=
    StDC.arg he hin hiw ((st_wt_mem (List.mem_of_getElem? he)).trans hin)
  have args := StDC.mk4 (get (i := 0) rfl (by have := hw.qle; omega))
    (get (i := 1) rfl (by have := hw.qle; omega))
    (get (i := 2) rfl (by have := hw.qle; omega))
    (get (i := 3) rfl (by have := hw.qle; omega)) hw.input (by have := hw.qle; omega)
  have comp := StDC.call args (itcs_comp_prog hi X x₀ v hcol hv) hw.labels
  have sa := StDC.mk2 comp (get (i := 4) rfl (by have := hw.qle; omega)) hszarg (by have := hw.qle; omega)
  have sc := StDC.call sa (it_szB_spec hi.c1.sz hi.c1.cnt (itcs_lab_lt X v) x₀) hout
  clear hw hc hj hvw hqn hxn hxq hjB budget hin hqp hl hszarg hsz hout get args comp sa
  exact StDC.funDet hf sc (by simp only [itcsSizeC, Nat.add_mul]; omega)

/-- Polynomial cost after inserting the round's degree and palette bound. -/
theorem itcs_size_pbu : PBU fun _ W _ => itcsSizeC (2 * W + 3) (2 * (2 * W + 3) ^ 64) := by
  simp only [itcsSizeC, itcsCompTotal, itcsCompC, itcsSqMapC, itcsCompW, itCfObjB,
    itcsGenW, countK, mapK, orbitK]
  norm_poly

end GI.Impl
