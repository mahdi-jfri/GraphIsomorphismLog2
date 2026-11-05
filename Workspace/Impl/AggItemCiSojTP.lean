module

public import Workspace.Impl.AggItemCiSojTest

@[expose] public section

/-!
# The imprimitive-pair callback with every bound discharged

Only the source's palette bound and goodness remain as mathematical preconditions.
Both come from the branch object interface. The table reader and component counter
are installed programs whose contracts are already proved.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- The fiber index list has polynomial weight in the old label set. -/
theorem itcs_fv_weight (X : PairCfg q) : (itcqFV X).wt ≤ 5 * (q + 1) ^ 2 := by
  have hn : X.fiber.card ≤ q := (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have h := wt_list_map_le (itciFl X.fiber) (fun a => Val.nat a.val) (W := q + 2)
    (fun a _ => (wt_nat_le _).trans (by have := a.isLt; omega))
  simp only [itciFl_length] at h
  have hh : (itcqFV X).wt ≤ X.fiber.card * (2 * (q + 2) + 1) + 4 := by
    simpa only [itcqFV, natList, List.map_map, Function.comp_def] using h
  have hm := Nat.mul_le_mul_right (2 * (q + 2) + 1) hn
  nlinarith

private theorem itcs_five_max {a b c d e : Val} {V : ℕ}
    (ha : a.wt ≤ V) (hb : b.wt ≤ V) (hc : c.wt ≤ V) (hd : d.wt ≤ V) (he : e.wt ≤ V) :
    (Val.list [a, b, c, d, e]).wt ≤ 10 * V + 9 := by
  have h := itcs_wt_list5 a b c d e
  omega

/-- Cost of one literal pair test with the full component computation. -/
def itcsTestC (q B : ℕ) : ℕ := 200 * (100 * itcsCompW q B + 1) + itcsSizeC q B

/-- The literal pair-test program, with all table-reader and counter preconditions proved. -/
theorem itcs_test_prog {q B : ℕ} {Pg : Program} {Ii : itcsCompIdx} {ft fp fs : ℕ}
    (hi : itcsCompOk Pg Ii) (hft : Pg.funs[ft]? = some (itcsTestF fp fs))
    (hfp : Pg.funs[fp]? = some itcqPcF) (hfs : Pg.funs[fs]? = some (itcsSizeF Ii.f Ii.c1.sz))
    (X : PairCfg q) (x₀ : Fin q) (hX : X.Good deltaB) (hx : x₀ ∈ X.fiber)
    (hcol : itCfColsLe (.pair X x₀) B) (t : Fin (X.fiber.card * X.fiber.card)) :
    FunDet Pg ft (.list [itcsTestCtx X x₀, .nat t]) (boolVal (itcsImpQ X (.nat t)))
      (itcsTestC q B) := by
  let a := ((itciPE X.fiber.card).symm t).1
  let b := ((itciPE X.fiber.card).symm t).2
  let v := itcqPC X rfl ((itciPE X.fiber.card).symm t)
  have hv : v ≤ B := hcol.1 _ _
  have hw := itcs_comp_weights X x₀ v hcol hv
  have hn : X.fiber.card ≤ q := (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have htq : (t : ℕ) < q * q := t.isLt.trans_le (Nat.mul_le_mul hn hn)
  have budget : 10 * itCfObjB q B + 50 * (q * q + 1) ^ 2 + 10 * itcsGenW q +
      20 * B + 20 * q + 100 ≤ itcsCompW q B := by unfold itcsCompW; omega
  have hcert : (rcCertIn X x₀).wt ≤ itcsCompW q B :=
    (st_wt_mem (by simp : rcCertIn X x₀ ∈ [.nat 2, rcCertIn X x₀])).trans
      ((itCfOutV_wt_le hcol).trans (by omega))
  have htab : (rcColVal X).wt ≤ itcsCompW q B :=
    (st_wt_mem (List.mem_cons_self ..)).trans hcert
  have hj : (Val.nat X.j).wt ≤ itcsCompW q B :=
    (st_wt_mem (by simp : Val.nat X.j ∈ [rcColVal X, .nat X.j, .nat x₀])).trans hcert
  have hvn : (Val.nat v).wt ≤ itcsCompW q B := (wt_nat_le _).trans (by omega)
  have hqn : (Val.nat q).wt ≤ itcsCompW q B := (wt_nat_le _).trans (by have := hw.qle; omega)
  have hnn : (Val.nat X.fiber.card).wt ≤ itcsCompW q B := (wt_nat_le _).trans (by have := hw.qle; omega)
  have hxn : (Val.nat x₀).wt ≤ itcsCompW q B :=
    (wt_nat_le _).trans (by have := x₀.isLt; have := hw.qle; omega)
  have htn : (Val.nat t).wt ≤ itcsCompW q B := (wt_nat_le _).trans (by have := hw.qsq; omega)
  have hqp : (q + 1) ^ 2 ≤ (q * q + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.le_mul_self q) 1) 2
  have hfv : (itcqFV X).wt ≤ itcsCompW q B := by
    have hh := (itcs_fv_weight X).trans (Nat.mul_le_mul_left 5 hqp)
    omega
  have hctx : (itcsTestCtx X x₀).wt ≤ 6 * itcsCompW q B + 7 :=
    st_wt_list3 hcert hfv hqn
  have hpc : (Val.list [rcColVal X, itcqFV X, .nat X.fiber.card]).wt ≤ 6 * itcsCompW q B + 7 :=
    st_wt_list3 htab hfv hnn
  have h10 : 10 ≤ itcsCompW q B := by have := hw.qle; omega
  refine itcs_test_spec hft hfp X x₀ hX hx t ?_ ?_ ?_
    (itcs_size_prog hi hfs X x₀ v hcol hv) ?_
  · have hh := wt_list2_le (itcsTestCtx X x₀) (.nat t)
    omega
  · have hh := wt_list2_le (.list [rcColVal X, itcqFV X, .nat X.fiber.card]) (.nat t)
    omega
  · exact (itcs_five_max htab hj hvn hqn hxn).trans (by omega)
  · have := hw.qle
    omega

/-- The callback cost remains polynomial at the round's degree and palette bounds. -/
theorem itcs_test_pbu : PBU fun _ W _ => itcsTestC (2 * W + 3) (2 * (2 * W + 3) ^ 64) := by
  unfold itcsTestC
  refine PBU.add ?_ itcs_size_pbu
  simp only [itcsCompW, itCfObjB, itcsGenW]
  norm_poly

end GI.Impl
