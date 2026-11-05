module

public import Workspace.Impl.AggItemCiSojFM

@[expose] public section

/-! # The full program for the even permutations fixing the left side -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {q : ℕ}

/-- From the source side-color table, build the pointwise marker and extract its
exact even stabilizer generators. -/
def itcsFixProgF (rng mp fg : ℕ) : Expr :=
  .letE (.call rng (.length (.var 0)))
    (.letE (.call mp (mk2 (.var 0) (.var 1))) (.call fg (.var 2)))

/-- Common budget for the full marker and generator construction. -/
def itcsFixProgW (q : ℕ) : ℕ :=
  1000*(itcsFixGenC (5*(q+1)^2)+20*(q+1)^2+10)

/-- Total cost of the pointwise-fixing generator program. -/
def itcsFixProgC (q : ℕ) : ℕ :=
  40*(itcsFixProgW q+1)+7000*(q+1)^3+itcsFixMarkC q+itcsFixGenC (5*(q+1)^2)

/-- All construction and stabilizer-program preconditions are discharged. -/
theorem itcs_fix_prog {Pg : Program} {Ii : ItciIdx} {f rng mp mk fg : ℕ}
    (hi : ItciOk Pg Ii) (hf : Pg.funs[f]? = some (itcsFixProgF rng mp fg))
    (hr : Pg.HasAt rng (rangeFuns rng)) (hm : Pg.HasAt mp (mapFuns mp mk))
    (hmarker : Pg.funs[mk]? = some itcsFixMarkF) (hfg : Pg.funs[fg]? = some (itcsFixGenF Ii.f))
    (lab : Fin q → ℕ) (hl : ∀ a,lab a≤2) :
    FunDet Pg f (encFun lab) (.list ((itciMs (itcsFixFrom lab) (itciOt (itcsFixFrom lab))).map encPerm))
      (itcsFixProgC q) := by
  let Bw := itcsFixProgW q
  have budget : 100*itcsFixGenC (5*(q+1)^2)+100*(q+1)^2+1000≤Bw := by
    dsimp only [Bw]; unfold itcsFixProgW; omega
  have hq : q+1≤(q+1)^2 := Nat.le_self_pow (by omega) _
  have h1 : 1≤(q+1)^2 := Nat.one_le_pow 2 (q+1) (by omega)
  have wl := wt_encFun_le lab hl
  have wr := wt_range_le q
  have wm : (encFun (itcsFixFrom lab)).wt ≤5*(q+1)^2 := it_encFun_wt _ (itcs_fix_from_le lab)
  have gen := itcs_fix_gen_prog hi hfg (itcsFixFrom lab) wm
  have wo := itcs_det_weight gen
  have wi : (Val.list [encFun lab,natList (List.range q)]).wt≤Bw := by
    have h:=wt_list2_le (encFun lab) (natList (List.range q))
    omega
  have vv : StDC Pg [encFun lab] (.var 0) (encFun lab) 1 0 Bw := StDC.var' rfl (wl.trans (by omega))
  have len := StDC.length vv (by simp only [List.length_map,List.length_finRange]; omega)
  simp only [List.length_map,List.length_finRange] at len
  have rg := StDC.call len (range_det hr q) (wr.trans (by omega))
  have v0 : StDC Pg [encFun lab,natList (List.range q)] (.var 0) (encFun lab) 1 0 Bw := StDC.var' rfl (wl.trans (by omega))
  have r1 : StDC Pg [encFun lab,natList (List.range q)] (.var 1) (natList (List.range q)) 1 0 Bw := StDC.var' rfl (wr.trans (by omega))
  have mc := StDC.call (StDC.mk2 v0 r1 wi (by omega)) (itcs_fix_mark_table hm hmarker lab hl) (wm.trans (by omega))
  have v2 : StDC Pg [encFun lab,natList (List.range q),encFun (itcsFixFrom lab)] (.var 2)
      (encFun (itcsFixFrom lab)) 1 0 Bw := StDC.var' rfl (wm.trans (by omega))
  have gc := StDC.call v2 gen (wo.trans (by omega))
  have body := StDC.letE rg (StDC.letE mc gc (wo.trans (by omega))) (wo.trans (by omega))
  exact StDC.funDet hf body (by unfold itcsFixProgC; dsimp only [Bw]; omega)

/-- Polynomial round cost of the full pointwise-fixing program. -/
theorem itcs_fix_prog_pbu : PBU fun _ W _ => itcsFixProgC (2*W+3) := by
  simp only [itcsFixProgC,itcsFixProgW,itcsFixGenC,itciFC,itcsFixMarkC,itcsMarkW,mapK]
  norm_poly

end GI.Impl
