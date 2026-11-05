module

public import Workspace.Impl.AggItemCiSojBal

@[expose] public section

/-!
# The complete balanced-partition program

Build the two row-color tables and apply the existing partition overcoset program.
Its singleton blocks are exactly the blocks of `PairCfg.balPart`.
-/

set_option maxHeartbeats 400000

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- On `[rcCertIn X x₀, rcCertIn Y y₀]`, return the balanced overcoset list. -/
def itcsBalPartF (rng mp part : ℕ) : Expr :=
  .letE (.call rng (.length (.get (arg 0) (.nat 0))))
    (.letE (.call mp (mk2 (arg 0) (.var 1)))
      (.letE (.call mp (mk2 (arg 1) (.var 1)))
        (.call part (mk2 (.var 2) (.var 3)))))

/-- Bound for one row-color table. -/
def itcsBalM (q B : ℕ) : ℕ := q * (4 * B + 7) + 4

/-- Common weight budget for the balanced item. -/
def itcsBalPartW (q B : ℕ) : ℕ :=
  1000 * (itCfObjB q B + itcsBalM q B + (q + 1) ^ 3 + 10)

/-- Cost of both table constructions and the exact overcoset program. -/
def itcsBalPartC (q B : ℕ) : ℕ :=
  100 * (itcsBalPartW q B + 1) + 7000 * (q + 1) ^ 3 +
    2 * itcsBalTC q B + itciFC (itcsBalM q B)

/-- The actual balanced-item body, including the two table maps. -/
theorem itcs_bal_part_prog {Pg : Program} {Ii : ItciIdx} {f rng mp fb fe B : ℕ}
    (hi : ItciOk Pg Ii) (hf : Pg.funs[f]? = some (itcsBalPartF rng mp Ii.f))
    (hr : Pg.HasAt rng (rangeFuns rng)) (hm : Pg.HasAt mp (mapFuns mp fe))
    (he : Pg.funs[fe]? = some (itcsBalB fb)) (hb : Pg.funs[fb]? = some itcqFbT)
    (X Y : PairCfg q) (x₀ y₀ : Fin q)
    (hX : itCfColsLe (.pair X x₀) B) (hY : itCfColsLe (.pair Y y₀) B)
    (E : Subgroup (alternatingGroup (Fin q))) :
    FunDet Pg f (.list [rcCertIn X x₀, rcCertIn Y y₀])
      (itciOV (itciOs (itcsBal X x₀) (itcsBal Y y₀) (itciOt (itcsBal X x₀)) E))
      (itcsBalPartC q B) := by
  let Bw := itcsBalPartW q B
  have budget : 10 * itCfObjB q B + 10 * itcsBalM q B + 500 * (q + 1) ^ 3 +
      1000 ≤ Bw := by dsimp only [Bw]; unfold itcsBalPartW; omega
  have pow1 : q + 1 ≤ (q + 1) ^ 3 := Nat.le_self_pow (by omega) _
  have pow2 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have cert (Z : PairCfg q) (z : Fin q) (hZ : itCfColsLe (.pair Z z) B) :
      (rcCertIn Z z).wt ≤ itCfObjB q B :=
    (st_wt_mem (by simp : rcCertIn Z z ∈ [.nat 2, rcCertIn Z z])).trans (itCfOutV_wt_le hZ)
  have cx := cert X x₀ hX
  have cy := cert Y y₀ hY
  have lx : (encFun (itcsBal X x₀)).wt ≤ itcsBalM q B := by
    have h := wt_encFun_le (itcsBal X x₀) (itcs_bal_le hX)
    dsimp only [itcsBalM]
    convert h using 1 <;> ring
  have ly : (encFun (itcsBal Y y₀)).wt ≤ itcsBalM q B := by
    have h := wt_encFun_le (itcsBal Y y₀) (itcs_bal_le hY)
    dsimp only [itcsBalM]
    convert h using 1 <;> ring
  have rin := wt_range_le q
  have winput : (Val.list [rcCertIn X x₀, rcCertIn Y y₀]).wt ≤ Bw := by
    have h := wt_list2_le (rcCertIn X x₀) (rcCertIn Y y₀)
    omega
  have wxr : (Val.list [rcCertIn X x₀, natList (List.range q)]).wt ≤ Bw := by
    have h := wt_list2_le (rcCertIn X x₀) (natList (List.range q))
    omega
  have wyr : (Val.list [rcCertIn Y y₀, natList (List.range q)]).wt ≤ Bw := by
    have h := wt_list2_le (rcCertIn Y y₀) (natList (List.range q))
    omega
  have wpart : (Val.list [encFun (itcsBal X x₀), encFun (itcsBal Y y₀)]).wt ≤ Bw := by
    have h := wt_list2_le (encFun (itcsBal X x₀)) (encFun (itcsBal Y y₀))
    omega
  let ov := itciOV (itciOs (itcsBal X x₀) (itcsBal Y y₀) (itciOt (itcsBal X x₀)) E)
  have wov : ov.wt ≤ Bw := (itciOV_wt (itciOs_props _ _ E).1 (itciOs_props _ _ E).2).trans (by omega)
  have get {rest : List Val} {i : ℕ} {v : Val}
      (hv : [rcCertIn X x₀, rcCertIn Y y₀][i]? = some v) (hiw : i + 2 ≤ Bw) :
      StDC Pg (.list [rcCertIn X x₀, rcCertIn Y y₀] :: rest) (arg i) v 3 0 Bw :=
    StDC.arg hv winput hiw ((st_wt_mem (List.mem_of_getElem? hv)).trans winput)
  have tabw : (rcColVal X).wt ≤ Bw := (st_wt_mem (List.mem_cons_self ..)).trans (cx.trans (by omega))
  have table := StDC.get (get (rest := []) (i := 0) rfl (by omega)) (StDC.nat 0 (by omega)) rfl tabw
  have qlen := StDC.length table (by simp only [List.length_map, List.length_finRange]; omega)
  simp only [List.length_map, List.length_finRange] at qlen
  have rg := StDC.call qlen (range_det hr q) (rin.trans (by omega))
  have r1 : StDC Pg [.list [rcCertIn X x₀, rcCertIn Y y₀], natList (List.range q)] (.var 1)
      (natList (List.range q)) 1 0 Bw := StDC.var' rfl (rin.trans (by omega))
  have xm := StDC.call (StDC.mk2 (get (i := 0) rfl (by omega)) r1 wxr (by omega))
    (itcs_bal_table hm he hb X x₀ hX) (lx.trans (by omega))
  have r2 : StDC Pg [.list [rcCertIn X x₀, rcCertIn Y y₀], natList (List.range q),
      encFun (itcsBal X x₀)] (.var 1) (natList (List.range q)) 1 0 Bw :=
    StDC.var' rfl (rin.trans (by omega))
  have ym := StDC.call (StDC.mk2 (get (i := 1) rfl (by omega)) r2 wyr (by omega))
    (itcs_bal_table hm he hb Y y₀ hY) (ly.trans (by omega))
  let env := [.list [rcCertIn X x₀, rcCertIn Y y₀], natList (List.range q),
      encFun (itcsBal X x₀), encFun (itcsBal Y y₀)]
  have x2 : StDC Pg env (.var 2) (encFun (itcsBal X x₀)) 1 0 Bw := StDC.var' rfl (lx.trans (by omega))
  have y3 : StDC Pg env (.var 3) (encFun (itcsBal Y y₀)) 1 0 Bw := StDC.var' rfl (ly.trans (by omega))
  have pc := StDC.call (StDC.mk2 x2 y3 wpart (by omega)) (itcs_bal_prog hi X Y x₀ y₀ lx ly E) wov
  have body := StDC.letE rg (StDC.letE xm (StDC.letE ym pc wov) wov) wov
  clear budget pow1 pow2 cx cy lx ly rin winput wxr wyr wpart wov get tabw table qlen rg r1 xm r2 ym x2 y3 pc
  exact StDC.funDet hf body (by unfold itcsBalPartC; dsimp only [Bw]; omega)

/-- The balanced-item cost is polynomial at the round's parameters. -/
theorem itcs_bal_part_pbu : PBU fun _ W _ => itcsBalPartC (2 * W + 3) (2 * (2 * W + 3) ^ 64) := by
  simp only [itcsBalPartC, itcsBalPartW, itcsBalM, itcsBalTC, itcsBalW, itCfObjB, itciFC, mapK]
  norm_poly

end GI.Impl
