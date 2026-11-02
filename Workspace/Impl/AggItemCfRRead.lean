import Workspace.Impl.AggItemCfRTable

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

/-- Read the table and the source vertex after the degree test succeeds. -/
def itCfRReadT (tb ce : ℕ) : Expr :=
  .letE (.get (arg 2) (.arith .sub (arg 3) (.nat 1)))
    (.letE (.call tb (mk2 (arg 1) (arg 0)))
      (mk2 (.nat 2) (mk3 (.var 2)
        (.call ce (mk2 (mk3 (arg 1) (arg 0) (.var 1)) (.var 1))) (.var 1))))

/-- On `[q,table,t,d]`, return the orbital object at degree `d`. -/
def itCfRReadF (tb ce : ℕ) : Expr :=
  .ite (.arith .lt (arg 3) (.length (arg 2))) (itCfRReadT tb ce)
    (.snoc .nil (.nat 0))

/-- Assemble the object after the successful degree test. The table and
cell programs are parameters so that this proof uses one free cost bound. -/
theorem itCfR_readT_spec {P : Program} {tb ce : ℕ} (dl tl : List ℕ) (q d : ℕ)
    (hd : d < tl.length) {B : ℕ} (hdw : (natList dl).wt ≤ B)
    (htw : (natList tl).wt ≤ B) (hq : q ≤ B) (hdu : d ≤ B)
    (hu : tl.getD (d - 1) 0 < q)
    (htb : FunDet P tb (.list [natList dl, .nat q]) (itCfRTable dl q) B)
    (hce : FunDet P ce
      (.list [.list [natList dl, .nat q, .nat (tl.getD (d - 1) 0)],
        .nat (tl.getD (d - 1) 0)])
      (.nat (itCfRColor dl q (tl.getD (d - 1) 0) (tl.getD (d - 1) 0))) B) :
    Det P [.list [.nat q, natList dl, natList tl, .nat d]] (itCfRReadT tb ce)
      (itCfROut dl tl q d) (10000 * (B + 1)) := by
  set u := tl.getD (d - 1) 0
  set inp : Val := .list [.nat q, natList dl, natList tl, .nat d]
  set W := 100 * (B + 1)
  have hwq := wt_nat_le q
  have hwd := wt_nat_le d
  have hwu := wt_nat_le u
  have ht := htb.wt_lt
  have hc := hce.wt_lt
  have hi := wt_list4_le (.nat q) (natList dl) (natList tl) (.nat d)
  have htabarg := wt_list2_le (natList dl) (.nat q)
  have hcellctx := wt_list3_le (natList dl) (.nat q) (.nat u)
  have hcellarg := wt_list2_le (.list [natList dl, .nat q, .nat u]) (.nat u)
  have hout3 := wt_list3_le (itCfRTable dl q) (.nat (itCfRColor dl q u u)) (.nat u)
  have hout2 := wt_list2_le (.nat 2)
    (.list [itCfRTable dl q, .nat (itCfRColor dl q u u), .nat u])
  have hn2 := wt_nat_le 2
  change (Val.nat (itCfRColor dl q u u)).wt < B at hc
  have hinpw : inp.wt ≤ W := by dsimp [inp, W]; omega
  have hW5 : 5 ≤ W := by dsimp [W]; omega
  have houtw : (Val.list [.nat 2,
      .list [itCfRTable dl q, .nat (itCfRColor dl q u u), .nat u]]).wt ≤ W := by
    dsimp [W]; omega
  have gq (rest : List Val) : StDC P (inp :: rest) (arg 0) (.nat q) 3 0 W :=
    StDC.arg rfl hinpw (by omega) (by dsimp [W]; omega)
  have gdl (rest : List Val) : StDC P (inp :: rest) (arg 1) (natList dl) 3 0 W :=
    StDC.arg rfl hinpw (by omega) (by dsimp [W]; omega)
  have gtl : StDC P [inp] (arg 2) (natList tl) 3 0 W :=
    StDC.arg rfl hinpw (by omega) (by dsimp [W]; omega)
  have gd : StDC P [inp] (arg 3) (.nat d) 3 0 W :=
    StDC.arg rfl hinpw (by omega) (by dsimp [W]; omega)
  have hd' : d - 1 < tl.length := by omega
  have gu := StDC.get gtl
    (StDC.arith' gd (StDC.nat 1 (by omega)) (op := .sub) (z := d - 1) rfl
      (by dsimp [W]; omega))
    (v := .nat u) (by
      rw [List.getElem?_map, List.getElem?_eq_getElem hd']
      simp only [u, List.getD_eq_getElem _ _ hd', Option.map_some])
    (by dsimp [W]; omega)
  have gt := StDC.call (StDC.mk2 (gdl [.nat u]) (gq [.nat u])
    (by dsimp [W]; omega) (by omega)) htb (by dsimp [W]; omega)
  have gv : StDC P [inp, .nat u, itCfRTable dl q] (.var 1) (.nat u) 1 0 W :=
    StDC.var' rfl (by dsimp [W]; omega)
  have gtab : StDC P [inp, .nat u, itCfRTable dl q] (.var 2) (itCfRTable dl q) 1 0 W :=
    StDC.var' rfl (by dsimp [W]; omega)
  have gcolor := StDC.call (StDC.mk2
    (StDC.mk3 (gdl [.nat u, itCfRTable dl q]) (gq [.nat u, itCfRTable dl q]) gv
      (by dsimp [W]; omega) (by omega)) gv (by dsimp [W]; omega) (by omega)) hce
    (by dsimp [W]; omega)
  have gout := StDC.mk2 (StDC.nat 2 (by omega))
    (StDC.mk3 gtab gcolor gv (by dsimp [W]; omega) (by omega)) houtw (by omega)
  have gbody := StDC.letE gu (StDC.letE gt gout houtw) houtw
  have he : itCfROut dl tl q d = .list [.nat 2,
      .list [itCfRTable dl q, .nat (itCfRColor dl q u u), .nat u]] := by
    simp only [itCfROut, if_pos hd]; rfl
  rw [he]
  exact gbody.det.mono (by dsimp [W]; omega)

/-- The orbital table reader allows arbitrary numeric colors. -/
theorem itCfR_read_spec {P : Program} {f tb mb rb rw rm ce : ℕ}
    (hf : P.funs[f]? = some (itCfRReadF tb ce))
    (htb : P.funs[tb]? = some (itCfRTableF mb rb))
    (hmb : P.HasAt mb (mapFuns mb rw)) (hrb : P.HasAt rb (rangeFuns rb))
    (hrw : P.funs[rw]? = some (itCfRRowF rm rb))
    (hrm : P.HasAt rm (mapFuns rm ce)) (hce : P.funs[ce]? = some itCfRCellF)
    (dl tl : List ℕ) (q d : ℕ) (hlen : dl.length = q * q)
    (htl : ∀ u ∈ tl, u < q) {N : ℕ} (hdw : (natList dl).wt ≤ N)
    (htw : (natList tl).wt ≤ N) (hqw : q ≤ N) (hd : d ≤ N) :
    FunDet P f (.list [.nat q, natList dl, natList tl, .nat d]) (itCfROut dl tl q d)
      (10 ^ 16 * (N + 1) ^ 4) := by
  have hp : N + 1 ≤ (N + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have h1 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  set inp : Val := .list [.nat q, natList dl, natList tl, .nat d]
  have hi := wt_list4_le (.nat q) (natList dl) (natList tl) (.nat d)
  have hwq := wt_nat_le q
  have hwd := wt_nat_le d
  have hln : tl.length < (natList tl).wt := by
    have := length_lt_wt_list (tl.map Val.nat); simpa [natList] using this
  have gd := Det.arg' (P := P) (vs := [.nat q, natList dl, natList tl, .nat d])
    (rest := []) (j := 3) rfl
  have gl := Det.length (Det.arg' (P := P) (vs := [.nat q, natList dl, natList tl, .nat d])
    (rest := []) (j := 2) rfl)
  simp only [List.length_map] at gl
  have gc := Det.arith gd gl (op := .lt)
  have hwb := wt_nat_le (BinOp.eval .lt d tl.length)
  have hble : BinOp.eval .lt d tl.length ≤ 1 := by
    simp only [BinOp.eval]; split_ifs <;> omega
  have hwzero := wt_nat_le 0
  simp only [BinOp.eval] at hwb hble
  by_cases hdt : d < tl.length
  · have hu : tl.getD (d - 1) 0 < q := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact htl _ (List.getElem_mem _)
    set B := 10 ^ 10 * (N + 1) ^ 4
    have hB : N ≤ B := by dsimp [B]; omega
    have ht := itCfR_table_spec htb hmb hrb hrw hrm hce dl q hlen hdw hqw
    have hc : FunDet P ce
        (.list [.list [natList dl, .nat q, .nat (tl.getD (d - 1) 0)],
          .nat (tl.getD (d - 1) 0)])
        (.nat (itCfRColor dl q (tl.getD (d - 1) 0) (tl.getD (d - 1) 0))) B :=
      (itCfR_cell_spec hce dl q _ _ hlen hu hu).mono (by dsimp [B]; omega)
    have gt := itCfR_readT_spec dl tl q d hdt (hdw.trans hB) (htw.trans hB)
      (hqw.trans hB) (hd.trans hB) hu ht hc
    have hx : BinOp.eval .lt d tl.length ≠ 0 := by simp [BinOp.eval, hdt]
    exact FunDet.intro hf ((Det.ite_pos gc hx gt).mono (by
      have ho := gt.wt_lt
      change (itCfROut dl tl q d).wt < 10000 * (B + 1) at ho
      dsimp [inp, B] at *
      omega))
  · have hx : BinOp.eval .lt d tl.length = 0 := by simp [BinOp.eval, hdt]
    rw [hx] at gc
    have gn : Det P [inp] (.snoc .nil (.nat 0)) (.list [.nat 0]) 20 :=
      (Det.snoc Det.nil (Det.nat 0)).mono (by decide)
    have he : itCfROut dl tl q d = .list [.nat 0] := by simp [itCfROut, hdt]
    rw [he]
    exact FunDet.intro hf ((Det.ite_zero gc gn).mono (by
      have hw0 : (Val.list [Val.nat 0]).wt = 9 := by decide
      rw [hw0]
      dsimp [inp] at *
      omega))

end GI.Impl
