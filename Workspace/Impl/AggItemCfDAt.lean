module

public import Workspace.Impl.AggItemCfDRead

@[expose] public section

set_option maxHeartbeats 400000
set_option maxRecDepth 2000

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited
open GI.Machine (BinOp)

def itCfDAtQ : Expr := .get (arg 0) (.nat 2)
def itCfDAtSrc : Expr := .get (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 3))
def itCfDAtSearch (rb : ℕ) : Expr := mk2 (mk2 (.var 1) itCfDAtQ) (.call rb itCfDAtQ)

/-- Read the partition or the dominant-class pair skeleton at a prefix. -/
def itCfDAtF (vm ad fd rb bl tb : ℕ) : Expr :=
  .letE (.call vm (.var 0))
    (.ite (.call ad (itCfDAtSearch rb))
      (.letE (.get (.var 1) (.call fd (itCfDAtSearch rb)))
        (.letE (.call tb (mk2 (.var 0) itCfDAtQ))
          (mk2 (.nat 2) (mk3 (.var 3) (.var 2) itCfDAtSrc))))
      (.letE (.call bl (mk2 (.var 1) itCfDAtQ))
        (mk3 (.nat 1) (.var 2) (.var 1))))

private theorem itCfD_at_parts {P : Program} {dl tl : List ℕ} {q κ m B : ℕ}
    (hA : (Val.list [stDA dl tl q κ, .nat m]).wt ≤ B) (hq : q ≤ B) (hk : κ ≤ B)
    (hkl : κ < tl.length) (rest : List Val) :
    StDC P (.list [stDA dl tl q κ, .nat m] :: rest) (.var 0)
        (.list [stDA dl tl q κ, .nat m]) 1 0 (100 * (B + 1)) ∧
    StDC P (.list [stDA dl tl q κ, .nat m] :: rest) (arg 0)
        (stDA dl tl q κ) 3 0 (100 * (B + 1)) ∧
    StDC P (.list [stDA dl tl q κ, .nat m] :: rest) itCfDAtQ
        (.nat q) 5 0 (100 * (B + 1)) ∧
    StDC P (.list [stDA dl tl q κ, .nat m] :: rest) itCfDAtSrc
        (.nat (tl.getD κ 0)) 11 0 (100 * (B + 1)) := by
  set W := 100 * (B + 1)
  have wA : (stDA dl tl q κ).wt < (Val.list [stDA dl tl q κ, .nat m]).wt :=
    wt_le_wt_list (by simp)
  have wtl : (natList tl).wt < (stDA dl tl q κ).wt := wt_stDA_ge.2.2.2.1
  have wq := wt_nat_le q
  have wk := wt_nat_le κ
  have wsrc : (Val.nat (tl.getD κ 0)).wt < (natList tl).wt := by
    rw [List.getD_eq_getElem _ _ hkl]
    exact wt_le_wt_list (List.mem_map.2 ⟨tl[κ], List.getElem_mem hkl, rfl⟩)
  have hw : 5 ≤ W := by dsimp [W]; omega
  have gi : StDC P (.list [stDA dl tl q κ, .nat m] :: rest) (.var 0)
      (.list [stDA dl tl q κ, .nat m]) 1 0 W := StDC.var' rfl (by dsimp [W]; omega)
  have ga : StDC P (.list [stDA dl tl q κ, .nat m] :: rest) (arg 0)
      (stDA dl tl q κ) 3 0 W := StDC.arg rfl (by dsimp [W]; omega) (by omega) (by dsimp [W]; omega)
  have gq := StDC.get (vs := [natList dl, natList tl, .nat q, .nat κ]) (v := .nat q)
    ga (StDC.nat 2 (by omega)) rfl (by dsimp [W]; omega)
  have gtl := StDC.get (vs := [natList dl, natList tl, .nat q, .nat κ]) (v := natList tl)
    ga (StDC.nat 1 (by omega)) rfl (by dsimp [W]; omega)
  have gk := StDC.get (vs := [natList dl, natList tl, .nat q, .nat κ]) (v := .nat κ)
    ga (StDC.nat 3 (by omega)) rfl (by dsimp [W]; omega)
  have gsrc := StDC.get gtl gk (v := .nat (tl.getD κ 0)) (by
    rw [List.getElem?_map, List.getElem?_eq_getElem hkl, List.getD_eq_getElem _ _ hkl]; rfl)
    (by dsimp [W]; omega)
  exact ⟨gi, ga, gq, gsrc⟩

/-- Assemble the readout from callees with one common cost bound. -/
theorem itCfD_at_calls {P : Program} {f vm ad fd rb bl tb B : ℕ}
    (hf : P.funs[f]? = some (itCfDAtF vm ad fd rb bl tb))
    (dl tl : List ℕ) (q κ m : ℕ) (hkl : κ < tl.length)
    (hA : (Val.list [stDA dl tl q κ, .nat m]).wt ≤ B) (hq : q ≤ B) (hk : κ ≤ B)
    (hvm : FunDet P vm (.list [stDA dl tl q κ, .nat m])
      (natList (stDV dl tl q κ m)) B)
    (hrb : FunDet P rb (.nat q) (natList (List.range q)) B)
    (had : FunDet P ad
      (.list [.list [natList (stDV dl tl q κ m), .nat q], natList (List.range q)])
      (boolVal ((List.range q).any (stDDom (stDV dl tl q κ m) q))) B)
    (hfd : FunDet P fd
      (.list [.list [natList (stDV dl tl q κ m), .nat q], natList (List.range q)])
      (.nat (stDZ (stDV dl tl q κ m) q)) B)
    (hbl : FunDet P bl (.list [natList (stDV dl tl q κ m), .nat q])
      (itCfDBlocks (stDV dl tl q κ m) q) B)
    (htb : FunDet P tb (.list [.list [stDA dl tl q κ, .nat m], .nat q])
      (itCfDTable dl tl q κ m) B) :
    FunDet P f (.list [stDA dl tl q κ, .nat m]) (itCfDAt dl tl q κ m)
      (10 ^ 6 * (B + 1)) := by
  set A := stDA dl tl q κ
  set inp : Val := .list [A, .nat m]
  set V := stDV dl tl q κ m
  set z := stDZ V q
  set W := 100 * (B + 1)
  have wV := hvm.wt_lt
  have wrng := hrb.wt_lt
  have wbl := hbl.wt_lt
  have wtb := htb.wt_lt
  change (natList V).wt < B at wV
  change (itCfDBlocks V q).wt < B at wbl
  have hVl : V.length = q := stDV_length dl tl q κ m
  have wA : A.wt < inp.wt := wt_le_wt_list (by simp [inp])
  have wtl : (natList tl).wt < A.wt := wt_stDA_ge.2.2.2.1
  have wq := wt_nat_le q
  have wk := wt_nat_le κ
  have wsrc : (Val.nat (tl.getD κ 0)).wt < (natList tl).wt := by
    rw [List.getD_eq_getElem _ _ hkl]
    exact wt_le_wt_list (List.mem_map.2 ⟨tl[κ], List.getElem_mem hkl, rfl⟩)
  have wcv := wt_list2_le (natList V) (.nat q)
  have wsearch := wt_list2_le (.list [natList V, .nat q]) (natList (List.range q))
  have wtablearg := wt_list2_le inp (.nat q)
  have hW5 : 5 ≤ W := by dsimp [W]; omega
  have parts := itCfD_at_parts (P := P) hA hq hk hkl
  have gi (rest : List Val) : StDC P (inp :: rest) (.var 0) inp 1 0 W := (parts rest).1
  have ga (rest : List Val) : StDC P (inp :: rest) (arg 0) A 3 0 W := (parts rest).2.1
  have gq (rest : List Val) : StDC P (inp :: rest) itCfDAtQ (.nat q) 5 0 W := (parts rest).2.2.1
  have gsrc (rest : List Val) : StDC P (inp :: rest) itCfDAtSrc (.nat (tl.getD κ 0)) 11 0 W :=
    (parts rest).2.2.2
  have gv (rest : List Val) : StDC P (inp :: natList V :: rest) (.var 1) (natList V) 1 0 W :=
    StDC.var' rfl (by dsimp [W]; omega)
  have gsearch (rest : List Val) : StDC P (inp :: natList V :: rest) (itCfDAtSearch rb)
      (.list [.list [natList V, .nat q], natList (List.range q)]) 18 B W := by
    exact (StDC.mk2 (StDC.mk2 (gv rest) (gq (natList V :: rest))
      (by dsimp [W]; omega) (by omega))
      (StDC.call (gq (natList V :: rest)) hrb (by dsimp [W]; omega))
      (by dsimp [W]; omega) (by omega)).mono (by omega) (by omega)
  have gvm := StDC.call (gi []) hvm (by dsimp [W]; omega)
  have gany := StDC.call (gsearch []) had
    (by have := wt_boolVal_le ((List.range q).any (stDDom V q)); dsimp [W]; omega)
  unfold itCfDAt
  change FunDet P f inp (if stDBal V q then _ else _) _
  by_cases haany : (List.range q).any (stDDom V q) = true
  · have hz : z < q := by
      obtain ⟨v, hv, hp⟩ := List.any_eq_true.1 haany
      have hh := List.findIdx_lt_length_of_exists (p := stDDom V q)
        (xs := List.range q) ⟨v, hv, hp⟩
      simpa [z, stDZ] using hh
    have jget : (V.map Val.nat)[z]? = some (.nat (V.getD z 0)) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega),
        List.getD_eq_getElem _ _ (by omega)]; rfl
    have wj : (Val.nat (V.getD z 0)).wt < (natList V).wt :=
      wt_le_wt_list (List.mem_of_getElem? jget)
    have wz := wt_nat_le z
    have gfind := StDC.call (gsearch []) hfd (by dsimp [W]; omega)
    have gj := StDC.get (gv []) gfind jget (by dsimp [W]; omega)
    have gtable := StDC.call (StDC.mk2 (gi [natList V, .nat (V.getD z 0)])
      (gq [natList V, .nat (V.getD z 0)]) (by dsimp [W]; change inp.wt ≤ B at hA; omega)
      (by omega)) htb (by dsimp [W]; omega)
    have vj : StDC P [inp, natList V, .nat (V.getD z 0), itCfDTable dl tl q κ m]
        (.var 2) (.nat (V.getD z 0)) 1 0 W := StDC.var' rfl (by dsimp [W]; omega)
    have vt : StDC P [inp, natList V, .nat (V.getD z 0), itCfDTable dl tl q κ m]
        (.var 3) (itCfDTable dl tl q κ m) 1 0 W := StDC.var' rfl (by dsimp [W]; omega)
    have wo3 := wt_list3_le (itCfDTable dl tl q κ m) (.nat (V.getD z 0)) (.nat (tl.getD κ 0))
    have wo2 := wt_list2_le (.nat 2)
      (.list [itCfDTable dl tl q κ m, .nat (V.getD z 0), .nat (tl.getD κ 0)])
    have wn2 := wt_nat_le 2
    have wow : (Val.list [.nat 2,
        .list [itCfDTable dl tl q κ m, .nat (V.getD z 0), .nat (tl.getD κ 0)]]).wt ≤ W := by
      dsimp [W]; change inp.wt ≤ B at hA; omega
    have gout := StDC.mk2 (StDC.nat 2 (by omega))
      (StDC.mk3 vt vj (gsrc [natList V, .nat (V.getD z 0), itCfDTable dl tl q κ m])
        (by dsimp [W]; change inp.wt ≤ B at hA; omega) (by omega)) wow (by omega)
    have gp := StDC.letE gj (StDC.letE gtable gout wow) wow
    have hb : stDBal V q = false := by simp [stDBal, haany]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    have gx : ((List.range q).any (stDDom V q)).toNat ≠ 0 := by rw [haany]; decide
    have gcond := StDC.ite (e := .letE (.call bl (mk2 (.var 1) itCfDAtQ))
      (mk3 (.nat 1) (.var 2) (.var 1))) (ne := 0) (Ee := 0) gany
      (fun _ => gp) (fun h => absurd h gx) wow
    exact StDC.funDet hf (StDC.letE gvm gcond wow) (by dsimp [W]; omega)
  · have hbany : (List.range q).any (stDDom V q) = false := Bool.eq_false_iff.2 haany
    have hb : stDBal V q = true := by simp [stDBal, hbany]
    simp only [hb, ↓reduceIte]
    have gblocks := StDC.call (StDC.mk2 (gv []) (gq [natList V])
      (by dsimp [W]; omega) (by omega)) hbl (by dsimp [W]; omega)
    have vb : StDC P [inp, natList V, itCfDBlocks V q] (.var 2) (itCfDBlocks V q) 1 0 W :=
      StDC.var' rfl (by dsimp [W]; omega)
    have wo := wt_list3_le (.nat 1) (itCfDBlocks V q) (natList V)
    have wn1 := wt_nat_le 1
    have wow : (Val.list [.nat 1, itCfDBlocks V q, natList V]).wt ≤ W := by dsimp [W]; omega
    have gout := StDC.mk3 (StDC.nat 1 (by omega)) vb (gv [itCfDBlocks V q]) wow (by omega)
    have gp := StDC.letE gblocks gout wow
    have gx : ((List.range q).any (stDDom V q)).toNat = 0 := by rw [hbany]; rfl
    have gcond := StDC.ite (t := .letE (.get (.var 1) (.call fd (itCfDAtSearch rb)))
      (.letE (.call tb (mk2 (.var 0) itCfDAtQ))
        (mk2 (.nat 2) (mk3 (.var 3) (.var 2) itCfDAtSrc)))) (nt := 0) (Et := 0) gany
      (fun h => absurd gx h) (fun _ => gp) wow
    exact StDC.funDet hf (StDC.letE gvm gcond wow) (by dsimp [W]; omega)

end GI.Impl
