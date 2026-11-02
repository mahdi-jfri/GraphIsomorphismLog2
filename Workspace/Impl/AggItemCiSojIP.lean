import Workspace.Impl.AggItemCiSojMA
import Workspace.Impl.AggItemCiSojIM
import Workspace.Impl.AggItemCiSojWt

/-!
# The complete imprimitive partition program

Construct source and target component labels, check that every target interior
block has at least two points, and apply Case 1's block-labeling program. A failed
target check returns the empty list, as proved in `itcs_imp_reject`.
-/

set_option maxRecDepth 2048

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- On `[rcCertIn X x₀, rcCertIn Y y₀, v]`, the component partition item. -/
def itcsImpPartF (rng comp mn part : ℕ) : Expr :=
  let q := Expr.length (.get (arg 0) (.nat 0))
  let cp (i : ℕ) := Expr.call comp (mk4 (.get (arg i) (.nat 0))
    (.get (arg i) (.nat 1)) (arg 2) q)
  .letE (.call rng q)
    (.letE (cp 0) (.letE (cp 1)
      (.letE (.call mn (mk2 (mk2 (.var 3) (arg 1)) (.var 1)))
        (.ite (.var 4) (.call part (mk2 (.var 2) (.var 3))) .nil))))

/-- Common budget including Case 1's deterministic result. -/
def itcsImpPartW (q B : ℕ) : ℕ :=
  1000 * (itCfObjB q B + itcsCompW q B + itC1C q + (q + 1) ^ 2 + B + q + 10)

/-- The total cost of the literal component-partition item. -/
def itcsImpPartC (q B : ℕ) : ℕ :=
  150 * (itcsImpPartW q B + 1) + 7000 * (q + 1) ^ 3 +
    2 * itcsCompTotal q B + itcsMinC q B + itC1C q

open Classical in
set_option maxHeartbeats 500000 in
/-- Both component tables and every target-check callback are actual programs. -/
theorem itcs_imp_part_prog {Pg : Program} {Ii : itcsCompIdx} {f mn mt fb B : ℕ}
    (hi : itcsCompOk Pg Ii)
    (hf : Pg.funs[f]? = some (itcsImpPartF Ii.c1.rng Ii.f mn Ii.c1.f))
    (hm : Pg.HasAt mn (allFuns mn mt))
    (ht : Pg.funs[mt]? = some (itcsMinF fb Ii.c1.sz))
    (hb : Pg.funs[fb]? = some itcqFbT)
    (X Y : PairCfg q) (x₀ y₀ : Fin q) (v : ℕ)
    (hX : itCfColsLe (.pair X x₀) B) (hY : itCfColsLe (.pair Y y₀) B) (hv : v ≤ B)
    (hex : ∃ a, 2 ≤ (X.comp v a).card) (E : Subgroup (alternatingGroup (Fin q))) :
    ∃ (a : Fin q) (ha : itcsLab X v a ≠ a),
      FunDet Pg f (.list [rcCertIn X x₀, rcCertIn Y y₀, .nat v])
        (if ∀ b ∈ Y.fiber, 2 ≤ (Y.comp v b).card then
          itciOV (itcOsM (itcs_component_labels X v) (itcsLab Y v) ha E
            (itcMs (itcsLab X v) a)) else .list []) (itcsImpPartC q B) := by
  obtain ⟨a, ha, hpart⟩ := itcs_component_prog hi.c1 X Y v hex E
  refine ⟨a, ha, ?_⟩
  let Bw := itcsImpPartW q B
  let inp : Val := .list [rcCertIn X x₀, rcCertIn Y y₀, .nat v]
  let LX := encFun (itcsLab X v)
  let LY := encFun (itcsLab Y v)
  let Rq := natList (List.range q)
  let ov := itciOV (itcOsM (itcs_component_labels X v) (itcsLab Y v) ha E (itcMs (itcsLab X v) a))
  have budget : 20 * itCfObjB q B + 20 * itcsCompW q B + 20 * itC1C q +
      100 * (q + 1) ^ 2 + 20 * B + 20 * q + 1000 ≤ Bw := by
    dsimp only [Bw]; unfold itcsImpPartW; omega
  have cx : (rcCertIn X x₀).wt ≤ itCfObjB q B :=
    (st_wt_mem (by simp : rcCertIn X x₀ ∈ [.nat 2, rcCertIn X x₀])).trans (itCfOutV_wt_le hX)
  have cy : (rcCertIn Y y₀).wt ≤ itCfObjB q B :=
    (st_wt_mem (by simp : rcCertIn Y y₀ ∈ [.nat 2, rcCertIn Y y₀])).trans (itCfOutV_wt_le hY)
  have lx : LX.wt ≤ 5 * (q + 1) ^ 2 := it_encFun_wt _ (fun b => (itcs_lab_lt X v b).le)
  have ly : LY.wt ≤ 5 * (q + 1) ^ 2 := it_encFun_wt _ (fun b => (itcs_lab_lt Y v b).le)
  have rr : Rq.wt ≤ 4 * (q + 1) ^ 2 := wt_range_le q
  have vv := wt_nat_le v
  have wi : inp.wt ≤ Bw := by
    have h := wt_list3_le (rcCertIn X x₀) (rcCertIn Y y₀) (.nat v)
    dsimp only [inp]; omega
  have wp : (Val.list [LX, LY]).wt ≤ Bw := by have h := wt_list2_le LX LY; omega
  have wmctx := wt_list2_le LY (rcCertIn Y y₀)
  have wm : (Val.list [.list [LY, rcCertIn Y y₀], Rq]).wt ≤ Bw := by
    have h := wt_list2_le (.list [LY, rcCertIn Y y₀]) Rq
    omega
  have wo : ov.wt ≤ Bw := (itcs_det_weight hpart).trans (by omega)
  have wr : (if ∀ b ∈ Y.fiber, 2 ≤ (Y.comp v b).card then ov else Val.list []).wt ≤ Bw := by
    split_ifs
    · exact wo
    · simp only [wt_list_nil]; omega
  have get {rest : List Val} {i : ℕ} {w : Val}
      (hh : [rcCertIn X x₀, rcCertIn Y y₀, .nat v][i]? = some w) (hii : i + 2 ≤ Bw) :
      StDC Pg (inp :: rest) (arg i) w 3 0 Bw :=
    StDC.arg hh wi hii ((st_wt_mem (List.mem_of_getElem? hh)).trans wi)
  have tx : (rcColVal X).wt ≤ Bw := (st_wt_mem (List.mem_cons_self ..)).trans (cx.trans (by omega))
  have ty : (rcColVal Y).wt ≤ Bw := (st_wt_mem (List.mem_cons_self ..)).trans (cy.trans (by omega))
  have jx : (Val.nat X.j).wt ≤ Bw := (st_wt_mem (by simp : Val.nat X.j ∈
    [rcColVal X, .nat X.j, .nat x₀])).trans (cx.trans (by omega))
  have jy : (Val.nat Y.j).wt ≤ Bw := (st_wt_mem (by simp : Val.nat Y.j ∈
    [rcColVal Y, .nat Y.j, .nat y₀])).trans (cy.trans (by omega))
  have tableX (rest : List Val) := StDC.get (get (rest := rest) (i := 0) rfl (by omega))
    (StDC.nat 0 (by omega)) rfl tx
  have tableY (rest : List Val) := StDC.get (get (rest := rest) (i := 1) rfl (by omega))
    (StDC.nat 0 (by omega)) rfl ty
  have qval (rest : List Val) : StDC Pg (inp :: rest)
      (.length (.get (arg 0) (.nat 0))) (.nat q) 6 0 Bw := by
    have h := StDC.length (tableX rest) (by simp only [List.length_map, List.length_finRange]; omega)
    simpa only [List.length_map, List.length_finRange] using h
  have rg := StDC.call (qval []) (range_det hi.c1.rng q) (rr.trans (by omega))
  have xc := StDC.call (StDC.mk4 (tableX [Rq])
    (StDC.get (get (rest := [Rq]) (i := 0) rfl (by omega)) (StDC.nat 1 (by omega)) rfl jx)
    (get (rest := [Rq]) (i := 2) rfl (by omega)) (qval [Rq])
    ((itcs_comp_weights X x₀ v hX hv).input.trans (by omega)) (by omega))
    (itcs_comp_prog hi X x₀ v hX hv) (lx.trans (by omega))
  have yc := StDC.call (StDC.mk4 (tableY [Rq, LX])
    (StDC.get (get (rest := [Rq, LX]) (i := 1) rfl (by omega)) (StDC.nat 1 (by omega)) rfl jy)
    (get (rest := [Rq, LX]) (i := 2) rfl (by omega)) (qval [Rq, LX])
    ((itcs_comp_weights Y y₀ v hY hv).input.trans (by omega)) (by omega))
    (itcs_comp_prog hi Y y₀ v hY hv) (ly.trans (by omega))
  let env : List Val := [inp, Rq, LX, LY]
  have y3 : StDC Pg env (.var 3) LY 1 0 Bw := StDC.var' rfl (ly.trans (by omega))
  have r1 : StDC Pg env (.var 1) Rq 1 0 Bw := StDC.var' rfl (rr.trans (by omega))
  have mc := StDC.call (StDC.mk2 (StDC.mk2 y3
    (get (rest := [Rq, LX, LY]) (i := 1) rfl (by omega)) (by omega) (by omega)) r1 wm (by omega))
    (itcs_min_prog hm ht hb hi.c1.sz hi.c1.cnt Y y₀ v hY)
    ((wt_boolVal_le _).trans (by omega))
  let test := decide (∀ b ∈ Y.fiber, 2 ≤ (Y.comp v b).card)
  have x2' : StDC Pg (env ++ [boolVal test]) (.var 2) LX 1 0 Bw := StDC.var' rfl (lx.trans (by omega))
  have y3' : StDC Pg (env ++ [boolVal test]) (.var 3) LY 1 0 Bw := StDC.var' rfl (ly.trans (by omega))
  have pc := StDC.call (StDC.mk2 x2' y3' wp (by omega)) hpart wo
  have tv : StDC Pg (env ++ [boolVal test]) (.var 4) (boolVal test) 1 0 Bw :=
    StDC.var' rfl ((wt_boolVal_le _).trans (by omega))
  have result : StDC Pg (env ++ [boolVal test])
      (.ite (.var 4) (.call Ii.c1.f (mk2 (.var 2) (.var 3))) .nil)
      (if ∀ b ∈ Y.fiber, 2 ≤ (Y.comp v b).card then ov else Val.list [])
      10 (itC1C q) Bw := by
    refine (StDC.ite (nt := 6) (ne := 1) (Et := itC1C q) (Ee := 0) tv ?_ ?_ wr).mono
      (by omega) (by omega)
    · intro hne
      have hmY : ∀ b ∈ Y.fiber, 2 ≤ (Y.comp v b).card := by
        by_contra hh
        have hz : test = false := by
          change decide (∀ b ∈ Y.fiber, 2 ≤ (Y.comp v b).card) = false
          exact decide_eq_false hh
        simp only [hz, Bool.toNat_false, ne_eq, not_true_eq_false] at hne
      rw [if_pos hmY]
      exact pc.mono (by omega) (by omega)
    · intro hz
      have hmY : ¬ ∀ b ∈ Y.fiber, 2 ≤ (Y.comp v b).card := by
        intro hh
        have ht : test = true := by
          change decide (∀ b ∈ Y.fiber, 2 ≤ (Y.comp v b).card) = true
          exact decide_eq_true hh
        simp only [ht, Bool.toNat_true] at hz
        omega
      rw [if_neg hmY]
      exact StDC.nil (by omega)

  have body := StDC.letE rg (StDC.letE xc (StDC.letE yc (StDC.letE mc result wr) wr) wr) wr
  clear budget cx cy lx ly rr vv wi wp wmctx wm wo wr get tx ty jx jy tableX tableY qval rg xc yc y3 r1 mc x2' y3' pc tv result
  exact StDC.funDet hf body (by unfold itcsImpPartC; dsimp only [Bw]; omega)

/-- Polynomial round cost of the full component partition item. -/
theorem itcs_imp_part_pbu : PBU fun _ W _ => itcsImpPartC (2 * W + 3) (2 * (2 * W + 3) ^ 64) := by
  simp only [itcsImpPartC, itcsImpPartW, itcsMinC, itcsMinW, itC1C, itcsCompTotal,
    itcsCompC, itcsSqMapC, itcsCompW, itCfObjB, itcsGenW, countK, mapK, orbitK, loopModK]
  norm_poly

end GI.Impl
