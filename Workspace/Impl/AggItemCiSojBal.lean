module

public import Workspace.Impl.AggItemCiSojMath
public import Workspace.Impl.AggItemCiCfgS
public import Workspace.Impl.AggItemCfObW

@[expose] public section

/-!
# Constructing the balanced vertex colors

The program reads one row of the pair-color table. Inside the fiber it returns
`2 * col x₀ a + 1`. Outside the fiber it returns zero. Thus omitted labels keep
one separate color, as in `PairCfg.balPart`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- On `[rcCertIn X x₀, a]`, the balanced vertex color at `a`. -/
def itcsBalB (fb : ℕ) : Expr :=
  .ite (.call fb (.var 0))
    (.arith .add (.arith .mul (.nat 2)
      (.get (.get (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 2))) (arg 1))) (.nat 1))
    (.nat 0)

/-- Each balanced vertex color is at most twice the input palette bound plus one. -/
theorem itcs_bal_le {X : PairCfg q} {x₀ : Fin q} {B : ℕ}
    (h : itCfColsLe (.pair X x₀) B) (a : Fin q) : itcsBal X x₀ a ≤ 2 * B + 1 := by
  classical
  change (if a ∈ X.fiber then 2 * X.col x₀ a + 1 else 0) ≤ _
  split_ifs
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (h.1 x₀ a)) 1
  · exact Nat.zero_le _

/-- The balanced color body, with an explicit input palette bound. -/
theorem itcs_balB_spec {Pg : Program} {f fb : ℕ}
    (hf : Pg.funs[f]? = some (itcsBalB fb)) (hfb : Pg.funs[fb]? = some itcqFbT)
    (X : PairCfg q) (x₀ a : Fin q) {B W : ℕ}
    (hcol : itCfColsLe (.pair X x₀) B)
    (hW : (Val.list [rcCertIn X x₀, .nat a]).wt ≤ W) (hB : 2 * B + 5 ≤ W)
    (h5 : 5 ≤ W) :
    FunDet Pg f (.list [rcCertIn X x₀, .nat a]) (.nat (itcsBal X x₀ a))
      (100 * (W + 1)) := by
  classical
  have h0 : (rcCertIn X x₀).wt ≤ W := (st_wt_mem (by simp)).trans hW
  have ht : (rcColVal X).wt ≤ W := (st_wt_mem (by simp : rcColVal X ∈
    [rcColVal X, .nat X.j, .nat x₀])).trans h0
  have hx : (Val.nat x₀).wt ≤ W := (st_wt_mem (by simp : Val.nat x₀ ∈
    [rcColVal X, .nat X.j, .nat x₀])).trans h0
  have ha : (Val.nat a).wt ≤ W := (st_wt_mem (by simp)).trans hW
  have hr : (encFun (X.col x₀)).wt ≤ W :=
    (st_wt_mem (List.mem_of_getElem? (itcq_col_get X x₀))).trans ht
  have hv : (Val.nat (X.col x₀ a)).wt ≤ W :=
    (st_wt_mem (List.mem_of_getElem? (encFun_getElem? (X.col x₀) a))).trans hr
  have hc := itcq_fbT_spec hfb X x₀ a hW
  let env : List Val := [.list [rcCertIn X x₀, .nat a]]
  have g0 : StDC Pg env (arg 0) (rcCertIn X x₀) 3 0 W :=
    StDC.arg rfl hW (by omega) (by omega)
  have g1 : StDC Pg env (arg 1) (.nat a) 3 0 W :=
    StDC.arg rfl hW (by omega) (by omega)
  have gt := StDC.get g0 (StDC.nat 0 (by omega)) (v := rcColVal X) rfl ht
  have gx := StDC.get g0 (StDC.nat 2 (by omega)) (v := .nat x₀) rfl hx
  have gr := StDC.get gt gx (itcq_col_get X x₀) hr
  have gv := StDC.get gr g1 (encFun_getElem? (X.col x₀) a) hv
  have hp := StDC.arith' (StDC.nat 2 (by omega)) gv (op := .mul)
    (z := 2 * X.col x₀ a) rfl (by have := hcol.1 x₀ a; omega)
  have gs := StDC.arith' hp (StDC.nat 1 (by omega)) (op := .add)
    (z := 2 * X.col x₀ a + 1) rfl (by have := hcol.1 x₀ a; omega)
  have gc : StDC Pg env (.call fb (.var 0)) (boolVal (itcqFq X (.nat a))) 2
      (30 * (W + 1)) W :=
    (StDC.call (cb := 30 * (W + 1)) (StDC.var' (W := W) rfl hW) hc
      ((wt_boolVal_le _).trans (by omega))).mono le_rfl (by omega)
  have hfib : itcqFq X (.nat a) = decide (a ∈ X.fiber) := by
    simp [itcqFq, a.isLt, PairCfg.mem_fiber]
  rw [hfib] at gc
  have hres : (Val.nat (itcsBal X x₀ a)).wt ≤ W :=
    (wt_nat_le _).trans (by have := itcs_bal_le hcol a; omega)
  have body : StDC Pg env (itcsBalB fb) (.nat (itcsBal X x₀ a)) 50
      (30 * (W + 1)) W := by
    unfold itcsBalB
    refine (StDC.ite (nt := 30) (ne := 1) (Et := 0) (Ee := 0) gc ?_ ?_ hres).mono
      (by omega) (by omega)
    · intro hne
      have hin : a ∈ X.fiber := by simpa [boolVal] using hne
      simpa only [itcsBal, PairCfg.balPart, if_pos hin] using gs.mono (by omega) le_rfl
    · intro hz
      have hout : a ∉ X.fiber := by simpa [boolVal] using hz
      simpa only [itcsBal, PairCfg.balPart, if_neg hout] using StDC.nat (P := Pg)
        (env := env) 0 (by omega : 0 + 2 ≤ W)
  exact StDC.funDet hf body (by omega)

/-- A common weight bound for one entry call. -/
def itcsBalW (q B : ℕ) : ℕ := 2 * itCfObjB q B + 2 * q + 20

/-- The input and the small arithmetic intermediates fit this bound. -/
theorem itcs_bal_weight (X : PairCfg q) (x₀ a : Fin q) {B : ℕ}
    (hcol : itCfColsLe (.pair X x₀) B) :
    (Val.list [rcCertIn X x₀, .nat a]).wt ≤ itcsBalW q B ∧
      2 * B + 5 ≤ itcsBalW q B ∧ 5 ≤ itcsBalW q B := by
  have hc : (rcCertIn X x₀).wt ≤ itCfObjB q B :=
    (st_wt_mem (by simp : rcCertIn X x₀ ∈ [.nat 2, rcCertIn X x₀])).trans
      (itCfOutV_wt_le hcol)
  have hin := wt_list2_le (rcCertIn X x₀) (.nat a)
  have ha := wt_nat_le (a : ℕ)
  have hqa := a.isLt
  have hb : 20 * (B + 5) ≤ itCfObjB q B := by
    unfold itCfObjB
    calc 20 * (B + 5) = (20 * 1) * (B + 5) := by omega
      _ ≤ (20 * (q + 1) ^ 2) * (B + 5) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega)))
  unfold itcsBalW
  exact ⟨by omega, by omega, by omega⟩

/-- The cost of the full balanced vertex-color table. -/
def itcsBalTC (q B : ℕ) : ℕ :=
  q * (100 * (itcsBalW q B + 1)) + mapK * (q + 1) *
    (2 * itCfObjB q B + 10 * (q + 1) ^ 2 + 10 + (q * (2 * (2 * B + 1) + 5) + 4) + 1)

/-- The table is a deterministic map over the old label set. -/
theorem itcs_bal_table {Pg : Program} {mp f fb : ℕ}
    (hmp : Pg.HasAt mp (mapFuns mp f))
    (hf : Pg.funs[f]? = some (itcsBalB fb)) (hfb : Pg.funs[fb]? = some itcqFbT)
    (X : PairCfg q) (x₀ : Fin q) {B : ℕ} (hcol : itCfColsLe (.pair X x₀) B) :
    FunDet Pg mp (.list [rcCertIn X x₀, natList (List.range q)])
      (encFun (itcsBal X x₀)) (itcsBalTC q B) := by
  rw [it_range_eq]
  let F : Val → Val := fun w => match w with
    | .nat a => if ha : a < q then .nat (itcsBal X x₀ ⟨a, ha⟩) else .nat 0
    | _ => .nat 0
  have hmap := map_det hmp (c := rcCertIn X x₀)
    (xs := (List.finRange q).map fun a => Val.nat a.val) (F := F)
    (B := 100 * (itcsBalW q B + 1)) (fun w hw => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
      have hw := itcs_bal_weight X x₀ a hcol
      simpa only [F, dif_pos a.isLt] using itcs_balB_spec hf hfb X x₀ a hcol hw.1 hw.2.1 hw.2.2)
  have he : ((List.finRange q).map (fun a => Val.nat a.val)).map F =
      (List.finRange q).map (fun a => Val.nat (itcsBal X x₀ a)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a _
    simp only [Function.comp_apply, F, dif_pos a.isLt]
  rw [he] at hmap
  refine hmap.mono ?_
  have hc : (rcCertIn X x₀).wt ≤ itCfObjB q B :=
    (st_wt_mem (by simp : rcCertIn X x₀ ∈ [.nat 2, rcCertIn X x₀])).trans
      (itCfOutV_wt_le hcol)
  have hr := it_range_wt (q := q)
  rw [it_range_eq] at hr
  have hin := wt_list2_le (rcCertIn X x₀)
    (.list ((List.finRange q).map fun a => Val.nat a.val))
  have hout := wt_encFun_le (itcsBal X x₀) (itcs_bal_le hcol)
  simp only [List.length_map, List.length_finRange]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  have hout' : (Val.list ((List.finRange q).map fun a => Val.nat (itcsBal X x₀ a))).wt ≤
      q * (2 * (2 * B + 1) + 5) + 4 := hout
  clear hout
  omega

end GI.Impl
