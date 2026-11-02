import Workspace.Impl.AggItemCiSojBP
import Workspace.Impl.AggItemCiSojAlign

/-!
# Constructing the two rectangle side colors

The balanced row colors already distinguish omitted labels. Compare them with
`2v_L+1` and `2v_R+1` to obtain the three colors used by the fixed alignment.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- The three-color side table read from the two raw row colors. -/
noncomputable def itcsSides (X : PairCfg q) (x₀ : Fin q) (vL vR : ℕ) : Fin q → ℕ :=
  itcsSide (X.fiber.filter fun a => X.col x₀ a = vL)
    (X.fiber.filter fun a => X.col x₀ a = vR)

/-- Equality with an interior row-color code includes membership in the fiber. -/
theorem itcs_bal_code (X : PairCfg q) (x₀ a : Fin q) (v : ℕ) :
    itcsBal X x₀ a = 2 * v + 1 ↔ a ∈ X.fiber ∧ X.col x₀ a = v := by
  classical
  change (if a ∈ X.fiber then 2 * X.col x₀ a + 1 else 0) = _ ↔ _
  by_cases ha : a ∈ X.fiber
  · simp only [ha, ↓reduceIte, true_and]
    omega
  · simp [ha]

/-- On `[[balanced row, vL, vR], a]`, the side color at `a`. -/
def itcsSideF : Expr :=
  let c := Expr.get (.get (arg 0) (.nat 0)) (arg 1)
  let val (i : ℕ) := Expr.arith .add (.arith .mul (.nat 2) (.get (arg 0) (.nat i))) (.nat 1)
  .ite (.arith .eq c (val 1)) (.nat 2) (.ite (.arith .eq c (val 2)) (.nat 1) (.nat 0))

/-- The fixed side-color callback. -/
theorem itcs_side_spec {Pg : Program} {f Bw : ℕ}
    (hf : Pg.funs[f]? = some itcsSideF) (X : PairCfg q) (x₀ a : Fin q) (vL vR : ℕ)
    (hin : (Val.list [.list [encFun (itcsBal X x₀), .nat vL, .nat vR], .nat a]).wt ≤ Bw)
    (hv : 2 * vL + 2 * vR + 10 ≤ Bw) :
    FunDet Pg f (.list [.list [encFun (itcsBal X x₀), .nat vL, .nat vR], .nat a])
      (.nat (itcsSides X x₀ vL vR a)) (100 * (Bw + 1)) := by
  classical
  let ctx : Val := .list [encFun (itcsBal X x₀), .nat vL, .nat vR]
  let env : List Val := [.list [ctx, .nat a]]
  have hctx : ctx.wt ≤ Bw := (st_wt_mem (by simp [ctx])).trans hin
  have get {i : ℕ} {w : Val}
      (hi : [encFun (itcsBal X x₀), .nat vL, .nat vR][i]? = some w) (hii : i + 2 ≤ Bw) :
      StDC Pg env (.get (arg 0) (.nat i)) w 5 0 Bw :=
    StDC.get (StDC.arg rfl hin (by omega) hctx) (StDC.nat i hii) hi
      ((st_wt_mem (List.mem_of_getElem? hi)).trans hctx)
  have tab := get (i := 0) rfl (by omega)
  have ai : StDC Pg env (arg 1) (.nat a) 3 0 Bw :=
    StDC.arg rfl hin (by omega) ((st_wt_mem (by simp)).trans hin)
  have cv := StDC.get tab ai (encFun_getElem? (itcsBal X x₀) a)
    ((st_wt_mem (List.mem_of_getElem? (encFun_getElem? (itcsBal X x₀) a))).trans
      ((st_wt_mem (List.mem_cons_self ..)).trans hctx))
  have code {i v : ℕ}
      (hi : [encFun (itcsBal X x₀), .nat vL, .nat vR][i]? = some (.nat v))
      (hii : i + 2 ≤ Bw) (hvv : 2 * v + 4 ≤ Bw) :=
    StDC.arith' (StDC.arith' (StDC.nat 2 (by omega)) (get hi hii) (op := .mul)
      (z := 2 * v) rfl (by omega)) (StDC.nat 1 (by omega)) (op := .add)
      (z := 2 * v + 1) rfl (by omega)
  have test {i v : ℕ}
      (hi : [encFun (itcsBal X x₀), .nat vL, .nat vR][i]? = some (.nat v))
      (hii : i + 2 ≤ Bw) (hvv : 2 * v + 4 ≤ Bw) :=
    StDC.arith' cv (code hi hii hvv) (op := .eq)
      (z := if itcsBal X x₀ a = 2 * v + 1 then 1 else 0) rfl (by split_ifs <;> omega)
  have tL := test (i := 1) (v := vL) rfl (by omega) (by omega)
  have tR := test (i := 2) (v := vR) rfl (by omega) (by omega)
  have out1 : StDC Pg env
      (.ite (.arith .eq (.get (.get (arg 0) (.nat 0)) (arg 1))
        (.arith .add (.arith .mul (.nat 2) (.get (arg 0) (.nat 2))) (.nat 1))) (.nat 1) (.nat 0))
      (.nat (if itcsBal X x₀ a = 2 * vR + 1 then 1 else 0)) 30 0 Bw := by
    by_cases hh : itcsBal X x₀ a = 2 * vR + 1
    · simp only [if_pos hh] at tR ⊢
      exact (StDC.ite (nt := 1) (ne := 1) (Et := 0) (Ee := 0) tR (fun _ => StDC.nat 1 (by omega))
        (fun h => by omega) ((wt_nat_le 1).trans (by omega))).mono (by omega) (by omega)
    · simp only [if_neg hh] at tR ⊢
      exact (StDC.ite (nt := 1) (ne := 1) (Et := 0) (Ee := 0) tR (fun h => by omega)
        (fun _ => StDC.nat 0 (by omega)) ((wt_nat_le 0).trans (by omega))).mono (by omega) (by omega)
  have he : itcsSides X x₀ vL vR a =
      if itcsBal X x₀ a = 2 * vL + 1 then 2 else
        if itcsBal X x₀ a = 2 * vR + 1 then 1 else 0 := by
    simp only [itcsSides, itcsSide, Finset.mem_filter, itcs_bal_code]
  have out : StDC Pg env itcsSideF (.nat (itcsSides X x₀ vL vR a)) 80 0 Bw := by
    rw [he]
    by_cases hh : itcsBal X x₀ a = 2 * vL + 1
    · simp only [if_pos hh] at tL ⊢
      exact (StDC.ite (nt := 1) (ne := 30) (Et := 0) (Ee := 0) tL (fun _ => StDC.nat 2 (by omega))
        (fun h => by omega) ((wt_nat_le 2).trans (by omega))).mono (by omega) (by omega)
    · simp only [if_neg hh] at tL ⊢
      exact (StDC.ite (nt := 1) (ne := 30) (Et := 0) (Ee := 0) tL (fun h => by omega)
        (fun _ => out1) (by split_ifs <;> exact (wt_nat_le _).trans (by omega))).mono (by omega) (by omega)
  exact StDC.funDet hf out (by omega)

/-- Every side color is at most two. -/
theorem itcs_sides_le (X : PairCfg q) (x₀ : Fin q) (vL vR : ℕ) (a : Fin q) :
    itcsSides X x₀ vL vR a ≤ 2 := by
  classical
  unfold itcsSides itcsSide
  split_ifs <;> omega

/-- Common weight budget for the side-color map. -/
def itcsSideW (q B : ℕ) : ℕ := 100 * (itcsBalM q B + B + q + 10)

/-- Cost of the full side-color table. -/
def itcsSideC (q B : ℕ) : ℕ :=
  q * (100 * (itcsSideW q B + 1)) + mapK * (q + 1) *
    (2 * itcsSideW q B + 22 * (q + 1) ^ 2)

/-- Tabulate both rectangle sides in the original label set. -/
theorem itcs_side_table {Pg : Program} {mp f B : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]? = some itcsSideF)
    (X : PairCfg q) (x₀ : Fin q) (vL vR : ℕ)
    (hcol : itCfColsLe (.pair X x₀) B) (hL : vL ≤ B) (hR : vR ≤ B) (hq : 2 ≤ q) :
    FunDet Pg mp (.list [.list [encFun (itcsBal X x₀), .nat vL, .nat vR],
      natList (List.range q)]) (encFun (itcsSides X x₀ vL vR)) (itcsSideC q B) := by
  have hl : (encFun (itcsBal X x₀)).wt ≤ itcsBalM q B := by
    have h := wt_encFun_le (itcsBal X x₀) (itcs_bal_le hcol)
    dsimp only [itcsBalM]
    convert h using 1 <;> ring
  have hvl := wt_nat_le vL
  have hvr := wt_nat_le vR
  have hctx := wt_list_map_le [encFun (itcsBal X x₀), .nat vL, .nat vR] id
    (W := itcsBalM q B + B + 4) (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> simp only [id_eq] <;> omega)
  simp only [List.map_id, List.length_cons, List.length_nil] at hctx
  have hw : (Val.list [encFun (itcsBal X x₀), .nat vL, .nat vR]).wt ≤ itcsSideW q B := by
    unfold itcsSideW
    omega
  have hm' := it_tab hm (itcsSides X x₀ vL vR) (fun a => (itcs_sides_le X x₀ vL vR a).trans hq)
    (B := 100 * (itcsSideW q B + 1)) (fun a => itcs_side_spec hf X x₀ a vL vR
      (by have h := wt_list2_le (.list [encFun (itcsBal X x₀), .nat vL, .nat vR]) (.nat a)
          have ha := wt_nat_le (a : ℕ)
          have hqa := a.isLt
          unfold itcsSideW
          omega)
      (by unfold itcsSideW; omega))
  exact hm'.mono (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)

/-- The side-table program has polynomial round cost. -/
theorem itcs_side_pbu : PBU fun _ W _ => itcsSideC (2 * W + 3) (2 * (2 * W + 3) ^ 64) := by
  simp only [itcsSideC, itcsSideW, itcsBalM, mapK]
  norm_poly

end GI.Impl
