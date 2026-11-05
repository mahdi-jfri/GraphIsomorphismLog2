module

public import Workspace.Impl.JohnPair
public import Workspace.Proved.JohnLambda

@[expose] public section

/-!
# The matrix `D` of the pairs with label `Δ`

`johnDV n labL δ` is the 0/1 matrix whose entry `(x, y)` is `johnD n labL δ x y`, as a list of
rows. The program builds it with `mapFuns 66 69` (`john_matD_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

/-- Mapping over the points `0, …, n - 1`. -/
theorem john_tab {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val} {n B : ℕ}
    {G : ℕ → Val} (hf : ∀ i < n, FunDet P f (.list [c, .nat i]) (G i) B) :
    FunDet P b (.list [c, natList (List.range n)]) (.list ((List.range n).map G))
      (n * B + mapK * (n + 1) * ((Val.list [c, natList (List.range n)]).wt +
        (Val.list ((List.range n).map G)).wt + 1)) := by
  have hT := tabulate_spec (m := n) h (c := c) (F := fun i => G i) (B := B)
    (fun i => hf i i.isLt)
  have e : (List.range n).map G = (List.finRange n).map fun i : Fin n => G (i : ℕ) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]; rfl
  rw [encFun_id] at hT
  rw [e]
  exact hT

/-- A row of `D`. -/
def johnDRow (n : ℕ) (labL : List ℕ) (δ x : ℕ) : List ℕ :=
  (List.range n).map fun y => (johnD n labL δ x y).toNat

/-- The matrix `D`, as the list of its rows. -/
def johnDV (n : ℕ) (labL : List ℕ) (δ : ℕ) : Val :=
  .list ((List.range n).map fun x => natList (johnDRow n labL δ x))

/-- The hypotheses on the labels: `n * n` of them, each below `n * n`, and `δ < n * n`. -/
structure JohnLabOK (n : ℕ) (labL : List ℕ) (δ : ℕ) : Prop where
  len : labL.length = n * n
  le : ∀ v ∈ labL, v ≤ n * n
  δle : δ ≤ n * n

theorem john_wt_natList_sq {xs : List ℕ} {n : ℕ} (hl : xs.length = n * n)
    (h : ∀ v ∈ xs, v ≤ n * n) : (natList xs).wt ≤ 7 * (n + 1) ^ 4 := by
  have h1 := wt_natList_le h
  rw [hl] at h1
  have : n * n * (2 * (n * n) + 5) + 4 ≤ 7 * (n + 1) ^ 4 := by nlinarith
  omega

theorem john_wt_bits {xs : List ℕ} (h : ∀ v ∈ xs, v ≤ 1) :
    (natList xs).wt ≤ xs.length * 7 + 4 := by
  have := wt_natList_le h; omega

theorem john_wt_DRow (n : ℕ) (labL : List ℕ) (δ x : ℕ) :
    (natList (johnDRow n labL δ x)).wt ≤ 7 * n + 4 := by
  have := john_wt_bits (xs := johnDRow n labL δ x) (by
    intro v hv; simp only [johnDRow, List.mem_map] at hv
    obtain ⟨y, -, rfl⟩ := hv; exact Bool.toNat_le _)
  simp only [johnDRow, List.length_map, List.length_range] at this
  unfold johnDRow
  omega

theorem john_wt_DV (n : ℕ) (labL : List ℕ) (δ : ℕ) :
    (johnDV n labL δ).wt ≤ 20 * (n + 1) ^ 2 := by
  have := john_wt_list_le (vs := (List.range n).map fun x => natList (johnDRow n labL δ x))
    (B := 7 * n + 4) (by
      intro v hv; obtain ⟨x, -, rfl⟩ := List.mem_map.mp hv; exact john_wt_DRow n labL δ x)
  simp only [List.length_map, List.length_range] at this
  unfold johnDV
  nlinarith

theorem john_D_toNat (n : ℕ) (labL : List ℕ) (δ x y : ℕ) :
    (johnD n labL δ x y).toNat = BinOp.eval .eq (labL.getD (n * x + y) 0) δ := by
  unfold johnD
  simp only [BinOp.eval]
  split <;> simp_all

/-- **An entry of `D`.** -/
theorem john_entD_spec {n : ℕ} {labL : List ℕ} {δ : ℕ} (hL : JohnLabOK n labL δ) {x y : ℕ}
    (hx : x < n) (hy : y < n) :
    FunDet johnProgram 73
      (.list [.list [natList labL, .nat n, .nat δ, .nat x], .nat y])
      (.nat (johnD n labL δ x y).toNat) (1000 * (n + 1) ^ 4) := by
  have hxy : n * x + y < n * n := by nlinarith
  set a := Val.list [.list [natList labL, .nat n, .nat δ, .nat x], .nat y]
  have hc : Det johnProgram [a] (arg 0) (.list [natList labL, .nat n, .nat δ, .nat x])
      (2 * a.wt + 5) := Det.arg' rfl
  have hl := Det.get' hc (Det.nat 0)
    (show [natList labL, Val.nat n, .nat δ, .nat x][0]? = some (natList labL) from rfl)
  have hn := Det.get' hc (Det.nat 1)
    (show [natList labL, Val.nat n, .nat δ, .nat x][1]? = some (.nat n) from rfl)
  have hd := Det.get' hc (Det.nat 2)
    (show [natList labL, Val.nat n, .nat δ, .nat x][2]? = some (.nat δ) from rfl)
  have hX := Det.get' hc (Det.nat 3)
    (show [natList labL, Val.nat n, .nat δ, .nat x][3]? = some (.nat x) from rfl)
  have hY : Det johnProgram [a] (arg 1) (.nat y) (2 * a.wt + 6) := Det.arg' rfl
  have hidx := Det.arith (op := .add) (Det.arith (op := .mul) hn hX) hY
  have hget : (labL.map Val.nat)[BinOp.eval .add (BinOp.eval .mul n x) y]? =
      some (.nat (labL.getD (n * x + y) 0)) := by
    simp only [BinOp.eval, List.getElem?_map, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by rw [hL.len]; exact hxy)]
    rfl
  have h1 := Det.get' (v := .nat (labL.getD (n * x + y) 0)) hl hidx hget
  have h2 := Det.arith (op := .eq) h1 hd
  rw [← john_D_toNat] at h2
  refine FunDet.intro john_at_entDF.single (h2.mono ?_)
  -- The bound.
  have wl := john_wt_natList_sq hL.len hL.le
  have hge : labL.getD (n * x + y) 0 ≤ n * n := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hL.len]; exact hxy)]
    exact hL.le _ (List.getElem_mem _)
  have e1 := wt_list4_le (natList labL) (.nat n) (.nat δ) (.nat x)
  have e2 := wt_list2_le (.list [natList labL, .nat n, .nat δ, .nat x]) (.nat y)
  have ea : a.wt = (Val.list [.list [natList labL, .nat n, .nat δ, .nat x], .nat y]).wt := rfl
  have w1 := wt_nat_le n; have w2 := wt_nat_le δ; have w3 := wt_nat_le x; have w4 := wt_nat_le y
  have w5 := wt_nat_le (labL.getD (n * x + y) 0)
  have w6 := wt_nat_le (BinOp.eval .mul n x)
  have w7 := wt_nat_le (BinOp.eval .add (BinOp.eval .mul n x) y)
  have w8 : (Val.nat (johnD n labL δ x y).toNat).wt ≤ 3 := wt_boolVal_le _
  have w9 := wt_nat_le 0; have w10 := wt_nat_le 1; have w11 := wt_nat_le 2
  have w12 := wt_nat_le 3
  have hmx : BinOp.eval .mul n x ≤ n * n := by
    simp only [BinOp.eval]; exact Nat.mul_le_mul_left _ hx.le
  have hax : BinOp.eval .add (BinOp.eval .mul n x) y ≤ n * n := by
    simp only [BinOp.eval] at hmx ⊢; omega
  have y1 : n * n ≤ (n + 1) ^ 4 := by nlinarith
  have y0 : n + 1 ≤ (n + 1) ^ 4 := by nlinarith
  have := hL.δle
  omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

theorem john_wt_Rn (n : ℕ) : (natList (List.range n)).wt ≤ 5 * (n + 1) ^ 2 :=
  wt_natList_le_sq (fun v hv => (List.mem_range.mp hv).le) (by simp)

theorem john_pow_le {Y i j : ℕ} (hY : 1 ≤ Y) (hij : i ≤ j) : Y ^ i ≤ Y ^ j :=
  Nat.pow_le_pow_right hY hij

/-- **A row of `D`.** -/
theorem john_rowD_spec {n : ℕ} {labL : List ℕ} {δ : ℕ} (hL : JohnLabOK n labL δ) {x : ℕ}
    (hx : x < n) :
    FunDet johnProgram 70
      (.list [.list [natList labL, .nat n, .nat δ, .nat x], natList (List.range n)])
      (natList (johnDRow n labL δ x)) (200000 * (n + 1) ^ 5) := by
  have hT := john_tab john_at_mapEntD (c := .list [natList labL, .nat n, .nat δ, .nat x])
    (n := n) (B := 1000 * (n + 1) ^ 4)
    (G := fun y => .nat (johnD n labL δ x y).toNat) fun y hy => john_entD_spec hL hx hy
  have e : Val.list ((List.range n).map fun y => Val.nat (johnD n labL δ x y).toNat) =
      natList (johnDRow n labL δ x) := by
    simp [natList, johnDRow, List.map_map, Function.comp_def]
  rw [e] at hT
  refine hT.mono ?_
  have wl := john_wt_natList_sq hL.len hL.le
  have wR := john_wt_Rn n
  have wo := john_wt_DRow n labL δ x
  have e1 := wt_list4_le (natList labL) (.nat n) (.nat δ) (.nat x)
  have e2 := wt_list2_le (.list [natList labL, .nat n, .nat δ, .nat x]) (natList (List.range n))
  have w1 := wt_nat_le n; have w2 := wt_nat_le δ; have w3 := wt_nat_le x
  have := hL.δle
  have y1 : n * n ≤ (n + 1) ^ 4 := by nlinarith
  have y2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := john_pow_le (by omega) (by omega)
  have y0 : n + 1 ≤ (n + 1) ^ 4 := by nlinarith
  set A := (Val.list [.list [natList labL, .nat n, .nat δ, .nat x], natList (List.range n)]).wt
  have hA : A + (natList (johnDRow n labL δ x)).wt + 1 ≤ 100 * (n + 1) ^ 4 := by omega
  have p1 : n * (1000 * (n + 1) ^ 4) ≤ 1000 * (n + 1) ^ 5 := by
    calc n * (1000 * (n + 1) ^ 4) ≤ (n + 1) * (1000 * (n + 1) ^ 4) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 1000 * (n + 1) ^ 5 := by ring
  have p2 : mapK * (n + 1) * (A + (natList (johnDRow n labL δ x)).wt + 1) ≤
      1000 * (100 * (n + 1) ^ 5) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (n + 1) * (A + (natList (johnDRow n labL δ x)).wt + 1) ≤ (n + 1) * (100 * (n + 1) ^ 4) :=
          Nat.mul_le_mul_left _ hA
      _ = 100 * (n + 1) ^ 5 := by ring
  omega

/-- **A row of `D`, as the function `johnRowDF`.** -/
theorem john_rowDF_spec {n : ℕ} {labL : List ℕ} {δ : ℕ} (hL : JohnLabOK n labL δ) {x : ℕ}
    (hx : x < n) :
    FunDet johnProgram 69
      (.list [.list [natList labL, .nat n, .nat δ, natList (List.range n)], .nat x])
      (natList (johnDRow n labL δ x)) (400000 * (n + 1) ^ 5) := by
  set c := Val.list [natList labL, .nat n, .nat δ, natList (List.range n)]
  set a := Val.list [c, .nat x]
  have hc : Det johnProgram [a] (arg 0) c (2 * a.wt + 5) := Det.arg' rfl
  have h0 := Det.get' hc (Det.nat 0)
    (show [natList labL, Val.nat n, .nat δ, natList (List.range n)][0]? = some (natList labL)
      from rfl)
  have h1 := Det.get' hc (Det.nat 1)
    (show [natList labL, Val.nat n, .nat δ, natList (List.range n)][1]? = some (.nat n) from rfl)
  have h2 := Det.get' hc (Det.nat 2)
    (show [natList labL, Val.nat n, .nat δ, natList (List.range n)][2]? = some (.nat δ) from rfl)
  have h3 := Det.get' hc (Det.nat 3)
    (show [natList labL, Val.nat n, .nat δ, natList (List.range n)][3]? =
      some (natList (List.range n)) from rfl)
  have hX : Det johnProgram [a] (arg 1) (.nat x) (2 * a.wt + 6) := Det.arg' rfl
  have hcall := Det.call (Det.mk2 (Det.mk4 h0 h1 h2 hX) h3) (john_rowD_spec hL hx)
  refine FunDet.intro john_at_rowDF.single (hcall.mono ?_)
  have wl := john_wt_natList_sq hL.len hL.le
  have wR := john_wt_Rn n
  have wo := john_wt_DRow n labL δ x
  have e1 := wt_list4_le (natList labL) (.nat n) (.nat δ) (.nat x)
  have e2 := wt_list2_le (.list [natList labL, .nat n, .nat δ, .nat x]) (natList (List.range n))
  have e3 := wt_list4_le (natList labL) (.nat n) (.nat δ) (natList (List.range n))
  have e4 := wt_list2_le c (.nat x)
  have ec : c.wt = (Val.list [natList labL, .nat n, .nat δ, natList (List.range n)]).wt := rfl
  have ea : a.wt = (Val.list [c, .nat x]).wt := rfl
  have w1 := wt_nat_le n; have w2 := wt_nat_le δ; have w3 := wt_nat_le x
  have w4 := wt_nat_le 0; have w5 := wt_nat_le 1; have w6 := wt_nat_le 2; have w7 := wt_nat_le 3
  have := hL.δle
  have y1 : n * n ≤ (n + 1) ^ 4 := by nlinarith
  have y2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := john_pow_le (by omega) (by omega)
  have y0 : n + 1 ≤ (n + 1) ^ 4 := by nlinarith
  have y45 : (n + 1) ^ 4 ≤ (n + 1) ^ 5 := john_pow_le (by omega) (by omega)
  omega

/-- **The matrix `D`.** -/
theorem john_matD_spec {n : ℕ} {labL : List ℕ} {δ : ℕ} (hL : JohnLabOK n labL δ) :
    FunDet johnProgram 66
      (.list [.list [natList labL, .nat n, .nat δ, natList (List.range n)],
        natList (List.range n)])
      (johnDV n labL δ) (1000000 * (n + 1) ^ 6) := by
  have hT := john_tab john_at_mapRowD
    (c := .list [natList labL, .nat n, .nat δ, natList (List.range n)])
    (n := n) (B := 400000 * (n + 1) ^ 5) (G := fun x => natList (johnDRow n labL δ x))
    fun x hx => john_rowDF_spec hL hx
  refine hT.mono ?_
  have wl := john_wt_natList_sq hL.len hL.le
  have wR := john_wt_Rn n
  have wo : (Val.list ((List.range n).map fun x => natList (johnDRow n labL δ x))).wt ≤
      20 * (n + 1) ^ 2 := john_wt_DV n labL δ
  have ed : (Val.list ((List.range n).map fun x => natList (johnDRow n labL δ x))).wt =
    (johnDV n labL δ).wt := rfl
  have e3 := wt_list4_le (natList labL) (.nat n) (.nat δ) (natList (List.range n))
  have e4 := wt_list2_le (.list [natList labL, .nat n, .nat δ, natList (List.range n)])
    (natList (List.range n))
  have w1 := wt_nat_le n; have w2 := wt_nat_le δ
  have := hL.δle
  have y1 : n * n ≤ (n + 1) ^ 4 := by nlinarith
  have y2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := john_pow_le (by omega) (by omega)
  have y0 : n + 1 ≤ (n + 1) ^ 4 := by nlinarith
  set A := (Val.list [.list [natList labL, .nat n, .nat δ, natList (List.range n)],
    natList (List.range n)]).wt
  have hA : A + (Val.list ((List.range n).map fun x => natList (johnDRow n labL δ x))).wt + 1 ≤
      200 * (n + 1) ^ 4 := by omega
  have p1 : n * (400000 * (n + 1) ^ 5) ≤ 400000 * (n + 1) ^ 6 := by
    calc n * (400000 * (n + 1) ^ 5) ≤ (n + 1) * (400000 * (n + 1) ^ 5) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 400000 * (n + 1) ^ 6 := by ring
  have p2 : mapK * (n + 1) * (A + (Val.list ((List.range n).map fun x =>
      natList (johnDRow n labL δ x))).wt + 1) ≤ 1000 * (200 * (n + 1) ^ 5) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (n + 1) * (A + (Val.list ((List.range n).map fun x =>
        natList (johnDRow n labL δ x))).wt + 1) ≤ (n + 1) * (200 * (n + 1) ^ 4) :=
          Nat.mul_le_mul_left _ hA
      _ = 200 * (n + 1) ^ 5 := by ring
  have y56 : (n + 1) ^ 5 ≤ (n + 1) ^ 6 := john_pow_le (by omega) (by omega)
  omega

end GI.Impl
