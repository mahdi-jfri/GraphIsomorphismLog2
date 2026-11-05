module

public import Workspace.Lang.Lib.NatList

@[expose] public section

/-!
# Step 9 of `camProg`: the transpose of the columns

The program computes the coordinates factor by factor, as columns: column `j` lists the `j`-th
coordinate of every point. The output `encKSetTuples e` lists the points, each with all its
coordinates. `camTrFuns b` turns the list of columns into the list of rows: on `[n, cols]`, row
`x` (for `x < n`) is the list of entries `x` of the columns.
-/

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

/-- A column: the values of `f` at the points `0, …, n - 1`. -/
def camColV {n : ℕ} (f : Fin n → Val) : Val := .list ((List.finRange n).map f)

/-- On `[n, cols]`: map the row function over `range n`. -/
def camTrEntry (b : ℕ) : Expr := .call (b + 1) (mk2 (arg 1) (.call (b + 9) (arg 0)))

/-- On `[cols, x]`: map the cell function over the columns, with context `x`. -/
def camTrRow (b : ℕ) : Expr := .call (b + 5) (mk2 (arg 1) (arg 0))

/-- On `[x, col]`: entry `x` of the column. -/
def camTrCell : Expr := .get (arg 1) (arg 0)

/-- The transpose, at base `b` (twelve functions). -/
def camTrFuns (b : ℕ) : List Expr :=
  [camTrEntry b] ++ mapFuns (b + 1) (b + 4) ++ [camTrRow b] ++ mapFuns (b + 5) (b + 8) ++
    [camTrCell] ++ rangeFuns (b + 9)

def camTrK : ℕ := 10 ^ 8

theorem cam_wt_list_le_of {vs : List Val} {B : ℕ} (h : ∀ v ∈ vs, v.wt ≤ B) :
    (Val.list vs).wt ≤ vs.length * (2 * B + 1) + 4 := by
  have h1 := wt_list_le vs
  have h2 : (vs.map Val.wt).sum ≤ vs.length * B := by
    have := List.sum_le_card_nsmul (vs.map Val.wt) B (by
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact h)
    simpa using this
  have : vs.length * (2 * B + 1) = 2 * (vs.length * B) + vs.length := by ring
  omega

theorem cam_wt_app_lt {n : ℕ} (f : Fin n → Val) (x : Fin n) : (f x).wt < (camColV f).wt :=
  wt_le_wt_list (List.mem_map_of_mem (List.mem_finRange x))

/-- The weight of a row is at most three times the weight of the columns. -/
theorem cam_wt_row_le {n : ℕ} (cols : List (Fin n → Val)) (x : Fin n) :
    (Val.list (cols.map fun f => f x)).wt + 1 ≤ 3 * ((Val.list (cols.map camColV)).wt + 1) := by
  have h1 := wt_list_le (cols.map fun f => f x)
  have h2 : ((cols.map fun f => f x).map Val.wt).sum ≤ ((cols.map camColV).map Val.wt).sum := by
    simp only [List.map_map]
    exact List.sum_le_sum fun f _ => (cam_wt_app_lt f x).le
  have h3 := sum_wt_lt_wt_list (cols.map camColV)
  have h4 := length_lt_wt_list (cols.map camColV)
  simp only [List.length_map] at h1 h4
  omega

theorem camColV_app {n : ℕ} {f g : Fin n → Val} (h : camColV f = camColV g) (x : Fin n) :
    f x = g x := by
  have h1 := congrArg (fun l : List Val => l[(x : ℕ)]?) (Val.list.inj h)
  simpa using h1

/-- The row with index `i`, with a default outside the range. -/
def camRowV {n : ℕ} (cols : List (Fin n → Val)) (i : ℕ) : Val :=
  .list (cols.map fun f => if h : i < n then f ⟨i, h⟩ else .nat 0)

theorem camRowV_fin {n : ℕ} (cols : List (Fin n → Val)) (x : Fin n) :
    camRowV cols x = .list (cols.map fun f => f x) := by
  simp [camRowV, x.isLt]

/-- **Transpose.** -/
theorem camTr_spec {P : Program} {b : ℕ} (h : P.HasAt b (camTrFuns b)) {n : ℕ}
    (cols : List (Fin n → Val)) :
    FunDet P b (.list [.nat n, .list (cols.map camColV)])
      (.list ((List.finRange n).map fun x => .list (cols.map fun f => f x)))
      (camTrK * ((Val.list [.nat n, .list (cols.map camColV)]).wt + n + 1) ^ 4) := by
  simp only [camTrFuns] at h
  have hE : P.funs[b]? = some (camTrEntry b) := h.left.left.left.left.left.single
  have hM1 : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.left.left.left.left.right
  have hR : P.funs[b + 4]? = some (camTrRow b) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.left.left.left.right.single
  have hM2 : P.HasAt (b + 5) (mapFuns (b + 5) (b + 8)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.left.left.right
  have hC : P.funs[b + 8]? = some camTrCell := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.left.right.single
  have hRg : P.HasAt (b + 9) (rangeFuns (b + 9)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.right
  set CV := Val.list (cols.map camColV) with hCV
  set W := (Val.list [.nat n, CV]).wt with hW
  set Y := W + n + 1 with hY
  have hCVw : CV.wt < W := wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hnw : (Val.nat n).wt < W := wt_le_wt_list (List.mem_cons_self ..)
  have hlen : cols.length < CV.wt := by
    have := length_lt_wt_list (cols.map camColV); simpa using this
  have hY1 : 1 ≤ Y := by omega
  have hYY : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by omega)
  have hY34 : Y ^ 3 ≤ Y ^ 4 := Nat.pow_le_pow_right hY1 (by omega)
  -- the cell
  have hcell : ∀ (x : Fin n), ∀ v ∈ cols.map camColV, FunAll P (b + 8) (.list [.nat x, v])
      (fun w cost => (∀ f, v = camColV f → w = f x) ∧ cost ≤ 50 * Y) := by
    intro x v hv
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hv
    have hfx : ((List.finRange n).map f)[(x : ℕ)]? = some (f x) := by simp
    refine FunAll.intro hC ((Det.get' (Det.arg' (P := P) (vs := [.nat x, camColV f]) (rest := [])
      (j := 1) rfl) (Det.arg' (P := P) (vs := [.nat x, camColV f]) (rest := []) (j := 0) rfl)
      hfx).post fun c hc => ⟨fun g hg => camColV_app hg x, ?_⟩)
    have h1 := wt_list2_le (.nat x) (camColV f)
    have h2 := wt_nat_le x
    have h3 : (camColV f).wt < CV.wt := wt_le_wt_list (List.mem_map_of_mem hf)
    have h4 := cam_wt_app_lt f x
    have h5 := x.isLt
    omega
  -- the row
  have hrow : ∀ v ∈ (List.range n).map Val.nat,
      FunAll P (b + 4) (.list [CV, v])
        (fun w cost => (∀ i, v = .nat i → w = camRowV cols i) ∧ cost ≤ 1000 * mapK * Y ^ 2) := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    have hin : i < n := List.mem_range.mp hi
    set x : Fin n := ⟨i, hin⟩ with hx
    refine FunAll.intro hR (EvalAll.call_funAll (Det.mk2 (Det.arg' (P := P) (vs := [CV, .nat i])
      (rest := []) (j := 1) rfl) (Det.arg' (P := P) (vs := [CV, .nat i]) (rest := []) (j := 0) rfl))
      fun a ca ha => ?_)
    obtain ⟨rfl, hca⟩ := ha
    refine (map_spec hM2 (c := .nat x) (xs := cols.map camColV) (hcell x)).mono
      fun w cb hw => ?_
    obtain ⟨ws, rfl, hws, hcb⟩ := hw
    have hws' := forall₂_map_eq (g := fun f => f x) (fun f _ w hw => hw f rfl) hws
    subst hws'
    refine ⟨fun j hj => ?_, ?_⟩
    · cases hj; exact (camRowV_fin cols x).symm
    · have hsum : ((cols.map camColV).map fun _ => 50 * Y).sum = cols.length * (50 * Y) := by
        simp [List.map_map, Function.comp_def, List.sum_replicate]
      rw [hsum] at hcb
      simp only [List.length_map] at hcb
      have hr := cam_wt_row_le cols x
      have h1 := wt_list2_le CV (.nat i)
      have h1' := wt_list2_le (.nat i) CV
      have h2 := wt_nat_le i
      have e1 : (Val.list [.nat (x : ℕ), .list (cols.map camColV)]).wt = (Val.list [.nat i, CV]).wt :=
        rfl
      rw [e1] at hcb
      have hCVe : (Val.list (cols.map camColV)).wt = CV.wt := rfl
      have hlY : cols.length + 1 ≤ Y := by omega
      have hwi : (Val.list [.nat i, CV]).wt ≤ 2 * (n + 1 + W) + 6 := by omega
      have k1 : cols.length * (50 * Y) ≤ Y * (50 * Y) := Nat.mul_le_mul_right _ (by omega)
      have k2 : mapK * (cols.length + 1) * ((Val.list [.nat i, CV]).wt +
          (Val.list (cols.map fun f => f x)).wt + 1) ≤ mapK * Y * (20 * Y) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hlY) (by
          have : (Val.list (cols.map fun f => f x)).wt + 1 ≤ 3 * (CV.wt + 1) := hr
          omega)
      have e2 : Y * (50 * Y) = 50 * Y ^ 2 := by ring
      have e3 : mapK * Y * (20 * Y) = 20 * mapK * Y ^ 2 := by ring
      have hwr : (Val.list (cols.map fun f => f x)).wt ≤ 3 * Y := by omega
      simp only [mapK] at *
      omega
  -- the outer map
  have fR : FunDet P (b + 9) (.nat n) (natList (List.range n))
      (loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1)) :=
    (range_spec hRg n).mono fun w c hw => by obtain ⟨rfl, h⟩ := hw; exact ⟨rfl, h⟩
  have dRange := Det.call (Det.arg' (P := P) (vs := [.nat n, CV]) (rest := []) (j := 0) rfl) fR
  refine FunAll.intro hE (EvalAll.call_funAll (Det.mk2 (Det.arg' (P := P) (vs := [.nat n, CV])
    (rest := []) (j := 1) rfl) dRange) fun a ca ha => ?_)
  obtain ⟨rfl, hca⟩ := ha
  refine (map_spec hM1 (c := CV) (xs := (List.range n).map Val.nat) hrow).mono fun w cb hw => ?_
  obtain ⟨ws, rfl, hws, hcb⟩ := hw
  have hws' := forall₂_map_eq (g := camRowV cols) (fun i _ w hw => hw i rfl) hws
  subst hws'
  have hrows : (List.range n).map (camRowV cols) =
      (List.finRange n).map fun x => .list (cols.map fun f => f x) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    exact List.map_congr_left fun x _ => camRowV_fin cols x
  rw [hrows] at hcb ⊢
  refine ⟨rfl, ?_⟩
  have hsum : (((List.range n).map Val.nat).map fun _ => 1000 * mapK * Y ^ 2).sum =
      n * (1000 * mapK * Y ^ 2) := by
    simp [List.map_map, Function.comp_def, List.sum_replicate]
  rw [hsum] at hcb
  simp only [List.length_map, List.length_range] at hcb
  have hout := cam_wt_list_le_of (vs := (List.finRange n).map fun x => .list (cols.map fun f => f x))
    (B := 3 * Y) (fun v hv => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hv
      have := cam_wt_row_le cols x
      have hCVe : (Val.list (cols.map camColV)).wt = CV.wt := rfl
      omega)
  simp only [List.length_map, List.length_finRange] at hout
  have hnl := wt_natList_le_sq (xs := List.range n) (B := n) (fun x hx => (List.mem_range.mp hx).le)
    (by simp)
  have hnl' : (natList (List.range n)).wt ≤ 5 * Y ^ 2 :=
    hnl.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hw2 := wt_list2_le CV (natList (List.range n))
  have e1 : (Val.list [CV, .list ((List.range n).map Val.nat)]).wt =
      (Val.list [CV, natList (List.range n)]).wt := rfl
  have hnn := wt_nat_le n
  have k1 : n * (2 * (3 * Y) + 1) ≤ Y * (7 * Y) := Nat.mul_le_mul (by omega) (by omega)
  have k2 : n * (1000 * mapK * Y ^ 2) ≤ Y * (1000 * mapK * Y ^ 2) := Nat.mul_le_mul_right _ (by omega)
  have e2 : Y * (7 * Y) = 7 * Y ^ 2 := by ring
  have e3 : Y * (1000 * mapK * Y ^ 2) = 1000 * mapK * Y ^ 3 := by ring
  have k3 : mapK * (n + 1) * ((Val.list [CV, .list ((List.range n).map Val.nat)]).wt +
      (Val.list ((List.finRange n).map fun x => .list (cols.map fun f => f x))).wt + 1) ≤
      mapK * Y * (40 * Y ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e4 : mapK * Y * (40 * Y ^ 2) = 40 * mapK * Y ^ 3 := by ring
  have k4 : loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1) ≤
      loopModK * Y * (10 * Y ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e5 : loopModK * Y * (10 * Y ^ 2) = 10 * loopModK * Y ^ 3 := by ring
  have hwa : (Val.list [.nat n, CV]).wt = W := rfl
  simp only [camTrK, mapK, loopModK] at *
  clear_value CV W
  generalize Y ^ 4 = Q4 at *
  generalize Y ^ 3 = Q3 at *
  generalize Y ^ 2 = Q2 at *
  omega

end GI.Lang
