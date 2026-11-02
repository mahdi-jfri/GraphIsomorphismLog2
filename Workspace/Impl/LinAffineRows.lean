import Workspace.Impl.LinAffineVector
import Workspace.Lang.Lib.List
import Workspace.Lang.Lib.LinIntVector

/-! Construct the dense rows [R_i, u_i] of a homogenized affine matrix.
This is list manipulation on the field-value encoding, with no new primitive. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linAffineRowsStep : Expr :=
  .snoc (arg 2) (.snoc (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.get (.get (arg 0) (.nat 1)) (arg 1)))

def linAffineRowsFuns (b : ℕ) : List Expr :=
  loopFuns b (.length (arg 0)) .nil linAffineRowsStep

theorem linAffineRowsFuns_length (b : ℕ) : (linAffineRowsFuns b).length = 3 := rfl

def linAffineRowsAcc (W r : ℕ) : ℕ := linVectorAccWt r (10 * (W + 1))
def linAffineRowsCost (W r : ℕ) : ℕ :=
  r * (1000 * (W + r + linAffineRowsAcc W r + 1)) +
    loopModK * (r + 1) * (W + r + linAffineRowsAcc W r + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linAffineRows_spec {P : Program} {b p r c : ℕ}
    (hp : P.HasAt b (linAffineRowsFuns b))
    (A : Matrix (Fin r) (Fin c) (ZMod p)) (v : Fin r → ZMod p) :
    FunDet P b (.list [.list ((List.finRange r).map fun i => encVec (A i)), encVec v])
      (.list ((List.finRange r).map fun i =>
        .list (((List.finRange c).map fun j => .nat (A i j).val) ++ [.nat (v i).val])))
      (linAffineRowsCost (Val.list [.list ((List.finRange r).map fun i => encVec (A i)), encVec v]).wt r) := by
  let av := Val.list ((List.finRange r).map fun i => encVec (A i))
  let a := Val.list [av, encVec v]
  let W := a.wt
  let rows := (List.finRange r).map fun i =>
    Val.list (((List.finRange c).map fun j => .nat (A i j).val) ++ [.nat (v i).val])
  have wa : av.wt < W := wt_le_wt_list (by simp [W, a])
  have wv : (encVec v).wt < W := wt_le_wt_list (by simp [W, a])
  have wr (i : Fin r) : (encVec (A i)).wt < W :=
    (wt_le_wt_list (vs := (List.finRange r).map fun i => encVec (A i))
      (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)).trans wa
  have we (i : Fin r) : (Val.nat (v i).val).wt < W :=
    (wt_le_wt_list (vs := (List.finRange r).map fun i => .nat (v i).val)
      (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)).trans wv
  have wrow (i : Fin r) :
      (Val.list (((List.finRange c).map fun j => .nat (A i j).val) ++ [.nat (v i).val])).wt ≤ 10 * (W + 1) := by
    have hh := wt_list_snoc_le ((List.finRange c).map fun j => .nat (A i j).val) (.nat (v i).val)
    have hi := wr i
    have hv := we i
    change (encVec (A i)).wt < W at hi
    dsimp only [encVec] at hi
    omega
  have wacc (k : ℕ) : (Val.list (rows.take k)).wt ≤ linAffineRowsAcc W r := by
    have hh := linWtList (vs := rows.take k) (B := 10 * (W + 1)) (by
      intro v hv; obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hv); exact wrow i)
    have hl : (rows.take k).length ≤ r := by simp [rows]
    exact hh.trans (by unfold linAffineRowsAcc linVectorAccWt; nlinarith [Nat.mul_le_mul_right (10 * (W + 1)) hl])
  have dk := Det.length (Det.arg' (P := P) (vs := [av, encVec v]) (rest := []) (j := 0) rfl)
  simp only [av, List.length_map, List.length_finRange] at dk
  have loop := loopBdd_spec hp dk Det.nil (by
      have := a.two_le_size.trans a.size_le_wt
      dsimp only [a, W, av] at *
      omega)
    (Inv := fun k acc => acc = .list (rows.take k)) (M := linAffineRowsAcc W r)
    (D := fun _ => 1000 * (W + r + linAffineRowsAcc W r + 1))
    (by simp) (fun k acc _ h => h ▸ wacc k) (fun k acc hk hacc => ?_)
  · refine loop.mono fun out cost ho => ⟨?_, ?_⟩
    · have hl : rows.length = r := by simp [rows]
      simpa only [← hl, List.take_length] using ho.1
    · simpa only [linAffineRowsCost, Finset.sum_const, Finset.card_range, smul_eq_mul] using ho.2
  · subst acc
    let i : Fin r := ⟨k, hk⟩
    have da (j : ℕ) {v : Val} (hv : [a, .nat k, .list (rows.take k)][j]? = some v) :=
      Det.arg' (P := P) (vs := [a, .nat k, .list (rows.take k)]) (rest := []) (j := j) hv
    have dm := Det.get' (da 0 rfl) (Det.nat 0) rfl
    have dc := Det.get' (da 0 rfl) (Det.nat 1) rfl
    have di := da 1 rfl
    have dr := Det.get' dm di (show ((List.finRange r).map fun j => encVec (A j))[k]? = some (encVec (A i)) by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hk)]; simp [i])
    have de := Det.get' dc di (show ((List.finRange r).map fun j => Val.nat (v j).val)[k]? = some (Val.nat (v i).val) by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hk)]; simp [i])
    have step := Det.snoc (da 2 rfl) (Det.snoc dr de)
    have ht : rows.take (k + 1) = rows.take k ++
        [.list (((List.finRange c).map fun j => .nat (A i j).val) ++ [.nat (v i).val])] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp [rows]; exact hk)]; simp [rows, i]
    refine step.post fun cost hcost => ⟨by dsimp only; rw [ht], ?_⟩
    have wo := wacc k
    have wn := wacc (k + 1)
    rw [ht] at wn
    have wi := wt_nat_le k
    have ws := wt_list3_le a (.nat k) (.list (rows.take k))
    have wr' := wr i
    have we' := we i
    have wy := wrow i
    change _ ≤ 1000 * (W + r + linAffineRowsAcc W r + 1) + 100 * (W + r + linAffineRowsAcc W r + 1)
    dsimp only [W, a, av, encVec] at *
    omega

/-- The construction is polynomial in its source weight and row count. -/
theorem linAffineRowsCost_poly : PBU (fun r W _ => linAffineRowsCost W r) := by
  unfold linAffineRowsCost linAffineRowsAcc linVectorAccWt
  norm_poly

end GI.Impl
