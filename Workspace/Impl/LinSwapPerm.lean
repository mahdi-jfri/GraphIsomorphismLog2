module

public import Workspace.Impl.LinSumPerm

@[expose] public section

/-! The permutation that exchanges the two consecutive copies. -/
namespace GI.Impl
open GI.Cited GI.Lang Equiv

def linSwapPerm (n : ℕ) : Perm (Fin (n + n)) := sumToFin (Equiv.sumComm (Fin n) (Fin n))

@[simp] theorem linSwapPerm_left {n : ℕ} (x : Fin n) : linSwapPerm n (x.castAdd n) = Fin.natAdd n x := by
  simp [linSwapPerm, sumToFin]

@[simp] theorem linSwapPerm_right {n : ℕ} (x : Fin n) : linSwapPerm n (Fin.natAdd n x) = x.castAdd n := by
  change finSumFinEquiv ((finSumFinEquiv.symm (Fin.natAdd n x)).swap) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem linSwapPerm_apply {n : ℕ} (x : Fin (n + n)) :
    (linSwapPerm n x : ℕ) = if (x : ℕ) < n then n + x else x - n := by
  induction x using Fin.addCases with
  | left i => simp [i.isLt, Nat.add_comm]
  | right i =>
    rw [linSwapPerm_right]
    simp only [Fin.val_natAdd, Fin.val_castAdd]
    split_ifs <;> omega

def linSwapPermPointF : Expr := .ite (.arith .lt (arg 1) (arg 0))
  (.arith .add (arg 0) (arg 1)) (.arith .sub (arg 1) (arg 0))

def linSwapPermF (range map : ℕ) : Expr :=
  .letE (.call range (.arith .add (.var 0) (.var 0)))
    (.call map (mk2 (.var 0) (.var 1)))

def linSwapPermFuns (b : ℕ) : List Expr :=
  [linSwapPermF (b + 2) (b + 5), linSwapPermPointF] ++
    rangeFuns (b + 2) ++ mapFuns (b + 5) (b + 1)

theorem linSwapPermFuns_length (b : ℕ) : (linSwapPermFuns b).length = 8 := rfl

theorem linSwapPermPoint_spec {P : Program} {f n : ℕ}
    (hf : P.funs[f]? = some linSwapPermPointF) (x : Fin (n + n)) :
    FunDet P f (.list [.nat n, .nat x]) (.nat (linSwapPerm n x)) (1000 * (n + 1)) := by
  have dn := Det.arg' (P := P) (vs := [.nat n, .nat x]) (rest := []) (j := 0) rfl
  have dx := Det.arg' (P := P) (vs := [.nat n, .nat x]) (rest := []) (j := 1) rfl
  have dt := Det.arith (op := .lt) dx dn
  have dplus := Det.arith (op := .add) dn dx
  have dminus := Det.arith (op := .sub) dx dn
  have hh := Det.ite' dt dplus dminus
  have hi := x.isLt
  have wn := wt_nat_le n
  have wx := wt_nat_le x.val
  have wa := wt_nat_le (n + x.val)
  have ws := wt_nat_le (x.val - n)
  have wi := wt_list2_le (.nat n) (.nat x.val)
  have wz : (Val.nat 0).wt = 2 := by decide
  have w₁ : (Val.nat 1).wt = 3 := by decide
  apply FunAll.intro hf
  refine hh.post fun cost hc => ⟨?_, ?_⟩
  · by_cases hx : (x : ℕ) < n <;> simp [GI.Machine.BinOp.eval, linSwapPerm_apply, hx]
  · simp only [GI.Machine.BinOp.eval] at hc
    simp only [_root_.max_def] at hc
    split_ifs at hc <;> omega

def linSwapPermRangeBudget (n : ℕ) : ℕ :=
  loopModK * (n + n + 1) * (n + n + 2 + (n + n) + 16 * (n + 1) ^ 2 + 1)
def linSwapPermMapBudget (n : ℕ) : ℕ :=
  linMapBudget (100 * (n + 1) ^ 2) (1000 * (n + 1))
def linSwapPermCost (n : ℕ) : ℕ :=
  100000 * (n + 1 + linSwapPermRangeBudget n + linSwapPermMapBudget n + 16 * (n + 1) ^ 2)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linSwapPerm_spec {P : Program} {b : ℕ} (hp : P.HasAt b (linSwapPermFuns b)) (n : ℕ) :
    FunDet P b (.nat n) (encPerm (linSwapPerm n)) (linSwapPermCost n) := by
  let ids := encPerm (1 : Perm (Fin (n + n)))
  have wid : ids.wt ≤ 16 * (n + 1) ^ 2 := wt_encPerm_sum_le 1
  have wo : (encPerm (linSwapPerm n)).wt ≤ 16 * (n + 1) ^ 2 := wt_encPerm_sum_le _
  have wn := wt_nat_le n
  have wnn := wt_nat_le (n + n)
  have wone : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have wi := wt_list2_le (.nat n) ids
  have ww : (Val.list [.nat n, ids]).wt ≤ 100 * (n + 1) ^ 2 := by omega
  have hs := range_spec (hp.block 2 rfl) (n + n)
  have hs' : FunDet P (b + 2) (.nat (n + n)) ids (linSwapPermRangeBudget n) := by
    refine hs.mono fun w cost hw => ⟨hw.1.trans range_eq_encPerm_one, ?_⟩
    have hc := hw.2
    rw [hw.1, range_eq_encPerm_one] at hc
    unfold linSwapPermRangeBudget
    dsimp only [ids] at *
    exact hc.trans (Nat.mul_le_mul_left _ (by omega))
  have hpt := (hp.block (gs := [linSwapPermPointF]) 1 rfl).single
  have hm := linMapEncoded_spec (hp.block 5 rfl) (fun i : Fin (n + n) => Val.nat i)
    (fun i j h => Fin.ext (Val.nat.inj h)) (fun i => Val.nat (linSwapPerm n i))
    (.nat n) (List.finRange (n + n)) (1000 * (n + 1))
    (fun i _ => linSwapPermPoint_spec hpt i)
  have hm' := hm.mono (linMapBudget_mono ww le_rfl)
  have dr := Det.call
    (Det.arith (op := .add) (Det.var' (P := P) (env := [.nat n]) (i := 0) rfl)
      (Det.var' (P := P) (env := [.nat n]) (i := 0) rfl)) hs'
  have dm := Det.call (Det.mk2
    (Det.var' (P := P) (env := [.nat n, ids]) (i := 0) rfl)
    (Det.var' (P := P) (env := [.nat n, ids]) (i := 1) rfl)) hm'
  apply FunAll.intro (hp.block (gs := [linSwapPermF (b + 2) (b + 5)]) 0 rfl).single
  refine (Det.letE dr dm).post fun cost hc => ⟨rfl, ?_⟩
  unfold linSwapPermCost
  have wout : (Val.list ((List.finRange (n + n)).map fun i => Val.nat (linSwapPerm n i))).wt ≤
      16 * (n + 1) ^ 2 := wo
  dsimp only [ids, linSwapPermMapBudget] at *
  simp only [GI.Machine.BinOp.eval_add] at hc
  omega

theorem linSwapPermCost_poly : PBU (fun n _ _ => linSwapPermCost n) := by
  unfold linSwapPermCost linSwapPermRangeBudget linSwapPermMapBudget linMapBudget
  norm_poly

end GI.Impl
