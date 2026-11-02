import Workspace.Impl.LinObjectFind

/-! Select a nonempty entry of a table of lists. In the object glue the
entries are the local transporter cosets, computed at recursive fuel zero. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linListNonempty : Val → Bool
  | .nat _ => false
  | .list xs => !xs.isEmpty

def linListNonemptyF : Expr := .arith .lt (.nat 0) (.length (arg 1))

def linListPickF (find : ℕ) : Expr :=
  .letE (.call find (mk2 .nil (.var 0))) (.get (.var 0) (.var 1))

def linListPickFuns (b : ℕ) : List Expr :=
  [linListPickF (b + 2), linListNonemptyF] ++ findFuns (b + 2) (b + 1)

theorem linListPickFuns_length (b : ℕ) : (linListPickFuns b).length = 5 := rfl

def linListPickCost (W : ℕ) : ℕ := 1000000 * (W + 1) ^ 3

theorem linListPickCost_poly : PBU (fun _ W _ => linListPickCost W) := by
  unfold linListPickCost
  norm_poly

set_option maxHeartbeats 1000000 in
theorem linListNonempty_spec {P : Program} {f : ℕ}
    (hf : P.funs[f]? = some linListNonemptyF) (c : Val) (xs : List Val) :
    FunDet P f (.list [c, .list xs]) (boolVal (linListNonempty (.list xs)))
      (100 * ((Val.list [c, .list xs]).wt + 1)) := by
  have d := Det.arith (op := .lt) (Det.nat 0)
    (Det.length (Det.arg' (P := P) (vs := [c, .list xs]) (rest := []) (j := 1) rfl))
  have he : GI.Machine.BinOp.lt.eval 0 xs.length =
      (linListNonempty (.list xs)).toNat := by
    cases xs <;> simp [GI.Machine.BinOp.eval, linListNonempty]
  rw [he] at d
  apply FunAll.intro hf
  refine d.post fun cost hc => ⟨rfl, ?_⟩
  have hl := length_lt_wt_list xs
  have hw : (Val.list xs).wt < (Val.list [c, .list xs]).wt := wt_le_wt_list (by simp)
  have hb := wt_boolVal_le (linListNonempty (.list xs))
  change (Val.nat (linListNonempty (.list xs)).toNat).wt ≤ 3 at hb
  have hz : (Val.nat 0).wt = 2 := rfl
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linListPick_spec {P : Program} {b : ℕ}
    (h : P.HasAt b (linListPickFuns b)) (xs : List Val)
    (hl : ∀ v ∈ xs, ∃ ys, v = .list ys)
    (hex : ∃ v ∈ xs, linListNonempty v = true) :
    FunAll P b (.list xs) (fun out cost => out ∈ xs ∧ linListNonempty out = true ∧
      cost ≤ linListPickCost (Val.list xs).wt) := by
  let W := (Val.list xs).wt
  let i := xs.findIdx linListNonempty
  have hi : i < xs.length := List.findIdx_lt_length_of_exists hex
  have hv : linListNonempty (xs.get ⟨i, hi⟩) = true := List.findIdx_getElem (w := hi)
  have hmem : xs.get ⟨i, hi⟩ ∈ xs := List.get_mem _ _
  have wx : (xs.get ⟨i, hi⟩).wt < W := wt_le_wt_list hmem
  have hlen : xs.length ≤ W := (length_lt_wt_list xs).le
  have ht : P.funs[b + 1]? = some linListNonemptyF :=
    (h.block (gs := [linListNonemptyF]) 1 rfl).single
  have hp : ∀ v ∈ xs, FunDet P (b + 1) (.list [.list [], v])
      (boolVal (linListNonempty v)) (1000 * (W + 1)) := by
    intro v hv
    obtain ⟨ys, rfl⟩ := hl v hv
    have ww : (Val.list ys).wt < W := wt_le_wt_list hv
    have ha := wt_list2_le (.list []) (.list ys)
    have hn : (Val.list []).wt = 4 := rfl
    exact (linListNonempty_spec ht (.list []) ys).mono (by omega)
  have hf := find_spec (h.block 2 rfl) hp
  have df := Det.call (Det.mk2 (Det.nil (P := P) (env := [.list xs]))
    (Det.var' (P := P) (env := [.list xs]) (i := 0) rfl)) hf
  have di := Det.get' (Det.var' (P := P) (env := [.list xs, .nat i]) (i := 0) rfl)
    (Det.var' (P := P) (env := [.list xs, .nat i]) (i := 1) rfl)
    (v := xs.get ⟨i, hi⟩) (List.getElem?_eq_getElem hi)
  apply FunAll.intro (h.block (gs := [linListPickF (b + 2)]) 0 rfl).single
  refine (Det.letE df di).post fun cost hc => ⟨hmem, hv, ?_⟩
  have ha := wt_list2_le (.list []) (.list xs)
  have hn : (Val.list []).wt = 4 := rfl
  have wi := wt_nat_le i
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hc
  change cost ≤ linListPickCost W
  unfold linListPickCost
  dsimp only [i, W] at *
  simp only [loopModK] at hc
  have hloop : 1000 * (xs.length + 1) *
      ((Val.list [.list [], .list xs]).wt + 2 * xs.length + 3) ≤
      1000 * ((Val.list xs).wt + 1) * (4 * (Val.list xs).wt + 17) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hsum := Nat.mul_le_mul_right (1000 * ((Val.list xs).wt + 1)) hlen
  nlinarith [Nat.zero_le ((Val.list xs).wt ^ 3)]

end GI.Impl
