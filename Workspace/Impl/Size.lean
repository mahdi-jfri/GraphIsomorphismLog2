module

public import Workspace.Impl.Cases
public import Workspace.Lang.Lib.Fold

@[expose] public section

/-!
# The size of the active domain, and the choice of case of `Solve`

The guards of `Solve` and of the threshold compare `s = |dom|` with `N₀` and with `N^γ`. The
value of a state stores the domain by its indicator (`DomVal`), so `s` is the sum of the
indicator: `sizeFuns b` folds `+` over it.

* `size_spec`: on a state value, `sizeFuns` returns `s` at cost at most `sizeK (wt v + 1)²`.
* `solveSelFuns`, `solveSel_spec`: the selector of `Solve`: case `0` (direct) if `s ≤ N₀`, case
  `1` (fresh) otherwise.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-! ### Counting the domain -/

open Classical in
/-- The size of the domain is the number of positions whose indicator is 1. -/
theorem size_eq_sum (e : Ω ≃ Fin k) (D : Set Ω) :
    Nat.card D = ((List.finRange k).map fun i => if e.symm i ∈ D then 1 else 0).sum := by
  rw [← Fin.sum_univ_def, Finset.sum_boole, Nat.cast_id]
  have h1 : Nat.card D = Nat.card {i : Fin k // e.symm i ∈ D} :=
    Nat.card_congr (e.subtypeEquiv fun a => by simp)
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The step of the sum: two numbers to their sum. -/
def sumG : Val → Val → Val
  | .nat a, .nat b => .nat (a + b)
  | _, _ => .nat 0

theorem foldl_sumG (a : ℕ) (l : List ℕ) :
    (l.map Val.nat).foldl sumG (.nat a) = .nat (a + l.sum) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.foldl_cons, sumG, ih, List.sum_cons]
    congr 1
    omega

/-- On `[c, a, x]`: `a + x`. -/
def addF : Expr := .arith .add (arg 1) (arg 2)

theorem addF_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some addF) (c : Val) (a x : ℕ) :
    FunDet P f (.list [c, .nat a, .nat x]) (.nat (a + x))
      (10 * (c.wt + a + x + 10)) := by
  have d1 := Det.arg' (P := P) (vs := [c, .nat a, .nat x]) (rest := []) (j := 1) rfl
  have d2 := Det.arg' (P := P) (vs := [c, .nat a, .nat x]) (rest := []) (j := 2) rfl
  refine FunDet.intro hf ((Det.arith' (op := .add) d1 d2 rfl).mono ?_)
  have : BinOp.eval .add a x = a + x := rfl
  have := wt_list3_le c (.nat a) (.nat x)
  have := wt_nat_le a
  have := wt_nat_le x
  omega

/-- The size module at base `b` (five functions): on a state value, the sum of the domain
indicator. -/
def sizeFuns (b : ℕ) : List Expr :=
  [.call (b + 1) (mk3 .nil (.get (.var 0) (.nat 2)) (.nat 0))] ++ foldlFuns (b + 1) (b + 4) ++
    [addF]

/-- The cost constant of the size module. -/
def sizeK : ℕ := 100000

open Classical in
/-- **The size of the domain.** On a state value, `sizeFuns` returns `s = |dom|`. -/
theorem size_spec {P : Program} {b : ℕ} (h : P.HasAt b (sizeFuns b)) {e : Ω ≃ Fin k}
    {c : C → ℕ} {v : Val} {S : State Ω C} (hv : StateVal e c v S) :
    FunDet P b v (.nat S.size) (sizeK * (v.wt + 1) ^ 2) := by
  have hk := StateVal.k_le_wt hv
  obtain ⟨gv, dv, xv, yv, hv', rv, -, hd, -, -, -, -, hvv⟩ := hv
  set f : Fin k → ℕ := fun i => if e.symm i ∈ S.dom then 1 else 0 with hf
  set xs : List Val := (List.finRange k).map fun i => Val.nat (f i) with hxs
  have hdv : dv = .list xs := hd
  have hdw : dv.wt < v.wt := by rw [hvv]; exact wt_le_wt_list (by simp)
  have hentry : P.funs[b]? = some (.call (b + 1) (mk3 .nil (.get (.var 0) (.nat 2)) (.nat 0))) :=
    by simpa [sizeFuns] using h 0 (by simp [sizeFuns])
  have hfold : P.HasAt (b + 1) (foldlFuns (b + 1) (b + 4)) := by
    have := (h.left (A := [_] ++ foldlFuns (b + 1) (b + 4)) (B := [addF])).right
    simpa using this
  have hadd : P.funs[b + 4]? = some addF := by
    have := h 4 (by simp [sizeFuns, foldlFuns, loopFuns])
    simpa [sizeFuns, foldlFuns, loopFuns] using this
  -- The argument of the fold.
  have hvar : Det P [v] (.var 0)
      (.list [.nat k, gv, dv, xv, yv, hv', rv, boolVal S.floor, .nat S.h, .nat S.N]) (v.wt + 1) := by
    have := Det.var' (P := P) (env := [v]) (i := 0) (v := v) rfl
    rw [hvv] at this ⊢
    exact this
  have hget : Det P [v] (.get (.var 0) (.nat 2)) dv (v.wt + 1 + (2 + 3) + dv.wt + 1) :=
    Det.get' hvar (Det.nat 2) rfl
  have harg := Det.mk3 (Det.nil (P := P) (env := [v])) hget (Det.nat 0)
  -- The partial sums are at most `k`.
  have hpart : ∀ i, ((xs.take i).foldl sumG (.nat 0)) =
      .nat (((List.finRange k).map f).take i).sum := by
    intro i
    have : xs = ((List.finRange k).map f).map Val.nat := by simp [hxs]
    rw [this, ← List.map_take, foldl_sumG, zero_add]
  have hfle : ∀ i, f i ≤ 1 := fun i => by simp only [hf]; split_ifs <;> omega
  have hsum_le : ∀ i, (((List.finRange k).map f).take i).sum ≤ k := by
    intro i
    calc (((List.finRange k).map f).take i).sum ≤ ((List.finRange k).map f).sum :=
          List.Sublist.sum_le_sum (List.take_sublist _ _) (fun _ _ => Nat.zero_le _)
      _ ≤ ((List.finRange k).map fun _ => 1).sum :=
          List.sum_le_sum fun i _ => hfle i
      _ = k := by simp
  have hxlen : xs.length = k := by simp [hxs]
  have hfd := foldl_spec_fun hfold (c := .list []) (xs := xs) (acc0 := .nat 0) (G := sumG)
    (M := k + 2) (B := fun _ => 10 * (4 + k + 1 + 10))
    (fun i _ => by rw [hpart]; have := wt_nat_le (((List.finRange k).map f).take i).sum
                   have := hsum_le i; omega)
    (fun i hi => by
      rw [hpart]
      have hxi : xs[i] = .nat (f ⟨i, by omega⟩) := by simp [hxs]
      rw [hxi]
      refine (addF_spec hadd (.list []) _ _).mono ?_
      have := hsum_le i
      have := hfle ⟨i, by omega⟩
      simp only [wt_list_nil]
      omega)
  have hres : xs.foldl sumG (.nat 0) = .nat S.size := by
    have := hpart xs.length
    rw [List.take_length] at this
    rw [this, List.take_of_length_le (by simp [hxlen]), State.size, size_eq_sum e S.dom]
  rw [hres] at hfd
  refine FunDet.intro hentry ((Det.call (P := P) harg (hdv ▸ hfd)).mono ?_)
  -- The cost.
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, hxlen]
  have w1 := wt_list3_le (.list []) dv (.nat 0)
  have w2 := wt_nat_le S.size
  have hs : S.size ≤ k := by
    rw [State.size, size_eq_sum e S.dom]
    have := hsum_le k
    rwa [List.take_of_length_le (by simp)] at this
  simp only [wt_list_nil] at w1
  rw [← hdv] at *
  have hw0 : (Val.nat 0).wt = 2 := by simp [wt_nat, GI.Machine.len_zero]
  rw [hw0] at w1
  have e1 : k * (10 * (4 + k + 1 + 10)) ≤ 10 * (v.wt + 1) ^ 2 * 20 := by nlinarith
  have e2 : loopModK * (k + 1) * ((Val.list [.list [], dv, .nat 0]).wt + k + (k + 2) + 1) ≤
      1000 * (v.wt + 1) * (4 * (v.wt + 1) + 30) := by
    unfold loopModK
    have : (Val.list [.list [], dv, .nat 0]).wt + k + (k + 2) + 1 ≤ 4 * (v.wt + 1) + 30 := by
      omega
    have h2 : k + 1 ≤ v.wt + 1 := by omega
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) this
  have e3 : 1000 * (v.wt + 1) * (4 * (v.wt + 1) + 30) ≤ 34000 * (v.wt + 1) ^ 2 := by nlinarith
  have hK : sizeK = 100000 := rfl
  rw [hK]
  nlinarith

/-! ### The selector of `Solve` -/

/-- The selector of `Solve` at base `b` (six functions): `1 - [s < N₀ + 1]`, so case `0`
(direct) when `s ≤ N₀` and case `1` (fresh) otherwise. -/
noncomputable def solveSelFuns (b : ℕ) : List Expr :=
  [.letE (.call (b + 1) (.var 0))
    (.arith .sub (.nat 1) (.arith .lt (.var 1) (.nat (P₀.N₀ + 1))))] ++ sizeFuns (b + 1)

/-- The cost constant of the selector of `Solve`. -/
noncomputable def solveSelK : ℕ := sizeK + 10 * P₀.N₀ + 100

/-- **The selector of `Solve` meets its specification**, if `Ks ≥ solveSelK` and `ds ≥ 2`. -/
theorem solveSel_spec (I : Iface) {Pg : Program} {b : ℕ} (h : Pg.HasAt b (solveSelFuns b))
    (hK : solveSelK ≤ I.Ks) (hd : 2 ≤ I.ds) : I.SelSpec Pg .solve Iface.solveCases b := by
  intro Ω C S k e c hc v hv _
  have hv' : StateVal e c v S := hv
  have hentry : Pg.funs[b]? = some (.letE (.call (b + 1) (.var 0))
      (.arith .sub (.nat 1) (.arith .lt (.var 1) (.nat (P₀.N₀ + 1))))) := by
    simpa [solveSelFuns] using h 0 (by simp [solveSelFuns])
  have hsz := size_spec (P := Pg) (b := b + 1) (by
    have := h.right (A := [_]) (B := sizeFuns (b + 1))
    simpa using this) hv'
  have hcall := Det.call (P := Pg) (env := [v]) (Det.var' (i := 0) rfl) hsz
  set j := 1 - (if S.size < P₀.N₀ + 1 then 1 else 0) with hj
  have hbody : Det Pg ([v] ++ [.nat S.size])
      (.arith .sub (.nat 1) (.arith .lt (.var 1) (.nat (P₀.N₀ + 1)))) (.nat j)
      (S.size + P₀.N₀ + 30) := by
    have d1 := Det.var' (P := Pg) (env := [v] ++ [.nat S.size]) (i := 1) (v := .nat S.size) rfl
    have d2 := Det.arith' (op := .lt) d1 (Det.nat (P₀.N₀ + 1)) rfl
    have d3 := Det.arith' (op := .sub) (Det.nat 1) d2 rfl
    refine d3.mono ?_
    have := wt_nat_le S.size
    have hl : BinOp.eval .lt S.size (P₀.N₀ + 1) ≤ 1 := by
      simp only [BinOp.eval]; split_ifs <;> omega
    have hs : BinOp.eval .sub 1 (BinOp.eval .lt S.size (P₀.N₀ + 1)) ≤ 1 := by
      simp only [BinOp.eval]; omega
    have hw1 : (Val.nat 1).wt ≤ 3 := by simp [wt_nat]
    have hjj : BinOp.eval .sub 1 (BinOp.eval .lt S.size (P₀.N₀ + 1)) = j := by
      simp only [hj, BinOp.eval]
    omega
  have hk := StateVal.k_le_wt hv'
  have hs : S.size ≤ k := by
    have := Nat.card_le_card_of_injective (fun a : S.dom => e a.1)
      (fun a b h => Subtype.ext (e.injective h))
    exact this.trans (by simp)
  refine FunAll.intro hentry (EvalAll.mono (Det.letE hcall hbody) fun w cost hw => ?_)
  obtain ⟨rfl, hcost⟩ := hw
  have hj1 : j ≤ 1 := by omega
  have hb : (cost : ℝ) ≤ I.selB .solve S v := by
    simp only [Iface.selB, if_true]
    have w1 := wt_nat_le S.size
    have w2 := wt_nat_le j
    have hn : cost ≤ solveSelK * (v.wt + 1) ^ 2 := by
      have h1 : 1 ≤ (v.wt + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h2 : v.wt + 1 ≤ (v.wt + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      unfold solveSelK
      nlinarith
    have hx : (0 : ℝ) ≤ v.wt := Nat.cast_nonneg _
    have hp : ((v.wt : ℝ) + 1) ^ 2 ≤ ((v.wt : ℝ) + 1) ^ I.ds := pow_le_pow_right₀ (by linarith) hd
    have hK' : (solveSelK : ℝ) ≤ I.Ks := by exact_mod_cast hK
    have hn' : (cost : ℝ) ≤ solveSelK * ((v.wt : ℝ) + 1) ^ 2 := by exact_mod_cast hn
    have : (solveSelK : ℝ) * ((v.wt : ℝ) + 1) ^ 2 ≤ I.Ks * ((v.wt : ℝ) + 1) ^ I.ds :=
      mul_le_mul hK' hp (by positivity) (by positivity)
    linarith
  by_cases hle : S.size ≤ P₀.N₀
  · have : j = 0 := by simp only [hj]; rw [if_pos (by omega)]
    rw [this]
    exact ⟨0, by simp [Iface.solveCases], rfl, hle, hb⟩
  · have : j = 1 := by simp only [hj]; rw [if_neg (by omega)]
    rw [this]
    exact ⟨1, by simp [Iface.solveCases], rfl, (Nat.lt_of_not_le hle : P₀.N₀ < S.size), hb⟩

end GI.Impl
