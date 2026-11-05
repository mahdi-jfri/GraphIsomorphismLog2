module

public import Workspace.Impl.GenNormInc
public import Workspace.Impl.GenCase
public import Workspace.Lang.Lib.NatList

@[expose] public section

/-!
# The incidence test as a program

The point-action recovery tests incidence in the subsets listed by Cameron recognition.
Membership is a scan of the sorted subset, using the equality test already in the language
library. The scan uses no cited task.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encKSetTuples)

/-- A sorted subset, in the format used inside the Cameron identification. -/
def normSetVal {m : ℕ} (A : Finset (Fin m)) : Val :=
  .list ((A.sort (· ≤ ·)).map fun a : Fin m => .nat a)

/-- Scan a subset for a point. -/
def normMemFuns (b : ℕ) : List Expr := anyFuns b (b + 3) ++ [eqTestF]

/-- Incidence in a subset can be tested in polynomial time without a cited hypothesis. -/
theorem normMem_spec {P : Program} {b m : ℕ} (hb : P.HasAt b (normMemFuns b))
    (A : Finset (Fin m)) (i : Fin m) :
    FunDet P b (.list [.nat i, normSetVal A]) (boolVal (decide (i ∈ A)))
      (100000 * (m + 1) ^ 3) := by
  have ht : P.funs[b + 3]? = some eqTestF := by
    simpa [normMemFuns, anyFuns, loopFuns] using hb.right.single
  let xs := (A.sort (· ≤ ·)).map fun a : Fin m => Val.nat a
  have htest : ∀ x ∈ xs, FunDet P (b + 3) (.list [.nat i, x]) (boolVal (natEq i x))
      (20 * m + 100) := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    exact (eqTest_det ht i a).mono (by have := i.2; have := a.2; omega)
  have heq : xs.any (natEq i) = decide (i ∈ A) := by
    apply Bool.eq_iff_iff.mpr
    simp only [xs, List.any_eq_true, List.mem_map, decide_eq_true_eq]
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, hx⟩
      have he : a = i := by
        have h := (of_decide_eq_true (show decide ((a : ℕ) = i) = true from hx))
        exact Fin.ext h
      exact he ▸ (Finset.mem_sort (· ≤ ·)).mp ha
    · intro hi
      exact ⟨.nat i, ⟨i, (Finset.mem_sort (· ≤ ·)).mpr hi, rfl⟩, by simp [natEq]⟩
  have h := any_spec hb.left htest
  rw [heq] at h
  refine h.mono fun w cost hw => ⟨hw.1, ?_⟩
  have hlen : xs.length ≤ m := by
    simp only [xs, List.length_map, Finset.length_sort]
    simpa using Finset.card_le_univ A
  have hwt : (normSetVal A).wt ≤ 5 * (m + 1) ^ 2 := by
    have h1 := wt_natList_le_sq (xs := (A.sort (· ≤ ·)).map fun a : Fin m => (a : ℕ))
      (B := m) (by intro a ha; obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha; exact j.isLt.le)
      (by simpa [xs] using hlen)
    simpa [normSetVal, natList, List.map_map, Function.comp_def] using h1
  have ha := wt_list2_le (.nat i) (normSetVal A)
  have hi := wt_nat_le (i : ℕ)
  have hm := i.2
  have hcost := hw.2
  have hs : (xs.map (fun _ => 20 * m + 100)).sum = xs.length * (20 * m + 100) := by
    simp [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at hcost
  change cost ≤ xs.length * (20 * m + 100) + loopModK * (xs.length + 1) *
    ((Val.list [.nat i, normSetVal A]).wt + xs.length + 4) at hcost
  have h1 : xs.length * (20 * m + 100) ≤ m * (20 * m + 100) :=
    Nat.mul_le_mul_right _ hlen
  have h2 : loopModK * (xs.length + 1) *
      ((Val.list [.nat i, normSetVal A]).wt + xs.length + 4) ≤
      loopModK * (m + 1) * (20 * (m + 1) ^ 2 + 20) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by nlinarith)
  have h3 : loopModK * (m + 1) * (20 * (m + 1) ^ 2 + 20) ≤
      40000 * (m + 1) ^ 3 := by
    simp only [loopModK]
    nlinarith [Nat.le_self_pow (by norm_num : 3 ≠ 0) (m + 1)]
  nlinarith

/-- Read a subset from a one-factor Cameron table. -/
theorem normTable_get {n m k : ℕ}
    (e : Fin n ≃ (Fin 1 → Product.KSet m k)) (b : Fin n) :
    ∃ row : Val, (encKSetTuples e : Val) =
      .list ((List.finRange n).map fun x => .list [normSetVal (e x 0).1]) ∧
      ((List.finRange n).map fun x => Val.list [normSetVal (e x 0).1])[b.val]? =
        some row ∧ row = .list [normSetVal (e b 0).1] := by
  refine ⟨.list [normSetVal (e b 0).1], ?_, ?_, rfl⟩
  · simp only [encKSetTuples, normSetVal]
    congr 1
    apply List.map_congr_left
    intro x _
    have hf : List.finRange 1 = [0] := by decide
    simp only [hf, List.map_cons, List.map_nil]
    congr 2
    induction (e x 0).1.sort (· ≤ ·) with
    | nil => rfl
    | cons a l ih =>
      simpa using congrArg Val.list (congrArg (List.cons (.nat a)) (Val.list.inj ih))
  · simp

/-- On `[[E, x, i, j], b]`, test whether point `i` lies in block `b` exactly when point `j`
lies in block `x b`. -/
def normIncTestF (mem : ℕ) : Expr :=
  .letE (.call mem (mk2 (.get (arg 0) (.nat 2))
    (.get (.get (.get (arg 0) (.nat 0)) (arg 1)) (.nat 0))))
  (.letE (.call mem (mk2 (.get (arg 0) (.nat 3))
    (.get (.get (.get (arg 0) (.nat 0))
      (.get (.get (arg 0) (.nat 1)) (arg 1))) (.nat 0))))
  (.arith .eq (.var 1) (.var 2)))

set_option maxHeartbeats 2000000 in
/-- The incidence test computes the predicate used by `normPointCandidates`. -/
theorem normIncTest_spec {P : Program} {f mem n m k : ℕ}
    (hf : P.funs[f]? = some (normIncTestF mem))
    (hm : P.HasAt mem (normMemFuns mem))
    (e : Fin n ≃ (Fin 1 → Product.KSet m k)) (x : Perm (Fin n))
    (i j : Fin m) (b : Fin n) :
    FunDet P f (.list [.list [encKSetTuples e, GI.Cited.encPerm x, .nat i, .nat j], .nat b])
      (boolVal (decide (i ∈ (e b 0).1 ↔ j ∈ (e (x b) 0).1)))
      (10000000 *
        ((Val.list [.list [encKSetTuples e, GI.Cited.encPerm x, .nat i, .nat j], .nat b]).wt +
          m + 1) ^ 3) := by
  let ctx := Val.list [encKSetTuples e, GI.Cited.encPerm x, .nat i, .nat j]
  let a := Val.list [ctx, .nat b]
  let W := a.wt
  have wc : ctx.wt < W := wt_le_wt_list (by simp)
  have wE : (encKSetTuples e).wt < W :=
    (wt_le_wt_list (by simp)).trans wc
  have wx : (GI.Cited.encPerm x).wt < W :=
    (wt_le_wt_list (by simp)).trans wc
  have hn : n < W := by
    have h := length_lt_wt_list ((List.finRange n).map fun z => Val.nat (x z))
    have heq : Val.list ((List.finRange n).map fun z : Fin n => Val.nat (x z)) =
        GI.Cited.encPerm x := rfl
    rw [heq] at h
    simp only [List.length_map, List.length_finRange] at h
    omega
  have dctx : ∀ rest, Det P (a :: rest) (arg 0) ctx (2 * W + 5) := fun rest =>
    Det.arg' (vs := [ctx, .nat b]) (rest := rest) rfl
  have db : ∀ rest, Det P (a :: rest) (arg 1) (.nat b) (2 * W + 6) := fun rest =>
    Det.arg' (vs := [ctx, .nat b]) (rest := rest) rfl
  have dE : ∀ rest, Det P (a :: rest) (.get (arg 0) (.nat 0)) (encKSetTuples e)
      (4 * W + 20) := fun rest =>
    (Det.get' (dctx rest) (Det.nat 0) rfl).mono (by omega)
  have dx : ∀ rest, Det P (a :: rest) (.get (arg 0) (.nat 1)) (GI.Cited.encPerm x)
      (4 * W + 20) := fun rest =>
    (Det.get' (dctx rest) (Det.nat 1) rfl).mono (by omega)
  have di : ∀ rest, Det P (a :: rest) (.get (arg 0) (.nat 2)) (.nat i)
      (4 * W + m + 20) := fun rest =>
    (Det.get' (dctx rest) (Det.nat 2) rfl).mono (by have := wt_nat_le (i : ℕ); have := i.2; omega)
  have dj : ∀ rest, Det P (a :: rest) (.get (arg 0) (.nat 3)) (.nat j)
      (4 * W + m + 20) := fun rest =>
    (Det.get' (dctx rest) (Det.nat 3) rfl).mono (by have := wt_nat_le (j : ℕ); have := j.2; omega)
  have dxb : ∀ rest, Det P (a :: rest) (.get (.get (arg 0) (.nat 1)) (arg 1)) (.nat (x b))
      (8 * W + 40) := fun rest =>
    (Det.get' (dx rest) (db rest) (encFun_getElem? (fun z => (x z : ℕ)) b)).mono
      (by have := wt_nat_le (x b : ℕ); have := (x b).2; omega)
  have dr : ∀ rest (t : Fin n) (expr : Expr) (ct : ℕ),
      Det P (a :: rest) expr (.nat t) ct →
      Det P (a :: rest) (.get (.get (.get (arg 0) (.nat 0)) expr) (.nat 0))
        (normSetVal (e t 0).1) (ct + 8 * W + 40) := by
    intro rest t expr ct dt
    obtain ⟨row, htable, hget, rfl⟩ := normTable_get e t
    have wr : (Val.list [normSetVal (e t 0).1]).wt < W := by
      have h := wt_getElem_lt ((List.finRange n).map fun z => Val.list [normSetVal (e z 0).1])
        t.val (by simp)
      have hr : ((List.finRange n).map fun z => Val.list [normSetVal (e z 0).1])[t.val] =
          Val.list [normSetVal (e t 0).1] := by simp
      rw [hr, ← htable] at h
      omega
    have ws : (normSetVal (e t 0).1).wt < W :=
      (wt_le_wt_list (by simp)).trans wr
    have dEt := dE rest
    rw [htable] at dEt
    exact (Det.get' (Det.get' dEt dt hget) (Det.nat 0) rfl).mono (by omega)
  have ds0 := dr [] b (arg 1) (2 * W + 6) (db [])
  have ds1 := dr [boolVal (decide (i ∈ (e b 0).1))] (x b)
    (.get (.get (arg 0) (.nat 1)) (arg 1)) (8 * W + 40) (dxb _)
  have c0 := Det.call (Det.mk2 (di []) ds0) (normMem_spec hm (e b 0).1 i)
  have c1 := Det.call (Det.mk2 (dj [boolVal (decide (i ∈ (e b 0).1))]) ds1)
    (normMem_spec hm (e (x b) 0).1 j)
  have deq := Det.arith' (op := .eq)
    (Det.var' (P := P) (env := [a, boolVal (decide (i ∈ (e b 0).1)),
      boolVal (decide (j ∈ (e (x b) 0).1))]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, boolVal (decide (i ∈ (e b 0).1)),
      boolVal (decide (j ∈ (e (x b) 0).1))]) (i := 2) rfl)
    (z := (decide (i ∈ (e b 0).1 ↔ j ∈ (e (x b) 0).1)).toNat) (by
      by_cases hi : i ∈ (e b 0).1 <;> by_cases hj : j ∈ (e (x b) 0).1 <;>
        simp [GI.Machine.BinOp.eval, hi, hj])
  refine FunDet.intro hf ((Det.letE c0 (Det.letE c1 deq)).mono ?_)
  have hS0 : (normSetVal (e b 0).1).wt < W := by
    obtain ⟨_, htable, -, -⟩ := normTable_get e b
    have h := wt_getElem_lt ((List.finRange n).map fun z => Val.list [normSetVal (e z 0).1])
      b.val (by simp)
    simp only [List.getElem_map, List.getElem_finRange] at h
    rw [← htable] at h
    exact (wt_le_wt_list (by simp)).trans (h.trans wE)
  have hS1 : (normSetVal (e (x b) 0).1).wt < W := by
    obtain ⟨_, htable, -, -⟩ := normTable_get e (x b)
    have h := wt_getElem_lt ((List.finRange n).map fun z => Val.list [normSetVal (e z 0).1])
      (x b).val (by simp)
    simp only [List.getElem_map, List.getElem_finRange] at h
    rw [← htable] at h
    exact (wt_le_wt_list (by simp)).trans (h.trans wE)
  have w0 := wt_list2_le (.nat i) (normSetVal (e b 0).1)
  have w1 := wt_list2_le (.nat j) (normSetVal (e (x b) 0).1)
  have wi := wt_nat_le (i : ℕ)
  have wj := wt_nat_le (j : ℕ)
  have hi := i.2
  have hj := j.2
  have wb0 := wt_boolVal_le (decide (i ∈ (e b 0).1))
  have wb1 := wt_boolVal_le (decide (j ∈ (e (x b) 0).1))
  have wb2 := wt_boolVal_le (decide (i ∈ (e b 0).1 ↔ j ∈ (e (x b) 0).1))
  have wb0' := wb0
  have wb1' := wb1
  have wb2' := wb2
  dsimp only [boolVal] at wb0 wb1 wb2
  have hb2 := Bool.toNat_le (decide (i ∈ (e b 0).1 ↔ j ∈ (e (x b) 0).1))
  have hm3 : (m + 1) ^ 3 ≤ (W + m + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hW3 : W + m + 1 ≤ (W + m + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  change _ ≤ 10000000 * (W + m + 1) ^ 3
  omega

end GI.Impl
