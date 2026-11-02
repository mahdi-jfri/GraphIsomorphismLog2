import Workspace.Impl.LinTabulate
import Workspace.Lang.Lib.LinIntVector
import Workspace.Proved.HNFRect

/-!
# The row reduction of the modular Hermite form, as a program

`hnfRed k m a g q` (`Workspace/Proved/HNFMod.lean`) is the row `a - q g`, with the entries right
of column `k` taken mod `m`. The program tabulates it entry by entry with the signed integer
library. Its argument is `[[k, m, a, g], q]`.

All integers in this file have absolute value below `2 ^ L`, and their products below
`2 ^ (2 L)`. The cost is stated with one number `X` that bounds `L`, the length of the rows and
the weight of the argument.
-/

namespace GI.Impl

open GI.Cited GI.Lang
open GI.Proved (hnfRed)

/-- The context `[k, m, a, g]` of a reduction. -/
def hnfCtx {n : ℕ} (k : ℕ) (m : ℤ) (a g : Fin n → ℤ) : Val :=
  .list [.nat k, encInt m, linVecVal a, linVecVal g]

/-- Entry `j` of an encoded row. -/
theorem hnf_vec_get {n : ℕ} (x : Fin n → ℤ) (j : Fin n) :
    ((List.finRange n).map fun i => encInt (x i))[(j : ℕ)]? = some (encInt (x j)) := by
  simp

/-- The weight of an integer below `2 ^ L`. -/
theorem hnf_wt_int {L : ℕ} {z : ℤ} (h : z.natAbs < 2 ^ L) : (encInt z).wt ≤ 20 * (L + 1) :=
  linWtInt h

/-- The bound on products. -/
theorem hnf_abs_mul {L : ℕ} {x y : ℤ} (hx : x.natAbs < 2 ^ L) (hy : y.natAbs < 2 ^ L) :
    (x * y).natAbs < 2 ^ (2 * L) := by
  rw [Int.natAbs_mul, show 2 * L = L + L by omega, pow_add]
  exact Nat.mul_lt_mul'' hx hy

/-- The bound on differences. -/
theorem hnf_abs_sub {L : ℕ} {x y : ℤ} (hx : x.natAbs < 2 ^ L) (hy : y.natAbs < 2 ^ L) :
    (x - y).natAbs < 2 ^ (L + 1) := by
  have := Int.natAbs_sub_le x y
  rw [pow_succ]
  omega

/-! ### One entry -/

/-- Entry `j` of `hnfRed`, on `[[[k, m, a, g], q], j]`. -/
def hnfRedCellF (ints : ℕ) : Expr :=
  .letE (.call (ints + 12) (mk2 (.get (.get (.get (arg 0) (.nat 0)) (.nat 2)) (arg 1))
      (.call (ints + 13) (mk2 (.get (arg 0) (.nat 1))
        (.get (.get (.get (arg 0) (.nat 0)) (.nat 3)) (arg 1))))))
    (.ite (.arith .lt (.get (.get (arg 0) (.nat 0)) (.nat 0)) (arg 1))
      (.call (ints + 15) (mk2 (.var 1) (.get (.get (arg 0) (.nat 0)) (.nat 1))))
      (.var 1))

/-- The cost of one entry. -/
def hnfRedCellCost (X : ℕ) : ℕ := 3 * linIntBinaryCost (1000 * (X + 1)) + 10000 * (X + 1)

set_option maxHeartbeats 2000000 in
theorem hnfRedCell_spec {P : Program} {ints f : ℕ} (hI : linIntSpec P ints)
    (hf : P.funs[f]? = some (hnfRedCellF ints)) {n : ℕ} (k : ℕ) (m : ℤ) (a g : Fin n → ℤ)
    (q : ℤ) (j : Fin n) {L X : ℕ} (hm : m.natAbs < 2 ^ L) (ha : (a j).natAbs < 2 ^ L)
    (hg : (g j).natAbs < 2 ^ L) (hq : q.natAbs < 2 ^ L)
    (hX : (Val.list [hnfCtx k m a g, encInt q]).wt + n + L ≤ X) :
    FunDet P f (.list [.list [hnfCtx k m a g, encInt q], .nat j])
      (encInt (hnfRed k m a g q j)) (hnfRedCellCost X) := by
  set c := Val.list [hnfCtx k m a g, encInt q] with hc
  have dc := fun rest => Det.arg' (P := P) (vs := [c, .nat j]) (rest := rest) (j := 0) rfl
  have dj := fun rest => Det.arg' (P := P) (vs := [c, .nat j]) (rest := rest) (j := 1) rfl
  have dctx := fun rest => Det.get' (dc rest) (Det.nat 0)
    (show [hnfCtx k m a g, encInt q][0]? = some (hnfCtx k m a g) from rfl)
  have dq := Det.get' (dc []) (Det.nat 1)
    (show [hnfCtx k m a g, encInt q][1]? = some (encInt q) from rfl)
  have da := Det.get' (Det.get' (dctx []) (Det.nat 2)
    (show [Val.nat k, encInt m, linVecVal a, linVecVal g][2]? = some (linVecVal a) from rfl))
    (dj []) (hnf_vec_get a j)
  have dg := Det.get' (Det.get' (dctx []) (Det.nat 3)
    (show [Val.nat k, encInt m, linVecVal a, linVecVal g][3]? = some (linVecVal g) from rfl))
    (dj []) (hnf_vec_get g j)
  have dmul := Det.call (Det.mk2 dq dg) (hI.mul q (g j))
  have dsub := Det.call (Det.mk2 da dmul) (hI.sub (a j) (q * g j))
  have dk := Det.get' (dctx [encInt (a j - q * g j)]) (Det.nat 0)
    (show [Val.nat k, encInt m, linVecVal a, linVecVal g][0]? = some (.nat k) from rfl)
  have dlt := Det.arith (op := .lt) dk (dj [encInt (a j - q * g j)])
  have dt := Det.var' (P := P) (env := [.list [c, .nat j], encInt (a j - q * g j)]) (i := 1) rfl
  have dmm := Det.get' (dctx [encInt (a j - q * g j)]) (Det.nat 1)
    (show [Val.nat k, encInt m, linVecVal a, linVecVal g][1]? = some (encInt m) from rfl)
  have drem := Det.call (Det.mk2 dt dmm) (hI.rem (a j - q * g j) m)
  simp only [GI.Machine.BinOp.eval_lt] at dlt
  have dite := Det.ite dlt (v := encInt (hnfRed k m a g q j))
    (fun h => by
      have hkj : k < (j : ℕ) := by by_contra h'; simp [h'] at h
      simpa [hnfRed, hkj] using drem)
    (fun h => by
      have hkj : ¬ k < (j : ℕ) := by intro h'; simp [h'] at h
      simpa [hnfRed, hkj] using dt)
  apply FunDet.intro hf
  refine (Det.letE dsub dite).mono ?_
  -- weights
  have wctx : (hnfCtx k m a g).wt < c.wt := wt_le_wt_list (by simp)
  have wqc : (encInt q).wt < c.wt := wt_le_wt_list (by simp)
  have wa : (linVecVal a).wt < (hnfCtx k m a g).wt := wt_le_wt_list (by simp)
  have wg : (linVecVal g).wt < (hnfCtx k m a g).wt := wt_le_wt_list (by simp)
  have wm : (encInt m).wt < (hnfCtx k m a g).wt := wt_le_wt_list (by simp)
  have wk : (Val.nat k).wt < (hnfCtx k m a g).wt := wt_le_wt_list (by simp)
  have waj := linVecEntryWt a j
  have wgj := linVecEntryWt g j
  have wj := wt_nat_le (j : ℕ)
  have hjn := j.isLt
  have wcj := wt_list2_le c (.nat j)
  have hqg := hnf_abs_mul hq hg
  have hqgL : (q * g j).natAbs < 2 ^ (2 * L + 1) :=
    hqg.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have haL : (a j).natAbs < 2 ^ (2 * L + 1) :=
    ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have htL := hnf_abs_sub haL hqgL
  have wqg := hnf_wt_int hqg
  have wt' := hnf_wt_int htL
  have hrem : ((a j - q * g j) % m).natAbs < 2 ^ (2 * L + 2) := by
    by_cases hm0 : m = 0
    · subst hm0; simpa using htL
    · have h1 := Int.emod_nonneg (a j - q * g j) hm0
      have h2 := Int.emod_lt (a j - q * g j) hm0
      have : ((a j - q * g j) % m).natAbs < m.natAbs := by omega
      exact this.trans (hm.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  have wr := hnf_wt_int hrem
  have wres : (encInt (hnfRed k m a g q j)).wt ≤ 20 * (2 * L + 2 + 1) := by
    unfold hnfRed
    split_ifs
    · exact wr
    · exact wt'.trans (by omega)
  have w1 := wt_list2_le (encInt q) (encInt (g j))
  have w2 := wt_list2_le (encInt (a j)) (encInt (q * g j))
  have w3 := wt_list2_le (encInt (a j - q * g j)) (encInt m)
  have c1 := linIntBinaryCost_mono (show (Val.list [encInt q, encInt (g j)]).wt ≤
    1000 * (X + 1) by omega)
  have c2 := linIntBinaryCost_mono (show (Val.list [encInt (a j), encInt (q * g j)]).wt ≤
    1000 * (X + 1) by omega)
  have c3 := linIntBinaryCost_mono (show (Val.list [encInt (a j - q * g j), encInt m]).wt ≤
    1000 * (X + 1) by omega)
  have wqgX : (encInt (q * g j)).wt ≤ 100 * (X + 1) := by omega
  have wtX : (encInt (a j - q * g j)).wt ≤ 100 * (X + 1) := by omega
  have wrX : (encInt (hnfRed k m a g q j)).wt ≤ 100 * (X + 1) := by omega
  have ww : (Val.list [c, .nat j]).wt ≤ 2 * X + 10 := by omega
  have e1 : (Val.list ((List.finRange n).map fun i => encInt (a i))).wt = (linVecVal a).wt := rfl
  have e2 : (Val.list ((List.finRange n).map fun i => encInt (g i))).wt = (linVecVal g).wt := rfl
  have e3 : (Val.nat 1).wt = 3 := rfl
  have e4 : (Val.nat 0).wt = 2 := rfl
  unfold hnfRedCellCost
  rw [max_def]
  split_ifs <;> omega

/-! ### The whole row -/

/-- `hnfRed`, on `[[k, m, a, g], q]`: tabulate the entries. -/
def hnfRedF (tab : ℕ) : Expr :=
  .call tab (mk2 (.var 0) (.length (.get (.get (.var 0) (.nat 0)) (.nat 2))))

/-- The functions of the reduction at base `b`. -/
def hnfRedFuns (b ints : ℕ) : List Expr :=
  [hnfRedF (b + 1)] ++ linTabulateFuns (b + 1) (b + 8) ++ [hnfRedCellF ints]

theorem hnfRedFuns_length (b ints : ℕ) : (hnfRedFuns b ints).length = 9 := rfl

/-- The reduction is installed at `b`. -/
structure hnfRedAt (P : Program) (b ints : ℕ) : Prop where
  hI : linIntSpec P ints
  entry : P.funs[b]? = some (hnfRedF (b + 1))
  tab : linTabulateAt P (b + 1) (b + 8)
  cell : P.funs[b + 8]? = some (hnfRedCellF ints)

theorem hnfRedAt_of {P : Program} {b ints : ℕ} (hI : linIntSpec P ints)
    (h : P.HasAt b (hnfRedFuns b ints)) : hnfRedAt P b ints where
  hI := hI
  entry := (h.block (gs := [hnfRedF (b + 1)]) 0 rfl).single
  tab := linTabulateAt_of (h.block 1 rfl)
  cell := (h.block (gs := [hnfRedCellF ints]) 8 rfl).single

/-- The cost of the reduction. -/
def hnfRedCost (X : ℕ) : ℕ :=
  2 * linTabulateCost (4 * X + 20) X (hnfRedCellCost X) + 100 * (X + 1)

set_option maxHeartbeats 1000000 in
theorem hnfRed_spec {P : Program} {b ints : ℕ} (h : hnfRedAt P b ints) {n : ℕ} (k : ℕ) (m : ℤ)
    (a g : Fin n → ℤ) (q : ℤ) {L X : ℕ} (hm : m.natAbs < 2 ^ L)
    (ha : ∀ j, (a j).natAbs < 2 ^ L) (hg : ∀ j, (g j).natAbs < 2 ^ L) (hq : q.natAbs < 2 ^ L)
    (hX : (Val.list [hnfCtx k m a g, encInt q]).wt + n + L ≤ X) :
    FunDet P b (.list [hnfCtx k m a g, encInt q]) (linVecVal (hnfRed k m a g q))
      (hnfRedCost X) := by
  set c := Val.list [hnfCtx k m a g, encInt q] with hc
  have ht := linTabulate_spec h.tab c (fun j : Fin n => encInt (hnfRed k m a g q j))
    (hnfRedCellCost X) (fun j => hnfRedCell_spec h.hI h.cell k m a g q j hm (ha j) (hg j) hq hX)
  have dctx := Det.get' (Det.var' (P := P) (env := [c]) (i := 0) rfl) (Det.nat 0)
    (show [hnfCtx k m a g, encInt q][0]? = some (hnfCtx k m a g) from rfl)
  have dl := Det.length (Det.get' dctx (Det.nat 2)
    (show [Val.nat k, encInt m, linVecVal a, linVecVal g][2]? =
      some (.list ((List.finRange n).map fun i => encInt (a i))) from rfl))
  simp only [List.length_map, List.length_finRange] at dl
  have dout := Det.call (Det.mk2 (Det.var' (P := P) (env := [c]) (i := 0) rfl) dl) ht
  apply FunDet.intro h.entry
  refine dout.mono ?_
  have wo := ht.wt_lt
  have wctx : (hnfCtx k m a g).wt < c.wt := wt_le_wt_list (by simp)
  have wa : (linVecVal a).wt < (hnfCtx k m a g).wt := wt_le_wt_list (by simp)
  have w2 := wt_list2_le c (.nat n)
  have wn := wt_nat_le n
  have e1 : (Val.list ((List.finRange n).map fun i => encInt (a i))).wt = (linVecVal a).wt := rfl
  have e2 : (Val.nat 0).wt = 2 := rfl
  have e3 : (Val.nat 2).wt = 4 := rfl
  have hm := linTabulateCost_mono (show (Val.list [c, .nat n]).wt ≤ 4 * X + 20 by omega)
    (show n ≤ X by omega) (le_refl (hnfRedCellCost X))
  have e4 : (Val.list ((List.finRange n).map fun j => encInt (hnfRed k m a g q j))).wt =
    (linVecVal (hnfRed k m a g q)).wt := rfl
  have e5 : (Val.list [hnfCtx k m a g, encInt q]).wt = c.wt := rfl
  unfold hnfRedCost
  omega

/-! ### Euclid's algorithm -/

/-- A pair of rows. -/
def hnfPairVal {n : ℕ} (p : (Fin n → ℤ) × (Fin n → ℤ)) : Val := .list [linVecVal p.1, linVecVal p.2]

/-- Euclid's algorithm on `[k, m, a, g]`, with `red` the reduction and `quo` the quotient. -/
def hnfEucF (self red quo : ℕ) : Expr :=
  .letE (.get (arg 3) (arg 0))
    (.ite (.length (.get (.var 1) (.nat 1)))
      (.call self (mk4 (arg 0) (arg 1) (arg 3)
        (.call red (mk2 (.var 0) (.call quo (mk2 (.get (arg 2) (arg 0)) (.var 1)))))))
      (mk2 (arg 2) (arg 3)))

/-- The potential of a pair: it drops at every step of Euclid's algorithm. -/
def hnfPot {n : ℕ} (k : Fin n) (a g : Fin n → ℤ) : ℕ :=
  Nat.size (a k).toNat + Nat.size (g k).toNat + if a k ≤ g k then 1 else 0

theorem hnf_two_mod_lt {a g : ℤ} (hg : 0 < g) (hga : g < a) : 2 * (a % g) < a := by
  have h1 := Int.emod_add_mul_ediv a g
  have h2 : 1 ≤ a / g := Int.le_ediv_of_mul_le hg (by omega)
  have h3 : g * 1 ≤ g * (a / g) := mul_le_mul_of_nonneg_left h2 hg.le
  have h4 := Int.emod_lt_of_pos a hg
  omega

theorem hnf_size_lt {r a : ℕ} (ha : 0 < a) (h : 2 * r < a) : Nat.size r < Nat.size a := by
  have h1 := Nat.lt_size_self a
  have h2 : 0 < Nat.size a := Nat.size_pos.mpr ha
  have h3 : r < 2 ^ (Nat.size a - 1) := by
    have : 2 ^ Nat.size a = 2 * 2 ^ (Nat.size a - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have := Nat.size_le.mpr h3
  omega

/-- The potential drops in one step. -/
theorem hnfPot_step {n : ℕ} (k : Fin n) {a g a' : Fin n → ℤ} (ha : 0 < a k) (hg : 0 < g k)
    (ha' : a' k = a k % g k) : hnfPot k g a' < hnfPot k a g := by
  unfold hnfPot
  rw [ha']
  have h0 := Int.emod_nonneg (a k) hg.ne'
  have h1 := Int.emod_lt_of_pos (a k) hg
  rcases lt_trichotomy (g k) (a k) with hlt | heq | hgt
  · have h2 := hnf_two_mod_lt hg hlt
    have h3 := hnf_size_lt (a := (a k).toNat) (r := (a k % g k).toNat) (by omega) (by omega)
    rw [if_neg (by omega), if_neg (by omega)]
    omega
  · rw [heq, Int.emod_self, if_pos le_rfl, if_neg (by omega)]
    have : 0 < Nat.size (a k).toNat := Nat.size_pos.mpr (by omega)
    simp
  · rw [Int.emod_eq_of_lt ha.le hgt, if_pos hgt.le, if_neg (by omega)]
    omega

/-- One step keeps the shape of the pair. -/
theorem hnfPair_step {n : ℕ} (k : Fin n) {m : ℤ} (hm : 0 < m) {a g : Fin n → ℤ}
    (hp : GI.Proved.HnfPair k m a g) (hg : g k ≠ 0) :
    GI.Proved.HnfPair k m g (hnfRed k m a g (a k / g k)) ∧
      hnfRed k m a g (a k / g k) k = a k % g k := by
  have hkey : hnfRed k m a g (a k / g k) k = a k % g k := by
    rw [GI.Proved.hnfRed_key, mul_comm, ← Int.emod_def]
  have hgpos : 0 < g k := lt_of_le_of_ne hp.gkey.1 (Ne.symm hg)
  refine ⟨⟨fun j hj => ⟨(hp.low j hj).2, ?_⟩, ⟨hgpos, hp.gkey.2.le⟩, ?_,
    fun j hj => ⟨(hp.high j hj).2, ?_⟩⟩, hkey⟩
  · simp [hnfRed, show ¬ (k : ℕ) < j by omega, (hp.low j hj).1, (hp.low j hj).2]
  · rw [hkey]
    exact ⟨Int.emod_nonneg _ hg, (Int.emod_lt_of_pos _ hgpos).trans hp.gkey.2⟩
  · simp only [hnfRed, if_pos hj]
    exact ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩

/-- The entries of a pair lie in `[0, m]`. -/
theorem hnfPair_bound {n : ℕ} {k : Fin n} {m : ℤ} {a g : Fin n → ℤ}
    (hp : GI.Proved.HnfPair k m a g) (j : Fin n) :
    (0 ≤ a j ∧ a j ≤ m) ∧ (0 ≤ g j ∧ g j ≤ m) := by
  rcases lt_trichotomy (j : ℕ) k with h | h | h
  · rw [(hp.low j h).1, (hp.low j h).2]
    have := hp.akey; omega
  · rw [show j = k from Fin.ext h]
    have := hp.akey; have := hp.gkey; omega
  · have := hp.high j h; omega

/-! ### Weights -/

theorem hnf_vec_wt {n L : ℕ} (x : Fin n → ℤ) (h : ∀ j, (x j).natAbs < 2 ^ L) :
    (linVecVal x).wt ≤ 45 * ((n + 1) * (L + 1)) := by
  have h1 := linWtList (vs := (List.finRange n).map fun i => encInt (x i)) (B := 20 * (L + 1))
    (by
      intro v hv
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
      exact hnf_wt_int (h j))
  simp only [List.length_map, List.length_finRange] at h1
  have e : (Val.list ((List.finRange n).map fun i => encInt (x i))).wt = (linVecVal x).wt := rfl
  have h2 : n * (20 * (L + 1)) = 20 * (n * (L + 1)) := by ring
  have h3 : n * (L + 1) ≤ (n + 1) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
  have h4 : n + 1 ≤ (n + 1) * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem hnf_entry_lt {m z : ℤ} {L : ℕ} (h0 : 0 ≤ z) (h1 : z ≤ m) (hm : m.natAbs < 2 ^ L) :
    z.natAbs < 2 ^ L := by
  have := Int.natAbs_of_nonneg h0
  have := Int.natAbs_of_nonneg (h0.trans h1)
  omega

/-- The weight of the argument of a reduction. -/
theorem hnf_redArg_wt {n L : ℕ} (k : ℕ) (hk : k < n) (m : ℤ) (a g : Fin n → ℤ) (q : ℤ)
    (hm : m.natAbs < 2 ^ L) (ha : ∀ j, (a j).natAbs < 2 ^ L) (hg : ∀ j, (g j).natAbs < 2 ^ L)
    (hq : q.natAbs < 2 ^ L) :
    (Val.list [hnfCtx k m a g, encInt q]).wt + n + L ≤ 1000 * ((n + 1) * (L + 1)) := by
  have w1 := hnf_vec_wt a ha
  have w2 := hnf_vec_wt g hg
  have w3 := hnf_wt_int hm
  have w4 := hnf_wt_int hq
  have w5 := wt_nat_le k
  have w6 := wt_list4_le (.nat k) (encInt m) (linVecVal a) (linVecVal g)
  have w7 := wt_list2_le (hnfCtx k m a g) (encInt q)
  have e : (Val.list [.nat k, encInt m, linVecVal a, linVecVal g]).wt = (hnfCtx k m a g).wt := rfl
  have h4 : n + 1 ≤ (n + 1) * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h5 : L + 1 ≤ (n + 1) * (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- The weight of a pair with entries in `[0, m]`. -/
theorem hnf_pairVal_wt {n L : ℕ} {m : ℤ} {a g : Fin n → ℤ} (hm : m.natAbs < 2 ^ L)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ m) (hg : ∀ j, 0 ≤ g j ∧ g j ≤ m) :
    (hnfPairVal (a, g)).wt ≤ 200 * ((n + 1) * (L + 1)) := by
  have w1 := hnf_vec_wt a fun j => hnf_entry_lt (ha j).1 (ha j).2 hm
  have w2 := hnf_vec_wt g fun j => hnf_entry_lt (hg j).1 (hg j).2 hm
  have w3 := wt_list2_le (linVecVal a) (linVecVal g)
  have e : (Val.list [linVecVal a, linVecVal g]).wt = (hnfPairVal (a, g)).wt := rfl
  have h4 : 1 ≤ (n + 1) * (L + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

/-! ### Euclid's algorithm as a program -/

/-- Euclid's algorithm is installed at `e`. -/
structure hnfEucAt (P : Program) (e red ints : ℕ) : Prop where
  hR : hnfRedAt P red ints
  entry : P.funs[e]? = some (hnfEucF e red (ints + 14))

/-- The cost of one step of Euclid's algorithm. -/
def hnfEucStepCost (X : ℕ) : ℕ :=
  hnfRedCost X + linIntBinaryCost (1000 * (X + 1)) + 10000 * (X + 1)

theorem hnfEuclid_zero {n : ℕ} (k : Fin n) (m : ℤ) (a g : Fin n → ℤ) (hg : g k = 0) :
    GI.Proved.hnfEuclid k m a g = (a, g) := by
  conv_lhs => unfold GI.Proved.hnfEuclid
  rw [dif_pos hg]

theorem hnfEuclid_ne {n : ℕ} (k : Fin n) (m : ℤ) (a g : Fin n → ℤ) (hg : g k ≠ 0) :
    GI.Proved.hnfEuclid k m a g = GI.Proved.hnfEuclid k m g (hnfRed k m a g (a k / g k)) := by
  conv_lhs => unfold GI.Proved.hnfEuclid
  rw [dif_neg hg]

set_option maxHeartbeats 4000000 in
theorem hnfEuc_spec_aux {P : Program} {e red ints : ℕ} (h : hnfEucAt P e red ints) {n : ℕ}
    (k : Fin n) {m : ℤ} {L X : ℕ} (hm0 : 0 < m) (hmL : m.natAbs < 2 ^ L)
    (hX : 1000 * ((n + 1) * (L + 1)) ≤ X) :
    ∀ N (a g : Fin n → ℤ), GI.Proved.HnfPair k m a g → hnfPot k a g ≤ N →
      FunDet P e (hnfCtx k m a g) (hnfPairVal (GI.Proved.hnfEuclid k m a g))
        ((N + 1) * hnfEucStepCost X) := by
  have hI := h.hR.hI
  intro N
  induction N with
  | zero =>
    intro a g hp hN
    have : 0 < Nat.size (a k).toNat := Nat.size_pos.mpr (by have := hp.akey; omega)
    unfold hnfPot at hN
    omega
  | succ N ih =>
  intro a g hp hN
  have hab := fun j => hnfPair_bound hp j
  have hal : ∀ j, (a j).natAbs < 2 ^ L := fun j => hnf_entry_lt (hab j).1.1 (hab j).1.2 hmL
  have hgl : ∀ j, (g j).natAbs < 2 ^ L := fun j => hnf_entry_lt (hab j).2.1 (hab j).2.2 hmL
  have hres := GI.Proved.hnfEuclid_spec k hm0 _ a g rfl hp
  have wres := hnf_pairVal_wt (L := L) hmL (fun j => (hnfPair_bound hres.1 j).1)
    (fun j => (hnfPair_bound hres.1 j).2)
  have wctx := hnf_redArg_wt (k : ℕ) k.isLt m a g 0 hmL hal hgl (by simp)
  have w1 := hnf_wt_int (hgl k)
  have dgk := Det.get' (Det.arg' (P := P) (vs := [Val.nat k, encInt m, linVecVal a, linVecVal g])
    (rest := []) (j := 3) rfl) (Det.arg' (j := 0) rfl) (hnf_vec_get g k)
  set env2 := [hnfCtx k m a g, encInt (g k)] with henv2
  have dlen := Det.length (Det.get' (Det.var' (P := P) (env := env2) (i := 1)
    (v := .list [.nat (if g k < 0 then 1 else 0),
      .list ((Nat.bits (g k).natAbs).map fun b => .nat (if b then 1 else 0))]) rfl) (Det.nat 1)
    (show [Val.nat (if g k < 0 then 1 else 0),
      .list ((Nat.bits (g k).natAbs).map fun b => .nat (if b then 1 else 0))][1]? =
      some (.list ((Nat.bits (g k).natAbs).map fun b => .nat (if b then 1 else 0))) from rfl))
  simp only [List.length_map] at dlen
  have e1 : (encInt (g k)).wt = (Val.list [.nat (if g k < 0 then 1 else 0),
      .list ((Nat.bits (g k).natAbs).map fun b => .nat (if b then 1 else 0))]).wt := rfl
  have wb : (Val.list ((Nat.bits (g k).natAbs).map fun b => .nat (if b then 1 else 0))).wt <
      (encInt (g k)).wt := wt_le_wt_list (by simp)
  have wlen := length_lt_wt_list ((Nat.bits (g k).natAbs).map fun b => Val.nat (if b then 1 else 0))
  simp only [List.length_map] at wlen
  have e2 : (hnfCtx k m a g).wt = (Val.list [.nat k, encInt m, linVecVal a, linVecVal g]).wt := rfl
  have wk := wt_nat_le (k : ℕ)
  have hkn := k.isLt
  have wgv : (linVecVal g).wt < (hnfCtx k m a g).wt := wt_le_wt_list (by simp)
  have wav : (linVecVal a).wt < (hnfCtx k m a g).wt := wt_le_wt_list (by simp)
  have wmv : (encInt m).wt < (hnfCtx k m a g).wt := wt_le_wt_list (by simp)
  have wkv : (Val.nat k).wt < (hnfCtx k m a g).wt := wt_le_wt_list (by simp)
  have wpair : (hnfCtx k m a g).wt < (Val.list [hnfCtx k m a g, encInt 0]).wt :=
    wt_le_wt_list (by simp)
  have hS : 10000 * (X + 1) ≤ hnfEucStepCost X := by unfold hnfEucStepCost; omega
  have ex : (N + 1 + 1) * hnfEucStepCost X = (N + 1) * hnfEucStepCost X + hnfEucStepCost X := by
    ring
  by_cases hg : g k = 0
  · -- the zero branch
    have hlen0 : (g k).natAbs.bits.length = 0 := (linIntBits_zero_iff _).mpr hg
    rw [hlen0] at dlen
    have dout := Det.mk2 (Det.arg' (P := P) (vs := [Val.nat k, encInt m, linVecVal a, linVecVal g])
      (rest := [encInt (g k)]) (j := 2) rfl) (Det.arg' (j := 3) rfl)
    have dite := Det.ite_zero (t := .call e (mk4 (arg 0) (arg 1) (arg 3)
        (.call red (mk2 (.var 0) (.call (ints + 14) (mk2 (.get (arg 2) (arg 0)) (.var 1)))))))
      dlen dout
    rw [hnfEuclid_zero k m a g hg]
    apply FunDet.intro h.entry
    refine (Det.letE dgk dite).mono ?_
    have e3 : (Val.list [linVecVal a, linVecVal g]).wt = (hnfPairVal (a, g)).wt := rfl
    rw [hnfEuclid_zero k m a g hg] at wres
    have wres' : (hnfPairVal (a, g)).wt ≤ 200 * ((n + 1) * (L + 1)) := wres
    have w2 := wt_list2_le (linVecVal a) (linVecVal g)
    rw [ex]
    generalize (N + 1) * hnfEucStepCost X = Z at *
    omega
  · -- the step
    obtain ⟨hp', hkey⟩ := hnfPair_step k hm0 hp hg
    have hgpos : 0 < g k := lt_of_le_of_ne hp.gkey.1 (Ne.symm hg)
    have hpot := hnfPot_step k hp.akey.1 hgpos hkey
    set a' := hnfRed k m a g (a k / g k) with ha'
    have hrec := ih g a' hp' (by omega)
    have hq : (a k / g k).natAbs < 2 ^ L := by
      have h1 := Int.ediv_nonneg (hab k).1.1 hgpos.le
      have h2 := Int.ediv_le_self (g k) (hab k).1.1
      exact hnf_entry_lt h1 (h2.trans (hab k).1.2) hmL
    have hXr := hnf_redArg_wt (k : ℕ) k.isLt m a g (a k / g k) hmL hal hgl hq
    have dred0 := hnfRed_spec h.hR (k : ℕ) m a g (a k / g k) hmL hal hgl hq
      (hXr.trans hX)
    have dak := Det.get' (Det.arg' (P := P) (vs := [Val.nat k, encInt m, linVecVal a, linVecVal g])
      (rest := [encInt (g k)]) (j := 2) rfl) (Det.arg' (j := 0) rfl) (hnf_vec_get a k)
    have dv1 := Det.var' (P := P) (env := env2) (i := 1) rfl
    have dquo := Det.call (Det.mk2 dak dv1) (hI.quo (a k) (g k))
    have dv0 := Det.var' (P := P) (env := env2) (i := 0) rfl
    have dred := Det.call (Det.mk2 dv0 dquo) dred0
    have dmk := Det.mk4 (Det.arg' (P := P) (vs := [Val.nat k, encInt m, linVecVal a, linVecVal g])
      (rest := [encInt (g k)]) (j := 0) rfl) (Det.arg' (j := 1) rfl) (Det.arg' (j := 3) rfl) dred
    have drec := Det.call dmk hrec
    have hlen : (g k).natAbs.bits.length ≠ 0 := fun h0 => hg ((linIntBits_zero_iff _).mp h0)
    have dite := Det.ite_pos (e := mk2 (arg 2) (arg 3)) dlen hlen drec
    rw [hnfEuclid_ne k m a g hg]
    apply FunDet.intro h.entry
    refine (Det.letE dgk dite).mono ?_
    rw [hnfEuclid_ne k m a g hg] at wres
    have wres' : (hnfPairVal (GI.Proved.hnfEuclid k m g a')).wt ≤ 200 * ((n + 1) * (L + 1)) := wres
    have eA : (linVecVal (hnfRed (↑k) m a g (a k / g k))).wt = (linVecVal a').wt := rfl
    have eB : (Val.list [Val.nat ↑k, encInt m, linVecVal g,
      linVecVal (hnfRed (↑k) m a g (a k / g k))]).wt = (hnfCtx k m g a').wt := rfl
    have wa' := hnf_vec_wt a' fun j => hnf_entry_lt (hnfPair_bound hp' j).2.1
      (hnfPair_bound hp' j).2.2 hmL
    have wq := hnf_wt_int hq
    have wak := hnf_wt_int (hal k)
    have w3 := wt_list2_le (encInt (a k)) (encInt (g k))
    have c1 := linIntBinaryCost_mono (show (Val.list [encInt (a k), encInt (g k)]).wt ≤
      1000 * (X + 1) by omega)
    have w4 := wt_list2_le (hnfCtx k m a g) (encInt (a k / g k))
    have w5 := wt_list4_le (.nat k) (encInt m) (linVecVal g) (linVecVal a')
    have e4 : (Val.list [.nat k, encInt m, linVecVal g, linVecVal a']).wt =
      (hnfCtx k m g a').wt := rfl
    rw [ex]
    generalize (N + 1) * hnfEucStepCost X = Z at *
    unfold hnfEucStepCost at hS ⊢
    omega

/-- **Euclid's algorithm as a program.** On a pair of the shape `HnfPair` with `m < 2 ^ L`, it
makes at most `2 L + 2` steps. -/
theorem hnfEuc_spec {P : Program} {e red ints : ℕ} (h : hnfEucAt P e red ints) {n : ℕ}
    (k : Fin n) {m : ℤ} {L X : ℕ} (hm0 : 0 < m) (hmL : m.natAbs < 2 ^ L)
    (hX : 1000 * ((n + 1) * (L + 1)) ≤ X) (a g : Fin n → ℤ) (hp : GI.Proved.HnfPair k m a g) :
    FunDet P e (hnfCtx k m a g) (hnfPairVal (GI.Proved.hnfEuclid k m a g))
      ((2 * L + 2) * hnfEucStepCost X) := by
  have hab := hnfPair_bound hp k
  have hs : ∀ z : ℤ, 0 ≤ z → z ≤ m → Nat.size z.toNat ≤ L := fun z h0 h1 => by
    apply Nat.size_le.mpr
    have := Int.natAbs_of_nonneg (h0.trans h1)
    omega
  have hpot : hnfPot k a g ≤ 2 * L + 1 := by
    unfold hnfPot
    have := hs _ hab.1.1 hab.1.2
    have := hs _ hab.2.1 hab.2.2
    split_ifs <;> omega
  exact hnfEuc_spec_aux h k hm0 hmL hX _ a g hp hpot

end GI.Impl
