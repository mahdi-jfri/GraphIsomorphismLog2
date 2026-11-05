module

public import Workspace.Impl.SmallZ
public import Workspace.Lang.Prims.Other
public import Workspace.Lang.Prims.PermGroups
public import Workspace.Algorithm.SupplyBuild

@[expose] public section

/-!
# The case decision of the general dispatcher

Algorithm 5, `Continue` off the floor: the dispatcher has a primitive quotient `Q` of the state
(degree `d`, block action `ρ`) and must decide which reduction applies. Section 3.3: "The
standard primitive-group reduction either enumerates a group of order `d^{O(log d)}` on an
actual `d`-block quotient, or exposes a large alternating action". The program decides as
follows.

1. If `d < 25`, the quotient is small (`small_of_lt_25`): enumerate.
2. Otherwise it computes `|ρ(G)|` with the cited **GroupOrder** and runs the integer small test
   `SmallZ` (`smallZ_spec_P₀`). If the test holds, the quotient is small (`small_of_smallZ`):
   enumerate.
3. Otherwise it calls the cited **Cameron recognition** on `ρ(G)`. Its preconditions hold: `ρ(G)`
   is primitive (`PrimitiveQuotient.primitive`) and `d ≥ 25` (step 1).
   * `[0]`: `|ρ(G)| < d^(1 + ⌊log₂ d⌋)`, which passes the integer test, so this output does not
     occur here; the program enumerates.
   * `[2]`: a structure in the Cameron range; the quotient is small
     (`small_of_cameron_range`): enumerate.
   * `[1, m, k, r, E]`: a Maróti structure with `r ≥ 1` coordinates. The program returns it.
     If `r ≥ 2` the dispatcher refines the product; if `r = 1` it normalizes. In both cases the
     quotient fails the integer test (step 2).

`case_spec`: the function `caseF` on `[d, gv]`, where `gv` is a group value of `ρ(G)`, returns
`[0]` with `Q.Small a`, or the Cameron output `[1, m, k, r, E]` with a product structure `e` of
`Q` (`E = encKSetTuples e`), `r ≥ 1`, and `¬ SmallZ`. The cost is the two cited calls, the
integer test, and an overhead linear in the input and the output (`caseCost` plus ten times the
weight of the output).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encGroup gens GroupOrder CameronRecognition encKSetTuples MarotiStructure)

/-- The body of the case decision on `[d, gv]` (see the module docstring). `sz` is the index of
the integer small test, `jo` and `jc` the primitives of **GroupOrder** and **Cameron
recognition**. -/
def caseBody (sz jo jc : ℕ) : Expr :=
  .ite (.arith .lt (arg 0) (.nat 25)) (mk1 (.nat 0))
    (.letE (.prim jo (arg 1))
    (.letE (.call sz (mk2 (.var 1) (arg 0)))
    (.ite (.var 2) (mk1 (.nat 0))
    (.letE (.prim jc (arg 1))
    (.ite (.arith .eq (.get (.var 3) (.nat 0)) (.nat 1)) (.var 3) (mk1 (.nat 0)))))))

variable {Ω C : Type} {S : State Ω C}

/-- **What the case decision returns**: `[0]` for a small quotient, or a Maróti structure
`[1, m, k, r, E]` with `r ≥ 1` of a quotient that fails the integer small test. -/
def CaseOut (Q : PrimitiveQuotient S) (w : Val) : Prop :=
  (w = .list [.nat 0] ∧ Q.Small P₀.a) ∨
  (∃ (m k r : ℕ) (e : Fin Q.d ≃ (Fin r → Product.KSet m k)),
    w = .list [.nat 1, .nat m, .nat k, .nat r, encKSetTuples e] ∧ Q.ProductStructure m k r e ∧
      1 ≤ r ∧ ¬ Q.SmallZ P₀.smallExp)

/-- The cost bound of the integer small test on `[|ρ(G)|, d]`. -/
def caseZ (d : ℕ) : ℕ := smallZK * (2 * d ^ 2 + 2 * d + 24955 * d + 25000) ^ 2

/-- The cost bound of the case decision on `[d, gv]`. -/
noncomputable def caseCost (hO : GroupOrder) (hC : CameronRecognition) (gv : Val) (d : ℕ) : ℕ :=
  (groupOrderPrim hO).bound gv + (cameronRecognitionPrim hC).bound gv + caseZ d +
    400 * (gv.wt + d + 40) + 10 * d ^ 2

/-- A Maróti structure of `ρ(G)` is a product structure of the quotient. -/
theorem _root_.GI.Algorithm.PrimitiveQuotient.productStructure_of_maroti
    (Q : PrimitiveQuotient S) {m k r : ℕ} {e : Fin Q.d ≃ (Fin r → Product.KSet m k)}
    (h : MarotiStructure Q.ρ.range e) : Q.ProductStructure m k r e := ⟨h.1, h.2⟩

/-- A product structure has at least one coordinate. -/
theorem _root_.GI.Algorithm.PrimitiveQuotient.one_le_r (Q : PrimitiveQuotient S) {m k r : ℕ} (e : Fin Q.d ≃ (Fin r → Product.KSet m k)) : 1 ≤ r := by
  have hd := Q.card_kset_pow e
  have := Q.two_le
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp at hd; omega
  · exact h

/-- **The Cameron output `[0]` passes the integer small test** for `d ≥ 25`: with
`L = ⌊log₂ d⌋ ≥ 4`, `1 + L ≤ b L` for `b ≥ 2`. -/
theorem _root_.GI.Algorithm.PrimitiveQuotient.smallZ_of_cameron_zero (Q : PrimitiveQuotient S)
    (hd : 25 ≤ Q.d)
    (h : Nat.card Q.ρ.range < Q.d ^ (1 + Nat.log 2 Q.d)) : Q.SmallZ P₀.smallExp := by
  unfold PrimitiveQuotient.SmallZ
  rw [P₀_smallExp]
  have hL : 1 ≤ Nat.log 2 Q.d := Nat.le_log_of_pow_le (by norm_num) (by simp; omega)
  refine h.le.trans (Nat.pow_le_pow_right (by omega) ?_)
  nlinarith

open Classical in
/-- **The case decision meets its specification.** -/
theorem case_spec (hO : GroupOrder) (hC : CameronRecognition) {P : Program} {f sz jo jc : ℕ}
    (hf : P.funs[f]? = some (caseBody sz jo jc)) (hsz : P.HasAt sz (smallZFuns sz 24953))
    (hjo : P.prims[jo]? = some (groupOrderPrim hO))
    (hjc : P.prims[jc]? = some (cameronRecognitionPrim hC))
    (Q : PrimitiveQuotient S) {gv : Val} (hgv : GroupVal Q.d gv Q.ρ.range) :
    FunAll P f (.list [.nat Q.d, gv]) (fun w c => CaseOut Q w ∧
      c ≤ caseCost hO hC gv Q.d + 10 * w.wt) := by
  set x := Val.list [.nat Q.d, gv] with hx
  have wx : x.wt ≤ 2 * (Q.d + 2 + gv.wt) + 6 := by
    rw [hx]
    have := wt_list2_le (.nat Q.d) gv
    have := wt_nat_le Q.d
    omega
  have g0 : ∀ rest, Det P (x :: rest) (arg 0) (.nat Q.d) (2 * x.wt + 0 + 5) := fun rest =>
    Det.arg' (vs := [.nat Q.d, gv]) rfl
  have g1 : ∀ rest, Det P (x :: rest) (arg 1) gv (2 * x.wt + 1 + 5) := fun rest =>
    Det.arg' (vs := [.nat Q.d, gv]) rfl
  have w0 : (Val.list [.nat 0]).wt ≤ 9 := by
    have := wt_list1_le (.nat 0); have := wt_nat_le 0; omega
  have hcc : 400 * (gv.wt + Q.d + 40) ≤ caseCost hO hC gv Q.d := by
    unfold caseCost
    generalize (groupOrderPrim hO).bound gv = A
    generalize (cameronRecognitionPrim hC).bound gv = B
    generalize caseZ Q.d = Z
    generalize Q.d ^ 2 = D
    omega
  have hcost0 : ∀ {c : ℕ}, c ≤ 100 * (x.wt + 10) → c ≤ caseCost hO hC gv Q.d := by
    intro c hc
    clear_value x
    omega
  refine FunAll.intro hf ?_
  unfold caseBody
  have dlt := Det.arith' (op := .lt) (g0 []) (Det.nat (P := P) (env := [x]) 25) rfl
  refine EvalAll.ite dlt (fun _ _ h => ⟨_, h.1⟩) fun t ct ht => ?_
  obtain ⟨ht, hct⟩ := ht
  injection ht with ht
  subst ht
  by_cases hd : Q.d < 25
  · -- 1. small degree
    have h1 : GI.Machine.BinOp.eval .lt Q.d 25 = 1 := by
      show (if Q.d < 25 then 1 else 0) = 1; rw [if_pos hd]
    rw [h1, if_neg one_ne_zero]
    refine (Det.mk1 (Det.nat (P := P) (env := [x]) 0)).post fun c hc => ⟨Or.inl ⟨rfl,
      Q.small_of_lt_25 P₀_a hd⟩, ?_⟩
    have := wt_nat_le (GI.Machine.BinOp.eval .lt Q.d 25)
    have h0 : (0 : ℕ) ≤ 4 * (Val.list [.nat 0]).wt := Nat.zero_le _
    rw [h1] at hct
    have := hcost0 (c := ct + c + (Val.list [.nat 0]).wt + 1) (by have := wt_nat_le 0; omega)
    omega
  have h0 : GI.Machine.BinOp.eval .lt Q.d 25 = 0 := by
    show (if Q.d < 25 then 1 else 0) = 0; rw [if_neg hd]
  rw [h0, if_pos rfl]
  push Not at hd
  -- 2. the order and the integer small test
  have dord := groupOrder_call hO (env := [x]) hjo (g1 []) hgv
  refine EvalAll.letE dord fun vo co hvo => ?_
  obtain ⟨rfl, hco⟩ := hvo
  set ord := Nat.card Q.ρ.range with hord
  have word : (Val.nat ord).wt ≤ Q.d ^ 2 + 3 := wt_card_le _
  have dsz := Det.call (Det.mk2 (Det.var' (P := P) (env := [x, .nat ord]) (i := 1) rfl) (g0 _))
    (smallZ_spec_P₀ hsz Q)
  refine EvalAll.letE dsz fun vb cb hvb => ?_
  obtain ⟨rfl, hcb⟩ := hvb
  rw [← hord] at hcb
  have wpair := wt_list2_le (.nat ord) (.nat Q.d)
  have wdd := wt_nat_le Q.d
  have hsmallc : smallZK * ((Val.list [.nat ord, .nat Q.d]).wt + 24953 * Q.d + 24953 + Q.d + 10) ^ 2
      ≤ caseZ Q.d := by
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2)
    omega
  have hbase : co + cb ≤ (groupOrderPrim hO).bound gv + caseZ Q.d + 20 * (x.wt + 10) +
        8 * Q.d ^ 2 + 20 * Q.d := by
    have := wt_boolVal_le (decide (Q.SmallZ P₀.smallExp))
    omega
  refine EvalAll.ite (Det.var' (P := P) (env := [x, .nat ord, boolVal (decide (Q.SmallZ P₀.smallExp))])
    (i := 2) rfl) (fun _ _ h => ⟨_, h.1⟩) fun t ct' ht => ?_
  obtain ⟨ht, hct'⟩ := ht
  injection ht with ht
  subst ht
  by_cases hz : Q.SmallZ P₀.smallExp
  · -- the integer test holds: enumerate
    have hb1 : (decide (Q.SmallZ P₀.smallExp)).toNat = 1 := by simp [hz]
    rw [hb1, if_neg one_ne_zero]
    refine (Det.mk1 (Det.nat (P := P) (env := [x, .nat ord, boolVal (decide (Q.SmallZ P₀.smallExp))])
      0)).post fun c hc => ⟨Or.inl ⟨rfl, Q.small_of_smallZ (P₀.smallExp_le (by
        have := P₀_a; linarith)) hz⟩, ?_⟩
    have := wt_boolVal_le (decide (Q.SmallZ P₀.smallExp))
    have := wt_nat_le 0
    unfold caseCost
    omega
  have hb0 : (decide (Q.SmallZ P₀.smallExp)).toNat = 0 := by simp [hz]
  rw [hb0, if_pos rfl]
  -- 3. Cameron recognition
  set env3 := [x, .nat ord, boolVal (decide (Q.SmallZ P₀.smallExp))] with henv3
  have dcam := cameronRecognition_call hC (env := env3) hjc (g1 _) hgv hd Q.primitive
  refine EvalAll.letE dcam fun w cw hw => ?_
  obtain ⟨hw, hcw⟩ := hw
  set env4 := env3 ++ [w] with henv4
  have hwb := wt_boolVal_le (decide (Q.SmallZ P₀.smallExp))
  rcases hw with ⟨rfl, hcard⟩ | ⟨m, k, r, e, -, hM, rfl⟩ | ⟨rfl, m, k, r, e, hm, hM⟩
  · -- `[0]`: does not occur
    exact absurd (Q.smallZ_of_cameron_zero hd hcard) hz
  · -- `[1, m, k, r, E]`: return it
    have dget := Det.get' (Det.var' (P := P) (env := env4) (i := 3) rfl) (Det.nat 0)
      (show [Val.nat 1, .nat m, .nat k, .nat r, encKSetTuples e][0]? = some (.nat 1) from rfl)
    have deq := Det.arith' (op := .eq) dget (Det.nat 1) rfl
    refine EvalAll.ite deq (fun _ _ h => ⟨_, h.1⟩) fun t ct'' ht => ?_
    obtain ⟨ht, hct''⟩ := ht
    injection ht with ht
    subst ht
    simp only [GI.Machine.BinOp.eval, if_true, one_ne_zero, if_false]
    refine (Det.var' (P := P) (env := env4) (i := 3) rfl).post fun c hc =>
      ⟨Or.inr ⟨m, k, r, e, rfl, Q.productStructure_of_maroti hM, Q.one_le_r e, hz⟩, ?_⟩
    simp only [GI.Machine.BinOp.eval, if_true] at hct''
    have := wt_nat_le 1
    have := wt_nat_le 0
    unfold caseCost
    omega
  · -- `[2]`: the Cameron range, small
    have hsm := Q.small_of_cameron_range P₀_a e (Q.productStructure_of_maroti hM) hm
    have dget := Det.get' (Det.var' (P := P) (env := env4) (i := 3) rfl) (Det.nat 0)
      (show [Val.nat 2][0]? = some (.nat 2) from rfl)
    have deq := Det.arith' (op := .eq) dget (Det.nat 1) rfl
    refine EvalAll.ite deq (fun _ _ h => ⟨_, h.1⟩) fun t ct'' ht => ?_
    obtain ⟨ht, hct''⟩ := ht
    injection ht with ht
    subst ht
    simp only [GI.Machine.BinOp.eval, show (2 : ℕ) ≠ 1 by norm_num, if_false, if_true]
    refine (Det.mk1 (Det.nat (P := P) (env := env4) 0)).post fun c hc =>
      ⟨Or.inl ⟨rfl, hsm⟩, ?_⟩
    simp only [GI.Machine.BinOp.eval, show (2 : ℕ) ≠ 1 by norm_num, if_false] at hct''
    have := wt_nat_le 2
    have := wt_nat_le 0
    have := wt_list1_le (.nat 2)
    unfold caseCost
    omega

end GI.Impl
