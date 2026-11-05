module

public import Workspace.Impl.AggStructDesTest

@[expose] public section

/-!
# The search for the source tuple of Case 3 as a program

The program runs over the indices `j < q ^ (κ + 1)` of the tuples of `stTs q (κ + 1)`. For each
index it decodes the tuple (its base-`q` digits, `stDDec`) and runs the Case 3 test of
`AggStructDesTest.lean`. It returns the digits of the first index that passes. By
`stDSrcIdx_eq` these digits are the entries of `stSrc3`.

* `stDPow_spec`: the power `q ^ e`, by a loop.
* `stDDec_spec`: the digits `stDDec q e j`, by a loop that divides by `q`.
* `stDSrc_spec`: the search.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp)

/-! ### The power -/

/-- The step of the power: `acc * q`. -/
def stDPowStep : Expr := .arith .mul (arg 2) (.get (arg 0) (.nat 0))

/-- **The power** at base `b` (three functions): on `[q, e]`, the number `q ^ e`. -/
def stDPowFuns (b : ℕ) : List Expr := loopFuns b (.get (.var 0) (.nat 1)) (.nat 1) stDPowStep

/-- The cost constant of the power. -/
def stDPowK : ℕ := 10 ^ 5

theorem stDPow_spec {P : Program} {b : ℕ} (hb : P.HasAt b (stDPowFuns b)) {q e : ℕ}
    (hq : 0 < q) {X : ℕ} (hX : (Val.list [.nat q, .nat e]).wt + e + q ^ e ≤ X) :
    FunDet P b (.list [.nat q, .nat e]) (.nat (q ^ e)) (stDPowK * (X + 1) ^ 2) := by
  have hqa : (Val.nat q).wt < (Val.list [.nat q, .nat e]).wt := wt_le_wt_list (by simp)
  have hea : (Val.nat e).wt < (Val.list [.nat q, .nat e]).wt := wt_le_wt_list (by simp)
  obtain ⟨M, hM⟩ : ∃ M, (Val.list [.nat q, .nat e]).wt = M := ⟨_, rfl⟩
  rw [hM] at hqa hea hX
  have hk : Det P [.list [.nat q, .nat e]] (.get (.var 0) (.nat 1)) (.nat e) (2 * M + 10) := by
    refine (Det.get' (Det.var' (i := 0) rfl) (Det.nat 1)
      (show [Val.nat q, .nat e][1]? = some (.nat e) from rfl)).mono ?_
    omega
  have hacc : Det P [.list [.nat q, .nat e]] (.nat 1) (.nat 1) (1 + 3) := Det.nat 1
  have hpow : ∀ i, i ≤ e → q ^ i ≤ q ^ e := fun i hi => Nat.pow_le_pow_right hq hi
  have hacc_wt : ∀ i acc, i ≤ e → acc = Val.nat (q ^ i) → acc.wt ≤ X + 2 := by
    rintro i acc hi rfl
    have := wt_nat_le (q ^ i); have := hpow i hi
    omega
  obtain ⟨Wd, hWd⟩ : ∃ Wd, Wd = 8 * X + 30 := ⟨_, rfl⟩
  refine (loopBdd_spec hb hk hacc (by have := wt_nat_le e; omega) (M := X + 2)
    (Inv := fun i acc => acc = .nat (q ^ i)) rfl hacc_wt
    (D := fun _ => 20 * (Wd + 1)) ?_).mono ?_
  · rintro i acc hi rfl
    have hH1 := hpow (i + 1) hi
    have hH := hpow i hi.le
    have hHw := wt_nat_le (q ^ i)
    have hiw := wt_nat_le i
    have hvs : (Val.list [.list [.nat q, .nat e], .nat i, .nat (q ^ i)]).wt ≤ Wd := by
      have := wt_list3_le (.list [.nat q, .nat e]) (.nat i) (.nat (q ^ i)); omega
    have g0 : StDC P [Val.list [.list [.nat q, .nat e], .nat i, .nat (q ^ i)]] (arg 0)
        (.list [.nat q, .nat e]) 3 0 Wd := StDC.arg rfl hvs (by omega) (by omega)
    have gq := StDC.get (v := .nat q) g0 (StDC.nat 0 (by omega)) rfl (by omega)
    have gacc : StDC P [Val.list [.list [.nat q, .nat e], .nat i, .nat (q ^ i)]] (arg 2)
        (.nat (q ^ i)) 3 0 Wd := StDC.arg rfl hvs (by omega) (by omega)
    have gS := StDC.arith' gacc gq (op := .mul)
      (show BinOp.eval .mul (q ^ i) q = q ^ (i + 1) by simp [BinOp.eval, pow_succ])
      (by omega)
    refine gS.det.post fun c hc => ⟨rfl, ?_⟩
    beta_reduce
    omega
  · rintro w c ⟨hw, hcost⟩
    refine ⟨hw, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, hM] at hcost
    have h1 : e * (20 * (Wd + 1)) ≤ (X + 1) * (1000 * (X + 1)) := by
      exact Nat.mul_le_mul (by omega) (by omega)
    have h2 : loopModK * (e + 1) * (M + e + (X + 2) + 1) ≤ 1000 * (X + 1) * (4 * (X + 1)) := by
      unfold loopModK
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e1 : (X + 1) ^ 2 = (X + 1) * (X + 1) := by ring
    have e2 : (X + 1) * (1000 * (X + 1)) = 1000 * ((X + 1) * (X + 1)) := by ring
    have e3 : 1000 * (X + 1) * (4 * (X + 1)) = 4000 * ((X + 1) * (X + 1)) := by ring
    unfold stDPowK
    rw [e1]
    omega

/-! ### The digits -/

/-- The step of the digits: `[r, ds] ↦ [r / q, ds ++ [r % q]]`. -/
def stDDecStep : Expr :=
  mk2 (.arith .div (.get (arg 2) (.nat 0)) (.get (arg 0) (.nat 1)))
    (.snoc (.get (arg 2) (.nat 1)) (.arith .mod (.get (arg 2) (.nat 0)) (.get (arg 0) (.nat 1))))

/-- **The digits** at base `b` (three functions): on `[[j, []], q, e]`, the pair
`[j / q ^ e, stDDec q e j]`. -/
def stDDecFuns (b : ℕ) : List Expr :=
  loopFuns b (.get (.var 0) (.nat 2)) (.get (.var 0) (.nat 0)) stDDecStep

/-- The argument of the digits. -/
def stDDA (j q e : ℕ) : Val := .list [.list [.nat j, .list []], .nat q, .nat e]

theorem stDDec_succ (q i j : ℕ) : stDDec q (i + 1) j = stDDec q i j ++ [j / q ^ i % q] := by
  unfold stDDec; rw [List.range_succ, List.map_append]; rfl

theorem stDDec_length (q i j : ℕ) : (stDDec q i j).length = i := by simp [stDDec]

theorem stDDec_lt {q i j : ℕ} (hq : 0 < q) : ∀ x ∈ stDDec q i j, x < q := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  exact Nat.mod_lt _ hq

/-- The cost constant of the digits. -/
def stDDecK : ℕ := 10 ^ 6

theorem stDDec_spec {P : Program} {b : ℕ} (hb : P.HasAt b (stDDecFuns b)) {j q e : ℕ}
    (hq : 0 < q) {X : ℕ} (hX : (stDDA j q e).wt + j + q + e ≤ X) :
    FunDet P b (stDDA j q e) (.list [.nat (j / q ^ e), natList (stDDec q e j)])
      (stDDecK * (X + 1) ^ 3) := by
  obtain ⟨M, hM⟩ : ∃ M, (stDDA j q e).wt = M := ⟨_, rfl⟩
  have eM : (Val.list [.list [.nat j, .list []], .nat q, .nat e]).wt = M := hM
  have hja : (Val.list [.nat j, .list []]).wt < M := by
    rw [← eM]; exact wt_le_wt_list (by simp)
  have hqa : (Val.nat q).wt < M := by rw [← eM]; exact wt_le_wt_list (by simp)
  have hea : (Val.nat e).wt < M := by rw [← eM]; exact wt_le_wt_list (by simp)
  rw [hM] at hX
  have hk : Det P [stDDA j q e] (.get (.var 0) (.nat 2)) (.nat e) (2 * M + 10) := by
    refine (Det.get' (Det.var' (i := 0) rfl) (Det.nat 2)
      (show [Val.list [.nat j, .list []], .nat q, .nat e][2]? = some (.nat e) from rfl)).mono ?_
    rw [← hM] at hea ⊢; unfold stDDA at hea ⊢; omega
  have hacc : Det P [stDDA j q e] (.get (.var 0) (.nat 0)) (.list [.nat j, .list []])
      (2 * M + 10) := by
    refine (Det.get' (Det.var' (i := 0) rfl) (Det.nat 0)
      (show [Val.list [.nat j, .list []], .nat q, .nat e][0]? =
        some (.list [.nat j, .list []]) from rfl)).mono ?_
    rw [← hM] at hja ⊢; unfold stDDA at hja ⊢; omega
  -- weights of the accumulator
  have hpair : ∀ r i, r ≤ j → i ≤ e →
      (Val.list [.nat r, natList (stDDec q i j)]).wt ≤ 20 * (X + 1) ^ 2 := by
    intro r i hr hi
    have h1 := wt_natList_le_sq (xs := stDDec q i j) (B := X)
      (fun x hx => by have := stDDec_lt hq x hx; omega) (by rw [stDDec_length]; omega)
    have h2 := wt_list2_le (.nat r) (natList (stDDec q i j))
    have h3 := wt_nat_le r
    have : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hdivle : ∀ i, j / q ^ i ≤ j := fun i => Nat.div_le_self _ _
  obtain ⟨Wd, hWd⟩ : ∃ Wd, Wd = 100 * (X + 1) ^ 2 + 100 := ⟨_, rfl⟩
  have hX2 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  refine (loopBdd_spec hb hk hacc (by have := wt_nat' q; omega) (M := 20 * (X + 1) ^ 2)
    (Inv := fun i acc => acc = .list [.nat (j / q ^ i), natList (stDDec q i j)])
    (by simp [stDDec, natList])
    (fun i acc hi h => by rw [h]; exact hpair _ _ (hdivle i) hi)
    (D := fun _ => 40 * (Wd + 1)) ?_).mono ?_
  · rintro i acc hi rfl
    obtain ⟨r, hr⟩ : ∃ r, j / q ^ i = r := ⟨_, rfl⟩
    have hrj : r ≤ j := hr ▸ hdivle i
    have hp := hpair r i hrj hi.le
    rw [hr]
    have hvs : (Val.list [stDDA j q e, .nat i, .list [.nat r, natList (stDDec q i j)]]).wt ≤ Wd := by
      have := wt_list3_le (stDDA j q e) (.nat i) (.list [.nat r, natList (stDDec q i j)])
      have := wt_nat_le i
      omega
    have hrw : (Val.nat r).wt < (Val.list [.nat r, natList (stDDec q i j)]).wt :=
      wt_le_wt_list (by simp)
    have hdw : (natList (stDDec q i j)).wt < (Val.list [.nat r, natList (stDDec q i j)]).wt :=
      wt_le_wt_list (by simp)
    have g0 : StDC P [Val.list [stDDA j q e, .nat i, .list [.nat r, natList (stDDec q i j)]]]
        (arg 0) (.list [.list [.nat j, .list []], .nat q, .nat e]) 3 0 Wd :=
      StDC.arg rfl hvs (by omega) (by rw [eM]; omega)
    have gq := StDC.get (v := .nat q) g0 (StDC.nat 1 (by omega)) rfl (by omega)
    have g2 : StDC P [Val.list [stDDA j q e, .nat i, .list [.nat r, natList (stDDec q i j)]]]
        (arg 2) (.list [.nat r, natList (stDDec q i j)]) 3 0 Wd :=
      StDC.arg rfl hvs (by omega) (by omega)
    have gr := StDC.get (v := .nat r) g2 (StDC.nat 0 (by omega)) rfl (by omega)
    have gd := StDC.get (v := natList (stDDec q i j)) g2 (StDC.nat 1 (by omega)) rfl (by omega)
    have hr1 : r / q = j / q ^ (i + 1) := by rw [← hr, Nat.div_div_eq_div_mul, pow_succ]
    have hd1 : natList (stDDec q (i + 1) j) =
        .list ((stDDec q i j).map Val.nat ++ [.nat (r % q)]) := by
      rw [stDDec_succ, hr]; simp [natList]
    have hp1 := hpair (j / q ^ (i + 1)) (i + 1) (hdivle _) hi
    have hd1w : (natList (stDDec q (i + 1) j)).wt <
        (Val.list [.nat (j / q ^ (i + 1)), natList (stDDec q (i + 1) j)]).wt :=
      wt_le_wt_list (by simp)
    have gdiv := StDC.arith' gr gq (op := .div) (show BinOp.eval .div r q = j / q ^ (i + 1) by
      rw [← hr1]; rfl) (by have := hdivle (i + 1); omega)
    have gmod := StDC.arith' gr gq (op := .mod) (show BinOp.eval .mod r q = r % q from rfl)
      (by have := Nat.mod_le r q; omega)
    have gsn := StDC.snoc (vs := (stDDec q i j).map Val.nat) gd gmod (by rw [← hd1]; omega)
    have gS := StDC.mk2 gdiv gsn (by rw [← hd1]; omega) (by omega)
    rw [← hd1] at gS
    refine gS.det.post fun c hc => ⟨rfl, ?_⟩
    beta_reduce
    omega
  · rintro w c ⟨hw, hcost⟩
    refine ⟨hw, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, hM] at hcost
    have h1 : e * (40 * (Wd + 1)) ≤ (X + 1) * (8040 * (X + 1) ^ 2) := by
      exact Nat.mul_le_mul (by omega) (by omega)
    have h2 : loopModK * (e + 1) * (M + e + 20 * (X + 1) ^ 2 + 1) ≤
        1000 * (X + 1) * (23 * (X + 1) ^ 2) := by
      unfold loopModK
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e2 : (X + 1) * (8040 * (X + 1) ^ 2) = 8040 * (X + 1) ^ 3 := by ring
    have e3 : 1000 * (X + 1) * (23 * (X + 1) ^ 2) = 23000 * (X + 1) ^ 3 := by ring
    unfold stDDecK
    omega

/-! ### The test of one index -/

/-- The input of the search: the colors `dl`, `q` and `κ`. -/
def stDSrcA (dl : List ℕ) (q κ : ℕ) : Val := .list [natList dl, .nat q, .nat κ]

/-- What the search needs of its input. -/
structure StDSrcCtx (dl : List ℕ) (q κ : ℕ) : Prop where
  len_dl : dl.length = q ^ κ
  q_two : 2 ≤ q
  κ_pos : 0 < κ
  dl_lt : ∀ x ∈ dl, x < 2 * q ^ κ

theorem StDSrcCtx.q_pos {dl : List ℕ} {q κ : ℕ} (h : StDSrcCtx dl q κ) : 0 < q := by
  have := h.q_two; omega

theorem StDSrcCtx.ctx {dl : List ℕ} {q κ : ℕ} (h : StDSrcCtx dl q κ) (j : ℕ) :
    StDCtx dl (stDDec q (κ + 1) j) q κ :=
  ⟨h.len_dl, stDDec_lt h.q_pos, by rw [stDDec_length]; omega, h.q_pos, h.κ_pos, h.dl_lt⟩

/-- The Case 3 test at `des` works, for all inputs. -/
def StDesOK (P : Program) (des : ℕ) : Prop :=
  ∀ {dl tl : List ℕ} {q κ : ℕ}, StDCtx dl tl q κ → ∀ {N : ℕ}, (stDA dl tl q κ).wt ≤ N →
    FunDet P des (stDA dl tl q κ) (boolVal (stDesB dl tl q κ)) (stDesK * (N + 1) ^ 17)

theorem stDes_ok {P : Program} {f fh ht rb vm mb vf cf h ad dv dv' cb : ℕ}
    (hf : P.funs[f]? = some (stDesF fh rb vm ad dv' cf))
    (hfh : P.HasAt fh (findFuns fh ht)) (hht : StDHitOK P ht) (hrb : P.HasAt rb (rangeFuns rb))
    (hvm : P.funs[vm]? = some (stDVMapF mb rb))
    (hmb : P.HasAt mb (mapFuns mb vf)) (hvf : P.funs[vf]? = some (stDVF cf))
    (hcf : P.funs[cf]? = some (stDColF h)) (hh : P.HasAt h (stDHorFuns h))
    (had : P.HasAt ad (anyFuns ad dv)) (hdv : P.funs[dv]? = some (stDDomF dv'))
    (hdv' : P.funs[dv']? = some (stDDomVF cb)) (hcb : P.HasAt cb (countFuns cb)) :
    StDesOK P f :=
  fun hc _ hN => stDes_spec hf hfh hht hrb hvm hmb hvf hcf hh had hdv hdv' hcb hc hN

/-- `q` and `κ + 1` inside an argument `[S, …]`. -/
def stDSq' : Expr := .get (arg 0) (.nat 1)
def stDSk1 : Expr := .arith .add (.get (arg 0) (.nat 2)) (.nat 1)

/-- **The test of one index** on `[S, j]`: decode `j` (module `dc`) and run the Case 3 test
(module `des`). -/
def stDSrcPF (des dc : ℕ) : Expr :=
  .call des (mk4 (.get (arg 0) (.nat 0))
    (.get (.call dc (mk3 (mk2 (arg 1) .nil) stDSq' stDSk1)) (.nat 1))
    stDSq' (.get (arg 0) (.nat 2)))

/-- The cost constant of the test of one index. -/
def stDSrcPK : ℕ := 10 ^ 80

theorem stDSrcA_wt {dl : List ℕ} {q κ : ℕ} (hc : StDSrcCtx dl q κ) :
    q ^ κ < (stDSrcA dl q κ).wt ∧ q < (stDSrcA dl q κ).wt ∧ κ < (stDSrcA dl q κ).wt ∧
      (natList dl).wt < (stDSrcA dl q κ).wt := by
  have h1 : (natList dl).wt < (stDSrcA dl q κ).wt := wt_le_wt_list (by simp)
  have h2 : dl.length < (natList dl).wt := by
    have := sum_wt_lt_wt_list (dl.map Val.nat)
    have h3 : dl.length ≤ ((dl.map Val.nat).map Val.wt).sum := by
      rw [List.map_map]
      calc dl.length = (dl.map fun _ => 1).sum := by simp
        _ ≤ _ := List.sum_le_sum fun x _ => by have := wt_nat' x; simp; omega
    exact lt_of_le_of_lt h3 this
  have hq := hc.q_pos
  have hpk : q ≤ q ^ κ := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ κ := Nat.pow_le_pow_right hq hc.κ_pos
  have hk : κ < q ^ κ := Nat.lt_pow_self (by have := hc.q_two; omega)
  rw [← hc.len_dl] at hpk hk ⊢
  omega

theorem stDSrcP_spec {P : Program} {f des dc : ℕ} (hf : P.funs[f]? = some (stDSrcPF des dc))
    (hdes : StDesOK P des) (hdc : P.HasAt dc (stDDecFuns dc)) {dl : List ℕ} {q κ : ℕ}
    (hc : StDSrcCtx dl q κ) {N : ℕ} (hN : (stDSrcA dl q κ).wt ≤ N) {j : ℕ}
    (hj : j ≤ q ^ (κ + 1)) :
    FunDet P f (.list [stDSrcA dl q κ, .nat j])
      (boolVal (stDesB dl (stDDec q (κ + 1) j) q κ)) (stDSrcPK * (N + 1) ^ 34) := by
  obtain ⟨hpk, hqS, hκS, hdlS⟩ := stDSrcA_wt hc
  have hq := hc.q_pos
  have hY1 : 1 ≤ N + 1 := by omega
  have hY2 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hjY : j ≤ (N + 1) ^ 2 := by
    have : q ^ (κ + 1) = q * q ^ κ := by rw [pow_succ, mul_comm]
    have h2 : q * q ^ κ ≤ (N + 1) * (N + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h3 : (N + 1) ^ 2 = (N + 1) * (N + 1) := by ring
    omega
  have hjw := wt_nat_le j
  have hqw := wt_nat_le q
  have hκw := wt_nat_le κ
  have hκ1w := wt_nat_le (κ + 1)
  have hnil : (Val.list []).wt ≤ 4 := by have := wt_list_le []; simpa using this
  have hSj : (Val.list [stDSrcA dl q κ, .nat j]).wt ≤ 2 * N + 2 * (N + 1) ^ 2 + 10 := by
    have := wt_list2_le (stDSrcA dl q κ) (.nat j); omega
  have hjn : (Val.list [.nat j, .list []]).wt ≤ 2 * (N + 1) ^ 2 + 18 := by
    have := wt_list2_le (.nat j) (.list []); omega
  have hDA : (stDDA j q (κ + 1)).wt ≤ 4 * (N + 1) ^ 2 + 4 * N + 60 := by
    have := wt_list3_le (.list [.nat j, .list []]) (.nat q) (.nat (κ + 1)); unfold stDDA; omega
  obtain ⟨X, hXd⟩ : ∃ X, X = 20 * (N + 1) ^ 2 + 100 := ⟨_, rfl⟩
  have hX : (stDDA j q (κ + 1)).wt + j + q + (κ + 1) ≤ X := by omega
  have hdec := stDDec_spec hdc hq hX
  obtain ⟨E1, hE1⟩ : ∃ E1, stDDecK * (X + 1) ^ 3 = E1 := ⟨_, rfl⟩
  rw [hE1] at hdec
  -- weights of the digits
  obtain ⟨D, hD⟩ : ∃ D, stDDec q (κ + 1) j = D := ⟨_, rfl⟩
  have hDw : (natList D).wt ≤ 5 * (N + 1) ^ 2 := by
    rw [← hD]
    have := wt_natList_le_sq (xs := stDDec q (κ + 1) j) (B := N)
      (fun x hx => by have := stDDec_lt hq x hx; omega) (by rw [stDDec_length]; omega)
    omega
  rw [hD] at hdec ⊢
  have hpair : (Val.list [.nat (j / q ^ (κ + 1)), natList D]).wt ≤ 20 * (X + 1) ^ 2 := by
    have h1 := wt_natList_le_sq (xs := D) (B := X)
      (fun x hx => by rw [← hD] at hx; have := stDDec_lt hq x hx; omega)
      (by rw [← hD, stDDec_length]; omega)
    have h2 := wt_list2_le (.nat (j / q ^ (κ + 1))) (natList D)
    have h3 := wt_nat_le (j / q ^ (κ + 1))
    have h4 : j / q ^ (κ + 1) ≤ j := Nat.div_le_self _ _
    have : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hA : (stDA dl D q κ).wt ≤ 20 * (N + 1) ^ 2 := by
    have := wt_list4_le (natList dl) (natList D) (.nat q) (.nat κ); unfold stDA; omega
  have hctx : StDCtx dl D q κ := hD ▸ hc.ctx j
  have hds := hdes hctx hA
  obtain ⟨E2, hE2⟩ : ∃ E2, stDesK * (20 * (N + 1) ^ 2 + 1) ^ 17 = E2 := ⟨_, rfl⟩
  rw [hE2] at hds
  obtain ⟨W, hW⟩ : ∃ W, W = 20 * (X + 1) ^ 2 + 100 := ⟨_, rfl⟩
  have hXW : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hNX : (N + 1) ^ 2 ≤ X := by omega
  have e0 : (Val.list [Val.list [natList dl, .nat q, .nat κ], .nat j]).wt =
      (Val.list [stDSrcA dl q κ, .nat j]).wt := rfl
  have e1 : (Val.list [natList dl, .nat q, .nat κ]).wt = (stDSrcA dl q κ).wt := rfl
  have gS : StDC P [.list [stDSrcA dl q κ, .nat j]] (arg 0)
      (.list [natList dl, .nat q, .nat κ]) 3 0 W :=
    StDC.arg rfl (by omega) (by omega) (by rw [e1]; omega)
  have gj : StDC P [.list [stDSrcA dl q κ, .nat j]] (arg 1) (.nat j) 3 0 W :=
    StDC.arg rfl (by omega) (by omega) (by omega)
  have gdl := StDC.get (v := natList dl) gS (StDC.nat 0 (by omega)) rfl (by omega)
  have gq := StDC.get (v := .nat q) gS (StDC.nat 1 (by omega)) rfl (by omega)
  have gκ := StDC.get (v := .nat κ) gS (StDC.nat 2 (by omega)) rfl (by omega)
  have gk1 := StDC.arith' gκ (StDC.nat 1 (by omega)) (op := .add)
    (show BinOp.eval .add κ 1 = κ + 1 from rfl) (by omega)
  have gpair := StDC.mk2 gj (StDC.nil (by omega)) (by omega) (by omega)
  have gdA := StDC.mk3 gpair gq gk1 (by unfold stDDA at hDA; omega) (by omega)
  have gdc := StDC.call (v := stDDA j q (κ + 1)) gdA hdec (by omega)
  have gdec := StDC.get (v := natList D) gdc (StDC.nat 1 (by omega)) rfl (by omega)
  have g4 := StDC.mk4 gdl gdec gq gκ (by unfold stDA at hA; omega) (by omega)
  have g := StDC.call (v := stDA dl D q κ) g4 hds
    (by have := wt_boolVal_le (stDesB dl D q κ); omega)
  refine StDC.funDet hf g ?_
  have hP := fun i k (h : i ≤ k) => Nat.pow_le_pow_right hY1 h
  have h1Y : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hX1 : X + 1 ≤ 121 * (N + 1) ^ 2 := by omega
  have u0 : (X + 1) ^ 2 ≤ 121 ^ 2 * (N + 1) ^ 4 := by
    calc (X + 1) ^ 2 ≤ (121 * (N + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hX1 2
      _ = _ := by ring
  have u1 : stDDecK * (X + 1) ^ 3 ≤ stDDecK * 121 ^ 3 * (N + 1) ^ 6 := by
    calc stDDecK * (X + 1) ^ 3 ≤ stDDecK * (121 * (N + 1) ^ 2) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX1 3)
      _ = _ := by ring
  have u2 : stDesK * (20 * (N + 1) ^ 2 + 1) ^ 17 ≤ stDesK * 21 ^ 17 * (N + 1) ^ 34 := by
    calc stDesK * (20 * (N + 1) ^ 2 + 1) ^ 17 ≤ stDesK * (21 * (N + 1) ^ 2) ^ 17 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 17)
      _ = _ := by ring
  have hp4 := hP 4 34 (by norm_num)
  have hp6 := hP 6 34 (by norm_num)
  rw [← hE1, ← hE2, hW]
  clear g g4 gdec gdc gdA gpair gk1 gκ gq gdl gj gS hds hdec
  simp only [stDSrcPK, stDDecK, stDesK] at u1 u2 ⊢
  norm_num at u0 u1 u2 ⊢
  linarith

/-! ### The search -/

/-- `q` and `κ + 1` inside an environment that starts with `S`. -/
def stDSq0 : Expr := .get (.var 0) (.nat 1)
def stDSk0 : Expr := .arith .add (.get (.var 0) (.nat 2)) (.nat 1)

/-- **The search** on `S = [dl, q, κ]`: modules `pw` (power), `fs` (find of the test of one
index), `rb` (range) and `dc` (digits). -/
def stDSrcF (pw fs rb dc : ℕ) : Expr :=
  .letE (.call pw (mk2 stDSq0 stDSk0))
    (.letE (.call fs (mk2 (.var 0) (.call rb (.var 1))))
      (.get (.call dc (mk3 (mk2 (.var 2) .nil) stDSq0 stDSk0)) (.nat 1)))

/-- The cost constant of the search. -/
def stDSrcK : ℕ := 10 ^ 82

theorem stDSrc_spec {P : Program} {f pw fs rb dc sp des : ℕ}
    (hf : P.funs[f]? = some (stDSrcF pw fs rb dc)) (hpw : P.HasAt pw (stDPowFuns pw))
    (hfs : P.HasAt fs (findFuns fs sp)) (hsp : P.funs[sp]? = some (stDSrcPF des dc))
    (hdes : StDesOK P des) (hdc : P.HasAt dc (stDDecFuns dc)) (hrb : P.HasAt rb (rangeFuns rb))
    {dl : List ℕ} {q κ : ℕ} (hc : StDSrcCtx dl q κ) {N : ℕ} (hN : (stDSrcA dl q κ).wt ≤ N) :
    FunDet P f (stDSrcA dl q κ) (natList (stDDec q (κ + 1) (stDSrcIdx dl q κ (κ + 1))))
      (stDSrcK * (N + 1) ^ 36) := by
  obtain ⟨hpk, hqS, hκS, hdlS⟩ := stDSrcA_wt hc
  have hq := hc.q_pos
  have hY1 : 1 ≤ N + 1 := by omega
  have hY2 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨n, hn⟩ : ∃ n, q ^ (κ + 1) = n := ⟨_, rfl⟩
  have hnY : n ≤ (N + 1) ^ 2 := by
    have : q ^ (κ + 1) = q * q ^ κ := by rw [pow_succ, mul_comm]
    have h2 : q * q ^ κ ≤ (N + 1) * (N + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h3 : (N + 1) ^ 2 = (N + 1) * (N + 1) := by ring
    omega
  have hqw := wt_nat_le q
  have hκw := wt_nat_le κ
  have hκ1w := wt_nat_le (κ + 1)
  have hnw := wt_nat_le n
  have hnil : (Val.list []).wt ≤ 4 := by have := wt_list_le []; simpa using this
  have h1Y : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hY4 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right hY1 (by norm_num)
  -- the power
  have hqk : (Val.list [.nat q, .nat (κ + 1)]).wt ≤ 4 * N + 20 := by
    have := wt_list2_le (.nat q) (.nat (κ + 1)); omega
  have hpow := stDPow_spec hpw hq (e := κ + 1) (X := 8 * (N + 1) ^ 2 + 100) (by rw [hn]; omega)
  rw [hn] at hpow
  -- the find
  obtain ⟨j, hjd⟩ : ∃ j, stDSrcIdx dl q κ (κ + 1) = j := ⟨_, rfl⟩
  have hjn : j ≤ n := by
    rw [← hjd, ← hn]; unfold stDSrcIdx; exact List.findIdx_le_length.trans (by simp)
  have hrn : (natList (List.range n)).wt ≤ 20 * (N + 1) ^ 4 := by
    have := wt_natList_le_sq (xs := List.range n) (B := n) (fun x hx => (List.mem_range.1 hx).le)
      (by simp)
    have h2 : (n + 1) ^ 2 ≤ (2 * (N + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 : (2 * (N + 1) ^ 2) ^ 2 = 4 * (N + 1) ^ 4 := by ring
    omega
  have hfind := st_find_det hfs (c := stDSrcA dl q κ) (n := n)
    (t := fun j => stDesB dl (stDDec q (κ + 1) j) q κ) (B := stDSrcPK * (N + 1) ^ 34)
    (X := 50 * (N + 1) ^ 4)
    (fun i hi => stDSrcP_spec hsp hdes hdc hc hN (by omega))
    (by have := wt_list2_le (stDSrcA dl q κ) (natList (List.range n)); omega) (by omega)
  have hidx : (List.range n).findIdx (fun j => stDesB dl (stDDec q (κ + 1) j) q κ) = j := by
    rw [← hjd, ← hn]; rfl
  rw [hidx] at hfind
  have hr := st_range_det hrb n
  -- the digits
  have hjw := wt_nat_le j
  have hjn' : (Val.list [.nat j, .list []]).wt ≤ 2 * (N + 1) ^ 2 + 18 := by
    have := wt_list2_le (.nat j) (.list []); omega
  have hDA : (stDDA j q (κ + 1)).wt ≤ 4 * (N + 1) ^ 2 + 4 * N + 60 := by
    have := wt_list3_le (.list [.nat j, .list []]) (.nat q) (.nat (κ + 1)); unfold stDDA; omega
  obtain ⟨X, hXd⟩ : ∃ X, X = 20 * (N + 1) ^ 2 + 100 := ⟨_, rfl⟩
  have hdec := stDDec_spec hdc hq (j := j) (e := κ + 1) (X := X) (by omega)
  obtain ⟨D, hD⟩ : ∃ D, stDDec q (κ + 1) j = D := ⟨_, rfl⟩
  rw [hD] at hdec
  have hpair : (Val.list [.nat (j / q ^ (κ + 1)), natList D]).wt ≤ 20 * (X + 1) ^ 2 := by
    have h1 := wt_natList_le_sq (xs := D) (B := X)
      (fun x hx => by rw [← hD] at hx; have := stDDec_lt hq x hx; omega)
      (by rw [← hD, stDDec_length]; omega)
    have h2 := wt_list2_le (.nat (j / q ^ (κ + 1))) (natList D)
    have h3 := wt_nat_le (j / q ^ (κ + 1))
    have h4 : j / q ^ (κ + 1) ≤ j := Nat.div_le_self _ _
    have : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hDw : (natList D).wt < (Val.list [.nat (j / q ^ (κ + 1)), natList D]).wt :=
    wt_le_wt_list (by simp)
  rw [hjd, hD]
  -- the program
  obtain ⟨W, hW⟩ : ∃ W, W = 20 * (X + 1) ^ 2 + 100 * (N + 1) ^ 4 + 100 := ⟨_, rfl⟩
  have e1 : (Val.list [natList dl, .nat q, .nat κ]).wt = (stDSrcA dl q κ).wt := rfl
  have gS : ∀ rest : List Val, StDC P (stDSrcA dl q κ :: rest) (.var 0) (stDSrcA dl q κ) 1 0 W :=
    fun rest => StDC.var' rfl (by omega)
  have gq : ∀ rest : List Val, StDC P (stDSrcA dl q κ :: rest) stDSq0 (.nat q) 3 0 W :=
    fun rest => StDC.get (vs := [natList dl, .nat q, .nat κ]) (gS rest) (StDC.nat 1 (by omega))
      rfl (by omega)
  have gk : ∀ rest : List Val, StDC P (stDSrcA dl q κ :: rest) stDSk0 (.nat (κ + 1)) 5 0 W :=
    fun rest => StDC.arith' (StDC.get (vs := [natList dl, .nat q, .nat κ]) (gS rest)
      (StDC.nat 2 (by omega)) rfl (by omega)) (StDC.nat 1 (by omega)) (op := .add)
      (show BinOp.eval .add κ 1 = κ + 1 from rfl) (by omega)
  have g1 := StDC.call (StDC.mk2 (gq []) (gk []) (by omega) (by omega)) hpow (by omega)
  have gn : StDC P [stDSrcA dl q κ, .nat n] (.var 1) (.nat n) 1 0 W := StDC.var' rfl (by omega)
  have g2 := StDC.call (StDC.mk2 (gS [.nat n]) (StDC.call gn hr (by omega))
    (by have := wt_list2_le (stDSrcA dl q κ) (natList (List.range n)); omega) (by omega)) hfind
    (by omega)
  have gj : StDC P [stDSrcA dl q κ, .nat n, .nat j] (.var 2) (.nat j) 1 0 W :=
    StDC.var' rfl (by omega)
  have gpair := StDC.mk2 gj (StDC.nil (by omega)) (by omega) (by omega)
  have gdA := StDC.mk3 gpair (gq [.nat n, .nat j]) (gk [.nat n, .nat j])
    (by unfold stDDA at hDA; omega) (by omega)
  have gdc := StDC.call (v := stDDA j q (κ + 1)) gdA hdec (by omega)
  have gdec := StDC.get (v := natList D) gdc (StDC.nat 1 (by omega)) rfl (by omega)
  have g := StDC.letE g1 (StDC.letE g2 gdec (by omega)) (by omega)
  refine StDC.funDet hf g ?_
  have hP := fun i k (h : i ≤ k) => Nat.pow_le_pow_right hY1 h
  have hX1 : X + 1 ≤ 121 * (N + 1) ^ 2 := by omega
  have u0 : (X + 1) ^ 2 ≤ 121 ^ 2 * (N + 1) ^ 4 := by
    calc (X + 1) ^ 2 ≤ (121 * (N + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hX1 2
      _ = _ := by ring
  have u1 : (X + 1) ^ 3 ≤ 121 ^ 3 * (N + 1) ^ 6 := by
    calc (X + 1) ^ 3 ≤ (121 * (N + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hX1 3
      _ = _ := by ring
  have u2 : (8 * (N + 1) ^ 2 + 100 + 1) ^ 2 ≤ 109 ^ 2 * (N + 1) ^ 4 := by
    calc (8 * (N + 1) ^ 2 + 100 + 1) ^ 2 ≤ (109 * (N + 1) ^ 2) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have u3 : (n + 1) ^ 3 ≤ 8 * (N + 1) ^ 6 := by
    calc (n + 1) ^ 3 ≤ (2 * (N + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = _ := by ring
  have u4 : n * (stDSrcPK * (N + 1) ^ 34) ≤ stDSrcPK * (N + 1) ^ 36 := by
    calc n * (stDSrcPK * (N + 1) ^ 34) ≤ (N + 1) ^ 2 * (stDSrcPK * (N + 1) ^ 34) :=
          Nat.mul_le_mul_right _ hnY
      _ = _ := by ring
  have u5 : loopModK * (50 * (N + 1) ^ 4 + 1) * (3 * (50 * (N + 1) ^ 4) + 3) ≤
      loopModK * 51 * 153 * (N + 1) ^ 8 := by
    have h1 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    calc _ ≤ loopModK * (51 * (N + 1) ^ 4) * (153 * (N + 1) ^ 4) :=
          st_mul3 le_rfl (by omega) (by omega)
      _ = _ := by ring
  have hp4 := hP 4 36 (by norm_num)
  have hp6 := hP 6 36 (by norm_num)
  have hp8 := hP 8 36 (by norm_num)
  have v1 := Nat.mul_le_mul_left stDDecK u1
  have v2 := Nat.mul_le_mul_left stDPowK u2
  have v3 := Nat.mul_le_mul_left 10000 u3
  rw [hW]
  clear g g1 g2 gj gpair gdA gdc gdec gn gS gq gk hfind hdec hpow hr
  simp only [stDSrcK, stDSrcPK, stDDecK, stDPowK, loopModK] at u4 u5 v1 v2 ⊢
  norm_num at u0 u4 u5 v1 v2 v3 ⊢
  linarith

/-- **The search on a coloring**: on `[c, q, κ]` (the coloring `c` as `encKColoring`), the
program returns the entries of the source tuple `stSrc3` over `stTs q (κ + 1)`. -/
theorem stDSrc3_spec {P : Program} {f pw fs rb dc sp des : ℕ}
    (hf : P.funs[f]? = some (stDSrcF pw fs rb dc)) (hpw : P.HasAt pw (stDPowFuns pw))
    (hfs : P.HasAt fs (findFuns fs sp)) (hsp : P.funs[sp]? = some (stDSrcPF des dc))
    (hdes : StDesOK P des) (hdc : P.HasAt dc (stDDecFuns dc)) (hrb : P.HasAt rb (rangeFuns rb))
    {q κ : ℕ} (c : (Fin κ → Fin q) → ℕ) (hq : 2 ≤ q) (hκ : 0 < κ)
    (hcl : ∀ u, c u < 2 * q ^ κ) {N : ℕ}
    (hN : (Val.list [GI.Cited.encKColoring c, .nat q, .nat κ]).wt ≤ N) :
    FunDet P f (.list [GI.Cited.encKColoring c, .nat q, .nat κ])
      (natList (stL fun i => (stSrc3 (ℓ := κ + 1) c (Nat.lt_succ_self κ) (by omega) i : ℕ)))
      (stDSrcK * (N + 1) ^ 36) := by
  have hc : StDSrcCtx (stDL c) q κ := ⟨stDL_length c, hq, hκ, fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact hcl _⟩
  have h := stDSrc_spec hf hpw hfs hsp hdes hdc hrb hc (N := N)
    (by unfold stDSrcA; rw [natList_stDL]; exact hN)
  rw [stDSrcIdx_eq c (Nat.lt_succ_self κ) (by omega)] at h
  unfold stDSrcA at h
  rw [natList_stDL] at h
  exact h

end GI.Impl
