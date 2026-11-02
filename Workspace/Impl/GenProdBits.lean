import Workspace.Impl.GenProdMath
import Workspace.Impl.GenCls

/-!
# The product refinement: the bit loop

For two points `p, q` of `Fin k`, each with a row of `r + 1` lists of numbers, the bits say
which entries of the two rows agree. The loop reads the bits from entry `r` down to entry `0`
and keeps the Horner sum (`hornerN`) and the number of leading ones (`leadN`) of the bits. The
pair `(p, q)` is the point `j = p k + q` of `Fin (k * k)`.

`pbit_spec` is the loop; `pmaskTab_spec` and `pleadTab_spec` tabulate the two numbers over
the pairs.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {k : ℕ}

/-- The rows of the points, as a value. -/
def rowsVal (rows : Fin k → List (List ℕ)) : Val :=
  .list ((List.finRange k).map fun p => .list ((rows p).map natList))

/-- Bit `i` of two rows: whether their entries `i` agree. -/
def rowBit (rows : Fin k → List (List ℕ)) (p q : Fin k) (i : ℕ) : ℕ :=
  if (rows p).getD i [] = (rows q).getD i [] then 1 else 0

/-- The first point of a pair. -/
def pairFst (j : Fin (k * k)) : Fin k := (finProdFinEquiv.symm j).1
/-- The second point of a pair. -/
def pairSnd (j : Fin (k * k)) : Fin k := (finProdFinEquiv.symm j).2

theorem pairFst_val (j : Fin (k * k)) : (pairFst j : ℕ) = j / k := by
  simp [pairFst, finProdFinEquiv_symm_apply, Fin.divNat]

theorem pairSnd_val (j : Fin (k * k)) : (pairSnd j : ℕ) = j % k := by
  simp [pairSnd, finProdFinEquiv_symm_apply, Fin.modNat]

/-- The context of the bit loop. -/
def pbCtx (rows : Fin k → List (List ℕ)) (r : ℕ) : Val := .list [rowsVal rows, .nat k, .nat r]

/-- The step of the bit loop, on `[[c, j], i, [h, lead]]` with `c = [rows, k, r]`. -/
def pbStep (beq : ℕ) : Expr :=
  let C := Expr.get (arg 0) (.nat 0)
  let J := Expr.get (arg 0) (.nat 1)
  let K := Expr.get C (.nat 1)
  let R := Expr.get C (.nat 2)
  let rowAt := fun (P : Expr) => Expr.get (.get (.get C (.nat 0)) P) (.arith .sub R (arg 1))
  .letE (.call beq (mk2 (rowAt (.arith .div J K)) (rowAt (.arith .mod J K))))
    (mk2 (.arith .add (.arith .mul (.nat 2) (.get (arg 2) (.nat 0))) (.var 1))
      (.ite (.arith .mul (.arith .eq (.get (arg 2) (.nat 1)) (arg 1)) (.var 1))
        (.arith .add (arg 1) (.nat 1)) (.get (arg 2) (.nat 1))))

/-- The bit loop at base `b` (three functions), with the list equality at `beq`. -/
def pbFuns (b beq : ℕ) : List Expr :=
  loopFuns b (.arith .add (.get (.get (.var 0) (.nat 0)) (.nat 2)) (.nat 1)) (mk2 (.nat 0) (.nat 0))
    (pbStep beq)

/-- The value of the bit loop after `i` steps. -/
def pbAcc (b : ℕ → ℕ) (r i : ℕ) : Val := .list [.nat (hornerN b r i), .nat (leadN b r i)]

theorem hornerN_lt_pow {b : ℕ → ℕ} {r : ℕ} (hb : ∀ i, b i ≤ 1) (t : ℕ) :
    hornerN b r t < 2 ^ t := by
  induction t with
  | zero => simp [hornerN]
  | succ t ih => rw [hornerN, pow_succ]; have := hb (r - t); omega

/-- The constant of the bit loop. -/
def pbK : ℕ := 10 ^ 9

set_option maxHeartbeats 1000000 in
/-- **The bit loop.** On `[[rows, k, r], j]` for a pair `j = p k + q`, after `r + 1` steps:
the Horner sum and the leading ones of the bits of the rows of `p` and `q`. -/
theorem pb_spec {P : Program} {b beq : ℕ} (h : P.HasAt b (pbFuns b beq))
    (heq : P.HasAt beq (eqNatsFuns beq)) (rows : Fin k → List (List ℕ)) {r : ℕ}
    (hlen : ∀ p, (rows p).length = r + 1) (j : Fin (k * k)) :
    FunDet P b (.list [pbCtx rows r, .nat j])
      (pbAcc (rowBit rows (pairFst j) (pairSnd j)) r (r + 1))
      (pbK * ((Val.list [pbCtx rows r, .nat j]).wt + 2 ^ (r + 1) + 1) ^ 3) := by
  set a := Val.list [pbCtx rows r, .nat j] with ha
  set Y := a.wt with hY
  set bt := rowBit rows (pairFst j) (pairSnd j) with hbt
  have hbt1 : ∀ i, bt i ≤ 1 := fun i => by simp only [hbt, rowBit]; split_ifs <;> omega
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd j.2 (by simp [h0])
    · exact h0
  -- weights
  have wc : (pbCtx rows r).wt < Y := wt_le_wt_list (by simp [ha])
  have wj : (Val.nat j).wt < Y := wt_le_wt_list (by simp [ha])
  have wrv : (rowsVal rows).wt < (pbCtx rows r).wt := wt_le_wt_list (by simp [pbCtx])
  have wk : (Val.nat k).wt < (pbCtx rows r).wt := wt_le_wt_list (by simp [pbCtx])
  have wr : (Val.nat r).wt < (pbCtx rows r).wt := wt_le_wt_list (by simp [pbCtx])
  set T := 2 ^ (r + 1) with hT
  set pf := pairFst j
  set qf := pairSnd j
  have hpv : (pf : ℕ) = j / k := pairFst_val j
  have hqv : (qf : ℕ) = j % k := pairSnd_val j
  -- the rows in the value
  have hrowP : ((List.finRange k).map fun p => Val.list ((rows p).map natList))[(j : ℕ) / k]? =
      some (.list ((rows pf).map natList)) := by
    rw [← hpv]; simp
  have hrowQ : ((List.finRange k).map fun p => Val.list ((rows p).map natList))[(j : ℕ) % k]? =
      some (.list ((rows qf).map natList)) := by
    rw [← hqv]; simp
  have wrowP : (Val.list ((rows pf).map natList)).wt < (rowsVal rows).wt :=
    wt_le_wt_list (List.mem_of_getElem? hrowP)
  have wrowQ : (Val.list ((rows qf).map natList)).wt < (rowsVal rows).wt :=
    wt_le_wt_list (List.mem_of_getElem? hrowQ)
  have hrY : r + 1 < Y := by
    have := length_lt_wt_list ((rows pf).map natList)
    rw [List.length_map, hlen] at this
    omega
  have hent : ∀ (p : Fin k) (i : ℕ), i ≤ r →
      ((rows p).map natList)[r - i]? = some (natList ((rows p).getD (r - i) [])) := by
    intro p i hi
    have hl : r - i < (rows p).length := by rw [hlen]; omega
    simp [List.getElem?_map, List.getElem?_eq_getElem hl, List.getD_eq_getElem _ _ hl]
  have went : ∀ (p : Fin k) (i : ℕ), i ≤ r →
      (natList ((rows p).getD (r - i) [])).wt < (Val.list ((rows p).map natList)).wt :=
    fun p i hi => wt_le_wt_list (List.mem_of_getElem? (hent p i hi))
  have hY6 : 6 ≤ Y := by
    have h1 := went pf 0 (Nat.zero_le _)
    have h2 := (natList ((rows pf).getD (r - 0) [])).two_le_size
    have h3 := (natList ((rows pf).getD (r - 0) [])).size_le_wt
    omega
  have hM : ∀ i, i ≤ r + 1 → (pbAcc bt r i).wt ≤ 2 * T + 2 * r + 20 := by
    intro i hi
    have h1 := hornerN_lt_pow hbt1 (r := r) i
    have h2 : 2 ^ i ≤ T := Nat.pow_le_pow_right (by norm_num) hi
    have h3 := leadN_le bt r i
    have := wt_list2_le (.nat (hornerN bt r i)) (.nat (leadN bt r i))
    have := wt_nat_le (hornerN bt r i)
    have := wt_nat_le (leadN bt r i)
    simp only [pbAcc]
    omega
  have hkE : Det P [a] (.arith .add (.get (.get (.var 0) (.nat 0)) (.nat 2)) (.nat 1))
      (.nat (r + 1)) _ :=
    Det.arith' (Det.get' (Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 0)
      (v := pbCtx rows r) rfl) (Det.nat 2) (v := .nat r) rfl) (Det.nat 1) (z := r + 1) rfl
  have h0E : Det P [a] (mk2 (.nat 0) (.nat 0)) (pbAcc bt r 0) _ :=
    Det.mk2 (Det.nat (P := P) (env := [a]) 0) (Det.nat 0)
  have w00 : (pbAcc bt r 0).wt ≤ 20 := by
    have := wt_list2_le (.nat 0) (.nat 0); have := wt_nat_le 0; simp only [pbAcc, hornerN, leadN]; omega
  refine (loopBdd_spec (P := P) (Inv := fun i acc => acc = pbAcc bt r i) h hkE h0E
    (M := 2 * T + 2 * r + 20) ?_ rfl (fun i acc hi hacc => hacc ▸ hM i hi)
    (D := fun _ => loopModK * (Y + 1) * (5 * Y + 30) + 1000 * (Y + T + 10)) ?_).mono ?_
  · have := wt_nat_le (r + 1)
    have := wt_nat_le 0
    have := wt_nat_le 1
    have := wt_nat_le 2
    have := wt_nat_le r
    have := wt_list2_le (.nat 0) (.nat 0)
    have e1 : (Val.list [pbCtx rows r, Val.nat j]).wt = Y := rfl
    have e2 : (Val.list [Val.nat (hornerN bt r 0), Val.nat (leadN bt r 0)]).wt =
      (pbAcc bt r 0).wt := rfl
    have e3 : (Val.list [Val.nat (hornerN bt r 0), Val.nat (leadN bt r 0)]).wt =
      (Val.list [Val.nat 0, Val.nat 0]).wt := rfl
    omega
  · rintro i acc hi rfl
    set A := Val.list [a, .nat i, pbAcc bt r i] with hA
    have wA := wt_stepArg_le a i (pbAcc bt r i)
    have wM := hM i hi.le
    have hir : i ≤ r := by omega
    have dA0 : ∀ rest, Det P (A :: rest) (arg 0) a (2 * A.wt + 5) := fun rest =>
      Det.arg' (vs := [a, .nat i, pbAcc bt r i]) (j := 0) rfl
    have dI : ∀ rest, Det P (A :: rest) (arg 1) (.nat i) (2 * A.wt + 6) := fun rest =>
      Det.arg' (vs := [a, .nat i, pbAcc bt r i]) (j := 1) rfl
    have dAcc : ∀ rest, Det P (A :: rest) (arg 2) (pbAcc bt r i) (2 * A.wt + 7) := fun rest =>
      Det.arg' (vs := [a, .nat i, pbAcc bt r i]) (j := 2) rfl
    have dC : ∀ rest, Det P (A :: rest) (.get (arg 0) (.nat 0)) (pbCtx rows r) _ := fun rest =>
      Det.get' (dA0 rest) (Det.nat 0) (v := pbCtx rows r) rfl
    have dJ : ∀ rest, Det P (A :: rest) (.get (arg 0) (.nat 1)) (.nat j) _ := fun rest =>
      Det.get' (dA0 rest) (Det.nat 1) (v := .nat j) rfl
    have dK := Det.get' (dC []) (Det.nat 1) (v := .nat k) rfl
    have dR := Det.get' (dC []) (Det.nat 2) (v := .nat r) rfl
    have dRows := Det.get' (dC []) (Det.nat 0) (v := rowsVal rows) rfl
    have dIdx := Det.arith' (op := .sub) dR (dI []) (z := r - i) rfl
    have dP := Det.arith' (op := .div) (dJ []) dK (z := j / k) rfl
    have dQ := Det.arith' (op := .mod) (dJ []) dK (z := j % k) rfl
    have dEP := Det.get' (Det.get' dRows dP hrowP) dIdx (hent pf i hir)
    have dEQ := Det.get' (Det.get' dRows dQ hrowQ) dIdx (hent qf i hir)
    have dcall := Det.call (Det.mk2 dEP dEQ) (eqNats_spec heq _ _)
    set bv : Val := boolVal (decide ((rows pf).getD (r - i) [] = (rows qf).getD (r - i) []))
      with hbv
    have hbv' : bv = .nat (bt (r - i)) := by
      rw [hbv, hbt]
      unfold rowBit boolVal
      by_cases hc : (rows pf).getD (r - i) [] = (rows qf).getD (r - i) []
      · rw [if_pos hc, decide_eq_true hc]; rfl
      · rw [if_neg hc, decide_eq_false hc]; rfl
    rw [hbv'] at dcall
    -- the body
    have dB := Det.var' (P := P) (env := [A, .nat (bt (r - i))]) (i := 1) (v := .nat (bt (r - i))) rfl
    have dH := Det.get' (dAcc [.nat (bt (r - i))]) (Det.nat 0) (v := .nat (hornerN bt r i)) rfl
    have dL := Det.get' (dAcc [.nat (bt (r - i))]) (Det.nat 1) (v := .nat (leadN bt r i)) rfl
    have dH' := Det.arith' (op := .add) (Det.arith' (op := .mul) (Det.nat 2) dH
      (z := 2 * hornerN bt r i) rfl) dB (z := hornerN bt r (i + 1)) (by rw [hornerN]; rfl)
    have dT := Det.arith' (op := .mul) (Det.arith' (op := .eq) dL (dI _)
      (z := if leadN bt r i = i then 1 else 0) rfl) dB
      (z := (if leadN bt r i = i then 1 else 0) * bt (r - i)) rfl
    have dL' := Det.ite' dT (Det.arith' (op := .add) (dI _) (Det.nat 1) (z := i + 1) rfl) dL
    have hlv : (if (if leadN bt r i = i then 1 else 0) * bt (r - i) = 0 then Val.nat (leadN bt r i)
        else Val.nat (i + 1)) = .nat (leadN bt r (i + 1)) := by
      rw [leadN]
      have := hbt1 (r - i)
      by_cases h1 : leadN bt r i = i <;> by_cases h2 : bt (r - i) = 1 <;>
        simp [h1, h2] <;> omega
    rw [hlv] at dL'
    have dbody := Det.letE dcall (Det.mk2 dH' dL')
    refine dbody.post fun c hc => ⟨rfl, ?_⟩
    -- the cost
    have hh := hornerN_lt_pow hbt1 (r := r) (i + 1)
    have hh0 := hornerN_lt_pow hbt1 (r := r) i
    have hpow : 2 ^ (i + 1) ≤ T := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow0 : 2 ^ i ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hl0 := leadN_le bt r i
    have hl1 := leadN_le bt r (i + 1)
    have wEP := went pf i hir
    have wEQ := went qf i hir
    have weq : loopModK * (((rows pf).getD (r - i) []).length + 1) *
        ((Val.list [natList ((rows pf).getD (r - i) []), natList ((rows qf).getD (r - i) [])]).wt +
          ((rows pf).getD (r - i) []).length + 4) ≤ loopModK * (Y + 1) * (5 * Y + 30) := by
      have l1 := length_lt_wt_list (((rows pf).getD (r - i) []).map Val.nat)
      rw [List.length_map] at l1
      have l2 := wt_list2_le (natList ((rows pf).getD (r - i) []))
        (natList ((rows qf).getD (r - i) []))
      have e1 : (natList ((rows pf).getD (r - i) [])).wt =
          (Val.list (((rows pf).getD (r - i) []).map Val.nat)).wt := rfl
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have wbv : (Val.nat (bt (r - i))).wt ≤ 3 := by have := hbt1 (r - i); have := wt_nat_le (bt (r - i)); omega
    have wl2 := wt_list2_le (natList ((rows pf).getD (r - i) [])) (natList ((rows qf).getD (r - i) []))
    have wacc1 := hM (i + 1) (by omega)
    have := wt_nat_le j
    have := wt_nat_le k
    have := wt_nat_le r
    have := wt_nat_le i
    simp only [pbAcc] at wacc1 wM ⊢
    have hjk : (j : ℕ) / k ≤ j := Nat.div_le_self _ _
    have hjk' : (j : ℕ) % k < k := Nat.mod_lt _ hk0
    have hjk2 : (j : ℕ) / k < k := Nat.div_lt_of_lt_mul j.2
    have hkY : k < Y := by
      have := length_lt_wt_list ((List.finRange k).map fun p => Val.list ((rows p).map natList))
      simp only [List.length_map, List.length_finRange] at this
      have : (rowsVal rows).wt = (Val.list ((List.finRange k).map fun p =>
        Val.list ((rows p).map natList))).wt := rfl
      omega
    have wbn : (Val.nat (hornerN bt r (i + 1))).wt ≤ T + 2 := by
      have := wt_nat_le (hornerN bt r (i + 1)); omega
    have wln : (Val.nat (leadN bt r (i + 1))).wt ≤ r + 3 := by
      have := wt_nat_le (leadN bt r (i + 1)); omega
    have wln0 : (Val.nat (leadN bt r i)).wt ≤ r + 3 := by
      have := wt_nat_le (leadN bt r i); omega
    have whn0 : (Val.nat (hornerN bt r i)).wt ≤ T + 2 := by
      have := wt_nat_le (hornerN bt r i); omega
    have := wt_nat_le (i + 1)
    have := wt_nat_le 0
    have := wt_nat_le 1
    have := wt_nat_le 2
    have eA : (Val.list [a, .nat i, pbAcc bt r i]).wt = (Val.list [a, .nat i, Val.list [.nat (hornerN bt r i), .nat (leadN bt r i)]]).wt := rfl
    have l3 := wt_list2_le (.nat (hornerN bt r (i + 1))) (.nat (leadN bt r (i + 1)))
    have eY : Y = a.wt := rfl
    have eAA : A.wt = (Val.list [a, .nat i, Val.list [.nat (hornerN bt r i), .nat (leadN bt r i)]]).wt := rfl
    have hif : (if leadN bt r i = i then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have hif2 : (if leadN bt r i = i then 1 else 0) * bt (r - i) ≤ 1 :=
      (Nat.mul_le_mul hif (hbt1 (r - i))).trans (by norm_num)
    have hzA : (Val.list [a, .nat i, Val.list [.nat (hornerN bt r i), .nat (leadN bt r i)]]).wt ≤
        2 * (a.wt + i + (Val.list [.nat (hornerN bt r i), .nat (leadN bt r i)]).wt) + 11 := wA
    have eW : (pbAcc bt r i).wt = (Val.list [.nat (hornerN bt r i), .nat (leadN bt r i)]).wt := rfl
    simp only [loopModK] at weq hc ⊢
    omega
  · rintro w c ⟨rfl, hc⟩
    refine ⟨rfl, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have eY : (Val.list [pbCtx rows r, Val.nat j]).wt = Y := rfl
    clear_value T
    set Z := Y + T + 1 with hZ
    have h1 : Y + 1 ≤ Z := by omega
    have h2 : 5 * Y + 30 ≤ 35 * Z := by omega
    have h3 : r + 1 ≤ Z := by omega
    have h4 : loopModK * (Y + 1) * (5 * Y + 30) ≤ 35000 * (Z * Z) := by
      have := Nat.mul_le_mul h1 h2
      simp only [loopModK]; nlinarith
    have h5 : (r + 1) * (loopModK * (Y + 1) * (5 * Y + 30) + 1000 * (Y + T + 10)) ≤
        Z * (35000 * (Z * Z) + 10000 * Z) :=
      Nat.mul_le_mul h3 (by omega)
    have h6 : loopModK * (r + 1 + 1) * (Y + (r + 1) + (2 * T + 2 * r + 20) + 1) ≤
        1000 * Z * (25 * Z) := by
      simp only [loopModK]
      exact Nat.mul_le_mul (by omega) (by omega)
    have h7 : Z * (35000 * (Z * Z) + 10000 * Z) + 1000 * Z * (25 * Z) ≤ pbK * Z ^ 3 := by
      have hZ1 : 1 ≤ Z := by omega
      have : Z * Z ≤ Z * Z * Z := Nat.le_mul_of_pos_right _ hZ1
      simp only [pbK]; nlinarith
    rw [eY] at hc
    omega

/-- Entry `sel` of the bit loop on `[c, j]`. -/
def pselF (bl sel : ℕ) : Expr := .get (.call bl (.var 0)) (.nat sel)

/-- The two numbers of a pair: the Horner sum (`sel = 0`) or the leading ones. -/
def pbSel (rows : Fin k → List (List ℕ)) (r sel : ℕ) (j : Fin (k * k)) : ℕ :=
  if sel = 0 then hornerN (rowBit rows (pairFst j) (pairSnd j)) r (r + 1)
  else leadN (rowBit rows (pairFst j) (pairSnd j)) r (r + 1)

theorem pbSel_le (rows : Fin k → List (List ℕ)) (r sel : ℕ) (j : Fin (k * k)) :
    pbSel rows r sel j ≤ 2 ^ (r + 1) := by
  have hb : ∀ i, rowBit rows (pairFst j) (pairSnd j) i ≤ 1 := fun i => by
    unfold rowBit; split_ifs <;> omega
  unfold pbSel
  split_ifs
  · exact (hornerN_lt_pow hb _).le
  · exact (leadN_le _ _ _).trans (Nat.lt_two_pow_self).le

/-- The constant of the tables. -/
def pbTabK : ℕ := 10 ^ 13

set_option maxHeartbeats 1000000 in
/-- **The tables of the pairs.** `map` of entry `sel ∈ {0, 1}` of the bit loop over the pairs
gives the table of the Horner sums or of the leading ones. -/
theorem pbTab_spec {P : Program} {bm fs bl beq : ℕ} (hmap : P.HasAt bm (mapFuns bm fs))
    {sel : ℕ} (hsel : sel ≤ 1) (hfs : P.funs[fs]? = some (pselF bl sel))
    (hl : P.HasAt bl (pbFuns bl beq)) (heq : P.HasAt beq (eqNatsFuns beq))
    (rows : Fin k → List (List ℕ)) {r : ℕ} (hlen : ∀ p, (rows p).length = r + 1) :
    FunDet P bm (.list [pbCtx rows r, encFun fun j : Fin (k * k) => (j : ℕ)])
      (encFun (pbSel rows r sel))
      (pbTabK * ((pbCtx rows r).wt + k * k + 2 ^ (r + 1) + 1) ^ 4) := by
  have hp1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hp2 : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
  have hcs := (pbCtx rows r).two_le_size
  have hcs' := (pbCtx rows r).size_le_wt
  set C := (pbCtx rows r).wt + k * k + 2 ^ (r + 1) + 1 with hC
  have hj : ∀ j : Fin (k * k), (Val.list [pbCtx rows r, .nat j]).wt + 2 ^ (r + 1) + 1 ≤ 3 * C :=
    fun j => by
      have := wt_list2_le (pbCtx rows r) (.nat j)
      have := wt_nat_le j
      have := j.2
      omega
  have hf : ∀ j : Fin (k * k), FunDet P fs (.list [pbCtx rows r, .nat j])
      (.nat (pbSel rows r sel j)) (pbK * (3 * C) ^ 3 + 100 * C + 100) := by
    intro j
    have d := Det.get' (Det.call (Det.var' (P := P) (env := [Val.list [pbCtx rows r, .nat j]])
      (i := 0) rfl) (pb_spec hl heq rows hlen j)) (Det.nat sel)
      (v := .nat (pbSel rows r sel j)) (by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsel with rfl | rfl <;> simp [pbAcc, pbSel])
    refine FunDet.intro hfs (d.mono ?_)
    have h1 := Nat.mul_le_mul_left pbK (Nat.pow_le_pow_left (hj j) 3)
    have h2 := FunDet.wt_lt (pb_spec (P := P) hl heq rows hlen j)
    have h3 := wt_list2_le (Val.nat (hornerN (rowBit rows (pairFst j) (pairSnd j)) r (r + 1)))
      (Val.nat (leadN (rowBit rows (pairFst j) (pairSnd j)) r (r + 1)))
    have h4 := wt_nat_le (pbSel rows r sel j)
    have h5 := pbSel_le rows r sel j
    have h6 := hj j
    have h7 : (pbAcc (rowBit rows (pairFst j) (pairSnd j)) r (r + 1)).wt ≤ 10 * C := by
      have := wt_nat_le (hornerN (rowBit rows (pairFst j) (pairSnd j)) r (r + 1))
      have := wt_nat_le (leadN (rowBit rows (pairFst j) (pairSnd j)) r (r + 1))
      have := pbSel_le rows r 0 j
      have := pbSel_le rows r 1 j
      simp only [pbSel, if_true, one_ne_zero, if_false] at *
      simp only [pbAcc]
      omega
    have := Nat.lt_two_pow_self (n := r + 1)
    have e7 : (pbAcc (rowBit rows (pairFst j) (pairSnd j)) r (r + 1)).wt =
      (Val.list [.nat (hornerN (rowBit rows (pairFst j) (pairSnd j)) r (r + 1)),
        .nat (leadN (rowBit rows (pairFst j) (pairSnd j)) r (r + 1))]).wt := rfl
    omega
  refine (tabulate_spec hmap (F := fun j => .nat (pbSel rows r sel j)) hf).mono ?_
  have e1 : (Val.list ((List.finRange (k * k)).map fun j => Val.nat (pbSel rows r sel j))) =
    encFun (pbSel rows r sel) := rfl
  rw [e1]
  have w1 := wt_encFun_le' (pbSel rows r sel) (B := C) (fun j => (pbSel_le rows r sel j).trans
    (by omega)) (by omega)
  have w2 := wt_list2_le (pbCtx rows r) (encFun fun j : Fin (k * k) => (j : ℕ))
  have w3 := wt_encFun_le' (fun j : Fin (k * k) => (j : ℕ)) (B := C) (fun j => by
    show (j : ℕ) ≤ C
    have := j.2; omega) (by omega)
  have hC1 : 1 ≤ C := by omega
  have hkk : k * k + 1 ≤ C := by omega
  have p2 : C ≤ C ^ 2 := Nat.le_self_pow (by norm_num) _
  have p3 : C ^ 2 ≤ C ^ 3 := Nat.pow_le_pow_right hC1 (by norm_num)
  have p4 : C ^ 3 ≤ C ^ 4 := Nat.pow_le_pow_right hC1 (by norm_num)
  have q1 : (C + 1) ^ 2 ≤ 4 * C ^ 2 := by nlinarith
  have q2 : k * k * (pbK * (3 * C) ^ 3 + 100 * C + 100) ≤ C * (27 * pbK * C ^ 3 + 200 * C) := by
    have : pbK * (3 * C) ^ 3 + 100 * C + 100 ≤ 27 * pbK * C ^ 3 + 200 * C := by
      have : pbK * (3 * C) ^ 3 = 27 * pbK * C ^ 3 := by ring
      rw [this]; omega
    exact Nat.mul_le_mul (by omega) this
  have q3 : C * (27 * pbK * C ^ 3 + 200 * C) = 27 * pbK * C ^ 4 + 200 * C ^ 2 := by ring
  have q4 : mapK * (k * k + 1) * ((Val.list [pbCtx rows r, encFun fun j : Fin (k * k) => (j : ℕ)]).wt +
      (encFun (pbSel rows r sel)).wt + 1) ≤ 1000 * C * (100 * C ^ 2) := by
    simp only [mapK]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hkk) (by omega)
  have q5 : 1000 * C * (100 * C ^ 2) = 100000 * C ^ 3 := by ring
  simp only [pbTabK, pbK] at *
  omega

end GI.Impl
