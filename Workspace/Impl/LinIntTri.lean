module

public import Workspace.Impl.LinIntTriCost

@[expose] public section

/-! Recursive triangular substitution in GI.Lang. The control flow follows
linUpperSolve: exact pivot division, a smaller residual system, and a lifted
coefficient vector. The helper programs are installed function bodies. -/
namespace GI.Impl
open GI.Cited GI.Lang
open Matrix

structure linTriIndices where
  ints : ℕ
  exactDiv : ℕ
  tail : ℕ
  trim : ℕ
  trimMap : ℕ
  scale : ℕ
  sub : ℕ
  append : ℕ

structure linTriInstalled (P : Program) (I : linTriIndices) : Prop where
  ints : linIntSpec P I.ints
  exactDiv : P.funs[I.exactDiv]? = some (linIntExactF (I.ints + 14) (I.ints + 15))
  tail : P.HasAt I.tail (linTailFuns I.tail)
  trim : P.funs[I.trim]? = some (linTrimF I.tail I.trimMap)
  trimMap : P.HasAt I.trimMap (linTrimMapFuns I.trimMap I.tail)
  scale : P.HasAt I.scale (linVectorScaleFuns I.scale I.ints)
  sub : P.HasAt I.sub (linVectorBinaryFuns I.sub (I.ints + 12))
  append : P.HasAt I.append (appendFuns I.append)

/-- A zero natural denotes failure. A successful answer is [1,coefficient-row]. -/
def linTriVal {n : ℕ} : Option (Fin n → ℤ) → Val
  | none => .nat 0
  | some z => .list [.nat 1, linVecVal z]

/-- The quotient in the successful exact-division answer held in variable 1. -/
def linTriQuotE : Expr := .get (.var 1) (.nat 1)

/-- Variables 2--7 hold the trailing matrix, trailing right-hand side,
trailing first row, scaled row, residual, and recursive answer. -/
def linTriAfterPivotF (self : ℕ) (I : linTriIndices) : Expr :=
  [Expr.call I.trim (arg 0), .call I.tail (arg 1), .call I.tail (.get (arg 0) (.nat 0)),
    .call I.scale (mk2 linTriQuotE (.var 4)), .call I.sub (mk2 (.var 3) (.var 5)),
    .call self (mk2 (.var 2) (.var 6))].foldr Expr.letE
    (.ite (.isNat (.var 7)) (.nat 0)
      (mk2 (.nat 1) (.call I.append (mk2 (mk1 linTriQuotE) (.get (.var 7) (.nat 1))))))

def linTriWorkF (self : ℕ) (I : linTriIndices) : Expr :=
  .letE (.call I.exactDiv (mk2 (.get (arg 1) (.nat 0))
    (.get (.get (arg 0) (.nat 0)) (.nat 0))))
    (.ite (.isNat (.var 1)) (.nat 0) (linTriAfterPivotF self I))

def linTriUpperF (self : ℕ) (I : linTriIndices) : Expr :=
  .ite (.length (arg 1)) (linTriWorkF self I) (mk2 (.nat 1) .nil)

set_option maxHeartbeats 5000000 in
/-- The recursive language program returns exactly the pure solver's answer,
with an explicit polynomial bit cost. -/
theorem linTriUpper_spec {P : Program} {f : ℕ} {I : linTriIndices}
    (h : linTriInstalled P I) (hf : P.funs[f]? = some (linTriUpperF f I))
    (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℤ)
    (B C : ℕ) (hH : EntriesBits B H) (hw : ∀ i, (w i).natAbs < 2 ^ C) :
    FunDet P f (.list [encIntMatrix H, linVecVal w])
      (linTriVal (linUpperSolve n H w)) (linTriCost n B C) := by
  induction n generalizing B C with
  | zero =>
    have dl := Det.length (Det.arg' (P := P) (vs := [encIntMatrix H, linVecVal w])
      (rest := []) (j := 1) rfl)
    have db := Det.mk2 (Det.nat (P := P) (env := [.list [encIntMatrix H, linVecVal w]]) 1) Det.nil
    apply FunDet.intro hf
    refine (Det.ite_zero (t := linTriWorkF f I) dl db).mono ?_
    have wi : (Val.list [encIntMatrix H, linVecVal w]).wt ≤ 100 := by change (Val.list [.list [], .list []]).wt ≤ 100; decide
    have wo : (Val.list [.nat 1, .list []]).wt ≤ 100 := by decide
    have hu : 10000 ≤ linTriUnitCost (linTriSize 0 B C) := by dsimp [linTriUnitCost]; omega
    simp only [linTriCost, Nat.zero_add, Nat.one_mul, List.length_map, List.length_finRange]
    omega
  | succ n ih =>
    let a := Val.list [encIntMatrix H, linVecVal w]
    let q := w 0 / H 0 0
    let T := linTail H
    let u : Fin n → ℤ := fun i => w i.succ
    let v : Fin n → ℤ := fun i => H 0 i.succ
    let s : Fin n → ℤ := fun i => q * v i
    let r := linResidual H w q
    have hargH (rest : List Val) := Det.arg' (P := P) (vs := [encIntMatrix H, linVecVal w]) (rest := rest) (j := 0) rfl
    have hargW (rest : List Val) := Det.arg' (P := P) (vs := [encIntMatrix H, linVecVal w]) (rest := rest) (j := 1) rfl
    have hrow (rest : List Val) := Det.get' (hargH rest) (Det.nat 0)
      (show ((List.finRange (n + 1)).map fun i => linVecVal (H i))[0]? = some (linVecVal (H 0)) by
        simp [List.finRange_succ])
    have hhead (rest : List Val) := Det.get' (hargW rest) (Det.nat 0)
      (show ((List.finRange (n + 1)).map fun i => encInt (w i))[0]? = some (encInt (w 0)) by
        simp [List.finRange_succ])
    have hpivot (rest : List Val) := Det.get' (hrow rest) (Det.nat 0)
      (show ((List.finRange (n + 1)).map fun i => encInt (H 0 i))[0]? = some (encInt (H 0 0)) by
        simp [List.finRange_succ])
    have dl := Det.length (hargW [])
    simp only [List.length_map, List.length_finRange] at dl
    let budgetT := linTriSize (n + 1) B C
    let budgetD := linTriDataBudget budgetT
    let budgetA := linTriArgBudget budgetT
    let budgetU := linTriUnitCost budgetT
    have hnT : n + 1 ≤ budgetT := by dsimp [budgetT, linTriSize]; omega
    have hBT : B ≤ budgetT := by dsimp [budgetT, linTriSize]; omega
    have hCT : C ≤ budgetT := by dsimp [budgetT, linTriSize]; omega
    have hFT : C + (n + 1) * (B + 1) ≤ budgetT := by dsimp [budgetT, linTriSize]; omega
    have hRT : C + B + 1 ≤ budgetT := by dsimp [budgetT, linTriSize]; nlinarith
    have hDA : budgetD ≤ budgetA := linTriDataBudget_le_arg budgetT
    have hTA : budgetT ≤ budgetA := linTriSize_le_arg budgetT
    have hAbig : 100 ≤ budgetA := by dsimp [budgetA, linTriArgBudget]; omega
    have hDdef : budgetA = 20 * budgetD + 100 := rfl
    have bH := linTriMatrixBudget hnT hBT H hH
    have bw := linTriVectorBudget hnT hCT w hw
    have bT := linTriMatrixBudget (show n ≤ budgetT by omega) hBT T (fun i j => hH i.succ j.succ)
    have bu := linTriVectorBudget (show n ≤ budgetT by omega) hCT u (fun i => hw i.succ)
    have bv := linTriVectorBudget (show n ≤ budgetT by omega) hBT v (fun i => hH 0 i.succ)
    have bRow := linTriVectorBudget hnT hBT (H 0) (fun i => hH 0 i)
    have qbits : q.natAbs < 2 ^ C := (Int.natAbs_ediv_le_natAbs _ _).trans_lt (hw 0)
    have bq := linTriScalarBudget hCT q qbits
    have bp := linTriScalarBudget hBT (H 0 0) (hH 0 0)
    have bw0 := linTriScalarBudget hCT (w 0) (hw 0)
    have sbits (i : Fin n) : (s i).natAbs < 2 ^ (C + B) := by
      rw [pow_add]
      change (q * H 0 i.succ).natAbs < _
      rw [Int.natAbs_mul]
      exact Nat.mul_lt_mul'' qbits (hH 0 i.succ)
    have bs := linTriVectorBudget (show n ≤ budgetT by omega) (show C + B ≤ budgetT by omega) s sbits
    have rbits := linTriResidualBits H w B C hH hw
    have br := linTriVectorBudget (show n ≤ budgetT by omega) hRT r rbits
    have ba := wt_list2_le (encIntMatrix H) (linVecVal w)
    have be := wt_list2_le (.nat 1) (encInt q)
    have bExactArg := wt_list2_le (encInt (w 0)) (encInt (H 0 0))
    have bScaleArg := wt_list2_le (encInt q) (linVecVal v)
    have bSubArg := wt_list2_le (linVecVal u) (linVecVal s)
    have bRecArg := wt_list2_le (encIntMatrix T) (linVecVal r)
    have w0 : (Val.nat 0).wt = 2 := rfl
    have w1 : (Val.nat 1).wt = 3 := rfl
    have bArgExact : (Val.list [encInt (w 0), encInt (H 0 0)]).wt ≤ budgetA := by omega
    have bArgScale : (Val.list [encInt q, linVecVal v]).wt ≤ budgetA := by omega
    have bArgSub : (Val.list [linVecVal u, linVecVal s]).wt ≤ budgetA := by omega
    have hExactCost := linIntDivModCost_mono bArgExact
    have hTrimCost := linTrimCost_mono (bH.trans hDA) (show n ≤ budgetT by omega)
    have hTailWCost := linTailCost_mono (bw.trans hDA)
    have hTailRowCost := linTailCost_mono (bRow.trans hDA)
    have hScaleCost := linVectorScaleCost_mono bArgScale (show n ≤ budgetT by omega)
    have hSubCost := linVectorBinaryCost_mono bArgSub (show n ≤ budgetT by omega)
      (show 20 * ((Val.list [linVecVal u, linVecVal s]).wt + 2) ≤ 20 * (budgetA + 2) by omega)
    have hRecCost : linTriCost n B (C + B + 1) ≤ (n + 1) * budgetU := by
      apply Nat.mul_le_mul_left
      apply linTriUnitCost_mono
      have he := linTriSize_step n B C
      change linTriSize n B (C + B + 1) ≤ budgetT
      omega
    have hUdef : budgetU = 10000 * (linIntDivModCost budgetA + linTailCost budgetA +
        linTrimCost budgetA budgetT + linVectorScaleCost budgetA budgetT +
        linVectorBinaryCost budgetA budgetT (20 * (budgetA + 2)) +
        loopModK * (budgetT + 1) * (budgetA + budgetT + budgetD + 1) + budgetA + budgetT + 1) := rfl
    have hex := linIntExact_spec h.ints h.exactDiv (w 0) (H 0 0)
    by_cases hdiv : H 0 0 ∣ w 0
    · rw [if_pos hdiv] at hex
      let e := Val.list [.nat 1, encInt q]
      have de := Det.call (Det.mk2 (hhead []) (hpivot [])) hex
      have dex := Det.isNat (Det.var' (P := P) (env := [a, e]) (i := 1) rfl)
      have dt := Det.call (hargH [e]) (linTrim_spec h.trim h.tail h.trimMap H)
      have du := Det.call (hargW [e, encIntMatrix T]) (linTail_vec_spec h.tail w)
      have dv := Det.call (hrow [e, encIntMatrix T, linVecVal u]) (linTail_vec_spec h.tail (H 0))
      have dq (rest : List Val) := Det.get'
        (Det.var' (P := P) (env := a :: e :: rest) (i := 1) rfl) (Det.nat 1)
        (show [Val.nat 1, encInt q][1]? = some (encInt q) from rfl)
      have ds := Det.call (Det.mk2 (dq [encIntMatrix T, linVecVal u, linVecVal v])
        (Det.var' (P := P) (env := [a, e, encIntMatrix T, linVecVal u, linVecVal v]) (i := 4) rfl))
        (linVectorScale_spec h.ints h.scale q v)
      have dr := Det.call (Det.mk2
        (Det.var' (P := P) (env := [a, e, encIntMatrix T, linVecVal u, linVecVal v, linVecVal s]) (i := 3) rfl)
        (Det.var' (P := P) (env := [a, e, encIntMatrix T, linVecVal u, linVecVal v, linVecVal s]) (i := 5) rfl))
        (linVectorSub_spec h.ints h.sub u s)
      have hr := ih T r B (C + B + 1) (fun i j => hH i.succ j.succ) rbits
      have hr' := FunDet.mono hr hRecCost
      have hp : (w 0 / H 0 0) * H 0 0 = w 0 := (linTriPivot_iff _ _).mpr hdiv
      cases hsolve : linUpperSolve n T r with
      | none =>
        rw [hsolve] at hr
        rw [hsolve] at hr'
        have drec := Det.call (Det.mk2
          (Det.var' (P := P) (env := [a, e, encIntMatrix T, linVecVal u, linVecVal v, linVecVal s, linVecVal r]) (i := 2) rfl)
          (Det.var' (P := P) (env := [a, e, encIntMatrix T, linVecVal u, linVecVal v, linVecVal s, linVecVal r]) (i := 6) rfl)) hr'
        have dtest := Det.isNat (Det.var' (P := P)
          (env := [a, e, encIntMatrix T, linVecVal u, linVecVal v, linVecVal s, linVecVal r, .nat 0]) (i := 7) rfl)
        have db := Det.ite_pos (e := mk2 (.nat 1) (.call I.append
          (mk2 (mk1 linTriQuotE) (.get (.var 7) (.nat 1))))) dtest (by decide) (Det.nat 0)
        have d := Det.ite_pos (e := mk2 (.nat 1) .nil) dl (by omega)
          (Det.letE de (Det.ite_zero (t := .nat 0) dex
            (Det.letE dt (Det.letE du (Det.letE dv (Det.letE ds (Det.letE dr (Det.letE drec db))))))))
        have ho : linUpperSolve (n + 1) H w = none := by
          simpa only [linUpperSolve, if_pos hp, Option.map_none] using congrArg (fun o : Option (Fin n → ℤ) => o.map (Fin.cons (n := n) (α := fun _ => ℤ) q)) hsolve
        rw [ho]
        apply FunDet.intro hf
        refine d.mono ?_
        change _ ≤ (n + 1 + 1) * budgetU
        rw [show (n + 1 + 1) * budgetU = (n + 1) * budgetU + budgetU by ring]
        simp only [linTriVal, Val.isNatNum, List.length_map, List.length_finRange] at *
        simp only [a, e, T, u, v, s, r, q, linResidual, linVecVal] at *
        omega
      | some z =>
        rw [hsolve] at hr
        rw [hsolve] at hr'
        let out := Val.list [.nat 1, linVecVal z]
        have drec := Det.call (Det.mk2
          (Det.var' (P := P) (env := [a, e, encIntMatrix T, linVecVal u, linVecVal v, linVecVal s, linVecVal r]) (i := 2) rfl)
          (Det.var' (P := P) (env := [a, e, encIntMatrix T, linVecVal u, linVecVal v, linVecVal s, linVecVal r]) (i := 6) rfl)) hr'
        have dtest := Det.isNat (Det.var' (P := P)
          (env := [a, e, encIntMatrix T, linVecVal u, linVecVal v, linVecVal s, linVecVal r, out]) (i := 7) rfl)
        have dz := Det.get' (Det.var' (P := P)
          (env := [a, e, encIntMatrix T, linVecVal u, linVecVal v, linVecVal s, linVecVal r, out]) (i := 7) rfl)
          (Det.nat 1) (show [Val.nat 1, linVecVal z][1]? = some (linVecVal z) from rfl)
        have dapp := Det.call (Det.mk2
          (Det.mk1 (dq [encIntMatrix T, linVecVal u, linVecVal v, linVecVal s, linVecVal r, out])) dz)
          (linAppend_det h.append [encInt q] ((List.finRange n).map fun i => encInt (z i)))
        have db := Det.ite_zero (t := .nat 0) dtest (Det.mk2 (Det.nat 1) dapp)
        have d := Det.ite_pos (e := mk2 (.nat 1) .nil) dl (by omega)
          (Det.letE de (Det.ite_zero (t := .nat 0) dex
            (Det.letE dt (Det.letE du (Det.letE dv (Det.letE ds (Det.letE dr (Det.letE drec db))))))))
        have ho : linUpperSolve (n + 1) H w = some (Fin.cons q z) := by
          simpa only [linUpperSolve, if_pos hp, Option.map_some] using congrArg (fun o : Option (Fin n → ℤ) => o.map (Fin.cons (n := n) (α := fun _ => ℤ) q)) hsolve
        rw [ho]
        have hvec : linVecVal (Fin.cons q z) = .list ([encInt q] ++ (List.finRange n).map (fun i => encInt (z i))) := by
          simp [linVecVal, List.finRange_succ, List.map_map]
        rw [linTriVal, hvec]
        apply FunDet.intro hf
        refine d.mono ?_
        have zbits := linTriSolutionBits n T r B (C + B + 1) (fun i j => hH i.succ j.succ) rbits z hsolve
        have bZ := linTriVectorBudget (show n ≤ budgetT by omega) (show C + B + 1 + n * (B + 1) ≤ budgetT by nlinarith) z zbits
        have bFull := linTriVectorBudget hnT hFT (Fin.cons q z)
          (linTriSolutionBits (n + 1) H w B C hH hw (Fin.cons q z) ho)
        have bOut := wt_list2_le (.nat 1) (linVecVal z)
        have bOne := wt_list1_le (encInt q)
        have bAppendArg := wt_list2_le (.list [encInt q]) (linVecVal z)
        have bApp : (Val.list [.list [encInt q], linVecVal z]).wt ≤ budgetA := by omega
        have bAppOut : (Val.list ([encInt q] ++ (List.finRange n).map fun i => encInt (z i))).wt ≤ budgetD := by rw [← hvec]; exact bFull
        have hAppendCost : loopModK * (n + 1) * ((Val.list [.list [encInt q], linVecVal z]).wt + n +
            (Val.list ([encInt q] ++ (List.finRange n).map fun i => encInt (z i))).wt + 1) ≤
            loopModK * (budgetT + 1) * (budgetA + budgetT + budgetD + 1) := by gcongr <;> omega
        have bFinal := wt_list2_le (.nat 1) (Val.list ([encInt q] ++ (List.finRange n).map fun i => encInt (z i)))
        change _ ≤ (n + 1 + 1) * budgetU
        rw [show (n + 1 + 1) * budgetU = (n + 1) * budgetU + budgetU by ring]
        simp only [linTriVal, Val.isNatNum, List.length_map, List.length_finRange] at *
        simp only [a, e, out, T, u, v, s, r, q, linResidual, linVecVal] at *
        omega
    · rw [if_neg hdiv] at hex
      have de := Det.call (Det.mk2 (hhead []) (hpivot [])) hex
      have dex := Det.isNat (Det.var' (P := P) (env := [a, .nat 0]) (i := 1) rfl)
      have db := Det.ite_pos (e := linTriAfterPivotF f I) dex (by decide) (Det.nat 0)
      have d := Det.ite_pos (e := mk2 (.nat 1) .nil) dl (by omega) (Det.letE de db)
      have hp : ¬ (w 0 / H 0 0) * H 0 0 = w 0 := by rw [linTriPivot_iff]; exact hdiv
      have ho : linUpperSolve (n + 1) H w = none := by simp only [linUpperSolve, if_neg hp]
      rw [ho]
      apply FunDet.intro hf
      refine d.mono ?_
      change _ ≤ (n + 1 + 1) * budgetU
      simp only [Val.isNatNum] at *
      have hu : budgetU ≤ (n + 1 + 1) * budgetU := Nat.le_mul_of_pos_left _ (by omega)
      omega

/-- Termination and exact value agreement, without requiring bit bounds from the caller. -/
theorem linTriUpper_eval {P : Program} {f : ℕ} {I : linTriIndices}
    (h : linTriInstalled P I) (hf : P.funs[f]? = some (linTriUpperF f I))
    (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℤ) :
    ∃ cost, FunDet P f (.list [encIntMatrix H, linVecVal w]) (linTriVal (linUpperSolve n H w)) cost := by
  have hH : EntriesBits (encIntMatrix H).wt H := by
    intro i j
    have hr : (linVecVal (H i)).wt < (encIntMatrix H).wt :=
      wt_le_wt_list (by exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    have he := (linVecEntryWt (H i) j).trans hr
    exact (linEncIntAbs (H i j)).trans_le (Nat.pow_le_pow_right (by decide) he.le)
  have hw (i : Fin n) : (w i).natAbs < 2 ^ (linVecVal w).wt :=
    (linEncIntAbs (w i)).trans_le (Nat.pow_le_pow_right (by decide) (linVecEntryWt w i).le)
  exact ⟨_, linTriUpper_spec h hf n H w (encIntMatrix H).wt (linVecVal w).wt hH hw⟩

/-- The observable row-system answer: failure proves insolubility, and success carries a solution. -/
def linTriAnswer {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℤ) (out : Val) : Prop :=
  (out = .nat 0 ∧ ¬ ∃ z, z ᵥ* H = w) ∨
    ∃ z : Fin n → ℤ, out = .list [.nat 1, linVecVal z] ∧ z ᵥ* H = w

/-- Upper triangular integer systems are solved completely, including a proved failure. -/
theorem linTriUpper_solve_spec {P : Program} {f : ℕ} {I : linTriIndices}
    (h : linTriInstalled P I) (hf : P.funs[f]? = some (linTriUpperF f I))
    (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℤ)
    (htri : ∀ i j, j < i → H i j = 0) (hdiag : ∀ i, H i i ≠ 0)
    (B C : ℕ) (hH : EntriesBits B H) (hw : ∀ i, (w i).natAbs < 2 ^ C) :
    FunAll P f (.list [encIntMatrix H, linVecVal w])
      (fun out cost => linTriAnswer H w out ∧ cost ≤ linTriCost n B C) := by
  refine FunAll.mono (linTriUpper_spec h hf n H w B C hH hw) fun out cost ho => ⟨?_, ho.2⟩
  cases hs : linUpperSolve n H w with
  | none =>
    rw [hs] at ho
    exact Or.inl ⟨ho.1, (linUpperSolve_none_iff n H htri hdiag w).mp hs⟩
  | some z =>
    rw [hs] at ho
    exact Or.inr ⟨z, ho.1, linUpperSolve_sound n H htri w z hs⟩

/-- A bit-weight-only polynomial cost bound for an encoded upper triangular system. -/
theorem linTriUpper_bit_spec {P : Program} {f : ℕ} {I : linTriIndices}
    (h : linTriInstalled P I) (hf : P.funs[f]? = some (linTriUpperF f I))
    (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℤ)
    (htri : ∀ i j, j < i → H i j = 0) (hdiag : ∀ i, H i i ≠ 0) :
    FunAll P f (.list [encIntMatrix H, linVecVal w]) (fun out cost =>
      linTriAnswer H w out ∧
      cost ≤ linTriCost (Val.list [encIntMatrix H, linVecVal w]).wt
        (Val.list [encIntMatrix H, linVecVal w]).wt (Val.list [encIntMatrix H, linVecVal w]).wt) := by
  let W := (Val.list [encIntMatrix H, linVecVal w]).wt
  have hm : (encIntMatrix H).wt < W := wt_le_wt_list (by simp)
  have hv : (linVecVal w).wt < W := wt_le_wt_list (by simp)
  have hn : n ≤ W := by
    have hl := length_lt_wt_list ((List.finRange n).map fun i => encInt (w i))
    simp only [List.length_map, List.length_finRange] at hl
    exact (hl.trans hv).le
  have hH : EntriesBits W H := by
    intro i j
    have hr : (linVecVal (H i)).wt < (encIntMatrix H).wt :=
      wt_le_wt_list (by exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    have he := ((linVecEntryWt (H i) j).trans hr).trans hm
    exact (linEncIntAbs (H i j)).trans_le (Nat.pow_le_pow_right (by decide) he.le)
  have hw (i : Fin n) : (w i).natAbs < 2 ^ W :=
    (linEncIntAbs (w i)).trans_le (Nat.pow_le_pow_right (by decide) ((linVecEntryWt w i).trans hv).le)
  refine FunAll.mono (linTriUpper_solve_spec h hf n H w htri hdiag W W hH hw) fun out cost ho => ?_
  exact ⟨ho.1, ho.2.trans (linTriCost_mono hn le_rfl le_rfl)⟩

end GI.Impl
