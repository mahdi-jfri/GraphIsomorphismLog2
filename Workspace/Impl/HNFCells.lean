module

public import Workspace.Impl.HNFNums

@[expose] public section

/-!
# The cells of the big matrix and of the outputs

The top-level program builds three tables with `hnfTab`.

* The big matrix `M = [[A', I], [0, K I]]` mod `m` (`GI.Proved.hnfBig`), with `A' = [A | E]`
  (`GI.Proved.hnfAp`). Its cell (`hnfBigCellF`) reads the context
  `[A, compl s, K, m, r, c]` and picks the entry by comparing `i, j` with `r` and `c`.
* The transform `U i j = hnfLift K (H' i (r + j))` (`hnfUCellF`), read from the Hermite form `H'`
  of `M`.
* The Hermite form `H i j = H' i j` (`hnfHCellF`).

Each cell is on `[[[C, r, n], i], j]`, the argument that `hnfTab` gives.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved
open GI.Machine (BinOp len len_le_iff)

variable {r c : ℕ}

/-! ### Tests -/

theorem hnf_det_ite_lt {P : Program} {env : List Val} {a b t e : Expr} {x y : ℕ} {v : Val}
    {ca cb ct ce : ℕ} (ha : Det P env a (.nat x) ca) (hb : Det P env b (.nat y) cb)
    (ht : x < y → Det P env t v ct) (he : ¬ x < y → Det P env e v ce) :
    Det P env (.ite (.arith .lt a b) t e) v (ca + cb + ct + ce + v.wt + 6) := by
  have dc := Det.arith (op := .lt) ha hb
  have w : (Val.nat (BinOp.lt.eval x y)).wt ≤ 3 := by
    simp only [BinOp.eval]; split_ifs <;> decide
  by_cases h : x < y
  · have e1 : BinOp.lt.eval x y = 1 := by simp [BinOp.eval, h]
    exact (Det.ite_pos dc (by rw [e1]; decide) (ht h)).mono (by omega)
  · have e1 : BinOp.lt.eval x y = 0 := by simp [BinOp.eval, h]
    rw [e1] at dc
    exact (Det.ite_zero dc (he h)).mono (by
      have : (Val.nat 0).wt = 2 := rfl
      omega)

theorem hnf_det_ite_eq {P : Program} {env : List Val} {a b t e : Expr} {x y : ℕ} {v : Val}
    {ca cb ct ce : ℕ} (ha : Det P env a (.nat x) ca) (hb : Det P env b (.nat y) cb)
    (ht : x = y → Det P env t v ct) (he : ¬ x = y → Det P env e v ce) :
    Det P env (.ite (.arith .eq a b) t e) v (ca + cb + ct + ce + v.wt + 6) := by
  have dc := Det.arith (op := .eq) ha hb
  have w : (Val.nat (BinOp.eq.eval x y)).wt ≤ 3 := by
    simp only [BinOp.eval]; split_ifs <;> decide
  by_cases h : x = y
  · have e1 : BinOp.eq.eval x y = 1 := by simp [BinOp.eval, h]
    exact (Det.ite_pos dc (by rw [e1]; decide) (ht h)).mono (by omega)
  · have e1 : BinOp.eq.eval x y = 0 := by simp [BinOp.eval, h]
    rw [e1] at dc
    exact (Det.ite_zero dc (he h)).mono (by
      have : (Val.nat 0).wt = 2 := rfl
      omega)

/-! ### Reading the cell argument -/

/-- The context `C` of the cell argument `[[[C, r, n], i], j]`. -/
def hnfCellCtxE : Expr := .get (.get (arg 0) (.nat 0)) (.nat 0)
/-- Entry `k` of the context. -/
def hnfCx (k : ℕ) : Expr := .get hnfCellCtxE (.nat k)
def hnfCellIE : Expr := .get (arg 0) (.nat 1)
def hnfCellJE : Expr := arg 1

/-- The cell argument. -/
def hnfCellArg (C : List Val) (r n i j : ℕ) : Val :=
  .list [.list [.list [.list C, .nat r, .nat n], .nat i], .nat j]

theorem hnfCellArg_wt (C : List Val) (r n i j : ℕ) :
    (Val.list C).wt < (hnfCellArg C r n i j).wt ∧ (Val.nat i).wt < (hnfCellArg C r n i j).wt ∧
      (Val.nat j).wt < (hnfCellArg C r n i j).wt := by
  have w1 : (Val.list C).wt < (Val.list [.list C, .nat r, .nat n]).wt := wt_le_wt_list (by simp)
  have w2 : (Val.list [.list C, .nat r, .nat n]).wt <
      (Val.list [.list [.list C, .nat r, .nat n], .nat i]).wt := wt_le_wt_list (by simp)
  have w3 : (Val.list [.list [.list C, .nat r, .nat n], .nat i]).wt <
      (hnfCellArg C r n i j).wt := wt_le_wt_list (by simp [hnfCellArg])
  have w4 : (Val.nat i).wt < (Val.list [.list [.list C, .nat r, .nat n], .nat i]).wt :=
    wt_le_wt_list (by simp)
  have w5 : (Val.nat j).wt < (hnfCellArg C r n i j).wt := wt_le_wt_list (by simp [hnfCellArg])
  omega

theorem hnf_det_cx {P : Program} {C : List Val} {r n i j k : ℕ} {v : Val} (rest : List Val)
    (hv : C[k]? = some v) :
    Det P (hnfCellArg C r n i j :: rest) (hnfCx k) v (5 * (hnfCellArg C r n i j).wt + k + 30) := by
  have w := hnfCellArg_wt C r n i j
  have w2 : (Val.list [.list [.list C, .nat r, .nat n], .nat i]).wt <
      (hnfCellArg C r n i j).wt := wt_le_wt_list (by simp [hnfCellArg])
  have wv : v.wt < (Val.list C).wt := by
    obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    exact wt_getElem_lt C k hk
  have w3 : (Val.list C).wt < (Val.list [.list C, .nat r, .nat n]).wt := wt_le_wt_list (by simp)
  have w4 : (Val.list [.list C, .nat r, .nat n]).wt <
      (Val.list [.list [.list C, .nat r, .nat n], .nat i]).wt := wt_le_wt_list (by simp)
  unfold hnfCellArg at w w2 ⊢
  have d0 := Det.arg' (P := P) (vs := [.list [.list [.list C, .nat r, .nat n], .nat i], .nat j])
    (rest := rest) (j := 0) rfl
  have d1 := Det.get' d0 (Det.nat 0)
    (show [Val.list [.list C, .nat r, .nat n], .nat i][0]? = some (.list [.list C, .nat r, .nat n])
      from rfl)
  have d2 := Det.get' d1 (Det.nat 0)
    (show [Val.list C, .nat r, .nat n][0]? = some (.list C) from rfl)
  have d3 := Det.get' d2 (Det.nat k) hv
  refine d3.mono ?_
  have e0 : (Val.nat 0).wt = 2 := rfl
  have := wt_nat_le k
  omega

theorem hnf_det_ci {P : Program} {C : List Val} {r n i j : ℕ} (rest : List Val) :
    Det P (hnfCellArg C r n i j :: rest) hnfCellIE (.nat i) (5 * (hnfCellArg C r n i j).wt + 30) := by
  have w := hnfCellArg_wt C r n i j
  have w2 : (Val.list [.list [.list C, .nat r, .nat n], .nat i]).wt <
      (hnfCellArg C r n i j).wt := wt_le_wt_list (by simp [hnfCellArg])
  unfold hnfCellArg at w w2 ⊢
  have d0 := Det.arg' (P := P) (vs := [.list [.list [.list C, .nat r, .nat n], .nat i], .nat j])
    (rest := rest) (j := 0) rfl
  have d1 := Det.get' d0 (Det.nat 1)
    (show [Val.list [.list C, .nat r, .nat n], .nat i][1]? = some (.nat i) from rfl)
  refine d1.mono ?_
  have e1 : (Val.nat 1).wt = 3 := rfl
  omega

theorem hnf_det_cj {P : Program} {C : List Val} {r n i j : ℕ} (rest : List Val) :
    Det P (hnfCellArg C r n i j :: rest) hnfCellJE (.nat j) (5 * (hnfCellArg C r n i j).wt + 30) := by
  unfold hnfCellArg
  exact (Det.arg' (P := P) (vs := [.list [.list [.list C, .nat r, .nat n], .nat i], .nat j])
    (rest := rest) (j := 1) rfl).mono (by omega)

/-! ### The big matrix -/

theorem hnf_wt_nat_sub (x y : ℕ) : (Val.nat (BinOp.sub.eval x y)).wt ≤ (Val.nat x).wt := by
  simp only [BinOp.eval, wt_nat]
  have := GI.Machine.len_mono (Nat.sub_le x y)
  omega

/-- The integer `0`. -/
def hnfZeroE : Expr := mk2 (.nat 0) .nil

theorem hnf_encInt_zero : encInt 0 = .list [.nat 0, .list []] := rfl
theorem hnf_encInt_one : encInt 1 = .list [.nat 0, .list [.nat 1]] := rfl

theorem hnf_det_zero {P : Program} {env : List Val} :
    Det P env hnfZeroE (encInt 0) 50 := by
  refine (Det.mk2 (Det.nat 0) Det.nil).mono ?_
  decide

theorem hnf_det_one {P : Program} {env : List Val} :
    Det P env hnfOneE (encInt 1) 100 := by
  refine (Det.mk2 (Det.nat 0) (Det.mk1 (Det.nat 1))).mono ?_
  decide

/-- The entry of `M` before the reduction mod `m`. Context `[A, compl s, K, m, r, c]`. -/
def hnfBigXE : Expr :=
  .ite (.arith .lt hnfCellIE (hnfCx 4))
    (.ite (.arith .lt hnfCellJE (hnfCx 4))
      (.ite (.arith .lt hnfCellJE (hnfCx 5))
        (.get (.get (hnfCx 0) hnfCellIE) hnfCellJE)
        (.ite (.arith .eq (.get (hnfCx 1) (.arith .sub hnfCellJE (hnfCx 5))) hnfCellIE)
          hnfOneE hnfZeroE))
      (.ite (.arith .eq (.arith .sub hnfCellJE (hnfCx 4)) hnfCellIE) hnfOneE hnfZeroE))
    (.ite (.arith .lt hnfCellJE (hnfCx 4)) hnfZeroE
      (.ite (.arith .eq (.arith .sub hnfCellJE (hnfCx 4)) (.arith .sub hnfCellIE (hnfCx 4)))
        (hnfCx 2) hnfZeroE))

/-- The cell of the big matrix: the entry mod `m`. -/
def hnfBigCellF (ints : ℕ) : Expr := .call (ints + 15) (mk2 hnfBigXE (hnfCx 3))

/-- The context of the big matrix. -/
def hnfBigCtx (A : Matrix (Fin r) (Fin c) ℤ) (s : List (Fin r)) (K m : ℤ) : List Val :=
  [encIntMatrix A, hnfComplVal s, encInt K, encInt m, .nat r, .nat c]

theorem hnf_compl_get (s : List (Fin r)) (k : ℕ) (hk : k < (hnfCompl s).length) (i : Fin r) :
    (hnfCompl s)[k]? = some i ↔ ((hnfCompl s)[k] : ℕ) = i := by
  rw [List.getElem?_eq_getElem hk, Option.some.injEq, Fin.ext_iff]

def hnfBigCellCost (Z : ℕ) : ℕ := 1000 * (Z + 40) + 2 * linIntBinaryCost (4 * Z + 100)

set_option maxHeartbeats 4000000 in
/-- **The cell of the big matrix.** -/
theorem hnfBigCell_spec {P : Program} {ints f : ℕ} (hI : linIntSpec P ints)
    (hf : P.funs[f]? = some (hnfBigCellF ints)) (A : Matrix (Fin r) (Fin c) ℤ) (s : List (Fin r))
    (hs : s.Nodup) (hsc : s.length = c) (hcr : c ≤ r) (K m : ℤ) (n : ℕ)
    (i j : Fin (r + r)) :
    FunDet P f (hnfCellArg (hnfBigCtx A s K m) n (r + r) i j)
      (encInt (hnfBig (hnfAp A s) K i j % m))
      (hnfBigCellCost (hnfCellArg (hnfBigCtx A s K m) n (r + r) i j).wt) := by
  set C := hnfBigCtx A s K m with hC
  set Z := (hnfCellArg C n (r + r) i j).wt with hZ
  have di := hnf_det_ci (P := P) (C := C) (r := n) (n := r + r) (i := i) (j := j) []
  have dj := hnf_det_cj (P := P) (C := C) (r := n) (n := r + r) (i := i) (j := j) []
  have dr := hnf_det_cx (P := P) (C := C) (r := n) (n := r + r) (i := i) (j := j) (k := 4) []
    (show C[4]? = some (.nat r) from rfl)
  have dc := hnf_det_cx (P := P) (C := C) (r := n) (n := r + r) (i := i) (j := j) (k := 5) []
    (show C[5]? = some (.nat c) from rfl)
  have dA := hnf_det_cx (P := P) (C := C) (r := n) (n := r + r) (i := i) (j := j) (k := 0) []
    (show C[0]? = some (encIntMatrix A) from rfl)
  have dL := hnf_det_cx (P := P) (C := C) (r := n) (n := r + r) (i := i) (j := j) (k := 1) []
    (show C[1]? = some (hnfComplVal s) from rfl)
  have dK := hnf_det_cx (P := P) (C := C) (r := n) (n := r + r) (i := i) (j := j) (k := 2) []
    (show C[2]? = some (encInt K) from rfl)
  have dm := hnf_det_cx (P := P) (C := C) (r := n) (n := r + r) (i := i) (j := j) (k := 3) []
    (show C[3]? = some (encInt m) from rfl)
  -- weights
  have wC : (Val.list C).wt < Z := (hnfCellArg_wt C n (r + r) i j).1
  have wA : (encIntMatrix A).wt < (Val.list C).wt := wt_le_wt_list (by simp [hC, hnfBigCtx])
  have wK : (encInt K).wt < (Val.list C).wt := wt_le_wt_list (by simp [hC, hnfBigCtx])
  have wm : (encInt m).wt < (Val.list C).wt := wt_le_wt_list (by simp [hC, hnfBigCtx])
  have w0 : (encInt 0).wt ≤ 15 := by decide
  have w1 : (encInt 1).wt ≤ 21 := by decide
  have hAw : ∀ a b, (encInt (A a b)).wt < (encIntMatrix A).wt := fun a b =>
    lt_trans (linVecEntryWt (A a) b) (hnf_row_wt_lt A a)
  have wv : (encInt (hnfBig (hnfAp A s) K i j)).wt ≤ Z + 30 := by
    unfold hnfBig hnfAp
    split_ifs <;> first
      | omega
      | exact (hAw _ _).le.trans (by omega)
  -- the entry before the reduction
  have hx : Det P [hnfCellArg C n (r + r) i j] hnfBigXE (encInt (hnfBig (hnfAp A s) K i j))
      (400 * (Z + 40)) := by
    refine (hnf_det_ite_lt di dr (ct := 200 * (Z + 40)) (ce := 100 * (Z + 40)) ?_ ?_).mono
      (by omega)
    · intro hi
      refine (hnf_det_ite_lt dj dr (ct := 100 * (Z + 40)) (ce := 30 * (Z + 40)) ?_ ?_).mono
        (by omega)
      · intro hj
        refine (hnf_det_ite_lt dj dc (ct := 20 * (Z + 40)) (ce := 40 * (Z + 40)) ?_ ?_).mono
          (by omega)
        · intro hjc
          have e : hnfBig (hnfAp A s) K i j = A ⟨i, hi⟩ ⟨j, hjc⟩ := by
            simp [hnfBig, hnfAp, hi, hj, hjc]
          rw [e]
          have d1 := Det.get' dA di (hnf_mat_get A ⟨i, hi⟩)
          have d2 := Det.get' d1 dj (hnf_vec_get (A ⟨i, hi⟩) ⟨j, hjc⟩)
          refine d2.mono ?_
          have := hnf_row_wt_lt A ⟨i, hi⟩
          have := linVecEntryWt (A ⟨i, hi⟩) ⟨j, hjc⟩
          omega
        · intro hjc
          have hlen : (hnfCompl s).length = r - c := by rw [hnfCompl_length hs, hsc]
          have hk : (j : ℕ) - c < (hnfCompl s).length := by omega
          set y := ((hnfCompl s)[(j : ℕ) - c] : ℕ) with hy
          have dsub := Det.arith (op := .sub) dj dc
          have dg := Det.get' dL dsub (v := .nat y) (by
            simp only [hnfComplVal, natList, BinOp.eval, List.getElem?_map, List.getElem?_eq_getElem hk,
              Option.map_some, hy])
          have wsub : (Val.nat (BinOp.sub.eval j c)).wt ≤ Z := by
            have := (hnfCellArg_wt C n (r + r) i j).2.2
            have := hnf_wt_nat_sub j c
            omega
          have wy : (Val.nat y).wt ≤ Z := by
            have : (Val.nat y).wt < (hnfComplVal s).wt := by
              have hmem : Val.nat y ∈ ((hnfCompl s).map Fin.val).map Val.nat :=
                List.mem_map.mpr ⟨y, List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩, rfl⟩
              exact wt_le_wt_list hmem
            have : (hnfComplVal s).wt < (Val.list C).wt := wt_le_wt_list (by simp [hC, hnfBigCtx])
            omega
          refine (hnf_det_ite_eq dg di (ct := 100) (ce := 100) (fun h => ?_) (fun h => ?_)).mono
            (by omega)
          · have e : hnfBig (hnfAp A s) K i j = 1 := by
              have h' : (hnfCompl s)[(j : ℕ) - c]? = some ⟨i, hi⟩ :=
                (hnf_compl_get s _ hk ⟨i, hi⟩).mpr h
              simp [hnfBig, hnfAp, hi, hj, hjc, h']
            rw [e]; exact hnf_det_one
          · have e : hnfBig (hnfAp A s) K i j = 0 := by
              have h' : ¬ (hnfCompl s)[(j : ℕ) - c]? = some ⟨i, hi⟩ :=
                fun h2 => h ((hnf_compl_get s _ hk ⟨i, hi⟩).mp h2)
              simp [hnfBig, hnfAp, hi, hj, hjc, h']
            rw [e]; exact hnf_det_zero.mono (by omega)
      · intro hj
        have dsub := Det.arith (op := .sub) dj dr
        have wsub : (Val.nat (BinOp.sub.eval j r)).wt ≤ Z := by
          have := (hnfCellArg_wt C n (r + r) i j).2.2
          have := hnf_wt_nat_sub j r
          omega
        refine (hnf_det_ite_eq dsub di (ct := 100) (ce := 100) (fun h => ?_) (fun h => ?_)).mono
          (by omega)
        · have e : hnfBig (hnfAp A s) K i j = 1 := by
            simp only [BinOp.eval] at h
            simp [hnfBig, hi, hj, h]
          rw [e]; exact hnf_det_one
        · have e : hnfBig (hnfAp A s) K i j = 0 := by
            simp only [BinOp.eval] at h
            simp [hnfBig, hi, hj, h]
          rw [e]; exact hnf_det_zero.mono (by omega)
    · intro hi
      refine (hnf_det_ite_lt dj dr (ct := 100) (ce := 50 * (Z + 40)) ?_ ?_).mono (by omega)
      · intro hj
        have e : hnfBig (hnfAp A s) K i j = 0 := by simp [hnfBig, hi, hj]
        rw [e]; exact hnf_det_zero.mono (by omega)
      · intro hj
        have ds1 := Det.arith (op := .sub) dj dr
        have ds2 := Det.arith (op := .sub) di dr
        have w1 := hnf_wt_nat_sub j r
        have w2 := hnf_wt_nat_sub i r
        have w3 := hnfCellArg_wt C n (r + r) i j
        refine (hnf_det_ite_eq ds1 ds2 (ct := 10 * (Z + 40)) (ce := 100) (fun h => ?_)
          (fun h => ?_)).mono (by omega)
        · have e : hnfBig (hnfAp A s) K i j = K := by
            simp only [BinOp.eval] at h
            simp [hnfBig, hi, hj, h]
          rw [e]; exact dK.mono (by omega)
        · have e : hnfBig (hnfAp A s) K i j = 0 := by
            simp only [BinOp.eval] at h
            simp [hnfBig, hi, hj, h]
          rw [e]; exact hnf_det_zero.mono (by omega)
  have dout := Det.call (Det.mk2 hx dm) (hI.rem (hnfBig (hnfAp A s) K i j) m)
  apply FunDet.intro hf
  refine dout.mono ?_
  have wo := (hI.rem (hnfBig (hnfAp A s) K i j) m).wt_lt
  have a1 := wt_list2_le (encInt (hnfBig (hnfAp A s) K i j)) (encInt m)
  have c1 := linIntBinaryCost_mono (show (Val.list [encInt (hnfBig (hnfAp A s) K i j),
    encInt m]).wt ≤ 4 * Z + 100 by omega)
  unfold hnfBigCellCost
  omega

/-! ### The cells of the outputs -/

/-- The context of the output tables: `[H', K, r]`. -/
def hnfOutCtx (Hb : Matrix (Fin (r + r)) (Fin (r + r)) ℤ) (K : ℤ) : List Val :=
  [encIntMatrix Hb, encInt K, .nat r]

/-- The cell of `U`: `hnfLift K (H' i (r + j))`. -/
def hnfUCellF (ints : ℕ) : Expr :=
  .letE (.get (.get (hnfCx 0) hnfCellIE) (.arith .add (hnfCx 2) hnfCellJE))
    (.ite (.call (ints + 16) (mk2 (.call (ints + 11) (mk2 (.var 1) (.var 1))) (hnfCx 1)))
      (.var 1)
      (.call (ints + 12) (mk2 (.var 1) (hnfCx 1))))

/-- The cell of `H`: `H' i j`. -/
def hnfHCellF : Expr := .get (.get (hnfCx 0) hnfCellIE) hnfCellJE

theorem hnf_abs_add_self {L : ℕ} {x : ℤ} (hx : x.natAbs < 2 ^ L) : (x + x).natAbs < 2 ^ (L + 1) := by
  have := Int.natAbs_add_le x x
  rw [pow_succ]; omega

def hnfUCellCost (Y : ℕ) : ℕ := 1000 * (Y + 40) + 6 * linIntBinaryCost (100 * (Y + 10))

set_option maxHeartbeats 4000000 in
/-- **The cell of `U`.** -/
theorem hnfUCell_spec {P : Program} {ints f : ℕ} (hI : linIntSpec P ints)
    (hf : P.funs[f]? = some (hnfUCellF ints)) (Hb : Matrix (Fin (r + r)) (Fin (r + r)) ℤ) (K : ℤ)
    (n : ℕ) (i j : Fin r) {L Y : ℕ} (hL : ∀ a b, (Hb a b).natAbs < 2 ^ L) (hK : K.natAbs < 2 ^ L)
    (hY : (hnfCellArg (hnfOutCtx Hb K) n r i j).wt + 100 * (L + 1) ≤ Y) :
    FunDet P f (hnfCellArg (hnfOutCtx Hb K) n r i j)
      (encInt (hnfLift K (Hb (Fin.castAdd r i) (Fin.natAdd r j)))) (hnfUCellCost Y) := by
  set C := hnfOutCtx Hb K with hC
  set Z := (hnfCellArg C n r i j).wt with hZ
  set x := Hb (Fin.castAdd r i) (Fin.natAdd r j) with hx
  have di := hnf_det_ci (P := P) (C := C) (r := n) (n := r) (i := i) (j := j) []
  have dj := hnf_det_cj (P := P) (C := C) (r := n) (n := r) (i := i) (j := j) []
  have dH := hnf_det_cx (P := P) (C := C) (r := n) (n := r) (i := i) (j := j) (k := 0) []
    (show C[0]? = some (encIntMatrix Hb) from rfl)
  have dr := hnf_det_cx (P := P) (C := C) (r := n) (n := r) (i := i) (j := j) (k := 2) []
    (show C[2]? = some (.nat r) from rfl)
  have dK := hnf_det_cx (P := P) (C := C) (r := n) (n := r) (i := i) (j := j) (k := 1)
    [encInt x] (show C[1]? = some (encInt K) from rfl)
  have dsum := Det.arith (op := .add) dr dj
  have dx := Det.get' (Det.get' dH di (hnf_mat_get Hb (Fin.castAdd r i))) dsum
    (hnf_vec_get (Hb (Fin.castAdd r i)) (Fin.natAdd r j))
  have dv := Det.var' (P := P) (env := [hnfCellArg C n r i j, encInt x]) (i := 1) rfl
  have dadd := Det.call (Det.mk2 dv dv) (hI.add x x)
  have dlt := Det.call (Det.mk2 dadd dK) (hI.lt (x + x) K)
  have dsub := Det.call (Det.mk2 dv dK) (hI.sub x K)
  -- weights
  have wC : (Val.list C).wt < Z := (hnfCellArg_wt C n r i j).1
  have wx : (encInt x).wt ≤ 20 * (L + 1) := hnf_wt_int (hL _ _)
  have wK := hnf_wt_int hK
  have wxx : (encInt (x + x)).wt ≤ 20 * (L + 1 + 1) := hnf_wt_int (hnf_abs_add_self (hL _ _))
  have wxK : (encInt (x - K)).wt ≤ 20 * (L + 1 + 1) := hnf_wt_int (hnf_abs_sub (hL _ _) hK)
  have wHb : (encIntMatrix Hb).wt < (Val.list C).wt := wt_le_wt_list (by simp [hC, hnfOutCtx])
  have wrr : (Val.nat r).wt < (Val.list C).wt := wt_le_wt_list (by simp [hC, hnfOutCtx])
  have wrow := hnf_row_wt_lt Hb (Fin.castAdd r i)
  have went : (encInt x).wt < (linVecVal (Hb (Fin.castAdd r i))).wt :=
    linVecEntryWt (Hb (Fin.castAdd r i)) (Fin.natAdd r j)
  have wsum : (Val.nat (BinOp.add.eval r j)).wt ≤ 2 * Z := by
    simp only [BinOp.eval, wt_nat]
    have := (hnfCellArg_wt C n r i j).2.2
    rw [wt_nat] at this wrr
    have := GI.Machine.len_add_le r j
    omega
  have a1 := wt_list2_le (encInt x) (encInt x)
  have a2 := wt_list2_le (encInt (x + x)) (encInt K)
  have a3 := wt_list2_le (encInt x) (encInt K)
  have c1 := linIntBinaryCost_mono (show (Val.list [encInt x, encInt x]).wt ≤ 100 * (Y + 10) by
    omega)
  have c2 := linIntBinaryCost_mono (show (Val.list [encInt (x + x), encInt K]).wt ≤
    100 * (Y + 10) by omega)
  have c3 := linIntBinaryCost_mono (show (Val.list [encInt x, encInt K]).wt ≤ 100 * (Y + 10) by
    omega)
  have wl : (Val.nat (if x + x < K then 1 else 0)).wt ≤ 3 := by split_ifs <;> decide
  have wenv : (Val.list [hnfCellArg C n r i j, encInt x]).wt ≤ 2 * (Z + 20 * (L + 1)) + 6 :=
    by have := wt_list2_le (hnfCellArg C n r i j) (encInt x); omega
  have e1 : (Val.nat 1).wt = 3 := rfl
  have e0 : (Val.nat 0).wt = 2 := rfl
  have dite : Det P [hnfCellArg C n r i j, encInt x]
      (.ite (.call (ints + 16) (mk2 (.call (ints + 11) (mk2 (.var 1) (.var 1))) (hnfCx 1)))
        (.var 1) (.call (ints + 12) (mk2 (.var 1) (hnfCx 1))))
      (encInt (hnfLift K x)) (100 * (Y + 40) + 3 * linIntBinaryCost (100 * (Y + 10))) := by
    by_cases h : x + x < K
    · have e : hnfLift K x = x := by unfold hnfLift; rw [if_pos (by omega)]
      rw [e]
      rw [if_pos h] at dlt
      refine (Det.ite_pos dlt one_ne_zero dv).mono ?_
      omega
    · have e : hnfLift K x = x - K := by unfold hnfLift; rw [if_neg (by omega)]
      rw [e]
      rw [if_neg h] at dlt
      refine (Det.ite_zero dlt dsub).mono ?_
      omega
  have dout := Det.letE dx dite
  apply FunDet.intro hf
  refine dout.mono ?_
  have : (encInt (hnfLift K x)).wt ≤ 20 * (L + 1 + 1) := by
    unfold hnfLift; split_ifs <;> omega
  have e2 : (Val.list ((List.finRange (r + r)).map fun y => encInt (Hb (Fin.castAdd r i) y))).wt =
    (linVecVal (Hb (Fin.castAdd r i))).wt := rfl
  have e3 : (encInt (Hb (Fin.castAdd r i) (Fin.natAdd r j))).wt = (encInt x).wt := rfl
  have e4 : (hnfCellArg C n r i j).wt = Z := rfl
  unfold hnfUCellCost
  omega

def hnfHCellCost (Y : ℕ) : ℕ := 100 * (Y + 40)

/-- **The cell of `H`.** -/
theorem hnfHCell_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some hnfHCellF) (hcr : c ≤ r)
    (Hb : Matrix (Fin (r + r)) (Fin (r + r)) ℤ) (K : ℤ) (n : ℕ) (i : Fin r) (j : Fin c) :
    FunDet P f (hnfCellArg (hnfOutCtx Hb K) n c i j)
      (encInt (Hb (Fin.castAdd r i) (Fin.castAdd r (Fin.castLE hcr j))))
      (hnfHCellCost (hnfCellArg (hnfOutCtx Hb K) n c i j).wt) := by
  set C := hnfOutCtx Hb K with hC
  set Z := (hnfCellArg C n c i j).wt with hZ
  have di := hnf_det_ci (P := P) (C := C) (r := n) (n := c) (i := i) (j := j) []
  have dj := hnf_det_cj (P := P) (C := C) (r := n) (n := c) (i := i) (j := j) []
  have dH := hnf_det_cx (P := P) (C := C) (r := n) (n := c) (i := i) (j := j) (k := 0) []
    (show C[0]? = some (encIntMatrix Hb) from rfl)
  have dx := Det.get' (Det.get' dH di (hnf_mat_get Hb (Fin.castAdd r i))) dj
    (hnf_vec_get (Hb (Fin.castAdd r i)) (Fin.castAdd r (Fin.castLE hcr j)))
  apply FunDet.intro hf
  refine dx.mono ?_
  have wC : (Val.list C).wt < Z := (hnfCellArg_wt C n c i j).1
  have wHb : (encIntMatrix Hb).wt < (Val.list C).wt := wt_le_wt_list (by simp [hC, hnfOutCtx])
  have wrow := hnf_row_wt_lt Hb (Fin.castAdd r i)
  have went := linVecEntryWt (Hb (Fin.castAdd r i)) (Fin.castAdd r (Fin.castLE hcr j))
  have e2 : (Val.list ((List.finRange (r + r)).map fun y => encInt (Hb (Fin.castAdd r i) y))).wt =
    (linVecVal (Hb (Fin.castAdd r i))).wt := rfl
  unfold hnfHCellCost
  omega

end GI.Impl
