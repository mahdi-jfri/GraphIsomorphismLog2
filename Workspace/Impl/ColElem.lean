module

public import Workspace.Impl.ColVal
public import Workspace.Lang.Lib.Fold
public import Workspace.Lang.Lib.Tabulate

@[expose] public section

/-!
# The entry functions of the column step

The column step computes arrays over the positions `Fin n` and over the row coordinates
`Fin m`. Each array is a tabulation (`tab_det`) of a small function on `[ctx, i]`. This file
gives these functions and their deterministic specifications. Each cost is linear in the
weight `W` of the argument `[ctx, i]` (or of the call of a library module inside).

* `colPickF`: `arr[idx[i]] + s` on `[[arr, idx, s], i]`;
* `colEqF`: `[a₁[i] = a₁[0] ∧ a₂[i] = a₂[0]]` on `[[a₁, a₂], i]`;
* `colKeyF`: `(rl[i] (n+1) + hl[i]) (n+1) + oc[i] + (n+1)` on `[[rl, hl, oc, n + 1], i]`;
* `colInvF`: the column coordinate `findIdx (· = i) rows[rl[i]]` of a domain position, `0`
  off the domain, on `[[dv, rl, rows], i]`;
* `colMinStepF`, `colMinF`: the least `bk[o]` over the `o` with `orb[o] = orb[c]`;
* `colLowPosF`, `colNotLowF`: the test that a stored level does not refine the rows.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val)

/-- Entry `j` of the context (entry `0` of the argument). -/
def colC (j : ℕ) : Expr := .get (arg 0) (.nat j)

section Access

variable {P : Program}

theorem colC_det' {ctx more : List Val} {rest : List Val} {j : ℕ} {v : Val}
    (h : ctx[j]? = some v) :
    Det P (.list (.list ctx :: more) :: rest) (colC j) v
      (4 * (Val.list (.list ctx :: more)).wt + j + 10) := by
  have h1 := Det.get' (P := P) (Det.arg' (vs := .list ctx :: more) (rest := rest) (j := 0) rfl)
    (Det.nat j) h
  refine h1.mono ?_
  have : v.wt < (Val.list ctx).wt := by
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
    exact wt_getElem_lt _ _ hj
  have : (Val.list ctx).wt < (Val.list (.list ctx :: more)).wt := wt_le_wt_list (by simp)
  omega

theorem colC_det {ctx : List Val} {x : Val} {rest : List Val} {j : ℕ} {v : Val}
    (h : ctx[j]? = some v) :
    Det P (.list [.list ctx, x] :: rest) (colC j) v (4 * (Val.list [.list ctx, x]).wt + j + 10) :=
  colC_det' (more := [x]) h

theorem colArg1_det {c x : Val} {rest : List Val} :
    Det P (.list [c, x] :: rest) (arg 1) x (3 * (Val.list [c, x]).wt + 6) := by
  have := Det.arg' (P := P) (vs := [c, x]) (rest := rest) (j := 1) rfl
  exact this.mono (by omega)

/-- An entry of an array. -/
theorem colAt_det {env : List Val} {aE iE : Expr} {k : ℕ} {f : Fin k → ℕ} {i : Fin k}
    {ca cb : ℕ} (ha : Det P env aE (encFun f) ca) (hb : Det P env iE (.nat i) cb) :
    Det P env (.get aE iE) (.nat (f i)) (ca + cb + (Val.nat (f i)).wt + 1) :=
  Det.get' ha hb (encFun_getElem? f i)

theorem colWt_nat_mono {a b : ℕ} (h : a ≤ b) : (Val.nat a).wt ≤ (Val.nat b).wt := by
  rw [wt_nat, wt_nat]
  have := GI.Machine.len_mono h
  omega

theorem colWt_at_lt {k : ℕ} (f : Fin k → ℕ) (i : Fin k) : (Val.nat (f i)).wt < (encFun f).wt := by
  unfold encFun
  exact wt_le_wt_list (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)

end Access

/-! ### `arr[idx[i]] + s` -/

/-- On `[[arr, idx, s], i]`: `arr[idx[i]] + s`. -/
def colPickF : Expr := .arith .add (.get (colC 0) (.get (colC 1) (arg 1))) (colC 2)

theorem colPick_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some colPickF) {p k : ℕ}
    (a : Fin p → ℕ) (x : Fin k → Fin p) (s : ℕ) (i : Fin k) :
    FunDet P f (.list [.list [encFun a, encFun fun j => (x j : ℕ), .nat s], .nat i])
      (.nat (a (x i) + s))
      (20 * (Val.list [.list [encFun a, encFun fun j => (x j : ℕ), .nat s], .nat i]).wt +
        a (x i) + s + 100) := by
  set ctx : List Val := [encFun a, encFun fun j => (x j : ℕ), .nat s] with hctx
  have d1 := colArg1_det (P := P) (c := .list ctx) (x := .nat i) (rest := [])
  have d2 := colC_det (P := P) (ctx := ctx) (x := .nat i) (rest := []) (j := 1)
    (v := encFun fun j => (x j : ℕ)) rfl
  have d3 := colAt_det d2 d1
  have d4 := colC_det (P := P) (ctx := ctx) (x := .nat i) (rest := []) (j := 0) (v := encFun a) rfl
  have d5 := colAt_det (f := a) (i := x i) d4 d3
  have d6 := colC_det (P := P) (ctx := ctx) (x := .nat i) (rest := []) (j := 2) (v := .nat s) rfl
  have d7 := Det.arith' (op := .add) (z := a (x i) + s) d5 d6 rfl
  refine FunDet.intro hf (d7.mono ?_)
  have w1 := colWt_at_lt (fun j => (x j : ℕ)) i
  have w2 := colWt_at_lt a (x i)
  have w3 : (encFun fun j => (x j : ℕ)).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
  have w4 : (encFun a).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
  have w5 : (Val.list ctx).wt < (Val.list [.list ctx, .nat i]).wt := wt_le_wt_list (by simp)
  clear d1 d2 d3 d4 d5 d6 d7
  omega

/-! ### Equality with entry `0` -/

/-- `[a[i] = a[0]]`. -/
def colEq0E (j : ℕ) : Expr := .arith .eq (.get (colC j) (arg 1)) (.get (colC j) (.nat 0))

/-- On `[[a₁, a₂], i]`: `1` if `a₁[i] = a₁[0]` and `a₂[i] = a₂[0]`, else `0`. -/
def colEqF : Expr := .arith .mul (colEq0E 0) (colEq0E 1)

/-- The value of `colEqF`. -/
def colEqv {k : ℕ} (a₁ a₂ : Fin k → ℕ) (h : 0 < k) (i : Fin k) : ℕ :=
  if a₁ i = a₁ ⟨0, h⟩ ∧ a₂ i = a₂ ⟨0, h⟩ then 1 else 0

theorem colEqv_le {k : ℕ} (a₁ a₂ : Fin k → ℕ) (h : 0 < k) (i : Fin k) : colEqv a₁ a₂ h i ≤ 1 := by
  unfold colEqv; split_ifs <;> omega

theorem colEq_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some colEqF) {k : ℕ}
    (a₁ a₂ : Fin k → ℕ) (h : 0 < k) (i : Fin k) :
    FunDet P f (.list [.list [encFun a₁, encFun a₂], .nat i]) (.nat (colEqv a₁ a₂ h i))
      (40 * (Val.list [.list [encFun a₁, encFun a₂], .nat i]).wt + 200) := by
  set ctx : List Val := [encFun a₁, encFun a₂] with hctx
  set W := (Val.list [.list ctx, .nat i]).wt with hW
  have d1 := colArg1_det (P := P) (c := .list ctx) (x := .nat i) (rest := [])
  have hz : ∀ (j : ℕ) (a : Fin k → ℕ), ctx[j]? = some (encFun a) →
      Det P [.list [.list ctx, .nat i]] (colEq0E j) (.nat (if a i = a ⟨0, h⟩ then 1 else 0))
        (19 * W + 2 * j + 60) := by
    intro j a hj
    have da := colC_det (P := P) (x := .nat i) (rest := []) hj
    have e1 := colAt_det da d1
    have e2 := colAt_det (i := ⟨0, h⟩) da (Det.nat 0)
    have e3 := Det.arith' (op := .eq) (z := if a i = a ⟨0, h⟩ then 1 else 0) e1 e2 rfl
    refine e3.mono ?_
    have w1 := colWt_at_lt a i
    have w2 := colWt_at_lt a ⟨0, h⟩
    have w4 : (encFun a).wt < (Val.list ctx).wt := by
      obtain ⟨hj', he⟩ := List.getElem?_eq_some_iff.mp hj
      rw [← he]; exact wt_getElem_lt _ _ hj'
    have w5 : (Val.list ctx).wt < W := wt_le_wt_list (by simp)
    have : (if a i = a ⟨0, h⟩ then 1 else 0) ≤ 1 := by split_ifs <;> omega
    clear e1 e2 e3 da
    omega
  have d2 := hz 0 a₁ rfl
  have d3 := hz 1 a₂ rfl
  have d4 := Det.arith' (op := .mul) (z := colEqv a₁ a₂ h i) d2 d3 (by
    simp only [BinOp.eval, colEqv]
    split_ifs <;> simp_all)
  refine FunDet.intro hf (d4.mono ?_)
  have := colEqv_le a₁ a₂ h i
  omega

/-! ### The key of a lower part -/

/-- `a[i]` for the context entry `j`. -/
def colAtE (j : ℕ) : Expr := .get (colC j) (arg 1)

/-- On `[[rl, hl, oc, N1], i]`: `(rl[i] N1 + hl[i]) N1 + oc[i] + N1`. -/
def colKeyF : Expr :=
  .arith .add (.arith .add (.arith .mul (.arith .add (.arith .mul (colAtE 0) (colC 3)) (colAtE 1))
    (colC 3)) (colAtE 2)) (colC 3)

/-- The value of `colKeyF`. -/
def colKeyv {k : ℕ} (rl hl oc : Fin k → ℕ) (N1 : ℕ) (i : Fin k) : ℕ :=
  (rl i * N1 + hl i) * N1 + oc i + N1

theorem colKey_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some colKeyF) {k : ℕ}
    (rl hl oc : Fin k → ℕ) {N1 : ℕ} (hN : 1 ≤ N1) (i : Fin k) :
    FunDet P f (.list [.list [encFun rl, encFun hl, encFun oc, .nat N1], .nat i])
      (.nat (colKeyv rl hl oc N1 i))
      (100 * (Val.list [.list [encFun rl, encFun hl, encFun oc, .nat N1], .nat i]).wt +
        5 * colKeyv rl hl oc N1 i + 200) := by
  set ctx : List Val := [encFun rl, encFun hl, encFun oc, .nat N1] with hctx
  set W := (Val.list [.list ctx, .nat i]).wt with hW
  have d1 := colArg1_det (P := P) (c := .list ctx) (x := .nat i) (rest := [])
  have hat : ∀ (j : ℕ) (a : Fin k → ℕ), ctx[j]? = some (encFun a) →
      Det P [.list [.list ctx, .nat i]] (colAtE j) (.nat (a i)) (8 * W + j + 20) := by
    intro j a hj
    have da := colC_det (P := P) (x := .nat i) (rest := []) hj
    refine (colAt_det da d1).mono ?_
    have w1 := colWt_at_lt a i
    have w4 : (encFun a).wt < (Val.list ctx).wt := by
      obtain ⟨hj', he⟩ := List.getElem?_eq_some_iff.mp hj
      rw [← he]; exact wt_getElem_lt _ _ hj'
    have w5 : (Val.list ctx).wt < W := wt_le_wt_list (by simp)
    clear da
    omega
  have dN := colC_det (P := P) (ctx := ctx) (x := .nat i) (rest := []) (j := 3) (v := .nat N1) rfl
  have e1 := Det.arith' (op := .mul) (z := rl i * N1) (hat 0 rl rfl) dN rfl
  have e2 := Det.arith' (op := .add) (z := rl i * N1 + hl i) e1 (hat 1 hl rfl) rfl
  have e3 := Det.arith' (op := .mul) (z := (rl i * N1 + hl i) * N1) e2 dN rfl
  have e4 := Det.arith' (op := .add) (z := (rl i * N1 + hl i) * N1 + oc i) e3 (hat 2 oc rfl) rfl
  have e5 := Det.arith' (op := .add) (z := colKeyv rl hl oc N1 i) e4 dN rfl
  refine FunDet.intro hf (e5.mono ?_)
  unfold colKeyv
  have h1 : rl i ≤ rl i * N1 := Nat.le_mul_of_pos_right _ hN
  have h2 : rl i * N1 + hl i ≤ (rl i * N1 + hl i) * N1 := Nat.le_mul_of_pos_right _ hN
  clear e1 e2 e3 e4 e5 dN hat d1
  omega

/-! ### The column coordinate of a position -/

/-- On `[[dv, rl, rows], i]`: for a position of the domain (`dv[i] ≠ 0`), the index of `i` in
row `rl[i]` (`findEq` at `fe`), and `0` off the domain. -/
def colInvF (fe : ℕ) : Expr :=
  .ite (colAtE 0) (.call fe (mk2 (arg 1) (.get (colC 2) (colAtE 1)))) (.nat 0)

/-- The value of `colInvF`. -/
def colInvv {k : ℕ} (R : List (List ℕ)) (dv rl : Fin k → ℕ) (i : Fin k) : ℕ :=
  if dv i = 0 then 0 else (R.getD (rl i) []).findIdx fun x => decide (x = (i : ℕ))

theorem colInv_det {P : Program} {f fe : ℕ} (hf : P.funs[f]? = some (colInvF fe))
    (hfe : P.HasAt fe (findEqFuns fe)) {k : ℕ} (R : List (List ℕ)) (dv rl : Fin k → ℕ)
    {B : ℕ} (hR : ∀ r ∈ R, (∀ x ∈ r, x ≤ B) ∧ r.length ≤ B) (hkB : k ≤ B)
    (hrl : ∀ i, dv i ≠ 0 → rl i < R.length) (i : Fin k) :
    FunDet P f (.list [.list [encFun dv, encFun rl, .list (R.map natList)], .nat i])
      (.nat (colInvv R dv rl i))
      (60 * (Val.list [.list [encFun dv, encFun rl, .list (R.map natList)], .nat i]).wt +
        3 * (findEqK * (B + 1) ^ 3) + 300) := by
  set ctx : List Val := [encFun dv, encFun rl, .list (R.map natList)] with hctx
  set W := (Val.list [.list ctx, .nat i]).wt with hW
  have d1 := colArg1_det (P := P) (c := .list ctx) (x := .nat i) (rest := [])
  have w5 : (Val.list ctx).wt < W := wt_le_wt_list (by simp)
  have hat : ∀ (j : ℕ) (a : Fin k → ℕ), ctx[j]? = some (encFun a) →
      Det P [.list [.list ctx, .nat i]] (colAtE j) (.nat (a i)) (8 * W + j + 20) := by
    intro j a hj
    have da := colC_det (P := P) (x := .nat i) (rest := []) hj
    refine (colAt_det da d1).mono ?_
    have w1 := colWt_at_lt a i
    have w4 : (encFun a).wt < (Val.list ctx).wt := by
      obtain ⟨hj', he⟩ := List.getElem?_eq_some_iff.mp hj
      rw [← he]; exact wt_getElem_lt _ _ hj'
    clear da
    omega
  have d0 := hat 0 dv rfl
  by_cases hdv : dv i = 0
  · have d := Det.ite_zero (t := .call fe (mk2 (arg 1) (.get (colC 2) (colAtE 1))))
      (hdv ▸ d0) (Det.nat (P := P) (env := [.list [.list ctx, .nat i]]) 0)
    have hv : colInvv R dv rl i = 0 := by simp [colInvv, hdv]
    rw [hv]
    refine FunDet.intro hf (d.mono ?_)
    have := wt_nat_le 0
    have w1 := colWt_at_lt dv i
    clear d d0 hat d1
    omega
  · have hr := hrl i hdv
    have dR := colC_det (P := P) (ctx := ctx) (x := .nat i) (rest := []) (j := 2)
      (v := .list (R.map natList)) rfl
    have dr := Det.get' dR (hat 1 rl rfl) (v := natList (R.getD (rl i) []))
      (by rw [List.getElem?_map, List.getD_eq_getElem _ _ hr, List.getElem?_eq_getElem hr]; rfl)
    have hRi := hR _ (List.getElem_mem hr)
    rw [← List.getD_eq_getElem _ [] hr] at hRi
    have dc := Det.call (Det.mk2 d1 dr) (findEq_spec hfe (j := i) hRi.1 (by omega) hRi.2)
    have d := Det.ite_pos (e := .nat 0) d0 hdv dc
    have hv : colInvv R dv rl i = (R.getD (rl i) []).findIdx fun x => decide (x = (i : ℕ)) := by
      simp [colInvv, hdv]
    rw [hv]
    refine FunDet.intro hf (d.mono ?_)
    have wr : (natList (R.getD (rl i) [])).wt < W := by
      have : (natList (R.getD (rl i) [])).wt < (Val.list (R.map natList)).wt := by
        rw [List.getD_eq_getElem _ _ hr]
        exact wt_le_wt_list (List.mem_map.2 ⟨_, List.getElem_mem hr, rfl⟩)
      have : (Val.list (R.map natList)).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
      omega
    have w2 := wt_list2_le (.nat i) (natList (R.getD (rl i) []))
    have wi : (Val.nat (i : ℕ)).wt < W := wt_le_wt_list (by simp)
    have wf : (Val.nat ((R.getD (rl i) []).findIdx fun x => decide (x = (i : ℕ)))).wt <
        findEqK * (B + 1) ^ 3 + 1 := by
      have := (findEq_spec hfe (j := i) hRi.1 (by omega) hRi.2).wt_lt
      omega
    clear d dc dr dR d0 hat d1
    omega

/-! ### The least label over an orbit -/

/-- The running minimum: start at `bk[c]`, and lower it to `bk[o]` for each `o < i` with
`orb[o] = orb[c]`. -/
def colMinAcc {m : ℕ} (bk orb : Fin m → ℕ) (c : Fin m) : ℕ → ℕ
  | 0 => bk c
  | i + 1 => if h : i < m then
      (if orb ⟨i, h⟩ = orb c ∧ bk ⟨i, h⟩ < colMinAcc bk orb c i then bk ⟨i, h⟩
        else colMinAcc bk orb c i)
    else colMinAcc bk orb c i

theorem colMinAcc_le {m : ℕ} (bk orb : Fin m → ℕ) (c : Fin m) :
    ∀ i, colMinAcc bk orb c i ≤ bk c
  | 0 => le_rfl
  | i + 1 => by
    have := colMinAcc_le bk orb c i
    simp only [colMinAcc]
    split_ifs <;> omega

/-- The running minimum is the least `bk[o]` over the `o < i` with `orb[o] = orb[c]` and `c`. -/
theorem colMinAcc_spec {m : ℕ} (bk orb : Fin m → ℕ) (c : Fin m) :
    ∀ i, (∀ o : Fin m, (o : ℕ) < i → orb o = orb c → colMinAcc bk orb c i ≤ bk o) ∧
      ∃ o, orb o = orb c ∧ bk o = colMinAcc bk orb c i
  | 0 => ⟨fun o ho => absurd ho (Nat.not_lt_zero _), c, rfl, rfl⟩
  | i + 1 => by
    obtain ⟨h1, o₀, ho₀, he₀⟩ := colMinAcc_spec bk orb c i
    by_cases him : i < m
    · simp only [colMinAcc, dif_pos him]
      split_ifs with hc
      · refine ⟨fun o ho horb => ?_, ⟨i, him⟩, hc.1, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ho with ho | ho
        · exact (hc.2.trans_le (h1 o ho horb)).le
        · rw [show o = ⟨i, him⟩ from Fin.ext ho]
      · refine ⟨fun o ho horb => ?_, o₀, ho₀, he₀⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ho with ho | ho
        · exact h1 o ho horb
        · have ho' : o = ⟨i, him⟩ := Fin.ext ho
          subst ho'
          simp only [not_and, not_lt] at hc
          exact hc horb
    · simp only [colMinAcc, dif_neg him]
      exact ⟨fun o ho horb => h1 o (by have := o.2; omega) horb, o₀, ho₀, he₀⟩

/-- The least `bk[o]` over the `o` with `orb[o] = orb[c]`. -/
def colMinv {m : ℕ} (bk orb : Fin m → ℕ) (c : Fin m) : ℕ := colMinAcc bk orb c m

theorem colMinv_le {m : ℕ} (bk orb : Fin m → ℕ) (c o : Fin m) (h : orb o = orb c) :
    colMinv bk orb c ≤ bk o :=
  (colMinAcc_spec bk orb c m).1 o o.2 h

theorem colMinv_exists {m : ℕ} (bk orb : Fin m → ℕ) (c : Fin m) :
    ∃ o, orb o = orb c ∧ bk o = colMinv bk orb c :=
  (colMinAcc_spec bk orb c m).2

/-- The step of the running minimum, on `[[bk, orb, c], o, acc]`. -/
def colMinStepF : Expr :=
  .ite (.arith .mul (.arith .eq (.get (colC 1) (arg 1)) (.get (colC 1) (colC 2)))
      (.arith .lt (.get (colC 0) (arg 1)) (arg 2)))
    (.get (colC 0) (arg 1)) (arg 2)

theorem colMinStep_det {P : Program} {g : ℕ} (hg : P.funs[g]? = some colMinStepF) {m : ℕ}
    (bk orb : Fin m → ℕ) (c : Fin m) (i : ℕ) (hi : i < m) :
    FunDet P g (.list [.list [encFun bk, encFun orb, .nat c], .nat i,
        .nat (colMinAcc bk orb c i)]) (.nat (colMinAcc bk orb c (i + 1)))
      (60 * (Val.list [.list [encFun bk, encFun orb, .nat c], .nat i,
        .nat (colMinAcc bk orb c i)]).wt + 200) := by
  set ctx : List Val := [encFun bk, encFun orb, .nat c] with hctx
  set more : List Val := [.nat i, .nat (colMinAcc bk orb c i)] with hmore
  set W := (Val.list (.list ctx :: more)).wt with hW
  have w5 : (Val.list ctx).wt < W := wt_le_wt_list (by simp)
  have wa : ∀ (a : Fin m → ℕ), (encFun a).wt < (Val.list ctx).wt → ∀ j : Fin m,
      (Val.nat (a j)).wt < W := fun a ha j => by have := colWt_at_lt a j; omega
  have wbk : (encFun bk).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
  have worb : (encFun orb).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
  have d1 : Det P [.list (.list ctx :: more)] (arg 1) (.nat (⟨i, hi⟩ : Fin m)) (2 * W + 6) :=
    Det.arg' (vs := .list ctx :: more) (j := 1) rfl
  have d2 : Det P [.list (.list ctx :: more)] (arg 2) (.nat (colMinAcc bk orb c i)) (2 * W + 7) :=
    Det.arg' (vs := .list ctx :: more) (j := 2) rfl
  have dB := colC_det' (P := P) (ctx := ctx) (more := more) (rest := []) (j := 0) (v := encFun bk) rfl
  have dO := colC_det' (P := P) (ctx := ctx) (more := more) (rest := []) (j := 1) (v := encFun orb) rfl
  have dc := colC_det' (P := P) (ctx := ctx) (more := more) (rest := []) (j := 2)
    (v := .nat (c : ℕ)) rfl
  have eO1 := colAt_det dO d1
  have eO2 := colAt_det (i := c) dO dc
  have eB := colAt_det dB d1
  have t1 := Det.arith' (op := .eq) (z := if orb ⟨i, hi⟩ = orb c then 1 else 0) eO1 eO2 rfl
  have t2 := Det.arith' (op := .lt) (z := if bk ⟨i, hi⟩ < colMinAcc bk orb c i then 1 else 0)
    eB d2 rfl
  have t3 := Det.arith' (op := .mul)
    (z := if orb ⟨i, hi⟩ = orb c ∧ bk ⟨i, hi⟩ < colMinAcc bk orb c i then 1 else 0) t1 t2 (by
      simp only [BinOp.eval]; split_ifs <;> simp_all)
  have d := Det.ite' t3 eB d2
  have hv : (if (if orb ⟨i, hi⟩ = orb c ∧ bk ⟨i, hi⟩ < colMinAcc bk orb c i then 1 else 0) = 0
      then Val.nat (colMinAcc bk orb c i) else Val.nat (bk ⟨i, hi⟩)) =
      .nat (colMinAcc bk orb c (i + 1)) := by
    simp only [colMinAcc, dif_pos hi]
    split_ifs <;> simp_all
  rw [hv] at d
  refine FunDet.intro hg (d.mono ?_)
  have := wa bk wbk ⟨i, hi⟩
  have := wa orb worb ⟨i, hi⟩
  have := wa orb worb c
  have h2 : (Val.nat (colMinAcc bk orb c i)).wt < W := wt_le_wt_list (by simp [hmore])
  have h3 : (Val.nat (colMinAcc bk orb c (i + 1))).wt ≤ W := by
    simp only [colMinAcc, dif_pos hi]
    split_ifs
    · exact (wa bk wbk ⟨i, hi⟩).le
    · exact h2.le
  have hmax1 : max (Val.nat (bk ⟨i, hi⟩)).wt (Val.nat (colMinAcc bk orb c i)).wt ≤ W :=
    max_le (by omega) (by omega)
  have b1 : (if orb ⟨i, hi⟩ = orb c then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have b2 : (if bk ⟨i, hi⟩ < colMinAcc bk orb c i then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have b3 : (if orb ⟨i, hi⟩ = orb c ∧ bk ⟨i, hi⟩ < colMinAcc bk orb c i then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  clear d t3 t2 t1 eB eO2 eO1 dc dO dB d1 d2 hv
  have hm : max (2 * W + 7) (4 * W + 0 + 10 + (2 * W + 6) + (Val.nat (bk ⟨i, hi⟩)).wt + 1) ≤
      7 * W + 17 := max_le (by omega) (by omega)
  omega

/-- On `[[bk, orb], c]`: the least `bk[o]` over the `o` with `orb[o] = orb[c]` (`iterate` at
`it` with the step `colMinStepF`). -/
def colMinF (it : ℕ) : Expr :=
  .call it (mk3 (mk3 (colC 0) (colC 1) (arg 1)) (.length (colC 0)) (.get (colC 0) (arg 1)))

/-- The cost constant of `colMinF`. -/
def colMinK : ℕ := 10 ^ 6

theorem colMin_det {P : Program} {f it g : ℕ} (hf : P.funs[f]? = some (colMinF it))
    (hit : P.HasAt it (iterFuns it g)) (hg : P.funs[g]? = some colMinStepF) {m : ℕ}
    (bk orb : Fin m → ℕ) (c : Fin m) :
    FunDet P f (.list [.list [encFun bk, encFun orb], .nat c]) (.nat (colMinv bk orb c))
      (colMinK * (m + 1) * ((Val.list [.list [encFun bk, encFun orb], .nat c]).wt + m + 1)) := by
  set ctx : List Val := [encFun bk, encFun orb] with hctx
  set W := (Val.list [.list ctx, .nat c]).wt with hW
  have w5 : (Val.list ctx).wt < W := wt_le_wt_list (by simp)
  have wbk : (encFun bk).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
  have worb : (encFun orb).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
  have wc : (Val.nat (c : ℕ)).wt < W := wt_le_wt_list (by simp)
  have d1 := colArg1_det (P := P) (c := .list ctx) (x := .nat c) (rest := [])
  have dB := colC_det (P := P) (ctx := ctx) (x := .nat c) (rest := []) (j := 0) (v := encFun bk) rfl
  have dO := colC_det (P := P) (ctx := ctx) (x := .nat c) (rest := []) (j := 1) (v := encFun orb) rfl
  have dL := Det.length (vs := (List.finRange m).map fun i => Val.nat (bk i)) dB
  rw [show ((List.finRange m).map fun i => Val.nat (bk i)).length = m by simp] at dL
  have dA := colAt_det (i := c) dB d1
  have dI := Det.mk3 (Det.mk3 dB dO d1) dL dA
  have hwc' : (Val.list [encFun bk, encFun orb, .nat c]).wt ≤ 7 * W + 20 := by
    have := wt_list3_le (encFun bk) (encFun orb) (.nat c)
    omega
  have hacc : ∀ i, (Val.nat (colMinAcc bk orb c i)).wt ≤ W := by
    intro i
    have h1 := colWt_nat_mono (colMinAcc_le bk orb c i)
    have h2 := colWt_at_lt bk c
    omega
  have hit' := iter_spec (P := P) (c := .list [encFun bk, encFun orb, .nat c]) (k := m) (acc0 := .nat (bk c)) hit
    (Inv := fun i acc => acc = .nat (colMinAcc bk orb c i)) (M := W)
    (B := fun _ => 60 * (2 * (7 * W + 20 + m + W) + 11) + 200)
    rfl (fun i acc _ h => by rw [h]; exact hacc i) (fun i acc hi h => by
      subst h
      refine FunAll.mono (colMinStep_det hg bk orb c i hi) fun w cost hw => ⟨hw.1, ?_⟩
      have := wt_list3_le (.list [encFun bk, encFun orb, .nat c]) (.nat i)
        (.nat (colMinAcc bk orb c i))
      have := wt_nat_le i
      have := hacc i
      have := hw.2
      show cost ≤ 60 * (2 * (7 * W + 20 + m + W) + 11) + 200
      omega)
  have dC := Det.call dI (w := .nat (colMinv bk orb c)) (FunAll.mono hit' fun w cost hw => ⟨hw.1, hw.2⟩)
  refine FunDet.intro hf (dC.mono ?_)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have := wt_nat_le m
  have := hacc 0
  have hv : (Val.nat (colMinv bk orb c)).wt ≤ W := hacc m
  have hw3 : (Val.list [Val.list [encFun bk, encFun orb, Val.nat ↑c], Val.nat m,
      Val.nat (bk c)]).wt ≤ 2 * (7 * W + 20 + m + 2 + W) + 10 := by
    have := wt_list3_le (.list [encFun bk, encFun orb, .nat c]) (.nat m) (.nat (bk c))
    have : (Val.nat (bk c)).wt ≤ W := hacc 0
    omega
  clear dC dI hit' dA dL dO dB d1
  generalize hA : (Val.list [Val.list [encFun bk, encFun orb, Val.nat ↑c], Val.nat m,
    Val.nat (bk c)]).wt = A at hw3 ⊢
  have e1 : m * (60 * (2 * (7 * W + 20 + m + W) + 11) + 200) ≤ (m + 1) * (W + m + 1) * 2000 := by
    have : m * (60 * (2 * (7 * W + 20 + m + W) + 11) + 200) ≤ (m + 1) * (2000 * (W + m + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    linarith
  have e2 : loopModK * (m + 1) * (A + m + W + 1) ≤ (m + 1) * (W + m + 1) * 80000 := by
    have : (m + 1) * (1000 * (A + m + W + 1)) ≤ (m + 1) * (80000 * (W + m + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [loopModK]
    linarith
  have e3 : W + m + 1 ≤ (m + 1) * (W + m + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have e4 : colMinK * (m + 1) * (W + m + 1) = (m + 1) * (W + m + 1) * 1000000 := by
    simp only [colMinK]; ring
  rw [e4]
  obtain ⟨Z, hZ⟩ : ∃ Z, (m + 1) * (W + m + 1) = Z := ⟨_, rfl⟩
  rw [hZ] at e1 e2 e3 ⊢
  have : (Val.list [Val.list ctx, Val.nat ↑c]).wt = W := rfl
  have : (Val.nat (bk c)).wt ≤ W := hacc 0
  omega

/-! ### The test that a level refines the rows -/

/-- The test of one position `i`: it is not a domain point in the class of `p00` with a nonzero
row label. -/
def colLowQ {n : ℕ} (pv dv rl : Fin n → ℕ) (p00 : Fin n) : Val → Bool
  | .nat i => if h : i < n then !(decide (dv ⟨i, h⟩ ≠ 0 ∧ pv ⟨i, h⟩ = pv p00 ∧ rl ⟨i, h⟩ ≠ 0))
      else true
  | .list _ => true

theorem colLowQ_all {n : ℕ} (pv dv rl : Fin n → ℕ) (p00 : Fin n) :
    ((List.range n).map Val.nat).all (colLowQ pv dv rl p00) = true ↔
      ∀ i : Fin n, ¬ (dv i ≠ 0 ∧ pv i = pv p00 ∧ rl i ≠ 0) := by
  simp only [List.all_eq_true, List.mem_map, List.mem_range, forall_exists_index, and_imp]
  constructor
  · intro h i
    have := h _ i i.2 rfl
    simp only [colLowQ, dif_pos i.2, Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact this
  · rintro h _ i hi rfl
    simp only [colLowQ, dif_pos hi, Bool.not_eq_true', decide_eq_false_iff_not]
    exact h ⟨i, hi⟩

/-- On `[[pv, dv, rl, p00], i]`: `colLowQ` as `1 - dv[i] [pv[i] = pv[p00]] (1 - [rl[i] = 0])`. -/
def colLowPosF : Expr :=
  .arith .sub (.nat 1) (.arith .mul (.arith .mul (colAtE 1)
    (.arith .eq (colAtE 0) (.get (colC 0) (colC 3))))
    (.arith .sub (.nat 1) (.arith .eq (colAtE 2) (.nat 0))))

theorem colLowPos_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some colLowPosF) {n : ℕ}
    (pv dv rl : Fin n → ℕ) (hdv : ∀ i, dv i ≤ 1) (p00 : Fin n) (i : Fin n) :
    FunDet P f (.list [.list [encFun pv, encFun dv, encFun rl, .nat p00], .nat i])
      (boolVal (colLowQ pv dv rl p00 (.nat i)))
      (100 * (Val.list [.list [encFun pv, encFun dv, encFun rl, .nat p00], .nat i]).wt + 200) := by
  set ctx : List Val := [encFun pv, encFun dv, encFun rl, .nat p00] with hctx
  set W := (Val.list [.list ctx, .nat i]).wt with hW
  have d1 := colArg1_det (P := P) (c := .list ctx) (x := .nat i) (rest := [])
  have w5 : (Val.list ctx).wt < W := wt_le_wt_list (by simp)
  have hat : ∀ (j : ℕ) (a : Fin n → ℕ), ctx[j]? = some (encFun a) →
      Det P [.list [.list ctx, .nat i]] (colAtE j) (.nat (a i)) (8 * W + j + 20) := by
    intro j a hj
    have da := colC_det (P := P) (x := .nat i) (rest := []) hj
    refine (colAt_det da d1).mono ?_
    have w1 := colWt_at_lt a i
    have w4 : (encFun a).wt < (Val.list ctx).wt := by
      obtain ⟨hj', he⟩ := List.getElem?_eq_some_iff.mp hj
      rw [← he]; exact wt_getElem_lt _ _ hj'
    clear da
    omega
  have dP := colC_det (P := P) (ctx := ctx) (x := .nat i) (rest := []) (j := 0) (v := encFun pv) rfl
  have dp := colC_det (P := P) (ctx := ctx) (x := .nat i) (rest := []) (j := 3)
    (v := .nat (p00 : ℕ)) rfl
  have e0 := colAt_det (i := p00) dP dp
  have t1 := Det.arith' (op := .eq) (z := if pv i = pv p00 then 1 else 0) (hat 0 pv rfl) e0 rfl
  have t2 := Det.arith' (op := .mul) (z := dv i * (if pv i = pv p00 then 1 else 0))
    (hat 1 dv rfl) t1 rfl
  have t3 := Det.arith' (op := .eq) (z := if rl i = 0 then 1 else 0) (hat 2 rl rfl)
    (Det.nat 0) rfl
  have t4 := Det.arith' (op := .sub) (z := 1 - (if rl i = 0 then 1 else 0)) (Det.nat 1) t3 rfl
  have t5 := Det.arith' (op := .mul)
    (z := dv i * (if pv i = pv p00 then 1 else 0) * (1 - (if rl i = 0 then 1 else 0))) t2 t4 rfl
  have t6 := Det.arith' (op := .sub) (z := (colLowQ pv dv rl p00 (.nat i)).toNat) (Det.nat 1) t5 (by
    have := hdv i
    simp only [BinOp.eval, colLowQ, dif_pos i.2, Fin.eta]
    by_cases h1 : dv i = 0
    · simp [h1]
    · have h1' : dv i = 1 := by omega
      by_cases h2 : pv i = pv p00 <;> by_cases h3 : rl i = 0 <;> simp [h1', h2, h3])
  refine FunDet.intro hf (t6.mono ?_)
  have := hdv i
  have w0 := colWt_at_lt pv p00
  have wpv : (encFun pv).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
  have b1 : (if pv i = pv p00 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have b2 : (if rl i = 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have b3 : dv i * (if pv i = pv p00 then 1 else 0) ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 b1 with h | h <;> rw [h] <;> omega
  have b4 : dv i * (if pv i = pv p00 then 1 else 0) * (1 - (if rl i = 0 then 1 else 0)) ≤ 1 := by
    have : 1 - (if rl i = 0 then 1 else 0) ≤ 1 := by omega
    calc _ ≤ 1 * 1 := Nat.mul_le_mul b3 this
      _ = 1 := rfl
  have b5 := Bool.toNat_le (colLowQ pv dv rl p00 (.nat i))
  clear t6 t5 t4 t3 t2 t1 e0 dp dP hat d1
  omega

/-- On `[[hv, dv, rl, p00, range n], k]`: `1` if level `k` of the hierarchy value `hv` does not
pass the test of `colLowPosF` at some position (`all` at `al`), else `0`. -/
def colNotLowF (al : ℕ) : Expr :=
  .arith .sub (.nat 1) (.call al (mk2 (mk4 (.get (.get (colC 0) (arg 1)) (.nat 0)) (colC 1)
    (colC 2) (colC 3)) (colC 4)))

/-- A hierarchy value with explicit labels, ratios, bounds and origins. -/
def colHV {len n : ℕ} (labs : Fin len → Fin n → ℕ) (rats caps origs : Fin len → ℕ) : Val :=
  .list ((List.finRange len).map fun k =>
    .list [encFun (labs k), .nat (rats k), .nat (caps k), .nat (origs k)])

/-- The value of `colNotLowF`: `1` when some domain position of the class of `p00` in level `k`
has a nonzero row label. -/
def colNotLowv {len n : ℕ} (labs : Fin len → Fin n → ℕ) (dv rl : Fin n → ℕ) (p00 : Fin n)
    (k : Fin len) : ℕ :=
  if ((List.range n).map Val.nat).all (colLowQ (labs k) dv rl p00) then 0 else 1

/-- The cost constant of `colNotLowF`. -/
def colNotLowK : ℕ := 10 ^ 6

theorem colHV_get {len n : ℕ} (labs : Fin len → Fin n → ℕ) (rats caps origs : Fin len → ℕ)
    (k : Fin len) :
    ((List.finRange len).map fun k =>
      Val.list [encFun (labs k), .nat (rats k), .nat (caps k), .nat (origs k)])[(k : ℕ)]? =
      some (.list [encFun (labs k), .nat (rats k), .nat (caps k), .nat (origs k)]) := by
  simp

theorem colNotLow_det {P : Program} {f al lp : ℕ} (hf : P.funs[f]? = some (colNotLowF al))
    (hal : P.HasAt al (allFuns al lp)) (hlp : P.funs[lp]? = some colLowPosF) {len n : ℕ}
    (labs : Fin len → Fin n → ℕ) (rats caps origs : Fin len → ℕ) (dv rl : Fin n → ℕ)
    (hdv : ∀ i, dv i ≤ 1) (p00 : Fin n) (k : Fin len) :
    FunDet P f (.list [.list [colHV labs rats caps origs, encFun dv, encFun rl, .nat p00,
        natList (List.range n)], .nat k]) (.nat (colNotLowv labs dv rl p00 k))
      (colNotLowK * (n + 1) * ((Val.list [.list [colHV labs rats caps origs, encFun dv, encFun rl,
        .nat p00, natList (List.range n)], .nat k]).wt + n + 1)) := by
  set ctx : List Val := [colHV labs rats caps origs, encFun dv, encFun rl, .nat p00,
    natList (List.range n)] with hctx
  set W := (Val.list [.list ctx, .nat k]).wt with hW
  have w5 : (Val.list ctx).wt < W := wt_le_wt_list (by simp)
  have d1 := colArg1_det (P := P) (c := .list ctx) (x := .nat k) (rest := [])
  have dH := colC_det (P := P) (ctx := ctx) (x := .nat k) (rest := []) (j := 0)
    (v := colHV labs rats caps origs) rfl
  have dHk := Det.get' dH d1 (colHV_get labs rats caps origs k)
  have dL := Det.get' dHk (Det.nat 0) (v := encFun (labs k)) rfl
  have dD := colC_det (P := P) (ctx := ctx) (x := .nat k) (rest := []) (j := 1) (v := encFun dv) rfl
  have dR := colC_det (P := P) (ctx := ctx) (x := .nat k) (rest := []) (j := 2) (v := encFun rl) rfl
  have dp := colC_det (P := P) (ctx := ctx) (x := .nat k) (rest := []) (j := 3)
    (v := .nat (p00 : ℕ)) rfl
  have dN := colC_det (P := P) (ctx := ctx) (x := .nat k) (rest := []) (j := 4)
    (v := natList (List.range n)) rfl
  have dA := Det.mk2 (Det.mk4 dL dD dR dp) dN
  set c' : Val := .list [encFun (labs k), encFun dv, encFun rl, .nat p00] with hc'
  -- weights
  have wH : (colHV labs rats caps origs).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
  have wHk : (Val.list [encFun (labs k), .nat (rats k), .nat (caps k), .nat (origs k)]).wt <
      (colHV labs rats caps origs).wt := by
    unfold colHV; exact wt_le_wt_list (List.mem_map.2 ⟨k, List.mem_finRange k, rfl⟩)
  have wLk : (encFun (labs k)).wt <
      (Val.list [encFun (labs k), .nat (rats k), .nat (caps k), .nat (origs k)]).wt :=
    wt_le_wt_list (by simp)
  have wD : (encFun dv).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
  have wR : (encFun rl).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
  have wp : (Val.nat (p00 : ℕ)).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
  have wN : (natList (List.range n)).wt < (Val.list ctx).wt := wt_le_wt_list (by simp [hctx])
  have wc' : c'.wt ≤ 8 * W + 8 := by
    have := wt_list4_le (encFun (labs k)) (encFun dv) (encFun rl) (.nat (p00 : ℕ))
    have : c'.wt = (Val.list [encFun (labs k), encFun dv, encFun rl, .nat (p00 : ℕ)]).wt := rfl
    omega
  have hall := all_spec (P := P) (c := c') (xs := (List.range n).map Val.nat) hal
    (q := colLowQ (labs k) dv rl p00) (B := fun _ => 100 * (2 * (8 * W + 8 + n + 2) + 6) + 200)
    (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      have hi' := List.mem_range.1 hi
      refine (colLowPos_det hlp (labs k) dv rl hdv p00 ⟨i, hi'⟩).mono ?_
      have := wt_list2_le c' (.nat i)
      have := wt_nat_le i
      have : c'.wt = (Val.list [encFun (labs k), encFun dv, encFun rl, .nat (p00 : ℕ)]).wt := rfl
      have : (Val.list [Val.list [encFun (labs k), encFun dv, encFun rl, .nat (p00 : ℕ)],
        .nat ((⟨i, hi'⟩ : Fin n) : ℕ)]).wt = (Val.list [c', .nat i]).wt := rfl
      show _ ≤ 100 * (2 * (8 * W + 8 + n + 2) + 6) + 200
      omega)
  have dC := Det.call dA (w := boolVal (((List.range n).map Val.nat).all (colLowQ (labs k) dv rl p00)))
    (FunAll.mono hall fun w cost hw => ⟨hw.1, hw.2⟩)
  have dS := Det.arith' (op := .sub) (z := colNotLowv labs dv rl p00 k) (Det.nat 1) dC (by
    simp only [BinOp.eval, colNotLowv]
    cases ((List.range n).map Val.nat).all (colLowQ (labs k) dv rl p00) <;> rfl)
  refine FunDet.intro hf (dS.mono ?_)
  have hsum : (((List.range n).map Val.nat).map
      fun _ => 100 * (2 * (8 * W + 8 + n + 2) + 6) + 200).sum =
      n * (100 * (2 * (8 * W + 8 + n + 2) + 6) + 200) := by
    simp only [List.map_map, Function.comp_def, List.map_const', List.sum_replicate,
      List.length_range, smul_eq_mul]
  rw [hsum]
  have wxs : (Val.list [c', natList (List.range n)]).wt ≤ 2 * (8 * W + 8 + W) + 6 := by
    have := wt_list2_le c' (natList (List.range n))
    have : (natList (List.range n)).wt = (Val.list ((List.range n).map Val.nat)).wt := rfl
    omega
  have hv1 : colNotLowv labs dv rl p00 k ≤ 1 := by unfold colNotLowv; split_ifs <;> omega
  have hb := wt_boolVal_le (((List.range n).map Val.nat).all (colLowQ (labs k) dv rl p00))
  have hlen : ((List.range n).map Val.nat).length = n := by simp
  rw [hlen]
  have e1 : n * (100 * (2 * (8 * W + 8 + n + 2) + 6) + 200) ≤ (n + 1) * (W + n + 1) * 2000 := by
    have : n * (100 * (2 * (8 * W + 8 + n + 2) + 6) + 200) ≤ (n + 1) * (2000 * (W + n + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    linarith
  have e2 : loopModK * (n + 1) *
      ((Val.list [c', Val.list ((List.range n).map Val.nat)]).wt + n + 4) ≤
      (n + 1) * (W + n + 1) * 30000 := by
    have : (Val.list [c', Val.list ((List.range n).map Val.nat)]).wt =
      (Val.list [c', natList (List.range n)]).wt := rfl
    have : (n + 1) * (1000 * ((Val.list [c', Val.list ((List.range n).map Val.nat)]).wt + n + 4)) ≤
        (n + 1) * (30000 * (W + n + 1)) := Nat.mul_le_mul_left _ (by omega)
    simp only [loopModK]
    linarith
  have e3 : W + n + 1 ≤ (n + 1) * (W + n + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have e4 : colNotLowK * (n + 1) * (W + n + 1) = (n + 1) * (W + n + 1) * 1000000 := by
    simp only [colNotLowK]; ring
  rw [e4]
  obtain ⟨Z, hZ⟩ : ∃ Z, (n + 1) * (W + n + 1) = Z := ⟨_, rfl⟩
  rw [hZ] at e1 e2 e3 ⊢
  have : (Val.list [Val.list ctx, Val.nat ↑k]).wt = W := rfl
  have : (Val.list [encFun (labs k), encFun dv, encFun rl, .nat (p00 : ℕ)]).wt = c'.wt := rfl
  clear dS dC hall dA dN dp dR dD dL dHk dH d1
  omega

end GI.Impl
