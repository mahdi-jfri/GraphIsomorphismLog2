module

public import Workspace.Impl.Size

@[expose] public section

/-!
# The choice of case of `Continue`: the phase threshold

The selector of `Continue` first compares `s = |dom|` with `N^γ`, `γ = 9/10` (Algorithm 5:
"if `|Ω| ≤ N^γ` then return `Solve`"). For natural numbers, `s ≤ N^{9/10}` holds exactly when
`s^10 ≤ N^9` (`le_rpow_iff`), so the test is exact arithmetic. At or below the threshold it
answers case `0`. Above the threshold it calls a function `rest` that chooses among the other
cases (orbit chain, floor reset, general dispatcher); this needs the orbits of the group and the
column floor, and its specification is `RestSelSpec`.

* `contSel_spec`: the selector meets `SelSpec .cont contCases` if `rest` meets `RestSelSpec`
  and `selW .cont S` covers the cost (`contSelCost` plus the bound of `rest`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val)
open scoped Pointwise

/-! ### The threshold as arithmetic -/

theorem P₀_γ_eq : P₀.γ = 9 / 10 := by norm_num [P₀]

/-- `s ≤ N^{9/10}` exactly when `s^10 ≤ N^9`. -/
theorem le_rpow_iff (s N : ℕ) : (s : ℝ) ≤ (N : ℝ) ^ P₀.γ ↔ s ^ 10 ≤ N ^ 9 := by
  rw [P₀_γ_eq]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : ((N : ℝ) ^ (9 / 10 : ℝ)) ^ (10 : ℕ) = (N : ℝ) ^ (9 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
    norm_num
  have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (9 / 10 : ℝ) := Real.rpow_nonneg hN _
  rw [← pow_le_pow_iff_left₀ (Nat.cast_nonneg s) h2 (by norm_num : (10 : ℕ) ≠ 0), h1]
  exact_mod_cast Iff.rfl

/-! ### Powers -/

/-- `e^n`, by `n` multiplications. -/
def powE (e : Expr) : ℕ → Expr
  | 0 => .nat 1
  | n + 1 => .arith .mul (powE e n) e

theorem Det.powE {P : Program} {env : List Val} {e : Expr} {x ce : ℕ}
    (he : Det P env e (.nat x) ce) :
    ∀ n, Det P env (powE e n) (.nat (x ^ n)) (n * (ce + (x + 1) ^ n + 4) + 4)
  | 0 => (Det.nat 1).mono (by simp)
  | n + 1 => by
    refine (Det.arith' (op := .mul) (Det.powE he n) he (z := x ^ (n + 1))
      (by simp [BinOp.eval, pow_succ])).mono ?_
    have h1 : (x + 1) ^ n ≤ (x + 1) ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : x ^ (n + 1) ≤ (x + 1) ^ (n + 1) := Nat.pow_le_pow_left (by omega) _
    have h3 : n * (ce + (x + 1) ^ n + 4) ≤ n * (ce + (x + 1) ^ (n + 1) + 4) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith

/-! ### The selector -/

/-- The cost of the selector of `Continue` besides the call of `rest`, in terms of a bound `W`
on the weight of the input and the phase size `N`. -/
def contSelCost (W N : ℕ) : ℕ :=
  4 * W + sizeK * (W + 1) ^ 2 + 9 * (W + N + 20 + (N + 1) ^ 9) + 10 * (W + 4 + (W + 1) ^ 10) + 200

/-- The body of the selector of `Continue`, at base `b`, with the size module at `b + 1` and the
rest of the selector at `rest`: in the environment `[v, s]`, answer `0` when `s^10 ≤ N^9`, and
call `rest` otherwise. -/
def contSelBody (b rest : ℕ) : Expr :=
  .letE (.call (b + 1) (.var 0))
    (.ite (.arith .lt (powE (.get (.var 0) (.nat 9)) 9) (powE (.var 1) 10))
      (.call rest (.var 0)) (.nat 0))

/-- The selector of `Continue` at base `b` (six functions). -/
def contSelFuns (b rest : ℕ) : List Expr := [contSelBody b rest] ++ sizeFuns (b + 1)

namespace Iface

variable (I : Iface) (Pg : Program)

/-- **The rest of the selector of `Continue`**: above the threshold, it returns case `1`
(intransitive), `2` (transitive, at the floor) or `3` (transitive, off the floor), at cost at most
`B S`. -/
def RestSelSpec (rest : ℕ) (B : ∀ {Ω C : Type}, State Ω C → ℝ) : Prop :=
  ∀ {Ω C : Type} (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ), Function.Injective c →
    ∀ v : Val, I.InVal .cont e c v S → Good P₀ .cont S → (S.N : ℝ) ^ P₀.γ < S.size →
      FunAll Pg rest v (fun i cost => ∃ (j : ℕ) (hj : j < contCases.length), i = .nat j ∧
        contCases[j].P e S v ∧ (cost : ℝ) ≤ B S)

/-- **The selector of `Continue` meets its specification.** -/
theorem contSel_spec {b rest : ℕ} (h : Pg.HasAt b (contSelFuns b rest))
    {B : ∀ {Ω C : Type}, State Ω C → ℝ} (hrest : I.RestSelSpec Pg rest B)
    (hW : ∀ {Ω C : Type} (S : State Ω C),
      (contSelCost (stateW (Nat.card Ω) S) S.N : ℝ) + max 0 (B S) ≤ I.selW .cont S) :
    I.SelSpec Pg .cont contCases b := by
  intro Ω C S k e c hc v hv hg
  have hv' : Canon e c v S := hv
  have hk := card_eq e
  have hwv := hv'.wt_le
  have hkw := StateVal.k_le_wt hv'.stateVal
  have hentry : Pg.funs[b]? = some (contSelBody b rest) := by
    simpa [contSelFuns] using h 0 (by simp [contSelFuns])
  have hsz := size_spec (P := Pg) (b := b + 1) (by
    have := h.right (A := [_]) (B := sizeFuns (b + 1))
    simpa using this) hv'.stateVal
  have hcall := Det.call (P := Pg) (env := [v]) (Det.var' (i := 0) rfl) hsz
  have hs : S.size ≤ k := by
    have := Nat.card_le_card_of_injective (fun a : S.dom => e a.1)
      (fun a b h => Subtype.ext (e.injective h))
    exact this.trans (by simp)
  -- Reading `N` from the input.
  obtain ⟨gv, dv, xv, yv, hhv, rv, -, -, -, -, -, -, hvv⟩ := hv'.val
  have hvar : Det Pg [v, .nat S.size] (.var 0)
      (.list [.nat k, gv, dv, xv, yv, hhv, rv, boolVal S.floor, .nat S.h, .nat S.N])
      (v.wt + 1) := by
    have := Det.var' (P := Pg) (env := [v, .nat S.size]) (i := 0) (v := v) rfl
    rw [hvv] at this ⊢
    exact this
  have hN : Det Pg [v, .nat S.size] (.get (.var 0) (.nat 9)) (.nat S.N)
      (v.wt + 1 + (9 + 3) + (Val.nat S.N).wt + 1) := Det.get' hvar (Det.nat 9) rfl
  have hNw := wt_nat_le S.N
  have hN' := hN.mono (show _ ≤ v.wt + S.N + 20 by omega)
  have hS : Det Pg [v, .nat S.size] (.var 1) (.nat S.size) (S.size + 3) :=
    (Det.var' (P := Pg) (env := [v, .nat S.size]) (i := 1) rfl).mono
      (by have := wt_nat_le S.size; omega)
  have hpN := Det.powE hN' 9
  have hpS := Det.powE hS 10
  set t := BinOp.eval .lt (S.N ^ 9) (S.size ^ 10) with ht
  have htest := Det.arith (op := .lt) hpN hpS
  have ht1 : t ≤ 1 := by simp only [ht, BinOp.eval]; split_ifs <;> omega
  have htw : (Val.nat t).wt ≤ 3 := by
    have := wt_nat_le t; omega
  have htw' : (Val.nat (BinOp.eval .lt (S.N ^ 9) (S.size ^ 10))).wt ≤ 3 := htw
  -- The bound on everything but the call of `rest`.
  set W := stateW k S with hWdef
  have hcostN : 9 * (v.wt + S.N + 20 + (S.N + 1) ^ 9) + 4 ≤ 9 * (W + S.N + 20 + (S.N + 1) ^ 9) + 4 :=
    by omega
  have hcostS : 10 * (S.size + 3 + (S.size + 1) ^ 10) + 4 ≤ 10 * (W + 4 + (W + 1) ^ 10) + 4 := by
    have : (S.size + 1) ^ 10 ≤ (W + 1) ^ 10 := Nat.pow_le_pow_left (by omega) 10
    omega
  have hsizeC : sizeK * (v.wt + 1) ^ 2 ≤ sizeK * (W + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hsw := wt_nat_le S.size
  refine FunAll.intro hentry (EvalAll.letE (Ra := fun w c => w = .nat S.size ∧
    c ≤ v.wt + 1 + sizeK * (v.wt + 1) ^ 2 + (Val.nat S.size).wt + 1) hcall fun w ca hw => ?_)
  obtain ⟨rfl, hca⟩ := hw
  refine EvalAll.ite htest (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
  obtain ⟨hx, hcc⟩ := hx
  by_cases habove : S.N ^ 9 < S.size ^ 10
  · -- Above the threshold: call `rest`.
    have hx1 : x = 1 := by
      have : t = 1 := by simp only [ht, BinOp.eval, if_pos habove]
      simp only [Val.nat.injEq] at hx; omega
    subst hx1
    simp only [one_ne_zero, if_false]
    have hlarge : (S.N : ℝ) ^ P₀.γ < S.size := by
      rw [← not_le, le_rpow_iff]; omega
    refine EvalAll.call_funAll (Det.var' (P := Pg) (env := [v, .nat S.size]) (i := 0) rfl)
      fun v' cv hv'' => ?_
    obtain ⟨hvv', hcv⟩ := hv''
    rw [hvv']
    refine (hrest S k e c hc v hv hg hlarge).mono fun i cr ⟨j, hj, hi, hP, hcr⟩ => ?_
    subst hi
    refine ⟨j, hj, rfl, hP, ?_⟩
    simp only [selB, reduceCtorEq, if_false]
    have hj4 : j < 4 := by simpa [contCases] using hj
    have hjw : (Val.nat j).wt ≤ 6 := by have := wt_nat_le j; omega
    have hnat : ca + (cc + (cv + cr + (Val.nat j).wt + 1) + (Val.nat j).wt + 1) +
        (Val.nat j).wt + 1 ≤ contSelCost W S.N + cr := by
      unfold contSelCost
      omega
    have hW' := hW S
    rw [hk, ← hWdef] at hW'
    have hnat' : ((ca + (cc + (cv + cr + (Val.nat j).wt + 1) + (Val.nat j).wt + 1) +
        (Val.nat j).wt + 1 : ℕ) : ℝ) ≤ (contSelCost W S.N : ℝ) + cr := by exact_mod_cast hnat
    have hcr' : (cr : ℝ) ≤ B S := hcr
    have := le_max_right 0 (B S)
    have := le_max_right 0 (I.selW .cont S)
    linarith
  · -- At or below the threshold: case `0`.
    have hx0 : x = 0 := by
      have : t = 0 := by simp only [ht, BinOp.eval, if_neg habove]
      simp only [Val.nat.injEq] at hx; omega
    subst hx0
    simp only [if_true]
    refine (Det.nat (P := Pg) (env := [v, .nat S.size]) 0).post fun c0 hc0 => ?_
    refine ⟨0, by simp [contCases], rfl, ?_, ?_⟩
    · show (S.size : ℝ) ≤ (S.N : ℝ) ^ P₀.γ
      rw [le_rpow_iff]; omega
    simp only [selB, reduceCtorEq, if_false]
    have hw0 : (Val.nat 0).wt ≤ 3 := by simp [wt_nat, GI.Machine.len_zero]
    have hnat : ca + (cc + c0 + (Val.nat 0).wt + 1) + (Val.nat 0).wt + 1 ≤ contSelCost W S.N := by
      unfold contSelCost
      omega
    have hW' := hW S
    rw [hk, ← hWdef] at hW'
    have hnat' : ((ca + (cc + c0 + (Val.nat 0).wt + 1) + (Val.nat 0).wt + 1 : ℕ) : ℝ) ≤
        (contSelCost W S.N : ℝ) := by exact_mod_cast hnat
    have := le_max_left 0 (B S)
    have := le_max_right 0 (I.selW .cont S)
    linarith

end Iface

end GI.Impl
