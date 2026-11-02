import Workspace.Impl.AggItemCiDisp

/-!
# Cases 2b and 3: the test `q ≤ N^α` in exact arithmetic

The item of two pair configurations is the configuration query when `q ≤ N^α` and the
first-rectangle item otherwise (`cfgOutItem`). With `α = 2/5` (`P₀`), the test is
`q⁵ ≤ N²` on naturals (`itci_rpow_iff`). The program reads `N` from the canonical state value
(its last entry, `Canon`) and `q` from the start state, both inside `K.v`
(`itci_test_spec`): it computes `[N² < q⁵]`, so `1` means the first-rectangle item.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)
open GI.Machine (BinOp)

theorem itci_P₀_α : P₀.α = 2 / 5 := rfl

/-- **The test in exact arithmetic**: `q ≤ N^{2/5}` exactly when `q⁵ ≤ N²`. -/
theorem itci_rpow_iff (q N : ℕ) : ((q : ℝ) ≤ (N : ℝ) ^ P₀.α) ↔ q ^ 5 ≤ N ^ 2 := by
  rw [itci_P₀_α]
  have hN : (0 : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 5) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h5 : ((N : ℝ) ^ ((2 : ℝ) / 5)) ^ (5 : ℕ) = (N : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  constructor
  · intro h
    have := pow_le_pow_left₀ (Nat.cast_nonneg q) h 5
    rw [h5] at this
    exact_mod_cast this
  · intro h
    have h' : ((q : ℝ)) ^ (5 : ℕ) ≤ ((N : ℝ) ^ ((2 : ℝ) / 5)) ^ (5 : ℕ) := by
      rw [h5]; exact_mod_cast h
    exact le_of_pow_le_pow_left₀ (by norm_num) hN h'

/-- The value `N` in `K.v`: entry `9` of the state value, entry `0` of the start state. -/
def itciNE (v : Expr) : Expr := .get (.get (.get v (.nat 0)) (.nat 0)) (.nat 9)

/-- The value `q` in `K.v`: entry `1` of the sizes `[k, q]` of the start state. -/
def itciQE (v : Expr) : Expr := .get (.get (.get v (.nat 0)) (.nat 1)) (.nat 1)

/-- **The test**: `[N² < q⁵]` on `K.v`. -/
def itciTestE (v : Expr) : Expr :=
  .arith .lt (.arith .mul (itciNE v) (itciNE v))
    (.arith .mul (.arith .mul (.arith .mul (.arith .mul (itciQE v) (itciQE v)) (itciQE v))
      (itciQE v)) (itciQE v))

theorem itci_wt_mem {vs : List Val} {v : Val} (h : v ∈ vs) : v.wt ≤ (Val.list vs).wt :=
  (wt_le_wt_list h).le

theorem itci_wt_mul {a b : ℕ} : (Val.nat (a * b)).wt ≤ (Val.nat a).wt + (Val.nat b).wt := by
  rw [wt_nat, wt_nat, wt_nat]; have := GI.Machine.len_mul_le a b; omega

section Ctx

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S} {e : Ω ≃ Fin k}
  {c : C → ℕ}

/-- **The test as a program**, on an expression `v` for `K.v`. -/
theorem itci_test_spec {K : ItSCtx k S L} (hK : K.OK e c) {P : Program} {env : List Val}
    {v : Expr} {nv Ev W : ℕ} (hv : StDC P env v K.v nv Ev W) (hW : 5 * K.v.wt + 20 ≤ W) :
    StDC P env (itciTestE v) (.nat (if S.N ^ 2 < L.q ^ 5 then 1 else 0)) (20 * nv + 100)
      (20 * Ev) W := by
  obtain ⟨gv, dv, xv, yv, hv', rv, -, -, -, -, -, -, hsv⟩ := hK.can.val
  have hst : K.st = .list [K.sv, .list [.nat k, .nat L.q], .list (K.ps.map pairV),
      .list (K.fx.map pairV), .list (K.fy.map pairV), stCv K.O.tuples
      (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)] := rfl
  have hKv : K.v = .list [K.st, .list [encKColoring K.d, encKColoring K.d'],
      .nat (AggCase.code K.case), natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))] := rfl
  -- weights of the parts
  have w1 : K.st.wt ≤ K.v.wt := by rw [hKv]; exact itci_wt_mem (by simp)
  have w2 : K.sv.wt ≤ K.st.wt := by rw [hst]; exact itci_wt_mem (by simp)
  have w3 : (Val.list [.nat k, .nat L.q]).wt ≤ K.st.wt := by rw [hst]; exact itci_wt_mem (by simp)
  have w4 : (Val.nat L.q).wt ≤ (Val.list [.nat k, .nat L.q]).wt := itci_wt_mem (by simp)
  have w5 : (Val.nat S.N).wt ≤ K.sv.wt := by rw [hsv]; exact itci_wt_mem (by simp)
  have w5' := w5
  have gst := StDC.get hv (StDC.nat 0 (by omega)) (v := K.st) rfl (by omega)
  have gsv := StDC.get gst (StDC.nat 0 (by omega)) (v := K.sv) rfl (by omega)
  rw [hsv] at gsv w5
  have gN := StDC.get gsv (StDC.nat 9 (by omega)) (v := .nat S.N) rfl (by omega)
  have gkq := StDC.get gst (StDC.nat 1 (by omega)) (v := .list [.nat k, .nat L.q])
    rfl (by omega)
  have gq := StDC.get gkq (StDC.nat 1 (by omega)) (v := .nat L.q) rfl (by omega)
  have m1 := StDC.arith gN gN (op := .mul) (z := S.N * S.N) rfl (le_trans itci_wt_mul (by omega))
  have q2 := StDC.arith gq gq (op := .mul) (z := L.q * L.q) rfl (le_trans itci_wt_mul (by omega))
  have q3 := StDC.arith q2 gq (op := .mul) (z := L.q * L.q * L.q) rfl
    (le_trans itci_wt_mul (by have := @itci_wt_mul L.q L.q; omega))
  have q4 := StDC.arith q3 gq (op := .mul) (z := L.q * L.q * L.q * L.q) rfl
    (le_trans itci_wt_mul (by have := @itci_wt_mul L.q L.q; have := @itci_wt_mul (L.q * L.q) L.q; omega))
  have q5 := StDC.arith q4 gq (op := .mul) (z := L.q * L.q * L.q * L.q * L.q) rfl
    (le_trans itci_wt_mul (by
      have := @itci_wt_mul L.q L.q; have := @itci_wt_mul (L.q * L.q) L.q
      have := @itci_wt_mul (L.q * L.q * L.q) L.q; omega))
  have hz : BinOp.lt.eval (S.N * S.N) (L.q * L.q * L.q * L.q * L.q) =
      if S.N ^ 2 < L.q ^ 5 then 1 else 0 := by
    simp only [BinOp.eval_lt]; ring_nf
  have t := StDC.arith m1 q5 hz (by split_ifs <;> (have := wt_nat_le 1; have := wt_nat_le 0; omega))
  unfold itciTestE itciNE itciQE
  exact t.mono (by omega) (by omega)

end Ctx

end GI.Impl
