module

public import Workspace.Impl.LinIntPresentation
public import Workspace.Lang.Lib.LinIntVector

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

/-- On [context,position,accumulator], append e at the selected position, zero elsewhere. -/
def linBasisStep : Expr :=
  .snoc (arg 2) (.ite (.arith .eq (.get (arg 0) (.nat 0)) (arg 1))
    (.get (arg 0) (.nat 1)) linIntZeroE)

def linBasisFuns (b : ℕ) : List Expr := loopFuns b (arg 2) .nil linBasisStep

def linBasisCost (W n : ℕ) : ℕ := 1000000 * (W + n + 1) ^ 3

set_option maxHeartbeats 1000000 in
theorem linBasis_spec {P : Program} {b n : ℕ} (hp : P.HasAt b (linBasisFuns b))
    (i : Fin n) (e : ℤ) :
    FunDet P b (.list [.nat i.val, encInt e, .nat n]) (linVecVal (Pi.single i e))
      (linBasisCost (Val.list [.nat i.val, encInt e, .nat n]).wt n) := by
  let a := Val.list [.nat i.val, encInt e, .nat n]
  let W := a.wt
  let xs := (List.finRange n).map fun j => encInt ((Pi.single i e : Fin n → ℤ) j)
  let M := linVectorAccWt n (W + 100)
  have we : (encInt e).wt < W := wt_le_wt_list (by simp)
  have w1 : (Val.nat 1).wt = 3 := rfl
  have wz : (encInt 0).wt ≤ 100 := by decide
  have wentry (j : Fin n) : (encInt ((Pi.single i e : Fin n → ℤ) j)).wt ≤ W + 100 := by
    by_cases h : j = i
    · subst j; simpa using we.le.trans (Nat.le_add_right W 100)
    · simpa [Pi.single_apply, h] using wz.trans (by omega : 100 ≤ W + 100)
  have wacc (k : ℕ) : (Val.list (xs.take k)).wt ≤ M := by
    have hh := linWtList (vs := xs.take k) (B := W + 100) (by
      intro x hx
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hx)
      exact wentry j)
    have hl : (xs.take k).length ≤ n := by simp [xs]
    unfold M linVectorAccWt
    exact hh.trans (by gcongr)
  have dk := Det.arg' (P := P) (vs := [.nat i.val, encInt e, .nat n]) (rest := []) (j := 2) rfl
  have hlp := loopBdd_spec hp dk Det.nil (by
    have := a.two_le_size
    have := a.size_le_wt
    simp only [a] at *
    omega)
    (Inv := fun k acc => acc = .list (xs.take k)) (M := M) (D := fun _ => 1000 * (W + n + M + 1))
    (by simp) (fun k acc _ he => he ▸ wacc k) (fun k acc hk he => ?_)
  · refine hlp.mono fun out cost ho => ⟨?_, ?_⟩
    · have hlen : xs.length = n := by simp [xs]
      have h1 := ho.1
      rw [← hlen, List.take_length] at h1
      exact h1
    · have hc := ho.2
      change cost ≤ (∑ _ ∈ Finset.range n, 1000 * (W + n + M + 1)) + loopModK * (n + 1) * (W + n + M + 1) at hc
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, loopModK] at hc
      unfold linBasisCost
      change cost ≤ 1000000 * (W + n + 1) ^ 3
      simp only [M, linVectorAccWt, W, a, loopModK] at hc ⊢
      ring_nf at *
      omega
  · subst acc
    let j : Fin n := ⟨k, hk⟩
    have dctx := Det.arg' (P := P) (vs := [a, .nat k, .list (xs.take k)]) (rest := []) (j := 0) rfl
    have di := Det.get' dctx (Det.nat 0) rfl
    have de := Det.get' dctx (Det.nat 1) rfl
    have dj := Det.arg' (P := P) (vs := [a, .nat k, .list (xs.take k)]) (rest := []) (j := 1) rfl
    have hii := i.isLt
    have dc := Det.arith (op := .eq) di dj
    have dz : Det P [.list [a, .nat k, .list (xs.take k)]] linIntZeroE (encInt 0) _ := Det.mk2 (Det.nat 0) Det.nil
    have db : Det P [.list [a, .nat k, .list (xs.take k)]]
        (.ite (.arith .eq (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)) linIntZeroE)
        (encInt ((Pi.single i e : Fin n → ℤ) j)) (100 * (W + n + M + 1)) := by
      by_cases hij : i = j
      · rw [← hij, Pi.single_eq_same]
        have hik : i.val = k := by simpa using congrArg Fin.val hij
        have dc' := dc
        simp only [GI.Machine.BinOp.eval_eq, hik, beq_self_eq_true, Bool.toNat_true] at dc'
        have dd := Det.ite_pos (e := linIntZeroE) dc' (by decide : 1 ≠ 0) de
        exact dd.mono (c' := 100 * (W + n + M + 1)) (by
          have wi := wt_nat_le i.val
          have wk := wt_nat_le k
          have wa := wt_list3_le a (.nat k) (.list (xs.take k))
          have wm := wacc k
          simp only [W, a, Fin.val_mk, ite_true] at *
          omega)
      · have hik : i.val ≠ k := by intro hh; apply hij; exact Fin.ext hh
        have dc' := dc
        simp only [GI.Machine.BinOp.eval_eq, if_neg hik] at dc'
        have dd := Det.ite_zero (t := .get (arg 0) (.nat 1)) dc' dz
        have hz : (Pi.single i e : Fin n → ℤ) j = 0 := by simp [Pi.single_apply, hij, Ne.symm hij]
        rw [hz]
        exact dd.mono (by
          have wi := wt_nat_le i.val
          have wk := wt_nat_le k
          have wa := wt_list3_le a (.nat k) (.list (xs.take k))
          have wm := wacc k
          have w0 : (Val.nat 0).wt = 2 := rfl
          have wnil : (Val.list []).wt = 4 := rfl
          simp only [W, a, j, Fin.val_mk, ite_true] at *
          norm_num [encInt, Nat.bits] at *
          omega)
    have da := Det.arg' (P := P) (vs := [a, .nat k, .list (xs.take k)]) (rest := []) (j := 2) rfl
    have dn := Det.snoc da db
    have hj : (List.finRange n)[k]'((by simpa using hk)) = j := by
      rw [List.getElem_finRange]
      apply Fin.ext
      rfl
    refine dn.post fun cost hc => ⟨?_, ?_⟩
    · have ht : xs.take (k + 1) = xs.take k ++ [encInt ((Pi.single i e : Fin n → ℤ) j)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp [xs]; omega)]
        simp only [xs, List.getElem_map, Option.toList_some]
        rw [hj]
      rw [ht]
    · have wa := wt_list3_le a (.nat k) (.list (xs.take k))
      have wk := wt_nat_le k
      have wm := wacc k
      have wn := wacc (k + 1)
      have we' := wentry j
      have ht : xs.take (k + 1) = xs.take k ++ [encInt ((Pi.single i e : Fin n → ℤ) j)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp [xs]; omega)]
        simp only [xs, List.getElem_map, Option.toList_some]
        rw [hj]
      rw [ht] at wn
      change cost ≤ 1000 * (W + n + M + 1) + 100 * (W + n + M + 1)
      simp only [W, a] at *
      omega

end GI.Impl
