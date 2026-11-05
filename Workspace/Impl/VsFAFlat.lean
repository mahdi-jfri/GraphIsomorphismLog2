module

public import Workspace.Impl.VStabLinUnit
public import Workspace.Impl.VsFMatMul

@[expose] public section

/-!
# Flattening a matrix

A matrix, as the list of its rows, becomes one vector: the rows one after the other. This is a
`foldl` of `append` over the rows (`vsFFlatFuns`, `vsFFlat_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- The step of the flattening, on `[c, acc, row]`: `acc ++ row`. -/
def vsFFlatStepF (app : ℕ) : Expr := .call app (mk2 (arg 1) (arg 2))

/-- The flattening, at base `b` (7 functions), on `[0, rows, []]`. -/
def vsFFlatFuns (b : ℕ) : List Expr :=
  foldlFuns b (b + 3) ++ [vsFFlatStepF (b + 4)] ++ appendFuns (b + 4)

theorem vsFFlatFuns_length (b : ℕ) : (vsFFlatFuns b).length = 7 := rfl

theorem vsFA_take_flatten_length_le (M : List (List ℕ)) (i : ℕ) :
    (M.take i).flatten.length ≤ M.flatten.length := by
  conv_rhs => rw [← List.take_append_drop i M]
  rw [List.flatten_append, List.length_append]
  omega

theorem vsFA_take_flatten_le {M : List (List ℕ)} {N : ℕ} (h : ∀ r ∈ M, ∀ y ∈ r, y ≤ N) (i : ℕ) :
    ∀ y ∈ (M.take i).flatten, y ≤ N := by
  intro y hy
  obtain ⟨r, hr, hyr⟩ := List.mem_flatten.mp hy
  exact h r (List.mem_of_mem_take hr) y hyr

theorem vsFA_take_succ_flatten (M : List (List ℕ)) (i : ℕ) (hi : i < M.length) :
    (M.take (i + 1)).flatten = (M.take i).flatten ++ M[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.flatten_append,
    List.flatten_singleton]

theorem vsFFlatStep_spec {P : Program} {f app : ℕ} (hf : P.funs[f]? = some (vsFFlatStepF app))
    (ha : P.HasAt app (appendFuns app)) {N : ℕ} {xs ys : List ℕ} (hx : ∀ y ∈ xs, y ≤ N)
    (hxl : xs.length ≤ N) (hy : ∀ y ∈ ys, y ≤ N) (hyl : ys.length ≤ N) (hxy : (xs ++ ys).length ≤ N) :
    FunDet P f (.list [.nat 0, natList xs, natList ys]) (natList (xs ++ ys))
      (10 ^ 5 * (N + 1) ^ 3) := by
  have wx := wt_natList_le_sq hx hxl
  have wy := wt_natList_le_sq hy hyl
  have wxy := wt_natList_le_sq (xs := xs ++ ys) (fun y h => by
    rcases List.mem_append.mp h with h | h
    · exact hx y h
    · exact hy y h) hxy
  have d1 := Det.arg' (P := P) (rest := []) (vs := [.nat 0, natList xs, natList ys]) (j := 1) rfl
  have d2 := Det.arg' (P := P) (rest := []) (vs := [.nat 0, natList xs, natList ys]) (j := 2) rfl
  have happ := append_spec ha (xs.map Val.nat) (ys.map Val.nat)
  have e : Val.list (xs.map Val.nat ++ ys.map Val.nat) = natList (xs ++ ys) := by
    simp [natList]
  rw [e] at happ
  have ew : (Val.list [Val.list (xs.map Val.nat), Val.list (ys.map Val.nat)]).wt =
    (Val.list [natList xs, natList ys]).wt := rfl
  have hl : (ys.map Val.nat).length = ys.length := List.length_map ..
  have happ' : FunAll P app (.list [natList xs, natList ys]) (fun w c => w = natList (xs ++ ys) ∧
      c ≤ 1000 * (N + 1) * (40 * (N + 1) ^ 2)) := by
    refine happ.mono fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
    rw [hw, hl, ew] at hc
    have w2 := wt_list2_le (natList xs) (natList ys)
    have hK : loopModK = 1000 := rfl
    rw [hK] at hc
    have hN1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    exact hc.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega))
  refine FunDet.intro hf ((Det.call (Det.mk2 d1 d2) happ').mono ?_)
  have w2 := wt_list2_le (natList xs) (natList ys)
  have w3 := wt_list3_le (.nat 0) (natList xs) (natList ys)
  have w0 := wt_nat_le 0
  have hN1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : 1000 * (N + 1) * (40 * (N + 1) ^ 2) = 40000 * (N + 1) ^ 3 := by ring
  omega

/-- **Flattening.** On `[0, rows, []]` the result is the flattened matrix. -/
theorem vsFFlat_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsFFlatFuns b)) {N : ℕ}
    {M : List (List ℕ)} (hM : ∀ r ∈ M, ∀ y ∈ r, y ≤ N) (hMl : ∀ r ∈ M, r.length ≤ N)
    (hl : M.length ≤ N) (hfl : M.flatten.length ≤ N) :
    FunDet P b (.list [.nat 0, .list (M.map natList), natList []]) (natList M.flatten)
      (10 ^ 6 * (N + 1) ^ 4) := by
  have hfo : P.HasAt b (foldlFuns b (b + 3)) := h.block 0 rfl
  have hst : P.funs[b + 3]? = some (vsFFlatStepF (b + 4)) :=
    h.get (j := 3) (by rw [vsFFlatFuns_length]; omega)
  have hap : P.HasAt (b + 4) (appendFuns (b + 4)) := h.block 4 rfl
  have hN1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  refine ((foldl_spec hfo (c := .nat 0) (xs := M.map natList) (acc0 := natList [])
    (M := 5 * (N + 1) ^ 2) (B := fun _ => 10 ^ 5 * (N + 1) ^ 3)
    (Inv := fun i acc => acc = natList (M.take i).flatten) (by simp)
    (fun i acc _ hacc => by
      rw [hacc]
      exact wt_natList_le_sq (vsFA_take_flatten_le hM i)
        ((vsFA_take_flatten_length_le M i).trans hfl))
    (fun i acc hi hacc => by
      rw [List.length_map] at hi
      rw [hacc, List.getElem_map]
      have ht := vsFA_take_succ_flatten M i hi
      have hs := vsFFlatStep_spec hst hap (vsFA_take_flatten_le hM i)
        ((vsFA_take_flatten_length_le M i).trans hfl) (hM _ (List.getElem_mem hi))
        (hMl _ (List.getElem_mem hi)) (by rw [← ht]; exact (vsFA_take_flatten_length_le M _).trans hfl)
      rw [← ht] at hs
      exact hs)).mono fun w c hw => ⟨?_, ?_⟩)
  · rw [hw.1, List.length_map, List.take_length]
  · have hc := hw.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map] at hc
    have wM := wt_vsFMat_le hM hMl (by omega)
    have w3 := wt_list3_le (.nat 0) (.list (M.map natList)) (natList [])
    have w0 := wt_nat_le 0
    have wn : (natList []).wt ≤ 5 := by decide
    have hK : loopModK = 1000 := rfl
    rw [hK] at hc
    have k1 : M.length * (10 ^ 5 * (N + 1) ^ 3) ≤ (N + 1) * (10 ^ 5 * (N + 1) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have k2 : 1000 * (M.length + 1) *
        ((Val.list [.nat 0, .list (M.map natList), natList []]).wt + M.length +
          5 * (N + 1) ^ 2 + 1) ≤ 1000 * (N + 1) * (100 * (N + 1) ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e1 : (N + 1) * (10 ^ 5 * (N + 1) ^ 3) = 10 ^ 5 * (N + 1) ^ 4 := by ring
    have e2 : 1000 * (N + 1) * (100 * (N + 1) ^ 3) = 10 ^ 5 * (N + 1) ^ 4 := by ring
    omega

end GI.Impl
