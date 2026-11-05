module

public import Workspace.Impl.JohnStep

@[expose] public section

/-!
# The fold over the pairs

The function at `74` folds `johnStepF` over the pair indices `0, …, n² - 1`, starting from the
empty list. It computes `johnLam` (`john_fold_spec`). The cost bound needs a bound on the
partial results, which is the hypothesis `hok`. It holds for the labels of the program by
`john_prefix` and `JohnHyp.m_le`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

theorem john_sq1_le (n : ℕ) : n * n + 1 ≤ (n + 1) ^ 4 := by
  have h1 : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have h2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := john_pow_le (by omega) (by omega)
  omega

/-- **The fold over the pairs.** -/
theorem john_fold_spec {n : ℕ} {labL : List ℕ} {δ υ : ℕ} (hL : JohnLabOK n labL δ)
    (hυ : υ ≤ n * n)
    (hok : ∀ i ≤ n * n, JohnAccOK n (((List.range (n * n)).take i).foldl (johnStep n labL δ υ) [])) :
    FunDet johnProgram 74 (.list [johnCtxV n labL δ υ, natList (List.range (n * n)), .list []])
      (.list ((johnLam n labL δ υ).map natList)) (100000000 * (n + 1) ^ 8) := by
  set xs := (List.range (n * n)).map Val.nat with hxs
  have hxl : xs.length = n * n := by simp [xs]
  have hR : natList (List.range (n * n)) = .list xs := rfl
  rw [hR]
  set F := fun i => ((List.range (n * n)).take i).foldl (johnStep n labL δ υ) [] with hF
  refine (foldl_spec john_at_fold (c := johnCtxV n labL δ υ) (xs := xs) (acc0 := .list [])
    (Inv := fun i acc => acc = .list ((F i).map natList)) (M := 20 * (n + 1) ^ 2)
    (B := fun _ => 10000000 * (n + 1) ^ 4) (by simp [F]) ?_ ?_).mono fun w cost hw => ⟨?_, ?_⟩
  · intro i acc hi hinv
    rw [hinv]
    exact john_wt_acc (hok i (hxl ▸ hi))
  · intro i acc hi hinv
    rw [hinv]
    have hi' : i < n * n := hxl ▸ hi
    have hx : xs[i] = .nat i := by simp [xs]
    rw [hx]
    refine FunAll.mono (john_stepF_spec hL hυ (hok i hi'.le) hi') fun w c hw => ⟨?_, hw.2⟩
    rw [hw.1]
    simp only [F]
    rw [List.take_add_one, List.getElem?_range hi', Option.toList_some, List.foldl_append]
    rfl
  · rw [hw.1, hxl]
    have e : F (n * n) = johnLam n labL δ υ := by
      simp only [F]
      rw [List.take_of_length_le (by simp)]
      rfl
    rw [e]
  · have hc := hw.2
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, hxl] at hc
    have ea := wt_list3_le (johnCtxV n labL δ υ) (.list xs) (.list [])
    rw [← hR] at ea
    have ec : (johnCtxV n labL δ υ).wt = (Val.list [johnDV n labL δ, natList labL, .nat n, .nat υ,
      natList (List.range n)]).wt := rfl
    have e1 := wt_list_le [johnDV n labL δ, natList labL, .nat n, .nat υ, natList (List.range n)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at e1
    have wD := john_wt_DV n labL δ
    have wl := john_wt_natList_sq hL.len hL.le
    have wR := john_wt_Rn n
    have wR2 := john_wt_R2 (n := n)
    have w1 := wt_nat_le n
    have w2 := wt_nat_le υ
    have w0 : (Val.list []).wt ≤ 10 := by simp [Val.wt, GI.Machine.len_zero]
    have y1 := john_sq_le4 n
    have y24 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := john_pow_le (by omega) (by omega)
    have ys := john_sq1_le n
    have y0 := john_le_sq n
    have yp : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hQ : (Val.list [johnCtxV n labL δ υ, natList (List.range (n * n)), .list []]).wt + n * n +
        20 * (n + 1) ^ 2 + 1 ≤ 500 * (n + 1) ^ 4 := by omega
    have p1 : n * n * (10000000 * (n + 1) ^ 4) ≤ 10000000 * (n + 1) ^ 8 := by
      calc _ ≤ (n + 1) ^ 4 * (10000000 * (n + 1) ^ 4) := Nat.mul_le_mul y1 le_rfl
        _ = _ := by ring
    have p2 : loopModK * (n * n + 1) * ((Val.list [johnCtxV n labL δ υ,
        natList (List.range (n * n)), .list []]).wt + n * n + 20 * (n + 1) ^ 2 + 1) ≤
        500000 * (n + 1) ^ 8 := by
      calc _ ≤ 1000 * (n + 1) ^ 4 * (500 * (n + 1) ^ 4) :=
            Nat.mul_le_mul (Nat.mul_le_mul le_rfl ys) hQ
        _ = _ := by ring
    rw [hR] at p2
    omega

end GI.Impl
