/-
**Searching an enumerated group.** A group given as the list `els` of its elements (for example
the result of the enumeration `enum_spec`, `Workspace.Lang.Lib.Schreier`) can be searched with a
test: a language function `tf` that sends `[c, encPerm σ]` to the Boolean `q σ`.

* `transpAll_spec`: the elements that pass the test (`filterFuns`), for instance the transporter
  `{σ ∈ G | σ(Δ) = Δ'}` when the test checks the condition.
* `transpFirst_spec`: the first element that passes the test, or nothing (`transpFirstFuns`).

Both cost at most `|els| T + 3 loopModK (|els| + 1) (W + 1)`, where `T` bounds the cost of the
test and `W` is the weight of the argument.
-/
import Workspace.Lang.Lib.Schreier

namespace GI.Lang

open GI.Machine (BinOp len len_le_self len_mono)
open GI.Cited (Val encPerm encPerms)
open Equiv

variable {n : ℕ}

open Classical in
/-- A test on permutations, as a test on values. -/
noncomputable def liftTest (n : ℕ) (q : Perm (Fin n) → Bool) (v : Val) : Bool :=
  decide (∃ σ : Perm (Fin n), v = encPerm σ ∧ q σ = true)

theorem liftTest_encPerm (q : Perm (Fin n) → Bool) (σ : Perm (Fin n)) :
    liftTest n q (encPerm σ) = q σ := by
  classical
  unfold liftTest
  by_cases h : q σ = true
  · rw [h]; exact decide_eq_true ⟨σ, rfl, h⟩
  · rw [Bool.not_eq_true] at h
    rw [h]
    refine decide_eq_false ?_
    rintro ⟨τ, hτ, hq⟩
    rw [← encPerm_injective hτ, h] at hq
    exact absurd hq (by decide)

theorem liftTest_comp (q : Perm (Fin n) → Bool) : liftTest n q ∘ encPerm = q :=
  funext fun σ => liftTest_encPerm q σ

/-- A sublist weighs at most as much as the list. -/
theorem wt_list_sublist {l₁ l₂ : List Val} (h : l₁.Sublist l₂) :
    (Val.list l₁).wt ≤ (Val.list l₂).wt := by
  rw [wt_list_eq, wt_list_eq]
  have h1 := (h.map Val.wt).sum_le_sum (fun _ _ => Nat.zero_le _)
  have h2 := len_mono h.length_le
  have h3 := len_mono ((h.map Val.size).sum_le_sum (fun _ _ => Nat.zero_le _))
  omega

/-! ### All elements that pass the test -/

/-- **All elements that pass a test.** On `[c, [encPerm σ | σ ∈ els]]`, the list of the elements
`σ` of `els` with `q σ`, in order. -/
theorem transpAll_spec {P : Program} {b tf : ℕ} (h : P.HasAt b (filterFuns b tf)) {c : Val}
    (els : List (Perm (Fin n))) (q : Perm (Fin n) → Bool) {T : ℕ}
    (ht : ∀ σ ∈ els, FunDet P tf (.list [c, encPerm σ]) (boolVal (q σ)) T) :
    FunAll P b (.list [c, .list (els.map encPerm)]) (fun w cost =>
      w = .list ((els.filter q).map encPerm) ∧
      cost ≤ els.length * T + 3 * loopModK * (els.length + 1) *
        ((Val.list [c, .list (els.map encPerm)]).wt + 1)) := by
  have hF := filter_spec h (c := c) (xs := els.map encPerm) (q := liftTest n q) (B := fun _ => T)
    (by
      intro x hx
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hx
      rw [liftTest_encPerm]; exact ht σ hσ)
  refine hF.mono fun w cost hw => ?_
  have e : (els.map encPerm).filter (liftTest n q) = (els.filter q).map encPerm := by
    rw [List.filter_map, liftTest_comp]
  rw [e] at hw
  refine ⟨hw.1, ?_⟩
  have hc := hw.2
  rw [hw.1] at hc
  rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
  have w1 : (Val.list ((els.filter q).map encPerm)).wt ≤ (Val.list (els.map encPerm)).wt :=
    wt_list_sublist ((List.filter_sublist).map encPerm)
  have w2 : (Val.list (els.map encPerm)).wt < (Val.list [c, .list (els.map encPerm)]).wt :=
    wt_le_wt_list (by simp)
  have w3 := length_lt_wt_list (els.map encPerm)
  rw [List.length_map] at w3
  have h1 : loopModK * (els.length + 1) * ((Val.list [c, .list (els.map encPerm)]).wt +
      els.length + (Val.list ((els.filter q).map encPerm)).wt + 1) ≤
      loopModK * (els.length + 1) * (3 * ((Val.list [c, .list (els.map encPerm)]).wt + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  have e2 : loopModK * (els.length + 1) * (3 * ((Val.list [c, .list (els.map encPerm)]).wt + 1)) =
      3 * loopModK * (els.length + 1) * ((Val.list [c, .list (els.map encPerm)]).wt + 1) := by ring
  omega

/-! ### The first element that passes the test -/

/-- On `[c, xs]`: `[xs[i]]` for the first `i` that passes the test, or `[]`. -/
def transpFirstF (fd : ℕ) : Expr :=
  .letE (.call fd (.var 0))
    (.ite (.arith .lt (.var 1) (.length (arg 1))) (mk1 (.get (arg 1) (.var 1))) .nil)

/-- The program of the first element that passes the test `tf`, at base `b` (four functions). -/
def transpFirstFuns (b tf : ℕ) : List Expr := [transpFirstF (b + 1)] ++ findFuns (b + 1) tf

theorem find?_eq_findIdx {α : Type} (l : List α) (q : α → Bool) :
    l.find? q = if h : l.findIdx q < l.length then some l[l.findIdx q] else none := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : q a = true
    · simp [List.findIdx_cons, ha]
    · simp only [Bool.not_eq_true] at ha
      simp only [List.find?_cons, ha, List.findIdx_cons, cond_false, List.length_cons,
        Nat.add_lt_add_iff_right, List.getElem_cons_succ, ih]

/-- **The first element that passes a test.** On `[c, [encPerm σ | σ ∈ els]]`, the list
`[encPerm σ]` for the first element `σ` of `els` with `q σ`, or `[]` if there is none. -/
theorem transpFirst_spec {P : Program} {b tf : ℕ} (h : P.HasAt b (transpFirstFuns b tf))
    {c : Val} (els : List (Perm (Fin n))) (q : Perm (Fin n) → Bool) {T : ℕ}
    (ht : ∀ σ ∈ els, FunDet P tf (.list [c, encPerm σ]) (boolVal (q σ)) T) :
    FunDet P b (.list [c, .list (els.map encPerm)]) (.list ((els.find? q).toList.map encPerm))
      (els.length * T + 3 * loopModK * (els.length + 1) *
        ((Val.list [c, .list (els.map encPerm)]).wt + 1)) := by
  simp only [transpFirstFuns] at h
  have he : P.funs[b]? = some (transpFirstF (b + 1)) := h.left.single
  have hfd : P.HasAt (b + 1) (findFuns (b + 1) tf) := by simpa using h.right
  set W := (Val.list [c, .list (els.map encPerm)]).wt with hW
  have hF : FunDet P (b + 1) (.list [c, .list (els.map encPerm)]) (.nat (els.findIdx q))
      (els.length * T + loopModK * (els.length + 1) * (W + 2 * els.length + 3)) := by
    refine (find_spec hfd (c := c) (xs := els.map encPerm) (q := liftTest n q)
      (B := fun _ => T) (by
        intro x hx
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hx
        rw [liftTest_encPerm]; exact ht σ hσ)).mono fun w cost hw => ⟨?_, ?_⟩
    · rw [hw.1, List.findIdx_map, liftTest_comp]
    · have hc := hw.2
      rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
      exact hc
  set vs : List Val := [c, .list (els.map encPerm)] with hvs
  have dF := Det.call (Det.var' (P := P) (env := [.list vs]) (i := 0) rfl) hF
  have e1 : ∀ r : List Val, Det P (.list vs :: r) (arg 1) (.list (els.map encPerm))
      (2 * (Val.list vs).wt + 1 + 5) := fun r => Det.arg' (j := 1) rfl
  have dCmp := Det.arith (op := .lt) (Det.var' (P := P) (env := [.list vs, .nat (els.findIdx q)])
    (i := 1) rfl) (Det.length (e1 _))
  have w3 := length_lt_wt_list (els.map encPerm)
  have w2 : (Val.list (els.map encPerm)).wt < W := wt_le_wt_list (by simp)
  rw [List.length_map] at w3
  have wI := wt_nat_le (els.findIdx q)
  have wI' : els.findIdx q ≤ els.length := List.findIdx_le_length
  have wB : (Val.nat (BinOp.eval .lt (els.findIdx q) (els.map encPerm).length)).wt ≤ 3 := by
    simp only [BinOp.eval]; split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
  have hres : (Val.list ((els.find? q).toList.map encPerm)).wt ≤ W := by
    refine le_of_lt (lt_of_le_of_lt (wt_list_sublist ?_) w2)
    rw [find?_eq_findIdx]
    split_ifs with hi
    · simp only [Option.toList_some, List.map_cons, List.map_nil, List.singleton_sublist]
      exact List.mem_map_of_mem (List.getElem_mem hi)
    · simp
  refine FunDet.intro he ((Det.letE dF (Det.ite dCmp (v := .list ((els.find? q).toList.map encPerm))
    (ct := 8 * W + 20) (ce := 5) (fun hx => ?_) (fun hx => ?_))).mono ?_)
  · have hi : els.findIdx q < els.length := by
      simp only [BinOp.eval, List.length_map] at hx; by_contra h; simp [h] at hx
    have hv : (els.find? q).toList.map encPerm = [encPerm els[els.findIdx q]] := by
      rw [find?_eq_findIdx, dif_pos hi]; rfl
    rw [hv]
    have dG := Det.get' (e1 [.nat (els.findIdx q)]) (Det.var' (P := P)
      (env := [.list vs, .nat (els.findIdx q)]) (i := 1) rfl)
      (show (els.map encPerm)[els.findIdx q]? = some (encPerm els[els.findIdx q]) by simp [hi])
    refine (Det.mk1 dG).mono ?_
    have hm : encPerm els[els.findIdx q] ∈ els.map encPerm := List.mem_map_of_mem (List.getElem_mem hi)
    have w4 : (encPerm els[els.findIdx q]).wt < (Val.list (els.map encPerm)).wt := wt_le_wt_list hm
    have w5 := wt_list1_le (encPerm els[els.findIdx q])
    have w6 : (Val.list vs).wt = W := rfl
    omega
  · have hi : ¬ els.findIdx q < els.length := fun h => by simp [BinOp.eval, h] at hx
    have hv : (els.find? q).toList.map encPerm = [] := by
      rw [find?_eq_findIdx, dif_neg hi]; rfl
    rw [hv]
    exact Det.nil
  · have w6 : (Val.list vs).wt = W := rfl
    have hl : 2 * els.length + 4 ≤ (Val.list (els.map encPerm)).wt := by
      have h1 := length_le_cellsList (els.map encPerm)
      have h2 := sum_size_le_sum_wt (els.map encPerm)
      rw [length_cellsList, List.length_map] at h1
      rw [wt_list_eq, List.length_map]
      omega
    have h1 : loopModK * (els.length + 1) * (W + 2 * els.length + 3) ≤
        loopModK * (els.length + 1) * (2 * W) := Nat.mul_le_mul_left _ (by omega)
    have h2 : 1000 * (W + 3) ≤ loopModK * (els.length + 1) * (W + 3) := by
      have := Nat.mul_le_mul_right (W + 3) (show 1000 ≤ loopModK * (els.length + 1) by
        simp only [loopModK]; nlinarith)
      exact this
    have e : 3 * loopModK * (els.length + 1) * (W + 1) =
      loopModK * (els.length + 1) * (2 * W) + loopModK * (els.length + 1) * (W + 3) := by ring
    simp only [List.length_map] at wB ⊢
    omega

end GI.Lang
