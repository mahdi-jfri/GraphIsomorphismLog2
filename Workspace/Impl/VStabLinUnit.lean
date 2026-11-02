import Workspace.Impl.VStabLinAll

/-!
# Unit tags

To compute kernels and coordinates we insert the pairs `(v_i, e_i)`, where `e_i` is the unit
vector of length `m`. This file builds them.

* `vsUnit m i`: the unit list of length `m` with `1` at `i`; program `vsUnitFuns`, `vsUnit_spec`.
* `vsUnitPairs m vs`: the pairs `(vs[i], vsUnit m i)`; program `vsUnitPairsFuns`,
  `vsUnitPairs_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- The unit list of length `m` with `1` at `i`. -/
def vsUnit (m i : ℕ) : List ℕ := (List.range m).map fun j => if j = i then 1 else 0

theorem vsUnit_length (m i : ℕ) : (vsUnit m i).length = m := by simp [vsUnit]

theorem vsUnit_le_one (m i : ℕ) : ∀ y ∈ vsUnit m i, y ≤ 1 := by
  intro y hy
  simp only [vsUnit, List.mem_map] at hy
  obtain ⟨j, -, rfl⟩ := hy
  split_ifs <;> omega

/-- The unit list, at base `b`, on `[m, i]` (3 functions). -/
def vsUnitFuns (b : ℕ) : List Expr :=
  loopFuns b (.get (.var 0) (.nat 0)) .nil (.snoc (arg 2) (.arith .eq (arg 1) (.get (arg 0) (.nat 1))))

theorem wt_vsUnit_le (m i : ℕ) : (natList (vsUnit m i)).wt ≤ 5 * (m + 2) ^ 2 := by
  have := wt_natList_le_sq (B := m + 1) (fun y hy => (vsUnit_le_one m i y hy).trans (by omega))
    (by rw [vsUnit_length]; omega)
  exact this

/-- **The unit list.** -/
theorem vsUnit_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsUnitFuns b)) (m i : ℕ) :
    FunAll P b (.list [.nat m, .nat i]) (fun w cost => w = natList (vsUnit m i) ∧
      cost ≤ loopModK * (m + 1) * ((Val.list [.nat m, .nat i]).wt + m + w.wt + 1)) := by
  set a := Val.list [.nat m, .nat i]
  have ha' : (Val.list [.nat m, .nat i]).wt = a.wt := rfl
  have hk : Det P [a] (.get (.var 0) (.nat 0)) (.nat m) _ := Det.get' (Det.var' rfl) (Det.nat 0) rfl
  have hma : (Val.nat m).wt < a.wt := wt_le_wt_list (by simp)
  have hia : (Val.nat i).wt < a.wt := wt_le_wt_list (by simp)
  refine (loopMono_spec h hk Det.nil (by have := wt_nat_le m; omega) (by simp)
    (Inv := fun j acc => acc = natList ((List.range j).map fun j' => if j' = i then 1 else 0))
    (by simp [natList]) (D := fun _ => 0) ?_).mono ?_
  · rintro j acc hj rfl
    have hv : [a, Val.nat j, natList ((List.range j).map fun j' => if j' = i then 1 else 0)][2]? =
        some (Val.list (((List.range j).map fun j' => if j' = i then 1 else 0).map Val.nat)) := rfl
    refine (Det.snoc (Det.arg' (rest := []) (j := 2) hv)
      (Det.arith (op := .eq) (Det.arg' (rest := []) (vs := [a, .nat j, _]) (j := 1) rfl)
        (Det.get' (Det.arg' (rest := []) (vs := [a, .nat j, _]) (j := 0) rfl)
        (Det.nat 1) (show [Val.nat m, .nat i][1]? = some (.nat i) from rfl)))).post fun c hc => ?_
    have hr : (List.map Val.nat (List.map (fun j' => if j' = i then 1 else 0) (List.range (j + 1)))) =
        List.map Val.nat (List.map (fun j' => if j' = i then 1 else 0) (List.range j)) ++
          [Val.nat (BinOp.eval .eq j i)] := by
      simp [List.range_succ, BinOp.eval_eq]
    refine ⟨by beta_reduce; simp only [natList]; rw [hr], ?_, ?_⟩
    · exact wt_list_mono (List.prefix_append _ _)
    · have := wt_stepArg_le a j (natList ((List.range j).map fun j' => if j' = i then 1 else 0))
      have h1 := wt_list_mono (List.prefix_append
        (List.map Val.nat (List.map (fun j' => if j' = i then 1 else 0) (List.range j)))
        [Val.nat (BinOp.eval .eq j i)])
      have h2 := wt_le_wt_list (vs := List.map Val.nat (List.map (fun j' => if j' = i then 1 else 0)
        (List.range j)) ++ [Val.nat (BinOp.eval .eq j i)]) (v := Val.nat (BinOp.eval .eq j i))
        (by simp)
      have e : (natList ((List.range j).map fun j' => if j' = i then 1 else 0)).wt =
        (Val.list (((List.range j).map fun j' => if j' = i then 1 else 0).map Val.nat)).wt := rfl
      omega
  · rintro w cost ⟨hw, hc⟩
    refine ⟨hw.trans rfl, ?_⟩
    simpa using hc

/-- The unit-tag pairs `(vs[i], e_i)`, with tags of length `m`. -/
def vsUnitPairs (m : ℕ) (vs : List (List ℕ)) : List (List ℕ × List ℕ) :=
  (List.range vs.length).map fun i => (vs.getD i [], vsUnit m i)

/-- The step of the pair builder, on `[[m, vs], i, acc]`. -/
def vsUnitPairsStep (unit : ℕ) : Expr :=
  .snoc (arg 2) (mk2 (.get (.get (arg 0) (.nat 1)) (arg 1))
    (.call unit (mk2 (.get (arg 0) (.nat 0)) (arg 1))))

/-- The pair builder, at base `b`, on `[m, vs]` (6 functions). -/
def vsUnitPairsFuns (b : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 1))) .nil (vsUnitPairsStep (b + 3)) ++ vsUnitFuns (b + 3)

theorem vsUnitPairsFuns_length (b : ℕ) : (vsUnitPairsFuns b).length = 6 := rfl

theorem vsUnitPairs_cost {m i a u : ℕ} (hu : u ≤ 5 * (m + 2) ^ 2) (ha : m + i ≤ a) {c : ℕ}
    (hc : c ≤ loopModK * (m + 1) * (2 * (m + 2 + (i + 2)) + 6 + m + u + 1)) :
    c ≤ 10 ^ 5 * (a + 2) ^ 3 := by
  have hK : loopModK = 1000 := rfl
  rw [hK] at hc
  have h1 : 2 * (m + 2 + (i + 2)) + 6 + m + u + 1 ≤ 20 * (a + 2) ^ 2 := by nlinarith
  have h2 : 1000 * (m + 1) * (2 * (m + 2 + (i + 2)) + 6 + m + u + 1) ≤
      1000 * (a + 2) * (20 * (a + 2) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) h1
  have e : 1000 * (a + 2) * (20 * (a + 2) ^ 2) = 20000 * (a + 2) ^ 3 := by ring
  omega

/-- **The unit-tag pairs.** On `[m, vs]`, the list of pair values of `vsUnitPairs m vs`. -/
theorem vsUnitPairs_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsUnitPairsFuns b)) (m : ℕ)
    (vs : List (List ℕ)) :
    FunAll P b (.list [.nat m, .list (vs.map natList)]) (fun w cost =>
      w = .list ((vsUnitPairs m vs).map vsPairVal) ∧
      cost ≤ vs.length * (10 ^ 5 * ((Val.list [.nat m, .list (vs.map natList)]).wt + m + 2) ^ 3 +
          1000) + loopModK * (vs.length + 1) *
        ((Val.list [.nat m, .list (vs.map natList)]).wt + vs.length + w.wt + 1)) := by
  have hl : P.HasAt b (loopFuns b (.length (.get (.var 0) (.nat 1))) .nil (vsUnitPairsStep (b + 3))) :=
    h.block 0 rfl
  have hu : P.HasAt (b + 3) (vsUnitFuns (b + 3)) := h.block 3 rfl
  set a := Val.list [.nat m, .list (vs.map natList)]
  have hk := Det.length (Det.get' (P := P) (env := [a]) (Det.var' (i := 0) rfl) (Det.nat 1)
      (show [Val.nat m, .list (vs.map natList)][1]? = some (.list (vs.map natList)) from rfl))
  rw [List.length_map] at hk
  have ha' : (Val.list [.nat m, .list (vs.map natList)]).wt = a.wt := rfl
  have hma : (Val.nat m).wt < a.wt := wt_le_wt_list (by simp)
  have hva : (Val.list (vs.map natList)).wt < a.wt := wt_le_wt_list (by simp)
  have hnv := length_lt_wt_list (vs.map natList)
  rw [List.length_map] at hnv
  have hm := wt_nat_le m
  refine (loopMono_spec hl hk Det.nil (by omega) (by simp)
    (Inv := fun j acc => acc = .list (((List.range j).map fun i => (vs.getD i [], vsUnit m i)).map
      vsPairVal))
    (by simp) (D := fun _ => 10 ^ 5 * (a.wt + m + 2) ^ 3 + 1000) ?_).mono ?_
  · rintro i acc hi rfl
    set A := Val.list (((List.range i).map fun i => (vs.getD i [], vsUnit m i)).map vsPairVal)
    have env := (rfl : [a, Val.nat i, A] = [a, Val.nat i, A])
    have d0 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, A]) (j := 0) rfl
    have d1 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, A]) (j := 1) rfl
    have d2 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, A]) (j := 2) rfl
    have hvi : (vs.map natList)[i]? = some (natList (vs.getD i [])) := by
      rw [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    have dv := Det.get' (Det.get' d0 (Det.nat 1)
      (show [Val.nat m, .list (vs.map natList)][1]? = some (.list (vs.map natList)) from rfl)) d1 hvi
    have dm := Det.get' d0 (Det.nat 0)
      (show [Val.nat m, .list (vs.map natList)][0]? = some (.nat m) from rfl)
    have du := Det.call (Det.mk2 dm d1) ((vsUnit_spec hu m i).mono fun w c hw => ⟨hw.1, by
      have := hw.2; rw [hw.1] at this; exact this⟩)
    refine (Det.snoc d2 (Det.mk2 dv du)).post fun c hc => ?_
    have hr : ((List.range (i + 1)).map fun i => (vs.getD i [], vsUnit m i)).map vsPairVal =
        ((List.range i).map fun i => (vs.getD i [], vsUnit m i)).map vsPairVal ++
          [Val.list [natList (vs.getD i []), natList (vsUnit m i)]] := by
      simp [List.range_succ, vsPairVal]
    refine ⟨by beta_reduce; rw [hr], ?_, ?_⟩
    · exact wt_list_mono (List.prefix_append _ _)
    · have wU := wt_vsUnit_le m i
      have wsa := wt_stepArg_le a i A
      have h1 := wt_list_mono (List.prefix_append
        (((List.range i).map fun i => (vs.getD i [], vsUnit m i)).map vsPairVal)
        [Val.list [natList (vs.getD i []), natList (vsUnit m i)]])
      have h2 := wt_le_wt_list (vs := ((List.range i).map fun i => (vs.getD i [], vsUnit m i)).map
        vsPairVal ++ [Val.list [natList (vs.getD i []), natList (vsUnit m i)]])
        (v := Val.list [natList (vs.getD i []), natList (vsUnit m i)]) (by simp)
      have h3 := wt_le_wt_list (vs := [natList (vs.getD i []), natList (vsUnit m i)])
        (v := natList (vs.getD i [])) (by simp)
      have h4 := wt_le_wt_list (vs := [natList (vs.getD i []), natList (vsUnit m i)])
        (v := natList (vsUnit m i)) (by simp)
      have hvw : (natList (vs.getD i [])).wt < (Val.list (vs.map natList)).wt := by
        have := wt_getElem_lt (vs.map natList) i (by rw [List.length_map]; exact hi)
        rwa [List.getElem_map, ← List.getD_eq_getElem (d := [])] at this
      have wi := wt_nat_le i
      have w2 := wt_list2_le (.nat m) (.nat i)
      have hcu := vsUnitPairs_cost (c := loopModK * (m + 1) * ((Val.list [.nat m, .nat i]).wt + m +
        (natList (vsUnit m i)).wt + 1)) (a := a.wt + m) wU (by omega)
        (Nat.mul_le_mul_left (loopModK * (m + 1))
            (show (Val.list [.nat m, .nat i]).wt + m + (natList (vsUnit m i)).wt + 1 ≤
              2 * (m + 2 + (i + 2)) + 6 + m + (natList (vsUnit m i)).wt + 1 by omega))
      have hA : (Val.list [Val.nat m, Val.nat i]).wt ≤ 2 * (m + 2 + (i + 2)) + 6 := by omega
      have eA : A.wt = (Val.list (((List.range i).map fun i => (vs.getD i [], vsUnit m i)).map
        vsPairVal)).wt := rfl
      beta_reduce
      omega
  · rintro w cost ⟨hw, hc⟩
    refine ⟨hw.trans rfl, ?_⟩
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    exact hc

end GI.Impl
