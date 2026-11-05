module

public import Workspace.Lang.Lib.NatList

@[expose] public section

/-!
# Positions in a list of numbers

`camIdxFuns b` (eight functions): on `[natList O, natList vs]`, the list of the positions in `O`
of the entries of `vs` (`O.findIdx (· = v)` for each `v`). It is the outer map of the library's
`inverse` (`invF` with `findEq`), for a list `O` that need not be a permutation. The program uses
it twice: to restrict a permutation to an orbit `O`, and to find, for each point, the orbit point
with the same label.
-/

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

/-- `camIdx`, at base `b` (eight functions). -/
def camIdxFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [invF (b + 4)] ++ findEqFuns (b + 4)

def camIdxK : ℕ := 10 ^ 7

theorem length_natList_lt (xs : List ℕ) : xs.length < (natList xs).wt := by
  have := length_lt_wt_list (xs.map Val.nat)
  simpa [natList] using this

/-- **Positions in a list.** Entries and lengths are at most `B`. -/
theorem camIdx_spec {P : Program} {b : ℕ} (h : P.HasAt b (camIdxFuns b)) {O vs : List ℕ} {B : ℕ}
    (hO : ∀ x ∈ O, x ≤ B) (hv : ∀ v ∈ vs, v ≤ B) (hl : O.length ≤ B) (hvl : vs.length ≤ B) :
    FunDet P b (.list [natList O, natList vs])
      (natList (vs.map fun v => O.findIdx fun x => decide (x = v))) (camIdxK * (B + 1) ^ 4) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left.left
  have hinv : P.funs[b + 3]? = some (invF (b + 4)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.left.right.single
  have hfind : P.HasAt (b + 4) (findEqFuns (b + 4)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.right
  have hwO := wt_natList_le_sq hO hl
  have hB1 : B + 1 ≤ (B + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hB2 : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hB3 : (B + 1) ^ 3 ≤ (B + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hG : ∀ x ∈ vs.map Val.nat, FunAll P (b + 3) (.list [natList O, x]) (fun w cost =>
      (∀ v : ℕ, x = .nat v → w = .nat (O.findIdx fun y => decide (y = v))) ∧
        cost ≤ findEqK * (B + 1) ^ 3 + 200 * (B + 1) ^ 2) := by
    intro x hx
    obtain ⟨v, hvv, rfl⟩ := List.mem_map.mp hx
    have hvB := hv v hvv
    refine FunAll.intro hinv ((Det.call (Det.mk2 (Det.arg' (rest := []) (j := 1) rfl)
      (Det.arg' (j := 0) rfl)) (findEq_spec hfind hO hvB hl)).post fun cost hc =>
        ⟨fun v' hv' => by cases hv'; rfl, ?_⟩)
    have h1 := wt_list2_le (natList O) (.nat v)
    have h2 := wt_list2_le (.nat v) (natList O)
    have h3 := wt_nat_le v
    have h4 := wt_nat_le (O.findIdx fun y => decide (y = v))
    have h5 : O.findIdx (fun y => decide (y = v)) ≤ B :=
      List.findIdx_le_length.trans hl
    have h6 : 1 ≤ (B + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  refine (map_spec hmap (c := natList O) (xs := vs.map Val.nat) hG).mono fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' := forall₂_map_eq (g := fun v => Val.nat (O.findIdx fun y => decide (y = v)))
    (fun a _ w hw => hw a rfl) hws
  subst hws'
  have e : Val.list (vs.map fun v => Val.nat (O.findIdx fun y => decide (y = v))) =
      natList (vs.map fun v => O.findIdx fun x => decide (x = v)) := by
    simp [natList, List.map_map, Function.comp_def]
  refine ⟨e, ?_⟩
  rw [e] at hc
  have hwr := wt_natList_le_sq (xs := vs.map fun v => O.findIdx fun x => decide (x = v)) (B := B)
    (by
      intro y hy
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hy
      exact List.findIdx_le_length.trans hl) (by simpa using hvl)
  have hwv := wt_natList_le_sq hv hvl
  have ha := wt_list2_le (natList O) (natList vs)
  have ha' : (Val.list [natList O, .list (vs.map Val.nat)]).wt ≤
      2 * ((natList O).wt + (natList vs).wt) + 6 := ha
  have hsum : ((vs.map Val.nat).map fun _ => findEqK * (B + 1) ^ 3 + 200 * (B + 1) ^ 2).sum =
      vs.length * (findEqK * (B + 1) ^ 3 + 200 * (B + 1) ^ 2) := by
    simp [List.map_map, Function.comp_def, List.map_const', List.sum_replicate]
  have e2 : (Val.list [natList O, .list (vs.map Val.nat)]).wt =
      (Val.list [natList O, natList vs]).wt := rfl
  rw [hsum, e2] at hc
  simp only [List.length_map] at hc
  have k1 : vs.length * (findEqK * (B + 1) ^ 3 + 200 * (B + 1) ^ 2) ≤
      (B + 1) * ((findEqK + 200) * (B + 1) ^ 3) :=
    Nat.mul_le_mul (by omega) (by rw [Nat.add_mul]; omega)
  have k2 : mapK * (vs.length + 1) *
      ((Val.list [natList O, natList vs]).wt + (natList (vs.map fun v => O.findIdx fun x =>
        decide (x = v))).wt + 1) ≤ mapK * (B + 1) * (40 * (B + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have k3 : (B + 1) * ((findEqK + 200) * (B + 1) ^ 3) = (findEqK + 200) * (B + 1) ^ 4 := by ring
  have k4 : mapK * (B + 1) * (40 * (B + 1) ^ 2) = 40 * mapK * (B + 1) ^ 3 := by ring
  rw [k3] at k1
  rw [k4] at k2
  simp only [camIdxK, findEqK, mapK] at *
  omega

end GI.Lang
