module

public import Workspace.Lang.Lib.NatList
public import Workspace.Lang.Lib.Search

@[expose] public section

/-!
# The equality pattern of a tuple, as a program

The tuple coloring relation `tupleRel` treats injective and noninjective tuples apart: two
noninjective tuples are related when they have the same equality pattern. A program decides
both questions from one list, the *first-occurrence pattern* `stPat f`: entry `i` is the first
position `j` with `f j = f i`.

* `stPat_eq_iff`: two tuples have the same pattern exactly when they have the same equality
  pattern (`f i = f j ↔ g i = g j` for all `i, j`).
* `stPat_eq_range_iff`: the pattern is `[0, …, n - 1]` exactly when the tuple is injective.
* `stPat_spec`: the program `stPatFuns` (nine functions) computes the pattern of a list of
  numbers, at cost `stPatK (B + 1)^4` when the entries and the length are at most `B`.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

variable {n : ℕ}

/-! ### The pattern -/

/-- The first position `j` with `f j = f i`. -/
def stFI (f : Fin n → ℕ) (i : Fin n) : ℕ := (List.finRange n).findIdx fun j => decide (f j = f i)

/-- **The first-occurrence pattern** of `f`: the list of `stFI f i`. -/
def stPat (f : Fin n → ℕ) : List ℕ := (List.finRange n).map (stFI f)

theorem stFI_lt (f : Fin n → ℕ) (i : Fin n) : stFI f i < n := by
  have := List.findIdx_lt_length_of_exists (p := fun j => decide (f j = f i))
    (xs := List.finRange n) ⟨i, List.mem_finRange i, by simp⟩
  simpa [stFI] using this

/-- The entry at the first position has the value of `i`. -/
theorem stFI_val (f : Fin n → ℕ) (i : Fin n) : f ⟨stFI f i, stFI_lt f i⟩ = f i := by
  have hlt : stFI f i < (List.finRange n).length := by simpa using stFI_lt f i
  have h := List.findIdx_getElem (p := fun j => decide (f j = f i)) (xs := List.finRange n)
    (w := hlt)
  simp only [decide_eq_true_eq] at h
  have e : (List.finRange n)[stFI f i]'hlt = ⟨stFI f i, stFI_lt f i⟩ := by
    simp [List.getElem_finRange, stFI]
  rw [← e]; exact h

theorem stFI_eq_iff (f : Fin n → ℕ) (i i' : Fin n) : stFI f i = stFI f i' ↔ f i = f i' := by
  constructor
  · intro h
    have h1 := stFI_val f i
    have h2 := stFI_val f i'
    have e : (⟨stFI f i, stFI_lt f i⟩ : Fin n) = ⟨stFI f i', stFI_lt f i'⟩ := Fin.ext h
    rw [e] at h1
    rw [← h1, h2]
  · intro h; unfold stFI; rw [h]

theorem stPat_getElem (f : Fin n → ℕ) (i : Fin n) :
    (stPat f)[(i : ℕ)]? = some (stFI f i) := by
  simp [stPat]

/-- **Same pattern, same equality pattern.** -/
theorem stPat_eq_iff (f g : Fin n → ℕ) : stPat f = stPat g ↔ ∀ i j, f i = f j ↔ g i = g j := by
  constructor
  · intro h i j
    have hp : ∀ i, stFI f i = stFI g i := fun i => by
      have h1 := stPat_getElem f i
      rw [h, stPat_getElem g i] at h1
      exact (Option.some.inj h1).symm
    rw [← stFI_eq_iff f, ← stFI_eq_iff g, hp i, hp j]
  · intro h
    unfold stPat
    refine List.map_congr_left fun i _ => ?_
    unfold stFI
    congr 1
    funext j
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    exact h j i

theorem stPat_val : stPat (fun i : Fin n => (i : ℕ)) = List.range n := by
  have hfi : ∀ i : Fin n, stFI (fun i : Fin n => (i : ℕ)) i = i := by
    intro i
    exact stFI_val (fun i : Fin n => (i : ℕ)) i
  unfold stPat
  rw [List.map_congr_left (fun i _ => hfi i)]
  rw [← List.map_coe_finRange_eq_range]

/-- **The pattern is `[0, …, n - 1]` exactly for injective tuples.** -/
theorem stPat_eq_range_iff (f : Fin n → ℕ) :
    stPat f = List.range n ↔ Function.Injective f := by
  rw [← stPat_val, stPat_eq_iff]
  constructor
  · intro h i j hij
    exact Fin.ext ((h i j).1 hij)
  · intro h i j
    exact ⟨fun hij => congrArg Fin.val (h hij), fun hij => by rw [Fin.ext hij]⟩

theorem stPat_le (f : Fin n → ℕ) : ∀ x ∈ stPat f, x ≤ n := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact (stFI_lt f i).le

theorem stPat_length (f : Fin n → ℕ) : (stPat f).length = n := by simp [stPat]

/-! ### The program -/

/-- The entry of the pattern: map over the list, with the list as context. -/
def stPatEntry (b : ℕ) : Expr := .call (b + 1) (mk2 (.var 0) (.var 0))

/-- **The pattern**, at base `b` (nine functions): on `natList l`, `natList` of the pattern. -/
def stPatFuns (b : ℕ) : List Expr :=
  [stPatEntry b] ++ mapFuns (b + 1) (b + 4) ++ [invF (b + 5)] ++ findEqFuns (b + 5)

/-- The cost constant of the pattern. -/
def stPatK : ℕ := 10 ^ 7

/-- The list of the values of `f`. -/
def stL (f : Fin n → ℕ) : List ℕ := (List.finRange n).map f

theorem stL_findIdx (f : Fin n → ℕ) (i : Fin n) :
    (stL f).findIdx (fun x => decide (x = f i)) = stFI f i := by
  rw [stL, List.findIdx_map]; rfl

theorem stL_le {f : Fin n → ℕ} {B : ℕ} (hB : ∀ i, f i ≤ B) : ∀ x ∈ stL f, x ≤ B := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact hB i

/-- **The pattern program.** -/
theorem stPat_spec {P : Program} {b : ℕ} (h : P.HasAt b (stPatFuns b)) (f : Fin n → ℕ) {B : ℕ}
    (hB : ∀ i, f i ≤ B) (hn : n ≤ B) :
    FunDet P b (natList (stL f)) (natList (stPat f)) (stPatK * (B + 1) ^ 4) := by
  simp only [stPatFuns] at h
  have hentry : P.funs[b]? = some (stPatEntry b) := h.left.left.left.single
  have hmap : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := by
    simpa using h.left.left.right
  have hinvF : P.funs[b + 4]? = some (invF (b + 5)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.left.right.single
  have hfe : P.HasAt (b + 5) (findEqFuns (b + 5)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.right
  have hL := stL_le hB
  have hlen : (stL f).length ≤ B := by simp [stL, hn]
  have hwL : (natList (stL f)).wt ≤ 5 * (B + 1) ^ 2 := wt_natList_le_sq hL hlen
  have hwP : (natList (stPat f)).wt ≤ 5 * (B + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => (stPat_le f x hx).trans hn) (by rw [stPat_length]; exact hn)
  -- the function of the map
  have hG : ∀ x ∈ (stL f).map Val.nat,
      FunAll P (b + 4) (.list [natList (stL f), x]) (fun w cost =>
        (∀ i : Fin n, x = .nat (f i) → w = .nat (stFI f i)) ∧
          cost ≤ (findEqK + 1000) * (B + 1) ^ 3) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hyB := hL y hy
    have hfd := findEq_spec hfe (xs := stL f) (j := y) hL hyB hlen
    refine FunAll.intro hinvF ((Det.call (Det.mk2 (Det.arg' (rest := []) (j := 1) rfl)
      (Det.arg' (j := 0) rfl)) hfd).post fun cost hc => ⟨fun i hi => ?_, ?_⟩)
    · simp only [Val.nat.injEq] at hi
      rw [hi, stL_findIdx]
    · have h1 := wt_list2_le (.nat y) (natList (stL f))
      have h2 := wt_list2_le (natList (stL f)) (.nat y)
      have h3 := wt_nat_le y
      have h4 := wt_nat_le ((stL f).findIdx fun x => decide (x = y))
      have h5 : (stL f).findIdx (fun x => decide (x = y)) ≤ B :=
        List.findIdx_le_length.trans hlen
      have h6 : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have h7 : B + 1 ≤ (B + 1) ^ 2 := Nat.le_self_pow (by omega) _
      have e : (findEqK + 1000) * (B + 1) ^ 3 = findEqK * (B + 1) ^ 3 + 1000 * (B + 1) ^ 3 := by
        ring
      rw [e]
      have e2 : (Val.list [Val.nat y, natList (stL f)]).wt =
        (Val.list [Val.nat y, natList (stL f)]).wt := rfl
      omega
  have hM := map_spec hmap (c := natList (stL f)) (xs := (stL f).map Val.nat) hG
  have hnat : natList (stL f) = .list ((stL f).map Val.nat) := rfl
  refine FunDet.intro hentry ?_
  refine (Det.call (Det.mk2 (Det.var' (i := 0) (v := natList (stL f)) rfl)
    (Det.var' (i := 0) (v := natList (stL f)) rfl)) (w := natList (stPat f))
    (cb := 5000000 * (B + 1) ^ 4) ?_).mono ?_
  · refine FunAll.mono hM fun w cost hw => ?_
    obtain ⟨ws, rfl, hws, hc⟩ := hw
    have hws' : ws = (List.finRange n).map fun i => Val.nat (stFI f i) := by
      have : (stL f).map Val.nat = (List.finRange n).map fun i => Val.nat (f i) := by
        simp [stL, List.map_map, Function.comp_def]
      rw [this] at hws
      exact forall₂_map_eq (fun i _ w hw => hw i rfl) hws
    have hw : Val.list ws = natList (stPat f) := by
      rw [hws']; simp [natList, stPat, List.map_map, Function.comp_def]
    refine ⟨hw, ?_⟩
    rw [hw] at hc
    simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
    have e1 : (Val.list [natList (stL f), .list ((stL f).map Val.nat)]).wt =
      (Val.list [natList (stL f), natList (stL f)]).wt := rfl
    rw [e1] at hc
    have h2 := wt_list2_le (natList (stL f)) (natList (stL f))
    have h3 : (stL f).length * ((findEqK + 1000) * (B + 1) ^ 3) ≤
        (findEqK + 1000) * (B + 1) ^ 4 := by
      have := Nat.mul_le_mul_right ((findEqK + 1000) * (B + 1) ^ 3) (show (stL f).length ≤ B + 1
        by omega)
      calc _ ≤ (B + 1) * ((findEqK + 1000) * (B + 1) ^ 3) := this
        _ = _ := by ring
    have hX : (B + 1) ^ 4 = (B + 1) * (B + 1) ^ 3 := by ring
    have hX3 : (B + 1) ^ 3 = (B + 1) * (B + 1) ^ 2 := by ring
    have hlen1 : (stL f).length + 1 ≤ B + 1 := Nat.add_le_add_right hlen 1
    clear hG hM hnat hws hws' hw e1 h hentry hmap hinvF hfe
    have h10 : 1 ≤ (B + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    generalize (Val.list [natList (stL f), natList (stL f)]).wt = A at *
    generalize (natList (stPat f)).wt = O at *
    generalize (natList (stL f)).wt = I at *
    generalize (stL f).length = l at *
    generalize (B + 1) ^ 2 = X2 at *
    generalize (B + 1) ^ 3 = X3 at *
    generalize (B + 1) ^ 4 = X4 at *
    have h4 : mapK * (l + 1) * (A + O + 1) ≤ mapK * (B + 1) * (35 * X2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left mapK hlen1) (by clear hc h3; omega)
    have h5 : mapK * (B + 1) * (35 * X2) = 35 * mapK * X3 := by rw [hX3]; ring
    have h5' : X3 ≤ X4 := by
      rw [hX]; exact Nat.le_mul_of_pos_left _ (by omega)
    have h6 : (findEqK + 1000) * X4 + 35 * mapK * X4 ≤ 5000000 * X4 := by
      have : (findEqK + 1000) * X4 + 35 * mapK * X4 = (findEqK + 1000 + 35 * mapK) * X4 := by
        ring
      rw [this]
      exact Nat.mul_le_mul_right _ (by norm_num [findEqK, mapK])
    have h7 : 35 * mapK * X3 ≤ 35 * mapK * X4 := Nat.mul_le_mul_left (35 * mapK) h5'
    generalize findEqK = F at *
    generalize mapK = Mk at *
    omega
  · have h2 := wt_list2_le (natList (stL f)) (natList (stL f))
    have h7 : (B + 1) ^ 2 ≤ (B + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h9 : stPatK * (B + 1) ^ 4 = 10000000 * (B + 1) ^ 4 := by norm_num [stPatK]
    have h10 : 1 ≤ (B + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    generalize (Val.list [natList (stL f), natList (stL f)]).wt = A at *
    generalize (natList (stPat f)).wt = O at *
    generalize (natList (stL f)).wt = I at *
    generalize (B + 1) ^ 2 = X2 at *
    generalize (B + 1) ^ 4 = X4 at *
    omega

end GI.Impl
