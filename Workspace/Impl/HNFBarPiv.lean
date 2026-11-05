module

public import Workspace.Impl.HNFTab
public import Workspace.Impl.HNFLoop

@[expose] public section

/-!
# The pivot search of Bareiss elimination, as a program

Step `k` of Bareiss elimination (`GI.Proved.hnfBarStep`) takes the first row `p` with
`W p k ≠ 0`. The program scans the rows in order and keeps a code: `0` while no row is found,
then `p + 1`. This file relates the code to `GI.Proved.hnfPivot` and gives the program.
-/

namespace GI.Impl

open GI.Cited GI.Lang
open GI.Proved (hnfPivot)

variable {r c : ℕ}

/-! ### The code of the pivot search -/

/-- The code after scanning the first `i` rows: `0` if none of them has a nonzero entry in
column `k`, else `p + 1` for the first such row `p`. -/
def hnfPivCode (W : Matrix (Fin r) (Fin c) ℤ) (k : Fin c) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if hnfPivCode W k i ≠ 0 then hnfPivCode W k i
      else if h : i < r then (if W ⟨i, h⟩ k ≠ 0 then i + 1 else 0) else 0

theorem hnfPivCode_spec (W : Matrix (Fin r) (Fin c) ℤ) (k : Fin c) : ∀ i,
    (hnfPivCode W k i = 0 → ∀ i' : Fin r, (i' : ℕ) < i → W i' k = 0) ∧
    (∀ p, hnfPivCode W k i = p + 1 →
      ∃ hp : p < r, W ⟨p, hp⟩ k ≠ 0 ∧ ∀ i' : Fin r, (i' : ℕ) < p → W i' k = 0) := by
  intro i
  induction i with
  | zero => exact ⟨fun _ i' h => absurd h (Nat.not_lt_zero _), fun p h => by simp [hnfPivCode] at h⟩
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    by_cases h0 : hnfPivCode W k i = 0
    · by_cases hi : i < r
      · by_cases hw : W ⟨i, hi⟩ k = 0
        · have e : hnfPivCode W k (i + 1) = 0 := by simp [hnfPivCode, h0, hi, hw]
          refine ⟨fun _ i' hi' => ?_, fun p hp => by omega⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | h
          · exact ih1 h0 i' h
          · rw [show i' = ⟨i, hi⟩ from Fin.ext h]; exact hw
        · have e : hnfPivCode W k (i + 1) = i + 1 := by simp [hnfPivCode, h0, hi, hw]
          refine ⟨fun h => by omega, fun p hp => ?_⟩
          rw [e] at hp
          obtain rfl : p = i := by omega
          exact ⟨hi, hw, fun i' h' => ih1 h0 i' h'⟩
      · have e : hnfPivCode W k (i + 1) = 0 := by simp [hnfPivCode, h0, hi]
        refine ⟨fun _ i' hi' => ih1 h0 i' (by have := i'.isLt; omega), fun p hp => by omega⟩
    · have e : hnfPivCode W k (i + 1) = hnfPivCode W k i := by simp [hnfPivCode, h0]
      rw [e]
      exact ⟨fun h => absurd h h0, ih2⟩

theorem hnfPivot_of_code_zero (W : Matrix (Fin r) (Fin c) ℤ) (k : Fin c)
    (h : hnfPivCode W k r = 0) : hnfPivot W k = none := by
  unfold hnfPivot
  rw [List.find?_eq_none]
  intro x _
  simpa using (hnfPivCode_spec W k r).1 h x x.isLt

theorem hnfPivot_of_code_succ (W : Matrix (Fin r) (Fin c) ℤ) (k : Fin c) {p : ℕ}
    (h : hnfPivCode W k r = p + 1) : ∃ hp : p < r, hnfPivot W k = some ⟨p, hp⟩ := by
  obtain ⟨hp, hne, hlow⟩ := (hnfPivCode_spec W k r).2 p h
  refine ⟨hp, ?_⟩
  unfold hnfPivot
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simpa using hne, p, by simpa using hp, by simp, fun j hj => ?_⟩
  have := hlow ⟨j, by omega⟩ hj
  simpa using this

/-! ### The program -/

/-- One step of the scan, on `[[W, k, r], i, code]`. -/
def hnfPivStepF : Expr :=
  .ite (arg 2) (arg 2)
    (.ite (.length (.get (.get (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))
      (.nat 1))) (.arith .add (arg 1) (.nat 1)) (.nat 0))

def hnfPivKE : Expr := .get (.var 0) (.nat 2)

def hnfPivFuns (b : ℕ) : List Expr := loopFuns b hnfPivKE (.nat 0) hnfPivStepF

theorem hnf_encInt_bits_length (z : ℤ) :
    ((Nat.bits z.natAbs).map fun b => Val.nat (if b then 1 else 0)).length = 0 ↔ z = 0 := by
  rw [List.length_map, Nat.size_eq_bits_len, Nat.size_eq_zero, Int.natAbs_eq_zero]

theorem hnf_mat_get (W : Matrix (Fin r) (Fin c) ℤ) (i : Fin r) :
    ((List.finRange r).map fun i => Val.list ((List.finRange c).map fun j => encInt (W i j)))[(i : ℕ)]?
      = some (linVecVal (W i)) := by
  simp [linVecVal]

theorem hnf_row_wt_lt (W : Matrix (Fin r) (Fin c) ℤ) (i : Fin r) :
    (linVecVal (W i)).wt < (encIntMatrix W).wt :=
  wt_le_wt_list (List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩)

def hnfPivCost (Y : ℕ) : ℕ := Y * (100 * (Y + 10)) + 1000 * (Y + 1) * (2 * Y + 10)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- **The pivot search.** -/
theorem hnfPiv_spec {P : Program} {b : ℕ} (h : P.HasAt b (hnfPivFuns b))
    (W : Matrix (Fin r) (Fin c) ℤ) (k : Fin c) {Y : ℕ}
    (hY : (Val.list [encIntMatrix W, .nat k, .nat r]).wt + r ≤ Y) :
    FunDet P b (.list [encIntMatrix W, .nat k, .nat r]) (.nat (hnfPivCode W k r)) (hnfPivCost Y) := by
  set a := Val.list [encIntMatrix W, .nat k, .nat r] with ha
  have hk : Det P [a] hnfPivKE (.nat r) _ :=
    Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 2)
      (show [encIntMatrix W, .nat k, .nat r][2]? = some (.nat r) from rfl)
  have hcode_le : ∀ i, hnfPivCode W k i ≤ i := by
    intro i
    induction i with
    | zero => simp [hnfPivCode]
    | succ i ih => unfold hnfPivCode; split_ifs <;> omega
  have hl := loopBdd_spec h hk (Det.nat 0) (M := r + 3)
    (Inv := fun i acc => acc = .nat (hnfPivCode W k i)) (D := fun _ => 100 * (Y + 10))
    (by
      have w1 := wt_nat_le r
      have w2 : (Val.nat r).wt < a.wt := wt_le_wt_list (by simp [ha])
      have e2 : (Val.nat 2).wt = 4 := rfl
      have e : (Val.list [encIntMatrix W, .nat k, .nat r]).wt = a.wt := rfl
      omega)
    rfl
    (fun i acc hi hacc => by
      subst hacc
      have := wt_nat_le (hnfPivCode W k i)
      have := hcode_le i
      omega)
    (by
      intro i acc hi hacc
      subst hacc
      set vs := [a, Val.nat i, .nat (hnfPivCode W k i)] with hvs
      have d2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
      have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
      have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
      have dW := Det.get' d0 (Det.nat 0)
        (show [encIntMatrix W, .nat k, .nat r][0]? = some (encIntMatrix W) from rfl)
      have dk := Det.get' d0 (Det.nat 1)
        (show [encIntMatrix W, .nat k, .nat r][1]? = some (.nat k) from rfl)
      have drow := Det.get' dW d1 (hnf_mat_get W ⟨i, hi⟩)
      have dent := Det.get' drow dk (hnf_vec_get (W ⟨i, hi⟩) k)
      have dbits := Det.length (Det.get' dent (Det.nat 1)
        (show [Val.nat (if W ⟨i, hi⟩ k < 0 then 1 else 0),
          .list ((Nat.bits (W ⟨i, hi⟩ k).natAbs).map fun b => Val.nat (if b then 1 else 0))][1]? =
          some (.list ((Nat.bits (W ⟨i, hi⟩ k).natAbs).map fun b => Val.nat (if b then 1 else 0)))
          from rfl))
      have dadd := Det.arith' (op := .add) (z := i + 1) d1 (Det.nat (P := P) (env := [Val.list vs]) 1) rfl
      have dinner := Det.ite' dbits dadd (Det.nat (P := P) (env := [Val.list vs]) 0)
      have dout := Det.ite' d2 d2 dinner
      have hv : (if hnfPivCode W k i = 0 then
          (if ((Nat.bits (W ⟨i, hi⟩ k).natAbs).map fun b => Val.nat (if b then 1 else 0)).length = 0
            then Val.nat 0 else Val.nat (i + 1))
          else Val.nat (hnfPivCode W k i)) = Val.nat (hnfPivCode W k (i + 1)) := by
        by_cases h0 : hnfPivCode W k i = 0
        · by_cases hw : W ⟨i, hi⟩ k = 0
          · have := (hnf_encInt_bits_length (W ⟨i, hi⟩ k)).mpr hw
            simp [h0, this, hnfPivCode, hi, hw]
          · have : ¬ ((Nat.bits (W ⟨i, hi⟩ k).natAbs).map
                fun b => Val.nat (if b then 1 else 0)).length = 0 :=
              fun e => hw ((hnf_encInt_bits_length _).mp e)
            simp only [h0, if_true, this, if_false]
            simp [hnfPivCode, h0, hi, hw]
        · simp [h0, hnfPivCode]
      rw [hv] at dout
      refine dout.post fun cst hc => ⟨rfl, hc.trans ?_⟩
      -- weights
      have hc1 := hcode_le i
      have hc2 := hcode_le (i + 1)
      have w0 := wt_nat_le (hnfPivCode W k i)
      have w0' := wt_nat_le (hnfPivCode W k (i + 1))
      have wi := wt_nat_le i
      have wi1 := wt_nat_le (i + 1)
      have wvs := wt_list3_le a (.nat i) (.nat (hnfPivCode W k i))
      have e3 : (Val.list vs).wt = (Val.list [a, .nat i, .nat (hnfPivCode W k i)]).wt := rfl
      have wW : (encIntMatrix W).wt < a.wt := wt_le_wt_list (by simp [ha])
      have wk : (Val.nat k).wt < a.wt := wt_le_wt_list (by simp [ha])
      have wrow := hnf_row_wt_lt W ⟨i, hi⟩
      have went := linVecEntryWt (W ⟨i, hi⟩) k
      have wbits : (Val.list ((Nat.bits (W ⟨i, hi⟩ k).natAbs).map
          fun b => Val.nat (if b then 1 else 0))).wt < (encInt (W ⟨i, hi⟩ k)).wt :=
        wt_le_wt_list (by simp [encInt])
      have hlen := length_lt_wt_list ((Nat.bits (W ⟨i, hi⟩ k).natAbs).map
          fun b => Val.nat (if b then 1 else 0))
      have e0 : (Val.nat 0).wt = 2 := rfl
      have e1 : (Val.nat 1).wt = 3 := rfl
      have e2 : (Val.nat 2).wt = 4 := rfl
      have hsize : (encInt (W ⟨i, hi⟩ k)).wt ≤ (linVecVal (W ⟨i, hi⟩)).wt := went.le
      rw [max_def, max_def, max_def, max_def]
      split_ifs <;> omega)
  apply hl.mono
  intro w cst hw
  refine ⟨hw.1, hw.2.trans ?_⟩
  have h0 : ∑ i ∈ Finset.range r, (fun _ => 100 * (Y + 10)) i = r * (100 * (Y + 10)) := by simp
  rw [h0]
  have h1 : r * (100 * (Y + 10)) ≤ Y * (100 * (Y + 10)) := Nat.mul_le_mul_right _ (by omega)
  have h2 : loopModK * (r + 1) * (a.wt + r + (r + 3) + 1) ≤ 1000 * (Y + 1) * (2 * Y + 10) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  unfold hnfPivCost
  omega

end GI.Impl
