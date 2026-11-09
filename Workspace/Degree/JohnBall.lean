module

public import Workspace.Impl.JohnD
public import Workspace.Degree.JohnRange

@[expose] public section

/-!
# The label `Δ` by a search in the graph `Υ`

The program grows the ball around the point `0` in the graph of the label `υ`, one step at a time,
as a list of `0`s and `1`s (`johnBall`). After `k - 1` steps the first point outside the ball is
a point whose `k`-set is disjoint from that of `0`, and `johnDeltaR` is the label of the pair
formed by `0` and that point. `john_deltaR_iff` shows that this label is `Δ`.
-/

namespace GI.Degree

open Finset GI.Proved GI.Impl

/-- One step of the ball: `z` is in the new ball when it is in the old one, or one of its
neighbours in the graph of `υ` is. -/
def johnBallStep (n : ℕ) (labL : List ℕ) (υ : ℕ) (R : List ℕ) : List ℕ :=
  (List.range n).map fun z => if R.getD z 0 = 0 then
    ((List.range n).any fun y => johnD n labL υ z y && R.getD y 0 == 1).toNat else 1

/-- The ball of radius `d` around the point `0`, as a list of `0`s and `1`s. The ball of radius
`0` is the row `0` of the label `labL[0]` of the pair `(0, 0)`. -/
def johnBall (n : ℕ) (labL : List ℕ) (υ : ℕ) : ℕ → List ℕ
  | 0 => johnDRow n labL (labL.getD 0 0) 0
  | d + 1 => johnBallStep n labL υ (johnBall n labL υ d)

/-- The label of the pair formed by `0` and the first point outside the ball of radius `k - 1`. -/
def johnDeltaR (n : ℕ) (labL : List ℕ) (υ k : ℕ) : ℕ :=
  (johnRow n labL).getD ((johnBall n labL υ (k - 1)).findIdx fun x => decide (x = 0)) 0

variable {n m k : ℕ} {ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}} {lab : Fin (n * n) → ℕ}

theorem john_D_pair (lab : Fin (n * n) → ℕ) (υ : ℕ) (x y : Fin n) :
    johnD n (johnLabL lab) υ x y = decide (lab (johnPair x y) = υ) := by
  unfold johnD; rw [john_labL_getD]

/-- The entries of the ball, read as a function on the points. -/
def johnBallF (ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}) (x0 : Fin n) (d z : ℕ) : ℕ :=
  if hz : z < n then (decide (k ≤ d + johnInter ι x0 ⟨z, hz⟩)).toNat else 0

/-- **The ball of radius `d`** is the set of `z` with `k ≤ d + |ι x0 ∩ ι z|`. The case `d = 0`
uses that the label of `(0, 0)` is the label of the pairs `(x, x)` only (`john_ball_zero`), and
the step uses `john_ball_step`. -/
theorem john_ball_eq (h : JohnHyp0 ι lab) {υ : ℕ}
    (hυ : ∀ x y, lab (johnPair x y) = υ ↔ johnInter ι x y + 1 = k) (d : ℕ) :
    johnBall n (johnLabL lab) υ d = (List.range n).map (johnBallF ι h.x0 d) := by
  have hx0 : (h.x0 : ℕ) = 0 := rfl
  have hget : ∀ z : Fin n, (johnLabL lab).getD z 0 = lab (johnPair h.x0 z) := fun z => by
    have := john_labL_getD lab h.x0 z
    rwa [hx0, Nat.mul_zero, Nat.zero_add] at this
  induction d with
  | zero =>
    have h00 : (johnLabL lab).getD 0 0 = lab (johnPair h.x0 h.x0) := hget h.x0
    simp only [johnBall, johnDRow]
    refine List.map_congr_left fun z hz => ?_
    have hz' := List.mem_range.mp hz
    simp only [johnBallF, hz', dite_true, Nat.zero_add]
    unfold johnD
    rw [Nat.mul_zero, Nat.zero_add, hget ⟨z, hz'⟩, h00]
    simp only [h.lab_iff]
    have e1 : johnInter ι h.x0 h.x0 = k := by
      have := (john_ball_zero ι h.x0 h.x0).mpr rfl
      have := john_inter_le ι h.x0 h.x0
      omega
    have e2 := john_inter_le ι h.x0 ⟨z, hz'⟩
    rw [e1]
    congr 1
    exact decide_eq_decide.mpr ⟨fun e => e.ge, fun e => le_antisymm e2 e⟩
  | succ d ih =>
    simp only [johnBall, johnBallStep, ih]
    refine List.map_congr_left fun z hz => ?_
    have hz' := List.mem_range.mp hz
    have hR : ∀ y, ((List.range n).map (johnBallF ι h.x0 d)).getD y 0 = johnBallF ι h.x0 d y :=
      fun y => by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map]
        rcases Nat.lt_or_ge y n with hy | hy
        · simp [hy]
        · rw [List.getElem?_eq_none (by simp; omega)]
          simp [johnBallF, Nat.not_lt.mpr hy]
    rw [hR]
    have hstep := john_ball_step ι h.x0 ⟨z, hz'⟩ d
    simp only [johnBallF, hz', dite_true]
    by_cases h0 : k ≤ d + johnInter ι h.x0 ⟨z, hz'⟩
    · have h1 : k ≤ d + 1 + johnInter ι h.x0 ⟨z, hz'⟩ := by omega
      simp [h0, h1]
    · simp only [h0, decide_false, Bool.toNat_false, ite_true]
      congr 1
      rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff, hstep]
      constructor
      · rintro ⟨y, hy, hq⟩
        have hy' := List.mem_range.mp hy
        rw [Bool.and_eq_true, beq_iff_eq] at hq
        refine Or.inr ⟨⟨y, hy'⟩, ?_, ?_⟩
        · have := hq.2
          rw [hR] at this
          by_contra hc
          simp [johnBallF, hy', hc] at this
        · have := hq.1
          rw [show johnD n (johnLabL lab) υ z y = johnD n (johnLabL lab) υ (⟨z, hz'⟩ : Fin n)
            (⟨y, hy'⟩ : Fin n) from rfl, john_D_pair, decide_eq_true_iff] at this
          exact (hυ _ _).mp this
      · rintro (h1 | ⟨y, hy, hzy⟩)
        · exact absurd h1 h0
        · refine ⟨y, List.mem_range.mpr y.isLt, ?_⟩
          rw [Bool.and_eq_true, beq_iff_eq]
          refine ⟨?_, ?_⟩
          · rw [show johnD n (johnLabL lab) υ z y = johnD n (johnLabL lab) υ (⟨z, hz'⟩ : Fin n) y
              from rfl, john_D_pair, decide_eq_true_iff]
            exact (hυ _ _).mpr hzy
          · simp [johnBallF, y.isLt, hy]

theorem john_inter_eq_zero (x y : Fin n) :
    johnInter ι x y = 0 ↔ Disjoint (ι x).1 (ι y).1 := by
  unfold johnInter
  rw [card_eq_zero, disjoint_iff_inter_eq_empty]

/-- **The first point outside the ball** of radius `k - 1` exists, and its `k`-set is disjoint
from that of `0`. The hypothesis `2k ≤ m` (from `JohnHyp0`) gives a point whose `k`-set is
disjoint from that of `0`, so the point exists. -/
theorem john_ball_first (h : JohnHyp0 ι lab) {υ : ℕ}
    (hυ : ∀ x y, lab (johnPair x y) = υ ↔ johnInter ι x y + 1 = k) :
    ∃ ht : (johnBall n (johnLabL lab) υ (k - 1)).findIdx (fun x => decide (x = 0)) < n,
      johnInter ι h.x0 ⟨_, ht⟩ = 0 ∧
      johnDeltaR n (johnLabL lab) υ k = lab (johnPair h.x0 ⟨_, ht⟩) := by
  have hk := h.one_le
  set R := johnBall n (johnLabL lab) υ (k - 1) with hRdef
  have hR := john_ball_eq h hυ (k - 1)
  rw [← hRdef] at hR
  have hkm : 2 * k ≤ m := by have := h.two_mul; omega
  obtain ⟨z, hz⟩ := john_exists_inter ι hkm h.x0 0 (Nat.zero_le _)
  have hmem : 0 ∈ R := by
    rw [hR]
    refine List.mem_map.mpr ⟨z, List.mem_range.mpr z.isLt, ?_⟩
    simp only [johnBallF, z.isLt, dite_true, hz]
    simp
    omega
  obtain ⟨hlt, hval⟩ := john_findIdx hmem
  have hlen : R.length = n := by rw [hR]; simp
  set t := R.findIdx fun x => decide (x = 0)
  have ht : t < n := hlen ▸ hlt
  refine ⟨ht, ?_, ?_⟩
  · have e : R[t] = johnBallF ι h.x0 (k - 1) t := by simp [hR]
    rw [hval] at e
    simp only [johnBallF, ht, dite_true] at e
    have := john_inter_le ι h.x0 ⟨t, ht⟩
    by_contra hne
    have : k ≤ k - 1 + johnInter ι h.x0 ⟨t, ht⟩ := by omega
    simp [this] at e
  · unfold johnDeltaR
    rw [← hRdef]
    exact john_row_getD h ht

/-- **The label `Δ`.** `johnDeltaR` is the label of the pairs whose `k`-sets are disjoint, by
`john_ball_first`. -/
theorem john_deltaR_iff (h : JohnHyp0 ι lab) {υ : ℕ}
    (hυ : ∀ x y, lab (johnPair x y) = υ ↔ johnInter ι x y + 1 = k) (x y : Fin n) :
    lab (johnPair x y) = johnDeltaR n (johnLabL lab) υ k ↔ Disjoint (ι x).1 (ι y).1 := by
  obtain ⟨ht, hI, hd⟩ := john_ball_first h hυ
  rw [hd, h.lab_iff, hI, john_inter_eq_zero]

end GI.Degree
