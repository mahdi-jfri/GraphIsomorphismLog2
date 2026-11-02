import Workspace.Impl.AggRectRepT5
import Workspace.Impl.AggRectRepFinH

/-!
# The generator lists of the program

Stage 2 lists the generators of the side stabilizer `P` by numbers: for `t < q²` with
`a = t / q` and `b = t % q`, the list `rcRGenL` of `swap w₀ w₁ * swap a b` (or of the identity).
Here `w₀, w₁` are the first two points of `W` (`rcRW0`, `rcRW1`).

* `rcR_W01`: these are two different points of `W`.
* `rcR_genLs_eq`: the lists are the lists of `rcRGens W R w₀ w₁`.
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Rectangle
open GI.Cited (gens)

variable {q : ℕ}

/-! ### The first two points of `W` -/

theorem rcR_ind_length (W : Finset (Fin q)) : (rcRInd W).length = q := by simp [rcRInd]

/-- **The first two points of `W`.** -/
theorem rcR_W01 {W : Finset (Fin q)} (hW : 2 ≤ W.card) :
    ∃ (h0 : rcRW0 (rcRInd W) < q) (h1 : rcRW1 (rcRInd W) q < q),
      (⟨_, h0⟩ : Fin q) ∈ W ∧ (⟨_, h1⟩ : Fin q) ∈ W ∧ rcRW0 (rcRInd W) ≠ rcRW1 (rcRInd W) q := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < W.card)
  -- the first point
  have hex0 : ∃ y ∈ rcRInd W, decide (y = 1) = true := by
    refine ⟨1, ?_, by simp⟩
    have := (rcR_ind_getD W a).2 ha
    rw [List.getD_eq_getElem _ _ (by rw [rcR_ind_length]; exact a.2)] at this
    rw [← this]; exact List.getElem_mem _
  have h0l : rcRW0 (rcRInd W) < (rcRInd W).length := List.findIdx_lt_length_of_exists hex0
  rw [rcR_ind_length] at h0l
  have h0v : (rcRInd W).getD (rcRW0 (rcRInd W)) 0 = 1 := by
    have hp := List.findIdx_getElem (w := (by rw [rcR_ind_length]; exact h0l :
      rcRW0 (rcRInd W) < (rcRInd W).length))
    rw [List.getD_eq_getElem _ _ (by rw [rcR_ind_length]; exact h0l)]
    exact of_decide_eq_true hp
  have h0W : (⟨_, h0l⟩ : Fin q) ∈ W := (rcR_ind_getD W ⟨_, h0l⟩).1 h0v
  -- the second point
  obtain ⟨c, hcW, hc0⟩ : ∃ c ∈ W, (c : ℕ) ≠ rcRW0 (rcRInd W) := by
    by_cases h : (a : ℕ) = rcRW0 (rcRInd W)
    · refine ⟨b, hb, fun hb' => hab (Fin.ext (h.trans hb'.symm))⟩
    · exact ⟨a, ha, h⟩
  have hex1 : ∃ j ∈ List.range q,
      ((rcRInd W).getD j 0 == 1 && !(j == rcRW0 (rcRInd W))) = true := by
    refine ⟨c, List.mem_range.2 c.2, ?_⟩
    have := (rcR_ind_getD W c).2 hcW
    rw [this]
    simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_true', beq_eq_false_iff_ne]
    exact hc0
  have h1l : rcRW1 (rcRInd W) q < (List.range q).length := List.findIdx_lt_length_of_exists hex1
  rw [List.length_range] at h1l
  have hp1 := List.findIdx_getElem (w := (by rw [List.length_range]; exact h1l :
    rcRW1 (rcRInd W) q < (List.range q).length))
  have hp1' : (rcRInd W).getD (rcRW1 (rcRInd W) q) 0 = 1 ∧
      rcRW1 (rcRInd W) q ≠ rcRW0 (rcRInd W) := by
    simp only [List.getElem_range, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
      beq_eq_false_iff_ne] at hp1
    exact hp1
  refine ⟨h0l, h1l, h0W, (rcR_ind_getD W ⟨_, h1l⟩).1 hp1'.1, fun h => hp1'.2 h.symm⟩

/-! ### The generator lists -/

theorem rcR_range_mul (n : ℕ) :
    List.range (n * q) = (List.range n).flatMap fun a => (List.range q).map fun b => a * q + b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append]
    simp

theorem rcR_swN_eq (x y z : Fin q) : rcRSwN x y z = (swap x y z : ℕ) := by
  unfold rcRSwN
  by_cases h1 : z = x
  · subst h1; simp
  · by_cases h2 : z = y
    · subst h2; simp [Fin.val_ne_of_ne h1]
    · rw [swap_apply_of_ne_of_ne h1 h2]
      simp [Fin.val_ne_of_ne h1, Fin.val_ne_of_ne h2]

theorem rcR_condN_eq (W R : Finset (Fin q)) (a b : Fin q) :
    rcRCondN (rcRInd W) (rcRInd R) a b = if a ≠ b ∧ rcRSame W R a b then 1 else 0 := by
  classical
  have hW : ∀ c : Fin q, (rcRInd W).getD c 0 = if c ∈ W then 1 else 0 := fun c => by
    rw [show rcRInd W = rcRL (fun i => if i ∈ W then 1 else 0) from rfl, rcR_L_getD]
  have hR : ∀ c : Fin q, (rcRInd R).getD c 0 = if c ∈ R then 1 else 0 := fun c => by
    rw [show rcRInd R = rcRL (fun i => if i ∈ R then 1 else 0) from rfl, rcR_L_getD]
  unfold rcRCondN rcRSame
  rw [hW a, hW b, hR a, hR b]
  simp only [GI.Machine.BinOp.eval]
  by_cases hab : a = b
  · subst hab; simp
  · have hab' : (a : ℕ) ≠ b := Fin.val_ne_of_ne hab
    by_cases ha : a ∈ W <;> by_cases hb : b ∈ W <;> by_cases ha' : a ∈ R <;>
      by_cases hb' : b ∈ R <;> simp [hab, hab', ha, hb, ha', hb']

/-- **The program's lists are the generators of `P`.** -/
theorem rcR_genLs_eq (W R : Finset (Fin q)) (w₀ w₁ : Fin q) :
    rcRGenLs (rcRInd W) (rcRInd R) w₀ w₁ q =
      (rcRGens W R w₀ w₁).map fun σ => rcRL fun i => (σ i : ℕ) := by
  classical
  unfold rcRGenLs rcRGens
  rw [rcR_range_mul, List.map_flatMap, List.map_flatMap, ← List.map_coe_finRange,
    List.flatMap_map]
  refine List.flatMap_congr fun a _ => ?_
  rw [List.map_map, List.map_map, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp_apply]
  have hq : 0 < q := Nat.pos_of_ne_zero (fun h => by subst h; exact a.elim0)
  have hdiv : ((a : ℕ) * q + b) / q = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt b.2, Nat.zero_add]
  have hmod : ((a : ℕ) * q + b) % q = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.2]
  unfold rcRGenL
  rw [hdiv, hmod, ← List.map_coe_finRange, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  unfold rcRGrN
  rw [rcR_condN_eq]
  unfold rcRGen
  by_cases h : a ≠ b ∧ rcRSame W R a b
  · rw [if_pos h, if_pos h, if_neg (by norm_num), rcR_swN_eq a b j, rcR_swN_eq w₀ w₁ (swap a b j)]
    rfl
  · rw [if_neg h, if_neg h, if_pos rfl]
    rfl

end GI.Impl
