module

public import Workspace.Impl.AggItemCiSojBal

@[expose] public section

/-!
# The balanced-color test in raw vertex labels

Only colors occurring in the row need to be counted. The extra color for labels
outside the fiber is distinct from every color inside the fiber.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.PairRefinement GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- The block of an interior vertex in the balanced coloring is its row-color class. -/
theorem itcs_bal_block (X : PairCfg q) (x₀ a : Fin q) (ha : a ∈ X.fiber) :
    itpBlk (itcsBal X x₀) a = X.fiber.filter (fun b => X.col x₀ b = X.col x₀ a) := by
  classical
  ext b
  simp only [itp_mem_blk, Finset.mem_filter]
  change (if b ∈ X.fiber then 2 * X.col x₀ b + 1 else 0) =
      (if a ∈ X.fiber then 2 * X.col x₀ a + 1 else 0) ↔ _
  rw [if_pos ha]
  by_cases hb : b ∈ X.fiber
  · simp only [hb, ↓reduceIte, true_and]
    omega
  · simp only [hb, ↓reduceIte, false_and]
    simp

/-- The exact real balance test is a finite family of integer counts. -/
theorem itcs_bal_test (X : PairCfg q) (x₀ : Fin q) (hx : x₀ ∈ X.fiber) :
    (∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤ etaB * X.fiber.card) ↔
      ∀ a ∈ X.fiber, 4 * itpSz (itcsBal X x₀) a ≤ 3 * X.fiber.card := by
  classical
  have hsize (a : Fin q) (ha : a ∈ X.fiber) :
      itpSz (itcsBal X x₀) a =
        (colorClass X.coloring false (X.idx hx) (X.enc (X.col x₀ a))).card := by
    rw [itpSz, itcs_bal_block X x₀ a ha]
    have h := X.filter_col_eq_map (X.vals_of_mem hx ha) (X.idx hx)
    rw [X.emb_idx hx] at h
    simpa only [Finset.card_map] using congrArg Finset.card h
  constructor
  · intro h a ha
    rw [hsize a ha]
    exact (itcs_bal_count_iff _ _).1 (h _)
  · intro h i
    by_cases hn : (colorClass X.coloring false (X.idx hx) i).Nonempty
    · obtain ⟨b, hb⟩ := hn
      have he : X.enc (X.col x₀ (X.emb rfl b)) = i := by
        have hh := (mem_colorClass _ _ _ _ _).1 hb
        simpa only [PairCfg.coloring_apply, X.emb_idx hx] using hh
      have hs := hsize (X.emb rfl b) (X.emb_mem rfl b)
      rw [he] at hs
      rw [← hs]
      exact (itcs_bal_count_iff _ _).2 (h _ (X.emb_mem rfl b))
    · rw [Finset.not_nonempty_iff_eq_empty.1 hn, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (by norm_num [etaB]) (Nat.cast_nonneg _)

/-- The usual size program also works for an arbitrary bounded palette.
The palette changes only the common weight bound and counting cost. -/
theorem itcs_sz_palette {Pg : Program} {f cnt B : ℕ}
    (hf : Pg.funs[f]? = some (itSzB cnt)) (hcnt : Pg.HasAt cnt (countFuns cnt))
    (lab : Fin q → ℕ) (hl : ∀ a, lab a ≤ B) (b : Fin q) :
    FunDet Pg f (.list [encFun lab, .nat b]) (.nat (itpSz lab b))
      ((countK + 1000) * (q + B + 1) ^ 3) := by
  rw [itpSz_eq_count]
  let W := 50 * (q + B + 1) ^ 2
  have h1 : 1 ≤ (q + B + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + B + 1 ≤ (q + B + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hL : (encFun lab).wt ≤ 5 * (q + B + 1) ^ 2 := by
    have h := wt_encFun_le lab hl
    nlinarith only [h]
  have hin := wt_list2_le (encFun lab) (.nat b)
  have hb := wt_nat_le (b : ℕ)
  have hlb := wt_nat_le (lab b)
  have hlb' := hl b
  have hq := b.isLt
  have hw2 := wt_list2_le (.nat (lab b)) (encFun lab)
  have hc : FunDet Pg cnt (.list [.nat (lab b), natList (acpLabs lab)])
      (.nat ((acpLabs lab).count (lab b))) (countK * (q + B + 1) ^ 3) :=
    count_spec hcnt (fun a ha => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
      exact (hl i).trans (Nat.le_add_left _ _))
      ((hl b).trans (Nat.le_add_left _ _)) (by simp only [acp_labs_length]; omega)
  rw [← acp_encFun] at hc
  let env : List Val := [.list [encFun lab, .nat b]]
  have g0 : StDC Pg env (arg 0) (encFun lab) 3 0 W := StDC.arg rfl (by dsimp [W]; omega) (by dsimp [W]; omega) (by dsimp [W]; omega)
  have g1 : StDC Pg env (arg 1) (.nat b) 3 0 W := StDC.arg rfl (by dsimp [W]; omega) (by dsimp [W]; omega) (by dsimp [W]; omega)
  have gl := StDC.get g0 g1 (encFun_getElem? lab b) (by dsimp [W]; omega)
  have g2 := StDC.mk2 gl g0 (by dsimp [W]; omega) (by dsimp [W]; omega)
  have hcount : (acpLabs lab).count (lab b) ≤ q := acp_count_le lab _
  have g3 := StDC.call g2 hc (by have := wt_nat_le ((acpLabs lab).count (lab b)); dsimp [W]; omega)
  refine StDC.funDet hf g3 ?_
  have hpow : (q + B + 1) ^ 2 ≤ (q + B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  dsimp only [W]
  simp only [Nat.add_mul]
  omega

end GI.Impl
