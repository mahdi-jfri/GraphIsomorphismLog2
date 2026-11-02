import Mathlib.GroupTheory.SpecificGroups.Alternating
import Aesop

/-! The explicit permutation generation used in the compatible completion of A.17. -/
namespace GI
open Equiv Equiv.Perm
variable {I : Type*} [DecidableEq I]

/-- The cycle a → b → c → a in the function-composition convention. -/
def cleanCycle (a b c : I) : Equiv.Perm I := Equiv.swap a c * Equiv.swap a b

theorem cleanCycle_inv (a b c : I) : (cleanCycle a b c)⁻¹ = cleanCycle a c b := by
  simp [cleanCycle, mul_inv_rev]

theorem root_swap_expand (o a b : I) (hbo : b ≠ o) (hba : b ≠ a) :
    Equiv.swap a b = Equiv.swap o a * Equiv.swap o b * Equiv.swap o a := by
  simpa only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hbo hba, Equiv.swap_inv]
    using Equiv.swap_apply_apply (Equiv.swap o a) o b

/-- Products of central transpositions generate all even permutations. -/
theorem alternating_le_of_root_pairs [Fintype I] (K : Subgroup (Equiv.Perm I)) (o : I)
    (hroot : ∀ a b : I, a ≠ o → b ≠ o → Equiv.swap o a * Equiv.swap o b ∈ K) :
    alternatingGroup I ≤ K := by
  have hsame : ∀ a b c : I, a ≠ b → a ≠ c → Equiv.swap a b * Equiv.swap a c ∈ K := by
    intro a b c hab hac
    by_cases hbc : b = c
    · subst c
      simpa using K.one_mem
    by_cases hao : a = o
    · subst a
      exact hroot b c (Ne.symm hab) (Ne.symm hac)
    by_cases hbo : b = o
    · subst b
      rw [Equiv.swap_comm a o, root_swap_expand o a c (Ne.symm hbc) (Ne.symm hac)]
      simpa only [mul_assoc, Equiv.swap_mul_self_mul] using hroot c a (Ne.symm hbc) hao
    by_cases hco : c = o
    · subst c
      rw [root_swap_expand o a b hbo (Ne.symm hab), Equiv.swap_comm a o]
      simpa only [mul_assoc, Equiv.swap_mul_self, mul_one] using hroot a b hao hbo
    rw [root_swap_expand o a b hbo (Ne.symm hab), root_swap_expand o a c hco (Ne.symm hac)]
    simpa [mul_assoc] using K.mul_mem (hroot a b hao hbo) (hroot c a hco hao)
  have hpairs : ∀ σ τ : Equiv.Perm I, σ.IsSwap → τ.IsSwap → σ * τ ∈ K := by
    rintro σ τ ⟨a, b, hab, rfl⟩ ⟨c, d, hcd, rfl⟩
    by_cases hac : a = c
    · subst c
      exact hsame a b d hab hcd
    have heq : Equiv.swap a b * Equiv.swap c d =
        (Equiv.swap a b * Equiv.swap a c) * (Equiv.swap c a * Equiv.swap c d) := by
      simp [Equiv.swap_comm c a, mul_assoc]
    rw [heq]
    exact K.mul_mem (hsame a b c hab hac) (hsame c a d (Ne.symm hac) hcd)
  intro σ hσ
  have hind : ∀ (n : ℕ) (l : List (Equiv.Perm I)),
      (∀ g ∈ l, g.IsSwap) → l.length = 2 * n → l.prod ∈ K := by
    intro n
    induction n with
    | zero =>
      intro l _ hn
      have hl : l = [] := List.length_eq_zero_iff.mp (by simpa using hn)
      simpa [hl] using K.one_mem
    | succ n ih =>
      intro l hl hn
      rw [Nat.mul_succ] at hn
      obtain ⟨a, l, rfl⟩ := l.exists_of_length_succ hn
      rw [List.length_cons, Nat.succ_inj] at hn
      obtain ⟨b, l, rfl⟩ := l.exists_of_length_succ hn
      rw [List.length_cons, Nat.succ_inj] at hn
      rw [List.prod_cons, List.prod_cons, ← mul_assoc]
      exact K.mul_mem
        (hpairs a b (hl a List.mem_cons_self) (hl b (List.mem_cons_of_mem a List.mem_cons_self)))
        (ih l (fun g hg => hl g (List.mem_cons_of_mem a (List.mem_cons_of_mem b hg))) hn)
  obtain ⟨l, rfl, hl⟩ := Equiv.Perm.truncSwapFactors σ
  obtain ⟨n, hn⟩ := (Equiv.Perm.prod_list_swap_mem_alternatingGroup_iff_even_length hl).1 hσ
  rw [← two_mul] at hn
  exact hind n l hl hn

/-- A commutator of two central cycles with otherwise disjoint supports gives
the central cross-pair cycle. This is an identity of actual permutations. -/
theorem clean_cross_pair_identity (o a a' b b' : I) (hn : [o, a, a', b, b'].Nodup) :
    cleanCycle o b b' * cleanCycle o a a' * (cleanCycle o b b')⁻¹ * (cleanCycle o a a')⁻¹ =
      Equiv.swap o a * Equiv.swap o b := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, List.nodup_nil, not_false_eq_true, not_or, and_true] at hn
  obtain ⟨⟨hoa, hoa', hob, hob'⟩, ⟨haa', hab, hab'⟩, ⟨ha'b, ha'b'⟩, hbb'⟩ := hn
  have hao := Ne.symm hoa
  have ha'o := Ne.symm hoa'
  have hbo := Ne.symm hob
  have hb'o := Ne.symm hob'
  have ha'a := Ne.symm haa'
  have hba := Ne.symm hab
  have hb'a := Ne.symm hab'
  have hba' := Ne.symm ha'b
  have hb'a' := Ne.symm ha'b'
  have hb'b := Ne.symm hbb'
  ext x
  by_cases ho : x = o
  · subst x
    simp_all [cleanCycle, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  by_cases ha : x = a
  · subst x
    simp_all [cleanCycle, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  by_cases ha' : x = a'
  · subst x
    simp_all [cleanCycle, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  by_cases hb : x = b
  · subst x
    simp_all [cleanCycle, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  by_cases hb' : x = b'
  · subst x
    simp_all [cleanCycle, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  · simp [cleanCycle, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_apply_def, ho, ha, ha', hb, hb']

section Pairs
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- None is the central point; each j supplies its two private points. -/
def pairedCleanCycle (j : J) : Equiv.Perm (Option (J × Bool)) :=
  cleanCycle none (some (j, false)) (some (j, true))

omit [Fintype J] in
theorem paired_variant_mem (K : Subgroup (Equiv.Perm (Option (J × Bool))))
    (hgen : ∀ j, pairedCleanCycle j ∈ K) (j : J) (b : Bool) :
    cleanCycle none (some (j, b)) (some (j, !b)) ∈ K := by
  cases b
  · exact hgen j
  · simpa only [pairedCleanCycle, cleanCycle_inv, Bool.not_true] using K.inv_mem (hgen j)

/-- The odd-degree generation assertion in A.17: one center and disjoint pairs
cover every point, and the corresponding cycles generate the full alternating group. -/
theorem paired_clean_cycles_generate :
    Subgroup.closure (Set.range (pairedCleanCycle (J := J))) =
      alternatingGroup (Option (J × Bool)) := by
  let K := Subgroup.closure (Set.range (pairedCleanCycle (J := J)))
  have hgen : ∀ j, pairedCleanCycle j ∈ K := fun j => Subgroup.subset_closure ⟨j, rfl⟩
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro p ⟨j, rfl⟩
    apply Equiv.Perm.IsThreeCycle.mem_alternatingGroup
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by simp) (by simp) (by simp)
  · apply alternating_le_of_root_pairs K none
    intro a b hao hbo
    cases a with
    | none => exact False.elim (hao rfl)
    | some a =>
      cases b with
      | none => exact False.elim (hbo rfl)
      | some b =>
        obtain ⟨j, c⟩ := a
        obtain ⟨l, d⟩ := b
        by_cases hjl : j = l
        · subst l
          cases c <;> cases d
          · simpa using K.one_mem
          · simpa only [pairedCleanCycle, cleanCycle, mul_inv_rev, Equiv.swap_inv] using K.inv_mem (hgen j)
          · exact hgen j
          · simpa using K.one_mem
        · have hn : [none, some (j, c), some (j, !c), some (l, d), some (l, !d)].Nodup := by
            cases c <;> cases d <;> simp [hjl, Ne.symm hjl]
          rw [← clean_cross_pair_identity _ _ _ _ _ hn]
          have hg := paired_variant_mem K hgen j c
          have hh := paired_variant_mem K hgen l d
          exact K.mul_mem (K.mul_mem (K.mul_mem hh hg) (K.inv_mem hh)) (K.inv_mem hg)
end Pairs

/-- One compatible three-cycle adjoining a new point completes the alternating
group already present on its complement. No relations of abstract lifts are assumed. -/
theorem alternating_le_one_point_extension [Fintype I] (K : Subgroup (Equiv.Perm I))
    (o a z : I) (hoa : o ≠ a) (hoz : o ≠ z) (haz : a ≠ z)
    (hold : ∀ p : Equiv.Perm I, p ∈ alternatingGroup I → p z = z → p ∈ K)
    (hnew : cleanCycle o a z ∈ K) : alternatingGroup I ≤ K := by
  have h_old : ∀ x y : I, x ≠ o → y ≠ o → x ≠ z → y ≠ z →
      Equiv.swap o x * Equiv.swap o y ∈ K := by
    intro x y hxo hyo hxz hyz
    apply hold
    · simp [Equiv.Perm.mem_alternatingGroup, map_mul,
        Equiv.Perm.sign_swap (Ne.symm hxo), Equiv.Perm.sign_swap (Ne.symm hyo)]
    · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Ne.symm hoz, Ne.symm hxz, Ne.symm hyz]
  have hazmem : Equiv.swap o a * Equiv.swap o z ∈ K := by
    simpa only [cleanCycle, mul_inv_rev, Equiv.swap_inv] using K.inv_mem hnew
  have htoNew : ∀ x : I, x ≠ o → x ≠ z → Equiv.swap o x * Equiv.swap o z ∈ K := by
    intro x hxo hxz
    simpa [mul_assoc] using K.mul_mem (h_old x a hxo (Ne.symm hoa) hxz haz) hazmem
  apply alternating_le_of_root_pairs K o
  intro x y hxo hyo
  by_cases hxz : x = z
  · subst x
    by_cases hyz : y = z
    · subst y
      simpa using K.one_mem
    · simpa only [mul_inv_rev, Equiv.swap_inv] using K.inv_mem (htoNew y hyo hyz)
  by_cases hyz : y = z
  · subst y
    exact htoNew x hxo hxz
  · exact h_old x y hxo hyo hxz hyz

theorem one_point_clean_cycle_generate [Fintype I] (o a z : I)
    (hoa : o ≠ a) (hoz : o ≠ z) (haz : a ≠ z) :
    Subgroup.closure ({p : Equiv.Perm I | p ∈ alternatingGroup I ∧ p z = z} ∪
      {cleanCycle o a z}) = alternatingGroup I := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro p (⟨hp, _⟩ | rfl)
    · exact hp
    · exact Equiv.Perm.IsThreeCycle.mem_alternatingGroup
        (Equiv.Perm.isThreeCycle_swap_mul_swap_same hoz hoa (Ne.symm haz))
  · apply alternating_le_one_point_extension _ o a z hoa hoz haz
    · intro p hp hfix
      exact Subgroup.subset_closure (Or.inl ⟨hp, hfix⟩)
    · exact Subgroup.subset_closure (Or.inr rfl)

end GI
