import Workspace.CleanComplementLG2
import Mathlib.GroupTheory.Perm.Fin

/-! Finite support sets and even full-support cycles for the actual LG2 inputs. -/
namespace GI.CleanLocalization
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_pair_sets {k : ℕ} (hk : 1 ≤ k) (hm : 2 * k - 1 ≤ Fintype.card I) :
    ∃ (T U : Finset I) (a : I), T.card = k ∧ U.card = k ∧
      (∀ i, (i ∈ T ∧ i ∈ U) ↔ i = a) := by
  have hkI : k ≤ (Finset.univ : Finset I).card := by simp only [Finset.card_univ]; omega
  obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq hkI
  have hpos : 0 < T.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  have hspace : k - 1 ≤ Tᶜ.card := by rw [Finset.card_compl, hT]; omega
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hspace
  have hdis : ∀ i ∈ S, i ∉ T := fun i hi => Finset.mem_compl.mp (hS hi)
  have has : a ∉ S := fun hs => hdis a hs ha
  refine ⟨T, insert a S, a, hT, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem has, hScard]
    omega
  · intro i
    constructor
    · rintro ⟨hi, hu⟩
      rcases Finset.mem_insert.mp hu with he | hs
      · exact he
      · exact False.elim (hdis i hs hi)
    · intro he
      subst i
      exact ⟨ha, Finset.mem_insert_self _ _⟩

theorem even_full_support (T : Finset I) (hk : 5 ≤ T.card) (hodd : Odd T.card) :
    ∃ p : alternatingGroup I, ∀ i, p.val i ≠ i ↔ i ∈ T := by
  obtain ⟨n, hn⟩ := hodd.exists_bit1
  let e : Fin (2 * n + 1) ≃ T := Fintype.equivOfCardEq (by simpa using hn.symm)
  let r : alternatingGroup (Fin (2 * n + 1)) :=
    ⟨finRotate (2 * n + 1), Equiv.Perm.finRotate_bit1_mem_alternatingGroup⟩
  have hr : ∀ x : Fin (2 * n + 1), r.val x ≠ x := by
    intro x
    apply Equiv.Perm.mem_support.mp
    change x ∈ (finRotate (2 * n + 1)).support
    rw [support_finRotate_of_le (by omega)]
    exact Finset.mem_univ x
  refine ⟨supportedTop T e r, ?_⟩
  intro i
  constructor
  · intro hm
    by_cases hi : i ∈ T
    · exact hi
    · exact False.elim (hm (supportedTop_fixes T e r i hi))
  · intro hi
    change Equiv.Perm.ofSubtype (relabelPerm e r.val) i ≠ i
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ hi]
    intro he
    have ht := congrArg e.symm (show relabelPerm e r.val ⟨i, hi⟩ = ⟨i, hi⟩ from Subtype.ext he)
    change e.symm (e (r.val (e.symm ⟨i, hi⟩))) = e.symm ⟨i, hi⟩ at ht
    rw [e.symm_apply_apply] at ht
    exact hr _ ht

theorem even_derangement (hk : 5 ≤ Fintype.card I) (hodd : Odd (Fintype.card I)) :
    ∃ p : alternatingGroup I, ∀ i, p.val i ≠ i := by
  obtain ⟨p, hp⟩ := even_full_support (Finset.univ : Finset I) (by simpa using hk) (by simpa using hodd)
  exact ⟨p, fun i => (hp i).mpr (Finset.mem_univ i)⟩

theorem even_full_support_send (T : Finset I) (hk : 5 ≤ T.card) (hodd : Odd T.card)
    (a b : I) (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) :
    ∃ p : alternatingGroup I, (∀ i, p.val i ≠ i ↔ i ∈ T) ∧ p.val a = b := by
  classical
  letI : Fintype T := Subtype.fintype (fun i : I => i ∈ T)
  have hcard : Fintype.card T = T.card := Fintype.card_coe T
  obtain ⟨r, hr⟩ := even_derangement (I := T) (by omega) (by simpa only [hcard] using hodd)
  let a' : T := ⟨a, ha⟩
  let b' : T := ⟨b, hb⟩
  have hab' : a' ≠ b' := fun he => hab (congrArg Subtype.val he)
  obtain ⟨t, ht, hta, htb⟩ := even_perm_maps_pair (I := T) (by omega) (Ne.symm (hr a')) hab'
  let q := t * r.val * t⁻¹
  have hq : q ∈ alternatingGroup T :=
    (alternatingGroup T).mul_mem ((alternatingGroup T).mul_mem ht r.property)
      ((alternatingGroup T).inv_mem ht)
  have hti : t.symm a' = a' := by
    apply t.injective
    rw [t.apply_symm_apply, hta]
  have hsend : q a' = b' := by
    change t (r.val (t.symm a')) = b'
    rw [hti, htb]
  have hmove : ∀ x : T, q x ≠ x := by
    intro x hx
    have he := congrArg t.symm hx
    change t.symm (t (r.val (t.symm x))) = t.symm x at he
    rw [t.symm_apply_apply] at he
    exact hr _ he
  let p : alternatingGroup I := ⟨Equiv.Perm.ofSubtype q, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
    exact Equiv.Perm.mem_alternatingGroup.mp hq⟩
  refine ⟨p, ?_, ?_⟩
  · intro i
    constructor
    · intro hm
      by_cases hi : i ∈ T
      · exact hi
      · exact False.elim (hm (Equiv.Perm.ofSubtype_apply_of_not_mem q hi))
    · intro hi hm
      rw [Equiv.Perm.ofSubtype_apply_of_mem q hi] at hm
      exact hmove ⟨i, hi⟩ (Subtype.ext hm)
  · change Equiv.Perm.ofSubtype q a = b
    rw [Equiv.Perm.ofSubtype_apply_of_mem q ha]
    exact congrArg Subtype.val hsend

theorem exists_two_containing_avoiding {k : ℕ} (hk : 2 ≤ k)
    (hm : k + 2 ≤ Fintype.card I) (a z b c : I)
    (haz : a ≠ z) (hba : b ≠ a) (hbz : b ≠ z) (hca : c ≠ a) (hcz : c ≠ z) :
    ∃ T : Finset I, T.card = k ∧ a ∈ T ∧ z ∈ T ∧ b ∉ T ∧ c ∉ T := by
  have hspace : k - 2 ≤ ({a, z, b, c} : Finset I)ᶜ.card := by
    rw [Finset.card_compl]
    have hs : ({a, z, b, c} : Finset I).card ≤ 4 := Finset.card_le_four
    omega
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hspace
  have haS : a ∉ S := by intro h; have := Finset.mem_compl.mp (hS h); simp at this
  have hzS : z ∉ S := by intro h; have := Finset.mem_compl.mp (hS h); simp at this
  have hbS : b ∉ S := by intro h; have := Finset.mem_compl.mp (hS h); simp at this
  have hcS : c ∉ S := by intro h; have := Finset.mem_compl.mp (hS h); simp at this
  refine ⟨insert a (insert z S), ?_, by simp, by simp, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [haz, haS]),
      Finset.card_insert_of_notMem hzS, hScard]
    omega
  · simp [hba, hbz, hbS]
  · simp [hca, hcz, hcS]

end GI.CleanLocalization
