import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.Finset.Card
import Aesop

/-! The explicit transfer construction (LG3) in Theorem A.18.
The coordinate group H is arbitrary; no commutativity or subdirectness is assumed. -/

namespace GI
variable {I H : Type*} [Fintype I] [DecidableEq I] [Group H]

def rowPermute (s : Equiv.Perm I) (x : I → H) : I → H := fun r => x (s r)

def RowAltInvariant (K : Subgroup (I → H)) : Prop :=
  ∀ s : Equiv.Perm I, s ∈ alternatingGroup I → ∀ x ∈ K, rowPermute s x ∈ K

def rowTransfer (i j : I) (n : H) : I → H :=
  fun r => if r = i then n else if r = j then n⁻¹ else 1

def rowCycle (i j k : I) : Equiv.Perm I := Equiv.swap i j * Equiv.swap j k

theorem row_cycle_even {i j k : I} (hij : i ≠ j) (hjk : j ≠ k) :
    rowCycle i j k ∈ alternatingGroup I := by
  simp [rowCycle, Equiv.Perm.mem_alternatingGroup, map_mul,
    Equiv.Perm.sign_swap hij, Equiv.Perm.sign_swap hjk]

omit [Fintype I] in
theorem row_cycle_first {i j k : I} (hij : i ≠ j) (hik : i ≠ k) :
    rowCycle i j k i = j := by
  simp [rowCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hij, hik]

omit [Fintype I] in
theorem row_cycle_second {i j k : I} (hik : i ≠ k) (hjk : j ≠ k) :
    rowCycle i j k j = k := by
  simp [rowCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Ne.symm hik, Ne.symm hjk]

omit [Fintype I] in
theorem row_cycle_third {i j k : I} : rowCycle i j k k = i := by
  simp [rowCycle, Equiv.Perm.mul_apply]

omit [Fintype I] in
theorem row_cycle_outside {i j k r : I} (hi : r ≠ i) (hj : r ≠ j) (hk : r ≠ k) :
    rowCycle i j k r = r := by
  simp [rowCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hi, hj, hk]

/-- A direct two-point extension, with its parity corrected on two unused points. -/
theorem even_perm_maps_pair (hcard : 4 ≤ Fintype.card I)
    {a b i j : I} (hab : a ≠ b) (hij : i ≠ j) :
    ∃ s : Equiv.Perm I, s ∈ alternatingGroup I ∧ s a = i ∧ s b = j := by
  let t : Equiv.Perm I := Equiv.swap a i
  let p : Equiv.Perm I := Equiv.swap (t b) j * t
  have hta : t a = i := by simp [t]
  have htbi : t b ≠ i := by
    intro he
    have he' : t b = t a := he.trans hta.symm
    exact hab (t.injective he').symm
  have hpa : p a = i := by
    change Equiv.swap (t b) j (t a) = i
    rw [hta, Equiv.swap_apply_of_ne_of_ne (Ne.symm htbi) hij]
  have hpb : p b = j := by simp [p, Equiv.Perm.mul_apply]
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with heven | hodd
  · exact ⟨p, Equiv.Perm.mem_alternatingGroup.mpr heven, hpa, hpb⟩
  · have hspare : 1 < ({a, b} : Finset I)ᶜ.card := by
      rw [Finset.card_compl]
      have hs : ({a, b} : Finset I).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hspare
    have hc' : c ≠ a ∧ c ≠ b := by simpa using hc
    have hd' : d ≠ a ∧ d ≠ b := by simpa using hd
    refine ⟨p * Equiv.swap c d, ?_, ?_, ?_⟩
    · simp [Equiv.Perm.mem_alternatingGroup, map_mul, hodd, Equiv.Perm.sign_swap hcd]
    · rw [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hc'.1) (Ne.symm hd'.1), hpa]
    · rw [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hc'.2) (Ne.symm hd'.2), hpb]

omit [Fintype I] in
theorem row_transfer_permute {s : Equiv.Perm I} {a b i j : I} (n : H)
    (ha : s a = i) (hb : s b = j) :
    rowPermute s (rowTransfer i j n) = rowTransfer a b n := by
  funext r
  have hi : s r = i ↔ r = a := by rw [← ha]; exact s.injective.eq_iff
  have hj : s r = j ↔ r = b := by rw [← hb]; exact s.injective.eq_iff
  simp only [rowPermute, rowTransfer, hi, hj]

/-- The paper's two three-cycle differences and intervening double transposition. -/
theorem row_transfer_of_five (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (i j k p q : I) (hn : [i, j, k, p, q].Nodup)
    (x : I → H) (hx : x ∈ K) (hxi : x i = 1) : rowTransfer i j (x j) ∈ K := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, not_false_eq_true, not_or, and_true] at hn
  have hij : i ≠ j := by aesop
  have hik : i ≠ k := by aesop
  have hip : i ≠ p := by aesop
  have hiq : i ≠ q := by aesop
  have hjk : j ≠ k := by aesop
  have hjp : j ≠ p := by aesop
  have hjq : j ≠ q := by aesop
  have hkp : k ≠ p := by aesop
  have hkq : k ≠ q := by aesop
  have hpq : p ≠ q := by aesop
  let d : I → H := x * (rowPermute (rowCycle i k j) x)⁻¹
  have hd : d ∈ K := K.mul_mem hx
    (K.inv_mem (hinv _ (row_cycle_even hik (Ne.symm hjk)) x hx))
  have hdj : d j = x j := by
    simp [d, rowPermute, row_cycle_third, hxi]
  have hdo : ∀ r, r ≠ i → r ≠ j → r ≠ k → d r = 1 := by
    intro r hi hj hk
    simp [d, rowPermute, row_cycle_outside hi hk hj]
  let s : Equiv.Perm I := Equiv.swap i p * Equiv.swap k q
  have hs : s ∈ alternatingGroup I := by
    simp [s, Equiv.Perm.mem_alternatingGroup, map_mul,
      Equiv.Perm.sign_swap hip, Equiv.Perm.sign_swap hkq]
  let y := rowPermute s d
  have hy : y ∈ K := hinv s hs d hd
  have hyi : y i = 1 := by
    simp only [y, rowPermute, s, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hik hiq, Equiv.swap_apply_left]
    exact hdo p (Ne.symm hip) (Ne.symm hjp) (Ne.symm hkp)
  have hyj : y j = x j := by
    simp only [y, rowPermute, s, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hjk hjq,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) hjp, hdj]
  have hyk : y k = 1 := by
    simp only [y, rowPermute, s, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hiq) (Ne.symm hpq)]
    exact hdo q (Ne.symm hiq) (Ne.symm hjq) (Ne.symm hkq)
  have hz : rowPermute (rowCycle i j k) y * y⁻¹ ∈ K :=
    K.mul_mem (hinv _ (row_cycle_even hij hjk) y hy) (K.inv_mem hy)
  have heq : rowPermute (rowCycle i j k) y * y⁻¹ = rowTransfer i j (x j) := by
    funext r
    by_cases hi : r = i
    · subst r
      simp [rowPermute, rowTransfer, row_cycle_first hij hik, hyi, hyj]
    by_cases hj : r = j
    · subst r
      simp [rowPermute, rowTransfer, row_cycle_second hik hjk, hyj, hyk, Ne.symm hij]
    by_cases hk : r = k
    · subst r
      simp [rowPermute, rowTransfer, row_cycle_third, hyi, hyk, Ne.symm hik, Ne.symm hjk]
    · simp [rowPermute, rowTransfer, row_cycle_outside hi hj hk, hi, hj]
  exact heq ▸ hz

/-- LG3 in full generality: every element visible at one coordinate while another
coordinate is fixed gives a transfer between any ordered pair of distinct rows. -/
theorem row_transfer_mem (K : Subgroup (I → H)) (hinv : RowAltInvariant K)
    (hcard : 5 ≤ Fintype.card I) {i j a b : I} (hij : i ≠ j) (hab : a ≠ b)
    (x : I → H) (hx : x ∈ K) (hxi : x i = 1) : rowTransfer a b (x j) ∈ K := by
  have hspare : 2 < ({i, j} : Finset I)ᶜ.card := by
    rw [Finset.card_compl]
    have hs : ({i, j} : Finset I).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨k, p, q, hk, hp, hq, hkp, hkq, hpq⟩ := Finset.two_lt_card_iff.mp hspare
  have hk' : k ≠ i ∧ k ≠ j := by simpa using hk
  have hp' : p ≠ i ∧ p ≠ j := by simpa using hp
  have hq' : q ≠ i ∧ q ≠ j := by simpa using hq
  have hn : [i, j, k, p, q].Nodup := by
    simp [hij, Ne.symm hk'.1, Ne.symm hk'.2, Ne.symm hp'.1, Ne.symm hp'.2,
      Ne.symm hq'.1, Ne.symm hq'.2, hkp, hkq, hpq]
  have ht := row_transfer_of_five K hinv i j k p q hn x hx hxi
  obtain ⟨s, hs, hsa, hsb⟩ := even_perm_maps_pair (by omega) hab hij
  have ht' := hinv s hs (rowTransfer i j (x j)) ht
  rwa [row_transfer_permute (x j) hsa hsb] at ht'

theorem fin_row_transfer_mem {m : ℕ} (K : Subgroup (Fin m → H))
    (hinv : RowAltInvariant K) (hm : 5 ≤ m)
    {i j a b : Fin m} (hij : i ≠ j) (hab : a ≠ b)
    (x : Fin m → H) (hx : x ∈ K) (hxi : x i = 1) : rowTransfer a b (x j) ∈ K :=
  row_transfer_mem K hinv (by simpa using hm) hij hab x hx hxi

end GI
