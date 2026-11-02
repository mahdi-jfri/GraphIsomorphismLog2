import Workspace.Proved.SSTable

/-!
# A closed table describes the group

A table is *closed* when the product of any two of its entries sifts through. For a closed,
well-formed table whose base contains every point, the permutations that sift through form a
group (`ssS_mul_closed`), and every one of them is a product of entries (`ssS_le_closure`). So
if the entries lie in `⟨gs⟩` and every generator sifts through, then the permutations that sift
through are exactly `⟨gs⟩` (`ss_mem_gens_iff`). The same argument at level `i` describes the
pointwise stabilizer of the first `i` base points (`ss_level_eq`).
-/

namespace GI.Proved

open Equiv GI.Cited

variable {n : ℕ}

/-- `g` is an entry of a level `≥ k`. -/
def SsEnt (T : List (SsSlot n)) (k : ℕ) (g : Perm (Fin n)) : Prop :=
  ∃ i j e, k ≤ i ∧ ssGet T i j = some e ∧ e.1 = g

/-- The product of any two entries sifts through. -/
def SsClosed (B : List (Fin n)) (T : List (SsSlot n)) : Prop :=
  ∀ i j e i' j' e', ssGet T i j = some e → ssGet T i' j' = some e' →
    ssThru T B 0 (e.1 * e'.1) = true

section Closed

variable {B : List (Fin n)} {T : List (SsSlot n)}

/-- If level `i` is closed under left multiplication by entries of levels `≥ i`, it is closed
under multiplication: write the left factor as a product of entries (`ssS_decomp`). -/
theorem ssS_mul_of_left (hB : ∀ x, x ∈ B) (hwf : SsWF B T) {i : ℕ}
    (hleft : ∀ s, SsEnt T i s → ∀ g ∈ ssS B T i, s * g ∈ ssS B T i)
    {g' : Perm (Fin n)} (hg' : g' ∈ ssS B T i) :
    ∀ d j, B.length - j = d → i ≤ j → ∀ h ∈ ssS B T j, h * g' ∈ ssS B T i := by
  intro d
  induction d with
  | zero =>
    intro j hd hij h hh
    have hj : j = B.length ∨ B.length < j := by omega
    rcases hj with rfl | hj
    · rw [ssS_length hB hh, one_mul]; exact hg'
    · rw [mem_ssS, List.take_of_length_le hj.le] at hh
      have : h = 1 := by ext x; simp [hh.1 x (hB x)]
      rw [this, one_mul]; exact hg'
  | succ d ih =>
    intro j hd hij h hh
    have hj : j < B.length := by omega
    rcases ssS_decomp hwf hj hh with h1 | ⟨k, e, he, h1⟩
    · exact ih (j + 1) (by omega) (by omega) h h1
    · have h2 := ih (j + 1) (by omega) (by omega) _ h1
      have h3 := hleft e.1 ⟨j, k, e, hij, he, rfl⟩ _ h2
      rwa [← mul_assoc, mul_inv_cancel_left] at h3

/-- **Closure.** For a closed table, every level is closed under multiplication. -/
theorem ssS_mul_closed (hB : ∀ x, x ∈ B) (hwf : SsWF B T) (hc : SsClosed B T) :
    ∀ i ≤ B.length, ∀ g ∈ ssS B T i, ∀ g' ∈ ssS B T i, g * g' ∈ ssS B T i := by
  intro i hi
  induction h : B.length - i generalizing i with
  | zero =>
    obtain rfl : i = B.length := by omega
    intro g hg g' hg'
    rw [ssS_length hB hg, one_mul]; exact hg'
  | succ d ih =>
    have hiL : i < B.length := by omega
    have hmul := ih (i + 1) (by omega) (by omega)
    -- left multiplication by entries of levels `≥ i`
    have hleft : ∀ s, SsEnt T i s → ∀ g ∈ ssS B T i, s * g ∈ ssS B T i := by
      rintro s ⟨k, j, es, hik, hes, rfl⟩ g hg
      -- `g = t * h` with `t` an entry of level `i` or `1`
      obtain ⟨t, ht, hth⟩ : ∃ t : Perm (Fin n), (t = 1 ∨ ∃ j e, ssGet T i j = some e ∧ e.1 = t) ∧
          t⁻¹ * g ∈ ssS B T (i + 1) := by
        rcases ssS_decomp hwf hiL hg with h1 | ⟨j, e, he, h1⟩
        · exact ⟨1, Or.inl rfl, by rw [inv_one, one_mul]; exact h1⟩
        · exact ⟨e.1, Or.inr ⟨j, e, he, rfl⟩, h1⟩
      -- `u = s * t` is in level `i`
      have hu : es.1 * t ∈ ssS B T i := by
        rcases ht with rfl | ⟨j', e', he', rfl⟩
        · rw [mul_one]; exact entry_mem_ssS hwf hes hik
        · obtain ⟨hk, hfk, -⟩ := hwf.slot _ _ _ hes
          obtain ⟨_, hfi, -⟩ := hwf.slot _ _ _ he'
          refine mem_ssS_of_thru hiL.le (hc _ _ _ _ _ _ hes he') fun b hb => ?_
          have hb' : b ∈ B.take k := List.take_subset_take_left _ hik hb
          rw [Perm.mul_apply, hfi b hb, hfk b hb']
      have key : es.1 * g = (es.1 * t) * (t⁻¹ * g) := by group
      rw [key]
      rcases ssS_decomp hwf hiL hu with h1 | ⟨j', e', he', h1⟩
      · exact ssS_succ_subset hiL (hmul _ h1 _ hth)
      · have h2 := ssS_mul_entry hwf he' (hmul _ h1 _ hth)
        rwa [← mul_assoc, mul_inv_cancel_left] at h2
    intro g hg g' hg'
    exact ssS_mul_of_left hB hwf hleft hg' _ i rfl le_rfl g hg

/-- Every element of level `i` is a product of entries of levels `≥ i`. -/
theorem ssS_le_closure (hB : ∀ x, x ∈ B) (hwf : SsWF B T) :
    ∀ i ≤ B.length, ∀ g ∈ ssS B T i, g ∈ Subgroup.closure {g | SsEnt T i g} := by
  intro i hi
  induction h : B.length - i generalizing i with
  | zero =>
    obtain rfl : i = B.length := by omega
    intro g hg
    rw [ssS_length hB hg]; exact Subgroup.one_mem _
  | succ d ih =>
    have hiL : i < B.length := by omega
    have hmono : Subgroup.closure {g | SsEnt T (i + 1) g} ≤ Subgroup.closure {g | SsEnt T i g} :=
      Subgroup.closure_mono fun g ⟨k, j, e, hk, he, hg⟩ => ⟨k, j, e, by omega, he, hg⟩
    intro g hg
    rcases ssS_decomp hwf hiL hg with h1 | ⟨j, e, he, h1⟩
    · exact hmono (ih (i + 1) (by omega) (by omega) g h1)
    · have h2 := hmono (ih (i + 1) (by omega) (by omega) _ h1)
      have h3 : e.1 ∈ Subgroup.closure {g | SsEnt T i g} :=
        Subgroup.subset_closure ⟨i, j, e, le_rfl, he, rfl⟩
      have := Subgroup.mul_mem _ h3 h2
      rwa [mul_inv_cancel_left] at this

/-- A finite set of permutations that contains `1` and is closed under multiplication is a
subgroup. -/
noncomputable def ssSubgroup (s : Finset (Perm (Fin n))) (h1 : (1 : Perm (Fin n)) ∈ s)
    (hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) : Subgroup (Perm (Fin n)) :=
  let M : Submonoid (Perm (Fin n)) := ⟨⟨(s : Set (Perm (Fin n))), fun ha hb => hmul _ ha _ hb⟩, h1⟩
  { M with
    inv_mem' := fun {a} ha => by
      obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (y := a⁻¹) (x := a)).mpr
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
      rw [← hk]
      exact M.pow_mem ha k }

theorem mem_ssSubgroup {s : Finset (Perm (Fin n))} {h1 : (1 : Perm (Fin n)) ∈ s}
    {hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s} {g : Perm (Fin n)} : g ∈ ssSubgroup s h1 hmul ↔ g ∈ s :=
  Iff.rfl

/-- **Levels of a closed table.** For a closed table whose base contains every point, level `i`
is the subgroup generated by the entries of levels `≥ i`. -/
theorem ss_level_eq (hB : ∀ x, x ∈ B) (hwf : SsWF B T) (hc : SsClosed B T) {i : ℕ}
    (hi : i ≤ B.length) (g : Perm (Fin n)) :
    g ∈ ssS B T i ↔ g ∈ Subgroup.closure {g | SsEnt T i g} := by
  refine ⟨ssS_le_closure hB hwf i hi g, fun hg => ?_⟩
  have hsub : Subgroup.closure {g | SsEnt T i g} ≤
      ssSubgroup (ssS B T i) one_mem_ssS (ssS_mul_closed hB hwf hc i hi) :=
    (Subgroup.closure_le _).mpr fun s ⟨k, j, e, hk, he, hs⟩ => by
      rw [← hs]; exact entry_mem_ssS hwf he hk
  exact hsub hg

/-- **Membership.** Let the table be closed and well formed, with a base that contains every
point. If its entries lie in `⟨gs⟩` and every generator sifts through, then a permutation lies in
`⟨gs⟩` exactly when it sifts through. -/
theorem ss_mem_gens_iff (hB : ∀ x, x ∈ B) (hwf : SsWF B T) (hc : SsClosed B T)
    {gs : List (Perm (Fin n))} (hent : ∀ i j e, ssGet T i j = some e → e.1 ∈ gens gs)
    (hgen : ∀ g ∈ gs, ssThru T B 0 g = true) (x : Perm (Fin n)) :
    x ∈ gens gs ↔ x ∈ ssS B T 0 := by
  have hgen' : gens gs ≤ ssSubgroup (ssS B T 0) one_mem_ssS
      (ssS_mul_closed hB hwf hc 0 (Nat.zero_le _)) :=
    (Subgroup.closure_le _).mpr fun g hg =>
      mem_ssS_of_thru (Nat.zero_le _) (hgen g hg) (by simp)
  have hle : Subgroup.closure {g | SsEnt T 0 g} ≤ gens gs :=
    (Subgroup.closure_le _).mpr fun s ⟨k, j, e, _, he, hs⟩ => by rw [← hs]; exact hent _ _ _ he
  exact ⟨fun h => hgen' h, fun h => hle (ssS_le_closure hB hwf 0 (Nat.zero_le _) x h)⟩

end Closed

end GI.Proved
