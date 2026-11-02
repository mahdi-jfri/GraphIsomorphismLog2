import Workspace.Impl.TermJProgYg
import Workspace.Impl.TermStep
import Workspace.Impl.TermJData

/-!
# The table `O` from the stored `N`-tests

The table programs (`tmJ_lg_spec`, `tmJ_tl_spec`, `tmJ_beta_spec`, `tmJ_ns_spec`) read the
`N`-test answers `us` through a table `O a a'` of the tests `(x_a, x_{a'})`: entry
`a (2q) + a'` of `us` is `tmJEntVal (O a a')`. This file builds `O` from the answers.

* `tmJOOf us q a a'`: the decoded entry (`none` for an empty answer).
* `tmJO_hus`: the entries of `us` are `tmJEntVal (O a a')`.
* `tmJO_some`, `tmJO_none`: what an entry says about the test `T (inl a, inl a')`.
* `tmJO_diag`: a diagonal test that is a subgroup `K` gives an entry `(r, gs)` with
  `⟨gs⟩ = K` and `r ∈ K` (`tmJ_coset_of_subgroup`).
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv
open GI.Cited (Val encPerm encGroup gens)
open scoped Pointwise

variable {m q : ℕ}

/-- **The entry `(a, a')` of the table**, decoded from the stored answers. -/
noncomputable def tmJOOf (us : List Val) (q : ℕ) (a a' : Fin q) :
    Option (Perm (Fin m) × List (Perm (Fin m))) := by
  classical
  exact if h : ∃ p : Perm (Fin m) × List (Perm (Fin m)),
      us[(a : ℕ) * (2 * q) + a']? = some (.list [encPerm p.1, encGroup p.2])
    then some h.choose else none

theorem tmJEntVal_some (p : Perm (Fin m) × List (Perm (Fin m))) :
    tmJEntVal (some p) = .list [encPerm p.1, encGroup p.2] := by
  obtain ⟨r, gs⟩ := p; rfl

/-- The test `(x_a, x_{a'})` sits at entry `a (2q) + a'` of the program's order. -/
theorem tmJO_test (a a' : Fin q) :
    (tmTests q)[(a : ℕ) * (2 * q) + a']? = some (.inl a, .inl a') := by
  have ha := a.2
  have ha' := a'.2
  have hj : (a : ℕ) * (2 * q) + a' < 4 * q ^ 2 := by
    have : (a : ℕ) * (2 * q) + a' < (a + 1) * (2 * q) := by
      rw [Nat.add_mul, one_mul]; omega
    have h2 : (a + 1) * (2 * q) ≤ q * (2 * q) := Nat.mul_le_mul_right _ ha
    have e : q * (2 * q) = 2 * q ^ 2 := by ring
    omega
  obtain ⟨h1, h2, he⟩ := tmTests_getElem? q _ hj
  have hq : 0 < 2 * q := by omega
  have hd : ((a : ℕ) * (2 * q) + a') / (2 * q) = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt (by omega), zero_add]
  have hm : ((a : ℕ) * (2 * q) + a') % (2 * q) = a' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [he]
  congr 2
  · unfold tmRowAt; simp only [hd, dif_pos ha]
  · unfold tmRowAt; simp only [hm, dif_pos ha']

variable {T : (Fin q ⊕ Fin q) × (Fin q ⊕ Fin q) → Set (Perm (Fin m))} {us : List Val}

/-- The stored answer of the test `(x_a, x_{a'})`. -/
theorem tmJO_entry (hus : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (T ac)) us
    (tmTests q)) (a a' : Fin q) :
    ∃ u, us[(a : ℕ) * (2 * q) + a']? = some u ∧ AnsC (Equiv.refl (Fin m)) u (T (.inl a, .inl a')) := by
  have ht := tmJO_test (q := q) a a'
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ht
  have hl := hus.length_eq
  have hlt' : (a : ℕ) * (2 * q) + a' < us.length := by rw [hl]; exact hlt
  refine ⟨us[(a : ℕ) * (2 * q) + a'], List.getElem?_eq_getElem hlt', ?_⟩
  have h := (List.forall₂_iff_get.1 hus).2 _ hlt' hlt
  have e : (tmTests q)[(a : ℕ) * (2 * q) + a'] = (.inl a, .inl a') := by
    have := List.getElem?_eq_getElem hlt
    rw [ht] at this
    exact (Option.some.inj this).symm
  simp only [List.get_eq_getElem] at h
  rw [e] at h
  exact h

theorem tmJO_hus (hus : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (T ac)) us
    (tmTests q)) (a a' : Fin q) :
    us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (tmJOOf (m := m) us q a a')) := by
  classical
  obtain ⟨u, hu, hA⟩ := tmJO_entry hus a a'
  rcases hA with ⟨rfl, -⟩ | ⟨x, gs, rfl, -, -⟩
  · have hn : ¬ ∃ p : Perm (Fin m) × List (Perm (Fin m)),
        us[(a : ℕ) * (2 * q) + a']? = some (.list [encPerm p.1, encGroup p.2]) := by
      rintro ⟨p, hp⟩
      rw [hu] at hp
      simp at hp
    unfold tmJOOf
    rw [dif_neg hn, hu]
    rfl
  · have hex : ∃ p : Perm (Fin m) × List (Perm (Fin m)),
        us[(a : ℕ) * (2 * q) + a']? = some (.list [encPerm p.1, encGroup p.2]) := ⟨(x, gs), hu⟩
    unfold tmJOOf
    rw [dif_pos hex]
    exact hex.choose_spec.trans (by rw [tmJEntVal_some])

/-- **A nonempty entry is the stored coset.** -/
theorem tmJO_some (hus : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (T ac)) us
    (tmTests q)) {a a' : Fin q} {r : Perm (Fin m)} {gs : List (Perm (Fin m))}
    (h : tmJOOf us q a a' = some (r, gs)) :
    T (.inl a, .inl a') = r • (gens gs : Set (Perm (Fin m))) ∧ gs.length ≤ m ^ 2 := by
  obtain ⟨u, hu, hA⟩ := tmJO_entry hus a a'
  have hu' := tmJO_hus hus a a'
  rw [h, hu] at hu'
  obtain rfl := Option.some.inj hu'
  rcases hA with ⟨he, -⟩ | ⟨x, gs', he, hl, hT⟩
  · simp [tmJEntVal] at he
  · simp only [tmJEntVal, Val.list.injEq, List.cons.injEq, and_true] at he
    obtain rfl := encPerm_injective he.1
    obtain rfl := encGroup_injective he.2
    refine ⟨?_, hl⟩
    rw [← hT]
    ext σ
    simp [toFin, Equiv.permCongr]

/-- **An empty entry is an empty test.** -/
theorem tmJO_none (hus : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (T ac)) us
    (tmTests q)) {a a' : Fin q} (h : tmJOOf (m := m) us q a a' = none) : T (.inl a, .inl a') = ∅ := by
  obtain ⟨u, hu, hA⟩ := tmJO_entry hus a a'
  have hu' := tmJO_hus hus a a'
  rw [h, hu] at hu'
  obtain rfl := Option.some.inj hu'
  rcases hA with ⟨-, he⟩ | ⟨x, gs', he, -, -⟩
  · exact he
  · simp [tmJEntVal] at he

/-- **A diagonal test that is a subgroup** gives an entry `(r, gs)` with `⟨gs⟩ = K`, `r ∈ K`. -/
theorem tmJO_diag (hus : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (T ac)) us
    (tmTests q)) (a : Fin q) {K : Subgroup (Perm (Fin m))}
    (hK : T (.inl a, .inl a) = (K : Set (Perm (Fin m)))) :
    ∃ r gs, tmJOOf us q a a = some (r, gs) ∧ gens gs = K ∧ r ∈ K ∧ gs.length ≤ m ^ 2 := by
  cases hO : tmJOOf us q a a with
  | none =>
    have := tmJO_none hus hO
    rw [hK] at this
    exact absurd (this ▸ K.one_mem : (1 : Perm (Fin m)) ∈ (∅ : Set (Perm (Fin m)))) (by simp)
  | some p =>
    obtain ⟨r, gs⟩ := p
    obtain ⟨hT, hl⟩ := tmJO_some hus hO
    rw [hK] at hT
    have hT' : (K : Set (Perm (Fin m))) = (r * ·) '' (gens gs : Set (Perm (Fin m))) := by
      rw [hT]; rfl
    obtain ⟨h1, h2⟩ := tmJ_coset_of_subgroup hT'
    exact ⟨r, gs, rfl, h1, h2, hl⟩

end GI.Impl
