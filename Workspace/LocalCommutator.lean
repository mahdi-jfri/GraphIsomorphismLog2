module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Dedup
public import Aesop

@[expose] public section

/-! Lemma A.16: localization of a commutator whose two supports meet in A.
The paper uses right point actions. In mathlib's function-composition convention,
its `g^-1 h^-1 g h` is the permutation `h * g * h^-1 * g^-1` below. -/

namespace GI
variable {V : Type*}

def localIntersection (g h : Equiv.Perm V) (a : V) : Prop :=
  g a ≠ a ∧ h a ≠ a

def LocalSeparated (g h : Equiv.Perm V) : Prop :=
  (∀ a, localIntersection g h a → ¬localIntersection g h (g a)) ∧
  (∀ a, localIntersection g h a → ¬localIntersection g h (h a))

def rightLocalCommutator (g h : Equiv.Perm V) : Equiv.Perm V :=
  h * g * h⁻¹ * g⁻¹

theorem perm_moves_image (g : Equiv.Perm V) {a : V} (ha : g a ≠ a) :
    g (g a) ≠ g a := fun he => ha (g.injective he)

theorem perm_moves_inverse (g : Equiv.Perm V) {a : V} (ha : g a ≠ a) :
    g (g.symm a) ≠ g.symm a := by
  intro he
  apply ha
  simpa using congrArg g he

theorem perm_inverse_fixes (g : Equiv.Perm V) {a : V} (ha : g a = a) :
    g.symm a = a := by
  apply g.injective
  simpa using ha.symm

theorem local_fixes_g_image (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a : V} (ha : localIntersection g h a) : h (g a) = g a := by
  by_contra hn
  exact sep.1 a ha ⟨perm_moves_image g ha.1, hn⟩

theorem local_fixes_h_image (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a : V} (ha : localIntersection g h a) : g (h a) = h a := by
  by_contra hn
  exact sep.2 a ha ⟨hn, perm_moves_image h ha.2⟩

theorem local_fixes_g_inverse (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a : V} (ha : localIntersection g h a) : h (g.symm a) = g.symm a := by
  by_contra hn
  have hp : localIntersection g h (g.symm a) := ⟨perm_moves_inverse g ha.1, hn⟩
  exact sep.1 _ hp (by simpa using ha)

theorem local_fixes_h_inverse (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a : V} (ha : localIntersection g h a) : g (h.symm a) = h.symm a := by
  by_contra hn
  have hp : localIntersection g h (h.symm a) := ⟨hn, perm_moves_inverse h ha.2⟩
  exact sep.2 _ hp (by simpa using ha)

theorem local_commutator_first (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a : V} (ha : localIntersection g h a) : rightLocalCommutator g h a = h a := by
  have hi := perm_inverse_fixes h (local_fixes_g_inverse g h sep ha)
  change h (g (h.symm (g.symm a))) = h a
  rw [hi, g.apply_symm_apply]

theorem local_commutator_second (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a : V} (ha : localIntersection g h a) : rightLocalCommutator g h (h a) = g a := by
  have hi := perm_inverse_fixes g (local_fixes_h_image g h sep ha)
  change h (g (h.symm (g.symm (h a)))) = g a
  rw [hi, h.symm_apply_apply, local_fixes_g_image g h sep ha]

theorem local_commutator_third (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a : V} (ha : localIntersection g h a) : rightLocalCommutator g h (g a) = a := by
  change h (g (h.symm (g.symm (g a)))) = a
  rw [g.symm_apply_apply, local_fixes_h_inverse g h sep ha, h.apply_symm_apply]

/-- Outside A, g(A), and h(A), the commutator is the identity. -/
theorem local_commutator_outside (g h : Equiv.Perm V) {v : V}
    (hv : ¬localIntersection g h v)
    (hgv : ¬localIntersection g h (g.symm v))
    (hhv : ¬localIntersection g h (h.symm v)) :
    rightLocalCommutator g h v = v := by
  change h (g (h.symm (g.symm v))) = v
  by_cases hg : g v = v
  · rw [perm_inverse_fixes g hg]
    by_cases hh : h v = v
    · rw [perm_inverse_fixes h hh, hg, hh]
    · have hfix : g (h.symm v) = h.symm v := by
        by_contra hn
        exact hhv ⟨hn, perm_moves_inverse h hh⟩
      rw [hfix, h.apply_symm_apply]
  · have hh : h v = v := by
      by_contra hn
      exact hv ⟨hg, hn⟩
    have hfix : h (g.symm v) = g.symm v := by
      by_contra hn
      exact hgv ⟨perm_moves_inverse g hg, hn⟩
    rw [perm_inverse_fixes h hfix, g.apply_symm_apply, hh]

def localTriple (g h : Equiv.Perm V) (a : V) : Set V := {a, h a, g a}

theorem local_triple_distinct (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a : V} (ha : localIntersection g h a) : a ≠ h a ∧ a ≠ g a ∧ h a ≠ g a := by
  refine ⟨Ne.symm ha.2, Ne.symm ha.1, ?_⟩
  intro he
  have hg := local_fixes_h_image g h sep ha
  rw [he] at hg
  exact perm_moves_image g ha.1 hg

theorem local_triples_disjoint (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a b : V} (ha : localIntersection g h a) (hb : localIntersection g h b) (hab : a ≠ b) :
    Disjoint (localTriple g h a) (localTriple g h b) := by
  have hahb : a ≠ h b := by
    intro he
    exact sep.2 b hb (he ▸ ha)
  have hagb : a ≠ g b := by
    intro he
    exact sep.1 b hb (he ▸ ha)
  have hhab : h a ≠ b := by
    intro he
    exact sep.2 a ha (he.symm ▸ hb)
  have hgab : g a ≠ b := by
    intro he
    exact sep.1 a ha (he.symm ▸ hb)
  have hhh : h a ≠ h b := fun he => hab (h.injective he)
  have hgg : g a ≠ g b := fun he => hab (g.injective he)
  have hhg : h a ≠ g b := by
    intro he
    have hfix := local_fixes_h_image g h sep ha
    rw [he] at hfix
    exact perm_moves_image g hb.1 hfix
  have hgh : g a ≠ h b := by
    intro he
    have hfix := local_fixes_g_image g h sep ha
    rw [he] at hfix
    exact perm_moves_image h hb.2 hfix
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [localTriple, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  aesop

theorem local_separated_of_supports (g h : Equiv.Perm V) (A : Set V)
    (hA : ∀ a, a ∈ A ↔ localIntersection g h a)
    (hg : Disjoint (g '' A) A) (hh : Disjoint (h '' A) A) : LocalSeparated g h := by
  constructor
  · intro a ha hga
    exact Set.disjoint_left.mp hg (Set.mem_image_of_mem g ((hA a).2 ha)) ((hA _).2 hga)
  · intro a ha hha
    exact Set.disjoint_left.mp hh (Set.mem_image_of_mem h ((hA a).2 ha)) ((hA _).2 hha)

section Cycles
variable [DecidableEq V]

/-- The cycle `(a, h(a), g(a))`, written using mathlib permutation multiplication. -/
def localThreeCycle (g h : Equiv.Perm V) (a : V) : Equiv.Perm V :=
  Equiv.swap a (g a) * Equiv.swap a (h a)

theorem local_cycle_first (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a : V} (ha : localIntersection g h a) : localThreeCycle g h a a = h a := by
  obtain ⟨hah, _, hhg⟩ := local_triple_distinct g h sep ha
  simp [localThreeCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Ne.symm hah, hhg]

theorem local_cycle_second (g h : Equiv.Perm V) (_sep : LocalSeparated g h)
    {a : V} (_ha : localIntersection g h a) : localThreeCycle g h a (h a) = g a := by
  simp [localThreeCycle, Equiv.Perm.mul_apply]

theorem local_cycle_third (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a : V} (ha : localIntersection g h a) : localThreeCycle g h a (g a) = a := by
  obtain ⟨_, hag, hhg⟩ := local_triple_distinct g h sep ha
  simp [localThreeCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Ne.symm hag, Ne.symm hhg]

theorem local_cycle_outside (g h : Equiv.Perm V) (a x : V)
    (hx : x ∉ localTriple g h a) : localThreeCycle g h a x = x := by
  have hn : x ≠ a ∧ x ≠ h a ∧ x ≠ g a := by
    simpa only [localTriple, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hx
  simp [localThreeCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hn.1, hn.2.1, hn.2.2]

/-- Each factor has exactly the advertised three-point support. -/
theorem local_cycle_moves_iff (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a x : V} (ha : localIntersection g h a) :
    localThreeCycle g h a x ≠ x ↔ x ∈ localTriple g h a := by
  constructor
  · intro hn
    by_contra hx
    exact hn (local_cycle_outside g h a x hx)
  · intro hx
    obtain ⟨hah, hag, hhg⟩ := local_triple_distinct g h sep ha
    simp only [localTriple, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [local_cycle_first g h sep ha]
      exact Ne.symm hah
    · rw [local_cycle_second g h sep ha]
      exact Ne.symm hhg
    · rw [local_cycle_third g h sep ha]
      exact hag

/-- Distinct factors have disjoint supports, stated directly as moved-point sets. -/
theorem local_cycles_disjoint (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a b : V} (ha : localIntersection g h a) (hb : localIntersection g h b) (hab : a ≠ b) :
    Disjoint {x | localThreeCycle g h a x ≠ x} {x | localThreeCycle g h b x ≠ x} := by
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  exact Set.disjoint_left.mp (local_triples_disjoint g h sep ha hb hab)
    ((local_cycle_moves_iff g h sep ha).1 hxa) ((local_cycle_moves_iff g h sep hb).1 hxb)

theorem local_cycle_preserves_triple (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a x : V} (ha : localIntersection g h a) (hx : x ∈ localTriple g h a) :
    localThreeCycle g h a x ∈ localTriple g h a := by
  simp only [localTriple, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl
  · exact Or.inr (Or.inl (local_cycle_first g h sep ha))
  · exact Or.inr (Or.inr (local_cycle_second g h sep ha))
  · exact Or.inl (local_cycle_third g h sep ha)

theorem local_cycle_matches_commutator (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    {a x : V} (ha : localIntersection g h a) (hx : x ∈ localTriple g h a) :
    localThreeCycle g h a x = rightLocalCommutator g h x := by
  simp only [localTriple, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [local_cycle_first g h sep ha, local_commutator_first g h sep ha]
  · rw [local_cycle_second g h sep ha, local_commutator_second g h sep ha]
  · rw [local_cycle_third g h sep ha, local_commutator_third g h sep ha]

omit [DecidableEq V] in
theorem list_perm_product_fixes {I : Type*} (l : List I) (p : I → Equiv.Perm V) (x : V)
    (hf : ∀ a ∈ l, p a x = x) : (l.map p).prod x = x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    rw [ih (fun b hb => hf b (List.mem_cons_of_mem a hb))]
    exact hf a List.mem_cons_self

omit [DecidableEq V] in
theorem list_perm_product_single {I : Type*} (l : List I) (p : I → Equiv.Perm V)
    (a : I) (x : V) (ha : a ∈ l) (hn : l.Nodup)
    (hf : ∀ b ∈ l, b ≠ a → p b x = x ∧ p b (p a x) = p a x) :
    (l.map p).prod x = p a x := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    obtain ⟨hbn, hln⟩ := List.nodup_cons.mp hn
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    by_cases hba : b = a
    · subst b
      rw [list_perm_product_fixes l p x]
      intro b hb
      exact (hf b (List.mem_cons_of_mem a hb) (fun he => hbn (he ▸ hb))).1
    · have hal : a ∈ l := (List.mem_cons.mp ha).resolve_left (Ne.symm hba)
      rw [ih hal hln (fun c hc => hf c (List.mem_cons_of_mem b hc))]
      exact (hf b List.mem_cons_self hba).2

/-- Full product formula of Lemma A.16. Any repetition-free enumeration of A works.
Together with `local_triples_disjoint`, the factors are disjoint three-cycles. -/
theorem local_commutator_cycle_product (g h : Equiv.Perm V) (sep : LocalSeparated g h)
    (l : List V) (hn : l.Nodup)
    (hl : ∀ a, a ∈ l ↔ localIntersection g h a) :
    rightLocalCommutator g h = (l.map (localThreeCycle g h)).prod := by
  ext x
  by_cases hx : ∃ a ∈ l, x ∈ localTriple g h a
  · obtain ⟨a, hal, hxa⟩ := hx
    have ha := (hl a).1 hal
    have hp : (l.map (localThreeCycle g h)).prod x = localThreeCycle g h a x := by
      apply list_perm_product_single l (localThreeCycle g h) a x hal hn
      intro b hbl hba
      have hd := local_triples_disjoint g h sep ha ((hl b).1 hbl) (Ne.symm hba)
      have hnot : x ∉ localTriple g h b := fun hxb => Set.disjoint_left.mp hd hxa hxb
      have hout := local_cycle_preserves_triple g h sep ha hxa
      exact ⟨local_cycle_outside g h b x hnot,
        local_cycle_outside g h b _ (fun hb' => Set.disjoint_left.mp hd hout hb')⟩
    rw [hp, local_cycle_matches_commutator g h sep ha hxa]
  · have hprod : (l.map (localThreeCycle g h)).prod x = x := by
      apply list_perm_product_fixes
      intro a hal
      exact local_cycle_outside g h a x (fun hxa => hx ⟨a, hal, hxa⟩)
    have h0 : ¬localIntersection g h x := by
      intro h
      exact hx ⟨x, (hl x).2 h, by simp [localTriple]⟩
    have hg : ¬localIntersection g h (g.symm x) := by
      intro h
      exact hx ⟨g.symm x, (hl _).2 h, by simp [localTriple]⟩
    have hh : ¬localIntersection g h (h.symm x) := by
      intro h'
      exact hx ⟨h.symm x, (hl _).2 h', by simp [localTriple]⟩
    rw [local_commutator_outside g h h0 hg hh, hprod]

/-- Lemma A.16 stated with the paper's support-intersection and image-disjointness
hypotheses. The finite set A may live in an infinite ambient type. -/
theorem block_local_clean_commutator (g h : Equiv.Perm V) (A : Finset V)
    (hA : ∀ a, a ∈ A ↔ g a ≠ a ∧ h a ≠ a)
    (hg : Disjoint (g '' (A : Set V)) (A : Set V))
    (hh : Disjoint (h '' (A : Set V)) (A : Set V)) :
    rightLocalCommutator g h = (A.toList.map (localThreeCycle g h)).prod := by
  have hA' : ∀ a, a ∈ (A : Set V) ↔ localIntersection g h a := hA
  have sep := local_separated_of_supports g h (A : Set V) hA' hg hh
  apply local_commutator_cycle_product g h sep A.toList A.nodup_toList
  intro a
  rw [Finset.mem_toList]
  exact hA a

omit [DecidableEq V] in
/-- The cycles in the preceding product are pairwise supported on disjoint triples. -/
theorem block_local_clean_commutator_disjoint (g h : Equiv.Perm V) (A : Finset V)
    (hA : ∀ a, a ∈ A ↔ g a ≠ a ∧ h a ≠ a)
    (hg : Disjoint (g '' (A : Set V)) (A : Set V))
    (hh : Disjoint (h '' (A : Set V)) (A : Set V))
    {a b : V} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    Disjoint (localTriple g h a) (localTriple g h b) := by
  have hA' : ∀ a, a ∈ (A : Set V) ↔ localIntersection g h a := hA
  exact local_triples_disjoint g h
    (local_separated_of_supports g h (A : Set V) hA' hg hh)
    ((hA a).1 ha) ((hA b).1 hb) hab

end Cycles
end GI
