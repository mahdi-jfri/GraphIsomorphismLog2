import Workspace.Cited.AlgoPermGroups
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Checks for the algorithm tasks

Small facts about the tasks: input bounds, totality (every instance has a
correct output within the output bounds of the task) and output sizes for the tasks of
`Workspace/Cited/Algo*.lean`. The harder totality proofs are in
`Workspace/CitedChecks/AlgoTotality.lean`. Nothing here is trusted.
-/

namespace GI.CitedChecks

open GI.Cited Equiv

/-- The cells of a list of numbers: two per number. -/
theorem cellsList_map_nat (l : List ℕ) :
    (Val.cellsList (l.map Val.nat)).length = 2 * l.length := by
  induction l with
  | nil => simp [Val.cellsList]
  | cons a l ih =>
    simp only [List.map_cons, Val.cellsList, List.length_append, ih, Val.cells,
      List.length_cons, List.length_nil]
    ring

/-- A permutation of `Fin n` takes `2 n + 3` cells. -/
theorem encPerm_length {n : ℕ} (σ : Perm (Fin n)) : (encPerm σ).cells.length = 2 * n + 3 := by
  have h := cellsList_map_nat ((List.finRange n).map fun i => (σ i : ℕ))
  simp only [List.map_map, List.length_map, List.length_finRange] at h
  simp only [encPerm, Val.cells, List.length_append, List.length_cons, List.length_nil]
  rw [show ((List.finRange n).map fun i => Val.nat (σ i)) =
    ((List.finRange n).map (Val.nat ∘ fun i => (σ i : ℕ))) from rfl, h]
  ring

/-- The cells of a list of values contain the cells of its first entry. -/
theorem cellsList_cons_length (v : Val) (vs : List Val) :
    v.cells.length ≤ (Val.cellsList (v :: vs)).length := by
  simp [Val.cellsList]

/-- **Input bound for groups.** The degree is at most the number of cells of `encGroup gs`, even
when `gs = []`: this is why the identity is prepended. -/
theorem n_le_encGroup {n : ℕ} (gs : List (Perm (Fin n))) : n ≤ (encGroup gs).cells.length := by
  have h1 : (encPerm (1 : Perm (Fin n))).cells.length ≤
      (Val.cellsList ((1 :: gs).map encPerm)).length := by
    rw [List.map_cons]; exact cellsList_cons_length _ _
  have h2 : (Val.list ((1 :: gs).map encPerm)).cells.length ≤
      (Val.cellsList [Val.nat n, Val.list ((1 :: gs).map encPerm)]).length := by
    simp [Val.cellsList]
  rw [encPerm_length] at h1
  simp only [encGroup, encPerms, Val.cells, List.length_append, List.length_cons,
    List.length_nil] at h1 h2 ⊢
  omega

/-! ### Generating lists of at most `n²` permutations -/

/-- A proper subgroup has at most half the order (Lagrange). -/
theorem two_mul_card_le_of_lt {G : Type*} [Group G] [Finite G] {K K' : Subgroup G} (h : K < K') :
    2 * Nat.card K ≤ Nat.card K' := by
  obtain ⟨q, hq⟩ := Subgroup.card_dvd_of_le h.le
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hne : Nat.card K' ≠ Nat.card K := fun e =>
    h.ne (Subgroup.eq_of_le_of_card_ge h.le e.le)
  rcases q with _ | _ | q
  · have : 0 < Nat.card K' := Nat.card_pos
    simp at hq; omega
  · simp at hq; exact absurd hq hne
  · rw [hq]; nlinarith

/-- **The doubling argument.** Every subgroup `H` of a finite group has a generating list `l`
with `2 ^ l.length ≤ |H|`. Add generators of `H` one at a time, each outside the group generated
so far; each one at least doubles its order (`two_mul_card_le_of_lt`). The induction is on
`|H| - |K|` for the group `K` generated so far. -/
theorem exists_list_closure_eq {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    ∃ l : List G, Subgroup.closure {g | g ∈ l} = H ∧ 2 ^ l.length ≤ Nat.card H := by
  classical
  suffices h : ∀ d (l : List G), Subgroup.closure {g | g ∈ l} ≤ H →
      Nat.card H - Nat.card (Subgroup.closure {g | g ∈ l}) = d →
      2 ^ l.length ≤ Nat.card (Subgroup.closure {g | g ∈ l}) →
      ∃ l' : List G, Subgroup.closure {g | g ∈ l'} = H ∧ 2 ^ l'.length ≤ Nat.card H by
    refine h _ [] ?_ rfl ?_
    · simp
    · simp
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro l hle hd hcard
  by_cases heq : Subgroup.closure {g | g ∈ l} = H
  · exact ⟨l, heq, heq ▸ hcard⟩
  obtain ⟨h, hH, hK⟩ : ∃ h ∈ H, h ∉ Subgroup.closure {g | g ∈ l} := by
    by_contra hc
    push Not at hc
    exact heq (le_antisymm hle hc)
  have hKK' : Subgroup.closure {g | g ∈ l} ≤ Subgroup.closure {g | g ∈ h :: l} :=
    Subgroup.closure_mono fun g hg => List.mem_cons_of_mem _ hg
  have hhK' : h ∈ Subgroup.closure {g | g ∈ h :: l} :=
    Subgroup.subset_closure (List.mem_cons_self ..)
  have hK'H : Subgroup.closure {g | g ∈ h :: l} ≤ H := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hH
    · exact hle (Subgroup.subset_closure hg)
  have hlt := lt_of_le_of_ne hKK' fun e => hK (e ▸ hhK')
  have h2 := two_mul_card_le_of_lt hlt
  have h3 := Subgroup.card_le_of_le hK'H
  have h4 := Subgroup.card_le_of_le hle
  have hpos : 0 < Nat.card (Subgroup.closure {g | g ∈ l}) := Nat.card_pos
  refine ih _ (by omega) (h :: l) hK'H rfl ?_
  rw [List.length_cons, pow_succ]
  omega

/-- `n! ≤ n^n ≤ 2^(n²)`. -/
theorem card_perm_le (n : ℕ) : Nat.card (Perm (Fin n)) ≤ 2 ^ (n ^ 2) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  calc n.factorial ≤ n ^ n := Nat.factorial_le_pow n
    _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left Nat.lt_two_pow_self.le n
    _ = 2 ^ (n ^ 2) := by rw [← pow_mul, sq]

/-- The order of a subgroup of `Sym(n)` has at most `n² + 1` bits. -/
theorem card_lt_two_pow {n : ℕ} (H : Subgroup (Perm (Fin n))) : Nat.card H < 2 ^ (n ^ 2 + 1) := by
  have := Subgroup.card_le_of_le (le_top : H ≤ ⊤)
  rw [Subgroup.card_top] at this
  have := card_perm_le n
  have h1 : 1 ≤ 2 ^ n ^ 2 := Nat.one_le_two_pow
  rw [pow_succ]
  generalize 2 ^ n ^ 2 = B at *
  omega

/-- **Totality of every "generating list" output**: every subgroup of `Sym(n)` has a generating
list of at most `n²` permutations, by the doubling argument and `|H| < 2^(n² + 1)`. -/
theorem exists_gensOf {n : ℕ} (H : Subgroup (Perm (Fin n))) : ∃ v, GensOf H v := by
  obtain ⟨l, hl, hc⟩ := exists_list_closure_eq H
  refine ⟨_, l, rfl, ?_, hl⟩
  have := card_lt_two_pow H
  have h : 2 ^ l.length < 2 ^ (n ^ 2 + 1) := by omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h
  omega

/-- The cells of a list of permutations of `Fin n`. -/
theorem cells_list_encPerm_length {n : ℕ} (hs : List (Perm (Fin n))) :
    (Val.list (hs.map encPerm)).cells.length = hs.length * (2 * n + 3) + 3 := by
  have h : (Val.cellsList (hs.map encPerm)).length = hs.length * (2 * n + 3) := by
    induction hs with
    | nil => simp [Val.cellsList]
    | cons g hs ih =>
      simp only [List.map_cons, Val.cellsList, List.length_append, encPerm_length, ih,
        List.length_cons]
      ring
  simp only [Val.cells, List.length_append, List.length_cons, List.length_nil, h]
  ring

/-- **Output size of `GensOf`**: at most `n² (2n + 3) + 3` cells, a polynomial in `n`, and `n`
is at most the number of cells of every group input (`n_le_encGroup`). -/
theorem gensOf_cells_le {n : ℕ} {H : Subgroup (Perm (Fin n))} {v : Val} (h : GensOf H v) :
    v.cells.length ≤ n ^ 2 * (2 * n + 3) + 3 := by
  obtain ⟨hs, rfl, hl, -⟩ := h
  rw [cells_list_encPerm_length]
  have := Nat.mul_le_mul_right (2 * n + 3) hl
  omega

/-- **Input bound of `SylowTask`.** A prime dividing the order of a subgroup of `Sym(n)` is at
most `n`, so the number `p` in the input is at most the number of cells. -/
theorem sylowInst_p_le (I : SylowInst) : I.p ≤ I.n := by
  have h1 : Nat.card (gens I.gs) ∣ Nat.card (Perm (Fin I.n)) :=
    Subgroup.card_subgroup_dvd_card _
  rw [Nat.card_eq_fintype_card (α := Perm (Fin I.n)), Fintype.card_perm, Fintype.card_fin] at h1
  exact (Nat.Prime.dvd_factorial I.prime).1 (I.dvd.trans h1)

/-- The preimage set of `PreimageTask` is a subgroup, for every graph group `D` and every `M`
(with or without the hypotheses of `PreimageInst`). -/
def preimageSubgroup (I : PreimageInst) : Subgroup (Perm (Fin I.n)) where
  carrier := preimageSet I
  one_mem' := ⟨1, Subgroup.one_mem _, by
    rw [show Equiv.sumCongr (1 : Perm (Fin I.n)) (1 : Perm (Fin I.n')) = 1 from
      Equiv.Perm.sumCongr_one]
    exact Subgroup.one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, hha, hda⟩ ⟨hb, hhb, hdb⟩
    refine ⟨ha * hb, Subgroup.mul_mem _ hha hhb, ?_⟩
    have := Subgroup.mul_mem _ hda hdb
    rwa [Equiv.Perm.sumCongr_mul] at this
  inv_mem' := by
    rintro a ⟨ha, hha, hda⟩
    refine ⟨ha⁻¹, Subgroup.inv_mem _ hha, ?_⟩
    have := Subgroup.inv_mem _ hda
    rwa [Equiv.Perm.sumCongr_inv] at this

/-- **Totality of `PreimageTask`.** -/
theorem preimage_total (I : PreimageInst) :
    ∃ v : Val, ∃ hs : List (Perm (Fin I.n)), v = Val.list (hs.map encPerm) ∧
      hs.length ≤ I.n ^ 2 ∧ ((gens hs : Set (Perm (Fin I.n))) = preimageSet I) := by
  obtain ⟨v, hs, hv, hl, h⟩ := exists_gensOf (preimageSubgroup I)
  exact ⟨v, hs, hv, hl, by rw [h]; rfl⟩

/-- **Totality of `OrbitsTask`.** Label each point by the least point of its orbit; the labels
are points, so below `n`. -/
theorem orbits_total {n : ℕ} (G : Subgroup (Perm (Fin n))) :
    ∃ lab : Fin n → ℕ, (∀ i, lab i < n) ∧ IsOrbitLabeling G lab := by
  classical
  let R : Fin n → Fin n → Prop := fun i j => ∃ g ∈ G, g i = j
  have refl : ∀ i, R i i := fun i => ⟨1, G.one_mem, rfl⟩
  have symm : ∀ i j, R i j → R j i := by
    rintro i j ⟨g, hg, rfl⟩
    exact ⟨g⁻¹, G.inv_mem hg, by simp⟩
  have trans : ∀ i j l, R i j → R j l → R i l := by
    rintro i j l ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
    exact ⟨h * g, G.mul_mem hh hg, rfl⟩
  let rep : Fin n → Fin n := fun i =>
    (Finset.univ.filter fun j => R i j).min' ⟨i, by simp [refl i]⟩
  have rep_mem : ∀ i, R i (rep i) := fun i => by
    have := Finset.min'_mem (Finset.univ.filter fun j => R i j) ⟨i, by simp [refl i]⟩
    simpa using this
  have rep_eq : ∀ i j, R i j → rep i = rep j := by
    intro i j hij
    have hs : (Finset.univ.filter fun l => R i l) = Finset.univ.filter fun l => R j l := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => trans _ _ _ (symm _ _ hij) h, fun h => trans _ _ _ hij h⟩
    simp only [rep, hs]
  refine ⟨fun i => rep i, fun i => (rep i).isLt, fun i j => ⟨fun h => ?_, fun h => by
    simp only [rep_eq i j h]⟩⟩
  have h' : rep i = rep j := Fin.ext h
  exact trans _ _ _ (rep_mem i) (h' ▸ symm _ _ (rep_mem j))

end GI.CitedChecks
