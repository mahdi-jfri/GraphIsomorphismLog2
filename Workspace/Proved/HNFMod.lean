import Workspace.Cited.AlgoTerminal
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Order.Group.Int.Sum

/-!
# Hermite form modulo a multiple of the determinant

We want the Hermite form of a square integer matrix `M` while keeping all numbers small. The
tool is a number `m > 0` such that `m ℤ^n` lies in the row lattice `L` of `M`. Then adding
multiples of `m e_j` to a row does not change the lattice it helps generate, so all entries can
be kept in `[0, m]` (Domich–Kannan–Trotter).

The algorithm handles the columns `k = 0, …, n-1` in turn. It keeps finished rows `H` and
working rows `G`.
* Column `k` starts from the row `a = m e_k`. For each working row `g`, Euclid's algorithm on
  the pair `(a, g)`, keyed on column `k`, makes `g k = 0` (`hnfEuclid`). Each Euclid step is
  `(a, g) ↦ (g, a - ⌊a_k / g_k⌋ g)`, with the entries right of column `k` taken mod `m`
  (`hnfRed`).
* The final `a` is the new finished row. The earlier finished rows are reduced in column `k`
  modulo `a k`, again with the entries right of `k` taken mod `m`.

The invariant (`HnfModInv`) is `span (H ∪ G) ⊔ V_k = L`, where `V_k` is the set of vectors that
vanish before column `k` and are divisible by `m` (`hnfV`). At the end `V_n = 0` and `G = 0`, so
the rows `H` span `L`, and they are in Hermite form.

The result used later is `hnfModMat_spec`.
-/

namespace GI.Proved

open GI.Cited

variable {n : ℕ}

/-! ### Vectors divisible by `m` from column `k` on -/

/-- `V_k`: the vectors that vanish before column `k` and whose entries are divisible by `m`. -/
def hnfV (n : ℕ) (m : ℤ) (k : ℕ) : Submodule ℤ (Fin n → ℤ) where
  carrier := {v | (∀ j : Fin n, (j : ℕ) < k → v j = 0) ∧ ∀ j, m ∣ v j}
  add_mem' := by
    rintro a b ⟨ha0, ham⟩ ⟨hb0, hbm⟩
    exact ⟨fun j hj => by simp [ha0 j hj, hb0 j hj], fun j => dvd_add (ham j) (hbm j)⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ => dvd_zero _⟩
  smul_mem' := by
    rintro c a ⟨ha0, ham⟩
    exact ⟨fun j hj => by simp [ha0 j hj], fun j => by simpa using dvd_mul_of_dvd_right (ham j) c⟩

theorem hnfV_mono {m : ℤ} {k k' : ℕ} (h : k ≤ k') : hnfV n m k' ≤ hnfV n m k :=
  fun _ hv => ⟨fun j hj => hv.1 j (by omega), hv.2⟩

theorem hnfV_n (m : ℤ) : hnfV n m n = ⊥ := by
  ext v
  simp only [Submodule.mem_bot]
  refine ⟨fun hv => funext fun j => hv.1 j j.isLt, fun hv => hv ▸ (hnfV n m n).zero_mem⟩

/-- `m e_k` lies in `V_k`, and `V_k = span {m e_k} ⊔ V_{k+1}`. -/
theorem hnfV_split (m : ℤ) (k : Fin n) :
    hnfV n m k = Submodule.span ℤ {Pi.single k m} ⊔ hnfV n m (k + 1) := by
  apply le_antisymm
  · intro v hv
    have hk := hv.2 k
    obtain ⟨t, ht⟩ := hk
    have hw : v - t • Pi.single k m ∈ hnfV n m (k + 1) := by
      refine ⟨fun j hj => ?_, fun j => ?_⟩
      · by_cases hjk : j = k
        · subst hjk; simp [ht, mul_comm]
        · have : (j : ℕ) < k := by
            have : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
            omega
          simp [hv.1 j this, hjk]
      · by_cases hjk : j = k
        · subst hjk; simp [ht, mul_comm]
        · simpa [hjk] using hv.2 j
    have : v = t • Pi.single k m + (v - t • Pi.single k m) := by abel
    rw [this]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span rfl)) hw
  · refine sup_le ?_ (hnfV_mono (by omega))
    rw [Submodule.span_le]
    rintro _ rfl
    refine ⟨fun j hj => ?_, fun j => ?_⟩
    · have : j ≠ k := fun h => by subst h; omega
      simp [this]
    · by_cases hjk : j = k
      · subst hjk; simp
      · simp [hjk]

/-- A vector that vanishes up to column `k` and is divisible by `m` lies in `V_{k+1}`. -/
theorem hnfV_mem {m : ℤ} {k : ℕ} {v : Fin n → ℤ} (h0 : ∀ j : Fin n, (j : ℕ) ≤ k → v j = 0)
    (hm : ∀ j, m ∣ v j) : v ∈ hnfV n m (k + 1) :=
  ⟨fun j hj => h0 j (by omega), hm⟩

/-! ### Spans of lists of rows -/

/-- The lattice spanned by a list of rows. -/
def hnfSpan (L : List (Fin n → ℤ)) : Submodule ℤ (Fin n → ℤ) := Submodule.span ℤ {v | v ∈ L}

theorem hnfSpan_append (L L' : List (Fin n → ℤ)) :
    hnfSpan (L ++ L') = hnfSpan L ⊔ hnfSpan L' := by
  simp only [hnfSpan, List.mem_append]
  rw [← Submodule.span_union]
  rfl

theorem hnfSpan_cons (a : Fin n → ℤ) (L : List (Fin n → ℤ)) :
    hnfSpan (a :: L) = Submodule.span ℤ {a} ⊔ hnfSpan L := by
  rw [show a :: L = [a] ++ L from rfl, hnfSpan_append]
  simp [hnfSpan]

/-- Changing each row by an element of `W` does not change `span ⊔ W`. -/
theorem hnfSpan_map_sup (W : Submodule ℤ (Fin n → ℤ)) (f : (Fin n → ℤ) → Fin n → ℤ)
    (L : List (Fin n → ℤ)) (hf : ∀ h ∈ L, f h - h ∈ W) :
    hnfSpan (L.map f) ⊔ W = hnfSpan L ⊔ W := by
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rw [hnfSpan, Submodule.span_le]
    intro v hv
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hv
    have : f h = h + (f h - h) := by abel
    rw [SetLike.mem_coe, this]
    exact Submodule.add_mem_sup (Submodule.subset_span hh) (hf h hh)
  · refine sup_le ?_ le_sup_right
    rw [hnfSpan, Submodule.span_le]
    intro h hh
    have : h = f h - (f h - h) := by abel
    rw [SetLike.mem_coe, this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span
      (List.mem_map.mpr ⟨h, hh, rfl⟩))) (Submodule.mem_sup_right (hf h hh))

/-! ### The reduction and Euclid's algorithm on two rows -/

/-- `a - q g`, with the entries right of column `k` taken mod `m`. -/
def hnfRed (k : ℕ) (m : ℤ) (a g : Fin n → ℤ) (q : ℤ) : Fin n → ℤ :=
  fun j => if k < (j : ℕ) then (a j - q * g j) % m else a j - q * g j

theorem hnfRed_sub_mem {k : ℕ} {m : ℤ} (a g : Fin n → ℤ) (q : ℤ) :
    hnfRed k m a g q - (a - q • g) ∈ hnfV n m (k + 1) := by
  refine hnfV_mem (fun j hj => ?_) (fun j => ?_)
  · simp [hnfRed, show ¬ k < (j : ℕ) by omega]
  · simp only [hnfRed, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · rw [Int.emod_def]; simp
    · simp

theorem hnfRed_key (k : Fin n) (m : ℤ) (a g : Fin n → ℤ) (q : ℤ) :
    hnfRed k m a g q k = a k - q * g k := by
  simp [hnfRed]

/-- **Euclid's algorithm on two rows**, keyed on column `k`. -/
def hnfEuclid (k : Fin n) (m : ℤ) (a g : Fin n → ℤ) : (Fin n → ℤ) × (Fin n → ℤ) :=
  if h : g k = 0 then (a, g) else hnfEuclid k m g (hnfRed k m a g (a k / g k))
termination_by (g k).natAbs
decreasing_by
  rw [hnfRed_key, mul_comm, ← Int.emod_def]
  have h1 := Int.emod_nonneg (a k) h
  have h2 := Int.emod_lt (a k) h
  rw [Int.natCast_natAbs] at h2
  zify
  rw [abs_of_nonneg h1]
  exact h2

/-- The shape of the rows entering Euclid's algorithm at column `k`. -/
structure HnfPair (k : Fin n) (m : ℤ) (a g : Fin n → ℤ) : Prop where
  low : ∀ j : Fin n, (j : ℕ) < k → a j = 0 ∧ g j = 0
  akey : 0 < a k ∧ a k ≤ m
  gkey : 0 ≤ g k ∧ g k < m
  high : ∀ j : Fin n, (k : ℕ) < j → (0 ≤ a j ∧ a j < m) ∧ (0 ≤ g j ∧ g j < m)

/-- **Euclid's algorithm.** The result `(a', g')` has `g' k = 0`, keeps the shape, and spans
the same lattice together with `V_{k+1}`. -/
theorem hnfEuclid_spec (k : Fin n) {m : ℤ} (hm : 0 < m) :
    ∀ (N : ℕ) (a g : Fin n → ℤ), (g k).natAbs = N → HnfPair k m a g →
      HnfPair k m (hnfEuclid k m a g).1 (hnfEuclid k m a g).2 ∧ (hnfEuclid k m a g).2 k = 0 ∧
      Submodule.span ℤ {(hnfEuclid k m a g).1, (hnfEuclid k m a g).2} ⊔ hnfV n m (k + 1) =
        Submodule.span ℤ {a, g} ⊔ hnfV n m (k + 1) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a g hN hp
  unfold hnfEuclid
  by_cases hg : g k = 0
  · simp only [hg, dite_true]
    exact ⟨hp, trivial, trivial⟩
  · simp only [hg, dite_false]
    set a' := hnfRed k m a g (a k / g k) with ha'
    have hgpos : 0 < g k := lt_of_le_of_ne hp.gkey.1 (Ne.symm hg)
    have hkey : a' k = a k % g k := by
      rw [ha', hnfRed_key, mul_comm, ← Int.emod_def]
    have hlt : (a' k).natAbs < N := by
      rw [hkey, ← hN]
      have h1 := Int.emod_nonneg (a k) hg
      have h2 := Int.emod_lt_of_pos (a k) hgpos
      zify
      rw [abs_of_nonneg h1, abs_of_pos hgpos]
      exact h2
    have hp' : HnfPair k m g a' := by
      refine ⟨fun j hj => ⟨(hp.low j hj).2, ?_⟩, ⟨hgpos, hp.gkey.2.le⟩, ?_, fun j hj => ⟨(hp.high j hj).2, ?_⟩⟩
      · simp [ha', hnfRed, show ¬ (k : ℕ) < j by omega, (hp.low j hj).1, (hp.low j hj).2]
      · rw [hkey]
        exact ⟨Int.emod_nonneg _ hg, (Int.emod_lt_of_pos _ hgpos).trans hp.gkey.2⟩
      · simp only [ha', hnfRed, if_pos hj]
        exact ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩
    obtain ⟨h1, h2, h3⟩ := ih _ hlt g a' rfl hp'
    refine ⟨h1, h2, h3.trans ?_⟩
    -- span {g, a'} ⊔ V = span {a, g} ⊔ V
    have hmem := hnfRed_sub_mem (k := k) (m := m) a g (a k / g k)
    rw [← ha'] at hmem
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨Submodule.mem_sup_left (Submodule.subset_span (by simp)), ?_⟩
      have : a' = (a - (a k / g k) • g) + (a' - (a - (a k / g k) • g)) := by abel
      rw [SetLike.mem_coe, this]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right hmem)
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · refine sup_le ?_ le_sup_right
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, Submodule.mem_sup_left (Submodule.subset_span (by simp))⟩
      have : a = (a' - (a' - (a - (a k / g k) • g))) + (a k / g k) • g := by abel
      rw [SetLike.mem_coe, this]
      exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.mem_sup_left
        (Submodule.subset_span (by simp))) (Submodule.mem_sup_right hmem))
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))

/-! ### Clearing one column -/

theorem hnfSpan_perm {L L' : List (Fin n → ℤ)} (h : L.Perm L') : hnfSpan L = hnfSpan L' := by
  simp only [hnfSpan, h.mem_iff]

theorem hnfSpan_cons2 (a g : Fin n → ℤ) (R : List (Fin n → ℤ)) :
    hnfSpan (a :: g :: R) = Submodule.span ℤ {a, g} ⊔ hnfSpan R := by
  rw [hnfSpan_cons, hnfSpan_cons, ← sup_assoc, ← Submodule.span_union]
  rfl

/-- Replacing a pair of rows by a pair with the same span modulo `V`. -/
theorem hnfSpan_replace {V : Submodule ℤ (Fin n → ℤ)} {a g a' g' : Fin n → ℤ}
    (h : Submodule.span ℤ {a', g'} ⊔ V = Submodule.span ℤ {a, g} ⊔ V) (R : List (Fin n → ℤ)) :
    hnfSpan (a' :: g' :: R) ⊔ V = hnfSpan (a :: g :: R) ⊔ V := by
  rw [hnfSpan_cons2, hnfSpan_cons2, sup_right_comm, h, sup_right_comm]

/-- One Euclid run inside the fold over the working rows. -/
def hnfFoldStep (k : Fin n) (m : ℤ) (acc : (Fin n → ℤ) × List (Fin n → ℤ)) (g : Fin n → ℤ) :
    (Fin n → ℤ) × List (Fin n → ℤ) :=
  ((hnfEuclid k m acc.1 g).1, acc.2 ++ [(hnfEuclid k m acc.1 g).2])

/-- A working row before column `k`: zero before `k`, entries in `[0, m)` from `k` on. -/
def HnfWork (k : ℕ) (m : ℤ) (g : Fin n → ℤ) : Prop :=
  (∀ j : Fin n, (j : ℕ) < k → g j = 0) ∧ ∀ j : Fin n, k ≤ (j : ℕ) → 0 ≤ g j ∧ g j < m

/-- A pivot row for column `k`. -/
def HnfPiv (k : Fin n) (m : ℤ) (a : Fin n → ℤ) : Prop :=
  (∀ j : Fin n, (j : ℕ) < k → a j = 0) ∧ (0 < a k ∧ a k ≤ m) ∧
    ∀ j : Fin n, (k : ℕ) < j → 0 ≤ a j ∧ a j < m

/-- **Clearing column `k`.** -/
theorem hnfFold_spec (k : Fin n) {m : ℤ} (hm : 0 < m) :
    ∀ (G : List (Fin n → ℤ)) (acc : (Fin n → ℤ) × List (Fin n → ℤ)),
      HnfPiv k m acc.1 → (∀ g ∈ acc.2, HnfWork (k + 1) m g) → (∀ g ∈ G, HnfWork k m g) →
      HnfPiv k m (G.foldl (hnfFoldStep k m) acc).1 ∧
        (∀ g ∈ (G.foldl (hnfFoldStep k m) acc).2, HnfWork (k + 1) m g) ∧
        hnfSpan ((G.foldl (hnfFoldStep k m) acc).1 :: (G.foldl (hnfFoldStep k m) acc).2) ⊔
          hnfV n m (k + 1) = hnfSpan (acc.1 :: (acc.2 ++ G)) ⊔ hnfV n m (k + 1) := by
  intro G
  induction G with
  | nil => intro acc ha hacc _; exact ⟨ha, hacc, by simp⟩
  | cons g G ih =>
    intro acc ha hacc hG
    have hg := hG g (by simp)
    have hpair : HnfPair k m acc.1 g :=
      ⟨fun j hj => ⟨ha.1 j hj, hg.1 j hj⟩, ha.2.1, hg.2 k le_rfl,
        fun j hj => ⟨ha.2.2 j hj, hg.2 j hj.le⟩⟩
    obtain ⟨hp, hz, hspan⟩ := hnfEuclid_spec k hm _ acc.1 g rfl hpair
    have ha' : HnfPiv k m (hnfFoldStep k m acc g).1 :=
      ⟨fun j hj => (hp.low j hj).1, hp.akey, fun j hj => (hp.high j hj).1⟩
    have hacc' : ∀ g' ∈ (hnfFoldStep k m acc g).2, HnfWork (k + 1) m g' := by
      intro g' hg'
      simp only [hnfFoldStep, List.mem_append, List.mem_singleton] at hg'
      rcases hg' with hg' | rfl
      · exact hacc g' hg'
      · refine ⟨fun j hj => ?_, fun j hj => (hp.high j (by omega)).2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact (hp.low j hj).2
        · rw [show j = k from Fin.ext hj]; exact hz
    obtain ⟨h1, h2, h3⟩ := ih (hnfFoldStep k m acc g) ha' hacc' (fun g' hg' => hG g' (by simp [hg']))
    simp only [List.foldl_cons]
    refine ⟨h1, h2, h3.trans ?_⟩
    simp only [hnfFoldStep]
    rw [hnfSpan_perm (List.Perm.cons _ (show (acc.2 ++ [(hnfEuclid k m acc.1 g).2] ++ G).Perm
        ((hnfEuclid k m acc.1 g).2 :: (acc.2 ++ G)) by
          rw [List.append_assoc, List.singleton_append]; exact List.perm_middle)),
      hnfSpan_replace hspan,
      hnfSpan_perm (List.Perm.cons _ (List.perm_middle (a := g) (l₁ := acc.2) (l₂ := G))).symm]

/-! ### The whole algorithm -/

/-- Column `k`: clear it in the working rows, then reduce the finished rows modulo the new
pivot. -/
def hnfStep (k : Fin n) (m : ℤ) (st : List (Fin n → ℤ) × List (Fin n → ℤ)) :
    List (Fin n → ℤ) × List (Fin n → ℤ) :=
  ((st.1.map fun h => hnfRed k m h (st.2.foldl (hnfFoldStep k m) (Pi.single k m, [])).1
      (h k / (st.2.foldl (hnfFoldStep k m) (Pi.single k m, [])).1 k)) ++
    [(st.2.foldl (hnfFoldStep k m) (Pi.single k m, [])).1],
   (st.2.foldl (hnfFoldStep k m) (Pi.single k m, [])).2)

/-- The starting working rows: the rows of `M` mod `m`. -/
def hnfModInit (m : ℤ) (M : Matrix (Fin n) (Fin n) ℤ) : List (Fin n → ℤ) :=
  (List.finRange n).map fun i j => M i j % m

/-- The state after `k` columns. -/
def hnfModIter (m : ℤ) (M : Matrix (Fin n) (Fin n) ℤ) : ℕ → List (Fin n → ℤ) × List (Fin n → ℤ)
  | 0 => ([], hnfModInit m M)
  | k + 1 => if h : k < n then hnfStep ⟨k, h⟩ m (hnfModIter m M k) else hnfModIter m M k

/-- The finished rows after `k` columns are in Hermite form on the first `k` columns, with all
entries in `[0, m]`. -/
def HnfDone (k : ℕ) (m : ℤ) (H : List (Fin n → ℤ)) : Prop :=
  H.length = k ∧ ∀ (i j : Fin n) (hi : (i : ℕ) < H.length),
    ((j : ℕ) < i → H[(i : ℕ)] j = 0) ∧ ((j : ℕ) = i → 0 < H[(i : ℕ)] j ∧ H[(i : ℕ)] j ≤ m) ∧
    (∀ hj : (j : ℕ) < H.length, (i : ℕ) < j → 0 ≤ H[(i : ℕ)] j ∧ H[(i : ℕ)] j < H[(j : ℕ)] j) ∧
    (k ≤ (j : ℕ) → 0 ≤ H[(i : ℕ)] j ∧ H[(i : ℕ)] j < m)

/-- The invariant after `k` columns, for the lattice `L`. -/
def HnfModInv (k : ℕ) (m : ℤ) (L : Submodule ℤ (Fin n → ℤ))
    (st : List (Fin n → ℤ) × List (Fin n → ℤ)) : Prop :=
  HnfDone k m st.1 ∧ (∀ g ∈ st.2, HnfWork k m g) ∧ hnfSpan (st.1 ++ st.2) ⊔ hnfV n m k = L

theorem hnf_getElem_map_append {α : Type*} (l : List α) (f : α → α) (a : α) (i : ℕ)
    (hi : i < (l.map f ++ [a]).length) :
    (l.map f ++ [a])[i] = if h : i < l.length then f l[i] else a := by
  split_ifs with h
  · rw [List.getElem_append_left (by simpa using h)]; simp
  · simp only [List.length_append, List.length_map, List.length_singleton] at hi
    rw [List.getElem_append_right (by simp; omega)]
    simp

theorem hnfRed_low {k : ℕ} {m : ℤ} {h a : Fin n → ℤ} {q : ℤ} {j : Fin n} (hj : (j : ℕ) < k)
    (ha : a j = 0) : hnfRed k m h a q j = h j := by
  simp [hnfRed, show ¬ k < (j : ℕ) by omega, ha]

/-- **One column.** The invariant passes from `k` to `k + 1`. -/
theorem hnfStep_inv (k : Fin n) {m : ℤ} (hm : 0 < m) {L : Submodule ℤ (Fin n → ℤ)}
    {st : List (Fin n → ℤ) × List (Fin n → ℤ)} (h : HnfModInv k m L st) :
    HnfModInv (k + 1) m L (hnfStep k m st) := by
  obtain ⟨⟨hlen, hH⟩, hG, hspan⟩ := h
  have hpiv0 : HnfPiv k m (Pi.single k m : Fin n → ℤ) := by
    refine ⟨fun j hj => ?_, ⟨by simp [hm], by simp⟩, fun j hj => ?_⟩
    · have : j ≠ k := fun e => by subst e; omega
      simp [this]
    · have : j ≠ k := fun e => by subst e; omega
      simp [this, hm]
  obtain ⟨hpa, hwork, hfs⟩ := hnfFold_spec k hm st.2 (Pi.single k m, []) hpiv0 (by simp) hG
  set f := st.2.foldl (hnfFoldStep k m) (Pi.single k m, []) with hf
  set a := f.1 with ha
  set red : (Fin n → ℤ) → Fin n → ℤ := fun h => hnfRed k m h a (h k / a k) with hred
  have hst : hnfStep k m st = (st.1.map red ++ [a], f.2) := rfl
  rw [hst]
  have hak := hpa.2.1
  refine ⟨⟨by simp [hlen], ?_⟩, hwork, ?_⟩
  · intro i j hi
    simp only [List.length_append, List.length_map, List.length_singleton] at hi
    rw [hnf_getElem_map_append]
    split_ifs with hik
    · -- an earlier row, reduced by the new pivot
      obtain ⟨h1, h2, h3, h4⟩ := hH i j hik
      have hik' : (i : ℕ) < k := hlen ▸ hik
      simp only [hred]
      refine ⟨fun hj => ?_, fun hj => ?_, fun hj hij => ?_, fun hj => ?_⟩
      · rw [hnfRed_low (by omega) (hpa.1 j (by omega))]; exact h1 hj
      · rw [hnfRed_low (by omega) (hpa.1 j (by omega))]; exact h2 hj
      · simp only [List.length_append, List.length_map, List.length_singleton] at hj
        rw [hnf_getElem_map_append]
        split_ifs with hjk
        · have hjk' : (j : ℕ) < k := hlen ▸ hjk
          simp only [hred]
          rw [hnfRed_low hjk' (hpa.1 j hjk'), hnfRed_low hjk' (hpa.1 j hjk')]
          exact h3 hjk hij
        · have hjk' : j = k := Fin.ext (by omega)
          subst hjk'
          simp only [hnfRed_key]
          rw [mul_comm, ← Int.emod_def]
          exact ⟨Int.emod_nonneg _ hak.1.ne', Int.emod_lt_of_pos _ hak.1⟩
      · simp only [hnfRed, if_pos (show (k : ℕ) < j by omega)]
        exact ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩
    · -- the new pivot row
      have hik' : (i : ℕ) = k := by omega
      refine ⟨fun hj => hpa.1 j (by omega), fun hj => ?_, fun hj hij => by
        simp only [List.length_append, List.length_map, List.length_singleton] at hj; omega,
        fun hj => hpa.2.2 j (by omega)⟩
      rw [show j = k from Fin.ext (by omega)]; exact hak
  · -- the lattice
    set V' := hnfV n m ((k : ℕ) + 1)
    have hW : ∀ h ∈ st.1, red h - h ∈ hnfSpan (a :: f.2) ⊔ V' := by
      intro h _
      have hm1 := hnfRed_sub_mem (k := k) (m := m) h a (h k / a k)
      have : red h - h = (hnfRed k m h a (h k / a k) - (h - (h k / a k) • a)) +
          (-((h k / a k) • a)) := by simp only [red]; abel
      rw [this]
      refine Submodule.add_mem _ (Submodule.mem_sup_right hm1) (Submodule.mem_sup_left ?_)
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    rw [List.append_assoc, List.singleton_append, hnfSpan_append, sup_assoc,
      hnfSpan_map_sup _ red st.1 hW, hfs, List.nil_append, hnfSpan_cons, ← hspan,
      hnfV_split m k, hnfSpan_append]
    simp only [sup_assoc, sup_left_comm, sup_comm]
    rfl

/-- The starting state satisfies the invariant for the row lattice of `M`, when `m ℤ^n` lies in
it. -/
theorem hnfModIter_zero_inv {m : ℤ} (hm : 0 < m) (M : Matrix (Fin n) (Fin n) ℤ)
    (hL : ∀ j : Fin n, Pi.single j m ∈ Submodule.span ℤ (Set.range M)) :
    HnfModInv 0 m (Submodule.span ℤ (Set.range M)) (hnfModIter m M 0) := by
  refine ⟨⟨rfl, fun i j hi => absurd hi (by simp [hnfModIter])⟩, ?_, ?_⟩
  · intro g hg
    simp only [hnfModIter, hnfModInit, List.mem_map, List.mem_finRange, true_and] at hg
    obtain ⟨i, rfl⟩ := hg
    exact ⟨fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j _ => ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩⟩
  · have hV0 : hnfV n m 0 ≤ Submodule.span ℤ (Set.range M) := by
      intro v hv
      have hv' : v = ∑ j, (v j / m) • (Pi.single j m : Fin n → ℤ) := by
        funext t
        simp [Finset.sum_apply, Pi.single_apply, Int.ediv_mul_cancel (hv.2 t)]
      rw [hv']
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hL j)
    have hspanM : hnfSpan ((List.finRange n).map M) = Submodule.span ℤ (Set.range M) := by
      simp only [hnfSpan, List.mem_map, List.mem_finRange, true_and]
      rfl
    have hinit : hnfModInit m M = ((List.finRange n).map M).map (fun r j => r j % m) := by
      simp [hnfModInit, List.map_map]
    have hsub : ∀ h ∈ (List.finRange n).map M, (fun j => h j % m) - h ∈ hnfV n m 0 :=
      fun h _ => ⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun j => by simp [Int.emod_def]⟩
    simp only [hnfModIter, List.nil_append]
    rw [hinit, hnfSpan_map_sup _ _ _ hsub, hspanM]
    exact sup_eq_left.mpr hV0

theorem hnfModIter_inv {m : ℤ} (hm : 0 < m) (M : Matrix (Fin n) (Fin n) ℤ)
    (hL : ∀ j : Fin n, Pi.single j m ∈ Submodule.span ℤ (Set.range M)) :
    ∀ k, k ≤ n → HnfModInv k m (Submodule.span ℤ (Set.range M)) (hnfModIter m M k) := by
  intro k
  induction k with
  | zero => exact fun _ => hnfModIter_zero_inv hm M hL
  | succ k ih =>
    intro hk
    have h := hnfStep_inv ⟨k, by omega⟩ hm (ih (by omega))
    simpa [hnfModIter, show k < n by omega] using h

/-- The Hermite form computed modulo `m`. -/
def hnfModMat (m : ℤ) (M : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i => ((hnfModIter m M n).1).getD i 0

/-- **The modular Hermite form.** If `m > 0` and `m ℤ^n` lies in the row lattice of `M`, then
`hnfModMat m M` is in Hermite form, has the same row lattice as `M`, and has its entries in
`[0, m]`. -/
theorem hnfModMat_spec {m : ℤ} (hm : 0 < m) (M : Matrix (Fin n) (Fin n) ℤ)
    (hL : ∀ j : Fin n, Pi.single j m ∈ Submodule.span ℤ (Set.range M)) :
    IsHermiteForm (hnfModMat m M) ∧
      Submodule.span ℤ (Set.range (hnfModMat m M)) = Submodule.span ℤ (Set.range M) ∧
      ∀ i j, 0 ≤ hnfModMat m M i j ∧ hnfModMat m M i j ≤ m := by
  obtain ⟨⟨hlen, hH⟩, hG, hspan⟩ := hnfModIter_inv hm M hL n le_rfl
  set H := (hnfModIter m M n).1 with hHdef
  have hget : ∀ i : Fin n, hnfModMat m M i = H[(i : ℕ)]'(by omega) := fun i => by
    simp only [hnfModMat, ← hHdef]
    exact List.getD_eq_getElem _ _ (by omega)
  have hdiag : ∀ j : Fin n, 0 < hnfModMat m M j j ∧ hnfModMat m M j j ≤ m := fun j => by
    rw [hget]; exact (hH j j (by omega)).2.1 rfl
  refine ⟨⟨fun i j hij => ?_, fun i j hij => ?_, fun i j i' hij hi' => ?_⟩, ?_, fun i j => ?_⟩
  · rw [hget]; exact (hH i j (by omega)).1 hij
  · rw [show i = j from Fin.ext hij]; exact (hdiag j).1
  · rw [show i' = j from Fin.ext hi', hget, hget]; exact (hH i j (by omega)).2.2.1 (by omega) hij
  · have hG0 : hnfSpan (hnfModIter m M n).2 = ⊥ := by
      rw [hnfSpan, Submodule.span_eq_bot]
      intro g hg
      exact funext fun j => (hG g hg).1 j j.isLt
    rw [hnfSpan_append, hG0, sup_bot_eq, hnfV_n, sup_bot_eq] at hspan
    rw [← hspan, hnfSpan]
    congr 1
    ext v
    simp only [Set.mem_range, Set.mem_setOf_eq, List.mem_iff_getElem]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, by omega, (hget i).symm⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, by omega⟩, hget ⟨i, by omega⟩⟩
  · rcases lt_trichotomy (j : ℕ) i with hji | hji | hji
    · rw [hget, (hH i j (by omega)).1 hji]; exact ⟨le_rfl, hm.le⟩
    · rw [show i = j from (Fin.ext hji).symm]; exact ⟨(hdiag j).1.le, (hdiag j).2⟩
    · have h := (hH i j (by omega)).2.2.1 (by omega) hji
      rw [← hget, ← hget] at h
      exact ⟨h.1, (h.2.trans_le (hdiag j).2).le⟩

end GI.Proved
