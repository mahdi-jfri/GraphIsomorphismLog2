import Workspace.Proved.JohnModel
import Mathlib.Data.Finset.Sort

/-!
# The sets `C(x, y)` and the bijection `ι`

This file follows [H, §2.8] on lists. With `D(x, y)` the test "the pair `(x, y)` has label `Δ`",
that is, the `k`-sets of `x` and `y` are disjoint (`john_D_eq`), let

* `B(x, y)` be the points `z` with `¬ D(x, z)` and `D(y, z)` (`johnB`);
* `C(x, y)` be the points `r` with `¬ D(z, r)` for all `z ∈ B(x, y)`, as a 0/1 list over the
  points (`johnC`).

For a pair `(x, y)` with label `Υ`, `C(x, y)` is the set of points whose `k`-set contains the
element `i` of `ι x` outside `ι y` (`john_C_eq`, from `john_C_iff`). The program collects the
distinct lists `C(x, y)` over the pairs with label `Υ`, in the order of the pairs
(`johnLam`). These are the `m` lists "`i ∈ ι r`" for `i ∈ Fin m`, each once
(`john_lam_mem`, `john_lam_nodup`, `john_lam_length`). Numbering them gives a permutation `π` of
`Fin m`, and the output `johnOut` lists, for each point `x`, the numbers `t` whose list has a 1 at
`x`. This is `ι` followed by the renaming `π⁻¹` (`john_out_eq`), which is correct by
`john_isJohnsonId_trans`.
-/

namespace GI.Proved

open Equiv Finset GI.Cited

variable {n m k : ℕ}

/-! ### The lists of the program -/

/-- The test "the pair `(x, y)` has label `δ`". -/
def johnD (n : ℕ) (labL : List ℕ) (δ x y : ℕ) : Bool := decide (labL.getD (n * x + y) 0 = δ)

/-- The set `B(x, y)`. -/
def johnB (n : ℕ) (labL : List ℕ) (δ x y : ℕ) : List ℕ :=
  (List.range n).filter fun z => !johnD n labL δ x z && johnD n labL δ y z

/-- The set `C(x, y)`, as a 0/1 list over the points. -/
def johnC (n : ℕ) (labL : List ℕ) (δ x y : ℕ) : List ℕ :=
  (List.range n).map fun r => ((johnB n labL δ x y).all fun z => !johnD n labL δ z r).toNat

/-- One step of the collection of the sets `C(x, y)`: the pair with index `p` is
`(p / n, p % n)`. -/
def johnStep (n : ℕ) (labL : List ℕ) (δ υ : ℕ) (acc : List (List ℕ)) (p : ℕ) :
    List (List ℕ) :=
  if decide (labL.getD p 0 = υ) &&
      !(acc.any fun v => decide (v = johnC n labL δ (p / n) (p % n))) then
    acc ++ [johnC n labL δ (p / n) (p % n)]
  else acc

/-- The collection `Λ` of the distinct sets `C(x, y)` over the pairs with label `υ`. -/
def johnLam (n : ℕ) (labL : List ℕ) (δ υ : ℕ) : List (List ℕ) :=
  (List.range (n * n)).foldl (johnStep n labL δ υ) []

/-- The output: for each point `x`, the indices `t` of the sets of `Λ` that contain `x`. -/
def johnOut (n : ℕ) (lam : List (List ℕ)) : List (List ℕ) :=
  (List.range n).map fun x =>
    (List.range lam.length).filter fun t => decide ((lam.getD t []).getD x 0 = 1)

/-! ### Collecting distinct values -/

/-- A fold that adds the value `F p` of each `p` with `P p`, unless it is already there, gives
a list without repeats whose entries are these values. -/
theorem john_dedup {α β : Type} [DecidableEq β] (P : α → Bool) (F : α → β) (l : List α)
    (acc0 : List β) (h0 : acc0.Nodup) :
    (l.foldl (fun acc p => if P p && !(acc.any fun v => decide (v = F p)) then acc ++ [F p]
      else acc) acc0).Nodup ∧
    ∀ v, v ∈ l.foldl (fun acc p => if P p && !(acc.any fun v => decide (v = F p)) then
      acc ++ [F p] else acc) acc0 ↔ v ∈ acc0 ∨ ∃ p ∈ l, P p ∧ F p = v := by
  induction l generalizing acc0 with
  | nil => simp [h0]
  | cons p l ih =>
    simp only [List.foldl_cons]
    by_cases hP : P p && !(acc0.any fun v => decide (v = F p))
    · rw [if_pos hP]
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq]
        at hP
      have hnd : (acc0 ++ [F p]).Nodup :=
        List.nodup_append.mpr ⟨h0, List.nodup_singleton _, by
          intro a ha b hb; rw [List.mem_singleton] at hb; subst hb
          exact fun he => hP.2 a ha he⟩
      refine ⟨(ih _ hnd).1, fun v => ?_⟩
      rw [(ih _ hnd).2]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h | h) | ⟨q, hq, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨p, Or.inl rfl, hP.1, h.symm⟩
        · exact Or.inr ⟨q, Or.inr hq, h⟩
      · rintro (h | ⟨q, rfl | hq, h⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h.2.symm)
        · exact Or.inr ⟨q, hq, h⟩
    · rw [if_neg hP]
      refine ⟨(ih _ h0).1, fun v => ?_⟩
      rw [(ih _ h0).2]
      simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨q, hq, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨q, Or.inr hq, h⟩
      · rintro (h | ⟨q, rfl | hq, h⟩)
        · exact Or.inl h
        · left
          simp only [h.1, Bool.true_and, Bool.not_eq_true, Bool.not_eq_false',
            List.any_eq_true, decide_eq_true_eq] at hP
          obtain ⟨a, ha, he⟩ := hP
          rw [← h.2, ← he]; exact ha
        · exact Or.inr ⟨q, hq, h⟩

/-! ### The sets `C(x, y)` -/

section
variable {ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}} {lab : Fin (n * n) → ℕ}

/-- The list of the points whose `k`-set contains `i`. -/
def johnInd (ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}) (i : Fin m) : List ℕ :=
  (List.finRange n).map fun r => if i ∈ (ι r).1 then 1 else 0

/-- The label `Δ` of `lab`. -/
abbrev JohnHyp.δ (_ : JohnHyp ι lab) : ℕ := johnDelta (johnRow n (johnLabL lab))

/-- The label `Υ` of `lab`. -/
abbrev JohnHyp.υ (_ : JohnHyp ι lab) : ℕ := johnUps m k (johnRow n (johnLabL lab))

theorem john_D_eq (h : JohnHyp ι lab) (x y : Fin n) :
    johnD n (johnLabL lab) h.δ x y = decide (Disjoint (ι x).1 (ι y).1) := by
  unfold johnD
  rw [john_labL_getD]
  exact decide_eq_decide.mpr (john_delta_iff h x y)

/-- **`C(x, y)` for a pair with label `Υ`.** -/
theorem john_C_eq (h : JohnHyp ι lab) {x y : Fin n} {i : Fin m} (hiA : i ∈ (ι x).1)
    (hiB : i ∉ (ι y).1) (hxy : johnInter ι x y + 1 = k) :
    johnC n (johnLabL lab) h.δ x y = johnInd ι i := by
  unfold johnC johnInd
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply]
  have key : ((johnB n (johnLabL lab) h.δ x y).all fun z => !johnD n (johnLabL lab) h.δ z r) =
      decide (i ∈ (ι r).1) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff,
      ← john_C_iff h.three_mul (ι x).2 (ι y).2 hiA hiB hxy (ι r).1 (ι r).2]
    unfold johnB
    rw [← List.map_coe_finRange_eq_range, List.filter_map]
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, Function.comp_apply,
      forall_exists_index, and_imp, Bool.and_eq_true, john_D_eq h,
      decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
    constructor
    · intro hall Z hZ hAZ hBZ
      have h1 := hall (ι.symm ⟨Z, hZ⟩ : Fin n) (ι.symm ⟨Z, hZ⟩)
      simp only [Equiv.apply_symm_apply, john_D_eq h, decide_eq_false_iff_not] at h1
      exact h1 hAZ hBZ trivial
    · intro hall z a hxa hya hz
      subst hz
      rw [john_D_eq h, decide_eq_false_iff_not]
      exact hall (ι a).1 (ι a).2 hxa hya
  rw [key]
  by_cases hi : i ∈ (ι r).1 <;> simp [hi]

theorem john_ind_getD (ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}) (i : Fin m) (r : Fin n) :
    (johnInd ι i).getD r 0 = if i ∈ (ι r).1 then 1 else 0 := by
  simp [johnInd, List.getD_eq_getElem?_getD]

/-- A `k`-set through `i` that misses `j`, when `k + 1 ≤ m`. -/
theorem john_exists_set (hk : 1 ≤ k) (hkm : k + 1 ≤ m) (i j : Fin m) (hij : i ≠ j) :
    ∃ T : Finset (Fin m), #T + 1 = k ∧ i ∉ T ∧ j ∉ T := by
  obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq (s := ({i, j} : Finset (Fin m))ᶜ) (n := k - 1)
    (by rw [card_compl, Fintype.card_fin, card_pair hij]; omega)
  refine ⟨T, by omega, fun h => ?_, fun h => ?_⟩
  · simpa using hT h
  · simpa using hT h

/-- The lists `johnInd ι i` are distinct. -/
theorem john_ind_inj (h : JohnHyp ι lab) {i j : Fin m} (he : johnInd ι i = johnInd ι j) :
    i = j := by
  by_contra hij
  have hkm := h.two_mul
  obtain ⟨T, hT, hiT, -⟩ := john_exists_set h.one_le (by omega) i j hij
  obtain ⟨T', hT', hiT', hjT'⟩ := john_exists_set h.one_le (by omega) i j hij
  have hR : #(insert i T') = k := by rw [card_insert_of_notMem hiT']; omega
  have h1 := congrArg (fun l => l.getD (ι.symm ⟨insert i T', hR⟩ : Fin n) 0) he
  simp only [john_ind_getD, Equiv.apply_symm_apply, mem_insert_self, if_true] at h1
  rw [if_neg (by simp [Ne.symm hij, hjT'])] at h1
  exact one_ne_zero h1

/-- The pair with index `p`. -/
theorem john_labL_getD_idx (lab : Fin (n * n) → ℕ) {p : ℕ} (hp : p < n * n) :
    ∃ x y : Fin n, (x : ℕ) = p / n ∧ (y : ℕ) = p % n ∧
      (johnLabL lab).getD p 0 = lab (johnPair x y) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hp
    · exact h0
  refine ⟨⟨p / n, Nat.div_lt_of_lt_mul hp⟩, ⟨p % n, Nat.mod_lt _ hn⟩, rfl, rfl, ?_⟩
  have e := john_labL_getD lab ⟨p / n, Nat.div_lt_of_lt_mul hp⟩ ⟨p % n, Nat.mod_lt _ hn⟩
  simp only [Nat.div_add_mod] at e
  exact e

/-- **The members of `Λ`.** -/
theorem john_lam_mem (h : JohnHyp ι lab) (v : List ℕ) :
    v ∈ johnLam n (johnLabL lab) h.δ h.υ ↔ ∃ i, johnInd ι i = v := by
  unfold johnLam johnStep
  rw [(john_dedup (fun p => decide ((johnLabL lab).getD p 0 = h.υ))
    (fun p => johnC n (johnLabL lab) h.δ (p / n) (p % n)) _ [] List.nodup_nil).2]
  simp only [List.not_mem_nil, false_or, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, hυ, rfl⟩
    obtain ⟨x, y, hx, hy, hl⟩ := john_labL_getD_idx lab hp
    rw [hl, john_ups_iff h] at hυ
    obtain ⟨i, hiA, hiAB⟩ := exists_mem_notMem_of_card_lt_card
      (s := (ι x).1 ∩ (ι y).1) (t := (ι x).1) (by
        have := (ι x).2; unfold johnInter at hυ; omega)
    have hiB : i ∉ (ι y).1 := fun hb => hiAB (mem_inter.mpr ⟨hiA, hb⟩)
    refine ⟨i, ?_⟩
    rw [← hx, ← hy, john_C_eq h hiA hiB hυ]
  · rintro ⟨i, rfl⟩
    have hkm := h.two_mul
    obtain ⟨j, -, hj⟩ := exists_mem_notMem_of_card_lt_card (s := ({i} : Finset (Fin m)))
      (t := univ) (by rw [card_singleton, card_univ, Fintype.card_fin]; omega)
    have hij : i ≠ j := fun e => hj (by simp [e])
    obtain ⟨T, hT, hiT, hjT⟩ := john_exists_set h.one_le (by omega) i j hij
    have hA : #(insert i T) = k := by rw [card_insert_of_notMem hiT]; omega
    have hB : #(insert j T) = k := by rw [card_insert_of_notMem hjT]; omega
    set x := ι.symm ⟨insert i T, hA⟩
    set y := ι.symm ⟨insert j T, hB⟩
    have hxA : (ι x).1 = insert i T := by simp [x]
    have hyB : (ι y).1 = insert j T := by simp [y]
    have hAB : (ι x).1 ∩ (ι y).1 = T := by
      rw [hxA, hyB]
      ext a
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨rfl | ha, rfl | hb⟩
        · exact absurd rfl hij
        · exact hb
        · exact ha
        · exact ha
      · intro ha; exact ⟨Or.inr ha, Or.inr ha⟩
    have hxy : johnInter ι x y + 1 = k := by unfold johnInter; rw [hAB]; exact hT
    have hlt : n * x + y < n * n := by rw [← john_pair_val]; exact (johnPair x y).isLt
    have hn : 0 < n := Fin.pos x
    have hdiv : (n * x + y) / n = x := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt y.isLt, zero_add]
    have hmod : (n * x + y) % n = y := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt]
    refine ⟨n * x + y, hlt, ?_, ?_⟩
    · rw [john_labL_getD, john_ups_iff h]; exact hxy
    · rw [hdiv, hmod]
      refine john_C_eq h (by rw [hxA]; exact mem_insert_self _ _) ?_ hxy
      rw [hyB, mem_insert, not_or]
      exact ⟨hij, hiT⟩

theorem john_lam_nodup (h : JohnHyp ι lab) : (johnLam n (johnLabL lab) h.δ h.υ).Nodup := by
  unfold johnLam johnStep
  exact (john_dedup (fun p => decide ((johnLabL lab).getD p 0 = h.υ))
    (fun p => johnC n (johnLabL lab) h.δ (p / n) (p % n)) _ [] List.nodup_nil).1

theorem john_lam_length (h : JohnHyp ι lab) : (johnLam n (johnLabL lab) h.δ h.υ).length = m := by
  rw [← List.toFinset_card_of_nodup (john_lam_nodup h)]
  have : (johnLam n (johnLabL lab) h.δ h.υ).toFinset = univ.image (johnInd ι) := by
    ext v
    rw [List.mem_toFinset, john_lam_mem h]
    simp
  rw [this, card_image_of_injective _ (fun i j he => john_ind_inj h he), card_univ,
    Fintype.card_fin]

/-- Sorting a set of `Fin m` gives the numbers below `m` in it, in increasing order. -/
theorem john_sort_eq (s : Finset (Fin m)) :
    (s.sort (· ≤ ·)).map (fun a : Fin m => (a : ℕ)) =
      (List.range m).filter fun t => decide (∃ h : t < m, (⟨t, h⟩ : Fin m) ∈ s) := by
  apply List.Perm.eq_of_pairwise' (r := fun a b : ℕ => a ≤ b)
  · rw [List.pairwise_map]
    exact (pairwise_sort s (fun a b : Fin m => a ≤ b)).imp fun {a b} hab => Fin.le_def.mp hab
  · exact (List.pairwise_lt_range.filter _).imp le_of_lt
  · apply (List.perm_ext_iff_of_nodup ((sort_nodup s _).map Fin.val_injective)
      (List.nodup_range.filter _)).mpr
    intro a
    simp only [List.mem_map, mem_sort, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.isLt, b.isLt, hb⟩
    · rintro ⟨-, ha, hs⟩
      exact ⟨⟨a, ha⟩, hs, rfl⟩

/-- **The output.** The program's output is `ι` followed by a renaming of `Fin m`. -/
theorem john_out_eq (h : JohnHyp ι lab) : ∃ π : Perm (Fin m),
    johnOut n (johnLam n (johnLabL lab) h.δ h.υ) = (List.finRange n).map fun x =>
      (((ι.trans (kSetPerm π)) x).1.sort (· ≤ ·)).map fun a : Fin m => (a : ℕ) := by
  set L := johnLam n (johnLabL lab) h.δ h.υ with hL
  have hlen : L.length = m := john_lam_length h
  have hex : ∀ t : Fin m, ∃ i, johnInd ι i = L[(t : ℕ)]'(by rw [hlen]; exact t.isLt) :=
    fun t => (john_lam_mem h _).mp (List.getElem_mem _)
  choose σ hσ using hex
  have hinj : Function.Injective σ := by
    intro t t' he
    have := (hσ t).symm.trans ((congrArg (johnInd ι) he).trans (hσ t'))
    exact Fin.ext ((List.Nodup.getElem_inj_iff (john_lam_nodup h)).mp this)
  set π := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
  refine ⟨π⁻¹, ?_⟩
  unfold johnOut
  rw [hlen, ← List.map_coe_finRange_eq_range (n := n), List.map_map]
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply]
  rw [john_sort_eq]
  refine List.filter_congr fun t ht => ?_
  rw [List.mem_range] at ht
  have hget : L.getD t [] = johnInd ι (σ ⟨t, ht⟩) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact ht),
      Option.getD_some, hσ]
  rw [hget, john_ind_getD]
  simp only [Equiv.trans_apply, GI.Impl.cam_kSetPerm_apply, mem_map_equiv, ht, exists_true_left]
  have hπ : (π⁻¹).symm ⟨t, ht⟩ = σ ⟨t, ht⟩ := rfl
  rw [hπ]
  by_cases hi : σ ⟨t, ht⟩ ∈ (ι x).1 <;> simp [hi]

/-! ### Facts for the cost of the program -/

/-- **There are at least `m` points.** Fix the point `x0`. The points `z` with
`|ι x0 ∩ ι z| = k - 1` number `k (m - k)` (`john_card_points`, `john_card_val`), and `x0` is not
one of them. So `n ≥ k (m - k) + 1 ≥ m`. -/
theorem JohnHyp.m_le (h : JohnHyp ι lab) : m ≤ n := by
  have hk := h.one_le
  have hkm := h.two_mul
  have hc := john_card_points ι h.x0 (k - 1)
  have hv := john_card_val (ι h.x0).1 (ι h.x0).2 1 (by omega)
  rw [john_val_one] at hv
  rw [hv] at hc
  have hlt : #(univ.filter fun z => johnInter ι h.x0 z = k - 1) < n := by
    calc _ < #(univ : Finset (Fin n)) := card_lt_card (filter_ssubset.mpr
          ⟨h.x0, mem_univ _, by unfold johnInter; rw [inter_self, (ι h.x0).2]; omega⟩)
      _ = n := by simp
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
  have h1 : a ≤ a * (m - (a + 1)) := Nat.le_mul_of_pos_right _ (by omega)
  have e : (a + 1) * (m - (a + 1)) = a * (m - (a + 1)) + (m - (a + 1)) := by ring
  omega

/-- Each list `C(x, y)` of a pair with label `Υ` is a list `johnInd ι i`. -/
theorem john_C_ind (h : JohnHyp ι lab) {p : ℕ} (hp : p < n * n)
    (hυ : (johnLabL lab).getD p 0 = h.υ) :
    ∃ i, johnInd ι i = johnC n (johnLabL lab) h.δ (p / n) (p % n) := by
  obtain ⟨x, y, hx, hy, hl⟩ := john_labL_getD_idx lab hp
  rw [hl, john_ups_iff h] at hυ
  obtain ⟨i, hiA, hiAB⟩ := exists_mem_notMem_of_card_lt_card
    (s := (ι x).1 ∩ (ι y).1) (t := (ι x).1) (by
      have := (ι x).2; unfold johnInter at hυ; omega)
  have hiB : i ∉ (ι y).1 := fun hb => hiAB (mem_inter.mpr ⟨hiA, hb⟩)
  refine ⟨i, ?_⟩
  rw [← hx, ← hy, john_C_eq h hiA hiB hυ]

/-- **The partial results of the fold.** After any list of pairs, the collected lists are
lists `johnInd ι i`, without repeats, so there are at most `m` of them. -/
theorem john_prefix (h : JohnHyp ι lab) (l : List ℕ) (hl : ∀ p ∈ l, p < n * n) :
    (l.foldl (johnStep n (johnLabL lab) h.δ h.υ) []).length ≤ m ∧
      ∀ v ∈ l.foldl (johnStep n (johnLabL lab) h.δ h.υ) [], ∃ i, johnInd ι i = v := by
  have hd := john_dedup (fun p => decide ((johnLabL lab).getD p 0 = h.υ))
    (fun p => johnC n (johnLabL lab) h.δ (p / n) (p % n)) l [] List.nodup_nil
  have hnd : (l.foldl (johnStep n (johnLabL lab) h.δ h.υ) []).Nodup := hd.1
  have hmem : ∀ v ∈ l.foldl (johnStep n (johnLabL lab) h.δ h.υ) [], ∃ i, johnInd ι i = v := by
    intro v hv
    obtain h0 | ⟨p, hpl, hP, rfl⟩ := (hd.2 v).mp hv
    · simp at h0
    · exact john_C_ind h (hl p hpl) (by simpa using hP)
  refine ⟨?_, hmem⟩
  rw [← List.toFinset_card_of_nodup hnd]
  calc _ ≤ #(univ.image (johnInd ι)) := card_le_card fun v hv => by
        obtain ⟨i, rfl⟩ := hmem v (List.mem_toFinset.mp hv)
        simp
    _ ≤ m := card_image_le.trans (by simp)

end

end GI.Proved
