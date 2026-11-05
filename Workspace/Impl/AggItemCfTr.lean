module

public import Workspace.Algorithm.OutOrbital
public import Workspace.Cited.AlgoPermGroups

@[expose] public section

/-!
# The degree of transitivity by a stabilizer chain

The object of Case 2b needs `transDeg H Φ`, the largest `r ≤ |Φ|` such that `H` is transitive
on the injective `r`-tuples of `Φ` (`TransOn`). The definition quantifies over all tuples, so a
program cannot test it directly. We test it along one fixed enumeration `x` of `Φ`, one point at
a time.

`ItCfChain H Φ x i` says: the elements of `H` that fix `x 0, …, x (i-1)` move `x i` to every
point of `Φ` other than `x 0, …, x (i-1)`. The main result is `itCf_transDeg_eq`: if
`ItCfChain` holds for every `i < d` and fails at `d` (or `d = |Φ|`), then `transDeg H Φ = d`.
It needs only that `H` maps `Φ` into itself. `itCf_chain_iff` restates `ItCfChain` with the
points of `Φ` named by their positions in `x`. This is the form the program `col` tests, with an
orbit computation of a pointwise stabilizer.
-/

namespace GI.Impl

open GI.Algorithm Equiv Equiv.Perm

variable {q : ℕ} (H : Subgroup (Perm (Fin q))) (Φ : Finset (Fin q))

/-- **The step `i` of the stabilizer chain along `x`**: the elements of `H` fixing
`x 0, …, x (i-1)` move `x i` to every point of `Φ` off these points. -/
def ItCfChain (x : ℕ → Fin q) (i : ℕ) : Prop :=
  ∀ b ∈ Φ, (∀ j < i, b ≠ x j) → ∃ h ∈ H, (∀ j < i, h (x j) = x j) ∧ h (x i) = b

variable {H Φ}

/-- If the chain steps below `r` hold, every injective `r`-tuple of `Φ` is the image of
`x 0, …, x (r-1)` under some element of `H`. We extend the element one position at a time. -/
theorem itCf_chain_reach (hpres : ∀ h ∈ H, ∀ a ∈ Φ, h a ∈ Φ) (x : ℕ → Fin q) {r : ℕ}
    (hc : ∀ i < r, ItCfChain H Φ x i) (a : Fin r → Fin q) (ha : Function.Injective a)
    (haΦ : ∀ i, a i ∈ Φ) : ∃ h ∈ H, ∀ i : Fin r, h (x i) = a i := by
  have key : ∀ m ≤ r, ∃ h ∈ H, ∀ i : Fin r, i.val < m → h (x i) = a i := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨1, H.one_mem, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨h, hh, hha⟩ := ih (by omega)
      set im : Fin r := ⟨m, by omega⟩
      -- the point that the next element must reach
      have hb : h⁻¹ (a im) ∈ Φ := hpres _ (H.inv_mem hh) _ (haΦ im)
      have hne : ∀ j < m, h⁻¹ (a im) ≠ x j := by
        intro j hj e
        have e' : a im = a ⟨j, by omega⟩ := by
          rw [← hha ⟨j, by omega⟩ hj, ← e, Perm.apply_inv_self]
        have := congrArg Fin.val (ha e')
        simp only [im] at this
        omega
      obtain ⟨s, hs, hfix, hsx⟩ := hc m (by omega) _ hb hne
      refine ⟨h * s, H.mul_mem hh hs, fun i hi => ?_⟩
      rw [Perm.mul_apply]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · rw [hfix _ hi, hha i hi]
      · have : i = im := Fin.ext hi
        subst this
        rw [hsx, Perm.apply_inv_self]
  obtain ⟨h, hh, hha⟩ := key r le_rfl
  exact ⟨h, hh, fun i => hha i i.2⟩

/-- If the chain steps below `r` hold, `H` is transitive on the injective `r`-tuples of `Φ`:
map the first tuple back to `x` and then to the second. -/
theorem itCf_transOn_of_chain (hpres : ∀ h ∈ H, ∀ a ∈ Φ, h a ∈ Φ) (x : ℕ → Fin q) {r : ℕ}
    (hc : ∀ i < r, ItCfChain H Φ x i) : TransOn H Φ r := by
  intro a b ha hb haΦ hbΦ
  obtain ⟨ga, hga, hgax⟩ := itCf_chain_reach hpres x hc a ha haΦ
  obtain ⟨gb, hgb, hgbx⟩ := itCf_chain_reach hpres x hc b hb hbΦ
  refine ⟨gb * ga⁻¹, H.mul_mem hgb (H.inv_mem hga), fun i => ?_⟩
  rw [Perm.mul_apply, ← hgax i, Perm.inv_apply_self, hgbx i]

/-- If `H` is transitive on the injective `r`-tuples of `Φ` (with `r ≤ |Φ|`), every chain step
below `r` holds along an injective enumeration `x` of points of `Φ`: apply transitivity on
`(i+1)`-tuples (`TransOn.mono`) to `x 0, …, x i` and `x 0, …, x (i-1), b`. -/
theorem itCf_chain_of_transOn (x : ℕ → Fin q) {r : ℕ} (hr : r ≤ Φ.card) (ht : TransOn H Φ r)
    (hxΦ : ∀ i < r, x i ∈ Φ) (hxinj : ∀ i j, i < r → j < r → x i = x j → i = j) {i : ℕ}
    (hi : i < r) : ItCfChain H Φ x i := by
  intro b hb hbx
  have ht' := ht.mono (show i + 1 ≤ r by omega) hr
  let a : Fin (i + 1) → Fin q := fun j => x j
  let a' : Fin (i + 1) → Fin q := fun j => if j.val < i then x j else b
  have ha : Function.Injective a := fun j l e =>
    Fin.ext (hxinj _ _ (by omega) (by omega) e)
  have ha' : Function.Injective a' := by
    intro j l e
    simp only [a'] at e
    by_cases hj : j.val < i <;> by_cases hl : l.val < i <;> simp only [hj, hl, if_true,
      if_false] at e
    · exact Fin.ext (hxinj _ _ (by omega) (by omega) e)
    · exact absurd e.symm (hbx _ hj)
    · exact absurd e (hbx _ hl)
    · exact Fin.ext (by omega)
  obtain ⟨h, hh, hha⟩ := ht' a a' ha ha' (fun j => hxΦ _ (by omega)) (fun j => by
    simp only [a']; split_ifs
    · exact hxΦ _ (by omega)
    · exact hb)
  refine ⟨h, hh, fun j hj => ?_, ?_⟩
  · have := hha ⟨j, by omega⟩
    simpa [a, a', hj] using this
  · have := hha ⟨i, by omega⟩
    simpa [a, a'] using this

/-- **The degree of transitivity from the chain.** Let `x` enumerate points of `Φ` injectively
on the positions `< |Φ|`, and let `H` map `Φ` into itself. If the chain steps below `d` hold, and
the step `d` fails when `d < |Φ|`, then `transDeg H Φ = d`. -/
theorem itCf_transDeg_eq (hpres : ∀ h ∈ H, ∀ a ∈ Φ, h a ∈ Φ) (x : ℕ → Fin q)
    (hxΦ : ∀ i < Φ.card, x i ∈ Φ) (hxinj : ∀ i j, i < Φ.card → j < Φ.card → x i = x j → i = j)
    {d : ℕ} (hd : d ≤ Φ.card) (hok : ∀ i < d, ItCfChain H Φ x i)
    (hstop : d < Φ.card → ¬ ItCfChain H Φ x d) : transDeg H Φ = d := by
  obtain ⟨htr, hle⟩ := transDeg_spec H Φ
  have hge : d ≤ transDeg H Φ := le_transDeg hd (itCf_transOn_of_chain hpres x hok)
  refine le_antisymm (Nat.le_of_not_lt fun hlt => ?_) hge
  -- a degree above `d` gives the chain step `d`
  exact hstop (by omega) (itCf_chain_of_transOn x hle htr (fun i hi => hxΦ i (by omega))
    (fun i j hi hj => hxinj i j (by omega) (by omega)) hlt)

/-- **The chain step by positions.** When `x` enumerates `Φ` (injectively on the positions
`< |Φ|`, onto `Φ`), the step `i < |Φ|` says: for every position `j` with `i ≤ j < |Φ|` some
element of `H` fixing `x 0, …, x (i-1)` maps `x i` to `x j`. -/
theorem itCf_chain_iff (x : ℕ → Fin q) (hxinj : ∀ i j, i < Φ.card → j < Φ.card → x i = x j → i = j)
    (hxon : ∀ b ∈ Φ, ∃ j < Φ.card, x j = b) (hxΦ : ∀ i < Φ.card, x i ∈ Φ) {i : ℕ}
    (hi : i < Φ.card) :
    ItCfChain H Φ x i ↔ ∀ j, i ≤ j → j < Φ.card →
      ∃ h ∈ H, (∀ l < i, h (x l) = x l) ∧ h (x i) = x j := by
  constructor
  · intro hc j hij hj
    exact hc _ (hxΦ j hj) fun l hl e => by
      have := hxinj j l hj (by omega) e
      omega
  · intro hc b hb hbx
    obtain ⟨j, hj, rfl⟩ := hxon b hb
    have hij : i ≤ j := Nat.le_of_not_lt fun h => hbx j h rfl
    exact hc j hij hj

/-! ### The chain step as an orbit size -/

/-- Two stabilizer steps are one: fixing the points of `S` and then `α` is fixing `S ++ [α]`. -/
theorem itCf_pstab_snoc (S : List (Fin q)) (α : Fin q) :
    GI.Cited.pointwiseStab (GI.Cited.pointwiseStab H S) [α] =
      GI.Cited.pointwiseStab H (S ++ [α]) := by
  ext g
  simp only [GI.Cited.pointwiseStab, Subgroup.mem_mk, Set.mem_setOf_eq, List.mem_append,
    List.mem_singleton]
  constructor
  · rintro ⟨⟨hg, hS⟩, hα⟩
    exact ⟨hg, fun i hi => hi.elim (hS i) fun e => e ▸ hα α rfl⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨hg, fun i hi => h i (Or.inl hi)⟩, fun i hi => h i (Or.inr hi)⟩

/-- **The chain step as an orbit size.** Let `xs` list the points of `Φ` without repeats, let `x`
agree with `xs` on its positions, and let `H` map `Φ` into itself. Let `O` list without repeats
the orbit of `xs[j]` under the elements of `H` fixing the first `j` points. Then the step `j`
holds exactly when `O` has `|Φ| - j` points. The orbit lies in `Φ` and misses the first `j`
points, and these are the only `|Φ| - j` candidates. -/
theorem itCf_chain_iff_length (hpres : ∀ h ∈ H, ∀ a ∈ Φ, h a ∈ Φ) (xs : List (Fin q))
    (hnd : xs.Nodup) (hmem : ∀ b, b ∈ xs ↔ b ∈ Φ) (x : ℕ → Fin q)
    (hx : ∀ l (hl : l < xs.length), x l = xs[l]) {j : ℕ} (hj : j < xs.length)
    (O : List (Fin q)) (hO : O.Nodup)
    (hOm : ∀ y, y ∈ O ↔ ∃ g ∈ GI.Cited.pointwiseStab H (xs.take j), g (x j) = y) :
    ItCfChain H Φ x j ↔ O.length = Φ.card - j := by
  classical
  have hcard : xs.length = Φ.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext b
    simp [hmem]
  have hxinj : ∀ i l, i < Φ.card → l < Φ.card → x i = x l → i = l := by
    intro i l hi hl e
    rw [hx i (by omega), hx l (by omega)] at e
    exact (hnd.getElem_inj_iff).1 e
  have hxΦ : ∀ i < Φ.card, x i ∈ Φ := fun i hi => by
    rw [hx i (by omega), ← hmem]; exact List.getElem_mem _
  have hxon : ∀ b ∈ Φ, ∃ l < Φ.card, x l = b := by
    intro b hb
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem ((hmem b).2 hb)
    exact ⟨l, by omega, hx l hl⟩
  -- membership in the stabilizer of the first `j` points
  have hstab : ∀ g, g ∈ GI.Cited.pointwiseStab H (xs.take j) ↔
      g ∈ H ∧ ∀ l < j, g (x l) = x l := by
    intro g
    simp only [GI.Cited.pointwiseStab, Subgroup.mem_mk, Set.mem_setOf_eq]
    refine and_congr_right fun _ => ⟨fun h l hl => ?_, fun h i hi => ?_⟩
    · rw [hx l (by omega)]
      exact h _ (List.mem_iff_getElem.2 ⟨l, by simp; omega, by simp⟩)
    · obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hi
      simp only [List.length_take] at hl
      have := h l (by omega)
      rw [hx l (by omega)] at this
      simpa using this
  -- the candidates
  let T : Finset (Fin q) := ((Finset.range Φ.card).filter (j ≤ ·)).image x
  have hT : T.card = Φ.card - j := by
    rw [Finset.card_image_of_injOn]
    · rw [show (Finset.range Φ.card).filter (j ≤ ·) = Finset.Ico j Φ.card by
        ext l; simp [Finset.mem_Ico]; omega]
      simp
    · intro i hi l hl e
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hl
      exact hxinj i l hi.1 hl.1 e
  have hOT : O.toFinset ⊆ T := by
    intro y hy
    rw [List.mem_toFinset, hOm] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    obtain ⟨hgH, hfix⟩ := (hstab g).1 hg
    obtain ⟨l, hl, hxl⟩ := hxon _ (hpres g hgH _ (hxΦ j (by omega)))
    refine Finset.mem_image.2 ⟨l, Finset.mem_filter.2 ⟨Finset.mem_range.2 hl, ?_⟩, hxl⟩
    by_contra hlt
    have e : g (x j) = g (x l) := by rw [← hxl, hfix l (by omega)]
    have := hxinj j l (by omega) hl (g.injective e)
    omega
  have hlen : O.length = O.toFinset.card := (List.toFinset_card_of_nodup hO).symm
  rw [itCf_chain_iff x hxinj hxon hxΦ (by omega), hlen, ← hT]
  constructor
  · intro hc
    congr 1
    refine Finset.Subset.antisymm hOT fun y hy => ?_
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hl1, hl2⟩ := Finset.mem_filter.1 hl
    obtain ⟨g, hg, hfix, hgx⟩ := hc l hl2 (Finset.mem_range.1 hl1)
    rw [List.mem_toFinset, hOm]
    exact ⟨g, (hstab g).2 ⟨hg, hfix⟩, hgx⟩
  · intro he l hjl hl
    have hT' : O.toFinset = T := Finset.eq_of_subset_of_card_le hOT (by omega)
    have hy : x l ∈ O.toFinset := by
      rw [hT']
      exact Finset.mem_image.2 ⟨l, Finset.mem_filter.2 ⟨Finset.mem_range.2 hl, hjl⟩, rfl⟩
    rw [List.mem_toFinset, hOm] at hy
    obtain ⟨g, hg, hgx⟩ := hy
    obtain ⟨hgH, hfix⟩ := (hstab g).1 hg
    exact ⟨g, hgH, hfix, hgx⟩

end GI.Impl
