import Workspace.Impl.SCosBigMath2

/-!
# The mathematics of `bigF` (function 5), part 3

The cosets of the kernel `K` and the sizes of the blocks. Write `m` for the number of blocks
(labels of `lab`).

* `scosBM_ncard_le`: the orbit of `labN` under `labAct` has at most `(m + 1)^c` points. Two
  elements of `𝒢` whose inverses act alike on the blocks move `labN` to the same labeling
  (`scosBM_labAct_eq_of_agree`); one inverse per orbit point gives a set to which `ScosPalfyC`
  applies.
* `scosBM_length_le`, `scosBM_cover`: on the output list `L` of `cosets_spec`, `|L| ≤ (m + 1)^c`,
  and the pairs `ts` behind its permutations lie in `𝒢` and meet every left coset of `K`.
* `scosBM_blocks`, `scosBM_mo_lt`: `2 ≤ m`, the blocks all have one size `s`, `m s ≤ |Φ|`, and
  the orbits of `K` on `Φ` have at most `s < |Φ|` points.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved GI.Algorithm GI.Assembly Equiv

variable {n : ℕ}

section
variable (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) (hinv : ScosInv 𝒢 Φ)
  (lab : Fin (scosBMk Φ) → ℕ)

/-- `labAct (nintSum g) labN` only depends on how the restriction of `g⁻¹` acts on the blocks. -/
theorem scosBM_labAct_eq_of_agree {g g' : ScosPair n} (hg : g ∈ 𝒢) (hg' : g' ∈ 𝒢)
    (hag : ∀ i, lab (scosBMPsi 𝒢 Φ hinv ⟨(g⁻¹).1, Subgroup.mem_map_of_mem _ (inv_mem hg)⟩ i) =
      lab (scosBMPsi 𝒢 Φ hinv ⟨(g'⁻¹).1, Subgroup.mem_map_of_mem _ (inv_mem hg')⟩ i)) :
    labAct (nintSum g) (scosBMLab Φ lab) = labAct (nintSum g') (scosBMLab Φ lab) := by
  funext x
  simp only [labAct, ← map_inv]
  by_cases hx : x ∈ scosPhiF Φ
  · obtain ⟨a, ha, rfl⟩ := scosBM_mem_phiF hx
    rw [scosBMLab_nint 𝒢 Φ hinv lab (inv_mem hg) ha, scosBMLab_nint 𝒢 Φ hinv lab (inv_mem hg') ha]
    exact hag _
  · rw [scosBMLab_off Φ lab (mt (scosBM_nint_mem_iff 𝒢 Φ hinv (inv_mem hg) x).1 hx),
      scosBMLab_off Φ lab (mt (scosBM_nint_mem_iff 𝒢 Φ hinv (inv_mem hg') x).1 hx)]

/-- **The number of cosets.** -/
theorem scosBM_ncard_le {c : ℕ} (hc : ScosPalfyC c) (htr : ScosTrans 𝒢 Φ)
    (hsol : IsSolvable (𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n)))))
    (hmb : IsMinimalBlocks (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv)).range lab)
    (gs : List (Perm (Fin (n + n)))) (hgs : genGroup gs = 𝒢.map nintSum) :
    (actOrbit labAct gs (scosBMLab Φ lab)).ncard ≤ ((Finset.univ.image lab).card + 1) ^ c := by
  classical
  set O := actOrbit labAct gs (scosBMLab Φ lab) with hO
  have hfin : O.Finite :=
    (Set.finite_range fun h : Perm (Fin (n + n)) => labAct h (scosBMLab Φ lab)).subset
      (by rintro y ⟨h, -, rfl⟩; exact ⟨h, rfl⟩)
  have hex : ∀ y ∈ O, ∃ g, ∃ _ : g ∈ 𝒢, labAct (nintSum g) (scosBMLab Φ lab) = y := by
    rintro y ⟨h, hh, rfl⟩
    rw [hgs] at hh
    obtain ⟨g, hg, rfl⟩ := hh
    exact ⟨g, hg, rfl⟩
  let sel : (Fin (n + n) → ℕ) → Perm (Fin (scosBMk Φ)) := fun y =>
    if hy : ∃ g, ∃ _ : g ∈ 𝒢, labAct (nintSum g) (scosBMLab Φ lab) = y then
      scosBMPsi 𝒢 Φ hinv ⟨(hy.choose⁻¹).1,
        Subgroup.mem_map_of_mem _ (inv_mem hy.choose_spec.choose)⟩
    else 1
  have hsel : ∀ y ∈ O, ∃ g, ∃ hg : g ∈ 𝒢, labAct (nintSum g) (scosBMLab Φ lab) = y ∧
      sel y = scosBMPsi 𝒢 Φ hinv ⟨(g⁻¹).1, Subgroup.mem_map_of_mem _ (inv_mem hg)⟩ := by
    intro y hy
    have hy' := hex y hy
    refine ⟨hy'.choose, hy'.choose_spec.choose, hy'.choose_spec.choose_spec, ?_⟩
    simp only [sel, dif_pos hy']
  have hinj : ∀ y ∈ O, ∀ z ∈ O, (∀ i, lab (sel y i) = lab (sel z i)) → y = z := by
    intro y hy z hz hag
    obtain ⟨g, hg, rfl, hgy⟩ := hsel y hy
    obtain ⟨g', hg', rfl, hgz⟩ := hsel z hz
    rw [hgy, hgz] at hag
    exact scosBM_labAct_eq_of_agree 𝒢 Φ hinv lab hg hg' hag
  set S := hfin.toFinset.image sel with hS
  have hSmem : ∀ s ∈ S, s ∈ (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv)).range := by
    intro s hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨g, hg, -, hgy⟩ := hsel y (hfin.mem_toFinset.1 hy)
    rw [hgy]
    exact (scosBM_mem_range 𝒢 Φ hinv).2 ⟨g⁻¹, inv_mem hg, rfl⟩
  have hSag : ∀ s ∈ S, ∀ t ∈ S, (∀ i, lab (s i) = lab (t i)) → s = t := by
    intro s hs t ht hag
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ht
    rw [hinj y (hfin.mem_toFinset.1 hy) z (hfin.mem_toFinset.1 hz) hag]
  have hcard : S.card = hfin.toFinset.card := by
    refine Finset.card_image_of_injOn ?_
    intro y hy z hz hyz
    exact hinj y (hfin.mem_toFinset.1 hy) z (hfin.mem_toFinset.1 hz) (fun i => by rw [hyz])
  have hP := hc _ _ lab (scosBM_solvable 𝒢 Φ hinv hsol) (scosBM_trans 𝒢 Φ hinv htr) hmb S hSmem
    hSag
  rw [Set.ncard_eq_toFinset_card O hfin, ← hcard]
  exact hP

/-- The bound `(m + 1)^c` is at most the bound `(n + n + 1)^c` given to `cosets_spec`. -/
theorem scosBM_pow_le (c : ℕ) :
    ((Finset.univ.image lab).card + 1) ^ c ≤ (n + n + 1) ^ c := by
  apply Nat.pow_le_pow_left
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin (scosBMk Φ)))) (f := lab)
  have h2 := Finset.card_le_univ Φ
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h3 := scosBMk_eq Φ
  simp only [Fintype.card_fin] at h2
  omega

/-- **The length of the list of cosets.** -/
theorem scosBM_length_le {c : ℕ} (hc : ScosPalfyC c) (htr : ScosTrans 𝒢 Φ)
    (hsol : IsSolvable (𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n)))))
    (hmb : IsMinimalBlocks (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv)).range lab)
    (gs : List (Perm (Fin (n + n)))) (hgs : genGroup gs = 𝒢.map nintSum)
    (L : List ((Fin (n + n) → ℕ) × Perm (Fin (n + n)))) (hnd : (L.map Prod.fst).Nodup)
    (hL : ∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit labAct gs (scosBMLab Φ lab)) :
    L.length ≤ ((Finset.univ.image lab).card + 1) ^ c := by
  classical
  have h := scosBM_ncard_le 𝒢 Φ hinv lab hc htr hsol hmb gs hgs
  have hset : ((L.map Prod.fst).toFinset : Set (Fin (n + n) → ℕ)) =
      actOrbit labAct gs (scosBMLab Φ lab) := by
    ext y
    rw [Finset.mem_coe, List.mem_toFinset]
    exact hL y
  rw [← hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map] at h
  exact h

/-- **The pairs behind the cosets.** -/
theorem scosBM_cover (gs : List (Perm (Fin (n + n)))) (hgs : genGroup gs = 𝒢.map nintSum)
    (L : List ((Fin (n + n) → ℕ) × Perm (Fin (n + n))))
    (hL : ∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit labAct gs (scosBMLab Φ lab))
    (hp : ∀ p ∈ L, p.2 ∈ genGroup gs ∧ labAct p.2 (scosBMLab Φ lab) = p.1) :
    ∃ ts : List (ScosPair n), L.map Prod.snd = ts.map nintSum ∧ (∀ t ∈ ts, t ∈ 𝒢) ∧
      ∀ g ∈ 𝒢, ∃ t ∈ ts, t⁻¹ * g ∈ scosBMKer 𝒢 Φ lab := by
  obtain ⟨l', hl'⟩ := nint_list_lift (fun t : 𝒢 => nintSum (t : ScosPair n)) (L.map Prod.snd)
    (by
      intro b hb
      obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hb
      have h1 := (hp p hp').1
      rw [hgs] at h1
      obtain ⟨g, hg, hgp⟩ := h1
      exact ⟨⟨g, hg⟩, hgp⟩)
  refine ⟨l'.map Subtype.val, by rw [← hl', List.map_map]; rfl, ?_, ?_⟩
  · intro t ht
    obtain ⟨t', -, rfl⟩ := List.mem_map.1 ht
    exact t'.2
  · intro g hg
    have hy : labAct (nintSum g) (scosBMLab Φ lab) ∈ actOrbit labAct gs (scosBMLab Φ lab) :=
      ⟨nintSum g, by rw [hgs]; exact Subgroup.mem_map_of_mem _ hg, rfl⟩
    obtain ⟨p, hpL, hp1⟩ := List.mem_map.1 ((hL _).2 hy)
    have hp2 : p.2 ∈ L.map Prod.snd := List.mem_map_of_mem hpL
    rw [← hl'] at hp2
    obtain ⟨t', ht', ht'p⟩ := List.mem_map.1 hp2
    refine ⟨t', List.mem_map_of_mem ht', ?_⟩
    have ht : (t' : ScosPair n) ∈ 𝒢 := t'.2
    rw [← scosBM_labAct_nint_iff 𝒢 Φ lab (mul_mem (inv_mem ht) hg), map_mul, isAct_lab.mul,
      ← hp1, ← (hp p hpL).2, ← ht'p, ← isAct_lab.mul, map_inv, inv_mul_cancel, isAct_lab.one]

/-! ### Blocks -/

/-- In a transitive group, the blocks of an invariant labeling have one size. -/
theorem scosBM_block_card_le {k : ℕ} {H : Subgroup (Perm (Fin k))} {f : Fin k → ℕ}
    (hf : InvariantLabeling H f) (htr : ∀ i j : Fin k, ∃ h ∈ H, h i = j) (i j : Fin k) :
    (Finset.univ.filter fun x => f x = f i).card ≤ (Finset.univ.filter fun x => f x = f j).card := by
  obtain ⟨h, hh, rfl⟩ := htr i j
  refine Finset.card_le_card_of_injOn h ?_ (fun x _ y _ hxy => h.injective hxy)
  intro x hx
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
  exact (hf h hh x i).2 hx

/-- **The blocks.** `2 ≤ m`, and there is a block size `s ≥ 1` with `m s ≤ |Φ|` that bounds
every orbit of `K` on `Φ`. -/
theorem scosBM_blocks (htr : ScosTrans 𝒢 Φ) (h2 : 2 ≤ Φ.card)
    (hmb : IsMinimalBlocks (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv)).range lab) :
    2 ≤ (Finset.univ.image lab).card ∧ ∃ s, 1 ≤ s ∧ (Finset.univ.image lab).card * s ≤ Φ.card ∧
      scosMo (scosBMKer 𝒢 Φ lab) Φ ≤ s := by
  classical
  have hk : 2 ≤ scosBMk Φ := by rw [scosBMk_eq]; exact h2
  have htrH := scosBM_trans 𝒢 Φ hinv htr
  set B : Fin (scosBMk Φ) → ℕ := fun i => (Finset.univ.filter fun x => lab x = lab i).card with hB
  have hBeq : ∀ i j, B i = B j := fun i j =>
    le_antisymm (scosBM_block_card_le hmb.1 htrH i j) (scosBM_block_card_le hmb.1 htrH j i)
  let j0 : Fin (scosBMk Φ) := ⟨0, by omega⟩
  refine ⟨?_, B j0, ?_, ?_, ?_⟩
  · obtain ⟨i, j, hij⟩ := hmb.2.1
    have hsub : ({lab i, lab j} : Finset ℕ) ⊆ Finset.univ.image lab := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hij] at this
  · exact Finset.card_pos.2 ⟨j0, by simp⟩
  · have hsum := Finset.card_eq_sum_card_image lab (Finset.univ : Finset (Fin (scosBMk Φ)))
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    have h3 := scosBMk_eq Φ
    have h4 : (Finset.univ.image lab).card * B j0 =
        ∑ b ∈ Finset.univ.image lab, (Finset.univ.filter fun a => lab a = b).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
      refine Finset.sum_congr rfl fun ℓ hℓ => ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hℓ
      exact (hBeq i j0).symm
    omega
  · unfold scosMo
    refine Finset.sup_le fun a ha => ?_
    rw [← hBeq ((scosBME Φ).symm ⟨a, ha⟩) j0]
    let f : Fin n → Fin (scosBMk Φ) := fun b =>
      if hb : b ∈ Φ then (scosBME Φ).symm ⟨b, hb⟩ else (scosBME Φ).symm ⟨a, ha⟩
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro b hb
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hb
      obtain ⟨hbΦ, g, hgK, rfl⟩ := hb
      have hg := scosBMKer_le 𝒢 Φ lab hgK
      have hfix := ((mem_scosBMKer 𝒢 Φ lab).1 hgK).2 (Fin.castAdd n a)
      rw [scosBMLab_nint 𝒢 Φ hinv lab hg ha, scosBMLab_castAdd Φ lab ha, scosBMPsi_symm] at hfix
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, f, dif_pos hbΦ]
      exact hfix
    · intro b hb b' hb' hbb
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hb hb'
      simp only [f, dif_pos hb.1, dif_pos hb'.1] at hbb
      exact congrArg Subtype.val ((scosBME Φ).symm.injective hbb)

/-- **The orbits of `K` on `Φ` are smaller than `Φ`.** -/
theorem scosBM_mo_lt (htr : ScosTrans 𝒢 Φ) (h2 : 2 ≤ Φ.card)
    (hmb : IsMinimalBlocks (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv)).range lab) :
    scosMo (scosBMKer 𝒢 Φ lab) Φ < Φ.card := by
  obtain ⟨hm, s, hs, hms, hmo⟩ := scosBM_blocks 𝒢 Φ hinv lab htr h2 hmb
  have : 2 * s ≤ (Finset.univ.image lab).card * s := Nat.mul_le_mul_right s hm
  omega

end

end GI.Impl
