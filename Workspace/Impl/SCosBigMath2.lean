import Workspace.Impl.SCosBigMath1

/-!
# The mathematics of `bigF` (function 5), part 2

The minimal block labels `lab` of the restricted group are pulled back to `Fin (n + n)`:
`scosBMLab Φ lab` gives the point at position `j` of `D` the label `lab j`, and every other point
the label `k` (this is the list `gather (lab ++ [k]) posVal` of the program).

* `scosBMLab_castAdd`, `scosBMLab_nint`, `scosBMLab_off`: its values.
* `scosBM_pres`: `G'` preserves the partition into labels (the hypothesis of `ker_spec`), and
  `scosBMLab_le`: the labels are at most `n + n` (for `cosets_spec`).
* `scosBMKer`: the kernel `K`, the pairs of `𝒢` that fix every label; `mem_map_scosBMKer`
  identifies the output of `ker_spec`, and `scosBM_labAct_eq_iff` the fixed points of `labAct`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved GI.Algorithm GI.Assembly Equiv

variable {n : ℕ}

/-- **The labels on `Fin (n + n)`.** -/
noncomputable def scosBMLab (Φ : Finset (Fin n)) (lab : Fin (scosBMk Φ) → ℕ) (i : Fin (n + n)) :
    ℕ :=
  ((List.finRange (scosBMk Φ)).map lab ++ [scosBMk Φ]).getD
    (posOf (domNat (Equiv.refl _) (scosPhiF Φ)) i) 0

section
variable (Φ : Finset (Fin n)) (lab : Fin (scosBMk Φ) → ℕ)

theorem scosBMLab_castAdd {a : Fin n} (ha : a ∈ Φ) :
    scosBMLab Φ lab (Fin.castAdd n a) = lab ((scosBME Φ).symm ⟨a, ha⟩) := by
  unfold scosBMLab
  rw [← scosBME_symm_val Φ ha]
  set j := (scosBME Φ).symm ⟨a, ha⟩
  rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem scosBMLab_off {x : Fin (n + n)} (hx : x ∉ scosPhiF Φ) : scosBMLab Φ lab x = scosBMk Φ := by
  unfold scosBMLab
  have hp : posOf (domNat (Equiv.refl _) (scosPhiF Φ)) x = scosBMk Φ := by
    unfold posOf
    rw [List.findIdx_eq_length.2, length_domNat]
    intro y hy
    simp only [decide_eq_false_iff_not]
    rintro rfl
    obtain ⟨j, hj, hjx⟩ := List.mem_map.1 hy
    have hj' := mem_domFin.1 hj
    have : j = x := Fin.ext hjx
    subst this
    exact hx hj'
  rw [hp, List.getD_eq_getElem _ _ (by simp)]
  simp

theorem scosBMLab_lt (hlt : ∀ j, lab j < scosBMk Φ) {x : Fin (n + n)} (hx : x ∈ scosPhiF Φ) :
    scosBMLab Φ lab x < scosBMk Φ := by
  obtain ⟨a, ha, rfl⟩ := scosBM_mem_phiF hx
  rw [scosBMLab_castAdd Φ lab ha]
  exact hlt _

/-- **The labels are at most `n + n`** (the hypothesis `hlab` of `cosets_spec`). -/
theorem scosBMLab_le (hlt : ∀ j, lab j < scosBMk Φ) (x : Fin (n + n)) :
    scosBMLab Φ lab x ≤ n + n := by
  have hk : scosBMk Φ ≤ n + n := by
    rw [scosBMk_eq]
    have := Finset.card_le_univ Φ
    simp only [Fintype.card_fin] at this
    omega
  by_cases hx : x ∈ scosPhiF Φ
  · exact (scosBMLab_lt Φ lab hlt hx).le.trans hk
  · rw [scosBMLab_off Φ lab hx]; exact hk

end

section
variable (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) (hinv : ScosInv 𝒢 Φ)
  (lab : Fin (scosBMk Φ) → ℕ)

/-- The label of `nintSum g (castAdd a)` is the label of the restricted image of the position
of `a`. -/
theorem scosBMLab_nint {g : ScosPair n} (hg : g ∈ 𝒢) {a : Fin n} (ha : a ∈ Φ) :
    scosBMLab Φ lab (nintSum g (Fin.castAdd n a)) =
      lab (scosBMPsi 𝒢 Φ hinv ⟨g.1, Subgroup.mem_map_of_mem _ hg⟩ ((scosBME Φ).symm ⟨a, ha⟩)) := by
  rw [scosBMPsi_symm, scosBM_castAdd, scosBMLab_castAdd]

/-- **`G'` preserves the partition into labels** (the hypothesis `hpres` of `ker_spec`). -/
theorem scosBM_pres (lab : Fin (scosBMk Φ) → ℕ) (hlt : ∀ j, lab j < scosBMk Φ)
    (hmb : IsMinimalBlocks (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv)).range lab) :
    ∀ h ∈ 𝒢.map nintSum, ∀ i j, scosBMLab Φ lab (h i) = scosBMLab Φ lab (h j) ↔
      scosBMLab Φ lab i = scosBMLab Φ lab j := by
  rintro _ ⟨g, hg, rfl⟩ i j
  have hm := scosBM_nint_mem_iff 𝒢 Φ hinv hg
  by_cases hi : i ∈ scosPhiF Φ <;> by_cases hj : j ∈ scosPhiF Φ
  · obtain ⟨a, ha, rfl⟩ := scosBM_mem_phiF hi
    obtain ⟨b, hb, rfl⟩ := scosBM_mem_phiF hj
    rw [scosBMLab_nint 𝒢 Φ hinv lab hg ha, scosBMLab_nint 𝒢 Φ hinv lab hg hb,
      scosBMLab_castAdd Φ lab ha, scosBMLab_castAdd Φ lab hb]
    exact hmb.1 _ ((scosBM_mem_range 𝒢 Φ hinv).2 ⟨g, hg, rfl⟩) _ _
  · have h1 := scosBMLab_lt Φ lab hlt ((hm i).2 hi)
    have h2 := scosBMLab_off Φ lab (mt (hm j).1 hj)
    have h3 := scosBMLab_lt Φ lab hlt hi
    have h4 := scosBMLab_off Φ lab hj
    constructor <;> intro h <;> omega
  · have h1 := scosBMLab_lt Φ lab hlt ((hm j).2 hj)
    have h2 := scosBMLab_off Φ lab (mt (hm i).1 hi)
    have h3 := scosBMLab_lt Φ lab hlt hj
    have h4 := scosBMLab_off Φ lab hi
    constructor <;> intro h <;> omega
  · rw [scosBMLab_off Φ lab (mt (hm i).1 hi), scosBMLab_off Φ lab (mt (hm j).1 hj),
      scosBMLab_off Φ lab hi, scosBMLab_off Φ lab hj]

/-! ### The kernel -/

/-- The permutations that fix every label. -/
def scosBMFix (f : Fin (n + n) → ℕ) : Subgroup (Perm (Fin (n + n))) where
  carrier := {h | ∀ i, f (h i) = f i}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb i
    simp only [Set.mem_setOf_eq, Perm.mul_apply] at *
    rw [ha, hb]
  inv_mem' := by
    intro a ha i
    simp only [Set.mem_setOf_eq] at *
    rw [← ha (a⁻¹ i), Perm.apply_inv_self]

/-- **The kernel `K`**: the pairs of `𝒢` that fix every label of `scosBMLab Φ lab`. -/
noncomputable def scosBMKer (lab : Fin (scosBMk Φ) → ℕ) : Subgroup (ScosPair n) :=
  𝒢 ⊓ (scosBMFix (scosBMLab Φ lab)).comap nintSum

theorem scosBMKer_le : scosBMKer 𝒢 Φ lab ≤ 𝒢 := inf_le_left

theorem mem_scosBMKer {g : ScosPair n} :
    g ∈ scosBMKer 𝒢 Φ lab ↔ g ∈ 𝒢 ∧ ∀ i, scosBMLab Φ lab (nintSum g i) = scosBMLab Φ lab i :=
  Iff.rfl

/-- **The image of the kernel** is the output of `ker_spec` with `R i j := labN i = labN j`. -/
theorem mem_map_scosBMKer (h : Perm (Fin (n + n))) :
    h ∈ (scosBMKer 𝒢 Φ lab).map nintSum ↔
      h ∈ 𝒢.map nintSum ∧ ∀ i, scosBMLab Φ lab (h i) = scosBMLab Φ lab i := by
  constructor
  · rintro ⟨g, ⟨hg, hk⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem _ hg, hk⟩
  · rintro ⟨⟨g, hg, rfl⟩, hk⟩
    exact ⟨g, ⟨hg, hk⟩, rfl⟩

/-- `h` fixes `f` under `labAct` exactly when it fixes every label. -/
theorem scosBM_labAct_eq_iff (f : Fin (n + n) → ℕ) (h : Perm (Fin (n + n))) :
    labAct h f = f ↔ ∀ i, f (h i) = f i := by
  rw [funext_iff]
  constructor
  · intro H i
    have := H (h i)
    simpa [labAct] using this.symm
  · intro H i
    simp only [labAct]
    have := H (h⁻¹ i)
    rw [Perm.apply_inv_self] at this
    exact this.symm

/-- **An element of `G'` fixes `labN` under `labAct` exactly when it lies in `K.map nintSum`.** -/
theorem scosBM_labAct_eq_iff_mem {h : Perm (Fin (n + n))} (hh : h ∈ 𝒢.map nintSum) :
    labAct h (scosBMLab Φ lab) = scosBMLab Φ lab ↔ h ∈ (scosBMKer 𝒢 Φ lab).map nintSum := by
  rw [scosBM_labAct_eq_iff, mem_map_scosBMKer]
  exact ⟨fun H => ⟨hh, H⟩, fun H => H.2⟩

/-- For a pair `g ∈ 𝒢`: `labAct (nintSum g) labN = labN` exactly when `g ∈ K`. -/
theorem scosBM_labAct_nint_iff {g : ScosPair n} (hg : g ∈ 𝒢) :
    labAct (nintSum g) (scosBMLab Φ lab) = scosBMLab Φ lab ↔ g ∈ scosBMKer 𝒢 Φ lab := by
  rw [scosBM_labAct_eq_iff, mem_scosBMKer]
  exact ⟨fun H => ⟨hg, H⟩, fun H => H.2⟩

/-- **`K` is a problem group**: solvable first coordinates, and `Φ` invariant. -/
theorem scosBMKer_solvable
    (hsol : IsSolvable (𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n))))) :
    IsSolvable ((scosBMKer 𝒢 Φ lab).map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n)))) :=
  solvable_of_solvable_injective
    (Subgroup.inclusion_injective (Subgroup.map_mono (scosBMKer_le 𝒢 Φ lab)))

include hinv in
theorem scosBMKer_inv : ScosInv (scosBMKer 𝒢 Φ lab) Φ :=
  fun g hg a ha => hinv g (scosBMKer_le 𝒢 Φ lab hg) a ha

end

end GI.Impl
