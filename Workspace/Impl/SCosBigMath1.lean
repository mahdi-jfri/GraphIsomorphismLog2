module

public import Workspace.Impl.SCosSpec

@[expose] public section

/-!
# The mathematics of `bigF` (function 5), part 1

`bigF` restricts the group `G' = 𝒢.map nintSum` to the set `D = scosPhiF Φ` of the points of the
first copy that lie in `Φ`, read on the positions `0, …, k - 1` of `D` (`restrK`, with
`e = Equiv.refl`). Here we show that this restriction only sees the first coordinates on `Φ`.

* `scosBM_invariant`: `D` is invariant under `G'`.
* `scosBME : Fin k ≃ Φ`: position `j` of `D` is the point `castAdd (scosBME Φ j)`.
* `scosBMPsi`: the action of the first coordinates of `𝒢` on `Φ`, read on the positions. Its
  range is the restricted group (`scosBM_range`), so the restricted group is solvable
  (`scosBM_solvable`) and transitive (`scosBM_trans`), and `k = |Φ|` (`scosBMk_eq`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved GI.Algorithm GI.Assembly Equiv

variable {n : ℕ}

/-- The number `k` of positions of `D = scosPhiF Φ`. -/
noncomputable abbrev scosBMk (Φ : Finset (Fin n)) : ℕ := (domFin (Equiv.refl (Fin (n + n))) (scosPhiF Φ)).length

theorem scosBM_castAdd (g : ScosPair n) (a : Fin n) :
    nintSum g (Fin.castAdd n a) = Fin.castAdd n (g.1 a) :=
  Fin.ext (by rw [nintSum_apply, sumToFin_sumCongr_castAdd]; rfl)

theorem scosBM_natAdd (g : ScosPair n) (b : Fin n) :
    nintSum g (Fin.natAdd n b) = Fin.natAdd n (g.2 b) :=
  Fin.ext (by rw [nintSum_apply, sumToFin_sumCongr_natAdd]; rfl)

theorem scosBM_mem_castAdd (Φ : Finset (Fin n)) {a : Fin n} :
    Fin.castAdd n a ∈ scosPhiF Φ ↔ a ∈ Φ := by
  simp only [scosPhiF, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨b, hb, h⟩
    rwa [← Fin.castAdd_injective n n h]
  · exact fun h => ⟨a, h, rfl⟩

theorem scosBM_natAdd_not (Φ : Finset (Fin n)) (b : Fin n) : Fin.natAdd n b ∉ scosPhiF Φ := by
  rintro ⟨a, -, h⟩
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

/-- The points of `D` are the `castAdd a` with `a ∈ Φ`. -/
theorem scosBM_mem_phiF {Φ : Finset (Fin n)} {x : Fin (n + n)} (hx : x ∈ scosPhiF Φ) :
    ∃ a ∈ Φ, x = Fin.castAdd n a := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, rfl⟩

section
variable (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n))

/-- The first coordinate of an element of `𝒢` maps `Φ` onto itself. -/
theorem scosBM_mem_iff (hinv : ScosInv 𝒢 Φ) {g : ScosPair n} (hg : g ∈ 𝒢) (a : Fin n) :
    g.1 a ∈ Φ ↔ a ∈ Φ := by
  refine ⟨fun h => ?_, fun h => hinv g hg a h⟩
  have := scos_perm_onto (fun b hb => hinv g hg b hb) h
  rwa [Perm.inv_apply_self] at this

theorem scosBM_fst_mem_iff (hinv : ScosInv 𝒢 Φ) {σ : Perm (Fin n)}
    (hσ : σ ∈ 𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n)))) (a : Fin n) :
    σ a ∈ (Φ : Set (Fin n)) ↔ a ∈ (Φ : Set (Fin n)) := by
  obtain ⟨g, hg, rfl⟩ := hσ
  exact scosBM_mem_iff 𝒢 Φ hinv hg a

/-- **`D` is invariant under `G'`.** -/
theorem scosBM_invariant (hinv : ScosInv 𝒢 Φ) : Invariant (𝒢.map nintSum) (scosPhiF Φ) := by
  rintro _ ⟨g, hg, rfl⟩ v
  induction v using Fin.addCases with
  | left a =>
    rw [scosBM_castAdd, scosBM_mem_castAdd, scosBM_mem_castAdd]
    exact scosBM_mem_iff 𝒢 Φ hinv hg a
  | right b =>
    rw [scosBM_natAdd]
    exact iff_of_false (scosBM_natAdd_not Φ _) (scosBM_natAdd_not Φ _)

/-- An element of `G'` maps `D` onto itself (`scosBM_invariant`, unfolded for `nintSum g`). -/
theorem scosBM_nint_mem_iff (hinv : ScosInv 𝒢 Φ) {g : ScosPair n} (hg : g ∈ 𝒢) (x : Fin (n + n)) :
    nintSum g x ∈ scosPhiF Φ ↔ x ∈ scosPhiF Φ :=
  scosBM_invariant 𝒢 Φ hinv _ (Subgroup.mem_map_of_mem _ hg) x

end

/-! ### Positions of `D` and points of `Φ` -/

/-- Position `j` of `D` is the point `castAdd (scosBME Φ j)`. -/
noncomputable def scosBME (Φ : Finset (Fin n)) : Fin (scosBMk Φ) ≃ (Φ : Set (Fin n)) :=
  (domEquiv (Equiv.refl _) (scosPhiF Φ)).symm.trans
    (Equiv.Set.image (Fin.castAdd n) (Φ : Set (Fin n)) (Fin.castAdd_injective n n)).symm

theorem scosBME_castAdd (Φ : Finset (Fin n)) (j : Fin (scosBMk Φ)) :
    Fin.castAdd n (scosBME Φ j : Fin n) =
      ((domEquiv (Equiv.refl _) (scosPhiF Φ)).symm j : Fin (n + n)) := by
  have := (Equiv.Set.image (Fin.castAdd n) (Φ : Set (Fin n)) (Fin.castAdd_injective n n)).apply_symm_apply
    ((domEquiv (Equiv.refl _) (scosPhiF Φ)).symm j)
  exact congrArg Subtype.val this

theorem scosBME_symm (Φ : Finset (Fin n)) {a : Fin n} (ha : a ∈ Φ) :
    (scosBME Φ).symm ⟨a, ha⟩ =
      domEquiv (Equiv.refl _) (scosPhiF Φ) ⟨Fin.castAdd n a, (scosBM_mem_castAdd Φ).2 ha⟩ := by
  apply (scosBME Φ).injective
  apply Subtype.ext
  apply Fin.castAdd_injective n n
  rw [Equiv.apply_symm_apply, scosBME_castAdd, Equiv.symm_apply_apply]

/-- The position of the point `castAdd a` of `D`. -/
theorem scosBME_symm_val (Φ : Finset (Fin n)) {a : Fin n} (ha : a ∈ Φ) :
    (((scosBME Φ).symm ⟨a, ha⟩ : Fin (scosBMk Φ)) : ℕ) =
      posOf (domNat (Equiv.refl _) (scosPhiF Φ)) (Fin.castAdd n a) := by
  rw [scosBME_symm, domEquiv_apply]
  rfl

/-- **`k = |Φ|`.** -/
theorem scosBMk_eq (Φ : Finset (Fin n)) : scosBMk Φ = Φ.card := by
  have := Fintype.card_congr (scosBME Φ)
  simpa using this

/-! ### The first coordinates on the positions -/

section
variable (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) (hinv : ScosInv 𝒢 Φ)

/-- The action of the first coordinates of `𝒢` on `Φ`, read on the positions of `D`. -/
noncomputable def scosBMPsi :
    𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n))) →* Perm (Fin (scosBMk Φ)) where
  toFun σ := (scosBME Φ).symm.permCongr
    ((σ : Perm (Fin n)).subtypePerm (scosBM_fst_mem_iff 𝒢 Φ hinv σ.2))
  map_one' := by ext; simp [Equiv.permCongr_apply]
  map_mul' σ τ := by ext; simp [Equiv.permCongr_apply]

theorem scosBMPsi_apply (σ : 𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n))))
    (j : Fin (scosBMk Φ)) :
    (scosBME Φ (scosBMPsi 𝒢 Φ hinv σ j) : Fin n) = (σ : Perm (Fin n)) (scosBME Φ j) := by
  simp [scosBMPsi, Equiv.permCongr_apply]

theorem scosBMPsi_symm (σ : 𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n))))
    {a : Fin n} (ha : a ∈ Φ) :
    scosBMPsi 𝒢 Φ hinv σ ((scosBME Φ).symm ⟨a, ha⟩) =
      (scosBME Φ).symm ⟨(σ : Perm (Fin n)) a, (scosBM_fst_mem_iff 𝒢 Φ hinv σ.2 a).2 ha⟩ := by
  apply (scosBME Φ).injective
  apply Subtype.ext
  rw [scosBMPsi_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **The restriction of `nintSum g` to `D` is `scosBMPsi` of `g.1`.** -/
theorem scosBM_restrK {x : Perm (Fin (n + n))}
    (hx : x ∈ groupFin (Equiv.refl _) (𝒢.map nintSum)) {g : ScosPair n} (hg : g ∈ 𝒢)
    (hxg : ∀ i, x i = nintSum g i) :
    restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ) (scosBM_invariant 𝒢 Φ hinv) ⟨x, hx⟩ =
      scosBMPsi 𝒢 Φ hinv ⟨g.1, Subgroup.mem_map_of_mem _ hg⟩ := by
  ext j
  have key : ((domEquiv (Equiv.refl _) (scosPhiF Φ)).symm
      (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ) (scosBM_invariant 𝒢 Φ hinv) ⟨x, hx⟩ j) :
        Fin (n + n)) = x ((domEquiv (Equiv.refl _) (scosPhiF Φ)).symm j) := by
    simp only [restrK, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      toFin_apply, Equiv.symm_apply_apply, restrictHom_apply, finIso_symm_apply]
    rfl
  have h2 : (scosBME Φ (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv) ⟨x, hx⟩ j) : Fin n) =
        (scosBME Φ (scosBMPsi 𝒢 Φ hinv ⟨g.1, Subgroup.mem_map_of_mem _ hg⟩ j) : Fin n) := by
    apply Fin.castAdd_injective n n
    rw [scosBMPsi_apply, scosBME_castAdd, key, hxg, ← scosBME_castAdd, scosBM_castAdd]
  exact congrArg Fin.val ((scosBME Φ).injective (Subtype.ext h2))

/-- **The restricted group is the range of `scosBMPsi`.** -/
theorem scosBM_range :
    (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ) (scosBM_invariant 𝒢 Φ hinv)).range =
      (scosBMPsi 𝒢 Φ hinv).range := by
  ext σ
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨h, ⟨g, hg, rfl⟩, rfl⟩ := mem_groupFin.1 hx
    exact ⟨_, (scosBM_restrK 𝒢 Φ hinv hx hg fun _ => rfl).symm⟩
  · rintro ⟨⟨σ, hσ⟩, rfl⟩
    obtain ⟨g, hg, rfl⟩ := hσ
    have hx : nintSum g ∈ groupFin (Equiv.refl _) (𝒢.map nintSum) :=
      mem_groupFin.2 ⟨nintSum g, Subgroup.mem_map_of_mem _ hg, rfl⟩
    exact ⟨⟨nintSum g, hx⟩, scosBM_restrK 𝒢 Φ hinv hx hg fun _ => rfl⟩

/-- The elements of the restricted group are the `scosBMPsi` of the first coordinates. -/
theorem scosBM_mem_range {σ : Perm (Fin (scosBMk Φ))} :
    σ ∈ (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ) (scosBM_invariant 𝒢 Φ hinv)).range ↔
      ∃ g, ∃ hg : g ∈ 𝒢, scosBMPsi 𝒢 Φ hinv ⟨g.1, Subgroup.mem_map_of_mem _ hg⟩ = σ := by
  rw [scosBM_range 𝒢 Φ hinv]
  constructor
  · rintro ⟨⟨τ, ⟨g, hg, rfl⟩⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, rfl⟩

/-- **The restricted group is solvable**: it is a quotient of the first coordinates. -/
theorem scosBM_solvable (hsol : IsSolvable (𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n))))) :
    IsSolvable
      (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ) (scosBM_invariant 𝒢 Φ hinv)).range := by
  haveI : Group.IsSolvable (𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n)))) := hsol
  rw [scosBM_range 𝒢 Φ hinv]
  exact solvable_of_surjective (scosBMPsi 𝒢 Φ hinv).rangeRestrict_surjective

/-- **The restricted group is transitive.** -/
theorem scosBM_trans (htr : ScosTrans 𝒢 Φ) (i j : Fin (scosBMk Φ)) :
    ∃ h ∈ (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv)).range, h i = j := by
  obtain ⟨g, hg, hgij⟩ := htr _ (scosBME Φ i).2 _ (scosBME Φ j).2
  refine ⟨_, (scosBM_mem_range 𝒢 Φ hinv).2 ⟨g, hg, rfl⟩, ?_⟩
  apply (scosBME Φ).injective
  apply Subtype.ext
  rw [scosBMPsi_apply]
  exact hgij

/-- With `e = Equiv.refl`, `groupFin` does nothing. -/
theorem scosBM_groupFin : groupFin (Equiv.refl (Fin (n + n))) (𝒢.map nintSum) = 𝒢.map nintSum := by
  ext x
  rw [mem_groupFin]
  exact ⟨fun ⟨h, hh, he⟩ => he ▸ hh, fun hx => ⟨x, hx, rfl⟩⟩

end

end GI.Impl
