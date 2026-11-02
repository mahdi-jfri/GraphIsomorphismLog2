import Workspace.Impl.SCosSpec

/-!
# The mathematics of functions 0–3

`N = n + n`. The indicator `scosInd Φ` is the list of numbers `scosNodeL Φ`. Its number of 1s is
`|Φ|` (`scosNode_count`), and its first 1 sits at a point `Fin.castAdd n a₀` with `a₀ ∈ Φ`
(`scosNode_findIdx`). The orbit `O = scosNodeO 𝒢 Φ a₀` of `a₀` under the first coordinates of
`𝒢` lies in `Φ`, is invariant, and its indicator is the indicator of the orbit labels equal to
the label of `Fin.castAdd n a₀` (`scosNode_orbitInd`). `O = Φ` exactly when the counts agree,
and then `𝒢` is transitive on `Φ`. The entrywise difference of the indicators of `Φ` and `O` is
the indicator of `Φ \ O` (`scosNode_sub`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

variable {n : ℕ}

/-- The indicator of `Φ` as a list of numbers. -/
noncomputable def scosNodeL (Φ : Finset (Fin n)) : List ℕ :=
  (List.finRange (n + n)).map (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ))

theorem scosInd_eq_natList (Φ : Finset (Fin n)) : scosInd Φ = natList (scosNodeL Φ) := by
  simp [scosInd, indVal, encFun, natList, scosNodeL, List.map_map]

theorem mem_scosPhiF {Φ : Finset (Fin n)} {i : Fin (n + n)} :
    i ∈ scosPhiF Φ ↔ ∃ b ∈ Φ, Fin.castAdd n b = i := by
  simp [scosPhiF]

open Classical in
theorem scosNode_indF (Φ : Finset (Fin n)) (i : Fin (n + n)) :
    indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ) i = if i ∈ scosPhiF Φ then 1 else 0 := by
  simp [indF]

theorem length_scosNodeL (Φ : Finset (Fin n)) : (scosNodeL Φ).length = n + n := by
  simp [scosNodeL]

theorem scosNodeL_le (Φ : Finset (Fin n)) : ∀ x ∈ scosNodeL Φ, x ≤ 1 := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact indF_le_one _ _ _

/-- The number of 1s of the indicator is `|Φ|`. -/
theorem scosNode_count (Φ : Finset (Fin n)) : (scosNodeL Φ).count 1 = Φ.card := by
  classical
  rw [scosNodeL, count_map_finRange]
  have : Finset.univ.filter (fun j => indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ) j = 1) =
      Φ.map ⟨Fin.castAdd n, Fin.castAdd_injective n n⟩ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, scosNode_indF, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    rw [← mem_scosPhiF]
    split_ifs with h <;> simp [h]
  rw [this, Finset.card_map]

/-- The first 1 of the indicator of a nonempty `Φ` is at a point of `Φ`. -/
theorem scosNode_findIdx {Φ : Finset (Fin n)} (hne : Φ.Nonempty) :
    ∃ a₀ ∈ Φ, (scosNodeL Φ).findIdx (fun x => decide (x = 1)) = (Fin.castAdd n a₀ : ℕ) := by
  obtain ⟨b, hb⟩ := hne
  have hex : ∃ x ∈ scosNodeL Φ, decide (x = 1) = true := by
    refine ⟨1, List.mem_map.mpr ⟨Fin.castAdd n b, List.mem_finRange _, ?_⟩, by simp⟩
    rw [scosNode_indF, if_pos (mem_scosPhiF.mpr ⟨b, hb, rfl⟩)]
  have hlt := List.findIdx_lt_length_of_exists hex
  have hget := List.findIdx_getElem (w := hlt)
  rw [length_scosNodeL] at hlt
  set k := (scosNodeL Φ).findIdx (fun x => decide (x = 1))
  have e1 : (scosNodeL Φ)[k]'(by rw [length_scosNodeL]; exact hlt) =
      indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ) ⟨k, hlt⟩ := by
    simp [scosNodeL]
  rw [e1, scosNode_indF] at hget
  split_ifs at hget with h
  · obtain ⟨a₀, ha₀, he⟩ := mem_scosPhiF.mp h
    exact ⟨a₀, ha₀, by rw [he]⟩
  · simp at hget

/-- `a ⊕ b` maps `Fin.castAdd n i` to `Fin.castAdd n (a i)`. -/
theorem scosNode_nintSum_castAdd (p : ScosPair n) (i : Fin n) :
    nintSum p (Fin.castAdd n i) = Fin.castAdd n (p.1 i) := by
  apply Fin.ext
  rw [nintSum_apply, sumToFin_sumCongr_castAdd]
  rfl

open Classical in
/-- The orbit of `a₀` under the first coordinates of `𝒢`, inside `Φ`. -/
noncomputable def scosNodeO (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) (a₀ : Fin n) :
    Finset (Fin n) :=
  Φ.filter fun b => ∃ g ∈ 𝒢, g.1 a₀ = b

theorem mem_scosNodeO {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} {a₀ b : Fin n} :
    b ∈ scosNodeO 𝒢 Φ a₀ ↔ b ∈ Φ ∧ ∃ g ∈ 𝒢, g.1 a₀ = b := by
  classical
  simp [scosNodeO]

theorem scosNodeO_subset (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) (a₀ : Fin n) :
    scosNodeO 𝒢 Φ a₀ ⊆ Φ := fun _ hb => (mem_scosNodeO.mp hb).1

theorem self_mem_scosNodeO {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} {a₀ : Fin n}
    (ha : a₀ ∈ Φ) : a₀ ∈ scosNodeO 𝒢 Φ a₀ :=
  mem_scosNodeO.mpr ⟨ha, 1, 𝒢.one_mem, rfl⟩

/-- A point of `Φ` is in the orbit when some element of `𝒢` maps `a₀` to it; for invariant `Φ`
the condition `b ∈ Φ` follows. -/
theorem mem_scosNodeO_of_inv {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} {a₀ b : Fin n}
    (hinv : ScosInv 𝒢 Φ) (ha : a₀ ∈ Φ) :
    b ∈ scosNodeO 𝒢 Φ a₀ ↔ ∃ g ∈ 𝒢, g.1 a₀ = b := by
  rw [mem_scosNodeO]
  constructor
  · exact fun h => h.2
  · rintro ⟨g, hg, rfl⟩
    exact ⟨hinv g hg a₀ ha, g, hg, rfl⟩

theorem scosInv_scosNodeO {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} {a₀ : Fin n}
    (hinv : ScosInv 𝒢 Φ) (ha : a₀ ∈ Φ) : ScosInv 𝒢 (scosNodeO 𝒢 Φ a₀) := by
  intro g hg b hb
  obtain ⟨h, hh, rfl⟩ := (mem_scosNodeO_of_inv hinv ha).mp hb
  exact (mem_scosNodeO_of_inv hinv ha).mpr ⟨g * h, 𝒢.mul_mem hg hh, rfl⟩

/-- The orbit is `Φ` exactly when it has `|Φ|` points. -/
theorem scosNodeO_eq_iff {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} {a₀ : Fin n} :
    scosNodeO 𝒢 Φ a₀ = Φ ↔ (scosNodeO 𝒢 Φ a₀).card = Φ.card := by
  constructor
  · intro h; rw [h]
  · intro h
    exact Finset.eq_of_subset_of_card_le (scosNodeO_subset _ _ _) h.ge

/-- If the orbit of a point of `Φ` is `Φ`, then `𝒢` is transitive on `Φ`. -/
theorem scosTrans_of_eq {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} {a₀ : Fin n}
    (h : scosNodeO 𝒢 Φ a₀ = Φ) : ScosTrans 𝒢 Φ := by
  intro a ha b hb
  rw [← h] at ha hb
  obtain ⟨-, g, hg, rfl⟩ := mem_scosNodeO.mp ha
  obtain ⟨-, k, hk, rfl⟩ := mem_scosNodeO.mp hb
  refine ⟨k * g⁻¹, 𝒢.mul_mem hk (𝒢.inv_mem hg), ?_⟩
  simp

/-- The labels from the orbit program on the group of pairs. -/
theorem scosNode_lab_iff {𝒢 : Subgroup (ScosPair n)} {gs : List (Perm (Fin (n + n)))}
    (hgs : gens gs = 𝒢.map nintSum) {lab : Fin (n + n) → ℕ}
    (hlab : ∀ x y, lab x = lab y ↔ y ∈ genOrbit (1 :: gs) x) (a₀ : Fin n) (i : Fin (n + n)) :
    lab i = lab (Fin.castAdd n a₀) ↔ ∃ g ∈ 𝒢, Fin.castAdd n (g.1 a₀) = i := by
  rw [eq_comm, hlab, mem_genOrbit]
  have hg : genGroup (1 :: gs) = 𝒢.map nintSum := (gens_cons_one gs).trans hgs
  rw [hg]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨p, hp, (scosNode_nintSum_castAdd p a₀).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨nintSum p, Subgroup.mem_map.mpr ⟨p, hp, rfl⟩, scosNode_nintSum_castAdd p a₀⟩

/-- The indicator of the labels equal to the label of `Fin.castAdd n a₀` is the indicator of the
orbit `O`. -/
theorem scosNode_orbitInd {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)}
    (hinv : ScosInv 𝒢 Φ) {a₀ : Fin n} (ha : a₀ ∈ Φ) {gs : List (Perm (Fin (n + n)))}
    (hgs : gens gs = 𝒢.map nintSum) {lab : Fin (n + n) → ℕ}
    (hlab : ∀ x y, lab x = lab y ↔ y ∈ genOrbit (1 :: gs) x) :
    natList (((List.finRange (n + n)).map lab).map
      fun x => if x = lab (Fin.castAdd n a₀) then 1 else 0) =
      scosInd (scosNodeO 𝒢 Φ a₀) := by
  rw [scosInd_eq_natList, scosNodeL, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, scosNode_indF]
  have : i ∈ scosPhiF (scosNodeO 𝒢 Φ a₀) ↔ lab i = lab (Fin.castAdd n a₀) := by
    rw [scosNode_lab_iff hgs hlab, mem_scosPhiF]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨g, hg, rfl⟩ := (mem_scosNodeO_of_inv hinv ha).mp hb
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g.1 a₀, (mem_scosNodeO_of_inv hinv ha).mpr ⟨g, hg, rfl⟩, rfl⟩
  by_cases h : lab i = lab (Fin.castAdd n a₀)
  · rw [if_pos h, if_pos (this.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (this.mp h'))]

/-- The entrywise difference of two indicators. -/
theorem scosNode_sub {Φ O : Finset (Fin n)} (hO : O ⊆ Φ) (i : Fin (n + n)) :
    indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ) i -
      indF (Equiv.refl (Fin (n + n))) (scosPhiF O) i =
      indF (Equiv.refl (Fin (n + n))) (scosPhiF (Φ \ O)) i := by
  classical
  simp only [scosNode_indF]
  have hiff : i ∈ scosPhiF (Φ \ O) ↔ i ∈ scosPhiF Φ ∧ i ∉ scosPhiF O := by
    simp only [mem_scosPhiF, Finset.mem_sdiff]
    constructor
    · rintro ⟨b, ⟨hb, hbO⟩, rfl⟩
      refine ⟨⟨b, hb, rfl⟩, ?_⟩
      rintro ⟨c, hc, he⟩
      exact hbO (Fin.castAdd_injective n n he ▸ hc)
    · rintro ⟨⟨b, hb, rfl⟩, h⟩
      exact ⟨b, ⟨hb, fun hbO => h ⟨b, hbO, rfl⟩⟩, rfl⟩
  have hsub : i ∈ scosPhiF O → i ∈ scosPhiF Φ := by
    simp only [mem_scosPhiF]
    rintro ⟨b, hb, rfl⟩
    exact ⟨b, hO hb, rfl⟩
  by_cases h2 : i ∈ scosPhiF O
  · rw [if_pos (hsub h2), if_pos h2, if_neg (fun h => (hiff.mp h).2 h2)]
  · by_cases h1 : i ∈ scosPhiF Φ
    · rw [if_pos h1, if_neg h2, if_pos (hiff.mpr ⟨h1, h2⟩)]
    · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 (hiff.mp h).1)]

/-- A subgroup of a solvable group of permutations is solvable. -/
theorem scosNode_solv {𝒢 K : Subgroup (ScosPair n)} (hK : K ≤ 𝒢)
    (h : IsSolvable (𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n))))) :
    IsSolvable (K.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n)))) :=
  solvable_of_solvable_injective (Subgroup.inclusion_injective (Subgroup.map_mono hK))

end GI.Impl
