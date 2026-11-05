module

public import Workspace.Proved.WielBurnside
public import Workspace.BochertJordan
public import Workspace.AlternatingSimple
public import Workspace.Schreier
public import Workspace.SocleOuter

@[expose] public section

set_option linter.style.haveILetI false

namespace GI.Proved

open scoped Pointwise commutatorElement
open GI.RadicalSocle GI.PrimitiveStructure

variable {Ω : Type*}

/-- Glue an embedding `f : Fin k ↪ Ω` and a disjoint embedding `e : Fin m ↪ Ω` into
an embedding `Fin (k + m) ↪ Ω`. -/
def appendEmbedding {k m : ℕ} (f : Fin k ↪ Ω) (e : Fin m ↪ Ω)
    (hdisj : ∀ i j, f i ≠ e j) : Fin (k + m) ↪ Ω where
  toFun := Fin.addCases f e
  inj' := by
    intro x y hxy
    dsimp at hxy
    induction x using Fin.addCases with
    | left i₁ =>
      induction y using Fin.addCases with
      | left i₂ =>
        rw [Fin.addCases_left, Fin.addCases_left] at hxy
        exact congrArg (Fin.castAdd m) (f.injective hxy)
      | right j₂ =>
        rw [Fin.addCases_left, Fin.addCases_right] at hxy
        exact (hdisj i₁ j₂ hxy).elim
    | right j₁ =>
      induction y using Fin.addCases with
      | left i₂ =>
        rw [Fin.addCases_right, Fin.addCases_left] at hxy
        exact (hdisj i₂ j₁ hxy.symm).elim
      | right j₂ =>
        rw [Fin.addCases_right, Fin.addCases_right] at hxy
        exact congrArg (Fin.natAdd k) (e.injective hxy)

@[simp]
theorem appendEmbedding_castAdd {k m : ℕ} (f : Fin k ↪ Ω) (e : Fin m ↪ Ω)
    (hdisj : ∀ i j, f i ≠ e j) (i : Fin k) :
    appendEmbedding f e hdisj (Fin.castAdd m i) = f i := by
  change Fin.addCases f e (Fin.castAdd m i) = f i
  exact Fin.addCases_left i

@[simp]
theorem appendEmbedding_natAdd {k m : ℕ} (f : Fin k ↪ Ω) (e : Fin m ↪ Ω)
    (hdisj : ∀ i j, f i ≠ e j) (j : Fin m) :
    appendEmbedding f e hdisj (Fin.natAdd k j) = e j := by
  change Fin.addCases f e (Fin.natAdd k j) = e j
  exact Fin.addCases_right j

/-- Given `f : Fin k ↪ Ω` and `k + m ≤ Fintype.card Ω`, there is an embedding `e : Fin m ↪ Ω`
whose image is disjoint from that of `f`. -/
theorem exists_disjoint_embedding [Fintype Ω] [DecidableEq Ω] {k : ℕ}
    (f : Fin k ↪ Ω) (m : ℕ) (hm : k + m ≤ Fintype.card Ω) :
    ∃ e : Fin m ↪ Ω, ∀ i j, f i ≠ e j := by
  let S : Finset Ω := Finset.univ \ Finset.univ.map f
  have hScard : m ≤ S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Finset.card_map,
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hScard
  let eqv : Fin m ≃ T :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hTcard)).symm
  let e : Fin m ↪ Ω := eqv.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨e, ?_⟩
  intro i j hfe
  have hjS : e j ∈ S := hTS (eqv j).property
  rw [Finset.mem_sdiff, Finset.mem_map] at hjS
  exact hjS.2 ⟨i, Finset.mem_univ i, hfe⟩

/-- An embedding `Fin 2 ↪ Ω` from two distinct elements. -/
def pairEmbedding {x₁ x₂ : Ω} (hne : x₁ ≠ x₂) : Fin 2 ↪ Ω where
  toFun := ![x₁, x₂]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne hij).elim
    · exact (hne hij.symm).elim
    · rfl

@[simp]
theorem pairEmbedding_zero {x₁ x₂ : Ω} (hne : x₁ ≠ x₂) :
    pairEmbedding hne 0 = x₁ := rfl

@[simp]
theorem pairEmbedding_one {x₁ x₂ : Ω} (hne : x₁ ≠ x₂) :
    pairEmbedding hne 1 = x₂ := rfl

/-- `r`-transitivity of a permutation subgroup `G ≤ Equiv.Perm Ω`. -/
def WielTransitive (r : ℕ) (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ a b : Fin r ↪ Ω, ∃ g ∈ G, ∀ i : Fin r, g (a i) = b i

theorem WielTransitive.mono [Fintype Ω] {r s : ℕ} (hrs : r ≤ s)
    (hs : s ≤ Fintype.card Ω) {G : Subgroup (Equiv.Perm Ω)} (hG : WielTransitive s G) :
    WielTransitive r G := by
  classical
  intro a b
  obtain ⟨ea, hea⟩ := exists_disjoint_embedding a (s - r) (by omega)
  obtain ⟨eb, heb⟩ := exists_disjoint_embedding b (s - r) (by omega)
  let eqv : Fin s ≃ Fin (r + (s - r)) := finCongr (by omega)
  let a' : Fin s ↪ Ω := eqv.toEmbedding.trans (appendEmbedding a ea hea)
  let b' : Fin s ↪ Ω := eqv.toEmbedding.trans (appendEmbedding b eb heb)
  obtain ⟨g, hg, hgab⟩ := hG a' b'
  refine ⟨g, hg, fun i => ?_⟩
  have hi := hgab (eqv.symm (Fin.castAdd (s - r) i))
  simpa only [a', b', Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply, appendEmbedding_castAdd] using hi

theorem WielTransitive.wielTwoTrans {G : Subgroup (Equiv.Perm Ω)} (h2 : WielTransitive 2 G) :
    WielTwoTrans G Ω := by
  intro x₁ x₂ y₁ y₂ hx hy
  obtain ⟨g, hg, hgab⟩ := h2 (pairEmbedding hx) (pairEmbedding hy)
  exact ⟨⟨g, hg⟩, hgab 0, hgab 1⟩

/-- Small-degree case (`7 ≤ |Ω| ≤ 9`): any 7-transitive subgroup of `Perm Ω` contains
`alternatingGroup Ω`. -/
theorem alternatingGroup_le_of_sevenTransitive_of_card_le_nine [Fintype Ω] [DecidableEq Ω]
    (h7 : 7 ≤ Fintype.card Ω) (h9 : Fintype.card Ω ≤ 9)
    {G : Subgroup (Equiv.Perm Ω)} (hG : WielTransitive 7 G) :
    alternatingGroup Ω ≤ G := by
  haveI : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have h2 : WielTwoTrans G Ω := (hG.mono (by decide) h7).wielTwoTrans
  have hprim : MulAction.IsPreprimitive G Ω := h2.isPreprimitive
  let emptyEmb : Fin 0 ↪ Ω := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  obtain ⟨a, _⟩ := exists_disjoint_embedding emptyEmb 7 (by omega)
  let c₁ : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 1 2
  let c₂ : Equiv.Perm (Fin 7) := Equiv.swap 0 3
  obtain ⟨x, hxG, hx⟩ := hG a (c₁.toEmbedding.trans a)
  obtain ⟨y, hyG, hy⟩ := hG a (c₂.toEmbedding.trans a)
  let x' : Equiv.Perm Ω := x ^ 2
  have hx'G : x' ∈ G := G.pow_mem hxG 2
  have hx'a : ∀ i : Fin 7, x' (a i) = a (c₁ (c₁ i)) := by
    intro i
    change x (x (a i)) = a (c₁ (c₁ i))
    rw [hx i, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      hx (c₁ i), Function.Embedding.trans_apply, Equiv.toEmbedding_apply]
  have hx'0 : x' (a 0) ≠ a 0 := by
    rw [hx'a 0]
    intro h
    have hc : c₁ (c₁ 0) = 0 := a.injective h
    revert hc; decide
  have hy0 : y (a 0) ≠ a 0 := by
    rw [hy 0, Function.Embedding.trans_apply, Equiv.toEmbedding_apply]
    intro h
    have hc : c₂ 0 = 0 := a.injective h
    revert hc; decide
  let R : Finset Ω := Finset.univ.map a
  let S : Finset Ω := Finset.univ \ R
  have hScard : S.card ≤ 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Finset.card_map,
      Finset.card_univ, Fintype.card_fin]
    omega
  have hxS : ∀ z ∈ S, x z ∈ S := by
    intro z hz
    rw [Finset.mem_sdiff] at hz ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_map]
    rintro ⟨j, _, hj⟩
    have hsurj : c₁ (c₁⁻¹ j) = j := c₁.apply_inv_self j
    have hxz : x z = x (a (c₁⁻¹ j)) := by
      rw [hx (c₁⁻¹ j), Function.Embedding.trans_apply, Equiv.toEmbedding_apply, hsurj, hj]
    exact hz.2 (Finset.mem_map.mpr ⟨c₁⁻¹ j, Finset.mem_univ _, (x.injective hxz).symm⟩)
  have hx'S : ∀ z ∈ S, x' z = z := by
    intro z hz
    change x (x z) = z
    by_cases hxz : x z = z
    · rw [hxz, hxz]
    · have hsub : ({z, x z} : Finset Ω) ⊆ S := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hz
        · exact hxS z hz
      have hpair : ({z, x z} : Finset Ω).card = 2 := Finset.card_pair (Ne.symm hxz)
      have heqS : ({z, x z} : Finset Ω) = S :=
        Finset.eq_of_subset_of_card_le hsub (by omega)
      have hxxz : x (x z) ∈ ({z, x z} : Finset Ω) := by
        rw [heqS]
        exact hxS (x z) (hxS z hz)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxxz
      rcases hxxz with h1 | h2
      · exact h1
      · exact (hxz (x.injective h2)).elim
  have h_i : ∀ i : Fin 7, i ≠ 0 → c₁ (c₁ i) = i ∨ c₂ i = i := by decide
  have huniq : ∀ b : Ω, b ≠ a 0 → x' b = b ∨ y b = b := by
    intro b hb0
    by_cases hbR : b ∈ R
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hbR
      have hi0 : i ≠ 0 := fun h => hb0 (congrArg a h)
      rcases h_i i hi0 with hc1 | hc2
      · left
        rw [hx'a i, hc1]
      · right
        rw [hy i, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, hc2]
    · left
      exact hx'S b (Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hbR⟩)
  have h3 : (⁅x', y⁆ : Equiv.Perm Ω).IsThreeCycle :=
    GI.Bochert.isThreeCycle_commutator_of_unique_common_moved hx'0 hy0 huniq
  have hcomm_mem : ⁅x', y⁆ ∈ G := by
    rw [commutatorElement_def]
    exact G.mul_mem (G.mul_mem (G.mul_mem hx'G hyG) (G.inv_mem hx'G)) (G.inv_mem hyG)
  exact GI.Bochert.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hcomm_mem

/-- If `G` is 7-transitive on `Ω` (`7 ≤ |Ω|`) and does not contain `alternatingGroup Ω`,
then any `x ∈ G` fixing `Ω \ Set.range γ` pointwise (`γ : Fin 5 ↪ Ω`) is `1`. -/
theorem eq_one_of_fixes_compl_five [Fintype Ω] [DecidableEq Ω]
    (h7 : 7 ≤ Fintype.card Ω) {G : Subgroup (Equiv.Perm Ω)} (hG : WielTransitive 7 G)
    (halt : ¬ alternatingGroup Ω ≤ G) (γ : Fin 5 ↪ Ω)
    {x : Equiv.Perm Ω} (hxG : x ∈ G) (hfix : ∀ z : Ω, z ∉ Set.range γ → x z = z) :
    x = 1 := by
  by_contra hx1
  have hmove : ∃ z : Ω, x z ≠ z := by
    by_contra hall; push Not at hall
    apply hx1; ext z; exact hall z
  obtain ⟨z₀, hz₀⟩ := hmove
  have hz₀_mem : z₀ ∈ Set.range γ := by
    by_contra hnot
    exact hz₀ (hfix z₀ hnot)
  obtain ⟨i₀, rfl⟩ := hz₀_mem
  haveI : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hprim : MulAction.IsPreprimitive G Ω := (hG.mono (by decide) h7).wielTwoTrans.isPreprimitive
  obtain ⟨e, he⟩ := exists_disjoint_embedding γ 2 (by omega)
  let eqv : Fin 7 ≃ Fin (5 + 2) := finCongr (by decide)
  let a : Fin 7 ↪ Ω := eqv.toEmbedding.trans (appendEmbedding γ e he)
  let σ : Equiv.Perm (Fin (5 + 2)) := Equiv.swap (Fin.castAdd 2 i₀) (Fin.natAdd 5 0)
  let b : Fin 7 ↪ Ω := eqv.toEmbedding.trans (σ.toEmbedding.trans (appendEmbedding γ e he))
  obtain ⟨y, hyG, hy⟩ := hG a b
  have hy_apply : ∀ j : Fin (5 + 2),
      y (appendEmbedding γ e he j) = appendEmbedding γ e he (σ j) := by
    intro j
    have hj := hy (eqv.symm j)
    simpa only [a, b, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.apply_symm_apply] using hj
  have hy_i₀ : y (γ i₀) ≠ γ i₀ := by
    have h := hy_apply (Fin.castAdd 2 i₀)
    dsimp only [σ] at h
    rw [appendEmbedding_castAdd, Equiv.swap_apply_left, appendEmbedding_natAdd] at h
    rw [h]
    exact (he i₀ 0).symm
  have hy_other : ∀ i : Fin 5, i ≠ i₀ → y (γ i) = γ i := by
    intro i hi
    have h := hy_apply (Fin.castAdd 2 i)
    have hne1 : Fin.castAdd 2 i ≠ Fin.castAdd 2 i₀ := by
      intro hc
      have hval := congrArg Fin.val hc
      simp only [Fin.val_castAdd] at hval
      exact hi (Fin.ext hval)
    have hne2 : Fin.castAdd 2 i ≠ Fin.natAdd 5 0 := by
      intro hc
      have hval := congrArg Fin.val hc
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
    dsimp only [σ] at h
    rw [appendEmbedding_castAdd, Equiv.swap_apply_of_ne_of_ne hne1 hne2,
      appendEmbedding_castAdd] at h
    exact h
  have huniq : ∀ z : Ω, z ≠ γ i₀ → x z = z ∨ y z = z := by
    intro z hz
    by_cases hzγ : z ∈ Set.range γ
    · obtain ⟨i, rfl⟩ := hzγ
      right
      exact hy_other i (fun h => hz (congrArg γ h))
    · left
      exact hfix z hzγ
  have h3 : (⁅x, y⁆ : Equiv.Perm Ω).IsThreeCycle :=
    GI.Bochert.isThreeCycle_commutator_of_unique_common_moved hz₀ hy_i₀ huniq
  have hcomm_mem : ⁅x, y⁆ ∈ G := by
    rw [commutatorElement_def]
    exact G.mul_mem (G.mul_mem (G.mul_mem hxG hyG) (G.inv_mem hxG)) (G.inv_mem hyG)
  exact halt (GI.Bochert.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hcomm_mem)

/-- The setwise stabilizer of `Set.range γ` in `G`. -/
def SetwiseStab (γ : Fin 5 ↪ Ω) (G : Subgroup (Equiv.Perm Ω)) : Subgroup (Equiv.Perm Ω) where
  carrier := {g : Equiv.Perm Ω | g ∈ G ∧ ∀ x : Ω, g x ∈ Set.range γ ↔ x ∈ Set.range γ}
  one_mem' := ⟨G.one_mem, fun _ => Iff.rfl⟩
  mul_mem' := fun {g h} hg hh => ⟨G.mul_mem hg.1 hh.1, fun x => (hg.2 (h x)).trans (hh.2 x)⟩
  inv_mem' := fun {g} hg => ⟨G.inv_mem hg.1, fun x => by
    have h := (hg.2 (g⁻¹ x)).symm
    rwa [g.apply_inv_self] at h⟩

/-- Restriction of `SetwiseStab γ G` to `Equiv.Perm (Fin 5)` via `γ`. -/
noncomputable def resFin5 (γ : Fin 5 ↪ Ω) (G : Subgroup (Equiv.Perm Ω)) :
    SetwiseStab γ G →* Equiv.Perm (Fin 5) where
  toFun g := (Equiv.ofInjective γ γ.injective).permCongr.symm
    (g.val.subtypePerm (fun x => g.property.2 x))
  map_one' := by
    apply Equiv.Perm.ext
    intro i
    refine γ.injective ?_
    change ((Equiv.ofInjective γ γ.injective)
      (((Equiv.ofInjective γ γ.injective).permCongr.symm
        ((1 : Equiv.Perm Ω).subtypePerm _)) i)).val = γ i
    rw [Equiv.permCongr_symm_apply]
    simp
  map_mul' g h := by
    apply Equiv.Perm.ext
    intro i
    refine γ.injective ?_
    change ((Equiv.ofInjective γ γ.injective)
      (((Equiv.ofInjective γ γ.injective).permCongr.symm _) i)).val =
      ((Equiv.ofInjective γ γ.injective)
        (((Equiv.ofInjective γ γ.injective).permCongr.symm _)
          (((Equiv.ofInjective γ γ.injective).permCongr.symm _) i))).val
    simp

@[simp]
theorem gamma_resFin5_apply (γ : Fin 5 ↪ Ω) (G : Subgroup (Equiv.Perm Ω))
    (g : SetwiseStab γ G) (i : Fin 5) :
    γ (resFin5 γ G g i) = (g : Equiv.Perm Ω) (γ i) := by
  change ((Equiv.ofInjective γ γ.injective) (resFin5 γ G g i)).val = (g : Equiv.Perm Ω) (γ i)
  unfold resFin5
  simp

theorem mem_ker_resFin5_iff (γ : Fin 5 ↪ Ω) (G : Subgroup (Equiv.Perm Ω))
    (g : SetwiseStab γ G) :
    g ∈ (resFin5 γ G).ker ↔ ∀ i : Fin 5, (g : Equiv.Perm Ω) (γ i) = γ i := by
  rw [MonoidHom.mem_ker, Equiv.Perm.ext_iff]
  refine ⟨fun h i => ?_, fun h i => ?_⟩
  · rw [← gamma_resFin5_apply, h i, Equiv.Perm.one_apply]
  · refine γ.injective ?_
    rw [gamma_resFin5_apply, h i, Equiv.Perm.one_apply]

/-- Restriction of `SetwiseStab γ G` to the complement `{x : Ω // x ∉ Set.range γ}`. -/
def resDelta (γ : Fin 5 ↪ Ω) (G : Subgroup (Equiv.Perm Ω)) :
    SetwiseStab γ G →* Equiv.Perm {x : Ω // x ∉ Set.range γ} where
  toFun g := g.val.subtypePerm (fun x => not_iff_not.mpr (g.property.2 x))
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

theorem resFin5_surjective [Fintype Ω] [DecidableEq Ω] (h7 : 7 ≤ Fintype.card Ω)
    {G : Subgroup (Equiv.Perm Ω)} (hG : WielTransitive 7 G) (γ : Fin 5 ↪ Ω) :
    Function.Surjective (resFin5 γ G) := by
  intro σ
  obtain ⟨e, he⟩ := exists_disjoint_embedding γ 2 (by omega)
  let eqv : Fin 7 ≃ Fin (5 + 2) := finCongr (by decide)
  let a : Fin 7 ↪ Ω := eqv.toEmbedding.trans (appendEmbedding γ e he)
  have heσ : ∀ i j, (σ.toEmbedding.trans γ) i ≠ e j := fun i j => he (σ i) j
  let b : Fin 7 ↪ Ω := eqv.toEmbedding.trans (appendEmbedding (σ.toEmbedding.trans γ) e heσ)
  obtain ⟨g, hgG, hgab⟩ := hG a b
  have hgγ : ∀ i : Fin 5, g (γ i) = γ (σ i) := by
    intro i
    have hi := hgab (eqv.symm (Fin.castAdd 2 i))
    simpa only [a, b, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.apply_symm_apply, appendEmbedding_castAdd] using hi
  have hg_stab : g ∈ SetwiseStab γ G := by
    refine ⟨hgG, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · obtain ⟨j, hj⟩ := hx
      exact ⟨σ⁻¹ j, g.injective (by rw [hgγ (σ⁻¹ j), σ.apply_inv_self, hj])⟩
    · obtain ⟨i, rfl⟩ := hx
      exact ⟨σ i, (hgγ i).symm⟩
  refine ⟨⟨g, hg_stab⟩, ?_⟩
  apply Equiv.Perm.ext
  intro i
  refine γ.injective ?_
  rw [gamma_resFin5_apply]
  exact hgγ i

/-- If `res : L →* Q` is surjective, `¬ Group.IsSolvable Q`, and `φ : L →* A` has
`φ.ker ≤ res.ker`, then `A` is not solvable. -/
theorem not_isSolvable_of_ker_le_ker {L Q A : Type*} [Group L] [Group Q] [Group A]
    (res : L →* Q) (hsurj : Function.Surjective res) (hnot : ¬ Group.IsSolvable Q)
    (φ : L →* A) (hker : φ.ker ≤ res.ker) : ¬ Group.IsSolvable A := by
  intro hsolvA
  letI := hsolvA
  haveI : Group.IsSolvable (L ⧸ φ.ker) :=
    Group.isSolvable_of_surjective (f := (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivRange φ).symm.surjective
  let liftHom : L ⧸ φ.ker →* Q := QuotientGroup.lift φ.ker res (fun g hg => hker hg)
  have hlift_surj : Function.Surjective liftHom := by
    intro q
    obtain ⟨g, rfl⟩ := hsurj q
    exact ⟨QuotientGroup.mk g, rfl⟩
  exact hnot (Group.isSolvable_of_surjective hlift_surj)

/-- `Equiv.Perm (Fin 5)` is not solvable. -/
theorem not_isSolvable_perm_fin5 : ¬ Group.IsSolvable (Equiv.Perm (Fin 5)) := by
  intro hsolv
  letI := hsolv
  letI : IsSimpleGroup (alternatingGroup (Fin 5)) := GI.AlternatingSimple.isSimple_fin (by decide)
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr
    (inferInstance : Group.IsSolvable (alternatingGroup (Fin 5)))
  obtain ⟨f, t, hft⟩ := GI.AlternatingSimple.nonabelian_fin (by decide : 5 ≤ 5)
  exact hft (hcomm f t)

/-- The automorphism group of a cyclic group is abelian and hence solvable. -/
theorem isSolvable_mulAut_of_isCyclic {M : Type*} [Group M] (hcyc : IsCyclic M) :
    Group.IsSolvable (MulAut M) := by
  obtain ⟨g₀, hg₀⟩ := hcyc.exists_generator
  apply Group.isSolvable_of_comm
  intro e₁ e₂
  obtain ⟨k₁, hk₁⟩ := hg₀ (e₁ g₀)
  obtain ⟨k₂, hk₂⟩ := hg₀ (e₂ g₀)
  change g₀ ^ k₁ = e₁ g₀ at hk₁
  change g₀ ^ k₂ = e₂ g₀ at hk₂
  apply MulEquiv.ext
  intro x
  obtain ⟨m, rfl⟩ := hg₀ x
  change e₁ (e₂ (g₀ ^ m)) = e₂ (e₁ (g₀ ^ m))
  calc e₁ (e₂ (g₀ ^ m))
    _ = e₁ ((e₂ g₀) ^ m) := by rw [map_zpow]
    _ = e₁ ((g₀ ^ k₂) ^ m) := by rw [← hk₂]
    _ = (e₁ g₀) ^ (k₂ * m) := by rw [← zpow_mul, map_zpow]
    _ = (g₀ ^ k₁) ^ (k₂ * m) := by rw [← hk₁]
    _ = g₀ ^ (k₁ * (k₂ * m)) := by rw [← zpow_mul]
    _ = g₀ ^ (k₂ * (k₁ * m)) := by rw [mul_left_comm]
    _ = (g₀ ^ k₂) ^ (k₁ * m) := by rw [zpow_mul]
    _ = (e₂ g₀) ^ (k₁ * m) := by rw [hk₂]
    _ = e₂ ((g₀ ^ k₁) ^ m) := by rw [← map_zpow, zpow_mul]
    _ = e₂ ((e₁ g₀) ^ m) := by rw [hk₁]
    _ = e₂ (e₁ (g₀ ^ m)) := by rw [← map_zpow]

/-- Wielandt's Hilfssatz: If `G ≤ Equiv.Perm Ω` is 7-transitive (`7 ≤ |Ω|`) and does not
contain `alternatingGroup Ω`, then `10 ≤ |Ω|`, and for any `γ : Fin 5 ↪ Ω`, there is a
subgroup `M ≤ G` fixing `Set.range γ` pointwise, normalized by the pointwise stabilizer
of `Set.range γ` in `G`, abelian, non-cyclic, and acting regularly on `Ω \ Set.range γ`. -/
theorem wielandt_lemma [Fintype Ω] [DecidableEq Ω]
    (h7 : 7 ≤ Fintype.card Ω) {G : Subgroup (Equiv.Perm Ω)} (hG : WielTransitive 7 G)
    (halt : ¬ alternatingGroup Ω ≤ G) (γ : Fin 5 ↪ Ω) :
    10 ≤ Fintype.card Ω ∧
    ∃ M : Subgroup (Equiv.Perm Ω),
      M ≤ G ∧
      (∀ m ∈ M, ∀ i : Fin 5, (m : Equiv.Perm Ω) (γ i) = γ i) ∧
      (∀ g ∈ G, (∀ i : Fin 5, (g : Equiv.Perm Ω) (γ i) = γ i) →
        ∀ m ∈ M, g * m * g⁻¹ ∈ M) ∧
      (∀ x y : M, x * y = y * x) ∧
      ¬ IsCyclic M ∧
      (∀ a : Ω, a ∉ Set.range γ → Function.Injective (fun m : M => (m : Equiv.Perm Ω) a)) ∧
      (∀ a b : Ω, a ∉ Set.range γ → b ∉ Set.range γ → ∃ m : M, (m : Equiv.Perm Ω) a = b) := by
  have h10 : 10 ≤ Fintype.card Ω := by
    by_contra hlt
    exact halt (alternatingGroup_le_of_sevenTransitive_of_card_le_nine h7 (by omega) hG)
  refine ⟨h10, ?_⟩
  let L₀ := SetwiseStab γ G
  let Δ := {x : Ω // x ∉ Set.range γ}
  letI : MulAction L₀ Δ := MulAction.compHom Δ (resDelta γ G)
  have hsmul_val : ∀ (g : L₀) (x : Δ), (g • x).val = (g : Equiv.Perm Ω) x.val :=
    fun _ _ => rfl
  haveI : FaithfulSMul L₀ Δ := by
    constructor
    intro g₁ g₂ h
    apply Subtype.ext
    rw [← inv_mul_eq_one]
    change (g₁⁻¹ * g₂ : L₀).val = 1
    refine eq_one_of_fixes_compl_five h7 hG halt γ (g₁⁻¹ * g₂).property.1 ?_
    intro z hz
    have hz' := congrArg Subtype.val (h ⟨z, hz⟩)
    change (g₁ : Equiv.Perm Ω) z = (g₂ : Equiv.Perm Ω) z at hz'
    change (g₁ : Equiv.Perm Ω)⁻¹ ((g₂ : Equiv.Perm Ω) z) = z
    rw [← hz', Equiv.Perm.inv_apply_self]
  have hH2 : ∀ x₁ x₂ y₁ y₂ : Δ, x₁ ≠ x₂ → y₁ ≠ y₂ →
      ∃ h : L₀, h ∈ (resFin5 γ G).ker ∧ h • x₁ = y₁ ∧ h • x₂ = y₂ := by
    intro x₁ x₂ y₁ y₂ hx hy
    have hx' : x₁.val ≠ x₂.val := fun h => hx (Subtype.ext h)
    have hy' : y₁.val ≠ y₂.val := fun h => hy (Subtype.ext h)
    have hdisj_x : ∀ i j, γ i ≠ pairEmbedding hx' j := by
      intro i j h
      fin_cases j
      · exact x₁.property ⟨i, h⟩
      · exact x₂.property ⟨i, h⟩
    have hdisj_y : ∀ i j, γ i ≠ pairEmbedding hy' j := by
      intro i j h
      fin_cases j
      · exact y₁.property ⟨i, h⟩
      · exact y₂.property ⟨i, h⟩
    let eqv : Fin 7 ≃ Fin (5 + 2) := finCongr (by decide)
    let a : Fin 7 ↪ Ω := eqv.toEmbedding.trans (appendEmbedding γ (pairEmbedding hx') hdisj_x)
    let b : Fin 7 ↪ Ω := eqv.toEmbedding.trans (appendEmbedding γ (pairEmbedding hy') hdisj_y)
    obtain ⟨g, hgG, hgab⟩ := hG a b
    have hg_apply : ∀ j : Fin (5 + 2),
        g (appendEmbedding γ (pairEmbedding hx') hdisj_x j) =
          appendEmbedding γ (pairEmbedding hy') hdisj_y j := by
      intro j
      have hj := hgab (eqv.symm j)
      simpa only [a, b, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
        Equiv.apply_symm_apply] using hj
    have hgγ : ∀ i : Fin 5, g (γ i) = γ i := by
      intro i
      simpa only [appendEmbedding_castAdd] using hg_apply (Fin.castAdd 2 i)
    have hg_stab : g ∈ L₀ := by
      refine ⟨hgG, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
      · obtain ⟨i, hi⟩ := hx
        exact ⟨i, g.injective (by rw [hgγ i, hi])⟩
      · obtain ⟨i, rfl⟩ := hx
        exact ⟨i, (hgγ i).symm⟩
    refine ⟨⟨g, hg_stab⟩, (mem_ker_resFin5_iff γ G ⟨g, hg_stab⟩).mpr hgγ, ?_, ?_⟩
    · apply Subtype.ext
      simpa only [hsmul_val, appendEmbedding_natAdd, pairEmbedding_zero] using
        hg_apply (Fin.natAdd 5 0)
    · apply Subtype.ext
      simpa only [hsmul_val, appendEmbedding_natAdd, pairEmbedding_one] using
        hg_apply (Fin.natAdd 5 1)
  have h2L : WielTwoTrans L₀ Δ := by
    intro x₁ x₂ y₁ y₂ hx hy
    obtain ⟨h, _, hh1, hh2⟩ := hH2 x₁ x₂ y₁ y₂ hx hy
    exact ⟨h, hh1, hh2⟩
  have hcardΔ : 5 ≤ Fintype.card Δ := by
    have hcard : Fintype.card Δ = (Finset.univ \ Finset.univ.map γ).card := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr ⟨fun x => ⟨x.val, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩,
        fun x => ⟨x.val, ?_⟩, fun _ => rfl, fun _ => rfl⟩
      · rw [Finset.mem_map]
        rintro ⟨i, _, hi⟩
        exact x.property ⟨i, hi⟩
      · rintro ⟨i, hi⟩
        exact (Finset.mem_sdiff.mp x.property).2 (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, hi⟩)
    rw [hcard, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Finset.card_map,
      Finset.card_univ, Fintype.card_fin]
    omega
  haveI : Nontrivial Δ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  haveI : MulAction.IsPreprimitive L₀ Δ := h2L.isPreprimitive
  obtain ⟨δ₁, δ₂, hδ₁₂⟩ := exists_pair_ne Δ
  have hH_ne : (resFin5 γ G).ker ≠ ⊥ := by
    intro hbot
    obtain ⟨h, hh_ker, hh1, _⟩ := hH2 δ₁ δ₂ δ₂ δ₁ hδ₁₂ hδ₁₂.symm
    rw [hbot, Subgroup.mem_bot] at hh_ker
    rw [hh_ker, one_smul] at hh1
    exact hδ₁₂ hh1
  obtain ⟨M₀, hM₀, hM₀_le⟩ := exists_minimal_normal_le (resFin5 γ G).ker hH_ne
  letI : M₀.Normal := hM₀.1
  have hsurj5 : Function.Surjective (resFin5 γ G) := resFin5_surjective h7 hG γ
  have hM₀_comm : ∀ x y : M₀, x * y = y * x := by
    by_contra hnot_comm
    push Not at hnot_comm
    letI : IsSimpleGroup M₀ := minimalNormal_simple_of_two_transitive h2L hM₀ hnot_comm δ₁
    have hcent_bot : Subgroup.centralizer (M₀ : Set L₀) = ⊥ := by
      by_contra hcent_ne
      let C := Subgroup.centralizer (M₀ : Set L₀)
      letI : C.Normal := centralizer_normal M₀
      obtain ⟨N₀, hN₀, hN₀_le⟩ := exists_minimal_normal_le C hcent_ne
      by_cases hNM : N₀ = M₀
      · subst hNM
        obtain ⟨x, y, hxy⟩ := hnot_comm
        exact hxy ((hN₀_le x.property y y.property).symm |> Subtype.ext)
      · have hregM₀ : Function.Bijective (fun m : M₀ => m • δ₁) :=
          (distinct_minimal_normals_regular hN₀ hM₀ hNM δ₁).2
        obtain ⟨x, y, hxy⟩ := hnot_comm
        exact hxy (regular_normal_abelian_of_two_transitive h2L M₀ δ₁ hregM₀ x y)
    let φ : L₀ →* GI.SocleOuter.OuterAut M₀ :=
      (QuotientGroup.mk' (GI.SocleOuter.innerAut M₀)).comp (MulAut.conjNormal (H := M₀))
    have hφ_ker : φ.ker ≤ (resFin5 γ G).ker := by
      intro g hg
      apply hM₀_le
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hg
      obtain ⟨m, hm⟩ := hg
      have hgm : m.val⁻¹ * g ∈ Subgroup.centralizer (M₀ : Set L₀) := by
        intro x hx
        have he := congrArg (fun f : MulAut M₀ => (f ⟨x, hx⟩ : L₀)) hm
        change m.val * x * m.val⁻¹ = g * x * g⁻¹ at he
        calc x * (m.val⁻¹ * g)
          _ = m.val⁻¹ * (m.val * x * m.val⁻¹) * g := by group
          _ = m.val⁻¹ * (g * x * g⁻¹) * g := by rw [he]
          _ = (m.val⁻¹ * g) * x := by group
      rw [hcent_bot, Subgroup.mem_bot, inv_mul_eq_one] at hgm
      exact hgm ▸ m.property
    exact not_isSolvable_of_ker_le_ker (resFin5 γ G) hsurj5 not_isSolvable_perm_fin5 φ hφ_ker
      (GI.schreier M₀ hnot_comm)
  have hM₀_not_cyc : ¬ IsCyclic M₀ := by
    intro hcyc
    letI : MulAction.IsPretransitive M₀ Δ := normal_pretransitive M₀ hM₀.2.1
    have hcent_eq : Subgroup.centralizer (M₀ : Set L₀) = M₀ :=
      centralizer_eq_of_commuting_transitive M₀ M₀
        (fun x y => congrArg Subtype.val (hM₀_comm x y)) δ₁
    let φ : L₀ →* MulAut M₀ := MulAut.conjNormal (H := M₀)
    have hφ_ker : φ.ker ≤ (resFin5 γ G).ker := by
      intro g hg
      apply hM₀_le
      rw [← hcent_eq]
      intro x hx
      have he := congrArg (fun f : MulAut M₀ => (f ⟨x, hx⟩ : L₀)) hg
      change g * x * g⁻¹ = x at he
      calc x * g = (g * x * g⁻¹) * g := by rw [he]
        _ = g * x := by group
    exact not_isSolvable_of_ker_le_ker (resFin5 γ G) hsurj5 not_isSolvable_perm_fin5 φ hφ_ker
      (isSolvable_mulAut_of_isCyclic hcyc)
  let M : Subgroup (Equiv.Perm Ω) := M₀.map L₀.subtype
  let eM : M₀ →* M := L₀.subtype.subgroupMap M₀
  have heM_bijective : Function.Bijective eM :=
    ⟨fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : M => z.val) h)),
      L₀.subtype.subgroupMap_surjective M₀⟩
  refine ⟨M, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨m, _, rfl⟩
    exact m.property.1
  · rintro _ ⟨m, hm, rfl⟩ i
    exact (mem_ker_resFin5_iff γ G m).mp (hM₀_le hm) i
  · rintro g hgG hgγ _ ⟨m, hm, rfl⟩
    have hgL : g ∈ L₀ := by
      refine ⟨hgG, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
      · obtain ⟨i, hi⟩ := hx
        exact ⟨i, g.injective (by rw [hgγ i, hi])⟩
      · obtain ⟨i, rfl⟩ := hx
        exact ⟨i, (hgγ i).symm⟩
    exact ⟨⟨g, hgL⟩ * m * ⟨g, hgL⟩⁻¹, hM₀.1.conj_mem m hm ⟨g, hgL⟩, rfl⟩
  · intro x y
    obtain ⟨x₀, rfl⟩ := heM_bijective.surjective x
    obtain ⟨y₀, rfl⟩ := heM_bijective.surjective y
    rw [← map_mul, ← map_mul, hM₀_comm x₀ y₀]
  · intro hcycM
    apply hM₀_not_cyc
    obtain ⟨g, hg⟩ := hcycM.exists_generator
    obtain ⟨g₀, rfl⟩ := heM_bijective.surjective g
    refine ⟨⟨g₀, fun x₀ => ?_⟩⟩
    obtain ⟨k, hk⟩ := hg (eM x₀)
    refine ⟨k, heM_bijective.injective ?_⟩
    change eM (g₀ ^ k) = eM x₀
    rw [map_zpow]
    exact hk
  · intro a ha m₁ m₂ hm
    obtain ⟨x₁, rfl⟩ := heM_bijective.surjective m₁
    obtain ⟨x₂, rfl⟩ := heM_bijective.surjective m₂
    have hreg := abelian_normal_regular M₀ hM₀.2.1 hM₀_comm (⟨a, ha⟩ : Δ)
    have hsmul : (x₁ • (⟨a, ha⟩ : Δ)) = (x₂ • (⟨a, ha⟩ : Δ)) := Subtype.ext hm
    exact congrArg eM (hreg.injective hsmul)
  · intro a b ha hb
    have hreg := abelian_normal_regular M₀ hM₀.2.1 hM₀_comm (⟨a, ha⟩ : Δ)
    obtain ⟨m₀, hm₀⟩ := hreg.surjective (⟨b, hb⟩ : Δ)
    exact ⟨eM m₀, congrArg Subtype.val hm₀⟩

end GI.Proved
