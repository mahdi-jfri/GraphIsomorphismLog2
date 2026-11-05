module

public import Workspace.Proved.VsMBasic
public import Workspace.Proved.Palfy

@[expose] public section

/-!
# M2, blocks of pieces and Pálfy's bound

`H` permutes the pieces `U i` (`i : Fin m`) through a hom `π : H →* Perm (Fin m)`, and `lab` is
a minimal block system of `π(H)` (`IsMinimalBlocks`). The block sums `X c` (sum of the pieces
with label `c`) are independent, span `V`, have equal dimension (transitivity), and `H` permutes
them through a hom `ρ : H →* Perm C` (`C` = the set of labels). The image of `ρ` is solvable and
primitive: a block `B` of it gives the coarser invariant labeling "least label in the translate
of `B`", which is `lab` itself or constant. Pálfy (`palfy_primitive_aux`) bounds `|ρ(H)|` by
`|C|^24`, and the kernel of `ρ` fixes every block sum.
-/

namespace GI.Proved

open Module
open scoped Pointwise

variable {p : ℕ} [hp : Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

local notation "𝔼" => End (ZMod p) V

/-- `dim V` is the sum of the dimensions of an independent family with sum `V`. -/
theorem vsM_finrank_sum [FiniteDimensional (ZMod p) V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι → Submodule (ZMod p) V) (hind : iSupIndep U) (htop : iSup U = ⊤) :
    ∑ i, finrank (ZMod p) (U i) = finrank (ZMod p) V := by
  have h := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap U) h
  rw [← e.finrank_eq, Module.finrank_directSum]

theorem vsM_perm [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMPermStmt p V := by
  intro H m U hU hind hperm
  classical
  have hinj := hind.injective hU
  let σ : H → Fin m → Fin m := fun h i => Classical.choose (hperm h h.2 i)
  have hσ : ∀ (h : H) i, (U i).map (((h : 𝔼ˣ)) : 𝔼) = U (σ h i) := fun h i =>
    Classical.choose_spec (hperm h h.2 i)
  have huniq : ∀ (h : H) i j, (U i).map (((h : 𝔼ˣ)) : 𝔼) = U j → σ h i = j :=
    fun h i j hj => hinj ((hσ h i).symm.trans hj)
  have hmul : ∀ h k i, σ (h * k) i = σ h (σ k i) := by
    intro h k i
    apply huniq
    rw [Subgroup.coe_mul, Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, hσ k i, hσ h]
  have hone : ∀ i, σ 1 i = i := fun i => huniq 1 i i (by
    rw [OneMemClass.coe_one, Units.val_one, Module.End.one_eq_id, Submodule.map_id])
  let π : H →* Equiv.Perm (Fin m) :=
    { toFun := fun h =>
        { toFun := σ h, invFun := σ h⁻¹
          left_inv := fun i => by rw [← hmul, inv_mul_cancel, hone]
          right_inv := fun i => by rw [← hmul, mul_inv_cancel, hone] }
      map_one' := Equiv.ext hone
      map_mul' := fun h k => Equiv.ext (hmul h k) }
  exact ⟨π, hσ⟩

theorem vsM_orbitSum [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMOrbitSumStmt p V := by
  intro H m U π O hπ hO h hh v hv
  have hle : (⨆ i ∈ O, U i) ≤ (⨆ i ∈ O, U i).comap (((⟨h, hh⟩ : H) : 𝔼ˣ) : 𝔼) := by
    refine iSup₂_le fun i hi => ?_
    rw [← Submodule.map_le_iff_le_comap, hπ]
    exact le_iSup₂ (f := fun j (_ : j ∈ O) => U j) _ (hO _ i hi)
  exact hle hv

theorem vsM_map_blockSum {H : Subgroup 𝔼ˣ} {m : ℕ} {U : Fin m → Submodule (ZMod p) V}
    {pm : H →* Equiv.Perm (Fin m)} {lab : Fin m → ℕ}
    (hpm : ∀ (h : H) i, (U i).map (((h : 𝔼ˣ)) : 𝔼) = U (pm h i))
    (hinv : GI.Cited.InvariantLabeling pm.range lab) (h : H) (i : Fin m) :
    (vsMBlockSum U lab (lab i)).map (((h : 𝔼ˣ)) : 𝔼) = vsMBlockSum U lab (lab (pm h i)) := by
  have hl : ∀ j, lab (pm h j) = lab (pm h i) ↔ lab j = lab i := fun j =>
    hinv (pm h) ⟨h, rfl⟩ j i
  unfold vsMBlockSum
  simp_rw [Submodule.map_iSup, hpm]
  rw [← (pm h).iSup_comp (g := fun j => ⨆ (_ : lab j = lab (pm h i)), U j)]
  exact iSup_congr fun j => iSup_congr_Prop (hl j).symm (fun _ => rfl)

/-- The permutation of the labels induced by `h`. -/
noncomputable def vsMLabPerm {m : ℕ} (lab : Fin m → ℕ) (σ : Equiv.Perm (Fin m)) :
    Set.range lab → Set.range lab :=
  fun c => ⟨lab (σ (Classical.choose c.2)), ⟨_, rfl⟩⟩

theorem vsMLabPerm_apply {H : Subgroup 𝔼ˣ} {m : ℕ}
    {pm : H →* Equiv.Perm (Fin m)} {lab : Fin m → ℕ} (hinv : GI.Cited.InvariantLabeling pm.range lab) (h : H) (i : Fin m) :
    vsMLabPerm lab (pm h) ⟨lab i, ⟨i, rfl⟩⟩ = ⟨lab (pm h i), ⟨pm h i, rfl⟩⟩ := by
  apply Subtype.ext
  have hc : lab (Classical.choose (⟨i, rfl⟩ : ∃ j, lab j = lab i)) = lab i :=
    Classical.choose_spec (⟨i, rfl⟩ : ∃ j, lab j = lab i)
  exact (hinv (pm h) ⟨h, rfl⟩ _ i).2 hc

/-- The action of `H` on the labels. -/
noncomputable def vsMLabHom {H : Subgroup 𝔼ˣ} {m : ℕ}
    {pm : H →* Equiv.Perm (Fin m)} {lab : Fin m → ℕ} (hinv : GI.Cited.InvariantLabeling pm.range lab) :
    H →* Equiv.Perm (Set.range lab) where
  toFun h :=
    { toFun := vsMLabPerm lab (pm h), invFun := vsMLabPerm lab (pm h⁻¹)
      left_inv := by
        rintro ⟨_, i, rfl⟩
        rw [vsMLabPerm_apply hinv, vsMLabPerm_apply hinv, ← Equiv.Perm.mul_apply, ← map_mul,
          inv_mul_cancel, map_one, Equiv.Perm.one_apply]
      right_inv := by
        rintro ⟨_, i, rfl⟩
        rw [vsMLabPerm_apply hinv, vsMLabPerm_apply hinv, ← Equiv.Perm.mul_apply, ← map_mul,
          mul_inv_cancel, map_one, Equiv.Perm.one_apply] }
  map_one' := by
    ext ⟨_, i, rfl⟩
    simp only [Equiv.coe_fn_mk, Equiv.Perm.one_apply]
    rw [vsMLabPerm_apply hinv, map_one, Equiv.Perm.one_apply]
  map_mul' h k := by
    ext ⟨_, i, rfl⟩
    simp only [Equiv.coe_fn_mk, Equiv.Perm.mul_apply]
    rw [vsMLabPerm_apply hinv, vsMLabPerm_apply hinv, vsMLabPerm_apply hinv, map_mul,
      Equiv.Perm.mul_apply]

theorem vsMLabHom_apply {H : Subgroup 𝔼ˣ} {m : ℕ}
    {pm : H →* Equiv.Perm (Fin m)} {lab : Fin m → ℕ} (hinv : GI.Cited.InvariantLabeling pm.range lab) (h : H) (i : Fin m) :
    vsMLabHom hinv h ⟨lab i, ⟨i, rfl⟩⟩ = ⟨lab (pm h i), ⟨pm h i, rfl⟩⟩ :=
  vsMLabPerm_apply hinv h i

/-- The image of `H` on the labels is preprimitive. -/
theorem vsM_labHom_preprimitive {H : Subgroup 𝔼ˣ} {m : ℕ}
    {pm : H →* Equiv.Perm (Fin m)} {lab : Fin m → ℕ} (hinv : GI.Cited.InvariantLabeling pm.range lab)
    (htr : ∀ i j, ∃ h : H, pm h i = j) (hmin : GI.Cited.IsMinimalBlocks pm.range lab) :
    MulAction.IsPreprimitive (vsMLabHom hinv).range (Set.range lab) := by
  classical
  set Γ := (vsMLabHom hinv).range
  have hsmul : ∀ (h : H) i, (⟨vsMLabHom hinv h, ⟨h, rfl⟩⟩ : Γ) • (⟨lab i, ⟨i, rfl⟩⟩ : Set.range lab)
      = ⟨lab (pm h i), ⟨pm h i, rfl⟩⟩ := fun h i => vsMLabHom_apply hinv h i
  have htrans : MulAction.IsPretransitive Γ (Set.range lab) := by
    refine ⟨?_⟩
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    obtain ⟨h, hh⟩ := htr i j
    refine ⟨⟨vsMLabHom hinv h, ⟨h, rfl⟩⟩, ?_⟩
    rw [hsmul]
    exact Subtype.ext (by simp only [hh])
  refine { htrans with isTrivialBlock_of_isBlock := ?_ }
  intro B hB
  rcases Set.eq_empty_or_nonempty B with hBe | ⟨b0, hb0⟩
  · left; rw [hBe]; exact Set.subsingleton_empty
  -- the relation "in a common translate of `B`"
  let R : Set.range lab → Set.range lab → Prop := fun x y => ∃ γ : Γ, x ∈ γ • B ∧ y ∈ γ • B
  have hrefl : ∀ x, R x x := by
    intro x
    obtain ⟨γ, hγ⟩ := MulAction.exists_smul_eq Γ b0 x
    exact ⟨γ, hγ ▸ Set.smul_mem_smul_set hb0, hγ ▸ Set.smul_mem_smul_set hb0⟩
  have hsymm : ∀ x y, R x y → R y x := fun x y ⟨γ, hx, hy⟩ => ⟨γ, hy, hx⟩
  have hsame : ∀ (γ δ : Γ) z, z ∈ γ • B → z ∈ δ • B → γ • B = δ • B := by
    intro γ δ z hz hz'
    by_contra hne
    exact Set.disjoint_left.1 (hB hne) hz hz'
  have htr' : ∀ x y z, R x y → R y z → R x z := by
    rintro x y z ⟨γ, hx, hy⟩ ⟨δ, hy', hz⟩
    exact ⟨γ, hx, (hsame γ δ y hy hy').symm ▸ hz⟩
  have hRinv : ∀ (γ : Γ) x y, R (γ • x) (γ • y) ↔ R x y := by
    intro γ x y
    constructor
    · rintro ⟨δ, hx, hy⟩
      refine ⟨γ⁻¹ * δ, ?_, ?_⟩
      · rw [mul_smul, ← Set.smul_mem_smul_set_iff (a := γ), smul_inv_smul]; exact hx
      · rw [mul_smul, ← Set.smul_mem_smul_set_iff (a := γ), smul_inv_smul]; exact hy
    · rintro ⟨δ, hx, hy⟩
      refine ⟨γ * δ, ?_, ?_⟩
      · rw [mul_smul]; exact Set.smul_mem_smul_set hx
      · rw [mul_smul]; exact Set.smul_mem_smul_set hy
  -- the coarser labeling
  let cl : Fin m → Set ℕ := fun i => lab '' {j | R ⟨lab i, ⟨i, rfl⟩⟩ ⟨lab j, ⟨j, rfl⟩⟩}
  let lab' : Fin m → ℕ := fun i => sInf (cl i)
  have hcl_ne : ∀ i, (cl i).Nonempty := fun i => ⟨lab i, i, hrefl _, rfl⟩
  have hlab' : ∀ i j, lab' i = lab' j ↔ R ⟨lab i, ⟨i, rfl⟩⟩ ⟨lab j, ⟨j, rfl⟩⟩ := by
    intro i j
    constructor
    · intro hij
      obtain ⟨k, hk, hkv⟩ := Nat.sInf_mem (hcl_ne i)
      obtain ⟨k', hk', hkv'⟩ := Nat.sInf_mem (hcl_ne j)
      have hkk : (⟨lab k, ⟨k, rfl⟩⟩ : Set.range lab) = ⟨lab k', ⟨k', rfl⟩⟩ :=
        Subtype.ext (by
          change lab k = lab k'
          rw [hkv, hkv']; exact hij)
      exact htr' _ _ _ hk (hsymm _ _ (hkk ▸ hk'))
    · intro hij
      have : cl i = cl j := by
        ext n
        constructor
        · rintro ⟨k, hk, rfl⟩; exact ⟨k, htr' _ _ _ (hsymm _ _ hij) hk, rfl⟩
        · rintro ⟨k, hk, rfl⟩; exact ⟨k, htr' _ _ _ hij hk, rfl⟩
      exact congrArg sInf this
  have hlabinv : GI.Cited.InvariantLabeling pm.range lab' := by
    rintro _ ⟨h, rfl⟩ i j
    rw [hlab', hlab']
    have e1 : (⟨lab (pm h i), ⟨pm h i, rfl⟩⟩ : Set.range lab) =
        (⟨vsMLabHom hinv h, ⟨h, rfl⟩⟩ : Γ) • ⟨lab i, ⟨i, rfl⟩⟩ := (hsmul h i).symm
    have e2 : (⟨lab (pm h j), ⟨pm h j, rfl⟩⟩ : Set.range lab) =
        (⟨vsMLabHom hinv h, ⟨h, rfl⟩⟩ : Γ) • ⟨lab j, ⟨j, rfl⟩⟩ := (hsmul h j).symm
    rw [e1, e2, hRinv]
  have hcoarse : ∀ i j, lab i = lab j → lab' i = lab' j := by
    intro i j hij
    rw [hlab']
    have : (⟨lab i, ⟨i, rfl⟩⟩ : Set.range lab) = ⟨lab j, ⟨j, rfl⟩⟩ := Subtype.ext hij
    rw [this]; exact hrefl _
  rcases hmin.2.2 lab' hlabinv hcoarse with hA | hA
  · left
    rintro ⟨_, i, rfl⟩ hi ⟨_, j, rfl⟩ hj
    apply Subtype.ext
    change lab i = lab j
    rw [← hA, hlab']
    exact ⟨1, by rw [one_smul]; exact hi, by rw [one_smul]; exact hj⟩
  · right
    ext ⟨_, j, rfl⟩
    simp only [Set.mem_univ, iff_true]
    obtain ⟨_, i, rfl⟩ := b0
    obtain ⟨γ, hi, hj⟩ := (hlab' i j).1 (hA i j)
    have hγ : γ • B = (1 : Γ) • B := hsame γ 1 _ hi (by rw [one_smul]; exact hb0)
    rw [hγ, one_smul] at hj
    exact hj

theorem vsM_blocks [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMBlocksStmt p V := by
  intro H m U pm lab hsol hU hind htop hpm htr hmin
  classical
  have hinv := hmin.1
  set C := Set.range lab
  set X : C → Submodule (ZMod p) V := fun c => vsMBlockSum U lab c
  have hmapX : ∀ (h : H) i, (X ⟨lab i, ⟨i, rfl⟩⟩).map (((h : 𝔼ˣ)) : 𝔼) =
      X ⟨lab (pm h i), ⟨pm h i, rfl⟩⟩ := fun h i => vsM_map_blockSum hpm hinv h i
  -- two blocks
  have hb : 2 ≤ C.ncard := by
    obtain ⟨i, j, hij⟩ := hmin.2.1
    have hsub : ({lab i, lab j} : Set ℕ) ⊆ C := by
      rintro _ (rfl | rfl)
      · exact ⟨i, rfl⟩
      · exact ⟨j, rfl⟩
    rw [← Set.ncard_pair hij]
    exact Set.ncard_le_ncard hsub (Set.toFinite C)
  -- independence and sum
  have hX : ∀ c : C, X c = ⨆ i ∈ {i | lab i = (c : ℕ)}, U i := fun c => rfl
  have hindX : iSupIndep X := by
    intro c
    have hle : (⨆ (c' : C) (_ : c' ≠ c), X c') ≤ ⨆ i ∈ {i | lab i ≠ (c : ℕ)}, U i := by
      refine iSup₂_le fun c' hc' => ?_
      rw [hX]
      refine iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ {i | lab i ≠ (c : ℕ)}) => U i) i ?_
      intro h
      exact hc' (Subtype.ext (hi.symm.trans h))
    refine Disjoint.mono_right hle ?_
    rw [hX]
    exact hind.disjoint_biSup_biSup (Set.disjoint_left.2 fun i hi hi' => hi' hi)
  have htopX : iSup X = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun i => ?_
    refine le_trans ?_ (le_iSup X ⟨lab i, ⟨i, rfl⟩⟩)
    exact le_iSup₂ (f := fun j (_ : lab j = lab i) => U j) i rfl
  -- equal dimension
  have hrank : ∀ c c' : C, finrank (ZMod p) (X c) = finrank (ZMod p) (X c') := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    obtain ⟨h, hh⟩ := htr i j
    have := hmapX h i
    simp only [hh] at this
    rw [← this]
    exact (Submodule.equivMapOfInjective _ (vsT_unit_inj (h : 𝔼ˣ)) _).finrank_eq
  have hsum := vsM_finrank_sum X hindX htopX
  refine ⟨hb, hindX, htopX, ?_, ?_, ?_⟩
  · intro c hc
    rw [← hsum, Finset.sum_congr rfl (fun c' _ => hrank c' ⟨c, hc⟩), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  · rintro h hh _ ⟨i, rfl⟩
    exact ⟨_, ⟨pm ⟨h, hh⟩ i, rfl⟩, hmapX ⟨h, hh⟩ i⟩
  · -- the index bound
    set ρ := vsMLabHom hinv
    haveI : Finite V := Module.finite_of_finite (ZMod p)
    have hker : ρ.ker ≤ (vsMStab X).subgroupOf H := by
      intro h hh
      rw [Subgroup.mem_subgroupOf]
      rintro ⟨_, i, rfl⟩
      rw [hmapX]
      have h1 := vsMLabHom_apply hinv h i
      rw [MonoidHom.mem_ker.1 hh, Equiv.Perm.one_apply] at h1
      exact congrArg X h1.symm
    have hidx : (vsMStab X).relIndex H ≤ Nat.card ρ.range := by
      rw [← Subgroup.index_ker]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hker)
    haveI : Group.IsSolvable H := hsol
    haveI : Group.IsSolvable ρ.range := solvable_of_surjective ρ.rangeRestrict_surjective
    haveI := vsM_labHom_preprimitive hinv htr hmin
    haveI : FaithfulSMul ρ.range C := ⟨fun h => Subtype.ext (Equiv.ext h)⟩
    have hΓ : Nat.card ρ.range ≤ C.ncard ^ 24 := by
      by_cases hnt : Nontrivial ρ.range
      · have h3 := palfy_primitive_aux (G := ρ.range) (α := C)
        rw [Nat.card_coe_set_eq] at h3
        have h' : Nat.card ρ.range ^ 3 ≤ (C.ncard ^ 24) ^ 3 := by rw [← pow_mul]; exact h3
        exact (Nat.pow_le_pow_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp h'
      · rw [not_nontrivial_iff_subsingleton] at hnt
        rw [Nat.card_unique]
        exact Nat.one_le_pow _ _ (by omega)
    exact hidx.trans (hΓ.trans (Nat.pow_le_pow_left (Nat.le_succ _) 24))

end GI.Proved
