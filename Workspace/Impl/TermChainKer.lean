module

public import Workspace.NonabelianChief
public import Workspace.Impl.FreshHier
public import Workspace.Impl.DomRestrict
public import Workspace.Impl.GenCls
public import Workspace.Impl.GenKernel
public import Workspace.Impl.TermConj
public import Workspace.Impl.TermRadStep
public import Workspace.MulticosetSupplement
public import Workspace.CitedChecks.AlgoChecks
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-!
# Orbit-block kernel step and loop for nonabelian chief chains

This file implements the orbit-block kernel reduction of Section 2.2 in `GI.Lang`:

1. `obKernelBody`: Given `[.nat n, encGroup js]` for a nontrivial subgroup `J = gens js ≤ Perm (Fin n)`
   with `js.length ≤ n ^ 2`, finds a largest orbit `D₁` of `J` (`loFuns`), restricts `J` to `D₁`
   (`DomAt`), computes a minimal block system `lab` of the transitive action `J|_{D₁}`
   (`minimalBlocksPrim`), pulls `lab` back to `Fin n` (`obBMLab`), numbers its classes (`clsFuns`),
   and computes the kernel `J' = gens js' < J` fixing all blocks (`kerNFFuns`).
   By `minBlocks_primitive_hom` and `orbitBlockStep_index_le`, `J'` is normal in `J`,
   `2 * |J'| ≤ |J|`, and for any normal transitive subgroup `N ≤ H` with `J ≤ H`,
   `N ⊔ J'` is normalized by `N ⊔ J` with index at most `max (24!) (n ^ (1 + log₂ n)) * n ^ (1 + log₂ n)`.
2. `obStepBody` and `obEntry`: Starting from `J₀ = U` on input `[encGroup us, encGroup ns]`
   (where `N = gens ns < U = gens us ≤ H`), iterates `obKernelBody` for `n ^ 2` steps while
   `U ≤ N ⊔ J` (`iterFuns`), then reduces the generators of `N ⊔ J` (`reduceFuns`).
   After `n ^ 2` steps, `Y = N ⊔ J` satisfies `N ≤ Y < U`, `U` normalizes `Y`, and
   `[U : Y] ≤ max (24!) (n ^ (1 + log₂ n)) * n ^ (1 + log₂ n)`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Cited Equiv Equiv.Perm
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### Orbit restriction and pulled-back block labels -/

/-- The size of the domain `D₁` on `Fin n`. -/
noncomputable abbrev obBMk (D₁ : Set (Fin n)) : ℕ :=
  (domFin (Equiv.refl (Fin n)) D₁).length

theorem obBMk_le (D₁ : Set (Fin n)) : obBMk D₁ ≤ n :=
  length_domFin_le

theorem ob_groupFin_refl (G : Subgroup (Perm (Fin n))) :
    groupFin (Equiv.refl (Fin n)) G = G := by
  ext x
  rw [mem_groupFin]
  exact ⟨fun ⟨h, hh, he⟩ => he ▸ hh, fun hx => ⟨x, hx, rfl⟩⟩

theorem ob_invariant_orbit {J : Subgroup (Perm (Fin n))} {a : Fin n} :
    Invariant J {w | ∃ g ∈ J, g a = w} := by
  intro g hg x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, hh, hgx⟩
    exact ⟨g⁻¹ * h, J.mul_mem (J.inv_mem hg) hh,
      by rw [Perm.mul_apply, hgx, Perm.inv_apply_self]⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨g * h, J.mul_mem hg hh, rfl⟩

/-- For a nontrivial subgroup `J`, a largest orbit `D₁` on `Fin n` has at least `2` points,
and `1 ≤ n`. -/
theorem ob_two_le_obBMk {J : Subgroup (Perm (Fin n))} {D₁ : Set (Fin n)}
    (hJ : ∃ g ∈ J, g ≠ 1)
    (hmax : ∀ b ∈ (Set.univ : Set (Fin n)), Nat.card {w | ∃ g ∈ J, g b = w} ≤ Nat.card D₁) :
    1 ≤ n ∧ 2 ≤ obBMk D₁ := by
  classical
  obtain ⟨g, hg, hne⟩ := hJ
  have hgb : ∃ b : Fin n, g b ≠ b := by
    by_contra! hall
    exact hne (Perm.ext hall)
  obtain ⟨b, hb⟩ := hgb
  have hn1 : 1 ≤ n := by have := b.isLt; omega
  have h2 : 2 ≤ Nat.card {w | ∃ h ∈ J, h b = w} := by
    rw [Nat.card_eq_fintype_card]
    have hlt : 1 < Fintype.card {w | ∃ h ∈ J, h b = w} := by
      rw [Fintype.one_lt_card_iff]
      refine ⟨⟨b, 1, J.one_mem, rfl⟩, ⟨g b, g, hg, rfl⟩, ?_⟩
      intro heq
      exact hb (congrArg Subtype.val heq).symm
    omega
  have hm := hmax b trivial
  rw [card_dom_eq (Equiv.refl (Fin n)) D₁] at hm
  exact ⟨hn1, h2.trans hm⟩

theorem ob_restrK_symm (J : Subgroup (Perm (Fin n))) (D₁ : Set (Fin n)) (hD₁ : Invariant J D₁)
    {g : Perm (Fin n)} (hg : g ∈ J) (j : Fin (obBMk D₁)) :
    ((domEquiv (Equiv.refl (Fin n)) D₁).symm
      (restrK (Equiv.refl (Fin n)) J D₁ hD₁ ⟨g, (ob_groupFin_refl J).symm ▸ hg⟩ j) : Fin n) =
      g ((domEquiv (Equiv.refl (Fin n)) D₁).symm j : Fin n) := by
  simp only [restrK, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    toFin_apply, Equiv.symm_apply_apply, restrictHom_apply, finIso_symm_apply]
  rfl

theorem ob_restrK_domEquiv (J : Subgroup (Perm (Fin n))) (D₁ : Set (Fin n)) (hD₁ : Invariant J D₁)
    {g : Perm (Fin n)} (hg : g ∈ J) {x : Fin n} (hx : x ∈ D₁) :
    restrK (Equiv.refl (Fin n)) J D₁ hD₁ ⟨g, (ob_groupFin_refl J).symm ▸ hg⟩
      (domEquiv (Equiv.refl (Fin n)) D₁ ⟨x, hx⟩) =
      domEquiv (Equiv.refl (Fin n)) D₁ ⟨g x, (hD₁ g hg x).2 hx⟩ := by
  apply (domEquiv (Equiv.refl (Fin n)) D₁).symm.injective
  apply Subtype.ext
  rw [ob_restrK_symm J D₁ hD₁ hg, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The restriction of `J` to an orbit `D₁` is transitive on `Fin (obBMk D₁)`. -/
theorem ob_restrK_trans {J : Subgroup (Perm (Fin n))} {D₁ : Set (Fin n)} (hD₁ : Invariant J D₁)
    {a : Fin n} (hD₁_eq : D₁ = {w | ∃ g ∈ J, g a = w}) (i j : Fin (obBMk D₁)) :
    ∃ h ∈ (restrK (Equiv.refl (Fin n)) J D₁ hD₁).range, h i = j := by
  set x := (domEquiv (Equiv.refl (Fin n)) D₁).symm i
  set y := (domEquiv (Equiv.refl (Fin n)) D₁).symm j
  have hx : x.1 ∈ {w | ∃ g ∈ J, g a = w} := hD₁_eq ▸ x.2
  have hy : y.1 ∈ {w | ∃ g ∈ J, g a = w} := hD₁_eq ▸ y.2
  obtain ⟨g₁, hg₁, hgx⟩ := hx
  obtain ⟨g₂, hg₂, hgy⟩ := hy
  have hg : g₂ * g₁⁻¹ ∈ J := J.mul_mem hg₂ (J.inv_mem hg₁)
  refine ⟨restrK (Equiv.refl (Fin n)) J D₁ hD₁ ⟨g₂ * g₁⁻¹, (ob_groupFin_refl J).symm ▸ hg⟩,
    ⟨_, rfl⟩, ?_⟩
  apply (domEquiv (Equiv.refl (Fin n)) D₁).symm.injective
  apply Subtype.ext
  rw [ob_restrK_symm J D₁ hD₁ hg]
  change (g₂ * g₁⁻¹) x.1 = y.1
  rw [Perm.mul_apply, ← hgx, Perm.inv_apply_self, hgy]

/-- The restricted generators of `1 :: js` on `D₁`. -/
noncomputable def obHs (J : Subgroup (Perm (Fin n))) (D₁ : Set (Fin n)) (hD₁ : Invariant J D₁)
    (js : List (Perm (Fin n))) : List (Perm (Fin (obBMk D₁))) :=
  (1 :: js).map (restrP (Equiv.refl (Fin n)) J D₁ hD₁)

theorem length_obHs (J : Subgroup (Perm (Fin n))) (D₁ : Set (Fin n)) (hD₁ : Invariant J D₁)
    (js : List (Perm (Fin n))) : (obHs J D₁ hD₁ js).length = js.length + 1 := by
  simp [obHs]

theorem ob_gensHs {J : Subgroup (Perm (Fin n))} (D₁ : Set (Fin n)) (hD₁ : Invariant J D₁)
    {js : List (Perm (Fin n))} (hjs : gens js = J) :
    gens (obHs J D₁ hD₁ js) = (restrK (Equiv.refl (Fin n)) J D₁ hD₁).range := by
  rw [range_restrK]
  refine gens_restrP _ _ _ _ ?_
  rw [gens_cons_one, hjs, ob_groupFin_refl]

theorem ob_mem_groupFin {J : Subgroup (Perm (Fin n))} {js : List (Perm (Fin n))}
    (hjs : gens js = J) :
    ∀ g ∈ (1 :: js), g ∈ groupFin (Equiv.refl (Fin n)) J := by
  intro g hg
  rw [ob_groupFin_refl, ← hjs]
  rcases List.mem_cons.1 hg with rfl | hg
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure hg

/-- **The pulled-back block labels on `Fin n`.** Points of `D₁` get their block label in
`0, …, obBMk D₁ - 1`; points outside `D₁` get the label `obBMk D₁`. -/
noncomputable def obBMLab (D₁ : Set (Fin n)) (lab : Fin (obBMk D₁) → ℕ) (i : Fin n) : ℕ :=
  ((List.finRange (obBMk D₁)).map lab ++ [obBMk D₁]).getD
    (posOf (domNat (Equiv.refl (Fin n)) D₁) i) 0

section Lab

variable (D₁ : Set (Fin n)) (lab : Fin (obBMk D₁) → ℕ)

theorem obBMLab_on {x : Fin n} (hx : x ∈ D₁) :
    obBMLab D₁ lab x = lab (domEquiv (Equiv.refl (Fin n)) D₁ ⟨x, hx⟩) := by
  unfold obBMLab
  have heq : posOf (domNat (Equiv.refl (Fin n)) D₁) x =
      (domEquiv (Equiv.refl (Fin n)) D₁ ⟨x, hx⟩ : ℕ) := rfl
  rw [heq]
  set j := domEquiv (Equiv.refl (Fin n)) D₁ ⟨x, hx⟩
  rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem obBMLab_off {x : Fin n} (hx : x ∉ D₁) : obBMLab D₁ lab x = obBMk D₁ := by
  unfold obBMLab
  have hp : posOf (domNat (Equiv.refl (Fin n)) D₁) x = obBMk D₁ := by
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

theorem obBMLab_lt (hlt : ∀ j, lab j < obBMk D₁) {x : Fin n} (hx : x ∈ D₁) :
    obBMLab D₁ lab x < obBMk D₁ := by
  rw [obBMLab_on D₁ lab hx]
  exact hlt _

theorem obBMLab_le (hlt : ∀ j, lab j < obBMk D₁) (x : Fin n) :
    obBMLab D₁ lab x ≤ n := by
  have hk := obBMk_le D₁
  by_cases hx : x ∈ D₁
  · exact (obBMLab_lt D₁ lab hlt hx).le.trans hk
  · rw [obBMLab_off D₁ lab hx]; exact hk

theorem obBig_key_iff (hlt : ∀ j, lab j < obBMk D₁) (i j : Fin n) :
    Cls.keyOf (obBMLab D₁ lab) (indF (Equiv.refl (Fin n)) D₁) i =
        Cls.keyOf (obBMLab D₁ lab) (indF (Equiv.refl (Fin n)) D₁) j ↔
      obBMLab D₁ lab i = obBMLab D₁ lab j := by
  classical
  have hk := obBMk_le D₁
  have hind : ∀ y : Fin n, indF (Equiv.refl (Fin n)) D₁ y = if y ∈ D₁ then 1 else 0 :=
    fun _ => rfl
  unfold Cls.keyOf
  rw [hind i, hind j]
  by_cases hi : i ∈ D₁ <;> by_cases hj : j ∈ D₁ <;>
    simp only [hi, hj, one_ne_zero, ↓reduceIte]
  · have h1 := obBMLab_lt D₁ lab hlt hi
    have h2 := obBMLab_off D₁ lab hj
    constructor <;> intro h <;> omega
  · have h1 := obBMLab_lt D₁ lab hlt hj
    have h2 := obBMLab_off D₁ lab hi
    constructor <;> intro h <;> omega
  · simp [obBMLab_off D₁ lab hi, obBMLab_off D₁ lab hj]

/-- The class representatives of `obBMLab D₁ lab`. -/
noncomputable abbrev obBigRep : Val :=
  encFun (Cls.repOf (Cls.keyOf (obBMLab D₁ lab) (indF (Equiv.refl (Fin n)) D₁)))

theorem obBig_reprVal (hlt : ∀ j, lab j < obBMk D₁) :
    ReprVal n (obBigRep D₁ lab) (fun i j => obBMLab D₁ lab i = obBMLab D₁ lab j) := by
  refine ⟨fun i => ⟨Cls.repOf (Cls.keyOf (obBMLab D₁ lab) (indF (Equiv.refl (Fin n)) D₁)) i,
    Cls.repOf_lt _ i⟩, rfl, fun i j => ?_, fun i => ?_⟩
  · rw [Fin.mk.injEq, Cls.repOf_eq_iff, obBig_key_iff D₁ lab hlt]
  · exact Fin.ext (Cls.repOf_idem _ i)

theorem obBig_wtRep : (obBigRep D₁ lab).wt ≤ 4 * (n + 1) ^ 2 :=
  wt_encFun_le_sq _ fun i => (Cls.repOf_lt _ i).le

theorem obBig_getD_map (l : List ℕ) (j : ℕ) :
    (l.map Val.nat).getD j (.nat 0) = .nat (l.getD j 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> rfl

theorem obBig_gather_eq :
    Val.list (((List.finRange n).map fun i : Fin n =>
        posOf (domNat (Equiv.refl (Fin n)) D₁) i).map fun i =>
      (((List.finRange (obBMk D₁)).map fun j => Val.nat (lab j)) ++
        [Val.nat (obBMk D₁)]).getD i (.nat 0)) = encFun (obBMLab D₁ lab) := by
  have e : ((List.finRange (obBMk D₁)).map fun j => Val.nat (lab j)) ++ [Val.nat (obBMk D₁)] =
      ((List.finRange (obBMk D₁)).map lab ++ [obBMk D₁]).map Val.nat := by
    simp [List.map_map, Function.comp_def]
  rw [e]
  simp only [List.map_map, encFun]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, obBig_getD_map]
  rfl

/-- `J` preserves the partition into labels `obBMLab D₁ lab`. -/
theorem obBM_pres {J : Subgroup (Perm (Fin n))} (hD₁ : Invariant J D₁)
    (hlt : ∀ j, lab j < obBMk D₁)
    (hmb : IsMinimalBlocks (restrK (Equiv.refl (Fin n)) J D₁ hD₁).range lab) :
    ∀ g ∈ J, ∀ i j : Fin n, obBMLab D₁ lab (g i) = obBMLab D₁ lab (g j) ↔
      obBMLab D₁ lab i = obBMLab D₁ lab j := by
  intro g hg i j
  by_cases hi : i ∈ D₁ <;> by_cases hj : j ∈ D₁
  · have hgi : g i ∈ D₁ := (hD₁ g hg i).2 hi
    have hgj : g j ∈ D₁ := (hD₁ g hg j).2 hj
    rw [obBMLab_on D₁ lab hgi, obBMLab_on D₁ lab hgj,
      obBMLab_on D₁ lab hi, obBMLab_on D₁ lab hj,
      ← ob_restrK_domEquiv J D₁ hD₁ hg hi, ← ob_restrK_domEquiv J D₁ hD₁ hg hj]
    exact hmb.1 _ ⟨⟨g, (ob_groupFin_refl J).symm ▸ hg⟩, rfl⟩ _ _
  · have hgi : g i ∈ D₁ := (hD₁ g hg i).2 hi
    have hgj : g j ∉ D₁ := mt (hD₁ g hg j).1 hj
    have h1 := obBMLab_lt D₁ lab hlt hgi
    have h2 := obBMLab_off D₁ lab hgj
    have h3 := obBMLab_lt D₁ lab hlt hi
    have h4 := obBMLab_off D₁ lab hj
    constructor <;> intro h <;> omega
  · have hgi : g i ∉ D₁ := mt (hD₁ g hg i).1 hi
    have hgj : g j ∈ D₁ := (hD₁ g hg j).2 hj
    have h1 := obBMLab_lt D₁ lab hlt hgj
    have h2 := obBMLab_off D₁ lab hgi
    have h3 := obBMLab_lt D₁ lab hlt hj
    have h4 := obBMLab_off D₁ lab hi
    constructor <;> intro h <;> omega
  · have hgi : g i ∉ D₁ := mt (hD₁ g hg i).1 hi
    have hgj : g j ∉ D₁ := mt (hD₁ g hg j).1 hj
    rw [obBMLab_off D₁ lab hgi, obBMLab_off D₁ lab hgj,
      obBMLab_off D₁ lab hi, obBMLab_off D₁ lab hj]

/-- An element `g ∈ J` fixes all labels `obBMLab D₁ lab` on `Fin n` if and only if its
restriction to `D₁` fixes all block labels `lab` on `Fin (obBMk D₁)`. -/
theorem obBM_fix_iff {J : Subgroup (Perm (Fin n))} (hD₁ : Invariant J D₁)
    {g : Perm (Fin n)} (hg : g ∈ J) :
    (∀ i : Fin n, obBMLab D₁ lab (g i) = obBMLab D₁ lab i) ↔
      (∀ j : Fin (obBMk D₁),
        lab (restrK (Equiv.refl (Fin n)) J D₁ hD₁ ⟨g, (ob_groupFin_refl J).symm ▸ hg⟩ j) =
          lab j) := by
  constructor
  · intro H j
    set x := (domEquiv (Equiv.refl (Fin n)) D₁).symm j
    have hj : domEquiv (Equiv.refl (Fin n)) D₁ x = j := Equiv.apply_symm_apply _ j
    have hgx : g x.1 ∈ D₁ := (hD₁ g hg x.1).2 x.2
    have h1 := H x.1
    rw [obBMLab_on D₁ lab hgx, obBMLab_on D₁ lab x.2,
      ← ob_restrK_domEquiv J D₁ hD₁ hg x.2, hj] at h1
    exact h1
  · intro H i
    by_cases hi : i ∈ D₁
    · have hgi : g i ∈ D₁ := (hD₁ g hg i).2 hi
      rw [obBMLab_on D₁ lab hgi, obBMLab_on D₁ lab hi,
        ← ob_restrK_domEquiv J D₁ hD₁ hg hi]
      exact H _
    · have hgi : g i ∉ D₁ := mt (hD₁ g hg i).1 hi
      rw [obBMLab_off D₁ lab hgi, obBMLab_off D₁ lab hi]

end Lab

/-! ### The orbit-block kernel function `obKernelBody` -/

/-- **Single orbit-block kernel step** on `[.nat n, encGroup js]`.
Environment:
`[a, ones, indD1, domL, posV, hsL, gvR, labV, labN, repV]`. -/
def obKernelBody (rep lo dom mg cls ker jmb : ℕ) : Expr :=
  .letE (.call rep (mk2 (arg 0) (.nat 1)))
  (.letE (.get (.call lo (mk2 (arg 1) (.var 1))) (.nat 0))
  (.letE (.call dom (.var 2))
  (.letE (.call (dom + 8) (mk2 (.var 3) (arg 0)))
  (.letE (.call (dom + 22) (mk2 (mk2 (.var 3) (.var 4)) (.get (arg 1) (.nat 1))))
  (.letE (.call mg (mk2 (.length (.var 3)) (.var 5)))
  (.letE (.prim jmb (.var 6))
  (.letE (.call (dom + 18) (mk2 (.snoc (.var 7) (.length (.var 3))) (.var 4)))
  (.letE (.get (.call cls (mk2 (.var 8) (.var 2))) (.nat 2))
    (.call ker (mk2 (arg 1) (.var 9)))))))))))

/-- Where `obKernelBody` and its modules sit in the program. -/
structure ObKernelAt (P : Program) (f rep lo dom mg cls ker jmb jpre jmem : ℕ)
    (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership) : Prop where
  entry : P.funs[f]? = some (obKernelBody rep lo dom mg cls ker jmb)
  rep : P.HasAt rep (replicateFuns rep)
  lo : P.HasAt lo (loFuns lo)
  dom : DomAt P dom
  mg : P.HasAt mg (mkGroupFuns mg)
  cls : P.HasAt cls (clsFuns cls)
  ker : P.HasAt ker (kerNFFuns ker jpre jmem)
  jmb_eq : P.prims[jmb]? = some (minimalBlocksPrim hmb)
  jpre_eq : P.prims[jpre]? = some (preimagePrim hpre)
  jmem_eq : P.prims[jmem]? = some (membershipPrim hmem)

/-- Cost bound of a single `obKernelBody` call on degree `n` with `≤ n ^ 2` generators. -/
noncomputable def obKernelCost (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (n : ℕ) : ℕ :=
  (minimalBlocksPrim hmb).boundSize (10 ^ 4 * (n + 1) ^ 6) +
    (preimagePrim hpre).boundSize (10 ^ 4 * (n + 1) ^ 6) +
    reduceCost hmem n (320 * (n + 1) ^ 6) +
    kerK * (700 * (n + 1) ^ 6) ^ 9 +
    10 ^ 16 * (n + 1) ^ 21

theorem ob_letDet {P : Program} {env : List Val} {e body : Expr} {v : Val} {ca B : ℕ}
    {R : Val → Prop} (hw : ∀ {w}, R w → w.wt ≤ 320 * (n + 1) ^ 6)
    (ha : Det P env e v ca)
    (hb : EvalAll P (env ++ [v]) body (fun w cb => R w ∧ cb ≤ B)) :
    EvalAll P env (.letE e body) (fun w c => R w ∧ c ≤ ca + B + 320 * (n + 1) ^ 6 + 1) := by
  refine EvalAll.letE ha fun v' ca' hv' => ?_
  obtain ⟨rfl, hca⟩ := hv'
  exact hb.mono fun w cb h => ⟨h.1, by have := hw h.1; have := h.2; omega⟩

theorem ob_letAll {P : Program} {env : List Val} {e body : Expr} {Q R : Val → Prop} {ca B : ℕ}
    (hw : ∀ {w}, R w → w.wt ≤ 320 * (n + 1) ^ 6)
    (ha : EvalAll P env e (fun v ca' => Q v ∧ ca' ≤ ca))
    (hb : ∀ v, Q v → EvalAll P (env ++ [v]) body (fun w cb => R w ∧ cb ≤ B)) :
    EvalAll P env (.letE e body) (fun w c => R w ∧ c ≤ ca + B + 320 * (n + 1) ^ 6 + 1) := by
  refine EvalAll.letE ha fun v ca' hv => ?_
  exact (hb v hv.1).mono fun w cb h => ⟨h.1, by have := hw h.1; have := hv.2; have := h.2; omega⟩

theorem ob_wt_inp {js : List (Perm (Fin n))} (hl : js.length ≤ n ^ 2) :
    (Val.list [.nat n, encGroup js]).wt ≤ 700 * (n + 1) ^ 6 := by
  have := wt_list2_le (.nat n) (encGroup js)
  have := wt_nat_le n
  have := wt_encGroup_le_sq hl
  have : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  omega

theorem ob_wt_obHs {J : Subgroup (Perm (Fin n))} {D₁ : Set (Fin n)} (hD₁ : Invariant J D₁)
    {js : List (Perm (Fin n))} (hl : js.length ≤ n ^ 2) :
    (Val.list ((obHs J D₁ hD₁ js).map encPerm)).wt ≤ 100 * (n + 1) ^ 6 ∧
      (encGroup (obHs J D₁ hD₁ js)).wt ≤ 400 * (n + 1) ^ 6 := by
  have hk := obBMk_le D₁
  have hk2 : (obBMk D₁ + 1) ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hp : ∀ σ : Perm (Fin (obBMk D₁)), (encPerm σ).wt ≤ 4 * (n + 1) ^ 2 := fun σ =>
    (wt_encPerm_le σ).trans (Nat.mul_le_mul_left _ hk2)
  have hl1 := GI.Lang.wt_list_le_of ((obHs J D₁ hD₁ js).map encPerm) (c := 4 * (n + 1) ^ 2) (by
    intro v hv; obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hv; exact hp σ)
  simp only [List.length_map, length_obHs] at hl1
  have hj2 : js.length + 1 ≤ (n + 1) ^ 2 := by
    have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  have hm1 : (js.length + 1) * (2 * (4 * (n + 1) ^ 2) + 1) ≤ 9 * (n + 1) ^ 4 := by
    calc (js.length + 1) * (2 * (4 * (n + 1) ^ 2) + 1) ≤
        (n + 1) ^ 2 * (9 * (n + 1) ^ 2) := Nat.mul_le_mul hj2 (by omega)
      _ = 9 * (n + 1) ^ 4 := by ring
  have p46 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have wG := wt_encGroup_le (obHs J D₁ hD₁ js)
  rw [length_obHs] at wG
  have hS : (js.length + 1 + 2) * (obBMk D₁ + 1) ≤ 3 * (n + 1) ^ 3 := by
    calc (js.length + 1 + 2) * (obBMk D₁ + 1) ≤ (3 * (n + 1) ^ 2) * (n + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 3 * (n + 1) ^ 3 := by ring
  have hS2 : ((js.length + 1 + 2) * (obBMk D₁ + 1)) ^ 2 ≤ 9 * (n + 1) ^ 6 := by
    calc ((js.length + 1 + 2) * (obBMk D₁ + 1)) ^ 2 ≤ (3 * (n + 1) ^ 3) ^ 2 :=
          Nat.pow_le_pow_left hS 2
      _ = 9 * (n + 1) ^ 6 := by ring
  constructor <;> omega

/-- Step 1 of `obKernelBody`: `ones = replicate n 1`. -/
theorem obKernel_step1 {P : Program} {rep : ℕ} (hrep : P.HasAt rep (replicateFuns rep))
    {js : List (Perm (Fin n))} (hl : js.length ≤ n ^ 2) :
    Det P [.list [.nat n, encGroup js]] (.call rep (mk2 (arg 0) (.nat 1)))
      (indVal (Equiv.refl (Fin n)) Set.univ) (10 ^ 6 * (n + 1) ^ 6) := by
  have g0 := Det.arg' (P := P) (vs := [.nat n, encGroup js]) (rest := []) (j := 0) rfl
  have hrs := replicate_spec hrep n (.nat 1)
  have hrs' : FunDet P rep (.list [.nat n, .nat 1]) (Val.list (List.replicate n (.nat 1)))
      (loopModK * (n + 1) * ((Val.list [.nat n, .nat 1]).wt + n +
        (Val.list (List.replicate n (.nat 1))).wt + 1)) :=
    hrs.mono fun w c ⟨hw, hc⟩ => ⟨hw, by subst hw; exact hc⟩
  have d1 := Det.call (Det.mk2 g0 (Det.nat 1)) hrs'
  rw [replicate_eq_indVal (Equiv.refl (Fin n))] at d1
  refine d1.mono ?_
  have wi := ob_wt_inp hl
  have wo := wt_replicate_one_le n
  rw [replicate_eq_indVal (Equiv.refl (Fin n))] at wo
  have w1 := wt_list2_le (.nat n) (.nat 1)
  have wn := wt_nat_le n
  have w1' := wt_nat_le 1
  have p16 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hrepc : loopModK * (n + 1) * ((Val.list [.nat n, .nat 1]).wt + n +
      (indVal (Equiv.refl (Fin n)) Set.univ).wt + 1) ≤
      loopModK * (n + 1) * (50 * (n + 1)) := Nat.mul_le_mul_left _ (by omega)
  have hrepc' : loopModK * (n + 1) * (50 * (n + 1)) = 50000 * (n + 1) ^ 2 := by
    simp only [loopModK]; ring
  omega

/-- Step 2 of `obKernelBody`: indicator of a largest orbit `D₁`. -/
theorem obKernel_step2 {P : Program} {lo : ℕ} {D₁ : Set (Fin n)} {js : List (Perm (Fin n))}
    (hl : js.length ≤ n ^ 2)
    (hlo' : FunDet P lo (.list [encGroup js, indVal (Equiv.refl (Fin n)) Set.univ])
      (.list [indVal (Equiv.refl (Fin n)) D₁, indVal (Equiv.refl (Fin n)) (Set.univ \ D₁)])
      (loK * (n + 1) ^ 15)) :
    Det P [.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ]
      (.get (.call lo (mk2 (arg 1) (.var 1))) (.nat 0))
      (indVal (Equiv.refl (Fin n)) D₁) (2 * loK * (n + 1) ^ 15) := by
  have g1 := Det.arg' (P := P) (vs := [.nat n, encGroup js])
    (rest := [indVal (Equiv.refl (Fin n)) Set.univ]) (j := 1) rfl
  have v1 := Det.var' (P := P)
    (env := [.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ]) (i := 1) rfl
  have dc := Det.call (Det.mk2 g1 v1) hlo'
  have dg := Det.get' dc (Det.nat 0) (v := indVal (Equiv.refl (Fin n)) D₁) rfl
  refine dg.mono ?_
  have wi := ob_wt_inp hl
  have wg := wt_encGroup_le_sq hl
  have wU : (indVal (Equiv.refl (Fin n)) Set.univ).wt ≤ 11 * (n + 1) := by
    have : (indVal (Equiv.refl (Fin n)) Set.univ).wt ≤ n * (2 * 1 + 5) + 4 :=
      wt_encFun_le _ (indF_le_one (Equiv.refl (Fin n)) Set.univ)
    omega
  have wD1 : (indVal (Equiv.refl (Fin n)) D₁).wt ≤ 11 * (n + 1) := by
    have : (indVal (Equiv.refl (Fin n)) D₁).wt ≤ n * (2 * 1 + 5) + 4 :=
      wt_encFun_le _ (indF_le_one (Equiv.refl (Fin n)) D₁)
    omega
  have wD2 : (indVal (Equiv.refl (Fin n)) (Set.univ \ D₁)).wt ≤ 11 * (n + 1) := by
    have : (indVal (Equiv.refl (Fin n)) (Set.univ \ D₁)).wt ≤ n * (2 * 1 + 5) + 4 :=
      wt_encFun_le _ (indF_le_one (Equiv.refl (Fin n)) (Set.univ \ D₁))
    omega
  have w2 := wt_list2_le (encGroup js) (indVal (Equiv.refl (Fin n)) Set.univ)
  have wlo := wt_list2_le (indVal (Equiv.refl (Fin n)) D₁)
    (indVal (Equiv.refl (Fin n)) (Set.univ \ D₁))
  have p115 : n + 1 ≤ (n + 1) ^ 15 := Nat.le_self_pow (by norm_num) _
  have p615 : (n + 1) ^ 6 ≤ (n + 1) ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [loK] at *
  omega

/-- Step 3 of `obKernelBody`: domain position list `domNat`. -/
theorem obKernel_step3 {P : Program} {dom : ℕ} (hdom : DomAt P dom) (D₁ : Set (Fin n))
    (js : List (Perm (Fin n))) (rest : List Val) :
    Det P ([.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
        indVal (Equiv.refl (Fin n)) D₁] ++ rest)
      (.call dom (.var 2))
      (natList (domNat (Equiv.refl (Fin n)) D₁)) (2 * domListK * (n + 1) ^ 3) := by
  have dv2 := Det.var' (P := P) (env := [.list [.nat n, encGroup js],
    indVal (Equiv.refl (Fin n)) Set.univ, indVal (Equiv.refl (Fin n)) D₁] ++ rest) (i := 2)
    (v := indVal (Equiv.refl (Fin n)) D₁) rfl
  have d := Det.call dv2 (domList_spec hdom (Equiv.refl (Fin n)) D₁)
  refine d.mono ?_
  have wD1 : (indVal (Equiv.refl (Fin n)) D₁).wt ≤ 11 * (n + 1) := by
    have : (indVal (Equiv.refl (Fin n)) D₁).wt ≤ n * (2 * 1 + 5) + 4 :=
      wt_encFun_le _ (indF_le_one (Equiv.refl (Fin n)) D₁)
    omega
  have wN := wt_domNat_le (Equiv.refl (Fin n)) D₁
  have p13 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have p23 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [domListK] at *
  omega

/-- Step 4 of `obKernelBody`: position lookup table `posVal`. -/
theorem obKernel_step4 {P : Program} {dom : ℕ} (hdom : DomAt P dom) (D₁ : Set (Fin n))
    {js : List (Perm (Fin n))} (hl : js.length ≤ n ^ 2) :
    Det P [.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
        indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁)]
      (.call (dom + 8) (mk2 (.var 3) (arg 0)))
      (posVal (Equiv.refl (Fin n)) D₁) (2 * posTabK * (n + 1) ^ 6) := by
  have dv3 := Det.var' (P := P) (env := [.list [.nat n, encGroup js],
    indVal (Equiv.refl (Fin n)) Set.univ, indVal (Equiv.refl (Fin n)) D₁,
    natList (domNat (Equiv.refl (Fin n)) D₁)]) (i := 3)
    (v := natList (domNat (Equiv.refl (Fin n)) D₁)) rfl
  have g0 := Det.arg' (P := P) (vs := [.nat n, encGroup js])
    (rest := [indVal (Equiv.refl (Fin n)) Set.univ, indVal (Equiv.refl (Fin n)) D₁,
      natList (domNat (Equiv.refl (Fin n)) D₁)]) (j := 0) (v := .nat n) rfl
  have d := Det.call (Det.mk2 dv3 g0) (posTab_spec hdom (Equiv.refl (Fin n)) D₁)
  refine d.mono ?_
  have wi := ob_wt_inp hl
  have wN := wt_domNat_le (Equiv.refl (Fin n)) D₁
  have wP := wt_posVal_le (Equiv.refl (Fin n)) D₁
  have wn := wt_nat_le n
  have w2 := wt_list2_le (natList (domNat (Equiv.refl (Fin n)) D₁)) (.nat n)
  have p16 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p46 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [posTabK] at *
  omega

/-- Step 5 of `obKernelBody`: restricted generators `obHs`. -/
theorem obKernel_step5 {P : Program} {dom : ℕ} (hdom : DomAt P dom) (D₁ : Set (Fin n))
    {js : List (Perm (Fin n))} (hD₁ : Invariant (gens js) D₁) (hl : js.length ≤ n ^ 2) :
    Det P [.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
        indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁),
        posVal (Equiv.refl (Fin n)) D₁]
      (.call (dom + 22) (mk2 (mk2 (.var 3) (.var 4)) (.get (arg 1) (.nat 1))))
      (.list ((obHs (gens js) D₁ hD₁ js).map encPerm)) (200 * restrListK * (n + 1) ^ 21) := by
  set env := [Val.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
    indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁),
    posVal (Equiv.refl (Fin n)) D₁]
  have dv3 := Det.var' (P := P) (env := env) (i := 3)
    (v := natList (domNat (Equiv.refl (Fin n)) D₁)) rfl
  have dv4 := Det.var' (P := P) (env := env) (i := 4)
    (v := posVal (Equiv.refl (Fin n)) D₁) rfl
  have da := Det.arg' (P := P) (vs := [.nat n, encGroup js])
    (rest := [indVal (Equiv.refl (Fin n)) Set.univ, indVal (Equiv.refl (Fin n)) D₁,
      natList (domNat (Equiv.refl (Fin n)) D₁), posVal (Equiv.refl (Fin n)) D₁])
    (j := 1) (v := encGroup js) rfl
  have dg := Det.get' da (Det.nat 1) (v := .list ((1 :: js).map encPerm))
    (show [Val.nat n, Val.list ((1 :: js).map encPerm)][1]? = some _ from rfl)
  have hr := restrList_spec (Equiv.refl (Fin n)) (gens js) D₁ hD₁ hdom (ob_mem_groupFin rfl)
  have d := Det.call (Det.mk2 (Det.mk2 dv3 dv4) dg) hr
  have e : (1 :: js).map (fun g => encPerm (restrP (Equiv.refl (Fin n)) (gens js) D₁ hD₁ g)) =
      (obHs (gens js) D₁ hD₁ js).map encPerm := by
    simp [obHs, List.map_map, Function.comp_def]
  rw [e] at d
  refine d.mono ?_
  have wi := ob_wt_inp hl
  have wg := wt_encGroup_le_sq hl
  have wN := wt_domNat_le (Equiv.refl (Fin n)) D₁
  have wP := wt_posVal_le (Equiv.refl (Fin n)) D₁
  have wCtx := wt_list2_le (natList (domNat (Equiv.refl (Fin n)) D₁))
    (posVal (Equiv.refl (Fin n)) D₁)
  have w1js : (Val.list ((1 :: js).map encPerm)).wt < (encGroup js).wt :=
    wt_le_wt_list (vs := [Val.nat n, Val.list ((1 :: js).map encPerm)]) (by simp)
  have wArg := wt_list2_le (.list [natList (domNat (Equiv.refl (Fin n)) D₁),
    posVal (Equiv.refl (Fin n)) D₁]) (.list ((1 :: js).map encPerm))
  have wOut := (ob_wt_obHs hD₁ hl).1
  have hS3 := measure_le_of_sq hl
  have h7 : (((1 :: js).length + 1) * (n + 1)) ^ 7 ≤ 128 * (n + 1) ^ 21 := by
    calc (((1 :: js).length + 1) * (n + 1)) ^ 7 = ((js.length + 2) * (n + 1)) ^ 7 := by simp
      _ ≤ (2 * (n + 1) ^ 3) ^ 7 := Nat.pow_le_pow_left hS3 7
      _ = 128 * (n + 1) ^ 21 := by ring
  have p221 : (n + 1) ^ 2 ≤ (n + 1) ^ 21 := Nat.pow_le_pow_right (by omega) (by omega)
  have p621 : (n + 1) ^ 6 ≤ (n + 1) ^ 21 := Nat.pow_le_pow_right (by omega) (by omega)
  have hrl := Nat.mul_le_mul_left restrListK h7
  simp only [restrListK] at *
  omega

/-- Step 6 of `obKernelBody`: restricted group value `encGroup (obHs ...)`. -/
theorem obKernel_step6 {P : Program} {mg : ℕ} (hmg : P.HasAt mg (mkGroupFuns mg))
    (D₁ : Set (Fin n)) {js : List (Perm (Fin n))} (hD₁ : Invariant (gens js) D₁)
    (hl : js.length ≤ n ^ 2) :
    Det P [.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
        indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁),
        posVal (Equiv.refl (Fin n)) D₁, .list ((obHs (gens js) D₁ hD₁ js).map encPerm)]
      (.call mg (mk2 (.length (.var 3)) (.var 5)))
      (encGroup (obHs (gens js) D₁ hD₁ js)) (50 * mkGroupK * (n + 1) ^ 9) := by
  set env := [Val.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
    indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁),
    posVal (Equiv.refl (Fin n)) D₁, .list ((obHs (gens js) D₁ hD₁ js).map encPerm)]
  have dv3 := Det.var' (P := P) (env := env) (i := 3)
    (v := .list ((domNat (Equiv.refl (Fin n)) D₁).map Val.nat)) rfl
  have dl := Det.length dv3
  have hlen : ((domNat (Equiv.refl (Fin n)) D₁).map Val.nat).length = obBMk D₁ := by
    rw [List.length_map, length_domNat]
  rw [hlen] at dl
  have dv5 := Det.var' (P := P) (env := env) (i := 5)
    (v := .list ((obHs (gens js) D₁ hD₁ js).map encPerm)) rfl
  have d := Det.call (Det.mk2 dl dv5) (mkGroup_spec hmg (obHs (gens js) D₁ hD₁ js))
  refine d.mono ?_
  have wN := wt_domNat_le (Equiv.refl (Fin n)) D₁
  have eN : (Val.list ((domNat (Equiv.refl (Fin n)) D₁).map Val.nat)).wt =
    (natList (domNat (Equiv.refl (Fin n)) D₁)).wt := rfl
  have w5 := (ob_wt_obHs hD₁ hl).1
  have w6 := (ob_wt_obHs hD₁ hl).2
  have hk := obBMk_le D₁
  have wk := wt_nat_le (obBMk D₁)
  have w2 := wt_list2_le (.nat (obBMk D₁)) (.list ((obHs (gens js) D₁ hD₁ js).map encPerm))
  have hj2 : js.length + 3 ≤ 3 * (n + 1) ^ 2 := by
    have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  have hS : ((obHs (gens js) D₁ hD₁ js).length + 2) * (obBMk D₁ + 1) ≤ 3 * (n + 1) ^ 3 := by
    rw [length_obHs]
    calc (js.length + 1 + 2) * (obBMk D₁ + 1) ≤ (3 * (n + 1) ^ 2) * (n + 1) :=
          Nat.mul_le_mul hj2 (by omega)
      _ = 3 * (n + 1) ^ 3 := by ring
  have hS3 : (((obHs (gens js) D₁ hD₁ js).length + 2) * (obBMk D₁ + 1)) ^ 3 ≤
      27 * (n + 1) ^ 9 := by
    calc (((obHs (gens js) D₁ hD₁ js).length + 2) * (obBMk D₁ + 1)) ^ 3 ≤
        (3 * (n + 1) ^ 3) ^ 3 := Nat.pow_le_pow_left hS 3
      _ = 27 * (n + 1) ^ 9 := by ring
  have hmk := Nat.mul_le_mul_left mkGroupK hS3
  have p19 : n + 1 ≤ (n + 1) ^ 9 := Nat.le_self_pow (by norm_num) _
  have p29 : (n + 1) ^ 2 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have p69 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [mkGroupK] at *
  omega

/-- Step 7 of `obKernelBody`: minimal blocks primitive call on `gvR`. -/
theorem obKernel_step7 (hmb : MinimalBlocks) {P : Program} {jmb : ℕ}
    (hjmb : P.prims[jmb]? = some (minimalBlocksPrim hmb))
    (D₁ : Set (Fin n)) {js : List (Perm (Fin n))} (hD₁ : Invariant (gens js) D₁)
    (hk2 : 2 ≤ obBMk D₁)
    (htr : ∀ i j : Fin (obBMk D₁),
      ∃ h ∈ (restrK (Equiv.refl (Fin n)) (gens js) D₁ hD₁).range, h i = j)
    (hl : js.length ≤ n ^ 2) :
    EvalAll P [.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
        indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁),
        posVal (Equiv.refl (Fin n)) D₁, .list ((obHs (gens js) D₁ hD₁ js).map encPerm),
        encGroup (obHs (gens js) D₁ hD₁ js)]
      (.prim jmb (.var 6))
      (fun v c => BlocksOut (restrK (Equiv.refl (Fin n)) (gens js) D₁ hD₁).range v ∧
        c ≤ (minimalBlocksPrim hmb).boundSize (10 ^ 4 * (n + 1) ^ 6) + 1000 * (n + 1) ^ 6) := by
  have dv6 := Det.var' (P := P) (env := [.list [.nat n, encGroup js],
    indVal (Equiv.refl (Fin n)) Set.univ, indVal (Equiv.refl (Fin n)) D₁,
    natList (domNat (Equiv.refl (Fin n)) D₁), posVal (Equiv.refl (Fin n)) D₁,
    .list ((obHs (gens js) D₁ hD₁ js).map encPerm), encGroup (obHs (gens js) D₁ hD₁ js)])
    (i := 6) (v := encGroup (obHs (gens js) D₁ hD₁ js)) rfl
  have hG : GroupVal (obBMk D₁) (encGroup (obHs (gens js) D₁ hD₁ js))
      (restrK (Equiv.refl (Fin n)) (gens js) D₁ hD₁).range :=
    ⟨obHs (gens js) D₁ hD₁ js, rfl, ob_gensHs D₁ hD₁ rfl⟩
  refine (minimalBlocks_call hmb hjmb dv6 hG hk2 htr).mono fun v c hv => ⟨hv.1, ?_⟩
  clear dv6 hG
  have w6 := (ob_wt_obHs hD₁ hl).2
  have hsz : (encGroup (obHs (gens js) D₁ hD₁ js)).size ≤ 10 ^ 4 * (n + 1) ^ 6 :=
    (Val.size_le_wt _).trans (by omega)
  have hb := (minimalBlocksPrim hmb).bound_le hsz
  have hk := obBMk_le D₁
  have hk2' : (obBMk D₁ + 1) ^ 2 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hc := hv.2
  omega

/-- Step 8 of `obKernelBody`: pulled-back labels `encFun (obBMLab D₁ lab)`. -/
theorem obKernel_step8 {P : Program} {dom : ℕ} (hdom : DomAt P dom)
    (D₁ : Set (Fin n)) {js : List (Perm (Fin n))} (hD₁ : Invariant (gens js) D₁)
    {lab : Fin (obBMk D₁) → ℕ} (hlt : ∀ j, lab j < obBMk D₁) :
    Det P [.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
        indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁),
        posVal (Equiv.refl (Fin n)) D₁, .list ((obHs (gens js) D₁ hD₁ js).map encPerm),
        encGroup (obHs (gens js) D₁ hD₁ js), encFun lab]
      (.call (dom + 18) (mk2 (.snoc (.var 7) (.length (.var 3))) (.var 4)))
      (encFun (obBMLab D₁ lab)) (10 ^ 10 * (n + 1) ^ 6) := by
  set env := [Val.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
    indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁),
    posVal (Equiv.refl (Fin n)) D₁, .list ((obHs (gens js) D₁ hD₁ js).map encPerm),
    encGroup (obHs (gens js) D₁ hD₁ js), encFun lab]
  have dv7 := Det.var' (P := P) (env := env) (i := 7)
    (v := .list ((List.finRange (obBMk D₁)).map fun j => .nat (lab j))) rfl
  have dv3 := Det.var' (P := P) (env := env) (i := 3)
    (v := .list ((domNat (Equiv.refl (Fin n)) D₁).map Val.nat)) rfl
  have dl := Det.length dv3
  have hlen : ((domNat (Equiv.refl (Fin n)) D₁).map Val.nat).length = obBMk D₁ := by
    rw [List.length_map, length_domNat]
  rw [hlen] at dl
  have ds := Det.snoc dv7 dl
  have epos : posVal (Equiv.refl (Fin n)) D₁ = natList ((List.finRange n).map
      fun i : Fin n => posOf (domNat (Equiv.refl (Fin n)) D₁) i) := by
    simp [posVal, encFun, natList, List.map_map, Function.comp_def]
  have dv4 := Det.var' (P := P) (env := env) (i := 4)
    (v := natList ((List.finRange n).map
      fun i : Fin n => posOf (domNat (Equiv.refl (Fin n)) D₁) i)) (congrArg some epos)
  have hg := gather_spec hdom.gather
    (L := (List.finRange (obBMk D₁)).map (fun j => Val.nat (lab j)) ++ [Val.nat (obBMk D₁)])
    (is := (List.finRange n).map
      fun i : Fin n => posOf (domNat (Equiv.refl (Fin n)) D₁) i) (by
        intro i hi
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
        have hp := posOf_le (domNat (Equiv.refl (Fin n)) D₁) j
        rw [length_domNat] at hp
        change posOf (domNat (Equiv.refl (Fin n)) D₁) j ≤ obBMk D₁ at hp
        simp only [List.length_append, List.length_map, List.length_finRange, List.length_cons,
          List.length_nil]
        omega)
  have d := Det.call (Det.mk2 ds dv4) hg
  rw [obBig_gather_eq D₁ lab] at d
  refine d.mono ?_
  have hk := obBMk_le D₁
  have hk2 : (obBMk D₁ + 1) ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have w7 := (wt_encFun_le_sq lab fun j => (hlt j).le).trans (Nat.mul_le_mul_left _ hk2)
  have e7 : (Val.list ((List.finRange (obBMk D₁)).map fun j => .nat (lab j))).wt =
    (encFun lab).wt := rfl
  have w3 := wt_domNat_le (Equiv.refl (Fin n)) D₁
  have e3 : (Val.list ((domNat (Equiv.refl (Fin n)) D₁).map Val.nat)).wt =
    (natList (domNat (Equiv.refl (Fin n)) D₁)).wt := rfl
  have w4 := wt_posVal_le (Equiv.refl (Fin n)) D₁
  rw [epos] at w4
  have wsn := wt_list_snoc_le ((List.finRange (obBMk D₁)).map fun j => Val.nat (lab j))
    (.nat (obBMk D₁))
  have wk := wt_nat_le (obBMk D₁)
  have wa := wt_list2_le (.list ((List.finRange (obBMk D₁)).map (fun j => Val.nat (lab j)) ++
    [Val.nat (obBMk D₁)])) (natList ((List.finRange n).map
      fun i : Fin n => posOf (domNat (Equiv.refl (Fin n)) D₁) i))
  have wo := wt_encFun_le_sq (obBMLab D₁ lab) (obBMLab_le D₁ lab hlt)
  have p12 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hA : (Val.list [.list ((List.finRange (obBMk D₁)).map (fun j => Val.nat (lab j)) ++
      [Val.nat (obBMk D₁)]), natList ((List.finRange n).map
      fun i : Fin n => posOf (domNat (Equiv.refl (Fin n)) D₁) i)]).wt + 1 ≤
      40 * (n + 1) ^ 2 := by omega
  have hA3 : gatherK * ((Val.list [.list ((List.finRange (obBMk D₁)).map
      (fun j => Val.nat (lab j)) ++ [Val.nat (obBMk D₁)]), natList ((List.finRange n).map
      fun i : Fin n => posOf (domNat (Equiv.refl (Fin n)) D₁) i)]).wt + 1) ^ 3 ≤
      gatherK * (64000 * (n + 1) ^ 6) := by
    refine Nat.mul_le_mul_left _ ?_
    calc _ ≤ (40 * (n + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hA 3
      _ = 64000 * (n + 1) ^ 6 := by ring
  simp only [gatherK] at *
  omega

/-- Step 9 of `obKernelBody`: class representatives `obBigRep D₁ lab`. -/
theorem obKernel_step9 {P : Program} {cls : ℕ} (hcls : P.HasAt cls (clsFuns cls))
    (D₁ : Set (Fin n)) {js : List (Perm (Fin n))} (hD₁ : Invariant (gens js) D₁)
    {lab : Fin (obBMk D₁) → ℕ} (hlt : ∀ j, lab j < obBMk D₁) :
    Det P [.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
        indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁),
        posVal (Equiv.refl (Fin n)) D₁, .list ((obHs (gens js) D₁ hD₁ js).map encPerm),
        encGroup (obHs (gens js) D₁ hD₁ js), encFun lab, encFun (obBMLab D₁ lab)]
      (.get (.call cls (mk2 (.var 8) (.var 2))) (.nat 2))
      (obBigRep D₁ lab) (10 * clsK * (n + 1) ^ 6) := by
  set env := [Val.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
    indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁),
    posVal (Equiv.refl (Fin n)) D₁, .list ((obHs (gens js) D₁ hD₁ js).map encPerm),
    encGroup (obHs (gens js) D₁ hD₁ js), encFun lab, encFun (obBMLab D₁ lab)]
  have dv8 := Det.var' (P := P) (env := env) (i := 8) (v := encFun (obBMLab D₁ lab)) rfl
  have dv2 := Det.var' (P := P) (env := env) (i := 2)
    (v := encFun (indF (Equiv.refl (Fin n)) D₁)) rfl
  have hc := cls_spec hcls (obBMLab D₁ lab) (indF (Equiv.refl (Fin n)) D₁) (X := n)
    (obBMLab_le D₁ lab hlt) (indF_le_one _ _) le_rfl
  have hcw : (clsVal (obBMLab D₁ lab) (indF (Equiv.refl (Fin n)) D₁)).wt < clsK * (n + 1) ^ 4 := by
    obtain ⟨body, -, h'⟩ := FunAll.wt_lt hc
    obtain ⟨v', c', -, ⟨⟨rfl, h1⟩, h2⟩⟩ := h'.exists_eval
    omega
  have dc := Det.call (Det.mk2 dv8 dv2) hc
  have dg := Det.get' dc (Det.nat 2) (v := obBigRep D₁ lab) rfl
  refine dg.mono ?_
  have w8 := wt_encFun_le_sq (obBMLab D₁ lab) (obBMLab_le D₁ lab hlt)
  have w2 : (encFun (indF (Equiv.refl (Fin n)) D₁)).wt ≤ 11 * (n + 1) := by
    have := wt_encFun_le _ (indF_le_one (Equiv.refl (Fin n)) D₁); omega
  have wa := wt_list2_le (encFun (obBMLab D₁ lab)) (encFun (indF (Equiv.refl (Fin n)) D₁))
  have wr := obBig_wtRep D₁ lab
  have p16 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p46 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [clsK] at *
  omega

/-- Tail call of `obKernelBody`: kernel `kerNFFuns` on `[encGroup js, obBigRep D₁ lab]`. -/
theorem obKernel_step10 (hpre : Preimage) (hmem : Membership) {P : Program}
    {ker jpre jmem : ℕ} (hker : P.HasAt ker (kerNFFuns ker jpre jmem))
    (hjpre : P.prims[jpre]? = some (preimagePrim hpre))
    (hjmem : P.prims[jmem]? = some (membershipPrim hmem))
    (D₁ : Set (Fin n)) {js : List (Perm (Fin n))} (hD₁ : Invariant (gens js) D₁)
    (hl : js.length ≤ n ^ 2)
    {lab : Fin (obBMk D₁) → ℕ} (hlt : ∀ j, lab j < obBMk D₁)
    (hmb_lab : IsMinimalBlocks (restrK (Equiv.refl (Fin n)) (gens js) D₁ hD₁).range lab) :
    EvalAll P [.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
        indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁),
        posVal (Equiv.refl (Fin n)) D₁, .list ((obHs (gens js) D₁ hD₁ js).map encPerm),
        encGroup (obHs (gens js) D₁ hD₁ js), encFun lab, encFun (obBMLab D₁ lab),
        obBigRep D₁ lab]
      (.call ker (mk2 (arg 1) (.var 9)))
      (fun w c =>
        (∃ K, GroupValC n w K ∧ ∀ g, g ∈ K ↔ g ∈ gens js ∧
          ∀ i, obBMLab D₁ lab (g i) = obBMLab D₁ lab i) ∧
        c ≤ (preimagePrim hpre).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          reduceCost hmem n (320 * (n + 1) ^ 6) +
          kerK * (700 * (n + 1) ^ 6) ^ 9 + 10 ^ 10 * (n + 1) ^ 6) := by
  set env := [Val.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
    indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁),
    posVal (Equiv.refl (Fin n)) D₁, .list ((obHs (gens js) D₁ hD₁ js).map encPerm),
    encGroup (obHs (gens js) D₁ hD₁ js), encFun lab, encFun (obBMLab D₁ lab),
    obBigRep D₁ lab]
  have da := Det.arg' (P := P) (vs := [.nat n, encGroup js])
    (rest := [indVal (Equiv.refl (Fin n)) Set.univ, indVal (Equiv.refl (Fin n)) D₁,
      natList (domNat (Equiv.refl (Fin n)) D₁), posVal (Equiv.refl (Fin n)) D₁,
      .list ((obHs (gens js) D₁ hD₁ js).map encPerm), encGroup (obHs (gens js) D₁ hD₁ js),
      encFun lab, encFun (obBMLab D₁ lab), obBigRep D₁ lab]) (j := 1) (v := encGroup js) rfl
  have dv9 := Det.var' (P := P) (env := env) (i := 9) (v := obBigRep D₁ lab) rfl
  have hk := kerNF_spec hpre hmem hker hjpre hjmem ⟨js, rfl, rfl⟩ (obBig_reprVal D₁ lab hlt)
    (obBM_pres D₁ lab hD₁ hlt hmb_lab)
  refine EvalAll.call_funAll (Det.mk2 da dv9) fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine hk.mono fun w cb h => ⟨h.1, ?_⟩
  clear da dv9 hk
  obtain ⟨K, ⟨js', rfl, rfl, hl'⟩, -⟩ := h.1
  have ww := wt_encGroup_le_sq hl'
  have wi := ob_wt_inp hl
  have wg := wt_encGroup_le_sq hl
  have wr := obBig_wtRep D₁ lab
  have wa := wt_list2_le (encGroup js) (obBigRep D₁ lab)
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hT : (Val.list [encGroup js, obBigRep D₁ lab]).wt ≤ 700 * (n + 1) ^ 6 := by omega
  have hb : (preimagePrim hpre).boundSize (3 * (Val.list [encGroup js, obBigRep D₁ lab]).wt) ≤
      (preimagePrim hpre).boundSize (10 ^ 4 * (n + 1) ^ 6) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hT9 : kerK * (Val.list [encGroup js, obBigRep D₁ lab]).wt ^ 9 ≤
      kerK * (700 * (n + 1) ^ 6) ^ 9 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT 9)
  have hc := h.2
  unfold kerNFCost at hc
  clear_value env
  generalize kerK * (700 * (n + 1) ^ 6) ^ 9 = K9 at *
  generalize kerK * (Val.list [encGroup js, obBigRep D₁ lab]).wt ^ 9 = KT9 at *
  omega

/-- The mathematical postcondition of `obKernel_spec`. -/
def ObKernelOut (J : Subgroup (Perm (Fin n))) (w : Val) : Prop :=
  ∃ js' : List (Perm (Fin n)), w = encGroup js' ∧ js'.length ≤ n ^ 2 ∧
    gens js' ≤ J ∧ 2 * Nat.card (gens js') ≤ Nat.card J ∧
    (∀ g ∈ J, ∀ x ∈ gens js', g * x * g⁻¹ ∈ gens js') ∧
    (∃ (d : ℕ) (_ : d ≤ n) (ρ : J →* Perm (Fin d)),
      MulAction.IsPreprimitive ρ.range (Fin d) ∧
      ρ.ker ≤ (gens js').subgroupOf J)

theorem ObKernelOut.wt_le {J : Subgroup (Perm (Fin n))} {w : Val} (h : ObKernelOut J w) :
    w.wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨js', rfl, hl, -⟩ := h
  exact wt_encGroup_le_sq hl

/-- **Specification of `obKernelBody`.** -/
theorem obKernel_spec {hmb : MinimalBlocks} {hpre : Preimage} {hmem : Membership}
    {P : Program} {f rep lo dom mg cls ker jmb jpre jmem : ℕ}
    (hP : ObKernelAt P f rep lo dom mg cls ker jmb jpre jmem hmb hpre hmem)
    {js : List (Perm (Fin n))} (hl : js.length ≤ n ^ 2) (hJ : ∃ g ∈ gens js, g ≠ 1) :
    FunAll P f (.list [.nat n, encGroup js])
      (fun w c => ObKernelOut (gens js) w ∧ c ≤ obKernelCost hmb hpre hmem n) := by
  classical
  obtain ⟨g₀, hg₀, hne₀⟩ := hJ
  have hne : (Set.univ : Set (Fin n)).Nonempty := by
    have hgb : ∃ b : Fin n, g₀ b ≠ b := by
      by_contra! hall; exact hne₀ (Perm.ext hall)
    obtain ⟨b, -⟩ := hgb
    exact ⟨b, trivial⟩
  obtain ⟨D₁, -, ⟨a, -, hD₁_eq⟩, hmax, hlo'⟩ :=
    lo_spec hP.lo (Equiv.refl (Fin n)) (G := gens js) (D := Set.univ)
      (fun _ _ _ => by simp) hne (ob_groupFin_refl (gens js)).symm hl
  have hD₁ : Invariant (gens js) D₁ := hD₁_eq ▸ ob_invariant_orbit
  obtain ⟨hn1, hk2⟩ := ob_two_le_obBMk ⟨g₀, hg₀, hne₀⟩ hmax
  have htr := ob_restrK_trans hD₁ hD₁_eq
  refine FunAll.intro hP.entry ?_
  have s1 := obKernel_step1 hP.rep hl
  have s2 := obKernel_step2 hl hlo'
  have s3 := obKernel_step3 hP.dom D₁ js []
  have s4 := obKernel_step4 hP.dom D₁ hl
  have s5 := obKernel_step5 hP.dom D₁ hD₁ hl
  have s6 := obKernel_step6 hP.mg D₁ hD₁ hl
  have s7 := obKernel_step7 hmb hP.jmb_eq D₁ hD₁ hk2 htr hl
  have s8_10 : ∀ v7, BlocksOut (restrK (Equiv.refl (Fin n)) (gens js) D₁ hD₁).range v7 →
      EvalAll P ([.list [.nat n, encGroup js], indVal (Equiv.refl (Fin n)) Set.univ,
        indVal (Equiv.refl (Fin n)) D₁, natList (domNat (Equiv.refl (Fin n)) D₁),
        posVal (Equiv.refl (Fin n)) D₁, .list ((obHs (gens js) D₁ hD₁ js).map encPerm),
        encGroup (obHs (gens js) D₁ hD₁ js)] ++ [v7])
      (.letE (.call (dom + 18) (mk2 (.snoc (.var 7) (.length (.var 3))) (.var 4)))
      (.letE (.get (.call cls (mk2 (.var 8) (.var 2))) (.nat 2))
        (.call ker (mk2 (arg 1) (.var 9)))))
      (fun w c => ObKernelOut (gens js) w ∧
        c ≤ 10 ^ 10 * (n + 1) ^ 6 +
          (10 * clsK * (n + 1) ^ 6 +
            ((preimagePrim hpre).boundSize (10 ^ 4 * (n + 1) ^ 6) +
              reduceCost hmem n (320 * (n + 1) ^ 6) +
              kerK * (700 * (n + 1) ^ 6) ^ 9 + 10 ^ 10 * (n + 1) ^ 6) +
            320 * (n + 1) ^ 6 + 1) +
          320 * (n + 1) ^ 6 + 1) := by
    intro v7 hv7
    obtain ⟨lab, rfl, hlt, hmb_lab⟩ := hv7
    have s8 := obKernel_step8 hP.dom D₁ hD₁ hlt
    have s9 := obKernel_step9 hP.cls D₁ hD₁ hlt
    have s10 := obKernel_step10 hpre hmem hP.ker hP.jpre_eq hP.jmem_eq D₁ hD₁ hl hlt hmb_lab
    refine ob_letDet ObKernelOut.wt_le s8 (ob_letDet ObKernelOut.wt_le s9 ?_)
    refine s10.mono fun w c hw => ⟨?_, hw.2⟩
    obtain ⟨K, ⟨js', rfl, rfl, hl'⟩, hK⟩ := hw.1
    let eJ : gens js ≃* groupFin (Equiv.refl (Fin n)) (gens js) :=
      MulEquiv.subgroupCongr (ob_groupFin_refl (gens js)).symm
    let res : gens js →* Perm (Fin (obBMk D₁)) :=
      (restrK (Equiv.refl (Fin n)) (gens js) D₁ hD₁).comp eJ.toMonoidHom
    have hres_range : res.range = (restrK (Equiv.refl (Fin n)) (gens js) D₁ hD₁).range := by
      ext σ
      simp only [res, MonoidHom.mem_range, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact ⟨fun ⟨g, hg⟩ => ⟨eJ g, hg⟩, fun ⟨g, hg⟩ => ⟨eJ.symm g, by simp [hg]⟩⟩
    obtain ⟨d, hd, ρ, hprim, hker_iff, g₁, hg₁⟩ :=
      minBlocks_primitive_hom (obBMk_le D₁) res (hres_range ▸ htr) (hres_range ▸ hmb_lab)
    have hKJ : gens js' ≤ gens js := fun g hg => ((hK g).1 hg).1
    have hnorm : ∀ g ∈ gens js, ∀ x ∈ gens js', g * x * g⁻¹ ∈ gens js' := by
      intro g hg x hx
      obtain ⟨hxJ, hxL⟩ := (hK x).1 hx
      refine (hK (g * x * g⁻¹)).2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxJ)
        (Subgroup.inv_mem _ hg), fun i => ?_⟩
      simp only [Perm.mul_apply]
      have h1 := (obBM_pres D₁ lab hD₁ hlt hmb_lab g hg (x (g⁻¹ i)) (g⁻¹ i)).2 (hxL (g⁻¹ i))
      rwa [Perm.apply_inv_self] at h1
    have hker_eq : ∀ g : gens js, g ∈ ρ.ker ↔ g.1 ∈ gens js' := by
      intro g
      rw [hker_iff]
      change (∀ j : Fin (obBMk D₁),
        lab (restrK (Equiv.refl (Fin n)) (gens js) D₁ hD₁
          ⟨g.1, (ob_groupFin_refl (gens js)).symm ▸ g.2⟩ j) = lab j) ↔ g.1 ∈ gens js'
      rw [← obBM_fix_iff D₁ lab hD₁ g.2, hK g.1]
      exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
    have hlt_J : gens js' < gens js :=
      lt_of_le_of_ne hKJ fun heq => hg₁ ((hker_eq g₁).2 (by rw [heq]; exact g₁.2))
    refine ⟨js', rfl, hl', hKJ, GI.CitedChecks.two_mul_card_le_of_lt hlt_J, hnorm,
      d, hd, ρ, hprim, fun g hg => (hker_eq g).1 hg⟩
  refine (ob_letDet ObKernelOut.wt_le s1
    (ob_letDet ObKernelOut.wt_le s2
    (ob_letDet ObKernelOut.wt_le s3
    (ob_letDet ObKernelOut.wt_le s4
    (ob_letDet ObKernelOut.wt_le s5
    (ob_letDet ObKernelOut.wt_le s6
    (ob_letAll ObKernelOut.wt_le s7 s8_10))))))).mono fun w c h => ?_
  clear s1 s2 s3 s4 s5 s6 s7 s8_10 hlo'
  obtain ⟨hout, hc⟩ := h
  refine ⟨hout, ?_⟩
  have p321 : (n + 1) ^ 3 ≤ (n + 1) ^ 21 := Nat.pow_le_pow_right (by omega) (by omega)
  have p621 : (n + 1) ^ 6 ≤ (n + 1) ^ 21 := Nat.pow_le_pow_right (by omega) (by omega)
  have p921 : (n + 1) ^ 9 ≤ (n + 1) ^ 21 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1521 : (n + 1) ^ 15 ≤ (n + 1) ^ 21 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 21 := Nat.one_le_pow _ _ (by omega)
  unfold obKernelCost
  simp only [loK, domListK, posTabK, restrListK, mkGroupK, clsK] at hc
  generalize kerK * (700 * (n + 1) ^ 6) ^ 9 = K9 at *
  omega

/-! ### The loop step `obStepBody` and entry `obEntry` -/

/-- **Loop step of the orbit-block reduction** on
`[.list [encGroup us, encGroup ns], .nat i, encGroup js]`.
Forms `encGroup (ns ++ 1 :: js)` via `ap`, tests `gens us ≤ gens ns ⊔ gens js` via `le`,
and if true calls `obk` on `[.nat n, encGroup js]`. -/
def obStepBody (ap le obk : ℕ) : Expr :=
  .letE (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0))
    (.call ap (mk2 (.get (.get (arg 0) (.nat 1)) (.nat 1)) (.get (arg 2) (.nat 1)))))
  (.letE (.call le (mk2 (.var 1) (.get (arg 0) (.nat 0))))
    (.ite (.var 2)
      (.call obk (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (arg 2)))
      (arg 2)))

/-- **Entry of the orbit-block loop** on `[encGroup us, encGroup ns]`.
Runs `iterFuns` (`it`) of `obStepBody` for `n * n` steps starting from `arg 0` (`encGroup us`),
then forms `encGroup (ns ++ 1 :: js)` via `ap` and reduces its generators to `≤ n ^ 2`
via `reduceFuns` (`red`). -/
def obEntry (it ap red : ℕ) : Expr :=
  .letE (.call it (mk3 (.var 0)
    (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0)))
    (arg 0)))
  (.call red (mk2 (.get (arg 0) (.nat 0))
    (.call ap (mk2 (.get (arg 1) (.nat 1)) (.get (.var 1) (.nat 1))))))

/-- Where `obEntry`, `obStepBody`, and `obKernelBody` sit in the program. -/
structure ObAt (P : Program) (f it g ap le red obk rep lo dom mg cls ker jmb jpre jmem : ℕ)
    (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership) : Prop where
  entry : P.funs[f]? = some (obEntry it ap red)
  iter : P.HasAt it (iterFuns it g)
  step : P.funs[g]? = some (obStepBody ap le obk)
  ap : P.HasAt ap (appendFuns ap)
  le : P.HasAt le (leFuns le jmem)
  red : P.HasAt red (reduceFuns red jmem)
  obk : ObKernelAt P obk rep lo dom mg cls ker jmb jpre jmem hmb hpre hmem

/-- Loop invariant after `i` steps of `obStepBody`. -/
def ObLoopInv (U N : Subgroup (Perm (Fin n))) (i : ℕ) (acc : Val) : Prop :=
  ∃ js : List (Perm (Fin n)), acc = encGroup js ∧ js.length ≤ n ^ 2 ∧ gens js ≤ U ∧
    ((U ≤ N ⊔ gens js ∧ 2 ^ i * Nat.card (gens js) ≤ Nat.card U) ∨
      (¬ (U ≤ N ⊔ gens js) ∧
        (∀ g ∈ U, ∀ x ∈ N ⊔ gens js, g * x * g⁻¹ ∈ N ⊔ gens js) ∧
        ((N ⊔ gens js).subgroupOf U).index ≤
          max (Nat.factorial 24) (n ^ (1 + Nat.log 2 n)) * n ^ (1 + Nat.log 2 n)))

theorem ObLoopInv.wt_le {U N : Subgroup (Perm (Fin n))} {i : ℕ} {acc : Val}
    (h : ObLoopInv U N i acc) : acc.wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨js, rfl, hl, -⟩ := h
  exact wt_encGroup_le_sq hl

theorem ob_gens_ns_one_js (ns js : List (Perm (Fin n))) :
    gens (ns ++ 1 :: js) = gens ns ⊔ gens js := by
  rw [rad_gens_append, gens_cons_one]

theorem ob_union_det {P : Program} {ap : ℕ} (hap : P.HasAt ap (appendFuns ap))
    {env : List Val} {nE nsE jsE : Expr} {cn cns cjs : ℕ} {ns js : List (Perm (Fin n))}
    (dn : Det P env nE (.nat n) cn)
    (dns : Det P env nsE (.list ((1 :: ns).map encPerm)) cns)
    (djs : Det P env jsE (.list ((1 :: js).map encPerm)) cjs)
    (hl_ns : ns.length ≤ n ^ 2) (hl_js : js.length ≤ n ^ 2) :
    Det P env (mk2 nE (.call ap (mk2 nsE jsE))) (encGroup (ns ++ 1 :: js))
      (cn + cns + cjs + 10 ^ 8 * (n + 1) ^ 8) ∧
      (encGroup (ns ++ 1 :: js)).wt ≤ 4000 * (n + 1) ^ 6 := by
  have fap : FunDet P ap
      (.list [.list ((1 :: ns).map encPerm), .list ((1 :: js).map encPerm)])
      (.list (((1 :: ns).map encPerm) ++ ((1 :: js).map encPerm)))
      (loopModK * (((1 :: js).map encPerm).length + 1) *
        ((Val.list [.list ((1 :: ns).map encPerm), .list ((1 :: js).map encPerm)]).wt +
          ((1 :: js).map encPerm).length +
          (Val.list (((1 :: ns).map encPerm) ++ ((1 :: js).map encPerm))).wt + 1)) :=
    (append_spec hap ((1 :: ns).map encPerm) ((1 :: js).map encPerm)).mono
      fun w cost ⟨hw, hc⟩ => ⟨hw, by subst hw; exact hc⟩
  have da := Det.call (Det.mk2 dns djs) fap
  have d := Det.mk2 dn da
  have heq : Val.list [.nat n,
      .list (((1 :: ns).map encPerm) ++ ((1 :: js).map encPerm))] =
      encGroup (ns ++ 1 :: js) := by
    simp [encGroup, encPerms, List.map_append]
  rw [heq] at d
  have wns0 := wt_encGroup_le_sq hl_ns
  have wjs0 := wt_encGroup_le_sq hl_js
  have wns : (Val.list ((1 :: ns).map encPerm)).wt < (encGroup ns).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: ns).map encPerm)]) (by simp)
  have wjs : (Val.list ((1 :: js).map encPerm)).wt < (encGroup js).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: js).map encPerm)]) (by simp)
  have wap := rad_wt_append ((1 :: ns).map encPerm) ((1 :: js).map encPerm)
  have wn := wt_nat_le n
  have w2 := wt_list2_le (.list ((1 :: ns).map encPerm)) (.list ((1 :: js).map encPerm))
  have wout := wt_list2_le (.nat n)
    (.list (((1 :: ns).map encPerm) ++ ((1 :: js).map encPerm)))
  have eout : (encGroup (ns ++ 1 :: js)).wt =
      (Val.list [.nat n, .list (((1 :: ns).map encPerm) ++ ((1 :: js).map encPerm))]).wt := by
    rw [heq]
  have hlen : ((1 :: js).map encPerm).length + 1 ≤ 2 * (n + 1) ^ 2 := by
    simp only [List.length_map, List.length_cons]
    have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  have hlen' : ((1 :: js).map encPerm).length ≤ 2 * (n + 1) ^ 2 := by omega
  have p16 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hapc : loopModK * (((1 :: js).map encPerm).length + 1) *
      ((Val.list [.list ((1 :: ns).map encPerm), .list ((1 :: js).map encPerm)]).wt +
        ((1 :: js).map encPerm).length +
        (Val.list (((1 :: ns).map encPerm) ++ ((1 :: js).map encPerm))).wt + 1) ≤
      loopModK * (2 * (n + 1) ^ 2) * (5000 * (n + 1) ^ 6) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hlen) (by omega)
  have hapc' : loopModK * (2 * (n + 1) ^ 2) * (5000 * (n + 1) ^ 6) =
      10 ^ 7 * (n + 1) ^ 8 := by
    simp only [loopModK]; ring
  refine ⟨d.mono (by omega), by omega⟩

open Classical in
theorem ob_le_det (hmem : Membership) {P : Program} {le jm : ℕ}
    (hle : P.HasAt le (leFuns le jm)) (hjm : P.prims[jm]? = some (membershipPrim hmem))
    {env : List Val} {gE hE : Expr} {cg ch : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hG : GroupVal n gv G) (hs : List (Perm (Fin n)))
    (dg : Det P env gE gv cg) (dh : Det P env hE (encGroup hs) ch)
    (hwg : gv.wt ≤ 4000 * (n + 1) ^ 6) (hwh : (encGroup hs).wt ≤ 400 * (n + 1) ^ 6) :
    Det P env (.call le (mk2 gE hE)) (boolVal (decide (gens hs ≤ G)))
      (cg + ch + 10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) +
        10 ^ 17 * (n + 1) ^ 18) := by
  have d := Det.call (Det.mk2 dg dh) (le_spec hmem hle hjm hG hs)
  refine d.mono ?_
  have w2 := wt_list2_le gv (encGroup hs)
  have w1 := wt_encPerm_le (1 : Perm (Fin n))
  have w2' := wt_list2_le gv (encPerm (1 : Perm (Fin n)))
  have wb : (boolVal (decide (gens hs ≤ G))).wt ≤ 3 := by
    cases decide (gens hs ≤ G) <;> simp [boolVal, wt_nat, GI.Machine.len_zero]
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p618 : (n + 1) ^ 6 ≤ (n + 1) ^ 18 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hT : (Val.list [gv, encGroup hs]).wt ≤ 10 ^ 4 * (n + 1) ^ 6 := by omega
  have hsz : (Val.list [gv, encPerm (1 : Perm (Fin n))]).size ≤ 10 ^ 4 * (n + 1) ^ 6 :=
    (Val.size_le_wt _).trans (by omega)
  have hb := (membershipPrim hmem).bound_le hsz
  have hTb : (Val.list [gv, encGroup hs]).wt *
      (membershipPrim hmem).bound (.list [gv, encPerm (1 : Perm (Fin n))]) ≤
      10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) :=
    Nat.mul_le_mul hT hb
  have hT3 : 20000 * (Val.list [gv, encGroup hs]).wt ^ 3 ≤
      20000 * (10 ^ 4) ^ 3 * (n + 1) ^ 18 := by
    calc 20000 * (Val.list [gv, encGroup hs]).wt ^ 3 ≤
          20000 * (10 ^ 4 * (n + 1) ^ 6) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT 3)
      _ = 20000 * (10 ^ 4) ^ 3 * (n + 1) ^ 18 := by ring
  clear d dg dh hG
  generalize 10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) = MB at *
  generalize (Val.list [gv, encGroup hs]).wt *
      (membershipPrim hmem).bound (.list [gv, encPerm (1 : Perm (Fin n))]) = MB0 at *
  generalize 20000 * (Val.list [gv, encGroup hs]).wt ^ 3 = T3 at *
  omega

/-- Cost bound of a single `obStepBody` call. -/
noncomputable def obStepCost (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (n : ℕ) : ℕ :=
  obKernelCost hmb hpre hmem n +
    10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) +
    10 ^ 20 * (n + 1) ^ 18

/-- **Specification of `obStepBody`.** -/
theorem obStep_spec (hMa : MarotiPrimitive) {hmb : MinimalBlocks} {hpre : Preimage}
    {hmem : Membership} {P : Program}
    {f it g ap le red obk rep lo dom mg cls ker jmb jpre jmem : ℕ}
    (hP : ObAt P f it g ap le red obk rep lo dom mg cls ker jmb jpre jmem hmb hpre hmem)
    {H : Subgroup (Perm (Fin n))} {us ns : List (Perm (Fin n))} (hn1 : 1 ≤ n)
    (hUH : gens us ≤ H) (hNU : gens ns ≤ gens us) (hUN_not : ¬ (gens us ≤ gens ns))
    (hnN : ∀ g ∈ H, ∀ x ∈ gens ns, g * x * g⁻¹ ∈ gens ns)
    (htrN : MulAction.IsPretransitive (gens ns) (Fin n))
    (hl_us : us.length ≤ n ^ 2) (hl_ns : ns.length ≤ n ^ 2)
    (i : ℕ) {acc : Val} (hinv : ObLoopInv (gens us) (gens ns) i acc) :
    FunAll P g (.list [.list [encGroup us, encGroup ns], .nat i, acc])
      (fun w c => ObLoopInv (gens us) (gens ns) (i + 1) w ∧
        c ≤ obStepCost hmb hpre hmem n + 50 * (Val.nat i).wt) := by
  classical
  obtain ⟨js, rfl, hl_js, hJU, hbr⟩ := hinv
  set ctx := Val.list [encGroup us, encGroup ns]
  set inp := Val.list [ctx, .nat i, encGroup js]
  have wus := wt_encGroup_le_sq hl_us
  have wns := wt_encGroup_le_sq hl_ns
  have wjs := wt_encGroup_le_sq hl_js
  have wctx := wt_list2_le (encGroup us) (encGroup ns)
  have winp := wt_list3_le ctx (.nat i) (encGroup js)
  have wn := wt_nat_le n
  have p16 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have p68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have p818 : (n + 1) ^ 8 ≤ (n + 1) ^ 18 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  -- step 1: `v1 = encGroup (ns ++ 1 :: js)`
  have dctx0 := Det.arg' (P := P) (vs := [ctx, .nat i, encGroup js]) (rest := []) (j := 0) rfl
  have dus0 := Det.get' dctx0 (Det.nat 0) (v := encGroup us) rfl
  have dn0 := Det.get' dus0 (Det.nat 0) (v := .nat n)
    (show [Val.nat n, Val.list ((1 :: us).map encPerm)][0]? = some (.nat n) from rfl)
  have dns0 := Det.get' dctx0 (Det.nat 1) (v := encGroup ns) rfl
  have dnsL := Det.get' dns0 (Det.nat 1) (v := .list ((1 :: ns).map encPerm))
    (show [Val.nat n, Val.list ((1 :: ns).map encPerm)][1]? = some _ from rfl)
  have djs0 := Det.arg' (P := P) (vs := [ctx, .nat i, encGroup js]) (rest := []) (j := 2) rfl
  have djsL := Det.get' djs0 (Det.nat 1) (v := .list ((1 :: js).map encPerm))
    (show [Val.nat n, Val.list ((1 :: js).map encPerm)][1]? = some _ from rfl)
  obtain ⟨dv1, wv1⟩ := ob_union_det hP.ap dn0 dnsL djsL hl_ns hl_js
  -- step 2: `v2 = boolVal (decide (gens us ≤ gens (ns ++ 1 :: js)))`
  set v1 := encGroup (ns ++ 1 :: js)
  have ev1 : (encGroup (ns ++ 1 :: js)).wt = v1.wt := rfl
  have dctx1 := Det.arg' (P := P) (vs := [ctx, .nat i, encGroup js]) (rest := [v1]) (j := 0) rfl
  have dus1 := Det.get' dctx1 (Det.nat 0) (v := encGroup us) rfl
  have dv1_var := Det.var' (P := P) (env := [inp, v1]) (i := 1) (v := v1) rfl
  have dv2 := ob_le_det hmem hP.le hP.obk.jmem_eq ⟨ns ++ 1 :: js, rfl, rfl⟩ us dv1_var dus1
    (by omega) (by omega)
  -- step 3: `.ite (.var 2) ...`
  set b := decide (gens us ≤ gens (ns ++ 1 :: js))
  set env2 := [inp, v1, boolVal b]
  have dv2_var := Det.var' (P := P) (env := env2) (i := 2) (v := boolVal b) rfl
  have db_eq : boolVal b = .nat (if b then 1 else 0) := by cases b <;> rfl
  rw [db_eq] at dv2_var
  have hite : EvalAll P env2
      (.ite (.var 2)
        (.call obk (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (arg 2)))
        (arg 2))
      (fun w c => ObLoopInv (gens us) (gens ns) (i + 1) w ∧
        c ≤ obKernelCost hmb hpre hmem n + 2 * 10 ^ 6 * (n + 1) ^ 6 + 12 * (Val.nat i).wt) := by
    refine (sup_ite dv2_var
      (R := fun w ce => ObLoopInv (gens us) (gens ns) (i + 1) w ∧
        ce ≤ obKernelCost hmb hpre hmem n + 10 ^ 6 * (n + 1) ^ 6 + 10 * (Val.nat i).wt)
      (fun ht => ?_) (fun he => ?_)).mono fun w c h => ?_
    · -- branch `b = true`: `gens us ≤ gens ns ⊔ gens js`
      have hb_true : gens us ≤ gens ns ⊔ gens js := by
        rw [← ob_gens_ns_one_js]
        by_contra hnot
        simp [b, hnot] at ht
      have hcard_i : 2 ^ i * Nat.card (gens js) ≤ Nat.card (gens us) := by
        rcases hbr with ⟨-, hc⟩ | ⟨hnot, -⟩
        · exact hc
        · exact absurd hb_true hnot
      have hJ_ne : ∃ g ∈ gens js, g ≠ 1 := by
        by_contra! hall
        have hbot : gens js ≤ ⊥ := fun g hg => Subgroup.mem_bot.mpr (hall g hg)
        have hUN : gens us ≤ gens ns := by
          calc gens us ≤ gens ns ⊔ gens js := hb_true
            _ ≤ gens ns ⊔ ⊥ := sup_le_sup_left hbot _
            _ = gens ns := by simp
        exact hUN_not hUN
      have dctx2 := Det.arg' (P := P) (vs := [ctx, .nat i, encGroup js])
        (rest := [v1, boolVal b]) (j := 0) rfl
      have dus2 := Det.get' dctx2 (Det.nat 0) (v := encGroup us) rfl
      have dn2 := Det.get' dus2 (Det.nat 0) (v := .nat n)
        (show [Val.nat n, Val.list ((1 :: us).map encPerm)][0]? = some (.nat n) from rfl)
      have djs2 := Det.arg' (P := P) (vs := [ctx, .nat i, encGroup js])
        (rest := [v1, boolVal b]) (j := 2) rfl
      refine EvalAll.call_funAll (Det.mk2 dn2 djs2) fun v ca hv => ?_
      obtain ⟨rfl, hca⟩ := hv
      refine (obKernel_spec hP.obk hl_js hJ_ne).mono fun w cb hw => ⟨?_, ?_⟩
      · obtain ⟨js', rfl, hl_js', hJ'J, hcard_J', hnorm_J', d, hd, ρ, hprim, hker⟩ := hw.1
        have hU_eq : gens ns ⊔ gens js = gens us :=
          le_antisymm (sup_le hNU hJU) hb_true
        have hJH : gens js ≤ H := hJU.trans hUH
        have hNH : gens ns ≤ H := hNU.trans hUH
        have hnorm_sup : ∀ g ∈ gens us, ∀ x ∈ gens ns ⊔ gens js', g * x * g⁻¹ ∈ gens ns ⊔ gens js' := by
          rw [← hU_eq, sup_comm (gens ns) (gens js), sup_comm (gens ns) (gens js')]
          exact sup_normalized_of_normalized hJH hnN hnorm_J'
        have hind_sup : ((gens ns ⊔ gens js').subgroupOf (gens us)).index ≤
            max (Nat.factorial 24) (n ^ (1 + Nat.log 2 n)) * n ^ (1 + Nat.log 2 n) := by
          rw [← hU_eq, sup_comm (gens ns) (gens js), sup_comm (gens ns) (gens js')]
          exact orbitBlockStep_index_le hMa hn1 hNH hJH hnN hnorm_J' htrN hd ρ hprim hker
        refine ⟨js', rfl, hl_js', hJ'J.trans hJU, ?_⟩
        by_cases hle' : gens us ≤ gens ns ⊔ gens js'
        · left
          refine ⟨hle', ?_⟩
          calc 2 ^ (i + 1) * Nat.card (gens js') = 2 ^ i * (2 * Nat.card (gens js')) := by ring
            _ ≤ 2 ^ i * Nat.card (gens js) := Nat.mul_le_mul_left _ hcard_J'
            _ ≤ Nat.card (gens us) := hcard_i
        · right
          exact ⟨hle', hnorm_sup, hind_sup⟩
      · clear dctx2 dus2 dn2 djs2 dv2_var dv2 dv1_var dus1 dctx1 dv1 djsL djs0 dnsL dns0 dn0 dus0 dctx0
        have hc := hw.2
        have ww := hw.1.wt_le
        have w2 := wt_list2_le (.nat n) (encGroup js)
        have : (Val.list ((1 :: us).map encPerm)).wt < (encGroup us).wt :=
          wt_le_wt_list (vs := [.nat n, .list ((1 :: us).map encPerm)]) (by simp)
        have e_inp : (Val.list [ctx, .nat i, encGroup js]).wt = inp.wt := rfl
        have e_ctx : (Val.list [encGroup us, encGroup ns]).wt = ctx.wt := rfl
        clear_value ctx inp v1 b env2
        generalize obKernelCost hmb hpre hmem n = OBK at *
        omega
    · -- branch `b = false`: `¬ (gens us ≤ gens ns ⊔ gens js)`
      have hb_false : ¬ (gens us ≤ gens ns ⊔ gens js) := by
        rw [← ob_gens_ns_one_js]
        intro hle
        simp [b, hle] at he
      have hright : (∀ g ∈ gens us, ∀ x ∈ gens ns ⊔ gens js, g * x * g⁻¹ ∈ gens ns ⊔ gens js) ∧
          ((gens ns ⊔ gens js).subgroupOf (gens us)).index ≤
            max (Nat.factorial 24) (n ^ (1 + Nat.log 2 n)) * n ^ (1 + Nat.log 2 n) := by
        rcases hbr with ⟨hle, -⟩ | ⟨-, h1, h2⟩
        · exact absurd hle hb_false
        · exact ⟨h1, h2⟩
      have djs2 := Det.arg' (P := P) (vs := [ctx, .nat i, encGroup js])
        (rest := [v1, boolVal b]) (j := 2) rfl
      refine djs2.post fun c hc => ⟨⟨js, rfl, hl_js, hJU, Or.inr ⟨hb_false, hright.1, hright.2⟩⟩, ?_⟩
      clear djs2 dv2_var dv2 dv1_var dus1 dctx1 dv1 djsL djs0 dnsL dns0 dn0 dus0 dctx0
      have e_inp : (Val.list [ctx, .nat i, encGroup js]).wt = inp.wt := rfl
      have e_ctx : (Val.list [encGroup us, encGroup ns]).wt = ctx.wt := rfl
      clear_value ctx inp v1 b env2
      generalize obKernelCost hmb hpre hmem n = OBK at *
      omega
    · clear dv2_var dv2 dv1_var dus1 dctx1 dv1 djsL djs0 dnsL dns0 dn0 dus0 dctx0
      obtain ⟨ce, ⟨hinv', hce⟩, htot⟩ := h
      have hw_out := hinv'.wt_le
      have wb : (Val.nat (if b = true then 1 else 0)).wt ≤ 3 := by
        split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
      have e_inp : (Val.list [ctx, .nat i, encGroup js]).wt = inp.wt := rfl
      have e_ctx : (Val.list [encGroup us, encGroup ns]).wt = ctx.wt := rfl
      refine ⟨hinv', ?_⟩
      clear_value ctx inp v1 b env2
      generalize obKernelCost hmb hpre hmem n = OBK at *
      omega
  refine FunAll.intro hP.step
    ((ob_letDet ObLoopInv.wt_le dv1 (ob_letDet ObLoopInv.wt_le dv2 hite)).mono fun w c h => ?_)
  clear hite dv2_var dv2 dv1_var dus1 dctx1 dv1 djsL djs0 dnsL dns0 dn0 dus0 dctx0
  obtain ⟨hinv', htot⟩ := h
  have : (Val.list ((1 :: us).map encPerm)).wt < (encGroup us).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: us).map encPerm)]) (by simp)
  have : (Val.list ((1 :: ns).map encPerm)).wt < (encGroup ns).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: ns).map encPerm)]) (by simp)
  have : (Val.list ((1 :: js).map encPerm)).wt < (encGroup js).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: js).map encPerm)]) (by simp)
  have e_inp : (Val.list [ctx, .nat i, encGroup js]).wt = inp.wt := rfl
  have e_ctx : (Val.list [encGroup us, encGroup ns]).wt = ctx.wt := rfl
  refine ⟨hinv', ?_⟩
  unfold obStepCost
  clear_value ctx inp v1 b env2
  generalize obKernelCost hmb hpre hmem n = OBK at *
  generalize 10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) = MB at *
  omega

/-- Cost bound of `obEntry` on degree `n` with `≤ n ^ 2` generators. -/
noncomputable def obCost (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership) (n : ℕ) : ℕ :=
  (n + 1) ^ 2 * obStepCost hmb hpre hmem n +
    reduceCost hmem n (3 * (n + 1) ^ 2) +
    10 ^ 22 * (n + 1) ^ 20

/-- **Specification of `obEntry`.**
On `[encGroup us, encGroup ns]` where `N = gens ns < U = gens us ≤ H` (`1 ≤ n`, `H` normalizes `N`,
`N` transitive on `Fin n`), returns `encGroup ys` (`ys.length ≤ n ^ 2`) generating a proper
`U`-normalized subgroup `Y = gens ys` of `U` containing `N` with
`[U : Y] ≤ max (24!) (n ^ (1 + log₂ n)) * n ^ (1 + log₂ n)`. -/
theorem obEntry_spec (hMa : MarotiPrimitive) {hmb : MinimalBlocks} {hpre : Preimage}
    {hmem : Membership} {P : Program}
    {f it g ap le red obk rep lo dom mg cls ker jmb jpre jmem : ℕ}
    (hP : ObAt P f it g ap le red obk rep lo dom mg cls ker jmb jpre jmem hmb hpre hmem)
    {H : Subgroup (Perm (Fin n))} {us ns : List (Perm (Fin n))} (hn1 : 1 ≤ n)
    (hUH : gens us ≤ H) (hNU : gens ns ≤ gens us) (hUN_not : ¬ (gens us ≤ gens ns))
    (hnN : ∀ g ∈ H, ∀ x ∈ gens ns, g * x * g⁻¹ ∈ gens ns)
    (htrN : MulAction.IsPretransitive (gens ns) (Fin n))
    (hl_us : us.length ≤ n ^ 2) (hl_ns : ns.length ≤ n ^ 2) :
    FunAll P f (.list [encGroup us, encGroup ns])
      (fun w c =>
        (∃ ys : List (Perm (Fin n)), w = encGroup ys ∧ ys.length ≤ n ^ 2 ∧
          gens ns ≤ gens ys ∧ gens ys ≤ gens us ∧ ¬ (gens us ≤ gens ys) ∧
          (∀ g ∈ gens us, ∀ x ∈ gens ys, g * x * g⁻¹ ∈ gens ys) ∧
          ((gens ys).subgroupOf (gens us)).index ≤
            max (Nat.factorial 24) (n ^ (1 + Nat.log 2 n)) * n ^ (1 + Nat.log 2 n)) ∧
        c ≤ obCost hmb hpre hmem n) := by
  set c := Val.list [encGroup us, encGroup ns]
  set k := n * n
  have hk_eq : k = n ^ 2 := (sq n).symm
  have wus := wt_encGroup_le_sq hl_us
  have wns := wt_encGroup_le_sq hl_ns
  have wc := wt_list2_le (encGroup us) (encGroup ns)
  have wn := wt_nat_le n
  have wk := wt_nat_le k
  have hk2 : k ≤ (n + 1) ^ 2 := by
    have : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    omega
  have p12 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have p820 : (n + 1) ^ 8 ≤ (n + 1) ^ 20 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  -- initial invariant at `i = 0`
  have h0 : ObLoopInv (gens us) (gens ns) 0 (encGroup us) :=
    ⟨us, rfl, hl_us, le_rfl, Or.inl ⟨le_sup_right, by simp⟩⟩
  -- loop step bound
  set B := obStepCost hmb hpre hmem n + 150 * (n + 1) ^ 2
  have hstep : ∀ i acc, i < k → ObLoopInv (gens us) (gens ns) i acc →
      FunAll P g (.list [c, .nat i, acc])
        (fun w cost => ObLoopInv (gens us) (gens ns) (i + 1) w ∧ cost ≤ B) := by
    intro i acc hi hinv
    refine (obStep_spec hMa hP hn1 hUH hNU hUN_not hnN htrN hl_us hl_ns i hinv).mono
      fun w cost hw => ⟨hw.1, ?_⟩
    have wi := wt_nat_le i
    have := hw.2
    omega
  have hit := iter_spec hP.iter (c := c) (k := k) (M := 320 * (n + 1) ^ 6) h0
    (fun i acc _ hinv => hinv.wt_le) hstep
  -- argument of `it`
  have darg0 := Det.var' (P := P) (env := [c]) (i := 0) (v := c) rfl
  have dus0 := Det.get' darg0 (Det.nat 0) (v := encGroup us) rfl
  have dn0 := Det.get' dus0 (Det.nat 0) (v := .nat n)
    (show [Val.nat n, Val.list ((1 :: us).map encPerm)][0]? = some (.nat n) from rfl)
  have dk := Det.arith' (z := k) (op := .mul) dn0 dn0 rfl
  have darg := Det.mk3 darg0 dk dus0
  have wc3 := wt_list3_le c (.nat k) (encGroup us)
  refine FunAll.intro hP.entry
    (EvalAll.letE
      (Ra := fun v1 c1 => ObLoopInv (gens us) (gens ns) k v1 ∧
        c1 ≤ (n + 1) ^ 2 * obStepCost hmb hpre hmem n + 10 ^ 8 * (n + 1) ^ 8)
      (EvalAll.call_funAll darg fun v ca hv => ?_) fun v1 c1 hv1 => ?_)
  · obtain ⟨rfl, hca⟩ := hv
    refine hit.mono fun w cb hw => ⟨hw.1, ?_⟩
    clear darg dk dn0 dus0 darg0 hit hstep
    have hc := hw.2
    have ww := hw.1.wt_le
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have hkb : k * B ≤ (n + 1) ^ 2 * obStepCost hmb hpre hmem n + 150 * (n + 1) ^ 4 := by
      calc k * B ≤ (n + 1) ^ 2 * (obStepCost hmb hpre hmem n + 150 * (n + 1) ^ 2) :=
            Nat.mul_le_mul_right _ hk2
        _ = (n + 1) ^ 2 * obStepCost hmb hpre hmem n + 150 * (n + 1) ^ 4 := by ring
    have p48 : (n + 1) ^ 4 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have ec : (Val.list [encGroup us, encGroup ns]).wt = c.wt := rfl
    have hloop : loopModK * (k + 1) *
        ((Val.list [c, .nat k, encGroup us]).wt + k + 320 * (n + 1) ^ 6 + 1) ≤
        loopModK * (2 * (n + 1) ^ 2) * (10000 * (n + 1) ^ 6) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have hloop' : loopModK * (2 * (n + 1) ^ 2) * (10000 * (n + 1) ^ 6) =
        2 * 10 ^ 7 * (n + 1) ^ 8 := by simp only [loopModK]; ring
    have : (Val.list ((1 :: us).map encPerm)).wt < (encGroup us).wt :=
      wt_le_wt_list (vs := [.nat n, .list ((1 :: us).map encPerm)]) (by simp)
    clear_value c k B
    generalize (n + 1) ^ 2 * obStepCost hmb hpre hmem n = N2OBS at *
    omega
  obtain ⟨⟨js, rfl, hl_js, hJU, hbr⟩, hc1⟩ := hv1
  -- after `k = n ^ 2` steps, the left branch is impossible
  have hright : ¬ (gens us ≤ gens ns ⊔ gens js) ∧
      (∀ g ∈ gens us, ∀ x ∈ gens ns ⊔ gens js, g * x * g⁻¹ ∈ gens ns ⊔ gens js) ∧
      ((gens ns ⊔ gens js).subgroupOf (gens us)).index ≤
        max (Nat.factorial 24) (n ^ (1 + Nat.log 2 n)) * n ^ (1 + Nat.log 2 n) := by
    rcases hbr with ⟨_, hcard⟩ | hright
    · rw [hk_eq] at hcard
      exact absurd hcard (not_two_pow_sq_mul_card_le hn1 (gens js) (gens us))
    · exact hright
  -- build `encGroup (ns ++ 1 :: js)` and call `red`
  have dctx1 := Det.arg' (P := P) (vs := [encGroup us, encGroup ns])
    (rest := [encGroup js]) (j := 0) (v := encGroup us) rfl
  have dn1 := Det.get' dctx1 (Det.nat 0) (v := .nat n)
    (show [Val.nat n, Val.list ((1 :: us).map encPerm)][0]? = some (.nat n) from rfl)
  have dns1 := Det.arg' (P := P) (vs := [encGroup us, encGroup ns])
    (rest := [encGroup js]) (j := 1) (v := encGroup ns) rfl
  have dnsL := Det.get' dns1 (Det.nat 1) (v := .list ((1 :: ns).map encPerm))
    (show [Val.nat n, Val.list ((1 :: ns).map encPerm)][1]? = some _ from rfl)
  have djs1 := Det.var' (P := P) (env := [c, encGroup js]) (i := 1) (v := encGroup js) rfl
  have djsL := Det.get' djs1 (Det.nat 1) (v := .list ((1 :: js).map encPerm))
    (show [Val.nat n, Val.list ((1 :: js).map encPerm)][1]? = some _ from rfl)
  obtain ⟨du, wu⟩ := ob_union_det hP.ap dn1 dnsL djsL hl_ns hl_js
  have dred := Det.call du (reduce_spec hmem hP.red hP.obk.jmem_eq (ns ++ 1 :: js))
  refine dred.post fun c2 hc2 => ⟨?_, ?_⟩
  · refine ⟨keepList (ns ++ 1 :: js), rfl, length_keepList_le _, ?_⟩
    rw [gens_keepList, ob_gens_ns_one_js]
    exact ⟨le_sup_left, sup_le hNU hJU, hright.1, hright.2.1, hright.2.2⟩
  · clear dred du djsL djs1 dnsL dns1 dn1 dctx1 darg dk dn0 dus0 darg0 hit hstep
    have wjs := wt_encGroup_le_sq hl_js
    have wout := wt_encGroup_le_sq (length_keepList_le (ns ++ 1 :: js))
    have hlen_u : (ns ++ 1 :: js).length ≤ 3 * (n + 1) ^ 2 := by
      simp only [List.length_append, List.length_cons]
      have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega
    have hrc := reduceCost_mono hmem n hlen_u
    have ec : (Val.list [encGroup us, encGroup ns]).wt = c.wt := rfl
    have : (Val.list ((1 :: us).map encPerm)).wt < (encGroup us).wt :=
      wt_le_wt_list (vs := [.nat n, .list ((1 :: us).map encPerm)]) (by simp)
    have : (Val.list ((1 :: ns).map encPerm)).wt < (encGroup ns).wt :=
      wt_le_wt_list (vs := [.nat n, .list ((1 :: ns).map encPerm)]) (by simp)
    have : (Val.list ((1 :: js).map encPerm)).wt < (encGroup js).wt :=
      wt_le_wt_list (vs := [.nat n, .list ((1 :: js).map encPerm)]) (by simp)
    unfold obCost
    clear_value c k B
    generalize (n + 1) ^ 2 * obStepCost hmb hpre hmem n = N2OBS at *
    generalize reduceCost hmem n (3 * (n + 1) ^ 2) = RC at *
    generalize reduceCost hmem n (ns ++ 1 :: js).length = RC0 at *
    omega

end GI.Impl
