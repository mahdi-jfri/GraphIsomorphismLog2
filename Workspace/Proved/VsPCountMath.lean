module

public import Workspace.Proved.VsPSpinMath
public import Workspace.Proved.VStabLinMath

@[expose] public section

/-!
# Few keys

The key map is constant on the cosets of `S` in `N`, so it takes at most `|N : N ∩ S|` values
(`VsPKeyHyp.ncard_le`). A list of numbers below `r` is determined by its vector `vsF r`
(`vsP_vsF_inj`), so the same bound holds for the program keys (`vsP_card_keys_le`).
-/

namespace GI.Proved

open Equiv

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] {N S : Subgroup G} {κ : G → M}

/-- **The key takes at most `|N : N ∩ S|` values on `N`.** -/
theorem VsPKeyHyp.ncard_le [Finite G] (hk : VsPKeyHyp N S κ) : (κ '' N).ncard ≤ S.relIndex N := by
  have hwd : ∀ x y : N, QuotientGroup.leftRel (S.subgroupOf N) x y → κ x = κ y := by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hxy
    have hxyN : ((x⁻¹ * y : N) : G) ∈ N := (x⁻¹ * y).2
    have e : (y : G) = x * ((x⁻¹ * y : N) : G) := by simp
    rw [e, hk.mul _ x.2 _ hxyN, hk.zero _ hxyN hxy, add_zero]
  let g : N ⧸ S.subgroupOf N → M := Quotient.lift (fun x : N => κ x) hwd
  have hrange : Set.range g = κ '' N := by
    ext v
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨((⟨x, hx⟩ : N) : N ⧸ S.subgroupOf N), rfl⟩
  rw [← hrange, ← Nat.card_coe_set_eq]
  unfold Subgroup.relIndex Subgroup.index
  exact Finite.card_range_le g

/-- Lists of numbers below `r` of the same length with the same vector are equal. -/
theorem vsP_vsF_inj {r : ℕ} {x y : List ℕ} (hx : ∀ a ∈ x, a < r) (hy : ∀ a ∈ y, a < r)
    (hl : x.length = y.length) (h : vsF r x = vsF r y) : x = y := by
  refine List.ext_getElem hl fun i hi hi' => ?_
  have := congrFun h i
  rw [vsF_apply, vsF_apply, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi',
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hx _ (List.getElem_mem hi)),
    Nat.mod_eq_of_lt (hy _ (List.getElem_mem hi'))] at this
  exact this

/-- **Few program keys.** If the keys of a set `T` of permutations are lists below `r` of
length `k` whose vectors lie in a finite set `X`, then the finset of keys has at most `|X|`
elements. -/
theorem vsP_card_keys_le {n r k : ℕ} {T : Set (Perm (Fin n))} [DecidablePred (· ∈ T)]
    {kf : Perm (Fin n) → List ℕ} (hfit : ∀ z ∈ T, (∀ a ∈ kf z, a < r) ∧ (kf z).length = k)
    {X : Set (ℕ → ZMod r)} (hX : X.Finite) (hmap : ∀ z ∈ T, vsF r (kf z) ∈ X) :
    ((Finset.univ.filter (· ∈ T)).image kf).card ≤ X.ncard := by
  classical
  set K := (Finset.univ.filter (· ∈ T)).image kf
  have hinj : Set.InjOn (vsF r) (K : Set (List ℕ)) := by
    intro x hx y hy e
    simp only [K, Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
      Set.mem_setOf_eq] at hx hy
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact vsP_vsF_inj (hfit z hz).1 (hfit z' hz').1 (by rw [(hfit z hz).2, (hfit z' hz').2]) e
  rw [← Set.ncard_coe_finset, ← hinj.ncard_image]
  refine Set.ncard_le_ncard ?_ hX
  rintro _ ⟨x, hx, rfl⟩
  simp only [K, Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
    Set.mem_setOf_eq] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  exact hmap z hz

end GI.Proved
