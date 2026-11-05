module

public import Workspace.Lang.Lib.OrbitT

@[expose] public section

/-!
# Orbits under an action defined on a subgroup only

The orbit program `orbT_spec` needs an action of all of `Perm (Fin n)`. The group `H` acts on
subspaces and vectors through `φ`, which is defined on `G = ⟨gs⟩` only. We pass to the induced
action: `Perm (Fin n)` acts on `Perm (Fin n) → Option Y` by `(g · f) h = f (g⁻¹ h)`, and
`y ↦ F y`, `F y h = α(h⁻¹) y` for `h ∈ K` (else `none`), is `K`-equivariant and injective. The
key of `F y` is `0 :: keyY y`; other functions get keys starting with `1` (an injection by
countability).

* `VsQPAct K α`: `α` is an action of `K`.
* `vsQ_orbT_spec`: `orbT_spec` restated for `α`, with keys `0 :: keyY y`.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

variable {n : ℕ} {Y : Type}

/-- `α` restricted to `K` is an action. -/
structure VsQPAct (K : Subgroup (Perm (Fin n))) (α : Perm (Fin n) → Y → Y) : Prop where
  one : ∀ y, α 1 y = y
  mul : ∀ g ∈ K, ∀ h ∈ K, ∀ y, α (g * h) y = α g (α h y)

/-- The induced action by left translation. -/
def vsQIndAct : Perm (Fin n) → (Perm (Fin n) → Option Y) → (Perm (Fin n) → Option Y) :=
  fun g f h => f (g⁻¹ * h)

theorem vsQIndAct_isAct : IsAct (vsQIndAct (n := n) (Y := Y)) :=
  ⟨fun f => by funext h; simp [vsQIndAct], fun g h f => by
    funext k; simp [vsQIndAct, mul_inv_rev, mul_assoc]⟩

open Classical in
/-- The equivariant embedding. -/
noncomputable def vsQF (K : Subgroup (Perm (Fin n))) (α : Perm (Fin n) → Y → Y) (y : Y) :
    Perm (Fin n) → Option Y :=
  fun h => if h ∈ K then some (α h⁻¹ y) else none

variable {K : Subgroup (Perm (Fin n))} {α : Perm (Fin n) → Y → Y}

theorem vsQF_one (hα : VsQPAct K α) (y : Y) : vsQF K α y 1 = some y := by
  simp [vsQF, K.one_mem, hα.one]

theorem vsQF_injective (hα : VsQPAct K α) : Function.Injective (vsQF K α) := by
  intro y z h
  have := congrFun h 1
  rw [vsQF_one hα, vsQF_one hα] at this
  exact Option.some.inj this

theorem vsQF_act (hα : VsQPAct K α) {g : Perm (Fin n)} (hg : g ∈ K) (y : Y) :
    vsQIndAct g (vsQF K α y) = vsQF K α (α g y) := by
  funext h
  simp only [vsQIndAct, vsQF]
  by_cases hh : h ∈ K
  · have : g⁻¹ * h ∈ K := K.mul_mem (K.inv_mem hg) hh
    rw [if_pos this, if_pos hh, mul_inv_rev, inv_inv, hα.mul _ (K.inv_mem hh) _ hg]
  · have : g⁻¹ * h ∉ K := fun h' => hh (by simpa using K.mul_mem hg h')
    rw [if_neg this, if_neg hh]

open Classical in
/-- The key: `0 :: keyY y` on `F y`, `1 :: code` elsewhere. -/
noncomputable def vsQIndKey [Countable Y] (K : Subgroup (Perm (Fin n))) (α : Perm (Fin n) → Y → Y)
    (keyY : Y → List ℕ) (f : Perm (Fin n) → Option Y) : List ℕ :=
  if h : ∃ y, vsQF K α y = f then 0 :: keyY h.choose
  else [1, (Countable.exists_injective_nat (Perm (Fin n) → Option Y)).choose f]

theorem vsQIndKey_F [Countable Y] (hα : VsQPAct K α) (keyY : Y → List ℕ) (y : Y) :
    vsQIndKey K α keyY (vsQF K α y) = 0 :: keyY y := by
  have h : ∃ y', vsQF K α y' = vsQF K α y := ⟨y, rfl⟩
  rw [vsQIndKey, dif_pos h, vsQF_injective hα h.choose_spec]

theorem vsQIndKey_injective [Countable Y] (hα : VsQPAct K α) {keyY : Y → List ℕ}
    (hk : Function.Injective keyY) : Function.Injective (vsQIndKey K α keyY) := by
  intro f g hfg
  by_cases hf : ∃ y, vsQF K α y = f
  · obtain ⟨y, rfl⟩ := hf
    by_cases hg : ∃ y, vsQF K α y = g
    · obtain ⟨z, rfl⟩ := hg
      rw [vsQIndKey_F hα, vsQIndKey_F hα] at hfg
      rw [hk (List.cons.inj hfg).2]
    · rw [vsQIndKey_F hα, vsQIndKey, dif_neg hg] at hfg
      simp at hfg
  · by_cases hg : ∃ y, vsQF K α y = g
    · obtain ⟨z, rfl⟩ := hg
      rw [vsQIndKey_F hα, vsQIndKey, dif_neg hf] at hfg
      simp at hfg
    · rw [vsQIndKey, vsQIndKey, dif_neg hf, dif_neg hg] at hfg
      exact (Countable.exists_injective_nat _).choose_spec (List.cons.inj (List.cons.inj hfg).2).1

/-- The orbit of `y₀` under `⟨gs⟩` through `α`. -/
def vsQOrb (α : Perm (Fin n) → Y → Y) (gs : List (Perm (Fin n))) (y₀ : Y) : Set Y :=
  {y | ∃ g ∈ genGroup gs, α g y₀ = y}

theorem vsQ_actOrbit (hα : VsQPAct K α) {gs : List (Perm (Fin n))} (hK : genGroup gs ≤ K)
    (y₀ : Y) : actOrbit vsQIndAct gs (vsQF K α y₀) = vsQF K α '' vsQOrb α gs y₀ := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨α g y₀, ⟨g, hg, rfl⟩, (vsQF_act hα (hK hg) y₀).symm⟩
  · rintro ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, vsQF_act hα (hK hg) y₀⟩

/-- The encoding of the pairs of an orbit. -/
def vsQPairs (keyY : Y → List ℕ) (L : List (Y × Perm (Fin n))) : Val :=
  .list (L.map fun q => .list [natList (0 :: keyY q.1), encPerm q.2])

set_option maxHeartbeats 1000000 in
/-- **Orbits with a transversal for an action of a subgroup.** -/
theorem vsQ_orbT_spec [Countable Y] {P : Program} {b fa : ℕ} (h : P.HasAt b (orbTFuns b fa))
    (hα : VsQPAct K α) {gs : List (Perm (Fin n))} (hK : genGroup gs ≤ K) {keyY : Y → List ℕ}
    (hk : Function.Injective keyY) {y₀ : Y} {ac : Val} {S A B : ℕ}
    (hn : n + 1 ≤ S) (hm : gs.length + 1 ≤ S) (hac : ac.wt ≤ S)
    (hkey : ∀ y ∈ vsQOrb α gs y₀, (natList (0 :: keyY y)).wt ≤ S)
    (hfa : ∀ g ∈ gs, ∀ y ∈ vsQOrb α gs y₀,
      FunDet P fa (.list [ac, encPerm g, natList (0 :: keyY y)]) (natList (0 :: keyY (α g y))) A)
    (hBS : B + 1 ≤ S) (hB : (vsQOrb α gs y₀).ncard ≤ B) :
    FunAll P b (.list [ac, .list (gs.map encPerm), natList (0 :: keyY y₀), .nat B, .nat n])
      (fun w cost => ∃ L : List (Y × Perm (Fin n)), w = vsQPairs keyY L ∧
        (L.map Prod.fst).Nodup ∧ (∀ y, y ∈ L.map Prod.fst ↔ y ∈ vsQOrb α gs y₀) ∧
        (∀ p ∈ L, p.2 ∈ genGroup gs ∧ α p.2 y₀ = p.1) ∧ L.head? = some (y₀, 1) ∧
        cost ≤ S ^ 2 * A + orbTK * S ^ 6) := by
  classical
  have horb := vsQ_actOrbit hα hK y₀
  have key0 := vsQIndKey_F hα keyY y₀
  have H : OrbTHyp P fa (vsQIndKey K α keyY) vsQIndAct gs (vsQF K α y₀) ac S A := by
    refine ⟨vsQIndAct_isAct, vsQIndKey_injective hα hk, hn, hm, hac, ?_, ?_⟩
    · intro f hf
      rw [horb] at hf
      obtain ⟨y, hy, rfl⟩ := hf
      rw [vsQIndKey_F hα]; exact hkey y hy
    · intro g hg f hf
      rw [horb] at hf
      obtain ⟨y, hy, rfl⟩ := hf
      have hgK : g ∈ K := hK (Subgroup.subset_closure hg)
      rw [vsQF_act hα hgK, vsQIndKey_F hα, vsQIndKey_F hα]
      exact hfa g hg y hy
  have hB' : (actOrbit vsQIndAct gs (vsQF K α y₀)).ncard ≤ B := by
    rw [horb, Set.ncard_image_of_injective _ (vsQF_injective hα)]; exact hB
  have hs := orbT_spec h H hBS hB'
  rw [key0] at hs
  refine hs.mono fun w cost hw => ?_
  obtain ⟨L', rfl, hnd, hmem, hpr, hhd, hc⟩ := hw
  -- every point of `L'` is `F` of the image of `y₀`
  have hpt : ∀ p ∈ L', p.1 = vsQF K α (α p.2 y₀) := by
    intro p hp
    rw [← (hpr p hp).2, vsQF_act hα (hK (hpr p hp).1)]
  set L := L'.map fun p => (α p.2 y₀, p.2) with hL
  have hL' : L' = L.map fun q => (vsQF K α q.1, q.2) := by
    rw [hL, List.map_map]
    conv_lhs => rw [← List.map_id L']
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply, id]
    rw [← hpt p hp]
  refine ⟨L, ?_, ?_, ?_, ?_, ?_, hc⟩
  · rw [hL']
    simp only [encPairs, encPair, vsQPairs, List.map_map, Function.comp_def, vsQIndKey_F hα]
  · rw [hL', List.map_map] at hnd
    have : (L.map Prod.fst).map (vsQF K α) = L.map ((fun q => q.1) ∘ fun q => (vsQF K α q.1, q.2)) := by
      simp [List.map_map, Function.comp_def]
    rw [← this] at hnd
    exact List.Nodup.of_map _ hnd
  · intro y
    have := hmem (vsQF K α y)
    rw [horb, (vsQF_injective hα).mem_set_image, hL', List.map_map] at this
    rw [← this]
    simp only [List.mem_map, Function.comp_apply]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, he⟩; exact ⟨q, hq, vsQF_injective hα he⟩
  · intro q hq
    rw [hL, List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact ⟨(hpr p hp).1, rfl⟩
  · rw [hL, List.head?_map, hhd]
    simp [hα.one]

end GI.Impl
