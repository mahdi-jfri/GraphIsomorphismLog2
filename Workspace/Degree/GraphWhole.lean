module

public import Workspace.Degree.GraphLev

/-!
# Whole graphs

Section 9.4 of the paper.

* `swPerm`: the map `sw(τ)`.
* `eq_autGroup`: Lemma 9.5. The proof here goes through the vertices in order, so it needs only
  the facts about `sw(τ)` and the fixers that the program gives. It replaces the count of moved
  components in the paper's proof.
* `exchange`, `PartIso`, `PartIso.extend`, `Agree`, `Agree.extend`: Lemma 9.6, with the invariant
  "an isomorphism agrees with `P`".
-/

@[expose] public section

namespace GI.Degree

open Equiv GI.Statement

variable {n : ℕ} {X Y : SimpleGraph (Fin n)} {v w : Fin n} {τ g : Perm (Fin n)}

theorem IsRooted.comp {Z : SimpleGraph (Fin n)} {z : Fin n} {h : Perm (Fin n)}
    (hg : IsRooted X v Y w g) (hh : IsRooted Y w Z z h) : IsRooted X v Z z (h * g) := by
  refine ⟨by simp [Perm.mul_apply, hg.root, hh.root], fun a b ha => ?_⟩
  rw [hg.adj a b ha, Perm.mul_apply, Perm.mul_apply]
  exact hh.adj _ _ (hg.reach ha)

/-- A graph isomorphism is rooted at each vertex. -/
theorem isRooted_of_iso (hg : ∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b)) (v : Fin n) :
    IsRooted X v Y (g v) g :=
  ⟨rfl, fun a b _ => hg a b⟩

theorem isRooted_of_aut (hg : g ∈ autGroup X) (v : Fin n) : IsRooted X v X (g v) g :=
  isRooted_of_iso (fun a b => (hg a b).symm) v

theorem IsRooted.reach_iff' (hτ : IsRooted X v X w τ) {a : Fin n} (h : X.Reachable v w) :
    X.Reachable v (τ a) ↔ X.Reachable v a := by
  rw [← hτ.reach_iff (a := a)]
  exact ⟨fun h1 => h.symm.trans h1, fun h1 => h.trans h1⟩

open Classical in
/-- `τ` on the component of `v`, `τ⁻¹` on the rest of the component of `w`, the identity elsewhere. -/
noncomputable def swMap (X : SimpleGraph (Fin n)) (v w : Fin n) (τ : Perm (Fin n)) (u : Fin n) :
    Fin n :=
  if X.Reachable v u then τ u else if X.Reachable w u then τ⁻¹ u else u

theorem swMap_left (hτ : IsRooted X v X w τ) (u : Fin n) :
    swMap X w v τ⁻¹ (swMap X v w τ u) = u := by
  by_cases h1 : X.Reachable v u
  · have h2 := hτ.reach h1
    simp [swMap, h1, h2]
  by_cases h2 : X.Reachable w u
  · have h3 : X.Reachable v (τ⁻¹ u) := hτ.inv.reach h2
    have h4 : ¬X.Reachable w (τ⁻¹ u) := fun h => h1 (h3.trans (h.symm.trans h2))
    have e1 : swMap X v w τ u = τ⁻¹ u := by
      unfold swMap
      rw [if_neg h1, if_pos h2]
    rw [e1]
    unfold swMap
    rw [if_neg h4, if_pos h3, inv_inv]
    simp
  · simp [swMap, h1, h2]

/-- The map `sw(τ)`. -/
noncomputable def swPerm (hτ : IsRooted X v X w τ) : Perm (Fin n) where
  toFun := swMap X v w τ
  invFun := swMap X w v τ⁻¹
  left_inv := swMap_left hτ
  right_inv u := by
    have := swMap_left hτ.inv u
    rwa [inv_inv] at this

theorem swPerm_apply (hτ : IsRooted X v X w τ) (u : Fin n) :
    swPerm hτ u = swMap X v w τ u := rfl

theorem swMap_adj (hτ : IsRooted X v X w τ) {a b : Fin n} (h : X.Adj a b) :
    X.Adj (swMap X v w τ a) (swMap X v w τ b) := by
  by_cases h1 : X.Reachable v a
  · have h2 : X.Reachable v b := h1.trans h.reachable
    simp only [swMap, h1, h2, if_true]
    exact (hτ.adj a b h1).1 h
  have h2 : ¬X.Reachable v b := fun h3 => h1 (h3.trans h.symm.reachable)
  by_cases h3 : X.Reachable w a
  · have h4 : X.Reachable w b := h3.trans h.reachable
    simp only [swMap, h1, h2, h3, h4, if_true, if_false]
    exact (hτ.inv.adj a b h3).1 h
  · have h4 : ¬X.Reachable w b := fun h5 => h3 (h5.trans h.symm.reachable)
    simp only [swMap, h1, h2, h3, h4, if_false]
    exact h

theorem swPerm_mem (hτ : IsRooted X v X w τ) : swPerm hτ ∈ autGroup X := fun a b => by
  refine ⟨fun h => ?_, swMap_adj hτ⟩
  have h1 := swMap_adj hτ.inv h
  rwa [swPerm_apply, swPerm_apply, swMap_left hτ, swMap_left hτ] at h1

theorem swPerm_root (hτ : IsRooted X v X w τ) : swPerm hτ v = w := by
  simp [swPerm_apply, swMap, hτ.root]

theorem swPerm_fix (hτ : IsRooted X v X w τ) {u : Fin n} (h1 : ¬X.Reachable v u)
    (h2 : ¬X.Reachable w u) : swPerm hτ u = u := by
  simp [swPerm_apply, swMap, h1, h2]

/-! ### Lemma 9.5 -/

/-- **Lemma 9.5.** Let `H` be a group of automorphisms of `X` that holds, for all `v` and all images
`w` of `v` under automorphisms, an element that maps `v` to `w` and fixes the other components, and
that holds the group `A_{n-1}` of each `v`. Then `H` is the group of all automorphisms. -/
theorem eq_autGroup {H : Subgroup (Perm (Fin n))} (hH : H ≤ autGroup X)
    (h2 : ∀ v w, (∃ g ∈ autGroup X, g v = w) → ∃ s ∈ H, s v = w ∧
      ∀ u, ¬X.Reachable v u → ¬X.Reachable w u → s u = u)
    (h3 : ∀ v, ballGroup (lev X v) (n - 1) X ≤ H) : H = autGroup X := by
  refine le_antisymm hH fun g hg => ?_
  suffices key : ∀ d k, k + d = n → ∀ g ∈ autGroup X,
      (∀ i : Fin n, (i : ℕ) < k → ∀ u, X.Reachable i u → g u = u) → g ∈ H from
    key n 0 (by omega) g hg (fun i hi => absurd hi (by omega))
  intro d
  induction d with
  | zero =>
    intro k hk g _ hi
    have : g = 1 := Equiv.ext fun u => hi u (by omega) u (SimpleGraph.Reachable.refl _)
    rw [this]
    exact H.one_mem
  | succ d ih =>
    intro k hk g hg hi
    have hkn : k < n := by omega
    set v : Fin n := ⟨k, hkn⟩ with hv
    by_cases hc : ∃ i : Fin n, (i : ℕ) < k ∧ X.Reachable i v
    · obtain ⟨i, hik, hiv⟩ := hc
      refine ih (k + 1) (by omega) g hg fun j hj u hu => ?_
      by_cases hjk : (j : ℕ) < k
      · exact hi j hjk u hu
      · have : j = v := Fin.ext (by simp [hv]; omega)
        subst this
        exact hi i hik u (hiv.trans hu)
    · obtain ⟨s, hsH, hsv, hsf⟩ := h2 v (g v) ⟨g, hg, rfl⟩
      have hsA : s ∈ autGroup X := hH hsH
      have hsfix : ∀ i : Fin n, (i : ℕ) < k → ∀ u, X.Reachable i u → s u = u := by
        intro i hik u hu
        refine hsf u (fun h => hc ⟨i, hik, hu.trans h.symm⟩) fun h => ?_
        have h1 : X.Reachable i (g v) := hu.trans h.symm
        have h2 := hi i hik _ h1
        have h3 : g v = v := g.injective h2
        rw [h3] at h1
        exact hc ⟨i, hik, h1⟩
      set g1 := s⁻¹ * g with hg1
      have hg1A : g1 ∈ autGroup X := (autGroup X).mul_mem ((autGroup X).inv_mem hsA) hg
      have hg1v : g1 v = v := by
        rw [hg1, Perm.mul_apply, ← hsv]
        simp
      have hr : IsRooted X v X v g1 := by
        have := isRooted_of_aut hg1A v
        rwa [hg1v] at this
      set f := ballCut (lev X v) (n - 1) g1 hr.lev_eq with hf
      have hfm : f ∈ ballGroup (lev X v) (n - 1) X := ball_of_rooted_cut hr
      have hfH : f ∈ H := h3 v hfm
      have hfA : f ∈ autGroup X := hH hfH
      set g2 := f⁻¹ * g1 with hg2
      have hg2A : g2 ∈ autGroup X := (autGroup X).mul_mem ((autGroup X).inv_mem hfA) hg1A
      have hn : 0 < n := v.pos
      have hg2H : g2 ∈ H := by
        refine ih (k + 1) (by omega) g2 hg2A fun j hj u hu => ?_
        by_cases hjk : (j : ℕ) < k
        · have e1 : g u = u := hi j hjk u hu
          have e2 : s u = u := hsfix j hjk u hu
          have e3 : g1 u = u := by
            rw [hg1, Perm.mul_apply, e1, Perm.inv_eq_iff_eq, e2]
          have e4 : ¬X.Reachable v u := fun h => hc ⟨j, hjk, hu.trans h.symm⟩
          have e5 : f u = u := ballCut_apply_of_lt hr.lev_eq (by
            rw [lev_of_not_reach e4]; omega)
          rw [hg2, Perm.mul_apply, e3, Perm.inv_eq_iff_eq, e5]
        · have : j = v := Fin.ext (by simp [hv]; omega)
          subst this
          have e1 : f u = g1 u := ballCut_apply_of_le hr.lev_eq (by
            have := lev_lt_iff.2 hu
            omega)
          rw [hg2, Perm.mul_apply, ← e1]
          simp
      have e : g = s * f * g2 := by
        rw [hg2, hg1]
        group
      rw [e]
      exact H.mul_mem (H.mul_mem hsH hfH) hg2H

/-! ### Lemma 9.6 -/

/-- **The exchange.** If `X, Y` are isomorphic by `g` and `τ` is a rooted map from `v` to `w`, then
some isomorphism is `τ` on the component of `v`, and is `g` on the points whose image lies outside
the components of `g v` and `w`. -/
theorem exchange {τ : Perm (Fin n)} (hg : ∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b))
    (hτ : IsRooted X v Y w τ) : ∃ g' : Perm (Fin n), (∀ a b, X.Adj a b ↔ Y.Adj (g' a) (g' b)) ∧
      (∀ u, X.Reachable v u → g' u = τ u) ∧
      ∀ u, ¬Y.Reachable (g v) (g u) → ¬Y.Reachable w (g u) → g' u = g u := by
  have h1 : IsRooted X v Y (g v) g := isRooted_of_iso hg v
  have h2 : IsRooted Y (g v) Y w (τ * g⁻¹) := h1.inv.comp hτ
  refine ⟨swPerm h2 * g, fun a b => ?_, fun u hu => ?_, fun u h3 h4 => ?_⟩
  · rw [hg, Perm.mul_apply, Perm.mul_apply]
    exact (swPerm_mem h2 _ _).symm
  · have h3 : Y.Reachable (g v) (g u) := h1.reach hu
    simp [Perm.mul_apply, swPerm_apply, swMap, h3]
  · rw [Perm.mul_apply, swPerm_fix h2 h3 h4]

/-- A partial isomorphism, with domain and image unions of components. -/
structure PartIso (X Y : SimpleGraph (Fin n)) (p : Fin n → Option (Fin n)) : Prop where
  dom : ∀ u u' a, p u = some a → X.Reachable u u' → ∃ a', p u' = some a'
  im : ∀ u a b, p u = some a → Y.Reachable a b → ∃ u', p u' = some b
  inj : ∀ u u' a, p u = some a → p u' = some a → u = u'
  adj : ∀ u u' a a', p u = some a → p u' = some a' → (X.Adj u u' ↔ Y.Adj a a')

theorem partIso_none : PartIso X Y fun _ => none :=
  ⟨by simp, by simp, by simp, by simp⟩

open Classical in
/-- Add `τ` on the component of `v`. -/
noncomputable def addComp (X : SimpleGraph (Fin n)) (p : Fin n → Option (Fin n)) (v : Fin n)
    (τ : Perm (Fin n)) (u : Fin n) : Option (Fin n) :=
  if X.Reachable v u then some (τ u) else p u

theorem addComp_new {p : Fin n → Option (Fin n)} {u : Fin n} (h : X.Reachable v u) :
    addComp X p v τ u = some (τ u) := by
  simp [addComp, h]

theorem addComp_old {p : Fin n → Option (Fin n)} {u : Fin n} (h : ¬X.Reachable v u) :
    addComp X p v τ u = p u := by
  simp [addComp, h]

variable {p : Fin n → Option (Fin n)}

/-- A vertex of the image of a new component would put `w` in the image. -/
theorem PartIso.not_old (hp : PartIso X Y p) (hw : ∀ u, p u ≠ some w)
    (hτ : IsRooted X v Y w τ) {u u' : Fin n} {a : Fin n} (hu : X.Reachable v u)
    (h1 : p u' = some a) (h2 : Y.Reachable a (τ u)) : False := by
  obtain ⟨z, hz⟩ := hp.im u' a w h1 (h2.trans (hτ.reach hu).symm)
  exact hw z hz

/-- A point of the old domain is not in the new component. -/
theorem PartIso.not_new (hp : PartIso X Y p) (hv : p v = none) {u : Fin n} {a : Fin n}
    (h1 : p u = some a) : ¬X.Reachable v u := fun h => by
  obtain ⟨a', ha⟩ := hp.dom u v a h1 h.symm
  rw [hv] at ha
  cases ha

/-- **Adding a component.** -/
theorem PartIso.extend (hp : PartIso X Y p) (hv : p v = none) (hw : ∀ u, p u ≠ some w)
    (hτ : IsRooted X v Y w τ) : PartIso X Y (addComp X p v τ) := by
  refine ⟨fun u u' a h1 h2 => ?_, fun u a b h1 h2 => ?_, fun u u' a h1 h2 => ?_,
    fun u u' a a' h1 h2 => ?_⟩
  · by_cases hu : X.Reachable v u
    · exact ⟨_, addComp_new (hu.trans h2)⟩
    · rw [addComp_old hu] at h1
      obtain ⟨a', ha⟩ := hp.dom u u' a h1 h2
      rw [addComp_old (hp.not_new hv ha)]
      exact ⟨a', ha⟩
  · by_cases hu : X.Reachable v u
    · rw [addComp_new hu] at h1
      cases h1
      have h3 : Y.Reachable w b := (hτ.reach hu).trans h2
      have h4 : X.Reachable v (τ⁻¹ b) := hτ.inv.reach h3
      exact ⟨τ⁻¹ b, by rw [addComp_new h4]; simp⟩
    · rw [addComp_old hu] at h1
      obtain ⟨u', hu'⟩ := hp.im u a b h1 h2
      exact ⟨u', by rw [addComp_old (hp.not_new hv hu')]; exact hu'⟩
  · by_cases hu : X.Reachable v u <;> by_cases hu' : X.Reachable v u'
    · rw [addComp_new hu] at h1
      rw [addComp_new hu'] at h2
      cases h1
      exact τ.injective (Option.some.inj h2).symm
    · rw [addComp_new hu] at h1
      rw [addComp_old hu'] at h2
      cases h1
      exact (hp.not_old hw hτ hu h2 (SimpleGraph.Reachable.refl _)).elim
    · rw [addComp_old hu] at h1
      rw [addComp_new hu'] at h2
      cases h2
      exact (hp.not_old hw hτ hu' h1 (SimpleGraph.Reachable.refl _)).elim
    · rw [addComp_old hu] at h1
      rw [addComp_old hu'] at h2
      exact hp.inj u u' a h1 h2
  · have mixed : ∀ {u u' a'}, X.Reachable v u → ¬X.Reachable v u' → p u' = some a' →
        (X.Adj u u' ↔ Y.Adj (τ u) a') := by
      intro u u' a' hu hu' h2
      constructor
      · intro h
        exact absurd (hu.trans h.reachable) hu'
      · intro h
        exact (hp.not_old hw hτ hu h2 h.symm.reachable).elim
    by_cases hu : X.Reachable v u <;> by_cases hu' : X.Reachable v u'
    · rw [addComp_new hu] at h1
      rw [addComp_new hu'] at h2
      cases h1
      cases h2
      exact hτ.adj u u' hu
    · rw [addComp_new hu] at h1
      rw [addComp_old hu'] at h2
      cases h1
      exact mixed hu hu' h2
    · rw [addComp_old hu] at h1
      rw [addComp_new hu'] at h2
      cases h2
      rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm Y]
      exact mixed hu' hu h1
    · rw [addComp_old hu] at h1
      rw [addComp_old hu'] at h2
      exact hp.adj u u' a a' h1 h2

/-- The isomorphism `g` agrees with `p`. -/
def Agree (p : Fin n → Option (Fin n)) (g : Perm (Fin n)) : Prop :=
  ∀ u a, p u = some a → g u = a

/-- The image of `v` is free, if `v` is not in the domain. -/
theorem Agree.free (ha : Agree p g) (hv : p v = none) (u : Fin n) : p u ≠ some (g v) := fun h => by
  have h1 := g.injective (ha u _ h)
  rw [h1, hv] at h
  cases h

/-- **Lemma 9.6, one step.** -/
theorem Agree.extend (hp : PartIso X Y p) (ha : Agree p g)
    (hg : ∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b)) (hv : p v = none) (hw : ∀ u, p u ≠ some w)
    (hτ : IsRooted X v Y w τ) : ∃ g' : Perm (Fin n), (∀ a b, X.Adj a b ↔ Y.Adj (g' a) (g' b)) ∧
      Agree (addComp X p v τ) g' := by
  obtain ⟨g', h1, h2, h3⟩ := exchange hg hτ
  refine ⟨g', h1, fun u a h => ?_⟩
  by_cases hu : X.Reachable v u
  · rw [addComp_new hu] at h
    cases h
    exact h2 u hu
  · rw [addComp_old hu] at h
    have e : g u = a := ha u a h
    rw [h3 u ?_ ?_, e]
    · intro hr
      obtain ⟨z, hz⟩ := hp.im u (g u) (g v) (by rw [e]; exact h) hr.symm
      exact ha.free hv z hz
    · intro hr
      obtain ⟨z, hz⟩ := hp.im u (g u) w (by rw [e]; exact h) hr.symm
      exact hw z hz

/-- A total partial isomorphism is an isomorphism. -/
theorem PartIso.total (hp : PartIso X Y p) {t : Fin n → Fin n} (ht : ∀ u, p u = some (t u)) :
    ∃ σ : X ≃g Y, ∀ i, σ i = t i := by
  have hinj : Function.Injective t := fun a b h => hp.inj a b (t a) (ht a) (by rw [h]; exact ht b)
  let e : Fin n ≃ Fin n := Equiv.ofBijective t (Finite.injective_iff_bijective.1 hinj)
  exact ⟨⟨e, fun {a b} => (hp.adj a b _ _ (ht a) (ht b)).symm⟩, fun _ => rfl⟩

end GI.Degree
