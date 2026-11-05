module

public import Workspace.Proved.VsWFrameMath

@[expose] public section

/-!
# Local matrices and lifts

Fix a frame `cs = vsWComp p ws' ws` for `W' = span ws'` inside `W' ⊔ W` (`W = span ws`), and
write `D = |cs|` and `co x` for the local coordinates of `x` (`vsWCo`).

* `vsWLoc_co`: if a stored matrix `A` maps `W'` and `W' ⊔ W` into themselves, then its local
  matrix acts on local coordinates: `co (A x) = Loc.mulVec (co x)`.
* `vsWLift_span`: the lift of a local span `U` is `W' ⊔ (∑ a_j c_j for a ∈ U)`.
* `vsWLift_mem`: a vector `x ∈ W' ⊔ W` lies in the lift exactly when `co x ∈ U`.
-/

namespace GI.Proved

open GI.Impl

variable {p : ℕ}

/-- The local coordinates of `x`, as a vector. -/
noncomputable abbrev vsWCoV (p : ℕ) (ws' ws : List (List ℕ)) (x : List ℕ) :
    Fin (vsWComp p ws' ws).length → ZMod p :=
  vsWV p (vsWComp p ws' ws).length (vsWCo p ws' (vsWComp p ws' ws) x)

theorem vsWLoc_fit (hp : 0 < p) {d : ℕ} (ws' cs A : List (List ℕ)) :
    VsWSq p cs.length (vsWLoc p d ws' cs A) := by
  refine ⟨fun y hy => ?_, by simp [vsWLoc, vsWImg]⟩
  simp only [vsWLoc, List.mem_map] at hy
  obtain ⟨x, -, rfl⟩ := hy
  exact vsWCo_fit hp ws' cs x _ (List.mem_singleton_self _)

theorem vsWImg_one_fit (hp : 0 < p) {d : ℕ} {A : List (List ℕ)} (hA : VsWSq p d A) (u : List ℕ) :
    VsWFit p d [vsFRowMul p u A (vsWZ d)] := by
  intro y hy
  simp only [List.mem_singleton] at hy
  subst hy
  exact vsWImg_fit hp hA [u] _ (by simp [vsWImg])

/-- **Local matrices act on local coordinates.** -/
theorem vsWLoc_co (hp : p.Prime) {d : ℕ} {ws' ws A : List (List ℕ)} (h' : VsWFit p d ws')
    (h : VsWFit p d ws) (hA : VsWSq p d A)
    (hW' : ∀ v ∈ vsWSp p d ws', vsWLin p d A v ∈ vsWSp p d ws')
    (hW : ∀ v ∈ vsWSp p d ws' ⊔ vsWSp p d ws, vsWLin p d A v ∈ vsWSp p d ws' ⊔ vsWSp p d ws)
    {x : List ℕ} (hx : VsWFit p d [x]) (hxW : vsWV p d x ∈ vsWSp p d ws' ⊔ vsWSp p d ws) :
    vsWCoV p ws' ws (vsFRowMul p x A (vsWZ d)) =
      (vsWM p (vsWComp p ws' ws).length (vsWLoc p d ws' (vsWComp p ws' ws) A)).mulVec
        (vsWCoV p ws' ws x) := by
  have hc := vsWComp_fit hp.pos h' h
  have himg : ∀ u : List ℕ, vsWV p d (vsFRowMul p u A (vsWZ d)) = vsWLin p d A (vsWV p d u) :=
    vsWV_img hA.2 fun r hr => (hA.1 r hr).2.le
  set cs := vsWComp p ws' ws with hcs
  set a := vsWCoV p ws' ws x
  have hcW : ∀ j : Fin cs.length, vsWV p d cs[j] ∈ vsWSp p d ws' ⊔ vsWSp p d ws := by
    intro j
    rw [← vsWFrame_sup hp h' h]
    exact Submodule.mem_sup_right (vsWV_mem_vsWSp d (List.getElem_mem j.2))
  -- the local matrix applied to `a`
  have hLoc : (vsWLoc p d ws' cs A).length = cs.length := by simp [vsWLoc, vsWImg]
  have hb : (vsWM p cs.length (vsWLoc p d ws' cs A)).mulVec a =
      ∑ j : Fin cs.length, a j • vsWCoV p ws' ws (vsFRowMul p cs[j] A (vsWZ d)) := by
    have := vsWLin_apply (p := p) hLoc a
    rw [vsWLin, Matrix.toLin'_apply] at this
    rw [this, vsWComb_apply]
    refine Fintype.sum_equiv (finCongr hLoc) _ _ fun i => ?_
    simp only [finCongr_apply]
    congr 1
    simp only [vsWLoc, vsWImg, List.map_map, vsWCoV]
    exact congrArg _ (List.getElem_map ..)
  have s1 := vsWCo_sub hp h' h hx hxW
  have s2 := hW' _ s1
  have s3 : ∀ j : Fin cs.length, vsWV p d (vsFRowMul p cs[j] A (vsWZ d)) -
      vsWComb p d cs (vsWCoV p ws' ws (vsFRowMul p cs[j] A (vsWZ d))) ∈ vsWSp p d ws' := by
    intro j
    refine vsWCo_sub hp h' h (vsWImg_one_fit hp.pos hA _) ?_
    rw [himg]; exact hW _ (hcW j)
  have s5 : vsWV p d (vsFRowMul p x A (vsWZ d)) -
      vsWComb p d cs ((vsWM p cs.length (vsWLoc p d ws' cs A)).mulVec a) ∈ vsWSp p d ws' := by
    have hsum : ∑ j : Fin cs.length, a j • (vsWV p d (vsFRowMul p cs[j] A (vsWZ d)) -
        vsWComb p d cs (vsWCoV p ws' ws (vsFRowMul p cs[j] A (vsWZ d)))) ∈ vsWSp p d ws' :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (s3 j)
    have := Submodule.add_mem _ s2 hsum
    convert this using 1
    rw [hb, map_sub, himg, map_sum, vsWComb_apply, map_sum]
    simp only [map_smul, smul_sub, Finset.sum_sub_distrib, himg]
    abel
  have hxW' : vsWV p d (vsFRowMul p x A (vsWZ d)) ∈ vsWSp p d ws' ⊔ vsWSp p d ws := by
    rw [himg]; exact hW _ hxW
  exact vsWCo_unique hp h' h (vsWCo_sub hp h' h (vsWImg_one_fit hp.pos hA _) hxW') s5

/-! ### Lifts -/

/-- **The lift of a local span.** -/
theorem vsWLift_span {d : ℕ} {cs : List (List ℕ)} (hc : VsWFit p d cs) (ws' us : List (List ℕ)) :
    vsWSp p d (vsWLift p d ws' cs us) =
      vsWSp p d ws' ⊔ (vsWSp p cs.length us).map (vsWComb p d cs) := by
  rw [vsWLift, vsWSp_append]
  congr 1
  rw [vsWSp, vsWSp, Submodule.map_span]
  congr 1
  ext v
  simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]
  have key : ∀ a, vsWV p d (vsFRowMul p a cs (vsWZ d)) = vsWComb p d cs (vsWV p cs.length a) :=
    fun a => vsWV_rowMul d a cs fun r hr => (hc r hr).2.le
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨_, ⟨a, ha, rfl⟩, (key a).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨_, ⟨a, ha, rfl⟩, key a⟩

/-- **Membership in a lift.** -/
theorem vsWLift_mem (hp : p.Prime) {d : ℕ} {ws' ws : List (List ℕ)} (h' : VsWFit p d ws')
    (h : VsWFit p d ws) (us : List (List ℕ)) {x : List ℕ} (hx : VsWFit p d [x])
    (hxW : vsWV p d x ∈ vsWSp p d ws' ⊔ vsWSp p d ws) :
    vsWV p d x ∈ vsWSp p d (vsWLift p d ws' (vsWComp p ws' ws) us) ↔
      vsWCoV p ws' ws x ∈ vsWSp p (vsWComp p ws' ws).length us := by
  have hc := vsWComp_fit hp.pos h' h
  rw [vsWLift_span hc]
  have s1 := vsWCo_sub hp h' h hx hxW
  constructor
  · intro hm
    obtain ⟨w, hw, y, ⟨u, hu, rfl⟩, he⟩ := Submodule.mem_sup.mp hm
    have hu' : vsWV p d x - vsWComb p d (vsWComp p ws' ws) u ∈ vsWSp p d ws' := by
      rw [← he, add_sub_cancel_right]; exact hw
    have e := vsWCo_unique hp h' h s1 hu'
    change vsWV p (vsWComp p ws' ws).length (vsWCo p ws' (vsWComp p ws' ws) x) ∈ _
    rw [e]
    exact hu
  · intro hm
    have : vsWV p d x = (vsWV p d x - vsWComb p d (vsWComp p ws' ws) (vsWCoV p ws' ws x)) +
        vsWComb p d (vsWComp p ws' ws) (vsWCoV p ws' ws x) := by abel
    rw [this]
    exact Submodule.add_mem_sup s1 ⟨_, hm, rfl⟩

end GI.Proved
