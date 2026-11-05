module

public import Workspace.Impl.NClMath

@[expose] public section

/-!
# The derived subgroup as a normal closure

For `G = ⟨S⟩`, the derived subgroup `[G, G]` is the normal closure in `G` of the commutators
`[a, b]` of generators `a, b ∈ S` (Luks 1993, DIMACS 11, item (3.12), p. 145). The reason: the
normal closure `C` of these commutators lies in `[G, G]`, which `G` normalizes. Conversely,
modulo `C` the generators commute with each other, so all of `G` is abelian modulo `C`; in
Lean this is two closure inductions with the identities
`[a, qr] = [a, q] · q [a, r] q⁻¹` and `[pr, q] = p [r, q] p⁻¹ · [p, q]` (`derived_eq_ncl`).

`derComms gs` is the list of the commutators `[a, b]` for `a, b ∈ 1 :: gs`, in the order the
program makes them.
-/

namespace GI.Impl

open GI.Cited Equiv
open scoped commutatorElement

variable {n : ℕ}

/-- The commutators of the generators, as a list. -/
def derComms (gs : List (Perm (Fin n))) : List (Perm (Fin n)) :=
  (1 :: gs).flatMap fun a => (1 :: gs).map fun b => ⁅a, b⁆

theorem mem_derComms {gs : List (Perm (Fin n))} {x : Perm (Fin n)} :
    x ∈ derComms gs ↔ ∃ a ∈ 1 :: gs, ∃ b ∈ 1 :: gs, ⁅a, b⁆ = x := by
  simp only [derComms, List.mem_flatMap, List.mem_map]

/-- The derived subgroup is normalized by `G`. -/
theorem derived_normal (G : Subgroup (Perm (Fin n))) :
    ∀ g ∈ G, ∀ x ∈ ⁅G, G⁆, g * x * g⁻¹ ∈ ⁅G, G⁆ := by
  intro g hg
  rw [Subgroup.commutator_def]
  refine ncl_conj_closure fun y hy => ?_
  obtain ⟨p, hp, q, hq, rfl⟩ := hy
  refine Subgroup.subset_closure ⟨g * p * g⁻¹, G.mul_mem (G.mul_mem hg hp) (G.inv_mem hg),
    g * q * g⁻¹, G.mul_mem (G.mul_mem hg hq) (G.inv_mem hg), ?_⟩
  simp only [commutatorElement_def]; group

/-- **The derived subgroup is the normal closure of the commutators of the generators.** -/
theorem derived_eq_ncl (gs : List (Perm (Fin n))) :
    ⁅gens gs, gens gs⁆ = nclTarget gs (derComms gs) := by
  set G := gens gs
  have hcG : ∀ x ∈ derComms gs, x ∈ ⁅G, G⁆ := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_derComms.mp hx
    have hmem : ∀ y ∈ 1 :: gs, y ∈ G := fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact G.one_mem
      · exact Subgroup.subset_closure hy
    exact Subgroup.commutator_mem_commutator (hmem a ha) (hmem b hb)
  have hgg : gens (gs ++ derComms gs) = G := by
    refine le_antisymm ((Subgroup.closure_le _).mpr fun y hy => ?_)
      (Subgroup.closure_mono fun y hy => List.mem_append_left _ hy)
    rcases List.mem_append.mp hy with hy | hy
    · exact Subgroup.subset_closure hy
    · exact Subgroup.commutator_le.mpr (fun p hp q hq => by
        rw [commutatorElement_def]
        exact G.mul_mem (G.mul_mem (G.mul_mem hp hq) (G.inv_mem hp)) (G.inv_mem hq)) (hcG y hy)
  set C := nclTarget gs (derComms gs)
  have hCn : ∀ g ∈ G, ∀ x ∈ C, g * x * g⁻¹ ∈ C := fun g hg =>
    nclTarget_normal gs (derComms gs) g (hgg ▸ hg)
  have hcC : ∀ x ∈ derComms gs, x ∈ C := fun x hx =>
    Subgroup.subset_closure ⟨1, Subgroup.one_mem _, x, hx, by group⟩
  refine le_antisymm ?_ ?_
  · -- `[G, G] ≤ C`
    -- first `[a, q] ∈ C` for a generator `a` and `q ∈ G`
    have h1 : ∀ a ∈ gs, ∀ q ∈ G, ⁅a, q⁆ ∈ C := by
      intro a ha q hq
      induction hq using Subgroup.closure_induction with
      | mem b hb => exact hcC _ (mem_derComms.mpr ⟨a, List.mem_cons_of_mem _ ha, b,
          List.mem_cons_of_mem _ hb, rfl⟩)
      | one => simp [C.one_mem]
      | mul q r hq hr ihq ihr =>
        have e : ⁅a, q * r⁆ = ⁅a, q⁆ * (q * ⁅a, r⁆ * q⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]; exact C.mul_mem ihq (hCn q hq _ ihr)
      | inv q hq ihq =>
        have e : ⁅a, q⁻¹⁆ = q⁻¹ * ⁅a, q⁆⁻¹ * q⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]; exact hCn q⁻¹ (G.inv_mem hq) _ (C.inv_mem ihq)
    -- then `[p, q] ∈ C` for `p, q ∈ G`
    have h2 : ∀ p ∈ G, ∀ q ∈ G, ⁅p, q⁆ ∈ C := by
      intro p hp q hq
      induction hp using Subgroup.closure_induction with
      | mem a ha => exact h1 a ha q hq
      | one => simp [C.one_mem]
      | mul p r hp hr ihp ihr =>
        have e : ⁅p * r, q⁆ = (p * ⁅r, q⁆ * p⁻¹) * ⁅p, q⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]; exact C.mul_mem (hCn p hp _ ihr) ihp
      | inv p hp ihp =>
        have e : ⁅p⁻¹, q⁆ = p⁻¹ * ⁅p, q⁆⁻¹ * p⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]; exact hCn p⁻¹ (G.inv_mem hp) _ (C.inv_mem ihp)
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro x ⟨p, hp, q, hq, rfl⟩
    exact h2 p hp q hq
  · -- `C ≤ [G, G]`
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨g, hg, y, hy, rfl⟩
    exact derived_normal G g (hgg ▸ hg) y (hcG y hy)

end GI.Impl
