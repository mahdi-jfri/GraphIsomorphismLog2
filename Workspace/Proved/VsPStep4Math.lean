import Workspace.Proved.VsPN2Math
import Workspace.Proved.VsPOrbGlue
import Workspace.Proved.VsPRadMath
import Workspace.Proved.VsPEnumMath
import Workspace.Proved.VsPDerMath

/-!
# The hypotheses, the output, and the grow branches

* `VsPHyp`: what the spine's A-loop guarantees for step 4.
* `VsPGrowOut`: the grow output (`A` grows strictly, stays abelian and normal, `≤ n²` gens).
* `vsP_grow_out`: the normal closure of `as ++ xs` is a valid grow output when `xs` lies in a
  subgroup `Nx` normalized by `⟨hs⟩`, with abelian local image commuting with `Ā`, and some
  `x ∈ xs` has `Λ(x) ∉ S`.
-/

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv
open scoped commutatorElement

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime]

/-- The hypotheses of step 4. -/
structure VsPHyp (hs : VsQStOK s) (as : List (Perm (Fin I.n))) (Lb : List (List (List ℕ)))
    (ccs : List (Perm (Fin I.n))) : Prop where
  has : gens as ≤ gens s.hs
  hasn : VsPNormd (gens s.hs) (gens as)
  hal : as.length ≤ I.n ^ 2
  habl : vsPBar hs (gens as) ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _)
  hdom : vsTDom (vsTAlg (vsPBar hs (gens as)))
  hLb : ∀ M ∈ Lb, VsFSq I.p (vsQD s) M
  hspan : vsFMatSpan I.p (vsQD s) Lb = Subalgebra.toSubmodule
    (vsFAlgOf I.p (vsQD s) (as.map (vsPLocL I s.ws' (vsQCs s))))
  hLbl : Lb.length ≤ vsQD s * vsQD s
  hcc : gens ccs ≤ gens s.hs
  hccn : VsPNormd (gens s.hs) (gens ccs)
  hccl : ccs.length ≤ I.n ^ 2
  hccC : vsPBar hs (gens ccs) ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _)
  hnab : ¬ vsPBar hs (gens ccs) ≤ Subgroup.centralizer (vsPBar hs (gens ccs) : Set _)
  hsolv : IsSolvable (vsPBar hs (gens s.hs))

/-- The grow output. -/
structure VsPGrowOut (hs : VsQStOK s) (as as' : List (Perm (Fin I.n))) : Prop where
  le : gens as ≤ gens as'
  le' : gens as' ≤ gens s.hs
  normd : VsPNormd (gens s.hs) (gens as')
  abel : vsPBar hs (gens as') ≤ Subgroup.centralizer (vsPBar hs (gens as') : Set _)
  len : as'.length ≤ I.n ^ 2
  lt : vsTAlg (vsPBar hs (gens as)) < vsTAlg (vsPBar hs (gens as'))

/-- The perms whose local unit is a scalar. -/
noncomputable def vsPSp (hs : VsQStOK s) (as : List (Perm (Fin I.n))) : Subgroup (Perm (Fin I.n)) :=
  ((vsMScal (vsPBar hs (gens as))).comap (vsQRho hs)).map (gens s.hs).subtype

theorem vsPSp_iff (hs : VsQStOK s) (as : List (Perm (Fin I.n))) {g : Perm (Fin I.n)}
    (hg : g ∈ gens s.hs) : g ∈ vsPSp hs as ↔ vsPRho hs g ∈ vsMScal (vsPBar hs (gens as)) := by
  rw [vsPRho_of hs hg]
  unfold vsPSp
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨⟨g', hg'⟩, h1, rfl⟩; exact h1
  · intro h; exact ⟨⟨g, hg⟩, h, rfl⟩

/-- `Ā` is an abelian normal subgroup of `H̄`. -/
theorem VsPHyp.abNormal {hs : VsQStOK s} {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
    {ccs : List (Perm (Fin I.n))} (h : VsPHyp hs as Lb ccs) :
    VsTAbNormal (vsPBar hs (gens s.hs)) (vsPBar hs (gens as)) := by
  refine ⟨fun u hu => ?_, ⟨fun a ha g => ?_⟩, fun a ha b hb => ?_⟩
  · obtain ⟨x, hxK, hx, rfl⟩ := (vsPBar_mem_iff hs).1 hu
    exact vsPRho_mem_vsPBar hs hx hx
  · rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨x, hxK, hx, ex⟩ := (vsPBar_mem_iff hs).1 ha
    obtain ⟨y, -, hy, ey⟩ := (vsPBar_mem_iff hs).1 g.2
    have e : ((g * a * g⁻¹ : vsPBar hs (gens s.hs)) : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ)
        = vsPRho hs (y * x * y⁻¹) := by
      rw [vsPRho_conj hs hx hy, ex, ey]; rfl
    rw [e]
    exact vsPRho_mem_vsPBar hs (h.hasn y hy x hxK) (mul_mem (mul_mem hy hx) (inv_mem hy))
  · exact Subgroup.mem_centralizer_iff.1 (h.habl hb) a ha

/-- `vsPBar` is monotone. -/
theorem vsPBar_le (hs : VsQStOK s) {K K' : Subgroup (Perm (Fin I.n))} (h : K ≤ K') :
    vsPBar hs K ≤ vsPBar hs K' := by
  intro u hu
  obtain ⟨x, hxK, hx, rfl⟩ := (vsPBar_mem_iff hs).1 hu
  exact vsPRho_mem_vsPBar hs (h hxK) hx

/-- **A grow output** from the normal closure of `as ++ xs`. -/
theorem vsP_grow_out {hs : VsQStOK s} {as : List (Perm (Fin I.n))}
    {Lb : List (List (List ℕ))} {ccs : List (Perm (Fin I.n))} (h : VsPHyp hs as Lb ccs)
    {xs : List (Perm (Fin I.n))} {Nx : Subgroup (Perm (Fin I.n))} (hNx : Nx ≤ gens s.hs)
    (hNxn : VsPNormd (gens s.hs) Nx) (hxs : ∀ x ∈ xs, x ∈ Nx)
    (hNab : vsPBar hs Nx ≤ Subgroup.centralizer (vsPBar hs Nx : Set _))
    (hNC : vsPBar hs Nx ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _))
    {x : Perm (Fin I.n)} (hx : x ∈ xs) (hxS : vsPRho hs x ∉ vsMScal (vsPBar hs (gens as)))
    {as' : List (Perm (Fin I.n))} (hl : as'.length ≤ I.n ^ 2)
    (he : gens as' = Subgroup.closure {x | ∃ g ∈ gens s.hs ⊔ gens (as ++ xs), ∃ y ∈ as ++ xs,
      x = g * y * g⁻¹}) :
    VsPGrowOut hs as as' := by
  have hyH : gens (as ++ xs) ≤ gens s.hs := (Subgroup.closure_le _).2 fun y hy => by
    rcases List.mem_append.1 hy with hy | hy
    · exact h.has (Subgroup.subset_closure hy)
    · exact hNx (hxs y hy)
  have hncl : gens as' = vsPNcl (gens s.hs) (as ++ xs) := he
  have hle : gens as' ≤ gens s.hs := by
    rw [hncl]; exact vsPNcl_le hyH (fun g hg y hy => mul_mem (mul_mem hg hy) (inv_mem hg))
      fun y hy => hyH (Subgroup.subset_closure hy)
  have hsup : gens as' ≤ gens as ⊔ Nx := by
    rw [hncl]
    refine vsPNcl_le hyH (vsP_normd_sup h.hasn hNxn) fun y hy => ?_
    rcases List.mem_append.1 hy with hy | hy
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure hy)
    · exact Subgroup.mem_sup_right (hxs y hy)
  have hxg : x ∈ gens s.hs := hNx (hxs x hx)
  refine ⟨?_, hle, ?_, ?_, hl, ?_⟩
  · rw [hncl]; exact vsPNcl_ge
  · rw [hncl]; exact vsPNcl_normd hyH
  · exact vsP_grow_abel hs h.has hNx hsup h.habl hNab hNC
  · refine vsP_grow_lt hs (by rw [hncl]; exact vsPNcl_ge) hxg ?_ ?_
    · rw [hncl]; exact vsPNcl_mem (List.mem_append_right _ hx)
    · rw [← vsPRho_of hs hxg]; exact hxS

end GI.Proved
