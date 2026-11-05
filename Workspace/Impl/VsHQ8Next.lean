module

public import Workspace.Impl.VsHQ8Out

@[expose] public section

/-!
# Continuing after a `Q₈`

After a `Q₈` output `[2, us, ⟨ks⟩]` with `⟨ks⟩ = C_C(Ȳ)`, the step-4 hypotheses hold again with
`ccs` replaced by `ks` (`VsHHyp.q8_next`): the main point is that `C_C(Ȳ)` is normal in `H`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

set_option backward.isDefEq.respectTransparency false

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime] {hs : VsQStOK s}
  {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ys : List (Perm (Fin I.n))} {r : ℕ}

/-- **The step-4 hypotheses for the centralizer of `Ȳ`.** -/
theorem VsHHyp.q8_next {ccs : List (Perm (Fin I.n))} (hH : VsPHyp hs as Lb ccs)
    (h : VsHHyp hs as Lb ys r) {ks : List (Perm (Fin I.n))}
    (hks : ∀ g, g ∈ gens ks ↔ g ∈ gens ccs ∧
      vsHAlT s g ((vsHB s Lb r ys).map (vsHT s)) = (vsHB s Lb r ys).map (vsHT s))
    (hksl : ks.length ≤ I.n ^ 2)
    (hnab : ¬ vsPBar hs (gens ks) ≤ Subgroup.centralizer (vsPBar hs (gens ks) : Set _)) :
    VsPHyp hs as Lb ks := by
  set B := vsHB s Lb r ys
  have hB : ∀ b ∈ B, b ∈ gens s.hs := fun b hb => h.hys b (h.bas.1 b hb)
  have hYB := h.bas.2.1
  -- membership in `⟨ks⟩`: in `⟨ccs⟩` and centralizing `Ȳ`
  have hmem : ∀ g, g ∈ gens ks ↔ g ∈ gens ccs ∧
      vsPRho hs g ∈ Subgroup.centralizer (vsHY hs as ys : Set _) := by
    intro g
    rw [hks g]
    constructor
    · rintro ⟨hg, hf⟩
      refine ⟨hg, ?_⟩
      have := (vsHQ8_stab hs hB hH.hcc hH.hccC hg).1 hf
      rwa [hYB]
    · rintro ⟨hg, hc⟩
      refine ⟨hg, (vsHQ8_stab hs hB hH.hcc hH.hccC hg).2 ?_⟩
      rwa [← hYB]
  have hle : gens ks ≤ gens ccs := fun g hg => ((hmem g).1 hg).1
  have hYn := h.hard.2.2.2.2.1
  refine { hH with hcc := hle.trans hH.hcc, hccn := ?_, hccl := hksl, hccC := ?_, hnab := hnab }
  · intro g hg x hx
    obtain ⟨hxc, hxz⟩ := (hmem x).1 hx
    have hxs : x ∈ gens s.hs := hH.hcc hxc
    refine (hmem _).2 ⟨hH.hccn g hg x hxc, ?_⟩
    rw [vsPRho_conj hs hxs hg, Subgroup.mem_centralizer_iff]
    intro y hy
    have hgH : (vsPRho hs g)⁻¹ ∈ vsPBar hs (gens s.hs) :=
      inv_mem (vsPRho_mem_vsPBar hs hg hg)
    have hy' : (vsPRho hs g)⁻¹ * y * (vsPRho hs g)⁻¹⁻¹ ∈ vsHY hs as ys := hYn _ hgH y hy
    have hc := Subgroup.mem_centralizer_iff.1 hxz _ hy'
    calc y * (vsPRho hs g * vsPRho hs x * (vsPRho hs g)⁻¹)
        = vsPRho hs g * (((vsPRho hs g)⁻¹ * y * (vsPRho hs g)⁻¹⁻¹) * vsPRho hs x) * (vsPRho hs g)⁻¹ := by
          group
      _ = vsPRho hs g * (vsPRho hs x * ((vsPRho hs g)⁻¹ * y * (vsPRho hs g)⁻¹⁻¹)) * (vsPRho hs g)⁻¹ := by
          rw [hc]
      _ = vsPRho hs g * vsPRho hs x * (vsPRho hs g)⁻¹ * y := by group
  · intro u hu
    obtain ⟨x, hx, hxs, rfl⟩ := (vsPBar_mem_iff hs).1 hu
    exact hH.hccC (vsPRho_mem_vsPBar hs (hle hx) hxs)

end GI.Impl
