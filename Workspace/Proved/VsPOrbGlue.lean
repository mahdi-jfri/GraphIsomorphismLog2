import Workspace.Proved.VsPOrbMath
import Workspace.Proved.VsPBridge
import Workspace.Proved.VsPCountMath

/-!
# The orbit list as an orbit set of local units

The orbit program runs on permutations with the program key `kf`. Its elements lie in the set
`vsPT hs N y` of conjugates `g y g⁻¹` (`g ∈ ⟨hs⟩`) whose local unit lies in `N`. This set is
closed under conjugation by `hs` (`vsPT_conj`), and its keys are few (`vsPT_card`). When the
list is closed up to keys, the local units of its elements form an orbit set of `ρ y`
(`vsP_orbHyp`).
-/

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv
open scoped commutatorElement

variable {I : VecStabInst} {s : VsQSt I} (hs : VsQStOK s)

/-- The conjugates of `y` (by `⟨hs⟩`) whose local unit lies in `N`. -/
def vsPT (N : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) (y : Perm (Fin I.n)) :
    Set (Perm (Fin I.n)) :=
  {z | (∃ g ∈ gens s.hs, z = g * y * g⁻¹) ∧ vsPRho hs z ∈ N}

variable {N : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ}

theorem vsPT_gens {y : Perm (Fin I.n)} (hy : y ∈ gens s.hs) {z : Perm (Fin I.n)}
    (hz : z ∈ vsPT hs N y) : z ∈ gens s.hs := by
  obtain ⟨⟨g, hg, rfl⟩, -⟩ := hz
  exact mul_mem (mul_mem hg hy) (inv_mem hg)

theorem vsPT_conj (hNn : ∀ h ∈ vsPRho hs '' {y | y ∈ s.hs}, ∀ x ∈ N, h * x * h⁻¹ ∈ N)
    {y : Perm (Fin I.n)} (hy : y ∈ gens s.hs) :
    ∀ h ∈ s.hs, ∀ z ∈ vsPT hs N y, h * z * h⁻¹ ∈ vsPT hs N y := by
  intro h hh z hz
  have hzg := vsPT_gens hs hy hz
  have hhg : h ∈ gens s.hs := Subgroup.subset_closure hh
  obtain ⟨⟨g, hg, rfl⟩, hzN⟩ := hz
  refine ⟨⟨h * g, mul_mem hhg hg, by group⟩, ?_⟩
  rw [vsPRho_conj hs hzg hhg]
  exact hNn _ ⟨h, hh, rfl⟩ _ hzN

variable [Fact I.p.Prime] {r : ℕ} [NeZero r] {c0 : Perm (Fin I.n)} {gs : List (Perm (Fin I.n))}

/-- The program key. -/
noncomputable abbrev vsPKf (s : VsQSt I) (c0 : Perm (Fin I.n)) (r : ℕ)
    (gs : List (Perm (Fin I.n))) : Perm (Fin I.n) → List ℕ :=
  vsPKey I s.ws' (vsQCs s) (vsPZp I s.ws' (vsQCs s) c0 r) gs

/-- **Few keys on the orbit set.** -/
theorem vsPT_card [Finite (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ]
    (hc0 : c0 ∈ gens s.hs) (hP : VsPPairHyp N r (vsPRho hs c0))
    (hgs : ∀ g ∈ gs, g ∈ gens s.hs) (hgN : ∀ g ∈ gs, vsPRho hs g ∈ N)
    {S : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ}
    (hk : VsPKeyHyp N S (vsPKV r (vsPRho hs c0) (gs.map (vsPRho hs)))) {y : Perm (Fin I.n)}
    (hy : y ∈ gens s.hs) [DecidablePred (· ∈ vsPT hs N y)] :
    ((Finset.univ.filter (· ∈ vsPT hs N y)).image (vsPKf s c0 r gs)).card ≤ S.relIndex N := by
  refine (vsP_card_keys_le (k := gs.length) (fun z hz => ?_) (Set.toFinite _)
    (X := vsPKV r (vsPRho hs c0) (gs.map (vsPRho hs)) '' N) fun z hz => ?_).trans hk.ncard_le
  · exact vsPKey_fit hs hc0 hP hgs hgN (vsPT_gens hs hy hz) hz.2
  · rw [vsF_vsPKey hs hc0 hP hgs hgN (vsPT_gens hs hy hz) hz.2]
    exact ⟨_, hz.2, rfl⟩

/-- **The orbit list gives an orbit set** of local units. -/
theorem vsP_orbHyp (hc0 : c0 ∈ gens s.hs) (hP : VsPPairHyp N r (vsPRho hs c0))
    (hgs : ∀ g ∈ gs, g ∈ gens s.hs) (hgN : ∀ g ∈ gs, vsPRho hs g ∈ N)
    (hNn : ∀ h ∈ vsPRho hs '' {y | y ∈ s.hs}, ∀ x ∈ N, h * x * h⁻¹ ∈ N)
    {y : Perm (Fin I.n)} (hy : y ∈ gens s.hs) {O : List (Perm (Fin I.n) × List ℕ)}
    (hinv : ∀ p ∈ O, p.2 = vsPKf s c0 r gs p.1 ∧ p.1 ∈ vsPT hs N y)
    (hmem : (y, vsPKf s c0 r gs y) ∈ O)
    (hcl : ∀ p ∈ O, ∀ h ∈ s.hs, ∃ q ∈ O, vsPKf s c0 r gs (h * p.1 * h⁻¹) = vsPKf s c0 r gs q.1) :
    VsPOrbHyp (vsPRho hs '' {y | y ∈ s.hs}) (vsPKV r (vsPRho hs c0) (gs.map (vsPRho hs)))
      (vsPRho hs y) (vsPRho hs '' {z | ∃ p ∈ O, p.1 = z}) := by
  refine ⟨?_, ⟨y, ⟨_, hmem, rfl⟩, rfl⟩, ?_⟩
  · rintro _ ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    obtain ⟨⟨g, hg, e⟩, -⟩ := (hinv p hp).2
    refine ⟨vsPRho hs g, ?_, ?_⟩
    · rw [← vsPBar_top_eq]; exact vsPRho_mem_vsPBar hs hg hg
    · rw [e, vsPRho_conj hs hy hg]
  · rintro _ ⟨z, ⟨p, hp, rfl⟩, rfl⟩ _ ⟨h, hh, rfl⟩
    obtain ⟨q, hq, e⟩ := hcl p hp h hh
    have hpT := (hinv p hp).2
    have hqT := (hinv q hq).2
    have hpg := vsPT_gens hs hy hpT
    have hhg : h ∈ gens s.hs := Subgroup.subset_closure hh
    have hcT := vsPT_conj hs hNn hy h hh p.1 hpT
    refine ⟨vsPRho hs q.1, ⟨q.1, ⟨q, hq, rfl⟩, rfl⟩, ?_⟩
    rw [← vsPRho_conj hs hpg hhg, ← vsF_vsPKey hs hc0 hP hgs hgN (vsPT_gens hs hy hcT) hcT.2,
      ← vsF_vsPKey hs hc0 hP hgs hgN (vsPT_gens hs hy hqT) hqT.2]
    exact congrArg (vsF r) e

end GI.Proved
