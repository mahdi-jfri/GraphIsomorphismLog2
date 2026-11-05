module

public import Workspace.Impl.TermGlueLabNS5
public import Workspace.Impl.TermGlueLabPGenM

@[expose] public section

/-!
# The label driver: the facts step 5 needs for each generator of `S`

Proof of Theorem A.23, step 5. The per-generator program of step 5
(`tmGLPGen_spec`) needs, for each generator `g` of the supplement `S ≤ D ⊓ R`:

* `g ∈ Aut_H(T)`, since `S ≤ D` (the stabilizer of the types);
* lifts of `g` and `g⁻¹` to blockwise elements of `G|_dom` (`rowLift_spec`, as `g ∈ H`);
* for every lift `y` of `h⁻¹` (with `h = g` or `h = g⁻¹`), `h y_i ∈ N` for every row `i`: two
  lifts differ by a zero-sum tuple (`tmGLN_hyk`), and the lift `rowLift` has rows of class
  `h⁻¹` (`tmGLP_lift_memN`);
* `g` and `g⁻¹` normalize `N` (`N` is normal in `H`).
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Lang GI.Paper Equiv
open GI.Cited (Val encPerm encGroup gens)

attribute [local instance] stringRAct

variable {Ω C : Type} {Pp : Params} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}
  (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
  (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
  (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
    (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
  (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
  (hqα : (S.N : ℝ) ^ Pp.α < L.q)

local notation "𝕀" => tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα
set_option quotPrecheck false in
local notation "𝕩" => @id (Fin L.q → Fin m → C) (rowTuple (𝕀).e S.x)
set_option quotPrecheck false in
local notation "ℕb" => @id (Subgroup (Perm (Fin m))) (𝕀).Nb
set_option quotPrecheck false in
local notation "ℍb" => @id (Subgroup (Perm (Fin m))) (𝕀).Hb

/-- **The facts of one generator of `S`**, in the form of the hypotheses `hD`, `hs`, `hyN`,
`hs1`, `hs2` of `tmGLPGen_spec`. -/
theorem tmGLN_gen_hyps {σN gs : List (Perm (Fin m))} (hσN : gens σN = (𝕀).Nb)
    (hgs : gens gs ≤ Aut ℍb (types ℕb (𝕩))) {g : Perm (Fin m)} (hg : g ∈ gs) :
    g ∈ Aut ℍb (types (gens σN) (fun i => tmRowStr S E (.inl i))) ∧
    (∀ h, h = g ∨ h = g⁻¹ → ∃ y : Fin L.q → Perm (Fin m),
      cleanRowPerm E y ∈ S.domGroup ∧ y ⟨0, by omega⟩ = h) ∧
    (∀ h, h = g ∨ h = g⁻¹ → ∀ y : Fin L.q → Perm (Fin m), cleanRowPerm E y ∈ S.domGroup →
      y ⟨0, by omega⟩ = h⁻¹ → ∀ i, h * y i ∈ gens σN) ∧
    (∀ a ∈ σN, g * a * g⁻¹ ∈ gens σN) ∧ (∀ a ∈ σN, g⁻¹ * a * g ∈ gens σN) := by
  have hgD : g ∈ Aut ℍb (types ℕb (𝕩)) := hgs (Subgroup.subset_closure hg)
  have hgH : g ∈ (𝕀).Hb := (mem_aut.mp hgD).1
  have hH : ∀ h, h = g ∨ h = g⁻¹ → h ∈ (𝕀).Hb := by
    rintro h (rfl | rfl)
    · exact hgH
    · exact (𝕀).Hb.inv_mem hgH
  have hσ : ∀ a ∈ σN, a ∈ (𝕀).Nb := fun a ha => hσN ▸ Subgroup.subset_closure ha
  refine ⟨by rw [hσN]; exact hgD, fun h hh => ⟨_, rowLift_spec (𝕀).e (𝕀).i0 (hH h hh)⟩,
    fun h hh y hy hy0 i => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨ν, hν, hyν⟩ := tmGLN_hyk hnat hq h0 E hP htr hcard hsN hN hqα h⁻¹
      ((𝕀).Hb.inv_mem (hH h hh)) y hy hy0
    rw [hσN]
    exact tmGLP_lift_memN (tmGL_liftI 𝕀) (hH h hh) hν hyν i
  · rw [hσN]; exact (𝕀).normalizes g hgH a (hσ a ha)
  · rw [hσN]; exact (𝕀).normalizes.inv hgH (hσ a ha)

end GI.Impl
