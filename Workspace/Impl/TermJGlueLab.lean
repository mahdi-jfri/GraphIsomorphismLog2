module

public import Workspace.Impl.TermJGlueAut

@[expose] public section

/-!
# Glue of the `J`-step: one label

For a label `h` of the row terminal, the per-label program `tmJH_spec` needs three facts about the
row terminal, stated there for the permutations on `Fin n`:

* `hx`: the constant pair `(h; 1)` factors in `⟨G|_dom⟩ ⟨N^q⟩` (`tmJH_const_fac`);
* `hmatch`: there is a perfect matching of local tests (`tmJ_local_match`);
* `hcorr`: for every possible lift `g` and local transporter `z`, the pair `z⁻¹ g` has all
  coordinates in `N`, the zero-sum equation is solvable, and an odd top needs a transposition
  (`tmJ_u_mem`, `tmJH_exists`, `tmJH_odd_ne`).

`tmJ_label_hyps` proves them, and `tmJ_label_out` reads the program's output as an element of the
piece in the class of `h` (`tmJH_corr`). Both are stated for any numbering `e'` of the pairs.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Paper Equiv Equiv.Perm
open GI.Cited (gens)

variable {Ω C : Type}

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

variable [Nonempty I.B] {n : ℕ} (e' : I.B × Fin L.q ≃ Fin n) {gsG gsNq : List (Perm (Fin n))}
  (hG : gens gsG = (tmJG I).map (toFin e').toMonoidHom)
  (hNq : ∀ σ, σ ∈ gens gsNq ↔ ∃ d : Fin L.q → Perm I.B, (∀ i, d i ∈ I.Nb) ∧ σ = toFin e' (tmJP (d, 1)))
  (Ac : Fin L.q × Fin L.q → Set (Perm I.B)) (hAc : ∀ ij, Ac ij = (I.cosetCall ij).answer)
  {lg : List (Fin L.q × Perm I.B)}
  (hlg : ∀ k : Fin lg.length,
    (lg.get k).2 ∈ tmJRowAut I.Nb (rowTuple I.e S.x (lg.get k).1))
  {Tl : List (Fin L.q × Fin L.q × Perm I.B)}
  (hTl : ∀ t ∈ Tl, t.1 ≠ t.2.1 ∧ t.2.2 ∈ I.Nb ∧
    rowTuple I.e S.x t.1 ∘ t.2.2 = rowTuple I.e S.x t.2.1)
  (hAut : tmJW I.Nb ⊓ tmJStab (tmJStr (rowTuple I.e S.x)) ≤
    Subgroup.closure (tmJHLocs lg ∪ tmJHSws Tl))

include hG in
theorem tmJ_lift_pull {g : Perm (Fin n)} (hg : g ∈ gens gsG) : (toFin e').symm g ∈ tmJG I := by
  rw [hG] at hg
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hg
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact hσ

include hNq in
theorem tmJ_nq_pull {w : Perm (Fin n)} (hw : w ∈ gens gsNq) :
    (toFin e').symm w ∈ tmJW I.Nb := by
  obtain ⟨d, hd, rfl⟩ := (hNq w).1 hw
  rw [MulEquiv.symm_apply_apply]
  exact ⟨(d, 1), hd, rfl⟩

theorem tmJ_fac_pull {h : Perm I.B} {g w : Perm (Fin n)}
    (hf : toFin e' (tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q)))) = g * w) :
    tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q))) =
      (toFin e').symm g * (toFin e').symm w := by
  rw [← map_mul, ← hf, MulEquiv.symm_apply_apply]

include hAc in
theorem tmJ_z_pull {h : Perm I.B} {d' : Fin L.q → Perm I.B} {π' : Perm (Fin L.q)}
    (hd' : ∀ a, d' a ∈ Ac (a, π' a) ∧ h⁻¹ * d' a ∈ I.Nb) :
    tmJStr (rowTuple I.e S.y) ∘ tmJP (d', π') = tmJStr (rowTuple I.e S.x) ∧
      tmJP (d', π') ∈ tmJCls I.Nb h := by
  refine ⟨(tmJ_mem_iso _ _ (d', π')).2 fun a => ?_, ⟨(d', π'), rfl, fun a => (hd' a).2⟩⟩
  have := (hd' a).1
  rw [hAc] at this
  exact ((tmJ_coset_answer I _ _ _).1 this).2

include hG hNq hAc hlg hTl hAut in
/-- **The three facts of the row terminal for one label.** -/
theorem tmJ_label_hyps {r h : Perm I.B} (hr : r ∈ I.Hb) (hL : h ∈ tmGlLab I r) :
    (∃ g ∈ gens gsG, ∃ w ∈ gens gsNq,
      toFin e' (tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q)))) = g * w) ∧
    (∃ π : Perm (Fin L.q), ∀ a, ∃ u ∈ Ac (a, π a), h⁻¹ * u ∈ I.Nb) ∧
    (∀ g, g ∈ gens gsG → (∃ w ∈ gens gsNq,
        toFin e' (tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q)))) = g * w) →
      ∀ (d' : Fin L.q → Perm I.B) (π' : Perm (Fin L.q)),
        (∀ a, d' a ∈ Ac (a, π' a) ∧ h⁻¹ * d' a ∈ I.Nb) →
      ∃ (d : Fin L.q → Perm I.B) (π : Perm (Fin L.q)), (∀ i, d i ∈ I.Nb) ∧
        (toFin e' (tmJP (d', π')))⁻¹ * g = toFin e' (tmJP (d, π)) ∧
        (∃ c : Fin lg.length → ℤ, tmJSumT I.Nb I.φ lg c = tmJLab I.Nb I.φ d) ∧
        (sign π = -1 → Tl ≠ [])) := by
  have hhH : h ∈ I.Hb := tmJ_lab_le I hL
  have hlgN : ∀ k : Fin lg.length, (lg.get k).2 ∈ I.Nb := fun k => (hlg k).1
  have hTl' : ∀ t ∈ Tl, t.1 ≠ t.2.1 ∧ t.2.2 ∈ I.Nb := fun t ht => ⟨(hTl t ht).1, (hTl t ht).2.1⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨g0, hg0, d, hd, he⟩ := tmJH_const_fac I hhH
    refine ⟨toFin e' g0, ?_, toFin e' (tmJP (d, 1)), (hNq _).2 ⟨d, hd, rfl⟩, ?_⟩
    · rw [hG]; exact Subgroup.mem_map_of_mem _ hg0
    · rw [he, map_mul]
  · obtain ⟨π, hπ⟩ := tmJ_local_match I hr hL
    refine ⟨π, fun a => ?_⟩
    obtain ⟨u, hu, hn⟩ := hπ a
    exact ⟨u, by rw [hAc]; exact hu, hn⟩
  · intro g hg ⟨w, hw, hf⟩ d' π' hd'
    have hg' := tmJ_lift_pull I e' hG hg
    have hw' := tmJ_nq_pull I e' hNq hw
    have hf' := tmJ_fac_pull I e' hf
    obtain ⟨hzY, hzc⟩ := tmJ_z_pull I Ac hAc hd'
    have hgc := tmJ_lift_cls I.normalizes hw' hf' hhH
    obtain ⟨p, hp, hpe⟩ := tmJ_u_mem I hhH hzc hgc
    refine ⟨p.1, p.2, hp, ?_, ?_, ?_⟩
    · rw [show (p.1, p.2) = p from rfl, hpe, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · exact tmJH_exists I hr hL hg' hw' hf' hzY hzc hp hpe.symm hlgN hTl' hAut
    · exact tmJH_odd_ne I hr hL hg' hw' hf' hzY hzc hp hpe.symm hlgN hTl' hAut

include hG hNq hAc hlg hTl hAut in
/-- **The output of the per-label program** lies in the piece and has class `h`. -/
theorem tmJ_label_out {r h : Perm I.B} (hr : r ∈ I.Hb) (hL : h ∈ tmGlLab I r)
    {g : Perm (Fin n)} (hg : g ∈ gens gsG) (hw : ∃ w ∈ gens gsNq,
      toFin e' (tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q)))) = g * w)
    {d' : Fin L.q → Perm I.B} {π' : Perm (Fin L.q)}
    (hd' : ∀ a, d' a ∈ Ac (a, π' a) ∧ h⁻¹ * d' a ∈ I.Nb)
    {d : Fin L.q → Perm I.B} {π : Perm (Fin L.q)} (hd : ∀ i, d i ∈ I.Nb)
    (he : (toFin e' (tmJP (d', π')))⁻¹ * g = toFin e' (tmJP (d, π)))
    (c : Fin lg.length → ℤ) (hc : tmJSumT I.Nb I.φ lg c = tmJLab I.Nb I.φ d)
    (odd : Bool) (hodd : odd = true ↔ sign π = -1) :
    tmJP (d', π') * tmJCorrE Tl odd lg c ∈ tmJP '' tmCosetT I r ∧
      tmJP (d', π') * tmJCorrE Tl odd lg c ∈ tmJCls I.Nb h := by
  obtain ⟨w, hw, hf⟩ := hw
  have hg' := tmJ_lift_pull I e' hG hg
  have hw' := tmJ_nq_pull I e' hNq hw
  have hf' := tmJ_fac_pull I e' hf
  obtain ⟨hzY, hzc⟩ := tmJ_z_pull I Ac hAc hd'
  have he' : (tmJP (d', π'))⁻¹ * (toFin e').symm g = tmJP (d, π) := by
    apply (toFin e').injective
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, he]
  exact tmJH_corr I hr hL hg' hw' hf' hzY hzc hd he' hlg hTl hAut c hc odd hodd

end RT

end GI.Impl
