import Workspace.Impl.VsHSplitPs
import Workspace.Proved.VsMQ8

/-!
# The second `Q₈`

Two commuting `Q₈`-type groups `Ȳ`, `Ȳ'` (both hard with `r = 2` and no isotropic element), and
`y ∈ Y`, `y' ∈ Y'` outside `S`: the pieces of `𝔽_p[A ∪ {ȳ ȳ'}]`, computed by `vsHPs_spec` with
`K = [y y']`, are `2` independent pieces of equal dimension spanning everything, and the orbit
of the pair of their spans has at most `72` points (`vsH_q8two_pieces`).
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime]

theorem vsH_q8two_pieces (hs : VsQStOK s) {as : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs)
    {Y Y' : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ}
    (hY : VsMHard (vsPBar hs (gens s.hs)) (vsPBar hs (gens as)) Y 2)
    (hYi : VsMIso (vsPBar hs (gens as)) Y 2 (Fin.elim0 : Fin 0 → _))
    (hY' : VsMHard (vsPBar hs (gens s.hs)) (vsPBar hs (gens as)) Y' 2)
    (hYi' : VsMIso (vsPBar hs (gens as)) Y' 2 (Fin.elim0 : Fin 0 → _))
    (hYY : Y' ≤ Subgroup.centralizer (Y : Set _))
    {y y' : Perm (Fin I.n)} (hy : y ∈ gens s.hs) (hy' : y' ∈ gens s.hs)
    (hyY : vsPRho hs y ∈ Y) (hyS : vsPRho hs y ∉ vsMScal (vsPBar hs (gens as)))
    (hyY' : vsPRho hs y' ∈ Y') (hyS' : vsPRho hs y' ∉ vsMScal (vsPBar hs (gens as))) :
    let Ps := vsHPs s ((1 :: as) ++ [y * y'])
    (∀ P ∈ Ps, VsWFit I.p (vsQD s) P) ∧ Ps.length = 2 ∧
      (iSupIndep fun i : Fin Ps.length => vsWSp I.p (vsQD s) Ps[i]) ∧
      (∃ e, 0 < e ∧ ∀ i : Fin Ps.length, finrank (ZMod I.p) (vsWSp I.p (vsQD s) Ps[i]) = e) ∧
      (⨆ i : Fin Ps.length, vsWSp I.p (vsQD s) Ps[i]) = ⊤ ∧
      (vsQOrb (vsQTAct s) s.hs (Ps.map (vsWSp I.p (vsQD s)))).ncard ≤ 72 := by
  intro Ps
  haveI := vsH_nontrivial hY
  have hyy : y * y' ∈ gens s.hs := mul_mem hy hy'
  have hg1 : gens (1 :: as) = gens as := vsH_genGroup_one as
  have has1 : gens (1 :: as) ≤ gens s.hs := hg1 ▸ has
  have he : vsHEf hs [y * y'] = ![vsPRho hs y * vsPRho hs y'] := by
    funext i
    fin_cases i
    simp [vsHEf, vsPRho_mul hs hy hy']
  have hP := vsM_q8Two (p := I.p) (V := Fin (vsQD s) → ZMod I.p) _ _ _ _ Fin.elim0
    (vsPRho hs y) (vsPRho hs y') hY hYi hY' hYi' hYY hyY hyS hyY' hyS'
  rw [← he] at hP
  have hP1 : VsMPiecesOut (vsPBar hs (gens s.hs)) (vsMAlgE (vsPBar hs (gens (1 :: as))) (vsHEf hs [y * y']))
      2 72 := by rw [hg1]; exact hP
  -- the generators commute
  have hA := hY.2.1.2.2
  have hYC := hY.2.2.2.2.2.1
  have hYC' := hY'.2.2.2.2.2.1
  have hAs : ∀ a ∈ as, vsPRho hs a ∈ vsPBar hs (gens as) := fun a ha =>
    vsPRho_mem_vsPBar hs (Subgroup.subset_closure ha) (has (Subgroup.subset_closure ha))
  have hcA : ∀ a ∈ as, vsPRho hs a * vsPRho hs (y * y') = vsPRho hs (y * y') * vsPRho hs a := by
    intro a ha
    rw [vsPRho_mul hs hy hy']
    have h1 := Subgroup.mem_centralizer_iff.1 (hYC hyY) _ (hAs a ha)
    have h2 := Subgroup.mem_centralizer_iff.1 (hYC' hyY') _ (hAs a ha)
    calc vsPRho hs a * (vsPRho hs y * vsPRho hs y') = (vsPRho hs a * vsPRho hs y) * vsPRho hs y' := by group
      _ = (vsPRho hs y * vsPRho hs a) * vsPRho hs y' := by rw [h1]
      _ = vsPRho hs y * (vsPRho hs a * vsPRho hs y') := by group
      _ = vsPRho hs y * (vsPRho hs y' * vsPRho hs a) := by rw [h2]
      _ = _ := by group
  have hc1 : ∀ x ∈ (1 :: as) ++ [y * y'], ∀ z ∈ (1 :: as) ++ [y * y'],
      vsPRho hs x * vsPRho hs z = vsPRho hs z * vsPRho hs x := by
    intro x hx z hz
    have hx' : x = 1 ∨ x ∈ as ∨ x = y * y' := by simpa using hx
    have hz' : z = 1 ∨ z ∈ as ∨ z = y * y' := by simpa using hz
    rcases hx' with rfl | hx' | rfl <;> rcases hz' with rfl | hz' | rfl <;>
      first
      | rw [vsPRho_one, one_mul, mul_one]
      | exact hA _ (hAs _ hx') _ (hAs _ hz')
      | exact hcA _ hx'
      | exact (hcA _ hz').symm
      | rfl
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := vsH_split_data hs has1 (by simpa using hyy) hc1 hP1
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end GI.Impl
