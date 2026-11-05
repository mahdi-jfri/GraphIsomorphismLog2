module

public import Workspace.Impl.VsQCentP

@[expose] public section

/-!
# Facts on the centralizer of `A`

The centralizer program (`vsQCent_spec`) with `ccs = hs` and `B = 1 :: as` returns `ks` with
`⟨ks⟩ = C_H(A)` and a transversal `us` of `⟨ks⟩` in `H`. Here:

* `vsQA3_cent`, `vsQA3_normd`, `vsQA3_le`: `C̄` centralizes `Ā`, and `C` is normal in `H`.
* `vsQAb_of_comm`: if the local matrices of `C` commute, `C` acts on `W/W'` as an abelian group.
* `vsQA3_splitOK`: then `(us, ks, [ws'])` is a correct split of case 3.
* `vsQA3_nab`: otherwise `C̄` is not abelian.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime] {hs : VsQStOK s}

/-- Commuting with the generators of `⟨as⟩` means commuting with all of it. -/
theorem vsQA3_comm_closure {as : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs)
    {u : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ}
    (hu : ∀ b ∈ as, u * vsPRho hs b = vsPRho hs b * u) :
    ∀ b ∈ gens as, u * vsPRho hs b = vsPRho hs b * u := by
  intro b hb
  induction hb using Subgroup.closure_induction with
  | mem b hb => exact hu b hb
  | one => rw [vsPRho_one hs, mul_one, one_mul]
  | mul a c ha hc iha ihc =>
    rw [vsPRho_mul hs (has ha) (has hc), ← mul_assoc, iha, mul_assoc, ihc, mul_assoc]
  | inv a ha iha =>
    rw [vsPRho_inv hs (has ha)]
    calc u * (vsPRho hs a)⁻¹ = (vsPRho hs a)⁻¹ * (vsPRho hs a * u) * (vsPRho hs a)⁻¹ := by group
      _ = (vsPRho hs a)⁻¹ * (u * vsPRho hs a) * (vsPRho hs a)⁻¹ := by rw [iha]
      _ = (vsPRho hs a)⁻¹ * u := by group

section

variable {as ks : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs)
  (hks : ∀ h, h ∈ gens ks ↔ h ∈ gens s.hs ∧
    vsHAlT s h ((1 :: as).map (vsHT s)) = (1 :: as).map (vsHT s))
include has hks

theorem vsQA3_B : ∀ b ∈ 1 :: as, b ∈ gens s.hs := fun b hb => by
  rcases List.mem_cons.1 hb with rfl | hb
  · exact one_mem _
  · exact has (Subgroup.subset_closure hb)

theorem vsQA3_le : gens ks ≤ gens s.hs := fun h hh => ((hks h).1 hh).1

theorem vsQA3_mem {x : Perm (Fin I.n)} (hx : x ∈ gens ks) :
    ∀ b ∈ gens as, vsPRho hs x * vsPRho hs b = vsPRho hs b * vsPRho hs x := by
  obtain ⟨hxH, hfix⟩ := (hks x).1 hx
  have h1 := (vsH_q8_fix hs (vsQA3_B has hks) hxH).1 hfix
  exact vsQA3_comm_closure has fun b hb => h1 b (List.mem_cons_of_mem _ hb)

theorem vsQA3_cent : vsPBar hs (gens ks) ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _) := by
  intro u hu
  obtain ⟨x, hxK, -, rfl⟩ := (vsPBar_mem_iff hs).1 hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨b, hbA, -, rfl⟩ := (vsPBar_mem_iff hs).1 hv
  exact (vsQA3_mem has hks hxK b hbA).symm

theorem vsQA3_normd (hs : VsQStOK s) (hasn : VsPNormd (gens s.hs) (gens as)) : VsPNormd (gens s.hs) (gens ks) := by
  intro g hg x hx
  have hxH := vsQA3_le has hks hx
  have hc := vsQA3_mem (hs := hs) has hks hx
  refine (hks _).2 ⟨mul_mem (mul_mem hg hxH) (inv_mem hg), ?_⟩
  refine (vsH_q8_fix hs (vsQA3_B has hks) (mul_mem (mul_mem hg hxH) (inv_mem hg))).2 fun b hb => ?_
  have hbA : b ∈ gens as := by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact one_mem _
    · exact Subgroup.subset_closure hb
  have hbH := has hbA
  -- `g⁻¹ b g` is in `A`
  have hb' : g⁻¹ * b * g⁻¹⁻¹ ∈ gens as := hasn _ (inv_mem hg) _ hbA
  rw [inv_inv] at hb'
  have hc' := hc _ hb'
  rw [vsPRho_mul hs (mul_mem (inv_mem hg) hbH) hg, vsPRho_mul hs (inv_mem hg) hbH,
    vsPRho_inv hs hg] at hc'
  rw [vsPRho_mul hs (mul_mem hg hxH) (inv_mem hg), vsPRho_mul hs hg hxH, vsPRho_inv hs hg]
  set G := vsPRho hs g
  set X := vsPRho hs x
  set Bb := vsPRho hs b
  calc G * X * G⁻¹ * Bb = G * (X * (G⁻¹ * Bb * G)) * G⁻¹ := by group
    _ = G * ((G⁻¹ * Bb * G) * X) * G⁻¹ := by rw [hc']
    _ = Bb * (G * X * G⁻¹) := by group

end

/-- **An abelian subgroup on `W/W'`.** If the local matrices of a subgroup `K ≤ H` commute,
`K` acts on `W/W'` as an abelian group. -/
theorem vsQAb_of_comm (hs : VsQStOK s) {K : Subgroup (Perm (Fin I.n))} (hK : K ≤ gens s.hs)
    (hc : ∀ g ∈ K, ∀ h ∈ K, vsQLam s g * vsQLam s h = vsQLam s h * vsQLam s g) :
    VsQAb I K (vsQSp I s.ws) (vsQSp I s.ws') := by
  intro g hg h hh w hw
  have hg' := hK hg
  have hh' := hK hh
  obtain ⟨w', hw', a, rfl⟩ := hs.decomp hw
  have e1 := hs.prob.invW' g hg' _ (hs.prob.invW' h hh' w' hw')
  have e2 := hs.prob.invW' h hh' _ (hs.prob.invW' g hg' w' hw')
  have h1 := vsQLam_comb hs (mul_mem hg' hh') a
  have h2 := vsQLam_comb hs (mul_mem hh' hg') a
  rw [vsQPhi_mul (hs.prob.le hg') (hs.prob.le hh'), ← mulVec_mulVec] at h1
  rw [vsQPhi_mul (hs.prob.le hh') (hs.prob.le hg'), ← mulVec_mulVec] at h2
  rw [vsQLam_mul hs hg' hh', hc g hg h hh] at h1
  rw [vsQLam_mul hs hh' hg'] at h2
  have := Submodule.add_mem _ (Submodule.sub_mem _ e1 e2) (Submodule.sub_mem _ h1 h2)
  convert this using 1
  simp only [mulVec_add]
  abel
  rfl

/-- The test of the program: the stored local matrices of `gh` and `hg` agree. -/
theorem vsQ_comm_of_test (hs : VsQStOK s) {ks : List (Perm (Fin I.n))} (hK : gens ks ≤ gens s.hs)
    (ht : ∀ g ∈ 1 :: ks, ∀ h ∈ 1 :: ks,
      vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)) :
    ∀ x ∈ gens ks, ∀ y ∈ gens ks, vsQLam s x * vsQLam s y = vsQLam s y * vsQLam s x := by
  refine vsQLam_comm_closure hs hK fun g hg h hh => ?_
  have hg' := hK (Subgroup.subset_closure hg)
  have hh' := hK (Subgroup.subset_closure hh)
  rw [← vsQLam_mul hs hg' hh', ← vsQLam_mul hs hh' hg']
  exact (vsPLocL_eq_iff hs _ _).1 (ht g (List.mem_cons_of_mem _ hg) h (List.mem_cons_of_mem _ hh))

/-- If the test fails, the local image of `⟨ks⟩` is not abelian. -/
theorem vsQ_nab_of_test (hs : VsQStOK s) {ks : List (Perm (Fin I.n))} (hK : gens ks ≤ gens s.hs)
    (ht : ¬ ∀ g ∈ 1 :: ks, ∀ h ∈ 1 :: ks,
      vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)) :
    ¬ vsPBar hs (gens ks) ≤ Subgroup.centralizer (vsPBar hs (gens ks) : Set _) := by
  intro hab
  apply ht
  intro g hg h hh
  have hgK : g ∈ gens ks := by
    rcases List.mem_cons.1 hg with rfl | hg
    · exact one_mem _
    · exact Subgroup.subset_closure hg
  have hhK : h ∈ gens ks := by
    rcases List.mem_cons.1 hh with rfl | hh
    · exact one_mem _
    · exact Subgroup.subset_closure hh
  have hg' := hK hgK
  have hh' := hK hhK
  have hcomm := Subgroup.mem_centralizer_iff.1 (hab (vsPRho_mem_vsPBar hs hgK hg')) _
    (vsPRho_mem_vsPBar hs hhK hh')
  rw [vsPLocL_eq_iff hs]
  have e1 : vsPRho hs (g * h) = vsPRho hs (h * g) := by
    rw [vsPRho_mul hs hg' hh', vsPRho_mul hs hh' hg', hcomm]
  rw [vsPRho_of hs (mul_mem hg' hh'), vsPRho_of hs (mul_mem hh' hg')] at e1
  have e2 := congrArg (fun u : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ =>
    (u : Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))) e1
  rw [vsQRho_eq_toLin' hs (mul_mem hg' hh'), vsQRho_eq_toLin' hs (mul_mem hh' hg')] at e2
  exact Matrix.toLin'.injective e2

/-- **The split of case 3.** -/
theorem vsQA3_splitOK (hs : VsQStOK s) {E Tm : ℕ} {ts ks : List (Perm (Fin I.n))}
    (hksl : ks.length ≤ I.n ^ 2) (hK : gens ks ≤ gens s.hs) (htmem : ∀ t ∈ ts, t ∈ gens s.hs)
    (hcov : ∀ h ∈ gens s.hs, ∃ t ∈ ts, t⁻¹ * h ∈ gens ks) (htl : ts.length ≤ Tm)
    (hab : VsQAb I (gens ks) (vsQSp I s.ws) (vsQSp I s.ws')) (hnab : ¬ s.Ab) (hD2 : 2 ≤ vsQD s)
    (hts : ts.length ≤ vsQD s) :
    VsQSplitOK s E Tm ts ks [s.ws'] := by
  have hD := vsQD_eq hs
  refine ⟨hksl, hK, htmem, hcov, htl, ?_, List.cons_ne_nil _ _, rfl, ?_, ?_,
    Or.inr (Or.inr ⟨hnab, rfl, hab, by omega, by omega⟩)⟩
  · show List.IsChain _ [s.ws, s.ws']
    haveI : Nontrivial (Fin (vsQD s) → ZMod I.p) := by
      haveI : Nonempty (Fin (vsQD s)) := ⟨⟨0, by omega⟩⟩
      infer_instance
    have hlt := vsQLift_lt hs (bot_lt_top : (⊥ : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) < ⊤)
    rw [vsQLift_bot hs, vsQLift_top hs] at hlt
    exact List.IsChain.cons_cons hlt (List.isChain_singleton _)
  · intro u hu
    rw [List.mem_singleton] at hu
    subst hu
    exact ⟨hs.fit', hs.wl'⟩
  · intro u hu
    rw [List.mem_singleton] at hu
    subst hu
    exact hs.prob.invW'.mono hK

end GI.Impl
