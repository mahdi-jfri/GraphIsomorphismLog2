import Workspace.Impl.VsHQ8Next
import Workspace.Impl.VsQA3M

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime]
  {hs : VsQStOK s} {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
  {ys : List (Perm (Fin I.n))} {r : ℕ}

/-- A hard group has a nonempty basis modulo the scalars. -/
theorem vsHC_basis_ne_nil (h : VsHHyp hs as Lb ys r) : vsHB s Lb r ys ≠ [] := by
  intro he
  have hY := h.bas.2.1
  rw [he] at hY
  simp only [List.not_mem_nil, Set.setOf_false, Set.image_empty, Subgroup.closure_empty,
    bot_sup_eq] at hY
  obtain ⟨x, hx, y, hy, hne⟩ := h.hard.nab
  change y ∈ vsHY hs as ys at hy
  rw [hY] at hy
  exact hne (h.hard.scal_comm hx hy)

/-- A hard group acts on a space of dimension at least two. -/
theorem vsHC_dim_two (h : VsHHyp hs as Lb ys r) : 2 ≤ vsQD s := by
  have hl : 1 ≤ (vsHB s Lb r ys).length := by
    have := vsHC_basis_ne_nil h
    rw [← List.length_pos_iff] at this
    omega
  have hp : r ≤ r ^ (vsHB s Lb r ys).length := by
    simpa using Nat.pow_le_pow_right (show 1 ≤ r from h.hard.prime.one_lt.le) hl
  have hb := h.bas.2.2.1
  have hr := h.hard.prime.two_le
  by_contra hn
  have hD : vsQD s ≤ 1 := by omega
  have hD2 : vsQD s ^ 2 ≤ 1 := by simpa using Nat.pow_le_pow_left hD 2
  omega

/-- The first basis element used by the two-`Q₈` split. -/
noncomputable def vsHCHead (s : VsQSt I) (Lb : List (List (List ℕ))) (r : ℕ)
    (ys : List (Perm (Fin I.n))) : Perm (Fin I.n) := (vsHB s Lb r ys).headD 1

/-- This element belongs to the hard group and is not a scalar. -/
theorem vsHC_head (h : VsHHyp hs as Lb ys r) :
    vsHCHead s Lb r ys ∈ gens s.hs ∧
    vsPRho hs (vsHCHead s Lb r ys) ∈ vsHY hs as ys ∧
    vsPRho hs (vsHCHead s Lb r ys) ∉ vsHS hs as := by
  have hne := vsHC_basis_ne_nil h
  have hlen : 0 < (vsHB s Lb r ys).length := List.length_pos_iff.2 hne
  have hh : ∀ (B : List (Perm (Fin I.n))) (hl : 0 < B.length), B.headD 1 = B[0] := by
    intro B hl
    cases B with
    | nil => simp at hl
    | cons b bs => rfl
  have he : vsHCHead s Lb r ys = (vsHB s Lb r ys)[0] := hh _ hlen
  have hm : vsHCHead s Lb r ys ∈ vsHB s Lb r ys := by rw [he]; exact List.getElem_mem hlen
  obtain ⟨hb, hind, -, -⟩ := vsHBas_out hs h.has h.hLb h.hspan h.hys h.hard ys h.inY
  refine ⟨h.hys _ (h.bas.1 _ hm), (h.inY _ (h.bas.1 _ hm)).2, ?_⟩
  have hi := hind 0 hlen
  simp only [List.take_zero, List.not_mem_nil, Set.setOf_false, Set.image_empty,
    Subgroup.closure_empty, bot_sup_eq] at hi
  rwa [he]

/-- The empty greedy family is maximal among good isotropic elements. -/
theorem vsHC_empty_iso (h : VsHHyp hs as Lb ys r) (hk : (vsHK s Lb r ys).length = 0) :
    VsMIso (vsPBar hs (gens as)) (vsHY hs as ys) r
      (Fin.elim0 : Fin 0 → (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) := by
  obtain ⟨hi, -⟩ := h.iso
  haveI : IsEmpty (Fin (vsHK s Lb r ys).length) := by rw [hk]; infer_instance
  refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    fun y hy hg _ => ?_⟩
  have hh := hi.2.2.2.2 y hy hg (fun i => isEmptyElim i)
  rw [Set.range_eq_empty] at hh
  rwa [Set.range_eq_empty]

/-- The second hand-off centralizes the first hard group. -/
theorem vsHC_next_cent {ccs ks ys' : List (Perm (Fin I.n))}
    (hH : VsPHyp hs as Lb ccs) (h : VsHHyp hs as Lb ys r)
    (hks : ∀ g, g ∈ gens ks ↔ g ∈ gens ccs ∧
      vsHAlT s g ((vsHB s Lb r ys).map (vsHT s)) = (vsHB s Lb r ys).map (vsHT s))
    (hy' : ∀ y ∈ ys', y ∈ gens ks) :
    vsHY hs as ys' ≤ Subgroup.centralizer (vsHY hs as ys : Set _) := by
  have hB : ∀ b ∈ vsHB s Lb r ys, b ∈ gens s.hs := fun b hb => h.hys b (h.bas.1 b hb)
  have hkC : gens ks ≤ gens ccs := fun g hg => ((hks g).1 hg).1
  have hyH : ∀ y ∈ ys', y ∈ gens s.hs := fun y hy => hH.hcc (hkC (hy' y hy))
  change vsPBar hs (gens ys') ⊔ vsHS hs as ≤ _
  apply sup_le
  · rw [vsPBar_gens hs hyH]
    apply (Subgroup.closure_le _).2
    rintro _ ⟨y, hy, rfl⟩
    have hyk := (hks y).1 (hy' y hy)
    have hc := (vsHQ8_stab hs hB hH.hcc hH.hccC hyk.1).1 hyk.2
    rwa [← h.bas.2.1] at hc
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    exact fun y hy => h.hard.scal_comm hy hu

/-- Multiply the two transversals in their group order. -/
def vsHCTrans {n : ℕ} (ts us : List (Perm (Fin n))) : List (Perm (Fin n)) :=
  ts.flatMap fun t => us.map fun u => t * u

theorem vsHCTrans_length {n : ℕ} (ts us : List (Perm (Fin n))) :
    (vsHCTrans ts us).length = ts.length * us.length := by
  simp [vsHCTrans, List.length_flatMap, List.sum_replicate]

/-- The product list covers the smaller subgroup. -/
theorem vsHCTrans_cover {n : ℕ} {H C K : Subgroup (Perm (Fin n))}
    {ts us : List (Perm (Fin n))} (ht : ∀ t ∈ ts, t ∈ H) (hu : ∀ u ∈ us, u ∈ H)
    (hc : ∀ h ∈ H, ∃ t ∈ ts, t⁻¹ * h ∈ C)
    (hk : ∀ c ∈ C, ∃ u ∈ us, u⁻¹ * c ∈ K) :
    (∀ t ∈ vsHCTrans ts us, t ∈ H) ∧
    ∀ h ∈ H, ∃ t ∈ vsHCTrans ts us, t⁻¹ * h ∈ K := by
  constructor
  · intro t hmem
    change t ∈ ts.flatMap (fun a => us.map (fun b => a * b)) at hmem
    obtain ⟨a, ha, hma⟩ := List.mem_flatMap.1 hmem
    obtain ⟨b, hb, he⟩ := List.mem_map.1 hma
    rw [← he]
    exact mul_mem (ht a ha) (hu b hb)
  · intro h hh
    obtain ⟨t, ht', htc⟩ := hc h hh
    obtain ⟨u, hu', huk⟩ := hk _ htc
    refine ⟨t * u, List.mem_flatMap.2 ⟨t, ht', List.mem_map.2 ⟨u, hu', rfl⟩⟩, ?_⟩
    simpa [_root_.mul_inv_rev, mul_assoc] using huk

theorem vsHC_splitOK (hs : VsQStOK s) {E Tm : ℕ} {ts ks : List (Perm (Fin I.n))}
    (hksl : ks.length ≤ I.n ^ 2) (hK : gens ks ≤ gens s.hs) (htmem : ∀ t ∈ ts, t ∈ gens s.hs)
    (hcov : ∀ h ∈ gens s.hs, ∃ t ∈ ts, t⁻¹ * h ∈ gens ks) (htl : ts.length ≤ Tm)
    (hab : VsQAb I (gens ks) (vsQSp I s.ws) (vsQSp I s.ws')) (hnab : ¬ s.Ab) (hD2 : 2 ≤ vsQD s)
    (hts : ts.length ≤ 24 * vsQD s) :
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
