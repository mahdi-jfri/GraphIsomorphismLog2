import Workspace.Impl.VsHPcOrb
import Workspace.Proved.VsHInjMath

/-!
# The list of pieces

For a commutative family of Frobenius fixed points `f i = vsWLin Fx[i]`, the pieces
`Ps = vsFEigL p D Fx` are the nonzero joint eigenspaces of `f`, each listed once
(`vsH_pieces`).
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The pieces, each listed once.** -/
theorem vsH_pieces {D : ℕ} {Fx : List (List (List ℕ))} (hFx : ∀ x ∈ Fx, VsWSq p D x)
    (B : Subalgebra (ZMod p) (Module.End (ZMod p) (Fin D → ZMod p)))
    (hB : ∀ x ∈ B, ∀ y ∈ B, Commute x y)
    (hfB : ∀ i : Fin Fx.length, vsWLin p D Fx[i] ∈ B)
    (hf : ∀ i : Fin Fx.length, vsWLin p D Fx[i] ^ p = vsWLin p D Fx[i]) :
    let f := fun i : Fin Fx.length => vsWLin p D Fx[i]
    let Ps := vsFEigL p D Fx
    ∃ a : Fin Ps.length → (Fin Fx.length → ZMod p), Function.Injective a ∧
      (∀ i, vsWSp p D Ps[i] = vsFEig f (a i) ∧ vsFEig f (a i) ≠ ⊥) ∧
      (∀ b, vsFEig f b ≠ ⊥ → ∃ i, a i = b) ∧
      Ps.length = {b | vsFEig f b ≠ ⊥}.ncard := by
  classical
  intro f Ps
  obtain ⟨h1, h2⟩ := vsFEigL_pieces hp.out Fx hFx
  obtain ⟨hc1, hc2⟩ := vsFEigL_cnt hp.out Fx hFx
  -- choose the eigenvalues of each piece
  have hch : ∀ i : Fin Ps.length, ∃ b, vsWSp p D Ps[i] = vsFEig f b :=
    fun i => (h1 _ (List.getElem_mem i.2)).2.2
  choose a ha using hch
  have hne : ∀ i, vsFEig f (a i) ≠ ⊥ := fun i => (ha i) ▸ (h1 _ (List.getElem_mem i.2)).2.1
  set T := Finset.univ.filter fun b : Fin Fx.length → ZMod p => vsFEig f b ≠ ⊥
  have hmap : ∀ i, a i ∈ T := fun i => by simp [T, hne i]
  have hsurj : ∀ b ∈ T, ∃ i, a i = b := by
    intro b hb
    have hb' : vsFEig f b ≠ ⊥ := (Finset.mem_filter.1 hb).2
    obtain ⟨Q, hQ, hQe⟩ := h2 b hb'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hQ
    refine ⟨⟨i, hi⟩, ?_⟩
    by_contra hab
    have hd : Disjoint (vsFEig f (a ⟨i, hi⟩)) (vsFEig f b) := by
      rw [Submodule.disjoint_def]
      exact fun v h1 h2 => vsFEig_disjoint f hab h1 h2
    have e1 : vsFEig f (a ⟨i, hi⟩) = vsFEig f b := (ha ⟨i, hi⟩).symm.trans hQe
    rw [e1, disjoint_self] at hd
    exact hb' hd
  -- dimensions
  set g := fun b : Fin Fx.length → ZMod p => finrank (ZMod p) (vsFEig f b)
  have hpos : ∀ b ∈ T, 0 < g b := fun b hb => by
    simp only [g]
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact (Finset.mem_filter.1 hb).2
  have hind := vsFEig_indep B hB f hfB hf
  have hsup := vsFEig_iSup B hB f hfB hf
  have hT : ∑ b ∈ T, g b = D := by
    rw [← vsW_finrank_biSup hind T]
    have : (⨆ b ∈ T, vsFEig f b) = ⊤ := by
      rw [eq_top_iff, ← hsup]
      refine iSup_le fun b => ?_
      by_cases hb : vsFEig f b = ⊥
      · rw [hb]; exact bot_le
      · exact le_biSup (fun b => vsFEig f b) (by simp [T, hb])
    rw [this, finrank_top, Module.finrank_fin_fun]
  have hsum : ∑ i, g (a i) ≤ ∑ b ∈ T, g b := by
    rw [hT]
    have e : ∑ i : Fin Ps.length, g (a i) = (Ps.map List.length).sum := by
      rw [← Fin.sum_univ_getElem (Ps.map List.length)]
      refine Fintype.sum_equiv (finCongr (List.length_map _).symm) _ _ fun i => ?_
      simp only [g, finCongr_apply, List.getElem_map, Fin.val_cast]
      rw [← ha i, (hc1 _ (List.getElem_mem i.2)).2.2]
      rfl
    rw [e]; exact hc2
  have hinj := vsH_inj_of_sum a T g hmap hsurj hpos hsum
  refine ⟨a, hinj, fun i => ⟨ha i, hne i⟩, fun b hb => hsurj b (by simp [T, hb]), ?_⟩
  have hbij : Ps.length = T.card := by
    have := Finset.card_image_of_injective Finset.univ hinj
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [← this]
    congr 1
    ext b
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ hmap i, fun hb => hsurj b hb⟩
  rw [hbij, ← Set.ncard_coe_finset]
  congr 1
  ext b; simp [T]

end GI.Impl
