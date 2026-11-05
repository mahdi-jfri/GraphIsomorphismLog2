module

public import Workspace.Proved.VsWAlgMath

@[expose] public section

/-!
# Joint eigenspaces as lists of bases

`vsFEigL p D Ss` refines the whole space one stored matrix `s ∈ Ss` at a time: each piece `P`
is cut into the nonzero parts `span P ∩ ker (s - c)`, for `c < p`. So at the end the pieces are
the nonzero joint eigenspaces of the `Ss`, each once for each eigenvalue vector.

* `vsWBas_nil_iff`: an echelon basis is empty iff the span is zero.
* `vsFEigL_pieces`: every piece is a basis of a nonzero `vsFEig f a`, and every nonzero
  `vsFEig f a` is spanned by some piece (`f i = vsWLin p D Ss[i]`). This is the result used
  later.
-/

namespace GI.Proved

open GI.Impl

variable {p : ℕ}

theorem vsWSp_nil (d : ℕ) : vsWSp p d [] = ⊥ := by simp [vsWSp]

/-- An echelon basis is empty iff its span is zero. -/
theorem vsWBas_nil_iff (hp : p.Prime) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) :
    vsWBas p us = [] ↔ vsWSp p d us = ⊥ := by
  haveI := Fact.mk hp
  rw [← vsWBas_span hp h]
  constructor
  · intro h0; rw [h0, vsWSp_nil]
  · intro h0
    by_contra hne
    have hpos : 0 < (vsWBas p us).length := List.length_pos_iff.mpr hne
    have hind := vsWBas_indep hp h
    have hz := hind.ne_zero ⟨0, hpos⟩
    have hm : vsWV p d (vsWBas p us)[0] ∈ vsWSp p d (vsWBas p us) :=
      vsWV_mem_vsWSp d (List.getElem_mem hpos)
    rw [h0, Submodule.mem_bot] at hm
    exact hz hm

/-- Cutting by `s - c`: the eigenspace of `s` for `c`. -/
theorem vsWSubC_cut (hp : p.Prime) {D c : ℕ} (hc : c ≤ p) {s : List (List ℕ)} (hs : VsWSq p D s)
    {P : List (List ℕ)} (hP : VsWFit p D P) :
    vsWSp p D (vsWBas p (vsWCut p D P (vsWSubC p c s))) =
      vsWSp p D P ⊓ (vsWLin p D s).eigenspace (c : ZMod p) := by
  rw [vsWBas_span hp vsWCut_fit', vsWCut_span hp hP (vsWSubC_fit hp.pos hs)]
  congr 1
  ext v
  rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff, vsWLin, vsWLin, Matrix.toLin'_apply,
    Matrix.toLin'_apply, vsWSubC_matrix hp.pos hc hs, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, sub_eq_zero]
where vsWCut_fit' : VsWFit p D (vsWCut p D P (vsWSubC p c s)) := vsWCut_fit hp.pos

/-! ### Joint eigenspaces of a list -/

/-- The joint eigenspace of the stored matrices `Ss`, with eigenvalue `a i` for `Ss[i]`. -/
noncomputable def vsWJE (p D : ℕ) (Ss : List (List (List ℕ))) (a : ℕ → ZMod p) :
    Submodule (ZMod p) (Fin D → ZMod p) :=
  ⨅ i : Fin Ss.length, (vsWLin p D Ss[i]).eigenspace (a i)

theorem mem_vsWJE {D : ℕ} (Ss : List (List (List ℕ))) (a : ℕ → ZMod p) (v : Fin D → ZMod p) :
    v ∈ vsWJE p D Ss a ↔ ∀ i (h : i < Ss.length), vsWLin p D Ss[i] v = a i • v := by
  simp only [vsWJE, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  exact ⟨fun H i h => H ⟨i, h⟩, fun H i => H i i.2⟩

theorem vsWJE_nil (D : ℕ) (a : ℕ → ZMod p) : vsWJE p D [] a = ⊤ :=
  eq_top_iff.mpr fun v _ => (mem_vsWJE [] a v).mpr fun i h => absurd h (by simp)

theorem vsWJE_snoc {D : ℕ} (T : List (List (List ℕ))) (s : List (List ℕ)) (a : ℕ → ZMod p) :
    vsWJE p D (T ++ [s]) a = vsWJE p D T a ⊓ (vsWLin p D s).eigenspace (a T.length) := by
  ext v
  rw [Submodule.mem_inf, mem_vsWJE, mem_vsWJE, Module.End.mem_eigenspace_iff]
  constructor
  · intro H
    refine ⟨fun i h => ?_, ?_⟩
    · have := H i (by simp; omega)
      rwa [List.getElem_append_left h] at this
    · have := H T.length (by simp)
      rwa [List.getElem_append_right (by omega), List.getElem_singleton] at this
  · rintro ⟨H1, H2⟩ i h
    simp only [List.length_append, List.length_singleton] at h
    by_cases hi : i < T.length
    · rw [List.getElem_append_left hi]; exact H1 i hi
    · have hi' : i = T.length := by omega
      subst hi'
      rw [List.getElem_append_right (by omega), List.getElem_singleton]
      exact H2

theorem vsWJE_congr {D : ℕ} (T : List (List (List ℕ))) {a b : ℕ → ZMod p}
    (h : ∀ i < T.length, a i = b i) : vsWJE p D T a = vsWJE p D T b := by
  ext v
  rw [mem_vsWJE, mem_vsWJE]
  exact forall_congr' fun i => forall_congr' fun hi => by rw [h i hi]

/-! ### The refinement -/

/-- The invariant of the refinement after the matrices `T`. -/
def VsWEigInv (p D : ℕ) (T : List (List (List ℕ))) (L : List (List (List ℕ))) : Prop :=
  (∀ Q ∈ L, VsWFit p D Q ∧ vsWSp p D Q ≠ ⊥ ∧ ∃ a, vsWSp p D Q = vsWJE p D T a) ∧
    (∀ a, vsWJE p D T a ≠ ⊥ → ∃ Q ∈ L, vsWSp p D Q = vsWJE p D T a)

theorem vsWEigInv_nil (hp : p.Prime) (D : ℕ) : VsWEigInv p D [] (vsFEig0 D) := by
  haveI := Fact.mk hp
  have hmem : ∀ Q, Q ∈ vsFEig0 D ↔ Q = vsWId D ∧ vsWId D ≠ [] := by
    intro Q
    simp only [vsFEig0, List.mem_filter, List.mem_singleton, Bool.not_eq_true',
      List.isEmpty_eq_false_iff]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
  refine ⟨fun Q hQ => ?_, fun a ha => ?_⟩
  · obtain ⟨rfl, hne⟩ := (hmem Q).mp hQ
    refine ⟨vsWId_fit hp.one_lt D, ?_, 0, by rw [vsWJE_nil, vsWId_span]⟩
    rw [vsWId_span]
    intro htop
    have hD : 0 < D := by
      rcases Nat.eq_zero_or_pos D with h0 | h0
      · exact absurd (by simp [vsWId, h0]) hne
      · exact h0
    have hm : vsWV p D (vsUnit D 0) ∈ (⊤ : Submodule (ZMod p) (Fin D → ZMod p)) := trivial
    rw [htop, Submodule.mem_bot, vsWV_unit hD] at hm
    have := congrFun hm ⟨0, hD⟩
    simp at this
  · rw [vsWJE_nil] at ha ⊢
    have hne : vsWId D ≠ [] := by
      intro h0
      have hD : D = 0 := by simpa [vsWId] using h0
      subst hD
      exact ha ((Submodule.eq_bot_iff _).mpr fun v _ => Subsingleton.elim v 0)
    exact ⟨vsWId D, (hmem _).mpr ⟨rfl, hne⟩, vsWId_span D⟩

theorem vsWEigInv_snoc (hp : p.Prime) {D : ℕ} {T : List (List (List ℕ))} {s : List (List ℕ)}
    (hs : VsWSq p D s) {L : List (List (List ℕ))} (hI : VsWEigInv p D T L) :
    VsWEigInv p D (T ++ [s]) (L.flatMap (vsFEigSplit p D s)) := by
  haveI := Fact.mk hp
  have hmem : ∀ Q, Q ∈ L.flatMap (vsFEigSplit p D s) ↔
      ∃ P ∈ L, ∃ c < p, vsWBas p (vsWCut p D P (vsWSubC p c s)) = Q ∧ Q ≠ [] := by
    intro Q
    simp only [List.mem_flatMap, vsFEigSplit, List.mem_filter, List.mem_map, List.mem_range,
      Bool.not_eq_true', List.isEmpty_eq_false_iff]
    constructor
    · rintro ⟨P, hP, ⟨c, hc, rfl⟩, hne⟩; exact ⟨P, hP, c, hc, rfl, hne⟩
    · rintro ⟨P, hP, c, hc, rfl, hne⟩; exact ⟨P, hP, ⟨c, hc, rfl⟩, hne⟩
  refine ⟨fun Q hQ => ?_, fun a ha => ?_⟩
  · obtain ⟨P, hP, c, hc, rfl, hne⟩ := (hmem Q).mp hQ
    obtain ⟨hPf, -, a, ha⟩ := hI.1 P hP
    have hcut : VsWFit p D (vsWCut p D P (vsWSubC p c s)) := vsWCut_fit hp.pos
    refine ⟨vsWBas_fit hp.pos hcut, fun h0 => hne ((vsWBas_nil_iff hp hcut).mpr ?_), ?_⟩
    · rwa [vsWBas_span hp hcut] at h0
    · refine ⟨fun i => if i = T.length then (c : ZMod p) else a i, ?_⟩
      rw [vsWSubC_cut hp hc.le hs hPf, vsWJE_snoc, if_pos rfl, ha]
      congr 1
      exact vsWJE_congr T fun i hi => by simp [show i ≠ T.length by omega]
  · have hT : vsWJE p D T a ≠ ⊥ := by
      intro h0
      apply ha
      rw [vsWJE_snoc, h0, bot_inf_eq]
    obtain ⟨P, hP, hPa⟩ := hI.2 a hT
    have hPf := (hI.1 P hP).1
    set c := (a T.length).val
    have hc : c < p := ZMod.val_lt _
    have hspan : vsWSp p D (vsWBas p (vsWCut p D P (vsWSubC p c s))) = vsWJE p D (T ++ [s]) a := by
      rw [vsWSubC_cut hp hc.le hs hPf, vsWJE_snoc, hPa, ZMod.natCast_zmod_val]
    refine ⟨_, (hmem _).mpr ⟨P, hP, c, hc, rfl, fun h0 => ha ?_⟩, hspan⟩
    rw [← hspan, h0, vsWSp_nil]

theorem vsFEigL_inv (hp : p.Prime) {D : ℕ} (Ss : List (List (List ℕ)))
    (hS : ∀ s ∈ Ss, VsWSq p D s) : VsWEigInv p D Ss (vsFEigL p D Ss) := by
  induction Ss using List.reverseRecOn with
  | nil => exact vsWEigInv_nil hp D
  | append_singleton T s ih =>
    rw [vsFEigL, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact vsWEigInv_snoc hp (hS s (by simp))
      (ih fun s' hs' => hS s' (List.mem_append_left _ hs'))

/-- **The pieces.** With `f i = vsWLin p D Ss[i]`: every piece of `vsFEigL p D Ss` is a list of
vectors whose span is a nonzero joint eigenspace `vsFEig f a`, and every nonzero `vsFEig f a` is
the span of some piece. -/
theorem vsFEigL_pieces (hp : p.Prime) {D : ℕ} (Ss : List (List (List ℕ)))
    (hS : ∀ s ∈ Ss, VsWSq p D s) :
    haveI := Fact.mk hp
    (∀ Q ∈ vsFEigL p D Ss, VsWFit p D Q ∧ vsWSp p D Q ≠ ⊥ ∧
      ∃ a, vsWSp p D Q = vsFEig (fun i : Fin Ss.length => vsWLin p D Ss[i]) a) ∧
    (∀ a, vsFEig (fun i : Fin Ss.length => vsWLin p D Ss[i]) a ≠ ⊥ →
      ∃ Q ∈ vsFEigL p D Ss, vsWSp p D Q = vsFEig (fun i : Fin Ss.length => vsWLin p D Ss[i]) a) := by
  haveI := Fact.mk hp
  obtain ⟨h1, h2⟩ := vsFEigL_inv hp Ss hS
  -- the two ways of indexing eigenvalues
  have e1 : ∀ a : ℕ → ZMod p, vsWJE p D Ss a =
      vsFEig (fun i : Fin Ss.length => vsWLin p D Ss[i]) (fun i => a i) := by
    intro a
    ext v
    rw [mem_vsWJE, mem_vsFEig]
    exact ⟨fun H i => H i i.2, fun H i h => H ⟨i, h⟩⟩
  have e2 : ∀ a : Fin Ss.length → ZMod p,
      vsFEig (fun i : Fin Ss.length => vsWLin p D Ss[i]) a =
        vsWJE p D Ss (fun j => if h : j < Ss.length then a ⟨j, h⟩ else 0) := by
    intro a
    rw [e1]
    congr 1
    funext i
    simp [i.2]
  refine ⟨fun Q hQ => ?_, fun a ha => ?_⟩
  · obtain ⟨hf, hne, a, ha⟩ := h1 Q hQ
    exact ⟨hf, hne, _, ha.trans (e1 a)⟩
  · rw [e2] at ha ⊢
    exact h2 _ ha

end GI.Proved
