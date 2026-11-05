module

public import Workspace.Proved.VsWEigMath

@[expose] public section

/-!
# The pieces of `vsFEigL` are few and small

The program for `vsFEigL` needs a bound on the number and size of the pieces. Each piece is a
basis of its span, and the spans of the pieces that come from one piece `P` lie in independent
eigenspaces inside `span P`. So the total number of vectors in all pieces never goes up, and it
starts at `D`.

* `vsWBas_length`: an echelon basis has as many vectors as the dimension of the span.
* `vsW_sum_eig_le`: the dimensions of `W ∩ ker (f - c)`, `c < p`, add up to at most `dim W`.
* `vsFEigL_count`: the pieces of `vsFEigL p D Ss` are nonempty bases of length at most `D`, and
  together they have at most `D` vectors. This is the result used later.
-/

namespace GI.Proved

open GI.Impl Module

variable {p : ℕ}

/-- The dimension of the sum of finitely many independent subspaces is the sum of dimensions. -/
theorem vsW_finrank_biSup {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι] {f : ι → Submodule K V} (hf : iSupIndep f)
    (s : Finset ι) : finrank K ↥(⨆ i ∈ s, f i) = ∑ i ∈ s, finrank K (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.iSup_insert]
    have hd : Disjoint (f a) (⨆ i ∈ s, f i) := hf.disjoint_biSup (by exact_mod_cast ha)
    have := Submodule.finrank_sup_add_finrank_inf_eq (f a) (⨆ i ∈ s, f i)
    rw [hd.eq_bot, finrank_bot] at this
    omega

theorem vsW_list_sum_range (n : ℕ) (g : ℕ → ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

/-- The parts of `W` in the eigenspaces of `f` have dimensions adding up to at most `dim W`. -/
theorem vsW_sum_eig_le (hp : p.Prime) {D : ℕ} (W : Submodule (ZMod p) (Fin D → ZMod p))
    (f : Module.End (ZMod p) (Fin D → ZMod p)) :
    ∑ c ∈ Finset.range p, finrank (ZMod p) ↥(W ⊓ f.eigenspace (c : ZMod p)) ≤
      finrank (ZMod p) W := by
  haveI := Fact.mk hp
  have hind : iSupIndep fun μ : ZMod p => W ⊓ f.eigenspace μ :=
    f.eigenspaces_iSupIndep.mono fun μ => inf_le_right
  have hinj : ∀ x ∈ Finset.range p, ∀ y ∈ Finset.range p, (x : ZMod p) = y → x = y := by
    intro x hx y hy hxy
    rw [← ZMod.val_cast_of_lt (Finset.mem_range.mp hx), ← ZMod.val_cast_of_lt (Finset.mem_range.mp hy),
      hxy]
  rw [← Finset.sum_image (f := fun μ : ZMod p => finrank (ZMod p) ↥(W ⊓ f.eigenspace μ)) hinj,
    ← vsW_finrank_biSup hind]
  exact Submodule.finrank_mono (iSup₂_le fun _ _ => inf_le_left)

/-- **An echelon basis has as many vectors as the dimension of its span.** -/
theorem vsWBas_length (hp : p.Prime) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) :
    (vsWBas p us).length = finrank (ZMod p) (vsWSp p d us) := by
  haveI := Fact.mk hp
  have hs : vsWSp p d (vsWBas p us) = Submodule.span (ZMod p)
      (Set.range fun i : Fin (vsWBas p us).length => vsWV p d (vsWBas p us)[i]) := by
    rw [vsWSp]
    congr 1
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, List.getElem_mem i.2, rfl⟩
  rw [← vsWBas_span hp h, hs, finrank_span_eq_card (vsWBas_indep hp h), Fintype.card_fin]

/-- The counting invariant: nonempty bases, with at most `D` vectors in all. -/
def VsWEigCnt (p D : ℕ) (L : List (List (List ℕ))) : Prop :=
  (∀ Q ∈ L, Q ≠ [] ∧ VsWFit p D Q ∧ Q.length = finrank (ZMod p) (vsWSp p D Q)) ∧
    (L.map List.length).sum ≤ D

theorem vsWEigCnt_nil (hp : p.Prime) (D : ℕ) : VsWEigCnt p D (vsFEig0 D) := by
  haveI := Fact.mk hp
  have hl : (vsWId D).length = D := by simp [vsWId]
  have hf : (vsWId D).length = finrank (ZMod p) (vsWSp p D (vsWId D)) := by
    rw [vsWId_span, finrank_top, Module.finrank_fin_fun, hl]
  unfold vsFEig0
  by_cases h : (vsWId D).isEmpty
  · have e : [vsWId D].filter (fun Q => !Q.isEmpty) = [] := by simp [h]
    rw [e]
    exact ⟨fun Q hQ => absurd hQ List.not_mem_nil, by simp⟩
  · have hne : vsWId D ≠ [] := fun h0 => h (by rw [h0]; rfl)
    have e : [vsWId D].filter (fun Q => !Q.isEmpty) = [vsWId D] := by simp [h]
    rw [e]
    refine ⟨fun Q hQ => ?_, by simp [hl]⟩
    rw [List.mem_singleton] at hQ
    subst hQ
    exact ⟨hne, vsWId_fit hp.one_lt D, hf⟩

theorem vsW_filter_ne_sum (l : List (List (List ℕ))) :
    ((l.filter fun Q => !Q.isEmpty).map List.length).sum = (l.map List.length).sum := by
  induction l with
  | nil => rfl
  | cons Q l ih =>
    by_cases h : Q.isEmpty
    · have : Q = [] := List.isEmpty_iff.mp h
      subst this
      simp [ih]
    · simp [h, ih]

/-- One piece splits into pieces with at most as many vectors in all. -/
theorem vsFEigSplit_sum_le (hp : p.Prime) {D : ℕ} {s : List (List ℕ)} (hs : VsWSq p D s)
    {P : List (List ℕ)} (hP : VsWFit p D P) (hPl : P.length = finrank (ZMod p) (vsWSp p D P)) :
    ((vsFEigSplit p D s P).map List.length).sum ≤ P.length := by
  rw [vsFEigSplit, vsW_filter_ne_sum, List.map_map, hPl]
  have he : ∀ c ∈ List.range p, (List.length ∘ fun c => vsWBas p (vsWCut p D P (vsWSubC p c s))) c =
      finrank (ZMod p) ↥(vsWSp p D P ⊓ (vsWLin p D s).eigenspace (c : ZMod p)) := by
    intro c hc
    simp only [Function.comp]
    rw [vsWBas_length hp (vsWCut_fit hp.pos), ← vsWBas_span hp (vsWCut_fit hp.pos),
      vsWSubC_cut hp (List.mem_range.mp hc).le hs hP]
  rw [List.map_congr_left he, vsW_list_sum_range]
  exact vsW_sum_eig_le hp _ _

theorem vsWEigCnt_snoc (hp : p.Prime) {D : ℕ} {s : List (List ℕ)} (hs : VsWSq p D s)
    {L : List (List (List ℕ))} (hI : VsWEigCnt p D L) :
    VsWEigCnt p D (L.flatMap (vsFEigSplit p D s)) := by
  refine ⟨fun Q hQ => ?_, ?_⟩
  · simp only [List.mem_flatMap, vsFEigSplit, List.mem_filter, List.mem_map, List.mem_range,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] at hQ
    obtain ⟨P, -, ⟨c, -, rfl⟩, hne⟩ := hQ
    have hcut : VsWFit p D (vsWCut p D P (vsWSubC p c s)) := vsWCut_fit hp.pos
    refine ⟨hne, vsWBas_fit hp.pos hcut, ?_⟩
    rw [vsWBas_length hp hcut, vsWBas_span hp hcut]
  · obtain ⟨h1, h2⟩ := hI
    refine le_trans ?_ h2
    clear h2
    induction L with
    | nil => simp
    | cons P L ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      have hP := h1 P List.mem_cons_self
      exact Nat.add_le_add (vsFEigSplit_sum_le hp hs hP.2.1 hP.2.2)
        (ih fun Q hQ => h1 Q (List.mem_cons_of_mem _ hQ))

theorem vsFEigL_cnt (hp : p.Prime) {D : ℕ} (Ss : List (List (List ℕ)))
    (hS : ∀ s ∈ Ss, VsWSq p D s) : VsWEigCnt p D (vsFEigL p D Ss) := by
  induction Ss using List.reverseRecOn with
  | nil => exact vsWEigCnt_nil hp D
  | append_singleton T s ih =>
    rw [vsFEigL, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact vsWEigCnt_snoc hp (hS s (by simp)) (ih fun s' hs' => hS s' (by simp [hs']))

/-- A list of nonempty lists has at most as many entries as the sum of their lengths. -/
theorem vsW_length_le_sum {L : List (List (List ℕ))} (h : ∀ Q ∈ L, Q ≠ []) :
    L.length ≤ (L.map List.length).sum := by
  induction L with
  | nil => simp
  | cons Q L ih =>
    have hQ : 0 < Q.length := List.length_pos_iff.mpr (h Q List.mem_cons_self)
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := ih fun Q' hQ' => h Q' (List.mem_cons_of_mem _ hQ')
    omega

theorem vsW_mem_length_le_sum {L : List (List (List ℕ))} {Q : List (List ℕ)} (hQ : Q ∈ L) :
    Q.length ≤ (L.map List.length).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem hQ)

/-- **The pieces are few and small.** -/
theorem vsFEigL_count (hp : p.Prime) {D : ℕ} (Ss : List (List (List ℕ)))
    (hS : ∀ s ∈ Ss, VsWSq p D s) :
    (vsFEigL p D Ss).length ≤ D ∧ ∀ Q ∈ vsFEigL p D Ss, VsWFit p D Q ∧ Q.length ≤ D := by
  obtain ⟨h1, h2⟩ := vsFEigL_cnt hp Ss hS
  exact ⟨(vsW_length_le_sum fun Q hQ => (h1 Q hQ).1).trans h2,
    fun Q hQ => ⟨(h1 Q hQ).2.1, (vsW_mem_length_le_sum hQ).trans h2⟩⟩

end GI.Proved
