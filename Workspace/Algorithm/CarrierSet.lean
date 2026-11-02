import Workspace.Algorithm.RowSteps
import Workspace.Algorithm.CarrierKeep

/-!
# The column step sets the carrier invariant

Algorithm 4: "Retain the degree-`q` row action and the resulting column partition". The row
record of the column step is `⟨q, rows, some cols⟩`, with the rows the fibers of the natural
labels and the columns `[m] × Δ_j` of Lemma A.14. This file proves that the new state satisfies
the carrier invariant `CarrierOK` (`ColumnStep.carrierOK`), from the data of Theorems A.17 and
A.18 (`RowForm`):

* the row map is the natural label map, and `G` acts on it through `π : G ↠ Alt(q)`;
* the clean complement `s(Alt(q))` fixes every column (it is pure: `s(p)` moves `e(b, i)` to
  `e(b, p i)`), and `π(s(p)) = p` (`indep`; Section A.4: "the clean carrier supplies every element
  of `Alt(m)`");
* the group `M` of Theorem A.18 is transitive on every cell `{i} × Δ_j` (Lemma A.14: "The
  `𝓜`-orbits are `{i} × Δ_j`"), fixes every column and every row (`cells`);
* the columns split the domain, since `N` has `t ≥ 2` orbits (`ColumnPre.proper`);
* the columns are a level of the new hierarchy: they are the coarse end of the row interval
  (`ColumnPre.hier'`: "the lower pieces, then the row interval with the columns as its coarse
  end, then the upper pieces").
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Paper GI.NormalTranspose

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

namespace ColumnPre

variable (I : ColumnPre S L)

theorem cols_r {v w : Ω} (hv : v ∈ S.dom) (hw : w ∈ S.dom) :
    I.cols.r v w ↔ colOf I.e I.Nl ⟨v, hv⟩ = colOf I.e I.Nl ⟨w, hw⟩ :=
  State.domKer_r_of_mem _ hv hw

theorem rowPart_r {v w : Ω} (hv : v ∈ S.dom) (hw : w ∈ S.dom) :
    I.rowPart.r v w ↔ I.label v = I.label w :=
  State.domKer_r_of_mem (fun v : S.dom => I.label v) hv hw

theorem label_e (b : I.B) (i : Fin L.q) : I.label (I.e (b, i)).1 = i := I.e_label b i

/-- An element of `G` that fixes every label acts trivially on the labels. -/
theorem pi_eq_one {g : S.G} (hg : ∀ v ∈ S.dom, I.label ((g : Perm Ω) v) = I.label v) :
    L.π g = 1 := by
  apply Subtype.ext
  ext j
  obtain ⟨v, hv, rfl⟩ := I.natural.onto j
  have := I.natural.equivariant g v hv
  rw [hg v hv] at this
  simp [← this]

/-- **The clean complement fixes every column and realizes every even row permutation.** -/
theorem indep (a : alternatingGroup (Fin L.q)) :
    ∃ g : S.G, L.π g = a ∧ FixesCols I.cols S.dom g := by
  obtain ⟨g, hg⟩ := (I.s a).2
  have hgx : ∀ x : S.dom, ((g : Perm Ω) x.1) = ((I.s a).1 x).1 := fun x => by
    rw [← hg]; rfl
  refine ⟨g, ?_, ?_⟩
  · obtain ⟨v₀, hv₀, -⟩ := I.natural.onto ⟨0, by have := I.four_le; omega⟩
    let b := (I.e.symm ⟨v₀, hv₀⟩).1
    apply Subtype.ext
    ext i
    have h1 := I.natural.equivariant g (I.e (b, i)).1 (I.e (b, i)).2
    rw [hgx, I.pure, label_e, label_e] at h1
    exact congrArg Fin.val h1.symm
  · intro v hv
    have hgv : (g : Perm Ω) v ∈ S.dom := (S.dom_inv g.1 g.2 v).2 hv
    rw [I.cols_r hgv hv]
    have e1 : (⟨(g : Perm Ω) v, hgv⟩ : S.dom) = (I.s a).1 ⟨v, hv⟩ := Subtype.ext (hgx ⟨v, hv⟩)
    rw [e1]
    obtain ⟨⟨b, i⟩, hbi⟩ := I.e.surjective ⟨v, hv⟩
    rw [← hbi, I.pure, colOf_apply, colOf_apply]

/-- **`M` is transitive on every cell**, and its elements fix every row and every column. -/
theorem cells (v : Ω) (hv : v ∈ S.dom) (w : Ω) (hw : w ∈ S.dom) (hl : I.label v = I.label w)
    (hc : I.cols.r v w) :
    ∃ g : S.G, L.π g = 1 ∧ FixesCols I.cols S.dom g ∧ (g : Perm Ω) v = w := by
  haveI : Finite S.dom := Finite.of_equiv _ I.e
  obtain ⟨⟨b, i⟩, hbi⟩ := I.e.surjective ⟨v, hv⟩
  obtain ⟨⟨b', i'⟩, hbi'⟩ := I.e.surjective ⟨w, hw⟩
  have hv' : v = (I.e (b, i)).1 := by rw [hbi]
  have hw' : w = (I.e (b', i')).1 := by rw [hbi']
  have hii : i = i' := by rw [← label_e I b i, ← label_e I b' i', ← hv', ← hw', hl]
  subst hii
  have hcol : colOf I.e I.Nl (I.e (b, i)) = colOf I.e I.Nl (I.e (b', i)) := by
    rw [I.cols_r hv hw] at hc
    rw [hbi, hbi']
    exact hc
  rw [colOf_apply, colOf_apply] at hcol
  have horb : b' ∈ MulAction.orbit I.Nl b := Quotient.exact hcol.symm
  obtain ⟨gd, hgd, hgv⟩ := ((lem_normal_transpose I.pure I.rnf
    (by simpa using I.four_le)).1 b b' i i).2 ⟨rfl, horb⟩
  obtain ⟨g, hg⟩ := gd.2
  have hgx : ∀ x : S.dom, ((g : Perm Ω) x.1) = (gd.1 x).1 := fun x => by rw [← hg]; rfl
  -- the elements of `M` are clean lifts: they fix every row
  obtain ⟨-, y, -, hyg0⟩ := id hgd
  have hyg : cleanLift I.e _ y = gd.val := hyg0
  have hrow : ∀ x ∈ S.dom, I.label ((g : Perm Ω) x) = I.label x := by
    intro x hx
    obtain ⟨⟨c, j⟩, hcj⟩ := I.e.surjective ⟨x, hx⟩
    have hx' : x = (I.e (c, j)).1 := by rw [hcj]
    rw [hx', hgx, ← hyg, cleanLift_apply, label_e, label_e]
  refine ⟨g, I.pi_eq_one hrow, ?_, ?_⟩
  · intro x hx
    have hgx' : (g : Perm Ω) x ∈ S.dom := (S.dom_inv g.1 g.2 x).2 hx
    rw [I.cols_r hgx' hx]
    have e1 : (⟨(g : Perm Ω) x, hgx'⟩ : S.dom) = gd.1 ⟨x, hx⟩ := Subtype.ext (hgx ⟨x, hx⟩)
    rw [e1]
    exact mem_columnFixer_of_M gd hgd ⟨x, hx⟩
  · rw [hv', hgx, hgv, ← hw']

end ColumnPre

/-- **The column step sets the carrier invariant** (Algorithm 4: "Retain the degree-`q` row
action and the resulting column partition"). -/
theorem ColumnStep.carrierOK (I : ColumnStep S L) :
    CarrierOK S.G S.dom (some ⟨L.q, I.rowPart, some I.cols⟩) I.hier' := by
  intro R hR
  cases hR
  refine ⟨I.cols, rfl, ⟨I.label, L.π, ?_⟩, ?_⟩
  · exact
    { three_le := I.three_le
      row_iff := fun v hv w hw => I.rowPart_r hv hw
      row_onto := I.natural.onto
      row_equivariant := fun g v hv => I.natural.equivariant g v hv
      cols_inv := fun g hg v _ w _ => I.cols_inv g hg v w
      two_cols := I.proper
      indep := I.indep
      cells := I.cells }
  · refine ⟨I.split.map Prod.fst ++ [{ I.rowI with part := I.cols }], I.split.map Prod.snd,
      by simp [ColumnPre.hier'], fun v _ w _ => ?_⟩
    unfold hierLevel
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

end GI.Algorithm
