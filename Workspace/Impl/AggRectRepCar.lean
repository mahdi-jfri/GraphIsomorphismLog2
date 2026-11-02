import Workspace.Impl.AggRectRepRow

/-!
# The carrier case read by the program

Lemma A.30 for single labels: "Choose `q` row labels and identify them with `[q]`. … Take its
full preimage `D̃` in `G`. … Restrict further to the inverse image of the setwise stabilizer of
`W` and `R` in `Alt(q)`, then select the physical orbit above `W × R`."

The representation is `RectRep.ofCarrier` for the data of Lemma A.30 built from the state
(`CarrierData.ofSpec`), with two choices made explicit so that a program can compute them:

* the rows are numbered by `rcRRow` (keys in increasing order), a carrier by
  `rcR_carrierSpec`, with row action `ρ` (`rcRRho`); the chosen rows are the first `q`;
* the labels are the natural labels of the kernel-orbit quotient on single labels
  (`rcRLab`).

`rcR_car_code`: the cell code of a position `v` of the domain is `1 + row(v) q + label(v)` when
`row(v) < q`, `row(v) ∈ W` and `label(v) ∈ R`, and `0` otherwise.

`rcR_car_memH`: `h` lies in the group of the query exactly when `h ∈ G`, `π(h) ∈ P` and
`ρ(h) = π(h)` on the first `q` rows (and `ρ(h)` fixes the other rows).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Carrier

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-! ### The natural labels -/

section Labels

variable {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) (hq : 0 < L.q)
  (f : KernelQuotient πd S.dom (Fin L.q))

/-- The natural label of a position: the value of the one-label quotient. -/
noncomputable def rcRLab (v : Ω) : Fin L.q :=
  open Classical in if hv : v ∈ S.dom then f.map ⟨v, hv⟩ else ⟨0, hq⟩

include hπ in
/-- The natural labels are natural rows (as in `naturalRows_of`). -/
theorem rcR_natRows : NaturalRows S L (rcRLab hq f) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro g v hv
    have hv' : (g : Perm Ω) v ∈ S.dom := (S.dom_inv g.1 g.2 v).2 hv
    simp only [rcRLab, dif_pos hv, dif_pos hv']
    exact kq_map_apply hπ f g hv
  · intro i
    obtain ⟨x, hx⟩ := f.onto i
    exact ⟨x.1, x.2, by simp only [rcRLab, dif_pos x.2]; exact hx⟩
  · intro v hv w hw
    simp only [rcRLab, dif_pos hv, dif_pos hw]
    rw [f.kernel_fibers]
    constructor
    · rintro ⟨k, hk1, hkv⟩
      obtain ⟨g, rfl⟩ := State.domGroup_elim k
      refine ⟨g, by rw [← hπ]; exact hk1, ?_⟩
      exact congrArg Subtype.val hkv
    · rintro ⟨g, hg1, hgv⟩
      refine ⟨⟨S.domHom g, g, rfl⟩, by rw [hπ]; exact hg1, Subtype.ext ?_⟩
      exact hgv

end Labels

/-! ### The carrier data -/

section Data

variable [Finite Ω] {k : ℕ} (e : Ω ≃ Fin k) (I : AggregationData P₀ S L)
  (hlam : (S.N : ℝ) ^ P₀.α < L.q) (f : KernelQuotient I.πd S.dom (Fin L.q))

include I in
theorem rcR_q_pos : 0 < L.q := by have := I.q_ten; omega

/-- The retained record, of degree at least `q`. -/
theorem rcR_rows (hlam : (S.N : ℝ) ^ P₀.α < L.q) (f : KernelQuotient I.πd S.dom (Fin L.q)) :
    ∃ R, S.rows = some R ∧ L.q ≤ R.m :=
  I.rows_fit hlam ⟨_, rcR_natRows I.πd_spec (rcR_q_pos I) f⟩

/-- The record. -/
noncomputable def rcRRec : RowRecord Ω := (rcR_rows I hlam f).choose

theorem rcR_rec_spec : S.rows = some (rcRRec I hlam f) ∧ L.q ≤ (rcRRec I hlam f).m :=
  (rcR_rows I hlam f).choose_spec

/-- The column partition of the record. -/
noncomputable def rcRCols : Setoid Ω :=
  (S.carrier (rcRRec I hlam f) (rcR_rec_spec I hlam f).1).choose

theorem rcR_cols_spec : (rcRRec I hlam f).cols = some (rcRCols I hlam f) ∧
    (∃ row ρ, CarrierSpec S.G S.dom (rcRRec I hlam f).m (rcRRec I hlam f).rows
      (rcRCols I hlam f) row ρ) :=
  ⟨(S.carrier _ (rcR_rec_spec I hlam f).1).choose_spec.1,
    (S.carrier _ (rcR_rec_spec I hlam f).1).choose_spec.2.1⟩

/-- The carrier of some numbering of the rows. -/
theorem rcR_spec0 : CarrierSpec S.G S.dom (rcRRec I hlam f).m (rcRRec I hlam f).rows
    (rcRCols I hlam f) (rcR_cols_spec I hlam f).2.choose
    (rcR_cols_spec I hlam f).2.choose_spec.choose :=
  (rcR_cols_spec I hlam f).2.choose_spec.choose_spec

theorem rcR_m_pos : 0 < (rcRRec I hlam f).m := by
  have := (rcR_spec0 I hlam f).three_le; omega

/-- The row numbers of the program. -/
noncomputable def rcRRowN : Ω → Fin (rcRRec I hlam f).m :=
  rcRRow e S.dom (rcRRec I hlam f).rows (rcR_m_pos I hlam f)

/-- The row action for these numbers. -/
noncomputable def rcRRhoN : S.G →* alternatingGroup (Fin (rcRRec I hlam f).m) :=
  rcRRho e (rcR_spec0 I hlam f) (rcR_m_pos I hlam f)

theorem rcR_specN : CarrierSpec S.G S.dom (rcRRec I hlam f).m (rcRRec I hlam f).rows
    (rcRCols I hlam f) (rcRRowN e I hlam f) (rcRRhoN e I hlam f) :=
  rcR_carrierSpec (rcR_spec0 I hlam f) (rcR_m_pos I hlam f) fun g hg v hv =>
    (S.dom_inv g hg v).2 hv

/-- **The data of Lemma A.30** with the program's row numbers and labels. -/
noncomputable def rcRCarD : CarrierData S L :=
  CarrierData.ofSpec (rcR_specN e I hlam f) (rcR_natRows I.πd_spec (rcR_q_pos I) f)
    (I.con.kills _ _ (rcR_rec_spec I hlam f).1 (rcR_cols_spec I hlam f).1)
    (rcR_rec_spec I hlam f).2 I.htr

/-! ### The cells -/

variable {W R : Finset (Fin L.q)}

/-- The code of the cell of a position of the domain in the carrier case. -/
def rcRCarCode {m : ℕ} (W R : Finset (Fin L.q)) (row : Fin m) (lab : Fin L.q) : ℕ :=
  if h : (row : ℕ) < L.q then
    (if (⟨row, h⟩ : Fin L.q) ∈ W ∧ lab ∈ R then 1 + (row : ℕ) * L.q + lab else 0)
  else 0

theorem rcR_car_cellD {v : Ω} (hv : v ∈ S.dom) :
    ((rcRCarD e I hlam f).d.label ⟨v, hv⟩).1 = rcRRowN e I hlam f v ∧
    ((rcRCarD e I hlam f).d.label ⟨v, hv⟩).2 ∈ (rcRCarD e I hlam f).d.C' := ⟨rfl, trivial⟩

/-- **The cell code in the carrier case.** -/
theorem rcR_car_code {v : Ω} (hv : v ∈ S.dom) :
    rcCellCode ((rcRCarD e I hlam f).cell W R v) =
      rcRCarCode W R (rcRRowN e I hlam f v) (rcRLab (rcR_q_pos I) f v) := by
  classical
  set D := rcRCarD e I hlam f
  set rw := rcRRowN e I hlam f v
  have hrows : ∀ i : Fin L.q, ((D.d.rows i : Fin _) : ℕ) = i := fun i => rfl
  have hlab : (D.d.label ⟨v, hv⟩).1 = rw := rfl
  unfold rcRCarCode
  by_cases hq : (rw : ℕ) < L.q
  · rw [dif_pos hq]
    have hp : (D.d.label ⟨v, hv⟩).1 ∈ Set.range D.d.rows ∧ (D.d.label ⟨v, hv⟩).2 ∈ D.d.C' :=
      ⟨⟨⟨rw, hq⟩, Fin.ext (by rw [hrows, hlab])⟩, trivial⟩
    -- the diagonal cell of `v` is `(row v, label v)`
    have hcell : D.d.cell ⟨⟨v, hv⟩, hp⟩ = (⟨rw, hq⟩, rcRLab (rcR_q_pos I) f v) := by
      refine Prod.ext ?_ ?_
      · apply D.d.rows.injective
        rw [show D.d.cell ⟨⟨v, hv⟩, hp⟩ = (D.d.rowIndex ⟨⟨v, hv⟩, hp⟩, D.d.colPart _) from rfl]
        simp only
        rw [D.d.rows_rowIndex, hlab]
        exact Fin.ext (by rw [hrows])
      · change D.d.colPart ⟨⟨v, hv⟩, hp⟩ = rcRLab (rcR_q_pos I) f v
        rfl
    by_cases hin : (⟨rw, hq⟩ : Fin L.q) ∈ W ∧ rcRLab (rcR_q_pos I) f v ∈ R
    · rw [if_pos hin]
      have : D.cell W R v = some (⟨_, hin.1⟩, ⟨_, hin.2⟩) := by
        rw [D.cell_eq_some hv hp, hcell]; rfl
      rw [this]; rfl
    · rw [if_neg hin]
      have : D.cell W R v = none := by
        rw [D.cell_eq_none hv hp, hcell]
        rintro ⟨⟨w, r⟩, hwr⟩
        have h1 : (w : Fin L.q) = ⟨rw, hq⟩ := congrArg Prod.fst hwr
        have h2 : (r : Fin L.q) = rcRLab (rcR_q_pos I) f v := congrArg Prod.snd hwr
        exact hin ⟨by rw [← h1]; exact w.2, by rw [← h2]; exact r.2⟩
      rw [this]; rfl
  · rw [dif_neg hq]
    have : D.cell W R v = none := by
      refine D.cell_of_not hv fun hp => hq ?_
      obtain ⟨i, hi'⟩ := hp.1
      have := congrArg Fin.val hi'
      rw [hrows, hlab] at this
      rw [← this]; exact i.2
    rw [this]; rfl

theorem rcR_car_off {v : Ω} (hv : v ∉ S.dom) : rcCellCode ((rcRCarD e I hlam f).cell W R v) = 0 := by
  have : (rcRCarD e I hlam f).cell W R v = none := by
    unfold CarrierData.cell; rw [dif_neg hv]
  rw [this]; rfl

/-! ### The group -/

/-- `Alt(q)` on the first `q` rows, as a permutation of the rows. -/
theorem rcR_embed_apply (a : alternatingGroup (Fin L.q)) (j : Fin (rcRCarD e I hlam f).m) :
    (((rcRCarD e I hlam f).d.embedAlt a : alternatingGroup (Fin (rcRCarD e I hlam f).m)) :
      Perm (Fin (rcRCarD e I hlam f).m)) j =
      if h : (j : ℕ) < L.q then Fin.castLE (rcR_rec_spec I hlam f).2 ((a : Perm (Fin L.q)) ⟨j, h⟩)
      else j := by
  split_ifs with h
  · have e1 : j = (rcRCarD e I hlam f).d.rows ⟨j, h⟩ := Fin.ext rfl
    conv_lhs => rw [e1]
    rw [(rcRCarD e I hlam f).d.embedAlt_apply]
    rfl
  · show (Equiv.Perm.viaFintypeEmbedding (a : Perm (Fin L.q)) (rcRCarD e I hlam f).d.rows) j = j
    refine Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ ?_
    rintro ⟨i, hi⟩
    exact h (by rw [← hi]; exact i.2)

/-- **The group of the carrier query**: `h ∈ G` with `π(h) ∈ P` and `ρ(h) = π(h)` on the chosen
rows (the diagonal preimage `D̃` cut down to the side stabilizer). -/
theorem rcR_car_memH {h : Perm Ω} :
    h ∈ (rcRCarD e I hlam f).H W R ↔ ∃ hg : h ∈ S.G, L.π ⟨h, hg⟩ ∈ permitted W R ∧
      rcRRhoN e I hlam f ⟨h, hg⟩ = (rcRCarD e I hlam f).d.embedAlt (L.π ⟨h, hg⟩) := by
  set D := rcRCarD e I hlam f
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨hg, hl⟩ := D.mem_liftD.1 h1
    obtain ⟨hg', hp⟩ := L.mem_lift.1 h2
    refine ⟨hg, hp, ?_⟩
    obtain ⟨z, hz⟩ := (D.d.mem_lift_iff _).1 hl
    replace hz := (CarrierOfState.piD_spec (rcR_specN e I hlam f) ⟨h, hg⟩).symm.trans hz
    have h3 := congrArg Prod.fst hz
    have h4 := congrArg Prod.snd hz
    simp only at h3 h4
    rw [h3]
    congr 1
    show CarrierOfState.psi0 (rcR_specN e I hlam f)
      (I.con.kills _ _ (rcR_rec_spec I hlam f).1 (rcR_cols_spec I hlam f).1) z.1 = _
    rw [← h4, CarrierOfState.psi0_spec]
  · rintro ⟨hg, hp, hρ⟩
    refine ⟨D.mem_liftD.2 ⟨hg, (D.d.mem_lift_iff _).2
      ⟨⟨(CarrierOfState.colHom (rcR_specN e I hlam f)).rangeRestrict ⟨h, hg⟩, trivial⟩, ?_⟩⟩,
      L.mem_lift.2 ⟨hg, hp⟩⟩
    refine (CarrierOfState.piD_spec (rcR_specN e I hlam f) ⟨h, hg⟩).trans ?_
    refine Prod.ext ?_ rfl
    show rcRRhoN e I hlam f ⟨h, hg⟩ = _
    rw [hρ]
    congr 1
    exact (CarrierOfState.psi0_spec (rcR_specN e I hlam f)
      (I.con.kills _ _ (rcR_rec_spec I hlam f).1 (rcR_cols_spec I hlam f).1) ⟨h, hg⟩).symm

end Data

end GI.Impl
