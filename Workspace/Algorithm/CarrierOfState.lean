import Workspace.Algorithm.AuxCarrierRect
import Workspace.Algorithm.CarrierKeep
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# The data of Lemma A.30 from the state

Section 5.3: "Suppose a later column action has `q` natural blocks and `q ≤ m`. Couple its even
permutations diagonally to the same permutations of `q` selected rows." This file builds the data
of Lemma A.30 (`CarrierData S L`, `Workspace/Algorithm/AuxCarrierRect.lean`) from what the state
records and what the labels carry:

* the retained rows are a carrier (`CarrierSpec`, the state invariant `CarrierOK`): the row map
  `row : dom → [m]`, the row action `ρ : G → Alt(m)`, the invariant columns, the subgroup `J` of
  the column-fixing elements with `ρ(J) = Alt(m)`, and `M = J ∩ ker ρ` transitive on every cell;
* the labels are natural (`NaturalRows`) and lie above the retained columns: every element of
  `J` has trivial label image (`GiantLabels.Constituent.kills`; Algorithm 5: "Expose the next
  primitive quotient above any retained column partition");
* `q ≤ m` (the state is not in the row case);
* `G` is transitive on its domain.

The data are those of the paper's setup (Section 6, "write the carrier quotient as
`G/M = Alt(m) × Q`"; Section A.4: "`G/J ≅ Q`, and the `J`-orbits are the columns `[m] × C`"):

* `𝒞` is the set of columns met by the domain, and `Q` is the image of `G` on `𝒞`;
* `π = (ρ, column action) : G|_dom ↠ Alt(m) × Q`. It is onto because `J` carries every even row
  permutation and acts trivially on `𝒞`. Its kernel is `M`, whose orbits are the cells
  `row × column` (`label_fibers`), all of the same size since `G` is transitive;
* `Q' = Q` and `𝒞' = 𝒞`: the current orbit is the whole of `[m] × 𝒞` (`above`);
* `ψ : Q ↠ Alt(q)` is the label map, which factors through the column action because `J` has
  trivial label image. The parts are the label fibers of the columns: the labels are constant on
  a column because `J` is transitive on it;
* the chosen rows are the first `q` rows.

So the column giant `ψ` is the label map on all of `G`, and in particular on the diagonal
preimage (`link`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Carrier

variable {Ω C : Type} {S : State Ω C}

namespace State

/-- A homomorphism of `G` that kills the elements fixing the domain pointwise factors through
the faithful image `G|_dom`. -/
noncomputable def domLift {H : Type*} [Group H] (φ : S.G →* H)
    (h : ∀ g, S.domHom g = 1 → φ g = 1) : S.domGroup →* H :=
  S.domHom.rangeRestrict.liftOfRightInverse
    (Function.surjInv S.domHom.rangeRestrict_surjective)
    (Function.rightInverse_surjInv S.domHom.rangeRestrict_surjective)
    ⟨φ, fun g hg => by
      rw [MonoidHom.mem_ker] at hg ⊢
      exact h g (by simpa using congrArg Subtype.val hg)⟩

theorem domLift_spec {H : Type*} [Group H] (φ : S.G →* H) (h : ∀ g, S.domHom g = 1 → φ g = 1)
    (g : S.G) : S.domLift φ h ⟨S.domHom g, g, rfl⟩ = φ g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

theorem domGroup_elim (x : S.domGroup) : ∃ g : S.G, x = ⟨S.domHom g, g, rfl⟩ := by
  obtain ⟨g, hg⟩ := x.2
  exact ⟨g, Subtype.ext hg.symm⟩

end State

namespace CarrierOfState

/-- The columns met by the domain. -/
abbrev Col (S : State Ω C) (c : Setoid Ω) : Type := Quotient (c.comap (Subtype.val : S.dom → Ω))

/-- The column of a point of the domain. -/
def col (c : Setoid Ω) (v : S.dom) : Col S c := Quotient.mk _ v

theorem col_eq_iff {c : Setoid Ω} {v w : S.dom} : col c v = col c w ↔ c.r v.1 w.1 :=
  Quotient.eq

theorem dom_mem (g : S.G) {v : Ω} (hv : v ∈ S.dom) : (g : Perm Ω) v ∈ S.dom :=
  (S.dom_inv g.1 g.2 v).2 hv

variable {m : ℕ} {rows c : Setoid Ω} {row : Ω → Fin m} {ρ : S.G →* alternatingGroup (Fin m)}
  (hs : CarrierSpec S.G S.dom m rows c row ρ)

/-! ### The column action -/

/-- The action of `G` on the columns. -/
noncomputable def colHom : S.G →* Perm (Col S c) where
  toFun g := Quotient.congr (S.domHom g) (fun a b => (hs.cols_inv g g.2 a.1 a.2 b.1 b.2).symm)
  map_one' := by
    ext x
    induction x using Quotient.inductionOn with
    | h a => simp [Quotient.congr_mk]
  map_mul' g k := by
    ext x
    induction x using Quotient.inductionOn with
    | h a => simp [Quotient.congr_mk]

theorem colHom_col (g : S.G) (v : S.dom) : colHom hs g (col c v) = col c (S.domHom g v) := rfl

include hs in
/-- An element acts trivially on the columns exactly when it fixes every column. -/
theorem colHom_eq_one_iff (g : S.G) : colHom hs g = 1 ↔ FixesCols c S.dom g := by
  constructor
  · intro h v hv
    have := congrArg (fun p : Perm (Col S c) => p (col c ⟨v, hv⟩)) h
    simp only [colHom_col, Perm.one_apply] at this
    exact col_eq_iff.1 this
  · intro h
    ext x
    induction x using Quotient.inductionOn with
    | h a =>
      change col c (S.domHom g a) = col c a
      exact col_eq_iff.2 (h a.1 a.2)

include hs in
theorem rho_dom (g : S.G) (hg : S.domHom g = 1) : ρ g = 1 := by
  apply Subtype.ext
  ext i
  obtain ⟨v, hv, rfl⟩ := hs.row_onto i
  have hgv : (g : Perm Ω) v = v := by
    have := congrArg (fun p : Perm S.dom => (p ⟨v, hv⟩ : Ω)) hg
    simpa using this
  have := hs.row_equivariant g v hv
  rw [hgv] at this
  simp [← this]

theorem colr_dom (g : S.G) (hg : S.domHom g = 1) : (colHom hs).rangeRestrict g = 1 := by
  apply Subtype.ext
  ext x
  induction x using Quotient.inductionOn with
  | h a =>
    change col c (S.domHom g a) = col c a
    rw [hg]
    rfl

/-! ### Moving inside the carrier -/

include hs in
/-- `Alt(m)` is transitive on the rows (`m ≥ 3`). -/
theorem exists_alt (i j : Fin m) : ∃ a : alternatingGroup (Fin m), (a : Perm (Fin m)) i = j := by
  haveI := _root_.alternatingGroup.isPretransitive_of_three_le_card (α := Fin m)
    (by simpa using hs.three_le)
  exact MulAction.exists_smul_eq (alternatingGroup (Fin m)) i j

include hs in
/-- `J` moves a point to any row inside its column. -/
theorem move_row {v : Ω} (hv : v ∈ S.dom) (i : Fin m) :
    ∃ j : S.G, FixesCols c S.dom j ∧ row ((j : Perm Ω) v) = i := by
  obtain ⟨a, ha⟩ := exists_alt hs (row v) i
  obtain ⟨j, hj, hf⟩ := hs.indep a
  exact ⟨j, hf, by rw [hs.row_equivariant j v hv, hj, ha]⟩

include hs in
/-- **`J` is transitive on every column.** -/
theorem same_col {v w : Ω} (hv : v ∈ S.dom) (hw : w ∈ S.dom) (h : c.r v w) :
    ∃ k : S.G, FixesCols c S.dom k ∧ (k : Perm Ω) v = w := by
  obtain ⟨j, hf, hj⟩ := move_row hs hv (row w)
  obtain ⟨g, -, hg, hgv⟩ := hs.cells _ (dom_mem j hv) w hw hj (c.iseqv.trans (hf v hv) h)
  refine ⟨g * j, ?_, ?_⟩
  · exact FixesCols.mul S.dom_inv j.2 hg hf
  · change (g : Perm Ω) ((j : Perm Ω) v) = w
    exact hgv

/-! ### The labels -/

variable {L : GiantLabels S} {label : Ω → Fin L.q} (hnat : NaturalRows S L label)
  (hkill : ∀ g : S.G, FixesCols c S.dom g → L.π g = 1)

include hs hnat hkill in
/-- The labels are constant on every column. -/
theorem label_col {v w : Ω} (hv : v ∈ S.dom) (hw : w ∈ S.dom) (h : c.r v w) :
    label v = label w := by
  obtain ⟨k, hk, hkv⟩ := same_col hs hv hw h
  exact (hnat.fibers v hv w hw).2 ⟨k, hkill k hk, hkv⟩

/-- The column giant: the label map on the image of `G` on the columns. -/
noncomputable def psi0 : (colHom hs).range →* alternatingGroup (Fin L.q) :=
  (colHom hs).rangeRestrict.liftOfRightInverse
    (Function.surjInv (colHom hs).rangeRestrict_surjective)
    (Function.rightInverse_surjInv (colHom hs).rangeRestrict_surjective)
    ⟨L.π, fun g hg => by
      rw [MonoidHom.mem_ker] at hg ⊢
      exact hkill g ((colHom_eq_one_iff hs g).1 (by simpa using congrArg Subtype.val hg))⟩

theorem psi0_spec (g : S.G) : psi0 hs hkill ((colHom hs).rangeRestrict g) = L.π g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

/-- The part of a column: its label. -/
noncomputable def part : Col S c → Fin L.q :=
  Quotient.lift (fun v : S.dom => label v.1) fun a b h => label_col hs hnat hkill a.2 b.2 h

theorem part_col (v : S.dom) : part hs hnat hkill (col c v) = label v.1 := rfl

/-! ### The data of Lemma A.30 -/

/-- The map `π = (ρ, column action)` on `G|_dom`. -/
noncomputable def piD : S.domGroup →* alternatingGroup (Fin m) × (colHom hs).range :=
  (S.domLift ρ (rho_dom hs)).prod (S.domLift (colHom hs).rangeRestrict (colr_dom hs))

theorem piD_spec (g : S.G) :
    piD hs ⟨S.domHom g, g, rfl⟩ = (ρ g, (colHom hs).rangeRestrict g) := by
  simp only [piD, MonoidHom.prod_apply, State.domLift_spec]

/-- The cell of a point: its row and its column. -/
def lab (row : Ω → Fin m) (c : Setoid Ω) (v : S.dom) : Fin m × Col S c := (row v.1, col c v)

theorem lab_smul (x : S.domGroup) (v : S.dom) :
    lab row c (x • v) = ((piD hs x).1 • (lab row c v).1, (piD hs x).2 • (lab row c v).2) := by
  obtain ⟨g, rfl⟩ := State.domGroup_elim x
  rw [piD_spec]
  refine Prod.ext ?_ ?_
  · exact hs.row_equivariant g v.1 v.2
  · rfl

include hs in
theorem lab_congr (x : S.domGroup) {v w : S.dom} (h : lab row c v = lab row c w) :
    lab row c (x • v) = lab row c (x • w) := by
  rw [lab_smul hs, lab_smul hs, h]

include hs in
theorem lab_card_eq (x : S.domGroup) (v : S.dom) :
    Nat.card {w : S.dom // lab row c w = lab row c v} =
      Nat.card {w : S.dom // lab row c w = lab row c (x • v)} :=
  Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm x) fun w => by
    constructor
    · exact lab_congr hs x
    · intro h
      have := lab_congr hs x⁻¹ h
      simpa only [MulAction.toPerm_apply, inv_smul_smul] using this)

include hs in
theorem lab_onto : Function.Surjective (lab (S := S) row c) := by
  rintro ⟨i, C⟩
  induction C using Quotient.inductionOn with
  | h w =>
    obtain ⟨j, hf, hj⟩ := move_row hs w.2 i
    refine ⟨⟨_, dom_mem j w.2⟩, Prod.ext hj ?_⟩
    exact col_eq_iff.2 (hf w.1 w.2)

include hs in
theorem dom_nonempty : Nonempty S.dom := by
  obtain ⟨v, hv, -⟩ := hs.row_onto ⟨0, by have := hs.three_le; omega⟩
  exact ⟨⟨v, hv⟩⟩

/-- A base point of the domain. -/
noncomputable def base : S.dom := (dom_nonempty hs).some

/-- The part fibers have equal size: a part map that commutes with the action. -/
theorem part_card_eq (z : (colHom hs).range) (j : Fin L.q) :
    Nat.card {C : (Set.univ : Set (Col S c)) // part hs hnat hkill C.1 = j} =
      Nat.card {C : (Set.univ : Set (Col S c)) //
        part hs hnat hkill C.1 = psi0 hs hkill z • j} := by
  obtain ⟨g, hg⟩ := z.2
  have hz : z = (colHom hs).rangeRestrict g := Subtype.ext hg.symm
  subst hz
  rw [psi0_spec]
  have key : ∀ C : Col S c, part hs hnat hkill (colHom hs g C) = L.π g • part hs hnat hkill C := by
    intro C
    induction C using Quotient.inductionOn with
    | h a =>
      change label ((g : Perm Ω) a.1) = (L.π g : Perm (Fin L.q)) (label a.1)
      exact hnat.equivariant g a.1 a.2
  refine Nat.card_congr (Equiv.subtypeEquiv
    ((Equiv.Set.univ _).trans ((colHom hs g).trans (Equiv.Set.univ _).symm)) fun C => ?_)
  change part hs hnat hkill C.1 = j ↔ part hs hnat hkill (colHom hs g C.1) = L.π g • j
  rw [key]
  exact (smul_left_cancel_iff (L.π g)).symm

variable [Finite Ω]

/-- **The data of Lemma A.30** for the domain action. -/
noncomputable def data (hqm : L.q ≤ m) (htr : S.Transitive) :
    Data S.domGroup S.dom (colHom hs).range (Col S c) m L.q where
  π := piD hs
  π_onto := by
    rintro ⟨a, z⟩
    obtain ⟨g₀, hg₀⟩ := z.2
    obtain ⟨j, hj, hf⟩ := hs.indep (a * (ρ g₀)⁻¹)
    refine ⟨⟨S.domHom (j * g₀), j * g₀, rfl⟩, ?_⟩
    rw [piD_spec]
    have hj1 : (colHom hs).rangeRestrict j = 1 :=
      Subtype.ext ((colHom_eq_one_iff hs j).2 hf)
    refine Prod.ext ?_ ?_
    · change ρ (j * g₀) = a
      rw [map_mul, hj, inv_mul_cancel_right]
    · change (colHom hs).rangeRestrict (j * g₀) = z
      rw [map_mul, hj1, one_mul]
      exact Subtype.ext hg₀
  label := lab row c
  label_onto := lab_onto hs
  label_equivariant := lab_smul hs
  label_fibers x y := by
    constructor
    · intro h
      have hr : row x.1 = row y.1 := congrArg Prod.fst h
      have hc : c.r x.1 y.1 := col_eq_iff.1 (congrArg Prod.snd h)
      obtain ⟨g, hg1, hf, hgv⟩ := hs.cells x.1 x.2 y.1 y.2 hr hc
      refine ⟨⟨S.domHom g, g, rfl⟩, ?_, Subtype.ext hgv⟩
      rw [piD_spec, hg1]
      exact Prod.ext rfl (Subtype.ext ((colHom_eq_one_iff hs g).2 hf))
    · rintro ⟨k, hk, rfl⟩
      rw [lab_smul hs, hk]
      rfl
  u := Nat.card {w : S.dom // lab row c w = lab row c (base hs)}
  label_card l := by
    obtain ⟨w, rfl⟩ := lab_onto hs l
    obtain ⟨g, hg, hgw⟩ := htr _ (base hs).2 w.1 w.2
    have hx : (⟨S.domHom ⟨g, hg⟩, ⟨g, hg⟩, rfl⟩ : S.domGroup) • base hs = w := Subtype.ext hgw
    rw [lab_card_eq hs ⟨S.domHom ⟨g, hg⟩, ⟨g, hg⟩, rfl⟩ (base hs), hx]
  Q' := ⊤
  C' := Set.univ
  preserved _ _ _ _ := trivial
  ψ := (psi0 hs hkill).comp (⊤ : Subgroup (colHom hs).range).subtype
  ψ_onto a := by
    obtain ⟨g, rfl⟩ := L.π_surj a
    exact ⟨⟨(colHom hs).rangeRestrict g, trivial⟩, psi0_spec hs hkill g⟩
  part C := part hs hnat hkill C.1
  part_onto i := by
    obtain ⟨v, hv, rfl⟩ := hnat.onto i
    exact ⟨⟨col c ⟨v, hv⟩, trivial⟩, rfl⟩
  part_equivariant z C := by
    obtain ⟨g, hg⟩ := z.1.2
    have hz : z.1 = (colHom hs).rangeRestrict g := Subtype.ext hg.symm
    change part hs hnat hkill ((z.1 : Perm (Col S c)) C.1) = psi0 hs hkill z.1 • _
    rw [hz, psi0_spec]
    obtain ⟨C, -⟩ := C
    induction C using Quotient.inductionOn with
    | h a =>
      change label ((g : Perm Ω) a.1) = (L.π g : Perm (Fin L.q)) (label a.1)
      exact hnat.equivariant g a.1 a.2
  part_fibers C C' h := by
    obtain ⟨C, hC⟩ := C
    obtain ⟨C', hC'⟩ := C'
    obtain ⟨a, rfl⟩ := Quotient.exists_rep C
    obtain ⟨b, rfl⟩ := Quotient.exists_rep C'
    obtain ⟨k, hk1, hkv⟩ := (hnat.fibers a.1 a.2 b.1 b.2).1 h
    refine ⟨⟨(colHom hs).rangeRestrict k, trivial⟩, ?_, ?_⟩
    · change psi0 hs hkill ((colHom hs).rangeRestrict k) = 1
      rw [psi0_spec, hk1]
    · change col c (S.domHom k a) = col c b
      exact congrArg (col c) (Subtype.ext hkv)
  r := Nat.card {C : (Set.univ : Set (Col S c)) //
    part hs hnat hkill C.1 = label (base hs).1}
  part_card j := by
    obtain ⟨w, hw, rfl⟩ := hnat.onto j
    obtain ⟨g, hg, hgw⟩ := htr _ (base hs).2 w hw
    have h1 : psi0 hs hkill ((colHom hs).rangeRestrict ⟨g, hg⟩) • label (base hs).1 = label w := by
      rw [psi0_spec, ← hgw]
      exact (hnat.equivariant ⟨g, hg⟩ _ (base hs).2).symm
    rw [← h1]
    exact (part_card_eq hs hnat hkill _ _).symm
  rows := Fin.castLEEmb hqm

end CarrierOfState

open CarrierOfState in
/-- **The data of Lemma A.30 from a carrier and natural labels above the columns.** -/
noncomputable def CarrierData.ofSpec [Finite Ω] {L : GiantLabels S} {m : ℕ} {rows c : Setoid Ω}
    {row : Ω → Fin m} {ρ : S.G →* alternatingGroup (Fin m)}
    (hs : CarrierSpec S.G S.dom m rows c row ρ) {label : Ω → Fin L.q}
    (hnat : NaturalRows S L label) (hkill : ∀ g : S.G, FixesCols c S.dom g → L.π g = 1)
    (hqm : L.q ≤ m) (htr : S.Transitive) : CarrierData S L where
  Q := (colHom hs).range
  𝒞 := Col S c
  fin := Fintype.ofFinite _
  m := m
  d := data hs hnat hkill hqm htr
  link g hg := by
    change psi0 hs hkill ((piD hs ⟨S.domHom g, g, rfl⟩).2) = L.π g
    rw [piD_spec, psi0_spec]
  above _ := trivial

/-- **The data of Lemma A.30 from the state** (Section 5.3): the retained record `R` has degree
`m ≥ q`; its rows are a carrier (the state invariant `CarrierOK`), and the natural labels lie
above its columns (`hkill`). -/
noncomputable def CarrierData.ofState [Finite Ω] {L : GiantLabels S} (htr : S.Transitive)
    (hkill : ∀ R c, S.rows = some R → R.cols = some c → ∀ g : S.G, FixesCols c S.dom g →
      L.π g = 1)
    (hnat : ∃ label, NaturalRows S L label) {R : RowRecord Ω} (hR : S.rows = some R)
    (hqm : L.q ≤ R.m) : CarrierData S L :=
  have hc := S.carrier R hR
  have hspec := hc.choose_spec.2.1.choose_spec.choose_spec
  CarrierData.ofSpec hspec hnat.choose_spec (hkill R _ hR hc.choose_spec.1) hqm htr

end GI.Algorithm
