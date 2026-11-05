module

public import Workspace.Impl.VsQProg
public import Workspace.Impl.NIntLib
public import Workspace.Impl.SSWrapProg
public import Workspace.Proved.SSPointwiseStab
public import Workspace.Proved.SSMembership
public import Workspace.Proved.MBlk
public import Workspace.Proved.NClNormal
public import Workspace.Proved.NClDerived
public import Workspace.Proved.SSConstructiveMembership

@[expose] public section

/-!
# The vector stabilizer, given the hard case

`vsQ_vectorStabilizer_of` proves `GI.Cited.VectorStabilizer` from two hypotheses about the
programs of the hard case and of the `Q₈` continuation: they are blocks `extra` placed after ours,
with entry points `hard` and `q8c`, and on every valid state they do what `VsQHardHyp` and
`VsQ8CHyp` say, at costs `CH` and `CQ` that are at most `K (Cφ + 1) (S + 1)^D`. The primitives
are the proved ones.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

/-- The program, with the proved primitives. -/
noncomputable def vsQProgP (hard q8c : ℕ) (extra : List (List Expr)) : Program :=
  vsQProg GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.minimalBlocks GI.Proved.normalClosure
    GI.Proved.derivedSubgroup GI.Proved.constructiveMembership hard q8c extra

/-! ### Cells of the input -/

/-- Values whose cells are at most `M` plus their size plus one. -/
def VsQCB (M : ℕ) (v : Val) : Prop := ∀ a ∈ v.cells, a ≤ M + v.size + 1

theorem vsQCB_list {M : ℕ} {vs : List Val} (h : ∀ v ∈ vs, VsQCB M v) : VsQCB M (.list vs) := by
  intro a ha
  rw [size_eq_length]
  simp only [cells_list, List.length_cons,
    List.cons_append, List.nil_append, List.mem_cons] at ha ⊢
  have hlen := length_le_cellsList vs
  rcases ha with rfl | rfl | rfl | ha
  · omega
  · omega
  · omega
  · obtain ⟨v, hv, ha⟩ := cam_mem_cellsList ha
    have h1 := h v hv a ha
    have h2 : v.size ≤ (Val.cellsList vs).length := by
      rw [length_cellsList]
      exact List.le_sum_of_mem (List.mem_map_of_mem hv)
    omega

theorem vsQCB_nat {M k : ℕ} (hk : k ≤ M) : VsQCB M (.nat k) := by
  intro a ha
  simp [Val.cells] at ha
  rcases ha with rfl | rfl <;> omega

theorem vsQCB_of {M : ℕ} {v : Val} (h : NIntCells v) : VsQCB M v := fun a ha => by
  have := h a ha; omega

theorem vsQCB_vec {p d : ℕ} [NeZero p] (v : Fin d → ZMod p) : VsQCB p (encVec v) := by
  apply vsQCB_list
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨i, -, rfl⟩ := hw
  exact vsQCB_nat (ZMod.val_lt _).le

theorem vsQ_cells (I : VecStabInst) :
    ∀ a ∈ (vsQTaskIn I).cells, a ≤ 2 * ((vsQTaskIn I).size + 1) ^ 1 := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hB : VsQCB I.p (vsQTaskIn I) := by
    apply vsQCB_list
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact vsQCB_of (nint_cells_group _)
    · exact vsQCB_nat le_rfl
    · apply vsQCB_list
      intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨g, -, rfl⟩ := hw
      apply vsQCB_list
      intro u hu
      simp only [List.mem_map] at hu
      obtain ⟨i, -, rfl⟩ := hu
      exact vsQCB_vec _
    · exact vsQCB_vec _
  have hn : I.n ≤ (vsQTaskIn I).size := by
    have h1 : (encPerm (1 : Perm (Fin I.n))).size ≤ (Val.list ((1 :: I.gs).map encPerm)).size :=
      ss_size_le_list (by simp)
    have h2 : (Val.list ((1 :: I.gs).map encPerm)).size ≤ (encGroup I.gs).size :=
      ss_size_le_list (by simp)
    have h3 : (encGroup I.gs).size ≤ (vsQTaskIn I).size := ss_size_le_list (by simp)
    have h4 := cam_encPerm_size (1 : Perm (Fin I.n))
    rw [← size_eq_length] at h4
    omega
  intro a ha
  have := hB a ha
  have := I.p_le
  rw [pow_one]
  omega

/-! ### The hypotheses on the hard case -/

/-- The hard case and the `Q₈` continuation do their job on every valid state, at costs `CH`
and `CQ`. -/
def VsQHQ (P : Program) (phi hard q8c : ℕ) (CH CQ : ℕ → VecStabInst → ℕ → ℕ) : Prop :=
  ∀ (I : VecStabInst) [Fact I.p.Prime] (Cφ S Tm : ℕ),
    (∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ) →
    VsQDSz I S Tm → (I.d + 1) ^ 278 ≤ Tm → ∀ (s : VsQSt I) (hs : VsQStOK s),
    VsQHardHyp P hard (CH Cφ I S) Tm hs ∧ VsQ8CHyp P q8c (CQ Cφ I S) Tm hs

/-- A polynomial bound on a cost of the hard part. -/
def VsQCostBd (C : ℕ → VecStabInst → ℕ → ℕ) : Prop :=
  ∃ K D : ℕ, ∀ (Cφ : ℕ) (I : VecStabInst) (S : ℕ), I.n + 1 ≤ S → C Cφ I S ≤ K * (Cφ + 1) * (S + 1) ^ D

variable {I : VecStabInst} in
theorem VsQHardHyp.mono [Fact I.p.Prime] {P : Program} {hard C C' Tm : ℕ} {s : VsQSt I} {hs : VsQStOK s}
    (h : VsQHardHyp P hard C Tm hs) (hC : C ≤ C') : VsQHardHyp P hard C' Tm hs :=
  fun as Lb ccs tcs ys r hH hn => (h as Lb ccs tcs ys r hH hn).mono fun _ _ hw => ⟨hw.1, hw.2.trans hC⟩

variable {I : VecStabInst} in
theorem VsQ8CHyp.mono [Fact I.p.Prime] {P : Program} {q8c C C' Tm : ℕ} {s : VsQSt I} {hs : VsQStOK s}
    (h : VsQ8CHyp P q8c C Tm hs) (hC : C ≤ C') : VsQ8CHyp P q8c C' Tm hs :=
  fun as Lb ccs tcs ys r Lo ks hH hn hL hk hl hLo hK0 =>
    (h as Lb ccs tcs ys r Lo ks hH hn hL hk hl hLo hK0).mono fun _ _ hw => ⟨hw.1, hw.2.trans hC⟩

/-- **The vector stabilizer, given the hard case and the `Q₈` continuation.** -/
theorem vsQ_vectorStabilizer_of (hard q8c : ℕ) (extra : List (List Expr))
    (CH CQ : ℕ → VecStabInst → ℕ → ℕ) (hCH : VsQCostBd CH) (hCQ : VsQCostBd CQ)
    (HQ : VsQHQ (vsQProgP hard q8c extra) (vsQIdx hard q8c).phi.phi hard q8c CH CQ) :
    GI.Cited.VectorStabilizer := by
  obtain ⟨KH, DH, hH⟩ := hCH
  obtain ⟨KQ, DQ, hQ⟩ := hCQ
  have L := vsQLay GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.minimalBlocks
    GI.Proved.normalClosure GI.Proved.derivedSubgroup GI.Proved.constructiveMembership hard q8c extra
  obtain ⟨K, D, hKD⟩ := vsQTot_poly GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.minimalBlocks
    GI.Proved.normalClosure GI.Proved.derivedSubgroup GI.Proved.constructiveMembership KH DH KQ DQ
  refine polyTimeAt_ofVal_of_lang_cells (vsQProgP hard q8c extra) (vsQIdx hard q8c).top.top K D 2 1
    vsQ_cells (fun I => ?_)
  have hall := vsQAll_spec L (CH := fun Cφ _ S => KH * (Cφ + 1) * (S + 1) ^ DH)
    (CQ := fun Cφ _ S => KQ * (Cφ + 1) * (S + 1) ^ DQ) (fun I _ Cφ S Tm hφ hS hTm s hs => by
      have h := HQ I Cφ S Tm hφ hS hTm s hs
      exact ⟨h.1.mono (hH Cφ I S hS.n), h.2.mono (hQ Cφ I S hS.n)⟩) I
  refine hall.mono fun w c hw => ⟨hw.1, hw.2.trans (hKD I _ (vsQ_in_sizes I).1)⟩

end GI.Impl
