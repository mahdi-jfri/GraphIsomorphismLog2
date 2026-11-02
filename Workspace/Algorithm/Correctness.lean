import Workspace.Algorithm.Procedure

/-!
# Exactness of every case (the steps of the proof of Lemma 6.1)

`Run.exact`: every run returns the exact answer of its state, and `Exec.exact`:
every script run returns `evalExact`. The proof is by induction on the run, one
case per constructor. The induction hypothesis is the paper's "assuming exact
answers to the recursive calls"; the one-step form is
`GI.Paper.lem_main_correctness`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm
open scoped Pointwise

variable {P : Params}

/-! ### One step of each case, from exact child answers -/

section Steps

variable {Ω C : Type}

theorem step_fresh {S S' : State Ω C} {A : Set (Perm Ω)} (hcore : S.SameCore S')
    (ih : A = S'.answer) : A = S.answer := by
  rw [ih, State.answer_of_sameCore hcore]

/-- A fresh phase: the lift of the answer on the faithful image is the answer of `S`
(`answer_restrict_image`). -/
theorem step_freshPhase {S : State Ω C} {S' : State S.dom C} {A : Set (Perm S.dom)}
    (hS' : S.FreshOf S') (ih : A = S'.answer) : S.liftAnswer A = S.answer := by
  rw [ih, hS'.liftAnswer_answer]

/-- The orbit chain stops: the largest orbit has no isomorphism. -/
theorem step_orbitStop {S S₁ : State Ω C} {D₁ : Set Ω} (hD₁ : S.LargestOrbit D₁)
    (h₁ : S₁.Inst S.G D₁ S.x S.y) (ih : (∅ : Set (Perm Ω)) = S₁.answer) :
    (∅ : Set (Perm Ω)) = S.answer := by
  rw [State.answer_of_inst h₁] at ih
  exact (answer_orbit_chain_empty hD₁.subset ih.symm).symm

/-- The orbit chain rule. -/
theorem step_orbitChain {S S₁ S₂ : State Ω C} {D₁ : Set Ω} {A₁ A₂ : Set (Perm Ω)}
    (hD₁ : S.LargestOrbit D₁) (h₁ : S₁.Inst S.G D₁ S.x S.y) (t : Perm Ω) (ht : t ∈ A₁)
    (h₂ : S₂.Inst (autGroup S.G D₁ hD₁.invariant S.x) (S.dom \ D₁) S.x (S.y ∘ t))
    (ih₁ : A₁ = S₁.answer) (ih₂ : A₂ = S₂.answer) : t • A₂ = S.answer := by
  rw [ih₁, State.answer_of_inst h₁] at ht
  rw [ih₂, State.answer_of_inst h₂]
  exact (answer_orbit_chain hD₁.invariant hD₁.subset ht).symm

/-- A coset enumeration: the dispatcher reduction and the normalization. -/
theorem step_cosets {S : State Ω C} {n : ℕ} {K : Subgroup (Perm Ω)} (τ : Fin n → Perm Ω)
    (hτ : ∀ j, τ j ∈ S.G) (hK : K ≤ S.G)
    (hcov : (S.G : Set (Perm Ω)) ⊆ ⋃ j, τ j • (K : Set (Perm Ω)))
    (child : Fin n → State Ω C) (hchild : ∀ j, (child j).Inst K S.dom S.x (S.y ∘ τ j))
    (A : Fin n → Set (Perm Ω)) (ih : ∀ j, A j = (child j).answer) :
    (⋃ j, τ j • A j) = S.answer := by
  simp_rw [ih, fun j => State.answer_of_inst (hchild j)]
  exact answer_cosets τ hτ hK hcov

/-- A representative of a coset `ρ H` gives the same coset. -/
theorem smul_coset_eq {ρ τ : Perm Ω} {H : Subgroup (Perm Ω)}
    (h : τ ∈ ρ • (H : Set (Perm Ω))) : τ • (H : Set (Perm Ω)) = ρ • (H : Set (Perm Ω)) := by
  obtain ⟨k, hk, rfl⟩ := h
  show (ρ * k) • (H : Set (Perm Ω)) = _
  rw [mul_smul]
  congr 1
  ext g
  simp only [Set.mem_smul_set, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact H.mul_mem hk hu
  · intro hg; exact ⟨k⁻¹ * g, H.mul_mem (H.inv_mem hk) hg, by group⟩

/-- The aggregation path: `LiftAndContinue` on each overcoset and `CombineExact`. The child of
the overcoset `ρ_j H_j` may use any representative `τ_j` of it. -/
theorem step_aggregate {S : State Ω C} (b : Branches Ω) (hb : Branches.Covers S b)
    (τ : Fin b.overs.length → Perm Ω)
    (hτ : ∀ j, τ j ∈ (b.overs.get j).1 • ((b.overs.get j).2 : Set (Perm Ω)))
    (child : Fin b.overs.length → State Ω C)
    (hchild : ∀ j, (child j).Inst (b.overs.get j).2 S.dom S.x (S.y ∘ τ j))
    (A : Fin b.overs.length → Set (Perm Ω)) (ih : ∀ j, A j = (child j).answer) :
    ((⋃ p ∈ b.pieces, p) ∪ ⋃ j, τ j • A j) = S.answer := by
  simp_rw [ih, fun j => State.answer_of_inst (hchild j)]
  have hτG : ∀ j, τ j ∈ S.G := fun j => by
    obtain ⟨k, hk, hkj⟩ := hτ j
    rw [← hkj]
    exact S.G.mul_mem (hb.overs_mem j) (hb.overs_le j hk)
  have h := answer_combine (κ := {p // p ∈ b.pieces}) (fun p => p.1)
    (fun p => hb.pieces_sub p.1 p.2) τ (fun j => (b.overs.get j).2)
    hτG hb.overs_le (by
      intro g hg
      rcases hb.cover hg with h | h
      · left
        simp only [Set.mem_iUnion] at h ⊢
        obtain ⟨p, hp, hgp⟩ := h
        exact ⟨⟨p, hp⟩, hgp⟩
      · right
        simp only [Set.mem_iUnion] at h ⊢
        obtain ⟨j, hj⟩ := h
        exact ⟨j, by rw [smul_coset_eq (hτ j)]; exact hj⟩)
  have hU : (⋃ p : {p // p ∈ b.pieces}, p.1) = ⋃ p ∈ b.pieces, p := by
    ext g; simp
  rw [hU] at h
  exact h

end Steps

/-! ### The induction -/

/-- Every run returns the exact answer of its state, and every script run returns
the result of its script under exact answers. -/
theorem run_exec_exact :
    (∀ {m : Mode} {Ω C : Type} {S : State Ω C} {L : Option (SuppliedLabels S)}
      {A : Set (Perm Ω)}, Run P m S L A →
      A = S.answer) ∧
    (∀ {α : Type} {s : Script α} {a : α}, Exec P s a → a = s.evalExact) := by
  refine ⟨fun r => ?_, fun e => ?_⟩
  · refine Run.rec (motive_1 := fun _ _ _ S _ A _ => A = S.answer)
      (motive_2 := fun s a _ => a = s.evalExact)
      (direct := fun _ _ => rfl)
      (fresh := fun _ hS' _ ih => step_freshPhase hS' ih)
      (threshold := fun _ _ ih => ih)
      (orbitStop := fun _ _ hD₁ h₁ _ _ _ _ ih => step_orbitStop hD₁ h₁ ih)
      (orbitChain := fun _ _ hD₁ h₁ _ _ _ _ t ht h₂ _ _ _ _ ih₁ ih₂ =>
        step_orbitChain hD₁ h₁ t ht h₂ ih₁ ih₂)
      (floorReset := fun _ _ _ hcore _ _ _ _ _ _ ih => step_fresh hcore ih)
      (dispatch := fun _ _ _ I child hchild _ _ _ A _ ih =>
        step_cosets I.τ I.τ_mem I.K_le I.cover child hchild A ih)
      (normalize := fun _ _ _ _ _ _ _ _ _ N _ _ _ A _ ih =>
        step_cosets N.I.τ N.I.τ_mem N.I.le N.I.cover N.child (fun _ => ⟨rfl, rfl, rfl, rfl⟩) A ih)
      (rowTerminal := fun _ _ _ _ I _ ih => ih.trans I.exact)
      (rowColumns := fun _ _ _ _ _ hcore _ _ _ _ _ _ ih => step_fresh hcore ih)
      (aggregate := fun _ _ _ _ _ I _ _ b _ τ hτ child hchild _ _ _ A _ ihb ih =>
        step_aggregate b (ihb ▸ I.covers) τ hτ child hchild A ih)
      (done := fun _ => rfl)
      (ask := fun {_ _ _ _ _ k _ _} _ _ ihr ihe =>
        ihe.trans (congrArg (fun B => (k B).evalExact) ihr))
      r
  · refine Exec.rec (motive_1 := fun _ _ _ S _ A _ => A = S.answer)
      (motive_2 := fun s a _ => a = s.evalExact)
      (direct := fun _ _ => rfl)
      (fresh := fun _ hS' _ ih => step_freshPhase hS' ih)
      (threshold := fun _ _ ih => ih)
      (orbitStop := fun _ _ hD₁ h₁ _ _ _ _ ih => step_orbitStop hD₁ h₁ ih)
      (orbitChain := fun _ _ hD₁ h₁ _ _ _ _ t ht h₂ _ _ _ _ ih₁ ih₂ =>
        step_orbitChain hD₁ h₁ t ht h₂ ih₁ ih₂)
      (floorReset := fun _ _ _ hcore _ _ _ _ _ _ ih => step_fresh hcore ih)
      (dispatch := fun _ _ _ I child hchild _ _ _ A _ ih =>
        step_cosets I.τ I.τ_mem I.K_le I.cover child hchild A ih)
      (normalize := fun _ _ _ _ _ _ _ _ _ N _ _ _ A _ ih =>
        step_cosets N.I.τ N.I.τ_mem N.I.le N.I.cover N.child (fun _ => ⟨rfl, rfl, rfl, rfl⟩) A ih)
      (rowTerminal := fun _ _ _ _ I _ ih => ih.trans I.exact)
      (rowColumns := fun _ _ _ _ _ hcore _ _ _ _ _ _ ih => step_fresh hcore ih)
      (aggregate := fun _ _ _ _ _ I _ _ b _ τ hτ child hchild _ _ _ A _ ihb ih =>
        step_aggregate b (ihb ▸ I.covers) τ hτ child hchild A ih)
      (done := fun _ => rfl)
      (ask := fun {_ _ _ _ _ k _ _} _ _ ihr ihe =>
        ihe.trans (congrArg (fun B => (k B).evalExact) ihr))
      e

/-- Every run returns the exact answer of its state. -/
theorem Run.exact {m : Mode} {Ω C : Type} {S : State Ω C} {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} (r : Run P m S L A) : A = S.answer :=
  run_exec_exact.1 r

/-- Every script run returns the result of its script under exact answers. -/
theorem Exec.exact {α : Type} {s : Script α} {a : α} (e : Exec P s a) : a = s.evalExact :=
  run_exec_exact.2 e

end GI.Algorithm
