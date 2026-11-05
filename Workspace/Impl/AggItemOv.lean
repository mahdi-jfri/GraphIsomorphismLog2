module

public import Workspace.Impl.AggItemRun

@[expose] public section

/-!
# A program's representative stands for the model's overcoset

The model fixes the representative of some overcosets by a classical choice (`invItem`:
`h.choose`; the configuration and rectangle queries: `read`). A program finds some other
representative `σ'` of the same coset. `AsItemsOK` asks only that the program's overcoset value
`(σ', E₀, ms)` stands for the model's `(L.rep σ, π⁻¹(E₀))` in the sense of `asOvAt`.

* `it_ovAt_of_mem`: this holds whenever `σ⁻¹ σ' ∈ E₀`, because `L.rep` is a section of `π`, so
  `(L.rep σ)⁻¹ L.rep σ'` lies in `G` with label image `σ⁻¹ σ'`.
* `it_invItem_ovAt`: for the overcoset item of an invariant (Case 1, balanced partitions), every
  even `σ'` that maps the invariant of `X` to that of `Y` will do, since `h.choose⁻¹ σ'` fixes the
  invariant of `X`.
-/

namespace GI.Impl

open GI.Algorithm Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type}

/-- **A representative in the same coset stands for the model's overcoset.** -/
theorem it_ovAt_of_mem {S : State Ω C} (L : GiantLabels S)
    {σ σ' : alternatingGroup (Fin L.q)} {E₀ : Subgroup (alternatingGroup (Fin L.q))}
    (h : σ⁻¹ * σ' ∈ E₀) (ms : List (Perm (Fin L.q))) :
    asOvAt L (σ', E₀, ms) (AuxItem.liftOver L E₀ σ) := by
  refine ⟨rfl, ?_⟩
  show L.rep σ' ∈ L.rep σ • (L.lift E₀ : Set (Perm Ω))
  rw [mem_leftCoset_iff]
  have hG : (L.rep σ)⁻¹ * L.rep σ' ∈ S.G := S.G.mul_mem (S.G.inv_mem (L.rep_mem σ)) (L.rep_mem σ')
  refine L.mem_lift.2 ⟨hG, ?_⟩
  have e : (⟨(L.rep σ)⁻¹ * L.rep σ', hG⟩ : S.G) =
      (⟨L.rep σ, L.rep_mem σ⟩ : S.G)⁻¹ * ⟨L.rep σ', L.rep_mem σ'⟩ := rfl
  rw [e, map_mul, map_inv, L.π_rep, L.π_rep]
  exact h

/-- **Case 1 and balanced partitions**: an even `σ'` that maps the invariant of `X` to that of `Y`
gives an overcoset value that stands for the overcoset of `invItem`. -/
theorem it_invItem_ovAt {P : Params} {S : State Ω C} (L : GiantLabels S) {Z : Type*}
    [MulAction (Perm (Fin L.q)) Z] {ℓ : ℕ} (F : GI.Algorithm.Canon L.q P.κ ℓ → Z)
    {X Y : GI.Algorithm.Canon L.q P.κ ℓ}
    (h : ∃ σ : alternatingGroup (Fin L.q), (σ : Perm (Fin L.q)) • F X = F Y)
    {σ' : alternatingGroup (Fin L.q)} (h' : (σ' : Perm (Fin L.q)) • F X = F Y)
    (ms : List (Perm (Fin L.q))) :
    asOvAt L (σ', evenStab (q := L.q) (F X), ms)
      (AuxItem.liftOver L (evenStab (q := L.q) (F X)) h.choose) := by
  refine it_ovAt_of_mem L ?_ ms
  show ((h.choose⁻¹ * σ' : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) ∈
    MulAction.stabilizer (Perm (Fin L.q)) (F X)
  have hc := h.choose_spec
  rw [MulAction.mem_stabilizer_iff, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h',
    inv_smul_eq_iff]
  exact hc.symm

end GI.Impl
