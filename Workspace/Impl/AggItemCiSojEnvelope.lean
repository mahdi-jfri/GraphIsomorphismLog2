module

public import Workspace.Impl.GenNormPoly

@[expose] public section

/-! # A monotone polynomial envelope for a proved own-cost bound -/

namespace GI.Impl

/-- A polynomial envelope chosen from a proved uniform polynomial bound. Its
extra linear term also bounds the input itself. This is used only in the cost
analysis and makes no choice in the item program. -/
noncomputable def itcsEnvelope (f : ℕ → ℕ) (hf : PBU fun _ W _ => f W) (W : ℕ) : ℕ :=
  (Classical.choose hf)*(W+2)^(Classical.choose (Classical.choose_spec hf))+W+1

/-- The envelope bounds the function at its exact argument. -/
theorem itcs_envelope_bound (f : ℕ → ℕ) (hf : PBU fun _ W _ => f W) (W : ℕ) :
    f W ≤ itcsEnvelope f hf W := by
  have h := Classical.choose_spec (Classical.choose_spec hf) 0 W 0
  simp only [PB,Nat.add_zero,Nat.zero_add] at h
  unfold itcsEnvelope
  exact h.trans ((Nat.le_add_right _ W).trans (Nat.le_add_right _ 1))

/-- The envelope is monotone even when the cited cost function is not. -/
theorem itcs_envelope_mono (f : ℕ → ℕ) (hf : PBU fun _ W _ => f W) :
    Monotone (itcsEnvelope f hf) := by
  intro a b hab
  unfold itcsEnvelope
  gcongr

/-- A call at any smaller encoded input weight fits the common envelope. -/
theorem itcs_envelope_of_le (f : ℕ → ℕ) (hf : PBU fun _ W _ => f W) {a b : ℕ} (h : a ≤ b) :
    f a ≤ itcsEnvelope f hf b :=
  (itcs_envelope_bound f hf a).trans (itcs_envelope_mono f hf h)

/-- Every growth step strictly exceeds its input. -/
theorem itcs_envelope_grow (f : ℕ → ℕ) (hf : PBU fun _ W _ => f W) (W : ℕ) :
    W+1 ≤ itcsEnvelope f hf W := by unfold itcsEnvelope; omega

/-- The scalar envelope is a fixed polynomial bound. -/
theorem itcs_envelope_pbu (f : ℕ → ℕ) (hf : PBU fun _ W _ => f W) :
    PBU fun k _ _ => itcsEnvelope f hf k := by
  unfold itcsEnvelope
  norm_poly

/-- A fixed number of growth steps preserves a uniform polynomial bound. -/
theorem itcs_iter_pbu (f : ℕ → ℕ) (hf : PBU fun _ W _ => f W) (n : ℕ)
    {g : ℕ → ℕ → ℕ → ℕ} (hg : PBU g) :
    PBU fun k W B => (itcsEnvelope f hf)^[n] (g k W B) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using normPoly_comp (itcs_envelope_pbu f hf) ih

end GI.Impl
