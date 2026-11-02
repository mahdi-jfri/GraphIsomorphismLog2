import Workspace.Impl.LinFiniteActionCost

/-! A monotone polynomial envelope for composing the existing input-bit
cost bounds. All three size arguments are counted. -/
namespace GI.Impl

noncomputable def linPolyEnvelope {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) (W : ℕ) : ℕ :=
  hf.choose * (3 * (W + 1) + 2) ^ hf.choose_spec.choose

theorem linPolyEnvelope_bound {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f)
    {n s B W : ℕ} (hn : n ≤ W) (hs : s ≤ W) (hB : B ≤ W) :
    f n s B ≤ linPolyEnvelope hf W := by
  have hh := hf.choose_spec.choose_spec n s B
  exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

theorem linPolyEnvelope_mono {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f)
    {W V : ℕ} (h : W ≤ V) : linPolyEnvelope hf W ≤ linPolyEnvelope hf V := by
  unfold linPolyEnvelope
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem linPolyEnvelope_poly {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) :
    PBU (fun _ W _ => linPolyEnvelope hf W) := by
  unfold linPolyEnvelope
  norm_poly

end GI.Impl
