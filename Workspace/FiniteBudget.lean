import Workspace.MarkedChains
import Mathlib.Data.Nat.Lattice
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace GI

theorem factorial_weight_lower {k : ℕ} (hk : 5 ≤ k) : 2 * (k + 1) ≤ k.factorial := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
    rw [Nat.factorial_succ]
    have hm := Nat.mul_le_mul_left (n + 1) ih
    nlinarith

theorem alternating_weight_lower {k : ℕ} (hk : 5 ≤ k) :
    k + 1 ≤ Nat.card (alternatingGroup (Fin k)) := by
  haveI : Nontrivial (Fin k) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa using (show 1 < k by omega))
  have hc := two_mul_card_alternatingGroup (α := Fin k)
  rw [Fintype.card_perm, Fintype.card_fin, ← Nat.card_eq_fintype_card] at hc
  have hf := factorial_weight_lower hk
  omega

variable {V : Type*} [Fintype V]

theorem subgroup_card_mono {L H : Subgroup (Equiv.Perm V)} (hle : L ≤ H) :
    Nat.card L ≤ Nat.card H := by
  let inclusion : L → H := fun l => ⟨l, hle l.property⟩
  apply Nat.card_le_card_of_injective inclusion
  intro x y h
  exact Subtype.ext (congrArg (fun h : H => (h : Equiv.Perm V)) h)

def visibleKernelEquiv {a : V} {H L : Subgroup (Equiv.Perm V)} {k : ℕ}
    (step : VisibleStep a H L k) : step.quotient.ker ≃ L where
  toFun h := ⟨h.1.1, (step.kernel h.1).1 h.2⟩
  invFun l := ⟨⟨l.1, step.lower l.2⟩, (step.kernel _).2 l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem visible_card_factorization {a : V} {H L : Subgroup (Equiv.Perm V)} {k : ℕ}
    (step : VisibleStep a H L k) :
    Nat.card L * Nat.card (alternatingGroup (Fin k)) = Nat.card H := by
  classical
  have h := step.quotient.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr step.onto] at h
  have he := Nat.card_congr (visibleKernelEquiv step)
  rw [he] at h
  simpa [Nat.card_eq_fintype_card] using h

theorem marked_card_drop {a : V} {H L : Subgroup (Equiv.Perm V)} {k : ℕ}
    (step : VisibleStep a H L k) (hk : 5 ≤ k) :
    Nat.card L + k ≤ Nat.card H := by
  have hL : 1 ≤ Nat.card L := Nat.card_pos
  have hA := alternating_weight_lower hk
  have hprod := visible_card_factorization step
  have hm := Nat.mul_le_mul_left (Nat.card L) hA
  nlinarith

/-- A crude unconditional order bound makes the paper's maximum well-defined.
This is only a finiteness bound; it is not the logarithmic budget theorem A.9. -/
theorem marked_chain_card_bound {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff)
    {a : V} {H : Subgroup (Equiv.Perm V)} (hw : MarkedChain cutoff a H w) :
    w + 1 ≤ Nat.card H := by
  induction hw with
  | stop H => exact Nat.card_pos
  | restrict hle _ ih => exact ih.trans (subgroup_card_mono hle)
  | mark hk step _ ih =>
    have hdrop := marked_card_drop step (hcutoff.trans hk)
    omega

noncomputable def sigma (cutoff : ℕ) (a : V) (H : Subgroup (Equiv.Perm V)) : ℕ :=
  sSup {w | MarkedChain cutoff a H w}

theorem marked_weights_bounded {cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (a : V) (H : Subgroup (Equiv.Perm V)) :
    BddAbove {w | MarkedChain cutoff a H w} := by
  refine ⟨Nat.card H, ?_⟩
  intro w hw
  have h := marked_chain_card_bound hcutoff hw
  omega

theorem sigma_achieved {cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (a : V) (H : Subgroup (Equiv.Perm V)) :
    MarkedChain cutoff a H (sigma cutoff a H) :=
  Nat.sSup_mem ⟨0, .stop H⟩ (marked_weights_bounded hcutoff a H)

theorem sigma_bounds_chain {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff)
    {a : V} {H : Subgroup (Equiv.Perm V)} (hw : MarkedChain cutoff a H w) :
    w ≤ sigma cutoff a H :=
  le_csSup (marked_weights_bounded hcutoff a H) hw

theorem sigma_card_bound {cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (a : V) (H : Subgroup (Equiv.Perm V)) : sigma cutoff a H + 1 ≤ Nat.card H :=
  marked_chain_card_bound hcutoff (sigma_achieved hcutoff a H)

theorem sigma_subgroup_mono {cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (a : V) {H L : Subgroup (Equiv.Perm V)} (hle : L ≤ H) :
    sigma cutoff a L ≤ sigma cutoff a H :=
  sigma_bounds_chain hcutoff (.restrict hle (sigma_achieved hcutoff a L))

theorem sigma_marked_decrease {cutoff k : ℕ} (hcutoff : 5 ≤ cutoff)
    {a : V} {H L : Subgroup (Equiv.Perm V)} (hk : cutoff ≤ k)
    (step : VisibleStep a H L k) :
    sigma cutoff a L + k ≤ sigma cutoff a H :=
  sigma_bounds_chain hcutoff (.mark hk step (sigma_achieved hcutoff a L))

end GI
