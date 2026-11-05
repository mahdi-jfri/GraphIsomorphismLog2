module

public import Workspace.SocleOuterBudget
public import Workspace.BudgetInductionAlternatives

@[expose] public section

namespace GI.RadicalSocle

variable {G : Type*} [Group G] [Finite G]

/-- Faithful socle conjugation embeds the actual group into the
permutation group of the actual socle. This coarse finite bound is
useful for bounded exceptional socles, without an automorphism theorem. -/
theorem card_dvd_socle_factorial
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥) :
    Nat.card G ∣ (Nat.card (socle G)).factorial := by
  let f := (MulAut.toPerm (socle G)).comp (socleConjugation (G := G))
  have hf : Function.Injective f := by
    intro g h he
    apply socleConjugation_injective radicalFree
    apply MulEquiv.ext
    intro s
    exact congrArg (fun p : Equiv.Perm (socle G) => p s) he
  rw [← Nat.card_perm]
  exact Subgroup.card_dvd_of_injective f hf

theorem bounded_socle_three_valuation
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    {b : ℕ} (size : Nat.card (socle G) ≤ b) :
    6 * padicValNat 3 (Nat.card G) ≤ 3 * b := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hd := (card_dvd_socle_factorial radicalFree).trans (Nat.factorial_dvd_factorial size)
  have hv := GI.primeValuation_mono (p := 3) (Nat.factorial_ne_zero b) hd
  have hleg := sub_one_mul_padicValNat_factorial (p := 3) b
  have hsub := Nat.sub_le b ((3 : ℕ).digits b).sum
  norm_num only at hleg
  omega

/-- All alternating socles of degree at most six, including the
exceptional degree six, are bounded by an explicit finite constant. -/
theorem small_alternating_socle_three_valuation
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    {m : ℕ} (e : socle G ≃* alternatingGroup (Fin m)) (hm : m ≤ 6) :
    6 * padicValNat 3 (Nat.card G) ≤ 2160 := by
  have hs : Nat.card (socle G) ≤ 720 := by
    rw [Nat.card_congr e.toEquiv]
    have hc := Subgroup.card_le_card_group (alternatingGroup (Fin m))
    have hperm : Nat.card (Equiv.Perm (Fin m)) = m.factorial := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hperm] at hc
    have hf := Nat.factorial_le hm
    norm_num at hf
    exact hc.trans hf
  have h := bounded_socle_three_valuation radicalFree hs
  norm_num at h
  exact h

end GI.RadicalSocle

namespace GI.BudgetInduction

/-- Bounded alternating-socle degrees meet the actual valuation
alternative, including Aut(A6) without any description of that group. -/
theorem primitive_alternative_of_small_alternating_socle {n m : ℕ} {A₀ : ℝ}
    (H : Subgroup (Equiv.Perm (Fin n)))
    (radicalFree : ∀ N : Subgroup H, N.Normal → IsSolvable N → N = ⊥)
    (e : RadicalSocle.socle H ≃* alternatingGroup (Fin m))
    (hm : m ≤ 6) (hn : 3 ≤ n) (hA : 2160 / Real.log 3 ≤ A₀) :
    PrimitiveReductionAlternative A₀ H := by
  have hv : 6 * (padicValNat 3 (Nat.card H) : ℝ) ≤ 2160 := by
    exact_mod_cast RadicalSocle.small_alternating_socle_three_valuation radicalFree e hm
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog : Real.log 3 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogn : 0 ≤ Real.log (n : ℝ) := hlog3.le.trans hlog
  refine Or.inl ⟨3, Or.inl rfl, hv.trans ?_⟩
  calc
    (2160 : ℝ) = (2160 / Real.log 3) * Real.log 3 := by field_simp [ne_of_gt hlog3]
    _ ≤ (2160 / Real.log 3) * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ A₀ * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hA hlogn

end GI.BudgetInduction
