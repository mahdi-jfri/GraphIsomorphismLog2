module

public import Workspace.Paper.HereditaryBudgetBasic
public import Workspace.PrimitiveExhaustion

@[expose] public section

/-!
# Paper, Appendix A: Lemma A.8 and Theorem A.9

Lemma A.8 (`lem_budget_primitive_valuation`) and Theorem A.9
(`thm_hereditary_budget`, `thm_hereditary_budget_chains`), proved unconditionally
from Schreier's conjecture (`GI.schreier`).
-/

namespace GI.Paper

open GI RadicalSocle PrimitiveValuation HbudAlmostSimple

variable {n : ℕ}

/-- Affine primitive action: the group has a nontrivial abelian normal subgroup
(for a primitive group, equivalently `G ≤ AGL_d(p)` on `p^d` points with its
translations). -/
def IsAffineAction (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ ∀ x y : N, x * y = y * x

/-- Almost simple: the socle is a nonabelian simple group (so `T ≤ G ≤ Aut T`). -/
def IsAlmostSimple (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  IsSimpleGroup (socle G) ∧ ∃ x y : socle G, x * y ≠ y * x

/-- The regular, diagonal, and twisted wreath cases of `eq:budget-diagonal-degree`:
`G` is radical-free and its socle has order at most `n^2`. -/
def IsRegularDiagonal (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  (∀ R : Subgroup G, R.Normal → Group.IsSolvable R → R = ⊥) ∧
    Nat.card (socle G) ≤ n ^ 2

/-- Almost simple with alternating socle `Alt(m)`, and the action is neither the
natural action (`G ⊇ Alt(n)`) nor a Johnson subset action. -/
def IsAlternatingNonJohnson (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  IsAlmostSimple G ∧ (∃ m : ℕ, Nonempty (socle G ≃* alternatingGroup (Fin m))) ∧
    ¬ alternatingGroup (Fin n) ≤ G ∧ ¬ JohnsonSubsetAction G

/-- For degree at most two the valuation at three vanishes. -/
theorem three_valuation_small (G : Subgroup (Equiv.Perm (Fin n))) (hn : n ≤ 2) :
    padicValNat 3 (Nat.card G) = 0 := by
  have hdvd : Nat.card G ∣ 2 := by
    have h1 : Nat.card G ∣ n.factorial := by
      have := G.card_subgroup_dvd_card
      rwa [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
    exact h1.trans (by interval_cases n <;> decide)
  apply padicValNat.eq_zero_of_not_dvd
  intro h3
  have := Nat.le_of_dvd (by norm_num) (h3.trans hdvd)
  omega

/-- No visible marked step occurs at an almost simple transitive group on `n ≥ 2`
points. -/
theorem lem_budget_almost_simple_no_mark
    (hn : 2 ≤ n) (G : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive G (Fin n)] (hAS : IsAlmostSimple G) {k : ℕ} (hk : 5 ≤ k)
    (L : Subgroup (Equiv.Perm (Fin n))) (a : Fin n) :
    IsEmpty (VisibleStep a G L k) :=
  ⟨fun s => no_almostSimple_step (by simpa using hn) hAS.1 hAS.2 hk s⟩

/-- **Lemma A.8** (`lem:budget-primitive-valuation`). There is an absolute
constant `A₀` such that:
1. every primitive action of degree `n` that is affine or almost simple with
   alternating socle (neither natural nor a Johnson subset action) has a prime
   `ℓ ∈ {3,5}` with `6 v_ℓ(|G|) ≤ A₀ log n`;
2. every primitive action of degree `n` that is affine, of regular/diagonal/twisted
   type as in `eq:budget-diagonal-degree`, or almost simple with alternating socle
   (neither natural nor a Johnson subset action) satisfies
   `σ(G, Ω) ≤ A₀ log n` for all `κ_cert ≥ 64`. -/
theorem lem_budget_primitive_valuation :
    ∃ A₀ : ℝ, ∀ n : ℕ, ∀ G : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPreprimitive G (Fin n) →
      ((IsAffineAction G ∨ IsAlternatingNonJohnson G) →
        ∃ ℓ : ℕ, (ℓ = 3 ∨ ℓ = 5) ∧ 6 * (padicValNat ℓ (Nat.card G) : ℝ) ≤ A₀ * Real.log n) ∧
      ((IsAffineAction G ∨ IsRegularDiagonal G ∨ IsAlternatingNonJohnson G) →
        ∀ kcert : ℕ, 64 ≤ kcert → ∀ a : Fin n,
          (def_hereditary_budget kcert G a : ℝ) ≤ A₀ * Real.log n) := by
  refine ⟨primitiveConstant, ?_⟩
  intro n G hp
  have := hp
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have h0 := primitiveConstant_nonneg
  have h12 : 12 / Real.log 2 ≤ primitiveConstant :=
    (le_max_left _ _).trans (le_max_left _ _)
  have halt : alternatingConstant ≤ primitiveConstant :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hdiag : diagonalBudgetConstant ≤ primitiveConstant :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hval : (IsAffineAction G ∨ IsAlternatingNonJohnson G) →
      ∃ ℓ : ℕ, (ℓ = 3 ∨ ℓ = 5) ∧
        6 * (padicValNat ℓ (Nat.card G) : ℝ) ≤ primitiveConstant * Real.log n := by
    intro hcase
    by_cases hsmall : n ≤ 2
    · refine ⟨3, Or.inl rfl, ?_⟩
      rw [three_valuation_small G hsmall]
      simpa using mul_nonneg h0 hlogn
    have hn : 3 ≤ n := by omega
    rcases hcase with ⟨N, hN, hne, comm⟩ | ⟨⟨hs, hna⟩, ⟨m, ⟨e⟩⟩, hnat, hjoh⟩
    · have := hN
      obtain ⟨ℓ, hℓ, hv⟩ := affine_valuation G N hne comm ⟨0, by omega⟩
      exact ⟨ℓ, hℓ, hv.trans (mul_le_mul_of_nonneg_right h12 hlogn)⟩
    · have hv := alternating_socle_valuation G
        (HbudAlmostSimple.radicalFree_of_simple_socle hs hna) e hn hnat hjoh
      exact ⟨3, Or.inl rfl, hv.trans (mul_le_mul_of_nonneg_right halt hlogn)⟩
  refine ⟨hval, ?_⟩
  intro hcase kcert hk a
  have hsmall_or_large : n ≤ 2 ∨ 3 ≤ n := by omega
  rcases hsmall_or_large with hsmall | hn
  · have hsig : def_hereditary_budget kcert G a ≤ 6 * padicValNat 3 (Nat.card G) :=
      sigma_valuation_bound (Or.inl rfl) hk a G
    rw [three_valuation_small G hsmall, mul_zero, Nat.le_zero] at hsig
    rw [hsig]
    simpa using mul_nonneg h0 hlogn
  rcases hcase with haff | ⟨hRF, hdeg⟩ | haltcase
  · obtain ⟨ℓ, hℓ, hv⟩ := hval (Or.inl haff)
    have hsig : (def_hereditary_budget kcert G a : ℝ) ≤ 6 * (padicValNat ℓ (Nat.card G) : ℝ) := by
      exact_mod_cast sigma_valuation_bound hℓ hk a G
    exact hsig.trans hv
  · exact (socle_sigma_bound hRF hdeg (by omega) a).trans
      (mul_le_mul_of_nonneg_right hdiag hlogn)
  · obtain ⟨ℓ, hℓ, hv⟩ := hval (Or.inr haltcase)
    have hsig : (def_hereditary_budget kcert G a : ℝ) ≤ 6 * (padicValNat ℓ (Nat.card G) : ℝ) := by
      exact_mod_cast sigma_valuation_bound hℓ hk a G
    exact hsig.trans hv

/-- **Theorem A.9** (`thm:hereditary-budget`). There are absolute constants
`C ≥ C_* = 128` and `B = C + 6` such that, for `κ_cert ≥ 64`, every faithful
transitive permutation group `G ≤ Sym(Ω)` of degree `n` satisfies
`σ(G, Ω) ≤ 0` for `n ≤ 2` and `σ(G, Ω) ≤ C log n - B` for `n ≥ 3`.
(The proof does not use transitivity; the hypothesis is kept as in the paper.) -/
theorem thm_hereditary_budget :
    ∃ C B : ℝ, 128 ≤ C ∧ B = C + 6 ∧ ∀ kcert : ℕ, 64 ≤ kcert →
      ∀ (Ω : Type*) [Fintype Ω] (G : Subgroup (Equiv.Perm Ω)),
        MulAction.IsPretransitive G Ω → ∀ α : Ω,
        (def_hereditary_budget kcert G α : ℝ) ≤
          if Fintype.card Ω ≤ 2 then 0 else C * Real.log (Fintype.card Ω) - B := by
  obtain ⟨C, hC, h⟩ := hereditary_budget
  refine ⟨C, C + 6, hC, rfl, ?_⟩
  intro kcert hk Ω _ G _ α
  exact h kcert hk Ω G α

/-- Chains whose marks of weight exactly `k` are counted: `CountedChain kcert k a G j`
says there is a chain from `G` (as in Definition A.2) with `j` marked steps whose
quotient is `Alt(k)`. -/
inductive CountedChain (kcert k : ℕ) {V : Type*} (a : V) :
    Subgroup (Equiv.Perm V) → ℕ → Prop
  | stop (H) : CountedChain kcert k a H 0
  | restrict {H L j} : L ≤ H → CountedChain kcert k a L j → CountedChain kcert k a H j
  | markCounted {H L j} : VisibleStep a H L k → CountedChain kcert k a L j →
      CountedChain kcert k a H (j + 1)
  | markOther {H L j k'} : kcert ≤ k' → VisibleStep a H L k' →
      CountedChain kcert k a L j → CountedChain kcert k a H j

theorem CountedChain.marked {kcert k : ℕ} (hk : kcert ≤ k) {V : Type*} {a : V}
    {H : Subgroup (Equiv.Perm V)} {j : ℕ} (c : CountedChain kcert k a H j) :
    ∃ w, MarkedChain kcert a H w ∧ j * k ≤ w := by
  induction c with
  | stop H => exact ⟨0, .stop H, by simp⟩
  | restrict hle _ ih =>
    obtain ⟨w, hw, hj⟩ := ih
    exact ⟨w, .restrict hle hw, hj⟩
  | markCounted step _ ih =>
    obtain ⟨w, hw, hj⟩ := ih
    exact ⟨w + k, .mark hk step hw, by rw [Nat.succ_mul]; omega⟩
  | markOther hk' step _ ih =>
    obtain ⟨w, hw, hj⟩ := ih
    exact ⟨w + _, .mark hk' step hw, by omega⟩

/-- **Theorem A.9**, consequences: an arbitrary chain of subgroup restrictions with
visible transitive normal quotient steps `Alt(k_i)`, `k_i ≥ κ_cert`, has total
marked weight at most `C log n`; for fixed `k ≥ κ_cert` it has at most
`C log n / k` steps `Alt(k)`. (Faithful orbit images are covered by
Lemma A.3, `lem_budget_inheritance_orbit`.) -/
theorem thm_hereditary_budget_chains :
    ∃ C : ℝ, 128 ≤ C ∧ ∀ kcert : ℕ, 64 ≤ kcert →
      ∀ (Ω : Type*) [Fintype Ω] (G : Subgroup (Equiv.Perm Ω)) (α : Ω),
        (∀ w, MarkedChain kcert α G w → (w : ℝ) ≤ C * Real.log (Fintype.card Ω)) ∧
        (∀ k j, kcert ≤ k → CountedChain kcert k α G j →
          (j : ℝ) ≤ C * Real.log (Fintype.card Ω) / k) := by
  obtain ⟨C, hC, h⟩ := hereditary_budget
  refine ⟨C, hC, ?_⟩
  intro kcert hk Ω _ G α
  have hlog : 0 ≤ Real.log (Fintype.card Ω : ℝ) := Real.log_natCast_nonneg _
  have hsig : (sigma kcert α G : ℝ) ≤ C * Real.log (Fintype.card Ω) := by
    refine (h kcert hk Ω G α).trans ?_
    unfold BudgetInduction.degreeAllowance
    split_ifs
    · exact mul_nonneg (by linarith) hlog
    · linarith
  have hw : ∀ w, MarkedChain kcert α G w → (w : ℝ) ≤ C * Real.log (Fintype.card Ω) :=
    fun w hw => (Nat.cast_le.mpr (sigma_bounds_chain (by omega) hw)).trans hsig
  refine ⟨hw, ?_⟩
  intro k j hkk c
  obtain ⟨w, hmw, hj⟩ := c.marked hkk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [le_div_iff₀ hkpos]
  have : ((j * k : ℕ) : ℝ) ≤ w := by exact_mod_cast hj
  push_cast at this
  linarith [hw w hmw]

end GI.Paper
