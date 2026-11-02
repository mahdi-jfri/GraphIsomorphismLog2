import Workspace.Paper.HereditaryBudgetBasic
import Workspace.PrimitiveExhaustion

/-!
# Paper, Appendix A: Lemma A.8 and Theorem A.9

Cited inputs (stated as `Prop`s, taken as hypotheses):
* `GI.Cited.AutCardLeSq`: `|Aut T| ≤ |T|^2` for nonabelian simple `T` [GMP, Lemma 7.7];
* `GI.Cited.SimpleValuationDegree`: for nonalternating nonabelian simple `T`,
  `v_ℓ(|Aut T|) = O(log μ(T))` for some `ℓ ∈ {3,5}` (order formulas, [GMPS, Table 4]).
-/

namespace GI.Paper

open GI RadicalSocle PrimitiveValuation

variable {n : ℕ}

/-- Affine primitive action: the group has a nontrivial abelian normal subgroup
(for a primitive group, equivalently `G ≤ AGL_d(p)` on `p^d` points with its
translations). -/
def IsAffineAction (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ ∀ x y : N, x * y = y * x

/-- Almost simple: the socle is a nonabelian simple group (so `T ≤ G ≤ Aut T`). -/
def IsAlmostSimple (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  IsSimpleGroup (socle G) ∧ ∃ x y : socle G, x * y ≠ y * x

/-- Almost simple with socle not isomorphic to any alternating group. -/
def IsAlmostSimpleNonalternating (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  IsAlmostSimple G ∧ ∀ m : ℕ, IsEmpty (socle G ≃* alternatingGroup (Fin m))

/-- The regular and diagonal cases of `eq:budget-diagonal-degree`: the socle is
`T^s` for a nonabelian simple `T`, `n ≥ |T|^{s/2}`, and `G ≤ Aut(T) wr Sym(s)` as
an abstract subgroup. -/
def IsRegularDiagonal (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∃ (T : Type) (_ : Group T) (_ : Finite T) (s : ℕ), IsSimpleGroup T ∧
    (∃ x y : T, x * y ≠ y * x) ∧ Nonempty (socle G ≃* (Fin s → T)) ∧
    Nat.card T ^ s ≤ n ^ 2 ∧ ∃ f : G →* AutWreath T s, Function.Injective f

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

/-- **Lemma A.8** (`lem:budget-primitive-valuation`). There is an absolute
constant `A₀` such that every primitive action of degree `n` that is affine,
almost simple with nonalternating socle, of regular/diagonal type as in
`eq:budget-diagonal-degree`, or almost simple with alternating socle but neither
natural nor a Johnson subset action, has a prime `ℓ ∈ {3,5}` with
`6 v_ℓ(|G|) ≤ A₀ log n`. -/
theorem lem_budget_primitive_valuation (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) :
    ∃ A₀ : ℝ, ∀ n : ℕ, ∀ G : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPreprimitive G (Fin n) →
      (IsAffineAction G ∨ IsAlmostSimpleNonalternating G ∨ IsRegularDiagonal G ∨
        IsAlternatingNonJohnson G) →
      ∃ ℓ : ℕ, (ℓ = 3 ∨ ℓ = 5) ∧ 6 * (padicValNat ℓ (Nat.card G) : ℝ) ≤ A₀ * Real.log n := by
  obtain ⟨A, hA⟩ := almostSimple_valuation hLie
  refine ⟨primitiveConstant A, ?_⟩
  intro n G hp hcase
  letI := hp
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have h0 := primitiveConstant_nonneg A
  by_cases hsmall : n ≤ 2
  · refine ⟨3, Or.inl rfl, ?_⟩
    rw [three_valuation_small G hsmall]
    simpa using mul_nonneg h0 hlogn
  have hn : 3 ≤ n := by omega
  have h12 : 12 / Real.log 2 ≤ primitiveConstant A :=
    (le_max_left _ _).trans (le_max_left _ _)
  have halt : alternatingConstant ≤ primitiveConstant A :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hdiag : WreathValuation.diagonalConstant ≤ primitiveConstant A :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hlie : A ≤ primitiveConstant A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  rcases hcase with ⟨N, hN, hne, comm⟩ | ⟨⟨hs, hna⟩, hnon⟩ | hdg | ⟨⟨hs, hna⟩, ⟨m, ⟨e⟩⟩, hnat, hjoh⟩
  · haveI := hN
    obtain ⟨ℓ, hℓ, hv⟩ := affine_valuation G N hne comm ⟨0, by omega⟩
    exact ⟨ℓ, hℓ, hv.trans (mul_le_mul_of_nonneg_right h12 hlogn)⟩
  · obtain ⟨ℓ, hℓ, hv⟩ := hA n G hs hna hnon
    exact ⟨ℓ, hℓ, hv.trans (mul_le_mul_of_nonneg_right hlie hlogn)⟩
  · obtain ⟨T, _, _, s, hT, hTna, _, hdeg, f, hf⟩ := hdg
    exact ⟨3, Or.inl rfl, (wreath_valuation hAut hT hTna f hf hdeg).trans
      (mul_le_mul_of_nonneg_right hdiag hlogn)⟩
  · have hv := alternating_socle_valuation G (radicalFree_of_simple_socle hs hna) e hn hnat hjoh
    exact ⟨3, Or.inl rfl, hv.trans (mul_le_mul_of_nonneg_right halt hlogn)⟩

/-- **Theorem A.9** (`thm:hereditary-budget`). There are absolute constants
`C ≥ C_* = 128` and `B = C + 6` such that, for `κ_cert ≥ 64`, every faithful
transitive permutation group `G ≤ Sym(Ω)` of degree `n` satisfies
`σ(G, Ω) ≤ 0` for `n ≤ 2` and `σ(G, Ω) ≤ C log n - B` for `n ≥ 3`.
(The proof does not use transitivity; the hypothesis is kept as in the paper.) -/
theorem thm_hereditary_budget (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) :
    ∃ C B : ℝ, 128 ≤ C ∧ B = C + 6 ∧ ∀ kcert : ℕ, 64 ≤ kcert →
      ∀ (Ω : Type*) [Fintype Ω] (G : Subgroup (Equiv.Perm Ω)),
        MulAction.IsPretransitive G Ω → ∀ α : Ω,
        (def_hereditary_budget kcert G α : ℝ) ≤
          if Fintype.card Ω ≤ 2 then 0 else C * Real.log (Fintype.card Ω) - B := by
  obtain ⟨C, hC, h⟩ := hereditary_budget hAut hLie
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
theorem thm_hereditary_budget_chains (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) :
    ∃ C : ℝ, 128 ≤ C ∧ ∀ kcert : ℕ, 64 ≤ kcert →
      ∀ (Ω : Type*) [Fintype Ω] (G : Subgroup (Equiv.Perm Ω)) (α : Ω),
        (∀ w, MarkedChain kcert α G w → (w : ℝ) ≤ C * Real.log (Fintype.card Ω)) ∧
        (∀ k j, kcert ≤ k → CountedChain kcert k α G j →
          (j : ℝ) ≤ C * Real.log (Fintype.card Ω) / k) := by
  obtain ⟨C, hC, h⟩ := hereditary_budget hAut hLie
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
