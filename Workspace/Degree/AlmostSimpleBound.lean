module

public import Workspace.Degree.MarotiFacts
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Workspace.AlternatingPrimitiveStabilizer
public import Maroti.Alternating.Case
public import Maroti.AlmostSimple.Basic
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

/-!
# Almost simple groups in `Γ̂_D`

A primitive almost simple group `H` of degree `n` whose socle `S` embeds in `Sym(D)` either acts on
the `k`-subsets of a set (`Maroti.IsSubsetActionType`) or has `log |H| ≤ O(log D log n)`.

* If `S` is not alternating, take the action of `S` on the cosets of a subgroup of least index `μ`.
  It is primitive and faithful, and `μ ≤ min(D, n)`. Maróti's theorem gives
  `|S| ≤ μ^(O(1) + log₂ μ)`, because a simple group of Johnson-product type is alternating.
* If `S = Alt(m)`, `m ≥ 7`, read `H` in `Sym(m)`. If a point stabilizer is intransitive on the `m`
  points, the action is on `k`-subsets. Otherwise `n ≥ 2^Ω(m)`, by counting and by Bochert, so
  `|H| ≤ m! ≤ n^O(log m)`.
-/

@[expose] public section

namespace GI.Degree

open Equiv MulAction Real

/-- `Nat.log 2 n ≤ log₂ n` as a real number. -/
theorem natLog_two_le {n : ℕ} (hn : 1 ≤ n) : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ h2]
  have h3 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h4 : ((2 : ℝ) ^ Nat.log 2 n) ≤ n := by exact_mod_cast h3
  calc (Nat.log 2 n : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ Nat.log 2 n) := by
        rw [Real.log_pow]
    _ ≤ Real.log n := Real.log_le_log (by positivity) h4

/-- A nontrivial group that acts faithfully on `X` has a proper subgroup of index at most `|X|`. -/
theorem exists_proper_index_le {S X : Type*} [Group S] [Finite X] [Nontrivial S]
    (φ : S →* Perm X) (hφ : Function.Injective φ) :
    ∃ M : Subgroup S, M ≠ ⊤ ∧ M.index ≠ 0 ∧ M.index ≤ Nat.card X := by
  obtain ⟨g, hg⟩ := exists_ne (1 : S)
  have hne : φ g ≠ 1 := fun h => hg (hφ (h.trans (map_one φ).symm))
  obtain ⟨x, hx⟩ : ∃ x, φ g x ≠ x := by
    by_contra hall
    push Not at hall
    exact hne (Equiv.ext hall)
  let _ : MulAction S X := MulAction.compHom X φ
  refine ⟨stabilizer S x, fun htop => hx ?_, ?_, ?_⟩
  · have : g ∈ stabilizer S x := htop ▸ Subgroup.mem_top g
    exact this
  · rw [index_stabilizer]
    exact (Set.ncard_pos (Set.toFinite _)).2 (Set.nonempty_of_mem (mem_orbit_self x)) |>.ne'
  · rw [index_stabilizer]
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)

/-- A finite simple group has a maximal subgroup of least index among proper subgroups. -/
theorem exists_coatom_index_le {S : Type*} [Group S] [Finite S] [Nontrivial S] :
    ∃ M : Subgroup S, IsCoatom M ∧ ∀ L : Subgroup S, L ≠ ⊤ → M.index ≤ L.index := by
  classical
  have hex : ∃ k, ∃ L : Subgroup S, L ≠ ⊤ ∧ L.index = k := ⟨_, ⊥, bot_ne_top, rfl⟩
  obtain ⟨L, hL, hk⟩ := Nat.find_spec hex
  obtain ⟨M, hM, hLM⟩ := (eq_top_or_exists_le_coatom L).resolve_left hL
  refine ⟨M, hM, fun L' hL' => ?_⟩
  calc M.index ≤ L.index := Subgroup.index_antitone hLM
    _ = Nat.find hex := hk
    _ ≤ L'.index := Nat.find_min' hex ⟨L', hL', rfl⟩

/-- **A simple group that is not alternating.** If `S` embeds in `Sym(D)` and acts faithfully on
`X`, then `log |S| ≤ (8 + log₂ D) log |X|`. -/
theorem log_card_simple_le {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnot : ∀ m, 5 ≤ m → IsEmpty (S ≃* alternatingGroup (Fin m))) {D : ℕ}
    (hE : EmbedsInSym D S) {X : Type} [Finite X] (φ : S →* Perm X) (hφ : Function.Injective φ) :
    Real.log (Nat.card S) ≤ (8 + Real.log D / Real.log 2) * Real.log (Nat.card X) := by
  obtain ⟨f, hf⟩ := hE
  obtain ⟨M, hM, hmin⟩ := exists_coatom_index_le (S := S)
  obtain ⟨L₁, hL₁, -, hle₁⟩ := exists_proper_index_le φ hφ
  obtain ⟨L₂, hL₂, -, hle₂⟩ := exists_proper_index_le f hf
  have hμX : M.index ≤ Nat.card X := (hmin L₁ hL₁).trans hle₁
  have hμD : M.index ≤ D := by
    have := (hmin L₂ hL₂).trans hle₂
    simpa using this
  have hMne : M ≠ ⊤ := hM.1
  have h0 : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : 2 ≤ M.index := by
    have h1 : M.index ≠ 1 := fun h => hMne (Subgroup.index_eq_one.1 h)
    omega
  set μ := M.index with hμ
  -- The action on the cosets of `M`.
  have hcardq : Nat.card (S ⧸ M) = μ := rfl
  have hnt : Nontrivial (S ⧸ M) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardq]
    omega
  have hprim : IsPreprimitive S (S ⧸ M) :=
    (isCoatom_stabilizer_iff_preprimitive S ((1 : S) : S ⧸ M)).1 (by
      rw [stabilizer_quotient]
      exact hM)
  let ρ := MulAction.toPermHom S (S ⧸ M)
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    by_contra hne
    have hker : ρ.ker = ⊤ := by
      rcases ρ.normal_ker.eq_bot_or_eq_top with h | h
      · exact absurd (by simpa [h] using (MonoidHom.mem_ker).2 ha) hne
      · exact h
    refine hMne (eq_top_iff.2 fun t _ => ?_)
    have ht : t ∈ ρ.ker := hker ▸ Subgroup.mem_top t
    have h1 : t • ((1 : S) : S ⧸ M) = ((1 : S) : S ⧸ M) :=
      congrArg (fun p : Perm (S ⧸ M) => p ((1 : S) : S ⧸ M)) (MonoidHom.mem_ker.1 ht)
    have h2 : ((t : S) : S ⧸ M) = ((1 : S) : S ⧸ M) := by
      rw [← h1]
      exact congrArg _ (mul_one t).symm
    simpa using QuotientGroup.eq.1 h2
  let E : S ≃* ρ.range := MonoidHom.ofInjective hρ
  have hG : IsPreprimitive ρ.range (S ⧸ M) := by
    let f : (S ⧸ M) →ₑ[ρ.rangeRestrict] (S ⧸ M) :=
      { toFun := id
        map_smul' := fun _ _ => rfl }
    exact IsPreprimitive.of_surjective (f := f) Function.surjective_id
  have hcard : Nat.card ρ.range = Nat.card S := (Nat.card_congr E.toEquiv).symm
  have hlogμ : Real.log μ ≤ Real.log (Nat.card X) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hμX)
  have hnn : 0 ≤ Real.log μ := Real.log_natCast_nonneg μ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : Real.log μ / Real.log 2 ≤ Real.log D / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (by exact_mod_cast hμD)) hlog2.le
  have hX : 0 ≤ Real.log (Nat.card X) := Real.log_natCast_nonneg _
  have hDn : 0 ≤ Real.log D / Real.log 2 := div_nonneg (Real.log_natCast_nonneg D) hlog2.le
  rcases marotiFull ρ.range hG with ⟨m, k, r, e, hm, hk, hkm, hr, hS⟩ | ⟨hc, -⟩ | hc
  · have : IsSimpleGroup ρ.range := E.symm.isSimpleGroup
    obtain ⟨E'⟩ := nonempty_equiv_alternating hS hk (by omega) hr hm
    exact ((hnot m hm).false (E.trans E')).elim
  · rw [← hcard]
    rw [hcardq] at hc
    calc Real.log (Nat.card ρ.range) ≤ Real.log ((μ : ℝ) ^ 7) :=
          Real.log_le_log (by exact_mod_cast Nat.card_pos) (by exact_mod_cast hc)
      _ = 7 * Real.log μ := by rw [Real.log_pow]; norm_num
      _ ≤ (8 + Real.log D / Real.log 2) * Real.log (Nat.card X) := by nlinarith
  · rw [← hcard]
    rw [hcardq] at hc
    have hlog : (Nat.log 2 μ : ℝ) ≤ Real.log D / Real.log 2 :=
      (natLog_two_le (by omega)).trans hlogD
    calc Real.log (Nat.card ρ.range) ≤ Real.log ((μ : ℝ) ^ (1 + Nat.log 2 μ)) :=
          Real.log_le_log (by exact_mod_cast Nat.card_pos) (by exact_mod_cast hc.le)
      _ = (1 + Nat.log 2 μ) * Real.log μ := by rw [Real.log_pow]; push_cast; ring
      _ ≤ (8 + Real.log D / Real.log 2) * Real.log (Nat.card X) := by
        have : (1 + (Nat.log 2 μ : ℝ)) ≤ 8 + Real.log D / Real.log 2 := by linarith
        exact mul_le_mul this hlogμ hnn (by linarith)

/-- `log m! ≤ m log m`. -/
theorem log_factorial_le (m : ℕ) : Real.log m.factorial ≤ m * Real.log m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  calc Real.log m.factorial ≤ Real.log ((m : ℝ) ^ m) :=
        Real.log_le_log (by exact_mod_cast Nat.factorial_pos m) h
    _ = m * Real.log m := Real.log_pow _ _

section Alternating

variable {D : ℕ} {α : Type} [Finite α] (H : Subgroup (Perm α)) [hp : IsPreprimitive H α]

/-- **The alternating case.** A primitive almost simple group with socle `Alt(m)`, `7 ≤ m ≤ D`, acts
on `k`-subsets, or `m = O(log n)` and so `log |H| = O(log D log n)`. -/
theorem alternating_alternatives {S : Type} [Group S] (hS : Maroti.IsAlmostSimpleWith H S)
    {m : ℕ} (hm : 7 ≤ m) (hmD : m ≤ D) (eS : S ≃* alternatingGroup (Fin m)) :
    Maroti.IsSubsetActionType H ∨
      Real.log (Nat.card H) ≤ (8 / Real.log 2) * Real.log D * Real.log (Nat.card α) := by
  classical
  cases nonempty_fintype α
  obtain ⟨hm_le, -, -, -, ψ, hψ, hA, -⟩ :=
    Maroti.Alternating.exists_injective_hom_perm_of_ne_six H hp hS (by omega) (by omega) eS
  have : Nonempty α := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card α)).1
  obtain ⟨ω⟩ := ‹Nonempty α›
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let G' := ψ.range
  let E : H ≃* G' := MonoidHom.ofInjective hψ
  let _ : MulAction G' α := MulAction.compHom α E.symm.toMonoidHom
  have hE (g : H) (x : α) : (E g : G') • x = g • x := by
    change (E.symm (E g)) • x = g • x
    rw [E.symm_apply_apply]
  have htr : IsPretransitive G' α := ⟨fun x y => by
    obtain ⟨g, hg⟩ := exists_smul_eq H x y
    exact ⟨E g, (hE g x).trans hg⟩⟩
  have hstab : (stabilizer G' ω).map G'.subtype = (stabilizer H ω).map ψ := by
    ext p
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨g', rfl⟩ := E.surjective g
      exact ⟨g', by simpa [mem_stabilizer_iff, hE] using hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨E g, by simpa [mem_stabilizer_iff, hE] using hg, rfl⟩
  by_cases htrans : IsPretransitive ((stabilizer G' ω).map G'.subtype) (Fin m)
  · right
    have hdeg : (m : ℝ) ≤ (8 / Real.log 2) * Real.log (Nat.card α) := by
      by_cases hprim : IsPreprimitive ((stabilizer G' ω).map G'.subtype) (Fin m)
      · have h1 := GI.AlternatingActions.primitive_stabilizer_natural_degree_log_bound G' hA
          (by simpa using (by omega : 3 ≤ m)) (by omega) ω hprim
        simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
        have hl : 0 ≤ Real.log (Nat.card α) := Real.log_natCast_nonneg _
        have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h3 : (6 / Real.log 2) * Real.log (Fintype.card α) ≤
            (8 / Real.log 2) * Real.log (Nat.card α) := by
          rw [Nat.card_eq_fintype_card] at hl ⊢
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (by norm_num) h2.le) hl
        exact h1.trans h3
      · have h1 := GI.AlternatingActions.imprimitive_stabilizer_natural_degree_log_bound G' hA ω
          (⟨0, by omega⟩ : Fin m) hprim
        simpa [Nat.card_eq_fintype_card] using h1
    have hc : Nat.card H ≤ m.factorial := by
      calc Nat.card H = Nat.card G' := Nat.card_congr E.toEquiv
        _ ≤ Nat.card (Perm (Fin m)) := Subgroup.card_le_card_group G'
        _ = m.factorial := by rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    have hlogm : Real.log m ≤ Real.log D :=
      Real.log_le_log (by positivity) (by exact_mod_cast hmD)
    have hlogm0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
    calc Real.log (Nat.card H) ≤ Real.log m.factorial :=
          Real.log_le_log (by exact_mod_cast Nat.card_pos) (by exact_mod_cast hc)
      _ ≤ m * Real.log m := log_factorial_le m
      _ ≤ (8 / Real.log 2) * Real.log (Nat.card α) * Real.log D :=
          mul_le_mul hdeg hlogm hlogm0 (le_trans (by positivity) hdeg)
      _ = _ := by ring
  · left
    rw [hstab] at htrans
    exact Maroti.Alternating.intransitive_isSubsetActionType H hp ω (by omega) hm_le ψ hA htrans

end Alternating

/-- The constants of `almostSimple_alternatives`. -/
noncomputable def asC₁ : ℝ := 8 / Real.log 2

theorem asC₁_nonneg : 0 ≤ asC₁ := by
  have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  unfold asC₁
  positivity

/-- **The alternatives for almost simple groups.** -/
theorem almostSimple_alternatives {D : ℕ} (hD : 6 ≤ D) {α : Type} [Finite α]
    (H : Subgroup (Perm α)) [hp : IsPreprimitive H α] {S : Type} [Group S]
    (hS : Maroti.IsAlmostSimpleWith H S) (hE : EmbedsInSym D S) :
    Maroti.IsSubsetActionType H ∨
      Real.log (Nat.card H) ≤ (asC₁ * Real.log D + 17) * Real.log (Nat.card α) := by
  have hSn := hS.isNonabelianSimple
  have : IsSimpleGroup S := hSn.1
  have hfin : Finite S := hS.finite
  have hαn := hS.nontrivial_alpha
  have h2α : 2 ≤ Nat.card α := Finite.one_lt_card
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log (Nat.card α) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h2α)
  have hlogD : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hC : 0 ≤ asC₁ * Real.log D := mul_nonneg asC₁_nonneg hlogD
  have hHS : Nat.card H ≤ Nat.card S ^ 2 :=
    hS.card_le_card_mulAut.trans (autBound hSn.2)
  have hHlog : Real.log (Nat.card H) ≤ 2 * Real.log (Nat.card S) := by
    calc Real.log (Nat.card H) ≤ Real.log ((Nat.card S : ℝ) ^ 2) :=
          Real.log_le_log (by exact_mod_cast Nat.card_pos) (by exact_mod_cast hHS)
      _ = 2 * Real.log (Nat.card S) := by rw [Real.log_pow]; norm_num
  by_cases halt : ∃ m, 5 ≤ m ∧ Nonempty (S ≃* alternatingGroup (Fin m))
  · obtain ⟨m, hm, ⟨eS⟩⟩ := halt
    have hmD : m ≤ D := by
      have hgS : GammaHat D S := gammaHat_simple_iff.2 hE
      exact hgS.le_of_alternating_section hm ⊤
        (eS.toMonoidHom.comp (Subgroup.topEquiv (G := S)).toMonoidHom)
        (eS.surjective.comp Subgroup.topEquiv.surjective)
    rcases Nat.lt_or_ge m 7 with hm7 | hm7
    · right
      have hcard : Nat.card S ≤ 360 := by
        have h2 : 2 * Nat.card S = m.factorial := by
          have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
          have := two_mul_card_alternatingGroup (α := Fin m)
          rw [Fintype.card_perm, Fintype.card_fin] at this
          rw [Nat.card_congr eS.toEquiv, Nat.card_eq_fintype_card]
          exact this
        have h3 : m.factorial ≤ 720 := Nat.factorial_le (show m ≤ 6 by omega)
        omega
      have h3 : Nat.card H ≤ 2 ^ 17 := hHS.trans ((Nat.pow_le_pow_left hcard 2).trans (by norm_num))
      calc Real.log (Nat.card H) ≤ Real.log ((2 : ℝ) ^ 17) :=
            Real.log_le_log (by exact_mod_cast Nat.card_pos) (by exact_mod_cast h3)
        _ = 17 * Real.log 2 := by rw [Real.log_pow]; norm_num
        _ ≤ 17 * Real.log (Nat.card α) := by linarith
        _ ≤ _ := by nlinarith
    · rcases alternating_alternatives H hS hm7 hmD eS with h | h
      · exact Or.inl h
      · refine Or.inr (h.trans ?_)
        unfold asC₁
        nlinarith
  · right
    have hnot : ∀ m, 5 ≤ m → IsEmpty (S ≃* alternatingGroup (Fin m)) := fun m hm =>
      ⟨fun e => halt ⟨m, hm, ⟨e⟩⟩⟩
    obtain ⟨T, -, -, -, -, -, ⟨eT⟩⟩ := id hS
    have hl := log_card_simple_le hnot hE
      (T.subtype.comp eT.symm.toMonoidHom) (T.subtype_injective.comp eT.symm.injective)
    calc Real.log (Nat.card H) ≤ 2 * Real.log (Nat.card S) := hHlog
      _ ≤ 2 * ((8 + Real.log D / Real.log 2) * Real.log (Nat.card α)) := by linarith
      _ ≤ _ := by
        unfold asC₁
        have h4 : 2 * (Real.log D / Real.log 2) ≤ 8 / Real.log 2 * Real.log D := by
          rw [div_mul_eq_mul_div, mul_div_assoc']
          exact div_le_div_of_nonneg_right (by nlinarith) hlog2.le
        nlinarith

end GI.Degree
