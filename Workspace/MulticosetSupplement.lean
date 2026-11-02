import Workspace.MulticosetDerived
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow

/-!
# Lemma A.19: the Frattini descent to a solvable supplement

The proof in the paper (the Frattini reduction of [LM, Theorem 1.3]) keeps a pair
`(S, K)` with `SN = H` and `K = S ∩ N`. If `K` is not nilpotent, it picks a nonnormal
Sylow subgroup `P` of `K` and passes to a subgroup `S₁ ≤ S` normalizing `P` with
`S₁ K = S` (Frattini's argument), so that `K₁ = S₁ ∩ K ≤ N_K(P) < K`. When `K` is
nilpotent, `S/K ≅ H/N` is solvable, hence `S` is solvable.

The paper builds `S₁` from corrected generators `k s⁻¹`; these lie in `N_S(P)`, and
the only properties used are `S₁ K = S` and `S₁ ∩ K ≤ N_K(P)`. We take `S₁ = N_S(P)`,
which has both properties by Frattini's argument (`Sylow.normalizer_sup_eq_top`).
The polynomial-time clause (Sylow construction and conjugacy, [LM, Theorem 3.1]) is
a stage-2 obligation.
-/

namespace GI.Multicoset

variable {G : Type*} [Group G]

/-- The nilpotent end of the descent: if `S ≤ H`, `SN = H` and `S ∩ N` is nilpotent, then
`S` is solvable, because `S/(S ∩ N)` embeds in the solvable `H/N`. -/
theorem solvable_of_nilpotent_kernel {H N S : Subgroup G} [(N.subgroupOf H).Normal]
    [IsSolvable (H ⧸ N.subgroupOf H)] (hSH : S ≤ H)
    [Group.IsNilpotent (N.subgroupOf S)] : IsSolvable S := by
  let ψ : S →* H ⧸ N.subgroupOf H :=
    (QuotientGroup.mk' (N.subgroupOf H)).comp (Subgroup.inclusion hSH)
  apply solvable_of_ker_le_range (N.subgroupOf S).subtype ψ
  intro s hs
  have hN : ((s : G)) ∈ N := by
    have : (Subgroup.inclusion hSH s : H) ∈ N.subgroupOf H := (QuotientGroup.eq_one_iff _).mp hs
    exact this
  exact ⟨⟨s, hN⟩, rfl⟩

/-- One Frattini step: if `S ∩ N` is not nilpotent, there is `S₁ ≤ S` with `S₁ N = S N`
and `N ∩ S₁ < N ∩ S`. -/
theorem frattini_step [Finite G] {N S : Subgroup G} (hn : Normalizes S N)
    (hnil : ¬ Group.IsNilpotent (N.subgroupOf S)) :
    ∃ S₁ : Subgroup G, S₁ ≤ S ∧ S ≤ S₁ ⊔ N ∧ N ⊓ S₁ < N ⊓ S := by
  classical
  set K : Subgroup S := N.subgroupOf S with hKdef
  haveI : K.Normal := ⟨fun k hk s => by
    change ((s : G) * k * (s : G)⁻¹) ∈ N
    exact hn s s.2 k hk⟩
  -- a nonnormal Sylow subgroup `P` of `K`
  have htfae := (isNilpotent_of_finite_tfae (G := K)).out 0 3
  obtain ⟨p, hp, P, hP⟩ : ∃ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p K),
      ¬ (P : Subgroup K).Normal := by
    by_contra h
    push Not at h
    exact hnil (htfae.mpr fun p hp P => h p hp P)
  -- Frattini's argument in `S`
  set T : Subgroup S := Subgroup.normalizer ((P : Subgroup K).map K.subtype : Set S) with hT
  have hfr : T ⊔ K = ⊤ := Sylow.normalizer_sup_eq_top P
  refine ⟨T.map S.subtype, Subgroup.map_subtype_le T, ?_, ?_⟩
  · intro s hs
    have : (⟨s, hs⟩ : S) ∈ T ⊔ K := hfr ▸ Subgroup.mem_top _
    have hm := Subgroup.mem_map_of_mem S.subtype this
    rw [Subgroup.map_sup, hKdef, Subgroup.subgroupOf_map_subtype] at hm
    exact (sup_le_sup_left (inf_le_left : N ⊓ S ≤ N) _) hm
  · refine lt_of_le_of_ne (inf_le_inf_left _ (Subgroup.map_subtype_le T)) ?_
    intro heq
    apply hP
    -- `K ≤ T`, so `P` is normal in `K`
    have hKT : K ≤ T := by
      intro k hk
      have hk' : (k : G) ∈ N ⊓ T.map S.subtype := by
        rw [heq]; exact ⟨hk, k.2⟩
      obtain ⟨t, ht, hte⟩ := hk'.2
      have : t = k := Subtype.ext hte
      rw [← this]; exact ht
    have hle : (P : Subgroup K).map K.subtype ≤ K := Subgroup.map_subtype_le _
    have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hKT
    have hcomap : ((P : Subgroup K).map K.subtype).subgroupOf K = (P : Subgroup K) :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [hcomap] at hnorm
    exact hnorm

/-- The descent: from any `S ≤ H` with `S N = H`, the Frattini steps reach a solvable
`S' ≤ S` with `S' N = H`. Induction on `|N ∩ S|`, which drops at each step. -/
theorem frattini_descent [Finite G] {H N : Subgroup G} [(N.subgroupOf H).Normal]
    [IsSolvable (H ⧸ N.subgroupOf H)] (hNH : N ≤ H) (hn : Normalizes H N) :
    ∀ (k : ℕ) (S : Subgroup G), Nat.card (N ⊓ S : Subgroup G) ≤ k → S ≤ H → S ⊔ N = H →
      ∃ S' : Subgroup G, S' ≤ S ∧ IsSolvable S' ∧ S' ⊔ N = H := by
  intro k
  induction k with
  | zero =>
    intro S hk
    have : 0 < Nat.card (N ⊓ S : Subgroup G) := Nat.card_pos
    omega
  | succ k ih =>
    intro S hk hSH hSN
    by_cases hnil : Group.IsNilpotent (N.subgroupOf S)
    · exact ⟨S, le_rfl, solvable_of_nilpotent_kernel (N := N) hSH, hSN⟩
    · obtain ⟨S₁, hS₁S, hSS₁, hlt⟩ := frattini_step (hn.mono hSH) hnil
      have hcard : Nat.card (N ⊓ S₁ : Subgroup G) < Nat.card (N ⊓ S : Subgroup G) := by
        rcases Nat.lt_or_ge (Nat.card (N ⊓ S₁ : Subgroup G)) (Nat.card (N ⊓ S : Subgroup G))
          with h | h
        · exact h
        · exact absurd (Subgroup.eq_of_le_of_card_ge hlt.le h) hlt.ne
      have hS₁N : S₁ ⊔ N = H := le_antisymm (sup_le (hS₁S.trans hSH) hNH)
        (hSN ▸ sup_le hSS₁ le_sup_right)
      obtain ⟨S', hS'S₁, hs, hS'N⟩ := ih S₁ (by omega) (hS₁S.trans hSH) hS₁N
      exact ⟨S', hS'S₁.trans hS₁S, hs, hS'N⟩

/-- Existence form of Lemma A.19, by the descent started at `(S, K) = (H, N)`. -/
theorem exists_solvable_supplement_descent [Finite G] {H N : Subgroup G}
    [(N.subgroupOf H).Normal] [IsSolvable (H ⧸ N.subgroupOf H)] (hNH : N ≤ H)
    (hn : Normalizes H N) : ∃ S : Subgroup G, S ≤ H ∧ IsSolvable S ∧ S ⊔ N = H := by
  obtain ⟨S, hSH, hs, hSN⟩ := frattini_descent hNH hn _ H le_rfl le_rfl (sup_eq_left.mpr hNH)
  exact ⟨S, hSH, hs, hSN⟩

/-- `S N = H` as subgroups gives the factorization `h = n s` used throughout. -/
theorem exists_kernel_mul_of_sup_eq {H N S : Subgroup G} (hn : Normalizes S N)
    (hSN : S ⊔ N = H) : ∀ h ∈ H, ∃ n ∈ N, ∃ s ∈ S, h = n * s := by
  intro h hh
  rw [← hSN, sup_comm] at hh
  -- `N ⊔ S = N S` since `S` normalizes `N`
  have key : ∀ x ∈ Subgroup.closure ((N : Set G) ∪ S), ∃ n ∈ N, ∃ s ∈ S, x = n * s := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨x, hx, 1, S.one_mem, by simp⟩
      · exact ⟨1, N.one_mem, x, hx, by simp⟩
    | one => exact ⟨1, N.one_mem, 1, S.one_mem, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨n, hn', s, hs, rfl⟩ := hx
      obtain ⟨n', hn'', s', hs', rfl⟩ := hy
      exact ⟨n * (s * n' * s⁻¹), N.mul_mem hn' (hn s hs n' hn''), s * s', S.mul_mem hs hs',
        by group⟩
    | inv x _ hx =>
      obtain ⟨n, hn', s, hs, rfl⟩ := hx
      exact ⟨s⁻¹ * n⁻¹ * s, by simpa using hn.inv hs (N.inv_mem hn'), s⁻¹, S.inv_mem hs,
        by group⟩
  rw [Subgroup.sup_eq_closure] at hh
  exact key h hh

end GI.Multicoset
