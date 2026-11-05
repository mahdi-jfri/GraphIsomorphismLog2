module

public import Workspace.Schreier
public import Workspace.QuadraticSocleBudget

@[expose] public section

/-!
# No marked step at an almost simple group, and the socle–outer budget bound

This file proves the two consequences of Schreier's conjecture (`GI.schreier`)
used in Section A.2 (Lemma A.8 and Theorem A.9):

1. **No visible marked step at an almost simple group** (`no_almostSimple_step`,
   `sigma_eq_zero_or_proper_subgroup`). If `H ≤ Sym(V)` is transitive on `|V| ≥ 2`
   points and `socle H` is nonabelian simple, then any transitive normal subgroup
   of `H` is nontrivial and therefore contains `socle H`. Thus any quotient of `H`
   by a transitive normal subgroup factors through `H / socle H ↪ Out(socle H)`,
   which is solvable by `GI.schreier` and cannot be `Alt(k)` for `k ≥ 5`. Every
   marked chain starting at `H` either has weight zero or first restricts to a
   proper subgroup `L < H`.
2. **Socle–outer budget bound** (`radicalFree_chain_bound`,
   `quadratic_socle_sigma_bound`). For a radical-free group `H` with socle `E`
   and `s` simple factors `T_i`, the outer factor group `∏ Out(T_i)` is solvable
   by `GI.schreier` and contributes no marks, so `σ(H) ≤ 6 v₃(|E|) + 3(s - 1)`.
   When `|E| ≤ d²`, this gives `σ(H) ≤ (12 / log 3 + 6 / log 2) log d`.
-/

namespace GI.HbudAlmostSimple

open RadicalSocle SocleOuter

/-- A group whose socle is nonabelian simple has no nontrivial solvable normal
subgroup: such a subgroup would contain a minimal normal subgroup, which lies in
the simple socle and so equals it. -/
theorem radicalFree_of_simple_socle {G : Type*} [Group G] [Finite G]
    (hs : IsSimpleGroup (socle G)) (hna : ∃ x y : socle G, x * y ≠ y * x) :
    ∀ R : Subgroup G, R.Normal → Group.IsSolvable R → R = ⊥ := by
  intro R hR hsol
  by_contra hne
  have := hR
  obtain ⟨M, hM, hMR⟩ := exists_minimal_normal_le R hne
  have hMS := minimalNormal_le_socle hM
  have : M.Normal := hM.1
  have : (M.subgroupOf (socle G)).Normal := Subgroup.Normal.subgroupOf hM.1 _
  rcases hs.eq_bot_or_eq_top_of_normal (M.subgroupOf (socle G)) with hb | ht
  · exact hM.2.1 ((Subgroup.subgroupOf_eq_bot.mp hb).eq_bot_of_le hMS)
  · have hSR : socle G ≤ R := (Subgroup.subgroupOf_eq_top.mp ht).trans hMR
    have : Group.IsSolvable R := hsol
    have hsolS : Group.IsSolvable (socle G) :=
      solvable_of_solvable_injective (f := Subgroup.inclusion hSR)
        (Subgroup.inclusion_injective hSR)
    have := hs
    obtain ⟨x, y, hxy⟩ := hna
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolS x y)

variable {V : Type*} [Fintype V]

/-- The composite homomorphism `H → MulAut (socle H) → OuterAut (socle H)`. -/
def toOuterAut (H : Subgroup (Equiv.Perm V)) : H →* OuterAut (socle H) :=
  (QuotientGroup.mk' (innerAut (socle H))).comp (socleConjugation (G := H))

/-- For a radical-free group `H`, the kernel of `toOuterAut H` is contained in `socle H`. -/
theorem toOuterAut_ker_le_socle {H : Subgroup (Equiv.Perm V)}
    (radicalFree : ∀ R : Subgroup H, R.Normal → Group.IsSolvable R → R = ⊥) :
    (toOuterAut H).ker ≤ socle H := by
  intro h hh
  change QuotientGroup.mk' (innerAut (socle H)) (socleConjugation h) = 1 at hh
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hh
  obtain ⟨s, hs⟩ := hh
  have hconj : socleConjugation (G := H) (s : H) = MulAut.conj s :=
    MulAut.conjNormal_val
  have heq : (s : H) = h :=
    socleConjugation_injective radicalFree (hconj.trans hs)
  rw [← heq]
  exact s.property

/-- **No visible marked step at an almost simple group.** If `H ≤ Sym(V)` is
transitive on `|V| ≥ 2` points and `socle H` is nonabelian simple, then no
`VisibleStep` with `k ≥ 5` can start at `H`. -/
theorem no_almostSimple_step {a : V} {H L : Subgroup (Equiv.Perm V)}
    [MulAction.IsPretransitive H V] (hcard : 2 ≤ Fintype.card V)
    (hs : IsSimpleGroup (socle H)) (hna : ∃ x y : socle H, x * y ≠ y * x)
    {k : ℕ} (hk : 5 ≤ k) (s : VisibleStep a H L k) : False := by
  have rf := radicalFree_of_simple_socle hs hna
  -- 1. `s.quotient.ker ≠ ⊥` because `L` is transitive on `V` and `|V| ≥ 2`.
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨b, hba⟩ := exists_ne a
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H a b
  obtain ⟨l, hl⟩ := s.transitiveKernel g
  have hker_ne : s.quotient.ker ≠ ⊥ := by
    intro hbot
    have hlker : Subgroup.inclusion s.lower l ∈ s.quotient.ker :=
      (s.kernel _).mpr l.property
    rw [hbot, Subgroup.mem_bot] at hlker
    have hlone : (l : Equiv.Perm V) = 1 := congrArg Subtype.val hlker
    change (l : Equiv.Perm V) • a = g • a at hl
    rw [hlone, one_smul, hg] at hl
    exact hba hl.symm
  -- 2. Every nontrivial normal subgroup of `H` contains the simple socle `socle H`.
  obtain ⟨M, hM, hMker⟩ := exists_minimal_normal_le s.quotient.ker hker_ne
  have hMS := minimalNormal_le_socle hM
  have : M.Normal := hM.1
  have : (M.subgroupOf (socle H)).Normal := Subgroup.Normal.subgroupOf hM.1 _
  have hsoc_ker : socle H ≤ s.quotient.ker := by
    rcases hs.eq_bot_or_eq_top_of_normal (M.subgroupOf (socle H)) with hb | ht
    · exfalso
      exact hM.2.1 ((Subgroup.subgroupOf_eq_bot.mp hb).eq_bot_of_le hMS)
    · exact (Subgroup.subgroupOf_eq_top.mp ht).trans hMker
  -- 3. Factor `s.quotient` through `(toOuterAut H).range ≤ OuterAut (socle H)`.
  have hkills : (toOuterAut H).rangeRestrict.ker ≤ s.quotient.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact (toOuterAut_ker_le_socle rf).trans hsoc_ker
  let qbar := HomDescent.factor (toOuterAut H).rangeRestrict
    (toOuterAut H).rangeRestrict_surjective s.quotient hkills
  have hqbar : Function.Surjective qbar :=
    HomDescent.factor_surjective _ _ _ _ s.onto
  have : IsSimpleGroup (socle H) := hs
  have : Group.IsSolvable (OuterAut (socle H)) := GI.schreier (socle H) hna
  have : Group.IsSolvable (toOuterAut H).range :=
    solvable_of_subgroup_le (le_top : (toOuterAut H).range ≤ ⊤)
  exact no_alternating_surjection_of_solvable hk qbar hqbar

omit [Fintype V] in
/-- Any `MarkedChain` starting at a group `H` with no visible steps either has
zero weight or first restricts to a proper subgroup `L < H` with the same weight. -/
theorem first_proper_restriction {cutoff w : ℕ} {a : V}
    {H H' : Subgroup (Equiv.Perm V)}
    (hno : ∀ (L : Subgroup (Equiv.Perm V)) (k : ℕ), cutoff ≤ k → VisibleStep a H L k → False)
    (chain : MarkedChain cutoff a H' w) (hH : H' = H) :
    w = 0 ∨ ∃ L : Subgroup (Equiv.Perm V), L < H ∧ MarkedChain cutoff a L w := by
  induction chain with
  | stop K => exact Or.inl rfl
  | @restrict K L w hle tail ih =>
      subst hH
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact ih rfl
      · exact Or.inr ⟨L, hlt, tail⟩
  | @mark K L w k hk s _ _ =>
      subst hH
      exact (hno L k hk s).elim

/-- If no `VisibleStep` starts at `H`, then either `σ(H) = 0` or `σ(H) ≤ σ(L)`
for a proper subgroup `L < H`. -/
theorem sigma_eq_zero_or_proper_subgroup {cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (a : V) (H : Subgroup (Equiv.Perm V))
    (hno : ∀ (L : Subgroup (Equiv.Perm V)) (k : ℕ), cutoff ≤ k → VisibleStep a H L k → False) :
    sigma cutoff a H = 0 ∨
      ∃ L : Subgroup (Equiv.Perm V), L < H ∧ sigma cutoff a H ≤ sigma cutoff a L := by
  rcases first_proper_restriction hno (sigma_achieved hcutoff a H) rfl with hz | ⟨L, hlt, hw⟩
  · exact Or.inl hz
  · exact Or.inr ⟨L, hlt, sigma_bounds_chain hcutoff hw⟩

/-- **Socle–outer chain bound** from `GI.schreier`: for a radical-free group `G`,
any quotient chain with cutoff `≥ 64` has weight at most `6 v₃(|socle G|) + 3(s - 1)`. -/
theorem radicalFree_chain_bound {G : Type*} [Group G] [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {cutoff w : ℕ} (hcutoff : 64 ≤ cutoff) {H : Subgroup G}
    (chain : QuotientChain cutoff H w) :
    w ≤ 6 * padicValNat 3 (Nat.card (socle G)) +
      3 * (Nat.card (MinimalNormals (socle G)) - 1) := by
  refine radicalFree_chain_bound_of_outer_solvable radicalFree (fun N => ?_) hcutoff chain
  have := socle_intrinsic_factor_simple N
  exact GI.schreier N.val (socle_intrinsic_factor_nonabelian radicalFree N)

/-- **Quadratic socle budget bound** from `GI.schreier`: for a radical-free
permutation group `H` with `|socle H| ≤ d²`, any cutoff `≥ 64` gives
`σ(H) ≤ (12 / log 3 + 6 / log 2) log d`. -/
theorem quadratic_socle_sigma_bound {H : Subgroup (Equiv.Perm V)}
    (radicalFree : ∀ N : Subgroup H, N.Normal → Group.IsSolvable N → N = ⊥)
    {d : ℕ} (orderBound : Nat.card (socle H) ≤ d ^ 2)
    {cutoff : ℕ} (hcutoff : 64 ≤ cutoff) (a : V) :
    (sigma cutoff a H : ℝ) ≤ (12 / Real.log 3 + 6 / Real.log 2) * Real.log (d : ℝ) := by
  refine quadratic_socle_sigma_bound_of_outer_solvable radicalFree orderBound
    (fun K => ?_) hcutoff a
  have := socle_intrinsic_factor_simple K
  exact GI.schreier K.val (socle_intrinsic_factor_nonabelian radicalFree K)

end GI.HbudAlmostSimple
