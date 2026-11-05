module

public import Workspace.AutWreath
public import Workspace.HbudAlmostSimple
public import Workspace.AffineRecognitionPrimitive
public import Workspace.AlternatingSocleAlternative
public import Workspace.AlternatingNaturalRealization
public import Workspace.SocleFactorCaps

@[expose] public section

/-!
# The cases of Lemma A.8 (primitive valuation and budget cases)

Each theorem below gives, for one class of primitive groups, either a prime
`ℓ ∈ {3,5}` with `6 v_ℓ(|G|) ≤ A log n` (affine actions and non-natural,
non-Johnson alternating-socle actions) or a direct budget bound
`σ(G, Ω) ≤ A log n` (regular, diagonal, and twisted-wreath actions with
`|socle(G)| ≤ n²`, proved via `GI.schreier` in `Workspace/HbudAlmostSimple.lean`).
-/

namespace GI.PrimitiveValuation

open RadicalSocle

/-! ### The affine case -/

/-- Affine case of Lemma A.8. A primitive group with a nontrivial abelian normal
subgroup lies in `AGL_d(p)` acting on `p^d = n` points (constructed in
`AffineRecognition`). The prime `ℓ ∈ {3,5}` is chosen different from `p`; then the
translations contribute nothing and the matrix estimate bounds `v_ℓ(|GL_d(p)|)`. -/
theorem affine_valuation {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPreprimitive H (Fin n)] (N : Subgroup H) [N.Normal] (hne : N ≠ ⊥)
    (comm : ∀ x y : N, x * y = y * x) (a : Fin n) :
    ∃ ℓ : ℕ, (ℓ = 3 ∨ ℓ = 5) ∧
      6 * (padicValNat ℓ (Nat.card H) : ℝ) ≤ (12 / Real.log 2) * Real.log n := by
  obtain ⟨p, hp, d, ⟨basis⟩⟩ := PrimitiveStructure.abelian_normal_coordinates N hne comm a
  letI : Fact p.Prime := ⟨hp⟩
  have regular := PrimitiveStructure.abelian_normal_regular N hne comm a
  have hdegree : n = (Fintype.card (ZMod p)) ^ d := by
    simpa only [Fintype.card_fin] using AffineRecognition.degree_eq N a regular basis
  have hH := AffineRecognition.permutation_group_le_affine_range H N a regular basis
  obtain ⟨q, hq, hv⟩ := MatrixValuation.affine_subgroup_uniform_bound (ZMod p) d ⊤
  have hc : Nat.card (⊤ : Subgroup (MatrixValuation.AffineGroup (ZMod p) d)) =
      Nat.card (MatrixValuation.AffineGroup (ZMod p) d) := Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [hc] at hv
  haveI : Fact q.Prime := ⟨by rcases hq with rfl | rfl <;> decide⟩
  have hdvd := (Subgroup.card_dvd_of_le hH).trans
    (Subgroup.card_range_dvd (AffineRecognition.physicalAffineAction N a regular basis))
  have hm := primeValuation_mono (p := q)
    (Nat.ne_of_gt (Nat.card_pos (α := MatrixValuation.AffineGroup (ZMod p) d))) hdvd
  have hmr : (padicValNat q (Nat.card H) : ℝ) ≤
      padicValNat q (Nat.card (MatrixValuation.AffineGroup (ZMod p) d)) := by exact_mod_cast hm
  have hv' : 6 * (padicValNat q (Nat.card (MatrixValuation.AffineGroup (ZMod p) d)) : ℝ) ≤
      (12 / Real.log 2) * Real.log n := by
    simpa only [hdegree, Nat.cast_pow] using hv
  exact ⟨q, hq, (mul_le_mul_of_nonneg_left hmr (by norm_num)).trans hv'⟩

/-! ### Almost simple groups -/

/-- A group whose socle is nonabelian simple has no nontrivial solvable normal
subgroup: such a subgroup would contain a minimal normal subgroup, which lies in
the simple socle and so equals it. -/
theorem radicalFree_of_simple_socle {G : Type*} [Group G] [Finite G]
    (hs : IsSimpleGroup (socle G)) (hna : ∃ x y : socle G, x * y ≠ y * x) :
    ∀ R : Subgroup G, R.Normal → Group.IsSolvable R → R = ⊥ :=
  HbudAlmostSimple.radicalFree_of_simple_socle hs hna

/-- The order of a group with nonabelian simple socle divides `|Aut(socle)|`:
conjugation on the socle is faithful. -/
theorem card_dvd_aut_socle {G : Type*} [Group G] [Finite G]
    (radicalFree : ∀ R : Subgroup G, R.Normal → Group.IsSolvable R → R = ⊥) :
    Nat.card G ∣ Nat.card (MulAut (socle G)) :=
  Subgroup.card_dvd_of_injective _ (socleConjugation_injective radicalFree)

/-! ### Regular, diagonal, and twisted-wreath types: `|socle(G)| ≤ n²` -/

/-- The constant of the regular/diagonal case of Lemma A.8. -/
noncomputable def diagonalBudgetConstant : ℝ := 12 / Real.log 3 + 6 / Real.log 2

/-- Regular/diagonal case of Lemma A.8: for a radical-free permutation group `H`
with `|socle H| ≤ n²`, the socle–outer chain reduction and Schreier's conjecture
give `σ(H) ≤ 6 v₃(|socle H|) + 3(s - 1) ≤ (12 / log 3 + 6 / log 2) log n`. -/
theorem socle_sigma_bound {n cutoff : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (radicalFree : ∀ R : Subgroup H, R.Normal → Group.IsSolvable R → R = ⊥)
    (hdeg : Nat.card (socle H) ≤ n ^ 2) (hcutoff : 64 ≤ cutoff) (a : Fin n) :
    (sigma cutoff a H : ℝ) ≤ diagonalBudgetConstant * Real.log n :=
  HbudAlmostSimple.quadratic_socle_sigma_bound radicalFree hdeg hcutoff a

/-! ### Alternating socle, not natural and not a Johnson subset action -/

/-- The action of `G ≤ Sym(n)` is a Johnson subset action: up to relabeling the
`n` points as the `t`-subsets of an `m`-set, with `2 ≤ t ≤ m/2`, the group lies
between the images of `Alt(m)` and of `Sym(m)` in their action on `t`-subsets. -/
def JohnsonSubsetAction {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∃ m t : ℕ, 2 ≤ t ∧ 2 * t ≤ m ∧ ∃ e : Fin n ≃ Johnson.SubsetVertex (Fin m) t,
    (alternatingGroup (Fin m)).map (Johnson.subsetAction t) ≤
      G.map (relabelPerm e).toMonoidHom ∧
    G.map (relabelPerm e).toMonoidHom ≤ Johnson.subsetImage t

/-- The constant of the alternating-socle case. -/
noncomputable def alternatingConstant : ℝ := max (24 / Real.log 2) (2160 / Real.log 3)

/-- Alternating-socle case of Lemma A.8. The socle `Alt(m)` is realized naturally
(Aut(Alt(m)) for the actual socle, `AlternatingSocleEmbedding`), and the
point stabilizer acts on the natural `m`-set. Intransitive gives the natural or a
Johnson action, which are excluded. Imprimitive and primitive stabilizers give
`log n ≥ c m` (the latter through Bochert's index bound), so
`v_3(|G|) ≤ v_3(m!) = O(log n)`. Bounded `m ≤ 6` is a finite check. -/
theorem alternating_socle_valuation {n m : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPreprimitive H (Fin n)]
    (radicalFree : ∀ N : Subgroup H, N.Normal → Group.IsSolvable N → N = ⊥)
    (e : socle H ≃* alternatingGroup (Fin m)) (hn : 3 ≤ n)
    (notNatural : ¬ alternatingGroup (Fin n) ≤ H) (notJohnson : ¬ JohnsonSubsetAction H) :
    6 * (padicValNat 3 (Nat.card H) : ℝ) ≤ alternatingConstant * Real.log n := by
  classical
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  by_cases hm : m ≤ 6
  · have hv : 6 * (padicValNat 3 (Nat.card H) : ℝ) ≤ 2160 := by
      exact_mod_cast small_alternating_socle_three_valuation radicalFree e hm
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hlog : Real.log 3 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    calc 6 * (padicValNat 3 (Nat.card H) : ℝ) ≤ 2160 := hv
      _ = (2160 / Real.log 3) * Real.log 3 := by field_simp
      _ ≤ (2160 / Real.log 3) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ alternatingConstant * Real.log n :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hlogn
  have hm7 : 7 ≤ m := by omega
  haveI : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa only [Fintype.card_fin] using (show 1 < n by omega))
  let hdegree : Fintype.card (Fin m) = 5 ∨ 7 ≤ Fintype.card (Fin m) :=
    Or.inr (by simpa only [Fintype.card_fin] using hm7)
  let K := (AlternatingSocle.naturalHom e hdegree).range
  let E : H ≃* K := AlternatingSocle.naturalEquiv radicalFree e hdegree
  letI : MulAction K (Fin n) := PhysicalTransport.action E
  letI : MulAction.IsPreprimitive K (Fin n) := PhysicalTransport.preprimitive E
  have hold : (MulAction.toPermHom H (Fin n)).range = H := by
    change H.subtype.range = H
    exact Subgroup.range_subtype H
  have himage : (MulAction.toPermHom K (Fin n)).range = H :=
    (PhysicalTransport.image_eq E).trans hold
  have giant : alternatingGroup (Fin m) ≤ K :=
    AlternatingSocle.alternating_le_natural_range e hdegree
  have hncard : Nat.card (Fin n) = n := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  have hmcard : Nat.card (Fin m) = m := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  let v : Fin n := ⟨0, by omega⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hp : MulAction.IsPreprimitive ((MulAction.stabilizer K v).map K.subtype) (Fin m)
  · have hb := AlternatingActions.primitive_stabilizer_valuation_log_bound K giant
      (by rw [hmcard]; omega) (by rw [hncard]; exact hn) v hp
    rw [himage, hncard] at hb
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ hlogn)
    exact (div_le_div_of_nonneg_right (by norm_num : (18 : ℝ) ≤ 24) hlog2.le).trans
      (le_max_left _ _)
  by_cases ht : MulAction.IsPretransitive ((MulAction.stabilizer K v).map K.subtype) (Fin m)
  · have hb := AlternatingActions.imprimitive_stabilizer_valuation_log_bound K giant v
      ⟨0, by omega⟩ hp
    rw [himage, hncard] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlogn)
  exfalso
  rcases AlternatingActions.natural_or_johnson_of_intransitive_stabilizer K giant
    (by simpa only [Fintype.card_fin] using (show 3 ≤ m by omega)) v ht with
    hnatural | hjohnson
  · obtain ⟨e', he'⟩ := hnatural
    have hg := AlternatingActions.natural_coordinates_giant K giant e' he'
    rw [himage] at hg
    exact notNatural hg
  · obtain ⟨t, ht2, hhalf, e', he', _⟩ := hjohnson
    have heq := AlternatingActions.subset_coordinates_image K e' he'
    rw [himage] at heq
    apply notJohnson
    refine ⟨m, t, ht2, by simpa only [Fintype.card_fin] using hhalf, e', ?_, ?_⟩
    · rw [heq]; exact Subgroup.map_mono giant
    · rw [heq]; rintro p ⟨g, _, rfl⟩; exact ⟨g, rfl⟩

end GI.PrimitiveValuation
