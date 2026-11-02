import Workspace.Proved.DixonCore

/-!
# Dixon's derived length bound

`GI.Proved.dixonDerivedLength` proves `GI.Cited.DixonDerivedLength`: a solvable `S ≤ Sym(n)` has
`S^{(k)} = 1` for every `k ≥ 5 log₃ n`.

`GI.Proved.solvDL_of_primitive` reduces this to primitive groups. Here we prove the
primitive case `GI.Proved.SolvDLPrimitive`.

*Proof.* Let `G` act faithfully and primitively on `α`, with `G` solvable and nontrivial, and let
`n = |α|`. Take an abelian minimal normal subgroup `N`. It is regular, so `|N| = n`. Let `H` be
the image of the conjugation map `ρ : G → Aut(N)`. Then `H` is solvable and acts faithfully on
`N`. An `H`-invariant subgroup of `N` is normal in `G`, so it is `1` or `N` by minimality. So
`GI.Proved.dixon_core` gives `H^{(solvL n - 1)} = 1`, hence `G^{(solvL n - 1)} ≤ ker ρ`. The
kernel of `ρ` lies in `N`: if `g` centralizes `N`, pick `y ∈ N` with `y a = g a`; then `y⁻¹ g`
fixes `a` and centralizes the transitive group `N`, so it is `1` (`GI.Proved.solvCent_top_eq_bot`).
As `N` is commutative, `G^{(solvL n)} = 1`.

This is not Dixon's proof, which uses the structure of solvable primitive linear groups. The
constant `5` in the trusted statement leaves enough room for the elementary argument of
`GI.Proved.dixon_core`.
-/

namespace GI.Proved

open MulAction GI.RadicalSocle GI.PrimitiveStructure

/-- **The primitive case**, for an abstract faithful primitive action. -/
theorem dixon_primitive_aux {G α : Type} [Group G] [Finite G] [MulAction G α] [FaithfulSMul G α]
    [Finite α] [IsSolvable G] [Nontrivial G] [IsPreprimitive G α]
    (ih : SolvDLIH.{0} (Nat.card α)) : derivedSeries G (solvL (Nat.card α)) = ⊥ := by
  haveI : IsSolvable (⊤ : Subgroup G) :=
    solvable_of_solvable_injective (Subgroup.subtype_injective ⊤)
  obtain ⟨N, hN, -, hc⟩ := exists_abelian_normal_of_solvable_normal (⊤ : Subgroup G) top_ne_bot
  haveI := hN.1
  haveI := normal_pretransitive (V := α) N hN.2.1
  have hα : Nonempty α := by
    by_contra hα
    rw [not_nonempty_iff] at hα
    obtain ⟨g, h, hgh⟩ := exists_pair_ne G
    exact hgh (eq_of_smul_eq_smul (α := α) (fun v => isEmptyElim v))
  obtain ⟨a⟩ := hα
  have hcard : Nat.card N = Nat.card α := abelian_normal_card N hN.2.1 hc a
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.2.1
  letI : CommGroup N := { (inferInstance : Group N) with mul_comm := hc }
  let ρ : G →* MulAut N := MulAut.conjNormal
  haveI : IsSolvable ρ.range := solvable_of_surjective ρ.rangeRestrict_surjective
  have hirr : ∀ W : Subgroup N, (∀ h : ρ.range, ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hnorm : (W.map N.subtype).Normal := by
      constructor
      rintro _ ⟨w, hw, rfl⟩ g
      refine ⟨(ρ g) w, hW ⟨ρ g, g, rfl⟩ w hw, ?_⟩
      exact MulAut.conjNormal_apply g w
    rcases hN.2.2 _ hnorm (Subgroup.map_subtype_le W) with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h
    · right
      rw [eq_top_iff]
      intro y _
      have hy : (y : G) ∈ W.map N.subtype := by rw [h]; exact y.2
      obtain ⟨w, hw, hwy⟩ := hy
      rwa [← Subtype.ext hwy]
  have ih' : SolvDLIH.{0} (Nat.card N) := hcard ▸ ih
  have hcore := dixon_core (H := ρ.range) (V := N) ih' hirr
  rw [hcard] at hcore
  set k := solvL (Nat.card α) - 1
  have hker : derivedSeries G k ≤ N := by
    intro g hg
    have hg1 : ρ g = 1 := solv_map_derived_eq_one ρ k hcore hg
    obtain ⟨y, hy⟩ := MulAction.exists_smul_eq N a (g • a)
    have hcent : (y : G)⁻¹ * g ∈ solvCent a N := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_stabilizer_iff, mul_smul, ← hy]
        exact inv_smul_smul (y : G) a
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hx' : g * x * g⁻¹ = x := by
          have := MulAut.conjNormal_apply g ⟨x, hx⟩
          rw [← this]
          change ((ρ g) ⟨x, hx⟩ : G) = x
          rw [hg1]
          rfl
        have hyx : Commute x (y : G) := congrArg Subtype.val (hc ⟨x, hx⟩ y)
        have hxg : Commute x g := (mul_inv_eq_iff_eq_mul.mp hx').symm
        exact hyx.inv_right.mul_right hxg
    rw [solvCent_top_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hcent
    rw [← hcent]
    exact y.2
  have hn2 : 2 ≤ Nat.card α := by
    rw [← hcard]
    exact Finite.one_lt_card
  have hL := dixon_solvL_add_three (le_refl 1) hn2
  have hk : solvL (Nat.card α) = k + 1 := by omega
  rw [hk, eq_bot_iff, derivedSeries_succ]
  refine (Subgroup.commutator_mono hker hker).trans ?_
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)

/-- **The primitive case** of Dixon's bound. -/
theorem dixon_solvDLPrimitive : SolvDLPrimitive := by
  intro α _ _ ih G hG hprim hnt
  haveI := hprim
  exact dixon_primitive_aux (G := G) (α := α) ih

/-- **Dixon's derived length bound** (Dixon, Math. Z. 107 (1968)), in the form
`dl(S) ≤ 5 log₃ n`. -/
theorem dixonDerivedLength : GI.Cited.DixonDerivedLength :=
  solvDL_of_primitive dixon_solvDLPrimitive

end GI.Proved
