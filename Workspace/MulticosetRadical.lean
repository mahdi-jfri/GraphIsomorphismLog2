import Workspace.MulticosetTransport
import Workspace.MulticosetBounds
import Workspace.RadicalSocleQuotient

/-!
# Corollary A.22: enumerate the radical cosets, solve each by Theorem A.20

`R` is the full preimage in `H` of the solvable radical of `H/N` (`radicalPreimage`).
For each left coset `q = k R` of `R` in `H` we put `g_q = k⁻¹`, so that the right cosets
`R g_q` cover `H`. The candidates in `R g_q` are `Iso_R(X, Y^{g_q⁻¹}) g_q`, computed by the
procedure of Theorem A.20 for `(R, N)`. The union of these sets is the transporter
(`radicalTransport_set`). The number of procedure calls is at most `[H : R]` times the bound
of Theorem A.20 (`radicalTransport_calls_le`).

The bound `[H : R] ≤ b(H/N)² ≤ b^{2 log₂ b}` comes from [GMP, Theorem 1.4] and Lemma A.21.
It is a hypothesis of the final inequality (`radicalTransport_calls_exp`).
-/

namespace GI.Multicoset

open Classical

universe u

variable {G : Type u} [Group G]

/-- The full preimage in `H` of the solvable radical of `H/N`. -/
noncomputable def radicalPreimage [Finite G] (H N : Subgroup G) : Subgroup G :=
  if h : (N.subgroupOf H).Normal then
    letI := h
    ((GI.RadicalSocle.solvableRadical (H ⧸ N.subgroupOf H)).comap
      (QuotientGroup.mk' (N.subgroupOf H))).map H.subtype
  else H

/-- A general form of `relDerived_le_preimage`: any descending family `D i` in `H/N` with
`[D i, D i] ≤ D (i+1)` bounds the series of a subgroup `K` lying over `D 0`. -/
theorem relDerived_le_preimage_of {H N K : Subgroup G} (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    (D : ℕ → Subgroup (H ⧸ N.subgroupOf H))
    (hD0 : K ≤ ((D 0).comap (QuotientGroup.mk' _)).map H.subtype)
    (hDs : ∀ i, ⁅D i, D i⁆ ≤ D (i + 1)) :
    ∀ i, relDerived K N i ≤ ((D i).comap (QuotientGroup.mk' _)).map H.subtype
  | 0 => hD0
  | i + 1 => by
    have ih := relDerived_le_preimage_of hNH D hD0 hDs i
    rw [relDerived_succ]
    refine sup_le ?_ ?_
    · refine (Subgroup.commutator_mono ih ih).trans ?_
      rw [← Subgroup.map_commutator]
      exact Subgroup.map_mono ((comap_commutator_le _ _).trans (Subgroup.comap_mono (hDs i)))
    · intro n hn
      refine ⟨⟨n, hNH hn⟩, ?_, rfl⟩
      change (QuotientGroup.mk' (N.subgroupOf H)) ⟨n, hNH hn⟩ ∈ D (i + 1)
      have : (QuotientGroup.mk' (N.subgroupOf H)) ⟨n, hNH hn⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hn
      rw [this]
      exact Subgroup.one_mem _

theorem radicalPreimage_spec [Finite G] {H N : Subgroup G} (hNH : N ≤ H) (hn : Normalizes H N) :
    radicalPreimage H N ≤ H ∧ N ≤ radicalPreimage H N ∧
      ∃ ℓ, relDerived (radicalPreimage H N) N ℓ ≤ N := by
  haveI hN := normal_of_normalizes hn
  rw [radicalPreimage, dif_pos hN]
  set Q := H ⧸ N.subgroupOf H
  set Rad := GI.RadicalSocle.solvableRadical Q
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro n hnN
    refine ⟨⟨n, hNH hnN⟩, ?_, rfl⟩
    change (QuotientGroup.mk' (N.subgroupOf H)) ⟨n, hNH hnN⟩ ∈ Rad
    have : (QuotientGroup.mk' (N.subgroupOf H)) ⟨n, hNH hnN⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hnN
    rw [this]
    exact Rad.one_mem
  · let D : ℕ → Subgroup Q := fun i => (derivedSeries Rad i).map Rad.subtype
    have hD0 : D 0 = Rad := by
      simp only [D, derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hDs : ∀ i, ⁅D i, D i⁆ ≤ D (i + 1) := by
      intro i
      simp only [D, derivedSeries_succ, Subgroup.map_commutator]
      exact le_rfl
    refine ⟨derivedLength Rad, ?_⟩
    refine (relDerived_le_preimage_of hNH D (by rw [hD0]) hDs _).trans ?_
    simp only [D, derivedSeries_derivedLength, Subgroup.map_bot, MonoidHom.comap_bot,
      QuotientGroup.ker_mk', Subgroup.subgroupOf_map_subtype]
    exact inf_le_left

/-- The coset representative `g_q = k⁻¹` of the right coset `R g_q` for `q = k R`. -/
noncomputable def cosetRep {H R : Subgroup G} (q : H ⧸ R.subgroupOf H) : G :=
  ((Quotient.out q : H) : G)⁻¹

/-- **The procedure of Corollary A.22.** -/
noncomputable def radicalTransport [Finite G] {Ω : Type u} [RAct G Ω] (H N : Subgroup G)
    (X Y : Multiset Ω) : Out G :=
  ⟨⋃ q : H ⧸ (radicalPreimage H N).subgroupOf H,
      (fun r => r * cosetRep q) ''
        (solvableTransport (radicalPreimage H N) N X (Y ↼ (cosetRep q)⁻¹)).set,
    ∑ᶠ q : H ⧸ (radicalPreimage H N).subgroupOf H,
      (solvableTransport (radicalPreimage H N) N X (Y ↼ (cosetRep q)⁻¹)).calls⟩

theorem cosetRep_mem {H R : Subgroup G} (q : H ⧸ R.subgroupOf H) : cosetRep q ∈ H :=
  H.inv_mem (Quotient.out q).2

/-- **Correctness of Corollary A.22's procedure**: the union over the radical cosets of the
answers of Theorem A.20 is the full transporter. -/
theorem radicalTransport_set [Finite G] {Ω : Type u} [RAct G Ω] {H N : Subgroup G}
    (hNH : N ≤ H) (hn : Normalizes H N) {X Y : Multiset Ω} (hX : Fixes N X) (hY : Fixes N Y) :
    (radicalTransport H N X Y).set = Iso H X Y := by
  obtain ⟨hRH, hNR, hsolv⟩ := radicalPreimage_spec hNH hn
  set R := radicalPreimage H N
  have hsub : ∀ q : H ⧸ R.subgroupOf H,
      (solvableTransport R N X (Y ↼ (cosetRep q)⁻¹)).set = Iso R X (Y ↼ (cosetRep q)⁻¹) :=
    fun q => solvableTransport_set hNR (hn.mono hRH) hsolv hX
      (hY.act hn (H.inv_mem (cosetRep_mem q)))
  show (⋃ q : H ⧸ R.subgroupOf H, (fun r => r * cosetRep q) ''
      (solvableTransport R N X (Y ↼ (cosetRep q)⁻¹)).set) = Iso H X Y
  ext h
  simp only [Set.mem_iUnion, hsub]
  constructor
  · rintro ⟨q, r, ⟨hrR, hrX⟩, rfl⟩
    refine ⟨H.mul_mem (hRH hrR) (cosetRep_mem q), ?_⟩
    rw [← act_act, hrX, act_inv_act]
  · rintro ⟨hh, hXY⟩
    let q : H ⧸ R.subgroupOf H := QuotientGroup.mk (⟨h, hh⟩⁻¹ : H)
    refine ⟨q, h * (cosetRep q)⁻¹, ⟨?_, ?_⟩, by simp⟩
    · -- `q.out⁻¹ h⁻¹ ∈ R`, so `h q.out ∈ R`
      have hq : (QuotientGroup.mk (Quotient.out q) : H ⧸ R.subgroupOf H) = q :=
        QuotientGroup.out_eq' q
      rw [QuotientGroup.eq] at hq
      have hmem := Subgroup.mem_subgroupOf.mp hq
      have := R.inv_mem hmem
      simpa [cosetRep, mul_assoc] using this
    · rw [← act_act, hXY]

/-- The count of Corollary A.22: at most `[H : R]` calls of Theorem A.20, each with at most
`(4M³ + 2)^ℓ` calls of its recursion, where `ℓ` is the derived length of `R/N`. -/
theorem radicalTransport_calls_le [Finite G] {Ω : Type u} [RAct G Ω] (H N : Subgroup G)
    (X Y : Multiset Ω) (M : ℕ) (hX : Multiset.card X ≤ M) (hY : Multiset.card Y ≤ M) :
    (radicalTransport H N X Y).calls ≤
      ((radicalPreimage H N).subgroupOf H).index * (4 * M ^ 3 + 2) ^
        quotLength (supplement (radicalPreimage H N) N)
          (supplement (radicalPreimage H N) N ⊓ N) := by
  letI : Fintype (H ⧸ (radicalPreimage H N).subgroupOf H) := Fintype.ofFinite _
  show ∑ᶠ q : H ⧸ (radicalPreimage H N).subgroupOf H,
    (solvableTransport (radicalPreimage H N) N X (Y ↼ (cosetRep q)⁻¹)).calls ≤ _
  rw [finsum_eq_sum_of_fintype, Subgroup.index, ← Fintype.card_eq_nat_card]
  refine (Finset.sum_le_sum (fun q _ => proc_calls_le _ _ _ X _ M hX (by simpa using hY))).trans ?_
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

/-- **The bound of Corollary A.22.** With Dixon's bound and the radical index bound
`[H : R] ≤ b^{2 log₂ b}` (from [GMP, Theorem 1.4] and Lemma A.21, taken as hypothesis
`hidx`), the number of calls is `exp(45 (log²(b+2) + log(M+2) log(b+2)))`. -/
theorem radicalTransport_calls_exp {B : Type u} [Fintype B] [DecidableEq B]
    (dixon : GI.Cited.DixonDerivedLength) {Ω : Type u} [RAct (Equiv.Perm B) Ω]
    {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H) (hn : Normalizes H N)
    (X Y : Multiset Ω) (M : ℕ) (hX : Multiset.card X ≤ M) (hY : Multiset.card Y ≤ M)
    (hidx : (((radicalPreimage H N).subgroupOf H).index : ℝ) ≤
      (Fintype.card B : ℝ) ^ (2 * Real.logb 2 (Fintype.card B))) :
    ((radicalTransport H N X Y).calls : ℝ) ≤
      Real.exp (45 * (Real.log ((Fintype.card B : ℝ) + 2) ^ 2 +
        Real.log ((M : ℝ) + 2) * Real.log ((Fintype.card B : ℝ) + 2))) := by
  obtain ⟨hRH, hNR, hsolv⟩ := radicalPreimage_spec hNH hn
  set b := Fintype.card B
  have hdepth := solvableTransport_depth dixon hNR (hn.mono hRH) hsolv
  have hcount := count_le_exp b M _ hdepth
  have hcalls := radicalTransport_calls_le H N X Y M hX hY
  have hidx' := hidx.trans (index_le_exp b)
  have hcast : ((radicalTransport H N X Y).calls : ℝ) ≤
      (((radicalPreimage H N).subgroupOf H).index : ℝ) *
        (((4 * M ^ 3 + 2) ^ quotLength (supplement (radicalPreimage H N) N)
          (supplement (radicalPreimage H N) N ⊓ N) : ℕ) : ℝ) := by
    exact_mod_cast hcalls
  refine hcast.trans ((mul_le_mul hidx' hcount (by positivity) (by positivity)).trans ?_)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hL := log_add_le b M
  have hl2 : 0 ≤ Real.log ((b : ℝ) + 2) :=
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans (log_two_le_log_add_two b)
  have hlM : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith)
  nlinarith [mul_le_mul_of_nonneg_right hL hl2, mul_nonneg hlM hl2, sq_nonneg (Real.log ((b : ℝ) + 2))]

end GI.Multicoset
