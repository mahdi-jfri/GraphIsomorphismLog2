module

public import Workspace.MulticosetTransport
public import Workspace.MulticosetBounds
public import Workspace.RadicalSocleQuotient

@[expose] public section

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

/-- **The procedure of Corollary A.22 for a given solvable-quotient subgroup `R ≤ H`.** -/
noncomputable def subTransport [Finite G] {Ω : Type u} [RAct G Ω] (H R N : Subgroup G)
    (X Y : Multiset Ω) : Out G :=
  ⟨⋃ q : H ⧸ R.subgroupOf H,
      (fun r => r * cosetRep q) ''
        (solvableTransport R N X (Y ↼ (cosetRep q)⁻¹)).set,
    ∑ᶠ q : H ⧸ R.subgroupOf H,
      (solvableTransport R N X (Y ↼ (cosetRep q)⁻¹)).calls⟩

theorem cosetRep_mem {H R : Subgroup G} (q : H ⧸ R.subgroupOf H) : cosetRep q ∈ H :=
  H.inv_mem (Quotient.out q).2

/-- **Correctness of `subTransport`**: for any `N ≤ R ≤ H` with `R/N` solvable (`relDerived`),
the union over the right cosets of `R` in `H` of the answers of Theorem A.20 is `Iso H X Y`. -/
theorem subTransport_set [Finite G] {Ω : Type u} [RAct G Ω] {H R N : Subgroup G}
    (hRH : R ≤ H) (hNR : N ≤ R) (hn : Normalizes H N) (hsolv : ∃ ℓ, relDerived R N ℓ ≤ N)
    {X Y : Multiset Ω} (hX : Fixes N X) (hY : Fixes N Y) :
    (subTransport H R N X Y).set = Iso H X Y := by
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
    · have hq : (QuotientGroup.mk (Quotient.out q) : H ⧸ R.subgroupOf H) = q :=
        QuotientGroup.out_eq' q
      rw [QuotientGroup.eq] at hq
      have hmem := Subgroup.mem_subgroupOf.mp hq
      have := R.inv_mem hmem
      simpa [cosetRep, mul_assoc] using this
    · rw [← act_act, hXY]

/-- Call count of `subTransport`: at most `[H : R]` calls of Theorem A.20. -/
theorem subTransport_calls_le [Finite G] {Ω : Type u} [RAct G Ω] (H R N : Subgroup G)
    (X Y : Multiset Ω) (M : ℕ) (hX : Multiset.card X ≤ M) (hY : Multiset.card Y ≤ M) :
    (subTransport H R N X Y).calls ≤
      (R.subgroupOf H).index * (4 * M ^ 3 + 2) ^ quotLength R N := by
  letI : Fintype (H ⧸ R.subgroupOf H) := Fintype.ofFinite _
  show ∑ᶠ q : H ⧸ R.subgroupOf H,
    (solvableTransport R N X (Y ↼ (cosetRep q)⁻¹)).calls ≤ _
  rw [finsum_eq_sum_of_fintype, Subgroup.index, ← Fintype.card_eq_nat_card]
  refine (Finset.sum_le_sum (fun q _ => proc_calls_le _ _ _ X _ M hX (by simpa using hY))).trans ?_
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

/-- Exponential call bound of `subTransport` when `[H : R] ≤ b^{2 log₂ b}`. -/
theorem subTransport_calls_exp {B : Type u} [Fintype B] [DecidableEq B]
    (dixon : GI.Cited.DixonDerivedLength) {Ω : Type u} [RAct (Equiv.Perm B) Ω]
    {H R N : Subgroup (Equiv.Perm B)} (hRH : R ≤ H) (hNR : N ≤ R) (hn : Normalizes H N)
    (hsolv : ∃ ℓ, relDerived R N ℓ ≤ N)
    (X Y : Multiset Ω) (M : ℕ) (hX : Multiset.card X ≤ M) (hY : Multiset.card Y ≤ M)
    (hidx : ((R.subgroupOf H).index : ℝ) ≤
      (Fintype.card B : ℝ) ^ (2 * Real.logb 2 (Fintype.card B))) :
    ((subTransport H R N X Y).calls : ℝ) ≤
      Real.exp (45 * (Real.log ((Fintype.card B : ℝ) + 2) ^ 2 +
        Real.log ((M : ℝ) + 2) * Real.log ((Fintype.card B : ℝ) + 2))) := by
  set b := Fintype.card B
  have hdepth := solvableTransport_depth dixon hNR (hn.mono hRH) hsolv
  have hcount := count_le_exp b M _ hdepth
  have hcalls := subTransport_calls_le H R N X Y M hX hY
  have hidx' := hidx.trans (index_le_exp b)
  have hcast : ((subTransport H R N X Y).calls : ℝ) ≤
      ((R.subgroupOf H).index : ℝ) *
        (((4 * M ^ 3 + 2) ^ quotLength R N : ℕ) : ℝ) := by
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

/-- The full preimage in `H` of the socle of `H/R`. -/
noncomputable def soclePreimage [Finite G] (H R : Subgroup G) : Subgroup G :=
  if h : (R.subgroupOf H).Normal then
    let _ := h
    ((GI.RadicalSocle.socle (H ⧸ R.subgroupOf H)).comap
      (QuotientGroup.mk' (R.subgroupOf H))).map H.subtype
  else H

theorem radicalPreimage_le [Finite G] (H N : Subgroup G) : radicalPreimage H N ≤ H := by
  unfold radicalPreimage
  split_ifs
  · exact Subgroup.map_subtype_le _
  · exact le_rfl

theorem le_radicalPreimage [Finite G] {H N : Subgroup G} (hNH : N ≤ H) :
    N ≤ radicalPreimage H N := by
  unfold radicalPreimage
  split_ifs with hN
  · intro n hn
    refine ⟨⟨n, hNH hn⟩, ?_, rfl⟩
    change (QuotientGroup.mk' (N.subgroupOf H)) ⟨n, hNH hn⟩ ∈
      GI.RadicalSocle.solvableRadical (H ⧸ N.subgroupOf H)
    have h1 : (QuotientGroup.mk' (N.subgroupOf H)) ⟨n, hNH hn⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hn
    rw [h1]
    exact Subgroup.one_mem _
  · exact hNH

theorem radicalPreimage_subgroupOf [Finite G] {H N : Subgroup G} [(N.subgroupOf H).Normal] :
    (radicalPreimage H N).subgroupOf H =
      (GI.RadicalSocle.solvableRadical (H ⧸ N.subgroupOf H)).comap
        (QuotientGroup.mk' (N.subgroupOf H)) := by
  unfold radicalPreimage
  split_ifs
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

instance normal_radicalPreimage [Finite G] {H N : Subgroup G} [(N.subgroupOf H).Normal] :
    ((radicalPreimage H N).subgroupOf H).Normal := by
  rw [radicalPreimage_subgroupOf]
  exact Subgroup.Normal.comap inferInstance _

theorem normalizes_radicalPreimage [Finite G] {H N : Subgroup G} (hn : Normalizes H N) :
    Normalizes H (radicalPreimage H N) := by
  have := normal_of_normalizes hn
  exact normalizes_of_normal (radicalPreimage_le H N)

theorem soclePreimage_le [Finite G] (H R : Subgroup G) : soclePreimage H R ≤ H := by
  unfold soclePreimage
  split_ifs
  · exact Subgroup.map_subtype_le _
  · exact le_rfl

theorem le_soclePreimage [Finite G] {H R : Subgroup G} (hRH : R ≤ H) :
    R ≤ soclePreimage H R := by
  unfold soclePreimage
  split_ifs with hR
  · intro r hr
    refine ⟨⟨r, hRH hr⟩, ?_, rfl⟩
    change (QuotientGroup.mk' (R.subgroupOf H)) ⟨r, hRH hr⟩ ∈
      GI.RadicalSocle.socle (H ⧸ R.subgroupOf H)
    have h1 : (QuotientGroup.mk' (R.subgroupOf H)) ⟨r, hRH hr⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hr
    rw [h1]
    exact Subgroup.one_mem _
  · exact hRH

theorem soclePreimage_subgroupOf [Finite G] {H R : Subgroup G} [(R.subgroupOf H).Normal] :
    (soclePreimage H R).subgroupOf H =
      (GI.RadicalSocle.socle (H ⧸ R.subgroupOf H)).comap (QuotientGroup.mk' (R.subgroupOf H)) := by
  unfold soclePreimage
  split_ifs
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

instance normal_soclePreimage [Finite G] {H R : Subgroup G} [(R.subgroupOf H).Normal] :
    ((soclePreimage H R).subgroupOf H).Normal := by
  rw [soclePreimage_subgroupOf]
  exact Subgroup.Normal.comap inferInstance _

theorem normalizes_soclePreimage [Finite G] {H R : Subgroup G} (hn : Normalizes H R) :
    Normalizes H (soclePreimage H R) := by
  have := normal_of_normalizes hn
  exact normalizes_of_normal (soclePreimage_le H R)

/-- `relDerived` is monotone in the kernel subgroup. -/
theorem relDerived_mono_kernel {K M N : Subgroup G} (hNM : N ≤ M) :
    ∀ i, relDerived K N i ≤ relDerived K M i
  | 0 => le_rfl
  | i + 1 => sup_le_sup
      (Subgroup.commutator_mono (relDerived_mono_kernel hNM i) (relDerived_mono_kernel hNM i)) hNM

/-- `relDerived K N (a + b) ≤ relDerived M N b` when `relDerived K N a ≤ M`. -/
theorem relDerived_add_le {K M N : Subgroup G} {a : ℕ} (ha : relDerived K N a ≤ M) :
    ∀ b, relDerived K N (a + b) ≤ relDerived M N b
  | 0 => ha
  | b + 1 => sup_le_sup
      (Subgroup.commutator_mono (relDerived_add_le ha b) (relDerived_add_le ha b)) le_rfl

/-- Extension of relative solvability along `N ≤ M ≤ K`. -/
theorem relDerived_trans {K M N : Subgroup G} (hNM : N ≤ M) {a b : ℕ}
    (ha : relDerived K M a ≤ M) (hb : relDerived M N b ≤ N) :
    relDerived K N (a + b) ≤ N :=
  (relDerived_add_le ((relDerived_mono_kernel hNM a).trans ha) b).trans hb

/-- If `S₁` is solvable and `R` is normal in `S₁ ⊔ R`, then `(S₁ ⊔ R) / R` is solvable. -/
theorem sup_quotient_solvable {S₁ R : Subgroup G} [(R.subgroupOf (S₁ ⊔ R)).Normal]
    [Group.IsSolvable S₁] :
    Group.IsSolvable ((S₁ ⊔ R : Subgroup G) ⧸ R.subgroupOf (S₁ ⊔ R)) := by
  set R' : Subgroup G := S₁ ⊔ R
  set q := QuotientGroup.mk' (R.subgroupOf R')
  let ψ : S₁ →* R' ⧸ R.subgroupOf R' := q.comp (Subgroup.inclusion (le_sup_left : S₁ ≤ R'))
  have hsurj : Function.Surjective ψ := by
    let M : Subgroup G := (ψ.range.comap q).map R'.subtype
    have hS₁M : S₁ ≤ M := by
      intro s hs
      exact ⟨⟨s, Subgroup.mem_sup_left hs⟩, ⟨⟨s, hs⟩, rfl⟩, rfl⟩
    have hRM : R ≤ M := by
      intro r hr
      refine ⟨⟨r, Subgroup.mem_sup_right hr⟩, ?_, rfl⟩
      change (QuotientGroup.mk' (R.subgroupOf R')) ⟨r, Subgroup.mem_sup_right hr⟩ ∈ ψ.range
      have h1 : (QuotientGroup.mk' (R.subgroupOf R')) ⟨r, Subgroup.mem_sup_right hr⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hr
      rw [h1]
      exact ψ.range.one_mem
    have hR'M : R' ≤ M := sup_le hS₁M hRM
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
    obtain ⟨y, hy, hyx⟩ := hR'M x.2
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
  exact Group.isSolvable_of_surjective hsurj

/-- Existence of a solvable supplement `S₁ ≤ K*_H` of `E_H` in `K*_H` (by Lemma A.19). -/
theorem exists_solvable_supplement_radicalOuter [Finite G] {H N : Subgroup G}
    [(N.subgroupOf H).Normal] :
    ∃ S₁ : Subgroup G,
      S₁ ≤ radicalPreimage H (soclePreimage H (radicalPreimage H N)) ∧
      Group.IsSolvable S₁ ∧
      S₁ ⊔ soclePreimage H (radicalPreimage H N) =
        radicalPreimage H (soclePreimage H (radicalPreimage H N)) := by
  set R := radicalPreimage H N
  set E_H := soclePreimage H R
  set K_H := radicalPreimage H E_H
  have hEH : E_H ≤ H := soclePreimage_le H R
  have hEK : E_H ≤ K_H := le_radicalPreimage hEH
  have hnH : Normalizes H E_H := normalizes_of_normal hEH
  have hnK : Normalizes K_H E_H := hnH.mono (radicalPreimage_le H E_H)
  have : (E_H.subgroupOf K_H).Normal := normal_of_normalizes hnK
  obtain ⟨-, -, ℓ, hℓ⟩ := radicalPreimage_spec hEH hnH
  have : Group.IsSolvable (K_H ⧸ E_H.subgroupOf K_H) := isSolvable_quot_of_relDerived hℓ
  exact exists_solvable_supplement_descent hEK hnK

/-- The solvable-quotient subgroup `R' = S₁ ⊔ R` of Lemma A.21, where `S₁` is a solvable
supplement of `E_H = soclePreimage H R` in `K*_H = radicalPreimage H E_H`. -/
noncomputable def radicalSubgroup [Finite G] (H N : Subgroup G) : Subgroup G :=
  if h : (N.subgroupOf H).Normal then
    let _ := h
    Classical.choose (exists_solvable_supplement_radicalOuter (H := H) (N := N)) ⊔
      radicalPreimage H N
  else H

theorem radicalSubgroup_spec [Finite G] {H N : Subgroup G} (hNH : N ≤ H) (hn : Normalizes H N) :
    radicalSubgroup H N ≤ H ∧ N ≤ radicalSubgroup H N ∧
      ∃ ℓ, relDerived (radicalSubgroup H N) N ℓ ≤ N := by
  have hN : (N.subgroupOf H).Normal := normal_of_normalizes hn
  rw [radicalSubgroup, dif_pos hN]
  obtain ⟨hS₁, hsolv, -⟩ :=
    Classical.choose_spec (exists_solvable_supplement_radicalOuter (H := H) (N := N))
  set S₁ := Classical.choose (exists_solvable_supplement_radicalOuter (H := H) (N := N))
  set R := radicalPreimage H N
  set E_H := soclePreimage H R
  set K_H := radicalPreimage H E_H
  set R' := S₁ ⊔ R
  obtain ⟨hRH, hNR, ℓ₂, hℓ₂⟩ := radicalPreimage_spec hNH hn
  have hKH : K_H ≤ H := radicalPreimage_le H E_H
  have hR'H : R' ≤ H := sup_le (hS₁.trans hKH) hRH
  have hRR' : R ≤ R' := le_sup_right
  have hNR' : N ≤ R' := hNR.trans hRR'
  have hnR : Normalizes H R := normalizes_of_normal hRH
  have : (R.subgroupOf R').Normal := normal_of_normalizes (hnR.mono hR'H)
  have : Group.IsSolvable (R' ⧸ R.subgroupOf R') := sup_quotient_solvable
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_relDerived_of_isSolvable hRR'
  exact ⟨hR'H, hNR', ℓ₁ + ℓ₂, relDerived_trans hNR hℓ₁ hℓ₂⟩

/-- **The procedure of Corollary A.22.** -/
noncomputable def radicalTransport [Finite G] {Ω : Type u} [RAct G Ω] (H N : Subgroup G)
    (X Y : Multiset Ω) : Out G :=
  subTransport H (radicalSubgroup H N) N X Y

/-- **Correctness of Corollary A.22's procedure**: the union over the cosets of `R'` of the
answers of Theorem A.20 is the full transporter. -/
theorem radicalTransport_set [Finite G] {Ω : Type u} [RAct G Ω] {H N : Subgroup G}
    (hNH : N ≤ H) (hn : Normalizes H N) {X Y : Multiset Ω} (hX : Fixes N X) (hY : Fixes N Y) :
    (radicalTransport H N X Y).set = Iso H X Y := by
  obtain ⟨hRH, hNR, hsolv⟩ := radicalSubgroup_spec hNH hn
  exact subTransport_set hRH hNR hn hsolv hX hY

/-- The count of Corollary A.22: at most `[H : R']` calls of Theorem A.20, each with at most
`(4M³ + 2)^ℓ` calls of its recursion, where `ℓ` is the derived length of `R'/N`. -/
theorem radicalTransport_calls_le [Finite G] {Ω : Type u} [RAct G Ω] (H N : Subgroup G)
    (X Y : Multiset Ω) (M : ℕ) (hX : Multiset.card X ≤ M) (hY : Multiset.card Y ≤ M) :
    (radicalTransport H N X Y).calls ≤
      ((radicalSubgroup H N).subgroupOf H).index * (4 * M ^ 3 + 2) ^
        quotLength (radicalSubgroup H N) N :=
  subTransport_calls_le H (radicalSubgroup H N) N X Y M hX hY

/-- **The bound of Corollary A.22.** With Dixon's bound and the index bound
`[H : R'] ≤ b^{2 log₂ b}` (from [GMP, Theorem 1.4] and Lemma A.21, taken as hypothesis
`hidx`), the number of calls is `exp(45 (log²(b+2) + log(M+2) log(b+2)))`. -/
theorem radicalTransport_calls_exp {B : Type u} [Fintype B] [DecidableEq B]
    (dixon : GI.Cited.DixonDerivedLength) {Ω : Type u} [RAct (Equiv.Perm B) Ω]
    {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H) (hn : Normalizes H N)
    (X Y : Multiset Ω) (M : ℕ) (hX : Multiset.card X ≤ M) (hY : Multiset.card Y ≤ M)
    (hidx : (((radicalSubgroup H N).subgroupOf H).index : ℝ) ≤
      (Fintype.card B : ℝ) ^ (2 * Real.logb 2 (Fintype.card B))) :
    ((radicalTransport H N X Y).calls : ℝ) ≤
      Real.exp (45 * (Real.log ((Fintype.card B : ℝ) + 2) ^ 2 +
        Real.log ((M : ℝ) + 2) * Real.log ((Fintype.card B : ℝ) + 2))) := by
  obtain ⟨hRH, hNR, hsolv⟩ := radicalSubgroup_spec hNH hn
  exact subTransport_calls_exp dixon hRH hNR hn hsolv X Y M hX hY hidx

end GI.Multicoset
