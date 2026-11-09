module

public import Workspace.Degree.FactorBound
public import Workspace.Degree.LineFactors
public import Workspace.Degree.LinearSylow

/-!
# The hard case for groups in the class

Let `H ≤ GL(V)` be irreducible and in `Γ̂_D`, with every abelian subgroup normalized by `H` scalar.
Then `D³ q⁶ |H|³ ≤ |V|^E`, with `E = GI.Degree.degE D` (`GI.Degree.deg_hard`).

Let `N` be a maximal good subgroup and `C = C_H(N)`, as in `GI.Proved.palfy_hard`. The radical `R`
of `C` is scalar (`GI.Degree.solvable_scalar`). So `|H| ≤ |N|^k |C| ≤ q (q m²)^k |C / R|`, and
`GI.Degree.cube_card_le` bounds `|C / R|`. Its hypotheses come from `GI.Degree.prod_index_le` and
`GI.Degree.sylow_cube_le`.
-/

@[expose] public section

namespace GI.Degree

open GI.Proved GI.RadicalSocle
open scoped commutatorElement

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/-- The exponent in the bound. -/
def degE (D : ℕ) : ℕ := 69 + 807 * (Nat.log 2 D + 1)

/-- **Step 1.** Every solvable subgroup of `C_H(N)` normalized by `H` is scalar, when `N` is a
maximal good subgroup. -/
theorem solvable_scalar [Finite V] {H N J : Subgroup (Module.End K V)ˣ}
    (hab : palfyAbSc H) (hN : palfyGood H N)
    (hmax : ∀ N', palfyGood H N' → ¬ N < N') (hJH : palfyNormal J H) (hJC : J ≤ palfyCent H N)
    [Group.IsSolvable J] :
    ∀ c ∈ J, palfySc ((c : (Module.End K V)ˣ) : Module.End K V) := by
  by_contra hne
  push Not at hne
  set C := palfyCent H N
  obtain ⟨M, ⟨hMH, hMJ, x0, hx0M, hx0⟩, hMmin⟩ := (wellFounded_lt (α := Subgroup (Module.End K V)ˣ)).has_min
    {M | palfyNormal M H ∧ M ≤ J ∧ ∃ x ∈ M, ¬ palfySc ((x : (Module.End K V)ˣ) : Module.End K V)}
    ⟨J, hJH, le_rfl, hne⟩
  have hMC : M ≤ C := hMJ.trans hJC
  have hMcomN : ∀ m ∈ M, ∀ n ∈ N, m * n = n * m := by
    intro m hm n hn
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hMC hm)).2 n hn).symm
  haveI : Group.IsSolvable M := solvable_of_solvable_injective (Subgroup.inclusion_injective hMJ)
  -- (a) commutators of `M` are scalar
  have hMcomm : ∀ x ∈ M, ∀ y ∈ M,
      palfySc ((y * x * y⁻¹ * x⁻¹ : (Module.End K V)ˣ) : Module.End K V) := by
    set D := ⁅M, M⁆
    have hDM : D ≤ M := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
    have hDH : palfyNormal D H := by
      refine ⟨hDM.trans hMH.1, ?_⟩
      intro h hh d hd
      have : D ≤ D.comap (MulAut.conj h).toMonoidHom := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_commutatorElement]
        exact Subgroup.commutator_mem_commutator (hMH.2 h hh a ha) (hMH.2 h hh b hb)
      exact this hd
    by_contra hD
    push Not at hD
    obtain ⟨a, ha, b, hb, hab'⟩ := hD
    have hmem : ⁅b, a⁆ ∈ D := Subgroup.commutator_mem_commutator hb ha
    have hDeq : D = M := by
      by_contra hDne
      exact hMmin D ⟨hDH, hDM.trans hMJ, ⁅b, a⁆, hmem, by rwa [commutatorElement_def]⟩
        (lt_of_le_of_ne hDM hDne)
    have hbot := palfy_perfect_bot M hDeq
    rw [hbot, Subgroup.mem_bot] at hx0M
    exact hx0 (by rw [hx0M]; exact palfySc_one)
  -- (b) the center of `M` is scalar
  have hMcent : ∀ x ∈ M, (∀ y ∈ M, x * y = y * x) →
      palfySc ((x : (Module.End K V)ˣ) : Module.End K V) := by
    set Z := M ⊓ Subgroup.centralizer (M : Set (Module.End K V)ˣ)
    have hZM : Z ≤ M := inf_le_left
    have hZH : palfyNormal Z H := by
      refine ⟨hZM.trans hMH.1, ?_⟩
      intro h hh z hz
      obtain ⟨hzM, hzc⟩ := Subgroup.mem_inf.mp hz
      refine Subgroup.mem_inf.mpr ⟨hMH.2 h hh z hzM, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro m hm
      have := Subgroup.mem_centralizer_iff.mp hzc _ (palfyNormal_conj hMH hh hm)
      calc m * (h * z * h⁻¹) = h * ((h⁻¹ * m * h) * z) * h⁻¹ := by group
        _ = h * (z * (h⁻¹ * m * h)) * h⁻¹ := by rw [this]
        _ = h * z * h⁻¹ * m := by group
    intro x hx hxc
    by_contra hxs
    have hxZ : x ∈ Z := Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_iff.mpr
      (fun y hy => (hxc y hy).symm)⟩
    have hZeq : Z = M := by
      by_contra hZne
      exact hMmin Z ⟨hZH, hZM.trans hMJ, x, hxZ, hxs⟩ (lt_of_le_of_ne hZM hZne)
    have hMab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
      intro a ha b hb
      rw [← hZeq] at ha
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2 b hb).symm
    exact hx0 (hab M hMH hMab x0 hx0M)
  -- (c) the product `NM`
  let NM : Subgroup (Module.End K V)ˣ :=
    { carrier := {x | ∃ n ∈ N, ∃ m ∈ M, n * m = x}
      mul_mem' := by
        rintro _ _ ⟨n, hn, m, hm, rfl⟩ ⟨n', hn', m', hm', rfl⟩
        refine ⟨n * n', N.mul_mem hn hn', m * m', M.mul_mem hm hm', ?_⟩
        calc n * n' * (m * m') = n * (n' * m) * m' := by group
          _ = n * (m * n') * m' := by rw [hMcomN m hm n' hn']
          _ = n * m * (n' * m') := by group
      one_mem' := ⟨1, N.one_mem, 1, M.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨n, hn, m, hm, rfl⟩
        refine ⟨n⁻¹, N.inv_mem hn, m⁻¹, M.inv_mem hm, ?_⟩
        rw [mul_inv_rev]
        exact ((Commute.inv_inv (hMcomN m hm n hn))).symm.eq }
  have hNM : N ≤ NM := fun n hn => ⟨n, hn, 1, M.one_mem, mul_one n⟩
  have hMNM : M ≤ NM := fun m hm => ⟨1, N.one_mem, m, hm, one_mul m⟩
  have hgood : palfyGood H NM := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rintro _ ⟨n, hn, m, hm, rfl⟩
      exact H.mul_mem (hN.1.1 hn) (hMH.1 hm)
    · rintro h hh _ ⟨n, hn, m, hm, rfl⟩
      refine ⟨h * n * h⁻¹, hN.1.2 h hh n hn, h * m * h⁻¹, hMH.2 h hh m hm, by group⟩
    · rintro _ ⟨n, hn, m, hm, rfl⟩ _ ⟨n', hn', m', hm', rfl⟩
      rw [palfy_comm_prod (Commute.eq (hMcomN m hm n hn) |> fun h => h)
        (hMcomN m hm n' hn') (hMcomN m' hm' n hn) (hMcomN m' hm' n' hn'), Units.val_mul]
      exact palfySc_mul (hN.2.1 n hn n' hn') (hMcomm m hm m' hm')
    · rintro _ ⟨n, hn, m, hm, rfl⟩ hc
      have hn' : ∀ y ∈ N, n * y = y * n := by
        intro y hy
        have := hc y (hNM hy)
        have e : n * m * y = n * y * m := by
          rw [mul_assoc, hMcomN m hm y hy, ← mul_assoc]
        rw [e, ← mul_assoc y] at this
        exact mul_right_cancel this
      have hns := hN.2.2 n hn hn'
      have hm' : ∀ y ∈ M, m * y = y * m := by
        intro y hy
        have := hc y (hMNM hy)
        have e : y * (n * m) = n * (y * m) := by
          have := palfySc_conj hns y
          calc y * (n * m) = (y * n * y⁻¹) * (y * m) := by group
            _ = n * (y * m) := by rw [palfySc_conj hns y]
        rw [e, mul_assoc] at this
        exact mul_left_cancel this
      rw [Units.val_mul]
      exact palfySc_mul hns (hMcent m hm hm')
  apply hmax NM hgood
  refine lt_of_le_of_ne hNM ?_
  intro heq
  have hx0N : x0 ∈ N := by rw [heq]; exact hMNM hx0M
  exact hx0 (hN.2.2 x0 hx0N (fun y hy => hMcomN x0 hx0M y hy))

theorem hard_calc {D q c Y X W A : ℕ} (h1 : c ≤ Y * X) (h2 : D ^ 3 * X ^ 3 ≤ W ^ A)
    (h3 : 24 * q ^ 6 * Y ^ 3 ≤ W ^ 69) : D ^ 3 * q ^ 6 * c ^ 3 ≤ W ^ (A + 69) := by
  have h4 : q ^ 6 * Y ^ 3 ≤ W ^ 69 := by
    refine le_trans ?_ h3
    have : 24 * q ^ 6 * Y ^ 3 = 24 * (q ^ 6 * Y ^ 3) := by ring
    rw [this]
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  calc D ^ 3 * q ^ 6 * c ^ 3 ≤ D ^ 3 * q ^ 6 * (Y * X) ^ 3 := by gcongr
    _ = (D ^ 3 * X ^ 3) * (q ^ 6 * Y ^ 3) := by ring
    _ ≤ W ^ A * W ^ 69 := Nat.mul_le_mul h2 h4
    _ = _ := (pow_add _ _ _).symm

/-- **The hard case.** -/
theorem deg_hard [Finite K] [Finite V] [Nontrivial V] {H : Subgroup (Module.End K V)ˣ} {D : ℕ}
    (hD : 6 ≤ D) (hcl : GammaHat D H) (hH : palfyIrr H) (hab : palfyAbSc H) :
    D ^ 3 * Nat.card K ^ 6 * Nat.card H ^ 3 ≤ Nat.card V ^ degE D := by
  classical
  haveI : Module.Finite K V := Module.Finite.of_finite
  have hV : Nat.card V = Nat.card K ^ Module.finrank K V := by
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K)]
  have hbot : palfyGood H ⊥ := by
    refine ⟨⟨bot_le, ?_⟩, ?_, ?_⟩
    · intro h _ c hc
      rw [Subgroup.mem_bot] at hc ⊢
      rw [hc]; group
    · intro x hx y hy
      rw [Subgroup.mem_bot] at hx hy
      rw [hx, hy]
      simpa using palfySc_one
    · intro x hx _
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact palfySc_one
  obtain ⟨N, hN, hmax⟩ := (wellFounded_gt (α := Subgroup (Module.End K V)ˣ)).has_min
    {N | palfyGood H N} ⟨⊥, hbot⟩
  set C := palfyCent H N
  have hCN : palfyNormal C H := palfyCent_normal hN.1
  set m := Module.finrank K V
  set q := Nat.card K
  -- the radical of `C` is scalar
  let Rg : Subgroup (Module.End K V)ˣ := (solvableRadical C).map C.subtype
  have hRgN : palfyNormal Rg H := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨c, -, rfl⟩
      exact hCN.1 c.2
    · rintro h hh _ ⟨c, hc, rfl⟩
      exact ⟨conjAut hCN h hh c, map_solvableRadical_le (conjAut hCN h hh) ⟨c, hc, rfl⟩, rfl⟩
  haveI hRgs : Group.IsSolvable Rg := solvable_of_surjective (C.subtype.subgroupMap_surjective _)
  have hRgC : Rg ≤ C := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hRsc := solvable_scalar hab hN hmax hRgN hRgC
  have hR : ∀ r : C, r ∈ solvableRadical C →
      palfySc ((r : (Module.End K V)ˣ) : Module.End K V) := fun r hr => hRsc _ ⟨r, hr, rfl⟩
  -- `|R| ≤ q`
  have hRq : Nat.card (solvableRadical C) ≤ q := by
    apply Nat.card_le_card_of_injective (fun c : solvableRadical C => Classical.choose (hR c c.2))
    intro a b hab'
    have ha := Classical.choose_spec (hR a a.2)
    have hb := Classical.choose_spec (hR b b.2)
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    rw [← ha, ← hb]
    simp only at hab'
    rw [hab']
  -- the quotient
  have rf := radical_quotient_radicalFree (G := C)
  letI : Fintype (Factors (C ⧸ solvableRadical C)) := Fintype.ofFinite _
  have hsimple : ∀ F : Factors (C ⧸ solvableRadical C), IsSimpleGroup F.val :=
    socle_intrinsic_factor_simple
  have hex : ∀ F : Factors (C ⧸ solvableRadical C), ∃ M : Subgroup F.val,
      IsCoatom M ∧ ∀ L : Subgroup F.val, L ≠ ⊤ → M.index ≤ L.index := fun F => by
    haveI := hsimple F
    exact exists_coatom_index_le
  choose M hMc hMmin using hex
  have hprod : ∏ F, (M F).index ≤ Nat.card V ^ 2 :=
    prod_index_le hH hCN hR rf (fun F => (M F).index) hMmin
  have hCH : C ≤ H := hCN.1
  have hQcl : GammaHat D (C ⧸ solvableRadical C) :=
    (hcl.of_injective (Subgroup.inclusion hCH) (Subgroup.inclusion_injective _)).of_surjective
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  obtain ⟨r, hr, hrK⟩ : ∃ r : ℕ, (r = 2 ∨ r = 3) ∧ (r : K) ≠ 0 := by
    by_cases h2 : ((2 : ℕ) : K) = 0
    · refine ⟨3, Or.inr rfl, fun h3 => ?_⟩
      have : ((3 : ℕ) : K) = ((2 : ℕ) : K) + 1 := by push_cast; ring
      rw [this, h2, zero_add] at h3
      exact one_ne_zero h3
    · exact ⟨2, Or.inl rfl, h2⟩
  haveI : Fact r.Prime := ⟨by
    rcases hr with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three⟩
  have hS := sylow_cube_le H r hrK
  have hdvd : Nat.card (C ⧸ solvableRadical C) ∣ Nat.card H :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hCH)
  have hW2 : 2 ≤ Nat.card V := Finite.one_lt_card
  have hQb := cube_card_le rf hD hQcl hW2 hr M (fun F => (hMc F).1) hprod hdvd Nat.card_pos.ne' hS
  have hCcard : Nat.card C ≤ q * Nat.card (C ⧸ solvableRadical C) := by
    rw [← Subgroup.card_mul_index (solvableRadical C)]
    exact Nat.mul_le_mul_right _ hRq
  -- the order of `N`
  obtain ⟨hidx, hNcard⟩ := palfy_card_le_of_scalar N hN.2.1 hN.2.2
  -- generators
  obtain ⟨T, hT, hTcard⟩ := palfy_exists_gens _ (palfyScSub N) rfl
  -- fibers
  have hfib := solv_card_le_mul_of_fibers H C inf_le_left
    (fun h : H => fun t : T => (⟨(h : (Module.End K V)ˣ) * ((t : N) : (Module.End K V)ˣ) *
      (h : (Module.End K V)ˣ)⁻¹, hN.1.2 h h.2 _ (t : N).2⟩ : N)) (by
      intro x y hxy
      refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem x.2) y.2,
        Subgroup.mem_centralizer_iff.mpr ?_⟩
      set z := (x : (Module.End K V)ˣ)⁻¹ * y
      let Z : Subgroup N := (Subgroup.centralizer {z}).comap N.subtype
      have hZ : Subgroup.closure (((palfyScSub N : Set N)) ∪ (T : Set N)) ≤ Z := by
        rw [Subgroup.closure_le]
        rintro t (ht | ht)
        · rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
          have := palfySc_conj ht z
          change (t : (Module.End K V)ˣ) * z = z * (t : (Module.End K V)ˣ)
          symm
          calc z * (t : (Module.End K V)ˣ) = (z * t * z⁻¹) * z := by group
            _ = (t : (Module.End K V)ˣ) * z := by rw [this]
        · rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
          have h1 := congrArg (fun F => ((F ⟨t, ht⟩ : N) : (Module.End K V)ˣ)) hxy
          simp only at h1
          change (t : (Module.End K V)ˣ) * z = z * (t : (Module.End K V)ˣ)
          symm
          calc z * (t : (Module.End K V)ˣ)
              = (x : (Module.End K V)ˣ)⁻¹ * ((y : (Module.End K V)ˣ) * t *
                (y : (Module.End K V)ˣ)⁻¹) * y := by simp only [z]; group
            _ = (x : (Module.End K V)ˣ)⁻¹ * ((x : (Module.End K V)ˣ) * t *
                (x : (Module.End K V)ˣ)⁻¹) * y := by rw [h1]
            _ = (t : (Module.End K V)ˣ) * z := by simp only [z]; group
      rw [hT] at hZ
      intro n hn
      have := hZ (Subgroup.mem_top (⟨n, hn⟩ : N))
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at this
      exact this)
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := T), Fintype.card_coe] at hfib
  have hk : 2 ^ T.card ≤ m ^ 2 := hTcard.trans hidx
  have hm : 1 ≤ m := Module.finrank_pos
  have hq : 2 ≤ q := Finite.one_lt_card
  have hHc : Nat.card H ≤ q * (q * m ^ 2) ^ T.card * Nat.card (C ⧸ solvableRadical C) := by
    calc Nat.card H ≤ Nat.card N ^ T.card * Nat.card C := hfib
      _ ≤ (q * m ^ 2) ^ T.card * (q * Nat.card (C ⧸ solvableRadical C)) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hNcard _) hCcard
      _ = _ := by ring
  have hnum : 24 * q ^ 6 * (q * (q * m ^ 2) ^ T.card) ^ 3 ≤ (q ^ m) ^ 69 := palfy_hard_num hq hm hk
  have hnum' : 24 * q ^ 6 * (q * (q * m ^ 2) ^ T.card) ^ 3 ≤ Nat.card V ^ 69 := hV ▸ hnum
  have := hard_calc hHc hQb hnum'
  rwa [degE, add_comm]

end GI.Degree
