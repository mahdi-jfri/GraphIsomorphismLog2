module

public import Workspace.Proved.PalfyField
public import Workspace.Proved.PalfyIndep
public import Workspace.Proved.PalfyNum

@[expose] public section

/-!
# The hard case: every abelian normal subgroup is scalar

Let `H ≤ GL_K(V)` be solvable, `|K| = q`, `dim V = m ≥ 1`, and suppose every abelian subgroup
normalized by `H` consists of scalars. Then `24 q^6 |H|^3 ≤ |V|^69` (`GI.Proved.palfy_hard`).

Call a subgroup `N` normalized by `H` *good* if all commutators of elements of `N` are scalars
and every central element of `N` is a scalar.

*Step 1* (`GI.Proved.palfy_cent_scalar`). If `N` is a maximal good subgroup, then every element
of `H` that commutes with all of `N` is a scalar. Otherwise the centralizer `C` of `N` in `H` is
not scalar. Take `M ≤ C` normalized by `H`, not scalar, and minimal with these properties.
- `[M, M]` is scalar: else `[M, M] = M` by minimality, and a solvable group equal to its own
  commutator subgroup is trivial.
- The center of `M` is scalar: else it is `M` by minimality, so `M` is abelian, hence scalar.
- Then `NM` is good: as `M` commutes with `N`, a commutator in `NM` is the product of a
  commutator in `N` and one in `M`, and a central element `nm` of `NM` has `n` central in `N`
  and `m` central in `M`. Also `M ⊄ N`, because an element of `N ∩ C` is central in `N`, hence
  scalar. This contradicts the maximality of `N`.

*Step 2.* `|C| ≤ q`, since `C` is scalar. By `GI.Proved.palfy_card_le_of_scalar`, the
scalars `S` of `N` have index at most `m^2` and `|N| ≤ q m^2`. Take generators `T` of `N`
modulo `S` with `2^{|T|} ≤ |N : S|` (`GI.Proved.palfy_exists_gens`). Then `h ↦ (h t h⁻¹)_{t ∈ T}`
has fibers in cosets of `C`, as scalars commute with everything. So `|H| ≤ q (q m^2)^{|T|}`,
and `GI.Proved.palfy_hard_num` finishes.
-/

namespace GI.Proved

open scoped commutatorElement

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/-- Every abelian subgroup normalized by `H` is scalar. -/
def palfyAbSc (H : Subgroup (Module.End K V)ˣ) : Prop :=
  ∀ A : Subgroup (Module.End K V)ˣ, palfyNormal A H → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
    ∀ a ∈ A, palfySc (a : Module.End K V)

/-- `N` is good: normalized by `H`, with scalar commutators and scalar center. -/
def palfyGood (H N : Subgroup (Module.End K V)ˣ) : Prop :=
  palfyNormal N H ∧
    (∀ x ∈ N, ∀ y ∈ N, palfySc ((y * x * y⁻¹ * x⁻¹ : (Module.End K V)ˣ) : Module.End K V)) ∧
    (∀ x ∈ N, (∀ y ∈ N, x * y = y * x) → palfySc ((x : (Module.End K V)ˣ) : Module.End K V))

theorem palfy_comm_prod {G : Type*} [Group G] {n m n' m' : G} (h1 : Commute m n)
    (h2 : Commute m n') (h3 : Commute m' n) (h4 : Commute m' n') :
    (n' * m') * (n * m) * (n' * m')⁻¹ * (n * m)⁻¹ =
      (n' * n * n'⁻¹ * n⁻¹) * (m' * m * m'⁻¹ * m⁻¹) := by
  have hc : Commute (m' * m * m'⁻¹) n'⁻¹ :=
    ((h4.mul_left h2).mul_left h4.inv_left).inv_right
  have hX : Commute (m' * m * m'⁻¹ * m⁻¹) n⁻¹ :=
    (((h3.mul_left h1).mul_left h3.inv_left).mul_left h1.inv_left).inv_right
  calc (n' * m') * (n * m) * (n' * m')⁻¹ * (n * m)⁻¹
      = n' * (m' * n) * m * m'⁻¹ * n'⁻¹ * m⁻¹ * n⁻¹ := by group
    _ = n' * (n * m') * m * m'⁻¹ * n'⁻¹ * m⁻¹ * n⁻¹ := by rw [h3.eq]
    _ = n' * n * ((m' * m * m'⁻¹) * n'⁻¹) * m⁻¹ * n⁻¹ := by group
    _ = n' * n * (n'⁻¹ * (m' * m * m'⁻¹)) * m⁻¹ * n⁻¹ := by rw [hc.eq]
    _ = n' * n * n'⁻¹ * ((m' * m * m'⁻¹ * m⁻¹) * n⁻¹) := by group
    _ = n' * n * n'⁻¹ * (n⁻¹ * (m' * m * m'⁻¹ * m⁻¹)) := by rw [hX.eq]
    _ = (n' * n * n'⁻¹ * n⁻¹) * (m' * m * m'⁻¹ * m⁻¹) := by group

/-- A solvable subgroup equal to its commutator subgroup is trivial. -/
theorem palfy_perfect_bot {G : Type*} [Group G] (M : Subgroup G) [Group.IsSolvable M]
    (h : ⁅M, M⁆ = M) : M = ⊥ := by
  have htop : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, h]
  have hall : ∀ n, derivedSeries M n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, htop]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := M)
  rw [hall n] at hn
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : M) ∈ (⊤ : Subgroup M) := Subgroup.mem_top _
  rw [hn, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem palfyNormal_conj {N H : Subgroup (Module.End K V)ˣ} (hN : palfyNormal N H)
    {h : (Module.End K V)ˣ} (hh : h ∈ H) {x : (Module.End K V)ˣ} (hx : x ∈ N) :
    h⁻¹ * x * h ∈ N := by
  have := hN.2 _ (H.inv_mem hh) x hx
  rwa [inv_inv] at this

theorem palfySc_conj {x : (Module.End K V)ˣ} (hx : palfySc (x : Module.End K V))
    (g : (Module.End K V)ˣ) : g * x * g⁻¹ = x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← palfySc_comm hx, mul_assoc, Units.mul_inv, mul_one]

/-- **Step 1.** -/
theorem palfy_cent_scalar [Finite V] {H N : Subgroup (Module.End K V)ˣ} [Group.IsSolvable H]
    (hab : palfyAbSc H) (hN : palfyGood H N)
    (hmax : ∀ N', palfyGood H N' → ¬ N < N') :
    ∀ c ∈ palfyCent H N, palfySc ((c : (Module.End K V)ˣ) : Module.End K V) := by
  by_contra hne
  push Not at hne
  set C := palfyCent H N
  have hCH : palfyNormal C H := palfyCent_normal hN.1
  obtain ⟨M, ⟨hMH, hMC, x0, hx0M, hx0⟩, hMmin⟩ := (wellFounded_lt (α := Subgroup (Module.End K V)ˣ)).has_min
    {M | palfyNormal M H ∧ M ≤ C ∧ ∃ x ∈ M, ¬ palfySc ((x : (Module.End K V)ˣ) : Module.End K V)}
    ⟨C, hCH, le_rfl, hne⟩
  have hMcomN : ∀ m ∈ M, ∀ n ∈ N, m * n = n * m := by
    intro m hm n hn
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hMC hm)).2 n hn).symm
  haveI : Group.IsSolvable M := solvable_of_solvable_injective (Subgroup.inclusion_injective hMH.1)
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
      exact hMmin D ⟨hDH, hDM.trans hMC, ⁅b, a⁆, hmem, by rwa [commutatorElement_def]⟩
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
      exact hMmin Z ⟨hZH, hZM.trans hMC, x, hxZ, hxs⟩ (lt_of_le_of_ne hZM hZne)
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

/-- **The hard case.** -/
theorem palfy_hard [Finite K] [Finite V] [Nontrivial V] {H : Subgroup (Module.End K V)ˣ}
    [Group.IsSolvable H] (hab : palfyAbSc H) :
    24 * Nat.card K ^ 6 * Nat.card H ^ 3 ≤ Nat.card V ^ 69 := by
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
  have hC := palfy_cent_scalar hab hN hmax
  set C := palfyCent H N
  set m := Module.finrank K V
  set q := Nat.card K
  -- `|C| ≤ q`
  have hCq : Nat.card C ≤ q := by
    apply Nat.card_le_card_of_injective (fun c : C => Classical.choose (hC c c.2))
    intro a b hab'
    have ha := Classical.choose_spec (hC a a.2)
    have hb := Classical.choose_spec (hC b b.2)
    apply Subtype.ext; apply Units.ext
    rw [← ha, ← hb]
    simp only at hab'
    rw [hab']
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
  have hH : Nat.card H ≤ q * (q * m ^ 2) ^ T.card := by
    calc Nat.card H ≤ Nat.card N ^ T.card * Nat.card C := hfib
      _ ≤ (q * m ^ 2) ^ T.card * q := Nat.mul_le_mul (Nat.pow_le_pow_left hNcard _) hCq
      _ = q * (q * m ^ 2) ^ T.card := by ring
  rw [hV]
  calc 24 * q ^ 6 * Nat.card H ^ 3 ≤ 24 * q ^ 6 * (q * (q * m ^ 2) ^ T.card) ^ 3 := by
        gcongr
    _ ≤ (q ^ m) ^ 69 := palfy_hard_num hq hm hk

end GI.Proved
