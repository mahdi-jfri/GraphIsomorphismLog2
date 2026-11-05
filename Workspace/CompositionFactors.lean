module

public import Workspace.Cited.CompositionFactors
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finite.Prod

@[expose] public section

/-!
# Jordan-Hölder for the products `a(X)` and `b(X)`

`GI.Cited.CompositionProducts X a b` (trusted, `Workspace/Cited/CompositionFactors.lean`) says
that some composition series of `X` has abelian-factor product `a` and nonabelian-factor
product `b`. Here we prove:

* a finite group has a composition series (`exists_compositionProducts`);
* `a` and `b` do not depend on the series (`compositionProducts_unique`, the Jordan-Hölder
  argument for these two numbers);
* the predicate is invariant under isomorphism, also across universes (`congr`);
* series concatenate over a normal subgroup (`concat`), so `a`, `b` are multiplicative;
* `a(X) b(X) = |X|`, `b` of a solvable group is `1`, `b` of a nonabelian simple group is its
  order, and products of groups multiply `a` and `b`.

The functions `a` and `b` themselves are `GI.Composition.aFac` and `GI.Composition.bFac`.
-/

namespace GI.Composition

open GI.Cited

universe u v w

section Weights

variable (S : Type*) [Group S]

open Classical in
/-- The contribution of a simple factor `S` to `a`: its order if abelian, else `1`. -/
noncomputable def wa : ℕ := if ∀ x y : S, x * y = y * x then Nat.card S else 1

open Classical in
/-- The contribution of a simple factor `S` to `b`: its order if nonabelian, else `1`. -/
noncomputable def wb : ℕ := if ∀ x y : S, x * y = y * x then 1 else Nat.card S

variable {S}

theorem comm_congr {S' : Type*} [Group S'] (e : S ≃* S') :
    (∀ x y : S, x * y = y * x) ↔ (∀ x y : S', x * y = y * x) := by
  constructor
  · intro h x y
    apply e.symm.injective
    rw [map_mul, map_mul, h]
  · intro h x y
    apply e.injective
    rw [map_mul, map_mul, h]

theorem wa_congr {S' : Type*} [Group S'] (e : S ≃* S') : wa S = wa S' := by
  unfold wa
  rw [Nat.card_congr e.toEquiv]
  by_cases h : ∀ x y : S, x * y = y * x
  · rw [if_pos h, if_pos ((comm_congr e).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((comm_congr e).mpr h'))]

theorem wb_congr {S' : Type*} [Group S'] (e : S ≃* S') : wb S = wb S' := by
  unfold wb
  rw [Nat.card_congr e.toEquiv]
  by_cases h : ∀ x y : S, x * y = y * x
  · rw [if_pos h, if_pos ((comm_congr e).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((comm_congr e).mpr h'))]

theorem wa_mul_wb : wa S * wb S = Nat.card S := by
  unfold wa wb
  split_ifs <;> simp

theorem wb_of_comm (h : ∀ x y : S, x * y = y * x) : wb S = 1 := by
  unfold wb
  rw [if_pos h]

theorem wb_of_not_comm (h : ¬ ∀ x y : S, x * y = y * x) : wb S = Nat.card S := by
  unfold wb
  rw [if_neg h]

theorem wa_of_not_comm (h : ¬ ∀ x y : S, x * y = y * x) : wa S = 1 := by
  unfold wa
  rw [if_neg h]

end Weights

section Basic

variable {X : Type u} [Group X]

/-- One step of a composition series, with both weights. -/
theorem step (K : Subgroup X) [K.Normal] {a b : ℕ} (hs : IsSimpleGroup (X ⧸ K))
    (h : CompositionProducts K a b) :
    CompositionProducts X (a * wa (X ⧸ K)) (b * wb (X ⧸ K)) := by
  by_cases hc : ∀ x y : X ⧸ K, x * y = y * x
  · have h1 : wa (X ⧸ K) = Nat.card (X ⧸ K) := by unfold wa; rw [if_pos hc]
    rw [h1, wb_of_comm hc, mul_one]
    exact CompositionProducts.abelianTop X K a b hs hc h
  · rw [wa_of_not_comm hc, wb_of_not_comm hc, mul_one]
    exact CompositionProducts.nonabelianTop X K a b hs hc h

/-- The two shapes of a composition series. -/
theorem cases' {a b : ℕ} (h : CompositionProducts X a b) :
    (Subsingleton X ∧ a = 1 ∧ b = 1) ∨
      ∃ (K : Subgroup X) (_ : K.Normal) (a' b' : ℕ), IsSimpleGroup (X ⧸ K) ∧
        CompositionProducts K a' b' ∧ a = a' * wa (X ⧸ K) ∧ b = b' * wb (X ⧸ K) := by
  cases h with
  | trivial _ => exact Or.inl ⟨inferInstance, rfl, rfl⟩
  | abelianTop _ K a' b' hs hc hK =>
    refine Or.inr ⟨K, inferInstance, a', b, hs, hK, ?_, ?_⟩
    · unfold wa; rw [if_pos hc]
    · rw [wb_of_comm hc, mul_one]
  | nonabelianTop _ K a' b' hs hc hK =>
    refine Or.inr ⟨K, inferInstance, a, b', hs, hK, ?_, ?_⟩
    · rw [wa_of_not_comm hc, mul_one]
    · rw [wb_of_not_comm hc]

/-- Isomorphic groups have the same composition products, also across universes. -/
theorem congr {a b : ℕ} (h : CompositionProducts X a b) :
    ∀ {Y : Type v} [Group Y], (X ≃* Y) → CompositionProducts Y a b := by
  induction h with
  | trivial X =>
    intro Y _ e
    haveI : Subsingleton Y := e.symm.toEquiv.subsingleton
    exact CompositionProducts.trivial Y
  | abelianTop X K a b hs hc hK ih =>
    intro Y _ e
    let K' : Subgroup Y := K.map e.toMonoidHom
    haveI : K'.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    let q : X ⧸ K ≃* Y ⧸ K' := QuotientGroup.congr K K' e rfl
    have hcard : Nat.card (X ⧸ K) = Nat.card (Y ⧸ K') := Nat.card_congr q.toEquiv
    rw [hcard]
    haveI := hs
    exact CompositionProducts.abelianTop Y K' a b q.symm.isSimpleGroup
      ((comm_congr q).mp hc) (ih (e.subgroupMap K))
  | nonabelianTop X K a b hs hc hK ih =>
    intro Y _ e
    let K' : Subgroup Y := K.map e.toMonoidHom
    haveI : K'.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    let q : X ⧸ K ≃* Y ⧸ K' := QuotientGroup.congr K K' e rfl
    have hcard : Nat.card (X ⧸ K) = Nat.card (Y ⧸ K') := Nat.card_congr q.toEquiv
    rw [hcard]
    haveI := hs
    exact CompositionProducts.nonabelianTop Y K' a b q.symm.isSimpleGroup
      (fun h' => hc ((comm_congr q).mpr h')) (ih (e.subgroupMap K))

/-- The product of all factor orders is the order of the group. -/
theorem mul_eq_card {a b : ℕ} (h : CompositionProducts X a b) : a * b = Nat.card X := by
  induction h with
  | trivial X => simp [Nat.card_unique]
  | abelianTop X K a b hs hc hK ih =>
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, ← ih]
    ring
  | nonabelianTop X K a b hs hc hK ih =>
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, ← ih]
    ring

/-- In a solvable group every composition factor is abelian. -/
theorem b_eq_one_of_solvable {a b : ℕ} (h : CompositionProducts X a b) (hX : Group.IsSolvable X) :
    b = 1 := by
  induction h with
  | trivial X => rfl
  | abelianTop X K a b hs hc hK ih =>
    haveI := hX
    exact ih inferInstance
  | nonabelianTop X K a b hs hc hK ih =>
    exfalso
    haveI := hs
    haveI := hX
    exact hc (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance)

/-- A simple group `K` with `X/K` simple-quotient criterion: if `X/K` is simple then `K` is a
maximal normal subgroup. -/
theorem eq_or_eq_top_of_simple {K M : Subgroup X} [K.Normal] [M.Normal]
    (hs : IsSimpleGroup (X ⧸ K)) (hKM : K ≤ M) : M = K ∨ M = ⊤ := by
  haveI : (M.map (QuotientGroup.mk' K)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective K)
  rcases hs.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' K)) with h | h
  · left
    refine le_antisymm (fun x hx => ?_) hKM
    have : (QuotientGroup.mk' K x) ∈ M.map (QuotientGroup.mk' K) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  · right
    refine eq_top_iff.mpr (fun x _ => ?_)
    have : (QuotientGroup.mk' K x) ∈ M.map (QuotientGroup.mk' K) := by rw [h]; trivial
    obtain ⟨m, hm, hmx⟩ := this
    have hk : m⁻¹ * x ∈ K := by
      rw [← QuotientGroup.eq]
      exact hmx
    have := M.mul_mem hm (hKM hk)
    simpa using this

theorem ne_top_of_simple {K : Subgroup X} [K.Normal] (hs : IsSimpleGroup (X ⧸ K)) : K ≠ ⊤ := by
  rintro rfl
  haveI := hs
  haveI := QuotientGroup.subsingleton_quotient_top (G := X)
  exact not_subsingleton (X ⧸ (⊤ : Subgroup X)) inferInstance

/-- A maximal proper normal subgroup has a simple quotient. -/
theorem isSimpleGroup_quotient {K : Subgroup X} [K.Normal] (hK : K ≠ ⊤)
    (hmax : ∀ M : Subgroup X, M.Normal → K ≤ M → M = K ∨ M = ⊤) :
    IsSimpleGroup (X ⧸ K) := by
  haveI : Nontrivial (X ⧸ K) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hK
    refine eq_top_iff.mpr (fun x _ => ?_)
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  refine ⟨fun M hM => ?_⟩
  haveI : (M.comap (QuotientGroup.mk' K)).Normal := hM.comap _
  have hle : K ≤ M.comap (QuotientGroup.mk' K) := by
    intro x hx
    change ((x : X ⧸ K)) ∈ M
    rw [(QuotientGroup.eq_one_iff x).mpr hx]
    exact M.one_mem
  rcases hmax _ inferInstance hle with h | h
  · left
    refine (Subgroup.eq_bot_iff_forall M).mpr (fun y hy => ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    have hx : x ∈ M.comap (QuotientGroup.mk' K) := hy
    rw [h] at hx
    exact (QuotientGroup.eq_one_iff x).mpr hx
  · right
    refine eq_top_iff.mpr (fun y _ => ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    have hx : x ∈ M.comap (QuotientGroup.mk' K) := by rw [h]; trivial
    exact hx

theorem card_lt_of_ne_top [Finite X] {K : Subgroup X} (hK : K ≠ ⊤) :
    Nat.card K < Nat.card X :=
  lt_of_le_of_ne (Subgroup.card_le_card_group K)
    (fun h => hK ((Subgroup.card_eq_iff_eq_top K).mp h))

/-- Every finite group has a composition series. -/
theorem exists_compositionProducts :
    ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X = n →
      ∃ a b : ℕ, CompositionProducts X a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn
  by_cases hsub : Subsingleton X
  · exact ⟨1, 1, CompositionProducts.trivial X⟩
  rw [not_subsingleton_iff_nontrivial] at hsub
  haveI : Finite (Subgroup X) :=
    Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
  let C : Set (Subgroup X) := {K | K.Normal ∧ K ≠ ⊤}
  have hC : C.Nonempty := ⟨⊥, inferInstance, bot_ne_top⟩
  obtain ⟨K, hK, hmax'⟩ := Set.Finite.exists_maximalFor id C (Set.toFinite C) hC
  haveI : K.Normal := hK.1
  have hmax : ∀ M : Subgroup X, M.Normal → K ≤ M → M = K ∨ M = ⊤ := by
    intro M hM hKM
    by_cases htop : M = ⊤
    · exact Or.inr htop
    · exact Or.inl (le_antisymm (hmax' ⟨hM, htop⟩ hKM) hKM)
  have hs := isSimpleGroup_quotient hK.2 hmax
  obtain ⟨a, b, hab⟩ := ih (Nat.card K) (hn ▸ card_lt_of_ne_top hK.2) K rfl
  exact ⟨_, _, step K hs hab⟩

theorem exists_compositionProducts' [Finite X] : ∃ a b : ℕ, CompositionProducts X a b :=
  exists_compositionProducts _ X rfl

theorem eq_top_of_subsingleton_quotient {N : Subgroup X} [N.Normal] (h : Subsingleton (X ⧸ N)) :
    N = ⊤ := by
  refine eq_top_iff.mpr (fun x _ => ?_)
  rw [← QuotientGroup.eq_one_iff]
  exact Subsingleton.elim _ _

theorem mem_ker_comp_subtype {K K' : Subgroup X} [K'.Normal] (x : K) :
    x ∈ ((QuotientGroup.mk' K').comp K.subtype).ker ↔ (x : X) ∈ K' := by
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]

/-- Two distinct maximal normal subgroups generate the whole group, so `K → X/K'` is onto. -/
theorem comp_subtype_surjective {K K' : Subgroup X} [K.Normal] [K'.Normal]
    (hs : IsSimpleGroup (X ⧸ K)) (hs' : IsSimpleGroup (X ⧸ K')) (hne : K ≠ K') :
    Function.Surjective ((QuotientGroup.mk' K').comp K.subtype) := by
  have hsup : K ⊔ K' = ⊤ := by
    haveI : (K ⊔ K').Normal := Subgroup.sup_normal K K'
    rcases eq_or_eq_top_of_simple hs (le_sup_left : K ≤ K ⊔ K') with h | h
    · exfalso
      have hK'K : K' ≤ K := h ▸ (le_sup_right : K' ≤ K ⊔ K')
      rcases eq_or_eq_top_of_simple hs' hK'K with h' | h'
      · exact hne h'
      · exact ne_top_of_simple hs h'
    · exact h
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K' y
  have hx : x ∈ K ⊔ K' := by rw [hsup]; trivial
  obtain ⟨k, hk, k', hk', rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  refine ⟨⟨k, hk⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq]
  simpa using hk'

/-- The two "intersections" `K ∩ K'`, seen inside `K` and inside `K'`, are isomorphic. -/
def interEquiv (K K' : Subgroup X) [K.Normal] [K'.Normal] :
    ((QuotientGroup.mk' K').comp K.subtype).ker ≃*
      ((QuotientGroup.mk' K).comp K'.subtype).ker where
  toFun y := ⟨⟨y.1.1, (mem_ker_comp_subtype y.1).mp y.2⟩,
    (mem_ker_comp_subtype (K := K') (K' := K) _).mpr y.1.2⟩
  invFun y := ⟨⟨y.1.1, (mem_ker_comp_subtype y.1).mp y.2⟩,
    (mem_ker_comp_subtype (K := K) (K' := K') _).mpr y.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- **Jordan-Hölder for `a` and `b`.** All composition series of a finite group give the same
two products. The proof is the usual one: if the tops `K`, `K'` differ, both `K` and `K'`
have a series through `K ∩ K'`, with top factors `X/K'` and `X/K`. -/
theorem unique_aux : ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X = n →
    ∀ {a b a' b' : ℕ}, CompositionProducts X a b → CompositionProducts X a' b' →
      a = a' ∧ b = b' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn a b a' b' h h'
  rcases cases' h with ⟨hsub, rfl, rfl⟩ | ⟨K, hKn, a1, b1, hs, hK, rfl, rfl⟩
  · rcases cases' h' with ⟨_, rfl, rfl⟩ | ⟨K, hKn, a1, b1, hs, hK, rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exfalso
      exact ne_top_of_simple hs (eq_top_iff.mpr (fun x _ => by
        rw [Subsingleton.elim x 1]; exact K.one_mem))
  rcases cases' h' with ⟨hsub, rfl, rfl⟩ | ⟨K', hK'n, a2, b2, hs', hK', rfl, rfl⟩
  · exfalso
    exact ne_top_of_simple hs (eq_top_iff.mpr (fun x _ => by
      rw [Subsingleton.elim x 1]; exact K.one_mem))
  have hlt : ∀ {M : Subgroup X} [M.Normal], IsSimpleGroup (X ⧸ M) → Nat.card M < n :=
    fun hsM => hn ▸ card_lt_of_ne_top (ne_top_of_simple hsM)
  by_cases hKK : K = K'
  · subst hKK
    obtain ⟨h1, h2⟩ := ih _ (hlt hs) K rfl hK hK'
    subst h1 h2
    exact ⟨rfl, rfl⟩
  -- the series of `K` and `K'` through their intersection
  have hφ := comp_subtype_surjective hs hs' hKK
  have hφ' := comp_subtype_surjective hs' hs (Ne.symm hKK)
  let L := ((QuotientGroup.mk' K').comp K.subtype).ker
  let L' := ((QuotientGroup.mk' K).comp K'.subtype).ker
  let q : K ⧸ L ≃* X ⧸ K' := QuotientGroup.quotientKerEquivOfSurjective _ hφ
  let q' : K' ⧸ L' ≃* X ⧸ K := QuotientGroup.quotientKerEquivOfSurjective _ hφ'
  have hsL : IsSimpleGroup (K ⧸ L) := by haveI := hs'; exact q.isSimpleGroup
  have hsL' : IsSimpleGroup (K' ⧸ L') := by haveI := hs; exact q'.isSimpleGroup
  obtain ⟨ad, bd, hD⟩ := exists_compositionProducts' (X := L)
  have hD' : CompositionProducts L' ad bd := congr hD (interEquiv K K')
  obtain ⟨e1, e2⟩ := ih _ (hlt hs) K rfl hK (step L hsL hD)
  obtain ⟨e3, e4⟩ := ih _ (hlt hs') K' rfl hK' (step L' hsL' hD')
  rw [e1, e2, e3, e4, wa_congr q, wb_congr q, wa_congr q', wb_congr q']
  constructor <;> ring

theorem compositionProducts_unique [Finite X] {a b a' b' : ℕ} (h : CompositionProducts X a b)
    (h' : CompositionProducts X a' b') : a = a' ∧ b = b' :=
  unique_aux _ X rfl h h'

/-- **Concatenation.** A series of `N` followed by (the preimage of) a series of `X/N`. -/
theorem concat_aux : ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X = n →
    ∀ (N : Subgroup X) [N.Normal] {a b a' b' : ℕ}, CompositionProducts N a b →
      CompositionProducts (X ⧸ N) a' b' → CompositionProducts X (a * a') (b * b') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn N _ a b a' b' hN hQ
  rcases cases' hQ with ⟨hsub, rfl, rfl⟩ | ⟨Lb, hLbn, a1, b1, hs, hLb, rfl, rfl⟩
  · have htop := eq_top_of_subsingleton_quotient hsub
    rw [mul_one, mul_one]
    exact congr hN ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
  let ψ : X →* (X ⧸ N) ⧸ Lb := (QuotientGroup.mk' Lb).comp (QuotientGroup.mk' N)
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective Lb).comp (QuotientGroup.mk'_surjective N)
  let L := ψ.ker
  let q : X ⧸ L ≃* (X ⧸ N) ⧸ Lb := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  have hsL : IsSimpleGroup (X ⧸ L) := by haveI := hs; exact q.isSimpleGroup
  have hlt : Nat.card L < n := hn ▸ card_lt_of_ne_top (ne_top_of_simple hsL)
  have hmemL : ∀ x : X, x ∈ L ↔ (QuotientGroup.mk' N x) ∈ Lb := by
    intro x
    change ψ x = 1 ↔ _
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hNL : N ≤ L := by
    intro x hx
    rw [hmemL, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Lb.one_mem
  let χ : L →* Lb := ((QuotientGroup.mk' N).comp L.subtype).codRestrict Lb
    (fun x => (hmemL x).mp x.2)
  have hχ : Function.Surjective χ := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N y.1
    have hxL : x ∈ L := (hmemL x).mpr (hx ▸ y.2)
    exact ⟨⟨x, hxL⟩, Subtype.ext hx⟩
  have hker : χ.ker = N.subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  have hNk : CompositionProducts χ.ker a b :=
    congr hN ((Subgroup.subgroupOfEquivOfLe hNL).symm.trans (MulEquiv.subgroupCongr hker.symm))
  have hQk : CompositionProducts (L ⧸ χ.ker) a1 b1 :=
    congr hLb (QuotientGroup.quotientKerEquivOfSurjective χ hχ).symm
  have hL := ih _ hlt L rfl χ.ker hNk hQk
  have hX := step L hsL hL
  rw [wa_congr q, wb_congr q] at hX
  convert hX using 1 <;> ring

theorem concat [Finite X] (N : Subgroup X) [N.Normal] {a b a' b' : ℕ}
    (hN : CompositionProducts N a b) (hQ : CompositionProducts (X ⧸ N) a' b') :
    CompositionProducts X (a * a') (b * b') :=
  concat_aux _ X rfl N hN hQ

end Basic

/-! ### The functions `a` and `b` -/

section Functions

variable (X : Type u) [Group X] [Finite X]

/-- `a(X)`: the product of the orders of the abelian composition factors of `X`. -/
noncomputable def aFac : ℕ := Classical.choose (exists_compositionProducts' (X := X))

/-- `b(X)`: the product of the orders of the nonabelian composition factors of `X`. -/
noncomputable def bFac : ℕ :=
  Classical.choose (Classical.choose_spec (exists_compositionProducts' (X := X)))

theorem spec : CompositionProducts X (aFac X) (bFac X) :=
  Classical.choose_spec (Classical.choose_spec (exists_compositionProducts' (X := X)))

variable {X}

theorem aFac_eq {a b : ℕ} (h : CompositionProducts X a b) : aFac X = a :=
  (compositionProducts_unique (spec X) h).1

theorem bFac_eq {a b : ℕ} (h : CompositionProducts X a b) : bFac X = b :=
  (compositionProducts_unique (spec X) h).2

theorem aFac_mul_bFac : aFac X * bFac X = Nat.card X := mul_eq_card (spec X)

theorem aFac_pos : 0 < aFac X := by
  have h := aFac_mul_bFac (X := X)
  have hc : 0 < Nat.card X := Nat.card_pos
  rcases Nat.eq_zero_or_pos (aFac X) with h0 | h0
  · rw [h0, zero_mul] at h; omega
  · exact h0

theorem bFac_pos : 0 < bFac X := by
  have h := aFac_mul_bFac (X := X)
  have hc : 0 < Nat.card X := Nat.card_pos
  rcases Nat.eq_zero_or_pos (bFac X) with h0 | h0
  · rw [h0, mul_zero] at h; omega
  · exact h0

theorem aFac_le_card : aFac X ≤ Nat.card X := by
  rw [← aFac_mul_bFac]
  exact Nat.le_mul_of_pos_right _ bFac_pos

theorem bFac_le_card : bFac X ≤ Nat.card X := by
  rw [← aFac_mul_bFac]
  exact Nat.le_mul_of_pos_left _ aFac_pos

theorem aFac_congr {Y : Type v} [Group Y] [Finite Y] (e : X ≃* Y) : aFac X = aFac Y :=
  (aFac_eq (congr (spec X) e)).symm

theorem bFac_congr {Y : Type v} [Group Y] [Finite Y] (e : X ≃* Y) : bFac X = bFac Y :=
  (bFac_eq (congr (spec X) e)).symm

/-- Multiplicativity over a normal subgroup: `a(X) = a(N) a(X/N)`. -/
theorem aFac_mul (N : Subgroup X) [N.Normal] : aFac X = aFac N * aFac (X ⧸ N) :=
  aFac_eq (concat N (spec N) (spec _))

/-- Multiplicativity over a normal subgroup: `b(X) = b(N) b(X/N)`. -/
theorem bFac_mul (N : Subgroup X) [N.Normal] : bFac X = bFac N * bFac (X ⧸ N) :=
  bFac_eq (concat N (spec N) (spec _))

theorem aFac_ker_range {Y : Type v} [Group Y] [Finite Y] (f : X →* Y) :
    aFac X = aFac f.ker * aFac f.range := by
  rw [aFac_mul f.ker, aFac_congr (QuotientGroup.quotientKerEquivRange f)]

theorem bFac_ker_range {Y : Type v} [Group Y] [Finite Y] (f : X →* Y) :
    bFac X = bFac f.ker * bFac f.range := by
  rw [bFac_mul f.ker, bFac_congr (QuotientGroup.quotientKerEquivRange f)]

/-- `b` of a solvable group is `1`. -/
theorem bFac_of_solvable [Group.IsSolvable X] : bFac X = 1 :=
  b_eq_one_of_solvable (spec X) inferInstance

omit [Finite X] in
theorem simple_compositionProducts [IsSimpleGroup X] :
    CompositionProducts X (wa X) (wb X) := by
  have hs : IsSimpleGroup (X ⧸ (⊥ : Subgroup X)) := QuotientGroup.quotientBot.isSimpleGroup
  have h := step (⊥ : Subgroup X) hs (CompositionProducts.trivial _)
  rw [one_mul, one_mul, wa_congr QuotientGroup.quotientBot,
    wb_congr QuotientGroup.quotientBot] at h
  exact h

/-- `b` of a nonabelian simple group is its order. -/
theorem bFac_of_simple [IsSimpleGroup X] (hc : ¬ ∀ x y : X, x * y = y * x) :
    bFac X = Nat.card X := by
  rw [bFac_eq simple_compositionProducts, wb_of_not_comm hc]

theorem aFac_of_simple [IsSimpleGroup X] (hc : ¬ ∀ x y : X, x * y = y * x) : aFac X = 1 := by
  rw [aFac_eq simple_compositionProducts, wa_of_not_comm hc]

end Functions

/-! ### Products -/

section Products

theorem prod_compositionProducts {A B : Type u} [Group A] [Group B] [Finite A] [Finite B]
    {a b a' b' : ℕ} (hA : CompositionProducts A a b) (hB : CompositionProducts B a' b') :
    CompositionProducts (A × B) (a * a') (b * b') := by
  let f := MonoidHom.snd A B
  have hf : Function.Surjective f := Prod.snd_surjective
  have hker : (MonoidHom.inl A B).range = f.ker := by
    ext ⟨x, y⟩
    simp only [MonoidHom.mem_range, MonoidHom.inl_apply, MonoidHom.mem_ker, f,
      MonoidHom.coe_snd, Prod.mk.injEq]
    constructor
    · rintro ⟨z, rfl, rfl⟩; rfl
    · rintro rfl; exact ⟨x, rfl, rfl⟩
  have e1 : A ≃* f.ker := (MonoidHom.ofInjective (f := MonoidHom.inl A B)
    (fun x y h => congrArg Prod.fst h)).trans (MulEquiv.subgroupCongr hker)
  exact concat f.ker (congr hA e1)
    (congr hB (QuotientGroup.quotientKerEquivOfSurjective f hf).symm)

/-- The group of functions on `Option ι`. -/
def piOptionMulEquiv {ι : Type u} (T : Option ι → Type u) [∀ i, Group (T i)] :
    (∀ i, T i) ≃* T none × ∀ i, T (some i) :=
  { Equiv.piOptionEquivProd with map_mul' := fun _ _ => rfl }

/-- Reindexing a product of groups. -/
def piCongrMulEquiv {α β : Type u} (e : α ≃ β) (T : β → Type u) [∀ i, Group (T i)] :
    (∀ b, T b) ≃* ∀ a, T (e a) :=
  { Equiv.piCongrLeft' T e.symm with map_mul' := fun _ _ => rfl }

/-- A finite product of finite groups has the products of the factors' `a` and `b`. -/
theorem pi_compositionProducts (ι : Type u) [Fintype ι] (T : ι → Type u) [∀ i, Group (T i)]
    [∀ i, Finite (T i)] :
    CompositionProducts (∀ i, T i) (∏ i, aFac (T i)) (∏ i, bFac (T i)) := by
  revert T
  refine Fintype.induction_empty_option (P := fun ι _ => ∀ (T : ι → Type u)
    [∀ i, Group (T i)] [∀ i, Finite (T i)],
    CompositionProducts (∀ i, T i) (∏ i, aFac (T i)) (∏ i, bFac (T i))) ?_ ?_ ?_ ι
  · intro α β _ e ih T _ _
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun a => T (e a))
    rw [Equiv.prod_comp e (fun b => aFac (T b)), Equiv.prod_comp e (fun b => bFac (T b))] at h
    exact congr h (piCongrMulEquiv e T).symm
  · intro T _ _
    haveI : Subsingleton (∀ i : PEmpty, T i) := ⟨fun _ _ => funext (fun i => i.elim)⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact CompositionProducts.trivial _
  · intro α _ ih T _ _
    have h := prod_compositionProducts (spec (T none)) (ih (fun a => T (some a)))
    rw [Fintype.prod_option, Fintype.prod_option]
    exact congr h (piOptionMulEquiv T).symm

end Products

end GI.Composition
