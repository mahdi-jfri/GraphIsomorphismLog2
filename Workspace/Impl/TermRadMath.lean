import Workspace.MulticosetRadical
import Workspace.RadicalCentralizers
import Workspace.Cited.AlgoPermGroups

/-!
# T2, the mathematics: the radical preimage from a chief series of `H`

The paragraph after Lemma A.21: "Compute a chief series of `H` and multiply each term by `N`.
After repetitions are removed, its image is a chief series of `H/N`: each original chief factor
maps injectively or trivially. For each nonabelian image factor `U/V`, compute the preimage of
`C_{H/V}(U/V)` … Their intersection is precisely the radical preimage."

We keep the repetitions instead of removing them: a repeated term gives a trivial factor, which
is abelian, so it is skipped by the nonabelian test. So we work with a *weak* chief chain
(`RadChain`): consecutive terms may be equal. The characterization of the radical
(`RadicalCentralizers.radical_eq_centInter`) holds for weak chains with the same proof
(`rad_radical_eq`); we repeat it here, since the strict inequality is used only to exclude
`U ≤ V`, which the nonabelian hypothesis excludes as well.

For a chief series `H = C₀ > C₁ > ⋯ > C_L = 1` of `H` (the cited `IsChiefSeries`), the images
`t j` of `C_j` in `Q = H/N` form a weak chief chain (`rad_chain`). Its chief property is the
fact of the paper "each original chief factor maps injectively or trivially": for a normal
`M` of `Q` between `t (j+1)` and `t j`, the preimage of `M` meets `C_j` in a normal subgroup of
`H` between `C_{j+1}` and `C_j`, which is one of them by minimality.

The result used later is `rad_mem_iff`: `h ∈ radicalPreimage H N` exactly when `h ∈ H` and, for
every `j` with `⁅C_j, C_j⁆ ≰ N C_{j+1}` (a nonabelian factor of `H/N`), every `x ∈ N C_j`
satisfies `h x h⁻¹ x⁻¹ ∈ N C_{j+1}`. These are the tests and the quotient centralizers that the
program computes (`TermRad.lean`).
-/

namespace GI.Impl

open Equiv GI.Cited
open scoped commutatorElement

/-! ### Weak chief chains -/

section Chain

variable {Q : Type*} [Group Q]

/-- A weak decreasing chief chain of length `L`: normal subgroups `t 0 = Q ≥ t 1 ≥ ⋯ ≥ t L = 1`
with no normal subgroup strictly between consecutive terms. -/
structure RadChain (L : ℕ) (t : ℕ → Subgroup Q) : Prop where
  normal : ∀ i, (t i).Normal
  top : t 0 = ⊤
  bot : t L = ⊥
  le : ∀ i < L, t (i + 1) ≤ t i
  chief : ∀ i < L, ∀ M : Subgroup Q, M.Normal → t (i + 1) ≤ M → M ≤ t i →
    M = t (i + 1) ∨ M = t i

variable {L : ℕ} {t : ℕ → Subgroup Q} (ht : RadChain L t)

/-- The intersection of the preimages of `C_{Q/t(i+1)}(t i / t(i+1))` over the nonabelian
factors. -/
def radCentInter : Subgroup Q :=
  ⨅ (i : ℕ) (_ : i < L) (_ : ¬ ⁅t i, t i⁆ ≤ t (i + 1)),
    GI.RadicalCentralizers.centPre (t i) (t (i + 1)) (ht.normal (i + 1))

include ht in
theorem rad_mem_centInter (x : Q) :
    x ∈ radCentInter ht ↔
      ∀ i < L, ¬ ⁅t i, t i⁆ ≤ t (i + 1) → ∀ u ∈ t i, ⁅x, u⁆ ∈ t (i + 1) := by
  simp only [radCentInter, Subgroup.mem_iInf, GI.RadicalCentralizers.mem_centPre]

theorem rad_centInter_normal : (radCentInter ht).Normal := by
  constructor
  intro x hx g
  rw [rad_mem_centInter] at hx ⊢
  intro i hi hna
  have hN := GI.RadicalCentralizers.centPre_normal (ht.normal i) (ht.normal (i + 1))
  have : x ∈ GI.RadicalCentralizers.centPre (t i) (t (i + 1)) (ht.normal (i + 1)) :=
    (GI.RadicalCentralizers.mem_centPre _ x).mpr (hx i hi hna)
  exact (GI.RadicalCentralizers.mem_centPre _ _).mp (hN.conj_mem x this g)

include ht in
/-- A solvable normal subgroup centralizes every nonabelian factor of the chain. -/
theorem rad_solvable_centralizes {R : Subgroup Q} [R.Normal] [IsSolvable R] {i : ℕ}
    (hi : i < L) (hna : ¬ ⁅t i, t i⁆ ≤ t (i + 1)) :
    ∀ x ∈ R, ∀ u ∈ t i, ⁅x, u⁆ ∈ t (i + 1) := by
  haveI := ht.normal i
  haveI := ht.normal (i + 1)
  set U := t i
  set V := t (i + 1)
  have hVU : V ≤ U := ht.le i hi
  haveI : IsSolvable (R ⊓ U : Subgroup Q) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (inf_le_left : R ⊓ U ≤ R))
  rcases ht.chief i hi ((R ⊓ U) ⊔ V) (Subgroup.sup_normal _ _) le_sup_right
      (sup_le inf_le_right hVU) with hM | hM
  · intro x hx u hu
    apply (le_sup_left : R ⊓ U ≤ (R ⊓ U) ⊔ V).trans hM.le
    exact Subgroup.commutator_le_inf (H₁ := R) (H₂ := U) |> fun h =>
      h (Subgroup.commutator_mem_commutator hx hu)
  · exfalso
    let D : ℕ → Subgroup Q := fun k => (derivedSeries (R ⊓ U : Subgroup Q) k).map
      (R ⊓ U).subtype
    have hD : ∀ k, U ≤ D k ⊔ V := by
      intro k
      induction k with
      | zero =>
        simp only [D, derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        exact hM.symm.le
      | succ k ih =>
        haveI : (⁅U, U⁆ ⊔ V).Normal := Subgroup.sup_normal _ _
        rcases ht.chief i hi (⁅U, U⁆ ⊔ V) inferInstance le_sup_right
            (sup_le (Subgroup.commutator_le_left U U) hVU) with hW | hW
        · exact absurd (le_sup_left.trans hW.le) hna
        · have hDk : D (k + 1) = ⁅D k, D k⁆ := by
            simp only [D, derivedSeries_succ, Subgroup.map_commutator]
          calc U = ⁅U, U⁆ ⊔ V := hW.symm
            _ ≤ ⁅D k ⊔ V, D k ⊔ V⁆ ⊔ V := sup_le_sup_right (Subgroup.commutator_mono ih ih) _
            _ ≤ (⁅D k, D k ⊔ V⁆ ⊔ V) ⊔ V :=
                sup_le_sup_right GI.RadicalCentralizers.commutator_sup_le _
            _ ≤ ((⁅D k, D k⁆ ⊔ V) ⊔ V) ⊔ V := by
                refine sup_le_sup_right (sup_le_sup_right ?_ _) _
                rw [Subgroup.commutator_comm (D k) (D k ⊔ V),
                  Subgroup.commutator_comm (D k) (D k)]
                exact GI.RadicalCentralizers.commutator_sup_le
            _ = D (k + 1) ⊔ V := by rw [hDk, sup_assoc, sup_idem, sup_assoc, sup_idem]
    obtain ⟨k, hk⟩ := (inferInstance : IsSolvable (R ⊓ U : Subgroup Q)).solvable
    have h := hD k
    simp only [D, hk, Subgroup.map_bot, bot_sup_eq] at h
    exact hna ((Subgroup.commutator_le_left U U).trans h)

include ht in
/-- The intersection meets each factor in an abelian section. -/
theorem rad_centInter_factor {i : ℕ} (hi : i < L) :
    ⁅radCentInter ht ⊓ t i, radCentInter ht ⊓ t i⁆ ≤ t (i + 1) := by
  haveI := ht.normal i
  haveI := ht.normal (i + 1)
  haveI := rad_centInter_normal ht
  set U := t i
  set V := t (i + 1)
  set C := radCentInter ht
  have hVU : V ≤ U := ht.le i hi
  by_cases hna : ⁅U, U⁆ ≤ V
  · exact (Subgroup.commutator_mono inf_le_right inf_le_right).trans hna
  have hCU : ⁅C ⊓ U, U⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro x hx u hu
    exact (rad_mem_centInter ht x).mp hx.1 i hi hna u hu
  rcases ht.chief i hi ((C ⊓ U) ⊔ V) (Subgroup.sup_normal _ _) le_sup_right
      (sup_le inf_le_right hVU) with hM | hM
  · exact (Subgroup.commutator_le_left _ _).trans (le_sup_left.trans hM.le)
  · exfalso
    apply hna
    calc ⁅U, U⁆ = ⁅(C ⊓ U) ⊔ V, U⁆ := by rw [hM]
      _ ≤ ⁅C ⊓ U, U⁆ ⊔ V := GI.RadicalCentralizers.commutator_sup_le
      _ ≤ V := sup_le hCU le_rfl

include ht in
/-- The intersection is solvable: its derived series goes down the chain. -/
theorem rad_centInter_solvable : IsSolvable (radCentInter ht) := by
  set C := radCentInter ht
  have key : ∀ k, k ≤ L → (derivedSeries C k).map C.subtype ≤ t k := by
    intro k
    induction k with
    | zero => intro _; rw [ht.top]; exact le_top
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hsub : (derivedSeries C k).map C.subtype ≤ C := Subgroup.map_subtype_le _
      rw [derivedSeries_succ, Subgroup.map_commutator]
      exact (Subgroup.commutator_mono (le_inf hsub h1) (le_inf hsub h1)).trans
        (rad_centInter_factor ht (by omega))
  refine ⟨⟨L, ?_⟩⟩
  have h := key L le_rfl
  rw [ht.bot] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp (le_bot_iff.mp h)

include ht in
/-- **The characterization of the radical for a weak chief chain.** -/
theorem rad_radical_eq [Finite Q] : GI.RadicalSocle.solvableRadical Q = radCentInter ht := by
  haveI := rad_centInter_normal ht
  haveI := rad_centInter_solvable ht
  apply le_antisymm
  · intro x hx
    rw [rad_mem_centInter]
    intro i hi hna u hu
    exact rad_solvable_centralizes ht (R := GI.RadicalSocle.solvableRadical Q) hi hna x hx u hu
  · exact GI.RadicalSocle.le_solvableRadical _

end Chain

/-! ### From `H` to `H/N` -/

section Perm

variable {n : ℕ} {H N : Subgroup (Perm (Fin n))}

/-- The term `j` of a list of subgroups, `⊥` past its end. -/
abbrev radTerm (Hs : List (Subgroup (Perm (Fin n)))) (j : ℕ) : Subgroup (Perm (Fin n)) :=
  Hs.getD j ⊥

/-- A subgroup normalized by `H`, seen in `H`, is normal. -/
theorem rad_subgroupOf_normal {A : Subgroup (Perm (Fin n))}
    (hA : ∀ g ∈ H, ∀ x ∈ A, g * x * g⁻¹ ∈ A) : (A.subgroupOf H).Normal :=
  ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hA g g.2 a ha⟩

/-- The join of two subgroups normalized by `H` is normalized by `H`. -/
theorem rad_sup_normalized {A B : Subgroup (Perm (Fin n))}
    (hA : ∀ g ∈ H, ∀ x ∈ A, g * x * g⁻¹ ∈ A) (hB : ∀ g ∈ H, ∀ x ∈ B, g * x * g⁻¹ ∈ B) :
    ∀ g ∈ H, ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ A ⊔ B := by
  intro g hg x hx
  have : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact (le_sup_left : A ≤ A ⊔ B) (hA g hg y hy)
    · exact (le_sup_right : B ≤ A ⊔ B) (hB g hg y hy)
  exact this hx

/-- Membership in the image of `A ≤ H` in `H/N` is membership in `N ⊔ A`. -/
theorem rad_mem_map_iff [(N.subgroupOf H).Normal] {A : Subgroup (Perm (Fin n))} (hA : A ≤ H)
    (hNH : N ≤ H) (y : H) :
    QuotientGroup.mk' (N.subgroupOf H) y ∈ (A.subgroupOf H).map (QuotientGroup.mk' _) ↔
      (y : Perm (Fin n)) ∈ N ⊔ A := by
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
    ← Subgroup.mem_map_iff_mem H.subtype_injective, Subgroup.map_sup,
    Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hA, inf_eq_left.mpr hNH, sup_comm]
  rfl

/-- The nonabelian test in `H/N` is the test `⁅A, A⁆ ≤ N ⊔ B` in `H`. -/
theorem rad_comm_le_iff [(N.subgroupOf H).Normal] {A B : Subgroup (Perm (Fin n))} (hA : A ≤ H)
    (hB : B ≤ H) (hNH : N ≤ H) :
    ⁅(A.subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H)),
        (A.subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H))⁆ ≤
      (B.subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H)) ↔ ⁅A, A⁆ ≤ N ⊔ B := by
  rw [← Subgroup.map_commutator, Subgroup.map_le_iff_le_comap]
  have hAA : ⁅A, A⁆ = ⁅A.subgroupOf H, A.subgroupOf H⁆.map H.subtype := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA]
  rw [hAA, Subgroup.map_le_iff_le_comap]
  constructor
  · intro h c hc
    exact (rad_mem_map_iff hB hNH c).mp (h hc)
  · intro h c hc
    exact (rad_mem_map_iff hB hNH c).mpr (h hc)

/-- For `y ∈ H` and `V ⊇ N` normalized by `H`, the `x ∈ H` with `y x y⁻¹ x⁻¹ ∈ V` form a
subgroup. -/
def radCentSub (H V : Subgroup (Perm (Fin n))) (y : Perm (Fin n))
    (hV : ∀ g ∈ H, ∀ x ∈ V, g * x * g⁻¹ ∈ V) : Subgroup (Perm (Fin n)) where
  carrier := {x | x ∈ H ∧ y * x * y⁻¹ * x⁻¹ ∈ V}
  one_mem' := ⟨H.one_mem, by simp [V.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
        (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact V.mul_mem ha' (hV a ha _ hb')
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, ?_⟩
    have e : y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact hV a⁻¹ (H.inv_mem ha) _ (V.inv_mem ha')

/-- The centralizer condition in `H/N` is the condition on `N ⊔ A` in `H`. -/
theorem rad_cent_iff [(N.subgroupOf H).Normal] {A B : Subgroup (Perm (Fin n))} (hA : A ≤ H)
    (hB : B ≤ H) (hNH : N ≤ H) (hn : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (hBn : ∀ g ∈ H, ∀ x ∈ B, g * x * g⁻¹ ∈ B) (y : H) :
    (∀ u ∈ (A.subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H)),
        ⁅QuotientGroup.mk' (N.subgroupOf H) y, u⁆ ∈
          (B.subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H))) ↔
      ∀ x ∈ N ⊔ A, (y : Perm (Fin n)) * x * (y : Perm (Fin n))⁻¹ * x⁻¹ ∈ N ⊔ B := by
  have key : ∀ a : H, ⁅QuotientGroup.mk' (N.subgroupOf H) y, QuotientGroup.mk' _ a⁆ ∈
      (B.subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H)) ↔
      (y : Perm (Fin n)) * a * (y : Perm (Fin n))⁻¹ * (a : Perm (Fin n))⁻¹ ∈ N ⊔ B := by
    intro a
    rw [← map_commutatorElement, rad_mem_map_iff hB hNH, commutatorElement_def]
    simp
  constructor
  · intro h
    have hVn := rad_sup_normalized hn hBn
    have hle : N ⊔ A ≤ radCentSub H (N ⊔ B) y hVn := by
      refine sup_le (fun x hx => ⟨hNH hx, ?_⟩) (fun x hx => ⟨hA hx, ?_⟩)
      · have : y * x * (y : Perm (Fin n))⁻¹ * x⁻¹ = (y * x * (y : Perm (Fin n))⁻¹) * x⁻¹ := rfl
        rw [this]
        exact (le_sup_left : N ≤ N ⊔ B) (N.mul_mem (hn y y.2 x hx) (N.inv_mem hx))
      · exact (key ⟨x, hA hx⟩).mp (h _ ⟨⟨x, hA hx⟩, hx, rfl⟩)
    intro x hx
    exact (hle hx).2
  · rintro h _ ⟨a, ha, rfl⟩
    exact (key a).mpr (h a ((le_sup_right : A ≤ N ⊔ A) ha))

/-- The terms of a chief series of `H` lie in `H`. -/
theorem rad_term_le {Hs : List (Subgroup (Perm (Fin n)))} (hs : IsChiefSeries H Hs) :
    ∀ j, radTerm Hs j ≤ H := by
  intro j
  induction j with
  | zero =>
    obtain ⟨h1, -, -, -⟩ := hs
    cases Hs with
    | nil => simp at h1
    | cons a l => simp only [List.head?_cons, Option.some.injEq] at h1; simp [h1]
  | succ j ih =>
    by_cases hj : j + 1 < Hs.length
    · have := (hs.2.2.2 j hj).1
      simp only [radTerm, List.getD_eq_getElem _ _ hj,
        List.getD_eq_getElem _ _ (show j < Hs.length by omega)] at ih ⊢
      exact this.le.trans ih
    · simp [radTerm, List.getElem?_eq_none (show Hs.length ≤ j + 1 by omega)]

/-- The terms of a chief series of `H` are normalized by `H`. -/
theorem rad_term_normalized {Hs : List (Subgroup (Perm (Fin n)))} (hs : IsChiefSeries H Hs)
    (j : ℕ) : ∀ g ∈ H, ∀ x ∈ radTerm Hs j, g * x * g⁻¹ ∈ radTerm Hs j := by
  by_cases hj : j < Hs.length
  · simp only [radTerm, List.getD_eq_getElem _ _ hj]
    exact hs.2.2.1 _ (List.getElem_mem hj)
  · simp only [radTerm, List.getD_eq_default _ _ (show Hs.length ≤ j by omega)]
    intro g _ x hx
    rw [Subgroup.mem_bot] at hx ⊢
    simp [hx]

theorem rad_term_zero {Hs : List (Subgroup (Perm (Fin n)))} (hs : IsChiefSeries H Hs) :
    radTerm Hs 0 = H := by
  obtain ⟨h1, -, -, -⟩ := hs
  cases Hs with
  | nil => simp at h1
  | cons a l => simp only [List.head?_cons, Option.some.injEq] at h1; simp [h1]

theorem rad_term_last {Hs : List (Subgroup (Perm (Fin n)))} (hs : IsChiefSeries H Hs) :
    radTerm Hs (Hs.length - 1) = ⊥ := by
  obtain ⟨-, h2, -, -⟩ := hs
  rw [List.getLast?_eq_getElem?] at h2
  simp only [radTerm, List.getD_eq_getElem?_getD, h2, Option.getD_some]

/-- **A chief series of `H`, multiplied by `N`, gives a chief chain of `H/N`** (paragraph after
Lemma A.21: "each original chief factor maps injectively or trivially"). The images
`t j = C_j N / N` form a weak chief chain of `H/N`: a normal subgroup `M` of `H/N` between
`t (j+1)` and `t j` is one of them, because the preimage of `M` meets `C_j` in a normal
subgroup of `H` between `C_{j+1}` and `C_j`. -/
theorem rad_chain [hN : (N.subgroupOf H).Normal] {Hs : List (Subgroup (Perm (Fin n)))}
    (hs : IsChiefSeries H Hs) :
    RadChain (Hs.length - 1)
      (fun j => ((radTerm Hs j).subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H))) := by
  set π := QuotientGroup.mk' (N.subgroupOf H)
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hle := rad_term_le hs
  refine ⟨fun i => ?_, ?_, ?_, fun i hi => ?_, fun i hi M hM h1 h2 => ?_⟩
  · haveI := rad_subgroupOf_normal (rad_term_normalized hs i)
    exact Subgroup.Normal.map inferInstance π hsurj
  · simp only [rad_term_zero hs, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective π hsurj]
  · simp only [rad_term_last hs, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  · have hi' : i + 1 < Hs.length := by omega
    have := (hs.2.2.2 i hi').1.le
    simp only [radTerm, List.getD_eq_getElem _ _ hi',
      List.getD_eq_getElem _ _ (show i < Hs.length by omega)]
    exact Subgroup.map_mono (fun x hx => this hx)
  · -- the preimage of `M`, cut to `C_i`, back in `Perm`
    have hi' : i + 1 < Hs.length := by omega
    set Ai := (radTerm Hs i).subgroupOf H
    set B := (M.comap π ⊓ Ai).map H.subtype
    have hBn : ∀ x ∈ H, ∀ y ∈ B, x * y * x⁻¹ ∈ B := by
      rintro x hx _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
      haveI := rad_subgroupOf_normal (rad_term_normalized hs i)
      haveI : (M.comap π).Normal := hM.comap π
      refine ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, ⟨?_, ?_⟩, rfl⟩
      · exact (inferInstance : (M.comap π).Normal).conj_mem y hy1 ⟨x, hx⟩
      · exact (inferInstance : Ai.Normal).conj_mem y hy2 ⟨x, hx⟩
    have hsucc : radTerm Hs (i + 1) ≤ radTerm Hs i := by
      have := (hs.2.2.2 i hi').1.le
      simpa only [radTerm, List.getD_eq_getElem _ _ hi',
        List.getD_eq_getElem _ _ (show i < Hs.length by omega)] using this
    have hB1 : radTerm Hs (i + 1) ≤ B := by
      intro x hx
      refine ⟨⟨x, hle (i + 1) hx⟩, ⟨?_, hsucc hx⟩, rfl⟩
      exact h1 ⟨⟨x, hle (i + 1) hx⟩, hx, rfl⟩
    have hB2 : B ≤ radTerm Hs i := by
      rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
      exact hy
    have hch := (hs.2.2.2 i hi').2 B
    simp only [← List.getD_eq_getElem _ ⊥ hi',
      ← List.getD_eq_getElem _ ⊥ (show i < Hs.length by omega)] at hch
    rcases hch hB1 hB2 hBn with hB | hB
    · left
      refine le_antisymm ?_ h1
      intro m hm
      obtain ⟨a, ha, rfl⟩ := h2 hm
      have : (a : Perm (Fin n)) ∈ B := ⟨a, ⟨hm, ha⟩, rfl⟩
      rw [hB] at this
      exact ⟨a, this, rfl⟩
    · right
      refine le_antisymm h2 ?_
      rintro _ ⟨a, ha, rfl⟩
      have : (a : Perm (Fin n)) ∈ B := by rw [hB]; exact ha
      obtain ⟨b, ⟨hb, -⟩, hba⟩ := this
      rw [Subtype.ext hba] at hb
      exact hb

/-- The condition of the program after the factors `j < i`: `h ∈ H`, and `h` centralizes
modulo `N C_{j+1}` every nonabelian factor `N C_j / N C_{j+1}` with `j < i`. -/
def radCond (H N : Subgroup (Perm (Fin n))) (Hs : List (Subgroup (Perm (Fin n)))) (i : ℕ)
    (h : Perm (Fin n)) : Prop :=
  h ∈ H ∧ ∀ j < i, ¬ ⁅radTerm Hs j, radTerm Hs j⁆ ≤ N ⊔ radTerm Hs (j + 1) →
    ∀ x ∈ N ⊔ radTerm Hs j, h * x * h⁻¹ * x⁻¹ ∈ N ⊔ radTerm Hs (j + 1)

/-- **The radical preimage from a chief series of `H`** (paragraph after Lemma A.21). -/
theorem rad_mem_iff (hNH : N ≤ H) (hn : GI.Multicoset.Normalizes H N)
    {Hs : List (Subgroup (Perm (Fin n)))} (hs : IsChiefSeries H Hs) (h : Perm (Fin n)) :
    h ∈ GI.Multicoset.radicalPreimage H N ↔ radCond H N Hs (Hs.length - 1) h := by
  haveI hN := GI.Multicoset.normal_of_normalizes hn
  have ht := rad_chain (H := H) (N := N) hs
  rw [GI.Multicoset.radicalPreimage, dif_pos hN, rad_radical_eq ht]
  have hle := rad_term_le hs
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun j hj hna => ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, rad_mem_centInter] at hy
    have hna' := hna
    rw [← rad_comm_le_iff (hle j) (hle (j + 1)) hNH] at hna'
    exact (rad_cent_iff (hle j) (hle (j + 1)) hNH hn (rad_term_normalized hs (j + 1)) y).mp
      (hy j hj hna')
  · rintro ⟨hH, hc⟩
    refine ⟨⟨h, hH⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, rad_mem_centInter]
    intro j hj hna
    rw [rad_comm_le_iff (hle j) (hle (j + 1)) hNH] at hna
    exact (rad_cent_iff (hle j) (hle (j + 1)) hNH hn (rad_term_normalized hs (j + 1))
      ⟨h, hH⟩).mpr (hc j hj hna)

end Perm

end GI.Impl
