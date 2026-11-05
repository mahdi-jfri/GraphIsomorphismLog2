module

public import Workspace.CamDirectSocle
public import Workspace.Impl.CamBranch
public import Workspace.Proved.GMPTransitive
public import Workspace.Proved.SCosPalfy
public import Workspace.Impl.TermRadMath

@[expose] public section

/-!
# Nonabelian-chief normal chains and the radical preimage

This file proves the mathematics for constructing a nonabelian-chief normal chain from `H` to `N`
when `N ⊴ H ≤ Perm (Fin n)` with `N` transitive on `Fin n`, without using a polynomial-time
chief series algorithm:

1. **Radical preimage from a nonabelian-chief chain (`nonabelianChief_rad_mem_iff`)**:
   In `RadicalCentralizers.lean` and `TermRadMath.lean`, the chief property between consecutive
   terms `t (i + 1) ≤ t i` of a normal chain is needed only when the factor is nonabelian
   (`¬ ⁅t i, t i⁆ ≤ t (i + 1)`), because abelian factors are skipped by the test and automatically
   satisfied by the commutator condition. Thus any normal chain `Hs` from `H` down to a subgroup
   of `N` whose nonabelian steps are chief in `H/N` (`IsNonabelianChiefChain H N Hs`) characterizes
   `radicalPreimage H N` via the exact same `radCond` used by `TermRadLoop` and `TermRad`.
2. **Subgroup cardinality and chain-length bounds**:
   Every strict subgroup inclusion `K < C` in `Perm (Fin n)` satisfies `2 * Nat.card K ≤ Nat.card C`
   and `1 ≤ n`, with `Nat.card C < 2 ^ (n ^ 2)`.
3. **Lemma 2.4 (`primitive_surjective_card_le_bFac`, `orbitBlockStep_index_le`)**:
   Under `MarotiPrimitive`, any quotient `Q` of a primitive group `G ≤ Perm (Fin d)` has order
   at most `max (24!) (d ^ (1 + Nat.log 2 d)) * bFac Q`. Combined with `gmp_degreeBound`
   (`bFac (H ⧸ N) ≤ n ^ (1 + Nat.log 2 n)` for transitive `N ⊴ H ≤ Perm (Fin n)`), any step
   `J' ⊴ J ≤ H` where `J / J'` acts primitively on `d ≤ n` blocks of an orbit satisfies
   `[(J ⊔ N) : (J' ⊔ N)] ≤ max (24!) (n ^ (1 + Nat.log 2 n)) * n ^ (1 + Nat.log 2 n)`.
4. **Lemma 2.5 (`greedyMaxFold_maximal`)**:
   Given `W < U ≤ A` with `U, W` normalized by `A` and a right-coset transversal `rs` of `W` in `U`,
   greedily replacing `V` by `camNormClosure A (V ⊔ ⟨{r}⟩)` whenever this normal closure does not
   contain `U` produces a maximal proper `A`-normalized subgroup `V` of `U` containing `W`.
5. **Lemma 2.6 (`simple_and_noncomm_of_maximal`, `isSimpleInter_index_le`, `conjPass`)**:
   Starting from `M_max` produced by `greedyMaxFold` with `A = U` on a perfect `U/N`, the quotient
   `U / M_max` is nonabelian simple, and repeatedly intersecting `W` with `h W h⁻¹` for generators
   `h` of `H` keeps `[U : W] = bFac (U / W) ≤ n ^ (1 + Nat.log 2 n)` and reaches an `H`-normalized
   subgroup `W` in at most `n ^ 2` passes. A second `greedyMaxFold` with `A = H` on `(U, W)` then
   yields `V` such that `U / V` is a nonabelian chief factor of `H`.
-/

namespace GI.Impl

open Equiv GI.Cited GI.Composition GI.Proved
open scoped commutatorElement

/-! ### 1. Nonabelian-chief chains and the radical preimage -/

section Chain

variable {Q : Type*} [Group Q]

/-- A decreasing normal chain `t 0 = Q ≥ t 1 ≥ ⋯ ≥ t L = 1` whose nonabelian steps have no
strictly intermediate normal subgroup of `Q`. -/
structure NonabelianRadChain (L : ℕ) (t : ℕ → Subgroup Q) : Prop where
  normal : ∀ i, (t i).Normal
  top : t 0 = ⊤
  bot : t L = ⊥
  le : ∀ i < L, t (i + 1) ≤ t i
  chief : ∀ i < L, ¬ ⁅t i, t i⁆ ≤ t (i + 1) → ∀ M : Subgroup Q, M.Normal →
    t (i + 1) ≤ M → M ≤ t i → M = t (i + 1) ∨ M = t i

variable {L : ℕ} {t : ℕ → Subgroup Q} (ht : NonabelianRadChain L t)

/-- The intersection of the preimages of `C_{Q/t(i+1)}(t i / t(i+1))` over the nonabelian
factors of `ht`. -/
def nonabelianRadCentInter : Subgroup Q :=
  ⨅ (i : ℕ) (_ : i < L) (_ : ¬ ⁅t i, t i⁆ ≤ t (i + 1)),
    GI.RadicalCentralizers.centPre (t i) (t (i + 1)) (ht.normal (i + 1))

include ht in
theorem nonabelianRad_mem_centInter (x : Q) :
    x ∈ nonabelianRadCentInter ht ↔
      ∀ i < L, ¬ ⁅t i, t i⁆ ≤ t (i + 1) → ∀ u ∈ t i, ⁅x, u⁆ ∈ t (i + 1) := by
  simp only [nonabelianRadCentInter, Subgroup.mem_iInf, GI.RadicalCentralizers.mem_centPre]

theorem nonabelianRad_centInter_normal : (nonabelianRadCentInter ht).Normal := by
  constructor
  intro x hx g
  rw [nonabelianRad_mem_centInter] at hx ⊢
  intro i hi hna
  have hN := GI.RadicalCentralizers.centPre_normal (ht.normal i) (ht.normal (i + 1))
  have : x ∈ GI.RadicalCentralizers.centPre (t i) (t (i + 1)) (ht.normal (i + 1)) :=
    (GI.RadicalCentralizers.mem_centPre _ x).mpr (hx i hi hna)
  exact (GI.RadicalCentralizers.mem_centPre _ _).mp (hN.conj_mem x this g)

include ht in
/-- A solvable normal subgroup centralizes every nonabelian factor of a `NonabelianRadChain`. -/
theorem nonabelianRad_solvable_centralizes {R : Subgroup Q} [R.Normal] [Group.IsSolvable R]
    {i : ℕ} (hi : i < L) (hna : ¬ ⁅t i, t i⁆ ≤ t (i + 1)) :
    ∀ x ∈ R, ∀ u ∈ t i, ⁅x, u⁆ ∈ t (i + 1) := by
  have := ht.normal i
  have := ht.normal (i + 1)
  set U := t i
  set V := t (i + 1)
  have hVU : V ≤ U := ht.le i hi
  have : Group.IsSolvable (R ⊓ U : Subgroup Q) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : R ⊓ U ≤ R))
  rcases ht.chief i hi hna ((R ⊓ U) ⊔ V) (Subgroup.sup_normal _ _) le_sup_right
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
        have : (⁅U, U⁆ ⊔ V).Normal := Subgroup.sup_normal _ _
        rcases ht.chief i hi hna (⁅U, U⁆ ⊔ V) inferInstance le_sup_right
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
    obtain ⟨k, hk⟩ := (inferInstance : Group.IsSolvable (R ⊓ U : Subgroup Q)).solvable
    have h := hD k
    simp only [D, hk, Subgroup.map_bot, bot_sup_eq] at h
    exact hna ((Subgroup.commutator_le_left U U).trans h)

include ht in
/-- The intersection meets each factor of a `NonabelianRadChain` in an abelian section. -/
theorem nonabelianRad_centInter_factor {i : ℕ} (hi : i < L) :
    ⁅nonabelianRadCentInter ht ⊓ t i, nonabelianRadCentInter ht ⊓ t i⁆ ≤ t (i + 1) := by
  have := ht.normal i
  have := ht.normal (i + 1)
  have := nonabelianRad_centInter_normal ht
  set U := t i
  set V := t (i + 1)
  set C := nonabelianRadCentInter ht
  have hVU : V ≤ U := ht.le i hi
  by_cases hna : ⁅U, U⁆ ≤ V
  · exact (Subgroup.commutator_mono inf_le_right inf_le_right).trans hna
  have hCU : ⁅C ⊓ U, U⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro x hx u hu
    exact (nonabelianRad_mem_centInter ht x).mp hx.1 i hi hna u hu
  rcases ht.chief i hi hna ((C ⊓ U) ⊔ V) (Subgroup.sup_normal _ _) le_sup_right
      (sup_le inf_le_right hVU) with hM | hM
  · exact (Subgroup.commutator_le_left _ _).trans (le_sup_left.trans hM.le)
  · exfalso
    apply hna
    calc ⁅U, U⁆ = ⁅(C ⊓ U) ⊔ V, U⁆ := by rw [hM]
      _ ≤ ⁅C ⊓ U, U⁆ ⊔ V := GI.RadicalCentralizers.commutator_sup_le
      _ ≤ V := sup_le hCU le_rfl

include ht in
/-- The intersection over a `NonabelianRadChain` is solvable. -/
theorem nonabelianRad_centInter_solvable : Group.IsSolvable (nonabelianRadCentInter ht) := by
  set C := nonabelianRadCentInter ht
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
        (nonabelianRad_centInter_factor ht (by omega))
  refine ⟨⟨L, ?_⟩⟩
  have h := key L le_rfl
  rw [ht.bot] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp (le_bot_iff.mp h)

include ht in
/-- **Characterization of the solvable radical for a `NonabelianRadChain`.** -/
theorem nonabelianRad_radical_eq [Finite Q] :
    GI.RadicalSocle.solvableRadical Q = nonabelianRadCentInter ht := by
  have := nonabelianRad_centInter_normal ht
  have := nonabelianRad_centInter_solvable ht
  apply le_antisymm
  · intro x hx
    rw [nonabelianRad_mem_centInter]
    intro i hi hna u hu
    exact nonabelianRad_solvable_centralizes ht (R := GI.RadicalSocle.solvableRadical Q)
      hi hna x hx u hu
  · exact GI.RadicalSocle.le_solvableRadical _

end Chain

section PermChain

variable {n : ℕ} {H N : Subgroup (Perm (Fin n))}

/-- A decreasing chain `Hs` of `H`-normalized subgroups of `H` starting at `H`, ending in a
subgroup of `N`, such that every nonabelian step `N Hs[i] / N Hs[i+1]` has no strictly
intermediate `H`-normalized subgroup. -/
def IsNonabelianChiefChain (H N : Subgroup (Perm (Fin n)))
    (Hs : List (Subgroup (Perm (Fin n)))) : Prop :=
  Hs.head? = some H ∧ (∃ K, Hs.getLast? = some K ∧ K ≤ N) ∧
  (∀ U ∈ Hs, U ≤ H ∧ ∀ x ∈ H, ∀ y ∈ U, x * y * x⁻¹ ∈ U) ∧
  ∀ i (h : i + 1 < Hs.length),
    Hs[i + 1] ≤ Hs[i] ∧
    (¬ ⁅Hs[i], Hs[i]⁆ ≤ N ⊔ Hs[i + 1] →
      ∀ M : Subgroup (Perm (Fin n)), N ⊔ Hs[i + 1] ≤ M → M ≤ N ⊔ Hs[i] →
        (∀ x ∈ H, ∀ y ∈ M, x * y * x⁻¹ ∈ M) → M = N ⊔ Hs[i + 1] ∨ M = N ⊔ Hs[i])

theorem nonabelianChief_term_le {Hs : List (Subgroup (Perm (Fin n)))}
    (hs : IsNonabelianChiefChain H N Hs) (j : ℕ) : radTerm Hs j ≤ H := by
  by_cases hj : j < Hs.length
  · simp only [radTerm, List.getD_eq_getElem _ _ hj]
    exact (hs.2.2.1 _ (List.getElem_mem hj)).1
  · simp [radTerm, List.getElem?_eq_none (show Hs.length ≤ j by omega)]

theorem nonabelianChief_term_normalized {Hs : List (Subgroup (Perm (Fin n)))}
    (hs : IsNonabelianChiefChain H N Hs) (j : ℕ) :
    ∀ g ∈ H, ∀ x ∈ radTerm Hs j, g * x * g⁻¹ ∈ radTerm Hs j := by
  by_cases hj : j < Hs.length
  · simp only [radTerm, List.getD_eq_getElem _ _ hj]
    exact (hs.2.2.1 _ (List.getElem_mem hj)).2
  · simp only [radTerm, List.getD_eq_default _ _ (show Hs.length ≤ j by omega)]
    intro g _ x hx
    rw [Subgroup.mem_bot] at hx ⊢
    simp [hx]

theorem nonabelianChief_term_zero {Hs : List (Subgroup (Perm (Fin n)))}
    (hs : IsNonabelianChiefChain H N Hs) : radTerm Hs 0 = H := by
  obtain ⟨h1, -, -, -⟩ := hs
  cases Hs with
  | nil => simp at h1
  | cons a l => simp only [List.head?_cons, Option.some.injEq] at h1; simp [h1]

theorem nonabelianChief_term_last_le {Hs : List (Subgroup (Perm (Fin n)))}
    (hs : IsNonabelianChiefChain H N Hs) : radTerm Hs (Hs.length - 1) ≤ N := by
  obtain ⟨-, ⟨K, h2, hKN⟩, -, -⟩ := hs
  rw [List.getLast?_eq_getElem?] at h2
  simp only [radTerm, List.getD_eq_getElem?_getD, h2, Option.getD_some]
  exact hKN

/-- An `IsNonabelianChiefChain` from `H` to `N` induces a `NonabelianRadChain` in `H ⧸ N`. -/
theorem nonabelianChief_chain [hN : (N.subgroupOf H).Normal] (hNH : N ≤ H)
    {Hs : List (Subgroup (Perm (Fin n)))} (hs : IsNonabelianChiefChain H N Hs) :
    NonabelianRadChain (Hs.length - 1)
      (fun j => ((radTerm Hs j).subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H))) := by
  set π := QuotientGroup.mk' (N.subgroupOf H)
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hle := nonabelianChief_term_le hs
  refine ⟨fun i => ?_, ?_, ?_, fun i hi => ?_, fun i hi hna M hM h1 h2 => ?_⟩
  · have := rad_subgroupOf_normal (nonabelianChief_term_normalized hs i)
    exact Subgroup.Normal.map inferInstance π hsurj
  · simp only [nonabelianChief_term_zero hs, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective π hsurj]
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact Subgroup.subgroupOf_mono H (nonabelianChief_term_last_le hs)
  · have hi' : i + 1 < Hs.length := by omega
    have := (hs.2.2.2 i hi').1
    simp only [radTerm, List.getD_eq_getElem _ _ hi',
      List.getD_eq_getElem _ _ (show i < Hs.length by omega)]
    exact Subgroup.map_mono (fun x hx => this hx)
  · have hi' : i + 1 < Hs.length := by omega
    have hi0 : i < Hs.length := by omega
    have hna' : ¬ ⁅Hs[i]'hi0, Hs[i]'hi0⁆ ≤ N ⊔ Hs[i + 1]'hi' := by
      intro hcomm
      apply hna
      have hcomm' : ⁅radTerm Hs i, radTerm Hs i⁆ ≤ N ⊔ radTerm Hs (i + 1) := by
        simpa only [radTerm, List.getD_eq_getElem _ _ hi0, List.getD_eq_getElem _ _ hi'] using hcomm
      exact (rad_comm_le_iff (hle i) (hle (i + 1)) hNH).mpr hcomm'
    set B := (M.comap π).map H.subtype
    have hBn : ∀ x ∈ H, ∀ y ∈ B, x * y * x⁻¹ ∈ B := by
      rintro x hx _ ⟨y, hy, rfl⟩
      have : (M.comap π).Normal := hM.comap π
      exact ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, (inferInstance : (M.comap π).Normal).conj_mem y hy ⟨x, hx⟩, rfl⟩
    have hNB : N ≤ B := by
      intro x hx
      refine ⟨⟨x, hNH hx⟩, ?_, rfl⟩
      change π ⟨x, hNH hx⟩ ∈ M
      have : ⟨x, hNH hx⟩ ∈ (QuotientGroup.mk' (N.subgroupOf H)).ker := by
        rw [QuotientGroup.ker_mk']; exact hx
      rw [show π ⟨x, hNH hx⟩ = 1 from this]
      exact M.one_mem
    have hB1 : N ⊔ Hs[i + 1]'hi' ≤ B := by
      refine sup_le hNB (fun x hx => ?_)
      have hx' : x ∈ radTerm Hs (i + 1) := by
        simpa only [radTerm, List.getD_eq_getElem _ _ hi'] using hx
      refine ⟨⟨x, hle (i + 1) hx'⟩, ?_, rfl⟩
      exact h1 ⟨⟨x, hle (i + 1) hx'⟩, hx', rfl⟩
    have hB2 : B ≤ N ⊔ Hs[i]'hi0 := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : π y ∈ ((radTerm Hs i).subgroupOf H).map π := h2 hy
      have hy'' : (y : Perm (Fin n)) ∈ N ⊔ Hs[i]'hi0 := by
        have := (rad_mem_map_iff (hle i) hNH y).mp hy'
        simpa only [radTerm, List.getD_eq_getElem _ _ hi0] using this
      exact hy''
    rcases (hs.2.2.2 i hi').2 hna' B hB1 hB2 hBn with hB | hB
    · left
      refine le_antisymm ?_ h1
      intro m hm
      obtain ⟨y, rfl⟩ := hsurj m
      have hyB : (y : Perm (Fin n)) ∈ B := ⟨y, hm, rfl⟩
      rw [hB] at hyB
      have hyB' : (y : Perm (Fin n)) ∈ N ⊔ radTerm Hs (i + 1) := by
        simpa only [radTerm, List.getD_eq_getElem _ _ hi'] using hyB
      exact (rad_mem_map_iff (hle (i + 1)) hNH y).mpr hyB'
    · right
      refine le_antisymm h2 ?_
      intro m hm
      obtain ⟨y, rfl⟩ := hsurj m
      have hy' : (y : Perm (Fin n)) ∈ N ⊔ Hs[i]'hi0 := by
        have := (rad_mem_map_iff (hle i) hNH y).mp hm
        simpa only [radTerm, List.getD_eq_getElem _ _ hi0] using this
      rw [← hB] at hy'
      obtain ⟨z, hz, hzy⟩ := hy'
      rw [Subtype.ext hzy] at hz
      exact hz

/-- **The radical preimage from an `IsNonabelianChiefChain`.** -/
theorem nonabelianChief_rad_mem_iff (hNH : N ≤ H) (hn : GI.Multicoset.Normalizes H N)
    {Hs : List (Subgroup (Perm (Fin n)))} (hs : IsNonabelianChiefChain H N Hs)
    (h : Perm (Fin n)) :
    h ∈ GI.Multicoset.radicalPreimage H N ↔ radCond H N Hs (Hs.length - 1) h := by
  have hN := GI.Multicoset.normal_of_normalizes hn
  have ht := nonabelianChief_chain hNH hs
  simp only [GI.Multicoset.radicalPreimage, hN, ↓reduceDIte, nonabelianRad_radical_eq ht]
  have hle := nonabelianChief_term_le hs
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun j hj hna => ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, nonabelianRad_mem_centInter] at hy
    have hna' := hna
    rw [← rad_comm_le_iff (hle j) (hle (j + 1)) hNH] at hna'
    exact (rad_cent_iff (hle j) (hle (j + 1)) hNH hn (nonabelianChief_term_normalized hs (j + 1))
      y).mp (hy j hj hna')
  · rintro ⟨hH, hc⟩
    refine ⟨⟨h, hH⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, nonabelianRad_mem_centInter]
    intro j hj hna
    rw [rad_comm_le_iff (hle j) (hle (j + 1)) hNH] at hna
    exact (rad_cent_iff (hle j) (hle (j + 1)) hNH hn (nonabelianChief_term_normalized hs (j + 1))
      ⟨h, hH⟩).mpr (hc j hj hna)

end PermChain

/-! ### 2. Subgroup cardinality and chain-length bounds -/

section ChainBounds

variable {n : ℕ}

/-- A strict subgroup has at most half the cardinality of the overgroup. -/
theorem two_mul_card_le_of_lt {K C : Subgroup (Perm (Fin n))} (h : K < C) :
    2 * Nat.card K ≤ Nat.card C := by
  have hmul := (K.subgroupOf C).card_mul_index
  have hcard : Nat.card (K.subgroupOf C) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  have hne : K.subgroupOf C ≠ ⊤ := by
    intro htop
    apply h.not_ge
    intro x hx
    have : (⟨x, hx⟩ : C) ∈ K.subgroupOf C := by rw [htop]; trivial
    exact this
  have hind : 2 ≤ (K.subgroupOf C).index := Subgroup.one_lt_index_of_ne_top hne
  calc 2 * Nat.card K = Nat.card K * 2 := Nat.mul_comm _ _
    _ ≤ Nat.card K * (K.subgroupOf C).index := Nat.mul_le_mul_left _ hind
    _ = Nat.card C := by rw [← hcard, hmul]

/-- If `Perm (Fin n)` has two subgroups with `¬ (C ≤ K)`, then `1 ≤ n`. -/
theorem one_le_of_not_le {K C : Subgroup (Perm (Fin n))} (h : ¬ C ≤ K) : 1 ≤ n := by
  by_contra hn0
  have hn : n = 0 := by omega
  subst hn
  apply h
  intro x _
  rw [Subsingleton.elim x 1]
  exact K.one_mem

/-- Every subgroup of `Perm (Fin n)` (`1 ≤ n`) has cardinality strictly less than `2 ^ (n ^ 2)`. -/
theorem subgroup_card_lt_two_pow_sq (hn : 1 ≤ n) (C : Subgroup (Perm (Fin n))) :
    Nat.card C < 2 ^ (n ^ 2) := by
  have h1 : Nat.card C ≤ n.factorial := by
    have := Subgroup.card_le_card_group C
    rwa [Nat.card_perm, Nat.card_fin] at this
  have h2 : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have h3 : n ^ n < (2 ^ n) ^ n := Nat.pow_lt_pow_left Nat.lt_two_pow_self (by omega)
  have h4 : (2 ^ n) ^ n = 2 ^ (n ^ 2) := by rw [← pow_mul, sq]
  omega

/-- No subgroup `J` can satisfy `2 ^ (n ^ 2) * Nat.card J ≤ Nat.card U` when `1 ≤ n`. -/
theorem not_two_pow_sq_mul_card_le (hn : 1 ≤ n) (J U : Subgroup (Perm (Fin n))) :
    ¬ 2 ^ (n ^ 2) * Nat.card J ≤ Nat.card U := by
  intro h
  have hpos : 1 ≤ Nat.card J := Nat.card_pos
  have hle : 2 ^ (n ^ 2) ≤ 2 ^ (n ^ 2) * Nat.card J := Nat.le_mul_of_pos_right _ hpos
  have hlt := subgroup_card_lt_two_pow_sq hn U
  omega

end ChainBounds

/-! ### 3. Lemma 2.4: Primitive quotients, `bFac` bounds, and orbit-block kernel steps -/

section Lemma24

variable {n m k r : ℕ} {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})}

/-- The socle `camProd e Finset.univ` is isomorphic to `Fin r → alternatingGroup (Fin m)`. -/
noncomputable def camX_socle_piEquiv (hk1 : 1 ≤ k) (hkm : k < m) :
    (Fin r → alternatingGroup (Fin m)) ≃* camProd e Finset.univ := by
  let φ : (Fin r → alternatingGroup (Fin m)) →* Perm (Fin n) :=
    { toFun := fun f => camHom e (fun i => (f i).1)
      map_one' := map_one (camHom e)
      map_mul' := fun f g => by rw [← map_mul]; rfl }
  have hinj : Function.Injective φ := by
    intro f g hfg
    have h := camX_camHom_injective hk1 hkm hfg
    funext i
    exact Subtype.ext (congrFun h i)
  have hrange : φ.range = camProd e Finset.univ := by
    ext x
    rw [MonoidHom.mem_range, camX_mem_prod]
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨fun i => (f i).1, fun i => ⟨fun _ => (f i).2, fun h => absurd (Finset.mem_univ i) h⟩, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨fun i => ⟨h i, (hh i).1 (Finset.mem_univ i)⟩, rfl⟩
  exact (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)

/-- For `5 ≤ m` and `1 ≤ k < m`, the nonabelian composition product `bFac` of the socle
`camProd e Finset.univ` equals its order. -/
theorem camX_bFac_socle (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hkm : k < m) :
    bFac (camProd e Finset.univ) = Nat.card (camProd e Finset.univ) := by
  have := GI.AlternatingSimple.isSimple_fin hm
  have hnc : ¬ ∀ x y : alternatingGroup (Fin m), x * y = y * x := by
    intro hcomm
    obtain ⟨f, t, hft⟩ := GI.AlternatingSimple.nonabelian_fin hm
    exact hft (hcomm f t)
  have hb_alt : bFac (alternatingGroup (Fin m)) = Nat.card (alternatingGroup (Fin m)) :=
    bFac_of_simple hnc
  have hpi := pi_compositionProducts (Fin r) (fun _ => alternatingGroup (Fin m))
  have hb_pi : bFac (Fin r → alternatingGroup (Fin m)) =
      Nat.card (Fin r → alternatingGroup (Fin m)) := by
    rw [bFac_eq hpi, Nat.card_pi]
    simp only [hb_alt]
  have e_soc := camX_socle_piEquiv (e := e) hk1 hkm
  rw [← bFac_congr e_soc, hb_pi, Nat.card_congr e_soc.toEquiv]

/-- In a Cameron-Maróti group `G` (`5 ≤ m`, `1 ≤ k`, `2 * k < m`), the index of the socle
`camProd e Finset.univ` in `G` is at most `n ^ (1 + Nat.log 2 n)`. -/
theorem camX_socle_index_le {G : Subgroup (Perm (Fin n))} (hM : MarotiStructure G e)
    (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m) :
    letI : ((camProd e Finset.univ).subgroupOf G).Normal :=
      rad_subgroupOf_normal (camX_socle_normal hM)
    Nat.card (G ⧸ (camProd e Finset.univ).subgroupOf G) ≤ n ^ (1 + Nat.log 2 n) := by
  have : ((camProd e Finset.univ).subgroupOf G).Normal :=
    rad_subgroupOf_normal (camX_socle_normal hM)
  set S := (camProd e Finset.univ).subgroupOf G
  have hkm : k < m := by omega
  have hle : camProd e Finset.univ ≤ G := camX_socle_le hM
  have hS_card : Nat.card S = (m.factorial / 2) ^ r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      camX_card_prod (by omega) hk1 hkm, Finset.card_univ, Fintype.card_fin]
  have hG_card : Nat.card G ≤ r.factorial * m.factorial ^ r := cam_card_le hM
  have hm_even : m.factorial = 2 * (m.factorial / 2) :=
    Nat.eq_mul_of_div_eq_right (Nat.dvd_factorial (by norm_num) (by omega)) rfl
  have hm_pow : m.factorial ^ r = 2 ^ r * (m.factorial / 2) ^ r := by
    conv_lhs => rw [hm_even]
    rw [mul_pow]
  have hmul : Nat.card (G ⧸ S) * (m.factorial / 2) ^ r ≤
      (2 ^ r * r.factorial) * (m.factorial / 2) ^ r := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup S
    rw [hS_card] at h1
    calc Nat.card (G ⧸ S) * (m.factorial / 2) ^ r = Nat.card G := h1.symm
      _ ≤ r.factorial * m.factorial ^ r := hG_card
      _ = (2 ^ r * r.factorial) * (m.factorial / 2) ^ r := by rw [hm_pow]; ring
  have hpos : 0 < (m.factorial / 2) ^ r := hS_card ▸ Nat.card_pos
  have hind : Nat.card (G ⧸ S) ≤ 2 ^ r * r.factorial := Nat.le_of_mul_le_mul_right hmul hpos
  have hch2 : 2 ≤ m.choose k := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h1 : 1 ≤ m'.choose k' := Nat.choose_pos (by omega)
    have h2 : 1 ≤ m'.choose (k' + 1) := Nat.choose_pos (by omega)
    rw [Nat.choose_succ_succ]
    exact Nat.add_le_add h1 h2
  have h2r : 2 ^ r ≤ n := by
    rw [cam_n_eq e]
    exact Nat.pow_le_pow_left hch2 r
  have hn1 : 1 ≤ n := Nat.one_le_two_pow.trans h2r
  have hrn : r ≤ n := r.lt_two_pow_self.le.trans h2r
  have hrlog : r ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) h2r
  have hfac : r.factorial ≤ n ^ r := (Nat.factorial_le_pow r).trans (Nat.pow_le_pow_left hrn r)
  calc Nat.card (G ⧸ S) ≤ 2 ^ r * r.factorial := hind
    _ ≤ n * n ^ r := Nat.mul_le_mul h2r hfac
    _ = n ^ (1 + r) := by rw [pow_add, pow_one]
    _ ≤ n ^ (1 + Nat.log 2 n) := Nat.pow_le_pow_right hn1 (by omega)

/-- Under `MarotiPrimitive`, every quotient `G ⧸ K` of a primitive group `G ≤ Perm (Fin d)` has
order bounded by `max (24!) (d ^ (1 + Nat.log 2 d)) * bFac (G ⧸ K)`. -/
theorem primitive_quotient_card_le_bFac (hMa : MarotiPrimitive) {d : ℕ}
    (G : Subgroup (Perm (Fin d))) (hprim : MulAction.IsPreprimitive G (Fin d))
    (K : Subgroup G) [K.Normal] :
    Nat.card (G ⧸ K) ≤ max (Nat.factorial 24) (d ^ (1 + Nat.log 2 d)) * bFac (G ⧸ K) := by
  have hb_pos : 1 ≤ bFac (G ⧸ K) := bFac_pos
  have hGK_le : Nat.card (G ⧸ K) ≤ Nat.card G :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective K)
  by_cases hd : 25 ≤ d
  · by_cases hcard : d ^ (1 + Nat.log 2 d) ≤ Nat.card G
    · obtain ⟨m, k, r, e, hM, hm, hk1, hk⟩ := cam_normal_form hMa hd hprim hcard
      have : ((camProd e Finset.univ).subgroupOf G).Normal :=
        rad_subgroupOf_normal (camX_socle_normal hM)
      set S := (camProd e Finset.univ).subgroupOf G
      have hS_ind : Nat.card (G ⧸ S) ≤ d ^ (1 + Nat.log 2 d) :=
        camX_socle_index_le hM hm hk1 hk
      by_cases hK : K = ⊥
      · subst hK
        have e_bot : G ⧸ (⊥ : Subgroup G) ≃* G := QuotientGroup.quotientBot
        have hS_le : camProd e Finset.univ ≤ G := camX_socle_le hM
        have hS_bFac : bFac S = Nat.card S := by
          rw [bFac_congr (Subgroup.subgroupOfEquivOfLe hS_le), camX_bFac_socle hm hk1 (by omega),
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_le).toEquiv]
        have hG_bFac : Nat.card S ≤ bFac G := by
          rw [← hS_bFac, bFac_mul S]
          exact Nat.le_mul_of_pos_right _ bFac_pos
        calc Nat.card (G ⧸ (⊥ : Subgroup G)) = Nat.card G := Nat.card_congr e_bot.toEquiv
          _ = Nat.card (G ⧸ S) * Nat.card S := Subgroup.card_eq_card_quotient_mul_card_subgroup S
          _ ≤ d ^ (1 + Nat.log 2 d) * bFac G := Nat.mul_le_mul hS_ind hG_bFac
          _ ≤ max (Nat.factorial 24) (d ^ (1 + Nat.log 2 d)) * bFac (G ⧸ (⊥ : Subgroup G)) := by
              rw [bFac_congr e_bot]
              exact Nat.mul_le_mul_right _ (le_max_right _ _)
      · have hK'_ne : K.map G.subtype ≠ ⊥ :=
          fun hbot => hK ((Subgroup.map_eq_bot_iff_of_injective _ G.subtype_injective).mp hbot)
        have hK'_le : K.map G.subtype ≤ G := Subgroup.map_subtype_le K
        have hK'_norm : ∀ x ∈ G, ∀ y ∈ K.map G.subtype, x * y * x⁻¹ ∈ K.map G.subtype := by
          rintro x hx _ ⟨k', hk', rfl⟩
          exact ⟨⟨x, hx⟩ * k' * ⟨x, hx⟩⁻¹,
            (inferInstance : K.Normal).conj_mem k' hk' ⟨x, hx⟩, rfl⟩
        have hsoc_le : camProd e Finset.univ ≤ K.map G.subtype :=
          camX_socle_le_every_normal hM hprim hd hm hk1 hk hK'_le hK'_ne hK'_norm
        have hSK : S ≤ K := by
          intro x hx
          obtain ⟨y, hy, hyx⟩ := hsoc_le hx
          rwa [Subtype.ext hyx] at hy
        have hq_le : Nat.card (G ⧸ K) ≤ Nat.card (G ⧸ S) :=
          Nat.card_le_card_of_surjective
            (QuotientGroup.map S K (MonoidHom.id G) hSK)
            (QuotientGroup.map_surjective_of_surjective S K (MonoidHom.id G)
              (QuotientGroup.mk'_surjective K) hSK)
        calc Nat.card (G ⧸ K) ≤ d ^ (1 + Nat.log 2 d) := hq_le.trans hS_ind
          _ ≤ max (Nat.factorial 24) (d ^ (1 + Nat.log 2 d)) := le_max_right _ _
          _ ≤ max (Nat.factorial 24) (d ^ (1 + Nat.log 2 d)) * bFac (G ⧸ K) :=
              Nat.le_mul_of_pos_right _ hb_pos
    · calc Nat.card (G ⧸ K) ≤ Nat.card G := hGK_le
        _ ≤ d ^ (1 + Nat.log 2 d) := by omega
        _ ≤ max (Nat.factorial 24) (d ^ (1 + Nat.log 2 d)) := le_max_right _ _
        _ ≤ max (Nat.factorial 24) (d ^ (1 + Nat.log 2 d)) * bFac (G ⧸ K) :=
            Nat.le_mul_of_pos_right _ hb_pos
  · have hG_fac : Nat.card G ≤ Nat.factorial 24 := by
      have h1 := Subgroup.card_le_card_group G
      rw [Nat.card_perm, Nat.card_fin] at h1
      exact h1.trans (Nat.factorial_le (by omega))
    calc Nat.card (G ⧸ K) ≤ Nat.factorial 24 := hGK_le.trans hG_fac
      _ ≤ max (Nat.factorial 24) (d ^ (1 + Nat.log 2 d)) := le_max_left _ _
      _ ≤ max (Nat.factorial 24) (d ^ (1 + Nat.log 2 d)) * bFac (G ⧸ K) :=
          Nat.le_mul_of_pos_right _ hb_pos

/-- Surjective homomorphism form of `primitive_quotient_card_le_bFac`. -/
theorem primitive_surjective_card_le_bFac (hMa : MarotiPrimitive) {d : ℕ}
    (G : Subgroup (Perm (Fin d))) (hprim : MulAction.IsPreprimitive G (Fin d))
    {Q : Type*} [Group Q] [Finite Q] (ψ : G →* Q) (hψ : Function.Surjective ψ) :
    Nat.card Q ≤ max (Nat.factorial 24) (d ^ (1 + Nat.log 2 d)) * bFac Q := by
  let e : G ⧸ ψ.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  rw [← Nat.card_congr e.toEquiv, ← bFac_congr e]
  exact primitive_quotient_card_le_bFac hMa G hprim ψ.ker

/-- Natural-number form of `gmp_degreeBound`: for `1 ≤ n` and transitive `N ⊴ H ≤ Perm (Fin n)`,
`bFac (H ⧸ N.subgroupOf H) ≤ n ^ (1 + Nat.log 2 n)`. -/
theorem bFac_quotient_le_pow_log (hn : 1 ≤ n) {H N : Subgroup (Perm (Fin n))}
    (hNH : N ≤ H) [(N.subgroupOf H).Normal] (htr : MulAction.IsPretransitive N (Fin n)) :
    bFac (H ⧸ N.subgroupOf H) ≤ n ^ (1 + Nat.log 2 n) := by
  have : MulAction.IsPretransitive (N.subgroupOf H) (Fin n) := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := htr.exists_smul_eq x y
    exact ⟨⟨⟨g.1, hNH g.2⟩, g.2⟩, hg⟩
  have hgmp := gmp_degreeBound n hn H (N.subgroupOf H)
  have hlt : n < 2 ^ (1 + Nat.log 2 n) := by
    rw [Nat.add_comm]
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  have hle : (n : ℝ) ≤ (2 : ℝ) ^ (1 + Nat.log 2 n) := by exact_mod_cast hlt.le
  have hlog : Real.logb 2 (n : ℝ) ≤ (1 + Nat.log 2 n : ℕ) := by
    have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (show 0 < n by omega)) hle
    simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using h1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrpow : (n : ℝ) ^ Real.logb 2 n ≤ ((n ^ (1 + Nat.log 2 n) : ℕ) : ℝ) := by
    calc (n : ℝ) ^ Real.logb 2 n ≤ (n : ℝ) ^ ((1 + Nat.log 2 n : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 hlog
      _ = ((n ^ (1 + Nat.log 2 n) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
  exact_mod_cast hgmp.trans hrpow

/-- Any subquotient `M ⧸ M'` of `H ⧸ N` (`N ≤ M'`, `M ≤ H`) has `bFac` at most `bFac (H ⧸ N)`. -/
theorem bFac_subquotient_le {H N M M' : Subgroup (Perm (Fin n))}
    (hNM' : N ≤ M') (hMH : M ≤ H)
    [(N.subgroupOf H).Normal] [(M'.subgroupOf M).Normal] :
    bFac (M ⧸ M'.subgroupOf M) ≤ bFac (H ⧸ N.subgroupOf H) := by
  let f : M →* H ⧸ N.subgroupOf H :=
    (QuotientGroup.mk' (N.subgroupOf H)).comp (Subgroup.inclusion hMH)
  have hker : f.ker = N.subgroupOf M := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have : (N.subgroupOf M).Normal := hker ▸ f.normal_ker
  have h1 : bFac (M ⧸ M'.subgroupOf M) ≤ bFac (M ⧸ N.subgroupOf M) :=
    gmp_bFac_quotient_antitone (N.subgroupOf M) (M'.subgroupOf M) (Subgroup.subgroupOf_mono M hNM')
  have hmap_ker : (N.subgroupOf M).map (MulEquiv.refl M).toMonoidHom = f.ker := by
    ext x
    simp [← hker]
  have e_ker : M ⧸ N.subgroupOf M ≃* f.range :=
    (QuotientGroup.congr (N.subgroupOf M) f.ker (MulEquiv.refl M) hmap_ker).trans
      (QuotientGroup.quotientKerEquivRange f)
  have h2 : bFac (M ⧸ N.subgroupOf M) ≤ bFac (H ⧸ N.subgroupOf H) := by
    rw [bFac_congr e_ker]
    exact gmp_bFac_subgroup_le f.range
  exact h1.trans h2

/-- The normalizer of a subgroup `M` in `Perm (Fin n)`. -/
def normSub (M : Subgroup (Perm (Fin n))) : Subgroup (Perm (Fin n)) where
  carrier := {g | ∀ x, x ∈ M ↔ g * x * g⁻¹ ∈ M}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb x
    have h1 : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    rw [h1, ← ha (b * x * b⁻¹), ← hb x]
  inv_mem' := by
    intro a ha x
    have h := ha (a⁻¹ * x * a)
    simpa [mul_assoc] using h.symm

theorem le_normSub_of_conj {G M : Subgroup (Perm (Fin n))}
    (h : ∀ g ∈ G, ∀ x ∈ M, g * x * g⁻¹ ∈ M) : G ≤ normSub M := by
  intro g hg x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (G.inv_mem hg) (g * x * g⁻¹) hx
  simpa [mul_assoc] using this

theorem self_le_normSub (M : Subgroup (Perm (Fin n))) : M ≤ normSub M :=
  le_normSub_of_conj fun _ hg _ hx => M.mul_mem (M.mul_mem hg hx) (M.inv_mem hg)

/-- If `J' ≤ J ≤ H` is normalized by `J` and `N ≤ H` is normalized by `H`, then `J' ⊔ N` is
normalized by `J ⊔ N`. -/
theorem sup_normalized_of_normalized {H N J J' : Subgroup (Perm (Fin n))}
    (hJH : J ≤ H) (hnN : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (hnJ' : ∀ g ∈ J, ∀ x ∈ J', g * x * g⁻¹ ∈ J') :
    ∀ g ∈ J ⊔ N, ∀ x ∈ J' ⊔ N, g * x * g⁻¹ ∈ J' ⊔ N := by
  have hJ_norm : J ≤ normSub (J' ⊔ N) := by
    refine le_normSub_of_conj fun g hg x hx => ?_
    have : J' ⊔ N ≤ (J' ⊔ N).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_sup_left (hnJ' g hg y hy)
      · exact Subgroup.mem_sup_right (hnN g (hJH hg) y hy)
    exact this hx
  have hN_norm : N ≤ normSub (J' ⊔ N) := le_sup_right.trans (self_le_normSub (J' ⊔ N))
  have hJN_norm : J ⊔ N ≤ normSub (J' ⊔ N) := sup_le hJ_norm hN_norm
  intro g hg x hx
  exact (hJN_norm hg x).mp hx

/-- **Lemma 2.4 (Index bound for an orbit-block kernel step modulo `N`).**
Let `N ≤ H ≤ Perm (Fin n)` (`1 ≤ n`) with `N` transitive and normalized by `H`. Let `J' ≤ J ≤ H`
with `J'` normalized by `J`, and suppose there is a homomorphism `ρ : J →* Perm (Fin d)` (`d ≤ n`)
whose range `ρ.range` is primitive on `Fin d` and whose kernel is contained in `J'.subgroupOf J`.
Then `M' := J' ⊔ N` is normalized by `M := J ⊔ N` and
`((J' ⊔ N).subgroupOf (J ⊔ N)).index ≤ max (24!) (n ^ (1 + Nat.log 2 n)) * n ^ (1 + Nat.log 2 n)`. -/
theorem orbitBlockStep_index_le (hMa : MarotiPrimitive) (hn : 1 ≤ n)
    {H N J J' : Subgroup (Perm (Fin n))}
    (hNH : N ≤ H) (hJH : J ≤ H)
    (hnN : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (hnJ' : ∀ g ∈ J, ∀ x ∈ J', g * x * g⁻¹ ∈ J')
    (htr : MulAction.IsPretransitive N (Fin n))
    {d : ℕ} (hd : d ≤ n) (ρ : J →* Perm (Fin d))
    (hprim : MulAction.IsPreprimitive ρ.range (Fin d))
    (hker : ρ.ker ≤ J'.subgroupOf J) :
    ((J' ⊔ N).subgroupOf (J ⊔ N)).index ≤
      max (Nat.factorial 24) (n ^ (1 + Nat.log 2 n)) * n ^ (1 + Nat.log 2 n) := by
  set M := J ⊔ N
  set M' := J' ⊔ N
  have hNM' : N ≤ M' := le_sup_right
  have hMH : M ≤ H := sup_le hJH hNH
  have : (N.subgroupOf H).Normal := rad_subgroupOf_normal hnN
  have : (M'.subgroupOf M).Normal :=
    rad_subgroupOf_normal (sup_normalized_of_normalized hJH hnN hnJ')
  have : ρ.ker.Normal := ρ.normal_ker
  let φ : J →* M ⧸ M'.subgroupOf M :=
    (QuotientGroup.mk' (M'.subgroupOf M)).comp (Subgroup.inclusion (le_sup_left : J ≤ J ⊔ N))
  have hφ_surj : Function.Surjective φ := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (M'.subgroupOf M) q
    have hJM' : J.subgroupOf M ⊔ M'.subgroupOf M = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (x : Perm (Fin n)) ∈ J ⊔ N := x.2
      have hsub : J ⊔ N ≤ (J.subgroupOf M ⊔ M'.subgroupOf M).map M.subtype := by
        refine sup_le (fun y hy => ?_) (fun y hy => ?_)
        · exact ⟨⟨y, Subgroup.mem_sup_left hy⟩, Subgroup.mem_sup_left hy, rfl⟩
        · exact ⟨⟨y, Subgroup.mem_sup_right hy⟩,
            Subgroup.mem_sup_right (Subgroup.mem_sup_right hy), rfl⟩
      obtain ⟨z, hz, hzx⟩ := hsub hx
      rwa [Subtype.ext hzx] at hz
    have hm_top : m ∈ J.subgroupOf M ⊔ M'.subgroupOf M := by rw [hJM']; trivial
    have hm_map : QuotientGroup.mk' (M'.subgroupOf M) m ∈
        (J.subgroupOf M ⊔ M'.subgroupOf M).map (QuotientGroup.mk' (M'.subgroupOf M)) :=
      ⟨m, hm_top, rfl⟩
    rw [Subgroup.map_sup] at hm_map
    have hM'_bot : (M'.subgroupOf M).map (QuotientGroup.mk' (M'.subgroupOf M)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hM'_bot, sup_bot_eq] at hm_map
    obtain ⟨j, hj, hjm⟩ := hm_map
    exact ⟨⟨j.1, hj⟩, hjm⟩
  have hker_le : ρ.ker ≤ φ.ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    intro j hj
    exact Subgroup.mem_sup_left (hker hj)
  let lift : J ⧸ ρ.ker →* M ⧸ M'.subgroupOf M := QuotientGroup.lift ρ.ker φ hker_le
  have hlift_surj : Function.Surjective lift := by
    intro q
    obtain ⟨j, rfl⟩ := hφ_surj q
    exact ⟨QuotientGroup.mk' ρ.ker j, rfl⟩
  let e_range : ρ.range ≃* J ⧸ ρ.ker := (QuotientGroup.quotientKerEquivRange ρ).symm
  let ψ : ρ.range →* M ⧸ M'.subgroupOf M := lift.comp e_range.toMonoidHom
  have hψ_surj : Function.Surjective ψ := hlift_surj.comp e_range.surjective
  have hcard := primitive_surjective_card_le_bFac hMa ρ.range hprim ψ hψ_surj
  have hb_sub := bFac_subquotient_le (M' := M') hNM' hMH
  have hb_top := bFac_quotient_le_pow_log hn hNH htr
  have hd_pow : d ^ (1 + Nat.log 2 d) ≤ n ^ (1 + Nat.log 2 n) :=
    (Nat.pow_le_pow_left hd _).trans
      (Nat.pow_le_pow_right hn (Nat.add_le_add_left (Nat.log_mono_right hd) 1))
  have hmax : max (Nat.factorial 24) (d ^ (1 + Nat.log 2 d)) ≤
      max (Nat.factorial 24) (n ^ (1 + Nat.log 2 n)) :=
    max_le_max le_rfl hd_pow
  rw [Subgroup.index_eq_card]
  exact hcard.trans (Nat.mul_le_mul hmax (hb_sub.trans hb_top))

/-- Given a homomorphism `res : J →* Perm (Fin k)` (`k ≤ n`) whose range is transitive on `Fin k`
and a minimal block system `lab : Fin k → ℕ` of `res.range`, there exist `d ≤ n` and a
homomorphism `ρ : J →* Perm (Fin d)` with `ρ.range` primitive on `Fin d`,
`∀ g : J, g ∈ ρ.ker ↔ ∀ i : Fin k, lab (res g i) = lab i`, and `∃ g : J, g ∉ ρ.ker`. -/
theorem minBlocks_primitive_hom {J : Subgroup (Perm (Fin n))} {k : ℕ} (hkn : k ≤ n)
    (res : J →* Perm (Fin k))
    (htr : ∀ i j : Fin k, ∃ h ∈ res.range, h i = j)
    {lab : Fin k → ℕ} (hmin : IsMinimalBlocks res.range lab) :
    ∃ (d : ℕ) (_ : d ≤ n) (ρ : J →* Perm (Fin d)),
      MulAction.IsPreprimitive ρ.range (Fin d) ∧
      (∀ g : J, g ∈ ρ.ker ↔ ∀ i : Fin k, lab (res g i) = lab i) ∧
      (∃ g : J, g ∉ ρ.ker) := by
  classical
  have hinv : InvariantLabeling res.range lab := hmin.1
  let ψ := scosHom hinv
  let d := Fintype.card (ScosCls lab)
  have hd : d ≤ n := (scosCls_card_le lab).trans hkn
  let e : ScosCls lab ≃ Fin d := Fintype.equivFin (ScosCls lab)
  let E : Perm (ScosCls lab) ≃* Perm (Fin d) := e.permCongrHom
  let ρ : J →* Perm (Fin d) := E.toMonoidHom.comp (ψ.comp res.rangeRestrict)
  have hrange : ρ.range = ψ.range.map E.toMonoidHom := by
    ext x
    simp only [ρ, MonoidHom.mem_range, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.mem_map]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨ψ (res.rangeRestrict g), ⟨res.rangeRestrict g, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨h, rfl⟩, rfl⟩
      obtain ⟨g, hg⟩ := res.rangeRestrict_surjective h
      exact ⟨g, by rw [hg]⟩
  let φ : ψ.range →* ρ.range :=
    MonoidHom.mk' (fun x => ⟨E x.1, hrange ▸ Subgroup.mem_map_of_mem _ x.2⟩)
      fun a b => Subtype.ext (map_mul E a.1 b.1)
  have hφ : Function.Surjective φ := by
    intro y
    have hy : y.1 ∈ ψ.range.map E.toMonoidHom := hrange ▸ y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hpre : MulAction.IsPreprimitive ψ.range (ScosCls lab) :=
    scos_isPreprimitive hinv htr hmin
  let f : ScosCls lab →ₑ[φ] Fin d :=
    { toFun := e
      map_smul' := fun r q => by
        change e ((r : Perm (ScosCls lab)) q) = (E r.1) (e q)
        simp [E, Equiv.permCongrHom, Equiv.permCongr_apply] }
  have hprim : MulAction.IsPreprimitive ρ.range (Fin d) :=
    MulAction.IsPreprimitive.of_surjective (f := f) e.surjective
  have hker : ∀ g : J, g ∈ ρ.ker ↔ ∀ i : Fin k, lab (res g i) = lab i := by
    intro g
    rw [MonoidHom.mem_ker]
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff E E.injective]
    constructor
    · intro hg i
      have h1 := congrArg (fun σ : Perm (ScosCls lab) => σ (scosCls lab i)) hg
      simp only [ψ, scosHom_apply, Perm.one_apply] at h1
      exact (scosCls_eq_iff lab).mp h1
    · intro hg
      ext q : 1
      rw [← scosCls_rep lab q, scosHom_apply, Perm.one_apply, scosCls_eq_iff]
      exact hg (scosRep lab q)
  have hne : ∃ g : J, g ∉ ρ.ker := by
    obtain ⟨i, j, hij⟩ := hmin.2.1
    obtain ⟨h, hh, hhi⟩ := htr i j
    obtain ⟨g, hg⟩ := res.rangeRestrict_surjective ⟨h, hh⟩
    refine ⟨g, fun hgk => hij ?_⟩
    have hgi := (hker g).mp hgk i
    have hres : res g = h := congrArg Subtype.val hg
    rw [hres, hhi] at hgi
    exact hgi.symm
  exact ⟨d, hd, ρ, hprim, hker, hne⟩

end Lemma24

/-! ### 4. Lemma 2.5: Greedy coset maximalization (`greedyMaxStep` and `greedyMaxFold`) -/

section Lemma25

variable {n : ℕ}

open Classical in
/-- One step of greedy coset maximalization: enlarge `V` by the normal closure under `A` of
`V ⊔ Subgroup.closure {r}` unless that normal closure contains `U`. -/
noncomputable def greedyMaxStep (A U V : Subgroup (Perm (Fin n))) (r : Perm (Fin n)) :
    Subgroup (Perm (Fin n)) :=
  let V' := camNormClosure A (V ⊔ Subgroup.closure {r})
  if U ≤ V' then V else V'

/-- Folding `greedyMaxStep A U` over a list `rs` of coset representatives starting from `W`. -/
noncomputable def greedyMaxFold (A U W : Subgroup (Perm (Fin n)))
    (rs : List (Perm (Fin n))) : Subgroup (Perm (Fin n)) :=
  rs.foldl (greedyMaxStep A U) W

theorem le_greedyMaxStep (A U V : Subgroup (Perm (Fin n))) (r : Perm (Fin n)) :
    V ≤ greedyMaxStep A U V r := by
  classical
  dsimp [greedyMaxStep]
  split_ifs
  · exact le_rfl
  · exact le_sup_left.trans (le_camNormClosure A _)

theorem greedyMaxStep_le {A U V : Subgroup (Perm (Fin n))} {r : Perm (Fin n)}
    (hVU : V ≤ U) (hrU : r ∈ U) (hnU : ∀ g ∈ A, ∀ x ∈ U, g * x * g⁻¹ ∈ U) :
    greedyMaxStep A U V r ≤ U := by
  classical
  dsimp [greedyMaxStep]
  split_ifs
  · exact hVU
  · refine camNormClosure_minimal (sup_le hVU ?_) hnU
    rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact hrU

theorem greedyMaxStep_not_le {A U V : Subgroup (Perm (Fin n))} (r : Perm (Fin n))
    (hnot : ¬ U ≤ V) : ¬ U ≤ greedyMaxStep A U V r := by
  classical
  dsimp [greedyMaxStep]
  split_ifs with h
  · exact hnot
  · exact h

theorem greedyMaxStep_normalized {A : Subgroup (Perm (Fin n))} (U : Subgroup (Perm (Fin n)))
    {V : Subgroup (Perm (Fin n))} (r : Perm (Fin n))
    (hnV : ∀ g ∈ A, ∀ x ∈ V, g * x * g⁻¹ ∈ V) :
    ∀ g ∈ A, ∀ x ∈ greedyMaxStep A U V r, g * x * g⁻¹ ∈ greedyMaxStep A U V r := by
  classical
  dsimp [greedyMaxStep]
  split_ifs
  · exact hnV
  · exact camNormClosure_normal A _

theorem greedyMaxStep_mem_or_le (A U V : Subgroup (Perm (Fin n))) (r : Perm (Fin n)) :
    r ∈ greedyMaxStep A U V r ∨ U ≤ camNormClosure A (V ⊔ Subgroup.closure {r}) := by
  classical
  dsimp [greedyMaxStep]
  split_ifs with h
  · exact Or.inr h
  · refine Or.inl (le_camNormClosure A _ (Subgroup.mem_sup_right (Subgroup.subset_closure rfl)))

theorem camNormClosure_mono_right (A : Subgroup (Perm (Fin n)))
    {K₁ K₂ : Subgroup (Perm (Fin n))} (h : K₁ ≤ K₂) :
    camNormClosure A K₁ ≤ camNormClosure A K₂ :=
  camNormClosure_minimal (h.trans (le_camNormClosure A K₂)) (camNormClosure_normal A K₂)

theorem greedyMaxFold_props {A U W : Subgroup (Perm (Fin n))} {rs : List (Perm (Fin n))}
    (hWU : W ≤ U) (hnot : ¬ U ≤ W) (hnU : ∀ g ∈ A, ∀ x ∈ U, g * x * g⁻¹ ∈ U)
    (hnW : ∀ g ∈ A, ∀ x ∈ W, g * x * g⁻¹ ∈ W) (hrs : ∀ r ∈ rs, r ∈ U) :
    W ≤ greedyMaxFold A U W rs ∧
    greedyMaxFold A U W rs ≤ U ∧
    ¬ U ≤ greedyMaxFold A U W rs ∧
    (∀ g ∈ A, ∀ x ∈ greedyMaxFold A U W rs, g * x * g⁻¹ ∈ greedyMaxFold A U W rs) ∧
    (∀ r ∈ rs, r ∈ greedyMaxFold A U W rs ∨
      U ≤ camNormClosure A (greedyMaxFold A U W rs ⊔ Subgroup.closure {r})) := by
  induction rs generalizing W with
  | nil =>
    exact ⟨le_rfl, hWU, hnot, hnW, fun _ h => absurd h List.not_mem_nil⟩
  | cons r rs ih =>
    have hrU : r ∈ U := hrs r List.mem_cons_self
    have hrs' : ∀ x ∈ rs, x ∈ U := fun x hx => hrs x (List.mem_cons_of_mem r hx)
    set W₁ := greedyMaxStep A U W r
    have hWW₁ : W ≤ W₁ := le_greedyMaxStep A U W r
    have hW₁U : W₁ ≤ U := greedyMaxStep_le hWU hrU hnU
    have hnot₁ : ¬ U ≤ W₁ := greedyMaxStep_not_le r hnot
    have hnW₁ := greedyMaxStep_normalized U r hnW
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih hW₁U hnot₁ hnW₁ hrs'
    refine ⟨hWW₁.trans h1, h2, h3, h4, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases greedyMaxStep_mem_or_le A U W x with hxW₁ | hU_le
      · exact Or.inl (h1 hxW₁)
      · refine Or.inr (hU_le.trans (camNormClosure_mono_right A ?_))
        exact sup_le_sup_right (hWW₁.trans h1) _
    · exact h5 x hx'

/-- **Lemma 2.5 (`greedyMaxFold_maximal`).**
If `W < U ≤ A` are normalized by `A` and `rs` is a right-coset transversal of `W` in `U`, then
`V := greedyMaxFold A U W rs` is a maximal proper `A`-normalized subgroup of `U` containing `W`. -/
theorem greedyMaxFold_maximal {A U W : Subgroup (Perm (Fin n))} {rs : List (Perm (Fin n))}
    (hWU : W ≤ U) (hnot : ¬ U ≤ W) (hnU : ∀ g ∈ A, ∀ x ∈ U, g * x * g⁻¹ ∈ U)
    (hnW : ∀ g ∈ A, ∀ x ∈ W, g * x * g⁻¹ ∈ W) (hrs : ∀ r ∈ rs, r ∈ U)
    (hcov : ∀ u ∈ U, ∃ r ∈ rs, ∃ w ∈ W, u = w * r) :
    let V := greedyMaxFold A U W rs
    W ≤ V ∧ V ≤ U ∧ ¬ U ≤ V ∧ (∀ g ∈ A, ∀ x ∈ V, g * x * g⁻¹ ∈ V) ∧
    (∀ K : Subgroup (Perm (Fin n)), V ≤ K → K ≤ U →
      (∀ g ∈ A, ∀ x ∈ K, g * x * g⁻¹ ∈ K) → K = V ∨ K = U) := by
  obtain ⟨hWV, hVU, hnotV, hnV, hmem⟩ := greedyMaxFold_props hWU hnot hnU hnW hrs
  refine ⟨hWV, hVU, hnotV, hnV, fun K hVK hKU hnK => ?_⟩
  by_cases hKV : K ≤ greedyMaxFold A U W rs
  · exact Or.inl (le_antisymm hKV hVK)
  · right
    obtain ⟨u, huK, huV⟩ : ∃ u ∈ K, u ∉ greedyMaxFold A U W rs := by
      by_contra hall
      push Not at hall
      exact hKV hall
    obtain ⟨r, hr_mem, w, hwW, rfl⟩ := hcov u (hKU huK)
    have hwV : w ∈ greedyMaxFold A U W rs := hWV hwW
    have hr_not_V : r ∉ greedyMaxFold A U W rs :=
      fun hrV => huV ((greedyMaxFold A U W rs).mul_mem hwV hrV)
    have hrK : r ∈ K := by
      have : r = w⁻¹ * (w * r) := by group
      rw [this]
      exact K.mul_mem (K.inv_mem (hVK hwV)) huK
    rcases hmem r hr_mem with hrV | hU_le
    · exact absurd hrV hr_not_V
    · refine le_antisymm hKU (hU_le.trans (camNormClosure_minimal (sup_le hVK ?_) hnK))
      rw [Subgroup.closure_le, Set.singleton_subset_iff]
      exact hrK

end Lemma25

/-! ### 5. Lemma 2.6: Simple quotient, conjugate-intersection loop, and chief step -/

section Lemma26

variable {n : ℕ}

/-- **Lemma 2.6(2) (`simple_and_noncomm_of_maximal`).**
If `N ≤ M < U` with `U ≤ ⁅U, U⁆ ⊔ N` and `M` is a maximal proper `U`-normalized subgroup of `U`,
then `U ⧸ M.subgroupOf U` is a nonabelian simple group. -/
theorem simple_and_noncomm_of_maximal {U N M : Subgroup (Perm (Fin n))}
    (hNM : N ≤ M) (hMU : M ≤ U) (hnot : ¬ U ≤ M) (hperf : U ≤ ⁅U, U⁆ ⊔ N)
    (hnM : ∀ g ∈ U, ∀ x ∈ M, g * x * g⁻¹ ∈ M)
    (hmax : ∀ K : Subgroup (Perm (Fin n)), M ≤ K → K ≤ U →
      (∀ g ∈ U, ∀ x ∈ K, g * x * g⁻¹ ∈ K) → K = M ∨ K = U) :
    letI : (M.subgroupOf U).Normal := rad_subgroupOf_normal hnM
    IsSimpleGroup (U ⧸ M.subgroupOf U) ∧
    ¬ (∀ x y : U ⧸ M.subgroupOf U, x * y = y * x) := by
  have : (M.subgroupOf U).Normal := rad_subgroupOf_normal hnM
  set π := QuotientGroup.mk' (M.subgroupOf U)
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hnt : Nontrivial (U ⧸ M.subgroupOf U) := by
    obtain ⟨u, huU, huM⟩ : ∃ u ∈ U, u ∉ M := by
      by_contra hall; push Not at hall; exact hnot hall
    refine ⟨⟨π ⟨u, huU⟩, 1, ?_⟩⟩
    intro h1
    have h2 : ⟨u, huU⟩ ∈ π.ker := h1
    rw [QuotientGroup.ker_mk'] at h2
    exact huM h2
  have hsimple : IsSimpleGroup (U ⧸ M.subgroupOf U) := by
    refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun Q hQ => ?_ }
    set K := (Q.comap π).map U.subtype
    have hMK : M ≤ K := by
      intro x hx
      refine ⟨⟨x, hMU hx⟩, ?_, rfl⟩
      change π ⟨x, hMU hx⟩ ∈ Q
      have : π ⟨x, hMU hx⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hx
      rw [this]
      exact Q.one_mem
    have hKU : K ≤ U := Subgroup.map_subtype_le _
    have hnK : ∀ g ∈ U, ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
      rintro g hg _ ⟨x, hx, rfl⟩
      have : (Q.comap π).Normal := hQ.comap π
      exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, (inferInstance : (Q.comap π).Normal).conj_mem x hx ⟨g, hg⟩, rfl⟩
    rcases hmax K hMK hKU hnK with hKM | hKU_eq
    · left
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨u, rfl⟩ := hsurj q
      have huK : (u : Perm (Fin n)) ∈ K := ⟨u, hq, rfl⟩
      rw [hKM] at huK
      exact (QuotientGroup.eq_one_iff u).mpr huK
    · right
      rw [eq_top_iff]
      intro q _
      obtain ⟨u, rfl⟩ := hsurj q
      have huK : (u : Perm (Fin n)) ∈ K := by
        rw [hKU_eq]
        exact u.2
      obtain ⟨z, hz, hzu⟩ := huK
      rwa [Subtype.ext hzu] at hz
  have hnc : ¬ (∀ x y : U ⧸ M.subgroupOf U, x * y = y * x) := by
    intro hcomm
    apply hnot
    refine hperf.trans (sup_le ?_ hNM)
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 : π ⟨a, ha⟩ * π ⟨b, hb⟩ = π ⟨b, hb⟩ * π ⟨a, ha⟩ := hcomm _ _
    let c : U := ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹
    have h2 : π c = 1 := by
      simp only [c, map_mul, map_inv, h1]
      group
    have hcM : (c : Perm (Fin n)) ∈ M := (QuotientGroup.eq_one_iff c).mp h2
    simpa [c, commutatorElement_def] using hcM
  exact ⟨hsimple, hnc⟩

/-- Key step for `bFac` of an intersection: if `W ≤ U` and `M ≤ U` are normalized by `U`,
`bFac (U ⧸ W.subgroupOf U) = Nat.card (U ⧸ W.subgroupOf U)`, and `U ⧸ M.subgroupOf U` is
nonabelian simple, then `bFac (U ⧸ (M ⊓ W).subgroupOf U) = Nat.card (U ⧸ (M ⊓ W).subgroupOf U)`. -/
theorem bFac_inf_eq_card_of_simple {U M W : Subgroup (Perm (Fin n))}
    (hnM : ∀ g ∈ U, ∀ x ∈ M, g * x * g⁻¹ ∈ M)
    (hnW : ∀ g ∈ U, ∀ x ∈ W, g * x * g⁻¹ ∈ W)
    (hsimple :
      letI : (M.subgroupOf U).Normal := rad_subgroupOf_normal hnM
      IsSimpleGroup (U ⧸ M.subgroupOf U))
    (hnc :
      letI : (M.subgroupOf U).Normal := rad_subgroupOf_normal hnM
      ¬ (∀ x y : U ⧸ M.subgroupOf U, x * y = y * x))
    (hbW :
      letI : (W.subgroupOf U).Normal := rad_subgroupOf_normal hnW
      bFac (U ⧸ W.subgroupOf U) = Nat.card (U ⧸ W.subgroupOf U)) :
    letI : ((M ⊓ W).subgroupOf U).Normal :=
      rad_subgroupOf_normal (fun g hg x hx => ⟨hnM g hg x hx.1, hnW g hg x hx.2⟩)
    bFac (U ⧸ (M ⊓ W).subgroupOf U) = Nat.card (U ⧸ (M ⊓ W).subgroupOf U) := by
  have : (M.subgroupOf U).Normal := rad_subgroupOf_normal hnM
  have : (W.subgroupOf U).Normal := rad_subgroupOf_normal hnW
  have : ((M ⊓ W).subgroupOf U).Normal :=
    rad_subgroupOf_normal (fun g hg x hx => ⟨hnM g hg x hx.1, hnW g hg x hx.2⟩)
  set M' := M.subgroupOf U
  set W' := W.subgroupOf U
  set MW := (M ⊓ W).subgroupOf U
  have hMW_le : MW ≤ W' := fun x hx => hx.2
  have hb_chain := gmp_bFac_quotient_chain MW W' hMW_le
  have hcard_chain : Nat.card (U ⧸ MW) = Nat.card (W' ⧸ MW.subgroupOf W') * Nat.card (U ⧸ W') := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup W'
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup MW
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (MW.subgroupOf W')
    have h4 : Nat.card (MW.subgroupOf W') = Nat.card MW :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMW_le).toEquiv
    rw [h4] at h3
    have hmul : Nat.card (U ⧸ MW) * Nat.card MW =
        (Nat.card (W' ⧸ MW.subgroupOf W') * Nat.card (U ⧸ W')) * Nat.card MW := by
      calc Nat.card (U ⧸ MW) * Nat.card MW = Nat.card U := h2.symm
        _ = Nat.card (U ⧸ W') * Nat.card W' := h1
        _ = Nat.card (U ⧸ W') * (Nat.card (W' ⧸ MW.subgroupOf W') * Nat.card MW) := by rw [h3]
        _ = (Nat.card (W' ⧸ MW.subgroupOf W') * Nat.card (U ⧸ W')) * Nat.card MW := by ring
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  rw [hb_chain, hcard_chain, hbW]
  congr 1
  let f : W' →* U ⧸ M' := (QuotientGroup.mk' M').comp W'.subtype
  have hker : f.ker = MW.subgroupOf W' := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    ext x
    exact ⟨fun hx => ⟨hx, x.2⟩, fun hx => hx.1⟩
  have hmap_ker : (MW.subgroupOf W').map (MulEquiv.refl W').toMonoidHom = f.ker := by
    ext x
    simp [← hker]
  have e_f : W' ⧸ MW.subgroupOf W' ≃* f.range :=
    (QuotientGroup.congr (MW.subgroupOf W') f.ker (MulEquiv.refl W') hmap_ker).trans
      (QuotientGroup.quotientKerEquivRange f)
  rw [bFac_congr e_f, Nat.card_congr e_f.toEquiv]
  have hrange_eq : f.range = W'.map (QuotientGroup.mk' M') := by
    ext q
    simp [f]
  have : f.range.Normal := by
    rw [hrange_eq]
    exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective M')
  have := hsimple
  rcases hsimple.eq_bot_or_eq_top_of_normal f.range with hbot | htop
  · have : Subsingleton f.range := hbot ▸ inferInstance
    rw [bFac_of_solvable, Nat.card_unique]
  · have e_top : f.range ≃* U ⧸ M' :=
      (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    rw [bFac_congr e_top, Nat.card_congr e_top.toEquiv, bFac_of_simple hnc]

/-- `M` is a `U`-normalized subgroup of `U` containing `N` such that `U ⧸ M.subgroupOf U` is
nonabelian simple. -/
def IsNonabelianSimpleNormal (U N M : Subgroup (Perm (Fin n))) : Prop :=
  N ≤ M ∧ M ≤ U ∧ (∀ g ∈ U, ∀ x ∈ M, g * x * g⁻¹ ∈ M) ∧
    ∃ (_ : (M.subgroupOf U).Normal),
      IsSimpleGroup (U ⧸ M.subgroupOf U) ∧ ¬ (∀ x y : U ⧸ M.subgroupOf U, x * y = y * x)

/-- `W` is a nonempty intersection of `IsNonabelianSimpleNormal U N` subgroups. -/
def IsSimpleInter (U N W : Subgroup (Perm (Fin n))) : Prop :=
  ∃ Ms : List (Subgroup (Perm (Fin n))),
    Ms ≠ [] ∧ W = Ms.foldr (· ⊓ ·) U ∧ ∀ M ∈ Ms, IsNonabelianSimpleNormal U N M

theorem isSimpleInter_singleton {U N M : Subgroup (Perm (Fin n))}
    (h : IsNonabelianSimpleNormal U N M) : IsSimpleInter U N M :=
  ⟨[M], List.cons_ne_nil _ _, (inf_eq_left.mpr h.2.1).symm,
    fun _ hM => (List.mem_singleton.mp hM) ▸ h⟩

private theorem foldr_inf_props {U N : Subgroup (Perm (Fin n))}
    (Ms : List (Subgroup (Perm (Fin n))))
    (hNU : N ≤ U) (hMs : ∀ M ∈ Ms, IsNonabelianSimpleNormal U N M) :
    let W := Ms.foldr (· ⊓ ·) U
    N ≤ W ∧ W ≤ U ∧ (∀ g ∈ U, ∀ x ∈ W, g * x * g⁻¹ ∈ W) ∧
    (∀ (_ : (W.subgroupOf U).Normal),
      bFac (U ⧸ W.subgroupOf U) = Nat.card (U ⧸ W.subgroupOf U)) := by
  induction Ms with
  | nil =>
    refine ⟨hNU, le_rfl, fun g hg x hx => U.mul_mem (U.mul_mem hg hx) (U.inv_mem hg), fun hnorm => ?_⟩
    let W₀ : Subgroup U := (List.foldr (· ⊓ ·) U []).subgroupOf U
    have hmap_top : W₀.map (MulEquiv.refl U).toMonoidHom = (⊤ : Subgroup U) := by
      ext x
      exact ⟨fun _ => trivial, fun _ => ⟨x, x.2, rfl⟩⟩
    have e : U ⧸ W₀ ≃* U ⧸ (⊤ : Subgroup U) :=
      QuotientGroup.congr W₀ (⊤ : Subgroup U) (MulEquiv.refl U) hmap_top
    have : Subsingleton (U ⧸ (⊤ : Subgroup U)) := QuotientGroup.subsingleton_quotient_top
    rw [bFac_congr e, Nat.card_congr e.toEquiv, bFac_of_solvable, Nat.card_unique]
  | cons M Ms ih =>
    have hM := hMs M List.mem_cons_self
    have hMs' : ∀ K ∈ Ms, IsNonabelianSimpleNormal U N K :=
      fun K hK => hMs K (List.mem_cons_of_mem M hK)
    obtain ⟨hNW', hW'U, hnW', hbW'⟩ := ih hMs'
    set W' := Ms.foldr (· ⊓ ·) U
    obtain ⟨hNM, hMU, hnM, hM_norm, hsimple, hnc⟩ := hM
    have : (W'.subgroupOf U).Normal := rad_subgroupOf_normal hnW'
    refine ⟨le_inf hNM hNW', inf_le_of_left_le hMU,
      fun g hg x hx => ⟨hnM g hg x hx.1, hnW' g hg x hx.2⟩, fun _ => ?_⟩
    exact bFac_inf_eq_card_of_simple hnM hnW' hsimple hnc (hbW' inferInstance)

theorem isSimpleInter_props {U N W : Subgroup (Perm (Fin n))}
    (h : IsSimpleInter U N W) :
    N ≤ W ∧ W ≤ U ∧ ¬ U ≤ W ∧ (∀ g ∈ U, ∀ x ∈ W, g * x * g⁻¹ ∈ W) ∧
    (∀ (_ : (W.subgroupOf U).Normal),
      bFac (U ⧸ W.subgroupOf U) = (W.subgroupOf U).index) := by
  obtain ⟨Ms, hne, rfl, hMs⟩ := h
  cases Ms with
  | nil => exact absurd rfl hne
  | cons M₀ Ms' =>
    have hM₀ := hMs M₀ List.mem_cons_self
    have hNU : N ≤ U := hM₀.1.trans hM₀.2.1
    obtain ⟨hNW, hWU, hnW, hbW⟩ := foldr_inf_props (M₀ :: Ms') hNU hMs
    have hnot : ¬ U ≤ (M₀ :: Ms').foldr (· ⊓ ·) U := by
      intro hle
      have hUM₀ : U ≤ M₀ := hle.trans inf_le_left
      obtain ⟨-, -, -, hM₀_norm, hsimple, -⟩ := hM₀
      have htop : M₀.subgroupOf U = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact hUM₀ x.2
      exact (ne_top_of_simple hsimple) htop
    refine ⟨hNW, hWU, hnot, hnW, fun hnorm => ?_⟩
    rw [Subgroup.index_eq_card]
    exact hbW hnorm

/-- **Lemma 2.6(3) (`isSimpleInter_index_le`).**
If `N ≤ U ≤ H ≤ Perm (Fin n)` with `N` transitive and normalized by `H`, then every `W` satisfying
`IsSimpleInter U N W` has `(W.subgroupOf U).index ≤ n ^ (1 + Nat.log 2 n)`. -/
theorem isSimpleInter_index_le {H U N W : Subgroup (Perm (Fin n))}
    (hUH : U ≤ H) (hnN : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (htr : MulAction.IsPretransitive N (Fin n)) (hW : IsSimpleInter U N W) :
    (W.subgroupOf U).index ≤ n ^ (1 + Nat.log 2 n) := by
  obtain ⟨hNW, hWU, hnot, hnW, hbW⟩ := isSimpleInter_props hW
  have hn1 : 1 ≤ n := one_le_of_not_le hnot
  have hNH : N ≤ H := hNW.trans (hWU.trans hUH)
  have : (N.subgroupOf H).Normal := rad_subgroupOf_normal hnN
  have : (W.subgroupOf U).Normal := rad_subgroupOf_normal hnW
  rw [← hbW inferInstance]
  exact (bFac_subquotient_le hNW hUH).trans (bFac_quotient_le_pow_log hn1 hNH htr)

/-- Conjugation of a subgroup by a permutation `h`: `K.map (MulAut.conj h).toMonoidHom`. -/
def conjSub (h : Perm (Fin n)) (K : Subgroup (Perm (Fin n))) : Subgroup (Perm (Fin n)) :=
  K.map (MulAut.conj h).toMonoidHom

theorem mem_conjSub_iff {h : Perm (Fin n)} {K : Subgroup (Perm (Fin n))} {x : Perm (Fin n)} :
    x ∈ conjSub h K ↔ ∃ y ∈ K, h * y * h⁻¹ = x := by
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem conjSub_eq_of_normalizes {U : Subgroup (Perm (Fin n))} {h : Perm (Fin n)}
    (hU : ∀ x ∈ U, h * x * h⁻¹ ∈ U) (hU_inv : ∀ x ∈ U, h⁻¹ * x * h ∈ U) :
    conjSub h U = U := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hU y hy
  · intro hx
    refine ⟨h⁻¹ * x * h, hU_inv x hx, ?_⟩
    group

theorem conjSub_inf (h : Perm (Fin n)) (A B : Subgroup (Perm (Fin n))) :
    conjSub h (A ⊓ B) = conjSub h A ⊓ conjSub h B := by
  ext x
  simp only [Subgroup.mem_inf, mem_conjSub_iff]
  constructor
  · rintro ⟨y, ⟨hyA, hyB⟩, rfl⟩
    exact ⟨⟨y, hyA, rfl⟩, ⟨y, hyB, rfl⟩⟩
  · rintro ⟨⟨y₁, hy₁, rfl⟩, ⟨y₂, hy₂, h2⟩⟩
    have hy : y₁ = y₂ := by
      have h1 := congrArg (fun p => h⁻¹ * p * h) h2
      simpa [mul_assoc] using h1.symm
    subst hy
    exact ⟨y₁, ⟨hy₁, hy₂⟩, rfl⟩

theorem conjSub_foldr_inf {U : Subgroup (Perm (Fin n))} {h : Perm (Fin n)}
    (hU : ∀ x ∈ U, h * x * h⁻¹ ∈ U) (hU_inv : ∀ x ∈ U, h⁻¹ * x * h ∈ U)
    (Ms : List (Subgroup (Perm (Fin n)))) :
    conjSub h (Ms.foldr (· ⊓ ·) U) = (Ms.map (conjSub h)).foldr (· ⊓ ·) U := by
  induction Ms with
  | nil => exact conjSub_eq_of_normalizes hU hU_inv
  | cons M Ms ih =>
    simp only [List.foldr_cons, List.map_cons, conjSub_inf, ih]

theorem foldr_inf_le_init (U : Subgroup (Perm (Fin n)))
    (Ms : List (Subgroup (Perm (Fin n)))) :
    Ms.foldr (· ⊓ ·) U ≤ U := by
  induction Ms with
  | nil => exact le_rfl
  | cons M Ms ih => exact inf_le_of_right_le ih

theorem foldr_inf_append (U : Subgroup (Perm (Fin n)))
    (Ms₁ Ms₂ : List (Subgroup (Perm (Fin n)))) :
    (Ms₁ ++ Ms₂).foldr (· ⊓ ·) U = (Ms₁.foldr (· ⊓ ·) U) ⊓ (Ms₂.foldr (· ⊓ ·) U) := by
  induction Ms₁ with
  | nil =>
    simp only [List.nil_append, List.foldr_nil]
    exact (inf_eq_right.mpr (foldr_inf_le_init U Ms₂)).symm
  | cons M Ms₁ ih =>
    simp only [List.cons_append, List.foldr_cons, ih, inf_assoc]

/-- Conjugating an `IsNonabelianSimpleNormal U N M` subgroup by `h ∈ H` (when `U, N` are
normalized by `H`) gives another `IsNonabelianSimpleNormal U N` subgroup. -/
theorem isNonabelianSimpleNormal_conjSub {H U N M : Subgroup (Perm (Fin n))}
    (hnU : ∀ g ∈ H, ∀ x ∈ U, g * x * g⁻¹ ∈ U)
    (hnN : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    {h : Perm (Fin n)} (hh : h ∈ H) (hM : IsNonabelianSimpleNormal U N M) :
    IsNonabelianSimpleNormal U N (conjSub h M) := by
  obtain ⟨hNM, hMU, hnM, hM_norm, hsimple, hnc⟩ := hM
  have hh_inv : h⁻¹ ∈ H := H.inv_mem hh
  have hN_conj : N ≤ conjSub h M := by
    intro x hx
    rw [mem_conjSub_iff]
    exact ⟨h⁻¹ * x * h, hNM (by simpa [mul_assoc] using hnN h⁻¹ hh_inv x hx), by group⟩
  have hU_conj : conjSub h M ≤ U := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_conjSub_iff.mp hx
    exact hnU h hh y (hMU hy)
  have hn_conj : ∀ g ∈ U, ∀ x ∈ conjSub h M, g * x * g⁻¹ ∈ conjSub h M := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := mem_conjSub_iff.mp hx
    rw [mem_conjSub_iff]
    have hg' : h⁻¹ * g * h ∈ U := by simpa [mul_assoc] using hnU h⁻¹ hh_inv g hg
    refine ⟨(h⁻¹ * g * h) * y * (h⁻¹ * g * h)⁻¹, hnM _ hg' y hy, ?_⟩
    group
  have hnorm_conj : ((conjSub h M).subgroupOf U).Normal := rad_subgroupOf_normal hn_conj
  let α : U ≃* U :=
    { toFun := fun u => ⟨h * u.1 * h⁻¹, hnU h hh u.1 u.2⟩
      invFun := fun u => ⟨h⁻¹ * u.1 * h, by simpa [mul_assoc] using hnU h⁻¹ hh_inv u.1 u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hmap_sub : (M.subgroupOf U).map α.toMonoidHom = (conjSub h M).subgroupOf U := by
    ext u
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf,
      mem_conjSub_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.1, hv, rfl⟩
    · rintro ⟨y, hy, hyu⟩
      exact ⟨⟨y, hMU hy⟩, hy, Subtype.ext hyu⟩
  let q : U ⧸ M.subgroupOf U ≃* U ⧸ (conjSub h M).subgroupOf U :=
    QuotientGroup.congr (M.subgroupOf U) ((conjSub h M).subgroupOf U) α hmap_sub
  have := hsimple
  refine ⟨hN_conj, hU_conj, hn_conj, hnorm_conj, q.symm.isSimpleGroup, fun hcomm => hnc ?_⟩
  intro x y
  apply q.injective
  rw [map_mul, map_mul, hcomm]

/-- Intersecting `W` with `conjSub h W` for `h ∈ H` preserves `IsSimpleInter U N`. -/
theorem isSimpleInter_inf_conjSub {H U N W : Subgroup (Perm (Fin n))}
    (hnU : ∀ g ∈ H, ∀ x ∈ U, g * x * g⁻¹ ∈ U)
    (hnN : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    {h : Perm (Fin n)} (hh : h ∈ H) (hW : IsSimpleInter U N W) :
    IsSimpleInter U N (W ⊓ conjSub h W) := by
  obtain ⟨Ms, hne, rfl, hMs⟩ := hW
  have hh_inv : h⁻¹ ∈ H := H.inv_mem hh
  have hU1 : ∀ x ∈ U, h * x * h⁻¹ ∈ U := hnU h hh
  have hU2 : ∀ x ∈ U, h⁻¹ * x * h ∈ U := fun x hx => by simpa [mul_assoc] using hnU h⁻¹ hh_inv x hx
  refine ⟨Ms ++ Ms.map (conjSub h), List.append_ne_nil_of_left_ne_nil hne _, ?_, ?_⟩
  · rw [foldr_inf_append, conjSub_foldr_inf hU1 hU2]
  · intro M hM
    rcases List.mem_append.mp hM with hM1 | hM2
    · exact hMs M hM1
    · obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.mp hM2
      exact isNonabelianSimpleNormal_conjSub hnU hnN hh (hMs M₀ hM₀)

open Classical in
/-- One step of the conjugate-intersection pass: if `conjSub h W ≤ W`, keep `W`; else replace `W`
by `W ⊓ conjSub h W`. -/
noncomputable def conjStep (W : Subgroup (Perm (Fin n))) (h : Perm (Fin n)) :
    Subgroup (Perm (Fin n)) :=
  if conjSub h W ≤ W then W else W ⊓ conjSub h W

/-- One pass of conjugate-intersection over `gs`: fold `conjStep` over `gs`. -/
noncomputable def conjPass (W : Subgroup (Perm (Fin n))) (gs : List (Perm (Fin n))) :
    Subgroup (Perm (Fin n)) :=
  gs.foldl conjStep W

/-- For finite subgroups, `conjSub h W ≤ W` implies `h ∈ normSub W` (both `h` and `h⁻¹`
normalize `W`). -/
theorem mem_normSub_of_conjSub_le {W : Subgroup (Perm (Fin n))} {h : Perm (Fin n)}
    (hle : conjSub h W ≤ W) : h ∈ normSub W := by
  have hcard : Nat.card (conjSub h W) = Nat.card W :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have heq : conjSub h W = W := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  intro x
  refine ⟨fun hx => hle (mem_conjSub_iff.mpr ⟨x, hx, rfl⟩), fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := mem_conjSub_iff.mp hx
  have : y = x := by
    have h1 := congrArg (fun p => h⁻¹ * p * h) hyx
    simpa [mul_assoc] using h1
  rwa [← this]

theorem conjStep_le (W : Subgroup (Perm (Fin n))) (h : Perm (Fin n)) :
    conjStep W h ≤ W := by
  classical
  dsimp [conjStep]
  split_ifs
  · exact le_rfl
  · exact inf_le_left

theorem isSimpleInter_conjStep {H U N W : Subgroup (Perm (Fin n))}
    (hnU : ∀ g ∈ H, ∀ x ∈ U, g * x * g⁻¹ ∈ U)
    (hnN : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    {h : Perm (Fin n)} (hh : h ∈ H) (hW : IsSimpleInter U N W) :
    IsSimpleInter U N (conjStep W h) := by
  classical
  dsimp [conjStep]
  split_ifs
  · exact hW
  · exact isSimpleInter_inf_conjSub hnU hnN hh hW

theorem isSimpleInter_conjPass {H U N W : Subgroup (Perm (Fin n))} {gs : List (Perm (Fin n))}
    (hnU : ∀ g ∈ H, ∀ x ∈ U, g * x * g⁻¹ ∈ U)
    (hnN : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (hgs : ∀ h ∈ gs, h ∈ H) (hW : IsSimpleInter U N W) :
    IsSimpleInter U N (conjPass W gs) := by
  induction gs generalizing W with
  | nil => exact hW
  | cons h gs ih =>
    exact ih (fun x hx => hgs x (List.mem_cons_of_mem h hx))
      (isSimpleInter_conjStep hnU hnN (hgs h List.mem_cons_self) hW)

theorem conjPass_le (W : Subgroup (Perm (Fin n))) (gs : List (Perm (Fin n))) :
    conjPass W gs ≤ W := by
  induction gs generalizing W with
  | nil => exact le_rfl
  | cons h gs ih => exact (ih (conjStep W h)).trans (conjStep_le W h)

/-- If every `h ∈ gs` satisfies `conjSub h W ≤ W`, then `W` is normalized by `gens gs`. -/
theorem normalizes_gens_of_forall_conjSub_le {W : Subgroup (Perm (Fin n))}
    {gs : List (Perm (Fin n))} (hall : ∀ h ∈ gs, conjSub h W ≤ W) :
    ∀ g ∈ gens gs, ∀ x ∈ W, g * x * g⁻¹ ∈ W := by
  have hle : gens gs ≤ normSub W := by
    unfold gens
    rw [Subgroup.closure_le]
    intro h hh
    exact mem_normSub_of_conjSub_le (hall h hh)
  intro g hg x hx
  exact (hle hg x).mp hx

/-- In one pass `conjPass W gs`, either `W` is already normalized by `gens gs` (and `conjPass W gs = W`),
or `2 * Nat.card (conjPass W gs) ≤ Nat.card W`. -/
theorem conjPass_normalizes_or_card_lt (W : Subgroup (Perm (Fin n)))
    (gs : List (Perm (Fin n))) :
    (conjPass W gs = W ∧ ∀ g ∈ gens gs, ∀ x ∈ W, g * x * g⁻¹ ∈ W) ∨
    2 * Nat.card (conjPass W gs) ≤ Nat.card W := by
  classical
  by_cases hall : ∀ h ∈ gs, conjSub h W ≤ W
  · left
    refine ⟨?_, normalizes_gens_of_forall_conjSub_le hall⟩
    induction gs with
    | nil => rfl
    | cons h gs ih =>
      have hh : conjSub h W ≤ W := hall h List.mem_cons_self
      have hstep : conjStep W h = W := by simp [conjStep, hh]
      simp only [conjPass, List.foldl_cons, hstep]
      exact ih (fun x hx => hall x (List.mem_cons_of_mem h hx))
  · right
    push Not at hall
    induction gs generalizing W with
    | nil =>
      obtain ⟨h, hh, -⟩ := hall
      exact absurd hh List.not_mem_nil
    | cons h gs ih =>
      by_cases hh : conjSub h W ≤ W
      · have hstep : conjStep W h = W := by simp [conjStep, hh]
        obtain ⟨h', hh', hnot⟩ := hall
        rcases List.mem_cons.mp hh' with rfl | hh''
        · exact absurd hh hnot
        · simpa only [conjPass, List.foldl_cons, hstep] using ih W ⟨h', hh'', hnot⟩
      · have hstep : conjStep W h = W ⊓ conjSub h W := by simp [conjStep, hh]
        have hlt : W ⊓ conjSub h W < W := by
          refine lt_of_le_of_ne inf_le_left fun heq => hh ?_
          have hcard : Nat.card (conjSub h W) = Nat.card W :=
            Subgroup.card_map_of_injective (MulAut.conj h).injective
          have hsub : W ≤ conjSub h W := heq.symm.le.trans inf_le_right
          exact (Subgroup.eq_of_le_of_card_ge hsub hcard.le).symm.le
        have h1 : Nat.card (conjPass (conjStep W h) gs) ≤ Nat.card (conjStep W h) :=
          Subgroup.card_le_of_le (conjPass_le (conjStep W h) gs)
        have h2 : 2 * Nat.card (conjStep W h) ≤ Nat.card W := by
          rw [hstep]
          exact two_mul_card_le_of_lt hlt
        calc 2 * Nat.card (conjPass W (h :: gs))
            = 2 * Nat.card (conjPass (conjStep W h) gs) := rfl
          _ ≤ 2 * Nat.card (conjStep W h) := Nat.mul_le_mul_left 2 h1
          _ ≤ Nat.card W := h2

end Lemma26

end GI.Impl
