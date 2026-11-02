import Workspace.RadicalSocleQuotient
import Mathlib.GroupTheory.Commutator.Basic

/-!
# The radical as an intersection of centralizers of nonabelian chief factors

Paragraph after Lemma A.21: "Their intersection is precisely the radical preimage. Every
solvable normal subgroup centralizes a nonabelian chief factor, since its normal intersection
with that factor must be trivial. Conversely a normal subgroup centralizing every such factor
cannot cover one of them: that would make a nonabelian centerless factor centralize itself.
Its restricted chief series therefore has only abelian factors, and it is solvable."

For a chief series `1 = Q₀ < Q₁ < ⋯ < Q_n = Q` of a finite group `Q` (normal subgroups of `Q`,
each `Q_{i+1}/Q_i` minimal normal in `Q/Q_i`), we prove
`Rad(Q) = ⋂ { preimage of C_{Q/Q_i}(Q_{i+1}/Q_i) : Q_{i+1}/Q_i nonabelian }`.
Applied to `Q = H/N` and pulled back to `H`, this is the radical preimage of the paper.
-/

namespace GI.RadicalCentralizers

open scoped commutatorElement

variable {Q : Type*} [Group Q]

/-- A chief series of length `n`: normal subgroups `s 0 = 1 < s 1 < ⋯ < s n = Q`, with no
normal subgroup of `Q` strictly between consecutive terms. -/
structure IsChiefSeries (n : ℕ) (s : ℕ → Subgroup Q) : Prop where
  normal : ∀ i, (s i).Normal
  bot : s 0 = ⊥
  top : s n = ⊤
  lt : ∀ i < n, s i < s (i + 1)
  chief : ∀ i < n, ∀ M : Subgroup Q, M.Normal → s i ≤ M → M ≤ s (i + 1) →
    M = s i ∨ M = s (i + 1)

/-- The preimage in `Q` of the centralizer `C_{Q/V}(U/V)`. -/
def centPre (U V : Subgroup Q) (hV : V.Normal) : Subgroup Q :=
  letI := hV
  (Subgroup.centralizer ((U.map (QuotientGroup.mk' V) : Subgroup (Q ⧸ V)) : Set (Q ⧸ V))).comap
    (QuotientGroup.mk' V)

theorem mem_centPre {U V : Subgroup Q} (hV : V.Normal) (x : Q) :
    x ∈ centPre U V hV ↔ ∀ u ∈ U, ⁅x, u⁆ ∈ V := by
  letI := hV
  simp only [centPre, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.coe_map,
    Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr (fun u _ => ?_)
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk'_apply]
  constructor
  · intro h; rw [← h]; group
  · intro h
    have := congrArg (· * ((u : Q ⧸ V) * (x : Q ⧸ V))) h
    simp only [one_mul] at this
    rw [← this]; group

/-- Modulo a normal `V`, a commutator with `A ⊔ V` is a commutator with `A`. -/
theorem commutator_sup_le {A B V : Subgroup Q} [V.Normal] :
    ⁅A ⊔ V, B⁆ ≤ ⁅A, B⁆ ⊔ V := by
  have hmap : ⁅A ⊔ V, B⁆.map (QuotientGroup.mk' V) = ⁅A, B⁆.map (QuotientGroup.mk' V) := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_sup]
    have : V.map (QuotientGroup.mk' V) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [this, sup_bot_eq]
  calc ⁅A ⊔ V, B⁆ ≤ (⁅A ⊔ V, B⁆.map (QuotientGroup.mk' V)).comap (QuotientGroup.mk' V) :=
        Subgroup.le_comap_map _ _
    _ = ⁅A, B⁆ ⊔ V := by
        rw [hmap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem centPre_normal {U V : Subgroup Q} (hU : U.Normal) (hV : V.Normal) :
    (centPre U V hV).Normal := by
  letI := hV
  haveI : (U.map (QuotientGroup.mk' V)).Normal := hU.map _ (QuotientGroup.mk'_surjective V)
  haveI := GI.RadicalSocle.centralizer_normal (U.map (QuotientGroup.mk' V))
  exact Subgroup.Normal.comap inferInstance _

section Chief

variable {n : ℕ} {s : ℕ → Subgroup Q} (hs : IsChiefSeries n s)

/-- The intersection over the nonabelian chief factors. -/
def centInter : Subgroup Q :=
  ⨅ (i : ℕ) (_ : i < n) (_ : ¬ ⁅s (i + 1), s (i + 1)⁆ ≤ s i), centPre (s (i + 1)) (s i) (hs.normal i)

include hs in
theorem mem_centInter (x : Q) :
    x ∈ centInter hs ↔ ∀ i < n, ¬ ⁅s (i + 1), s (i + 1)⁆ ≤ s i → ∀ u ∈ s (i + 1), ⁅x, u⁆ ∈ s i := by
  simp only [centInter, Subgroup.mem_iInf, mem_centPre]

theorem centInter_normal : (centInter hs).Normal := by
  constructor
  intro x hx g
  rw [mem_centInter] at hx ⊢
  intro i hi hna
  have hN := centPre_normal (hs.normal (i + 1)) (hs.normal i)
  have : x ∈ centPre (s (i + 1)) (s i) (hs.normal i) := (mem_centPre _ x).mpr (hx i hi hna)
  exact (mem_centPre _ _).mp (hN.conj_mem x this g)

include hs in
/-- A solvable normal subgroup meets a nonabelian chief factor trivially, hence centralizes it. -/
theorem solvable_centralizes {R : Subgroup Q} [R.Normal] [IsSolvable R] {i : ℕ} (hi : i < n)
    (hna : ¬ ⁅s (i + 1), s (i + 1)⁆ ≤ s i) : ∀ x ∈ R, ∀ u ∈ s (i + 1), ⁅x, u⁆ ∈ s i := by
  haveI := hs.normal i
  haveI := hs.normal (i + 1)
  set U := s (i + 1)
  set V := s i
  have hVU : V ≤ U := (hs.lt i hi).le
  haveI : IsSolvable (R ⊓ U : Subgroup Q) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (inf_le_left : R ⊓ U ≤ R))
  -- `M = (R ∩ U) V` is normal between `V` and `U`
  rcases hs.chief i hi ((R ⊓ U) ⊔ V) (Subgroup.sup_normal _ _) le_sup_right
      (sup_le inf_le_right hVU) with hM | hM
  · intro x hx u hu
    apply (le_sup_left : R ⊓ U ≤ (R ⊓ U) ⊔ V).trans hM.le
    exact Subgroup.commutator_le_inf (H₁ := R) (H₂ := U) |> fun h =>
      h (Subgroup.commutator_mem_commutator hx hu)
  · -- `U ≤ (R ∩ U) V`: then `U ≤ D_k V` for every term `D_k` of the derived series of `R ∩ U`
    exfalso
    let D : ℕ → Subgroup Q := fun k => (derivedSeries (R ⊓ U : Subgroup Q) k).map
      (R ⊓ U).subtype
    have hD : ∀ k, U ≤ D k ⊔ V := by
      intro k
      induction k with
      | zero =>
        simp only [D, derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        exact hM.symm.le
      | succ k ih =>
        -- `⁅U, U⁆ V` is normal between `V` and `U`, and is not `V`
        haveI : (⁅U, U⁆ ⊔ V).Normal := Subgroup.sup_normal _ _
        rcases hs.chief i hi (⁅U, U⁆ ⊔ V) inferInstance le_sup_right
            (sup_le (Subgroup.commutator_le_left U U) hVU) with hW | hW
        · exact absurd (le_sup_left.trans hW.le) hna
        · have hDk : D (k + 1) = ⁅D k, D k⁆ := by
            simp only [D, derivedSeries_succ, Subgroup.map_commutator]
          calc U = ⁅U, U⁆ ⊔ V := hW.symm
            _ ≤ ⁅D k ⊔ V, D k ⊔ V⁆ ⊔ V := sup_le_sup_right (Subgroup.commutator_mono ih ih) _
            _ ≤ (⁅D k, D k ⊔ V⁆ ⊔ V) ⊔ V := sup_le_sup_right commutator_sup_le _
            _ ≤ ((⁅D k, D k⁆ ⊔ V) ⊔ V) ⊔ V := by
                refine sup_le_sup_right (sup_le_sup_right ?_ _) _
                rw [Subgroup.commutator_comm (D k) (D k ⊔ V), Subgroup.commutator_comm (D k) (D k)]
                exact commutator_sup_le
            _ = D (k + 1) ⊔ V := by rw [hDk, sup_assoc, sup_idem, sup_assoc, sup_idem]
    obtain ⟨k, hk⟩ := (inferInstance : IsSolvable (R ⊓ U : Subgroup Q)).solvable
    have h := hD k
    simp only [D, hk, Subgroup.map_bot, bot_sup_eq] at h
    exact (hs.lt i hi).not_ge h

include hs in
/-- The intersection meets each chief factor in an abelian section: a normal subgroup that
centralizes a nonabelian chief factor cannot cover it. -/
theorem centInter_factor {i : ℕ} (hi : i < n) :
    ⁅centInter hs ⊓ s (i + 1), centInter hs ⊓ s (i + 1)⁆ ≤ s i := by
  haveI := hs.normal i
  haveI := hs.normal (i + 1)
  haveI := centInter_normal hs
  set U := s (i + 1)
  set V := s i
  set C := centInter hs
  have hVU : V ≤ U := (hs.lt i hi).le
  by_cases hna : ⁅U, U⁆ ≤ V
  · exact (Subgroup.commutator_mono inf_le_right inf_le_right).trans hna
  have hCU : ⁅C ⊓ U, U⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro x hx u hu
    exact (mem_centInter hs x).mp hx.1 i hi hna u hu
  rcases hs.chief i hi ((C ⊓ U) ⊔ V) (Subgroup.sup_normal _ _) le_sup_right
      (sup_le inf_le_right hVU) with hM | hM
  · exact (Subgroup.commutator_le_left _ _).trans (le_sup_left.trans hM.le)
  · exfalso
    apply hna
    calc ⁅U, U⁆ = ⁅(C ⊓ U) ⊔ V, U⁆ := by rw [hM]
      _ ≤ ⁅C ⊓ U, U⁆ ⊔ V := commutator_sup_le
      _ ≤ V := sup_le hCU le_rfl

include hs in
/-- The intersection is solvable: its restricted chief series has abelian factors. -/
theorem centInter_solvable : IsSolvable (centInter hs) := by
  set C := centInter hs
  have key : ∀ k, k ≤ n → (derivedSeries C k).map C.subtype ≤ s (n - k) := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.sub_zero, hs.top]; exact le_top
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hsub : (derivedSeries C k).map C.subtype ≤ C := Subgroup.map_subtype_le _
      have heq : n - k = (n - (k + 1)) + 1 := by omega
      rw [derivedSeries_succ, Subgroup.map_commutator]
      refine (Subgroup.commutator_mono (le_inf hsub h1) (le_inf hsub h1)).trans ?_
      rw [heq]
      exact centInter_factor hs (by omega)
  refine ⟨⟨n, ?_⟩⟩
  have h := key n le_rfl
  rw [Nat.sub_self, hs.bot] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp (le_bot_iff.mp h)

include hs in
/-- **The characterization of the radical** (paragraph after Lemma A.21): the solvable
radical is the intersection of the preimages of the centralizers of the nonabelian chief
factors. -/
theorem radical_eq_centInter [Finite Q] :
    GI.RadicalSocle.solvableRadical Q = centInter hs := by
  haveI := centInter_normal hs
  haveI := centInter_solvable hs
  apply le_antisymm
  · intro x hx
    rw [mem_centInter]
    intro i hi hna u hu
    exact solvable_centralizes hs (R := GI.RadicalSocle.solvableRadical Q) hi hna x hx u hu
  · exact GI.RadicalSocle.le_solvableRadical _

end Chief

end GI.RadicalCentralizers
