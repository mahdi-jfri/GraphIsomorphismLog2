module

public import Workspace.RadicalFreeOrder
public import Workspace.Impl.TermRadMath
public import Workspace.OutbSuppMath
public import Workspace.NonabelianChief

@[expose] public section

/-!
# Computing the socle preimage from a nonabelian-chief chain (the mathematics)

Given `R ⊴ H ≤ Sym(n)` with `H / R` radical-free and a chain
`H = W₀ ≥ W₁ ≥ ⋯ ≥ W_L = R` of subgroups normalized by `H` whose nonabelian steps
(`¬ ⁅W_j, W_j⁆ ≤ W_{j+1}`) are chief in `H`, we compute `E_H = soclePreimage H R` by
maintaining `C` (normalized by `H`, `R ≤ C ≤ H`) and `E` (normalized by `H`,
`R ≤ E ≤ soclePreimage H R`) with `C / R = C_{H/R}(E / R)`, starting from `C = H`, `E = R`:

1. While `¬ (C ≤ R)`:
   - Let `j < L` be the largest index with `¬ (W_j ⊓ C ≤ R)`, so `W_{j+1} ⊓ C ≤ R`.
     Put `I = W_j ⊓ C`.
   - Since `W_{j+1} ⊓ C = R` and `H / R` is radical-free, the factor `W_j / W_{j+1}` cannot be
     abelian (`soc_quot_step_nonabelian`), so it is a chief factor of `H` and `I / R` is a
     minimal normal subgroup of `H / R` (`soc_quot_minimalNormal`), hence `I ≤ soclePreimage H R`
     (`soc_le_soclePreimage`) and `(R.subgroupOf I).index ≤ (R.subgroupOf (soclePreimage H R)).index`.
   - Update `E ← E ⊔ I` and `C ← C ⊓ Z`, where `Z = {h ∈ H | ∀ u ∈ I, [h, u] ∈ R}` is the
     preimage of `C_{H/R}(I / R)`. Since `Z(I / R) = 1` in the radical-free group `H / R`,
     `I ⊓ Z = R` (`soc_quot_inf_centralizer_eq_bot`), so `C ⊓ Z < C` and `2 * |C ⊓ Z| ≤ |C|`
     (as well as `2 * [(C ⊓ Z ⊓ E_H) : R] ≤ [C ⊓ E_H : R]`).
2. When `C ≤ R`, `C_{H/R}(E / R) = 1`; every minimal normal subgroup of `H / R` meets `E / R`
   nontrivially and therefore lies in `E / R`, so `E = soclePreimage H R`
   (`soc_eq_soclePreimage_of_le`).
-/

namespace GI.Impl

open Equiv GI.Cited GI.RadicalSocle GI.RadicalFreeOrder
open scoped commutatorElement

/-! ### Part 1: Socle accumulation in a radical-free group `Q` -/

section QuotientChain

variable {Q : Type*} [Group Q]

/-- A decreasing chain `⊤ = t 0 ≥ t 1 ≥ ⋯ ≥ t L = ⊥` of normal subgroups of `Q` whose
nonabelian factors have no normal subgroup of `Q` strictly between consecutive terms. -/
structure SocQuotChain (L : ℕ) (t : ℕ → Subgroup Q) : Prop where
  normal : ∀ j, (t j).Normal
  top : t 0 = ⊤
  bot : t L = ⊥
  le : ∀ j < L, t (j + 1) ≤ t j
  chief : ∀ j < L, ¬ ⁅t j, t j⁆ ≤ t (j + 1) →
    ∀ M : Subgroup Q, M.Normal → t (j + 1) ≤ M → M ≤ t j →
      M = t (j + 1) ∨ M = t j

variable (hrf : ∀ N : Subgroup Q, N.Normal → Group.IsSolvable N → N = ⊥)

include hrf in
/-- In a radical-free group `Q`, if `I = t j ⊓ C ≠ ⊥` and `t (j + 1) ⊓ C = ⊥` with `C` normal,
then the step `t j / t (j + 1)` is nonabelian. -/
theorem soc_quot_step_nonabelian {L : ℕ} {t : ℕ → Subgroup Q} (ht : SocQuotChain L t)
    {C : Subgroup Q} [C.Normal] {j : ℕ} (hj : j < L)
    (hI : t j ⊓ C ≠ ⊥) (hnext : t (j + 1) ⊓ C = ⊥) :
    ¬ ⁅t j, t j⁆ ≤ t (j + 1) := by
  intro hab
  set I : Subgroup Q := t j ⊓ C
  have : (t j).Normal := ht.normal j
  have : I.Normal := inferInstance
  have hI_next : I ⊓ t (j + 1) = ⊥ := by
    calc (t j ⊓ C) ⊓ t (j + 1) = (t j ⊓ t (j + 1)) ⊓ C := by ac_rfl
      _ = t (j + 1) ⊓ C := by rw [inf_of_le_right (ht.le j hj)]
      _ = ⊥ := hnext
  have hcomm_bot : ⁅I, I⁆ ≤ ⊥ := by
    rw [← hI_next]
    exact le_inf (Subgroup.commutator_le_left I I)
      ((Subgroup.commutator_mono inf_le_left inf_le_left).trans hab)
  have hcomm : ∀ x y : I, x * y = y * x := by
    intro x y
    apply Subtype.ext
    have hc : ⁅(x : Q), (y : Q)⁆ ∈ (⊥ : Subgroup Q) :=
      hcomm_bot (Subgroup.commutator_mem_commutator x.2 y.2)
    rw [Subgroup.mem_bot, commutatorElement_def] at hc
    have h1 := congrArg (· * (y * x : Q)) hc
    group at h1
    exact h1
  have : Group.IsSolvable I := Group.isSolvable_of_comm hcomm
  exact hI (hrf I inferInstance inferInstance)

include hrf in
/-- In a radical-free group `Q`, if `I = t j ⊓ C ≠ ⊥` and `t (j + 1) ⊓ C = ⊥` with `C` normal,
then `I` is a minimal normal subgroup of `Q`. -/
theorem soc_quot_minimalNormal {L : ℕ} {t : ℕ → Subgroup Q} (ht : SocQuotChain L t)
    {C : Subgroup Q} [C.Normal] {j : ℕ} (hj : j < L)
    (hI : t j ⊓ C ≠ ⊥) (hnext : t (j + 1) ⊓ C = ⊥) :
    MinimalNormal (t j ⊓ C) := by
  set I : Subgroup Q := t j ⊓ C
  have : (t j).Normal := ht.normal j
  have : (t (j + 1)).Normal := ht.normal (j + 1)
  have : I.Normal := inferInstance
  have hI_next : I ⊓ t (j + 1) = ⊥ := by
    calc (t j ⊓ C) ⊓ t (j + 1) = (t j ⊓ t (j + 1)) ⊓ C := by ac_rfl
      _ = t (j + 1) ⊓ C := by rw [inf_of_le_right (ht.le j hj)]
      _ = ⊥ := hnext
  have hna := soc_quot_step_nonabelian hrf ht hj hI hnext
  refine ⟨inferInstance, hI, fun K hK_norm hKI => ?_⟩
  by_cases hK : K = ⊥
  · exact Or.inl hK
  · right
    have : K.Normal := hK_norm
    have : (K ⊔ t (j + 1)).Normal := Subgroup.sup_normal K (t (j + 1))
    rcases ht.chief j hj hna (K ⊔ t (j + 1)) inferInstance le_sup_right
        (sup_le (hKI.trans inf_le_left) (ht.le j hj)) with hM | hM
    · exfalso
      apply hK
      rw [← le_bot_iff, ← hI_next]
      exact le_inf hKI (le_sup_left.trans hM.le)
    · apply le_antisymm hKI
      intro x hxI
      have hxt : x ∈ K ⊔ t (j + 1) := by
        rw [hM]
        exact hxI.1
      rw [Subgroup.mem_sup_of_normal_left] at hxt
      obtain ⟨k, hk, v, hv, rfl⟩ := hxt
      have hvI : v ∈ I := by
        have : k⁻¹ * (k * v) ∈ I := I.mul_mem (I.inv_mem (hKI hk)) hxI
        simpa using this
      have hv_bot : v ∈ (⊥ : Subgroup Q) := by
        rw [← hI_next]
        exact ⟨hvI, hv⟩
      rw [Subgroup.mem_bot] at hv_bot
      simpa [hv_bot] using hk

include hrf in
/-- Under the hypotheses of `soc_quot_minimalNormal`, `t j ⊓ C ≤ socle Q`. -/
theorem soc_quot_le_socle [Finite Q] {L : ℕ} {t : ℕ → Subgroup Q} (ht : SocQuotChain L t)
    {C : Subgroup Q} [C.Normal] {j : ℕ} (hj : j < L)
    (hI : t j ⊓ C ≠ ⊥) (hnext : t (j + 1) ⊓ C = ⊥) :
    t j ⊓ C ≤ socle Q :=
  minimalNormal_le_socle (soc_quot_minimalNormal hrf ht hj hI hnext)

include hrf in
/-- In a radical-free group `Q`, any normal subgroup `I` has trivial center `I ⊓ C_Q(I) = ⊥`. -/
theorem soc_quot_inf_centralizer_eq_bot (I : Subgroup Q) [I.Normal] :
    I ⊓ Subgroup.centralizer (I : Set Q) = ⊥ := by
  set Z := Subgroup.centralizer (I : Set Q)
  have : Z.Normal := centralizer_normal I
  have : (I ⊓ Z).Normal := inferInstance
  have hcomm : ∀ x y : ↥(I ⊓ Z), x * y = y * x := by
    intro x y
    apply Subtype.ext
    change (x : Q) * (y : Q) = (y : Q) * (x : Q)
    exact y.2.2 x.1 x.2.1
  have : Group.IsSolvable ↥(I ⊓ Z) := Group.isSolvable_of_comm hcomm
  exact hrf (I ⊓ Z) inferInstance inferInstance

/-- The centralizer of `E ⊔ I` is the intersection of the centralizers of `E` and `I`. -/
theorem soc_quot_centralizer_sup (E I : Subgroup Q) :
    Subgroup.centralizer ((E ⊔ I : Subgroup Q) : Set Q) =
      Subgroup.centralizer (E : Set Q) ⊓ Subgroup.centralizer (I : Set Q) := by
  have hkey : ∀ S : Subgroup Q, ∀ g : Q,
      g ∈ Subgroup.centralizer (S : Set Q) ↔ S ≤ Subgroup.centralizer ({g} : Set Q) := by
    intro S g
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h s hs
      rw [Subgroup.mem_centralizer_iff]
      rintro _ (rfl : _ = g)
      exact (h s hs).symm
    · intro h s hs
      have hs' := h hs
      rw [Subgroup.mem_centralizer_iff] at hs'
      exact (hs' g rfl).symm
  ext g
  rw [hkey (E ⊔ I) g, Subgroup.mem_inf, hkey E g, hkey I g, sup_le_iff]

/-- If `E ⊴ Q` with `E ≤ socle Q` and `C_Q(E) = ⊥`, then `E = socle Q`. -/
theorem soc_quot_eq_socle_of_centralizer_eq_bot [Finite Q] {E : Subgroup Q} [E.Normal]
    (hE : E ≤ socle Q) (hC : Subgroup.centralizer (E : Set Q) = ⊥) :
    E = socle Q := by
  apply le_antisymm hE
  apply socle_le_normal E
  intro M hM
  have : M.Normal := hM.1
  have : (M ⊓ E).Normal := inferInstance
  rcases hM.2.2 (M ⊓ E) inferInstance inf_le_left with hbot | hME
  · exfalso
    apply hM.2.1
    rw [← le_bot_iff, ← hC]
    intro m hm e he
    have hcomm_mem : e * m * e⁻¹ * m⁻¹ ∈ M ⊓ E := by
      refine ⟨?_, ?_⟩
      · exact M.mul_mem (hM.1.conj_mem m hm e) (M.inv_mem hm)
      · have he' : m * e⁻¹ * m⁻¹ ∈ E :=
          (inferInstance : E.Normal).conj_mem e⁻¹ (E.inv_mem he) m
        simpa [mul_assoc] using E.mul_mem he he'
    rw [hbot, Subgroup.mem_bot] at hcomm_mem
    have h1 := congrArg (· * (m * e)) hcomm_mem
    group at h1
    exact h1
  · exact inf_eq_left.mp hME

end QuotientChain

/-! ### Part 2: Nonabelian-chief chains from `H` to `R` in `Sym(n)` -/

section PermChain

variable {n : ℕ} {H R : Subgroup (Perm (Fin n))}

/-- A decreasing chain `H = W₀ ≥ W₁ ≥ ⋯ ≥ W_L = R` of subgroups normalized by `H` whose
nonabelian steps are chief in `H`. Defined as an `abbrev` so inline hypotheses match
definitionally. -/
abbrev SocChain (H R : Subgroup (Perm (Fin n)))
    (Ws : List (Subgroup (Perm (Fin n)))) : Prop :=
  Ws.head? = some H ∧ Ws.getLast? = some R ∧
  (∀ W ∈ Ws, ∀ g ∈ H, ∀ x ∈ W, g * x * g⁻¹ ∈ W) ∧
  ∀ j (h : j + 1 < Ws.length),
    Ws[j + 1] ≤ Ws[j] ∧
    (¬ ⁅Ws[j], Ws[j]⁆ ≤ Ws[j + 1] →
      ∀ K : Subgroup (Perm (Fin n)), Ws[j + 1] ≤ K → K ≤ Ws[j] →
        (∀ g ∈ H, ∀ x ∈ K, g * x * g⁻¹ ∈ K) → K = Ws[j + 1] ∨ K = Ws[j])

/-- Term `j` of a subgroup chain from `H` to `R`, defaulting to `R` past the end. -/
abbrev socTerm (R : Subgroup (Perm (Fin n))) (Ws : List (Subgroup (Perm (Fin n)))) (j : ℕ) :
    Subgroup (Perm (Fin n)) :=
  Ws.getD j R

theorem soc_chain_length_pos {Ws : List (Subgroup (Perm (Fin n)))}
    (hs : SocChain H R Ws) : 0 < Ws.length := by
  obtain ⟨h1, -, -, -⟩ := hs
  cases Ws with
  | nil => simp at h1
  | cons _ _ => exact Nat.succ_pos _

theorem soc_term_zero {Ws : List (Subgroup (Perm (Fin n)))}
    (hs : SocChain H R Ws) : socTerm R Ws 0 = H := by
  obtain ⟨h1, -, -, -⟩ := hs
  cases Ws with
  | nil => simp at h1
  | cons a l => simp only [List.head?_cons, Option.some.injEq] at h1; simp [socTerm, h1]

theorem soc_term_last {Ws : List (Subgroup (Perm (Fin n)))}
    (hs : SocChain H R Ws) : socTerm R Ws (Ws.length - 1) = R := by
  obtain ⟨-, h2, -, -⟩ := hs
  rw [List.getLast?_eq_getElem?] at h2
  simp only [socTerm, List.getD_eq_getElem?_getD, h2, Option.getD_some]

theorem soc_term_succ_le {Ws : List (Subgroup (Perm (Fin n)))}
    (hs : SocChain H R Ws) {j : ℕ} (hj : j < Ws.length - 1) :
    socTerm R Ws (j + 1) ≤ socTerm R Ws j := by
  have hj' : j + 1 < Ws.length := by omega
  have h := (hs.2.2.2 j hj').1
  simpa only [socTerm, List.getD_eq_getElem _ _ hj',
    List.getD_eq_getElem _ _ (show j < Ws.length by omega)] using h

theorem soc_term_le_H (hRH : R ≤ H) {Ws : List (Subgroup (Perm (Fin n)))}
    (hs : SocChain H R Ws) : ∀ j, socTerm R Ws j ≤ H := by
  intro j
  induction j with
  | zero => rw [soc_term_zero hs]
  | succ j ih =>
    by_cases hj : j + 1 < Ws.length
    · exact (soc_term_succ_le hs (by omega)).trans ih
    · simp only [socTerm, List.getD_eq_default _ _ (show Ws.length ≤ j + 1 by omega)]
      exact hRH

theorem soc_R_le_term {Ws : List (Subgroup (Perm (Fin n)))}
    (hs : SocChain H R Ws) : ∀ j, R ≤ socTerm R Ws j := by
  intro j
  by_cases hj : j < Ws.length
  · obtain ⟨k, rfl⟩ : ∃ k, j = Ws.length - 1 - k := ⟨Ws.length - 1 - j, by omega⟩
    induction k with
    | zero =>
      simp only [Nat.sub_zero, soc_term_last hs, le_rfl]
    | succ k ih =>
      by_cases hk : k < Ws.length - 1
      · have h1 := ih (by omega)
        have hstep := soc_term_succ_le hs (j := Ws.length - 1 - (k + 1)) (by omega)
        have heq : Ws.length - 1 - (k + 1) + 1 = Ws.length - 1 - k := by omega
        rw [heq] at hstep
        exact h1.trans hstep
      · have heq : Ws.length - 1 - (k + 1) = Ws.length - 1 - k := by omega
        rw [heq]
        exact ih (by omega)
  · simp only [socTerm, List.getD_eq_default _ _ (show Ws.length ≤ j by omega), le_rfl]

theorem soc_term_normalized (hnR : GI.Multicoset.Normalizes H R)
    {Ws : List (Subgroup (Perm (Fin n)))} (hs : SocChain H R Ws) (j : ℕ) :
    GI.Multicoset.Normalizes H (socTerm R Ws j) := by
  by_cases hj : j < Ws.length
  · simp only [socTerm, List.getD_eq_getElem _ _ hj]
    exact hs.2.2.1 _ (List.getElem_mem hj)
  · simp only [socTerm, List.getD_eq_default _ _ (show Ws.length ≤ j by omega)]
    exact hnR

/-- Bridge: any nonabelian-chief chain `Cs` from `H` to `⊥`, multiplied by `R`, gives a
`SocChain` from `H` to `R`. -/
theorem soc_chain_of_bot (hRH : R ≤ H) (hnR : GI.Multicoset.Normalizes H R)
    {Cs : List (Subgroup (Perm (Fin n)))} (hc : SocChain H ⊥ Cs) :
    SocChain H R (Cs.map (fun C => R ⊔ C)) := by
  obtain ⟨hhead, hlast, hnorm, hstep⟩ := hc
  refine ⟨?_, ?_, ?_, fun j hj => ?_⟩
  · cases Cs with
    | nil => simp at hhead
    | cons c l =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp [hhead, sup_eq_right.mpr hRH]
  · rw [List.getLast?_map, hlast]
    simp
  · intro W hW
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hW
    exact rad_sup_normalized hnR (hnorm C hC)
  · simp only [List.length_map] at hj
    have hj0 : j < Cs.length := by omega
    simp only [List.getElem_map]
    obtain ⟨hle, hch⟩ := hstep j hj
    refine ⟨sup_le_sup_left hle R, fun hna K hK1 hK2 hKn => ?_⟩
    have hnaC : ¬ ⁅Cs[j], Cs[j]⁆ ≤ Cs[j + 1] := by
      intro hab
      apply hna
      have : (R.subgroupOf H).Normal := rad_subgroupOf_normal hnR
      have hCj : Cs[j] ≤ H := by
        simpa only [socTerm, List.getD_eq_getElem _ _ hj0] using
          soc_term_le_H bot_le ⟨hhead, hlast, hnorm, hstep⟩ j
      have hCj1 : Cs[j + 1] ≤ H := by
        simpa only [socTerm, List.getD_eq_getElem _ _ hj] using
          soc_term_le_H bot_le ⟨hhead, hlast, hnorm, hstep⟩ (j + 1)
      have hRCj : R ⊔ Cs[j] ≤ H := sup_le hRH hCj
      have hRCj1 : R ⊔ Cs[j + 1] ≤ H := sup_le hRH hCj1
      rw [show R ⊔ Cs[j + 1] = R ⊔ (R ⊔ Cs[j + 1]) by rw [← sup_assoc, sup_idem],
        ← rad_comm_le_iff (N := R) hRCj hRCj1 hRH]
      have heq1 : ((R ⊔ Cs[j]).subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H)) =
          (Cs[j].subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H)) := by
        ext ⟨y, hy⟩
        exact (rad_mem_map_iff hRCj hRH ⟨y, hy⟩).trans
          (by rw [← sup_assoc, sup_idem]; exact (rad_mem_map_iff hCj hRH ⟨y, hy⟩).symm)
      have heq2 : ((R ⊔ Cs[j + 1]).subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H)) =
          (Cs[j + 1].subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H)) := by
        ext ⟨y, hy⟩
        exact (rad_mem_map_iff hRCj1 hRH ⟨y, hy⟩).trans
          (by rw [← sup_assoc, sup_idem]; exact (rad_mem_map_iff hCj1 hRH ⟨y, hy⟩).symm)
      rw [heq1, heq2, rad_comm_le_iff hCj hCj1 hRH]
      exact hab.trans le_sup_right
    set B := K ⊓ Cs[j]
    have hB1 : Cs[j + 1] ≤ B := le_inf (le_sup_right.trans hK1) hle
    have hB2 : B ≤ Cs[j] := inf_le_right
    have hBn : ∀ g ∈ H, ∀ x ∈ B, g * x * g⁻¹ ∈ B :=
      fun g hg x ⟨hx1, hx2⟩ => ⟨hKn g hg x hx1, hnorm Cs[j] (List.getElem_mem hj0) g hg x hx2⟩
    have hRB : R ⊔ B = K := by
      apply le_antisymm (sup_le (le_sup_left.trans hK1) inf_le_left)
      intro x hxK
      have hxRC : x ∈ R ⊔ Cs[j] := hK2 hxK
      have hsub : R ⊔ Cs[j] ≤ (R.subgroupOf H ⊔ Cs[j].subgroupOf H).map H.subtype := by
        have hCj : Cs[j] ≤ H := by
          simpa only [socTerm, List.getD_eq_getElem _ _ hj0] using
            soc_term_le_H bot_le ⟨hhead, hlast, hnorm, hstep⟩ j
        rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
          inf_of_le_left hRH, inf_of_le_left hCj]
      obtain ⟨⟨_, hyH⟩, hy, rfl⟩ := hsub hxRC
      have : (R.subgroupOf H).Normal := rad_subgroupOf_normal hnR
      rw [SetLike.mem_coe, Subgroup.mem_sup_of_normal_left] at hy
      obtain ⟨⟨r, _⟩, hrR, ⟨c, _⟩, hcC, hmul⟩ := hy
      have hrc : r * c = _ := congrArg Subtype.val hmul
      dsimp at hrc
      have hcK : c ∈ K := by
        have : r⁻¹ * (r * c) ∈ K := K.mul_mem (K.inv_mem (le_sup_left.trans hK1 hrR)) (hrc ▸ hxK)
        simpa using this
      dsimp
      rw [← hrc]
      exact Subgroup.mul_mem_sup hrR ⟨hcK, hcC⟩
    rcases hch hnaC B hB1 hB2 hBn with hB | hB
    · left; rw [← hRB, hB]
    · right; rw [← hRB, hB]

/-- Bridge: any `IsNonabelianChiefChain H R Hs` from `NonabelianChief.lean`, mapped by `R ⊔ ·`,
satisfies `SocChain H R`. -/
theorem soc_chain_of_nonabelianChiefChain (hRH : R ≤ H) (hnR : GI.Multicoset.Normalizes H R)
    {Hs : List (Subgroup (Perm (Fin n)))} (hc : IsNonabelianChiefChain H R Hs) :
    SocChain H R (Hs.map (fun C => R ⊔ C)) := by
  obtain ⟨hhead, ⟨K, hlast, hKR⟩, hnorm, hstep⟩ := hc
  refine ⟨?_, ?_, ?_, fun j hj => ?_⟩
  · cases Hs with
    | nil => simp at hhead
    | cons c l =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp [hhead, sup_eq_right.mpr hRH]
  · rw [List.getLast?_map, hlast]
    simp [sup_eq_left.mpr hKR]
  · intro W hW
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hW
    exact rad_sup_normalized hnR (hnorm C hC).2
  · simp only [List.length_map] at hj
    have hj0 : j < Hs.length := by omega
    simp only [List.getElem_map]
    obtain ⟨hle, hch⟩ := hstep j hj
    refine ⟨sup_le_sup_left hle R, fun hna M hM1 hM2 hMn => ?_⟩
    have hnaC : ¬ ⁅Hs[j], Hs[j]⁆ ≤ R ⊔ Hs[j + 1] := by
      intro hab
      apply hna
      have : (R.subgroupOf H).Normal := rad_subgroupOf_normal hnR
      have hCj : Hs[j] ≤ H := (hnorm Hs[j] (List.getElem_mem hj0)).1
      have hCj1 : Hs[j + 1] ≤ H := (hnorm Hs[j + 1] (List.getElem_mem hj)).1
      have hRCj : R ⊔ Hs[j] ≤ H := sup_le hRH hCj
      have hRCj1 : R ⊔ Hs[j + 1] ≤ H := sup_le hRH hCj1
      rw [show R ⊔ Hs[j + 1] = R ⊔ (R ⊔ Hs[j + 1]) by rw [← sup_assoc, sup_idem],
        ← rad_comm_le_iff (N := R) hRCj hRCj1 hRH]
      have heq1 : ((R ⊔ Hs[j]).subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H)) =
          (Hs[j].subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H)) := by
        ext ⟨y, hy⟩
        exact (rad_mem_map_iff hRCj hRH ⟨y, hy⟩).trans
          (by rw [← sup_assoc, sup_idem]; exact (rad_mem_map_iff hCj hRH ⟨y, hy⟩).symm)
      have heq2 : ((R ⊔ Hs[j + 1]).subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H)) =
          (Hs[j + 1].subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H)) := by
        ext ⟨y, hy⟩
        exact (rad_mem_map_iff hRCj1 hRH ⟨y, hy⟩).trans
          (by rw [← sup_assoc, sup_idem]; exact (rad_mem_map_iff hCj1 hRH ⟨y, hy⟩).symm)
      rw [heq1, heq2, rad_comm_le_iff hCj hCj1 hRH]
      exact hab
    exact hch hnaC M hM1 hM2 hMn

/-! ### Part 3: Quotient correspondence for subgroups between `R` and `H` -/

variable [(R.subgroupOf H).Normal]

/-- The image in `H / R` of a subgroup `A` of `Sym(n)`. -/
def socQuot (H R A : Subgroup (Perm (Fin n))) [(R.subgroupOf H).Normal] :
    Subgroup (H ⧸ R.subgroupOf H) :=
  (A.subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H))

theorem soc_mem_quot_iff {A : Subgroup (Perm (Fin n))} (hRA : R ≤ A) (hAH : A ≤ H)
    (hRH : R ≤ H) (y : H) :
    QuotientGroup.mk' (R.subgroupOf H) y ∈ socQuot H R A ↔ (y : Perm (Fin n)) ∈ A := by
  rw [socQuot, rad_mem_map_iff hAH hRH y, sup_eq_right.mpr hRA]

theorem soc_quot_le_iff {A B : Subgroup (Perm (Fin n))}
    (hRA : R ≤ A) (hAH : A ≤ H) (hRB : R ≤ B) (hBH : B ≤ H) :
    socQuot H R A ≤ socQuot H R B ↔ A ≤ B := by
  have hRH := hRA.trans hAH
  constructor
  · intro h x hxA
    have hy : QuotientGroup.mk' (R.subgroupOf H) ⟨x, hAH hxA⟩ ∈ socQuot H R B :=
      h ((soc_mem_quot_iff hRA hAH hRH ⟨x, hAH hxA⟩).mpr hxA)
    exact (soc_mem_quot_iff hRB hBH hRH ⟨x, hAH hxA⟩).mp hy
  · intro h
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H h)

theorem soc_quot_eq_iff {A B : Subgroup (Perm (Fin n))}
    (hRA : R ≤ A) (hAH : A ≤ H) (hRB : R ≤ B) (hBH : B ≤ H) :
    socQuot H R A = socQuot H R B ↔ A = B := by
  rw [le_antisymm_iff, soc_quot_le_iff hRA hAH hRB hBH, soc_quot_le_iff hRB hBH hRA hAH,
    ← le_antisymm_iff]

theorem soc_quot_self : socQuot H R R = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact (QuotientGroup.eq_one_iff y).mpr hy

theorem soc_quot_top : socQuot H R H = ⊤ := by
  simp [socQuot, Subgroup.subgroupOf_self,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem soc_quot_eq_bot_iff {A : Subgroup (Perm (Fin n))} (hRA : R ≤ A) (hAH : A ≤ H) :
    socQuot H R A = ⊥ ↔ A ≤ R := by
  rw [← soc_quot_self (H := H) (R := R), soc_quot_eq_iff hRA hAH le_rfl (hRA.trans hAH)]
  exact ⟨fun h => h.le, fun h => le_antisymm h hRA⟩

theorem soc_quot_sup {A B : Subgroup (Perm (Fin n))} (hAH : A ≤ H) (hBH : B ≤ H) :
    socQuot H R (A ⊔ B) = socQuot H R A ⊔ socQuot H R B := by
  unfold socQuot
  rw [← Subgroup.map_sup]
  congr 1
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left (sup_le hAH hBH),
    inf_of_le_left hAH, inf_of_le_left hBH]

theorem soc_quot_inf {A B : Subgroup (Perm (Fin n))}
    (hRA : R ≤ A) (hAH : A ≤ H) (hRB : R ≤ B) (hBH : B ≤ H) :
    socQuot H R (A ⊓ B) = socQuot H R A ⊓ socQuot H R B := by
  have hRH := hRA.trans hAH
  ext z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf H) z
  rw [Subgroup.mem_inf, soc_mem_quot_iff (le_inf hRA hRB) (inf_le_left.trans hAH) hRH,
    soc_mem_quot_iff hRA hAH hRH, soc_mem_quot_iff hRB hBH hRH, Subgroup.mem_inf]

theorem soc_quot_normal {A : Subgroup (Perm (Fin n))} (hnA : GI.Multicoset.Normalizes H A) :
    (socQuot H R A).Normal := by
  have := rad_subgroupOf_normal hnA
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

theorem soc_quot_comm_le_iff {A B : Subgroup (Perm (Fin n))}
    (hAH : A ≤ H) (hRB : R ≤ B) (hBH : B ≤ H) :
    ⁅socQuot H R A, socQuot H R A⁆ ≤ socQuot H R B ↔ ⁅A, A⁆ ≤ B := by
  rw [socQuot, socQuot, rad_comm_le_iff hAH hBH (hRB.trans hBH), sup_eq_right.mpr hRB]

theorem soc_quot_soclePreimage :
    socQuot H R (soclePreimage H R) = socle (H ⧸ R.subgroupOf H) := by
  unfold socQuot
  rw [soclePreimage_subgroupOf]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

/-- A nonabelian-chief chain from `H` to `R` projects to a `SocQuotChain` in `H / R`. -/
theorem soc_quot_chain (hRH : R ≤ H) (hnR : GI.Multicoset.Normalizes H R)
    {Ws : List (Subgroup (Perm (Fin n)))} (hs : SocChain H R Ws) :
    SocQuotChain (Ws.length - 1) (fun j => socQuot H R (socTerm R Ws j)) := by
  set π := QuotientGroup.mk' (R.subgroupOf H)
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  refine ⟨fun j => soc_quot_normal (soc_term_normalized hnR hs j), ?_, ?_, fun j hj => ?_,
    fun j hj hna M hM h1 h2 => ?_⟩
  · rw [soc_term_zero hs, soc_quot_top]
  · rw [soc_term_last hs, soc_quot_self]
  · exact (soc_quot_le_iff (soc_R_le_term hs (j + 1)) (soc_term_le_H hRH hs (j + 1))
      (soc_R_le_term hs j) (soc_term_le_H hRH hs j)).mpr (soc_term_succ_le hs hj)
  · have hj' : j + 1 < Ws.length := by omega
    have hj0 : j < Ws.length := by omega
    have hWj : socTerm R Ws j = Ws[j] := by simp [socTerm, hj0]
    have hWj1 : socTerm R Ws (j + 1) = Ws[j + 1] := by simp [socTerm, hj']
    have hnaW : ¬ ⁅Ws[j], Ws[j]⁆ ≤ Ws[j + 1] := by
      rw [← hWj, ← hWj1, ← soc_quot_comm_le_iff (soc_term_le_H hRH hs j)
        (soc_R_le_term hs (j + 1)) (soc_term_le_H hRH hs (j + 1))]
      exact hna
    set K := (M.comap π).map H.subtype
    have hKH : K ≤ H := Subgroup.map_subtype_le _
    have hRK : R ≤ K := by
      intro r hr
      refine ⟨⟨r, hRH hr⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have h0 : π ⟨r, hRH hr⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hr
      rw [h0]
      exact M.one_mem
    have hK_quot : socQuot H R K = M := by
      unfold socQuot
      have hsub : K.subgroupOf H = M.comap π :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
      rw [hsub]
      exact Subgroup.map_comap_eq_self_of_surjective hsurj M
    have hK1 : Ws[j + 1] ≤ K := by
      rw [← hWj1, ← soc_quot_le_iff (soc_R_le_term hs (j + 1)) (soc_term_le_H hRH hs (j + 1))
        hRK hKH, hK_quot]
      exact h1
    have hK2 : K ≤ Ws[j] := by
      rw [← hWj, ← soc_quot_le_iff hRK hKH (soc_R_le_term hs j) (soc_term_le_H hRH hs j),
        hK_quot]
      exact h2
    have hKn : ∀ g ∈ H, ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
      rintro g hg _ ⟨y, hy, rfl⟩
      have : (M.comap π).Normal := hM.comap π
      exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, (inferInstance : (M.comap π).Normal).conj_mem y hy ⟨g, hg⟩,
        rfl⟩
    rcases (hs.2.2.2 j hj').2 hnaW K hK1 hK2 hKn with hK | hK
    · left; rw [← hK_quot, hK, hWj1]
    · right; rw [← hK_quot, hK, hWj]

theorem soc_mul_comm_iff {Q : Type*} [Group Q] (a b : Q) :
    a * b = b * a ↔ b * a * b⁻¹ * a⁻¹ = 1 := by
  constructor
  · intro h
    rw [← h, mul_inv_cancel_right, mul_inv_cancel]
  · intro h
    have h1 := congrArg (· * (a * b)) h
    group at h1
    exact h1.symm

/-- For `R ≤ I ≤ H`, the subgroup `Z = {h ∈ H | ∀ u ∈ I, [h, u] ∈ R}` produced by
`gmpFactorKernelFuns` satisfies `R ≤ Z ≤ H`, `Normalizes H Z`, and
`socQuot H R Z = C_{H/R}(socQuot H R I)`. -/
theorem soc_factorKernel_props (hRH : R ≤ H) (hnR : GI.Multicoset.Normalizes H R)
    {I Z : Subgroup (Perm (Fin n))} (hIH : I ≤ H)
    (hnI : GI.Multicoset.Normalizes H I)
    (hZ : ∀ h, h ∈ Z ↔ h ∈ H ∧ ∀ u ∈ I, h * u * h⁻¹ * u⁻¹ ∈ R) :
    R ≤ Z ∧ Z ≤ H ∧ GI.Multicoset.Normalizes H Z ∧
      socQuot H R Z = Subgroup.centralizer (socQuot H R I : Set (H ⧸ R.subgroupOf H)) := by
  have hRZ : R ≤ Z := by
    intro r hr
    rw [hZ]
    refine ⟨hRH hr, fun u hu => ?_⟩
    have hu' : u * r⁻¹ * u⁻¹ ∈ R := hnR u (hIH hu) r⁻¹ (R.inv_mem hr)
    simpa [mul_assoc] using R.mul_mem hr hu'
  have hZH : Z ≤ H := fun h hh => ((hZ h).mp hh).1
  have hnZ : GI.Multicoset.Normalizes H Z := by
    intro g hg y hy
    rw [hZ] at hy ⊢
    refine ⟨H.mul_mem (H.mul_mem hg hy.1) (H.inv_mem hg), fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ I := hnI g⁻¹ (H.inv_mem hg) x hx
    have h1 := hnR g hg _ (hy.2 _ hx')
    convert h1 using 1
    group
  refine ⟨hRZ, hZH, hnZ, ?_⟩
  ext q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf H) q
  rw [soc_mem_quot_iff hRZ hZH hRH y, hZ, Subgroup.mem_centralizer_iff]
  refine ⟨fun ⟨_, hy⟩ z hz => ?_, fun hy => ⟨y.2, fun u hu => ?_⟩⟩
  · obtain ⟨x, hx, rfl⟩ := hz
    rw [soc_mul_comm_iff]
    change QuotientGroup.mk' (R.subgroupOf H) (y * x * y⁻¹ * x⁻¹) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hy (x : Perm (Fin n)) hx)
  · have hx : QuotientGroup.mk' (R.subgroupOf H) ⟨u, hIH hu⟩ ∈ socQuot H R I :=
      ⟨⟨u, hIH hu⟩, hu, rfl⟩
    have hcomm := (soc_mul_comm_iff _ _).mp (hy _ hx)
    set z : H := y * ⟨u, hIH hu⟩ * y⁻¹ * ⟨u, hIH hu⟩⁻¹
    change QuotientGroup.mk' (R.subgroupOf H) z = 1 at hcomm
    exact (QuotientGroup.eq_one_iff z).mp hcomm

/-- Index of `R` in `I` (`R ≤ I ≤ H`) equals `|socQuot H R I|`. -/
theorem soc_index_eq_card_quot {I : Subgroup (Perm (Fin n))} (hIH : I ≤ H) :
    (R.subgroupOf I).index = Nat.card (socQuot H R I) := by
  let f : I →* H ⧸ R.subgroupOf H :=
    (QuotientGroup.mk' (R.subgroupOf H)).comp (Subgroup.inclusion hIH)
  have hrange : f.range = socQuot H R I := by
    ext z
    simp only [MonoidHom.mem_range, socQuot, Subgroup.mem_map, Subgroup.mem_subgroupOf, f,
      MonoidHom.comp_apply]
    exact ⟨fun ⟨⟨x, hx⟩, h⟩ => ⟨⟨x, hIH hx⟩, hx, h⟩,
      fun ⟨⟨x, _⟩, hxI, h⟩ => ⟨⟨x, hxI⟩, h⟩⟩
  have hker : f.ker = R.subgroupOf I := by
    ext ⟨x, hx⟩
    exact QuotientGroup.eq_one_iff (Subgroup.inclusion hIH ⟨x, hx⟩)
  have h := Subgroup.index_ker f
  rw [hrange, hker] at h
  exact h

/-- Main step lemma in `Sym(n)`: if `H / R` is radical-free, `Ws` is a nonabelian-chief chain from
`H` to `R`, `C` and `E` satisfy the loop invariant (`socQuot H R C = C_{H/R}(socQuot H R E)` and
`E ≤ soclePreimage H R`), `j < Ws.length - 1` has `¬ (socTerm R Ws j ⊓ C ≤ R)` and
`socTerm R Ws (j + 1) ⊓ C ≤ R`, and `Z = {h ∈ H | ∀ u ∈ socTerm R Ws j ⊓ C, [h, u] ∈ R}`,
then:
1. `I = socTerm R Ws j ⊓ C ≤ soclePreimage H R`,
2. `(R.subgroupOf I).index ≤ (R.subgroupOf (soclePreimage H R)).index`,
3. `E ⊔ I ≤ soclePreimage H R`,
4. `socQuot H R (C ⊓ Z) = C_{H/R}(socQuot H R (E ⊔ I))`,
5. `2 * Nat.card (C ⊓ Z) ≤ Nat.card C`. -/
theorem soc_round_step_math (hRH : R ≤ H) (hnR : GI.Multicoset.Normalizes H R)
    (hrf : ∀ N : Subgroup (H ⧸ R.subgroupOf H), N.Normal → Group.IsSolvable N → N = ⊥)
    {Ws : List (Subgroup (Perm (Fin n)))} (hs : SocChain H R Ws)
    {C E Z : Subgroup (Perm (Fin n))}
    (hRC : R ≤ C) (hCH : C ≤ H) (hnC : GI.Multicoset.Normalizes H C)
    (hES : E ≤ soclePreimage H R)
    (hCE : socQuot H R C = Subgroup.centralizer (socQuot H R E : Set (H ⧸ R.subgroupOf H)))
    {j : ℕ} (hj : j < Ws.length - 1)
    (hI_not_le : ¬ (socTerm R Ws j ⊓ C ≤ R))
    (hnext_le : socTerm R Ws (j + 1) ⊓ C ≤ R)
    (hZ : ∀ h, h ∈ Z ↔ h ∈ H ∧ ∀ u ∈ socTerm R Ws j ⊓ C, h * u * h⁻¹ * u⁻¹ ∈ R) :
    let I := socTerm R Ws j ⊓ C
    I ≤ soclePreimage H R ∧
    (R.subgroupOf I).index ≤ (R.subgroupOf (soclePreimage H R)).index ∧
    E ⊔ I ≤ soclePreimage H R ∧
    socQuot H R (C ⊓ Z) =
      Subgroup.centralizer (socQuot H R (E ⊔ I) : Set (H ⧸ R.subgroupOf H)) ∧
    2 * Nat.card (C ⊓ Z : Subgroup (Perm (Fin n))) ≤ Nat.card C := by
  intro I
  have ht := soc_quot_chain hRH hnR hs
  have : (socQuot H R C).Normal := soc_quot_normal hnC
  have hRWj := soc_R_le_term hs j
  have hWjH := soc_term_le_H hRH hs j
  have hRWj1 := soc_R_le_term hs (j + 1)
  have hWj1H := soc_term_le_H hRH hs (j + 1)
  have hRI : R ≤ I := le_inf hRWj hRC
  have hIH : I ≤ H := inf_le_right.trans hCH
  have hnI : GI.Multicoset.Normalizes H I :=
    fun g hg x ⟨hx1, hx2⟩ => ⟨soc_term_normalized hnR hs j g hg x hx1, hnC g hg x hx2⟩
  have hI_quot : socQuot H R I = socQuot H R (socTerm R Ws j) ⊓ socQuot H R C :=
    soc_quot_inf hRWj hWjH hRC hCH
  have hI_ne : socQuot H R (socTerm R Ws j) ⊓ socQuot H R C ≠ ⊥ := by
    rw [← hI_quot, ne_eq, soc_quot_eq_bot_iff hRI hIH]
    exact hI_not_le
  have hnext_bot : socQuot H R (socTerm R Ws (j + 1)) ⊓ socQuot H R C = ⊥ := by
    rw [← soc_quot_inf hRWj1 hWj1H hRC hCH,
      soc_quot_eq_bot_iff (le_inf hRWj1 hRC) (inf_le_right.trans hCH)]
    exact hnext_le
  have hI_soc_quot : socQuot H R I ≤ socle (H ⧸ R.subgroupOf H) := by
    rw [hI_quot]
    exact soc_quot_le_socle hrf ht hj hI_ne hnext_bot
  have hI_soc : I ≤ soclePreimage H R := by
    rw [← soc_quot_soclePreimage (H := H) (R := R),
      soc_quot_le_iff hRI hIH (le_soclePreimage hRH) (soclePreimage_le H R)] at hI_soc_quot
    exact hI_soc_quot
  have hidx_le : (R.subgroupOf I).index ≤ (R.subgroupOf (soclePreimage H R)).index := by
    rw [soc_index_eq_card_quot hIH, soc_index_eq_card_quot (soclePreimage_le H R)]
    exact Subgroup.card_le_of_le (by rwa [soc_quot_soclePreimage])
  obtain ⟨hRZ, hZH, hnZ, hZ_quot⟩ := soc_factorKernel_props hRH hnR hIH hnI hZ
  have hCZ_quot : socQuot H R (C ⊓ Z) =
      Subgroup.centralizer (socQuot H R (E ⊔ I) : Set (H ⧸ R.subgroupOf H)) := by
    rw [soc_quot_inf hRC hCH hRZ hZH, soc_quot_sup (hES.trans (soclePreimage_le H R)) hIH,
      soc_quot_centralizer_sup, hCE, hZ_quot]
  have hlt : C ⊓ Z < C := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hIZ_le : I ≤ I ⊓ Z := le_inf le_rfl (inf_le_right.trans (heq ▸ inf_le_right))
    have : (socQuot H R I).Normal := soc_quot_normal hnI
    have hbot := soc_quot_inf_centralizer_eq_bot hrf (socQuot H R I)
    rw [← hZ_quot, ← soc_quot_inf hRI hIH hRZ hZH] at hbot
    have hI_bot : socQuot H R I ≤ ⊥ := by
      rw [← hbot]
      exact (soc_quot_le_iff hRI hIH (le_inf hRI hRZ) (inf_le_left.trans hIH)).mpr hIZ_le
    exact hI_ne (hI_quot ▸ le_bot_iff.mp hI_bot)
  exact ⟨hI_soc, hidx_le, sup_le hES hI_soc, hCZ_quot,
    GI.CitedChecks.two_mul_card_le_of_lt hlt⟩

/-- Termination lemma in `Sym(n)`: when `C ≤ R`, `R ≤ E ≤ soclePreimage H R`,
`Normalizes H E`, and `socQuot H R C = C_{H/R}(socQuot H R E)`, we have
`E = soclePreimage H R`. -/
theorem soc_eq_soclePreimage_of_le (hRH : R ≤ H)
    {C E : Subgroup (Perm (Fin n))} (hRC : R ≤ C) (hCR : C ≤ R)
    (hRE : R ≤ E) (hES : E ≤ soclePreimage H R) (hnE : GI.Multicoset.Normalizes H E)
    (hCE : socQuot H R C = Subgroup.centralizer (socQuot H R E : Set (H ⧸ R.subgroupOf H))) :
    E = soclePreimage H R := by
  have : (socQuot H R E).Normal := soc_quot_normal hnE
  have hEH : E ≤ H := hES.trans (soclePreimage_le H R)
  have hC_bot : socQuot H R C = ⊥ := (soc_quot_eq_bot_iff hRC (hCR.trans hRH)).mpr hCR
  have hE_soc_quot : socQuot H R E ≤ socle (H ⧸ R.subgroupOf H) := by
    rw [← soc_quot_soclePreimage]
    exact (soc_quot_le_iff hRE hEH (le_soclePreimage hRH) (soclePreimage_le H R)).mpr hES
  have heq := soc_quot_eq_socle_of_centralizer_eq_bot hE_soc_quot (hCE.symm.trans hC_bot)
  rw [← soc_quot_soclePreimage] at heq
  exact (soc_quot_eq_iff hRE hEH (le_soclePreimage hRH) (soclePreimage_le H R)).mp heq

/-- Convenience lemma: if `radicalPreimage H R = R`, then `H / R` is radical-free. -/
theorem soc_radicalFree_of_radicalPreimage_eq
    (h : GI.Multicoset.radicalPreimage H R = R) :
    ∀ N : Subgroup (H ⧸ R.subgroupOf H), N.Normal → Group.IsSolvable N → N = ⊥ := by
  have hrf := radicalPreimage_quotient_radicalFree (H := H) (N := R)
  intro N hN hsolv
  let e := QuotientGroup.congr (R.subgroupOf H)
    ((GI.Multicoset.radicalPreimage H R).subgroupOf H) (MulEquiv.refl H)
    (by ext x; simp [h])
  have hN' : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map hN _ e.surjective
  have hs' : Group.IsSolvable (N.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective N)
  have hbot := hrf (N.map e.toMonoidHom) hN' hs'
  rw [eq_bot_iff] at hbot ⊢
  intro x hx
  have hx' : e x ∈ N.map e.toMonoidHom := ⟨x, hx, rfl⟩
  rw [Subgroup.mem_bot] at *
  exact (MulEquiv.map_eq_one_iff e).mp (hbot hx')

/-! ### Part 4: Loop invariants for the scan and outer loops -/

/-- Invariant of the inner scan loop after `j` steps on a chain `Ws` and current centralizer `C`:
either `j = 0` and `I = C`, or `I = socTerm R Ws k ⊓ C` for the largest `k < j` with
`¬ (socTerm R Ws k ⊓ C ≤ R)`. -/
def SocScanInv (R : Subgroup (Perm (Fin n))) (Ws : List (Subgroup (Perm (Fin n))))
    (C : Subgroup (Perm (Fin n))) (j : ℕ) (I : Subgroup (Perm (Fin n))) : Prop :=
  (j = 0 ∧ I = C) ∨
  ∃ k < j, I = socTerm R Ws k ⊓ C ∧ ¬ (socTerm R Ws k ⊓ C ≤ R) ∧
    ∀ m, k < m → m < j → socTerm R Ws m ⊓ C ≤ R

theorem soc_scan_init {Ws : List (Subgroup (Perm (Fin n)))} {C : Subgroup (Perm (Fin n))} :
    SocScanInv R Ws C 0 C :=
  Or.inl ⟨rfl, rfl⟩

theorem soc_scan_step_false {Ws : List (Subgroup (Perm (Fin n)))} {C : Subgroup (Perm (Fin n))}
    {j : ℕ} (hnot : ¬ (socTerm R Ws j ⊓ C ≤ R)) :
    SocScanInv R Ws C (j + 1) (socTerm R Ws j ⊓ C) :=
  Or.inr ⟨j, Nat.lt_succ_self j, rfl, hnot, fun _ hjm hmj1 => by omega⟩

omit [(R.subgroupOf H).Normal] in
theorem soc_scan_step_true {Ws : List (Subgroup (Perm (Fin n)))} (hs : SocChain H R Ws)
    {C I : Subgroup (Perm (Fin n))} (hCH : C ≤ H) (hCR : ¬ (C ≤ R))
    {j : ℕ} (hinv : SocScanInv R Ws C j I) (hle : socTerm R Ws j ⊓ C ≤ R) :
    SocScanInv R Ws C (j + 1) I := by
  rcases hinv with ⟨rfl, rfl⟩ | ⟨k, hkj, hI, hnot, hafter⟩
  · exfalso
    rw [soc_term_zero hs, inf_of_le_right hCH] at hle
    exact hCR hle
  · refine Or.inr ⟨k, Nat.lt_succ_of_lt hkj, hI, hnot, fun m hkm hmj1 => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hmj1) with hmj | rfl
    · exact hafter m hkm hmj
    · exact hle

omit [(R.subgroupOf H).Normal] in
theorem soc_scan_done {Ws : List (Subgroup (Perm (Fin n)))} (hs : SocChain H R Ws)
    {C I : Subgroup (Perm (Fin n))} (hCH : C ≤ H) (hCR : ¬ (C ≤ R))
    (hinv : SocScanInv R Ws C (Ws.length - 1) I) :
    ∃ k < Ws.length - 1, I = socTerm R Ws k ⊓ C ∧
      ¬ (socTerm R Ws k ⊓ C ≤ R) ∧ socTerm R Ws (k + 1) ⊓ C ≤ R := by
  rcases hinv with ⟨h0, _⟩ | ⟨k, hk, hI, hnot, hafter⟩
  · exfalso
    have hHR : H = R := by
      calc H = socTerm R Ws 0 := (soc_term_zero hs).symm
        _ = socTerm R Ws (Ws.length - 1) := by rw [h0]
        _ = R := soc_term_last hs
    exact hCR (hHR ▸ hCH)
  · refine ⟨k, hk, hI, hnot, ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hk) with hk1 | hk1
    · exact hafter (k + 1) (Nat.lt_succ_self k) hk1
    · change k + 1 = Ws.length - 1 at hk1
      rw [hk1, soc_term_last hs]
      exact inf_le_left

/-- Invariant of the outer round loop after `i` rounds on `(C, E)`. -/
def SocRoundInv (H R : Subgroup (Perm (Fin n))) [(R.subgroupOf H).Normal]
    (i : ℕ) (C E : Subgroup (Perm (Fin n))) : Prop :=
  R ≤ C ∧ C ≤ H ∧ GI.Multicoset.Normalizes H C ∧
  R ≤ E ∧ E ≤ soclePreimage H R ∧ GI.Multicoset.Normalizes H E ∧
  socQuot H R C = Subgroup.centralizer (socQuot H R E : Set (H ⧸ R.subgroupOf H)) ∧
  (C ≤ R ∨ 2 ^ i * Nat.card C ≤ Nat.card H)

theorem soc_round_init (hRH : R ≤ H) (hnR : GI.Multicoset.Normalizes H R) :
    SocRoundInv H R 0 H R := by
  refine ⟨hRH, le_rfl, fun g hg x hx => H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg),
    le_rfl, le_soclePreimage hRH, hnR, ?_, Or.inr (by simp)⟩
  rw [soc_quot_top, soc_quot_self, eq_comm, eq_top_iff]
  intro x _
  rw [Subgroup.mem_centralizer_iff]
  rintro y (rfl : y = 1)
  simp

theorem soc_round_done (hRH : R ≤ H) {C E : Subgroup (Perm (Fin n))}
    (h : SocRoundInv H R (n ^ 2 + 1) C E) :
    E = soclePreimage H R := by
  obtain ⟨hRC, _, _, hRE, hES, hnE, hCE, hCR | hcard⟩ := h
  · exact soc_eq_soclePreimage_of_le hRH hRC hCR hRE hES hnE hCE
  · exfalso
    have h1 := GI.CitedChecks.card_lt_two_pow H
    have h2 : 0 < Nat.card C := Nat.card_pos
    have : 2 ^ (n ^ 2 + 1) ≤ 2 ^ (n ^ 2 + 1) * Nat.card C :=
      Nat.le_mul_of_pos_right _ h2
    omega

end PermChain

end GI.Impl
