import Workspace.CertificateLockstep
import Workspace.LocalPermFamilies

/-!
# Ordered comparisons of local certificates

Paper, Appendix A, `sec:certificates`, "Ordered comparisons and equivariance".

Let `G ≤ Sym(Ω)` with `π : G → Alt(Γ)`. A test is an ordered tuple
`t : Fin k → Γ` with underlying set `T = tset t`. The endpoint procedure of
`(x, T)` runs with `P_T` and `φ_T` (`GI.LocalGroups.phiT`); its final window is
`W(x, T)` (`finalWin`), which depends on `T` only.

For two endpoints `(x, t)` and `(y, t')`, eq. `comparison` is the set of `g ∈ G`
with `π(g) t = t'` that transport the marked final windows,
`Iso_{J_T τ}(x^{W(x,T)}, y^{W(y,T')})` (`comparison`). The lockstep coset at
stage `j` (`lockstep`) uses the stage-`j` windows instead.

Proved here:

* `lockstep_eq_coset`: a nonempty lockstep set is a coset of
  `Aut_{J_T}(x^{W_j}) = A_j ∩ J_T = N_j` (`automorphisms_J_eq`).
* `comparison_lockstep`: "An empty partial comparison cannot revive": a member of
  the comparison set lies in every earlier lockstep coset and conjugates every
  earlier endpoint group; the stopping tests agree (`comparison_isFull_iff`).
* `comparison_refl`, `comparison_inv`, `comparison_mul`, `compareRel_equivalence`:
  nonemptiness is an equivalence relation.
* `comparison_of_iso`: parent isomorphisms preserve the comparison classes, and
  the certificates (`certificate_of_iso`).
* `tupleRel`: the extension to noninjective tuples by equality patterns; it is an
  equivalence relation, preserved by parent isomorphisms.
* `no_large_twin`: for a nonfull `T`, some ordering of `T` has a color different
  from a given ordering.
* `nonfull_Q`: at nonfull termination, `Aut_{Q_T}(x)` does not induce `Alt(T)`.

The paper's right-action coset `J_T τ` is written with left multiplication here,
as in `Workspace/Transport.lean`.
-/

namespace GI.LocalCertificates

open Equiv Equiv.Perm GI.Endpoint GI.LocalGroups

variable {Ω Γ C : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ) {k : ℕ}

/-- The underlying set `T` of a test tuple. -/
def tset (t : Fin k → Γ) : Finset Γ := Finset.univ.image t

/-- The lockstep comparison set at stage `j`. -/
def lockstep (j : ℕ) (x : Ω → C) (t : Fin k → Γ) (y : Ω → C) (t' : Fin k → Γ) :
    Set (Perm Ω) :=
  {g | g ∈ G ∧ (∀ i, lab G π g (t i) = t' i) ∧
    Transports (mask x (win (phiT G π (tset t)) x j))
      (mask y (win (phiT G π (tset t')) y j)) g}

/-- **The ordered comparison**, eq. `comparison`:
`Iso_{J_T τ}(x^{W(x,T)}, y^{W(y,T')})`, the full ordered-tuple transporter of the
marked final windows. -/
def comparison (x : Ω → C) (t : Fin k → Γ) (y : Ω → C) (t' : Fin k → Γ) : Set (Perm Ω) :=
  lockstep G π (Fintype.card Ω) x t y t'

variable {G π}

omit [Fintype Ω] [DecidableEq Ω] in
theorem tset_lab {g : Perm Ω} {t t' : Fin k → Γ} (h : ∀ i, lab G π g (t i) = t' i) :
    tset t' = wmap (lab G π g) (tset t) := by
  ext c
  simp only [tset, Finset.mem_image, Finset.mem_univ, true_and, mem_wmap]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by rw [← h i]; simp⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← h i, hi]; simp⟩

omit [Fintype Γ] in
theorem mem_tset {t : Fin k → Γ} {c : Γ} : c ∈ tset t ↔ ∃ i, t i = c := by
  simp [tset]

/-- `Aut_{J_T}(x^{W_j}) = A_j ∩ J_T = N_j`. -/
theorem automorphisms_J_eq (x : Ω → C) (T : Finset Γ) (j : ℕ) :
    automorphisms (Jgrp G π T) (mask x (win (phiT G π T) x j)) =
        grp (phiT G π T) x j ⊓ Jgrp G π T ∧
      grp (phiT G π T) x j ⊓ Jgrp G π T = kernelIn (phiT G π T) (grp (phiT G π T) x j) := by
  refine ⟨?_, ?_⟩
  · rw [grp_eq_automorphisms_mask]
    ext g
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hJ, htr⟩
      exact ⟨⟨Jgrp_le_Pgrp hJ, htr⟩, hJ⟩
    · rintro ⟨⟨_, htr⟩, hJ⟩
      exact ⟨hJ, htr⟩
  · rw [kernelIn, phiT_ker]

/-- A nonempty lockstep set is a coset `g₀ · Aut_{J_T}(x^{W_j})`. -/
theorem lockstep_eq_coset {j : ℕ} {x y : Ω → C} {t t' : Fin k → Γ} {g₀ : Perm Ω}
    (hg₀ : g₀ ∈ lockstep G π j x t y t') :
    lockstep G π j x t y t' =
      {g | ∃ a ∈ automorphisms (Jgrp G π (tset t)) (mask x (win (phiT G π (tset t)) x j)),
        g = g₀ * a} := by
  obtain ⟨hg₀G, hg₀l, hg₀t⟩ := hg₀
  ext g
  constructor
  · rintro ⟨hgG, hgl, hgt⟩
    refine ⟨g₀⁻¹ * g, ⟨⟨G.mul_mem (G.inv_mem hg₀G) hgG, fun c hc => ?_⟩,
      hgt.comp hg₀t.inv⟩, by simp⟩
    obtain ⟨i, rfl⟩ := mem_tset.1 hc
    rw [lab_mul (G.inv_mem hg₀G) hgG, lab_inv hg₀G, Perm.mul_apply, hgl i, ← hg₀l i]
    simp
  · rintro ⟨a, ⟨⟨haG, hal⟩, hat⟩, rfl⟩
    refine ⟨G.mul_mem hg₀G haG, fun i => ?_, hat.comp hg₀t⟩
    rw [lab_mul hg₀G haG, Perm.mul_apply, hal _ (mem_tset.2 ⟨i, rfl⟩), hg₀l i]

/-- **An empty partial comparison cannot revive.** A member `g` of the final
comparison set lies in every earlier lockstep coset, and conjugates each endpoint
group `A_j(x, T)` to `A_j(y, T')` and maps each window `W_j(x, T)` to
`W_j(y, T')`. -/
theorem comparison_lockstep {x y : Ω → C} {t t' : Fin k → Γ} {g : Perm Ω}
    (hg : g ∈ comparison G π x t y t') :
    ∀ j ≤ Fintype.card Ω, g ∈ lockstep G π j x t y t' ∧
      grp (phiT G π (tset t')) y j = cmap g (grp (phiT G π (tset t)) x j) ∧
      win (phiT G π (tset t')) y j = wmap g (win (phiT G π (tset t)) x j) := by
  obtain ⟨hgG, hgl, hgt⟩ := hg
  have hT := tset_lab hgl
  intro j hj
  have key := lockstep_of_transports (compat (T := tset t) hgG) (by rw [← hT]; exact hgt) j hj
  rw [← hT] at key
  exact ⟨⟨hgG, hgl, key.2.2⟩, key.1, key.2.1⟩

/-- **Every representative conjugates.** A member `g` of the lockstep coset at
stage `j` conjugates `A_i(x, T)` to `A_i(y, T')` and maps `W_i(x, T)` to
`W_i(y, T')` for every `i ≤ j`; it maps the increment `V_j` (the affected set or
the extra orbit union) to `V'_j`, and the stopping tests at stage `j` agree. -/
theorem lockstep_conj {j : ℕ} {x y : Ω → C} {t t' : Fin k → Γ} {g : Perm Ω}
    (hg : g ∈ lockstep G π j x t y t') :
    (∀ i ≤ j, grp (phiT G π (tset t')) y i = cmap g (grp (phiT G π (tset t)) x i) ∧
      win (phiT G π (tset t')) y i = wmap g (win (phiT G π (tset t)) x i)) ∧
    inc (phiT G π (tset t')) y j = wmap g (inc (phiT G π (tset t)) x j) ∧
    (Stopped (phiT G π (tset t')) (grp (phiT G π (tset t')) y j)
        (win (phiT G π (tset t')) y j) ↔
      Stopped (phiT G π (tset t)) (grp (phiT G π (tset t)) x j)
        (win (phiT G π (tset t)) x j)) := by
  obtain ⟨hgG, hgl, hgt⟩ := hg
  have hT := tset_lab hgl
  have hc := compat (G := G) (π := π) (T := tset t) hgG
  rw [hT] at hgt ⊢
  have key := lockstep_of_transports hc hgt
  obtain ⟨hA, hW, _⟩ := key j le_rfl
  refine ⟨fun i hi => ⟨(key i hi).1, (key i hi).2.1⟩, ?_, stopped_iff_of_lockstep hc hA hW⟩
  simp only [inc]
  rw [hA, hW, hc.increment_cmap]

/-- **The next comparison is string isomorphism on the new window.** The lockstep
coset at stage `j + 1` consists of the members of the stage-`j` coset that agree
with the two strings on the new window `V_j`. -/
theorem lockstep_succ (j : ℕ) (x y : Ω → C) (t t' : Fin k → Γ) :
    lockstep G π (j + 1) x t y t' =
      {g | g ∈ lockstep G π j x t y t' ∧
        ∀ v ∈ inc (phiT G π (tset t)) x j, y (g v) = x v} := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgG, hgl, hgt⟩ := hg
    have hT := tset_lab hgl
    have hc := compat (G := G) (π := π) (T := tset t) hgG
    have hgt' := hgt
    rw [hT] at hgt'
    obtain ⟨_, _, htj⟩ := lockstep_of_transports hc hgt' j (Nat.le_succ j)
    rw [← hT] at htj
    have hxy := ((transports_mask_iff _ _ _ _ _).1 hgt).2
    refine ⟨⟨hgG, hgl, htj⟩, fun v hv => hxy v ?_⟩
    rw [win_succ]
    exact Finset.mem_union_right _ hv
  · rintro ⟨hg, hnew⟩
    obtain ⟨hA, hinc, -⟩ := lockstep_conj hg
    obtain ⟨hgG, hgl, hgt⟩ := hg
    refine ⟨hgG, hgl, ?_⟩
    rw [transports_mask_iff, win_succ, win_succ, hinc, (hA j le_rfl).2]
    have hold := ((transports_mask_iff _ _ _ _ _).1 hgt).2
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [Finset.mem_union, Finset.mem_union, apply_mem_wmap, apply_mem_wmap]
    · rcases Finset.mem_union.1 hv with hv | hv
      · exact hold v hv
      · exact hnew v hv

/-- Incompatible stopping stages give an empty comparison: along a member of the
comparison set, the stopping tests and the final full test agree. -/
theorem comparison_isFull_iff {x y : Ω → C} {t t' : Fin k → Γ} {g : Perm Ω}
    (hg : g ∈ comparison G π x t y t') :
    (IsFull (phiT G π (tset t')) y ↔ IsFull (phiT G π (tset t)) x) ∧
    ∀ j ≤ Fintype.card Ω,
      (Stopped (phiT G π (tset t')) (grp (phiT G π (tset t')) y j)
          (win (phiT G π (tset t')) y j) ↔
        Stopped (phiT G π (tset t)) (grp (phiT G π (tset t)) x j)
          (win (phiT G π (tset t)) x j)) := by
  have hgG := hg.1
  have hT := tset_lab hg.2.1
  have hl := comparison_lockstep hg
  have hc := compat (G := G) (π := π) (T := tset t) hgG
  rw [hT] at hl ⊢
  refine ⟨?_, fun j hj => ?_⟩
  · obtain ⟨_, hA, _⟩ := hl _ le_rfl
    exact full_iff_of_lockstep hc hA
  · obtain ⟨_, hA, hW⟩ := hl j hj
    exact stopped_iff_of_lockstep hc hA hW

/-! ### Comparison is an equivalence relation -/

theorem comparison_refl (x : Ω → C) (t : Fin k → Γ) : (1 : Perm Ω) ∈ comparison G π x t x t :=
  ⟨G.one_mem, fun i => by rw [lab_one]; rfl, transports_one _⟩

theorem comparison_inv {x y : Ω → C} {t t' : Fin k → Γ} {g : Perm Ω}
    (hg : g ∈ comparison G π x t y t') : g⁻¹ ∈ comparison G π y t' x t := by
  obtain ⟨hgG, hgl, hgt⟩ := hg
  refine ⟨G.inv_mem hgG, fun i => ?_, hgt.inv⟩
  rw [lab_inv hgG, ← hgl i]
  simp

theorem comparison_mul {x y z : Ω → C} {t t' t'' : Fin k → Γ} {g h : Perm Ω}
    (hg : g ∈ comparison G π x t y t') (hh : h ∈ comparison G π y t' z t'') :
    h * g ∈ comparison G π x t z t'' := by
  obtain ⟨hgG, hgl, hgt⟩ := hg
  obtain ⟨hhG, hhl, hht⟩ := hh
  refine ⟨G.mul_mem hhG hgG, fun i => ?_, hgt.comp hht⟩
  rw [lab_mul hhG hgG, Perm.mul_apply, hgl i, hhl i]

/-- Nonemptiness of the comparison set. -/
def CompareRel (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ) (k : ℕ) :
    (Ω → C) × (Fin k → Γ) → (Ω → C) × (Fin k → Γ) → Prop :=
  fun a b => (comparison G π a.1 a.2 b.1 b.2).Nonempty

/-- "Full transporter composition and inversion make nonemptiness in
(comparison) a genuine equivalence relation." -/
theorem compareRel_equivalence : Equivalence (CompareRel (C := C) G π k) where
  refl a := ⟨1, comparison_refl a.1 a.2⟩
  symm := fun ⟨g, hg⟩ => ⟨g⁻¹, comparison_inv hg⟩
  trans := fun ⟨g, hg⟩ ⟨h, hh⟩ => ⟨h * g, comparison_mul hg hh⟩

/-! ### Parent isomorphisms -/

/-- **Equivariance of the certificates.** A parent isomorphism `g ∈ G`, `x^g = y`,
carries the endpoint procedure of `(x, T)` to that of `(y, T^{π(g)})` at every
stage: the groups are conjugated, the windows mapped, and the full tests agree. -/
theorem certificate_of_iso {x y : Ω → C} {g : Perm Ω} (hgG : g ∈ G) (hxy : Transports x y g)
    (T : Finset Γ) (j : ℕ) :
    grp (phiT G π (wmap (lab G π g) T)) y j = cmap g (grp (phiT G π T) x j) ∧
    win (phiT G π (wmap (lab G π g) T)) y j = wmap g (win (phiT G π T) x j) ∧
    (Full (phiT G π (wmap (lab G π g) T)) (grp (phiT G π (wmap (lab G π g) T)) y j) ↔
      Full (phiT G π T) (grp (phiT G π T) x j)) := by
  have hc := compat (G := G) (π := π) (T := T) hgG
  obtain ⟨hA, hW⟩ := stage_cmap_of_transports hc hxy j
  exact ⟨hA, hW, full_iff_of_lockstep hc hA⟩

/-- Parent isomorphisms map the full certificate `K(T)` to `K(T^{π(g)})`. -/
theorem fullCert_of_iso {x y : Ω → C} {g : Perm Ω} (hgG : g ∈ G) (hxy : Transports x y g)
    (T : Finset Γ) :
    fullCert (phiT G π (wmap (lab G π g) T)) y = cmap g (fullCert (phiT G π T) x) := by
  obtain ⟨hA, hW, _⟩ := certificate_of_iso hgG hxy T (Fintype.card Ω)
  simp only [fullCert, finalGrp, finalWin]
  rw [hA, hW, outside_wmap, fix_cmap]

/-- **Equivariance of the comparison classes.** A parent isomorphism `g` lies in
the comparison set of `(x, t)` and `(y, π(g) t)`. -/
theorem comparison_of_iso {x y : Ω → C} {g : Perm Ω} (hgG : g ∈ G) (hxy : Transports x y g)
    (t : Fin k → Γ) : g ∈ comparison G π x t y (fun i => lab G π g (t i)) := by
  refine ⟨hgG, fun _ => rfl, ?_⟩
  have hT : tset (fun i => lab G π g (t i)) = wmap (lab G π g) (tset t) := tset_lab (fun _ => rfl)
  rw [hT, transports_mask_iff, (certificate_of_iso hgG hxy (tset t) _).2.1]
  exact ⟨fun v => apply_mem_wmap, fun v _ => hxy v⟩

/-! ### Noninjective tuples -/

/-- The tuple coloring relation on all of `Γ^k`: injective tuples are related by
nonempty comparison; noninjective tuples by equal equality patterns; an injective
tuple is never related to a noninjective one (disjoint palettes). -/
def tupleRel (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ) (k : ℕ)
    (a b : (Ω → C) × (Fin k → Γ)) : Prop :=
  (Function.Injective a.2 ∧ Function.Injective b.2 ∧ CompareRel G π k a b) ∨
  (¬ Function.Injective a.2 ∧ ¬ Function.Injective b.2 ∧
    ∀ i j, a.2 i = a.2 j ↔ b.2 i = b.2 j)

theorem tupleRel_equivalence : Equivalence (tupleRel (C := C) G π k) where
  refl a := by
    by_cases h : Function.Injective a.2
    · exact Or.inl ⟨h, h, (compareRel_equivalence).refl a⟩
    · exact Or.inr ⟨h, h, fun _ _ => Iff.rfl⟩
  symm := by
    rintro a b (⟨ha, hb, hr⟩ | ⟨ha, hb, hp⟩)
    · exact Or.inl ⟨hb, ha, (compareRel_equivalence).symm hr⟩
    · exact Or.inr ⟨hb, ha, fun i j => (hp i j).symm⟩
  trans := by
    rintro a b c (⟨ha, hb, hr⟩ | ⟨ha, hb, hp⟩) (⟨hb', hc, hr'⟩ | ⟨hb', hc, hp'⟩)
    · exact Or.inl ⟨ha, hc, (compareRel_equivalence).trans hr hr'⟩
    · exact absurd hb hb'
    · exact absurd hb' hb
    · exact Or.inr ⟨ha, hc, fun i j => (hp i j).trans (hp' i j)⟩

/-- The extended coloring is preserved by parent isomorphisms. -/
theorem tupleRel_of_iso {x y : Ω → C} {g : Perm Ω} (hgG : g ∈ G) (hxy : Transports x y g)
    (t : Fin k → Γ) : tupleRel G π k (x, t) (y, fun i => lab G π g (t i)) := by
  have hinj : Function.Injective (fun i => lab G π g (t i)) ↔ Function.Injective t :=
    ⟨fun h => fun i j hij => h (by simp only [hij]),
      fun h => (lab G π g).injective.comp h⟩
  by_cases ht : Function.Injective t
  · exact Or.inl ⟨ht, hinj.2 ht, ⟨g, comparison_of_iso hgG hxy t⟩⟩
  · refine Or.inr ⟨ht, fun h => ht (hinj.1 h), fun i j => ?_⟩
    exact ((lab G π g).injective.eq_iff).symm

/-! ### No large twins and the nonfull obstruction -/

/-- **No large twin.** If the certificate of `T` is nonfull, then for every
ordering `t₀` of `T` some other ordering `t₁` of `T` has an empty comparison with
it. (Otherwise the transporters would realize all of `Sym(T)` on the final marked
window, and the even part would force `φ_T(A_final) = Alt(T)`.) -/
theorem no_large_twin {x : Ω → C} {t₀ : Fin k → Γ} (ht₀ : Function.Injective t₀)
    (hnf : ¬ IsFull (phiT G π (tset t₀)) x) :
    ∃ t₁ : Fin k → Γ, Function.Injective t₁ ∧ tset t₁ = tset t₀ ∧
      ¬ (comparison G π x t₀ x t₁).Nonempty := by
  by_contra hall
  push Not at hall
  apply hnf
  set T := tset t₀ with hTdef
  rw [IsFull, Full, eq_top_iff]
  intro σ _
  have hmem : ∀ i, t₀ i ∈ T := fun i => mem_tset.2 ⟨i, rfl⟩
  let t₁ : Fin k → Γ := fun i => ((σ : Perm T) ⟨t₀ i, hmem i⟩ : Γ)
  have ht₁ : Function.Injective t₁ := by
    intro i j hij
    have := (σ : Perm T).injective (Subtype.ext hij)
    exact ht₀ (congrArg Subtype.val this)
  have hT₁ : tset t₁ = T := by
    ext c
    rw [mem_tset]
    constructor
    · rintro ⟨i, rfl⟩
      exact ((σ : Perm T) ⟨t₀ i, hmem i⟩).2
    · intro hc
      obtain ⟨i, hi⟩ := mem_tset.1 (((σ : Perm T)⁻¹ ⟨c, hc⟩).2)
      refine ⟨i, ?_⟩
      simp only [t₁]
      have : (⟨t₀ i, hmem i⟩ : T) = (σ : Perm T)⁻¹ ⟨c, hc⟩ := Subtype.ext hi
      rw [this]
      simp
  obtain ⟨g, hgG, hgl, hgt⟩ := hall t₁ ht₁ hT₁
  change Transports (mask x (win (phiT G π T) x _)) (mask x (win (phiT G π (tset t₁)) x _)) g
    at hgt
  rw [hT₁] at hgt
  -- `π(g)` agrees with `σ` on `T`.
  have hlabT : ∀ c (hc : c ∈ T), lab G π g c = ((σ : Perm T) ⟨c, hc⟩ : Γ) := by
    intro c hc
    obtain ⟨i, rfl⟩ := mem_tset.1 hc
    exact hgl i
  have hQ : g ∈ Qgrp G π T := by
    refine ⟨hgG, fun c => ⟨fun h => ?_, fun hc => by rw [hlabT c hc]; exact Subtype.property _⟩⟩
    set d : T := (σ : Perm T)⁻¹ ⟨lab G π g c, h⟩
    have hd : lab G π g d = lab G π g c := by
      rw [hlabT d d.2]
      simp [d]
    rw [← (lab G π g).injective hd]
    exact d.2
  have hres : restrictQ G π T ⟨g, hQ⟩ = (σ : Perm T) := by
    ext c
    rw [restrictQ_apply]
    exact hlabT c c.2
  have hP : g ∈ Pgrp G π T := mem_Pgrp.2 ⟨hQ, by rw [hres]; exact mem_alternatingGroup.1 σ.2⟩
  have hA : g ∈ finalGrp (phiT G π T) x := by
    rw [finalGrp, grp_eq_automorphisms_mask]
    exact ⟨hP, hgt⟩
  refine (mem_img _).2 ⟨⟨g, hP⟩, hA, Subtype.ext ?_⟩
  exact hres

/-- **Nonfull termination in `Q_T`.** "The full setwise group `Aut_{Q_T}(x)`
therefore cannot contain `Alt(T)` in its induced action either." -/
theorem nonfull_Q {x : Ω → C} {T : Finset Γ} (hnf : ¬ IsFull (phiT G π T) x) :
    ¬ ∀ σ ∈ alternatingGroup T, ∃ (g : Perm Ω) (hg : g ∈ automorphisms (Qgrp G π T) x),
      restrictQ G π T ⟨g, hg.1⟩ = σ := by
  intro hall
  apply hnf
  rw [IsFull, Full, eq_top_iff]
  intro σ _
  obtain ⟨g, hg, hres⟩ := hall σ σ.2
  have hP : g ∈ Pgrp G π T := mem_Pgrp.2 ⟨hg.1, by rw [hres]; exact mem_alternatingGroup.1 σ.2⟩
  have hA : g ∈ finalGrp (phiT G π T) x := automorphisms_le_grp _ x _ ⟨hP, hg.2⟩
  exact (mem_img _).2 ⟨⟨g, hP⟩, hA, Subtype.ext hres⟩

end GI.LocalCertificates
