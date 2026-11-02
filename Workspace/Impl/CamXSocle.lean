import Workspace.Impl.CamXFactors
import Workspace.Impl.CamSmallM

/-!
# The socle is the last nontrivial term of a chief series

Let `G` be primitive with a Maróti structure `e`, and let `N = camProd e univ ≅ Alt(m)^r`. We show
that the last nontrivial term `M` of any chief series of `G` is `N` (`camX_chief_last`).

`M` is a minimal normal subgroup of `G` (`camX_chief_min`), and it is transitive, since `G` is
primitive. If `M ∩ N = 1`, then `M` and `N` commute, so `N` acts freely: an element of `N` fixing
one point fixes all its images under `M`, that is, all points. Then `|N| ≤ n`, but
`|N| = (m!/2)^r > binom(m, k)^r = n`. So `M ∩ N = M`, that is `M ≤ N`. Then `M = camProd e T` for
some `T` (`camX_normal_prod`). If `i ∉ T`, then `M` fixes coordinate `i` of every point
(`camX_orbit_others`), so `M` is not transitive. Hence `T = univ`.
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n m k r : ℕ} {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})}

/-- The socle `camProd e univ` lies in `G`. -/
theorem camX_socle_le {G : Subgroup (Perm (Fin n))} (hM : MarotiStructure G e) :
    camProd e Finset.univ ≤ G := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := camX_mem_prod.mp hg
  exact hM.2 h fun i => (hh i).1 (Finset.mem_univ i)

/-- `G` normalizes the socle: conjugating by `g` permutes the coordinates and conjugates each
one by a permutation of `Fin m`. -/
theorem camX_socle_normal {G : Subgroup (Perm (Fin n))} (hM : MarotiStructure G e) :
    ∀ g ∈ G, ∀ y ∈ camProd e Finset.univ, g * y * g⁻¹ ∈ camProd e Finset.univ := by
  intro g hg y hy
  obtain ⟨σ, h, hgh⟩ := hM.1 g hg
  obtain ⟨b, hb, rfl⟩ := camX_mem_prod.mp hy
  let b' : Fin r → Perm (Fin m) := fun i => h i * b (σ i) * (h i)⁻¹
  have hcomm : g * camHom e b = camHom e b' * g := by
    refine Equiv.ext fun w => e.injective (funext fun i => ?_)
    rw [Perm.mul_apply, Perm.mul_apply, hgh, camHom_apply, camHom_apply, hgh]
    change kSetPerm (h i) (kSetPerm (b (σ i)) (e w (σ i))) =
      kSetPerm (h i * b (σ i) * (h i)⁻¹) (kSetPerm (h i) (e w (σ i)))
    rw [← Perm.mul_apply, ← Perm.mul_apply, ← cam_kSetPerm_mul, ← cam_kSetPerm_mul,
      inv_mul_cancel_right]
  rw [hcomm, mul_inv_cancel_right]
  refine camX_mem_prod.mpr ⟨b', fun i => ⟨fun _ => ?_, fun hi => absurd (Finset.mem_univ i) hi⟩,
    rfl⟩
  exact (alternatingGroup.normal (α := Fin m)).conj_mem _ ((hb (σ i)).1 (Finset.mem_univ _)) (h i)

/-- A nontrivial subgroup of `Perm (Fin n)` inside the primitive group `G` and normalized by `G`
is transitive (Mathlib's `IsPreprimitive.isQuasiPreprimitive`). -/
theorem camX_normal_transitive {G M : Subgroup (Perm (Fin n))}
    (hprim : MulAction.IsPreprimitive G (Fin n)) (hMG : M ≤ G) (hM : M ≠ ⊥)
    (hMn : ∀ x ∈ G, ∀ y ∈ M, x * y * x⁻¹ ∈ M) (x y : Fin n) : ∃ g ∈ M, g x = y := by
  let N : Subgroup G := M.subgroupOf G
  haveI : N.Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hMn g g.2 a ha⟩
  have hfix : MulAction.fixedPoints N (Fin n) ≠ Set.univ := by
    obtain ⟨⟨g, hgM⟩, hg1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hM
    have hg1 : g ≠ 1 := fun h => hg1' (Subtype.ext h)
    obtain ⟨z, hz⟩ : ∃ z, g z ≠ z := by
      by_contra hcon
      push Not at hcon
      exact hg1 (Equiv.ext hcon)
    intro hall
    have hzfix : z ∈ MulAction.fixedPoints N (Fin n) := hall ▸ Set.mem_univ z
    exact hz (hzfix ⟨⟨g, hMG hgM⟩, (Subgroup.mem_subgroupOf).mpr hgM⟩)
  haveI := MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := N) hfix
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N x y
  exact ⟨g.1.1, (Subgroup.mem_subgroupOf).mp g.2, hg⟩

/-- `binom(m, k) < m!/2` for `m ≥ 5`: `binom(m, k) ≤ 2^m` and `2^(m+1) < m!`. -/
private theorem camX_choose_lt_half (hm : 5 ≤ m) (k : ℕ) : m.choose k < m.factorial / 2 := by
  have hpow : ∀ j, 2 ^ (j + 5 + 1) < (j + 5).factorial := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      rw [show j + 1 + 5 = (j + 5) + 1 by omega, Nat.factorial_succ, pow_succ]
      nlinarith
  have h1 := Nat.choose_le_two_pow m k
  have h2 := hpow (m - 5)
  rw [show m - 5 + 5 = m by omega, pow_succ] at h2
  obtain ⟨q, hq⟩ := Nat.dvd_factorial (by norm_num : 0 < 2) (by omega : 2 ≤ m)
  rw [hq, Nat.mul_div_cancel_left _ (by norm_num)]
  omega

theorem camX_chief_last {G : Subgroup (Perm (Fin n))} (hM : MarotiStructure G e)
    (hprim : MulAction.IsPreprimitive G (Fin n)) (hn : 25 ≤ n) (hm : 5 ≤ m) (hk1 : 1 ≤ k)
    (hk : 2 * k < m) {Hs : List (Subgroup (Perm (Fin n)))} (hHs : IsChiefSeries G Hs) :
    Hs[Hs.length - 2]? = some (camProd e Finset.univ) := by
  have hkm : k < m := by omega
  have hnr := cam_n_eq e
  have hr : r ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hnr
    omega
  have i₀ : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
  have hNG := camX_socle_le hM
  have hNn := camX_socle_normal hM
  have hNne : camProd e Finset.univ ≠ ⊥ := fun h => camX_prod_ne_bot hm hk1 hkm i₀
    (le_bot_iff.mp (h ▸ camX_prod_mono (Finset.subset_univ {i₀})))
  have hGne : G ≠ ⊥ := fun h => hNne (le_bot_iff.mp (h ▸ hNG))
  obtain ⟨M, hMeq, hMG, hMne, hMn, hMmin⟩ := camX_chief_min hHs hGne
  rw [hMeq]
  have htrans := camX_normal_transitive hprim hMG hMne hMn
  -- Step 1: `M ≤ N`.
  have hMN : M ≤ camProd e Finset.univ := by
    have hinf_n : ∀ x ∈ G, ∀ y ∈ M ⊓ camProd e Finset.univ,
        x * y * x⁻¹ ∈ M ⊓ camProd e Finset.univ := fun x hx y hy =>
      ⟨hMn x hx y hy.1, hNn x hx y hy.2⟩
    rcases hMmin _ inf_le_left hinf_n with hbot | heq
    · -- `M ∩ N = 1` is impossible: `N` would act freely.
      exfalso
      have hcomm : ∀ c ∈ camProd e Finset.univ, ∀ a ∈ M, c * a = a * c := by
        intro c hc a ha
        have h1 : c * a * c⁻¹ * a⁻¹ ∈ M ⊓ camProd e Finset.univ := by
          refine ⟨M.mul_mem (hMn c (hNG hc) a ha) (M.inv_mem ha), ?_⟩
          have h2 := (camProd e Finset.univ).mul_mem hc (hNn a (hMG ha) c⁻¹
            ((camProd e Finset.univ).inv_mem hc))
          simpa only [mul_assoc] using h2
        rw [hbot, Subgroup.mem_bot] at h1
        exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
      let x₀ : Fin n := ⟨0, by omega⟩
      have hinj : Function.Injective fun c : camProd e Finset.univ => (c : Perm (Fin n)) x₀ := by
        intro c c' hcc
        apply Subtype.ext
        refine Equiv.ext fun y => ?_
        obtain ⟨a, ha, rfl⟩ := htrans x₀ y
        have e1 := hcomm c c.2 a ha
        have e2 := hcomm c' c'.2 a ha
        rw [show (c : Perm (Fin n)) (a x₀) = a ((c : Perm (Fin n)) x₀) from
            congrArg (fun p : Perm (Fin n) => p x₀) e1,
          show (c' : Perm (Fin n)) (a x₀) = a ((c' : Perm (Fin n)) x₀) from
            congrArg (fun p : Perm (Fin n) => p x₀) e2]
        exact congrArg a hcc
      have hle := Nat.card_le_card_of_injective _ hinj
      rw [camX_card_prod (by omega) hk1 hkm, Finset.card_univ, Fintype.card_fin,
        Nat.card_eq_fintype_card, Fintype.card_fin, hnr] at hle
      exact absurd hle (not_le.mpr (Nat.pow_lt_pow_left (camX_choose_lt_half hm k) hr))
    · exact heq ▸ inf_le_right
  -- Step 2: `M = camProd e T`, and transitivity forces `T = univ`.
  obtain ⟨T, -, rfl⟩ := camX_normal_prod hm hk1 hkm hMN fun x hx y hy => hMn x (hNG hx) y hy
  by_cases hT : T = Finset.univ
  · rw [hT]
  · exfalso
    obtain ⟨i, hi⟩ : ∃ i, i ∉ T := by
      by_contra hcon
      push Not at hcon
      exact hT (Finset.eq_univ_of_forall hcon)
    have hTi : camProd e T ≤ camProd e {i}ᶜ :=
      camX_prod_mono fun j hj => Finset.mem_compl.mpr fun hji =>
        hi (Finset.mem_singleton.mp hji ▸ hj)
    obtain ⟨A, B, hAB⟩ : ∃ A B : {A : Finset (Fin m) // A.card = k}, A ≠ B := by
      rw [← Fintype.one_lt_card_iff, Fintype.card_finset_len, Fintype.card_fin]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Nat.choose_succ_succ]
      simp only [Nat.succ_eq_add_one]
      have := Nat.choose_pos (show k' ≤ m' by omega)
      have := Nat.choose_pos (show k' + 1 ≤ m' by omega)
      omega
    obtain ⟨g, hg, hgxy⟩ := htrans (e.symm fun _ => A) (e.symm fun _ => B)
    have horb : e.symm (fun _ => B) ∈ MulAction.orbit (camProd e {i}ᶜ) (e.symm fun _ => A) :=
      ⟨⟨g, hTi hg⟩, hgxy⟩
    rw [camX_orbit_others (by omega) hkm.le] at horb
    simp only [Equiv.apply_symm_apply] at horb
    exact hAB horb.symm

end GI.Impl
