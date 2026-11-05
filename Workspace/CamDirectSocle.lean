module

public import Workspace.Impl.CamXSocle
public import Workspace.Proved.JohnScheme
public import Workspace.Impl.NClMath

@[expose] public section

/-!
# Direct socle and factor finding for Cameron–Maróti groups

This file proves the mathematical core for computing the socle `N = camProd e univ ≅ Alt(m)^r`
of a primitive group `G` with a Maróti structure `e` (`25 ≤ n`, `5 ≤ m`, `1 ≤ k`, `2 * k < m`)
and decomposing `N` into its simple factors `camProd e {i} ≅ Alt(m)` without computing a
chief series:

* `camX_socle_le_every_normal`: every nontrivial normal subgroup `M` of `G` contains the socle
  `camProd e univ`. Consequently, `camProd e univ` is the unique nontrivial normal subgroup of
  `G` of minimum order (`camX_eq_socle_of_card_le`).
* Lemma 2.1 (`adjKSet` and `Alt(m)`-stabilizers): for a `k`-subset `A` of `Fin m`, the stabilizer
  of `A` in `Alt(m)` is nonabelian (`camX_alt_stab_noncomm`), acts transitively on the `k`-subsets
  `B` meeting `A` in `k - 1` points (`camX_adjKSet_transitive`), and any permutation of `Fin m`
  fixing `A` and all such `B` is the identity (`camX_eq_one_of_fix_adjKSet`).
* Proposition 2.2 (`camFactorCand_single`, `camFactorCand_min_is_single`): for `Cur = camProd e S`
  with `S` nonempty and base point `x₀`, the normal closure `camFactorCand Cur x₀ z` of the
  pointwise stabilizer of `x₀` and the `Cur_{x₀}`-orbit of `z` is always a subproduct
  `camProd e A` (`A ⊆ S`), realizes every single factor `camProd e {i₀}` (`i₀ ∈ S`), and its
  minimum-order nontrivial value over `z : Fin n` is a single factor `camProd e {i}`.
* Proposition 2.3 (`camSocleCand_exists_eq_socle`, `camSocleCand_min_eq_socle`): for `G` primitive
  with Maróti structure `e` and base point `x₀`, the normal closure `camSocleCand G x₀ y₁ z` in `G`
  of the derived subgroup of the pointwise stabilizer of `x₀` and the `G_{x₀, y₁}`-orbit of `z`
  realizes `camProd e univ`, and its minimum-order nontrivial value over `y₁, z : Fin n` equals
  `camProd e univ`.
-/

namespace GI.Impl

open Equiv GI.Cited
open scoped commutatorElement

variable {n m k r : ℕ} {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})}

/-! ### 1. The socle is contained in every nontrivial normal subgroup -/

/-- `binom(m, k) < m!/2` for `m ≥ 5`: `binom(m, k) ≤ 2^m` and `2^(m+1) < m!`. -/
private theorem camDirect_choose_lt_half (hm : 5 ≤ m) (k : ℕ) :
    m.choose k < m.factorial / 2 := by
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

/-- Every nontrivial `G`-normal subgroup `M ≤ G` contains the socle `camProd e univ`. -/
theorem camX_socle_le_every_normal {G M : Subgroup (Perm (Fin n))} (hM : MarotiStructure G e)
    (hprim : MulAction.IsPreprimitive G (Fin n)) (hn : 25 ≤ n) (hm : 5 ≤ m) (hk1 : 1 ≤ k)
    (hk : 2 * k < m) (hMG : M ≤ G) (hMne : M ≠ ⊥)
    (hMn : ∀ x ∈ G, ∀ y ∈ M, x * y * x⁻¹ ∈ M) :
    camProd e Finset.univ ≤ M := by
  have hkm : k < m := by omega
  have hnr := cam_n_eq e
  have hr : r ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hnr
    omega
  have hNG := camX_socle_le hM
  have hNn := camX_socle_normal hM
  have htransM := camX_normal_transitive hprim hMG hMne hMn
  set M' := M ⊓ camProd e Finset.univ
  have hM'G : M' ≤ G := inf_le_left.trans hMG
  have hM'n : ∀ x ∈ G, ∀ y ∈ M', x * y * x⁻¹ ∈ M' := fun x hx y hy =>
    ⟨hMn x hx y hy.1, hNn x hx y hy.2⟩
  have hM'ne : M' ≠ ⊥ := by
    intro hbot
    have hcomm : ∀ c ∈ camProd e Finset.univ, ∀ a ∈ M, c * a = a * c := by
      intro c hc a ha
      have h1 : c * a * c⁻¹ * a⁻¹ ∈ M' := by
        refine ⟨M.mul_mem (hMn c (hNG hc) a ha) (M.inv_mem ha), ?_⟩
        have h2 : c * a * c⁻¹ * a⁻¹ = c * (a * c⁻¹ * a⁻¹) := by group
        rw [h2]
        exact (camProd e Finset.univ).mul_mem hc (hNn a (hMG ha) c⁻¹
          ((camProd e Finset.univ).inv_mem hc))
      rw [hbot, Subgroup.mem_bot] at h1
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
    let x₀ : Fin n := ⟨0, by omega⟩
    have hinj : Function.Injective fun c : camProd e Finset.univ => (c : Perm (Fin n)) x₀ := by
      intro c c' hcc
      apply Subtype.ext
      refine Equiv.ext fun y => ?_
      obtain ⟨a, ha, rfl⟩ := htransM x₀ y
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
    exact absurd hle (not_le.mpr (Nat.pow_lt_pow_left (camDirect_choose_lt_half hm k) hr))
  have htransM' := camX_normal_transitive hprim hM'G hM'ne hM'n
  obtain ⟨T, -, hM'eq⟩ := camX_normal_prod hm hk1 hkm (inf_le_right : M' ≤ camProd e Finset.univ)
    fun x hx y hy => hM'n x (hNG hx) y hy
  have hT : T = Finset.univ := by
    by_contra hT
    obtain ⟨i, hi⟩ : ∃ i, i ∉ T := by
      by_contra hcon
      push Not at hcon
      exact hT (Finset.eq_univ_of_forall hcon)
    have hTi : M' ≤ camProd e {i}ᶜ := by
      change M ⊓ camProd e Finset.univ ≤ camProd e {i}ᶜ
      rw [hM'eq]
      exact camX_prod_mono fun j hj => Finset.mem_compl.mpr fun hji =>
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
    obtain ⟨g, hg, hgxy⟩ := htransM' (e.symm fun _ => A) (e.symm fun _ => B)
    have horb : e.symm (fun _ => B) ∈ MulAction.orbit (camProd e {i}ᶜ) (e.symm fun _ => A) :=
      ⟨⟨g, hTi hg⟩, hgxy⟩
    rw [camX_orbit_others (by omega) hkm.le] at horb
    simp only [Equiv.apply_symm_apply] at horb
    exact hAB horb.symm
  rw [hT] at hM'eq
  exact hM'eq ▸ inf_le_left

theorem camX_socle_card_le_normal {G M : Subgroup (Perm (Fin n))} (hM : MarotiStructure G e)
    (hprim : MulAction.IsPreprimitive G (Fin n)) (hn : 25 ≤ n) (hm : 5 ≤ m) (hk1 : 1 ≤ k)
    (hk : 2 * k < m) (hMG : M ≤ G) (hMne : M ≠ ⊥)
    (hMn : ∀ x ∈ G, ∀ y ∈ M, x * y * x⁻¹ ∈ M) :
    Nat.card (camProd e Finset.univ) ≤ Nat.card M :=
  Subgroup.card_le_of_le (camX_socle_le_every_normal hM hprim hn hm hk1 hk hMG hMne hMn)

theorem camX_eq_socle_of_card_le {G M : Subgroup (Perm (Fin n))} (hM : MarotiStructure G e)
    (hprim : MulAction.IsPreprimitive G (Fin n)) (hn : 25 ≤ n) (hm : 5 ≤ m) (hk1 : 1 ≤ k)
    (hk : 2 * k < m) (hMG : M ≤ G) (hMne : M ≠ ⊥)
    (hMn : ∀ x ∈ G, ∀ y ∈ M, x * y * x⁻¹ ∈ M)
    (hcard : Nat.card M ≤ Nat.card (camProd e Finset.univ)) :
    M = camProd e Finset.univ :=
  (Subgroup.eq_of_le_of_card_ge
    (camX_socle_le_every_normal hM hprim hn hm hk1 hk hMG hMne hMn) hcard).symm

/-! ### 2. Lemma 2.1: Adjacent `k`-sets and `Alt(m)`-stabilizers -/

/-- Two `k`-sets `A` and `B` are adjacent in the Johnson graph when `|A ∩ B| + 1 = k`. -/
def adjKSet (A B : {A : Finset (Fin m) // A.card = k}) : Prop :=
  (A.1 ∩ B.1).card + 1 = k

/-- Replacing `a ∈ A` with `b ∉ A` via `kSetPerm (swap a b) A`. -/
def swapKSet (A : {A : Finset (Fin m) // A.card = k}) (a b : Fin m) :
    {A : Finset (Fin m) // A.card = k} :=
  kSetPerm (Equiv.swap a b) A

theorem mem_swapKSet {A : {A : Finset (Fin m) // A.card = k}} {a b : Fin m}
    (ha : a ∈ A.1) (hb : b ∉ A.1) (x : Fin m) :
    x ∈ (swapKSet A a b).1 ↔ x = b ∨ (x ∈ A.1 ∧ x ≠ a) := by
  simp only [swapKSet, cam_kSetPerm_apply, Finset.mem_map_equiv, Equiv.symm_swap]
  rcases eq_or_ne x a with rfl | hxa
  · rw [swap_apply_left]
    have hab : x ≠ b := fun h => hb (h ▸ ha)
    simp [hb, hab]
  rcases eq_or_ne x b with rfl | hxb
  · rw [swap_apply_right]
    simp [ha]
  rw [swap_apply_of_ne_of_ne hxa hxb]
  simp [hxa, hxb]

theorem inter_swapKSet_eq_erase {A : {A : Finset (Fin m) // A.card = k}} {a b : Fin m}
    (ha : a ∈ A.1) (hb : b ∉ A.1) :
    A.1 ∩ (swapKSet A a b).1 = A.1.erase a := by
  ext x
  rw [Finset.mem_inter, mem_swapKSet ha hb, Finset.mem_erase]
  constructor
  · rintro ⟨hxA, rfl | ⟨_, hxa⟩⟩
    · exact absurd hxA hb
    · exact ⟨hxa, hxA⟩
  · rintro ⟨hxa, hxA⟩
    exact ⟨hxA, Or.inr ⟨hxA, hxa⟩⟩

theorem adjKSet_swapKSet {A : {A : Finset (Fin m) // A.card = k}} {a b : Fin m}
    (ha : a ∈ A.1) (hb : b ∉ A.1) :
    adjKSet A (swapKSet A a b) := by
  unfold adjKSet
  rw [inter_swapKSet_eq_erase ha hb, Finset.card_erase_add_one ha, A.2]

/-- Lemma 2.1(a): For `1 ≤ k < m`, every `k`-set has at least one adjacent `k`-set. -/
theorem camX_exists_adjKSet (hk1 : 1 ≤ k) (hkm : k < m)
    (A : {A : Finset (Fin m) // A.card = k}) :
    ∃ B : {A : Finset (Fin m) // A.card = k}, adjKSet A B := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [A.2]; omega)
  have hc : 0 < A.1ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, A.2]; omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hc
  exact ⟨swapKSet A a b, adjKSet_swapKSet ha (Finset.mem_compl.mp hb)⟩

/-- When `m - k ≥ 2`, for any `k`-sets `A, C`, there is a `k`-set `B ≠ C` adjacent to `A`. -/
theorem camX_exists_adjKSet_ne (hk1 : 1 ≤ k) (hkm2 : k + 2 ≤ m)
    (A C : {A : Finset (Fin m) // A.card = k}) :
    ∃ B : {A : Finset (Fin m) // A.card = k}, adjKSet A B ∧ B ≠ C := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [A.2]; omega)
  have hc : 1 < A.1ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, A.2]; omega
  obtain ⟨b₁, hb₁, b₂, hb₂, hb12⟩ := Finset.one_lt_card.mp hc
  rw [Finset.mem_compl] at hb₁ hb₂
  by_cases h1 : swapKSet A a b₁ = C
  · refine ⟨swapKSet A a b₂, adjKSet_swapKSet ha hb₂, fun h2 => hb12 ?_⟩
    have hmem : b₁ ∈ (swapKSet A a b₁).1 := (mem_swapKSet ha hb₁ b₁).mpr (Or.inl rfl)
    rw [h1, ← h2, mem_swapKSet ha hb₂] at hmem
    rcases hmem with h | ⟨hA, -⟩
    · exact h
    · exact absurd hA hb₁
  · exact ⟨swapKSet A a b₁, adjKSet_swapKSet ha hb₁, h1⟩

/-- Lemma 2.1(b): The `Alt(m)`-stabilizer of `A` acts transitively on `{B | adjKSet A B}`. -/
theorem camX_adjKSet_transitive (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m)
    (A B B' : {A : Finset (Fin m) // A.card = k}) (hB : adjKSet A B) (hB' : adjKSet A B') :
    ∃ a ∈ alternatingGroup (Fin m), kSetPerm a A = A ∧ kSetPerm a B = B' := by
  have hab : (A.1 ∩ B.1).card = (A.1 ∩ B'.1).card := by
    unfold adjKSet at hB hB'; omega
  have hout : 2 ≤ (A.1 ∪ B'.1)ᶜ.card := by
    have hu := Finset.card_union_add_card_inter A.1 B'.1
    rw [Finset.card_compl, Fintype.card_fin, A.2, B'.2] at *
    unfold adjKSet at hB'
    omega
  obtain ⟨a, ha, haA, haB⟩ := GI.Proved.john_exists_alt_pair rfl (by rw [B.2, B'.2]) hab hout
  exact ⟨a, ha, Subtype.ext haA, Subtype.ext haB⟩

/-- Lemma 2.1(c): Any `h : Perm (Fin m)` fixing `A` and all `B` adjacent to `A` is `1`. -/
theorem camX_eq_one_of_fix_adjKSet (hk1 : 1 ≤ k) (hkm : k < m)
    (A : {A : Finset (Fin m) // A.card = k}) (h : Perm (Fin m))
    (hA : kSetPerm h A = A) (hadj : ∀ B, adjKSet A B → kSetPerm h B = B) :
    h = 1 := by
  have hmem : ∀ S : {A : Finset (Fin m) // A.card = k}, kSetPerm h S = S →
      ∀ x : Fin m, h x ∈ S.1 ↔ x ∈ S.1 := by
    intro S hS x
    have : h x ∈ (kSetPerm h S).1 ↔ h x ∈ S.1 := by rw [hS]
    simpa [cam_kSetPerm_apply] using this.symm
  have hpair : ∀ a b : Fin m, a ∈ A.1 → b ∉ A.1 → h a = a ∧ h b = b := by
    intro a b ha hb
    have hB := hadj (swapKSet A a b) (adjKSet_swapKSet ha hb)
    have hhaA : h a ∈ A.1 := (hmem A hA a).mpr ha
    have haB : a ∉ (swapKSet A a b).1 := by
      rw [mem_swapKSet ha hb]
      rintro (rfl | ⟨-, hne⟩)
      · exact hb ha
      · exact hne rfl
    have hhaB : h a ∉ (swapKSet A a b).1 := fun h' => haB ((hmem _ hB a).mp h')
    rw [mem_swapKSet ha hb] at hhaB
    have ha_eq : h a = a := by
      by_contra hne
      exact hhaB (Or.inr ⟨hhaA, hne⟩)
    have hhbA : h b ∉ A.1 := fun h' => hb ((hmem A hA b).mp h')
    have hbB : b ∈ (swapKSet A a b).1 := (mem_swapKSet ha hb b).mpr (Or.inl rfl)
    have hhbB : h b ∈ (swapKSet A a b).1 := (hmem _ hB b).mpr hbB
    rw [mem_swapKSet ha hb] at hhbB
    have hb_eq : h b = b := by
      rcases hhbB with h' | ⟨h', -⟩
      · exact h'
      · exact absurd h' hhbA
    exact ⟨ha_eq, hb_eq⟩
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.mp (by rw [A.2]; omega)
  have hc : 0 < A.1ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, A.2]; omega
  obtain ⟨b₀, hb₀⟩ := Finset.card_pos.mp hc
  rw [Finset.mem_compl] at hb₀
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ A.1
  · exact (hpair x b₀ hx hb₀).1
  · exact (hpair a₀ x ha₀ hx).2

theorem swap_kSetPerm_eq (A : {A : Finset (Fin m) // A.card = k}) {u v : Fin m}
    (h : u ∈ A.1 ↔ v ∈ A.1) : kSetPerm (Equiv.swap u v) A = A := by
  apply Subtype.ext
  ext x
  simp only [cam_kSetPerm_apply, Finset.mem_map_equiv, Equiv.symm_swap]
  rcases eq_or_ne x u with rfl | hxu
  · rw [swap_apply_left]; exact h.symm
  rcases eq_or_ne x v with rfl | hxv
  · rw [swap_apply_right]; exact h
  rw [swap_apply_of_ne_of_ne hxu hxv]

/-- Lemma 2.1(d): For `5 ≤ m`, `1 ≤ k`, `2 * k < m`, the `Alt(m)`-stabilizer of `A` is nonabelian. -/
theorem camX_alt_stab_noncomm (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m)
    (A : {A : Finset (Fin m) // A.card = k}) :
    ∃ a b : Perm (Fin m), a ∈ alternatingGroup (Fin m) ∧ b ∈ alternatingGroup (Fin m) ∧
      kSetPerm a A = A ∧ kSetPerm b A = A ∧ a * b ≠ b * a := by
  have hc3 : 3 ≤ A.1ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, A.2]; omega
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hc3
  obtain ⟨b₁, T₁, hb₁T₁, rfl, hT₁⟩ : ∃ b₁ T₁, b₁ ∉ T₁ ∧ S = insert b₁ T₁ ∧ T₁.card = 2 := by
    obtain ⟨b₁, hb₁⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    refine ⟨b₁, S.erase b₁, Finset.notMem_erase b₁ S, (Finset.insert_erase hb₁).symm, ?_⟩
    have := Finset.card_erase_add_one hb₁; omega
  obtain ⟨b₂, b₃, hb₂₃, rfl⟩ := Finset.card_eq_two.mp hT₁
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb₁T₁
  obtain ⟨hb₁₂, hb₁₃⟩ := hb₁T₁
  change b₁ ≠ b₂ at hb₁₂
  change b₁ ≠ b₃ at hb₁₃
  have hb₁ : b₁ ∉ A.1 := Finset.mem_compl.mp (hSsub (by simp))
  have hb₂ : b₂ ∉ A.1 := Finset.mem_compl.mp (hSsub (by simp))
  have hb₃ : b₃ ∉ A.1 := Finset.mem_compl.mp (hSsub (by simp))
  let σ₁ : Perm (Fin m) := Equiv.swap b₁ b₂ * Equiv.swap b₁ b₃
  have hσ₁alt : σ₁ ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hb₁₂, Perm.sign_swap hb₁₃]; rfl
  have hσ₁A : kSetPerm σ₁ A = A := by
    rw [cam_kSetPerm_mul, Perm.mul_apply, swap_kSetPerm_eq A (iff_of_false hb₁ hb₃),
      swap_kSetPerm_eq A (iff_of_false hb₁ hb₂)]
  have hσ₁_b₁ : σ₁ b₁ = b₃ := by
    change Equiv.swap b₁ b₂ (Equiv.swap b₁ b₃ b₁) = b₃
    rw [swap_apply_left, swap_apply_of_ne_of_ne hb₁₃.symm hb₂₃.symm]
  have hσ₁_b₂ : σ₁ b₂ = b₁ := by
    change Equiv.swap b₁ b₂ (Equiv.swap b₁ b₃ b₂) = b₁
    rw [swap_apply_of_ne_of_ne hb₁₂.symm hb₂₃, swap_apply_right]
  by_cases hk2 : 2 ≤ k
  · obtain ⟨a₁, ha₁, a₂, ha₂, ha₁₂⟩ := Finset.one_lt_card.mp (by rw [A.2]; omega)
    let σ₂ : Perm (Fin m) := Equiv.swap a₁ a₂ * Equiv.swap b₁ b₂
    have hσ₂alt : σ₂ ∈ alternatingGroup (Fin m) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap ha₁₂, Perm.sign_swap hb₁₂]; rfl
    have hσ₂A : kSetPerm σ₂ A = A := by
      rw [cam_kSetPerm_mul, Perm.mul_apply, swap_kSetPerm_eq A (iff_of_false hb₁ hb₂),
        swap_kSetPerm_eq A (iff_of_true ha₁ ha₂)]
    have hσ₂_b₁ : σ₂ b₁ = b₂ := by
      have h1 : b₂ ≠ a₁ := fun h => hb₂ (h ▸ ha₁)
      have h2 : b₂ ≠ a₂ := fun h => hb₂ (h ▸ ha₂)
      change Equiv.swap a₁ a₂ (Equiv.swap b₁ b₂ b₁) = b₂
      rw [swap_apply_left, swap_apply_of_ne_of_ne h1 h2]
    have hσ₂_b₃ : σ₂ b₃ = b₃ := by
      have h1 : b₃ ≠ a₁ := fun h => hb₃ (h ▸ ha₁)
      have h2 : b₃ ≠ a₂ := fun h => hb₃ (h ▸ ha₂)
      change Equiv.swap a₁ a₂ (Equiv.swap b₁ b₂ b₃) = b₃
      rw [swap_apply_of_ne_of_ne hb₁₃.symm hb₂₃.symm, swap_apply_of_ne_of_ne h1 h2]
    refine ⟨σ₁, σ₂, hσ₁alt, hσ₂alt, hσ₁A, hσ₂A, fun hcomm => hb₁₃ ?_⟩
    have := congrArg (fun p : Perm (Fin m) => p b₁) hcomm
    simpa [Perm.mul_apply, hσ₁_b₁, hσ₁_b₂, hσ₂_b₁, hσ₂_b₃] using this
  · have hc4 : 4 ≤ A.1ᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin, A.2]; omega
    have hpos4 : 0 < (A.1ᶜ \ insert b₁ {b₂, b₃}).card := by
      have := Finset.card_sdiff_add_card_eq_card hSsub
      omega
    obtain ⟨b₄, hb₄mem⟩ := Finset.card_pos.mp hpos4
    obtain ⟨hb₄A, hb₄S⟩ := Finset.mem_sdiff.mp hb₄mem
    rw [Finset.mem_compl] at hb₄A
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb₄S
    obtain ⟨hb₄₁, hb₄₂, hb₄₃⟩ := hb₄S
    change b₄ ≠ b₁ at hb₄₁
    change b₄ ≠ b₂ at hb₄₂
    change b₄ ≠ b₃ at hb₄₃
    let σ₂ : Perm (Fin m) := Equiv.swap b₁ b₂ * Equiv.swap b₃ b₄
    have hσ₂alt : σ₂ ∈ alternatingGroup (Fin m) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hb₁₂, Perm.sign_swap hb₄₃.symm]
      rfl
    have hσ₂A : kSetPerm σ₂ A = A := by
      rw [cam_kSetPerm_mul, Perm.mul_apply, swap_kSetPerm_eq A (iff_of_false hb₃ hb₄A),
        swap_kSetPerm_eq A (iff_of_false hb₁ hb₂)]
    have hσ₂_b₁ : σ₂ b₁ = b₂ := by
      change Equiv.swap b₁ b₂ (Equiv.swap b₃ b₄ b₁) = b₂
      rw [swap_apply_of_ne_of_ne hb₁₃ hb₄₁.symm, swap_apply_left]
    have hσ₂_b₃ : σ₂ b₃ = b₄ := by
      change Equiv.swap b₁ b₂ (Equiv.swap b₃ b₄ b₃) = b₄
      rw [swap_apply_left, swap_apply_of_ne_of_ne hb₄₁ hb₄₂]
    refine ⟨σ₁, σ₂, hσ₁alt, hσ₂alt, hσ₁A, hσ₂A, fun hcomm => hb₄₁.symm ?_⟩
    have := congrArg (fun p : Perm (Fin m) => p b₁) hcomm
    simpa [Perm.mul_apply, hσ₁_b₁, hσ₁_b₂, hσ₂_b₁, hσ₂_b₃] using this

/-! ### 3. Orbit stabilizers and normal closures -/

/-- The pointwise stabilizer in `G` of `x₀` and the `H`-orbit of `z`. -/
def camOrbStab (G H : Subgroup (Perm (Fin n))) (x₀ z : Fin n) :
    Subgroup (Perm (Fin n)) where
  carrier := {g | g ∈ G ∧ g x₀ = x₀ ∧ ∀ y ∈ MulAction.orbit H z, g y = y}
  one_mem' := ⟨G.one_mem, rfl, fun _ _ => rfl⟩
  mul_mem' ha hb := ⟨G.mul_mem ha.1 hb.1, by simp [Perm.mul_apply, hb.2.1, ha.2.1],
    fun y hy => by simp [Perm.mul_apply, hb.2.2 y hy, ha.2.2 y hy]⟩
  inv_mem' ha := ⟨G.inv_mem ha.1, by rw [Perm.inv_eq_iff_eq]; exact ha.2.1.symm,
    fun y hy => by rw [Perm.inv_eq_iff_eq]; exact (ha.2.2 y hy).symm⟩

theorem mem_camOrbStab {G H : Subgroup (Perm (Fin n))} {x₀ z : Fin n} {g : Perm (Fin n)} :
    g ∈ camOrbStab G H x₀ z ↔ g ∈ G ∧ g x₀ = x₀ ∧ ∀ y ∈ MulAction.orbit H z, g y = y :=
  Iff.rfl

theorem camOrbStab_le (G H : Subgroup (Perm (Fin n))) (x₀ z : Fin n) :
    camOrbStab G H x₀ z ≤ G := fun _ hg => hg.1

theorem mem_pointwiseStab {G : Subgroup (Perm (Fin n))} {pts : List (Fin n)} {g : Perm (Fin n)} :
    g ∈ pointwiseStab G pts ↔ g ∈ G ∧ ∀ i ∈ pts, g i = i :=
  Iff.rfl

theorem pointwiseStab_eq_camOrbStab (G H : Subgroup (Perm (Fin n))) (x₀ z : Fin n)
    (pts : List (Fin n)) (hpts : ∀ y : Fin n, y ∈ pts ↔ y ∈ MulAction.orbit H z) :
    pointwiseStab (pointwiseStab G [x₀]) pts = camOrbStab G H x₀ z := by
  ext g
  simp only [mem_pointwiseStab, List.mem_singleton, forall_eq, mem_camOrbStab, hpts, and_assoc]

theorem pointwiseStab_cons_eq_camOrbStab (G H : Subgroup (Perm (Fin n))) (x₀ z : Fin n)
    (pts : List (Fin n)) (hpts : ∀ y : Fin n, y ∈ pts ↔ y ∈ MulAction.orbit H z) :
    pointwiseStab G (x₀ :: pts) = camOrbStab G H x₀ z := by
  ext g
  simp only [mem_pointwiseStab, List.mem_cons, forall_eq_or_imp, mem_camOrbStab, hpts]

/-- The normal closure of `K` under `G`: the subgroup generated by `{g y g⁻¹ | g ∈ G, y ∈ K}`. -/
def camNormClosure (G K : Subgroup (Perm (Fin n))) : Subgroup (Perm (Fin n)) :=
  Subgroup.closure {x | ∃ g ∈ G, ∃ y ∈ K, x = g * y * g⁻¹}

theorem le_camNormClosure (G K : Subgroup (Perm (Fin n))) : K ≤ camNormClosure G K := by
  intro y hy
  refine Subgroup.subset_closure ⟨1, G.one_mem, y, hy, by group⟩

theorem camNormClosure_le {G K : Subgroup (Perm (Fin n))} (hKG : K ≤ G) :
    camNormClosure G K ≤ G := by
  rw [camNormClosure, Subgroup.closure_le]
  rintro x ⟨g, hg, y, hy, rfl⟩
  exact G.mul_mem (G.mul_mem hg (hKG hy)) (G.inv_mem hg)

theorem camNormClosure_normal (G K : Subgroup (Perm (Fin n))) :
    ∀ g ∈ G, ∀ x ∈ camNormClosure G K, g * x * g⁻¹ ∈ camNormClosure G K := by
  intro g hg
  refine ncl_conj_closure fun x hx => ?_
  obtain ⟨g', hg', y, hy, rfl⟩ := hx
  refine Subgroup.subset_closure ⟨g * g', G.mul_mem hg hg', y, hy, by group⟩

theorem camNormClosure_minimal {G K M : Subgroup (Perm (Fin n))} (hKM : K ≤ M)
    (hMn : ∀ g ∈ G, ∀ y ∈ M, g * y * g⁻¹ ∈ M) :
    camNormClosure G K ≤ M := by
  rw [camNormClosure, Subgroup.closure_le]
  rintro x ⟨g, hg, y, hy, rfl⟩
  exact hMn g hg y (hKM hy)

theorem camNormClosure_ne_bot {G K : Subgroup (Perm (Fin n))} (hK : K ≠ ⊥) :
    camNormClosure G K ≠ ⊥ :=
  fun h => hK (le_bot_iff.mp (h ▸ le_camNormClosure G K))

/-- Bridge from `normalClosure_call` to `camNormClosure`: when `gens hs = K ≤ G`, the subgroup
returned by `normalClosurePrim` on `[gv, encGroup hs]` is `camNormClosure G K`. -/
theorem camNormClosure_eq_of_gens {G K : Subgroup (Perm (Fin n))} {hs : List (Perm (Fin n))}
    (hhs : gens hs = K) (hKG : K ≤ G) :
    Subgroup.closure {x | ∃ g ∈ G ⊔ gens hs, ∃ y ∈ hs, x = g * y * g⁻¹} =
      camNormClosure G K := by
  rw [hhs, sup_eq_left.mpr hKG]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨g, hg, y, hy, rfl⟩
    exact Subgroup.subset_closure ⟨g, hg, y, hhs ▸ Subgroup.subset_closure hy, rfl⟩
  · rw [camNormClosure, Subgroup.closure_le]
    rintro x ⟨g, hg, y, hy, rfl⟩
    rw [← hhs] at hy
    refine ncl_conj_closure (fun y' hy' => ?_) y hy
    exact Subgroup.subset_closure ⟨g, hg, y', hy', rfl⟩

/-! ### 4. Proposition 2.2: Direct factor finding in `camProd e S` -/

/-- The candidate factor in `Cur` associated to base point `x₀` and point `z`: the normal closure
in `Cur` of the pointwise stabilizer of `x₀` and the `Cur_{x₀}`-orbit of `z`. -/
def camFactorCand (Cur : Subgroup (Perm (Fin n))) (x₀ z : Fin n) :
    Subgroup (Perm (Fin n)) :=
  camNormClosure Cur (camOrbStab Cur (pointwiseStab Cur [x₀]) x₀ z)

theorem camFactorCand_le (Cur : Subgroup (Perm (Fin n))) (x₀ z : Fin n) :
    camFactorCand Cur x₀ z ≤ Cur :=
  camNormClosure_le (camOrbStab_le Cur _ x₀ z)

theorem camFactorCand_normal (Cur : Subgroup (Perm (Fin n))) (x₀ z : Fin n) :
    ∀ g ∈ Cur, ∀ x ∈ camFactorCand Cur x₀ z, g * x * g⁻¹ ∈ camFactorCand Cur x₀ z :=
  camNormClosure_normal Cur _

/-- Every candidate `camFactorCand (camProd e S) x₀ z` is a subproduct `camProd e A` (`A ⊆ S`). -/
theorem camFactorCand_eq_prod (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m)
    (S : Finset (Fin r)) (x₀ z : Fin n) :
    ∃ A ⊆ S, camFactorCand (camProd e S) x₀ z = camProd e A :=
  camX_normal_prod hm hk1 (by omega) (camFactorCand_le _ x₀ z) (camFactorCand_normal _ x₀ z)

@[simp] theorem camHom_apply_coord (b : Fin r → Perm (Fin m)) (x : Fin n) (i : Fin r) :
    e (camHom e b x) i = kSetPerm (b i) (e x i) :=
  congrFun (camHom_apply e b x) i

theorem card_inter_kSetPerm (a : Perm (Fin m)) (A B : {A : Finset (Fin m) // A.card = k}) :
    ((kSetPerm a A).1 ∩ (kSetPerm a B).1).card = (A.1 ∩ B.1).card := by
  rw [cam_kSetPerm_apply, cam_kSetPerm_apply, ← Finset.map_inter, Finset.card_map]

/-- Proposition 2.2 (existence): For every `i₀ ∈ S`, there exists `z : Fin n` such that
`camFactorCand (camProd e S) x₀ z = camProd e {i₀}`. -/
theorem camFactorCand_single (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m)
    {S : Finset (Fin r)} {i₀ : Fin r} (hi₀ : i₀ ∈ S) (x₀ : Fin n) :
    ∃ z : Fin n, camFactorCand (camProd e S) x₀ z = camProd e {i₀} := by
  have hkm : k < m := by omega
  have hadj : ∀ i : Fin r, ∃ B, adjKSet (e x₀ i) B :=
    fun i => camX_exists_adjKSet hk1 hkm (e x₀ i)
  choose B hB using hadj
  let z : Fin n := e.symm (fun i => if i = i₀ then e x₀ i₀ else B i)
  have hez_i₀ : e z i₀ = e x₀ i₀ := by simp [z]
  have hez_ne : ∀ i ≠ i₀, e z i = B i := fun i hi => by simp [z, hi]
  refine ⟨z, ?_⟩
  set Cur := camProd e S
  set P := camOrbStab Cur (pointwiseStab Cur [x₀]) x₀ z
  -- Step 1: `P ≤ camProd e {i₀}`.
  have hP_le : P ≤ camProd e {i₀} := by
    intro g hg
    obtain ⟨b, hb, rfl⟩ := camX_mem_prod.mp hg.1
    refine camX_mem_prod.mpr ⟨b, fun i => ⟨fun hi => (hb i).1 (Finset.mem_singleton.mp hi ▸ hi₀),
      fun hi => ?_⟩, rfl⟩
    have hi_ne : i ≠ i₀ := Finset.notMem_singleton.mp hi
    by_cases hiS : i ∈ S
    · apply camX_eq_one_of_fix_adjKSet hk1 hkm (e x₀ i) (b i)
      · have hx₀ := congrArg (fun u => e u i) hg.2.1
        simpa [camHom_apply] using hx₀
      · intro C hC
        obtain ⟨a, ha, ha_x₀, ha_z⟩ :=
          camX_adjKSet_transitive hm hk1 hk (e x₀ i) (e z i) C (hez_ne i hi_ne ▸ hB i) hC
        let u := camHom e (Pi.mulSingle i a)
        have huCur : u ∈ Cur :=
          camX_prod_mono (Finset.singleton_subset_iff.mpr hiS) (camX_single_mem ha)
        have hu_x₀ : u x₀ = x₀ := by
          apply e.injective
          funext j
          rw [camHom_apply]
          rcases eq_or_ne j i with rfl | hji
          · simp [ha_x₀]
          · simp [Pi.mulSingle_eq_of_ne hji, cam_kSetPerm_one]
        have hu_orb : u z ∈ MulAction.orbit (pointwiseStab Cur [x₀]) z := by
          refine ⟨⟨u, huCur, ?_⟩, rfl⟩
          simp [hu_x₀]
        have hg_uz := congrArg (fun w => e w i) (hg.2.2 (u z) hu_orb)
        have he_uz : e (u z) i = C := by
          change e (camHom e (Pi.mulSingle i a) z) i = C
          rw [camHom_apply_coord, Pi.mulSingle_eq_same, ha_z]
        simpa [camHom_apply_coord, he_uz] using hg_uz
    · exact (hb i).2 hiS
  -- Step 2: `P ≠ ⊥`.
  have hP_ne : P ≠ ⊥ := by
    obtain ⟨a, _, ha_alt, _, ha_x₀, _, hne⟩ := camX_alt_stab_noncomm hm hk1 hk (e x₀ i₀)
    have ha1 : a ≠ 1 := fun h => by subst h; simp at hne
    let g := camHom e (Pi.mulSingle i₀ a)
    have hgP : g ∈ P := by
      refine ⟨camX_prod_mono (Finset.singleton_subset_iff.mpr hi₀) (camX_single_mem ha_alt),
        ?_, ?_⟩
      · apply e.injective
        funext j
        rw [camHom_apply]
        rcases eq_or_ne i₀ j with rfl | hji
        · simp [ha_x₀]
        · simp [Pi.mulSingle_eq_of_ne hji.symm, cam_kSetPerm_one]
      · rintro y ⟨⟨h, hhCur, hh_x₀⟩, rfl⟩
        simp only [List.mem_singleton, forall_eq] at hh_x₀
        obtain ⟨d, hd, rfl⟩ := camX_mem_prod.mp hhCur
        have hd_x₀ : kSetPerm (d i₀) (e x₀ i₀) = e x₀ i₀ := by
          have := congrArg (fun w => e w i₀) hh_x₀
          simpa [camHom_apply_coord] using this
        apply e.injective
        funext j
        change e (camHom e (Pi.mulSingle i₀ a) (camHom e d z)) j = e (camHom e d z) j
        rw [camHom_apply_coord]
        rcases eq_or_ne i₀ j with rfl | hji
        · rw [Pi.mulSingle_eq_same, camHom_apply_coord, hez_i₀, hd_x₀, ha_x₀]
        · rw [Pi.mulSingle_eq_of_ne hji.symm, cam_kSetPerm_one]; rfl
    intro hbot
    have hg1 : g = 1 := Subgroup.mem_bot.mp (hbot ▸ hgP)
    have hpi : Pi.mulSingle (M := fun _ : Fin r => Perm (Fin m)) i₀ a = 1 :=
      camX_camHom_injective hk1 hkm (hg1.trans (map_one (camHom e)).symm)
    exact ha1 (by simpa using congrFun hpi i₀)
  -- Step 3: `camNormClosure Cur P = camProd e {i₀}`.
  have hT_le : camFactorCand Cur x₀ z ≤ camProd e {i₀} :=
    camNormClosure_minimal hP_le (camX_prod_normal S {i₀})
  have hT_ne : camFactorCand Cur x₀ z ≠ ⊥ := camNormClosure_ne_bot hP_ne
  obtain ⟨A, hAsub, hTeq⟩ := camX_normal_prod hm hk1 hkm hT_le fun x hx y hy =>
    camFactorCand_normal Cur x₀ z x (camX_prod_mono (Finset.singleton_subset_iff.mpr hi₀) hx) y hy
  rcases Finset.subset_singleton_iff.mp hAsub with rfl | rfl
  · rw [camX_prod_empty] at hTeq
    exact absurd hTeq hT_ne
  · exact hTeq

/-- Proposition 2.2 (optimality): Any `z` minimizing `Nat.card (camFactorCand (camProd e S) x₀ z)`
among those with `1 < Nat.card (camFactorCand (camProd e S) x₀ z)` gives a single factor
`camProd e {i}` with `i ∈ S`. -/
theorem camFactorCand_min_is_single (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m)
    {S : Finset (Fin r)} (x₀ z : Fin n)
    (hgt : 1 < Nat.card (camFactorCand (camProd e S) x₀ z))
    (hmin : ∀ z' : Fin n, 1 < Nat.card (camFactorCand (camProd e S) x₀ z') →
      Nat.card (camFactorCand (camProd e S) x₀ z) ≤
        Nat.card (camFactorCand (camProd e S) x₀ z')) :
    ∃ i ∈ S, camFactorCand (camProd e S) x₀ z = camProd e {i} := by
  have hkm : k < m := by omega
  have hhalf : 1 < m.factorial / 2 := by
    have := camDirect_choose_lt_half hm k
    have := Nat.choose_pos hkm.le
    omega
  obtain ⟨A, hAS, hAz⟩ := camFactorCand_eq_prod hm hk1 hk S x₀ z
  have hcardA : Nat.card (camFactorCand (camProd e S) x₀ z) = (m.factorial / 2) ^ A.card := by
    rw [hAz, camX_card_prod (by omega) hk1 hkm]
  have hAne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.card_empty, pow_zero] at hcardA
    omega
  have hApos : 0 < A.card := Finset.card_pos.mpr hAne
  obtain ⟨i₀, hi₀A⟩ := hAne
  obtain ⟨z₀, hz₀⟩ := camFactorCand_single hm hk1 hk (hAS hi₀A) x₀
  have hcard0 : Nat.card (camFactorCand (camProd e S) x₀ z₀) = m.factorial / 2 := by
    rw [hz₀, camX_card_prod (by omega) hk1 hkm, Finset.card_singleton, pow_one]
  have hle := hmin z₀ (by omega)
  rw [hcardA, hcard0] at hle
  have hA1 : A.card = 1 := by
    by_contra hne1
    have h2 : 2 ≤ A.card := by omega
    have hlt : (m.factorial / 2) ^ 1 < (m.factorial / 2) ^ A.card :=
      Nat.pow_lt_pow_right hhalf (by omega)
    rw [pow_one] at hlt
    omega
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hA1
  exact ⟨i, hAS (Finset.mem_singleton_self i), hAz⟩

/-! ### 5. Proposition 2.3: Direct socle finding in `G` -/

/-- The candidate socle in `G` associated to base point `x₀` and pair `(y₁, z)`: the normal
closure in `G` of the derived subgroup of the pointwise stabilizer in `G` of `x₀` and the
`G_{x₀, y₁}`-orbit of `z`. -/
def camSocleCand (G : Subgroup (Perm (Fin n))) (x₀ y₁ z : Fin n) :
    Subgroup (Perm (Fin n)) :=
  let P := camOrbStab G (pointwiseStab G [x₀, y₁]) x₀ z
  camNormClosure G ⁅P, P⁆

theorem camSocleCand_le (G : Subgroup (Perm (Fin n))) (x₀ y₁ z : Fin n) :
    camSocleCand G x₀ y₁ z ≤ G := by
  refine camNormClosure_le ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  have haG := camOrbStab_le G _ x₀ z ha
  have hbG := camOrbStab_le G _ x₀ z hb
  exact G.mul_mem (G.mul_mem (G.mul_mem haG hbG) (G.inv_mem haG)) (G.inv_mem hbG)

theorem camSocleCand_normal (G : Subgroup (Perm (Fin n))) (x₀ y₁ z : Fin n) :
    ∀ g ∈ G, ∀ x ∈ camSocleCand G x₀ y₁ z, g * x * g⁻¹ ∈ camSocleCand G x₀ y₁ z :=
  camNormClosure_normal G _

/-- Proposition 2.3 (existence): Under a Maróti structure on a primitive group `G`, for every
base point `x₀ : Fin n`, there exist `y₁, z : Fin n` such that
`camSocleCand G x₀ y₁ z = camProd e Finset.univ` and `1 < Nat.card (camSocleCand G x₀ y₁ z)`. -/
theorem camSocleCand_exists_eq_socle {G : Subgroup (Perm (Fin n))} (hM : MarotiStructure G e)
    (hprim : MulAction.IsPreprimitive G (Fin n)) (hn : 25 ≤ n) (hm : 5 ≤ m) (hk1 : 1 ≤ k)
    (hk : 2 * k < m) (x₀ : Fin n) :
    ∃ y₁ z : Fin n, camSocleCand G x₀ y₁ z = camProd e Finset.univ ∧
      1 < Nat.card (camSocleCand G x₀ y₁ z) := by
  have hkm : k < m := by omega
  have hnr := cam_n_eq e
  have hr : r ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hnr
    omega
  let i₀ : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
  have hadj : ∀ i : Fin r, ∃ B, adjKSet (e x₀ i) B :=
    fun i => camX_exists_adjKSet hk1 hkm (e x₀ i)
  choose B hB using hadj
  let y₁ : Fin n := e.symm (fun i => if i = i₀ then B i₀ else e x₀ i)
  let z : Fin n := e.symm (fun i => if i = i₀ then e x₀ i₀ else B i)
  have hey₁_i₀ : e y₁ i₀ = B i₀ := by simp [y₁]
  have hey₁_ne : ∀ i ≠ i₀, e y₁ i = e x₀ i := fun i hi => by simp [y₁, hi]
  have hez_i₀ : e z i₀ = e x₀ i₀ := by simp [z]
  have hez_ne : ∀ i ≠ i₀, e z i = B i := fun i hi => by simp [z, hi]
  set H₁ := pointwiseStab G [x₀, y₁]
  set P := camOrbStab G H₁ x₀ z
  -- Step 1: Every `g ∈ H₁` fixes coordinate `i₀` and hence maps `z` to a point with `i₀`-th
  -- coordinate `e x₀ i₀`.
  have horb_i₀ : ∀ y ∈ MulAction.orbit H₁ z, e y i₀ = e x₀ i₀ := by
    rintro y ⟨⟨g, hgH₁⟩, rfl⟩
    obtain ⟨hgG, hg_pts⟩ := mem_pointwiseStab.mp hgH₁
    have hg_x₀ : g x₀ = x₀ := hg_pts x₀ (by simp)
    have hg_y₁ : g y₁ = y₁ := hg_pts y₁ (by simp)
    obtain ⟨σ, h, hgh⟩ := hM.1 g hgG
    have hσ_i₀ : σ i₀ = i₀ := by
      by_contra hne
      have hx₀_i₀ := congrFun (hgh x₀) i₀
      have hy₁_i₀ := congrFun (hgh y₁) i₀
      rw [hg_x₀] at hx₀_i₀
      rw [hg_y₁] at hy₁_i₀
      have hint := card_inter_kSetPerm (h i₀) (e x₀ (σ i₀)) (e y₁ (σ i₀))
      rw [← hx₀_i₀, ← hy₁_i₀, hey₁_i₀, hey₁_ne (σ i₀) hne, Finset.inter_self,
        (e x₀ (σ i₀)).2] at hint
      have := hB i₀
      unfold adjKSet at this
      omega
    have hz_i₀ := congrFun (hgh z) i₀
    have hx₀_i₀ := congrFun (hgh x₀) i₀
    rw [hg_x₀, hσ_i₀] at hx₀_i₀
    change e (g z) i₀ = e x₀ i₀
    rw [hz_i₀, hσ_i₀, hez_i₀, ← hx₀_i₀]
  -- Step 2: `⁅P, P⁆ ≠ ⊥`.
  have hD_ne : ⁅P, P⁆ ≠ ⊥ := by
    obtain ⟨a, b, ha_alt, hb_alt, ha_x₀, hb_x₀, hab_ne⟩ :=
      camX_alt_stab_noncomm hm hk1 hk (e x₀ i₀)
    let g₁ := camHom e (Pi.mulSingle i₀ a)
    let g₂ := camHom e (Pi.mulSingle i₀ b)
    have h_memP : ∀ c : Perm (Fin m), c ∈ alternatingGroup (Fin m) →
        kSetPerm c (e x₀ i₀) = e x₀ i₀ → camHom e (Pi.mulSingle i₀ c) ∈ P := by
      intro c hc hc_x₀
      refine ⟨camX_socle_le hM (camX_prod_mono (Finset.subset_univ {i₀}) (camX_single_mem hc)),
        ?_, ?_⟩
      · apply e.injective
        funext j
        rw [camHom_apply_coord]
        rcases eq_or_ne i₀ j with rfl | hji
        · rw [Pi.mulSingle_eq_same, hc_x₀]
        · rw [Pi.mulSingle_eq_of_ne hji.symm, cam_kSetPerm_one]; rfl
      · intro y hy
        apply e.injective
        funext j
        rw [camHom_apply_coord]
        rcases eq_or_ne i₀ j with rfl | hji
        · rw [Pi.mulSingle_eq_same, horb_i₀ y hy, hc_x₀]
        · rw [Pi.mulSingle_eq_of_ne hji.symm, cam_kSetPerm_one]; rfl
    have hg₁P : g₁ ∈ P := h_memP a ha_alt ha_x₀
    have hg₂P : g₂ ∈ P := h_memP b hb_alt hb_x₀
    have hcomm_mem : ⁅g₁, g₂⁆ ∈ ⁅P, P⁆ := Subgroup.commutator_mem_commutator hg₁P hg₂P
    intro hbot
    have hcomm1 : ⁅g₁, g₂⁆ = 1 := Subgroup.mem_bot.mp (hbot ▸ hcomm_mem)
    have hmap : ⁅g₁, g₂⁆ = camHom e (Pi.mulSingle i₀ ⁅a, b⁆) := by
      simp only [g₁, g₂, commutatorElement_def, ← map_inv, ← map_mul, ← Pi.mulSingle_inv,
        ← Pi.mulSingle_mul]
    rw [hmap] at hcomm1
    have hpi : Pi.mulSingle (M := fun _ : Fin r => Perm (Fin m)) i₀ ⁅a, b⁆ = 1 :=
      camX_camHom_injective hk1 hkm (hcomm1.trans (map_one (camHom e)).symm)
    have hab1 : ⁅a, b⁆ = 1 := by simpa using congrFun hpi i₀
    exact hab_ne (commutatorElement_eq_one_iff_mul_comm.mp hab1)
  -- Step 3: Every `g ∈ P` acts as `1` outside coordinate `i₀`, so `⁅P, P⁆ ≤ camProd e univ`.
  have h_z_upd : ∀ j ≠ i₀, ∀ C, adjKSet (e x₀ j) C →
      e.symm (Function.update (e z) j C) ∈ MulAction.orbit H₁ z := by
    intro j hj C hC
    obtain ⟨a, ha, ha_x₀, ha_z⟩ :=
      camX_adjKSet_transitive hm hk1 hk (e x₀ j) (e z j) C (hez_ne j hj ▸ hB j) hC
    let u := camHom e (Pi.mulSingle j a)
    have huG : u ∈ G :=
      camX_socle_le hM (camX_prod_mono (Finset.subset_univ {j}) (camX_single_mem ha))
    have hu_x₀ : u x₀ = x₀ := by
      apply e.injective
      funext i
      change e (camHom e (Pi.mulSingle j a) x₀) i = e x₀ i
      rw [camHom_apply_coord]
      rcases eq_or_ne j i with rfl | hij
      · rw [Pi.mulSingle_eq_same, ha_x₀]
      · rw [Pi.mulSingle_eq_of_ne hij.symm, cam_kSetPerm_one]; rfl
    have hu_y₁ : u y₁ = y₁ := by
      apply e.injective
      funext i
      change e (camHom e (Pi.mulSingle j a) y₁) i = e y₁ i
      rw [camHom_apply_coord]
      rcases eq_or_ne j i with rfl | hij
      · rw [Pi.mulSingle_eq_same, hey₁_ne j hj, ha_x₀]
      · rw [Pi.mulSingle_eq_of_ne hij.symm, cam_kSetPerm_one]; rfl
    have hu_z : u z = e.symm (Function.update (e z) j C) := by
      apply e.injective
      rw [Equiv.apply_symm_apply]
      funext i
      change e (camHom e (Pi.mulSingle j a) z) i = Function.update (e z) j C i
      rw [camHom_apply_coord]
      rcases eq_or_ne j i with rfl | hij
      · rw [Pi.mulSingle_eq_same, Function.update_self, ha_z]
      · rw [Pi.mulSingle_eq_of_ne hij.symm, Function.update_of_ne hij.symm, cam_kSetPerm_one]; rfl
    refine ⟨⟨u, huG, ?_⟩, hu_z⟩
    simp [hu_x₀, hu_y₁]
  have hP_single : ∀ g ∈ P, ∃ d : Perm (Fin m), g = camHom e (Pi.mulSingle i₀ d) := by
    intro g hg
    obtain ⟨σ, h, hgh⟩ := hM.1 g hg.1
    have hgz : g z = z := hg.2.2 z (MulAction.mem_orbit_self z)
    have hσ_ne : ∀ j ≠ i₀, σ j = j := by
      intro j hj
      obtain ⟨C, hC, hCne⟩ := camX_exists_adjKSet_ne hk1 (by omega) (e x₀ j) (e z j)
      let z' := e.symm (Function.update (e z) j C)
      have hgz' : g z' = z' := hg.2.2 z' (h_z_upd j hj C hC)
      have e1 := congrFun (hgh z) j
      have e2 := congrFun (hgh z') j
      rw [hgz] at e1
      rw [hgz'] at e2
      by_contra hσj
      have heq : e z' (σ j) = e z (σ j) := by
        simp [z', Function.update_of_ne hσj]
      rw [heq, ← e1] at e2
      have : e z' j = C := by simp [z']
      exact hCne (this ▸ e2)
    have hσ_i₀ : σ i₀ = i₀ := by
      by_contra hne
      exact hne (σ.injective (hσ_ne (σ i₀) hne))
    have hh_ne : ∀ j ≠ i₀, h j = 1 := by
      intro j hj
      apply camX_eq_one_of_fix_adjKSet hk1 hkm (e x₀ j) (h j)
      · have hx₀_j := congrFun (hgh x₀) j
        rw [hg.2.1, hσ_ne j hj] at hx₀_j
        exact hx₀_j.symm
      · intro C hC
        let z' := e.symm (Function.update (e z) j C)
        have hgz' : g z' = z' := hg.2.2 z' (h_z_upd j hj C hC)
        have hz'_j := congrFun (hgh z') j
        rw [hgz', hσ_ne j hj] at hz'_j
        simpa [z'] using hz'_j.symm
    refine ⟨h i₀, Equiv.ext fun x => e.injective (funext fun i => ?_)⟩
    rw [hgh x, camHom_apply_coord]
    rcases eq_or_ne i i₀ with rfl | hii₀
    · simp [hσ_i₀]
    · simp [hσ_ne i hii₀, hh_ne i hii₀, Pi.mulSingle_eq_of_ne hii₀, cam_kSetPerm_one]
  have hD_le : ⁅P, P⁆ ≤ camProd e Finset.univ := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨d₁, rfl⟩ := hP_single g₁ hg₁
    obtain ⟨d₂, rfl⟩ := hP_single g₂ hg₂
    have hmap : ⁅camHom e (Pi.mulSingle i₀ d₁), camHom e (Pi.mulSingle i₀ d₂)⁆ =
        camHom e (Pi.mulSingle i₀ ⁅d₁, d₂⁆) := by
      simp only [commutatorElement_def, ← map_inv, ← map_mul, ← Pi.mulSingle_inv,
        ← Pi.mulSingle_mul]
    rw [hmap]
    refine camX_prod_mono (Finset.subset_univ {i₀}) (camX_single_mem ?_)
    rw [Equiv.Perm.mem_alternatingGroup, commutatorElement_def, map_mul, map_mul, map_mul,
      map_inv, map_inv, mul_right_comm (Perm.sign d₁), mul_inv_cancel_right, mul_inv_cancel]
  -- Step 4: `camSocleCand G x₀ y₁ z = camProd e Finset.univ`.
  have hM_le : camSocleCand G x₀ y₁ z ≤ camProd e Finset.univ :=
    camNormClosure_minimal hD_le (camX_socle_normal hM)
  have hM_ne : camSocleCand G x₀ y₁ z ≠ ⊥ := camNormClosure_ne_bot hD_ne
  have hsoc_le : camProd e Finset.univ ≤ camSocleCand G x₀ y₁ z :=
    camX_socle_le_every_normal hM hprim hn hm hk1 hk
      (camSocleCand_le G x₀ y₁ z) hM_ne (camSocleCand_normal G x₀ y₁ z)
  have heq : camSocleCand G x₀ y₁ z = camProd e Finset.univ := le_antisymm hM_le hsoc_le
  refine ⟨y₁, z, heq, ?_⟩
  rw [heq, camX_card_prod (by omega) hk1 hkm, Finset.card_univ, Fintype.card_fin]
  have hhalf : 1 < m.factorial / 2 := by
    have := camDirect_choose_lt_half hm k
    have := Nat.choose_pos hkm.le
    omega
  exact Nat.one_lt_pow hr hhalf

/-- Proposition 2.3 (optimality): Any `(y₁, z)` minimizing `Nat.card (camSocleCand G x₀ y₁ z)`
among those with `1 < Nat.card (camSocleCand G x₀ y₁ z)` satisfies
`camSocleCand G x₀ y₁ z = camProd e Finset.univ`. -/
theorem camSocleCand_min_eq_socle {G : Subgroup (Perm (Fin n))} (hM : MarotiStructure G e)
    (hprim : MulAction.IsPreprimitive G (Fin n)) (hn : 25 ≤ n) (hm : 5 ≤ m) (hk1 : 1 ≤ k)
    (hk : 2 * k < m) (x₀ y₁ z : Fin n)
    (hgt : 1 < Nat.card (camSocleCand G x₀ y₁ z))
    (hmin : ∀ y₁' z' : Fin n, 1 < Nat.card (camSocleCand G x₀ y₁' z') →
      Nat.card (camSocleCand G x₀ y₁ z) ≤ Nat.card (camSocleCand G x₀ y₁' z')) :
    camSocleCand G x₀ y₁ z = camProd e Finset.univ := by
  have hne : camSocleCand G x₀ y₁ z ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hgt
    omega
  obtain ⟨y₁₀, z₀, heq₀, hgt₀⟩ := camSocleCand_exists_eq_socle hM hprim hn hm hk1 hk x₀
  have hle := hmin y₁₀ z₀ hgt₀
  rw [heq₀] at hle
  exact camX_eq_socle_of_card_le hM hprim hn hm hk1 hk
    (camSocleCand_le G x₀ y₁ z) hne (camSocleCand_normal G x₀ y₁ z) hle

end GI.Impl
