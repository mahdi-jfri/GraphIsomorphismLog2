import Workspace.Proved.VsMBasic

/-!
# The nondegenerate pairing (M4) and the least spin (M5)

* `vsM_indep` (`VsMIndepStmt`): let `N ≤ C(A)` have commutators in `S`, and suppose every
  element of `N` central in `N` lies in `S`. Then `|N : N ∩ S| ≤ (dim V)^2`.
  *Proof.* Take one element `x_q` in each coset `q` of `N ∩ S`. For `y ∈ N` we have
  `y x_q y⁻¹ = ψ_q(y) x_q` with `ψ_q(y) = ⁅y, x_q⁆ ∈ L`. Distinct cosets have distinct `ψ`
  (else `x_{q'}⁻¹ x_q` is central, so in `S`). Then the `x_q` are linearly independent over `L`
  (Artin's argument, by induction on the support, `vsM_indep_aux`), so over `𝔽_p`, and there
  are at most `dim End V = (dim V)^2` of them.
* `vsM_least` (`VsMLeastStmt`): if the spin of `x₀` has the least size modulo `S` among the
  spins of its elements outside `S`, it is minimal.
-/

namespace GI.Proved

open Module
open scoped commutatorElement IsMulCommutative

variable {p : ℕ} [hp : Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

local notation "𝔼" => End (ZMod p) V

/-- Artin's argument: elements `x_i ∈ N` with pairwise distinct characters `⁅·, x_i⁆` are
linearly independent over `L`. -/
theorem vsM_indep_aux [FiniteDimensional (ZMod p) V] {A N : Subgroup 𝔼ˣ}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hdom : vsTDom (vsTAlg A))
    (hNC : N ≤ Subgroup.centralizer (A : Set 𝔼ˣ)) (hc : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ vsMScal A)
    {ι : Type*} [DecidableEq ι] (xs : ι → 𝔼ˣ) (hxs : ∀ i, xs i ∈ N)
    (hdist : ∀ i j, i ≠ j → ∃ y ∈ N, ⁅y, xs i⁆ ≠ ⁅y, xs j⁆) :
    ∀ (s : Finset ι) (c : ι → 𝔼), (∀ i, c i ∈ vsTAlg A) →
      ∑ i ∈ s, c i * (xs i : 𝔼) = 0 → ∀ i ∈ s, c i = 0 := by
  have hLc := vsTAlg_comm hA
  -- `ψ i y`
  let ψ : ι → 𝔼ˣ → 𝔼 := fun i y => ((⁅y, xs i⁆ : 𝔼ˣ) : 𝔼)
  have hψL : ∀ i, ∀ y ∈ N, ψ i y ∈ vsTAlg A := fun i y hy => (hc y hy _ (hxs i)).1
  intro s
  induction s using Finset.induction_on with
  | empty => intro c _ _ i hi; simp at hi
  | insert i0 s hi0 ih =>
    intro c hcL hsum
    rw [Finset.sum_insert hi0] at hsum
    -- the derived relations
    have hder : ∀ y ∈ N, ∀ i ∈ s, c i * (ψ i y - ψ i0 y) = 0 := by
      intro y hy
      apply ih (fun i => c i * (ψ i y - ψ i0 y))
      · intro i
        exact mul_mem (hcL i) (sub_mem (hψL i y hy) (hψL i0 y hy))
      -- conjugating the relation by `y`
      have hterm : ∀ i, (y : 𝔼) * (c i * (xs i : 𝔼)) * ((y⁻¹ : 𝔼ˣ) : 𝔼) =
          c i * ψ i y * (xs i : 𝔼) := by
        intro i
        have hyc : (y : 𝔼) * c i = c i * y := vsM_comm_alg (hNC hy) (hcL i)
        have hx : (y : 𝔼) * (xs i : 𝔼) * ((y⁻¹ : 𝔼ˣ) : 𝔼) = ψ i y * (xs i : 𝔼) := by
          simp only [ψ, commutatorElement_def, Units.val_mul, mul_assoc, Units.inv_mul,
            mul_one]
        calc (y : 𝔼) * (c i * (xs i : 𝔼)) * ((y⁻¹ : 𝔼ˣ) : 𝔼)
            = c i * ((y : 𝔼) * (xs i : 𝔼) * ((y⁻¹ : 𝔼ˣ) : 𝔼)) := by
              rw [← mul_assoc, hyc]; simp only [mul_assoc]
          _ = c i * ψ i y * (xs i : 𝔼) := by rw [hx, mul_assoc]
      have h1 : c i0 * ψ i0 y * (xs i0 : 𝔼) + ∑ i ∈ s, c i * ψ i y * (xs i : 𝔼) = 0 := by
        have := congrArg (fun z : 𝔼 => (y : 𝔼) * z * ((y⁻¹ : 𝔼ˣ) : 𝔼)) hsum
        simp only [mul_zero, zero_mul, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul] at this
        rw [hterm, Finset.sum_congr rfl (fun i _ => hterm i)] at this
        exact this
      have h2 : c i0 * ψ i0 y * (xs i0 : 𝔼) + ∑ i ∈ s, c i * ψ i0 y * (xs i : 𝔼) = 0 := by
        have := congrArg (fun z : 𝔼 => ψ i0 y * z) hsum
        simp only [mul_zero, mul_add, Finset.mul_sum] at this
        have hcm : ∀ i, ψ i0 y * (c i * (xs i : 𝔼)) = c i * ψ i0 y * (xs i : 𝔼) := by
          intro i
          rw [← mul_assoc, (hLc _ (hψL i0 y hy) _ (hcL i)).eq]
        rw [hcm, Finset.sum_congr rfl (fun i _ => hcm i)] at this
        exact this
      have h3 := congrArg₂ (· - ·) h1 h2
      simp only [sub_self, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib] at h3
      rw [← h3]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_sub, sub_mul]
    -- each `c i` with `i ∈ s` vanishes
    have hs0 : ∀ i ∈ s, c i = 0 := by
      intro i hi
      have hne : i ≠ i0 := fun h => hi0 (h ▸ hi)
      obtain ⟨y, hy, hyne⟩ := hdist i i0 hne
      have hd0 : ψ i y - ψ i0 y ≠ 0 := by
        intro h
        apply hyne
        exact Units.ext (sub_eq_zero.1 h)
      rcases hdom _ (sub_mem (hψL i y hy) (hψL i0 y hy)) with h | hinj
      · exact absurd h hd0
      have h0 := hder y hy i hi
      rw [(hLc _ (hcL i) _ (sub_mem (hψL i y hy) (hψL i0 y hy))).eq] at h0
      ext v
      exact hinj _ (by simpa using congrArg (fun f : 𝔼 => f v) h0)
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [Finset.sum_eq_zero (fun j hj => by rw [hs0 j hj, zero_mul]), add_zero] at hsum
      calc c i = c i * (xs i : 𝔼) * (((xs i)⁻¹ : 𝔼ˣ) : 𝔼) := by
            rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
        _ = 0 := by rw [hsum, zero_mul]
    · exact hs0 i hi

/-- **M4, nondegenerate case** (`VsMIndepStmt`). -/
theorem vsM_indep [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMIndepStmt p V := by
  intro A N hA hdom hNC hc hrad
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  set Q := N ⧸ (vsMScal A).subgroupOf N
  haveI : Fintype Q := Fintype.ofFinite Q
  let xs : Q → 𝔼ˣ := fun q => ((q.out : N) : 𝔼ˣ)
  have hxs : ∀ q, xs q ∈ N := fun q => q.out.2
  have hdist : ∀ i j : Q, i ≠ j → ∃ y ∈ N, ⁅y, xs i⁆ ≠ ⁅y, xs j⁆ := by
    intro i j hij
    by_contra hall
    push Not at hall
    apply hij
    set a := xs i
    set b := xs j
    have hz : b⁻¹ * a ∈ vsMScal A := by
      apply hrad _ (N.mul_mem (N.inv_mem (hxs j)) (hxs i))
      intro y hy
      have h := hall y⁻¹ (N.inv_mem hy)
      simp only [commutatorElement_def, inv_inv] at h
      calc b⁻¹ * a * y = b⁻¹ * (y * (y⁻¹ * a * y * a⁻¹)) * a := by group
        _ = b⁻¹ * (y * (y⁻¹ * b * y * b⁻¹)) * a := by rw [h]
        _ = y * (b⁻¹ * a) := by group
    rw [← QuotientGroup.out_eq' i, ← QuotientGroup.out_eq' j, eq_comm, QuotientGroup.eq,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hz
  have hli : LinearIndependent (ZMod p) (fun q => ((xs q : 𝔼ˣ) : 𝔼)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h := vsM_indep_aux hA hdom hNC (fun x hx y hy => hc x hx y hy) xs hxs hdist s
      (fun q => algebraMap (ZMod p) 𝔼 (g q)) (fun q => Subalgebra.algebraMap_mem _ _)
      (by simpa [Algebra.smul_def] using hg) i hi
    exact (algebraMap (ZMod p) 𝔼).injective (by rw [map_zero]; exact h)
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_linearMap, ← pow_two] at hcard
  calc (vsMScal A).relIndex N = Fintype.card Q := by
        rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
    _ ≤ _ := hcard

/-- **M5** (`VsMLeastStmt`). -/
theorem vsM_least [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMLeastStmt p V := by
  intro H S x0 hS hx0 hmin y hy hyS
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  set Y0 := vsMSpin H x0
  -- conjugation by `h ∈ H` maps `Y0` into itself
  have hY0 : ∀ h ∈ H, ∀ z ∈ Y0, h * z * h⁻¹ ∈ Y0 := by
    intro h hh z hz
    have hle : Y0.map (MulAut.conj h).toMonoidHom ≤ Y0 := by
      rw [show Y0 = Subgroup.closure _ from rfl, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨h * k, H.mul_mem hh hk, by simp [mul_assoc]⟩
    exact hle ⟨z, hz, rfl⟩
  have hspin : vsMSpin H y ≤ Y0 := by
    rw [show vsMSpin H y = Subgroup.closure _ from rfl, Subgroup.closure_le]
    rintro _ ⟨h, hh, rfl⟩
    exact hY0 h hh y hy
  set M := vsMSpin H y ⊔ S
  set M' := Y0 ⊔ S
  have hMM' : M ≤ M' := sup_le_sup_right hspin S
  have h1 := Subgroup.relIndex_mul_relIndex S M M' le_sup_right hMM'
  have h2 := hmin y hy hyS
  have hpos : S.relIndex M ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h3 : M.relIndex M' = 1 := by
    have h4 : S.relIndex M * M.relIndex M' ≤ S.relIndex M * 1 := by rw [h1, mul_one]; exact h2
    have h5 := Nat.le_of_mul_le_mul_left h4 (Nat.pos_of_ne_zero hpos)
    have h6 : M.relIndex M' ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.1 h3)

end GI.Proved
