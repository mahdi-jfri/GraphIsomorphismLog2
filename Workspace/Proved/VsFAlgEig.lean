import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The Frobenius map and eigenspaces over `ZMod p`

In an algebra over `ZMod p`, the map `x ↦ x ^ p` is additive on commuting elements. An
endomorphism `s` with `s ^ p = s` is diagonalizable with eigenvalues in `ZMod p`, because
`X ^ p - X` is the product of all `X - c`. For a commuting family of such maps, the joint
eigenspaces are independent and span the space.

* `vsFA_add_pow`, `vsFA_sub_pow`, `vsFA_sub_scalar_pow`: the Frobenius map on commuting elements.
* `vsFA_maxGen_eq`: for `s ^ p = s`, generalized eigenspaces are eigenspaces.
* `vsFA_iSup_eig`: for `s ^ p = s`, the eigenspaces of `s` span the space.
* `vsFA_iSup_joint`, `vsFA_indep_joint`: the same for joint eigenspaces of a commuting family.
-/

namespace GI.Proved

open Module Polynomial

section Frob

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [Ring A] [Algebra (ZMod p) A]

theorem vsFA_add_pow {x y : A} (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  · haveI : CharP A p := charP_of_injective_algebraMap (algebraMap (ZMod p) A).injective p
    exact add_pow_char_of_commute (R := A) (p := p) (x := x) (y := y) h

theorem vsFA_sub_pow {x y : A} (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  · haveI : CharP A p := charP_of_injective_algebraMap (algebraMap (ZMod p) A).injective p
    exact sub_pow_char_of_commute (R := A) (p := p) (x := x) (y := y) h

theorem vsFA_smul_pow (c : ZMod p) (x : A) : (c • x) ^ p = c • x ^ p := by
  rw [smul_pow, ZMod.pow_card]

theorem vsFA_sub_scalar_pow (x : A) (c : ZMod p) :
    (x - algebraMap (ZMod p) A c) ^ p = x ^ p - algebraMap (ZMod p) A c := by
  rw [vsFA_sub_pow (Algebra.commutes c x).symm, ← map_pow, ZMod.pow_card]

omit hp in
theorem vsFA_pow_pow_eq {t : A} (ht : t ^ p = t) (j : ℕ) : t ^ (p ^ j) = t := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, pow_mul, ih, ht]

end Frob

section Eig

variable {p : ℕ} [hp : Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- For `s ^ p = s`, every generalized eigenspace is an eigenspace: `t = s - μ` has `t ^ p = t`,
so `t ^ k v = 0` gives `t v = t ^ (p ^ k) v = 0`. -/
theorem vsFA_maxGen_eq (s : End (ZMod p) V) (hs : s ^ p = s) (μ : ZMod p) :
    s.maxGenEigenspace μ = s.eigenspace μ := by
  refine le_antisymm ?_ Module.End.eigenspace_le_maxGenEigenspace
  intro v hv
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨k, hk⟩ := hv
  rw [Module.End.eigenspace_def, LinearMap.mem_ker]
  have ht : (s - μ • 1) ^ p = s - μ • 1 := by
    have := vsFA_sub_scalar_pow (p := p) s μ
    rwa [hs, Algebra.algebraMap_eq_smul_one] at this
  have hk' : k ≤ p ^ k := (Nat.lt_pow_self hp.out.one_lt).le
  rw [← vsFA_pow_pow_eq ht k, ← Nat.sub_add_cancel hk', pow_add, Module.End.mul_apply, hk,
    map_zero]

theorem vsFA_ker_prod (s : End (ZMod p) V) (S : Finset (ZMod p)) :
    LinearMap.ker (aeval s (∏ c ∈ S, (X - C c))) = ⨆ c ∈ S, s.eigenspace c := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, ← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime, ih,
      Finset.iSup_insert]
    · congr 1
      rw [Module.End.eigenspace_def]
      simp [Algebra.algebraMap_eq_smul_one]
    · exact IsCoprime.prod_right fun c hc =>
        pairwise_coprime_X_sub_C (s := id) Function.injective_id (fun h => ha (h ▸ hc))

theorem vsFA_prod_X_sub_C : (∏ c : ZMod p, (X - C c)) = (X ^ p - X : (ZMod p)[X]) := by
  have hm : (X ^ p - X : (ZMod p)[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hp.out.one_lt)
  have hr := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card] at hr
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm, hr, Finset.prod_eq_multiset_prod]
  rw [hr, Finset.card_val, Finset.card_univ, ZMod.card,
    FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.out.one_lt]

/-- For `s ^ p = s`, the eigenspaces of `s` span the space: the kernel of `s ^ p - s` is
everything, and it is the sum of the kernels of the coprime factors `s - c`. -/
theorem vsFA_iSup_eig (s : End (ZMod p) V) (hs : s ^ p = s) : ⨆ c, s.eigenspace c = ⊤ := by
  have h := vsFA_ker_prod s Finset.univ
  rw [vsFA_prod_X_sub_C] at h
  simp only [Finset.mem_univ, iSup_pos] at h
  rw [← h, eq_top_iff]
  intro v _
  simp [hs]

theorem vsFA_iSup_joint [FiniteDimensional (ZMod p) V] {ι : Type*} (f : ι → End (ZMod p) V)
    (hc : ∀ i j, Commute (f i) (f j)) (hf : ∀ i, f i ^ p = f i) :
    ⨆ a : ι → ZMod p, ⨅ i, (f i).eigenspace (a i) = ⊤ := by
  have := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f (fun i j _ => hc i j) (fun i => by simp_rw [vsFA_maxGen_eq _ (hf i)]; exact vsFA_iSup_eig _ (hf i))
  simpa only [vsFA_maxGen_eq _ (hf _)] using this

theorem vsFA_indep_joint {ι : Type*} (f : ι → End (ZMod p) V)
    (hc : ∀ i j, Commute (f i) (f j)) (hf : ∀ i, f i ^ p = f i) :
    iSupIndep fun a : ι → ZMod p => ⨅ i, (f i).eigenspace (a i) := by
  have := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc _ _) φ)
  simpa only [vsFA_maxGen_eq _ (hf _)] using this

end Eig

end GI.Proved
