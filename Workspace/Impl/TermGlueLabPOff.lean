import Workspace.Impl.TermGlueLabPRep
import Workspace.Impl.TermGlueLabLift

/-!
# The offsets from transporters computed row by row

Step 3 of the label program. The offset is
`u(h) = Π_i [t_{a_i}(h)] · Π_i [h⁻¹ k_i(h)]`, with `t_a(h) ∈ N` and
`(z_a)^h = (z_{a^h})^{t_a(h)}` for the representatives `z_a` ("for a later `h` carrying type `a`
to type `c` ... supplies the required local `N`-transporter").

The program computes a transporter `s_i` for every row `i` (for the representative of the type
of `x_i`), by a NormalizedFactor call, so two rows of one type may get different transporters.
This does not matter: two transporters with the same source and target differ by a stabilizer of
a row of a type of `x`, whose class in `A/B(x)` is trivial (`tmGL_aut_label`). So any such
`s_i` give the official product (`tmGLP_off_rows`), and with any lift `k(h) ν`, `ν` zero-sum,
the offset `u(h)` (`tmGLP_u_rows`).
-/

namespace GI.Impl

open GI.Multicoset Equiv

variable {P : Type*} [Group P] {Ω : Type} [RAct P Ω] {q : ℕ}
variable {N H : Subgroup P} {A : Type*} [CommGroup A] {φ : N →* A} {x : Fin q → Ω}

/-- **Two transporters between the same rows have the same class.** -/
theorem tmGLP_c_trans_eq {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) {a : Set Ω}
    (ha : a ∈ types N x) {s t : P} (hs : s ∈ N) (ht : t ∈ N) {Z : Ω}
    (hsZ : rep a ↼ s = Z) (htZ : rep a ↼ t = Z) : tmGLc N φ x s = tmGLc N φ x t := by
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp ha
  obtain ⟨c, hc, hce⟩ := hrep j
  -- `s t⁻¹` fixes the representative `x_j^c`
  have hst : s * t⁻¹ ∈ Aut N (x j ↼ c) := by
    refine mem_aut.mpr ⟨N.mul_mem hs (N.inv_mem ht), ?_⟩
    rw [hce, ← act_act, hsZ, ← htZ, act_act, mul_inv_cancel, act_one]
  have h1 := tmGLc_eq_one (x := x) (N.mul_mem hs (N.inv_mem ht)) (tmGL_aut_label (φ := φ) hc hst)
  rw [tmGLc_mul hs (N.inv_mem ht), tmGLc_inv ht, mul_inv_eq_one] at h1
  exact h1

/-- **Row-by-row transporters give the official product.** -/
theorem tmGLP_off_rows (hn : Normalizes H N) {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) {h : P}
    (hD : h ∈ Aut H (types N x)) {s : Fin q → P} (hs : ∀ i, s i ∈ N)
    (hsr : ∀ i, rep (orbitN N (x i)) ↼ h = rep (orbitN N (x i) ↼ h) ↼ s i) :
    ∏ i, tmGLc N φ x (s i) = ∏ i, tmGLc N φ x (tmGLtch N x rep h (orbitN N (x i))) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  have hT := tmGLtch_spec hn hrep hD
  have hai : orbitN N (x i) ∈ types N x := Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  obtain ⟨htN, htr⟩ := hT _ hai
  have hah : orbitN N (x i) ↼ h ∈ types N x := hD.2 ▸ act_mem_act h hai
  exact tmGLP_c_trans_eq hrep hah (hs i) htN (hsr i).symm htr.symm

/-- **The offset from row-by-row transporters and any lift** `k(h) ν`, `ν` zero-sum. -/
theorem tmGLP_u_rows (hn : Normalizes H N) (hker : TmGLKer N H φ)
    {k : P → Fin q → P} (hk : TmGLLift N H φ k) {rep : Set Ω → Ω} (hrep : TmGLRep N x rep)
    {h : P} (hD : h ∈ Aut H (types N x)) {s : Fin q → P} (hs : ∀ i, s i ∈ N)
    (hsr : ∀ i, rep (orbitN N (x i)) ↼ h = rep (orbitN N (x i) ↼ h) ↼ s i)
    {ν : Fin q → P} (hν : TmGLZero N φ ν) :
    (∏ i, tmGLc N φ x (s i)) * ∏ i, tmGLc N φ x (h⁻¹ * (k h i * ν i)) = tmGLu N φ x rep k h := by
  rw [tmGLP_off_rows hn hrep hD hs hsr]
  exact tmGLu_indep (hn := hn) (hker := hker) hk hrep hD (tmGLtch_spec hn hrep hD) hν

end GI.Impl
