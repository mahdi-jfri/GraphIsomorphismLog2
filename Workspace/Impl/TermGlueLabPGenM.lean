module

public import Workspace.Impl.TermGlueLabPGen

@[expose] public section

/-!
# The item of one generator is the contract's item (step 5, math link)

Step 5 of the label program (proof of Theorem A.23). `tmGLPGen_spec` returns a
value with the facts `TmGLPGenOut`. Here we show that this value is exactly the item
`tmGLAffItem gs (tmGLQMod D) ρ c g` of the affine procedure, with the linear part
`ρ = E ∘ λ ∘ E⁻¹` (`λ(g) = κ_{g⁻¹}`, `tmGLlam`) and the offsets `c = E ∘ o`, `o(g) = u(g⁻¹)`
(`tmGLo`), for the representatives `tmGLPRep` (first rows of the types) and any lift `k`
(`TmGLLift`) such that every blockwise lift of `h` is `k(h) ν` with `ν` zero-sum
(hypothesis `hyk`; in the row form this is `tmGLP_lift_zero` with `k = rowLift`).

* the matrices: `tmGLP_item_mat`, `tmGLP_item_mat_inv`;
* the offsets: `tmGLP_item_off` with `tmGLP_item_u`, whose row transporters come from
  `tmGLP_off_item` (`tmGLP_half_val`).
-/

namespace GI.Impl

open GI.Multicoset Equiv
open GI.Algorithm (State)
open GI.Cited (Val encPerm encGroup encIntMatrix gens)
open GI.Lang (linVecVal encPerm_injective)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]
variable {N H : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] {φ : N →* A}

/-- **The lift parts lie in `N` after the shift.** If `y = k(h⁻¹) ν` with `ν` zero-sum, then
`h y_i ∈ N` (`TmGLLift.cls` at `h⁻¹`). -/
theorem tmGLP_lift_memN {q : ℕ} {k : Perm (Fin n) → Fin q → Perm (Fin n)} (hk : TmGLLift N H φ k)
    {h : Perm (Fin n)} (hh : h ∈ H) {y ν : Fin q → Perm (Fin n)} (hν : TmGLZero N φ ν)
    (hy : ∀ i, y i = k h⁻¹ i * ν i) (i : Fin q) : h * y i ∈ N := by
  have h1 := hk.cls h⁻¹ (H.inv_mem hh) i
  rw [inv_inv] at h1
  rw [hy i, ← mul_assoc]
  exact N.mul_mem h1 (hν.1 i)

variable {Ω₀ C₀ : Type} {S : State Ω₀ C₀} {L : GI.Algorithm.GiantLabels S}

/-- **The offset vector of one element is the contract's.** -/
theorem tmGLP_half_val (hn : Normalizes H N) (hker : TmGLKer N H φ)
    {k : Perm (Fin n) → Fin L.q → Perm (Fin n)} (hk : TmGLLift N H φ k)
    (E : Fin n × Fin L.q ≃ S.dom) (i0 j0 : Fin L.q) {x : Fin L.q → Ω}
    (hyk : ∀ h ∈ H, ∀ y : Fin L.q → Perm (Fin n), GI.Paper.cleanRowPerm E y ∈ S.domGroup →
      y i0 = h → ∃ ν, TmGLZero N φ ν ∧ ∀ i, y i = k h i * ν i)
    {σN : List (Perm (Fin n))} (hN : gens σN = N)
    {V D : Matrix (Fin σN.length) (Fin σN.length) ℤ} (hpos : ∀ i, 0 < D i i)
    (E' : Additive (tmGLV N φ x) ≃+ tmGLVec (tmGLQMod D))
    (hE' : ∀ z, E' (tmGLPg N φ x (fun i => σN[i.val]) z) = tmGLQMap V D z)
    {gs : List (Perm (Fin n))} (hgs : gens gs ≤ Aut H (types N x)) (g : gens gs) {w : Val}
    (hw : TmGLPHalfOut E i0 σN x V (fun i => D i i) (g : Perm (Fin n)) w) :
    w = linVecVal (tmGLVecZ (tmGLcE E' (tmGLo (tmGLPRep N x j0) k) g)) := by
  subst hN
  obtain ⟨J, s, y, zs, hit, hy, hy0, hz, rfl⟩ := hw
  have hD : (g : Perm (Fin n))⁻¹ ∈ Aut H (types (gens σN) x) := hgs ((gens gs).inv_mem g.2)
  have hgH : (g : Perm (Fin n)) ∈ H := by simpa using H.inv_mem (mem_aut.mp hD).1
  -- the row transporters
  have hrow : ∀ i, s i ∈ gens σN ∧
      tmGLPRep (gens σN) x j0 (orbitN (gens σN) (x i)) ↼ (g : Perm (Fin n))⁻¹ =
        tmGLPRep (gens σN) x j0 (orbitN (gens σN) (x i) ↼ (g : Perm (Fin n))⁻¹) ↼ s i := by
    intro i
    obtain ⟨j, s', hs', he, -, hr⟩ := tmGLP_off_item hn j0 hD (hit i)
    have hss : s i = s' := by
      simp only [Val.list.injEq, List.cons.injEq, and_true] at he
      exact encPerm_injective he.2
    rw [hss]
    exact ⟨hs', hr⟩
  -- the lift
  obtain ⟨ν, hν, hyν⟩ := hyk _ (H.inv_mem hgH) y hy hy0
  have hx : ∀ z ∈ List.ofFn s ++ List.ofFn (fun i => (g : Perm (Fin n)) * y i), z ∈ gens σN := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact (hrow i).1
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact tmGLP_lift_memN hk hgH hν hyν i
  have hu := tmGLP_item_u hn hker hk (tmGLP_rep_ok (gens σN) x j0) g hD (fun i => (hrow i).1)
    (fun i => (hrow i).2) hν
  have hyf : (fun i => (g : Perm (Fin n)) * y i) =
      fun i => (g : Perm (Fin n)) * (k (g : Perm (Fin n))⁻¹ i * ν i) := by
    funext i; rw [hyν i]
  rw [← hyf] at hu
  rw [tmGLP_item_off rfl hpos E' hE' _ g hx hu hz]

/-- **The item of one generator is the contract's item.** The value with the facts
`TmGLPGenOut` (the result of `tmGLPGen_spec`) is `tmGLAffItem gs (tmGLQMod D) ρ c g` with
`ρ = tmGLρE E' (tmGLlam …)` and `c = tmGLcE E' (tmGLo (tmGLPRep N x j0) k)`. -/
theorem tmGLP_gen_item (hn : Normalizes H N) (hker : TmGLKer N H φ) (hNH : N ≤ H)
    {k : Perm (Fin n) → Fin L.q → Perm (Fin n)} (hk : TmGLLift N H φ k)
    (E : Fin n × Fin L.q ≃ S.dom) (i0 j0 : Fin L.q) {x : Fin L.q → Ω}
    (hyk : ∀ h ∈ H, ∀ y : Fin L.q → Perm (Fin n), GI.Paper.cleanRowPerm E y ∈ S.domGroup →
      y i0 = h → ∃ ν, TmGLZero N φ ν ∧ ∀ i, y i = k h i * ν i)
    {σN : List (Perm (Fin n))} (hN : gens σN = N)
    {U V D : Matrix (Fin σN.length) (Fin σN.length) ℤ} (hpos : ∀ i, 0 < D i i)
    (hUV : U * V = 1) (E' : Additive (tmGLV N φ x) ≃+ tmGLVec (tmGLQMod D))
    (hE' : ∀ z, E' (tmGLPg N φ x (fun i => σN[i.val]) z) = tmGLQMap V D z)
    {gs : List (Perm (Fin n))} (hgs : gens gs ≤ Aut H (types N x)) (g : gens gs) {w : Val}
    (hw : TmGLPGenOut E i0 σN x U V (fun i => D i i) (g : Perm (Fin n)) w) :
    w = tmGLAffItem gs (tmGLQMod D) (tmGLρE E' (tmGLlam hn hker hgs hNH))
      (tmGLcE E' (tmGLo (tmGLPRep N x j0) k)) g := by
  obtain ⟨C₁, C₂, v₁, v₂, rfl, hC₁, hC₂, h₁, h₂⟩ := hw
  have hD : (g : Perm (Fin n))⁻¹ ∈ Aut H (types N x) := hgs ((gens gs).inv_mem g.2)
  have hgH : (g : Perm (Fin n)) ∈ H := by simpa using H.inv_mem (mem_aut.mp hD).1
  have hm1 : ∀ j : Fin σN.length,
      (g : Perm (Fin n)) * σN[j.val] * (g : Perm (Fin n))⁻¹ ∈ gens σN := fun j => by
    rw [hN]; exact hn _ hgH _ (tmGLP_stored_mem hN j)
  have hm2 : ∀ j : Fin σN.length,
      (g : Perm (Fin n))⁻¹ * σN[j.val] * (g : Perm (Fin n)) ∈ gens σN := fun j => by
    rw [hN]; exact hn.inv hgH (tmGLP_stored_mem hN j)
  rw [tmGLAffItem, tmGLP_item_mat hN hpos hUV E' hE' g hm1 hC₁,
    tmGLP_item_mat_inv hN hpos hUV E' hE' g hm2 hC₂,
    tmGLP_half_val hn hker hk E i0 j0 hyk hN hpos E' hE' hgs g h₁,
    tmGLP_half_val hn hker hk E i0 j0 hyk hN hpos E' hE' hgs g⁻¹ h₂]

end GI.Impl
