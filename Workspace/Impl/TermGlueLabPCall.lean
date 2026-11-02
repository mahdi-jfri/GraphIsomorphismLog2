import Workspace.Impl.TermGlueLabPE
import Workspace.Impl.TermGlueLabEnc

/-!
# The call of the affine transporter procedure in the label step (step 6)

Proof of Theorem A.23: "The finite abelian affine transporter procedure in the
proof of Theorem A.20 now imposes both labels in polynomial time within this radical coset.
With the possible orientation factor included, the characteristic bound is `p ≤ max{b, 2}`."

The procedure is the hypothesis `Iface.TmGLAffineSpec Pg Ka Da ja`.
Here we check its four preconditions at the call of the label step and read off its answer:

* solvability of `S = ⟨gs⟩`: a hypothesis (it comes from `TermSupSpec`);
* positive moduli: a hypothesis (`tmGLQMod D` with `0 < D i i`, `tmGLQ_spec`);
* every prime divisor of a modulus is at most `max n 2`: `tmGL_prime_le'` / `tmGL_prime_le`,
  since `|A/B(x)|` divides `n!`;
* the cocycle identity: `tmGLρE_cocycle` with `tmGLo_cocycle` / `tmGLoO_cocycle`.

The hypothesis `_hgl : gs.length ≤ n ^ 2` is not used yet: it is there for the termlin proof of
`TmGLAffineSpec` (`LinAffineCaller*`), whose mixed-prime loop needs it; once the spec takes it,
pass `_hgl` to `hA`. At the label call it holds since the group comes from the T4 output
(`GensOf` bounds the list by `n²`).

The answer is a transporter of label points in `S` (`tmGL_contract_trans'`,
`tmGL_contract_trans`), which is what `tmGL_lab_out` takes.

`tmGLP_aff_call'` is the case where some type repeats (no orientation coordinate),
`tmGLP_aff_call` the case where every type is distinct.
-/

namespace GI.Impl

open GI.Multicoset GI.Cited Equiv

variable {Pg : GI.Lang.Program} {Ka Da ja : ℕ}
variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {q : ℕ}
variable {N H : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] {φ : N →* A}
  {x : Fin q → Ω}

/-- **The call when some type repeats.** -/
theorem tmGLP_aff_call' (hA : Iface.TmGLAffineSpec Pg Ka Da ja)
    (hn : Normalizes H N) (hker : TmGLKer N H φ) (hNH : N ≤ H) {gs : List (Perm (Fin n))}
    (hgs : gens gs ≤ Aut H (types N x)) (hsol : IsSolvable (gens gs))
    (_hgl : gs.length ≤ n ^ 2)
    (hT : ¬ (types N x).Nodup) {d : ℕ} {m : Fin d → ℕ} (hm : ∀ i, 0 < m i)
    (E : Additive (tmGLV N φ x) ≃+ tmGLVec m) {k : Perm (Fin n) → Fin q → Perm (Fin n)}
    (hk : TmGLLift N H φ k) {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) (s s' : tmGLV N φ x) :
    GI.Lang.FunAll Pg ja (tmGLAffIn gs m (tmGLρE E (tmGLlam hn hker hgs hNH)) (tmGLcE E (tmGLo rep k))
        (E (Additive.ofMul s')) (E (Additive.ofMul s)))
      (fun u cost => TmGLAffOut n u {g | g ∈ gens gs ∧ tmGLF hn hker rep k g (s, 1) = (s', 1)} ∧
        cost ≤ Ka * ((tmGLAffIn gs m (tmGLρE E (tmGLlam hn hker hgs hNH))
          (tmGLcE E (tmGLo rep k)) (E (Additive.ofMul s')) (E (Additive.ofMul s))).wt + 1) ^ Da) := by
  refine (hA gs m _ _ _ _ hsol hm (fun i p hp hpm => tmGL_prime_le' hm E i p hp hpm)
    (tmGLρE_cocycle E _ _ (tmGLo_cocycle hk hrep))).mono fun u cost h => ⟨?_, h.2⟩
  rw [← tmGL_contract_trans' hT E hk hrep s s']
  exact h.1

/-- **The call when every type is distinct** (with the orientation coordinate). -/
theorem tmGLP_aff_call (hA : Iface.TmGLAffineSpec Pg Ka Da ja)
    (hn : Normalizes H N) (hker : TmGLKer N H φ) (hNH : N ≤ H) {gs : List (Perm (Fin n))}
    (hgs : gens gs ≤ Aut H (types N x)) (hsol : IsSolvable (gens gs))
    (_hgl : gs.length ≤ n ^ 2)
    {d : ℕ} {m : Fin d → ℕ} (hm : ∀ i, 0 < m i)
    (E : Additive (tmGLV N φ x × ℤˣ) ≃+ tmGLVec m) {k : Perm (Fin n) → Fin q → Perm (Fin n)}
    (hk : TmGLLift N H φ k) {rep : Set Ω → Ω} (hrep : TmGLRep N x rep)
    (p p' : tmGLV N φ x × ℤˣ) :
    GI.Lang.FunAll Pg ja (tmGLAffIn gs m (tmGLρE E (tmGLlamO hn hker hgs hNH)) (tmGLcE E (tmGLoO rep k))
        (E (Additive.ofMul p')) (E (Additive.ofMul p)))
      (fun u cost => TmGLAffOut n u {g | g ∈ gens gs ∧ tmGLF hn hker rep k g p = p'} ∧
        cost ≤ Ka * ((tmGLAffIn gs m (tmGLρE E (tmGLlamO hn hker hgs hNH))
          (tmGLcE E (tmGLoO rep k)) (E (Additive.ofMul p')) (E (Additive.ofMul p))).wt + 1) ^ Da) := by
  refine (hA gs m _ _ _ _ hsol hm (fun i p hp hpm => tmGL_prime_le hm E i p hp hpm)
    (tmGLρE_cocycle E _ _ (tmGLoO_cocycle hk hrep))).mono fun u cost h => ⟨?_, h.2⟩
  rw [← tmGL_contract_trans E hk hrep p p']
  exact h.1

/-- The moduli of the quotient program are positive. -/
theorem tmGLQMod_pos {t : ℕ} {D : Matrix (Fin t) (Fin t) ℤ} (hpos : ∀ i, 0 < D i i) (i : Fin t) :
    0 < tmGLQMod D i := by
  simp [tmGLQMod, hpos i]

/-- The moduli with the orientation coordinate are positive. -/
theorem tmGLQMod_cons_pos {t : ℕ} {D : Matrix (Fin t) (Fin t) ℤ} (hpos : ∀ i, 0 < D i i)
    (i : Fin (t + 1)) : 0 < (Fin.cons 2 (tmGLQMod D) : Fin (t + 1) → ℕ) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using tmGLQMod_pos hpos j

end GI.Impl
