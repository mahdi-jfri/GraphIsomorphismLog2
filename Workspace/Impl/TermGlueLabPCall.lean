module

public import Workspace.Impl.TermGlueLabPE
public import Workspace.Impl.TermGlueLabEnc

@[expose] public section

/-!
# The call of the affine transporter procedure in the label step (step 6)

Proof of Theorem A.23: "The finite abelian affine transporter procedure in the
proof of Theorem A.20 now imposes both labels in polynomial time within this radical coset.
With the possible orientation factor included, the characteristic bound is `p ≤ max{b, 2}`."

The procedure is the hypothesis `Iface.TmGLAffineSpec Pg Ka Da ja`.
Here we check its four preconditions at the call of the label step and read off its answer:

* solvability of the linear image `ρ(⟨gs⟩)` (`tmGLρE_range_solvable`): `N` acts trivially on
  `A/B(x)` (`tmGLκ_N`) and on the orientation factor, and `⟨gs⟩ / (N ∩ ⟨gs⟩)` is solvable;
* positive moduli: a hypothesis (`tmGLQMod D` with `0 < D i i`, `tmGLQ_spec`);
* every prime divisor of a modulus is at most `max n 2`: `tmGL_prime_le'` / `tmGL_prime_le`,
  since `|A/B(x)|` divides `n!`;
* the cocycle identity: `tmGLρE_cocycle` with `tmGLo_cocycle` / `tmGLoO_cocycle`.

The answer is a transporter of label points in `⟨gs⟩` (`tmGL_contract_trans'`,
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

/-- If `N` acts trivially under `lam` and `(gens gs) / (N ∩ gens gs)` is solvable, then the
linear image `(tmGLρE E lam).range` is solvable. -/
theorem tmGLρE_range_solvable {d : ℕ} {m : Fin d → ℕ} {Y : Type*} [CommGroup Y]
    {gs : List (Perm (Fin n))} [hnorm : (N.subgroupOf (gens gs)).Normal]
    (hsol : Group.IsSolvable ((gens gs) ⧸ N.subgroupOf (gens gs)))
    (E : Additive Y ≃+ tmGLVec m) (lam : gens gs →* MulAut Y)
    (hN : ∀ g : gens gs, g.1 ∈ N → lam g = 1) :
    Group.IsSolvable (tmGLρE E lam).range := by
  let ρ := tmGLρE E lam
  have hker : N.subgroupOf (gens gs) ≤ ρ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    have h1 : lam g = 1 := hN g hg
    ext v i
    simp [ρ, tmGLρE, h1]
  let f := QuotientGroup.lift (N.subgroupOf (gens gs)) ρ.rangeRestrict (fun g hg => by
    ext1; exact hker hg)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, g, rfl⟩
    exact ⟨QuotientGroup.mk' (N.subgroupOf (gens gs)) g, rfl⟩
  exact Group.isSolvable_of_surjective hsurj

/-- **The call when some type repeats.** -/
theorem tmGLP_aff_call' (hA : Iface.TmGLAffineSpec Pg Ka Da ja)
    (hn : Normalizes H N) (hker : TmGLKer N H φ) (hNH : N ≤ H) {gs : List (Perm (Fin n))}
    (hgs : gens gs ≤ Aut H (types N x))
    [hnorm : (N.subgroupOf (gens gs)).Normal]
    (hsol : Group.IsSolvable ((gens gs) ⧸ N.subgroupOf (gens gs)))
    (_hgl : gs.length ≤ n ^ 2)
    (hT : ¬ (types N x).Nodup) {d : ℕ} {m : Fin d → ℕ} (hm : ∀ i, 0 < m i)
    (E : Additive (tmGLV N φ x) ≃+ tmGLVec m) {k : Perm (Fin n) → Fin q → Perm (Fin n)}
    (hk : TmGLLift N H φ k) {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) (s s' : tmGLV N φ x) :
    GI.Lang.FunAll Pg ja (tmGLAffIn gs m (tmGLρE E (tmGLlam hn hker hgs hNH)) (tmGLcE E (tmGLo rep k))
        (E (Additive.ofMul s')) (E (Additive.ofMul s)))
      (fun u cost => TmGLAffOut n u {g | g ∈ gens gs ∧ tmGLF hn hker rep k g (s, 1) = (s', 1)} ∧
        cost ≤ Ka * ((tmGLAffIn gs m (tmGLρE E (tmGLlam hn hker hgs hNH))
          (tmGLcE E (tmGLo rep k)) (E (Additive.ofMul s')) (E (Additive.ofMul s))).wt + 1) ^ Da) := by
  have hsol' : Group.IsSolvable (tmGLρE E (tmGLlam hn hker hgs hNH)).range :=
    tmGLρE_range_solvable hsol E (tmGLlam hn hker hgs hNH) (fun g hg => by
      ext v
      exact tmGLκ_N hker (N.inv_mem hg) (hgs ((gens gs).inv_mem g.2)) v)
  refine (hA gs m _ _ _ _ hsol' hm (fun i p hp hpm => tmGL_prime_le' hm E i p hp hpm)
    (tmGLρE_cocycle E _ _ (tmGLo_cocycle hk hrep))).mono fun u cost h => ⟨?_, h.2⟩
  rw [← tmGL_contract_trans' hT E hk hrep s s']
  exact h.1

/-- **The call when every type is distinct** (with the orientation coordinate). -/
theorem tmGLP_aff_call (hA : Iface.TmGLAffineSpec Pg Ka Da ja)
    (hn : Normalizes H N) (hker : TmGLKer N H φ) (hNH : N ≤ H) {gs : List (Perm (Fin n))}
    (hgs : gens gs ≤ Aut H (types N x))
    [hnorm : (N.subgroupOf (gens gs)).Normal]
    (hsol : Group.IsSolvable ((gens gs) ⧸ N.subgroupOf (gens gs)))
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
  have hsol' : Group.IsSolvable (tmGLρE E (tmGLlamO hn hker hgs hNH)).range :=
    tmGLρE_range_solvable hsol E (tmGLlamO hn hker hgs hNH) (fun g hg => by
      ext v
      · exact tmGLκ_N hker (N.inv_mem hg) (hgs ((gens gs).inv_mem g.2)) v.1
      · rfl)
  refine (hA gs m _ _ _ _ hsol' hm (fun i p hp hpm => tmGL_prime_le hm E i p hp hpm)
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
