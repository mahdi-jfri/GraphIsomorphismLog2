module

public import Workspace.Proved.VsPSpinMath
public import Workspace.Proved.VsMBasic

@[expose] public section

/-!
# The hand-off satisfies `VsMHard`

Here `N ≤ C(A)` has commutators and `r`-th powers in `S = vsMScal A`.
* `vsP_pairHyp`: a nontrivial commutator `ζ` of `N` has order `r`, and every commutator of `N`
  is a power of `ζ` (so the pairing is a bilinear form with values in `ZMod r`).
* `vsP_quotHyp`: `N` modulo `S` is an elementary abelian `r`-group.
* `vsP_hard`: if `Y = ⟨Ob⟩ ⊔ S` comes from an orbit set of `x0 ∈ N` that passed the descent test,
  and `⟨Ob⟩` is not abelian, then `VsMHard H A Y r`.
-/

namespace GI.Proved

open Module
open scoped commutatorElement

/-- Commutators ignore factors that commute with everything involved. -/
theorem vsP_comm_mul_mul {G : Type*} [Group G] {a b s t : G} (hsb : Commute s b) (hta : Commute t a)
    (hst : Commute s t) : ⁅a * s, b * t⁆ = ⁅a, b⁆ := by
  have e1 : a * s * (b * t) = a * b * (s * t) := hsb.mul_mul_mul_comm a t
  have e2 : b * t * (a * s) = b * a * (t * s) := hta.mul_mul_mul_comm b s
  have key : ∀ x y : G, ⁅x, y⁆ = x * y * (y * x)⁻¹ := fun x y => by
    rw [commutatorElement_def]; group
  rw [key, key, e1, e2, hst.eq, mul_inv_rev, mul_assoc (a * b), mul_inv_cancel_left]

variable {p : ℕ} [hp : Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

/-- **The pairing hypotheses** for a nontrivial commutator `ζ` of `N`. -/
theorem vsP_pairHyp [FiniteDimensional (ZMod p) V] [Nontrivial V]
    {A N : Subgroup (End (ZMod p) V)ˣ} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hdom : vsTDom (vsTAlg A)) {r : ℕ} (hr : r.Prime)
    (hNC : N ≤ Subgroup.centralizer (A : Set (End (ZMod p) V)ˣ))
    (hc : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ vsMScal A) (hpow : ∀ x ∈ N, x ^ r ∈ vsMScal A)
    {ζ : (End (ZMod p) V)ˣ} (hζN : ∃ x ∈ N, ∃ y ∈ N, ζ = ⁅x, y⁆) (hζ1 : ζ ≠ 1) :
    VsPPairHyp N r ζ := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hcl : Subgroup.closure (N : Set (End (ZMod p) V)ˣ) = N := Subgroup.closure_eq N
  obtain ⟨-, hpr, -⟩ := vsM_pair (p := p) (V := V) A (N : Set (End (ZMod p) V)ˣ) r hNC
    (by rw [hcl]; exact hc)
  rw [hcl] at hpr
  have hrpow : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ^ r = 1 := fun x hx y hy => hpr x hx y hy (hpow x hx)
  obtain ⟨x0, hx0, y0, hy0, rfl⟩ := hζN
  have hζS := hc x0 hx0 y0 hy0
  have hζr := hrpow x0 hx0 y0 hy0
  refine ⟨orderOf_eq_prime hζr hζ1, fun x hx y hy z hz => ?_, fun x hx y hy => ?_⟩
  · exact (vsM_comm_scal (hNC hz) (hc x hx y hy)).symm
  · obtain ⟨j, hj, e⟩ := vsM_dlog A r _ ⁅x, y⁆ hA hdom hr hζS hζ1 hζr (hc x hx y hy)
      (hrpow x hx y hy)
    exact ⟨(j : ZMod r), by rw [ZMod.val_cast_of_lt hj]; exact e⟩

theorem vsP_quotHyp {A N : Subgroup (End (ZMod p) V)ˣ} {r : ℕ}
    (hNC : N ≤ Subgroup.centralizer (A : Set (End (ZMod p) V)ˣ))
    (hc : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ vsMScal A) (hpow : ∀ x ∈ N, x ^ r ∈ vsMScal A) :
    VsPQuotHyp N (vsMScal A) r :=
  ⟨fun s hs x hx => (vsM_comm_scal (hNC hx) hs).symm, hc, hpow⟩

/-- **The hand-off is a hard case.** -/
theorem vsP_hard [Finite (End (ZMod p) V)ˣ] {M : Type*} [AddCommGroup M] {r : ℕ} [Fact r.Prime] [Module (ZMod r) M]
    {Hg : Set (End (ZMod p) V)ˣ} {A N : Subgroup (End (ZMod p) V)ˣ}
    (hsolv : IsSolvable (Subgroup.closure Hg)) (hAN : VsTAbNormal (Subgroup.closure Hg) A)
    (hdom : vsTDom (vsTAlg A))
    (hNC : N ≤ Subgroup.centralizer (A : Set (End (ZMod p) V)ˣ))
    (hNn : ∀ h ∈ Hg, ∀ x ∈ N, h * x * h⁻¹ ∈ N)
    (hc : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ vsMScal A) (hpow : ∀ x ∈ N, x ^ r ∈ vsMScal A)
    {κ : (End (ZMod p) V)ˣ → M} (hk : VsPKeyHyp N (vsMScal A) κ)
    {x0 : (End (ZMod p) V)ˣ} {Ob : Set (End (ZMod p) V)ˣ}
    (hO : VsPOrbHyp Hg κ x0 Ob) (hfin : Ob.Finite) (hx0 : x0 ∈ N)
    {Wd : Set (End (ZMod p) V)ˣ} (hWd : ∀ w ∈ Wd, w ∈ Subgroup.closure Ob)
    (hcov : ∀ v ∈ Submodule.span (ZMod r) (κ '' Ob), ∃ w ∈ Wd, κ w = v)
    (hdesc : ∀ w ∈ Wd, w ∉ vsMScal A → ∃ Ow, VsPOrbHyp Hg κ w Ow ∧
      finrank (ZMod r) (Submodule.span (ZMod r) (κ '' Ob)) ≤
        finrank (ZMod r) (Submodule.span (ZMod r) (κ '' Ow)))
    (hnab : ∃ x ∈ Subgroup.closure Ob, ∃ y ∈ Subgroup.closure Ob, x * y ≠ y * x) :
    VsMHard (Subgroup.closure Hg) A (Subgroup.closure Ob ⊔ vsMScal A) r := by
  set S := vsMScal A
  have hAc := hAN.2.2
  have hSn : ∀ h ∈ Hg, ∀ s ∈ S, h * s * h⁻¹ ∈ S := fun h hh s hs =>
    vsM_scal_norm hAN h (Subgroup.subset_closure hh) s hs
  have hON := hO.subset_N hNn hx0
  have hClN : Subgroup.closure Ob ≤ N := (Subgroup.closure_le _).2 hON
  have hSc : ∀ a ∈ Subgroup.closure Ob, ∀ s ∈ S, a * s = s * a := fun a ha s hs =>
    vsM_comm_scal (hNC (hClN ha)) hs
  have hSS : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := fun s hs t ht => vsM_scal_comm hAc hs ht
  refine ⟨hsolv, hAN, hdom, Fact.out, fun h hh x hx => ?_, ?_, fun x hx y hy => ?_,
    fun y hy => ?_, fun y hy hyS => ?_, ?_⟩
  · exact vsP_norm_closure (hO.norm hk hNn hSn hx0) h hh x hx
  · exact sup_le (hClN.trans hNC) (vsM_scal_le_centralizer hAc)
  · obtain ⟨a, ha, s, hs, rfl⟩ := vsM_mem_sup_comm hSc hx
    obtain ⟨b, hb, t, ht, rfl⟩ := vsM_mem_sup_comm hSc hy
    rw [vsP_comm_mul_mul (hSc b hb s hs).symm (hSc a ha t ht).symm (hSS s hs t ht)]
    exact hc a (hClN ha) b (hClN hb)
  · obtain ⟨a, ha, s, hs, rfl⟩ := vsM_mem_sup_comm hSc hy
    rw [Commute.mul_pow (hSc a ha s hs) r]
    exact S.mul_mem (hpow a (hClN ha)) (S.pow_mem hs r)
  · exact vsP_min hk hO hfin hNn hSn hx0 hWd hcov hdesc y hy hyS
  · obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    exact ⟨x, Subgroup.mem_sup_left hx, y, Subgroup.mem_sup_left hy, hxy⟩

end GI.Proved
