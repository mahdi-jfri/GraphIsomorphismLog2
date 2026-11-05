module

public import Workspace.Proved.VsBFldNT
public import Workspace.Proved.VsBAff
public import Workspace.Impl.VsQSot

@[expose] public section

/-!
# The λ-chain of the field line

On a valid state `s` whose local group is abelian and whose local algebra
`L = 𝔽_p[Λ(H)]` has no zero divisors (the field line), every `Λ(h)` lies in `L`, and the map
`h ↦ Λ(h)^{F_q}` is a homomorphism. The stage `q` of the chain acts on local vectors by
`y ↦ Λ(h)^{F_q} y`.

* `vsBLamA s`: the algebra `L`; `vsB_lam_mem`: `Λ(h) ∈ L` for `h ∈ H`.
* `vsBAq s q`, `vsBAq_act`: the stage action.
* `vsB_orb_le`: the orbit of `e₀` has at most `n + 1` points.
* `vsB_stab_iff`: `h` fixes `e₀` iff `Λ(h)^{F_q} = 1`.
* `vsB_lam_eq_one`: `Λ(h) = 1` iff `Λ(h)^{F_q} = 1` for all `2 ≤ q ≤ max n 2`.
-/

open Matrix

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv

variable {I : VecStabInst}

/-- The local algebra `L` of a state. -/
noncomputable def vsBLamA (s : VsQSt I) :
    Subalgebra (ZMod I.p) (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) :=
  Algebra.adjoin (ZMod I.p) {X | ∃ g ∈ s.hs, vsQLam s g = X}

/-- The field property of `L`. -/
def VsBDom (s : VsQSt I) : Prop :=
  ∀ X ∈ vsBLamA s, X = 0 ∨ ∀ v, X *ᵥ v = 0 → v = 0

/-- The action of stage `q`. -/
noncomputable def vsBAq (s : VsQSt I) (q : ℕ) (h : Perm (Fin I.n)) (y : Fin (vsQD s) → ZMod I.p) :
    Fin (vsQD s) → ZMod I.p :=
  (vsQLam s h ^ vsBF I.n q) *ᵥ y

/-- The first unit vector. -/
noncomputable def vsBe0 (s : VsQSt I) (hD : 1 ≤ vsQD s) : Fin (vsQD s) → ZMod I.p :=
  Pi.single ⟨0, hD⟩ 1

section

variable {s : VsQSt I} (hs : VsQStOK s)
include hs

theorem vsB_lam_pow {h : Perm (Fin I.n)} (hh : h ∈ gens s.hs) (k : ℕ) :
    vsQLam s (h ^ k) = vsQLam s h ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, vsQLam_one hs]
  | succ k ih => rw [pow_succ, pow_succ, vsQLam_mul hs (pow_mem hh k) hh, ih]

theorem vsB_lam_pow_E {h : Perm (Fin I.n)} (hh : h ∈ gens s.hs) : vsQLam s h ^ vsBE I.n = 1 := by
  obtain ⟨c, hc⟩ := vsB_orderOf_dvd h
  rw [← vsB_lam_pow hs hh, hc, pow_mul, pow_orderOf_eq_one, one_pow, vsQLam_one hs]

theorem vsB_lam_mem {h : Perm (Fin I.n)} (hh : h ∈ gens s.hs) : vsQLam s h ∈ vsBLamA s := by
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  | one => rw [vsQLam_one hs]; exact one_mem _
  | mul x y hx hy ihx ihy => rw [vsQLam_mul hs hx hy]; exact mul_mem ihx ihy
  | inv x hx ihx =>
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [e, vsB_lam_pow hs hx]
    exact pow_mem ihx _

theorem vsB_comm (hab : s.Ab) {g h : Perm (Fin I.n)} (hg : g ∈ gens s.hs) (hh : h ∈ gens s.hs) :
    Commute (vsQLam s g) (vsQLam s h) :=
  (vsQAb_iff hs).mp hab g hg h hh

theorem vsBAq_act (hab : s.Ab) (q : ℕ) : VsQPAct (gens s.hs) (vsBAq s q) where
  one y := by rw [vsBAq, vsQLam_one hs, one_pow, one_mulVec]
  mul g hg h hh y := by
    rw [vsBAq, vsBAq, vsBAq, mulVec_mulVec, vsQLam_mul hs hg hh, (vsB_comm hs hab hg hh).mul_pow]

omit hs in
theorem vsB_e0_ne (hD : 1 ≤ vsQD s) : vsBe0 s hD ≠ 0 := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  intro h
  have := congrFun h ⟨0, hD⟩
  simp [vsBe0] at this

omit hs in
/-- In `L`, a matrix that kills one nonzero vector is `0`. -/
theorem vsB_dom_eq_zero (hdom : VsBDom s) {X : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)}
    (hX : X ∈ vsBLamA s) {v : Fin (vsQD s) → ZMod I.p} (hv : v ≠ 0) (h : X *ᵥ v = 0) : X = 0 :=
  (hdom X hX).resolve_right fun hi => hv (hi v h)

theorem vsB_stab_iff (hD : 1 ≤ vsQD s) (hdom : VsBDom s) (q : ℕ) {h : Perm (Fin I.n)}
    (hh : h ∈ gens s.hs) : vsBAq s q h (vsBe0 s hD) = vsBe0 s hD ↔ vsQLam s h ^ vsBF I.n q = 1 := by
  constructor
  · intro he
    have hm : vsQLam s h ^ vsBF I.n q - 1 ∈ vsBLamA s :=
      sub_mem (pow_mem (vsB_lam_mem hs hh) _) (one_mem _)
    have := vsB_dom_eq_zero hdom hm (vsB_e0_ne hD) (by
      rw [sub_mulVec, one_mulVec]; exact sub_eq_zero.mpr he)
    exact sub_eq_zero.mp this
  · intro he; rw [vsBAq, he, one_mulVec]

omit hs in
theorem vsB_lam_eq_one (h : Perm (Fin I.n)) :
    vsQLam s h = 1 ↔ ∀ q, 2 ≤ q → q ≤ max I.n 2 → vsQLam s h ^ vsBF I.n q = 1 := by
  constructor
  · intro he q _ _; rw [he, one_pow]
  · exact vsB_eq_one

/-- **The orbits of the λ-chain are small.** -/
theorem vsB_orb_le (hab : s.Ab) (hD : 1 ≤ vsQD s) (hdom : VsBDom s) {q : ℕ} (hq : 2 ≤ q)
    {gs : List (Perm (Fin I.n))} (hgs : genGroup gs ≤ gens s.hs) :
    (vsQOrb (vsBAq s q) gs (vsBe0 s hD)).ncard ≤ I.n + 1 := by
  classical
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hcomm : ({X | ∃ g ∈ s.hs, vsQLam s g = X} : Set _).Pairwise Commute := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ _
    exact vsB_comm hs hab (Subgroup.subset_closure hg) (Subgroup.subset_closure hh)
  letI : CommRing (vsBLamA s) := Algebra.adjoinCommRingOfComm (ZMod I.p) hcomm
  haveI : Nontrivial (vsBLamA s) := by
    haveI : Fact I.p.Prime := ⟨I.prime⟩
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 : ((0 : vsBLamA s) : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) ⟨0, hD⟩ ⟨0, hD⟩ =
        ((1 : vsBLamA s) : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) ⟨0, hD⟩ ⟨0, hD⟩ := by
      rw [h]
    simp at h1
  have hnzd : ∀ a b : vsBLamA s, a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab'
    by_contra hne
    push Not at hne
    rcases hdom a a.2 with ha | ha
    · exact hne.1 (Subtype.ext ha)
    · apply hne.2
      apply Subtype.ext
      have hb : ∀ v, (b : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) *ᵥ v = 0 := fun v => ha _ (by
        rw [mulVec_mulVec]
        have : ((a * b : vsBLamA s) : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) =
          (a : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) * b := rfl
        rw [← this, hab']; simp)
      ext i j
      have := congrFun (hb (Pi.single j 1)) i
      simpa [mulVec_single] using this
  set R := q.minFac ^ Nat.log q.minFac I.n
  have hR : 0 < R := Nat.pow_pos (Nat.minFac_pos q)
  have hsub : vsQOrb (vsBAq s q) gs (vsBe0 s hD) ⊆
      (fun z : vsBLamA s => (z : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) *ᵥ vsBe0 s hD) '' {z | z ^ R = 1} := by
    rintro _ ⟨g, hg, rfl⟩
    have hgg := hgs hg
    refine ⟨⟨vsQLam s g ^ vsBF I.n q, pow_mem (vsB_lam_mem hs hgg) _⟩, ?_, rfl⟩
    apply Subtype.ext
    show (vsQLam s g ^ vsBF I.n q) ^ R = 1
    exact vsB_pow_F hq (vsB_lam_pow_E hs hgg)
  calc (vsQOrb (vsBAq s q) gs (vsBe0 s hD)).ncard
      ≤ ((fun z : vsBLamA s => (z : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) *ᵥ vsBe0 s hD) '' {z | z ^ R = 1}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ {z : vsBLamA s | z ^ R = 1}.ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ R := vsB_roots_le hnzd hR
    _ ≤ I.n + 1 := vsB_minFac_pow_le _ _

end

end GI.Proved
