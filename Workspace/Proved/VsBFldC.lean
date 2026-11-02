import Workspace.Proved.VsBFldB
import Workspace.Proved.VsFAlgPiece

/-!
# The two cases of the field line

Write `f(h) = vsBAlpha s h 0` and `T = f(H₁)`. Conjugation gives `f(g k g⁻¹) = Λ(g) f(k)`, so
`T` is invariant under `L`. On a field line (`L` has no zero divisors and `L e₀` is everything)
an `L`-invariant subspace is `0` or everything (`vsFSpin_irred`), so `T = 0` or `T = M'`
(`vsB_dich`).
-/

open Matrix

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv

variable {I : VecStabInst} {s : VsQSt I} (hs : VsQStOK s)
include hs

theorem vsBAlpha_inv0 {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    vsBAlpha s g (vsBAlpha s g⁻¹ 0) = 0 := by
  rw [← (vsBAlpha_act hs).mul g hg g⁻¹ (inv_mem hg), mul_inv_cancel, (vsBAlpha_act hs).one]

/-- Conjugation: `f(g k g⁻¹) = Λ(g) f(k)`. -/
theorem vsB_f_conj {g k : Perm (Fin I.n)} (hg : g ∈ gens s.hs) (hk : k ∈ vsBH1 hs) :
    vsBAlpha s (g * k * g⁻¹) 0 = vsQLam s g *ᵥ vsBAlpha s k 0 := by
  have hkg := (vsBH1_le hs) hk
  rw [(vsBAlpha_act hs).mul _ (mul_mem hg hkg) _ (inv_mem hg), (vsBAlpha_act hs).mul _ hg _ hkg,
    vsBAlpha_H1 hs hk, vsBAlpha_lin hs hg, mulVec_add, add_right_comm, ← vsBAlpha_lin hs hg,
    vsBAlpha_inv0 hs hg, zero_add]

theorem vsBH1_conj {g k : Perm (Fin I.n)} (hg : g ∈ gens s.hs) (hk : k ∈ vsBH1 hs) :
    g * k * g⁻¹ ∈ vsBH1 hs := by
  refine ⟨mul_mem (mul_mem hg hk.1) (inv_mem hg), ?_⟩
  rw [vsQLam_mul hs (mul_mem hg hk.1) (inv_mem hg), vsQLam_mul hs hg hk.1, hk.2, mul_one,
    vsB_lam_inv hs hg]

/-- The image `T = f(H₁)` as a subspace. -/
noncomputable def vsBT : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p) :=
  AddSubgroup.toZModSubmodule I.p
    { carrier := {v | ∃ k ∈ vsBH1 hs, vsBAlpha s k 0 = v}
      zero_mem' := ⟨1, one_mem _, (vsBAlpha_act hs).one 0⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, mul_mem ha hb, vsBf_mul hs ha hb⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, ?_⟩
        have := vsBf_mul hs (inv_mem ha) ha
        rw [inv_mul_cancel, (vsBAlpha_act hs).one] at this
        exact (neg_eq_of_add_eq_zero_left this.symm).symm }

theorem mem_vsBT {v : Fin (vsQD s) → ZMod I.p} : v ∈ vsBT hs ↔ ∃ k ∈ vsBH1 hs, vsBAlpha s k 0 = v :=
  Iff.rfl

/-- `T` is invariant under `L`. -/
theorem vsBT_inv {X : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)} (hX : X ∈ vsBLamA s) :
    ∀ v ∈ vsBT hs, X *ᵥ v ∈ vsBT hs := by
  induction hX using Algebra.adjoin_induction with
  | mem X hX =>
    obtain ⟨g, hg, rfl⟩ := hX
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨_, vsBH1_conj hs (Subgroup.subset_closure hg) hk,
      vsB_f_conj hs (Subgroup.subset_closure hg) hk⟩
  | algebraMap c =>
    intro v hv
    rw [Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec]
    exact Submodule.smul_mem _ c hv
  | add X Y _ _ hX hY =>
    intro v hv
    rw [add_mulVec]; exact add_mem (hX v hv) (hY v hv)
  | mul X Y _ _ hX hY =>
    intro v hv
    rw [← mulVec_mulVec]; exact hX _ (hY v hv)

/-- **The dichotomy** `T = 0` or `T = M'`, on a field line. -/
theorem vsB_dich (hdom : VsBDom s) (hD : 1 ≤ vsQD s)
    (hspan : ∀ v, ∃ X ∈ vsBLamA s, X *ᵥ vsBe0 s hD = v) :
    (∀ k ∈ vsBH1 hs, vsBAlpha s k 0 = 0) ∨ (∀ v, ∃ k ∈ vsBH1 hs, vsBAlpha s k 0 = v) := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  by_cases h0 : vsBT hs = ⊥
  · left
    intro k hk
    have : vsBAlpha s k 0 ∈ vsBT hs := ⟨k, hk, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    exact this
  · right
    set B := (vsBLamA s).map (Matrix.toLinAlgEquiv' : _ ≃ₐ[ZMod I.p] _).toAlgHom
    have hF : ∀ b ∈ B, b = 0 ∨ ∀ v, b v = 0 → v = 0 := by
      rintro _ ⟨X, hX, rfl⟩
      rcases hdom X hX with h | h
      · left; simp [h]
      · right; intro v hv; exact h v (by simpa [Matrix.toLinAlgEquiv'_apply] using hv)
    have hsp : Submodule.map (LinearMap.applyₗ (vsBe0 s hD)) (Subalgebra.toSubmodule B) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      obtain ⟨X, hX, rfl⟩ := hspan v
      exact ⟨Matrix.toLinAlgEquiv' X, ⟨X, hX, rfl⟩, by simp [Matrix.toLinAlgEquiv'_apply]⟩
    have hW : ∀ b ∈ B, ∀ w ∈ vsBT hs, b w ∈ vsBT hs := by
      rintro _ ⟨X, hX, rfl⟩ w hw
      simpa [Matrix.toLinAlgEquiv'_apply] using vsBT_inv hs hX w hw
    have htop := vsFSpin_irred B hF hsp (vsBT hs) hW h0
    intro v
    have : v ∈ vsBT hs := htop ▸ Submodule.mem_top
    exact this

/-- The stabilizer of `0` under the affine action, as a subgroup. -/
noncomputable def vsBStab0 : Subgroup (Perm (Fin I.n)) where
  carrier := {h | h ∈ gens s.hs ∧ vsBAlpha s h 0 = 0}
  one_mem' := ⟨one_mem _, (vsBAlpha_act hs).one 0⟩
  mul_mem' := by
    rintro a b ⟨ha, ha0⟩ ⟨hb, hb0⟩
    exact ⟨mul_mem ha hb, by rw [(vsBAlpha_act hs).mul a ha b hb, hb0, ha0]⟩
  inv_mem' := by
    rintro a ⟨ha, ha0⟩
    refine ⟨inv_mem ha, ?_⟩
    have := vsBAlpha_inv0 hs ha
    conv_rhs => rw [← (vsBAlpha_act hs).one 0, ← inv_mul_cancel a,
      (vsBAlpha_act hs).mul _ (inv_mem ha) _ ha, ha0]

/-- If `f` vanishes on the generators, it vanishes on `H`. -/
theorem vsB_f_zero (h0 : ∀ g ∈ s.hs, vsBAlpha s g 0 = 0) :
    ∀ h ∈ gens s.hs, vsBAlpha s h 0 = 0 := by
  have hle : gens s.hs ≤ vsBStab0 hs := Subgroup.closure_le _ |>.mpr fun g hg =>
    ⟨Subgroup.subset_closure hg, h0 g hg⟩
  exact fun h hh => (hle hh).2

/-- **The case `T = M'`.** With `ks` generating the kernel of `f` on `H₁`, and for every
generator `g` an element `c_g ∈ g H₁` with `f(c_g) = 0`, the list `ks ++ cs` generates the
stabilizer of `0`. -/
theorem vsB_stab_gens {ks cs : List (Perm (Fin I.n))}
    (hks : (gens ks : Set (Perm (Fin I.n))) = {k | k ∈ vsBH1 hs ∧ vsBAlpha s k 0 = 0})
    (hcs : ∀ c ∈ cs, c ∈ gens s.hs ∧ vsBAlpha s c 0 = 0)
    (hcov : ∀ g ∈ s.hs, ∃ c ∈ cs, g⁻¹ * c ∈ vsBH1 hs) :
    gens (ks ++ cs) = vsBStab0 hs := by
  apply le_antisymm
  · refine Subgroup.closure_le _ |>.mpr fun g hg => ?_
    rcases List.mem_append.mp hg with hg | hg
    · have : g ∈ (gens ks : Set (Perm (Fin I.n))) := Subgroup.subset_closure hg
      rw [hks] at this
      exact ⟨(vsBH1_le hs) this.1, this.2⟩
    · exact hcs g hg
  · have hG' : gens (ks ++ cs) ≤ vsBStab0 hs := Subgroup.closure_le _ |>.mpr fun g hg => by
      rcases List.mem_append.mp hg with hg | hg
      · have : g ∈ (gens ks : Set (Perm (Fin I.n))) := Subgroup.subset_closure hg
        rw [hks] at this
        exact ⟨(vsBH1_le hs) this.1, this.2⟩
      · exact hcs g hg
    have key : ∀ h ∈ gens s.hs, ∃ g' ∈ gens (ks ++ cs), g'⁻¹ * h ∈ vsBH1 hs := by
      intro h hh
      induction hh using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨c, hc, hgc⟩ := hcov g hg
        refine ⟨c, Subgroup.subset_closure (List.mem_append_right _ hc), ?_⟩
        have := inv_mem hgc
        rwa [_root_.mul_inv_rev, inv_inv] at this
      | one => exact ⟨1, one_mem _, by rw [inv_one, one_mul]; exact one_mem _⟩
      | mul x y hx hy ihx ihy =>
        obtain ⟨gx, hgx, ha⟩ := ihx
        obtain ⟨gy, hgy, hb⟩ := ihy
        refine ⟨gx * gy, mul_mem hgx hgy, ?_⟩
        have hgy' : gy⁻¹ ∈ gens s.hs := inv_mem (hG' hgy).1
        have hc := vsBH1_conj hs hgy' ha
        have e : (gx * gy)⁻¹ * (x * y) = gy⁻¹ * (gx⁻¹ * x) * gy⁻¹⁻¹ * (gy⁻¹ * y) := by group
        rw [e]
        exact mul_mem hc hb
      | inv x hx ihx =>
        obtain ⟨gx, hgx, ha⟩ := ihx
        refine ⟨gx⁻¹, inv_mem hgx, ?_⟩
        have hc := vsBH1_conj hs (hG' hgx).1 (inv_mem ha)
        have e : gx⁻¹⁻¹ * x⁻¹ = gx * (gx⁻¹ * x)⁻¹ * gx⁻¹ := by group
        rw [e]
        exact hc
    rintro h ⟨hh, h0⟩
    obtain ⟨g', hg', hk⟩ := key h hh
    have hg'S := hG' hg'
    have hg'i := (vsBStab0 hs).inv_mem hg'S
    have hk0 : vsBAlpha s (g'⁻¹ * h) 0 = 0 := by
      rw [(vsBAlpha_act hs).mul _ hg'i.1 _ hh, h0, hg'i.2]
    have : g'⁻¹ * h ∈ (gens ks : Set (Perm (Fin I.n))) := by rw [hks]; exact ⟨hk, hk0⟩
    have hmem : g'⁻¹ * h ∈ gens (ks ++ cs) :=
      Subgroup.closure_mono (fun x hx => List.mem_append_left _ hx) this
    have := mul_mem hg' hmem
    rwa [mul_inv_cancel_left] at this

/-- The cocycle identity `f(gh) = f(g) + Λ(g) f(h)`. -/
theorem vsB_f_mul' {g h : Perm (Fin I.n)} (hg : g ∈ gens s.hs) (hh : h ∈ gens s.hs) :
    vsBAlpha s (g * h) 0 = vsBAlpha s g 0 + vsQLam s g *ᵥ vsBAlpha s h 0 := by
  rw [(vsBAlpha_act hs).mul g hg h hh, vsBAlpha_lin hs hg, add_comm]

/-- In the case `T = 0`: `(1 - Λ h) f(g) = (1 - Λ g) f(h)`. -/
theorem vsB_T0_swap (hab : s.Ab) (hT : ∀ k ∈ vsBH1 hs, vsBAlpha s k 0 = 0) {g h : Perm (Fin I.n)}
    (hg : g ∈ gens s.hs) (hh : h ∈ gens s.hs) :
    vsBAlpha s g 0 - vsQLam s h *ᵥ vsBAlpha s g 0 = vsBAlpha s h 0 - vsQLam s g *ᵥ vsBAlpha s h 0 := by
  set c := (h * g)⁻¹ * (g * h)
  have hc : c ∈ vsBH1 hs := by
    refine ⟨mul_mem (inv_mem (mul_mem hh hg)) (mul_mem hg hh), ?_⟩
    have e1 := vsB_lam_inv' hs (mul_mem hh hg)
    rw [vsQLam_mul hs (inv_mem (mul_mem hh hg)) (mul_mem hg hh), vsQLam_mul hs hg hh,
      (vsB_comm hs hab hg hh).eq, ← vsQLam_mul hs hh hg, e1]
  have e : g * h = (h * g) * c := (mul_inv_cancel_left _ _).symm
  have h1 : vsBAlpha s (g * h) 0 = vsBAlpha s (h * g) 0 := by
    rw [e, vsB_f_mul' hs (mul_mem hh hg) hc.1, hT c hc, mulVec_zero, add_zero]
  rw [vsB_f_mul' hs hg hh, vsB_f_mul' hs hh hg] at h1
  rw [sub_eq_sub_iff_add_eq_add]
  exact h1

/-- In the case `T = 0` with `f(g₀) ≠ 0`: `f(h) = (Λ h - 1) m` for the solution `m` of
`(Λ g₀ - 1) m = f(g₀)`. -/
theorem vsB_T0_form (hab : s.Ab) (hdom : VsBDom s) (hT : ∀ k ∈ vsBH1 hs, vsBAlpha s k 0 = 0)
    {g₀ : Perm (Fin I.n)} (hg₀ : g₀ ∈ gens s.hs) {m : Fin (vsQD s) → ZMod I.p}
    (hm : (vsQLam s g₀ - 1) *ᵥ m = vsBAlpha s g₀ 0) (hne : vsBAlpha s g₀ 0 ≠ 0)
    {h : Perm (Fin I.n)} (hh : h ∈ gens s.hs) :
    vsBAlpha s h 0 = (vsQLam s h - 1) *ᵥ m := by
  have hX : vsQLam s g₀ - 1 ∈ vsBLamA s := sub_mem (vsB_lam_mem hs hg₀) (one_mem _)
  have hX0 : vsQLam s g₀ - 1 ≠ 0 := by
    intro h0; rw [h0, zero_mulVec] at hm; exact hne hm.symm
  have hinj := (hdom _ hX).resolve_left hX0
  have hsw := vsB_T0_swap hs hab hT hg₀ hh
  have hcomm := vsB_U_comm hs hab hX (sub_mem (vsB_lam_mem hs hh) (one_mem _))
  have e1 : (vsQLam s g₀ - 1) *ᵥ vsBAlpha s h 0 = (vsQLam s h - 1) *ᵥ vsBAlpha s g₀ 0 := by
    rw [sub_mulVec, one_mulVec, sub_mulVec, one_mulVec, ← neg_sub, ← hsw, neg_sub]
  apply eq_of_sub_eq_zero
  apply hinj
  rw [mulVec_sub, e1, ← hm, mulVec_mulVec, mulVec_mulVec, hcomm.eq, sub_self]

/-- A nonzero element of `L` is a unit of `L`. -/
theorem vsB_unit (hab : s.Ab) (hdom : VsBDom s) {X : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)}
    (hX : X ∈ vsBLamA s) (hX0 : X ≠ 0) : ∃ u : vsBU s, ((u : (vsBMt s)ˣ) : vsBMt s) = X := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  have hinj := (hdom X hX).resolve_left hX0
  -- left multiplication by `X` on `L` is injective, hence onto
  let φ : Subalgebra.toSubmodule (vsBLamA s) →ₗ[ZMod I.p] Subalgebra.toSubmodule (vsBLamA s) :=
    { toFun := fun Y => ⟨X * Y.1, (vsBLamA s).mul_mem hX (show Y.1 ∈ vsBLamA s from Y.2)⟩
      map_add' := fun Y Z => by ext1; simp [mul_add]
      map_smul' := fun c Y => by ext1; simp }
  have hφ : Function.Injective φ := by
    intro Y Z hYZ
    have e : X * Y.1 = X * Z.1 := congrArg Subtype.val hYZ
    ext1
    apply Matrix.ext_of_mulVec_single
    intro j
    apply eq_of_sub_eq_zero
    apply hinj
    rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, e, sub_self]
  have hsurj := LinearMap.injective_iff_surjective.mp hφ
  obtain ⟨Y, hY⟩ := hsurj ⟨1, (vsBLamA s).one_mem⟩
  have hXY : X * Y.1 = 1 := congrArg Subtype.val hY
  have hYX : Y.1 * X = 1 := Matrix.mul_eq_one_comm.mp hXY
  exact ⟨⟨⟨X, Y, hXY, hYX⟩, hX, Y.2⟩, rfl⟩

end GI.Proved
