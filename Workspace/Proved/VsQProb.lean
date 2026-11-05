module

public import Workspace.Cited.AlgoLinear
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.Submodule.Map

@[expose] public section

/-!
# The recursive problem

`G = ⟨gs⟩ ≤ Sym(n)` acts on `𝔽_p^d` through `φ`. The algorithm solves, for a subgroup `H ≤ G`,
two `H`-invariant subspaces `W' ≤ W` and vectors `x, y` with `φ(h) x - x ∈ W` for `h ∈ H` and
`y - x ∈ W` (`VsQProb`), the problem

  `S = {h ∈ H : φ(h) x - y ∈ W'}`  (`vsQSol`).

`S` is empty or a left coset `z • T` of `T = {h ∈ H : φ(h) x - x ∈ W'}` (`vsQSol_coset`). The
vector stabilizer `C_G(v)` is the case `H = G`, `W = 𝔽_p^d`, `W' = 0`, `x = y = v`.

The recursion uses two splittings, proved here:
* a chain `W' ≤ U ≤ W` of `H`-invariant subspaces (`vsQSol_chain_empty`, `vsQSol_chain`):
  first the problem modulo `U`, then the problem inside `U` for its stabilizer;
* left cosets `t • C` covering `H` (`vsQSol_cosets`): `S` is the union of the sets
  `t • S_t`, where `S_t` is the problem for `C` with target `φ(t)⁻¹ y`; the pieces are pasted
  by `vsQSol_paste`.
-/

namespace GI.Proved

open GI.Cited Equiv Matrix
open scoped Pointwise

variable (I : VecStabInst)

open Classical in
/-- `φ`, extended by the identity outside `G`. -/
noncomputable def vsQPhi (x : Perm (Fin I.n)) : Matrix (Fin I.d) (Fin I.d) (ZMod I.p) :=
  if hx : x ∈ gens I.gs then ((I.φ ⟨x, hx⟩ : GL (Fin I.d) (ZMod I.p)) : Matrix _ _ _) else 1

/-- The vectors. -/
abbrev VsQV := Fin I.d → ZMod I.p

variable {I}

theorem vsQPhi_of_mem {x : Perm (Fin I.n)} (hx : x ∈ gens I.gs) :
    vsQPhi I x = ((I.φ ⟨x, hx⟩ : GL (Fin I.d) (ZMod I.p)) : Matrix _ _ _) := by
  rw [vsQPhi, dif_pos hx]

theorem vsQPhi_one : vsQPhi I 1 = 1 := by
  rw [vsQPhi_of_mem (one_mem _)]
  have : (⟨1, one_mem _⟩ : gens I.gs) = 1 := rfl
  rw [this, map_one]; rfl

theorem vsQPhi_mul {x y : Perm (Fin I.n)} (hx : x ∈ gens I.gs) (hy : y ∈ gens I.gs) :
    vsQPhi I (x * y) = vsQPhi I x * vsQPhi I y := by
  rw [vsQPhi_of_mem (mul_mem hx hy), vsQPhi_of_mem hx, vsQPhi_of_mem hy]
  have : (⟨x * y, mul_mem hx hy⟩ : gens I.gs) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul]; rfl

theorem vsQPhi_inv_mul {x : Perm (Fin I.n)} (hx : x ∈ gens I.gs) :
    vsQPhi I x⁻¹ * vsQPhi I x = 1 := by
  rw [← vsQPhi_mul (inv_mem hx) hx, inv_mul_cancel, vsQPhi_one]

theorem vsQPhi_mul_inv {x : Perm (Fin I.n)} (hx : x ∈ gens I.gs) :
    vsQPhi I x * vsQPhi I x⁻¹ = 1 := by
  rw [← vsQPhi_mul hx (inv_mem hx), mul_inv_cancel, vsQPhi_one]

theorem vsQPhi_mulVec_mul {x y : Perm (Fin I.n)} (hx : x ∈ gens I.gs) (hy : y ∈ gens I.gs)
    (v : VsQV I) : vsQPhi I (x * y) *ᵥ v = vsQPhi I x *ᵥ (vsQPhi I y *ᵥ v) := by
  rw [vsQPhi_mul hx hy, mulVec_mulVec]

theorem vsQPhi_mulVec_inv {x : Perm (Fin I.n)} (hx : x ∈ gens I.gs) (v : VsQV I) :
    vsQPhi I x⁻¹ *ᵥ (vsQPhi I x *ᵥ v) = v := by
  rw [mulVec_mulVec, vsQPhi_inv_mul hx, one_mulVec]

theorem vsQPhi_mulVec_inv' {x : Perm (Fin I.n)} (hx : x ∈ gens I.gs) (v : VsQV I) :
    vsQPhi I x *ᵥ (vsQPhi I x⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, vsQPhi_mul_inv hx, one_mulVec]

variable (I)

/-- `W` is mapped into itself by every element of `H`. -/
def VsQInv (H : Subgroup (Perm (Fin I.n))) (W : Submodule (ZMod I.p) (VsQV I)) : Prop :=
  ∀ h ∈ H, ∀ w ∈ W, vsQPhi I h *ᵥ w ∈ W

/-- The hypotheses of the problem `(H, W, W', x, y)`. -/
structure VsQProb (H : Subgroup (Perm (Fin I.n))) (W W' : Submodule (ZMod I.p) (VsQV I))
    (x y : VsQV I) : Prop where
  le : H ≤ gens I.gs
  sub : W' ≤ W
  invW : VsQInv I H W
  invW' : VsQInv I H W'
  cx : ∀ h ∈ H, vsQPhi I h *ᵥ x - x ∈ W
  cy : y - x ∈ W

/-- The answer set `{h ∈ H : φ(h) x - y ∈ W'}`. -/
def vsQSol (H : Subgroup (Perm (Fin I.n))) (W' : Submodule (ZMod I.p) (VsQV I)) (x y : VsQV I) :
    Set (Perm (Fin I.n)) :=
  {h | h ∈ H ∧ vsQPhi I h *ᵥ x - y ∈ W'}

variable {I}

theorem VsQInv.mono {H K : Subgroup (Perm (Fin I.n))} {W : Submodule (ZMod I.p) (VsQV I)}
    (h : VsQInv I H W) (hK : K ≤ H) : VsQInv I K W := fun k hk => h k (hK hk)

/-- An element of `H` maps `W` onto `W` (its inverse maps `W` into `W`). -/
theorem VsQInv.inv_mem {H : Subgroup (Perm (Fin I.n))} {W : Submodule (ZMod I.p) (VsQV I)}
    (h : VsQInv I H W) (hle : H ≤ gens I.gs) {g : Perm (Fin I.n)} (hg : g ∈ H) {w : VsQV I}
    (hw : vsQPhi I g *ᵥ w ∈ W) : w ∈ W := by
  have := h g⁻¹ (H.inv_mem hg) _ hw
  rwa [vsQPhi_mulVec_inv (hle hg)] at this

/-- The stabilizer `{h ∈ H : φ(h) x - x ∈ W'}` is a subgroup when `W'` is invariant. -/
def vsQStab (H : Subgroup (Perm (Fin I.n))) (W' : Submodule (ZMod I.p) (VsQV I)) (x : VsQV I)
    (hle : H ≤ gens I.gs) (hinv : VsQInv I H W') : Subgroup (Perm (Fin I.n)) where
  carrier := vsQSol I H W' x x
  one_mem' := ⟨H.one_mem, by simp [vsQPhi_one]⟩
  mul_mem' := by
    rintro a b ⟨ha, hax⟩ ⟨hb, hbx⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    have e : vsQPhi I (a * b) *ᵥ x - x =
        vsQPhi I a *ᵥ (vsQPhi I b *ᵥ x - x) + (vsQPhi I a *ᵥ x - x) := by
      rw [vsQPhi_mulVec_mul (hle ha) (hle hb), mulVec_sub]; abel
    rw [e]
    exact W'.add_mem (hinv a ha _ hbx) hax
  inv_mem' := by
    rintro a ⟨ha, hax⟩
    refine ⟨H.inv_mem ha, ?_⟩
    have e : vsQPhi I a⁻¹ *ᵥ x - x = -(vsQPhi I a⁻¹ *ᵥ (vsQPhi I a *ᵥ x - x)) := by
      rw [mulVec_sub, vsQPhi_mulVec_inv (hle ha)]; abel
    rw [e]
    exact W'.neg_mem (hinv _ (H.inv_mem ha) _ hax)

theorem mem_vsQStab {H : Subgroup (Perm (Fin I.n))} {W' : Submodule (ZMod I.p) (VsQV I)}
    {x : VsQV I} {hle : H ≤ gens I.gs} {hinv : VsQInv I H W'} {h : Perm (Fin I.n)} :
    h ∈ vsQStab H W' x hle hinv ↔ h ∈ H ∧ vsQPhi I h *ᵥ x - x ∈ W' := Iff.rfl

theorem vsQStab_le {H : Subgroup (Perm (Fin I.n))} {W' : Submodule (ZMod I.p) (VsQV I)}
    {x : VsQV I} {hle : H ≤ gens I.gs} {hinv : VsQInv I H W'} : vsQStab H W' x hle hinv ≤ H :=
  fun _ h => h.1

/-- **The answer is a coset.** If `z` is a solution, the solutions are `z • T`. -/
theorem vsQSol_coset {H : Subgroup (Perm (Fin I.n))} {W W' : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} (hP : VsQProb I H W W' x y) {z : Perm (Fin I.n)} (hz : z ∈ vsQSol I H W' x y) :
    vsQSol I H W' x y = z • (vsQStab H W' x hP.le hP.invW' : Set (Perm (Fin I.n))) := by
  ext h
  simp only [Set.mem_smul_set, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨hh, hhy⟩
    refine ⟨z⁻¹ * h, ⟨H.mul_mem (H.inv_mem hz.1) hh, ?_⟩, by group⟩
    have e : vsQPhi I (z⁻¹ * h) *ᵥ x - x =
        vsQPhi I z⁻¹ *ᵥ ((vsQPhi I h *ᵥ x - y) - (vsQPhi I z *ᵥ x - y)) := by
      simp only [vsQPhi_mulVec_mul (hP.le (H.inv_mem hz.1)) (hP.le hh), mulVec_sub,
        vsQPhi_mulVec_inv (hP.le hz.1)]
      abel
    rw [e]
    exact hP.invW' _ (H.inv_mem hz.1) _ (W'.sub_mem hhy hz.2)
  · rintro ⟨k, ⟨hk, hkx⟩, rfl⟩
    refine ⟨H.mul_mem hz.1 hk, ?_⟩
    have e : vsQPhi I (z * k) *ᵥ x - y =
        vsQPhi I z *ᵥ (vsQPhi I k *ᵥ x - x) + (vsQPhi I z *ᵥ x - y) := by
      rw [vsQPhi_mulVec_mul (hP.le hz.1) (hP.le hk), mulVec_sub]; abel
    rw [e]
    exact W'.add_mem (hP.invW' _ hz.1 _ hkx) hz.2

/-- With `W' = W` every element of `H` is a solution. -/
theorem vsQSol_top {H : Subgroup (Perm (Fin I.n))} {W : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} (hP : VsQProb I H W W x y) : vsQSol I H W x y = H := by
  ext h
  refine ⟨fun hh => hh.1, fun hh => ⟨hh, ?_⟩⟩
  have e : vsQPhi I h *ᵥ x - y = (vsQPhi I h *ᵥ x - x) - (y - x) := by abel
  rw [e]
  exact W.sub_mem (hP.cx h hh) hP.cy

/-! ### Chains -/

/-- The problem modulo an intermediate invariant subspace `U`. -/
theorem VsQProb.upper {H : Subgroup (Perm (Fin I.n))} {W W' U : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} (hP : VsQProb I H W W' x y) (hUW : U ≤ W) (hU : VsQInv I H U) :
    VsQProb I H W U x y :=
  ⟨hP.le, hUW, hP.invW, hU, hP.cx, hP.cy⟩

theorem vsQSol_mono {H : Subgroup (Perm (Fin I.n))} {W' U : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} (hWU : W' ≤ U) : vsQSol I H W' x y ⊆ vsQSol I H U x y :=
  fun _ h => ⟨h.1, hWU h.2⟩

theorem vsQSol_chain_empty {H : Subgroup (Perm (Fin I.n))} {W' U : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} (hWU : W' ≤ U) (h : vsQSol I H U x y = ∅) : vsQSol I H W' x y = ∅ :=
  Set.subset_eq_empty (vsQSol_mono hWU) h

/-- The problem inside `U` for the stabilizer modulo `U`. -/
theorem VsQProb.lower {H : Subgroup (Perm (Fin I.n))} {W W' U : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} (hP : VsQProb I H W W' x y) (hWU : W' ≤ U) (hU : VsQInv I H U)
    {z : Perm (Fin I.n)} (hz : z ∈ vsQSol I H U x y) :
    VsQProb I (vsQStab H U x hP.le hU) U W' x (vsQPhi I z⁻¹ *ᵥ y) := by
  refine ⟨vsQStab_le.trans hP.le, hWU, hU.mono vsQStab_le, hP.invW'.mono vsQStab_le,
    fun h hh => hh.2, ?_⟩
  have e : vsQPhi I z⁻¹ *ᵥ y - x = -(vsQPhi I z⁻¹ *ᵥ (vsQPhi I z *ᵥ x - y)) := by
    rw [mulVec_sub, vsQPhi_mulVec_inv (hP.le hz.1)]; abel
  rw [e]
  exact U.neg_mem (hU _ (H.inv_mem hz.1) _ hz.2)

theorem vsQSol_chain {H : Subgroup (Perm (Fin I.n))} {W W' U : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} (hP : VsQProb I H W W' x y) (hWU : W' ≤ U) (hU : VsQInv I H U)
    {z : Perm (Fin I.n)} (hz : z ∈ vsQSol I H U x y) :
    vsQSol I H W' x y = z • vsQSol I (vsQStab H U x hP.le hU) W' x (vsQPhi I z⁻¹ *ᵥ y) := by
  ext h
  simp only [Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨hh, hhy⟩
    refine ⟨z⁻¹ * h, ⟨⟨H.mul_mem (H.inv_mem hz.1) hh, ?_⟩, ?_⟩, by group⟩
    · have e : vsQPhi I (z⁻¹ * h) *ᵥ x - x =
          vsQPhi I z⁻¹ *ᵥ ((vsQPhi I h *ᵥ x - y) - (vsQPhi I z *ᵥ x - y)) := by
        simp only [vsQPhi_mulVec_mul (hP.le (H.inv_mem hz.1)) (hP.le hh), mulVec_sub,
          vsQPhi_mulVec_inv (hP.le hz.1)]
        abel
      rw [e]
      exact hU _ (H.inv_mem hz.1) _ (U.sub_mem (hWU hhy) hz.2)
    · have e : vsQPhi I (z⁻¹ * h) *ᵥ x - vsQPhi I z⁻¹ *ᵥ y =
          vsQPhi I z⁻¹ *ᵥ (vsQPhi I h *ᵥ x - y) := by
        rw [vsQPhi_mulVec_mul (hP.le (H.inv_mem hz.1)) (hP.le hh), mulVec_sub]
      rw [e]
      exact hP.invW' _ (H.inv_mem hz.1) _ hhy
  · rintro ⟨k, ⟨⟨hk, -⟩, hky⟩, rfl⟩
    refine ⟨H.mul_mem hz.1 hk, ?_⟩
    have e : vsQPhi I (z * k) *ᵥ x - y =
        vsQPhi I z *ᵥ (vsQPhi I k *ᵥ x - vsQPhi I z⁻¹ *ᵥ y) := by
      rw [vsQPhi_mulVec_mul (hP.le hz.1) (hP.le hk), mulVec_sub, vsQPhi_mulVec_inv' (hP.le hz.1)]
    rw [e]
    exact hP.invW' _ hz.1 _ hky

/-- The stabilizer of the lower problem is the stabilizer of the whole problem. -/
theorem vsQSol_chain_stab {H : Subgroup (Perm (Fin I.n))} {W W' U : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} (hP : VsQProb I H W W' x y) (hWU : W' ≤ U) (hU : VsQInv I H U) :
    vsQSol I (vsQStab H U x hP.le hU) W' x x = vsQSol I H W' x x := by
  ext h
  exact ⟨fun hh => ⟨hh.1.1, hh.2⟩, fun hh => ⟨⟨hh.1, hWU hh.2⟩, hh.2⟩⟩

/-! ### Cosets -/

/-- The problem for a subgroup `C` with target `φ(t)⁻¹ y`. -/
theorem VsQProb.coset {H C : Subgroup (Perm (Fin I.n))} {W W' : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} (hP : VsQProb I H W W' x y) (hC : C ≤ H) {t : Perm (Fin I.n)} (ht : t ∈ H) :
    VsQProb I C W W' x (vsQPhi I t⁻¹ *ᵥ y) := by
  refine ⟨hC.trans hP.le, hP.sub, hP.invW.mono hC, hP.invW'.mono hC,
    fun h hh => hP.cx h (hC hh), ?_⟩
  have e : vsQPhi I t⁻¹ *ᵥ y - x = -(vsQPhi I t⁻¹ *ᵥ (vsQPhi I t *ᵥ x - y)) := by
    rw [mulVec_sub, vsQPhi_mulVec_inv (hP.le ht)]; abel
  have hm : vsQPhi I t *ᵥ x - y ∈ W := by
    have := W.sub_mem (hP.cx t ht) hP.cy
    rwa [show vsQPhi I t *ᵥ x - x - (y - x) = vsQPhi I t *ᵥ x - y by abel] at this
  rw [e]
  exact W.neg_mem (hP.invW _ (H.inv_mem ht) _ hm)

/-- The solutions in one coset `t • C`. -/
theorem vsQSol_inter_coset {H C : Subgroup (Perm (Fin I.n))} {W W' : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} (hP : VsQProb I H W W' x y) (hC : C ≤ H) {t : Perm (Fin I.n)} (ht : t ∈ H) :
    vsQSol I H W' x y ∩ t • (C : Set (Perm (Fin I.n))) =
      t • vsQSol I C W' x (vsQPhi I t⁻¹ *ᵥ y) := by
  ext h
  simp only [Set.mem_inter_iff, Set.mem_smul_set, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨⟨hh, hhy⟩, c, hc, rfl⟩
    refine ⟨c, ⟨hc, ?_⟩, rfl⟩
    have e : vsQPhi I c *ᵥ x - vsQPhi I t⁻¹ *ᵥ y = vsQPhi I t⁻¹ *ᵥ (vsQPhi I (t * c) *ᵥ x - y) := by
      rw [vsQPhi_mulVec_mul (hP.le ht) (hP.le (hC hc)), mulVec_sub, vsQPhi_mulVec_inv (hP.le ht)]
    rw [e]
    exact hP.invW' _ (H.inv_mem ht) _ hhy
  · rintro ⟨c, ⟨hc, hcy⟩, rfl⟩
    refine ⟨⟨H.mul_mem ht (hC hc), ?_⟩, c, hc, rfl⟩
    have e : vsQPhi I (t * c) *ᵥ x - y = vsQPhi I t *ᵥ (vsQPhi I c *ᵥ x - vsQPhi I t⁻¹ *ᵥ y) := by
      rw [vsQPhi_mulVec_mul (hP.le ht) (hP.le (hC hc)), mulVec_sub, vsQPhi_mulVec_inv' (hP.le ht)]
    rw [e]
    exact hP.invW' _ ht _ hcy

/-- **Cosets.** If the cosets `t • C`, `t ∈ T ⊆ H`, cover `H`, the solutions are the union of
the solutions in each coset. -/
theorem vsQSol_cosets {H C : Subgroup (Perm (Fin I.n))} {W W' : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} (hP : VsQProb I H W W' x y) (hC : C ≤ H) (T : List (Perm (Fin I.n)))
    (hT : ∀ t ∈ T, t ∈ H) (hcov : ∀ h ∈ H, ∃ t ∈ T, t⁻¹ * h ∈ C) :
    vsQSol I H W' x y = ⋃ t ∈ T, t • vsQSol I C W' x (vsQPhi I t⁻¹ *ᵥ y) := by
  ext h
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · intro hh
    obtain ⟨t, htT, htc⟩ := hcov h hh.1
    refine ⟨t, htT, ?_⟩
    rw [← vsQSol_inter_coset hP hC (hT t htT)]
    exact ⟨hh, t⁻¹ * h, htc, by simp⟩
  · rintro ⟨t, htT, hh⟩
    rw [← vsQSol_inter_coset hP hC (hT t htT)] at hh
    exact hh.1

end GI.Proved
