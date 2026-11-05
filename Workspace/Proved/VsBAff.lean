module

public import Workspace.Proved.VsQLoc
public import Workspace.Impl.VsBAct
public import Workspace.Impl.VsQSot

@[expose] public section

/-!
# The affine action of a state on local coordinates

For a valid state `s`, the points of `(x + W)/W'` are `x + comb a` for local vectors `a`
(`comb = vsQComb s`). The group `H = gens s.hs` acts on them, and in coordinates
`vsBAlpha s g a` is the coordinate vector of `φ(g)(x + comb a) - x`.

* `vsBCo`: coordinates of a vector of `W` (modulo `W'`); `vsBCo_sub`, `vsBCo_eq`.
* `vsBAlpha_act`: this is an action of `H` (`VsQPAct`).
* `vsBAlpha_zero_eq`: `vsBAlpha s g 0 = vsBCo s (y - x)` iff `φ(g) x - y ∈ W'`. So the answer
  set of the state is the transporter from `0` to `vsBCo s (y - x)`, and the stabilizer of the
  state is the stabilizer of `0`. This is the result used later.
* `vsBAct_vsQVec`: the program's list function `vsBAct` computes `vsBAlpha` on keys.
-/

namespace GI.Proved

open GI.Impl GI.Cited Equiv Matrix

variable {I : VecStabInst} {s : VsQSt I}

/-- The local coordinates of a vector (meaningful for vectors of `W`). -/
noncomputable def vsBCo (s : VsQSt I) (v : VsQV I) : Fin (vsQD s) → ZMod I.p :=
  vsWV I.p (vsQD s) (vsWCo I.p s.ws' (vsQCs s) (vsQVec v))

/-- The action on local coordinates. -/
noncomputable def vsBAlpha (s : VsQSt I) (g : Perm (Fin I.n)) (a : Fin (vsQD s) → ZMod I.p) :
    Fin (vsQD s) → ZMod I.p :=
  vsBCo s ((vsQPhi I g).mulVec (vsWV I.p I.d s.x + vsQComb s a) - vsWV I.p I.d s.x)

variable (hs : VsQStOK s)
include hs

theorem vsBCo_sub {v : VsQV I} (hv : v ∈ vsQSp I s.ws) :
    v - vsQComb s (vsBCo s v) ∈ vsQSp I s.ws' := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h := vsWCo_sub I.prime hs.fit' hs.fit (vsQVec_fit v) (by
    rw [vsWV_vsQVec, hs.sup]; exact hv)
  rw [vsWV_vsQVec] at h
  exact h

theorem vsBCo_eq {v : VsQV I} {a : Fin (vsQD s) → ZMod I.p}
    (h : v - vsQComb s a ∈ vsQSp I s.ws') : vsBCo s v = a := by
  have hv : v ∈ vsQSp I s.ws := by
    have := Submodule.add_mem _ (hs.prob.sub h) (hs.comb_mem a)
    rwa [sub_add_cancel] at this
  exact vsWCo_unique I.prime hs.fit' hs.fit (vsBCo_sub hs hv) h

/-- Two vectors of `W` have the same coordinates iff they agree modulo `W'`. -/
theorem vsBCo_eq_iff {u v : VsQV I} (hu : u ∈ vsQSp I s.ws) (hv : v ∈ vsQSp I s.ws) :
    vsBCo s u = vsBCo s v ↔ u - v ∈ vsQSp I s.ws' := by
  constructor
  · intro h
    have h1 := vsBCo_sub hs hu
    have h2 := vsBCo_sub hs hv
    rw [h] at h1
    have := Submodule.sub_mem _ h1 h2
    rwa [sub_sub_sub_cancel_right] at this
  · intro h
    apply vsBCo_eq hs
    have := Submodule.add_mem _ h (vsBCo_sub hs hv)
    rwa [sub_add_sub_cancel] at this

theorem vsBCo_comb (a : Fin (vsQD s) → ZMod I.p) : vsBCo s (vsQComb s a) = a :=
  vsBCo_eq hs (by rw [sub_self]; exact zero_mem _)

/-- The moved point stays in `x + W`. -/
theorem vsBAlpha_mem {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) (a : Fin (vsQD s) → ZMod I.p) :
    (vsQPhi I g).mulVec (vsWV I.p I.d s.x + vsQComb s a) - vsWV I.p I.d s.x ∈ vsQSp I s.ws := by
  rw [Matrix.mulVec_add, add_sub_right_comm]
  exact Submodule.add_mem _ (hs.prob.cx g hg) (hs.prob.invW g hg _ (hs.comb_mem a))

/-- **The action.** -/
theorem vsBAlpha_act : GI.Impl.VsQPAct (gens s.hs) (vsBAlpha s) where
  one a := by
    rw [vsBAlpha, vsQPhi_one, Matrix.one_mulVec, add_sub_cancel_left]
    exact vsBCo_comb hs a
  mul g hg h hh a := by
    set x := vsWV I.p I.d s.x
    set w := (vsQPhi I h).mulVec (x + vsQComb s a) - x with hw
    have hwW : w ∈ vsQSp I s.ws := vsBAlpha_mem hs hh a
    have hb := vsBCo_sub hs hwW
    set b := vsBCo s w
    have e1 : (vsQPhi I (g * h)).mulVec (x + vsQComb s a) - x =
        (vsQPhi I g).mulVec (x + w) - x := by
      rw [hw, add_sub_cancel, ← vsQPhi_mulVec_mul (hs.prob.le hg) (hs.prob.le hh)]
    show vsBCo s ((vsQPhi I (g * h)).mulVec (x + vsQComb s a) - x) =
      vsBCo s ((vsQPhi I g).mulVec (x + vsQComb s b) - x)
    have hm1 : (vsQPhi I g).mulVec (x + w) - x ∈ vsQSp I s.ws := by
      rw [← e1]; exact vsBAlpha_mem hs (mul_mem hg hh) a
    rw [e1, vsBCo_eq_iff hs hm1 (vsBAlpha_mem hs hg b)]
    have : (vsQPhi I g).mulVec (x + w) - x - ((vsQPhi I g).mulVec (x + vsQComb s b) - x) =
        (vsQPhi I g).mulVec (w - vsQComb s b) := by
      rw [sub_sub_sub_cancel_right, ← Matrix.mulVec_sub, add_sub_add_left_eq_sub]
    rw [this]
    exact hs.prob.invW' g hg _ hb

/-- **The transporter.** -/
theorem vsBAlpha_zero_eq {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) (y : VsQV I)
    (hy : y - vsWV I.p I.d s.x ∈ vsQSp I s.ws) :
    vsBAlpha s g 0 = vsBCo s (y - vsWV I.p I.d s.x) ↔
      (vsQPhi I g).mulVec (vsWV I.p I.d s.x) - y ∈ vsQSp I s.ws' := by
  have hm := vsBAlpha_mem hs hg 0
  rw [map_zero, add_zero] at hm
  rw [vsBAlpha, map_zero, add_zero, vsBCo_eq_iff hs hm hy, sub_sub_sub_cancel_right]

/-- **The stabilizer.** -/
theorem vsBAlpha_zero_eq_zero {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    vsBAlpha s g 0 = 0 ↔
      (vsQPhi I g).mulVec (vsWV I.p I.d s.x) - vsWV I.p I.d s.x ∈ vsQSp I s.ws' := by
  have h := vsBAlpha_zero_eq hs hg (vsWV I.p I.d s.x) (by rw [sub_self]; exact zero_mem _)
  rwa [sub_self, show vsBCo s 0 = 0 from by
    have := vsBCo_comb hs 0; rwa [map_zero] at this] at h

/-- **The list function computes the action** on canonical coordinate lists. -/
theorem vsBAct_vsQVec {g : Perm (Fin I.n)} (a : Fin (vsQD s) → ZMod I.p) :
    vsBAct I s.ws' (vsQCs s) s.x g (vsQVec a) = vsQVec (vsBAlpha s g a) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hp := I.prime.pos
  have hx := hs.fx s.x (List.mem_singleton_self _)
  have hc : VsWFit I.p I.d (vsQCs s) := vsWComp_fit hp hs.fit' hs.fit
  set pt := vsBPt I.p I.d (vsQCs s) s.x (vsQVec a)
  have hpt := vsBPt_fit hp (vsQCs s) hs.fx (vsQVec a) pt (List.mem_singleton_self _)
  set u := vsQApp I g⁻¹ pt
  have hu := vsQApp_fit (t := g⁻¹) (vsBPt_fit hp (vsQCs s) hs.fx (vsQVec a)) u
    (List.mem_singleton_self _)
  set L := vsLin I.p 1 (I.p - 1) u s.x
  have hL := vsLin_fit (a := 1) (b' := I.p - 1) (u := s.x) hp
    (vsQApp_fit (t := g⁻¹) (vsBPt_fit hp (vsQCs s) hs.fx (vsQVec a))) L (List.mem_singleton_self _)
  -- the vector of `L`
  have hcomb : vsWV I.p I.d (vsFRowMul I.p (vsQVec a) (vsQCs s) (vsWZ I.d)) = vsQComb s a := by
    rw [vsWV_rowMul I.d _ _ (fun r hr => (hc r hr).2.le), vsWV_vsQVec]
  have hptv : vsWV I.p I.d pt = vsWV I.p I.d s.x + vsQComb s a := by
    funext j
    have hl : (vsFRowMul I.p (vsQVec a) (vsQCs s) (vsWZ I.d)).length ≤ s.x.length := by
      rw [vsFRowMul, vsFMulAcc_foldl_length, hx.2]; simp [vsWZ]
    simp only [pt, vsBPt, vsWV_apply, vsF_vsLin _ _ _ hl, Nat.cast_one, one_smul, Pi.add_apply]
    rw [← hcomb]; rfl
  have huv : vsWV I.p I.d u = (vsQPhi I g).mulVec (vsWV I.p I.d s.x + vsQComb s a) := by
    rw [vsQApp_vsWV, inv_inv, hptv]
  have hLv : vsWV I.p I.d L = (vsQPhi I g).mulVec (vsWV I.p I.d s.x + vsQComb s a) -
      vsWV I.p I.d s.x := by
    funext j
    have hl : s.x.length ≤ u.length := by rw [hx.2, hu.2]
    have e := congrFun huv j
    rw [vsWV_apply] at e
    simp only [L, vsWV_apply, vsF_vsLin _ _ _ hl, Nat.cast_one, one_smul, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply]
    have : ((I.p - 1 : ℕ) : ZMod I.p) = -1 := by
      rw [Nat.cast_sub hp, ZMod.natCast_self, zero_sub, Nat.cast_one]
    rw [e, this, smul_eq_mul, neg_one_mul, ← sub_eq_add_neg]
  have hLq : L = vsQVec (vsWV I.p I.d L) := by
    have := vsQVec_of (d := I.d) hL.2 hL.1
    exact this
  have hco := vsWCo_fit hp s.ws' (vsQCs s) L _ (List.mem_singleton_self _)
  rw [vsBAct, vsBAlpha, vsBCo, ← hLv, ← hLq]
  exact vsQVec_of hco.2 hco.1

omit hs in
/-- The group of `1 :: hs` is `⟨hs⟩`. -/
theorem vsB_genGroup_cons (hs' : List (Perm (Fin I.n))) :
    GI.Lang.genGroup (1 :: hs') = gens hs' := by
  apply le_antisymm
  · refine Subgroup.closure_le _ |>.mpr fun g hg => ?_
    rcases List.mem_cons.mp hg with rfl | hg
    · exact one_mem _
    · exact Subgroup.subset_closure hg
  · exact Subgroup.closure_mono fun g hg => List.mem_cons_of_mem _ hg

/-- **The stabilizer of `0`** is the stabilizer of the state. -/
theorem vsB_stabG_eq :
    GI.Impl.vsQStabG (vsBAlpha_act hs) (le_of_eq (vsB_genGroup_cons s.hs)) 0 =
      vsQStab (gens s.hs) (vsQSp I s.ws') (vsWV I.p I.d s.x) hs.prob.le hs.prob.invW' := by
  ext g
  rw [mem_vsQStab]
  change g ∈ GI.Lang.genGroup (1 :: s.hs) ∧ vsBAlpha s g 0 = 0 ↔ _
  rw [vsB_genGroup_cons]
  constructor
  · rintro ⟨hg, h0⟩; exact ⟨hg, (vsBAlpha_zero_eq_zero hs hg).mp h0⟩
  · rintro ⟨hg, h0⟩; exact ⟨hg, (vsBAlpha_zero_eq_zero hs hg).mpr h0⟩

/-- The target key: the program computes `vsQVec (vsBCo s (y - x))`. -/
theorem vsB_target :
    vsWCo I.p s.ws' (vsQCs s) (vsLin I.p 1 (I.p - 1) s.y s.x) =
      vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hp := I.prime.pos
  have hx := hs.fx s.x (List.mem_singleton_self _)
  have hy := hs.fy s.y (List.mem_singleton_self _)
  have hL := vsLin_fit (a := 1) (b' := I.p - 1) (u := s.x) hp hs.fy _ (List.mem_singleton_self _)
  have hLv : vsWV I.p I.d (vsLin I.p 1 (I.p - 1) s.y s.x) = vsWV I.p I.d s.y - vsWV I.p I.d s.x := by
    funext j
    have hl : s.x.length ≤ s.y.length := by rw [hx.2, hy.2]
    simp only [vsWV_apply, vsF_vsLin _ _ _ hl, Nat.cast_one, one_smul, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply]
    have : ((I.p - 1 : ℕ) : ZMod I.p) = -1 := by
      rw [Nat.cast_sub hp, ZMod.natCast_self, zero_sub, Nat.cast_one]
    rw [this, smul_eq_mul, neg_one_mul, ← sub_eq_add_neg]
  have hLq : vsLin I.p 1 (I.p - 1) s.y s.x = vsQVec (vsWV I.p I.d (vsLin I.p 1 (I.p - 1) s.y s.x)) :=
    vsQVec_of (d := I.d) hL.2 hL.1
  have hco := vsWCo_fit hp s.ws' (vsQCs s) (vsLin I.p 1 (I.p - 1) s.y s.x) _ (List.mem_singleton_self _)
  rw [vsBCo, ← hLv, ← hLq]
  exact vsQVec_of hco.2 hco.1

end GI.Proved
