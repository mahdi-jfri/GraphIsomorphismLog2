import Workspace.Proved.VsQDrvMath
import Workspace.Proved.VsWFrameLoc
import Workspace.Proved.VsQMat

/-!
# Local matrices of a state

For a valid state `s` (problem `(H, W, W', x, y)`), the frame `cs = vsWComp p ws' ws` is a basis
of a complement of `W'` in `W`. Write `D = |cs|` and `comb a = ∑ a_j c_j`. The local matrix
`Λ(h)` of `h ∈ H` is the matrix of `φ(h)` on `W/W'` in this basis.

* `vsQLam_comb`: `φ(h) (comb a) - comb (Λ(h) a) ∈ W'`.
* `vsQLam_mul`, `vsQLam_one`: `Λ` is multiplicative on `H`.
* `vsQD_eq`: `D = s.dim`.
* `vsQAb_iff`: `H` acts on `W/W'` as an abelian group iff the `Λ(h)` commute.
* `vsQLift`: the lift `W' ⊔ comb U` of a local subspace `U`; it is `K`-invariant when `U` is
  `Λ(K)`-invariant (`vsQLift_inv`), and its rank is `rk W' + dim U` (`vsQLift_finrank`).
-/

open Matrix

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv

variable {I : VecStabInst}

/-- The frame of a state. -/
noncomputable def vsQCs (s : VsQSt I) : List (List ℕ) := vsWComp I.p s.ws' s.ws

/-- The local dimension. -/
noncomputable abbrev vsQD (s : VsQSt I) : ℕ := (vsQCs s).length

/-- The local matrix of `h`. -/
noncomputable def vsQLam (s : VsQSt I) (h : Perm (Fin I.n)) :
    Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p) :=
  vsWM I.p (vsQD s) (vsWLoc I.p I.d s.ws' (vsQCs s) (vsQL (vsQPhi I h)ᵀ))

/-- The combination of the frame. -/
noncomputable abbrev vsQComb (s : VsQSt I) : (Fin (vsQD s) → ZMod I.p) →ₗ[ZMod I.p] VsQV I :=
  vsWComb I.p I.d (vsQCs s)

theorem vsWV_vsQVec {p d : ℕ} [NeZero p] (v : Fin d → ZMod p) : vsWV p d (vsQVec v) = v := by
  funext j
  simp [vsWV, vsWR, vsF, vsQVec, List.getD_eq_getElem?_getD]

theorem vsQVec_fit {p d : ℕ} [NeZero p] (v : Fin d → ZMod p) : VsWFit p d [vsQVec v] := by
  intro u hu
  rw [List.mem_singleton] at hu
  subst hu
  refine ⟨fun y hy => ?_, by simp [vsQVec]⟩
  simp only [vsQVec, List.mem_map] at hy
  obtain ⟨j, -, rfl⟩ := hy
  exact ZMod.val_lt _

section

variable {s : VsQSt I} (hs : VsQStOK s)
include hs

theorem VsQStOK.sup : vsQSp I s.ws' ⊔ vsQSp I s.ws = vsQSp I s.ws := sup_eq_right.mpr hs.prob.sub

theorem VsQStOK.frame : vsQSp I s.ws' ⊔ vsQSp I (vsQCs s) = vsQSp I s.ws := by
  rw [vsQCs, vsWFrame_sup I.prime hs.fit' hs.fit, hs.sup]

theorem VsQStOK.comb_mem (a : Fin (vsQD s) → ZMod I.p) : vsQComb s a ∈ vsQSp I s.ws := by
  rw [← hs.frame]
  refine Submodule.mem_sup_right ?_
  change _ ∈ vsWSp I.p I.d (vsQCs s)
  rw [← vsWComb_range]
  exact ⟨a, rfl⟩

theorem VsQStOK.comb_eq_zero {a : Fin (vsQD s) → ZMod I.p} (h : vsQComb s a ∈ vsQSp I s.ws') :
    a = 0 :=
  vsWFrame_indep I.prime hs.fit' hs.fit h

/-- Every `w ∈ W` is `w' + comb a` with `w' ∈ W'`. -/
theorem VsQStOK.decomp {w : VsQV I} (hw : w ∈ vsQSp I s.ws) :
    ∃ w' ∈ vsQSp I s.ws', ∃ a, w = w' + vsQComb s a := by
  rw [← hs.frame] at hw
  obtain ⟨w', hw', c, hc, rfl⟩ := Submodule.mem_sup.mp hw
  change c ∈ vsWSp I.p I.d (vsQCs s) at hc
  rw [← vsWComb_range] at hc
  obtain ⟨a, rfl⟩ := hc
  exact ⟨w', hw', a, rfl⟩

/-- **The local matrix acts on the frame.** -/
theorem vsQLam_comb {h : Perm (Fin I.n)} (hh : h ∈ gens s.hs) (a : Fin (vsQD s) → ZMod I.p) :
    (vsQPhi I h).mulVec (vsQComb s a) - vsQComb s ((vsQLam s h).mulVec a) ∈ vsQSp I s.ws' := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  set v := vsQComb s a with hv
  set x := vsQVec v with hx
  have hxf : VsWFit I.p I.d [x] := vsQVec_fit v
  have hxv : vsWV I.p I.d x = v := vsWV_vsQVec v
  have hvW : vsWV I.p I.d x ∈ vsWSp I.p I.d s.ws' ⊔ vsWSp I.p I.d s.ws := by
    rw [hxv]; exact hs.sup.symm ▸ hs.comb_mem a
  -- the coordinates of `x` are `a`
  have hco : vsWCoV I.p s.ws' s.ws x = a := by
    refine vsWCo_unique I.prime hs.fit' hs.fit (vsWCo_sub I.prime hs.fit' hs.fit hxf hvW) ?_
    rw [hxv, hv, show vsQComb s a = vsWComb I.p I.d (vsWComp I.p s.ws' s.ws) a from rfl, sub_self]
    exact Submodule.zero_mem _
  set A := vsQL (vsQPhi I h)ᵀ with hA
  have hsq := vsQL_sq (vsQPhi I h)ᵀ
  have hAsq : VsWSq I.p I.d A := ⟨fun r hr => hsq.rows r hr, hsq.len⟩
  have hlin : ∀ u, vsWLin I.p I.d A u = (vsQPhi I h).mulVec u := by
    intro u
    simp only [hA, vsWLin, vsWM, vsFMatrix_vsQL, transpose_transpose, Matrix.toLin'_apply]
  have hW' : ∀ u ∈ vsWSp I.p I.d s.ws', vsWLin I.p I.d A u ∈ vsWSp I.p I.d s.ws' := by
    intro u hu; rw [hlin]; exact hs.prob.invW' h hh u hu
  have hW : ∀ u ∈ vsWSp I.p I.d s.ws' ⊔ vsWSp I.p I.d s.ws,
      vsWLin I.p I.d A u ∈ vsWSp I.p I.d s.ws' ⊔ vsWSp I.p I.d s.ws := by
    intro u hu
    have hs' : vsWSp I.p I.d s.ws' ⊔ vsWSp I.p I.d s.ws = vsWSp I.p I.d s.ws := hs.sup
    rw [hs'] at hu ⊢
    rw [hlin]; exact hs.prob.invW h hh u hu
  have hloc := vsWLoc_co I.prime hs.fit' hs.fit hAsq hW' hW hxf hvW
  rw [hco] at hloc
  have himg : vsWV I.p I.d (vsFRowMul I.p x A (vsWZ I.d)) = (vsQPhi I h).mulVec v := by
    rw [vsWV_img hAsq.2 (fun r hr => (hAsq.1 r hr).2.le), hlin, hxv]
  have hx'W : vsWV I.p I.d (vsFRowMul I.p x A (vsWZ I.d)) ∈
      vsWSp I.p I.d s.ws' ⊔ vsWSp I.p I.d s.ws := by
    have hs' : vsWSp I.p I.d s.ws' ⊔ vsWSp I.p I.d s.ws = vsWSp I.p I.d s.ws := hs.sup
    rw [himg, hs']; exact hs.prob.invW h hh v (hs.comb_mem a)
  have hsub := vsWCo_sub I.prime hs.fit' hs.fit (vsWImg_one_fit I.prime.pos hAsq x) hx'W
  rw [himg] at hsub
  change _ - vsWComb I.p I.d (vsWComp I.p s.ws' s.ws) (vsWCoV I.p s.ws' s.ws _) ∈ _ at hsub
  rw [hloc] at hsub
  exact hsub

/-- Two local vectors with the same combination modulo `W'` are equal. -/
theorem VsQStOK.comb_inj {a b : Fin (vsQD s) → ZMod I.p}
    (h : vsQComb s a - vsQComb s b ∈ vsQSp I s.ws') : a = b := by
  rw [← map_sub] at h
  exact sub_eq_zero.mp (hs.comb_eq_zero h)

theorem vsQLam_ext {M N : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)}
    (h : ∀ a, vsQComb s (M.mulVec a) - vsQComb s (N.mulVec a) ∈ vsQSp I s.ws') : M = N := by
  have : ∀ a, M.mulVec a = N.mulVec a := fun a => hs.comb_inj (h a)
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun a => by simp only [Matrix.toLin'_apply]; exact this a

theorem vsQLam_one : vsQLam s 1 = 1 := by
  apply vsQLam_ext hs
  intro a
  have := vsQLam_comb hs (one_mem _) a
  rw [vsQPhi_one, one_mulVec] at this
  have h2 := Submodule.neg_mem _ this
  rw [neg_sub] at h2
  rw [one_mulVec]
  exact h2

theorem vsQLam_mul {g h : Perm (Fin I.n)} (hg : g ∈ gens s.hs) (hh : h ∈ gens s.hs) :
    vsQLam s (g * h) = vsQLam s g * vsQLam s h := by
  apply vsQLam_ext hs
  intro a
  have h1 := vsQLam_comb hs (mul_mem hg hh) a
  have h2 := vsQLam_comb hs hh a
  have h3 := vsQLam_comb hs hg ((vsQLam s h).mulVec a)
  have h4 := hs.prob.invW' g hg _ h2
  rw [vsQPhi_mul (hs.prob.le hg) (hs.prob.le hh), ← mulVec_mulVec] at h1
  rw [mulVec_sub] at h4
  rw [← mulVec_mulVec]
  have := Submodule.sub_mem _ (Submodule.add_mem _ h4 h3) h1
  convert this using 1
  abel

/-- The local matrices as a hom to units of `End`. -/
noncomputable def vsQRho : gens s.hs →* (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun h => Matrix.toLin' (vsQLam s h.1)
      map_one' := by simp [vsQLam_one hs]; rfl
      map_mul' := fun g h => by
        simp only [Subgroup.coe_mul, vsQLam_mul hs g.2 h.2, Matrix.toLin'_mul]; rfl }

theorem vsQRho_apply (h : gens s.hs) (a : Fin (vsQD s) → ZMod I.p) :
    ((vsQRho hs h : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ) :
      Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) a = (vsQLam s h.1).mulVec a := by
  simp [vsQRho, Matrix.toLin'_apply]

/-- **`D` is the rank of `W/W'`.** -/
theorem vsQD_eq : vsQD s = s.dim := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  have hinj : Function.Injective (vsQComb s) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    exact hs.comb_eq_zero (by rw [LinearMap.mem_ker.mp ha]; exact Submodule.zero_mem _)
  have hinf : vsQSp I s.ws' ⊓ LinearMap.range (vsQComb s) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hv, a, rfl⟩
    rw [hs.comb_eq_zero hv, map_zero]
  have hsup : vsQSp I s.ws' ⊔ LinearMap.range (vsQComb s) = vsQSp I s.ws := by
    rw [vsWComb_range]; exact hs.frame
  have e := Submodule.finrank_sup_add_finrank_inf_eq (vsQSp I s.ws') (LinearMap.range (vsQComb s))
  rw [hsup, hinf, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_fin_fun] at e
  unfold VsQSt.dim vsQRk
  omega

/-- **The abelian test.** -/
theorem vsQAb_iff : s.Ab ↔ ∀ g ∈ gens s.hs, ∀ h ∈ gens s.hs,
    vsQLam s g * vsQLam s h = vsQLam s h * vsQLam s g := by
  constructor
  · intro hab g hg h hh
    rw [← vsQLam_mul hs hg hh, ← vsQLam_mul hs hh hg]
    apply vsQLam_ext hs
    intro a
    have h1 := vsQLam_comb hs (mul_mem hg hh) a
    have h2 := vsQLam_comb hs (mul_mem hh hg) a
    have h3 := hab g hg h hh _ (hs.comb_mem a)
    rw [vsQPhi_mul (hs.prob.le hg) (hs.prob.le hh), ← mulVec_mulVec] at h1
    rw [vsQPhi_mul (hs.prob.le hh) (hs.prob.le hg), ← mulVec_mulVec] at h2
    have := Submodule.add_mem _ (Submodule.sub_mem _ h2 h1) h3
    convert this using 1
    simp only [mulVec_mulVec]
    abel
  · intro hc g hg h hh w hw
    obtain ⟨w', hw', a, rfl⟩ := hs.decomp hw
    have e1 := hs.prob.invW' g hg _ (hs.prob.invW' h hh w' hw')
    have e2 := hs.prob.invW' h hh _ (hs.prob.invW' g hg w' hw')
    have h1 := vsQLam_comb hs (mul_mem hg hh) a
    have h2 := vsQLam_comb hs (mul_mem hh hg) a
    rw [vsQPhi_mul (hs.prob.le hg) (hs.prob.le hh), ← mulVec_mulVec] at h1
    rw [vsQPhi_mul (hs.prob.le hh) (hs.prob.le hg), ← mulVec_mulVec] at h2
    rw [vsQLam_mul hs hg hh, hc g hg h hh] at h1
    rw [vsQLam_mul hs hh hg] at h2
    have := Submodule.add_mem _ (Submodule.sub_mem _ e1 e2) (Submodule.sub_mem _ h1 h2)
    convert this using 1
    simp only [mulVec_add]
    abel

/-! ### Lifts -/

/-- The lift of a local subspace. -/
noncomputable def vsQLift (s : VsQSt I) (U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :
    Submodule (ZMod I.p) (VsQV I) :=
  vsQSp I s.ws' ⊔ U.map (vsQComb s)

theorem vsQLift_inv {K : Subgroup (Perm (Fin I.n))} (hK : K ≤ gens s.hs)
    {U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)}
    (hU : ∀ h ∈ K, ∀ a ∈ U, (vsQLam s h).mulVec a ∈ U) : VsQInv I K (vsQLift s U) := by
  intro h hh w hw
  obtain ⟨w', hw', c, ⟨a, ha, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hw
  rw [mulVec_add]
  have h1 := hs.prob.invW' h (hK hh) w' hw'
  have h2 := vsQLam_comb hs (hK hh) a
  have : (vsQPhi I h).mulVec (vsQComb s a) =
      ((vsQPhi I h).mulVec (vsQComb s a) - vsQComb s ((vsQLam s h).mulVec a)) +
        vsQComb s ((vsQLam s h).mulVec a) := by abel
  rw [this, ← add_assoc]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.add_mem _ h1 h2))
    (Submodule.mem_sup_right ⟨_, hU h hh a ha, rfl⟩)

theorem vsQLift_finrank (U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :
    Module.finrank (ZMod I.p) (vsQLift s U) =
      Module.finrank (ZMod I.p) (vsQSp I s.ws') + Module.finrank (ZMod I.p) U := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  have hinj : Function.Injective (vsQComb s) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    exact hs.comb_eq_zero (by rw [LinearMap.mem_ker.mp ha]; exact Submodule.zero_mem _)
  have hinf : vsQSp I s.ws' ⊓ U.map (vsQComb s) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hv, a, -, rfl⟩
    rw [hs.comb_eq_zero hv, map_zero]
  have e := Submodule.finrank_sup_add_finrank_inf_eq (vsQSp I s.ws') (U.map (vsQComb s))
  rw [hinf, finrank_bot, add_zero,
    ← (Submodule.equivMapOfInjective _ hinj U).finrank_eq] at e
  unfold vsQLift
  omega

theorem vsQLift_top : vsQLift s ⊤ = vsQSp I s.ws := by
  rw [vsQLift, Submodule.map_top, vsWComb_range]; exact hs.frame

theorem vsQLift_bot : vsQLift s ⊥ = vsQSp I s.ws' := by
  rw [vsQLift, Submodule.map_bot, sup_bot_eq]

theorem vsQLift_mono {U U' : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)} (h : U ≤ U') :
    vsQLift s U ≤ vsQLift s U' :=
  sup_le_sup_left (Submodule.map_mono h) _

theorem vsQLift_lt {U U' : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)} (h : U < U') :
    vsQLift s U < vsQLift s U' := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  refine lt_of_le_of_ne (vsQLift_mono hs h.le) fun he => ?_
  have h1 := vsQLift_finrank hs U
  have h2 := vsQLift_finrank hs U'
  rw [he] at h1
  have := Submodule.finrank_lt_finrank_of_lt h
  omega

end

end GI.Proved
