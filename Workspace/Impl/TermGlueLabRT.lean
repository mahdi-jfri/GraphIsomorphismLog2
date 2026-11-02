import Workspace.Impl.TermGlueLabLift

/-!
# The label coset of one radical coset through the affine action

The terminal `I` of Theorem A.23 is an instance of the setting of
`TermGlueLabLift`: `P = Sym(B)`, rows `B → C`, the lifts `k = rowLift` of Theorem A.18.

* `tmGL_kerI`: conjugation by `H` keeps `ker φ = N*` (it is normal in `H`).
* `tmGL_liftI`: the lifts satisfy `TmGLLift` (Theorem A.18 through `tmGL_blockwise`).
* `tmGLAlign I τ`: the aligned target `y' = y^{k(τ)⁻¹}` ("Choose a blockwise lift `k(τ) ∈ K`
  of `τ N`, and put `y' = y^{k(τ)^{-1}}`").
* `tmGL_lab_affine`: for `τ` in the residual set, `h ∈ tmGlLab I r` exactly when `h` is a
  residual element and `F_{h τ⁻¹}` carries the label point of `x` to that of `y'`. With
  `tmGL_trans_supp` this is the paper's reduction to the affine transporter in the solvable
  supplement `S`, adjoined with `N`.
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Paper Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type}

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

/-- **Conjugation by `H` keeps `ker φ = N*`.** -/
theorem tmGL_kerI : TmGLKer I.Nb I.Hb I.φ := by
  intro h hh n hn h1
  have hk : ∀ x (hx : x ∈ I.Nb), phiT I.Nb I.φ x = 1 ↔
      x ∈ I.Nstar.map (cleanLocalGroup S.domGroup I.e I.i0).subtype := by
    intro x hx
    simp only [phiT, dif_pos hx]
    exact I.φ_ker ⟨x, hx⟩
  rw [hk _ hn] at h1
  rw [hk _ (I.normalizes.inv hh hn)]
  obtain ⟨m, hm, hme⟩ := h1
  let g : I.Hb := ⟨h, hh⟩
  refine ⟨_, I.Nstar_normal.conj_mem m hm g⁻¹, ?_⟩
  rw [← hme]
  rfl

/-- **The lifts of Theorem A.18 satisfy `TmGLLift`.** -/
theorem tmGL_liftI : TmGLLift I.Nb I.Hb I.φ (rowLift I.e I.i0) where
  cls h hh i := I.lift_mem hh i
  mul g hg h hh := by
    obtain ⟨mg, eg⟩ := rowLift_spec I.e I.i0 hg
    obtain ⟨mh, eh⟩ := rowLift_spec I.e I.i0 hh
    obtain ⟨mgh, egh⟩ := rowLift_spec I.e I.i0 (I.Hb.mul_mem hg hh)
    have hy : cleanRowPerm I.e (fun i => (rowLift I.e I.i0 g i * rowLift I.e I.i0 h i)⁻¹ *
        rowLift I.e I.i0 (g * h) i) ∈ S.domGroup := by
      have : (fun i => (rowLift I.e I.i0 g i * rowLift I.e I.i0 h i)⁻¹ *
          rowLift I.e I.i0 (g * h) i) =
          (rowLift I.e I.i0 g * rowLift I.e I.i0 h)⁻¹ * rowLift I.e I.i0 (g * h) := rfl
      rw [this, map_mul, map_inv, map_mul]
      exact S.domGroup.mul_mem (S.domGroup.inv_mem (S.domGroup.mul_mem mg mh)) mgh
    exact tmGL_blockwise I hy (by
      show (rowLift I.e I.i0 g I.i0 * rowLift I.e I.i0 h I.i0)⁻¹ *
        rowLift I.e I.i0 (g * h) I.i0 ∈ I.Nb
      rw [eg, eh, egh, inv_mul_cancel]; exact I.Nb.one_mem)
  kN n hn := by
    obtain ⟨m, e0⟩ := rowLift_spec I.e I.i0 (I.Nb_le hn)
    exact tmGL_blockwise I m (by rw [e0]; exact hn)

/-- **The aligned target** `y' = y^{k(τ)⁻¹}`. -/
noncomputable def tmGLAlign (τ : Perm I.B) : Fin L.q → I.B → C :=
  rowAct (fun i => (rowLift I.e I.i0 τ i)⁻¹) 1 (rowTuple I.e S.y)

variable {I}

theorem tmGL_res_H {r h : Perm I.B} (hh : h ∈ tmGlRes I r) : h ∈ I.Hb := hh.1.1

/-- A quotient of residual elements lies in `D`. -/
theorem tmGL_res_D {r h τ : Perm I.B} (hh : h ∈ tmGlRes I r) (hτ : τ ∈ tmGlRes I r) :
    h * τ⁻¹ ∈ Aut I.Hb (types I.Nb (rowTuple I.e S.x)) := by
  refine mem_aut.mpr ⟨I.Hb.mul_mem hh.1.1 (I.Hb.inv_mem hτ.1.1), ?_⟩
  rw [← act_act, hh.1.2, act_eq_iff, inv_inv, hτ.1.2]

/-- The aligned target has the type multiset of `x`. -/
theorem tmGL_align_types {r τ : Perm I.B} (hτ : τ ∈ tmGlRes I r) :
    types I.Nb (tmGLAlign I τ) = types I.Nb (rowTuple I.e S.x) := by
  have hc := tmGL_cls_inv I.normalizes hτ.1.1 (I.lift_mem hτ.1.1)
  rw [tmGLAlign, tmGL_types_d' I.normalizes (I.Hb.inv_mem hτ.1.1) hc, ← hτ.1.2, act_act,
    mul_inv_cancel, act_one]

/-- The label condition of `tmGlLab` as a `J`-isomorphism of strings. -/
theorem tmGL_lab_J {r h : Perm I.B} :
    h ∈ tmGlLab I r ↔ h ∈ tmGlRes I r ∧ ∃ μ π, InJ I.Nb I.φ μ π ∧
      rowAct μ π (rowAct (rowLift I.e I.i0 h) 1 (rowTuple I.e S.x)) = rowTuple I.e S.y := by
  have hcos : ∀ i j (g : Perm I.B), g ∈ (I.cosetCall (i, j)).answer ↔
      g ∈ I.Hb ∧ rowTuple I.e S.x i ∘ g = rowTuple I.e S.y j := by
    intro i j g
    simp only [RowTerminal.cosetCall, rowState_answer, Set.mem_setOf_eq]
    rfl
  simp only [tmGlLab, Set.mem_setOf_eq]
  refine and_congr_right fun hres => ?_
  refine exists_congr fun μ => exists_congr fun π => and_congr_right fun hJ => ?_
  rw [rowAct_eq_iff]
  refine forall_congr' fun i => ?_
  rw [hcos]
  simp only [rowAct, Perm.one_symm, Perm.one_apply, act_act]
  exact and_iff_right (I.Hb.mul_mem (I.lift_mem_H hres.1.1 i) (I.Nb_le (hJ.1 i)))

/-- **The label coset through the affine action.** For `τ` in the residual set, `h` lies in the
label coset exactly when it is a residual element and `F_{h τ⁻¹}` carries the label point of
`x` to the label point of the aligned target `y'`. -/
theorem tmGL_lab_affine {rep : Set (I.B → C) → (I.B → C)}
    (hrep : TmGLRep I.Nb (rowTuple I.e S.x) rep) {r τ : Perm I.B} (hτ : τ ∈ tmGlRes I r)
    (h : Perm I.B) :
    h ∈ tmGlLab I r ↔ h ∈ tmGlRes I r ∧
      tmGLF I.normalizes (tmGL_kerI I) rep (rowLift I.e I.i0) (h * τ⁻¹)
          (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (rowTuple I.e S.x)) =
        tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ) := by
  rw [tmGL_lab_J]
  refine and_congr_right fun hres => ?_
  have hn := I.normalizes
  have hker := tmGL_kerI I
  have hk := tmGL_liftI I
  set k := rowLift I.e I.i0
  set x := rowTuple I.e S.x
  set g := h * τ⁻¹
  have hD : g ∈ Aut I.Hb (types I.Nb x) := tmGL_res_D hres hτ
  have hτH : τ ∈ I.Hb := hτ.1.1
  have hc := tmGL_cls_inv hn hτH (I.lift_mem hτH)
  -- move both strings by `k(τ)⁻¹`
  rw [← tmGL_J_transport_iff hn hker (I.Hb.inv_mem hτH) hc, ← rowAct_mul]
  change (∃ μ π, InJ I.Nb I.φ μ π ∧ rowAct μ π (rowAct (fun i => k h i * (k τ i)⁻¹) 1 x) =
    tmGLAlign I τ) ↔ _
  -- the moved string has class `g`
  have hd : ∀ i, g⁻¹ * (k h i * (k τ i)⁻¹) ∈ I.Nb := by
    intro i
    have e : g⁻¹ * (k h i * (k τ i)⁻¹) =
        (τ * (h⁻¹ * k h i) * τ⁻¹) * (τ⁻¹⁻¹ * (k τ i)⁻¹) := by
      simp only [g]; group
    rw [e]
    exact I.Nb.mul_mem (hn τ hτH _ (I.lift_mem hres.1.1 i)) (hc i)
  have hw := tmGL_types_d hn hD hd (rfl : types I.Nb x = types I.Nb x)
  rw [tmGL_J_iff hrep hw (tmGL_align_types hτ)]
  -- its label point is `F_g` of that of `x`
  have hpt : tmGLPt I.Nb I.φ x rep (rowAct (fun i => k h i * (k τ i)⁻¹) 1 x) =
      tmGLF hn hker rep k g (tmGLPt I.Nb I.φ x rep x) := by
    refine Prod.ext ?_ (tmGL_equivariant_or (hn := hn) hD hd rfl)
    show tmGLLab I.Nb I.φ x rep _ = tmGLκ hn hker g (tmGLLab I.Nb I.φ x rep x) *
      tmGLu I.Nb I.φ x rep k g
    rw [tmGL_equivariant (hn := hn) hker hrep hD (tmGLtch_spec hn hrep hD) hd rfl, mul_assoc]
    congr 1
    -- the tuple is `k(g) ν` with `ν = k(τ) μ₀ k(τ)⁻¹` zero-sum
    have hμ0 := hk.mul g hD.1 τ hτH
    have hν := tmGL_conj_zero hn hker (I.Hb.inv_mem hτH) hc hμ0 1
    have hgτ : g * τ = h := by simp [g]
    have e : ∀ i, k h i * (k τ i)⁻¹ = k g i * ((fun i => (k τ i)⁻¹) i)⁻¹ *
        ((k g i * k τ i)⁻¹ * k (g * τ) i) * (fun i => (k τ i)⁻¹) ((1 : Perm (Fin L.q)) i) := by
      intro i
      simp only [Perm.one_apply, inv_inv, hgτ]
      group
    have := tmGLu_indep (hn := hn) (hker := hker) hk hrep hD (tmGLtch_spec hn hrep hD) hν
    rw [← this]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [e i]
    simp only [mul_assoc, Perm.one_apply]
    rfl
  have hpt' : tmGLPt I.Nb I.φ x rep (rowAct (fun i => k h i * (k τ i)⁻¹) 1 x) =
      (tmGLLab I.Nb I.φ x rep (rowAct (fun i => k h i * (k τ i)⁻¹) 1 x),
        tmGLOr I.Nb x (rowAct (fun i => k h i * (k τ i)⁻¹) 1 x)) := rfl
  rw [← hpt, hpt', tmGLPt, Prod.mk.injEq]

/-- **The residual set is `D' τ`** with `D' = D ⊓ R`: `R = tmRad I` is the radical preimage. -/
theorem tmGL_res_iff {r τ : Perm I.B} (hτ : τ ∈ tmGlRes I r) (h : Perm I.B) :
    h ∈ tmGlRes I r ↔ h * τ⁻¹ ∈ Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I := by
  constructor
  · intro hh
    refine ⟨tmGL_res_D hh hτ, ?_⟩
    obtain ⟨-, a, ha, rfl⟩ := hh
    obtain ⟨-, b, hb, rfl⟩ := hτ
    rw [show a * r * (b * r)⁻¹ = a * b⁻¹ by group]
    exact (tmRad I).mul_mem ha ((tmRad I).inv_mem hb)
  · rintro ⟨hD, hR⟩
    obtain ⟨⟨hτH, hτT⟩, b, hb, rfl⟩ := hτ
    have hh : h = (h * (b * r)⁻¹) * (b * r) := by group
    refine ⟨⟨?_, ?_⟩, h * (b * r)⁻¹ * b, (tmRad I).mul_mem hR hb, by group⟩
    · rw [hh]; exact I.Hb.mul_mem hD.1 hτH
    · rw [hh, ← act_act, hD.2, hτT]

/-- **The label coset from the affine transporter in a supplement.** Let `D' = D ⊓ R`, let
`Σ ≤ D'` with `Σ ⊔ N = D'` (Lemma `lem:solvable-supplement`), and let the transporter of label
points in `Σ` be `t L`. Then the label coset is `t τ · τ⁻¹ (L ⊔ N) τ` ("Adjoining `N` lifts the
resulting label stabilizer and transporter back to `D`"). -/
theorem tmGL_lab_out {rep : Set (I.B → C) → (I.B → C)}
    (hrep : TmGLRep I.Nb (rowTuple I.e S.x) rep) {r τ : Perm I.B} (hτ : τ ∈ tmGlRes I r)
    {Sg : Subgroup (Perm I.B)}
    (hSN : Sg ⊔ I.Nb = Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I)
    {t : Perm I.B} {Lg : Subgroup (Perm I.B)}
    (hT : {s | s ∈ Sg ∧ tmGLF I.normalizes (tmGL_kerI I) rep (rowLift I.e I.i0) s
        (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (rowTuple I.e S.x)) =
        tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ)} = t • (Lg : Set (Perm I.B))) :
    tmGlLab I r = (t * τ) • (((Lg ⊔ I.Nb).map (MulAut.conj τ⁻¹).toMonoidHom :
      Subgroup (Perm I.B)) : Set (Perm I.B)) := by
  set D' := Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I
  have hn := I.normalizes
  have hNH := I.Nb_le
  have hSD : Sg ≤ D' := hSN ▸ le_sup_left
  have hND : I.Nb ≤ D' := hSN ▸ le_sup_right
  have hD'D : D' ≤ Aut I.Hb (types I.Nb (rowTuple I.e S.x)) := inf_le_left
  have hSH : Sg ≤ I.Hb := fun s hs => (hD'D (hSD hs)).1
  -- `Σ ⊔ N = Σ N`
  have hcov : ∀ g ∈ D', ∃ s ∈ Sg, ∃ n ∈ I.Nb, g = s * n := by
    intro g hg
    rw [← hSN, Subgroup.sup_eq_closure] at hg
    refine closure_mem_mul (hn.mono hSH) (fun γ hγ => ?_) g hg
    rcases hγ with hγ | hγ
    · exact ⟨γ, hγ, 1, I.Nb.one_mem, by simp⟩
    · exact ⟨1, Sg.one_mem, γ, hγ, by simp⟩
  have htr := tmGL_trans_supp (hn := hn) (hker := tmGL_kerI I) hNH (tmGL_liftI I) hrep hD'D hND
    hSD hcov (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (rowTuple I.e S.x))
    (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ))
  -- `t` lies in the transporter, so `L ≤ Σ`
  have htT : t ∈ {s | s ∈ Sg ∧ tmGLF I.normalizes (tmGL_kerI I) rep (rowLift I.e I.i0) s
        (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (rowTuple I.e S.x)) =
        tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ)} := by
    rw [hT]; exact ⟨1, Lg.one_mem, mul_one t⟩
  have hLS : ∀ l ∈ Lg, l ∈ Sg := by
    intro l hl
    have : t * l ∈ Sg := by
      have h1 : t * l ∈ t • (Lg : Set (Perm I.B)) := ⟨l, hl, rfl⟩
      rw [← hT] at h1; exact h1.1
    simpa using Sg.mul_mem (Sg.inv_mem htT.1) this
  have hLN : ∀ g ∈ Lg ⊔ I.Nb, ∃ l ∈ Lg, ∃ n ∈ I.Nb, g = l * n := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    refine closure_mem_mul (hn.mono fun l hl => hSH (hLS l hl)) (fun γ hγ => ?_) g hg
    rcases hγ with hγ | hγ
    · exact ⟨γ, hγ, 1, I.Nb.one_mem, by simp⟩
    · exact ⟨1, Lg.one_mem, γ, hγ, by simp⟩
  ext h
  rw [tmGL_lab_affine hrep hτ, tmGL_res_iff hτ]
  have hstep : (h * τ⁻¹ ∈ D' ∧ tmGLF I.normalizes (tmGL_kerI I) rep (rowLift I.e I.i0)
      (h * τ⁻¹) (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (rowTuple I.e S.x)) =
      tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ)) ↔
      h * τ⁻¹ ∈ {g | ∃ s ∈ Sg, tmGLF I.normalizes (tmGL_kerI I) rep (rowLift I.e I.i0) s
        (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (rowTuple I.e S.x)) =
        tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ) ∧ ∃ n ∈ I.Nb, g = s * n} := by
    rw [← htr]; rfl
  rw [hstep]
  simp only [Set.mem_setOf_eq, Set.mem_smul_set, SetLike.mem_coe, smul_eq_mul,
    Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨s, hs, hsF, n, hnN, hsn⟩
    have : s ∈ t • (Lg : Set (Perm I.B)) := by rw [← hT]; exact ⟨hs, hsF⟩
    obtain ⟨l, hl, rfl⟩ := this
    have hsn' : h * τ⁻¹ = t * l * n := by simpa [smul_eq_mul] using hsn
    refine ⟨τ⁻¹ * (l * n) * τ, ⟨l * n, Subgroup.mul_mem_sup hl hnN, rfl⟩, ?_⟩
    calc t * τ * (τ⁻¹ * (l * n) * τ) = t * l * n * τ := by group
      _ = h * τ⁻¹ * τ := by rw [hsn']
      _ = h := by group
  · rintro ⟨_, ⟨g, hg, rfl⟩, he⟩
    obtain ⟨l, hl, n, hnN, rfl⟩ := hLN g hg
    have hlT : t * l ∈ {s | s ∈ Sg ∧ tmGLF I.normalizes (tmGL_kerI I) rep (rowLift I.e I.i0) s
        (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (rowTuple I.e S.x)) =
        tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ)} := by
      rw [hT]; exact ⟨l, hl, rfl⟩
    refine ⟨t * l, hlT.1, hlT.2, n, hnN, ?_⟩
    rw [← he]
    group

/-- **No transporter in the supplement: the label coset is empty.** -/
theorem tmGL_lab_out_empty {rep : Set (I.B → C) → (I.B → C)}
    (hrep : TmGLRep I.Nb (rowTuple I.e S.x) rep) {r τ : Perm I.B} (hτ : τ ∈ tmGlRes I r)
    {Sg : Subgroup (Perm I.B)}
    (hSN : Sg ⊔ I.Nb = Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I)
    (hT : {s | s ∈ Sg ∧ tmGLF I.normalizes (tmGL_kerI I) rep (rowLift I.e I.i0) s
        (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (rowTuple I.e S.x)) =
        tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ)} = ∅) :
    tmGlLab I r = ∅ := by
  set D' := Aut I.Hb (types I.Nb (rowTuple I.e S.x)) ⊓ tmRad I
  have hn := I.normalizes
  have hSD : Sg ≤ D' := hSN ▸ le_sup_left
  have hND : I.Nb ≤ D' := hSN ▸ le_sup_right
  have hD'D : D' ≤ Aut I.Hb (types I.Nb (rowTuple I.e S.x)) := inf_le_left
  have hSH : Sg ≤ I.Hb := fun s hs => (hD'D (hSD hs)).1
  have hcov : ∀ g ∈ D', ∃ s ∈ Sg, ∃ n ∈ I.Nb, g = s * n := by
    intro g hg
    rw [← hSN, Subgroup.sup_eq_closure] at hg
    refine closure_mem_mul (hn.mono hSH) (fun γ hγ => ?_) g hg
    rcases hγ with hγ | hγ
    · exact ⟨γ, hγ, 1, I.Nb.one_mem, by simp⟩
    · exact ⟨1, Sg.one_mem, γ, hγ, by simp⟩
  have htr := tmGL_trans_supp (hn := hn) (hker := tmGL_kerI I) I.Nb_le (tmGL_liftI I) hrep hD'D
    hND hSD hcov (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (rowTuple I.e S.x))
    (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ))
  ext h
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [tmGL_lab_affine hrep hτ, tmGL_res_iff hτ]
  intro hh
  have : h * τ⁻¹ ∈ {g | g ∈ D' ∧ tmGLF I.normalizes (tmGL_kerI I) rep (rowLift I.e I.i0) g
      (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (rowTuple I.e S.x)) =
      tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ)} := hh
  rw [htr] at this
  obtain ⟨s, hs, hsF, -⟩ := this
  have : s ∈ (∅ : Set (Perm I.B)) := by rw [← hT]; exact ⟨hs, hsF⟩
  exact this

end RT

end GI.Impl
