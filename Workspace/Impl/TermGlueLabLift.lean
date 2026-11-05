module

public import Workspace.Impl.TermGlueLabAct

@[expose] public section

/-!
# The affine action through the lifts: an action of `D/N`

Proof of Theorem A.23: "Different lifts differ by `𝓜` and have the same action
on this torsor. Likewise `h ∈ N` acts trivially: its lift lies in `𝓜`. Thus the affine action
factors through `D/N`."

The lifts `k : P → (Fin q → P)` satisfy `TmGLLift`: `k(h)` has class `h`, `k(g) k(h)` and
`k(gh)` differ by a zero-sum `N`-tuple, and `k(n)` is a zero-sum `N`-tuple for `n ∈ N` (the
augmentation condition for `𝓜`). In the terminal these come from Theorem A.18
(`tmGL_blockwise`).

* `tmGLu k h`: the offset `Π_i [t_{a_i}(h)] · Π_i [d_i(h)]` with `k_i(h) = h d_i(h)`.
* `tmGLF k h`: the affine map `(s, o) ↦ (κ_h(s) · u(h), o ε(h))` on `A/B(x) × C₂`.
* `tmGL_F_lab`: `F_h` sends the label point of `z` to that of `z^{k(h)}`.
* `tmGLu_indep`: the offset does not depend on the choices of `t` and of the lift.
* `tmGL_F_mul`: `F_{gh} = F_h ∘ F_g` (a right action). `tmGL_F_N`: `F_n = id` for `n ∈ N`, so
  `F` factors through `D/N` (`tmGL_F_mulN`).
* `tmGL_J_transport`: a tuple of class `h ∈ H` carries `J`-isomorphic strings to `J`-isomorphic
  strings (`J` is normal in `G`).
-/

namespace GI.Impl

open GI.Multicoset Equiv Equiv.Perm

section Lift

variable {P : Type*} [Group P] {Ω : Type} [RAct P Ω] {q : ℕ}
variable {N H : Subgroup P} {A : Type*} [CommGroup A] {φ : N →* A} {x : Fin q → Ω}

/-- A zero-sum `N`-tuple. -/
def TmGLZero (N : Subgroup P) (φ : N →* A) (μ : Fin q → P) : Prop :=
  (∀ i, μ i ∈ N) ∧ ∏ i, phiT N φ (μ i) = 1

variable (N H φ) in
/-- **The lifts of Theorem A.18**: `k(h)` has class `h`; lifts multiply up to `𝓜`; lifts of
elements of `N` lie in `𝓜`. -/
structure TmGLLift (k : P → Fin q → P) : Prop where
  cls : ∀ h ∈ H, ∀ i, h⁻¹ * k h i ∈ N
  mul : ∀ g ∈ H, ∀ h ∈ H, TmGLZero N φ fun i => (k g i * k h i)⁻¹ * k (g * h) i
  kN : ∀ n ∈ N, TmGLZero N φ (k n)

/-- **Conjugating a zero-sum tuple by a tuple of class `h` keeps it zero-sum**, for any matching
`π`: `ker φ` is normalized by `H`. -/
theorem tmGL_conj_zero (hn : Normalizes H N) (hker : TmGLKer N H φ) {h : P} (hh : h ∈ H)
    {e : Fin q → P} (he : ∀ i, h⁻¹ * e i ∈ N) {μ : Fin q → P} (hμ : TmGLZero N φ μ)
    (π : Perm (Fin q)) : TmGLZero N φ fun i => (e i)⁻¹ * μ i * e (π i) := by
  set n : Fin q → P := fun a => h⁻¹ * e a
  have hen : ∀ a, e a = h * n a := fun a => by simp [n]
  have hc : ∀ i, (e i)⁻¹ * μ i * e (π i) = (n i)⁻¹ * (h⁻¹ * μ i * h) * n (π i) := fun i => by
    rw [hen, hen]; group
  have hμh : ∀ i, h⁻¹ * μ i * h ∈ N := fun i => hn.inv hh (hμ.1 i)
  refine ⟨fun i => by show (e i)⁻¹ * μ i * e (π i) ∈ N; rw [hc]; exact N.mul_mem (N.mul_mem (N.inv_mem (he i)) (hμh i)) (he _), ?_⟩
  simp_rw [hc]
  rw [Finset.prod_congr rfl fun i _ => phiT_mul (N.mul_mem (N.inv_mem (he i)) (hμh i)) (he _),
    Finset.prod_mul_distrib, Finset.prod_congr rfl fun i _ =>
      phiT_mul (N.inv_mem (he i)) (hμh i), Finset.prod_mul_distrib,
    Equiv.prod_comp π (fun i => phiT N φ (n i)),
    Finset.prod_congr rfl fun i _ => phiT_inv (he i), Finset.prod_inv_distrib]
  -- the conjugate of the product of `μ` lies in the kernel
  obtain ⟨hM, hMφ⟩ := tmGL_phiT_ofFn (φ := φ) hμ.1
  have hk := hker h hh _ hM (by rw [hMφ, hμ.2])
  have hconj : h⁻¹ * (List.ofFn μ).prod * h = (List.ofFn fun i => h⁻¹ * μ i * h).prod := by
    have := map_list_prod (MulAut.conj h⁻¹).toMonoidHom (List.ofFn μ)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, List.map_ofFn] at this
    rw [this]
    congr 2
    funext i
    simp
  obtain ⟨-, hφ'⟩ := tmGL_phiT_ofFn (φ := φ) hμh
  rw [hconj, hφ'] at hk
  rw [hk, mul_one, inv_mul_cancel]

/-- **`J` is normal in `G`**: a tuple `e` of class `h ∈ H` carries `J`-isomorphic strings to
`J`-isomorphic strings. -/
theorem tmGL_J_transport (hn : Normalizes H N) (hker : TmGLKer N H φ) {h : P} (hh : h ∈ H)
    {e : Fin q → P} (he : ∀ i, h⁻¹ * e i ∈ N) {u v : Fin q → Ω}
    (huv : ∃ μ π, InJ N φ μ π ∧ rowAct μ π u = v) :
    ∃ μ π, InJ N φ μ π ∧ rowAct μ π (rowAct e 1 u) = rowAct e 1 v := by
  obtain ⟨μ, π, ⟨hμN, hμ1, hπ⟩, huv⟩ := huv
  have hz := tmGL_conj_zero hn hker hh he ⟨hμN, hμ1⟩ π
  refine ⟨_, π, ⟨hz.1, hz.2, hπ⟩, rowAct_eq_iff.mpr fun i => ?_⟩
  simp only [rowAct, Perm.one_symm, Perm.one_apply]
  rw [act_act, show e i * ((e i)⁻¹ * μ i * e (π i)) = μ i * e (π i) by group, ← act_act,
    rowAct_eq_iff.mp huv i]

/-- Undoing a tuple: `(z^e)^{e⁻¹} = z`. -/
theorem tmGL_rowAct_inv (e : Fin q → P) (z : Fin q → Ω) :
    rowAct (fun i => (e i)⁻¹) 1 (rowAct e 1 z) = z := by
  funext i
  simp [rowAct, Perm.one_symm]

/-- The inverse tuple has class `h⁻¹`. -/
theorem tmGL_cls_inv (hn : Normalizes H N) {h : P} (hh : h ∈ H) {e : Fin q → P}
    (he : ∀ i, h⁻¹ * e i ∈ N) (i : Fin q) : h⁻¹⁻¹ * (e i)⁻¹ ∈ N := by
  have := hn h hh _ (N.inv_mem (he i))
  simpa [mul_assoc] using this

/-- **`J`-isomorphism is invariant under a tuple of class `h ∈ H`.** -/
theorem tmGL_J_transport_iff (hn : Normalizes H N) (hker : TmGLKer N H φ) {h : P} (hh : h ∈ H)
    {e : Fin q → P} (he : ∀ i, h⁻¹ * e i ∈ N) {u v : Fin q → Ω} :
    (∃ μ π, InJ N φ μ π ∧ rowAct μ π (rowAct e 1 u) = rowAct e 1 v) ↔
      ∃ μ π, InJ N φ μ π ∧ rowAct μ π u = v := by
  refine ⟨fun h' => ?_, tmGL_J_transport hn hker hh he⟩
  have := tmGL_J_transport hn hker (H.inv_mem hh) (tmGL_cls_inv hn hh he) h'
  rwa [tmGL_rowAct_inv, tmGL_rowAct_inv] at this

/-- A zero-sum tuple keeps the label and the orientation. -/
theorem tmGL_lab_zero {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) {z : Fin q → Ω}
    (hz : types N z = types N x) {μ : Fin q → P} (hμ : TmGLZero N φ μ) :
    tmGLLab N φ x rep (rowAct μ 1 z) = tmGLLab N φ x rep z ∧
      tmGLOr N x (rowAct μ 1 z) = tmGLOr N x z := by
  have hz' : types N (rowAct μ 1 z) = types N x := by rw [types_rowAct_J hμ.1, hz]
  have := (tmGL_J_iff hrep hz hz').mp ⟨μ, 1, ⟨hμ.1, hμ.2, Subgroup.one_mem _⟩, rfl⟩
  exact ⟨this.1.symm, this.2.symm⟩

/-! ### The official choices and the affine map -/

variable (N φ x)

open Classical in
/-- The chosen transporters `t_a(h)` between representatives. -/
noncomputable def tmGLtch (rep : Set Ω → Ω) (h : P) : Set Ω → P :=
  if ht : ∃ t, TmGLT N x rep h t then ht.choose else fun _ => 1

/-- **The offset** `u(h) = Π_i [t_{a_i}(h)] · Π_i [h⁻¹ k_i(h)]`. -/
noncomputable def tmGLu (rep : Set Ω → Ω) (k : P → Fin q → P) (h : P) : tmGLV N φ x :=
  (∏ i, tmGLc N φ x (tmGLtch N x rep h (orbitN N (x i)))) * ∏ i, tmGLc N φ x (h⁻¹ * k h i)

variable {N φ x}

variable (hn : Normalizes H N) (hker : TmGLKer N H φ)

/-- **The affine map of `h`** on `A/B(x) × C₂`: `(s, o) ↦ (κ_h(s) · u(h), o · ε(h))`. -/
noncomputable def tmGLF (rep : Set Ω → Ω) (k : P → Fin q → P) (h : P)
    (p : tmGLV N φ x × ℤˣ) : tmGLV N φ x × ℤˣ :=
  (tmGLκ hn hker h p.1 * tmGLu N φ x rep k h, p.2 * tmGLε N x h)

variable {hn hker}

theorem tmGLtch_spec (hn : Normalizes H N) {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) {h : P}
    (hD : h ∈ Aut H (types N x)) : TmGLT N x rep h (tmGLtch N x rep h) := by
  have ht := tmGLT_exists hrep hD hn
  simp only [tmGLtch, dif_pos ht]
  exact ht.choose_spec

/-- The label point `(s(z), o(z))`. -/
noncomputable def tmGLPt (N : Subgroup P) (φ : N →* A) (x : Fin q → Ω) (rep : Set Ω → Ω)
    (z : Fin q → Ω) : tmGLV N φ x × ℤˣ :=
  (tmGLLab N φ x rep z, tmGLOr N x z)

/-- **`F_h` moves label points along the lift `k(h)`.** -/
theorem tmGL_F_lab {k : P → Fin q → P} (hk : TmGLLift N H φ k) {rep : Set Ω → Ω}
    (hrep : TmGLRep N x rep) {h : P} (hD : h ∈ Aut H (types N x)) {z : Fin q → Ω}
    (hz : types N z = types N x) :
    tmGLPt N φ x rep (rowAct (k h) 1 z) = tmGLF hn hker rep k h (tmGLPt N φ x rep z) := by
  refine Prod.ext ?_ (tmGL_equivariant_or (hn := hn) hD (hk.cls h hD.1) hz)
  show tmGLLab N φ x rep (rowAct (k h) 1 z) =
    tmGLκ hn hker h (tmGLLab N φ x rep z) * tmGLu N φ x rep k h
  rw [tmGL_equivariant (hn := hn) hker hrep hD (tmGLtch_spec hn hrep hD) (hk.cls h hD.1) hz, tmGLu,
    mul_assoc]

include hn hker in
/-- **The offset does not depend on the choices**: any valid transporters `t` and any tuple
`k(h) ν` with `ν` zero-sum give `u(h)`. -/
theorem tmGLu_indep {k : P → Fin q → P} (hk : TmGLLift N H φ k) {rep : Set Ω → Ω}
    (hrep : TmGLRep N x rep) {h : P} (hD : h ∈ Aut H (types N x)) {t : Set Ω → P}
    (ht : TmGLT N x rep h t) {ν : Fin q → P} (hν : TmGLZero N φ ν) :
    (∏ i, tmGLc N φ x (t (orbitN N (x i)))) * ∏ i, tmGLc N φ x (h⁻¹ * (k h i * ν i)) =
      tmGLu N φ x rep k h := by
  have hd : ∀ i, h⁻¹ * (k h i * ν i) ∈ N := fun i => by
    rw [← mul_assoc]; exact N.mul_mem (hk.cls h hD.1 i) (hν.1 i)
  have e1 := tmGL_equivariant (hn := hn) hker hrep hD ht hd (rfl : types N x = types N x)
  have e2 := tmGL_equivariant (hn := hn) hker hrep hD (tmGLtch_spec hn hrep hD) (hk.cls h hD.1)
    (rfl : types N x = types N x)
  have hrw : rowAct (fun i => k h i * ν i) 1 x = rowAct ν 1 (rowAct (k h) 1 x) :=
    rowAct_mul (k h) ν 1 x
  rw [hrw, (tmGL_lab_zero hrep (tmGL_types_d hn hD (hk.cls h hD.1) rfl) hν).1, e2,
    mul_assoc, mul_assoc] at e1
  exact (mul_left_cancel e1).symm

/-- `N` lies in `D`. -/
theorem tmGL_N_D (hNH : N ≤ H) {n : P} (hnN : n ∈ N) : n ∈ Aut H (types N x) :=
  mem_aut.mpr ⟨hNH hnN, (fixes_types N x).act_eq hnN⟩

/-- **`N` acts trivially** ("Likewise `h ∈ N` acts trivially: its lift lies in `𝓜`"). -/
theorem tmGL_F_N (hNH : N ≤ H) {k : P → Fin q → P} (hk : TmGLLift N H φ k) {rep : Set Ω → Ω}
    (hrep : TmGLRep N x rep) {n : P} (hnN : n ∈ N) (p : tmGLV N φ x × ℤˣ) :
    tmGLF hn hker rep k n p = p := by
  have hD := tmGL_N_D (x := x) hNH hnN
  have e := tmGL_F_lab (hn := hn) (hker := hker) hk hrep hD (rfl : types N x = types N x)
  have hz := tmGL_lab_zero hrep (rfl : types N x = types N x) (hk.kN n hnN)
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  simp only [tmGLPt, tmGLF, hz.1, hz.2, tmGLκ_N hker hnN hD] at e1 e2
  have hu : tmGLu N φ x rep k n = 1 := (mul_eq_left.mp e1.symm)
  have hε : tmGLε N x n = 1 := (mul_eq_left.mp e2.symm)
  simp only [tmGLF, tmGLκ_N hker hnN hD, hu, hε, mul_one]

/-- **`F` is a right action of `D`**: `F_{gh} = F_h ∘ F_g`. The cocycle identity for the offsets
and the multiplicativity of `ε` come from comparing the label points of `x^{k(gh)}` and
`(x^{k(g)})^{k(h)}`, which differ by a zero-sum tuple. -/
theorem tmGL_F_mul {k : P → Fin q → P} (hk : TmGLLift N H φ k) {rep : Set Ω → Ω}
    (hrep : TmGLRep N x rep) {g h : P} (hg : g ∈ Aut H (types N x))
    (hh : h ∈ Aut H (types N x)) (p : tmGLV N φ x × ℤˣ) :
    tmGLF hn hker rep k (g * h) p = tmGLF hn hker rep k h (tmGLF hn hker rep k g p) := by
  have hgh := (Aut H (types N x)).mul_mem hg hh
  have hx1 := tmGL_types_d hn hg (hk.cls g hg.1) (rfl : types N x = types N x)
  have hx2 := tmGL_types_d hn hh (hk.cls h hh.1) hx1
  have hμ := hk.mul g hg.1 h hh.1
  have hsplit : rowAct (k (g * h)) 1 x =
      rowAct (fun i => (k g i * k h i)⁻¹ * k (g * h) i) 1 (rowAct (k h) 1 (rowAct (k g) 1 x)) := by
    rw [← rowAct_mul (k g) (k h) 1 x, ← rowAct_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply]
    group
  have e := tmGL_F_lab (hn := hn) (hker := hker) hk hrep hgh (rfl : types N x = types N x)
  rw [hsplit] at e
  have hz := tmGL_lab_zero hrep hx2 hμ
  have e2 := tmGL_F_lab (hn := hn) (hker := hker) hk hrep hh hx1
  have e1 := tmGL_F_lab (hn := hn) (hker := hker) hk hrep hg (rfl : types N x = types N x)
  have hpt : tmGLPt N φ x rep (rowAct (fun i => (k g i * k h i)⁻¹ * k (g * h) i) 1
      (rowAct (k h) 1 (rowAct (k g) 1 x))) = tmGLPt N φ x rep (rowAct (k h) 1 (rowAct (k g) 1 x)) :=
    Prod.ext hz.1 hz.2
  rw [hpt, e2, e1] at e
  -- compare the two coordinates
  have c1 := congrArg Prod.fst e
  have c2 := congrArg Prod.snd e
  simp only [tmGLF, tmGLPt, map_mul, tmGLκ_mul hker hg hh] at c1 c2
  have hu : tmGLu N φ x rep k (g * h) = tmGLκ hn hker h (tmGLu N φ x rep k g) *
      tmGLu N φ x rep k h := by
    rw [mul_assoc] at c1
    exact (mul_left_cancel c1).symm
  have hε : tmGLε N x (g * h) = tmGLε N x g * tmGLε N x h := by
    rw [mul_assoc] at c2
    exact (mul_left_cancel c2).symm
  simp only [tmGLF, map_mul, tmGLκ_mul hker hg hh, hu, hε, mul_assoc]

/-- **The action factors through `D/N`.** -/
theorem tmGL_F_mulN (hNH : N ≤ H) {k : P → Fin q → P} (hk : TmGLLift N H φ k) {rep : Set Ω → Ω}
    (hrep : TmGLRep N x rep) {g n : P} (hg : g ∈ Aut H (types N x)) (hnN : n ∈ N)
    (p : tmGLV N φ x × ℤˣ) : tmGLF hn hker rep k (g * n) p = tmGLF hn hker rep k g p := by
  rw [tmGL_F_mul hk hrep hg (tmGL_N_D hNH hnN), tmGL_F_N hNH hk hrep hnN]

/-- **Restricting to a supplement loses no orbit.** Let `D' ≤ D` contain `N`, and let `Σ ≤ D'`
with `D' = Σ N`. The transporter of label points in `D'` is the transporter in `Σ`, times `N`. -/
theorem tmGL_trans_supp (hNH : N ≤ H) {k : P → Fin q → P} (hk : TmGLLift N H φ k)
    {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) {D' Sg : Subgroup P}
    (hD' : D' ≤ Aut H (types N x)) (hND : N ≤ D') (hSD : Sg ≤ D')
    (hcov : ∀ g ∈ D', ∃ s ∈ Sg, ∃ n ∈ N, g = s * n) (p p' : tmGLV N φ x × ℤˣ) :
    {g | g ∈ D' ∧ tmGLF hn hker rep k g p = p'} =
      {g | ∃ s ∈ Sg, tmGLF hn hker rep k s p = p' ∧ ∃ n ∈ N, g = s * n} := by
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hg, he⟩
    obtain ⟨s, hs, n, hnN, rfl⟩ := hcov g hg
    refine ⟨s, hs, ?_, n, hnN, rfl⟩
    rw [← tmGL_F_mulN hNH hk hrep (hD' (hSD hs)) hnN]
    exact he
  · rintro ⟨s, hs, he, n, hnN, rfl⟩
    exact ⟨D'.mul_mem (hSD hs) (hND hnN), by rw [tmGL_F_mulN hNH hk hrep (hD' (hSD hs)) hnN, he]⟩

/-- **The cocycle identity** `u(gh) = κ_h(u(g)) · u(h)` and the multiplicativity of `ε`. -/
theorem tmGLu_mul {k : P → Fin q → P} (hk : TmGLLift N H φ k) {rep : Set Ω → Ω}
    (hrep : TmGLRep N x rep) {g h : P} (hg : g ∈ Aut H (types N x))
    (hh : h ∈ Aut H (types N x)) :
    tmGLu N φ x rep k (g * h) = tmGLκ hn hker h (tmGLu N φ x rep k g) * tmGLu N φ x rep k h ∧
      tmGLε N x (g * h) = tmGLε N x g * tmGLε N x h := by
  have e := tmGL_F_mul (hn := hn) (hker := hker) hk hrep hg hh (1, 1)
  simp only [tmGLF, map_one, one_mul, Prod.mk.injEq] at e
  exact e

/-- `F_1` is the identity. -/
theorem tmGL_F_one (hNH : N ≤ H) {k : P → Fin q → P} (hk : TmGLLift N H φ k) {rep : Set Ω → Ω}
    (hrep : TmGLRep N x rep) (p : tmGLV N φ x × ℤˣ) : tmGLF hn hker rep k 1 p = p :=
  tmGL_F_N hNH hk hrep N.one_mem p

end Lift

end GI.Impl
