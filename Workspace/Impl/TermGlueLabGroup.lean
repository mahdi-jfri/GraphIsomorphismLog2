module

public import Workspace.Impl.TermGlueLabYoung

@[expose] public section

/-!
# The groups of the label step of Theorem A.23

For a row terminal `I`, the domain group `G|_dom` acts on `B × [q]` through the
coordinates `I.e`. This file identifies the groups of the label step with sets of pairs, and
proves the facts about `tmGlLab` that the algorithm uses.

* `tmGLG I`: `G|_dom` on `B × [q]`. `tmGLG_mem_iff`: its elements are the pairs of `G = K R₀`
  (`InG`), by `actsAs_inG` and `tm_inG_mem` (Theorems A.17 and A.18).
* `tmGL_blockwise`: a blockwise element of `G|_dom` whose coordinate at `i0` lies in `N` has all
  coordinates in `N` and total label `1` (Theorem A.18; the paper: "Likewise `h ∈ N` acts
  trivially: its lift lies in `𝓜`"). `tmGL_lift_N`: lifts of `h` and `h'` with `h⁻¹ h' ∈ N`
  differ by a zero-sum tuple ("Different lifts differ by `𝓜`").
* `tmGLJ I = tmGLG I ⊓ tmGLW N` is the set of `J`-pairs (`tmGLJ_mem_iff`), and a pair with a
  class in `H` normalizes it (`tmGLJ_conj`): conjugating by `h ∈ H` keeps `N* = ker φ`.
* `tmGL_lab_iff`: `h ∈ tmGlLab I r` exactly when `h ∈ tmGlRes I r` and some element of `G|_dom`
  of class `h` carries `X` to `Y`.
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Paper Equiv Equiv.Perm

variable {Ω C : Type}

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

/-- **The domain group on `B × [q]`**, through the coordinates `I.e`. -/
def tmGLG : Subgroup (Perm (I.B × Fin L.q)) :=
  S.domGroup.comap (Equiv.permCongrHom I.e).toMonoidHom

theorem mem_tmGLG {σ : Perm (I.B × Fin L.q)} : σ ∈ tmGLG I ↔ I.e.permCongr σ ∈ S.domGroup :=
  Iff.rfl

/-- **The domain group consists of the pairs of `G = K R₀`.** -/
theorem tmGLG_mem_iff {σ : Perm (I.B × Fin L.q)} :
    σ ∈ tmGLG I ↔ ∃ p : (Fin L.q → Perm I.B) × Perm (Fin L.q),
      InG I.Hb I.Nb I.φ (rowLift I.e I.i0) p.1 p.2 ∧ tmGLP p = σ := by
  rw [mem_tmGLG]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨d, π, hG, hact⟩ := actsAs_inG I.e I.i0 I.pure I.three_le I.rnf I.complement I.φ
      I.φ_ker g.1 g.2
    refine ⟨(d, π), hG, ?_⟩
    ext1 a
    apply I.e.injective
    apply Subtype.ext
    have h1 := congrArg (fun τ : Perm S.dom => ((τ (I.e a) : S.dom) : Ω)) hg
    simp only [State.domHom_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply] at h1
    rw [← h1]
    obtain ⟨c, i⟩ := a
    rw [hact c i]
    rfl
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨τ, hτ, hτp⟩ := tm_inG_mem I hp
    convert hτ using 1
    ext1 v
    obtain ⟨⟨c, i⟩, rfl⟩ := I.e.surjective v
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, hτp]
    rfl

/-- **A blockwise element of `G|_dom` with coordinate at `i0` in `N` lies in `𝓜`**: all its
coordinates lie in `N` and its total label is `1` (Theorem A.18). -/
theorem tmGL_blockwise {y : Fin L.q → Perm I.B} (hy : cleanRowPerm I.e y ∈ S.domGroup)
    (h0 : y I.i0 ∈ I.Nb) : (∀ i, y i ∈ I.Nb) ∧ ∏ i, phiT I.Nb I.φ (y i) = 1 := by
  classical
  have hK : (⟨_, hy⟩ : S.domGroup) ∈ blockKernel I.e := ⟨y, rfl⟩
  -- its `θ` is trivial, so it lies in `M`
  obtain ⟨θ, hθ, hker⟩ := exists_theta I.e I.i0 I.pure I.three_le I.rnf
  have hθ1 : θ ⟨_, hy⟩ = 1 := by
    rw [hθ hy I.i0, QuotientGroup.eq_one_iff]
    obtain ⟨n, hn, hny⟩ := h0
    have : coordsIn I.e I.i0 I.pure I.three_le hy I.i0 = n := Subtype.ext hny.symm
    rw [this]; exact hn
  have hM : (⟨_, hy⟩ : S.domGroup) ∈ rowNormalM S.domGroup (blockKernel I.e) I.e I.i0 I.Nl := by
    have : (⟨⟨_, hy⟩, hK⟩ : blockKernel I.e) ∈ (θ.comp (blockKernel I.e).subtype).ker := hθ1
    rw [hker] at this
    exact this
  -- its coordinates lie in `N`
  obtain ⟨z, hz, hzμ⟩ := (Subgroup.mem_inf.1 hM).2
  have hzμ' : (fun r => (z r : Perm I.B)) = y := cleanRowPerm_injective I.e hzμ
  have hμN : ∀ i, y i ∈ I.Nb := fun i => ⟨z i, hz i, by rw [← hzμ']; rfl⟩
  refine ⟨hμN, ?_⟩
  -- the zero-sum clause: the total of the coordinates lies in `N*`
  obtain ⟨ψ, hψ, -, hrange⟩ := I.rnf.zero_sum
  have hψz := hψ ⟨_, hM⟩ z (by rw [hzμ]; rfl)
  have hzs : (fun r => ((z r : cleanLocalGroup S.domGroup I.e I.i0) :
      cleanLocalGroup S.domGroup I.e I.i0 ⧸ I.Nstar)) ∈ rowZeroSum I.Nl I.Nstar := by
    rw [← hrange, ← hψz]; exact ⟨_, rfl⟩
  have htot : ((Finset.univ.toList.map z).prod :
      cleanLocalGroup S.domGroup I.e I.i0 ⧸ I.Nstar) = 1 := by
    rw [← hzs.2]
    change QuotientGroup.mk' I.Nstar (Finset.univ.toList.map z).prod = _
    rw [map_list_prod, List.map_map]
    rfl
  rw [QuotientGroup.eq_one_iff] at htot
  let μN : Fin L.q → I.Nb := fun i => ⟨y i, hμN i⟩
  have hphi : ∀ i, phiT I.Nb I.φ (y i) = I.φ (μN i) := fun i => by
    simp only [phiT, dif_pos (hμN i)]; rfl
  simp_rw [hphi]
  rw [← Finset.prod_map_toList, show (fun x => I.φ (μN x)) = ⇑I.φ ∘ μN from rfl, ← List.map_map,
    ← map_list_prod, I.φ_ker]
  have e1 : (Subgroup.subtype _) (Finset.univ.toList.map μN).prod =
      (Finset.univ.toList.map y).prod := by
    rw [map_list_prod, List.map_map]; rfl
  have e2 : (cleanLocalGroup S.domGroup I.e I.i0).subtype (Finset.univ.toList.map z).prod =
      (Finset.univ.toList.map y).prod := by
    rw [map_list_prod, List.map_map, ← hzμ']; rfl
  exact ⟨_, htot, e2.trans e1.symm⟩

/-- Totals of `N`-tuples multiply coordinatewise. -/
theorem tmGL_tot_mul {μ ν : Fin L.q → Perm I.B} (hμ : ∀ i, μ i ∈ I.Nb) (hν : ∀ i, ν i ∈ I.Nb) :
    ∏ i, phiT I.Nb I.φ (μ i * ν i) = (∏ i, phiT I.Nb I.φ (μ i)) * ∏ i, phiT I.Nb I.φ (ν i) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => phiT_mul (hμ i) (hν i)

/-- **Different lifts differ by `𝓜`.** If `h, h' ∈ H` and `h⁻¹ h' ∈ N`, then `k(h)⁻¹ k(h')` has
all coordinates in `N` and total label `1`. -/
theorem tmGL_lift_N {h h' : Perm I.B} (hh : h ∈ I.Hb) (hh' : h' ∈ I.Hb) (hN : h⁻¹ * h' ∈ I.Nb) :
    (∀ i, (rowLift I.e I.i0 h i)⁻¹ * rowLift I.e I.i0 h' i ∈ I.Nb) ∧
      ∏ i, phiT I.Nb I.φ ((rowLift I.e I.i0 h i)⁻¹ * rowLift I.e I.i0 h' i) = 1 := by
  obtain ⟨m1, e1⟩ := rowLift_spec I.e I.i0 hh
  obtain ⟨m2, e2⟩ := rowLift_spec I.e I.i0 hh'
  have hy : cleanRowPerm I.e (fun i => (rowLift I.e I.i0 h i)⁻¹ * rowLift I.e I.i0 h' i) ∈
      S.domGroup := by
    have : (fun i => (rowLift I.e I.i0 h i)⁻¹ * rowLift I.e I.i0 h' i) =
        (rowLift I.e I.i0 h)⁻¹ * rowLift I.e I.i0 h' := rfl
    rw [this, map_mul, map_inv]
    exact S.domGroup.mul_mem (S.domGroup.inv_mem m1) m2
  exact tmGL_blockwise I hy (show (rowLift I.e I.i0 h I.i0)⁻¹ * rowLift I.e I.i0 h' I.i0 ∈ I.Nb by
    rw [e1, e2]; exact hN)

/-- A pair of `G` has all its coordinates in the class of its coordinate at `i0`. -/
theorem tmGL_inG_cls {p : (Fin L.q → Perm I.B) × Perm (Fin L.q)}
    (hp : InG I.Hb I.Nb I.φ (rowLift I.e I.i0) p.1 p.2) :
    p.1 I.i0 ∈ I.Hb ∧ tmGLCls I.Nb (p.1 I.i0) (tmGLP p) := by
  obtain ⟨h, hh, μ, ⟨hμN, -, -⟩, hd⟩ := hp
  have hi0 : p.1 I.i0 = h * μ I.i0 := by rw [hd, Pi.mul_apply, (rowLift_spec I.e I.i0 hh).2]
  refine ⟨by rw [hi0]; exact I.Hb.mul_mem hh (I.Nb_le (hμN _)), p.1, p.2, rfl, fun i => ?_⟩
  rw [hi0, hd, Pi.mul_apply]
  have e : (h * μ I.i0)⁻¹ * (rowLift I.e I.i0 h i * μ i) =
      (μ I.i0)⁻¹ * (h⁻¹ * rowLift I.e I.i0 h i) * μ i := by group
  rw [e]
  exact I.Nb.mul_mem (I.Nb.mul_mem (I.Nb.inv_mem (hμN _)) (I.lift_mem hh i)) (hμN i)

/-! ### `J` as a group of permutations -/

/-- **`J = 𝓜 R₀`** on `B × [q]`: the elements of `G|_dom` in `N ≀ Sym(q)`. -/
def tmGLJ : Subgroup (Perm (I.B × Fin L.q)) := tmGLG I ⊓ tmGLW I.Nb

/-- **`tmGLJ I` is the set of `J`-pairs.** -/
theorem tmGLJ_mem_iff [Nonempty I.B] {σ : Perm (I.B × Fin L.q)} :
    σ ∈ tmGLJ I ↔ ∃ μ π, InJ I.Nb I.φ μ π ∧ σ = tmGLP (μ, π) := by
  constructor
  · rintro ⟨hG, hW⟩
    obtain ⟨p, hp, rfl⟩ := (tmGLG_mem_iff I).mp hG
    obtain ⟨d, π, he, hd⟩ := mem_tmGLW.mp hW
    have hpe := tmGL_injective he
    obtain ⟨h, hh, μ, ⟨hμN, hμ1, hπ⟩, hdμ⟩ := hp
    subst hpe
    simp only at hdμ
    -- the coordinate at `i0` is `h μ_{i0} ∈ N`, so `h ∈ N` and its lift lies in `𝓜`
    have hhN : h ∈ I.Nb := by
      have h1 := hd I.i0
      rw [hdμ, Pi.mul_apply, (rowLift_spec I.e I.i0 hh).2] at h1
      have := I.Nb.mul_mem h1 (I.Nb.inv_mem (hμN I.i0))
      simpa using this
    obtain ⟨hm, h0⟩ := rowLift_spec I.e I.i0 hh
    obtain ⟨hkN, hk1⟩ := tmGL_blockwise I hm (by rw [h0]; exact hhN)
    refine ⟨d, π, ⟨hd, ?_, hπ⟩, rfl⟩
    rw [hdμ]
    simp only [Pi.mul_apply]
    rw [tmGL_tot_mul I hkN hμN, hk1, hμ1, one_mul]
  · rintro ⟨μ, π, ⟨hμN, hμ1, hπ⟩, rfl⟩
    refine ⟨(tmGLG_mem_iff I).mpr ⟨(μ, π), ?_, rfl⟩, mem_tmGLW.mpr ⟨μ, π, rfl, hμN⟩⟩
    -- `μ = k(1) (k(1)⁻¹ μ)`
    obtain ⟨hm, h0⟩ := rowLift_spec I.e I.i0 I.Hb.one_mem
    obtain ⟨hkN, hk1⟩ := tmGL_blockwise I hm (by rw [h0]; exact I.Nb.one_mem)
    refine ⟨1, I.Hb.one_mem, fun i => (rowLift I.e I.i0 1 i)⁻¹ * μ i,
      ⟨fun i => I.Nb.mul_mem (I.Nb.inv_mem (hkN i)) (hμN i), ?_, hπ⟩, ?_⟩
    · rw [tmGL_tot_mul I (fun i => I.Nb.inv_mem (hkN i)) hμN, hμ1, mul_one]
      rw [Finset.prod_congr rfl fun i _ => phiT_inv (hkN i), Finset.prod_inv_distrib, hk1,
        inv_one]
    · funext i; simp

/-- The total label of a list product is the product of the totals. -/
theorem tmGL_phiT_list (l : List (Perm I.B)) (hl : ∀ x ∈ l, x ∈ I.Nb) :
    l.prod ∈ I.Nb ∧ phiT I.Nb I.φ l.prod = (l.map (phiT I.Nb I.φ)).prod := by
  induction l with
  | nil => exact ⟨I.Nb.one_mem, phiT_one⟩
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih fun x hx => hl x (List.mem_cons_of_mem a hx)
    have ha := hl a List.mem_cons_self
    refine ⟨by simpa using I.Nb.mul_mem ha h1, ?_⟩
    rw [List.prod_cons, phiT_mul ha h1, h2, List.map_cons, List.prod_cons]

/-- **Conjugation by `h ∈ H` keeps total label `1`**, since `N* = ker φ` is normal in `H`. -/
theorem tmGL_tot_conj {h : Perm I.B} (hh : h ∈ I.Hb) {μ : Fin L.q → Perm I.B}
    (hμ : ∀ i, μ i ∈ I.Nb) (h1 : ∏ i, phiT I.Nb I.φ (μ i) = 1) :
    ∏ i, phiT I.Nb I.φ (h⁻¹ * μ i * h) = 1 := by
  have hμ' : ∀ i, h⁻¹ * μ i * h ∈ I.Nb := fun i => I.normalizes.inv hh (hμ i)
  have hl := tmGL_phiT_list I (List.ofFn μ) (by simpa [List.mem_ofFn] using hμ)
  have hl' := tmGL_phiT_list I (List.ofFn fun i => h⁻¹ * μ i * h)
    (by simpa [List.mem_ofFn] using hμ')
  have A1 : phiT I.Nb I.φ (List.ofFn μ).prod = ∏ i, phiT I.Nb I.φ (μ i) := by
    rw [hl.2, List.map_ofFn, List.prod_ofFn]; rfl
  have A2 : phiT I.Nb I.φ (List.ofFn fun i => h⁻¹ * μ i * h).prod =
      ∏ i, phiT I.Nb I.φ (h⁻¹ * μ i * h) := by
    rw [hl'.2, List.map_ofFn, List.prod_ofFn]; rfl
  rw [← A1] at h1
  rw [← A2]
  -- the conjugated product
  have hprod : (List.ofFn fun i => h⁻¹ * μ i * h).prod = h⁻¹ * (List.ofFn μ).prod * h := by
    have : ∀ l : List (Perm I.B), (l.map fun x => h⁻¹ * x * h).prod = h⁻¹ * l.prod * h := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih => rw [List.map_cons, List.prod_cons, ih, List.prod_cons]; group
    rw [← this, List.map_ofFn]
    rfl
  rw [hprod]
  -- membership in `N* = ker φ`
  have hk : ∀ x (hx : x ∈ I.Nb), phiT I.Nb I.φ x = 1 ↔
      x ∈ I.Nstar.map (cleanLocalGroup S.domGroup I.e I.i0).subtype := by
    intro x hx
    simp only [phiT, dif_pos hx]
    exact I.φ_ker ⟨x, hx⟩
  have hc : h⁻¹ * (List.ofFn μ).prod * h ∈ I.Nb := by rw [← hprod]; exact hl'.1
  rw [hk _ hl.1] at h1
  rw [hk _ hc]
  obtain ⟨n, hn, hne⟩ := h1
  let g : I.Hb := ⟨h, hh⟩
  have hc' : g⁻¹ * n * g⁻¹⁻¹ ∈ I.Nstar := I.Nstar_normal.conj_mem n hn g⁻¹
  refine ⟨_, hc', ?_⟩
  rw [← hne]
  rfl

/-- **A pair with a class in `H` normalizes `J`.** -/
theorem tmGLJ_conj [Nonempty I.B] {h : Perm I.B} (hh : h ∈ I.Hb) {σ τ : Perm (I.B × Fin L.q)}
    (hσ : tmGLCls I.Nb h σ) (hτ : τ ∈ tmGLJ I) : σ * τ * σ⁻¹ ∈ tmGLJ I := by
  obtain ⟨d, π, rfl, hd⟩ := hσ
  obtain ⟨μ, ρ, ⟨hμN, hμ1, hρ⟩, rfl⟩ := (tmGLJ_mem_iff I).mp hτ
  rw [tmGLJ_mem_iff, tmGL_inv, tmGL_mul, tmGL_mul]
  -- write `d_a = h n_a`
  set n : Fin L.q → Perm I.B := fun a => h⁻¹ * d a with hn
  have hnN : ∀ a, n a ∈ I.Nb := hd
  have hdn : ∀ a, d a = h * n a := fun a => by simp [hn]
  refine ⟨_, _, ⟨fun i => ?_, ?_, ?_⟩, rfl⟩
  · rw [hdn, hdn]
    rw [show ∀ a b, (h * n a)⁻¹ * (μ a * (h * n b)) = (n a)⁻¹ * (h⁻¹ * μ a * h) * n b from
      fun a b => by group]
    exact I.Nb.mul_mem (I.Nb.mul_mem (I.Nb.inv_mem (hnN _)) (I.normalizes.inv hh (hμN _)))
      (hnN _)
  · -- reindex by `π`, then split off the telescoping part
    rw [← Equiv.prod_comp π]
    simp only [Perm.inv_apply_self]
    have e : ∀ a, (d a)⁻¹ * (μ a * d (ρ a)) =
        ((n a)⁻¹ * n (ρ a)) * ((n (ρ a))⁻¹ * (h⁻¹ * μ a * h) * n (ρ a)) := by
      intro a; rw [hdn, hdn]; group
    simp_rw [e]
    rw [Finset.prod_congr rfl fun a _ => phiT_mul (I.Nb.mul_mem (I.Nb.inv_mem (hnN a))
      (hnN (ρ a))) (I.Nb.mul_mem (I.Nb.mul_mem (I.Nb.inv_mem (hnN _))
        (I.normalizes.inv hh (hμN a))) (hnN _)), Finset.prod_mul_distrib]
    have t1 : ∏ a, phiT I.Nb I.φ ((n a)⁻¹ * n (ρ a)) = 1 := by
      rw [Finset.prod_congr rfl fun a _ => phiT_mul (I.Nb.inv_mem (hnN a)) (hnN (ρ a)),
        Finset.prod_mul_distrib, Equiv.prod_comp ρ (fun a => phiT I.Nb I.φ (n a)),
        Finset.prod_congr rfl fun a _ => phiT_inv (hnN a), Finset.prod_inv_distrib,
        inv_mul_cancel]
    have t2 : ∏ a, phiT I.Nb I.φ ((n (ρ a))⁻¹ * (h⁻¹ * μ a * h) * n (ρ a)) =
        ∏ a, phiT I.Nb I.φ (h⁻¹ * μ a * h) := by
      refine Finset.prod_congr rfl fun a _ => ?_
      have := phiT_conj (φ := I.φ) (I.Nb.inv_mem (hnN (ρ a))) (I.normalizes.inv hh (hμN a))
      simpa using this
    rw [t1, t2, one_mul]
    exact tmGL_tot_conj I hh hμN hμ1
  · rw [Equiv.Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv]
    rw [Equiv.Perm.mem_alternatingGroup] at hρ
    rw [hρ]; simp

/-! ### What the labels are -/

variable [Nonempty I.B]

/-- **The label test as a transporter in `G|_dom`.** `h ∈ tmGlLab I r` exactly when `h` is a
residual element and some element of `G|_dom` of class `h` carries `X` to `Y`. -/
theorem tmGL_lab_iff (r : Perm I.B) {h : Perm I.B} :
    h ∈ tmGlLab I r ↔ h ∈ tmGlRes I r ∧ ∃ σ ∈ tmGLG I, tmGLCls I.Nb h σ ∧
      tmGLStr (rowTuple I.e S.y) ∘ σ = tmGLStr (rowTuple I.e S.x) := by
  have hcos : ∀ i j (g : Perm I.B), g ∈ (I.cosetCall (i, j)).answer ↔
      g ∈ I.Hb ∧ rowTuple I.e S.x i ∘ g = rowTuple I.e S.y j := by
    intro i j g
    simp only [RowTerminal.cosetCall, rowState_answer, Set.mem_setOf_eq]
    rfl
  constructor
  · rintro ⟨hres, μ, π, hJ, hT⟩
    have hhH : h ∈ I.Hb := hres.1.1
    refine ⟨hres, tmGLP (rowLift I.e I.i0 h * μ, π),
      (tmGLG_mem_iff I).mpr ⟨_, ⟨h, hhH, μ, hJ, rfl⟩, rfl⟩, ⟨_, _, rfl, fun i => ?_⟩, ?_⟩
    · rw [Pi.mul_apply, ← mul_assoc]
      exact I.Nb.mul_mem (I.lift_mem hhH i) (hJ.1 i)
    · rw [tmGL_str_comp]
      intro i
      exact ((hcos _ _ _).mp (hT i)).2
  · rintro ⟨hres, σ, hσG, hσc, hσY⟩
    have hhH : h ∈ I.Hb := hres.1.1
    obtain ⟨p, hp, rfl⟩ := (tmGLG_mem_iff I).mp hσG
    obtain ⟨hp0, hpc⟩ := tmGL_inG_cls I hp
    have hq : 0 < L.q := by have := I.three_le; omega
    have hhp : h⁻¹ * p.1 I.i0 ∈ I.Nb := tmGLCls_unique hq hσc hpc
    obtain ⟨h', hh', μ, ⟨hμN, hμ1, hπ⟩, hd⟩ := hp
    -- `h⁻¹ h' ∈ N`
    have hi0 : p.1 I.i0 = h' * μ I.i0 := by rw [hd, Pi.mul_apply, (rowLift_spec I.e I.i0 hh').2]
    have hhh' : h⁻¹ * h' ∈ I.Nb := by
      have := I.Nb.mul_mem hhp (I.Nb.inv_mem (hμN I.i0))
      rw [hi0] at this
      simpa [mul_assoc] using this
    obtain ⟨hνN, hν1⟩ := tmGL_lift_N I hhH hh' hhh'
    set ν : Fin L.q → Perm I.B := fun i => (rowLift I.e I.i0 h i)⁻¹ * rowLift I.e I.i0 h' i
    refine ⟨hres, ν * μ, p.2, ⟨fun i => I.Nb.mul_mem (hνN i) (hμN i), ?_, hπ⟩, fun i => ?_⟩
    · simp only [Pi.mul_apply]
      rw [tmGL_tot_mul I hνN hμN, hν1, hμ1, one_mul]
    · have e : rowLift I.e I.i0 h i * (ν * μ) i = p.1 i := by
        rw [hd]; simp [ν, mul_assoc]
      rw [e, hcos]
      refine ⟨?_, (tmGL_str_comp _ _ p.1 p.2).mp hσY i⟩
      rw [← e]
      exact I.Hb.mul_mem (I.lift_mem_H hhH i) (I.Nb_le (I.Nb.mul_mem (hνN i) (hμN i)))

end RT

end GI.Impl
