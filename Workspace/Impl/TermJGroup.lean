import Workspace.Impl.TermJPair

/-!
# The groups of the `J`-step of Theorem A.23

For a row terminal `I`, the domain group `G|_dom` acts on `B × [q]` through the coordinates
`I.e`. This file identifies it, and the groups the `J`-step uses, with sets of pairs:

* `tmJG I`: the domain group on `B × [q]`. `tmJG_mem_iff`: it consists of the pairs of
  `G = K R₀` of the model (`InG`: `(k(h) μ, π)` with `h ∈ H` and `(μ, π) ∈ J`). This is
  `actsAs_inG` and `tm_inG_mem` (Theorems A.17 and A.18).
* `tmJ_blockwise`: a blockwise element of `G|_dom` whose coordinate at `i0` lies in `N` has all
  coordinates in `N` and total label zero (Theorem A.18: "`K/M` is the diagonal `H/N`", and the
  zero-sum description of `M/M*`). The paper: "Likewise `h ∈ N` acts trivially: its lift lies in
  `𝓜`".
* `tmJJ I = tmJG I ⊓ tmJW N`: the group `J = 𝓜 R₀` (`tmJJ_mem_iff`). It is normalized by
  `N ≀ Sym(q)` (`tmJJ_normalized`).
* `tmJG_le_D`: `G|_dom` lies in the pairs of one class modulo `N`, so it normalizes `N ≀ Sym(q)`.
* `tmJ_mem_T`: the piece `tmCosetT I r` as permutations: the elements of `G|_dom` that carry `X`
  to `Y` and whose class lies in `R r`.
* `tmJ_lab_exists`, `tmJ_T_lab`: the label coset `tmGlLab I r` is the set of classes of the
  piece (modulo `N`).
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Paper Equiv Equiv.Perm

variable {Ω C : Type}

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

/-- **The domain group on `B × [q]`**, through the coordinates `I.e`. -/
def tmJG : Subgroup (Perm (I.B × Fin L.q)) :=
  S.domGroup.comap (Equiv.permCongrHom I.e).toMonoidHom

theorem mem_tmJG {σ : Perm (I.B × Fin L.q)} : σ ∈ tmJG I ↔ I.e.permCongr σ ∈ S.domGroup :=
  Iff.rfl

/-- **The domain group consists of the pairs of `G = K R₀`.** -/
theorem tmJG_mem_iff {σ : Perm (I.B × Fin L.q)} :
    σ ∈ tmJG I ↔ ∃ p : (Fin L.q → Perm I.B) × Perm (Fin L.q),
      InG I.Hb I.Nb I.φ (rowLift I.e I.i0) p.1 p.2 ∧ tmJP p = σ := by
  rw [mem_tmJG]
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
coordinates lie in `N` and its total label is zero (Theorem A.18). -/
theorem tmJ_blockwise {y : Fin L.q → Perm I.B} (hy : cleanRowPerm I.e y ∈ S.domGroup)
    (h0 : y I.i0 ∈ I.Nb) : (∀ i, y i ∈ I.Nb) ∧ ∏ i, phiT I.Nb I.φ (y i) = 1 := by
  classical
  have hK : (⟨_, hy⟩ : S.domGroup) ∈ blockKernel I.e := ⟨y, rfl⟩
  -- Its `θ` is trivial, so it lies in `M`.
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
  -- Its coordinates lie in `N`.
  obtain ⟨z, hz, hzμ⟩ := (Subgroup.mem_inf.1 hM).2
  have hzμ' : (fun r => (z r : Perm I.B)) = y := cleanRowPerm_injective I.e hzμ
  have hμN : ∀ i, y i ∈ I.Nb := fun i => ⟨z i, hz i, by rw [← hzμ']; rfl⟩
  refine ⟨hμN, ?_⟩
  -- The zero-sum clause: the total of the coordinates lies in `N*`.
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

/-- The lift of `h ∈ N` lies in `𝓜`. -/
theorem tmJ_lift_inJ {h : Perm I.B} (hh : h ∈ I.Nb) :
    (∀ i, rowLift I.e I.i0 h i ∈ I.Nb) ∧ ∏ i, phiT I.Nb I.φ (rowLift I.e I.i0 h i) = 1 := by
  obtain ⟨hmem, h0⟩ := rowLift_spec I.e I.i0 (I.Nb_le hh)
  exact tmJ_blockwise I hmem (by rw [h0]; exact hh)

/-- A pair of `G` has all its coordinates in the class of its coordinate at `i0`. -/
theorem tmJ_inG_cls {p : (Fin L.q → Perm I.B) × Perm (Fin L.q)}
    (hp : InG I.Hb I.Nb I.φ (rowLift I.e I.i0) p.1 p.2) :
    p.1 I.i0 ∈ I.Hb ∧ tmJP p ∈ tmJCls I.Nb (p.1 I.i0) := by
  obtain ⟨h, hh, μ, ⟨hμN, -, -⟩, hd⟩ := hp
  have hi0 : p.1 I.i0 = h * μ I.i0 := by rw [hd, Pi.mul_apply, (rowLift_spec I.e I.i0 hh).2]
  refine ⟨by rw [hi0]; exact I.Hb.mul_mem hh (I.Nb_le (hμN _)), p, rfl, fun i => ?_⟩
  rw [hi0, hd, Pi.mul_apply]
  have e : (h * μ I.i0)⁻¹ * (rowLift I.e I.i0 h i * μ i) =
      (μ I.i0)⁻¹ * (h⁻¹ * rowLift I.e I.i0 h i) * μ i := by group
  rw [e]
  exact I.Nb.mul_mem (I.Nb.mul_mem (I.Nb.inv_mem (hμN _)) (I.lift_mem hh i)) (hμN i)

/-- **`G|_dom` lies in the pairs of one class modulo `N`.** -/
theorem tmJG_cls {σ : Perm (I.B × Fin L.q)} (hσ : σ ∈ tmJG I) :
    ∃ h ∈ I.Hb, σ ∈ tmJCls I.Nb h := by
  obtain ⟨p, hp, rfl⟩ := (tmJG_mem_iff I).1 hσ
  exact ⟨_, tmJ_inG_cls I hp⟩

theorem tmJG_le_D : tmJG I ≤ tmJD I.Hb I.Nb I.normalizes := by
  intro σ hσ
  obtain ⟨h, hh, hσ'⟩ := tmJG_cls I hσ
  exact tmJCls_mem_D hh hσ'

/-! ### The group `J` -/

/-- **The group `J = 𝓜 R₀`** on `B × [q]`: `G|_dom ∩ N ≀ Sym(q)`. -/
def tmJJ : Subgroup (Perm (I.B × Fin L.q)) := tmJG I ⊓ tmJW I.Nb

/-- **`G|_dom ∩ N ≀ Sym(q)` consists of the pairs of `J`.** -/
theorem tmJJ_mem_iff [Nonempty I.B] {σ : Perm (I.B × Fin L.q)} :
    σ ∈ tmJJ I ↔ ∃ p : (Fin L.q → Perm I.B) × Perm (Fin L.q),
      InJ I.Nb I.φ p.1 p.2 ∧ tmJP p = σ := by
  constructor
  · rintro ⟨hG, hW⟩
    obtain ⟨p, hp, rfl⟩ := (tmJG_mem_iff I).1 hG
    obtain ⟨p', hp', he⟩ := hW
    rw [tmJP_injective he] at hp'
    obtain ⟨h, hh, μ, ⟨hμN, hμ1, hπ⟩, hd⟩ := hp
    have hi0 : p.1 I.i0 = h * μ I.i0 := by rw [hd, Pi.mul_apply, (rowLift_spec I.e I.i0 hh).2]
    have hhN : h ∈ I.Nb := by
      have : h = p.1 I.i0 * (μ I.i0)⁻¹ := by rw [hi0]; group
      rw [this]; exact I.Nb.mul_mem (hp' _) (I.Nb.inv_mem (hμN _))
    obtain ⟨-, hk1⟩ := tmJ_lift_inJ I hhN
    refine ⟨p, ⟨hp', ?_, hπ⟩, rfl⟩
    rw [hd]
    simp only [Pi.mul_apply]
    rw [Finset.prod_congr rfl fun i _ =>
      phiT_mul ((tmJ_lift_inJ I hhN).1 i) (hμN i), Finset.prod_mul_distrib, hk1, hμ1, one_mul]
  · rintro ⟨p, ⟨hμN, hμ1, hπ⟩, rfl⟩
    refine ⟨(tmJG_mem_iff I).2 ⟨p, ?_, rfl⟩, ⟨p, hμN, rfl⟩⟩
    obtain ⟨hk, hk1⟩ := tmJ_lift_inJ I I.Nb.one_mem
    refine ⟨1, I.Hb.one_mem, (rowLift I.e I.i0 1)⁻¹ * p.1, ⟨fun i => ?_, ?_, hπ⟩, ?_⟩
    · exact I.Nb.mul_mem (I.Nb.inv_mem (hk i)) (hμN i)
    · simp only [Pi.mul_apply, Pi.inv_apply]
      rw [Finset.prod_congr rfl fun i _ =>
        phiT_mul (I.Nb.inv_mem (hk i)) (hμN i), Finset.prod_mul_distrib,
        Finset.prod_congr rfl fun i _ => phiT_inv (hk i), Finset.prod_inv_distrib, hk1, hμ1]
      simp
    · simp

/-- **`J` is normalized by `N ≀ Sym(q)`.** The conjugate of `(μ, ρ)` by `(n, π)` has
coordinates `n_a⁻¹ μ_a n_{ρ a}`, whose labels sum to the total of `μ`, and an even matching. -/
theorem tmJJ_normalized [Nonempty I.B] {w : Perm (I.B × Fin L.q)} (hw : w ∈ tmJW I.Nb)
    {j : Perm (I.B × Fin L.q)} (hj : j ∈ tmJJ I) : w * j * w⁻¹ ∈ tmJJ I := by
  obtain ⟨⟨n, π⟩, hn, rfl⟩ := hw
  obtain ⟨⟨μ, ρ⟩, ⟨hμN, hμ1, hρ⟩, rfl⟩ := (tmJJ_mem_iff I).1 hj
  rw [tmJP_inv, tmJP_mul, tmJP_mul]
  refine (tmJJ_mem_iff I).2 ⟨_, ⟨fun i => ?_, ?_, ?_⟩, rfl⟩
  · simp only
    exact I.Nb.mul_mem (I.Nb.inv_mem (hn _)) (I.Nb.mul_mem (hμN _) (hn _))
  · simp only
    have hterm : ∀ i, phiT I.Nb I.φ ((n (π⁻¹ i))⁻¹ * (μ (π⁻¹ i) * n (ρ (π⁻¹ i)))) =
        (phiT I.Nb I.φ (n (π⁻¹ i)))⁻¹ * (phiT I.Nb I.φ (μ (π⁻¹ i)) *
          phiT I.Nb I.φ (n (ρ (π⁻¹ i)))) := fun i => by
      rw [phiT_mul (I.Nb.inv_mem (hn _)) (I.Nb.mul_mem (hμN _) (hn _)), phiT_inv (hn _),
        phiT_mul (hμN _) (hn _)]
    rw [Finset.prod_congr rfl fun i _ => hterm i]
    rw [Equiv.prod_comp (π⁻¹) (fun a => (phiT I.Nb I.φ (n a))⁻¹ *
      (phiT I.Nb I.φ (μ a) * phiT I.Nb I.φ (n (ρ a))))]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hμ1,
      Equiv.prod_comp ρ (fun a => phiT I.Nb I.φ (n a))]
    simp
  · simp only
    rw [mem_alternatingGroup] at hρ ⊢
    simp [Perm.sign_mul, hρ]

/-! ### The piece of one radical coset -/

/-- **The piece `tmCosetT I r` as permutations of `B × [q]`**: the elements of `G|_dom` that carry
`X` to `Y` and whose class lies in `R r`. -/
theorem tmJ_mem_T [Nonempty I.B] {r : Perm I.B} (hr : r ∈ I.Hb) {σ : Perm (I.B × Fin L.q)} :
    σ ∈ tmJP '' tmCosetT I r ↔ σ ∈ tmJG I ∧
      tmJStr (rowTuple I.e S.y) ∘ σ = tmJStr (rowTuple I.e S.x) ∧
      ∃ x ∈ tmRad I, σ ∈ tmJCls I.Nb (x * r) := by
  have hex : ∀ p : (Fin L.q → Perm I.B) × Perm (Fin L.q), p ∈ tmExactT I ↔
      InG I.Hb I.Nb I.φ (rowLift I.e I.i0) p.1 p.2 ∧
        ∀ i, rowTuple I.e S.x i ∘ p.1 i = rowTuple I.e S.y (p.2 i) := by
    intro p
    have h1 : p ∈ tmExactT I ↔ p ∈ isoG I.Hb I.Nb I.φ (rowLift I.e I.i0) (rowTuple I.e S.x)
        (rowTuple I.e S.y) := by
      rw [tmExactT, I.tableTransport_exact,
        terminalTransport_eq I.Nb_le I.normalizes (fun h hh i => I.lift_mem hh i)]
    rw [h1]
    exact and_congr_right fun _ => rowAct_eq_iff
  have hNR : I.Nb ≤ tmRad I := (radicalPreimage_spec I.Nb_le I.normalizes).2.1
  constructor
  · rintro ⟨p, ⟨hp, x, hx, hxr⟩, rfl⟩
    obtain ⟨hG, hxy⟩ := (hex p).1 hp
    refine ⟨(tmJG_mem_iff I).2 ⟨p, hG, rfl⟩, (tmJ_mem_iso _ _ p).2 hxy, x, hx, ?_⟩
    rw [← hxr]
    exact (tmJ_inG_cls I hG).2
  · rintro ⟨hG, hxy, x, hx, hcl⟩
    obtain ⟨p, hp, rfl⟩ := (tmJG_mem_iff I).1 hG
    refine ⟨p, ⟨(hex p).2 ⟨hp, (tmJ_mem_iso _ _ p).1 hxy⟩, ?_⟩, rfl⟩
    have hu := tmJCls_unique I.i0 hcl (tmJ_inG_cls I hp).2
    -- `p_{i0} = x r n = (x · r n r⁻¹) r`
    refine ⟨x * (r * ((x * r)⁻¹ * p.1 I.i0) * r⁻¹),
      (tmRad I).mul_mem hx (hNR (I.normalizes r hr _ hu)), by group⟩

/-- **Every label element has an element of the piece in its class** (`tmGl_cosetT_eq`). -/
theorem tmJ_lab_exists {r : Perm I.B} {h : Perm I.B} (hh : h ∈ tmGlLab I r) :
    ∃ t ∈ tmJP '' tmCosetT I r, t ∈ tmJCls I.Nb h := by
  obtain ⟨⟨hiso, hR⟩, μ, π, hJ, hT⟩ := hh
  have hhH : h ∈ I.Hb := (mem_iso.1 hiso).1
  refine ⟨tmJP (rowLift I.e I.i0 h * μ, π), ⟨_, ?_, rfl⟩, _, rfl, fun i => ?_⟩
  · rw [tmGl_cosetT_eq]
    exact ⟨h, ⟨⟨hiso, hR⟩, μ, π, hJ, hT⟩, μ, hJ, rfl, hT⟩
  · simp only [Pi.mul_apply]
    rw [← mul_assoc]
    exact I.Nb.mul_mem (I.lift_mem hhH i) (hJ.1 i)

/-- **Every element of the piece has its class in the label coset.** -/
theorem tmJ_T_lab {r : Perm I.B} {t : Perm (I.B × Fin L.q)} (ht : t ∈ tmJP '' tmCosetT I r) :
    ∃ h ∈ tmGlLab I r, t ∈ tmJCls I.Nb h := by
  obtain ⟨p, hp, rfl⟩ := ht
  rw [tmGl_cosetT_eq] at hp
  obtain ⟨h, hh, μ, hJ, hd, -⟩ := hp
  have hhH : h ∈ I.Hb := (mem_iso.1 hh.1.1).1
  refine ⟨h, hh, p, rfl, fun i => ?_⟩
  rw [hd, Pi.mul_apply, ← mul_assoc]
  exact I.Nb.mul_mem (I.lift_mem hhH i) (hJ.1 i)

/-- The label coset lies in `H`. -/
theorem tmJ_lab_le {r h : Perm I.B} (hh : h ∈ tmGlLab I r) : h ∈ I.Hb := (mem_iso.1 hh.1.1).1

/-- **A lift of `h ∈ H` in `G|_dom`**: `(k(h), 1)`, of class `h`. So the constant pair `(h; 1)`
lies in `G|_dom · (N ≀ Sym(q))`. -/
theorem tmJ_const_mem_GW {h : Perm I.B} (hh : h ∈ I.Hb) :
    ∃ g ∈ tmJG I, ∃ w ∈ tmJW (q := L.q) I.Nb,
      tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q))) = g * w := by
  have hg : tmJP (rowLift I.e I.i0 h, 1) ∈ tmJG I := by
    refine (tmJG_mem_iff I).2 ⟨_, ⟨h, hh, 1, ⟨fun _ => I.Nb.one_mem, ?_, ?_⟩, by simp⟩, rfl⟩
    · simp [phiT_one]
    · exact Subgroup.one_mem _
  have hgc : tmJP (rowLift I.e I.i0 h, 1) ∈ tmJCls I.Nb h :=
    ⟨_, rfl, fun i => I.lift_mem hh i⟩
  refine ⟨_, hg, _, ?_, (mul_inv_cancel_left _ _).symm⟩
  have := tmJCls_mul I.normalizes (I.Hb.inv_mem hh) (tmJCls_inv I.normalizes hh hgc)
    (tmJ_const_mem I.Nb h)
  rw [mul_inv_cancel] at this
  exact tmJCls_one_iff.1 this

end RT

end GI.Impl
