module

public import Workspace.Proved.VsPStep4Math
public import Workspace.Proved.VsQSplit1
public import Workspace.Proved.VsTCliff
public import Workspace.Proved.VsWKey
public import Workspace.Proved.VsQAlg

@[expose] public section

/-!
# The algebra of an abelian normal subgroup

The A-loop keeps a list `as` of elements of `H` whose local images `Ā` form an abelian normal
subgroup of `H̄`, and a list `Lb` of stored local matrices spanning `L = 𝔽_p[Λ(as)]` (what
`vsFAlgSpan` returns). Here:

* `VsQAHyp`: these hypotheses.
* `VsQAHyp.memB`: the maps of the span of `Lb` are exactly `vsTAlg Ā`.
* `vsQA_ann`: the common kernel of the nilpotent elements of `L` is nonzero and invariant
  under every generator of `H`. When it is not everything, it gives a chain split.
-/

open Matrix

set_option backward.isDefEq.respectTransparency false

namespace GI.Proved

open GI.Impl GI.Cited Equiv

variable {I : VecStabInst} {s : VsQSt I}

/-- The hypotheses of the A-loop on `as` and the basis `Lb` of `L = 𝔽_p[Λ(as)]`. -/
structure VsQAHyp (hs : VsQStOK s) (as : List (Perm (Fin I.n))) (Lb : List (List (List ℕ))) : Prop where
  has : gens as ≤ gens s.hs
  hasn : VsPNormd (gens s.hs) (gens as)
  hal : as.length ≤ I.n ^ 2
  habl : vsPBar hs (gens as) ≤ Subgroup.centralizer (vsPBar hs (gens as) : Set _)
  hLb : ∀ M ∈ Lb, VsFSq I.p (vsQD s) M
  hspan : vsFMatSpan I.p (vsQD s) Lb = Subalgebra.toSubmodule
    (vsFAlgOf I.p (vsQD s) (as.map (vsPLocL I s.ws' (vsQCs s))))
  hLbl : Lb.length ≤ vsQD s * vsQD s

namespace VsQAHyp

variable [Fact I.p.Prime] {hs : VsQStOK s} {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}

/-- `Ā` is an abelian normal subgroup of `H̄`. -/
theorem abNormal (h : VsQAHyp hs as Lb) :
    VsTAbNormal (vsPBar hs (gens s.hs)) (vsPBar hs (gens as)) := by
  refine ⟨fun u hu => ?_, ⟨fun a ha g => ?_⟩, fun a ha b hb => ?_⟩
  · obtain ⟨x, hxK, hx, rfl⟩ := (vsPBar_mem_iff hs).1 hu
    exact vsPRho_mem_vsPBar hs hx hx
  · rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨x, hxK, hx, ex⟩ := (vsPBar_mem_iff hs).1 ha
    obtain ⟨y, -, hy, ey⟩ := (vsPBar_mem_iff hs).1 g.2
    have e : ((g * a * g⁻¹ : vsPBar hs (gens s.hs)) : (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ)
        = vsPRho hs (y * x * y⁻¹) := by
      rw [vsPRho_conj hs hx hy, ex, ey]; rfl
    rw [e]
    exact vsPRho_mem_vsPBar hs (h.hasn y hy x hxK) (mul_mem (mul_mem hy hx) (inv_mem hy))
  · exact Subgroup.mem_centralizer_iff.1 (h.habl hb) a ha

theorem sq (h : VsQAHyp hs as Lb) : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M := fun M hM =>
  ⟨(h.hLb M hM).rows, (h.hLb M hM).len⟩

/-- **The span of `Lb`, as maps, is `vsTAlg Ā`.** -/
theorem memB (h : VsQAHyp hs as Lb) (f : Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :
    f ∈ vsTAlg (vsPBar hs (gens as)) ↔
      ∃ x ∈ Submodule.span (ZMod I.p) {X | ∃ M ∈ Lb, vsWM I.p (vsQD s) M = X},
        Matrix.toLinAlgEquiv' x = f := by
  have hset : {X | ∃ M ∈ as.map (vsPLocL I s.ws' (vsQCs s)), vsFMatrix I.p (vsQD s) M = X} =
      Matrix.transpose '' {X | ∃ a ∈ as, vsQLam s a = X} := by
    ext X
    simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨vsQLam s a, ⟨a, ha, rfl⟩, (vsFMatrix_loc a).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, vsFMatrix_loc a⟩
  -- the span of the `vsWM M` is the transpose of the span of the `vsFMatrix M`
  have hT : ∀ x, x ∈ Submodule.span (ZMod I.p) {X | ∃ M ∈ Lb, vsWM I.p (vsQD s) M = X} ↔
      xᵀ ∈ vsFMatSpan I.p (vsQD s) Lb := by
    intro x
    have e : Submodule.span (ZMod I.p) {X | ∃ M ∈ Lb, vsWM I.p (vsQD s) M = X} =
        (vsFMatSpan I.p (vsQD s) Lb).map (Matrix.transposeLinearEquiv (Fin (vsQD s)) (Fin (vsQD s))
          (ZMod I.p) (ZMod I.p)).toLinearMap := by
      rw [vsFMatSpan, Submodule.map_span]
      congr 1
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_image, LinearEquiv.coe_coe,
        Matrix.transposeLinearEquiv_apply]
      constructor
      · rintro ⟨M, hM, rfl⟩; exact ⟨_, ⟨M, hM, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨M, hM, rfl⟩, rfl⟩; exact ⟨M, hM, rfl⟩
    rw [e, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨xᵀ, hx, by simp⟩
  constructor
  · intro hf
    refine ⟨Matrix.toLinAlgEquiv'.symm f, ?_, by simp⟩
    rw [hT, h.hspan, Subalgebra.mem_toSubmodule, vsFAlgOf, hset, vsP_adjoin_transpose,
      ← vsP_mem_vsTAlg_iff hs h.has]
    convert hf using 1
    exact Matrix.toLin'_toMatrix' f
  · rintro ⟨x, hx, rfl⟩
    rw [hT, h.hspan, Subalgebra.mem_toSubmodule, vsFAlgOf, hset, vsP_adjoin_transpose,
      ← vsP_mem_vsTAlg_iff hs h.has] at hx
    change Matrix.toLinAlgEquiv' x ∈ vsTAlg (vsPBar hs (gens as)) at hx
    exact hx

/-- The stored matrices of `Lb` commute. -/
theorem comm (h : VsQAHyp hs as Lb) : VsWComm I.p (vsQD s) Lb := by
  intro M hM M' hM'
  have hB := vsTAlg_comm h.abNormal.2.2
  have h1 := (h.memB _).2 ⟨_, Submodule.subset_span ⟨M, hM, rfl⟩, rfl⟩
  have h2 := (h.memB _).2 ⟨_, Submodule.subset_span ⟨M', hM', rfl⟩, rfl⟩
  have := hB _ h1 _ h2
  have e := congrArg Matrix.toLinAlgEquiv'.symm this.eq
  simp only [map_mul, AlgEquiv.symm_apply_apply] at e
  exact e

end VsQAHyp

/-- **The kernel of the nilpotent part of `L`.** It is nonzero, and invariant under `H`
because `Ā` is normal in `H̄`. -/
theorem vsQA_ann [Fact I.p.Prime] {hs : VsQStOK s} {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
    (h : VsQAHyp hs as Lb) (hD : 1 ≤ vsQD s) :
    vsWSp I.p (vsQD s) (vsFAnnL I.p (vsQD s) (vsFNilL I.p (vsQD s) Lb)) ≠ ⊥ ∧
      ∀ g ∈ s.hs, ∀ a ∈ vsWSp I.p (vsQD s) (vsFAnnL I.p (vsQD s) (vsFNilL I.p (vsQD s) Lb)),
        vsQLam s g *ᵥ a ∈ vsWSp I.p (vsQD s) (vsFAnnL I.p (vsQD s) (vsFNilL I.p (vsQD s) Lb)) := by
  haveI : Nontrivial (Fin (vsQD s) → ZMod I.p) := by
    haveI : Nonempty (Fin (vsQD s)) := ⟨⟨0, hD⟩⟩
    infer_instance
  have hsp := vsFAnnL_nil I.prime h.sq h.comm (vsTAlg (vsPBar hs (gens as))) h.memB
  rw [hsp]
  refine ⟨vsFAnn_ne_bot _ (vsTAlg_comm h.abNormal.2.2), fun g hg a ha => ?_⟩
  have hgg : g ∈ gens s.hs := Subgroup.subset_closure hg
  set T := vsQRho hs ⟨g, hgg⟩
  have hTG : T ∈ vsPBar hs (gens s.hs) :=
    Subgroup.mem_map.2 ⟨⟨g, hgg⟩, by rw [Subgroup.mem_subgroupOf]; exact hgg, rfl⟩
  have hT : ∀ x ∈ vsTAlg (vsPBar hs (gens as)),
      (↑T⁻¹ : Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) * x * ↑T ∈ vsTAlg (vsPBar hs (gens as)) :=
    fun x hx => by
      have := vsT_conj_mem h.abNormal (inv_mem hTG) hx
      simpa using this
  have := vsFAnn_map _ T hT ha
  rwa [vsQRho_apply hs] at this

/-! ### The pieces -/

section Pieces

variable [Fact I.p.Prime] {hs : VsQStOK s} {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}

/-- The Frobenius fixed points of `L`, as maps. -/
noncomputable def vsQAFix (s : VsQSt I) (Lb : List (List (List ℕ))) :
    Fin (vsFFixL I.p (vsQD s) Lb).length → Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p) :=
  fun i => vsWLin I.p (vsQD s) (vsFFixL I.p (vsQD s) Lb)[i]

theorem vsQAFix_sq (Lb : List (List (List ℕ))) : ∀ M ∈ vsFFixL I.p (vsQD s) Lb, VsWSq I.p (vsQD s) M := by
  intro M hM
  simp only [vsFFixL, List.mem_map] at hM
  obtain ⟨a, -, rfl⟩ := hM
  exact vsWMC_sq I.prime.pos _ a

theorem VsQAHyp.fix (h : VsQAHyp hs as Lb) (i) :
    vsQAFix s Lb i ∈ vsTAlg (vsPBar hs (gens as)) ∧ vsQAFix s Lb i ^ I.p = vsQAFix s Lb i := by
  have hm := (vsFFixL_span I.prime h.sq h.comm (vsWM I.p (vsQD s) (vsFFixL I.p (vsQD s) Lb)[i])).1
    (Submodule.subset_span ⟨_, List.getElem_mem i.2, rfl⟩)
  refine ⟨(h.memB _).2 ⟨_, hm.1, rfl⟩, ?_⟩
  have e := congrArg (Matrix.toLinAlgEquiv' : _ ≃ₐ[ZMod I.p] _) hm.2
  rw [map_pow] at e
  change vsQAFix s Lb i ^ I.p = vsQAFix s Lb i at e
  exact e

theorem VsQAHyp.fixSpan (h : VsQAHyp hs as Lb) :
    ∀ t ∈ vsTAlg (vsPBar hs (gens as)), t ^ I.p = t →
      t ∈ Submodule.span (ZMod I.p) (Set.range (vsQAFix s Lb)) := by
  intro t ht hfix
  obtain ⟨x, hx, rfl⟩ := (h.memB t).1 ht
  rw [← map_pow] at hfix
  have hx' : x ^ I.p = x := Matrix.toLinAlgEquiv'.injective hfix
  have hmem := (vsFFixL_span I.prime h.sq h.comm x).2 ⟨hx, hx'⟩
  have hle : (Submodule.span (ZMod I.p)
      {X | ∃ y ∈ vsFFixL I.p (vsQD s) Lb, vsWM I.p (vsQD s) y = X}).map
        (Matrix.toLinAlgEquiv' : _ ≃ₐ[ZMod I.p] _).toLinearMap ≤
      Submodule.span (ZMod I.p) (Set.range (vsQAFix s Lb)) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  exact hle ⟨x, hmem, rfl⟩

/-- The pieces of `L`. -/
noncomputable def vsQAPcs (s : VsQSt I) (Lb : List (List (List ℕ))) : List (List (List ℕ)) :=
  vsFEigL I.p (vsQD s) (vsFFixL I.p (vsQD s) Lb)

/-- **`H` permutes the pieces.** -/
theorem vsQA_piece_map (h : VsQAHyp hs as Lb) {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs)
    {Q : List (List ℕ)} (hQ : Q ∈ vsQAPcs s Lb) :
    ∃ Q' ∈ vsQAPcs s Lb, (vsWSp I.p (vsQD s) Q).map (Matrix.toLin' (vsQLam s g)) =
      vsWSp I.p (vsQD s) Q' := by
  obtain ⟨-, hne, c, hc⟩ := (vsFEigL_pieces I.prime _ (vsQAFix_sq (s := s) Lb)).1 Q hQ
  set T := vsQRho hs ⟨g, hg⟩
  have hTG : T ∈ vsPBar hs (gens s.hs) :=
    Subgroup.mem_map.2 ⟨⟨g, hg⟩, by rw [Subgroup.mem_subgroupOf]; exact hg, rfl⟩
  have hT : ∀ x ∈ vsTAlg (vsPBar hs (gens as)),
      (↑T⁻¹ : Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) * x * ↑T ∈ vsTAlg (vsPBar hs (gens as)) :=
    fun x hx => by simpa using vsT_conj_mem h.abNormal (inv_mem hTG) hx
  have hT' : ∀ x ∈ vsTAlg (vsPBar hs (gens as)),
      (↑T : Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) * x * ↑T⁻¹ ∈ vsTAlg (vsPBar hs (gens as)) :=
    fun x hx => vsT_conj_mem h.abNormal hTG hx
  have hne' : vsFEig (vsQAFix s Lb) c ≠ ⊥ := fun hb => hne (hc.trans hb)
  obtain ⟨c', hc'⟩ := vsFEig_map _ (vsQAFix s Lb) (fun i => (h.fix i).1) (fun i => (h.fix i).2)
    h.fixSpan T hT hT' c hne'
  have hne'' : vsFEig (vsQAFix s Lb) c' ≠ ⊥ := by
    rw [← hc']
    intro hb
    apply hne'
    rw [eq_bot_iff]
    intro v hv
    have hm : (T : Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) v ∈
        (vsFEig (vsQAFix s Lb) c).map (T : Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) :=
      Submodule.mem_map_of_mem hv
    rw [hb] at hm
    exact (Submodule.mem_bot _).2 (vsT_unit_inj T (by rw [(Submodule.mem_bot _).1 hm, map_zero]))
  obtain ⟨Q', hQ', hQ'c⟩ := (vsFEigL_pieces I.prime _ (vsQAFix_sq (s := s) Lb)).2 c' hne''
  refine ⟨Q', hQ', ?_⟩
  rw [hQ'c]
  have eT : (T : Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) = Matrix.toLin' (vsQLam s g) :=
    vsQRho_eq_toLin' hs hg
  rw [hc, ← eT]
  exact hc'

/-- **One piece: `L` is a field.** If the nilpotent kernel is everything and some piece is
everything, every nonzero element of `vsTAlg Ā` is injective. -/
theorem vsQA_field (h : VsQAHyp hs as Lb)
    (hann : vsWSp I.p (vsQD s) (vsFAnnL I.p (vsQD s) (vsFNilL I.p (vsQD s) Lb)) = ⊤)
    {Q : List (List ℕ)} (hQ : Q ∈ vsQAPcs s Lb) (htop : vsWSp I.p (vsQD s) Q = ⊤) :
    vsTDom (vsTAlg (vsPBar hs (gens as))) := by
  obtain ⟨-, -, c, hc⟩ := (vsFEigL_pieces I.prime _ (vsQAFix_sq (s := s) Lb)).1 Q hQ
  have hsp := vsFAnnL_nil I.prime h.sq h.comm (vsTAlg (vsPBar hs (gens as))) h.memB
  rw [hsp] at hann
  have hN : ∀ y ∈ vsTAlg (vsPBar hs (gens as)), y ^ I.p = 0 → y = 0 := by
    intro y hy hyp
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ vsFAnn (vsTAlg (vsPBar hs (gens as))) := hann ▸ Submodule.mem_top
    rw [LinearMap.zero_apply]
    exact (mem_vsFAnn _ v).1 hv y hy hyp
  exact vsFField_of_top _ hN (vsQAFix s Lb) c h.fixSpan (hc.symm.trans htop)

/-- **Distinct pieces are disjoint.** If two entries had the same eigenvalue vector, the
dimensions of the entries would add up to more than `D`. -/
theorem vsQA_pcs_disj (h : VsQAHyp hs as Lb) (k₁ k₂ : Fin (vsQAPcs s Lb).length) (hij : k₁ ≠ k₂) :
    Disjoint (vsWSp I.p (vsQD s) (vsQAPcs s Lb)[k₁]) (vsWSp I.p (vsQD s) (vsQAPcs s Lb)[k₂]) := by
  classical
  set f := vsQAFix s Lb
  have hP := vsFEigL_pieces I.prime _ (vsQAFix_sq (s := s) Lb)
  have hC := vsFEigL_cnt I.prime _ (vsQAFix_sq (s := s) Lb)
  choose a ha0 using fun k : Fin (vsQAPcs s Lb).length => (hP.1 (vsQAPcs s Lb)[k] (List.getElem_mem k.2)).2.2
  have ha : ∀ k, vsWSp I.p (vsQD s) (vsQAPcs s Lb)[k] = vsFEig f (a k) := ha0
  have hB := vsTAlg_comm h.abNormal.2.2
  have hind := vsFEig_indep _ hB f (fun k => (h.fix k).1) (fun k => (h.fix k).2)
  have hsup := vsFEig_iSup _ hB f (fun k => (h.fix k).1) (fun k => (h.fix k).2)
  -- `a` is injective
  have hinj : a k₁ ≠ a k₂ := by
    intro he
    set g : (Fin (vsFFixL I.p (vsQD s) Lb).length → ZMod I.p) → ℕ := fun c => Module.finrank (ZMod I.p) (vsFEig f c)
    -- the sum over the image of `a` is `D`
    have himg : ⨆ c ∈ Finset.univ.image a, vsFEig f c = ⊤ := by
      rw [eq_top_iff, ← hsup]
      refine iSup_le fun c => ?_
      by_cases hc : vsFEig f c = ⊥
      · rw [hc]; exact bot_le
      · obtain ⟨Q, hQ, hQc0⟩ := hP.2 c hc
        have hQc : vsWSp I.p (vsQD s) Q = vsFEig f c := hQc0
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hQ
        have : vsFEig f c = vsFEig f (a ⟨k, hk⟩) := hQc.symm.trans (ha ⟨k, hk⟩)
        rw [this]
        exact le_iSup₂_of_le (a ⟨k, hk⟩) (Finset.mem_image_of_mem a (Finset.mem_univ _)) le_rfl
    have hD : ∑ c ∈ Finset.univ.image a, g c = vsQD s := by
      rw [← vsW_finrank_biSup hind, himg, finrank_top, Module.finrank_fin_fun]
    -- the sum over the entries is at most `D`
    have hsum : ∑ k : Fin (vsQAPcs s Lb).length, g (a k) ≤ vsQD s := by
      have e : ∀ k : Fin (vsQAPcs s Lb).length, g (a k) = (vsQAPcs s Lb)[k].length := fun k => by
        simp only [g]
        rw [← ha k, (hC.1 (vsQAPcs s Lb)[k] (List.getElem_mem k.2)).2.2]
      simp only [e]
      have e2 : ∑ k : Fin (vsQAPcs s Lb).length, (vsQAPcs s Lb)[k].length = ((vsQAPcs s Lb).map List.length).sum := by
        conv_rhs => rw [← @List.ofFn_getElem _ (vsQAPcs s Lb)]
        rw [List.map_ofFn, List.sum_ofFn]
        rfl
      rw [e2]; exact hC.2
    -- but the entries count `a i` twice
    have h1 : ∑ c ∈ (Finset.univ.erase k₂).image a, g c ≤ ∑ k ∈ Finset.univ.erase k₂, g (a k) :=
      Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
    have h2 : (Finset.univ.erase k₂).image a = Finset.univ.image a := by
      ext c
      rw [Finset.mem_image, Finset.mem_image]
      constructor
      · rintro ⟨k, -, rfl⟩; exact ⟨k, Finset.mem_univ _, rfl⟩
      · rintro ⟨k, -, rfl⟩
        by_cases hk : k = k₂
        · exact ⟨k₁, Finset.mem_erase.2 ⟨hij, Finset.mem_univ _⟩, he.trans (congrArg a hk.symm)⟩
        · exact ⟨k, Finset.mem_erase.2 ⟨hk, Finset.mem_univ _⟩, rfl⟩
    have h3 : ∑ k ∈ Finset.univ.erase k₂, g (a k) + g (a k₂) = ∑ k : Fin (vsQAPcs s Lb).length, g (a k) :=
      Finset.sum_erase_add _ _ (Finset.mem_univ k₂)
    have h4 : 0 < g (a k₂) := by
      simp only [g]
      rw [← ha k₂]
      exact Nat.pos_of_ne_zero fun h0 =>
        (hP.1 _ (List.getElem_mem k₂.2)).2.1 (Submodule.finrank_eq_zero.1 h0)
    rw [h2, hD] at h1
    omega
  rw [Submodule.disjoint_def]
  intro v hv1 hv2
  have hv1' : v ∈ vsFEig f (a k₁) := (ha k₁) ▸ hv1
  have hv2' : v ∈ vsFEig f (a k₂) := (ha k₂) ▸ hv2
  exact vsFEig_disjoint f hinj hv1' hv2'

/-! ### The permutation of the pieces by a generator -/

/-- The keys of the pieces. -/
noncomputable def vsQAKeys (s : VsQSt I) (Lb : List (List (List ℕ))) : List (List (List ℕ)) :=
  (vsQAPcs s Lb).map (vsWKey I.p (vsQD s))

/-- Where `g` sends piece `i`: the first piece whose key is the key of `Λ(g) P_i`. -/
noncomputable def vsQATbl (s : VsQSt I) (Lb : List (List (List ℕ))) (g : Perm (Fin I.n)) : List ℕ :=
  (List.range (vsQAPcs s Lb).length).map fun i =>
    (vsQAKeys s Lb).findIdx fun k => decide (k = vsWKey I.p (vsQD s)
      (vsWImg I.p (vsQD s) (vsQL (vsQLam s g)ᵀ) ((vsQAPcs s Lb).getD i [])))

theorem vsQA_lam_wM (g : Perm (Fin I.n)) : vsWM I.p (vsQD s) (vsQL (vsQLam s g)ᵀ) = vsQLam s g := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  rw [vsWM, vsFMatrix_vsQL, transpose_transpose]

theorem vsQA_lam_sq (g : Perm (Fin I.n)) : VsWSq I.p (vsQD s) (vsQL (vsQLam s g)ᵀ) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have := vsQL_sq (p := I.p) (vsQLam s g)ᵀ
  exact ⟨this.2, this.1⟩

/-- **The table.** Entry `i` is the `j` with `Λ(g) P_i = P_j`. -/
theorem vsQATbl_spec (h : VsQAHyp hs as Lb) {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs)
    {i : ℕ} (hi : i < (vsQAPcs s Lb).length) :
    ∃ hj : (vsQATbl s Lb g)[i]'(by simp [vsQATbl]; exact hi) < (vsQAPcs s Lb).length,
      (vsWSp I.p (vsQD s) (vsQAPcs s Lb)[i]).map (Matrix.toLin' (vsQLam s g)) =
        vsWSp I.p (vsQD s) (vsQAPcs s Lb)[(vsQATbl s Lb g)[i]'(by simp [vsQATbl]; exact hi)] := by
  have hP := vsFEigL_pieces I.prime _ (vsQAFix_sq (s := s) Lb)
  obtain ⟨Q', hQ', hmap⟩ := vsQA_piece_map h hg (List.getElem_mem hi)
  obtain ⟨j0, hj0, rfl⟩ := List.mem_iff_getElem.mp hQ'
  set img := vsWImg I.p (vsQD s) (vsQL (vsQLam s g)ᵀ) (vsQAPcs s Lb)[i]
  have himg : vsWSp I.p (vsQD s) img = vsWSp I.p (vsQD s) (vsQAPcs s Lb)[j0] := by
    rw [vsWImg_span (vsQA_lam_sq g), ← hmap]
    congr 1
    rw [vsWLin, vsQA_lam_wM]
  have hfit : ∀ Q ∈ vsQAPcs s Lb, VsWFit I.p (vsQD s) Q := fun Q hQ => (hP.1 Q hQ).1
  have hfimg : VsWFit I.p (vsQD s) img := vsWImg_fit I.prime.pos (vsQA_lam_sq g) _
  set q : List (List ℕ) → Bool := fun k => decide (k = vsWKey I.p (vsQD s) img)
  have hentry : (vsQATbl s Lb g)[i]'(by simp [vsQATbl]; exact hi) = (vsQAKeys s Lb).findIdx q := by
    simp only [vsQATbl, List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ hi]
    rfl
  have hex : ∃ k ∈ vsQAKeys s Lb, q k = true :=
    ⟨vsWKey I.p (vsQD s) (vsQAPcs s Lb)[j0], List.mem_map_of_mem (List.getElem_mem hj0), by
      simp only [q, decide_eq_true_eq]
      exact (vsWKey_eq_iff I.prime (hfit _ (List.getElem_mem hj0)) hfimg).2 himg.symm⟩
  have hlt := List.findIdx_lt_length.2 hex
  have hlen : (vsQAKeys s Lb).length = (vsQAPcs s Lb).length := List.length_map _
  have hj : (vsQATbl s Lb g)[i]'(by simp [vsQATbl]; exact hi) < (vsQAPcs s Lb).length := by
    rw [hentry]; omega
  refine ⟨hj, ?_⟩
  -- the found key is the key of the image
  have hq := List.findIdx_getElem (w := hlt)
  simp only [q, decide_eq_true_eq, vsQAKeys, List.getElem_map] at hq
  have hsp0 := (vsWKey_eq_iff I.prime (hfit _ (List.getElem_mem _)) hfimg).1 hq
  have hsp : vsWSp I.p (vsQD s) ((vsQAPcs s Lb)[(vsQAKeys s Lb).findIdx q]'(by omega)) =
      vsWSp I.p (vsQD s) img := hsp0
  -- so it is piece `j0`
  have hjj : (vsQAKeys s Lb).findIdx q = j0 := by
    by_contra hne
    have hd := vsQA_pcs_disj h ⟨(vsQAKeys s Lb).findIdx q, by omega⟩ ⟨j0, hj0⟩
      (fun he => hne (congrArg Fin.val he))
    simp only [Fin.getElem_fin] at hd
    rw [hsp, himg, disjoint_self] at hd
    exact (hP.1 _ (List.getElem_mem hj0)).2.1 hd
  have e : ∀ (k : ℕ) (hk : k < (vsQAPcs s Lb).length), k = j0 → (vsQAPcs s Lb)[k] = (vsQAPcs s Lb)[j0] := by
    rintro k hk rfl; rfl
  rw [e _ hj (hentry.trans hjj), ← hmap]

/-! ### The orbit sum of piece `0` -/

/-- **The algebra of `H` is spanned by the local matrices of `H`.** -/
theorem vsQ_adjoin_le_span (hs : VsQStOK s) {X : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)}
    (hX : X ∈ Algebra.adjoin (ZMod I.p) {X | ∃ g ∈ s.hs, vsQLam s g = X}) :
    X ∈ Submodule.span (ZMod I.p) {X | ∃ h ∈ gens s.hs, vsQLam s h = X} := by
  set V := Submodule.span (ZMod I.p) {X | ∃ h ∈ gens s.hs, vsQLam s h = X}
  have hmul : ∀ x ∈ V, ∀ y ∈ V, x * y ∈ V := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, hk, rfl⟩ := hy
        rw [← vsQLam_mul hs hh hk]
        exact Submodule.subset_span ⟨h * k, mul_mem hh hk, rfl⟩
      | zero => rw [mul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
    | zero => rw [zero_mul]; exact zero_mem _
    | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
    | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha
  induction hX using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact Submodule.subset_span ⟨g, Subgroup.subset_closure hg, rfl⟩
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, ← vsQLam_one hs]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨1, one_mem _, rfl⟩)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact hmul x hx y hy

/-- The pieces as joint eigenspaces, with distinct eigenvalue vectors. -/
theorem vsQA_pcs_eig (h : VsQAHyp hs as Lb) :
    ∃ a : Fin (vsQAPcs s Lb).length → (Fin (vsFFixL I.p (vsQD s) Lb).length → ZMod I.p),
      Function.Injective a ∧ ∀ k, vsWSp I.p (vsQD s) (vsQAPcs s Lb)[k] = vsFEig (vsQAFix s Lb) (a k) := by
  have hP := vsFEigL_pieces I.prime _ (vsQAFix_sq (s := s) Lb)
  choose a ha0 using fun k : Fin (vsQAPcs s Lb).length =>
    (hP.1 (vsQAPcs s Lb)[k] (List.getElem_mem k.2)).2.2
  have ha : ∀ k, vsWSp I.p (vsQD s) (vsQAPcs s Lb)[k] = vsFEig (vsQAFix s Lb) (a k) := ha0
  refine ⟨a, fun i j he => ?_, ha⟩
  by_contra hij
  have hd := vsQA_pcs_disj h i j hij
  rw [ha i, ha j, he, disjoint_self, ← ha j] at hd
  exact (hP.1 _ (List.getElem_mem j.2)).2.1 hd

/-- The images of piece `0` under the basis of the algebra of `H`. -/
noncomputable def vsQASpin (s : VsQSt I) (Lb : List (List (List ℕ))) : List (List ℕ) :=
  (vsQBm s).flatMap fun M => vsWImg I.p (vsQD s) M ((vsQAPcs s Lb).getD 0 [])

/-- The `B_H`-submodule spanned by piece `0`. -/
noncomputable def vsQAW (s : VsQSt I) (Lb : List (List (List ℕ))) : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p) :=
  Submodule.span (ZMod I.p) {w | ∃ X ∈ vsQBl s, ∃ u ∈ vsWSp I.p (vsQD s) ((vsQAPcs s Lb).getD 0 []), X *ᵥ u = w}

theorem vsQASpin_span : vsWSp I.p (vsQD s) (vsQASpin s Lb) = vsQAW s Lb := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, rfl⟩
    simp only [vsQASpin, List.mem_flatMap, vsWImg, List.mem_map] at hu
    obtain ⟨M, hM, v, hv, rfl⟩ := hu
    have hMs := vsQBm_sq s M hM
    refine Submodule.subset_span ⟨vsWM I.p (vsQD s) M, vsQBm_wM_mem s hM, vsWV I.p (vsQD s) v,
      vsWV_mem_vsWSp _ hv, ?_⟩
    rw [vsWV_img hMs.2 (fun r hr => (hMs.1 r hr).2.le), vsWLin, Matrix.toLin'_apply]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨X, hX, u, hu, rfl⟩
    rw [← vsQBm_mem s] at hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨M, hM, rfl⟩ := hX
      have hMs := vsQBm_sq s M hM
      induction hu using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨v, hv, rfl⟩ := hw
        refine Submodule.subset_span ⟨vsFRowMul I.p v M (vsWZ (vsQD s)), ?_, ?_⟩
        · simp only [vsQASpin, List.mem_flatMap, vsWImg, List.mem_map]
          exact ⟨M, hM, v, hv, rfl⟩
        · rw [vsWV_img hMs.2 (fun r hr => (hMs.1 r hr).2.le), vsWLin, Matrix.toLin'_apply]
      | zero => rw [mulVec_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
      | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ c ha
    | zero => rw [zero_mulVec]; exact zero_mem _
    | add X Y _ _ hX hY => rw [add_mulVec]; exact add_mem hX hY
    | smul c X _ hX => rw [smul_mulVec]; exact Submodule.smul_mem _ c hX

/-- The orbit sum is invariant under `H`. -/
theorem vsQAW_inv : ∀ g ∈ s.hs, ∀ w ∈ vsQAW s Lb, vsQLam s g *ᵥ w ∈ vsQAW s Lb := by
  intro g hg w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨X, hX, u, hu, rfl⟩ := hw
    refine Submodule.subset_span ⟨vsQLam s g * X, mul_mem (vsQLam_mem_Bl s (List.mem_cons_of_mem _ hg)) hX,
      u, hu, ?_⟩
    rw [mulVec_mulVec]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
  | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ c ha

theorem vsQAW_ge : vsWSp I.p (vsQD s) ((vsQAPcs s Lb).getD 0 []) ≤ vsQAW s Lb := fun u hu =>
  Submodule.subset_span ⟨1, (vsQBl s).one_mem, u, hu, one_mulVec u⟩

/-- **Transitivity.** If the orbit sum is everything, every piece is the image of piece `0` by
some element of `H`. -/
theorem vsQA_trans (h : VsQAHyp hs as Lb) (h0 : 0 < (vsQAPcs s Lb).length) (htop : vsQAW s Lb = ⊤)
    (j : Fin (vsQAPcs s Lb).length) :
    ∃ g ∈ gens s.hs, (vsWSp I.p (vsQD s) (vsQAPcs s Lb)[0]).map (Matrix.toLin' (vsQLam s g)) =
      vsWSp I.p (vsQD s) (vsQAPcs s Lb)[j] := by
  classical
  obtain ⟨a, hainj, ha⟩ := vsQA_pcs_eig h
  set f := vsQAFix s Lb
  have hB := vsTAlg_comm h.abNormal.2.2
  have hind := vsFEig_indep _ hB f (fun k => (h.fix k).1) (fun k => (h.fix k).2)
  -- the set of images of piece `0`
  set O : Set (Fin (vsQAPcs s Lb).length) := {k | ∃ g ∈ gens s.hs,
    (vsWSp I.p (vsQD s) (vsQAPcs s Lb)[0]).map (Matrix.toLin' (vsQLam s g)) = vsWSp I.p (vsQD s) (vsQAPcs s Lb)[k]}
  by_contra hj
  have hjO : j ∉ O := hj
  -- the orbit sum lies in the sum of the pieces of `O`
  have hle : vsQAW s Lb ≤ ⨆ c ∈ a '' O, vsFEig f c := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨X, hX, u, hu, rfl⟩
    rw [vsQBl_eq s hs] at hX
    have hX' := vsQ_adjoin_le_span hs hX
    have hu0 : u ∈ vsWSp I.p (vsQD s) (vsQAPcs s Lb)[0] := by
      rwa [List.getD_eq_getElem _ _ h0] at hu
    clear hX hu
    induction hX' using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨g, hg, rfl⟩ := hX
      obtain ⟨Q', hQ', hmap⟩ := vsQA_piece_map h hg (List.getElem_mem h0)
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hQ'
      have hkO : (⟨k, hk⟩ : Fin _) ∈ O := ⟨g, hg, hmap⟩
      have hv : vsQLam s g *ᵥ u ∈ vsWSp I.p (vsQD s) (vsQAPcs s Lb)[k] := by
        rw [← hmap]; exact ⟨u, hu0, by rw [Matrix.toLin'_apply]⟩
      have hv' : vsQLam s g *ᵥ u ∈ vsFEig f (a ⟨k, hk⟩) := (ha ⟨k, hk⟩) ▸ hv
      have hle1 : vsFEig f (a ⟨k, hk⟩) ≤ ⨆ c ∈ a '' O, vsFEig f c :=
        le_iSup₂_of_le (f := fun c (_ : c ∈ a '' O) => vsFEig f c) (a ⟨k, hk⟩) ⟨⟨k, hk⟩, hkO, rfl⟩ le_rfl
      exact hle1 hv'
    | zero => rw [zero_mulVec]; exact zero_mem _
    | add X Y _ _ hX hY => rw [add_mulVec]; exact add_mem hX hY
    | smul c X _ hX => rw [smul_mulVec]; exact Submodule.smul_mem _ c hX
  have hd := @iSupIndep.disjoint_biSup _ _ _ (fun c => vsFEig f c) hind (a j) (a '' O) (by
    rintro ⟨k, hk, he⟩
    exact hjO (hainj he ▸ hk))
  have htop' : (⨆ c ∈ a '' O, vsFEig f c) = ⊤ := top_le_iff.1 (htop ▸ hle)
  rw [htop', disjoint_top] at hd
  have hP := vsFEigL_pieces I.prime _ (vsQAFix_sq (s := s) Lb)
  exact (hP.1 _ (List.getElem_mem j.2)).2.1 ((ha j).trans hd)

end Pieces

end GI.Proved
