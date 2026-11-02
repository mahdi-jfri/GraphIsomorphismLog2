import Workspace.Impl.AggItemCiSojSpec

/-!
# The partition branch and the rectangle call preconditions

The balanced branch has singleton blocks. Its transporter is therefore exactly
that of the vertex coloring, so the existing colored-partition program applies.
For the other branches we record why the certificate and representation contracts
can be called. These facts do not need a bound on the raw binary palette.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance GI.PairRefinement Equiv Equiv.Perm
open GI.Cited (Val gens)

variable {q : ℕ}

/-- The vertex coloring of the balanced partition, including the omitted labels. -/
noncomputable def itcsBal (X : PairCfg q) (x₀ : Fin q) : Fin q → ℕ :=
  (X.balPart x₀).col

/-- Singleton blocks impose no further constraint beyond their colors. -/
theorem itcs_bal_iff (σ : Perm (Fin q)) (X Y : PairCfg q) (x₀ y₀ : Fin q) :
    σ • X.balPart x₀ = Y.balPart y₀ ↔ ∀ a, itcsBal Y y₀ (σ a) = itcsBal X x₀ a := by
  constructor
  · intro h a
    have hc := congrArg (fun z : ColPart (Fin q) => z.col (σ a)) h
    simpa only [ColPart.smul_col, Perm.inv_apply_self] using hc.symm
  · intro h
    apply ColPart.ext
    · funext a
      simp only [ColPart.smul_blk, PairCfg.balPart, Finset.map_singleton,
        Equiv.toEmbedding_apply, Perm.apply_inv_self]
    · funext a
      exact (h (σ⁻¹ a)).symm.trans (by rw [Perm.apply_inv_self]; rfl)

variable {Ω C : Type} {P : Params} {S : State Ω C}

/-- The model's balanced item, with the existing program's overcosets and generators. -/
theorem itcs_bal_item (L : GiantLabels S) (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q) :
    ∃ ovs, (objItem (P := P) (X.balPart x₀) (Y.balPart y₀) : AuxItem P S L).script =
        Script.done ⟨[], ovs⟩ ∧
      List.Forall₂ (asOvAt L)
        (itciOs (itcsBal X x₀) (itcsBal Y y₀) (itciOt (itcsBal X x₀))
          (evenStab (q := L.q) (X.balPart x₀))) ovs ∧
      ∀ o ∈ itciOs (itcsBal X x₀) (itcsBal Y y₀) (itciOt (itcsBal X x₀))
          (evenStab (q := L.q) (X.balPart x₀)),
        gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype :=
  itci_item L _ _ (fun σ => itcs_bal_iff σ X Y x₀ y₀)
    (fun σ => itcs_bal_iff σ X X x₀ x₀) (itciOt_spec _)

/-- The existing partition program applies to these exact vertex colors. -/
theorem itcs_bal_prog {Pg : Program} {Ii : ItciIdx} (h : ItciOk Pg Ii)
    (X Y : PairCfg q) (x₀ y₀ : Fin q) {M : ℕ}
    (hX : (encFun (itcsBal X x₀)).wt ≤ M) (hY : (encFun (itcsBal Y y₀)).wt ≤ M)
    (E₀ : Subgroup (alternatingGroup (Fin q))) :
    FunDet Pg Ii.f (.list [encFun (itcsBal X x₀), encFun (itcsBal Y y₀)])
      (itciOV (itciOs (itcsBal X x₀) (itcsBal Y y₀) (itciOt (itcsBal X x₀)) E₀))
      (itciFC M) :=
  itci_prog h _ _ hX hY E₀

/-- In the primitive unbalanced branch, the certificate required by the search exists. -/
theorem itcs_cert_exists {X : PairCfg q} (hX : X.Good deltaB) {x₀ : Fin q}
    (hx : x₀ ∈ X.fiber) (hp : PrimitiveColorCuts X.coloring false)
    (hb : ¬ ∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤
      etaB * X.fiber.card) :
    Nonempty (RectangleCertificate X.coloring false (X.idx hx) etaB) := by
  rcases primitive_entrance_alternative X.coloring (PairCfg.coloring_coherent hX) false
      (X.coloring_homogeneous false) (PairCfg.coloring_nontrivial hX false) hp (X.idx hx)
      etaB (by norm_num [etaB]) with h | h
  · exact False.elim (hb (fun i => by simpa only [colorClass_card] using h i))
  · exact h

/-- In the imprimitive branch, the component choice required by `SojChoice.imp` exists. -/
theorem itcs_imp_exists {X : PairCfg q} (hX : X.Good deltaB)
    (hp : ¬ PrimitiveColorCuts X.coloring false) : ∃ a b, ImpPair X a b := by
  obtain ⟨a, b, hab, -, hsz⟩ := nonprimitive_balanced_components X.coloring
    (PairCfg.coloring_coherent hX) false (X.coloring_homogeneous false) hp
  exact ⟨a, b, hab, hsz⟩

/-- The representation preconditions follow from the certificate and the size guard.
The threshold is precisely the failed pair-dispatch test. -/
theorem itcs_rect_conds {L : GiantLabels S} (X : PairCfg L.q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB)
    (hq : ¬ (L.q : ℝ) ≤ (S.N : ℝ) ^ P₀.α) (h3 : 3 ≤ (rectW X i₀ cert).card) :
    RectConds P₀ S L (rectW X i₀ cert) (rectR X i₀ cert) := by
  have hc : (0 : ℝ) * Fintype.card (Fin L.q) ≤ X.fiber.card := by simp
  obtain ⟨hd, -, -, ha, -⟩ := cert_facts (δ := 0) (β := 1) X.coloring false
    (X.emb rfl) cert (by norm_num [etaB]) (by norm_num [etaB]) hc (by norm_num [etaB])
  refine ⟨lt_of_not_ge hq, hd, h3, ?_, ?_⟩
  · exact ⟨_, Finset.mem_map_of_mem _
      ((mem_colorClass _ _ _ _ _).2 cert.rightPoint.property)⟩
  · simpa only [Fintype.card_fin] using ha

/-- The good source and fiber membership come from the round that supplies the objects. -/
theorem itcs_obj_good {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {L : SuppliedLabels S}
    {K : ItSCtx k S L} (hK : K.OK e c) (hc : K.case = .twoB ∨ K.case = .three)
    {b : Fin (P₀.κ + 1) → Fin L.q} {X Y : PairCfg L.q} {x₀ y₀ : Fin L.q}
    (ho : ItCfObjOf K b (.pair X x₀) (.pair Y y₀)) : X.Good deltaB ∧ x₀ ∈ X.fiber := by
  obtain ⟨Ag, hAg, ho, -, -⟩ := ho
  have hcase := itS_case_eq hK hAg
  have hg := Ag.out_good (hc.imp (fun h => hcase.trans h) (fun h => hcase.trans h)) (Ag.strY b)
  change (Ag.out (Ag.strX Ag.src) (Ag.strY b)).1.Good P₀.β at hg
  rw [ho] at hg
  exact hg

/-- The balanced branch is the partition item proved above. -/
theorem itcs_bal_script {k : ℕ} (e : Ω ≃ Fin k) {L : GiantLabels S}
    (ch : ItCfCh S L) (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q) (hx : x₀ ∈ X.fiber)
    (hp : PrimitiveColorCuts X.coloring false)
    (hb : ∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤ etaB * X.fiber.card) :
    itcsSb e X Y x₀ y₀ ch =
      (objItem (P := P₀) (X.balPart x₀) (Y.balPart y₀) : AuxItem P₀ S L).script := by
  classical
  simp only [itcsSb, sojItem, dif_pos hx, if_pos hp, if_pos hb]

/-- All context preconditions of the representation contract are supplied at this call.
The caller only has to establish the rectangle conditions, for example by `itcs_rect_conds`. -/
theorem itcs_rep_call {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {L : SuppliedLabels S}
    {K : ItSCtx k S L} (hK : K.OK e c) (hinj : Function.Injective c)
    {Pg : Program} {fr : ℕ} {Br : ℕ → ℕ} (hr : RcRepSpec Pg fr Br) :
    ∃ Rf : ∀ W R : Finset (Fin L.q), RectConds P₀ S L.toGiantLabels W R →
        RectRep P₀ S L.toGiantLabels W R,
      ∀ (W R : Finset (Fin L.q)) (h : RectConds P₀ S L.toGiantLabels W R),
        FunAll Pg fr (rcRepIn K.sv L.q K.ps W R) fun w cost =>
          ∃ hs : List (Perm (Fin k) × Perm (Fin L.q)),
            w = rcRepVal e (Rf W R h) hs ∧ PairGens e L.toGiantLabels (Rf W R h).H hs ∧
              hs.length ≤ k ^ 2 ∧ cost ≤ Br (rcRepIn K.sv L.q K.ps W R).wt ∧
              w.wt ≤ Br (rcRepIn K.sv L.q K.ps W R).wt :=
  hr e c S K.sv L.toGiantLabels K.Ag₀.toAggregationData K.ps hinj hK.can hK.hps

/-- The certificate program fixes one certificate function for every branch.
Fiber membership is the only input precondition of this call. -/
theorem itcs_cert_call {Pg : Program} {fc : ℕ} {Bc : ℕ → ℕ}
    (hc : RcCertSpec Pg fc Bc) :
    ∃ cf : RcCertFn, ∀ {q : ℕ} (X : PairCfg q) (x₀ : Fin q) (hx : x₀ ∈ X.fiber)
      (hcert : Nonempty (RectangleCertificate X.coloring false (X.idx hx) etaB)),
      FunAll Pg fc (rcCertIn X x₀) fun w cost =>
        w = rcCertVal X (X.idx hx) (cf X (X.idx hx) hcert) ∧
          cost ≤ Bc (rcCertIn X x₀).wt ∧ w.wt ≤ Bc (rcCertIn X x₀).wt := by
  obtain ⟨cf, hc⟩ := hc
  exact ⟨cf, fun X x₀ hx hcert => (hc X x₀ hx).mono fun _ _ h => ⟨h.1 hcert, h.2.2⟩⟩

/-- The balance test can compare integer counts, with no real arithmetic. -/
theorem itcs_bal_count_iff (n m : ℕ) :
    (m : ℝ) ≤ etaB * n ↔ 4 * m ≤ 3 * n := by
  have he : (m : ℝ) ≤ etaB * n ↔ (4 : ℝ) * m ≤ 3 * n := by
    unfold etaB
    constructor <;> intro h <;> linarith
  rw [he]
  exact_mod_cast (Iff.rfl : 4 * m ≤ 3 * n ↔ 4 * m ≤ 3 * n)

end GI.Impl
