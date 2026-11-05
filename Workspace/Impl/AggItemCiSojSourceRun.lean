module

public import Workspace.Impl.AggItemCiSojSourceBudget
public import Workspace.Impl.AggItemCiSojCertFixed
public import Workspace.Impl.AggItemCiSojRawPost

@[expose] public section

/-! # The full first-rectangle start contract -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val gens)
open Classical

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
/-- The actual source dispatch satisfies the complete first-rectangle start
contract. All three cases use the same fixed functions and the same kept set.
The own cost fits growth stage 67, hence the common polynomial item bound. -/
theorem itcs_source_run (I : Iface) {Pg : Program} {Funs₀ : Funs} {A : itcsSourceIdx}
    (hA : itcsSourceOk Pg A) {e : Ω ≃ Fin k} {c : C → ℕ} {sv lv : Val}
    (hcall : AsCall I Pg Funs₀ e c S sv lv L) (K : ItSCtx k S L) (hK : K.OK e c)
    (hcase : K.case=.twoB ∨ K.case=.three) (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (cf : RcCertFn) (hCert : itcsCertFnOK Pg A.cert Bc cf)
    (b : Fin (P₀.κ+1) → Fin L.q) (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q)
    (ho : ItCfObjOf K b (.pair X x₀) (.pair Y y₀)) (hlarge : ¬(L.q : ℝ)≤(S.N : ℝ)^P₀.α)
    (w : Val) (E : Set (ItCfCh S L.toGiantLabels)) (hKeep : itcsKeep Pg A.rect.rep Br cf e c K w E) :
    let B := itcsXs pf Bc Br hBc hBr (I.inW .giant S)
    FunAll Pg A.f (.list [K.v,stTv b,itCfOutV (.pair X x₀),itCfOutV (.pair Y y₀),w]) fun w' cost =>
      cost≤ B ∧ ItCfIPost (itcsRel I Pg A.rect.rep Br cf pf Bc hBc hBr) e c S L K b (.pair X x₀) (.pair Y y₀) E
        (itcsSb e X Y x₀ y₀) B B w' := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨rfl,rf,hRep,rfl⟩ := hKeep
  let E : Set (ItCfCh S L.toGiantLabels) := {(itcsChoices cf,rf)}
  have keep : itcsKeep Pg A.rect.rep Br cf e c K (.list []) E := ⟨rfl,rf,hRep,rfl⟩
  let W₀ := I.inW .giant S
  let G := itcsGrow pf Bc Br hBc hBr
  let BB := itcsXs pf Bc Br hBc hBr W₀
  let P : Val → Prop := ItCfIPost (itcsRel I Pg A.rect.rep Br cf pf Bc hBc hBr) e c S L K b
    (.pair X x₀) (.pair Y y₀) E (itcsSb e X Y x₀ y₀) BB BB
  obtain ⟨hX,hx⟩ := itcs_obj_good hK hcase ho
  have cols := ho
  obtain ⟨_,_,_,colX,colY⟩ := cols
  have size := itS_size I Pg Funs₀ hcall
  have hq : L.q≤2*W₀+3 := by dsimp only [W₀]; omega
  have leaf := itcs_leaf_bounds pf Bc Br hBc hBr W₀ k L.q (2*L.q^P₀.κ) (itcs_parent_sizes I hcall).1 hq
    (Nat.mul_le_mul_left 2 size.2.2.1)
  have frontCall := itcs_front_prog hA.comp hA.front hA.rect.query.rng hA.fiber hA.rect.fiberB
    hA.find hA.test hA.pc hA.size X x₀ hX hx colX
  have pcBound := itcs_pc_cost_stage I hcall pf Bc Br hBc hBr ho frontCall
  have balCall := itcs_bal_table hA.rect.bal hA.rect.balB hA.rect.fiberB X x₀ colX
  have btCall := itcs_bal_test_prog hA.baltest hA.baltestB hA.comp.c1.sz hA.comp.c1.cnt X x₀ hx colX
  let j := itcsImpScan X
  let Bal : Prop := ∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤ etaB*X.fiber.card
  let g : ℕ := if Bal then 1 else 0
  have balyes (hg : g≠0) : Bal := by
    by_contra hn
    simp only [g,if_neg hn] at hg
    exact hg rfl
  have balno (hg : g=0) : ¬Bal := by
    intro hh
    simp only [g,if_pos hh] at hg
    exact Nat.one_ne_zero hg
  have primitive (hn : ¬j<X.fiber.card*X.fiber.card) : PrimitiveColorCuts X.coloring false := by
    by_contra hh
    exact hn ((itcs_imp_scan_lt X hX hx).2 hh)
  have script {ovs : List (Perm Ω × Subgroup (Perm Ω))}
      (hs : (sojItem (RectOracle.ofReps rf) (itcsChoices cf) X Y x₀ y₀).script=.done ⟨[],ovs⟩) :
      ∀ch∈E,itcsSb e X Y x₀ y₀ ch=.done ⟨[],ovs⟩ := by
    intro ch hch
    rw [Set.mem_singleton_iff] at hch
    subst ch
    exact hs
  have out {ovs : List (Perm Ω × Subgroup (Perm Ω))} {os : List (LcOver L.q)}
      (ho : List.Forall₂ (asOvAt L.toGiantLabels) os ovs)
      (hg : ∀o∈os,gens o.2.2=o.2.1.map (alternatingGroup (Fin L.q)).subtype) :
      ItSOut e L.toGiantLabels ⟨[],ovs⟩ [] os :=
    ⟨ho,rfl,fun i hi _ => (Nat.not_lt_zero i hi).elim,hg⟩
  obtain ⟨v,iovs,pcCall,impCall,impPost⟩ : ∃ v iovs : Val,
      (j<X.fiber.card*X.fiber.card → FunDet Pg A.pc
        (.list [.list [rcColVal X,itcqFV X,.nat X.fiber.card],.nat j]) v (G^[3] (W₀+100))) ∧
      (j<X.fiber.card*X.fiber.card → FunDet Pg A.imp (.list [rcCertIn X x₀,rcCertIn Y y₀,v]) iovs
        (itcsImpPartC L.q (2*L.q^P₀.κ))) ∧
      (j<X.fiber.card*X.fiber.card → P (itcsResV iovs)) := by
    by_cases hj : j<X.fiber.card*X.fiber.card
    · have hn := (itcs_imp_scan_lt X hX hx).1 hj
      let himp := (itcs_imp_cut_iff X hX hx).2 hn
      obtain ⟨ovs,os,hs,hov,hgens,hprog⟩ := itcs_soj_imp_raw hA.comp hA.imp hA.min hA.minB hA.rect.fiberB
        (RectOracle.ofReps rf) cf X Y x₀ y₀ hX hx colX colY hn
      have hpc := (itcs_imp_color_prog hA.pc X himp).mono pcBound
      refine ⟨.nat (itcsImpValue X himp),itciOV os,fun _ => hpc,fun _ => hprog,fun _ => ?_⟩
      exact itcs_raw_done_post (itcsRel I Pg A.rect.rep Br cf pf Bc hBc hBr) e c K b (.pair X x₀) (.pair Y y₀)
        E (itcsSb e X Y x₀ y₀) ovs os _ keep (script hs) (out hov hgens) hprog pf Bc Br hBc hBr W₀
        (i:=1) (by decide) leaf.imppart
    · exact ⟨.list [],.list [],fun h => (hj h).elim,fun h => (hj h).elim,fun h => (hj h).elim⟩
  obtain ⟨povs,partCall,partPost⟩ : ∃ povs : Val,
      (¬j<X.fiber.card*X.fiber.card → g≠0 → FunDet Pg A.part (.list [rcCertIn X x₀,rcCertIn Y y₀]) povs
        (itcsBalPartC L.q (2*L.q^P₀.κ))) ∧
      (¬j<X.fiber.card*X.fiber.card → g≠0 → P (itcsResV povs)) := by
    by_cases hn : ¬j<X.fiber.card*X.fiber.card
    · by_cases hg : g≠0
      · obtain ⟨ovs,os,hs,hov,hgens,hprog⟩ := itcs_soj_bal_raw hA.rect.part hA.part hA.rect.query.rng
          hA.rect.bal hA.rect.balB hA.rect.fiberB (RectOracle.ofReps rf) (itcsChoices cf)
          X Y x₀ y₀ hx (primitive hn) (balyes hg) colX colY
        refine ⟨itciOV os,fun _ _ => hprog,fun _ _ => ?_⟩
        exact itcs_raw_done_post (itcsRel I Pg A.rect.rep Br cf pf Bc hBc hBr) e c K b (.pair X x₀) (.pair Y y₀)
          E (itcsSb e X Y x₀ y₀) ovs os _ keep (script hs) (out hov hgens) hprog pf Bc Br hBc hBr W₀
          (i:=1) (by decide) leaf.balpart
      · exact ⟨.list [],fun _ h => (hg h).elim,fun _ h => (hg h).elim⟩
    · exact ⟨.list [],fun h _ => (hn h).elim,fun h _ => (hn h).elim⟩
  let RR : Val → Prop := fun cv => ∃ hc : Nonempty (RectangleCertificate X.coloring false (X.idx hx) etaB),
    cv=rcCertVal X (X.idx hx) (cf X (X.idx hx) hc)
  have certCall (hn : ¬j<X.fiber.card*X.fiber.card) (hg : g=0) :
      FunAll Pg A.cert (rcCertIn X x₀) (fun cv cost => RR cv ∧ cost≤ Bc (rcCertIn X x₀).wt) := by
    have he := itcs_cert_exists hX hx (primitive hn) (balno hg)
    exact (hCert X x₀ hx he).mono fun cv cost ⟨hv,hc,_⟩ => ⟨⟨he,hv⟩,hc⟩
  have rectCall (cv : Val) (hn : ¬j<X.fiber.card*X.fiber.card) (hg : g=0) (hr : RR cv) :
      FunAll Pg A.rect.f (.list [.list [K.v,stTv b,itCfOutV (.pair X x₀),itCfOutV (.pair Y y₀),.list []],
        itcqFV X,encFun (itcsBal X x₀),cv]) (fun w cost => P w ∧ cost≤ G^[66] (W₀+100)) := by
    obtain ⟨hcert,rfl⟩ := hr
    exact itcs_rect_global I hA.rect hcall K hK hcall.good pf Bc Br hBc hBr cf b X Y x₀ y₀ ho hX hx
      (primitive hn) (balno hg) hlarge hcert (cf X (X.idx hx) hcert) rfl E rf keep rfl hRep
  let xc := [rcColVal X,Val.nat X.j,Val.nat x₀]
  let yc := [rcColVal Y,Val.nat Y.j,Val.nat y₀]
  let rows := (List.finRange L.q).map fun a => encFun (X.col a)
  let fl := ((itciFl X.fiber).map Fin.val).map Val.nat
  have flen : fl.length=X.fiber.card := by simp only [fl,List.length_map,itciFl_length]
  have rlen : rows.length=L.q := by simp only [rows,List.length_map,List.length_finRange]
  have he : boolVal (decide Bal)=Val.nat g := by
    by_cases hh : Bal <;> simp [boolVal,g,hh]
  have testCall : FunDet Pg A.baltest (.list [.list [encFun (itcsBal X x₀),.nat X.fiber.card],itcqFV X])
      (.nat g) (itcsBTC L.q (2*L.q^P₀.κ)) := by rw [←he]; exact btCall
  have run := itcs_start_prog hA.body K.v (stTv b) (.list []) xc yc rows fl j g v iovs povs
    (natList (List.range L.q)) (encFun (itcsBal X x₀)) rfl RR P frontCall
    (fun h => by simpa only [flen,fl,itcqFV,natList,rows,rcColVal] using pcCall (by simpa only [flen] using h))
    (fun h => impCall (by simpa only [flen] using h))
    (fun h => impPost (by simpa only [flen] using h))
    (by simpa only [rlen] using range_det hA.rect.query.rng L.q) balCall
    (by simpa only [flen,fl,itcqFV,natList] using testCall)
    (fun hn hg => partCall (by simpa only [flen] using hn) hg)
    (fun hn hg => partPost (by simpa only [flen] using hn) hg)
    (fun hn hg => certCall (by simpa only [flen] using hn) hg)
    (fun cv hn hg hr => rectCall cv (by simpa only [flen] using hn) hg hr)
  have own := itcs_source_own_stage I hcall hK pf Bc Br hBc hBr ho
  have total := own.trans (itcs_budget_iter_le pf Bc Br hBc hBr W₀ (i:=67) (by decide))
  exact run.mono fun w cost ⟨hp,hc⟩ => ⟨hc.trans total,hp⟩

end GI.Impl
