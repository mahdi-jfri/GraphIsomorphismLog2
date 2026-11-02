import Workspace.Impl.AggItemCfOb

/-!
# Cases 2b and 3: the case contract

**`itS_c23_caseOK`**: the init `itCfIF` and the branch step `itCfBF` of Cases 2b/3 meet
`ItSCaseOK … (fun a => a = .twoB ∨ a = .three) f0 fb (itCfX Co Do c₂ k₂ Xt)`, for every
interface `I`, from
* the object stage `ItCfObjSpec Pg fcol forb fdes Co Do` and the item stage
  `ItCfItemSpec I Pg F fi fs fk Xt` at index parameters;
* the cited `KaryRefinement 2` at a primitive index `j` (`c₂, k₂` are the constants of its
  primitive);
* the library functions at index parameters (`find`, `eqNats`, `replicate`, `range`, `map`,
  `append`).

`itCfX_pbu` (`AggItemCfRel.lean`): the bound is polynomial when `Xt` is.

The kept value `[wO, wI]` carries the cache of binary values from one branch to the next; the
rounds of a kept value are those whose joint refinement `hK` agrees with the cache
(`itCfD`). The binary values are results of the call, so the program never needs the model's
`hK`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring KaryRefinement)

variable {Ω C : Type} {k : ℕ}

theorem itCf_shape_of_post {RI : ItCfIRel} {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
    {L : SuppliedLabels S} {K : ItSCtx k S L} {b : Fin (P₀.κ + 1) → Fin L.q} {oX oY : CfgOut L.q}
    {E : Set (ItCfCh S L.toGiantLabels)} {sb : ItCfCh S L.toGiantLabels → Script (Branches Ω)}
    {f B : ℕ} {r : Val} (h : ItCfIPost RI e c S L K b oX oY E sb f B r) : ItCfShape r := by
  rcases h with ⟨_, pcs, os, wI, _, rfl, -⟩ |
    ⟨-, m, _, _, _, _, _, _, arg, kst, _, _, -, -, -, -, rfl, -⟩
  · exact Or.inr ⟨_, _, _, rfl⟩
  · exact Or.inl ⟨_, _, _, rfl⟩

theorem itCfStC_mono {X X' Bo Bs : ℕ} (h : X ≤ X') : itCfStC X Bo Bs ≤ itCfStC X' Bo Bs := by
  unfold itCfStC; omega

theorem itCfCtC_mono {X X' Bk : ℕ} (h : X ≤ X') : itCfCtC X Bk ≤ itCfCtC X' Bk := by
  unfold itCfCtC
  have := itCfWrC_mono (show 4 * (X + Bk) + 6 ≤ 4 * (X' + Bk) + 6 by omega)
  omega

variable (I : Iface) (Pg : Program)

set_option maxHeartbeats 8000000 in
/-- **The case contract of Cases 2b and 3.** -/
theorem itS_c23_caseOK {F : Funs} {f0 fb st ct ob o2 o3 wr grp rb mp sf app fcol forb fdes fd kt
      eqn ref brep j fi fs fk Co Do : ℕ} {Xt : ℕ → ℕ}
    (hobj : ItCfObjSpec Pg fcol forb fdes Co Do) (hitem : ItCfItemSpec I Pg F fi fs fk Xt)
    (h2 : KaryRefinement 2) (hj : Pg.prims[j]? = some (karyRefinementPrim h2))
    (hf0 : Pg.funs[f0]? = some (itCfIF grp fcol fi)) (hfb : Pg.funs[fb]? = some (itCfBF st ct))
    (hst : Pg.funs[st]? = some (itCfStF ob fs wr)) (hct : Pg.funs[ct]? = some (itCfCtF fk wr))
    (hwr : Pg.funs[wr]? = some itCfWrF) (hob : Pg.funs[ob]? = some (itCfObF o2 o3))
    (ho2 : Pg.funs[o2]? = some (itCfO2F fcol fd ref forb))
    (ho3 : Pg.funs[o3]? = some (itCfO3F fdes P₀.κ))
    (hgrp : Pg.funs[grp]? = some (itGrpF rb mp app)) (hrb : Pg.HasAt rb (rangeFuns rb))
    (hmp : Pg.HasAt mp (mapFuns mp sf)) (hsf : Pg.funs[sf]? = some itSndF)
    (happ : Pg.HasAt app (appendFuns app))
    (hfd : Pg.HasAt fd (findFuns fd kt)) (hkt : Pg.funs[kt]? = some (itCfKeyF eqn))
    (heqn : Pg.HasAt eqn (eqNatsFuns eqn)) (href : Pg.funs[ref]? = some (stRefF brep j))
    (hrep : Pg.HasAt brep (replicateFuns brep)) :
    ItSCaseOK I Pg F (fun a => a = .twoB ∨ a = .three) f0 fb
      (itCfX Co Do (karyRefinementPrim h2).c (karyRefinementPrim h2).k Xt) := by
  obtain ⟨RI, hRI⟩ := hitem
  refine ⟨itCfRel I RI Xt, fun {Ω C k} e c S sv lv L hc K hK hcs => ?_⟩
  have hA := hRI e c S sv lv L hc K hK hcs
  obtain ⟨hkq, hκ, hq, hq0, -, hκq⟩ := itS_size I Pg F hc
  have hvw := itS_vW I Pg F hc hK
  have hk64 : P₀.κ = 64 := rfl
  -- the pieces of the bound
  have hX : itCfX Co Do (karyRefinementPrim h2).c (karyRefinementPrim h2).k Xt (I.inW .giant S) =
      itCfRB (I.inW .giant S) (Xt (I.inW .giant S)) + Xt (I.inW .giant S) +
        itCfSB Co Do (karyRefinementPrim h2).c (karyRefinementPrim h2).k (I.inW .giant S)
          (Xt (I.inW .giant S)) + itCfIB Co Do (I.inW .giant S) (Xt (I.inW .giant S)) + 10 := rfl
  rw [hX]
  have hKR : itCfKB (I.inW .giant S) (Xt (I.inW .giant S)) + 10 ≤
      itCfRB (I.inW .giant S) (Xt (I.inW .giant S)) := by unfold itCfRB; omega
  have hTK : Xt (I.inW .giant S) ≤ itCfKB (I.inW .giant S) (Xt (I.inW .giant S)) := by
    unfold itCfKB; omega
  have hWK : itCfWOB (I.inW .giant S) ≤ itCfKB (I.inW .giant S) (Xt (I.inW .giant S)) := by
    unfold itCfKB; omega
  have hGq : 2 * I.inW .giant S + 3 + 1 ≤ itCfG (I.inW .giant S) := by unfold itCfG; omega
  have hG2 : 5 * (2 * I.inW .giant S + 3 + 1) ^ 2 ≤ 5 * itCfG (I.inW .giant S) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hGq 2)
  have hRBv : 2 * (itSVB (I.inW .giant S) + 5 * itCfG (I.inW .giant S) ^ 2 +
      itCfKB (I.inW .giant S) (Xt (I.inW .giant S))) + 7 ≤
      itCfRB (I.inW .giant S) (Xt (I.inW .giant S)) := by unfold itCfRB; omega
  refine ⟨?_, fun w D h => ?_, fun w D h => ?_, fun b w D h => ?_, fun b bst D sb f h => ?_,
    fun b bst D sb f h => ?_⟩
  · -- init
    have hfxw : (Val.list (K.fx.map pairV)).wt ≤ itSVB (I.inW .giant S) := by
      have ev := itCf_v_eq K
      have w1 : (Val.list (K.fx.map pairV)).wt < K.v.wt := by
        rw [ev]
        exact lt_trans (wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self)))) (wt_le_wt_list List.mem_cons_self)
      omega
    have hfyw : (Val.list (K.fy.map pairV)).wt ≤ itSVB (I.inW .giant S) := by
      have ev := itCf_v_eq K
      have w1 : (Val.list (K.fy.map pairV)).wt < K.v.wt := by
        rw [ev]
        exact lt_trans (wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
          (wt_le_wt_list List.mem_cons_self)
      omega
    have hqS : L.q ≤ itSVB (I.inW .giant S) := by
      have : 2 * I.inW .giant S + 3 + 1 ≤ (2 * I.inW .giant S + 3 + 1) ^ 2 :=
        Nat.le_self_pow (by norm_num) _
      unfold itSVB; omega
    have hgx := it_grp_spec hgrp hrb hmp hsf happ K.fx hfxw hqS
    have hgy := it_grp_spec hgrp hrb hmp hsf happ K.fy hfyw hqS
    have hgw := it_grp_wt K.fx hfxw hqS
    have hcolw : (itCfColIn (K.fx.map Prod.snd) (itCfSrc K)).wt ≤
        1000 * itCfG (I.inW .giant S) ^ 3 := by
      have ev := itCf_v_eq K
      have wsrc : (stTv (itCfSrc K)).wt < K.v.wt := by rw [ev]; exact wt_le_wt_list (by simp)
      have h3 := wt_list3_le (.nat L.q) (encGroup (K.fx.map Prod.snd)) (stTv (itCfSrc K))
      have wq : (Val.nat L.q).wt ≤ L.q + 2 := by
        have := GI.Machine.len_le_self L.q; simp only [wt_nat]; omega
      have p3 : (itSVB (I.inW .giant S) + 1) ^ 3 ≤ itCfG (I.inW .giant S) ^ 3 :=
        Nat.pow_le_pow_left (by unfold itCfG; omega) 3
      have p13 : itCfG (I.inW .giant S) ≤ itCfG (I.inW .giant S) ^ 3 :=
        Nat.le_self_pow (by norm_num) _
      have hGd : itCfG (I.inW .giant S) = itSVB (I.inW .giant S) + 2 * I.inW .giant S + 5 := rfl
      unfold itCfColIn
      omega
    have hcol : FunDet Pg fcol (itCfColIn (K.fx.map Prod.snd) (itCfSrc K))
        (encKColoring (itCfcX K)) (itCfB Co Do (1000 * itCfG (I.inW .giant S) ^ 3)) :=
      (hobj.col (K.fx.map Prod.snd) (itCfSrc K)).mono fun w cst h =>
        ⟨h.1, h.2.trans (itCfB_mono hcolw)⟩
    have hca0 : ItCfCache K [] := ⟨List.nodup_nil, fun a ha => absurd ha (List.not_mem_nil)⟩
    have hwO0 := itCf_wO_wt I Pg F hc hK hca0
    rw [itCf_v_eq K]
    refine (it_cfI_spec hf0 K.sv (.list (K.ps.map pairV)) (.list (K.fx.map pairV))
      (.list (K.fy.map pairV)) (stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ))
      (.list [encKColoring K.d, encKColoring K.d']) (.nat (AggCase.code K.case))
      (stTv (itCfSrc K)) _ _ _ k L.q hgx hgy hcol (Qi := fun w => ∃ E, RI.Ki e c S L K w E)
      (Bi := Xt (I.inW .giant S)) (hA.init.mono fun w cst ⟨E, hE, hc'⟩ => ⟨⟨E, hE⟩, hc'⟩)).mono
      fun w cost ⟨wI, ⟨E, hKi⟩, hw, hcost⟩ => ⟨itCfD K [] E, itCfD_sub_base K [] E,
        ⟨?_, [], wI, E, hw, hca0, hKi, rfl⟩, ?_⟩
    · have := hA.wtK wI E hKi
      have h2' := wt_list2_le (itCfWOK K []) wI
      have : w = .list [itCfWOK K [], wI] := hw
      rw [this]
      unfold itCfKB
      omega
    · have e : (Val.list [.list [K.sv, .list [.nat k, .nat L.q], .list (K.ps.map pairV),
          .list (K.fx.map pairV), .list (K.fy.map pairV),
          stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)],
          .list [encKColoring K.d, encKColoring K.d'], .nat (AggCase.code K.case),
          stTv (itCfSrc K)]).wt = K.v.wt := rfl
      rw [e] at hcost
      have : itCfIC K.v.wt (itGrpC (itSVB (I.inW .giant S)))
          (itCfB Co Do (1000 * itCfG (I.inW .giant S) ^ 3)) (Xt (I.inW .giant S)) ≤
          itCfIB Co Do (I.inW .giant S) (Xt (I.inW .giant S)) := by
        unfold itCfIB itCfIC; omega
      omega
  · -- ne
    obtain ⟨-, cache, wI, E, -, hca, hKi, rfl⟩ := h
    exact itCfD_nonempty hK hca (hA.ne wI E hKi)
  · -- wtK
    have := h.1
    omega
  · -- start
    have h3 := wt_list3_le K.v (stTv b) w
    have htb : (stTv b).wt ≤ 5 * (2 * I.inW .giant S + 3 + 1) ^ 2 :=
      wt_stTv_le b (by omega) (by omega)
    have hw := h.1
    exact ⟨by omega, Or.inl ⟨w, rfl, h, rfl, by omega⟩⟩
  · -- wtR
    have := h.1
    omega
  -- the step
  obtain ⟨hbw, ⟨w, rfl, hKc, rfl, hf⟩ | ⟨cache, kst, u, E, oX, oY, sbI, fI, rfl, hca, hRi, hfI,
    rfl, hsb⟩⟩ := h
  · -- the start of a branch
    obtain ⟨hww, cache, wI, E, rfl, hca, hKi, rfl⟩ := hKc
    have hob' := it_cfOb_start I Pg F hob ho2 ho3 hobj hfd hkt heqn h2 href hrep hj hc hK hcs
      (Xt (I.inW .giant S)) hca b
    refine (it_cfB_spec hfb [K.v, stTv b, .list [itCfWOK K cache, wI]]
      (Q := fun w cst => ItSBrPost (itCfRel I RI Xt) e c S L K b (itCfD K cache E)
        (fun Ag => (Ag.items b).script) f _ w ∧ w.wt < cst ∧
        cst ≤ itCfStC (itCfRB (I.inW .giant S) (Xt (I.inW .giant S)))
          (itCfBo Co Do (karyRefinementPrim h2).c (karyRefinementPrim h2).k (I.inW .giant S)
            (Xt (I.inW .giant S))) (Xt (I.inW .giant S))) (fun _ => ?_)
      (fun h => absurd rfl h)).mono fun w cost ⟨c', ⟨hpost, hwc, hc'⟩, hcost⟩ => ⟨?_, hpost⟩
    · refine (it_cfSt_spec hst hwr K.v (stTv b) (itCfWOK K cache) wI
        (Bs := Xt (I.inW .giant S))
        (Qo := fun oXv oYv wO' => ItCfObQ K b cache oXv oYv wO')
        (Qs := fun oXv oYv wO' r => ∃ (oX oY : CfgOut L.q) (cache' : List (ItCfEnt L.q)),
          oXv = itCfOutV oX ∧ oYv = itCfOutV oY ∧ wO' = itCfWOK K cache' ∧ ItCfCache K cache' ∧
          (∀ a ∈ cache, a ∈ cache') ∧ (∀ (E' : Set (ItCfCh S L.toGiantLabels)),
            ∀ Ag ∈ itCfD K cache' E', Ag.out (Ag.strX Ag.src) (Ag.strY b) = (oX, oY)) ∧
          ItCfIPost RI e c S L K b oX oY E (itCfSb e oX oY) (Xt (I.inW .giant S))
            (Xt (I.inW .giant S)) r)
        hob' fun oXv oYv wO' hq => ?_).wt_lt.mono
        fun w cst ⟨⟨oXv, oYv, wO', r, _, ⟨oX, oY, cache', _, _, hwO', hca', hsub, hout, hpost⟩,
          hwr', hcs'⟩, hwc⟩ => ⟨?_, hwc, ?_⟩
      · obtain ⟨oX, oY, cache', rfl, rfl, rfl, hca', hsub, hout, hcX, hcY⟩ := hq
        obtain ⟨Ag₁, hAg₁⟩ := itCfD_nonempty hK hca' (hA.ne wI E hKi)
        refine (hA.start b oX oY wI E ⟨Ag₁, hAg₁.1, hout E Ag₁ hAg₁, hcX, hcY⟩ hKi).mono
          fun r cst ⟨hcs', hp⟩ => ⟨⟨oX, oY, cache', rfl, rfl, rfl, hca', hsub, hout, hp⟩,
            itCf_shape_of_post hp, hcs'⟩
      · -- the branch output
        subst hwO'
        exact itCf_post I hK hca' (itCfD_mono K hsub subset_rfl)
          (fun Ag hAg => itCf_script hK hAg.1 hcs b (hout E Ag hAg)) (by omega) (by omega)
          (itCf_wO_wt I Pg F hc hK hca') hA.wtK (hA.wtR b oX oY) hpost hwr'
      · exact hcs'.trans (itCfStC_mono hbw)
    · -- the cost
      have : 3 * itCfStC (itCfRB (I.inW .giant S) (Xt (I.inW .giant S)))
          (itCfBo Co Do (karyRefinementPrim h2).c (karyRefinementPrim h2).k (I.inW .giant S)
            (Xt (I.inW .giant S))) (Xt (I.inW .giant S)) +
          100 * (itCfRB (I.inW .giant S) (Xt (I.inW .giant S)) + 11) ≤
          itCfSB Co Do (karyRefinementPrim h2).c (karyRefinementPrim h2).k (I.inW .giant S)
            (Xt (I.inW .giant S)) := by unfold itCfSB; omega
      omega
  · -- a later state
    refine (it_cfB_spec hfb [.list [itCfWOK K cache, kst], u]
      (Q := fun w cst => ItSBrPost (itCfRel I RI Xt) e c S L K b (itCfD K cache E) sb f _ w ∧
        w.wt < cst ∧ cst ≤ itCfCtC (itCfRB (I.inW .giant S) (Xt (I.inW .giant S)))
          (Xt (I.inW .giant S))) (fun h => absurd h (by simp)) (fun _ => ?_)).mono
      fun w cost ⟨c', ⟨hpost, hwc, hc'⟩, hcost⟩ => ⟨?_, hpost⟩
    · refine (it_cfCt_spec hct hwr (itCfWOK K cache) kst u
        (Qk := fun r => ItCfIPost RI e c S L K b oX oY E sbI fI (Xt (I.inW .giant S)) r)
        ((hA.step b oX oY _ E sbI fI hRi).mono fun r cst ⟨hcs', hp⟩ =>
          ⟨hp, itCf_shape_of_post hp, hcs'⟩)).wt_lt.mono
        fun w cst ⟨⟨r, hp, hwr', hcs'⟩, hwc⟩ => ⟨?_, hwc, hcs'.trans (itCfCtC_mono hbw)⟩
      exact itCf_post I hK hca subset_rfl hsb hfI (by omega) (itCf_wO_wt I Pg F hc hK hca)
        hA.wtK (hA.wtR b oX oY) hp hwr'
    · have : 3 * itCfCtC (itCfRB (I.inW .giant S) (Xt (I.inW .giant S))) (Xt (I.inW .giant S)) +
          100 * (itCfRB (I.inW .giant S) (Xt (I.inW .giant S)) + 11) ≤
          itCfSB Co Do (karyRefinementPrim h2).c (karyRefinementPrim h2).k (I.inW .giant S)
            (Xt (I.inW .giant S)) := by unfold itCfSB; omega
      omega

end GI.Impl
