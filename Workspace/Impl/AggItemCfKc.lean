module

public import Workspace.Impl.AggItemCfRel

@[expose] public section

/-!
# Cases 2b and 3: the relations, the weight of the object part, and the branch outputs

* `itCf_wO_wt`: the object part `itCfWO H_X H_Y c_X cache` of a good cache weighs at most
  `itCfWOB W₀` (at most `q^{κ+1}` entries, `itCfCache_length`).
* `itCfKc`, `itCfRel`: the relations of the case program (see `AggItemCfRel.lean`).
* `itCf_post`: an output of the item stage for the choice set `E`, wrapped with the object part,
  is a branch output (`ItSBrPost`) for the rounds `itCfD K cache E`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)

variable {Ω C : Type} {k : ℕ}

/-- The object part of a kept value for the cache `cache`. -/
noncomputable def itCfWOK {S : State Ω C} {L : SuppliedLabels S} (K : ItSCtx k S L)
    (cache : List (ItCfEnt L.q)) : Val :=
  itCfWO (K.fx.map Prod.snd) (K.fy.map Prod.snd) (itCfcX K) cache

theorem itCf_sq_le {q G : ℕ} (h : q + 1 ≤ G) : (q ^ 2 + 1) ^ 2 ≤ G ^ 4 := by
  have h1 : q ^ 2 + 1 ≤ G ^ 2 := by
    have h2 : (q + 1) ^ 2 ≤ G ^ 2 := Nat.pow_le_pow_left h 2
    have h3 : q ^ 2 + 1 ≤ (q + 1) ^ 2 := by
      have : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
      omega
    omega
  calc (q ^ 2 + 1) ^ 2 ≤ (G ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = G ^ 4 := by ring

section Wt

variable (I : Iface) (Pg : Program) (F : Funs) {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
  {sv lv : Val} {L : SuppliedLabels S}

theorem itCf_v_eq (K : ItSCtx k S L) :
    K.v = .list [.list [K.sv, .list [.nat k, .nat L.q], .list (K.ps.map pairV),
      .list (K.fx.map pairV), .list (K.fy.map pairV),
      stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)],
      .list [encKColoring K.d, encKColoring K.d'], .nat (AggCase.code K.case),
      stTv (itCfSrc K)] := rfl

/-- **The weight of the object part** of a kept value with a good cache. -/
theorem itCf_wO_wt (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L} (hK : K.OK e c)
    {cache : List (ItCfEnt L.q)} (hca : ItCfCache K cache) :
    (itCfWOK K cache).wt ≤ itCfWOB (I.inW .giant S) := by
  obtain ⟨hkq, hκ, hq, hq0, -, hκq⟩ := itS_size I Pg F hc
  have hvw := itS_vW I Pg F hc hK
  obtain ⟨G, hG⟩ : ∃ G, G = itCfG (I.inW .giant S) := ⟨_, rfl⟩
  have hqG : L.q + 1 ≤ G := by rw [hG]; unfold itCfG; omega
  have hVG : K.v.wt + 1 ≤ G := by rw [hG]; unfold itCfG; omega
  have hG5 : 5 ≤ G := by rw [hG]; unfold itCfG; omega
  -- the parts of `K.v`
  have ev := itCf_v_eq K
  have w1 : (Val.list [K.sv, .list [.nat k, .nat L.q], .list (K.ps.map pairV),
      .list (K.fx.map pairV), .list (K.fy.map pairV),
      stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)]).wt < K.v.wt := by
    rw [ev]; exact wt_le_wt_list (by simp)
  have wfx : (Val.list (K.fx.map pairV)).wt < (Val.list [K.sv, .list [.nat k, .nat L.q],
      .list (K.ps.map pairV), .list (K.fx.map pairV), .list (K.fy.map pairV),
      stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)]).wt := wt_le_wt_list (by simp)
  have wfy : (Val.list (K.fy.map pairV)).wt < (Val.list [K.sv, .list [.nat k, .nat L.q],
      .list (K.ps.map pairV), .list (K.fx.map pairV), .list (K.fy.map pairV),
      stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)]).wt := wt_le_wt_list (by simp)
  have hgx := it_grp_wt K.fx (W := G) (by omega) (by omega)
  have hgy := it_grp_wt K.fy (W := G) (by omega) (by omega)
  -- powers of `G`
  have p3 : (G + 1) ^ 3 ≤ 8 * G ^ 3 := by
    have : (G + 1) ^ 3 ≤ (2 * G) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    rw [mul_pow] at this
    have e8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [e8] at this
    exact this
  have p369 : G ^ 3 ≤ G ^ 69 := Nat.pow_le_pow_right (by omega) (by omega)
  have p469 : G ^ 4 ≤ G ^ 69 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ G ^ 69 := Nat.one_le_pow _ _ (by omega)
  have p14 : 1 ≤ G ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hY : (L.q ^ 2 + 1) ^ 2 ≤ G ^ 4 := itCf_sq_le hqG
  have hk64 : P₀.κ = 64 := rfl
  have hq2 : 9 ≤ L.q ^ 2 := by
    have := Nat.pow_le_pow_left (show 3 ≤ L.q by omega) 2
    simpa using this
  -- the coloring of the source
  have hcX : (encKColoring (itCfcX K)).wt ≤ 5 * (L.q ^ 2 + 1) ^ 2 :=
    wt_encKColoring_le fun z => by
      have := itCf_orbColOut_le_sq (show 3 ≤ L.q by omega) (itCfHX K) (itCfSrc K) z
      show orbColOut (itCfHX K) (itCfSrc K) z < 2 * L.q ^ 2
      omega
  -- the cache
  have hent : ∀ v ∈ cache.map itCfEntV, v.wt ≤ 68 * G ^ 4 := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
    obtain ⟨-, hd, hd', b, hb⟩ := hca.2 a ha
    have k1 : (encKColoring a.1).wt ≤ 5 * (L.q ^ 2 + 1) ^ 2 :=
      wt_encKColoring_le fun z => by
        rw [hb]; have := itCf_orbColOut_le_sq (show 3 ≤ L.q by omega) (itCfHY K) b z
        show orbColOut (itCfHY K) b z < 2 * L.q ^ 2
        omega
    have k2 : (encKColoring a.2.1).wt ≤ 5 * (L.q ^ 2 + 1) ^ 2 := wt_encKColoring_le hd
    have k3 : (encKColoring a.2.2).wt ≤ 5 * (L.q ^ 2 + 1) ^ 2 := wt_encKColoring_le hd'
    have k4 := wt_list2_le (encKColoring a.2.1) (encKColoring a.2.2)
    have k5 := wt_list2_le (encKColoring a.1) (.list [encKColoring a.2.1, encKColoring a.2.2])
    show (Val.list [encKColoring a.1, .list [encKColoring a.2.1, encKColoring a.2.2]]).wt ≤ _
    omega
  have hcl := wt_list_le_of (cache.map itCfEntV) hent
  have hlen : cache.length ≤ G ^ 65 :=
    (itCfCache_length hca).trans (Nat.pow_le_pow_left (by omega) _)
  have hprod : cache.length * (2 * (68 * G ^ 4) + 1) ≤ 137 * G ^ 69 := by
    calc cache.length * (2 * (68 * G ^ 4) + 1) ≤ G ^ 65 * (137 * G ^ 4) :=
          Nat.mul_le_mul hlen (by omega)
      _ = 137 * G ^ 69 := by ring
  rw [List.length_map] at hcl
  have h4 := wt_list4_le (encGroup (K.fx.map Prod.snd)) (encGroup (K.fy.map Prod.snd))
    (encKColoring (itCfcX K)) (.list (cache.map itCfEntV))
  show (Val.list [encGroup (K.fx.map Prod.snd), encGroup (K.fy.map Prod.snd),
    encKColoring (itCfcX K), .list (cache.map itCfEntV)]).wt ≤ _
  unfold itCfWOB
  rw [← hG]
  omega

end Wt

/-! ### The relations -/

variable (I : Iface)

/-- **The kept value stands for the rounds `D`.** -/
def itCfKc (RI : ItCfIRel) (Xt : ℕ → ℕ) {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ)
    (S : State Ω C) (L : SuppliedLabels S) (K : ItSCtx k S L) (w : Val)
    (D : Set (Aggregation P₀ S L.toGiantLabels)) : Prop :=
  w.wt ≤ itCfKB (I.inW .giant S) (Xt (I.inW .giant S)) ∧
    ∃ (cache : List (ItCfEnt L.q)) (wI : Val) (E : Set (ItCfCh S L.toGiantLabels)),
      w = .list [itCfWOK K cache, wI] ∧ ItCfCache K cache ∧ RI.Ki e c S L K wI E ∧
        D = itCfD K cache E

/-- **The relations of Cases 2b and 3.** -/
def itCfRel (RI : ItCfIRel) (Xt : ℕ → ℕ) : ItSCaseRel where
  Kc e c S L K w D := itCfKc I RI Xt e c S L K w D
  Rb e c S L K b bst D sb f := bst.wt ≤ itCfRB (I.inW .giant S) (Xt (I.inW .giant S)) ∧
    ((∃ w, bst = .list [K.v, stTv b, w] ∧ itCfKc I RI Xt e c S L K w D ∧
        sb = (fun Ag => (Ag.items b).script) ∧ Xt (I.inW .giant S) ≤ f) ∨
      (∃ (cache : List (ItCfEnt L.q)) (kst u : Val) (E : Set (ItCfCh S L.toGiantLabels))
          (oX oY : CfgOut L.q) (sbI : ItCfCh S L.toGiantLabels → Script (Branches _)) (fI : ℕ),
        bst = .list [.list [itCfWOK K cache, kst], u] ∧ ItCfCache K cache ∧
        RI.Ri e c S L K b oX oY (.list [kst, u]) E sbI fI ∧ fI ≤ f ∧ D = itCfD K cache E ∧
        ∀ Ag ∈ D, sb Ag = sbI (Ag.soj, Ag.rep)))

/-! ### The branch outputs -/

/-- **An item output is a branch output.** The item stage answered for the choice set `E` of the
rounds `itCfD K cache E ⊆ D` (whose scripts are `sbI` of their choices), and the program wrapped
its output with the object part of `cache`. -/
theorem itCf_post
    {RI : ItCfIRel} {Xt : ℕ → ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
    {L : SuppliedLabels S} {K : ItSCtx k S L} (hK : K.OK e c) {b : Fin (P₀.κ + 1) → Fin L.q}
    {oX oY : CfgOut L.q} {cache : List (ItCfEnt L.q)} (hca : ItCfCache K cache)
    {E : Set (ItCfCh S L.toGiantLabels)} {sbI : ItCfCh S L.toGiantLabels → Script (Branches Ω)}
    {fI f B : ℕ} {D : Set (Aggregation P₀ S L.toGiantLabels)}
    {sb : Aggregation P₀ S L.toGiantLabels → Script (Branches Ω)}
    (hD : itCfD K cache E ⊆ D) (hsb : ∀ Ag ∈ itCfD K cache E, sb Ag = sbI (Ag.soj, Ag.rep))
    (hfI : fI ≤ f) (hTB : Xt (I.inW .giant S) ≤ B)
    (hwO : (itCfWOK K cache).wt ≤ itCfWOB (I.inW .giant S))
    (hwK : ∀ w E', RI.Ki e c S L K w E' → w.wt ≤ Xt (I.inW .giant S))
    (hwR : ∀ ist E' sb' f', RI.Ri e c S L K b oX oY ist E' sb' f' → ist.wt ≤ Xt (I.inW .giant S))
    {r w : Val} (hp : ItCfIPost RI e c S L K b oX oY E sbI fI (Xt (I.inW .giant S)) r)
    (hw : ItCfWrRel (itCfWOK K cache) r w) :
    ItSBrPost (itCfRel I RI Xt) e c S L K b D sb f B w := by
  rcases hp with ⟨rr, pcs, os, wI, E', hr, hE', hdone, hKi, hout, hwt⟩ |
    ⟨hf0, m, Ω', C', T, k', e', c', arg, kst, E', kk, hE', hne, hinj, hm, hr, hcan, hgood, hlt,
      hask, hcont⟩
  · -- a finished branch
    rcases hw with ⟨md, a, kst, hr', -⟩ | ⟨pcsV, osV, w', hr', hw⟩
    · rw [hr] at hr'; simp at hr'
    rw [hr] at hr'
    simp only [Val.list.injEq, List.cons.injEq, and_true] at hr'
    obtain ⟨-, rfl, rfl, rfl⟩ := hr'
    refine Or.inl ⟨rr, pcs, os, .list [itCfWOK K cache, wI], itCfD K cache E', hw,
      (itCfD_mono K (fun a ha => ha) hE').trans hD, fun Ag hAg => ?_, ⟨?_, cache, wI, E', rfl,
        hca, hKi, rfl⟩, hout, hwt.trans hTB⟩
    · rw [hsb Ag (itCfD_mono K (fun a ha => ha) hE' hAg)]
      exact hdone _ hAg.2.2
    · have := hwK wI E' hKi
      have := wt_list2_le (itCfWOK K cache) wI
      unfold itCfKB
      omega
  · -- an ask
    rcases hw with ⟨md, a, kst', hr', hw⟩ | ⟨pcsV, osV, w', hr', -⟩
    swap
    · rw [hr] at hr'; simp at hr'
    rw [hr] at hr'
    simp only [Val.list.injEq, List.cons.injEq, and_true] at hr'
    obtain ⟨-, rfl, rfl, rfl⟩ := hr'
    refine Or.inr ⟨by omega, m, Ω', C', T, k', e', c', arg, .list [itCfWOK K cache, kst],
      itCfD K cache E', fun Ag => kk (Ag.soj, Ag.rep), (itCfD_mono K (fun a ha => ha) hE').trans hD,
      itCfD_nonempty hK hca hne, hinj, hm, hw, hcan, hgood, hlt, fun Ag hAg => ?_,
      fun u hu => ?_⟩
    · rw [hsb Ag (itCfD_mono K (fun a ha => ha) hE' hAg)]
      exact hask _ hAg.2.2
    · have hRi := hcont u hu
      refine ⟨?_, Or.inr ⟨cache, kst, u, E', oX, oY, fun ch => kk ch T.answer, fI - 1, rfl, hca,
        hRi, by omega, rfl, fun Ag _ => rfl⟩⟩
      have := hwR _ _ _ _ hRi
      have h1 := wt_list2_le (itCfWOK K cache) kst
      have h2 := wt_list2_le (.list [itCfWOK K cache, kst]) u
      have h3 : kst.wt < (Val.list [kst, u]).wt := wt_le_wt_list (by simp)
      have h4 : u.wt < (Val.list [kst, u]).wt := wt_le_wt_list (by simp)
      unfold itCfRB itCfKB
      omega

end GI.Impl
