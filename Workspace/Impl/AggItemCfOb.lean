import Workspace.Impl.AggItemCfKc
import Workspace.Impl.AggItemCfObW

/-!
# Cases 2b and 3: the objects of a branch at the start

`it_cfOb_start`: at a context of Case 2b or 3 and a good cache, the dispatcher `itCfObF` on
`[K.v, ⟨b⟩, itCfWOK K cache]` returns `[⟨oX⟩, ⟨oY⟩, itCfWOK K cache']` with a good cache `cache'`
extending `cache` such that every round agreeing with `cache'` has the objects `(oX, oY)` in the
branch of `b` (`ItCfObQ`), at cost at most `itCfBo`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring KaryRefinement)

variable {Ω C : Type} {k : ℕ}

/-- **What the object step gives at the start of the branch of `b`.** -/
def ItCfObQ {S : State Ω C} {L : SuppliedLabels S} (K : ItSCtx k S L)
    (b : Fin (P₀.κ + 1) → Fin L.q) (cache : List (ItCfEnt L.q)) (oXv oYv wO' : Val) : Prop :=
  ∃ (oX oY : CfgOut L.q) (cache' : List (ItCfEnt L.q)), oXv = itCfOutV oX ∧ oYv = itCfOutV oY ∧
    wO' = itCfWOK K cache' ∧ ItCfCache K cache' ∧ (∀ a ∈ cache, a ∈ cache') ∧
    (∀ (E : Set (ItCfCh S L.toGiantLabels)), ∀ Ag ∈ itCfD K cache' E,
      Ag.out (Ag.strX Ag.src) (Ag.strY b) = (oX, oY)) ∧
    itCfColsLe oX (2 * L.q ^ P₀.κ) ∧ itCfColsLe oY (2 * L.q ^ P₀.κ)

theorem itCf_sq_le_pow (q : ℕ) : q ^ 2 ≤ q ^ P₀.κ := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [show P₀.κ = 64 from rfl]
  · exact Nat.pow_le_pow_right hq (by decide)

/-- A cache extended by a new key stays good. -/
theorem itCfCache_snoc {S : State Ω C} {L : SuppliedLabels S} {K : ItSCtx k S L}
    {cache : List (ItCfEnt L.q)} (hca : ItCfCache K cache) (b : Fin (P₀.κ + 1) → Fin L.q)
    {d d' : (Fin 2 → Fin L.q) → ℕ} (hnone : ∀ a ∈ cache, a.1 ≠ itCfcY K b)
    (hJ : GI.Cited.JointRefinement (itCfcX K) (itCfcY K b) d d') (hd : ∀ z, d z < 2 * L.q ^ 2)
    (hd' : ∀ z, d' z < 2 * L.q ^ 2) : ItCfCache K (cache ++ [(itCfcY K b, d, d')]) := by
  refine ⟨?_, fun a ha => ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hca.1, List.nodup_singleton _, ?_⟩
    intro x hx y hy hxy
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact hnone a ha (hxy.trans hy)
  · rcases List.mem_append.1 ha with ha | ha
    · exact hca.2 a ha
    · rw [List.mem_singleton] at ha
      subst ha
      exact ⟨hJ, hd, hd', b, rfl⟩

section Ob

variable (I : Iface) (Pg : Program) (F : Funs) {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
  {sv lv : Val} {L : SuppliedLabels S}

set_option maxHeartbeats 4000000 in
/-- **The objects at the start of a branch.** -/
theorem it_cfOb_start {ob o2 o3 fcol forb fdes fd kt eqn ref brep j Co Do : ℕ}
    (hob : Pg.funs[ob]? = some (itCfObF o2 o3))
    (ho2 : Pg.funs[o2]? = some (itCfO2F fcol fd ref forb))
    (ho3 : Pg.funs[o3]? = some (itCfO3F fdes P₀.κ))
    (hobj : ItCfObjSpec Pg fcol forb fdes Co Do)
    (hfd : Pg.HasAt fd (findFuns fd kt)) (hkt : Pg.funs[kt]? = some (itCfKeyF eqn))
    (heqn : Pg.HasAt eqn (eqNatsFuns eqn)) (h2 : KaryRefinement 2)
    (href : Pg.funs[ref]? = some (stRefF brep j)) (hrep : Pg.HasAt brep (replicateFuns brep))
    (hj : Pg.prims[j]? = some (karyRefinementPrim h2))
    (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L} (hK : K.OK e c)
    (hcs : K.case = .twoB ∨ K.case = .three) (T : ℕ) {cache : List (ItCfEnt L.q)}
    (hca : ItCfCache K cache) (b : Fin (P₀.κ + 1) → Fin L.q) :
    FunAll Pg ob (.list [K.v, stTv b, itCfWOK K cache]) (fun w cost =>
      ∃ oXv oYv wO', w = .list [oXv, oYv, wO'] ∧ ItCfObQ K b cache oXv oYv wO' ∧
        cost ≤ itCfBo Co Do (karyRefinementPrim h2).c (karyRefinementPrim h2).k
          (I.inW .giant S) T) := by
  obtain ⟨hkq, hκ, hq, hq0, -, hκq⟩ := itS_size I Pg F hc
  have hvw := itS_vW I Pg F hc hK
  have hwO := itCf_wO_wt I Pg F hc hK hca
  have hk64 : P₀.κ = 64 := rfl
  obtain ⟨W₀, hW₀⟩ : ∃ W₀, W₀ = I.inW .giant S := ⟨_, rfl⟩
  rw [← hW₀] at hkq hκ hq hvw hwO ⊢
  obtain ⟨G, hG⟩ : ∃ G, G = itCfG W₀ := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = itCfV W₀ T := ⟨_, rfl⟩
  obtain ⟨Bp, hBp⟩ : ∃ Bp, Bp = itCfBp Co Do (karyRefinementPrim h2).c (karyRefinementPrim h2).k
    W₀ T := ⟨_, rfl⟩
  have hqG : L.q + 1 ≤ G := by rw [hG]; unfold itCfG; omega
  have hVbG : itSVB W₀ + 1 ≤ G := by rw [hG]; unfold itCfG; omega
  have hY := itCf_sq_le hqG
  have hq2 : 9 ≤ L.q ^ 2 := by
    have := Nat.pow_le_pow_left (show 3 ≤ L.q by omega) 2
    simpa using this
  have hG2 : 5 * (2 * W₀ + 3 + 1) ^ 2 ≤ 5 * G ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [hG]; unfold itCfG; omega) 2)
  have htb : (stTv b).wt ≤ 5 * (2 * W₀ + 3 + 1) ^ 2 := wt_stTv_le b (by omega) (by omega)
  -- the weight of the input
  have hx3 := wt_list3_le K.v (stTv b) (itCfWOK K cache)
  have hRB : 2 * (K.v.wt + (stTv b).wt + (itCfWOK K cache).wt) + 7 ≤ itCfRB W₀ T := by
    unfold itCfRB itCfKB; rw [← hG]; omega
  have hVR : itCfRB W₀ T * 10 + 100 * G ^ 4 + 10 ≤ V := by rw [hV, hG]; unfold itCfV; omega
  have ev := itCf_v_eq K
  have wdd : (Val.list [encKColoring K.d, encKColoring K.d']).wt < K.v.wt := by
    rw [ev]; exact wt_le_wt_list (by simp)
  have wd : (encKColoring K.d).wt < K.v.wt :=
    lt_trans (wt_le_wt_list (by simp)) wdd
  have wd' : (encKColoring K.d').wt < K.v.wt :=
    lt_trans (wt_le_wt_list (by simp)) wdd
  have wsrc : (stTv (itCfSrc K)).wt < K.v.wt := by rw [ev]; exact wt_le_wt_list (by simp)
  have wO_ : ∀ v ∈ [encGroup (K.fx.map Prod.snd), encGroup (K.fy.map Prod.snd),
      encKColoring (itCfcX K), .list (cache.map itCfEntV)], v.wt < (itCfWOK K cache).wt :=
    fun v hv => wt_le_wt_list hv
  have wgx := wO_ (encGroup (K.fx.map Prod.snd)) (by simp)
  have wgy := wO_ (encGroup (K.fy.map Prod.snd)) (by simp)
  have wcX := wO_ (encKColoring (itCfcX K)) (by simp)
  have wqn : (Val.nat L.q).wt ≤ L.q + 2 := by
    have := wt_nat_le L.q; have := GI.Machine.len_le_self L.q; simp only [wt_nat] at *; omega
  have hG4 : G ^ 2 ≤ G ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hqG4 : L.q + 2 ≤ G ^ 4 := by
    have : G ≤ G ^ 4 := Nat.le_self_pow (by norm_num) _
    have : L.q + 2 ≤ G := by rw [hG]; unfold itCfG; omega
    omega
  -- the bounds of the callees
  have hBp1 : itCfB Co Do (8 * V + 8) ≤ Bp := by rw [hBp]; unfold itCfBp; rw [← hV]; omega
  have hBl : itCfLkC (4 * V + 6) ≤ Bp := by rw [hBp]; unfold itCfBp; rw [← hV]; omega
  have hBo : ∀ (hs : List (Perm (Fin L.q))) {ℓ : ℕ} (t : Fin ℓ → Fin L.q)
      (r : (Fin 2 → Fin L.q) → ℕ), (∀ z, r z < 2 * L.q ^ 2) → (encGroup hs).wt ≤ V →
      (stTv t).wt ≤ V → itCfB Co Do (itCfOrbIn hs t r).wt ≤ Bp := by
    intro hs ℓ t r hr h1 h2'
    have h4 := wt_list4_le (.nat L.q) (encGroup hs) (stTv t) (encKColoring r)
    have h5 : (encKColoring r).wt ≤ 5 * (L.q ^ 2 + 1) ^ 2 := wt_encKColoring_le hr
    exact (itCfB_mono (show (itCfOrbIn hs t r).wt ≤ 8 * V + 8 by unfold itCfOrbIn; omega)).trans
      hBp1
  have hxV : (Val.list [K.v, stTv b, itCfWOK K cache]).wt ≤ V := by omega
  rw [ev]
  refine (it_cfOb_spec hob K.st (.list [encKColoring K.d, encKColoring K.d']) (stTv (itCfSrc K))
    (stTv b) (itCfWOK K cache) (AggCase.code K.case) (Q := fun w c =>
      (∃ oXv oYv wO', w = .list [oXv, oYv, wO'] ∧ ItCfObQ K b cache oXv oYv wO') ∧ w.wt < c ∧
        c ≤ itCfO2C V Bp) ?_ ?_).mono fun w c ⟨c', ⟨⟨oXv, oYv, wO', hw, hq'⟩, hwc, hc'⟩, hcc⟩ =>
      ⟨oXv, oYv, wO', hw, hq', ?_⟩
  · -- Case 2b
    intro hcd
    have hcase : K.case = .twoB := by
      rcases hcs with h | h
      · exact h
      · rw [h] at hcd; simp [AggCase.code] at hcd
    have hBr : (karyRefinementPrim h2).bound (karyEnc (itCfcX K) (orbColOut (gens
        (K.fy.map Prod.snd)) b)) + 30 * (L.q ^ 2 + 1) ^ 2 + stRefK * (6 * V + 20 + 1) ^ 2 ≤ Bp := by
      have hke : (karyEnc (itCfcX K) (orbColOut (gens (K.fy.map Prod.snd)) b)).wt ≤ V := by
        have h1 := wt_replicate_zero_le L.q
        have h2' : (encKColoring (orbColOut (gens (K.fy.map Prod.snd)) b)).wt ≤
            5 * (L.q ^ 2 + 1) ^ 2 := wt_encKColoring_le fun z => by
          have := itCf_orbColOut_le_sq (show 3 ≤ L.q by omega) (gens (K.fy.map Prod.snd)) b z; omega
        have h3 := wt_list3_le (.list (List.replicate L.q (.nat 0))) (encKColoring (itCfcX K))
          (encKColoring (orbColOut (gens (K.fy.map Prod.snd)) b))
        unfold karyEnc
        omega
      have hs := (karyEnc (itCfcX K) (orbColOut (gens (K.fy.map Prod.snd)) b)).size_le_wt
      have hpow : ((karyEnc (itCfcX K) (orbColOut (gens (K.fy.map Prod.snd)) b)).size + 2) ^
          (karyRefinementPrim h2).k ≤ (V + 2) ^ (karyRefinementPrim h2).k :=
        Nat.pow_le_pow_left (by omega) _
      have hm := Nat.mul_le_mul_left (karyRefinementPrim h2).c hpow
      have h30 : 30 * (L.q ^ 2 + 1) ^ 2 ≤ 30 * G ^ 4 := Nat.mul_le_mul_left _ hY
      unfold Prim.bound
      rw [hBp]
      unfold itCfBp
      rw [← hV, ← hG]
      omega
    refine (it_cfO2_spec ho2 hobj hfd hkt heqn h2 href hrep hj K.sv (.list (K.ps.map pairV))
      (.list (K.fx.map pairV)) (.list (K.fy.map pairV))
      (stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ))
      (.list [encKColoring K.d, encKColoring K.d']) (.nat (AggCase.code K.case)) k (itCfSrc K) b
      (K.fx.map Prod.snd) (K.fy.map Prod.snd) (itCfcX K) cache (by omega)
      (fun z => by have := itCf_orbColOut_le_sq (show 3 ≤ L.q by omega) (itCfHX K) (itCfSrc K) z
                   show orbColOut (itCfHX K) (itCfSrc K) z ≤ _; omega)
      (fun a ha => ⟨(hca.2 a ha).2.1, (hca.2 a ha).2.2.1⟩) (V := V) (B := Bp) ?_ ?_ hBl hBr
      fun r hr => ⟨hBo _ _ r hr (by omega) (by omega), hBo _ _ r hr (by omega) (by omega)⟩
      ).wt_lt.mono fun w c ⟨⟨d, d', cache', hstep, hw, hcst⟩, hwc⟩ => ⟨⟨_, _, _, hw, ?_⟩, hwc, hcst⟩
    · show (Val.list [K.v, stTv b, itCfWOK K cache]).wt + 100 * (L.q ^ 2 + 1) ^ 2 ≤ V
      have : 100 * (L.q ^ 2 + 1) ^ 2 ≤ 100 * G ^ 4 := Nat.mul_le_mul_left _ hY
      omega
    · have h3 := wt_list3_le (.nat L.q) (encGroup (K.fy.map Prod.snd)) (stTv b)
      exact (itCfB_mono (show (itCfColIn (K.fy.map Prod.snd) b).wt ≤ 8 * V + 8 by
        unfold itCfColIn; omega)).trans hBp1
    · -- the objects of the rounds agreeing with the new cache
      have hmem : ((itCfcY K b), d, d') ∈ cache' := by
        rcases hstep with ⟨rfl, h⟩ | ⟨rfl, -, -, -, -⟩
        · exact h
        · exact List.mem_append_right _ (List.mem_singleton_self _)
      have hca'' : ItCfCache K cache' := by
        rcases hstep with ⟨rfl, -⟩ | ⟨rfl, hnone, hJ, hd, hd'⟩
        · exact hca
        · exact itCfCache_snoc hca b hnone hJ hd hd'
      have hsq := itCf_sq_le_pow L.q
      obtain ⟨-, hdb, hdb', -⟩ := hca''.2 _ hmem
      refine ⟨_, _, cache', rfl, rfl, rfl, hca'', ?_, fun E Ag hAg => ?_,
        itCf_orbitalOut_cols _ _ _ fun z => (lt_of_lt_of_le (hdb z) (Nat.mul_le_mul_left 2 hsq)).le,
        itCf_orbitalOut_cols _ _ _ fun z => (lt_of_lt_of_le (hdb' z) (Nat.mul_le_mul_left 2 hsq)).le⟩
      · rcases hstep with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact fun a ha => ha
        · exact fun a ha => List.mem_append_left _ ha
      · exact itCf_out_twoB hK hAg.1 hcase b (hAg.2.1 _ hmem)
  · -- Case 3
    intro hcd
    have hcase : K.case = .three := by
      rcases hcs with h | h
      · rw [h] at hcd; simp [AggCase.code] at hcd
      · exact h
    have hd1 : itCfB Co Do (itCfDesIn K.d (itCfSrc K)).wt ≤ Bp := by
      have h4 := wt_list4_le (.nat L.q) (.nat P₀.κ) (encKColoring K.d) (stTv (itCfSrc K))
      have := wt_nat_le P₀.κ
      exact (itCfB_mono (show (itCfDesIn K.d (itCfSrc K)).wt ≤ 8 * V + 8 by
        unfold itCfDesIn; omega)).trans hBp1
    have hd2 : itCfB Co Do (itCfDesIn K.d' b).wt ≤ Bp := by
      have h4 := wt_list4_le (.nat L.q) (.nat P₀.κ) (encKColoring K.d') (stTv b)
      have := wt_nat_le P₀.κ
      exact (itCfB_mono (show (itCfDesIn K.d' b).wt ≤ 8 * V + 8 by
        unfold itCfDesIn; omega)).trans hBp1
    refine FunAll.mono (FunAll.wt_lt (it_cfO3_spec ho3 hobj K.sv (.list (K.ps.map pairV))
      (.list (K.fx.map pairV)) (.list (K.fy.map pairV))
      (stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)) (.nat (AggCase.code K.case))
      (itCfWOK K cache) k (itCfSrc K) b K.d K.d' (V := V) (B := Bp) ?_ hd1 hd2))
      fun w c ⟨⟨hw, hcst⟩, hwc⟩ => ⟨⟨_, _, _, hw, _, _, cache, rfl, rfl, rfl, hca,
        fun a ha => ha, fun E Ag hAg => itCf_out_three hK hAg.1 hcase b,
        itCf_designOut_cols _ _ fun z => (hK.dlt z).le,
        itCf_designOut_cols _ _ fun z => (hK.dlt' z).le⟩, hwc, ?_⟩
    · show (Val.list [K.v, stTv b, itCfWOK K cache]).wt + P₀.κ ≤ V
      omega
    · have : itCfO3C V Bp ≤ itCfO2C V Bp := by unfold itCfO3C itCfO2C; omega
      omega
  · -- the cost of the dispatch
    have hx' : (Val.list [Val.list [K.st, .list [encKColoring K.d, encKColoring K.d'],
        .nat (AggCase.code K.case), stTv (itCfSrc K)], stTv b, itCfWOK K cache]).wt =
        (Val.list [K.v, stTv b, itCfWOK K cache]).wt := rfl
    rw [hx'] at hcc
    have hbo : itCfBo Co Do (karyRefinementPrim h2).c (karyRefinementPrim h2).k W₀ T =
        3 * itCfO2C V Bp + 100 * (V + 11) := by rw [hV, hBp]; rfl
    rw [hbo]
    refine hcc.trans ((Nat.add_le_add (Nat.add_le_add hc' (Nat.mul_le_mul_left 2
      (hwc.le.trans hc'))) (Nat.mul_le_mul_left 100 (Nat.add_le_add_right hxV 11))).trans
      (le_of_eq (by ring)))

end Ob

end GI.Impl
