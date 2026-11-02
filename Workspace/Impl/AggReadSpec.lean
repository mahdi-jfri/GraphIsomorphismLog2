import Workspace.Impl.AggReadOut

/-!
# The reading: the specification of `rdF`

`rd_spec`: on `[sv, lv]`, with the entries that the reading uses (`k`, the domain indicator,
`q`, the graph pairs `ps` of `G`, the selected interval) and the first test set `T` of
`sbOrder q κ`, the reading returns `[cpInitV …, lcCtx …]` with the graph form `p0` of `P_T`
(`rd_out_eq`). Its cost is at most `10⁸ (U + 20)`, where `U` bounds the weight of the input and
the cost of every module it calls (`RdBud`). The bound on `U` in terms of the input weight is in
`Workspace/Impl/AggReadOK.lean`.

The proof goes along the seven `let` steps of `rdF` (`rd_letE_det` for the deterministic ones).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm GI.LocalGroups
open GI.Cited (Val encPerm encGroup encPts gens Preimage)

/-- A deterministic `let` step before a step with a bound: the cost grows from `K` to
`ca + 2 K + 1`, since the result weighs less than its cost. -/
theorem rd_letE_det {P : Program} {env : List Val} {e body : Expr} {v : Val} {ca K : ℕ}
    (ha : Det P env e v ca) {R : Val → Prop}
    (hb : EvalAll P (env ++ [v]) body (fun w c => R w ∧ c ≤ K)) :
    EvalAll P env (.letE e body) (fun w c => R w ∧ c ≤ ca + 2 * K + 1) :=
  EvalAll.letE ha fun v' ca' h => by
    obtain ⟨rfl, hca⟩ := h
    exact EvalAll.mono hb.wt_lt fun w cb h => ⟨h.1.1, by have := h.1.2; have := h.2; omega⟩

/-- **The budget of the reading.** `U₁` bounds the weight of the input and the cost of the
test-set list; `U` bounds `U₁`, the cost of the tail of that list and of every other module. -/
structure RdBud (hpre : Preimage) (k q : ℕ) (ps : List (Perm (Fin k) × Perm (Fin q)))
    (T : Finset (Fin q)) (A : Val) (U₁ U : ℕ) : Prop where
  wA : A.wt ≤ U₁
  sb : sbK * (q ^ 64 + k + q + 64 + 10 + 1) ^ 5 ≤ U₁
  tl : 1000 * (U₁ + 1) * (3 * U₁ + 1) ≤ U
  le : U₁ ≤ U
  dom : domListK * (k + 1) ^ 3 ≤ U
  rk : 8000 * (k + 1) ^ 3 ≤ U
  rq : 8000 * (q + 1) ^ 3 ≤ U
  grp : grpK * pM k q ps ^ 6 ≤ U
  pt : (preimagePrim hpre).boundSize (1000 * preM k q ps (mtGens q T) ^ 4) +
    ptK * ptM k q ps ^ 24 ≤ U
  D : rdD + 3 ≤ U
  q : 10 * q + k + 10 ≤ U

set_option maxRecDepth 100000 in
/-- The cost of `fstMap` is at most that of the group of the pairs. -/
theorem rd_fstMap_le {k q : ℕ} (ps : List (Perm (Fin k) × Perm (Fin q))) :
    ps.length * (40 * (4 * (q + 1) ^ 2 + 22 * (k + q + 1) ^ 2) + 400) + mapK * (ps.length + 1) *
      ((Val.list [encPerm (1 : Perm (Fin q)), .list (ps.map pairV)]).wt +
        (Val.list ((onePairs ps).map pairV)).wt + 1) ≤ grpK * pM k q ps ^ 6 := by
  have w1 := wt_pairList_le ps
  have w2 := wt_pairList_le (onePairs ps)
  have hl : pM k q (onePairs ps) = pM k q ps := by simp [pM, onePairs]
  rw [hl] at w2
  have w3 := wt_encPerm_le (1 : Perm (Fin q))
  have w4 := wt_list2_le (encPerm (1 : Perm (Fin q))) (.list (ps.map pairV))
  set M := pM k q ps with hM
  have hM2 : k + q + 1 ≤ M := by simp only [hM, pM]; omega
  have hlM : ps.length + 1 ≤ M := by simp only [hM, pM]; omega
  have p2 : (q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have p2' : (k + q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hM2 2
  have m1 : 1 ≤ M := by omega
  have m23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right m1 (by omega)
  have m34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right m1 (by omega)
  have m46 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right m1 (by omega)
  have a1 : ps.length * (40 * (4 * (q + 1) ^ 2 + 22 * (k + q + 1) ^ 2) + 400) ≤
      M * (1440 * M ^ 3) := Nat.mul_le_mul (by omega) (by
        have : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega)
  have a2 : mapK * (ps.length + 1) * ((Val.list [encPerm (1 : Perm (Fin q)),
      .list (ps.map pairV)]).wt + (Val.list ((onePairs ps).map pairV)).wt + 1) ≤
      mapK * M * (200 * M ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hlM) (by
      have : 1 ≤ M ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega)
  have e1 : M * (1440 * M ^ 3) = 1440 * M ^ 4 := by ring
  have e2 : mapK * M * (200 * M ^ 3) = 200000 * M ^ 4 := by simp only [mapK]; ring
  have e3 : grpK = 1000000000000 := rfl
  have m6 : 1440 * M ^ 4 + 200000 * M ^ 4 ≤ grpK * M ^ 6 := by rw [e3]; omega
  omega

theorem rd_wt_ids (k q : ℕ) : (idsVal k q).wt ≤ 8 * (k + 1) ^ 2 + 8 * (q + 1) ^ 2 + 6 := by
  have w1 := wt_encPerm_le (1 : Perm (Fin k))
  have w2 := wt_encPerm_le (1 : Perm (Fin q))
  have := wt_list2_le (encPerm (1 : Perm (Fin k))) (encPerm (1 : Perm (Fin q)))
  unfold idsVal
  omega

/-- The bound of the seven steps of `rdF`. -/
theorem rd_chain_le (U : ℕ) :
    10 * (U + 20) + 2 * (40 * (U + 20) + 2 * (10 * (U + 20) + 2 * (40 * (U + 20) +
      2 * (80 * (U + 20) + 2 * (200 * (U + 20) + 2 * (400000 * (U + 20)) + 1) + 1) + 1) + 1) +
      1) + 1 ≤ 10 ^ 8 * (U + 20) := by
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- **The reading.** -/
theorem rd_spec (hpre : Preimage) {P : Program} {b jpre fr : ℕ}
    (hf : P.funs[fr]? = some (rdF b)) (hb : P.HasAt b (rdFuns b jpre))
    (hj : P.prims[jpre]? = some (preimagePrim hpre))
    {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (L : GiantLabels S)
    {svs lvs : List Val} {ps : List (Perm (Fin k) × Perm (Fin L.q))} {sel : ℕ}
    (hk : svs[0]? = some (.nat k)) (hdv : svs[2]? = some (indVal e S.dom))
    (hq : lvs[0]? = some (.nat L.q)) (hps : lvs[1]? = some (.list (ps.map pairV)))
    (hsel : lvs[2]? = some (.nat sel)) (hpg : PairGens e L S.G ps)
    (πd : S.domGroup →* alternatingGroup (Fin L.q))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
    {T : Finset (Fin L.q)} {Ts : List (Finset (Fin L.q))}
    (hO : (sbOrder L.q P₀.κ).sets = T :: Ts) (hq0 : 0 < L.q) {U₁ U : ℕ}
    (hU : RdBud hpre k L.q ps T (.list [.list svs, .list lvs]) U₁ U) :
    FunAll P fr (.list [.list svs, .list lvs]) (fun w c => ∃ p0 : GPairs k L.q,
      w = .list [cpInitV (.list svs) k L.q (domNat e S.dom).length ps (rdOsA e S L.q) T Ts p0,
        lcCtx (.list svs) k L.q ps sel (9 * L.q / 10)] ∧
      PairGens e L (S.liftGroup (Pgrp S.domGroup πd T)) p0 ∧ p0.length ≤ (k + L.q) ^ 2 ∧
      c ≤ 10 ^ 8 * (U + 20)) := by
  -- the modules
  have hR := rdAt_of hb
  have hdom := hR.dom
  have hrng := hR.rng
  have htl := hR.tl
  have hsb := hR.sb
  have hpt := hR.pt
  have hen := hR.en
  have hmk := hR.mkg
  have hfm := hR.fm
  have hgr := hR.gr
  set A : Val := .list [.list svs, .list lvs] with hA
  have wA := hU.wA
  have wA' : A.wt ≤ U := wA.trans hU.le
  -- step 1: the domain positions
  have h0 : [A][0]? = some A := rfl
  have d1 := rd_call (rd_rdS (P := P) h0 wA' hdv (by norm_num)) (domList_spec hdom e S.dom)
  have w1 := (domList_spec (P := P) hdom e S.dom).wt_lt
  -- step 2: the test sets
  have hY : L.q ^ 64 + k + L.q + 64 + 10 ≤ L.q ^ 64 + k + L.q + 64 + 10 := le_rfl
  have sbS := sb_spec hsb hq0 hY (k := k)
  have hO' : (sbOrder L.q 64).sets = T :: Ts := hO
  rw [hO'] at sbS
  have w2 := sbS.wt_lt
  have hU2 := hU.sb
  set L2 : Val := .list ((T :: Ts).map (tsV k)) with hL2
  set e1 : List Val := [A, natList (domNat e S.dom)] with he1
  have h0' : ∀ rest : List Val, (A :: rest)[0]? = some A := fun _ => rfl
  have dk1 := rd_rdS (P := P) (h0' [natList (domNat e S.dom)]) wA hk (by norm_num)
  have dq1 := rd_rdL (P := P) (h0' [natList (domNat e S.dom)]) wA hq (by norm_num)
  have wk := rd_wtS (lvs := lvs) hk
  have wq := rd_wtL (svs := svs) hq
  have w64 := wt_nat_le 64
  have wkq64 := wt_list3_le (.nat k) (.nat L.q) (.nat 64)
  have d2 := rd_call (Det.mk3 dk1 dq1 (Det.nat (P := P) (env := e1) 64)) sbS
  -- step 3: the tail
  have tlS := GI.Lang.tail_spec htl (tsV k T) (Ts.map (tsV k))
  have w3 := tlS.wt_lt
  have hlen : Ts.length + 1 < L2.wt := by
    have := length_lt_wt_list ((T :: Ts).map (tsV k)); simpa [hL2] using this
  have tlC : loopModK * ((Ts.map (tsV k)).length + 1) *
      (3 * (Val.list (tsV k T :: Ts.map (tsV k))).wt + 1) ≤ U := by
    have e2 : (Val.list (tsV k T :: Ts.map (tsV k))).wt = L2.wt := rfl
    rw [e2, List.length_map]
    refine le_trans ?_ hU.tl
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  set e2 : List Val := [A, natList (domNat e S.dom), L2] with he2
  have d3 := rd_call (Det.var' (P := P) (env := e2) (i := 2) (v := L2) rfl) tlS
  -- step 4: the identities
  set e3 : List Val := e2 ++ [.list (Ts.map (tsV k))] with he3
  have dk3 := rd_rdS (P := P) (env := e3) rfl wA' hk (by norm_num)
  have dq3 := rd_rdL (P := P) (env := e3) rfl wA' hq (by norm_num)
  have r1 := GI.Lang.range_det (P := P) hrng k
  have r2 := GI.Lang.range_det (P := P) hrng L.q
  have d4 := Det.mk2 (rd_call dk3 r1) (rd_call dq3 r2)
  have w4 := wt_list2_le (encPerm (1 : Perm (Fin k))) (encPerm (1 : Perm (Fin L.q)))
  have w41 := wt_encPerm_le (1 : Perm (Fin k))
  have w42 := wt_encPerm_le (1 : Perm (Fin L.q))
  have hrk := hU.rk
  have hrq := hU.rq
  have hk3 : 1000 * (k + 1) ^ 2 ≤ 8000 * (k + 1) ^ 3 := by
    have : (k + 1) ^ 2 ≤ (k + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hq3 : 1000 * (L.q + 1) ^ 2 ≤ 8000 * (L.q + 1) ^ 3 := by
    have : (L.q + 1) ^ 2 ≤ (L.q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hids : (idsVal k L.q).wt ≤ U := by
    have := rd_wt_ids k L.q
    have : 1 ≤ (k + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  -- step 5: `Ĥ`
  set e4 : List Val := e3 ++ [idsVal k L.q] with he4
  have dkq4 := rd_rdKQ (P := P) (env := e4) rfl wA' hk hq
  have dps4 := rd_rdL (P := P) (env := e4) rfl wA' hps (by norm_num)
  have gS := grp_spec hgr hen hmk ps
  have w5 := gS.wt_lt
  have hgU := hU.grp
  have wps := rd_wtL (svs := svs) hps
  have wkq := wt_list2_le (.nat k) (.nat L.q)
  have wkqp := wt_list2_le (.list [.nat k, .nat L.q]) (.list (ps.map pairV))
  have d5 := rd_call (Det.mk2 dkq4 dps4) gS
  -- step 6: `N̂`
  set e5 : List Val := e4 ++ [encGroup (ps.map encPair)] with he5
  have dkq5 := rd_rdKQ (P := P) (env := e5) rfl wA' hk hq
  have dps5 := rd_rdL (P := P) (env := e5) rfl wA' hps (by norm_num)
  have di5 := Det.get' (Det.var' (P := P) (env := e5) (i := 4) (v := idsVal k L.q) rfl)
    (Det.nat 1) (vs := [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin L.q))])
    (v := encPerm (1 : Perm (Fin L.q))) rfl
  have fS := fstMap_spec hfm ps
  have hfC := rd_fstMap_le ps
  have w6a := fS.wt_lt
  have gS' := grp_spec hgr hen hmk (onePairs ps)
  have hpo : pM k L.q (onePairs ps) = pM k L.q ps := by simp [pM, onePairs]
  rw [hpo] at gS'
  have w6 := gS'.wt_lt
  have wkqo := wt_list2_le (.list [.nat k, .nat L.q]) (.list ((onePairs ps).map pairV))
  have wpo := wt_list2_le (encPerm (1 : Perm (Fin L.q))) (.list (ps.map pairV))
  have d6 := rd_call (Det.mk2 dkq5 (rd_call (Det.mk2 di5 dps5) fS)) gS'
  -- step 7: `P_T`, and the result
  set e6 : List Val := e5 ++ [encGroup ((onePairs ps).map encPair)] with he6
  have dkq6 := rd_rdKQ (P := P) (env := e6) rfl wA' hk hq
  have dps6 := rd_rdL (P := P) (env := e6) rfl wA' hps (by norm_num)
  have dT6 := Det.get' (Det.var' (P := P) (env := e6) (i := 2) (v := L2) rfl) (Det.nat 0)
    (vs := (T :: Ts).map (tsV k)) (v := tsV k T) (by simp)
  have dI6 := Det.get' dT6 (Det.nat 0) (vs := [indT T, natList (ptsKey (labPts k (tlist T)))])
    (v := indT T) rfl
  have wT : (tsV k T).wt < L2.wt := wt_le_wt_list (by simp)
  have wI : (indT T).wt < (tsV k T).wt := wt_le_wt_list (by simp)
  have d7a := Det.mk3 dkq6 dps6 dI6
  have w7a := wt_list3_le (.list [.nat k, .nat L.q]) (.list (ps.map pairV)) (indT T)
  have hptU := hU.pt
  have hDU := hU.D
  have hqU := hU.q
  have hdU := hU.dom
  have hpre_le : ∀ hms, (preimagePrim hpre).bound (GI.Lang.preimageEnc (pairInst
      (MonoidHom.snd _ _) ps (mtGens L.q T) hms)) ≤
      (preimagePrim hpre).boundSize (1000 * preM k L.q ps (mtGens L.q T) ^ 4) := fun hms =>
    (preimagePrim hpre).bound_le ((GI.Lang.preimageEnc _).size_le_wt.trans (lcPreEnc_wt _ _ hms))
  have hAo : (Val.list [Val.list svs, Val.list lvs]).wt ≤ U₁ := wA
  have hle := hU.le
  -- the steps in `rdF`
  refine FunAll.intro hf ?_
  have Q7 : EvalAll P e6
      (.letE (.call (b + 63) (mk3 rdKQ rdPs (.get (.get (.var 2) (.nat 0)) (.nat 0)))) rdOutE)
      (fun w c => (∃ p0 : GPairs k L.q,
        w = .list [cpInitV (.list svs) k L.q (domNat e S.dom).length ps (rdOsA e S L.q) T Ts p0,
          lcCtx (.list svs) k L.q ps sel (9 * L.q / 10)] ∧
        PairGens e L (S.liftGroup (Pgrp S.domGroup πd T)) p0 ∧ p0.length ≤ (k + L.q) ^ 2) ∧
        c ≤ 400000 * (U + 20)) := by
    refine EvalAll.letE (Ra := fun v c => ∃ qs : GPairs k L.q, v = .list (qs.map pairV) ∧
        qs.length ≤ (k + L.q) ^ 2 ∧ PairGens e L (S.liftGroup (Pgrp S.domGroup πd T)) qs ∧
        (Val.list (qs.map pairV)).wt ≤ U ∧ c ≤ 150 * (U + 20))
      (EvalAll.call_funAll d7a fun v ca h => ?_) fun v c7 h => ?_
    · obtain ⟨rfl, hca⟩ := h
      refine ((ptGraph_spec hpre hpt hj hpg πd hπ T).wt_lt).mono fun w c h => ?_
      obtain ⟨⟨qs, rfl, hl, hq', hc⟩, hwc⟩ := h
      have := hpre_le (mtGens_snd hpg T)
      exact ⟨qs, rfl, hl, hq', by omega, by omega⟩
    · obtain ⟨qs, rfl, hl, hq', wqs, hc⟩ := h
      have dO := rd_out_det (P := P) e S hk hq hps hsel T Ts qs (U := U) wA'
        (w1.trans_le hdU).le (w2.trans_le (hU2.trans hle)).le (w3.trans_le tlC).le
        hids (w5.trans_le hgU).le (w6.trans_le hgU).le
        wqs hDU hqU
      have hw := dO.wt_lt
      refine EvalAll.mono dO fun w c h => ?_
      obtain ⟨rfl, hc'⟩ := h
      exact ⟨⟨qs, rfl, hq', hl⟩, by omega⟩
  have hsbU : sbK * (L.q ^ 64 + k + L.q + 64 + 10 + 1) ^ 5 ≤ U := hU2.trans hle
  have d1' := d1.mono (c' := 10 * (U + 20)) (by omega)
  have d2' := d2.mono (c' := 40 * (U + 20)) (by omega)
  have d3' := d3.mono (c' := 10 * (U + 20)) (by omega)
  have d4' := d4.mono (c' := 40 * (U + 20)) (by omega)
  have d5' := d5.mono (c' := 80 * (U + 20)) (by omega)
  have d6' := d6.mono (c' := 200 * (U + 20)) (by omega)
  clear d1 d2 d3 d4 d5 d6
  have Q6 := rd_letE_det d6' Q7
  have Q5 := rd_letE_det d5' Q6
  have Q4 := rd_letE_det d4' Q5
  have Q3 := rd_letE_det d3' Q4
  have Q2 := rd_letE_det d2' Q3
  have Q1 := rd_letE_det d1' Q2
  refine Q1.mono fun w c h => ?_
  obtain ⟨⟨p0, h1, h2, h3⟩, hc⟩ := h
  exact ⟨p0, h1, h2, h3, hc.trans (rd_chain_le U)⟩

end GI.Impl
