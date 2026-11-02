import Workspace.Impl.AggReadProg

/-!
# The reading: reading the input and building the result

`rd_rd*`: reading `sv`, `lv` and their entries from the environment, at a cost linear in a
weight bound `U` of the input. `rd_out_det`: the result expression `rdOutE`, in the
environment `[[sv, lv], dom, sets, tail, ids, Ĥ, N̂, p0]` whose entries weigh at most `U`, gives
the list of `rd_out_eq` at cost at most `10⁵ (U + 20)`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)

section Read

variable {P : Program} {env : List Val} {svs lvs : List Val} {U : ℕ}

theorem rd_rdSv (h0 : env[0]? = some (.list [.list svs, .list lvs]))
    (hA : (Val.list [.list svs, .list lvs]).wt ≤ U) :
    Det P env rdSv (.list svs) (2 * U + 6) := by
  have h1 : (Val.list svs).wt < _ := cp_wt_get (vs := [.list svs, .list lvs]) (j := 0) rfl
  exact (Det.get' (Det.var' h0) (Det.nat 0) rfl).mono (by omega)

theorem rd_rdLv (h0 : env[0]? = some (.list [.list svs, .list lvs]))
    (hA : (Val.list [.list svs, .list lvs]).wt ≤ U) :
    Det P env rdLv (.list lvs) (2 * U + 7) := by
  have h1 : (Val.list lvs).wt < _ := cp_wt_get (vs := [.list svs, .list lvs]) (j := 1) rfl
  exact (Det.get' (Det.var' h0) (Det.nat 1) rfl).mono (by omega)

/-- An entry of `sv`. -/
theorem rd_rdS (h0 : env[0]? = some (.list [.list svs, .list lvs]))
    (hA : (Val.list [.list svs, .list lvs]).wt ≤ U) {j : ℕ} {v : Val} (hv : svs[j]? = some v)
    (hj : j ≤ 15) : Det P env (.get rdSv (.nat j)) v (3 * U + 30) := by
  have h1 : (Val.list svs).wt < _ := cp_wt_get (vs := [.list svs, .list lvs]) (j := 0) rfl
  have h2 := cp_wt_get hv
  exact (Det.get' (rd_rdSv h0 hA) (Det.nat j) hv).mono (by omega)

/-- An entry of `lv`. -/
theorem rd_rdL (h0 : env[0]? = some (.list [.list svs, .list lvs]))
    (hA : (Val.list [.list svs, .list lvs]).wt ≤ U) {j : ℕ} {v : Val} (hv : lvs[j]? = some v)
    (hj : j ≤ 15) : Det P env (.get rdLv (.nat j)) v (3 * U + 30) := by
  have h1 : (Val.list lvs).wt < _ := cp_wt_get (vs := [.list svs, .list lvs]) (j := 1) rfl
  have h2 := cp_wt_get hv
  exact (Det.get' (rd_rdLv h0 hA) (Det.nat j) hv).mono (by omega)

theorem rd_wtS {j : ℕ} {v : Val} (hv : svs[j]? = some v) :
    v.wt < (Val.list [.list svs, .list lvs]).wt :=
  (cp_wt_get hv).trans (cp_wt_get (vs := [.list svs, .list lvs]) (j := 0) rfl)

theorem rd_wtL {j : ℕ} {v : Val} (hv : lvs[j]? = some v) :
    v.wt < (Val.list [.list svs, .list lvs]).wt :=
  (cp_wt_get hv).trans (cp_wt_get (vs := [.list svs, .list lvs]) (j := 1) rfl)

/-- `[k, q]`. -/
theorem rd_rdKQ (h0 : env[0]? = some (.list [.list svs, .list lvs]))
    (hA : (Val.list [.list svs, .list lvs]).wt ≤ U) {k q : ℕ} (hk : svs[0]? = some (.nat k))
    (hq : lvs[0]? = some (.nat q)) :
    Det P env rdKQ (.list [.nat k, .nat q]) (20 * U + 100) := by
  have w1 := rd_wtS (lvs := lvs) hk
  have w2 := rd_wtL (svs := svs) hq
  have w3 := wt_list2_le (.nat k) (.nat q)
  exact (Det.mk2 (rd_rdS h0 hA hk (by norm_num)) (rd_rdL h0 hA hq (by norm_num))).mono
    (by omega)

end Read

/-! ### The result -/

/-- A call of a function with a specification, with the weight of the result bounded by the
cost. -/
theorem rd_call {P : Program} {env : List Val} {f : ℕ} {a : Expr} {v w : Val} {ca cb : ℕ}
    (ha : Det P env a v ca) (hb : FunDet P f v w cb) :
    Det P env (.call f a) w (ca + 2 * cb + 1) := by
  have := hb.wt_lt
  exact (Det.call ha hb).mono (by omega)

set_option maxHeartbeats 2000000 in
/-- **The result expression.** In the environment of the reading, whose entries weigh at most
`U`, with `D + 3 ≤ U` and `10 q + k + 10 ≤ U`, `rdOutE` gives the list of `rd_out_eq`. -/
theorem rd_out_det {P : Program} {Ω C : Type} {k q : ℕ} (e : Ω ≃ Fin k) (S : State Ω C)
    {svs lvs : List Val} {ps : List (Perm (Fin k) × Perm (Fin q))} {sel : ℕ}
    (hk : svs[0]? = some (.nat k)) (hq : lvs[0]? = some (.nat q))
    (hps : lvs[1]? = some (.list (ps.map pairV))) (hsel : lvs[2]? = some (.nat sel))
    (T : Finset (Fin q)) (Ts : List (Finset (Fin q))) (p0 : GPairs k q) {U : ℕ}
    (hA : (Val.list [.list svs, .list lvs]).wt ≤ U)
    (h1 : (natList (domNat e S.dom)).wt ≤ U)
    (h2 : (Val.list ((T :: Ts).map (tsV k))).wt ≤ U)
    (h3 : (Val.list (Ts.map (tsV k))).wt ≤ U) (h4 : (idsVal k q).wt ≤ U)
    (h5 : (encGroup (ps.map encPair)).wt ≤ U) (h6 : (encGroup ((onePairs ps).map encPair)).wt ≤ U)
    (h7 : (Val.list (p0.map pairV)).wt ≤ U) (hD : rdD + 3 ≤ U) (hqU : 10 * q + k + 10 ≤ U) :
    Det P [.list [.list svs, .list lvs], natList (domNat e S.dom),
        .list ((T :: Ts).map (tsV k)), .list (Ts.map (tsV k)), idsVal k q,
        encGroup (ps.map encPair), encGroup ((onePairs ps).map encPair),
        .list (p0.map pairV)] rdOutE
      (.list [cpInitV (.list svs) k q (domNat e S.dom).length ps (rdOsA e S q) T Ts p0,
        lcCtx (.list svs) k q ps sel (9 * q / 10)]) (10 ^ 5 * (U + 20)) := by
  rw [← rd_out_eq e S (.list svs) ps T Ts p0 sel]
  set env : List Val := [.list [.list svs, .list lvs], natList (domNat e S.dom),
    .list ((T :: Ts).map (tsV k)), .list (Ts.map (tsV k)), idsVal k q,
    encGroup (ps.map encPair), encGroup ((onePairs ps).map encPair), .list (p0.map pairV)]
    with henv
  have h0 : env[0]? = some (.list [.list svs, .list lvs]) := rfl
  -- reads
  have dSv := rd_rdSv (P := P) h0 hA
  have dK := rd_rdS (P := P) h0 hA hk (by norm_num)
  have dQ := rd_rdL (P := P) h0 hA hq (by norm_num)
  have dPs := rd_rdL (P := P) h0 hA hps (by norm_num)
  have dSel := rd_rdL (P := P) h0 hA hsel (by norm_num)
  have dKQ := rd_rdKQ (P := P) h0 hA hk hq
  have v1 := Det.var' (P := P) (env := env) (i := 1) rfl
  have v2 := Det.var' (P := P) (env := env) (i := 2) rfl
  have v3 := Det.var' (P := P) (env := env) (i := 3) rfl
  have v4 := Det.var' (P := P) (env := env) (i := 4) rfl
  have v5 := Det.var' (P := P) (env := env) (i := 5) rfl
  have v6 := Det.var' (P := P) (env := env) (i := 6) rfl
  have v7 := Det.var' (P := P) (env := env) (i := 7) rfl
  -- weights of the atoms
  have wsv : (Val.list svs).wt < _ := cp_wt_get (vs := [.list svs, .list lvs]) (j := 0) rfl
  have wk := rd_wtS (lvs := lvs) hk
  have wq := rd_wtL (svs := svs) hq
  have wps := rd_wtL (svs := svs) hps
  have wsel := rd_wtL (svs := svs) hsel
  have wkq := wt_list2_le (.nat k) (.nat q)
  have wT : (tsV k T).wt < (Val.list ((T :: Ts).map (tsV k))).wt :=
    wt_le_wt_list (by simp)
  have wD := wt_nat_le rdD
  have wkq' := wt_nat_le (k + q)
  have wn : (domNat e S.dom).length < (natList (domNat e S.dom)).wt := by
    have := length_lt_wt_list ((domNat e S.dom).map Val.nat)
    simpa [natList] using this
  have wn' := wt_nat_le (domNat e S.dom).length
  have wc := wt_nat_le (9 * q / 10)
  have wc9 : 9 * q / 10 ≤ 9 * q := Nat.div_le_self _ _
  -- the parent data
  have dSp := Det.mk2 dK v4
  have wSp := wt_list2_le (.nat k) (idsVal k q)
  have dLen := Det.length v1
  rw [show ((domNat e S.dom).map Val.nat).length = (domNat e S.dom).length by simp] at dLen
  have dAdd := Det.arith' (op := .add) dK dQ (z := k + q) rfl
  set parV : Val := .list [.list svs, .list [.nat k, .nat q], .list (ps.map pairV),
    .nat (domNat e S.dom).length, .nat rdD, natList (domNat e S.dom),
    .list [.nat k, idsVal k q], .nat (k + q)] with hparV
  have wPar : parV.wt ≤ 2 * ((Val.list svs).wt + (Val.list [.nat k, .nat q]).wt +
      (Val.list (ps.map pairV)).wt + (Val.nat (domNat e S.dom).length).wt + (Val.nat rdD).wt +
      (natList (domNat e S.dom)).wt + (Val.list [.nat k, idsVal k q]).wt +
      (Val.nat (k + q)).wt) + 12 := by
    rw [hparV]
    have := wt_list_le [.list svs, .list [.nat k, .nat q], .list (ps.map pairV),
      .nat (domNat e S.dom).length, .nat rdD, natList (domNat e S.dom),
      .list [.nat k, idsVal k q], .nat (k + q)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    omega
  set c8 := 30 * U + 200 with hc8
  have dPar := Det.mkList (P := P) (env := env) (c := c8)
    [(rdSv, .list svs), (rdKQ, .list [.nat k, .nat q]), (rdPs, .list (ps.map pairV)),
      (.length (.var 1), .nat (domNat e S.dom).length), (.nat rdD, .nat rdD),
      (.var 1, natList (domNat e S.dom)), (mk2 rdK (.var 4), .list [.nat k, idsVal k q]),
      (.arith .add rdK rdQ, .nat (k + q))] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact dSv.mono (by omega)
      · exact dKQ.mono (by omega)
      · exact dPs.mono (by omega)
      · exact dLen.mono (by omega)
      · exact (Det.nat rdD).mono (by omega)
      · exact v1.mono (by omega)
      · exact dSp.mono (by omega)
      · exact dAdd.mono (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at dPar
  rw [← hparV] at dPar
  -- the program state
  have dT := Det.get' v2 (Det.nat 0) (vs := (T :: Ts).map (tsV k)) (v := tsV k T) (by simp)
  set kV : Val := .list [parV, .list (Ts.map (tsV k)), .nat 0, .list [], .list [],
    .list (p0.map pairV), .list [], .nat 0, .list (p0.map pairV), natList (domNat e S.dom),
    .list [], tsV k T, .list [], .list [], .list []] with hkV
  have wNil : (Val.list []).wt ≤ 10 := by rw [wt_list_eq]; simp [GI.Machine.len]
  have w0 := wt_nat_le 0
  have wK : kV.wt ≤ 2 * (parV.wt + (Val.list (Ts.map (tsV k))).wt + 2 * (Val.nat 0).wt +
      7 * (Val.list []).wt + 2 * (Val.list (p0.map pairV)).wt + (natList (domNat e S.dom)).wt +
      (tsV k T).wt) + 19 := by
    rw [hkV]
    have := wt_list_le [parV, .list (Ts.map (tsV k)), .nat 0, .list [], .list [],
      .list (p0.map pairV), .list [], .nat 0, .list (p0.map pairV), natList (domNat e S.dom),
      .list [], tsV k T, .list [], .list [], .list []]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    omega
  set c15 := 1000 * U + 20000 with hc15
  have dKs := Det.mkList (P := P) (env := env) (c := c15)
    [(Expr.mkList [rdSv, rdKQ, rdPs, .length (.var 1), .nat rdD, .var 1, mk2 rdK (.var 4),
        .arith .add rdK rdQ], parV),
      (.var 3, .list (Ts.map (tsV k))), (.nat 0, .nat 0), (.nil, .list []), (.nil, .list []),
      (.var 7, .list (p0.map pairV)), (.nil, .list []), (.nat 0, .nat 0),
      (.var 7, .list (p0.map pairV)), (.var 1, natList (domNat e S.dom)), (.nil, .list []),
      (.get (.var 2) (.nat 0), tsV k T), (.nil, .list []), (.nil, .list []), (.nil, .list [])]
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      all_goals first
        | exact dPar.mono (by omega)
        | exact v3.mono (by omega)
        | exact (Det.nat 0).mono (by omega)
        | exact Det.nil.mono (by omega)
        | exact v7.mono (by omega)
        | exact v1.mono (by omega)
        | exact dT.mono (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at dKs
  rw [← hkV] at dKs
  have dSt := Det.mk2 dKs (Det.nat (P := P) (env := env) 0)
  have wSt := wt_list2_le kV (.nat 0)
  -- the context
  have dL := Det.mk4 dK v5 v6 dSp
  have wL := wt_list4_le (.nat k) (encGroup (ps.map encPair)) (encGroup ((onePairs ps).map encPair))
    (.list [.nat k, idsVal k q])
  have dCap := Det.arith' (op := .div) (Det.arith' (op := .mul) (Det.nat (P := P) (env := env) 9)
    dQ (z := 9 * q) rfl) (Det.nat 10) (z := 9 * q / 10) rfl
  set cV : Val := .list [.list svs, .list [.nat k, .nat q], .list (ps.map pairV),
    .list [.nat k, encGroup (ps.map encPair), encGroup ((onePairs ps).map encPair),
      .list [.nat k, idsVal k q]], .nat sel, .nat (9 * q / 10)] with hcV
  have wC : cV.wt ≤ 2 * ((Val.list svs).wt + (Val.list [.nat k, .nat q]).wt +
      (Val.list (ps.map pairV)).wt + (Val.list [.nat k, encGroup (ps.map encPair),
        encGroup ((onePairs ps).map encPair), .list [.nat k, idsVal k q]]).wt +
      (Val.nat sel).wt + (Val.nat (9 * q / 10)).wt) + 10 := by
    rw [hcV]
    have := wt_list_le [.list svs, .list [.nat k, .nat q], .list (ps.map pairV),
      .list [.nat k, encGroup (ps.map encPair), encGroup ((onePairs ps).map encPair),
        .list [.nat k, idsVal k q]], .nat sel, .nat (9 * q / 10)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    omega
  set c6 := 100 * U + 1000 with hc6
  have dC := Det.mkList (P := P) (env := env) (c := c6)
    [(rdSv, .list svs), (rdKQ, .list [.nat k, .nat q]), (rdPs, .list (ps.map pairV)),
      (mk4 rdK (.var 5) (.var 6) (mk2 rdK (.var 4)), .list [.nat k, encGroup (ps.map encPair),
        encGroup ((onePairs ps).map encPair), .list [.nat k, idsVal k q]]),
      (.get rdLv (.nat 2), .nat sel),
      (.arith .div (.arith .mul (.nat 9) rdQ) (.nat 10), .nat (9 * q / 10))] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact dSv.mono (by omega)
      · exact dKQ.mono (by omega)
      · exact dPs.mono (by omega)
      · exact dL.mono (by omega)
      · exact dSel.mono (by omega)
      · exact dCap.mono (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at dC
  rw [← hcV] at dC
  have dOut := Det.mk2 dSt dC
  have wO := wt_list2_le (.list [kV, .nat 0]) cV
  exact dOut.mono (by omega)

end GI.Impl
