module

public import Workspace.Impl.AggCmpClBud

@[expose] public section

/-!
# The call of a stage: `CmCallOK`

`cm_call_ok` shows that the function `cmCallF` (at `b + 4`) meets `CmCallOK`, the hypothesis of
`cm_mv_spec` for the call of a stage. The steps are those of `AggCmpClProg.lean`: the log search
(`cm_cl_log`), the stage of the string of `t`, the stage kernel (`cm_cl_ker`), the increment
(`cm_cl_dv`) and the codes (`cmWp_spec`). With these values the returned value is the one of
`cm_stage_call`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups GI.LocalCertificates Equiv
  Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-- The cost of the call of a stage, for program states of weight at most `W`. -/
noncomputable def cmClCost (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) (W : ℕ) : ℕ :=
  8 * cpG hst hpre hm W + 10 ^ 5 * (W + 20)

/-! ### Selecting by the bit of a tuple -/

section Sel

variable {k q : ℕ}

theorem cm_sel_log (l : CmLog k q) (bt : Bool) :
    [tsV k l.T, .list (l.lx.map cmStgV), .list (l.ly.map cmStgV)][1 + bt.toNat]? =
      some (.list ((if bt then l.ly else l.lx).map cmStgV)) := by
  cases bt <;> rfl

theorem cm_sel_sv (a0 a1 a2 x y a5 a6 a7 a8 a9 : Val) (bt : Bool) :
    [a0, a1, a2, x, y, a5, a6, a7, a8, a9][3 + bt.toNat]? = some (if bt then y else x) := by
  cases bt <;> rfl

theorem cm_sel_mem (l : CmLog k q) (bt : Bool) :
    Val.list ((if bt then l.ly else l.lx).map cmStgV) ∈
      [tsV k l.T, .list (l.lx.map cmStgV), .list (l.ly.map cmStgV)] := by
  cases bt <;> simp

end Sel

section Call

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : SuppliedLabels S} {Cs : Set (Aggregation P₀ S L.toGiantLabels)}
  {Ag₀ : Aggregation P₀ S L.toGiantLabels} {O : TestTupleOrder L.q P₀.κ}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}

theorem cm_stgs_sel {l : CmLog k L.q} (h : CmStgs e πd l.T S.x l.lx ∧ CmStgs e πd l.T S.y l.ly)
    (bt : Bool) : CmStgs e πd l.T (cmZ S bt) (if bt then l.ly else l.lx) := by
  cases bt
  · exact h.1
  · exact h.2

theorem cm_color_sel {c : C → ℕ} {xv yv : Val} (hx : ColorVal e c xv S.x) (hy : ColorVal e c yv S.y)
    (bt : Bool) : ColorVal e c (if bt then yv else xv) (cmZ S bt) := by
  cases bt
  · exact hx
  · exact hy

theorem cm_code_sel {c : C → ℕ} {sv : Val} (hS : Canon e c sv S) (bt : Bool) :
    ∀ v, c (cmZ S bt v) < 2 * k := by
  intro v
  cases bt
  · exact (hS.colors v).1
  · exact (hS.colors v).2

theorem cm_groupW_le (k q : ℕ) : groupW k ≤ 160 * (k + q + 1) ^ 6 := by
  unfold groupW
  have h1 : (k ^ 2 + 2) * (k + 1) ≤ 2 * (k + 1) ^ 3 := by nlinarith
  have h2 := Nat.pow_le_pow_left h1 2
  have h3 : (2 * (k + 1) ^ 3) ^ 2 = 4 * (k + 1) ^ 6 := by ring
  have h4 : (k + 1) ^ 6 ≤ (k + q + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  omega

/-- The codes of a comparison call are light. -/
theorem cm_wt_codes (c : C → ℕ) (z z' : Ω → C) (a : Perm (Fin k)) :
    (natList (cmCodesX e c S z z' a)).wt ≤ 10 * (k + 1) ^ 2 ∧
      (natList (cmCodesY e c S z z' a)).wt ≤ 10 * (k + 1) ^ 2 := by
  have hb : ∀ x : ℕ, posOf (cmList e c S z z' a) x ≤ 2 * k := fun x =>
    (posOf_le _ x).trans (by rw [cm_length_list])
  have h1 := wt_natList_le (xs := cmCodesX e c S z z' a) (B := 2 * k) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hb _)
  have h2 := wt_natList_le (xs := cmCodesY e c S z z' a) (B := 2 * k) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hb _)
  have l1 : (cmCodesX e c S z z' a).length = k := by simp [cmCodesX]
  have l2 : (cmCodesY e c S z z' a).length = k := by simp [cmCodesY]
  rw [l1] at h1
  rw [l2] at h2
  have : k * (2 * (2 * k) + 5) + 4 ≤ 10 * (k + 1) ^ 2 := by nlinarith
  omega

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
/-- **The call of a stage meets `CmCallOK`.** -/
theorem cm_call_ok (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)
    {Pg : Program} {b jp : ℕ} (hsa : CmStAt Pg b jp) (hca : CmClAt Pg b)
    (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    {c : C → ℕ} (hci : Function.Injective c) {sv : Val} (hS : Canon e c sv S)
    (hgood : Good P₀ .giant S) (htr : S.Transitive)
    (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs)
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.toGiantLabels.π g)
    {ps fx fy : GPairs k L.q} {logs : List (CmLog k L.q)} (hlogs : CmLogsOK e πd logs)
    {M₀ Bw W : ℕ}
    (hBw : cmBw (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)).wt k L.q M₀
      (O.tuples.length * O.tuples.length) ≤ Bw) (hW : 100 * Bw + 1000 ≤ W)
    (hW2 : 10 ^ 10 * (k + L.q + 1) ^ 12 ≤ W) (Out : List Bool → Val → Prop) :
    CmCallOK e Cs Ag₀ O πd Pg b W (cmClCost hst hpre hm W)
      (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)) Out Bw M₀ := by
  intro m f acc ab ps' j o σ ents rec u hmeq hmf hM hc hF hlen hfl hacc hdrop hσj hj hok hne hwt
  set par := cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom) with hpar
  set N := O.tuples.length with hN
  obtain ⟨hP5, hparB⟩ := cm_st_sizes hBw
  obtain ⟨f1, f2, f3, f24, f46, -, -, -, f9, f66⟩ := cp_pow_facts k L.q
  have h612 : (k + L.q + 1) ^ 6 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hP6 : (k + L.q + 1) ^ 6 ≤ (N + 1) * (k + L.q + 1) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
  have hBw6 : 10 ^ 5 * (k + L.q + 1) ^ 6 ≤ Bw := by omega
  have hWB : 50 * Bw + 10 ^ 9 * (k + L.q + 1) ^ 6 ≤ W := by omega
  have hcardk : Fintype.card S.dom ≤ k := by
    have := Fintype.card_le_of_injective (fun v : S.dom => e v.1)
      (fun a b h => Subtype.ext (e.injective h))
    simpa using this
  -- the pair
  have hlt : acc.length < N * N := by
    by_contra h
    rw [cm_pairs_drop_end O (Nat.le_of_not_lt h)] at hdrop
    exact List.cons_ne_nil _ _ hdrop.symm
  obtain ⟨hi1, hi2, hdrop'⟩ := cm_pairs_drop O hlt
  have hab : (O.tuples[acc.length / N], O.tuples[acc.length % N]) = ab :=
    (List.cons.inj (hdrop'.symm.trans hdrop)).1
  subst hab
  set bt := (O.tuples[acc.length / N]).1 with hbt
  set tt := (O.tuples[acc.length / N]).2 with htt
  set bt' := (O.tuples[acc.length % N]).1 with hbt'
  -- the representative
  obtain ⟨a₀, hσo⟩ := Option.ne_none_iff_exists'.1 hne
  rw [hσo] at hok
  rcases o with _ | g₀
  · exact hok.elim
  obtain ⟨ha₀, hg₀⟩ := hok
  -- the canonical value and the logs
  obtain ⟨gv0, dv0, xv, yv, hv, rv, -, hdv0, hxv, hyv, hhv, -, hsv⟩ := hS.val
  obtain ⟨hO, hlgs⟩ := hlogs
  -- the program state
  set ks := σ.vals par with hks
  have hsvl : σ.val par = .list ks := rfl
  have hwW : (Val.list [.list ks, u]).wt ≤ W := by rw [← hsvl]; omega
  have h0 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? = some (.list [.list ks, u]) :=
    fun _ => rfl
  set pv : List Val := [sv, .list [.nat k, .nat L.q], .list (ps.map pairV),
    .list (fx.map pairV), .list (fy.map pairV), .list (logs.map cmLogV), .list (O.tuples.map stTT),
    .nat (Fintype.card S.dom), .nat N] with hpv
  have hp0 : ks[0]? = some (.list pv) := rfl
  have hpvW : ∀ v ∈ pv, v.wt < Bw := fun v hv => lt_trans (cm_wt_lt_of_mem hv) hparB
  have hsvB : sv.wt < Bw := hpvW _ (by simp [hpv])
  have hkqB : (Val.list [.nat k, .nat L.q]).wt < Bw := hpvW _ (by simp [hpv])
  have hlgB : (Val.list (logs.map cmLogV)).wt < Bw := hpvW _ (by simp [hpv])
  have httB : (Val.list (O.tuples.map stTT)).wt < Bw := hpvW _ (by simp [hpv])
  have hksB : (Val.list ks).wt < Bw := by
    have := cm_wt_lt_of_mem (vs := [.list ks, u]) (v := .list ks) (by simp)
    rw [← hsvl] at this ⊢
    omega
  have hAl : acc.length + 2 ≤ W := by
    have h1 := length_lt_wt_list (σ.acc.map boolVal)
    have h2 := cm_wt_lt_of_mem (vs := ks) (v := .list (σ.acc.map boolVal)) (by simp [hks, CmSt.vals])
    simp only [List.length_map] at h1
    rw [← hacc]
    omega
  set svs : List Val := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h, .nat S.N]
    with hsvs
  have hsvE : sv = .list svs := hsv
  have hsvsB : ∀ v ∈ svs, v.wt < Bw := fun v hv =>
    lt_trans (cm_wt_lt_of_mem hv) (by rw [← hsvE]; exact hsvB)
  -- reading the pieces
  have dKQ := fun rest => cp_rdP (P := Pg) (h0 rest) hwW hp0 (j := 1)
    (v := .list [.nat k, .nat L.q]) rfl (by omega)
  have dK : ∀ rest, Det Pg (.list [.list ks, u] :: rest) (.get (cpPf 1) (.nat 0)) (.nat k)
      (5 * (W + 20)) := fun rest =>
    Det.rd (dKQ rest) le_rfl rfl
      (by have := cm_wt_lt_of_mem (vs := [Val.nat k, .nat L.q]) (v := .nat k) (by simp); omega)
      (by omega)
  have dQ : ∀ rest, Det Pg (.list [.list ks, u] :: rest) (.get (cpPf 1) (.nat 1)) (.nat L.q)
      (5 * (W + 20)) := fun rest =>
    Det.rd (dKQ rest) le_rfl rfl
      (by have := cm_wt_lt_of_mem (vs := [Val.nat k, .nat L.q]) (v := .nat L.q) (by simp); omega)
      (by omega)
  have dLg := fun rest => cp_rdP (P := Pg) (h0 rest) hwW hp0 (j := 5)
    (v := .list (logs.map cmLogV)) rfl (by omega)
  have dTT := fun rest => cp_rdP (P := Pg) (h0 rest) hwW hp0 (j := 6)
    (v := .list (O.tuples.map stTT)) rfl (by omega)
  have dN := fun rest => cp_rdP (P := Pg) (h0 rest) hwW hp0 (j := 8) (v := .nat N) rfl (by omega)
  have dSV : ∀ rest, Det Pg (.list [.list ks, u] :: rest) (cpPf 0) (.list svs) (4 * (W + 20)) :=
    fun rest => cp_rdP (P := Pg) (h0 rest) hwW hp0 (j := 0) (v := .list svs) (by rw [← hsvE]; rfl)
      (by omega)
  have dSVi : ∀ rest (i : ℕ) (v : Val), svs[i]? = some v → i ≤ 15 →
      Det Pg (.list [.list ks, u] :: rest) (.get (cpPf 0) (.nat i)) v (5 * (W + 20)) :=
    fun rest i v hv hi => Det.rd (dSV rest) le_rfl hv
      (le_of_lt (lt_of_lt_of_le (hsvsB v (List.mem_of_getElem? hv)) (by omega))) hi
  have dA := fun rest => cp_rdK (P := Pg) (h0 rest) hwW (j := 4)
    (v := .list (σ.acc.map boolVal)) rfl (by omega)
  have dK0 := fun rest => cp_rdK (P := Pg) (h0 rest) hwW (j := 0) (v := par) rfl (by omega)
  have dK1 := fun rest => cp_rdK (P := Pg) (h0 rest) hwW (j := 1) (v := .nat σ.j) rfl (by omega)
  have dK2 := fun rest => cp_rdK (P := Pg) (h0 rest) hwW (j := 2) (v := cmOV σ.o) rfl (by omega)
  have dK3 := fun rest => cp_rdK (P := Pg) (h0 rest) hwW (j := 3)
    (v := .list (σ.cache.map cmEntV)) rfl (by omega)
  have hlenA : (σ.acc.map boolVal).length = acc.length := by rw [List.length_map, hacc]
  have dDiv : ∀ rest, Det Pg (.list [.list ks, u] :: rest)
      (.arith .div (.length (cpKf 4)) (cpPf 8)) (.nat (acc.length / N)) (10 * (W + 20)) :=
    fun rest => by
      refine (Det.arith' (op := .div) (Det.length (dA rest)) (dN rest) (z := acc.length / N)
        (by rw [hlenA]; rfl)).mono ?_
      have : acc.length / N ≤ acc.length := Nat.div_le_self _ _
      omega
  have dMod : ∀ rest, Det Pg (.list [.list ks, u] :: rest)
      (.arith .mod (.length (cpKf 4)) (cpPf 8)) (.nat (acc.length % N)) (10 * (W + 20)) :=
    fun rest => by
      refine (Det.arith' (op := .mod) (Det.length (dA rest)) (dN rest) (z := acc.length % N)
        (by rw [hlenA]; rfl)).mono ?_
      have : acc.length % N ≤ acc.length := Nat.mod_le _ _
      omega
  -- the tuples as values
  have dTup : ∀ rest (iE : Expr) (i : ℕ) (hi : i < N),
      Det Pg (.list [.list ks, u] :: rest) iE (.nat i) (10 * (W + 20)) →
      Det Pg (.list [.list ks, u] :: rest) (.get (cpPf 6) iE)
        (.list [boolVal O.tuples[i].1, stTv (O.tuples[i].2 : Fin P₀.κ → Fin L.q)])
        (16 * (W + 20)) := by
    intro rest iE i hi dI
    have eT : stTT O.tuples[i] =
        .list [boolVal O.tuples[i].1, stTv (O.tuples[i].2 : Fin P₀.κ → Fin L.q)] := rfl
    have hT : (O.tuples.map stTT)[i]? = some (.list [boolVal O.tuples[i].1,
        stTv (O.tuples[i].2 : Fin P₀.κ → Fin L.q)]) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, eT]
    have hTw : (Val.list [boolVal O.tuples[i].1,
        stTv (O.tuples[i].2 : Fin P₀.κ → Fin L.q)]).wt < Bw :=
      lt_trans (cm_wt_lt_of_mem (List.mem_of_getElem? hT)) httB
    exact (Det.get' (dTT rest) dI hT).mono (by omega)
  have hT1w : (Val.list [boolVal bt, stTv (tt : Fin P₀.κ → Fin L.q)]).wt < Bw := by
    have eT : stTT O.tuples[acc.length / N] =
        .list [boolVal bt, stTv (tt : Fin P₀.κ → Fin L.q)] := rfl
    have hm : stTT O.tuples[acc.length / N] ∈ O.tuples.map stTT :=
      List.mem_map.2 ⟨_, List.getElem_mem hi1, rfl⟩
    rw [eT] at hm
    exact lt_trans (cm_wt_lt_of_mem hm) httB
  have hstB : (stTv (tt : Fin P₀.κ → Fin L.q)).wt < Bw :=
    lt_trans (cm_wt_lt_of_mem (by simp)) hT1w
  refine CpFB.intro hca.call ?_
  unfold cmCallF
  rw [hsvl]
  have hbw := wt_boolVal_le bt
  have hbw' := wt_boolVal_le bt'
  -- step 1: the tuple `t`
  set V1 := Val.list [boolVal bt, stTv (tt : Fin P₀.κ → Fin L.q)] with hV1
  have dT1 : Det Pg [.list [.list ks, u]] (.get (cpPf 6) (.arith .div (.length (cpKf 4)) (cpPf 8)))
      V1 (16 * (W + 20)) := dTup [] _ _ hi1 (dDiv [])
  refine (CpEB.letE (Cb := 7 * cpG hst hpre hm W + 90000 * (W + 20))
    (CpEB.det dT1 le_rfl (by omega) (Q := fun v => v = V1) rfl) fun v1 hv1 _ => ?_).mono
    (by unfold cmClCost; omega) fun _ h => h
  subst hv1
  set env1 : List Val := [.list [.list ks, u], V1] with henv1
  have dB : ∀ rest, Det Pg (env1 ++ rest) (.get (.var 1) (.nat 0)) (boolVal bt) (W + 30) :=
    fun rest => (Det.get' (Det.var' (i := 1) (v := V1) rfl) (Det.nat 0)
      (vs := [boolVal bt, stTv (tt : Fin P₀.κ → Fin L.q)]) rfl).mono (by omega)
  -- step 2: the log of `tset t`
  have hLaw : (Val.list [.nat L.q, stTv (tt : Fin P₀.κ → Fin L.q),
      .list (logs.map cmLogV)]).wt ≤ W := by
    have := wt_list3_le (.nat L.q) (stTv (tt : Fin P₀.κ → Fin L.q)) (.list (logs.map cmLogV))
    have := cm_wt_lt_of_mem (vs := [Val.nat k, .nat L.q]) (v := .nat L.q) (by simp)
    omega
  have dLa : Det Pg env1 (mk3 (.get (cpPf 1) (.nat 1)) (.get (.var 1) (.nat 1)) (cpPf 5))
      (.list [.nat L.q, stTv (tt : Fin P₀.κ → Fin L.q), .list (logs.map cmLogV)])
      (30 * (W + 20)) := by
    refine (Det.mk3 (dQ _) (Det.get' (Det.var' (i := 1) (v := V1) rfl) (Det.nat 1)
      (vs := [boolVal bt, stTv (tt : Fin P₀.κ → Fin L.q)]) rfl) (dLg _)).mono ?_
    omega
  refine (CpEB.letE (Cb := 6 * cpG hst hpre hm W + 80000 * (W + 20))
    (CpEB.call (CpEB.det dLa le_rfl hLaw (Q := fun v => v = .list [.nat L.q,
      stTv (tt : Fin P₀.κ → Fin L.q), .list (logs.map cmLogV)]) rfl) fun v hv _ => by
        subst hv
        exact cm_cl_log hst hpre hm hsa hca hO tt hLaw hW2) fun v2 hv2 _ => ?_).mono
    (by omega) fun _ h => h
  obtain ⟨l, hl, hlT, rfl⟩ := hv2
  -- step 3: stage `j` of the string of `t`
  set lz := if bt then l.ly else l.lx with hlz
  have hzS : CmStgs e πd l.T (cmZ S bt) lz := cm_stgs_sel (hlgs l hl) bt
  have hjl : j < lz.length := by rw [hzS.1]; exact hj
  set d := lz[j] with hd
  have hdS : CmStg e πd l.T (cmZ S bt) j d := hzS.2 j hjl
  have hlB : (cmLogV l).wt < Bw :=
    lt_trans (cm_wt_lt_of_mem (List.mem_map.2 ⟨l, hl, rfl⟩)) hlgB
  have hlzB : (Val.list (lz.map cmStgV)).wt < Bw :=
    lt_trans (cm_wt_lt_of_mem (cm_sel_mem l bt)) hlB
  have hdB : (cmStgV d).wt < Bw :=
    lt_trans (cm_wt_lt_of_mem (List.mem_map.2 ⟨d, List.getElem_mem hjl, rfl⟩)) hlzB
  have htsB : (tsV k l.T).wt < Bw :=
    lt_trans (cm_wt_lt_of_mem (vs := [tsV k l.T, .list (l.lx.map cmStgV),
      .list (l.ly.map cmStgV)]) (by simp)) hlB
  have hpB : (encPts d.2).wt < Bw :=
    lt_trans (cm_wt_lt_of_mem (vs := [gpV d.1, encPts d.2]) (by simp)) hdB
  set env2 := env1 ++ [cmLogV l] with henv2
  have dLV : Det Pg env2 (.var 2) (.list [tsV k l.T, .list (l.lx.map cmStgV),
      .list (l.ly.map cmStgV)]) ((cmLogV l).wt + 1) := Det.var' rfl
  have dSt : Det Pg env2
      (.get (.get (.var 2) (.arith .add (.nat 1) (.get (.var 1) (.nat 0)))) (cpKf 1))
      (cmStgV d) (40 * (W + 20)) := by
    have dI := Det.arith' (op := .add) (Det.nat 1) (dB [cmLogV l]) (z := 1 + bt.toNat) rfl
    have dL := Det.get' dLV dI (cm_sel_log l bt)
    have hget : (lz.map cmStgV)[j]? = some (cmStgV d) := by simp [hjl, hd]
    have dJ : Det Pg env2 (cpKf 1) (.nat j) (3 * (W + 20)) := hσj ▸ dK1 _
    refine (Det.get' dL dJ hget).mono ?_
    have : bt.toNat ≤ 1 := Bool.toNat_le bt
    have : (Val.list ((if bt then l.ly else l.lx).map cmStgV)).wt =
      (Val.list (lz.map cmStgV)).wt := rfl
    have := wt_nat_le (1 + bt.toNat)
    have : (Val.list [tsV k l.T, .list (l.lx.map cmStgV), .list (l.ly.map cmStgV)]).wt =
      (cmLogV l).wt := rfl
    omega
  refine (CpEB.letE (Cb := 6 * cpG hst hpre hm W + 70000 * (W + 20))
    (CpEB.det dSt le_rfl (by omega) (Q := fun v => v = cmStgV d) rfl) fun v3 hv3 _ => ?_).mono
    (by omega) fun _ h => h
  subst hv3
  set env3 := env2 ++ [cmStgV d] with henv3
  -- step 4: the stage kernel
  have hKaw : 10 * (Val.list [.list [.nat k, .nat L.q], cmStgV d, tsV k l.T]).wt + 100 ≤ W := by
    have := wt_list3_le (.list [.nat k, .nat L.q]) (cmStgV d) (tsV k l.T)
    omega
  have dKa : Det Pg env3 (mk3 (cpPf 1) (.var 3) (.get (.var 2) (.nat 0)))
      (.list [.list [.nat k, .nat L.q], cmStgV d, tsV k l.T]) (30 * (W + 20)) := by
    refine (Det.mk3 (dKQ _) (Det.var' (i := 3) rfl)
      (Det.get' (Det.var' (i := 2) (v := .list [tsV k l.T, .list (l.lx.map cmStgV),
        .list (l.ly.map cmStgV)]) rfl) (Det.nat 0) rfl)).mono ?_
    have := wt_list3_le (.list [.nat k, .nat L.q]) (cmStgV d) (tsV k l.T)
    have : (Val.list [tsV k l.T, .list (l.lx.map cmStgV), .list (l.ly.map cmStgV)]).wt =
      (cmLogV l).wt := rfl
    omega
  refine (CpEB.letE (Cb := 4 * cpG hst hpre hm W + 60000 * (W + 20))
    (CpEB.call (CpEB.det dKa le_rfl (by omega) (Q := fun v => v =
      .list [.list [.nat k, .nat L.q], cmStgV d, tsV k l.T]) rfl) fun v hv _ => by
        subst hv
        exact cm_cl_ker hst hpre hm hsa hca hjp hπ hdS hKaw hW2) fun v4 hv4 _ => ?_).mono
    (by omega) fun _ h => h
  have hv4w := hv4.wt_le
  set env4 := env3 ++ [v4] with henv4
  -- step 5: the increment
  have hDaw : (Val.list [.nat k, encPts d.2]).wt ≤ W := by
    have := wt_list2_le (.nat k) (encPts d.2)
    have := wt_nat_le k
    omega
  have dDa : Det Pg env4 (mk2 (.get (cpPf 1) (.nat 0)) (.get (.var 3) (.nat 1)))
      (.list [.nat k, encPts d.2]) (20 * (W + 20)) := by
    refine (Det.mk2 (dK _) (Det.get' (Det.var' (i := 3) (v := .list [gpV d.1, encPts d.2]) rfl)
      (Det.nat 1) rfl)).mono ?_
    have : (Val.list [gpV d.1, encPts d.2]).wt = (cmStgV d).wt := rfl
    omega
  refine (CpEB.letE (Cb := 3 * cpG hst hpre hm W + 50000 * (W + 20))
    (CpEB.call (CpEB.det dDa le_rfl hDaw (Q := fun v => v = .list [.nat k, encPts d.2]) rfl)
      fun v hv _ => by
        subst hv
        exact cm_cl_dv hst hpre hm hsa hca hdS hW2) fun v5 hv5 _ => ?_).mono
    (by omega) fun _ h => h
  have hv5w := DomVal.wt_le hv5
  set env5 := env4 ++ [v5] with henv5
  -- step 6: the codes
  set xz := if bt then yv else xv with hxz
  set yz := if bt' then yv else xv with hyz
  have hxzB : xz.wt < Bw := hsvsB _ (List.mem_of_getElem? (cm_sel_sv _ _ _ xv yv _ _ _ _ _ bt))
  have hyzB : yz.wt < Bw := hsvsB _ (List.mem_of_getElem? (cm_sel_sv _ _ _ xv yv _ _ _ _ _ bt'))
  have hdvB : dv0.wt < Bw := hsvsB _ (by simp [hsvs])
  have hoV : cmOV σ.o = .list [encPerm a₀] := by rw [hσo]; rfl
  have hoB : (encPerm a₀).wt < Bw := by
    have h1 := cm_wt_lt_of_mem (vs := ks) (v := cmOV σ.o) (by simp [hks, CmSt.vals])
    have h2 := cm_wt_lt_of_mem (vs := [encPerm a₀]) (v := encPerm a₀) (by simp)
    rw [hoV] at h1
    omega
  have dX : Det Pg env5 (.get (cpPf 0) (.arith .add (.nat 3) (.get (.var 1) (.nat 0)))) xz
      (10 * (W + 20)) := by
    have dI := Det.arith' (op := .add) (Det.nat 3) (dB [cmLogV l, cmStgV d, v4, v5])
      (z := 3 + bt.toNat) rfl
    refine (Det.get' (dSV _) dI (cm_sel_sv _ _ _ xv yv _ _ _ _ _ bt)).mono ?_
    have : bt.toNat ≤ 1 := Bool.toNat_le bt
    have : (if bt = true then yv else xv).wt = xz.wt := rfl
    omega
  have dY : Det Pg env5 (.get (cpPf 0) (.arith .add (.nat 3)
      (cmBitE (.arith .mod (.length (cpKf 4)) (cpPf 8))))) yz (40 * (W + 20)) := by
    have dT2 := dTup [V1, cmLogV l, cmStgV d, v4, v5] _ _ hi2 (dMod _)
    have dB2 := Det.get' dT2 (Det.nat 0) (v := boolVal bt') rfl
    have dI := Det.arith' (op := .add) (Det.nat 3) dB2 (z := 3 + bt'.toNat) rfl
    refine (Det.get' (dSV _) dI (cm_sel_sv _ _ _ xv yv _ _ _ _ _ bt')).mono ?_
    have : bt'.toNat ≤ 1 := Bool.toNat_le bt'
    have : (if bt' = true then yv else xv).wt = yz.wt := rfl
    omega
  have dO : Det Pg env5 (.get (cpKf 2) (.nat 0)) (encPerm a₀) (5 * (W + 20)) := by
    have : Det Pg env5 (cpKf 2) (cmOV σ.o) (3 * (W + 20)) := dK2 _
    rw [hoV] at this
    exact (Det.rd this (a := 3) le_rfl rfl (by omega) (by omega)).mono (by omega)
  have dV2 : Det Pg env5 (.get (cpPf 0) (.nat 2)) dv0 (5 * (W + 20)) := dSVi _ 2 dv0 rfl (by omega)
  have hWaw : (Val.list [dv0, xz, yz, encPerm a₀]).wt ≤ W := by
    have := wt_list4_le dv0 xz yz (encPerm a₀)
    omega
  have dWa := Det.mk4 dV2 dX dY dO
  have hwp := cmWp_spec hca.wp hca.dom hdv0 (cmZ S bt) (cmZ S bt') (cm_color_sel hxv hyv bt)
    (cm_color_sel hxv hyv bt') (cm_code_sel hS bt) (cm_code_sel hS bt') a₀
  obtain ⟨hcXw, hcYw⟩ := cm_wt_codes (e := e) (S := S) c (cmZ S bt) (cmZ S bt') a₀
  set cX := natList (cmCodesX e c S (cmZ S bt) (cmZ S bt') a₀) with hcX
  set cY := natList (cmCodesY e c S (cmZ S bt) (cmZ S bt') a₀) with hcY
  have hk6 : (k + 1) ^ 2 ≤ (k + L.q + 1) ^ 6 := le_trans f3 (le_trans f24 f46)
  have hCw : (Val.list [cX, cY]).wt ≤ W := by
    have := wt_list2_le cX cY
    omega
  have hwpc : wpK * (3 * k + 2) ^ 6 ≤ cpG hst hpre hm W := by
    have hW1 : 1 ≤ W := by omega
    have hp := cp_poly_le (W := W) (K := wpK) (d := 6) (by simp [wpK]) (by norm_num) hW1
    have : (3 * k + 2) ^ 6 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_left (by
      have : k + L.q + 1 ≤ (k + L.q + 1) ^ 2 := Nat.le_self_pow (by omega) _
      omega) 6
    have := Nat.mul_le_mul_left wpK this
    have := cpG_poly hst hpre hm (W := W)
    omega
  refine (CpEB.letE (Cb := 1000 * (W + 20))
    (CpEB.call (CpEB.det (dWa.mono (c' := 70 * (W + 20)) (by
        have := wt_list4_le dv0 xz yz (encPerm a₀); omega)) le_rfl hWaw
      (Q := fun v => v = .list [dv0, xz, yz, encPerm a₀]) rfl) fun v hv _ => by
        subst hv
        exact CpFB.det hwp hwpc hCw (Q := fun w => w = .list [cX, cY]) rfl) fun v6 hv6 _ => ?_).mono
    (by omega) fun _ h => h
  subst hv6
  set env6 := env5 ++ [.list [cX, cY]] with henv6
  -- step 7: the returned value
  have hσjk : σ.j ≤ k := by omega
  have hst' : ∀ u', u'.wt ≤ ansW k →
      (Val.list [({ σ with fl := 2 } : CmSt k).val par, u']).wt ≤ Bw := fun u' hu' =>
    (cm_wt_state (q := L.q) (M₀ := M₀) (L := N * N) (σ := { σ with fl := 2 }) hσjk
      (show 2 ≤ 2 by omega) (show σ.cache.length ≤ M₀ by omega) hlen
      (show σ.acc.length ≤ N * N by rw [hacc]; omega) hu').trans hBw
  have hk'B : (({ σ with fl := 2 } : CmSt k).val par).wt < Bw :=
    lt_of_lt_of_le (cm_wt_lt_of_mem (by simp)) (hst' (.list []) cm_wt_nil_le)
  have dl2 := cp_mkList' (P := Pg) (env := env6) (W := W) (c := 10 * (W + 20))
    [(cpKf 0, par), (cpKf 1, .nat σ.j), (cpKf 2, cmOV σ.o),
      (cpKf 3, .list (σ.cache.map cmEntV)), (cpKf 4, .list (σ.acc.map boolVal)),
      (.nat 2, .nat 2)] (v := ({ σ with fl := 2 } : CmSt k).val par) rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (dK0 _).mono (by omega)
      · exact (dK1 _).mono (by omega)
      · exact (dK2 _).mono (by omega)
      · exact (dK3 _).mono (by omega)
      · exact (dA _).mono (by omega)
      · exact (Det.nat 2).mono (by omega))
    (by omega)
  -- the window value
  have hsum := sum_wt_lt_wt_list svs
  simp only [hsvs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  rw [← hsvE] at hsum
  have hgw := cm_groupW_le k L.q
  have hwin : (winVal' k v4 v5 cX cY hv S.N).wt ≤ 2 * sv.wt + 1000 * (k + L.q + 1) ^ 6 := by
    have := wt_list_le [.nat k, v4, v5, cX, cY, hv, .list [], boolVal false, .nat 2, .nat S.N]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    have := wt_nat_le k
    have := wt_nat_le 2
    have := wt_boolVal_le false
    have : (Val.list []).wt ≤ 4 := by have := wt_list_le ([] : List Val); simpa using this
    have : k ≤ (k + L.q + 1) ^ 6 := by
      have : k + L.q + 1 ≤ (k + L.q + 1) ^ 6 := Nat.le_self_pow (by omega) _
      omega
    unfold winVal'
    omega
  have dl1 := cp_mkList' (P := Pg) (env := env6) (W := W) (c := 10 * (W + 20))
    [(.get (cpPf 1) (.nat 0), .nat k), (.var 4, v4), (.var 5, v5), (.get (.var 6) (.nat 0), cX),
      (.get (.var 6) (.nat 1), cY), (.get (cpPf 0) (.nat 5), hv), (.nil, .list []),
      (.nat 0, boolVal false), (.nat 2, .nat 2), (.get (cpPf 0) (.nat 9), .nat S.N)]
    (v := winVal' k v4 v5 cX cY hv S.N) rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (dK _).mono (by omega)
      · exact (Det.var' (v := v4) rfl).mono (by omega)
      · exact (Det.var' (v := v5) rfl).mono (by omega)
      · exact (Det.get' (Det.var' (i := 6) (v := .list [cX, cY]) rfl) (Det.nat 0) rfl).mono
          (by omega)
      · exact (Det.get' (Det.var' (i := 6) (v := .list [cX, cY]) rfl) (Det.nat 1) rfl).mono
          (by omega)
      · exact (dSVi _ 5 hv rfl (by omega)).mono (by omega)
      · exact Det.nil.mono (by omega)
      · exact (Det.nat 0).mono (by omega)
      · exact (Det.nat 2).mono (by omega)
      · exact (dSVi _ 9 (.nat S.N) rfl (by omega)).mono (by omega))
    (by omega)
  have hOutw : (Val.list [.nat 1, .nat 1, winVal' k v4 v5 cX cY hv S.N,
      ({ σ with fl := 2 } : CmSt k).val par]).wt ≤ W := by
    have := wt_list4_le (.nat 1) (.nat 1) (winVal' k v4 v5 cX cY hv S.N)
      (({ σ with fl := 2 } : CmSt k).val par)
    have := wt_nat_le 1
    omega
  have dl := cp_mkList' (P := Pg) (env := env6) (W := W) (c := 200 * (W + 20))
    [(.nat 1, .nat 1), (.nat 1, .nat 1),
      (Expr.mkList [.get (cpPf 1) (.nat 0), .var 4, .var 5, .get (.var 6) (.nat 0),
        .get (.var 6) (.nat 1), .get (cpPf 0) (.nat 5), .nil, .nat 0, .nat 2,
        .get (cpPf 0) (.nat 9)], winVal' k v4 v5 cX cY hv S.N),
      (Expr.mkList [cpKf 0, cpKf 1, cpKf 2, cpKf 3, cpKf 4, .nat 2],
        ({ σ with fl := 2 } : CmSt k).val par)]
    (v := .list [.nat 1, .nat 1, winVal' k v4 v5 cX cY hv S.N,
      ({ σ with fl := 2 } : CmSt k).val par]) rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact (Det.nat 1).mono (by omega)
      · exact (Det.nat 1).mono (by omega)
      · exact dl1.mono (by simp only [List.length_cons, List.length_nil]; omega)
      · exact dl2.mono (by simp only [List.length_cons, List.length_nil]; omega))
    hOutw
  have hgv : GroupValC k v4 (groupFin e (S.liftGroup
      (stageKer S πd (dstr S (cmZ S bt)) (tt : Fin P₀.κ → Fin L.q) j))) := by
    rw [hlT] at hv4
    exact hv4
  have hdv : DomVal e v5 (Subtype.val '' (inc (phiT S.domGroup πd (tset (tt : Fin P₀.κ → Fin L.q)))
      (dstr S (cmZ S bt)) j : Set S.dom)) := by
    rw [hlT] at hv5
    exact hv5
  refine CpEB.det dl (by simp only [List.length_cons, List.length_nil]; omega) hOutw ?_
  exact Or.inl (cm_stage_call hci hS hhv hgood htr hAg₀ hsub hcl hj hmeq hmf hM hc hF hlen hacc
    hdrop hσj hσo ha₀ hg₀ hgv hdv (fun u' hu' => hst' u' hu'.wt_le))

end Call

end GI.Impl
