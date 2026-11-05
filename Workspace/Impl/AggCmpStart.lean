module

public import Workspace.Impl.AggCmpStBud

@[expose] public section

/-!
# The start of a pair: `CmStartOK`

`cm_start_ok` shows that the function `cmStartF` (at `b + 5`) meets `CmStartOK`, the hypothesis of
`cm_mv_spec` for the start of a pair. The steps are those of `AggCmpStProg.lean`:

1. read the pair `(t, t')` at index `p = |acc|` (`cm_pairs_drop`) and compute the label points of
   both tuples;
2. compute the orbit of the label points of `t` under the graph pairs of `G` and search it for
   the label points of `t'`;
3. if they are not found, the first coset is empty (`cm_init_empty`), so the new state has no
   representative;
4. otherwise the transversal element `encPair g` gives `g.1`, the positions of a member of the
   coset (`cm_init_mem`), and the stabilizer of the label points of `t` (one **PointwiseStab**
   call, then the reduction `kr_spec`) gives the group of the coset (`cm_zero_ent`); the choice
   `cm_ch_spec` picks the representative.

Either way the new state stands for the candidates at stage `0` of the pair
(`cm_pair_cons_rep`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-- The cost of the start of a pair, for program states of weight at most `W`. -/
noncomputable def cmStCost (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) (W : ℕ) : ℕ :=
  8 * cpG hst hpre hm W + cmFindCost hm W + 10 ^ 4 * (W + 20)

section Start

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : SuppliedLabels S} {Cs : Set (Aggregation P₀ S L.toGiantLabels)}
  {Ag₀ : Aggregation P₀ S L.toGiantLabels} {O : TestTupleOrder L.q P₀.κ}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
/-- **The start of a pair meets `CmStartOK`.** -/
theorem cm_start_ok (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)
    {Pg : Program} {b jm jp : ℕ} (hat : CmMvAt0 Pg b jm) (hsa : CmStAt Pg b jp)
    (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.toGiantLabels.π g)
    {sv : Val} {ps fx fy : GPairs k L.q} {logs : List (CmLog k L.q)}
    (hps : PairGens e L.toGiantLabels S.G ps) (hpl : ps.length ≤ (k + L.q) ^ 2)
    {M₀ Bw W : ℕ}
    (hBw : cmBw (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)).wt k L.q M₀
      (O.tuples.length * O.tuples.length) ≤ Bw) (hW : 100 * Bw + 1000 ≤ W)
    (hW2 : 10 ^ 10 * (k + L.q + 1) ^ 12 ≤ W) (Out : List Bool → Val → Prop) :
    CmStartOK e Cs Ag₀ O πd Pg b W (cmStCost hst hpre hm W)
      (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)) Out Bw M₀ := by
  intro m f acc ps' σ ents rec u hmeq hmf hM hc hF hlen hfl hacc hps' hlt hwt
  set par := cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom) with hpar
  set N := O.tuples.length with hN
  obtain ⟨hP5, hparB⟩ := cm_st_sizes hBw
  set P := (N + 1) * (k + L.q + 1) ^ 6 with hP
  obtain ⟨f1, f2, f3, f24, f46, -, -, -, -, -⟩ := cp_pow_facts k L.q
  have hP6 : (k + L.q + 1) ^ 6 ≤ P := Nat.le_mul_of_pos_left _ (by omega)
  have hPN : N + 1 ≤ P := Nat.le_mul_of_pos_right _ (by omega)
  have g0 : k + L.q + 1 ≤ (k + L.q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  -- the pair
  obtain ⟨hi1, hi2, hdrop⟩ := cm_pairs_drop O hlt
  set T1 := O.tuples[acc.length / N] with hT1
  set T2 := O.tuples[acc.length % N] with hT2
  rw [hdrop] at hps'
  subst hps'
  have hκ : P₀.κ ≤ L.q := by
      have := Fintype.card_le_of_embedding T1.2
      rwa [Fintype.card_fin, Fintype.card_fin] at this
  set t : Fin P₀.κ → Fin L.q := (T1.2 : Fin P₀.κ → Fin L.q) with ht
  set t' : Fin P₀.κ → Fin L.q := (T2.2 : Fin P₀.κ → Fin L.q) with ht'
  set X := cmLabPts k t with hX
  set X' := cmLabPts k t' with hX'
  have hXl : X.length ≤ L.q := by rw [hX, cm_lab_length]; exact hκ
  have hXl' : X'.length ≤ L.q := by rw [hX', cm_lab_length]; exact hκ
  have hXw := cm_wt_key (k := k) (q := L.q) hXl
  have hXw' := cm_wt_key (k := k) (q := L.q) hXl'
  -- the program state
  set ks := σ.vals par with hks
  have hsv : σ.val par = .list ks := rfl
  have hwW : (Val.list [.list ks, u]).wt ≤ W := by rw [← hsv]; omega
  have h0 : ∀ rest : List Val, (Val.list [.list ks, u] :: rest)[0]? = some (.list [.list ks, u]) :=
    fun _ => rfl
  set pv : List Val := [sv, .list [.nat k, .nat L.q], .list (ps.map pairV),
    .list (fx.map pairV), .list (fy.map pairV), .list (logs.map cmLogV), .list (O.tuples.map stTT),
    .nat (Fintype.card S.dom), .nat N] with hpv
  have hp0 : ks[0]? = some (.list pv) := rfl
  have hpvW : ∀ v ∈ pv, v.wt < Bw := fun v hv => lt_trans (cm_wt_lt_of_mem hv) hparB
  have hksB : (Val.list ks).wt < Bw := by
    have := cm_wt_lt_of_mem (vs := [.list ks, u]) (v := .list ks) (by simp)
    rw [← hsv] at this ⊢
    omega
  have hkqB : (Val.list [.nat k, .nat L.q]).wt < Bw := hpvW _ (by simp [hpv])
  have hpsB : (Val.list (ps.map pairV)).wt < Bw := hpvW _ (by simp [hpv])
  have httB : (Val.list (O.tuples.map stTT)).wt < Bw := hpvW _ (by simp [hpv])
  have hNB : (Val.nat N).wt < Bw := hpvW _ (by simp [hpv])
  have hcB : (Val.list (σ.cache.map cmEntV)).wt < Bw := by
    have := cm_wt_lt_of_mem (vs := ks) (v := .list (σ.cache.map cmEntV)) (by simp [hks, CmSt.vals])
    omega
  have hAl : acc.length + 2 ≤ W := by
    have h1 := length_lt_wt_list (σ.acc.map boolVal)
    have h2 := cm_wt_lt_of_mem (vs := ks) (v := .list (σ.acc.map boolVal)) (by simp [hks, CmSt.vals])
    simp only [List.length_map] at h1
    rw [← hacc]
    omega
  -- reading the pieces
  have dK : ∀ rest, Det Pg (.list [.list ks, u] :: rest) (.get (cpPf 1) (.nat 0)) (.nat k)
      (5 * (W + 20)) := fun rest =>
    Det.rd (cp_rdP (P := Pg) (h0 rest) hwW hp0 (j := 1) rfl (by omega)) le_rfl rfl
      (by have := wt_nat_le k; have := cm_wt_lt_of_mem (vs := [Val.nat k, .nat L.q])
            (v := .nat k) (by simp); omega) (by omega)
  have dKQ := fun rest => cp_rdP (P := Pg) (h0 rest) hwW hp0 (j := 1)
    (v := .list [.nat k, .nat L.q]) rfl (by omega)
  have dPS := fun rest => cp_rdP (P := Pg) (h0 rest) hwW hp0 (j := 2)
    (v := .list (ps.map pairV)) rfl (by omega)
  have dTT := fun rest => cp_rdP (P := Pg) (h0 rest) hwW hp0 (j := 6)
    (v := .list (O.tuples.map stTT)) rfl (by omega)
  have dN := fun rest => cp_rdP (P := Pg) (h0 rest) hwW hp0 (j := 8) (v := .nat N) rfl (by omega)
  have dA := fun rest => cp_rdK (P := Pg) (h0 rest) hwW (j := 4)
    (v := .list (σ.acc.map boolVal)) rfl (by omega)
  have dK3 := fun rest => cp_rdK (P := Pg) (h0 rest) hwW (j := 3)
    (v := .list (σ.cache.map cmEntV)) rfl (by omega)
  have dK0 := fun rest => cp_rdK (P := Pg) (h0 rest) hwW (j := 0) (v := par) rfl (by omega)
  have dKs := fun rest => cp_rdKs (P := Pg) (h0 rest) hwW
  have hlenA : (σ.acc.map boolVal).length = acc.length := by rw [List.length_map, hacc]
  -- the label points of a tuple at index `i`
  have dLab : ∀ (rest : List Val) (iE : Expr) (i : ℕ) (T : TestTuple L.q P₀.κ),
      (O.tuples.map stTT)[i]? = some (stTT T) →
      Det Pg (.list [.list ks, u] :: rest) iE (.nat i) (10 * (W + 20)) →
      CpEB Pg (.list [.list ks, u] :: rest) (cmLabE b iE) W (cpG hst hpre hm W + 60 * (W + 20))
        (fun w => w = natList (ptsKey (cmLabPts k (T.2 : Fin P₀.κ → Fin L.q)))) := by
    intro rest iE i T hT dI
    obtain ⟨bT, tT⟩ := T
    have hT' : (O.tuples.map stTT)[i]? = some (.list [boolVal bT, stTv (tT : Fin P₀.κ → Fin L.q)]) :=
      hT
    have hTw : (Val.list [boolVal bT, stTv (tT : Fin P₀.κ → Fin L.q)]).wt < Bw :=
      lt_trans (cm_wt_lt_of_mem (List.mem_of_getElem? hT')) httB
    have dT := Det.get' (dTT rest) dI hT'
    have hmem : stTv (tT : Fin P₀.κ → Fin L.q) ∈ [boolVal bT, stTv (tT : Fin P₀.κ → Fin L.q)] :=
      List.mem_cons_of_mem _ (List.mem_singleton_self _)
    have hvw : (stTv (tT : Fin P₀.κ → Fin L.q)).wt < Bw := lt_trans (cm_wt_lt_of_mem hmem) hTw
    have dV : Det Pg (.list [.list ks, u] :: rest) (.get (.get (cpPf 6) iE) (.nat 1))
        (stTv (tT : Fin P₀.κ → Fin L.q)) (20 * (W + 20)) :=
      (Det.get' dT (Det.nat 1) (v := stTv (tT : Fin P₀.κ → Fin L.q)) rfl).mono
        (by omega)
    have dArg := Det.mk2 (dK rest) dV
    have hAw : (Val.list [.nat k, stTv (tT : Fin P₀.κ → Fin L.q)]).wt ≤ W := by
      have := wt_list2_le (.nat k) (stTv (tT : Fin P₀.κ → Fin L.q))
      have := wt_nat_le k
      have : k ≤ (k + L.q + 1) ^ 6 := by
        have : k + L.q + 1 ≤ (k + L.q + 1) ^ 6 := Nat.le_self_pow (by omega) _
        omega
      omega
    have hκ' : P₀.κ ≤ L.q := by
      have := Fintype.card_le_of_embedding tT
      rwa [Fintype.card_fin, Fintype.card_fin] at this
    refine (CpEB.call (Cb := cpG hst hpre hm W) (CpEB.det dArg le_rfl hAw (Q := fun v =>
      v = .list [.nat k, stTv (tT : Fin P₀.κ → Fin L.q)]) rfl) fun v hv _ => ?_).mono
      (by omega) fun _ h => h
    subst hv
    exact cm_bud_sh (k := k) hst hpre hm hsa tT hκ' (by omega)
  have hTi : ∀ (i : ℕ) (hi : i < N), (O.tuples.map stTT)[i]? = some (stTT O.tuples[i]) :=
    fun i hi => by rw [List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
  -- the indices
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
  -- the new state is light
  have hm1 : 1 ≤ m := by rw [hmeq]; simp only [cmMs, cmMeas]; omega
  have hnew : ∀ (o' : Option (Perm (Fin k))) (cache' : List (List (Perm (Fin k)) × Perm (Fin k))),
      cache'.length ≤ σ.cache.length + 1 → (∀ p ∈ cache', p.1.length ≤ (k + L.q) ^ 2) →
      (Val.list [(⟨0, o', cache', σ.acc, 1⟩ : CmSt k).val par, .list []]).wt ≤ Bw := by
    intro o' cache' hcl hcl'
    refine le_trans (cm_wt_state (q := L.q) (M₀ := M₀) (L := N * N)
      ?_ ?_ ?_ hcl' ?_ cm_wt_nil_le) hBw
    · show 0 ≤ k; omega
    · show 1 ≤ 2; omega
    · show cache'.length ≤ M₀; omega
    · show σ.acc.length ≤ _; rw [hacc]; exact hlt.le
  refine CpFB.intro hsa.start ?_
  unfold cmStartF
  rw [hsv]
  -- step 1: the label points of `t` and `t'`
  refine (CpEB.letE (Cb := 7 * cpG hst hpre hm W + cmFindCost hm W + 8000 * (W + 20))
    (dLab [] _ _ _ (hTi _ hi1) (dDiv [])) fun v1 hv1 _ => ?_).mono (by unfold cmStCost; omega) fun _ h => h
  subst hv1
  refine (CpEB.letE (Cb := 6 * cpG hst hpre hm W + cmFindCost hm W + 7000 * (W + 20))
    (dLab [natList (ptsKey X)] _ _ _ (hTi _ hi2) (dMod _)) fun v2 hv2 _ => ?_).mono (by omega)
    fun _ h => h
  subst hv2
  -- step 2: the orbit and the search
  set env2 : List Val := [.list [.list ks, u], natList (ptsKey X), natList (ptsKey X')] with henv2
  have hTa : (Val.list [.list [.nat k, .nat L.q], .list (ps.map pairV), natList (ptsKey X),
      .nat N]).wt ≤ W := by
    have := wt_list4_le (.list [.nat k, .nat L.q]) (.list (ps.map pairV)) (natList (ptsKey X))
      (.nat N)
    omega
  have dTa : Det Pg env2 (mk4 (cpPf 1) (cpPf 2) (.var 1) (cpPf 8))
      (.list [.list [.nat k, .nat L.q], .list (ps.map pairV), natList (ptsKey X), .nat N])
      (30 * (W + 20)) := by
    refine (Det.mk4 (dKQ _) (dPS _) (Det.var' (i := 1) rfl) (dN _)).mono ?_
    omega
  refine (CpEB.letE (Cb := 5 * cpG hst hpre hm W + cmFindCost hm W + 6000 * (W + 20))
    (CpEB.call (CpEB.det dTa le_rfl hTa (Q := fun v => v = .list [.list [.nat k, .nat L.q],
      .list (ps.map pairV), natList (ptsKey X), .nat N]) rfl) fun v hv _ => by
        subst hv
        exact cm_bud_tup hst hpre hm hsa O hpl T1.2 (by rw [← hN]; omega)) fun v3 hv3 _ => ?_).mono
    (by omega) fun _ h => h
  obtain ⟨Lo, rfl, hnd, hmem, hgood, hLl, hLw⟩ := hv3
  rw [← hN] at hLl hLw
  set env3 := env2 ++ [encPairs ptsKey Lo] with henv3
  have hFa : (Val.list [natList (ptsKey X'), encPairs ptsKey Lo]).wt ≤ W := by
    have := wt_list2_le (natList (ptsKey X')) (encPairs ptsKey Lo)
    omega
  have dFa : Det Pg env3 (mk2 (.var 2) (.var 3))
      (.list [natList (ptsKey X'), encPairs ptsKey Lo]) (10 * (W + 20)) := by
    refine (Det.mk2 (Det.var' (i := 2) rfl) (Det.var' (i := 3) rfl)).mono ?_
    omega
  set i := Lo.findIdx (fun r => decide (r.1 = X')) with hi
  have hiL : i ≤ Lo.length := List.findIdx_le_length
  have hiW : (Val.nat i).wt ≤ W := by have := wt_nat_le i; omega
  refine (CpEB.letE (Cb := 4 * cpG hst hpre hm W + cmFindCost hm W + 5000 * (W + 20))
    (CpEB.call (CpEB.det dFa le_rfl hFa (Q := fun v => v =
      .list [natList (ptsKey X'), encPairs ptsKey Lo]) rfl) fun v hv _ => by
        subst hv
        exact cm_bud_kfd hst hpre hm hsa X' Lo hFa) fun v4 hv4 _ => ?_).mono
    (by omega) fun _ h => h
  subst hv4
  set env4 := env3 ++ [.nat i] with henv4
  have dI : Det Pg env4 (.var 4) (.nat i) (W + 1) := (Det.var' rfl).mono (by omega)
  have hLlen : (Lo.map (GI.Lang.encPair ptsKey)).length = Lo.length := List.length_map _
  have dLL : Det Pg env4 (.length (.var 3)) (.nat Lo.length) (2 * (W + 20)) := by
    have d0 := Det.length (Det.var' (P := Pg) (env := env4) (i := 3)
      (v := .list (Lo.map (GI.Lang.encPair ptsKey))) rfl)
    rw [hLlen] at d0
    refine d0.mono ?_
    have e : (encPairs ptsKey Lo).wt = (Val.list (Lo.map (GI.Lang.encPair ptsKey))).wt := rfl
    omega
  have dLt := Det.arith' (op := .lt) dI dLL (z := if i < Lo.length then 1 else 0) rfl
  have hlt01 := wt_nat_le (if i < Lo.length then 1 else 0)
  by_cases hfound : i < Lo.length
  · -- step 4: the coset is not empty
    rw [if_pos hfound] at dLt hlt01
    set r : List (Fin (k + L.q)) × Perm (Fin (k + L.q)) := Lo[i]'hfound with hr
    have hrX : r.1 = X' := by
      have := List.findIdx_getElem
        (p := fun r : List (Fin (k + L.q)) × Perm (Fin (k + L.q)) => decide (r.1 = X'))
        (w := hfound)
      simpa using this
    obtain ⟨hrg, hrmap⟩ := hgood r (List.getElem_mem hfound)
    obtain ⟨pp, -, hpp⟩ := mem_gens_encPair.1 hrg
    have hpg : encPair pp ∈ gens (ps.map encPair) := hpp ▸ hrg
    have hmap : (cmLabPts k t).map (encPair pp) = cmLabPts k t' := by rw [hpp, hrmap, hrX]
    refine (CpEB.ite dLt (Ct := 4 * cpG hst hpre hm W + cmFindCost hm W + 4000 * (W + 20))
      (Ce := 0) (fun _ => ?_) fun h => absurd h one_ne_zero).mono (by omega) fun _ h => h
    -- the stabilizer
    have hSa : (Val.list [.list [.nat k, .nat L.q], .list (ps.map pairV),
        natList (ptsKey X)]).wt ≤ W := by
      have := wt_list_le [.list [.nat k, .nat L.q], .list (ps.map pairV), natList (ptsKey X)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at this
      omega
    have dSa : Det Pg env4 (mk3 (cpPf 1) (cpPf 2) (.var 1))
        (.list [.list [.nat k, .nat L.q], .list (ps.map pairV), natList (ptsKey X)])
        (30 * (W + 20)) := by
      refine (Det.mk3 (dKQ _) (dPS _) (Det.var' (i := 1) rfl)).mono ?_
      omega
    refine (CpEB.letE (Cb := 3 * cpG hst hpre hm W + cmFindCost hm W + 3000 * (W + 20))
      (CpEB.call (CpEB.det dSa le_rfl hSa (Q := fun v => v = .list [.list [.nat k, .nat L.q],
        .list (ps.map pairV), natList (ptsKey X)]) rfl) fun v hv _ => by
          subst hv
          exact cm_bud_stab hst hpre hm hsa hjp hpl hXl hW2) fun v5 hv5 _ => ?_).mono
      (by omega) fun _ h => h
    obtain ⟨qs, rfl, hql, hqcl⟩ := hv5
    set env5 := env4 ++ [.list (qs.map pairV)] with henv5
    have hqw := cp_wt_gp (k := k) (q := L.q) hql
    have hKa : (Val.list [.nat k, gpV qs]).wt ≤ W := by
      have := wt_list2_le (.nat k) (gpV qs)
      have := wt_nat_le k
      have : k ≤ (k + L.q + 1) ^ 6 := by
        have : k + L.q + 1 ≤ (k + L.q + 1) ^ 6 := Nat.le_self_pow (by omega) _
        omega
      omega
    have dKa : Det Pg env5 (mk2 (.get (cpPf 1) (.nat 0)) (.var 5)) (.list [.nat k, gpV qs])
        (30 * (W + 20)) := by
      refine (Det.mk2 (dK _) (Det.var' (i := 5) (v := gpV qs) rfl)).mono ?_
      omega
    refine (CpEB.letE (Cb := 2 * cpG hst hpre hm W + cmFindCost hm W + 2000 * (W + 20))
      (CpEB.call (CpEB.det dKa le_rfl hKa (Q := fun v => v = .list [.nat k, gpV qs]) rfl)
        fun v hv _ => by
          subst hv
          exact cp_bud_kr hst hpre hm hsa.kr hjp hql hW2) fun v6 hv6 _ => ?_).mono
      (by omega) fun _ h => h
    obtain ⟨hs, rfl, hgs, hhl⟩ := hv6
    set env6 := env5 ++ [encGroup hs] with henv6
    have hgw := wt_encGroup_le_sq hhl
    -- the first part of the transversal element
    have hLi : (Lo.map (GI.Lang.encPair ptsKey))[i]? = some (GI.Lang.encPair ptsKey r) := by
      simp [hr, hfound]
    have dE : Det Pg env6 (.get (.get (.var 3) (.var 4)) (.nat 1)) (encPerm (encPair pp))
        (10 * (W + 20)) := by
      have d1 := Det.get' (Det.var' (P := Pg) (env := env6) (i := 3)
        (v := .list (Lo.map (GI.Lang.encPair ptsKey))) rfl) (Det.var' (i := 4) rfl) hLi
      have d2 := Det.get' d1 (Det.nat 1) (vs := [natList (ptsKey r.1), encPerm r.2]) rfl
      rw [hpp]
      refine d2.mono ?_
      have e : (encPairs ptsKey Lo).wt = (Val.list (Lo.map (GI.Lang.encPair ptsKey))).wt := rfl
      have h1 := cm_wt_lt_of_mem (List.mem_of_getElem? hLi)
      have h2 := cm_wt_lt_of_mem (vs := [natList (ptsKey r.1), encPerm r.2]) (v := encPerm r.2)
        (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      have e2 : (GI.Lang.encPair ptsKey r).wt = (Val.list [natList (ptsKey r.1), encPerm r.2]).wt :=
        rfl
      omega
    have hk2 : 100 * (k + 1) ^ 2 ≤ W := by
      have : (k + 1) ^ 2 ≤ (k + L.q + 1) ^ 6 := le_trans f3 (le_trans f24 f46)
      omega
    have dR : CpEB Pg env6 (.call (cmRng b) (.get (cpPf 1) (.nat 0))) W
        (cpG hst hpre hm W + 10 * (W + 20)) (fun w => w = encPerm (1 : Perm (Fin k))) :=
      (CpEB.call (CpEB.det (dK _) le_rfl (by have := wt_nat_le k; omega)
        (Q := fun v => v = .nat k) rfl) fun v hv _ => by
          subst hv
          exact cm_bud_rng hst hpre hm hsa hk2).mono (by omega) fun _ h => h
    have hpe := wt_encPerm_le (encPair pp)
    have hpe1 := wt_encPerm_le (1 : Perm (Fin k))
    have hpa := wt_encPerm_le pp.1
    have hk6 : (k + 1) ^ 2 ≤ (k + L.q + 1) ^ 6 := le_trans f3 (le_trans f24 f46)
    have hkq2 : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 6 := le_trans f24 f46
    refine (CpEB.letE (Cb := cmFindCost hm W + 1500 * (W + 20))
      (CpEB.call (Ca := cpG hst hpre hm W + 30 * (W + 20)) (Qa := fun v =>
          v = .list [encPerm (encPair pp), encPerm (1 : Perm (Fin k))]) ?_ fun v hv _ => by
        subst hv
        exact cm_bud_gat hst hpre hm hsa pp (by omega)) fun v7 hv7 _ => ?_).mono
      (by omega) fun _ h => h
    · -- the argument of the gather
      have := wt_list2_le (encPerm (encPair pp)) (encPerm (1 : Perm (Fin k)))
      refine EvalAll.snoc_det (Det.mk1 dE) dR |>.mono fun w c h => ?_
      obtain ⟨w', cb, ⟨rfl, -, hcb⟩, rfl, hc'⟩ := h
      refine ⟨rfl, by simpa using (by omega : _ ≤ W), ?_⟩
      have : (Val.list ([encPerm (encPair pp)] ++ [encPerm (1 : Perm (Fin k))])).wt =
        (Val.list [encPerm (encPair pp), encPerm (1 : Perm (Fin k))]).wt := rfl
      have := wt_list1_le (encPerm (encPair pp))
      omega
    subst hv7
    set env7 := env6 ++ [encPerm pp.1] with henv7
    -- the entry of the coset
    obtain ⟨E, hE, hset⟩ := cm_zero_ent (L := L.toGiantLabels) (πd := πd) hπ hps t t' hqcl hpg
      hmap (dstr S (cmZ S T1.1)) (dstr S (cmZ S T2.1))
    have hE' : CmEntOK e S (hs, pp.1) E := by
      obtain ⟨h1, h2, h3, h4⟩ := hE
      exact ⟨h1, by rw [hgs]; exact h2, h3, h4⟩
    have hhl' : hs.length ≤ (k + L.q) ^ 2 :=
      hhl.trans (Nat.pow_le_pow_left (by omega) 2)
    have hkey : (cmKeyV hs pp.1).wt ≤ 1000 * (k + L.q + 1) ^ 6 := by
      have := wt_list2_le (encGroup hs) (encPerm pp.1)
      have : (k + 1) ^ 6 ≤ (k + L.q + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      unfold cmKeyV
      omega
    have hCa : (Val.list [σ.val par, cmKeyV hs pp.1]).wt ≤ 4 * Bw + 6 := by
      have := wt_list2_le (σ.val par) (cmKeyV hs pp.1)
      rw [hsv] at this ⊢
      omega
    have dCa : Det Pg env7 (mk2 cpKs (mk2 (.var 6) (.var 7)))
        (.list [.list ks, cmKeyV hs pp.1]) (20 * (W + 20)) := by
      refine (Det.mk2 (dKs _) (Det.mk2 (Det.var' (i := 6) rfl) (Det.var' (i := 7) rfl))).mono ?_
      have := wt_list2_le (encGroup hs) (encPerm pp.1)
      have : (cmKeyV hs pp.1).wt = (Val.list [encGroup hs, encPerm pp.1]).wt := rfl
      have : (Val.list [.list ks, cmKeyV hs pp.1]).wt =
        (Val.list [.list ks, .list [encGroup hs, encPerm pp.1]]).wt := rfl
      have := wt_list2_le (Val.list ks) (cmKeyV hs pp.1)
      rw [hsv] at hCa
      omega
    refine (CpEB.call (Cb := cmFindCost hm W + 1000 * (W + 20)) (CpEB.det dCa le_rfl (by rw [hsv] at hCa; omega)
      (Q := fun v => v = .list [.list ks, cmKeyV hs pp.1]) rfl) fun v hv _ => ?_).mono (by omega)
      fun _ h => h
    subst hv
    rw [← hsv]
    refine (cm_ch_spec (L := L) hm hat hsa hjm hE' hhl' hW (Bk := 4 * Bw + 6) (by omega) hCa
      hnew hlen).mono le_rfl fun w hw => ?_
    obtain ⟨o', cache', hch, hcl', hw', rfl⟩ := hw
    rw [hset] at hch
    rw [hacc] at hw' ⊢
    exact Or.inr ⟨_, cm_pair_cons_rep hmeq hmf hM hc hF hlen hdrop hch hw', rfl⟩
  · -- step 3: the coset is empty
    rw [if_neg hfound] at dLt hlt01
    have hno : cmLabPts k t' ∉ actOrbit (fun g (xs : List (Fin (k + L.q))) => xs.map g)
        (ps.map encPair) (cmLabPts k t) := by
      intro hin
      obtain ⟨r, hr, hr1⟩ := List.mem_map.1 ((hmem _).2 hin)
      have : i < Lo.length := by
        rw [hi]
        exact List.findIdx_lt_length_of_exists ⟨r, hr, by simpa using hr1⟩
      exact hfound this
    have hemp := cm_init_empty (L := L.toGiantLabels) πd hπ hps hno (dstr S (cmZ S T1.1))
      (dstr S (cmZ S T2.1))
    have hch : CmChoice (e := e) (L := L) σ.cache
        (GI.LocalCertificates.lockstep S.domGroup πd 0 (dstr S (cmZ S T1.1)) t (dstr S (cmZ S T2.1)) t') none
        σ.cache := Or.inl ⟨hemp, rfl, rfl⟩
    have hw' := hnew none σ.cache le_self_add hlen
    have dl := cp_mkList' (P := Pg) (env := env4) (W := W) (c := 10 * (W + 20))
      [(cpKf 0, par), (.nat 0, .nat 0), (.nil, cmOV (none : Option (Perm (Fin k)))),
        (cpKf 3, .list (σ.cache.map cmEntV)), (cpKf 4, .list (σ.acc.map boolVal)),
        (.nat 1, .nat 1)] (v := (⟨0, none, σ.cache, σ.acc, 1⟩ : CmSt k).val par) rfl (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
        · exact (dK0 _).mono (by omega)
        · exact (Det.nat 0).mono (by omega)
        · exact Det.nil.mono (by omega)
        · exact (dK3 _).mono (by omega)
        · exact (dA _).mono (by omega)
        · exact (Det.nat 1).mono (by omega))
      (by
        have := cm_wt_lt_of_mem (vs := [(⟨0, none, σ.cache, σ.acc, 1⟩ : CmSt k).val par, .list []])
          (v := (⟨0, none, σ.cache, σ.acc, 1⟩ : CmSt k).val par) (by simp)
        omega)
    refine (CpEB.ite dLt (Ct := 0) (Ce := 6 * (11 * (W + 20) + W + 1) + 5 + 2 * W + 100)
      (fun h => absurd rfl h) fun _ => ?_).mono (by omega) fun _ h => h
    refine (cm_ret_eb dl hw' hW).mono (by simp only [List.length_cons, List.length_nil]; omega)
      fun w hw => ?_
    subst hw
    rw [hacc] at hw' ⊢
    exact Or.inr ⟨_, cm_pair_cons_rep hmeq hmf hM hc hF hlen hdrop hch hw', rfl⟩

end Start

end GI.Impl
