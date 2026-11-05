module

public import Workspace.Impl.AggItemStepWt
public import Workspace.Impl.AggItemC1Prog

@[expose] public section

/-!
# The Case 1 item meets its contract

In Case 1 the item of every branch is `caseOneItem X Y`; it asks no call, and it depends on the
branch only through the groups of `X` and `Y`, which are the same for all branches. So the case
keeps nothing between the branches (the kept value is `0`), and its branch step finishes at once.

The branch step `itSC1F grp orb c1` on `[K.v, stTv b, 0]`:
1. reads the start state `st` and `q`;
2. computes `encGroup` of the second parts of `fx` and of `fy` (`it_grp_spec`);
3. computes their orbit labels (`orbits_spec`);
4. calls the Case 1 program `itC1F` (`it_c1_prog`) on the two labelings;
5. returns `[0, [⟨⟩, ⟨overcosets⟩, 0]]`.

`it_c1_itemM` says that for every round of the base set the script of the item is finished with
no piece and overcosets for which the program's list stands (`asOvAt`). `itS_c1_caseOK` is the
contract `ItSCaseOK` for the case `.one`, with the bound `itSC1X`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms gens encGroup encKColoring)

variable {Ω C : Type} {k : ℕ}

/-! ### The program -/

/-- On `[G, tb, cache]` with `G = [st, …]`: the Case 1 item. -/
def itSC1F (grp orb c1 : ℕ) : Expr :=
  .letE (.get (arg 0) (.nat 0))
  (.letE (.get (.get (.var 1) (.nat 1)) (.nat 1))
  (.letE (.call grp (mk2 (.var 2) (.get (.var 1) (.nat 3))))
  (.letE (.call grp (mk2 (.var 2) (.get (.var 1) (.nat 4))))
  (.letE (.call orb (.var 3))
  (.letE (.call orb (.var 4))
  (.letE (.call c1 (mk2 (.var 5) (.var 6)))
    (mk2 (.nat 0) (mk3 .nil (.var 7) (arg 2)))))))))

/-- The init program of Case 1: the kept value `0`. -/
def itSC1IF : Expr := .nat 0

/-- The cost bound of `itSC1F` for inputs of weight at most `W`. -/
def itSC1C (W : ℕ) : ℕ := 10 ^ 13 * (W + 1) ^ 10

/-- **The branch step of Case 1, as values**, for a size `M` at least the input weight and `q`. -/
theorem it_sc1_prog {Pg : Program} {fb grp orb rb mp sf app : ℕ} {IC : ItC1Idx}
    (hfb : Pg.funs[fb]? = some (itSC1F grp orb IC.f))
    (hgrp : Pg.funs[grp]? = some (itGrpF rb mp app)) (hrb : Pg.HasAt rb (rangeFuns rb))
    (hmp : Pg.HasAt mp (mapFuns mp sf)) (hsf : Pg.funs[sf]? = some itSndF)
    (happ : Pg.HasAt app (appendFuns app)) (horb : Pg.HasAt orb (orbitFuns orb))
    (hc1 : ItC1Ok Pg IC) {q : ℕ} (sv psV cv ws cd sr tb cache : Val)
    (fx fy : List (Perm (Fin k) × Perm (Fin q)))
    (hex : ∀ labX : Fin q → ℕ, ItcLab (1 :: fx.map Prod.snd) labX → ∃ a : Fin q, labX a ≠ a)
    (E₀ : Subgroup (alternatingGroup (Fin q))) {M : ℕ}
    (hM : (Val.list [.list [.list [sv, .list [.nat k, .nat q], psV, .list (fx.map pairV),
          .list (fy.map pairV), cv], ws, cd, sr], tb, cache]).wt ≤ M) (hqM : q ≤ M) :
    ∃ (labX labY : Fin q → ℕ) (hlX : ItcLab (1 :: fx.map Prod.snd) labX)
      (_ : ItcLab (1 :: fy.map Prod.snd) labY) (a : Fin q) (ha : labX a ≠ a),
      FunDet Pg fb (.list [.list [.list [sv, .list [.nat k, .nat q], psV, .list (fx.map pairV),
          .list (fy.map pairV), cv], ws, cd, sr], tb, cache])
        (.list [.nat 0, .list [.list [], .list ((itcOsM hlX labY ha E₀ (itcMs labX a)).map
          fun o => lcOv (o.1 : Perm (Fin q)) o.2.2), cache]])
        (itSC1C M) := by
  set st := Val.list [sv, .list [.nat k, .nat q], psV, .list (fx.map pairV),
    .list (fy.map pairV), cv] with hst
  set G := Val.list [st, ws, cd, sr] with hG
  set bst := Val.list [G, tb, cache] with hbst
  have wG : G.wt < bst.wt := wt_le_wt_list (by simp)
  have wst : st.wt < G.wt := wt_le_wt_list (by simp)
  have wc : cache.wt < bst.wt := wt_le_wt_list (by simp)
  have wkq : (Val.list [.nat k, .nat q]).wt < st.wt := wt_le_wt_list (by simp)
  have wq : (Val.nat q).wt < (Val.list [.nat k, .nat q]).wt := wt_le_wt_list (by simp)
  have wfx : (Val.list (fx.map pairV)).wt < st.wt := wt_le_wt_list (by simp)
  have wfy : (Val.list (fy.map pairV)).wt < st.wt := wt_le_wt_list (by simp)
  have lfx : (fx.map pairV).length < (Val.list (fx.map pairV)).wt := length_lt_wt_list _
  have lfy : (fy.map pairV).length < (Val.list (fy.map pairV)).wt := length_lt_wt_list _
  rw [List.length_map] at lfx lfy
  -- the groups
  have hgx := it_grp_spec hgrp hrb hmp hsf happ fx (W := M) (by omega) hqM
  have hgy := it_grp_spec hgrp hrb hmp hsf happ fy (W := M) (by omega) hqM
  have wgx := it_grp_wt fx (W := M) (by omega) hqM
  have wgy := it_grp_wt fy (W := M) (by omega) hqM
  -- the labels
  obtain ⟨labX, hoX, hX1, hX2⟩ := orbits_spec horb (1 :: fx.map Prod.snd)
  obtain ⟨labY, hoY, hY1, hY2⟩ := orbits_spec horb (1 :: fy.map Prod.snd)
  have hlX : ItcLab (1 :: fx.map Prod.snd) labX := ⟨hX1, hX2⟩
  have hlY : ItcLab (1 :: fy.map Prod.snd) labY := ⟨hY1, hY2⟩
  have wlX : (encFun labX).wt ≤ 4 * (q + 1) ^ 2 :=
    wt_encFun_le_sq labX fun x => (hX2 x).1.le
  have wlY : (encFun labY).wt ≤ 4 * (q + 1) ^ 2 :=
    wt_encFun_le_sq labY fun x => (hY2 x).1.le
  -- the item
  obtain ⟨a, ha, hc⟩ := it_c1_prog hc1 hlX hlY (hex labX hlX) E₀
  set osV := Val.list ((itcOsM hlX labY ha E₀ (itcMs labX a)).map
    fun o => lcOv (o.1 : Perm (Fin q)) o.2.2) with hosV
  have wos : osV.wt < itC1C q := FunDet.wt_lt hc
  refine ⟨labX, labY, hlX, hlY, a, ha, FunDet.intro hfb ?_⟩
  -- the chain
  have d1 : Det Pg [bst] (.get (arg 0) (.nat 0)) st _ :=
    Det.get' (Det.arg' (vs := [G, tb, cache]) (rest := []) (j := 0) rfl) (Det.nat 0)
      (vs := [st, ws, cd, sr]) rfl
  have d2 : Det Pg [bst, st] (.get (.get (.var 1) (.nat 1)) (.nat 1)) (.nat q) _ :=
    Det.get' (Det.get' (Det.var' (i := 1) rfl) (Det.nat 1) (vs := [sv, .list [.nat k, .nat q], psV,
      .list (fx.map pairV), .list (fy.map pairV), cv]) rfl) (Det.nat 1) (vs := [.nat k, .nat q]) rfl
  have d3 : Det Pg [bst, st, .nat q] (.call grp (mk2 (.var 2) (.get (.var 1) (.nat 3))))
      (encGroup (fx.map Prod.snd)) _ :=
    Det.call (Det.mk2 (Det.var' (i := 2) rfl) (Det.get' (Det.var' (i := 1) rfl) (Det.nat 3)
      (vs := [sv, .list [.nat k, .nat q], psV, .list (fx.map pairV), .list (fy.map pairV), cv])
      rfl)) hgx
  have d4 : Det Pg [bst, st, .nat q, encGroup (fx.map Prod.snd)]
      (.call grp (mk2 (.var 2) (.get (.var 1) (.nat 4)))) (encGroup (fy.map Prod.snd)) _ :=
    Det.call (Det.mk2 (Det.var' (i := 2) rfl) (Det.get' (Det.var' (i := 1) rfl) (Det.nat 4)
      (vs := [sv, .list [.nat k, .nat q], psV, .list (fx.map pairV), .list (fy.map pairV), cv])
      rfl)) hgy
  have d5 : Det Pg [bst, st, .nat q, encGroup (fx.map Prod.snd), encGroup (fy.map Prod.snd)]
      (.call orb (.var 3)) (encFun labX) _ := Det.call (Det.var' (i := 3) rfl) hoX
  have d6 : Det Pg [bst, st, .nat q, encGroup (fx.map Prod.snd), encGroup (fy.map Prod.snd),
      encFun labX] (.call orb (.var 4)) (encFun labY) _ := Det.call (Det.var' (i := 4) rfl) hoY
  have d7 : Det Pg [bst, st, .nat q, encGroup (fx.map Prod.snd), encGroup (fy.map Prod.snd),
      encFun labX, encFun labY] (.call IC.f (mk2 (.var 5) (.var 6))) osV _ :=
    Det.call (Det.mk2 (Det.var' (i := 5) rfl) (Det.var' (i := 6) rfl)) hc
  have d8 : Det Pg [bst, st, .nat q, encGroup (fx.map Prod.snd), encGroup (fy.map Prod.snd),
      encFun labX, encFun labY, osV] (mk2 (.nat 0) (mk3 .nil (.var 7) (arg 2)))
      (.list [.nat 0, .list [.list [], osV, cache]]) _ :=
    Det.mk2 (Det.nat 0) (Det.mk3 Det.nil (Det.var' (i := 7) rfl)
      (Det.arg' (vs := [G, tb, cache]) (j := 2) rfl))
  refine (Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4 (Det.letE d5 (Det.letE d6
    (Det.letE d7 d8))))))).mono ?_
  -- the cost
  have wout := wt_list2_le (.nat 0) (.list [.list [], osV, cache])
  have wout3 := wt_list3_le (.list []) osV cache
  have wk1 := wt_list2_le (.nat q) (.list (fx.map pairV))
  have wk2 := wt_list2_le (.nat q) (.list (fy.map pairV))
  have wk3 := wt_list2_le (encFun labX) (encFun labY)
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have w2 := wt_nat_le 2
  have w3 := wt_nat_le 3
  have w4 := wt_nat_le 4
  have p1 : (M + 1) ^ 2 ≤ (M + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
  have p3 : (M + 1) ^ 3 ≤ (M + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
  have p5 : (M + 1) ^ 5 ≤ (M + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
  have p6 : (q + 1) ^ 6 ≤ (M + 1) ^ 10 :=
    (Nat.pow_le_pow_left (by omega) 6).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have pq2 : (q + 1) ^ 2 ≤ (M + 1) ^ 10 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have pM : M + 1 ≤ (M + 1) ^ 10 := by
    have := Nat.pow_le_pow_right (n := M + 1) (by omega) (show 1 ≤ 10 by omega)
    rwa [pow_one] at this
  have hlx : ((1 :: fx.map Prod.snd).length + 1) * (q + 1) ≤ (M + 1) ^ 2 := by
    rw [List.length_cons, List.length_map, sq]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hly : ((1 :: fy.map Prod.snd).length + 1) * (q + 1) ≤ (M + 1) ^ 2 := by
    rw [List.length_cons, List.length_map, sq]
    exact Nat.mul_le_mul (by omega) (by omega)
  have ox : (((1 :: fx.map Prod.snd).length + 1) * (q + 1)) ^ 5 ≤ (M + 1) ^ 10 := by
    have := Nat.pow_le_pow_left hlx 5
    rwa [← pow_mul] at this
  have oy : (((1 :: fy.map Prod.snd).length + 1) * (q + 1)) ^ 5 ≤ (M + 1) ^ 10 := by
    have := Nat.pow_le_pow_left hly 5
    rwa [← pow_mul] at this
  have eb : (Val.list [G, tb, cache]).wt = bst.wt := rfl
  have eG : (Val.list [st, ws, cd, sr]).wt = G.wt := rfl
  have es : (Val.list [sv, .list [.nat k, .nat q], psV, .list (fx.map pairV),
    .list (fy.map pairV), cv]).wt = st.wt := rfl
  have wn : (Val.list []).wt = 4 := wt_list_nil
  unfold itSC1C itC1C itGrpC orbitK at *
  simp only [Nat.reducePow] at *
  omega

/-! ### The rounds of the base set in Case 1 -/

/-- The second parts of graph pairs of the lift of `F_y` generate the group of the target
structure, for every individualized tuple. -/
theorem itS_gens_strY (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (Ag : Aggregation P₀ S L) {fy : List (Perm (Fin k) × Perm (Fin L.q))}
    (h : PairGens e L (itCertLift Ag.fin S Ag.πd P₀.κ S.y) fy) (t : Fin Ag.ℓ → Fin L.q) :
    gens (fy.map Prod.snd) = (Ag.strY t).grp :=
  it_snd_gens e L Ag.πd Ag.πd_spec _ h

section Base

variable {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S}
  {K : ItSCtx k S L}

/-- **The groups of the structures of a round of the base set** are those of the program. -/
theorem itS_grps (hK : K.OK e c) {Ag : Aggregation P₀ S L.toGiantLabels} (hAg : Ag ∈ itSBase K)
    (b : Fin (P₀.κ + 1) → Fin L.q) :
    (Ag.strX Ag.src).grp = gens (K.fx.map Prod.snd) ∧ (Ag.strY b).grp = gens (K.fy.map Prod.snd) := by
  have hR : Ag ∈ asRounds L := hK.sub (itSBase_sub hAg)
  have hR0 : K.Ag₀ ∈ asRounds L := hK.sub hK.mem
  have hfx : PairGens e L.toGiantLabels (itCertLift Ag.fin S Ag.πd P₀.κ S.x) K.fx := by
    rw [cm_certLift_eq hR hR0]; exact hK.hfx
  have hfy : PairGens e L.toGiantLabels (itCertLift Ag.fin S Ag.πd P₀.κ S.y) K.fy := by
    rw [cm_certLift_eq hR hR0]; exact hK.hfy
  exact ⟨(it_gens_strX e Ag hfx _).symm, (itS_gens_strY e Ag hfy b).symm⟩

/-- **The case of a round of the base set** is the case of the context. -/
theorem itS_case_eq (hK : K.OK e c) {Ag : Aggregation P₀ S L.toGiantLabels} (hAg : Ag ∈ itSBase K) :
    aggCase (Ag.strX Ag.src).grp = K.case := by
  rw [(itS_grps hK hAg (fun _ => ⟨0, it_q_pos Ag⟩)).1, ItSCtx.case,
    it_gens_itX0 e K.Ag₀ hK.hfx K.J]

/-- In Case 1 the item of a round of the base set is `caseOneItem`. -/
theorem itS_items_one (hK : K.OK e c) {Ag : Aggregation P₀ S L.toGiantLabels}
    (hAg : Ag ∈ itSBase K) (hc : K.case = .one) (b : Fin (P₀.κ + 1) → Fin L.q) :
    Ag.items b = caseOneItem (Ag.strX Ag.src) (Ag.strY b) := by
  have h := itS_case_eq hK hAg
  rw [hc] at h
  unfold Aggregation.items plan
  rw [h]

end Base

/-! ### The contract -/

/-- **The relations of Case 1**: the kept value is `0`; a branch state is `[K.v, stTv b, 0]` at
the start of the item script. -/
noncomputable def itSC1Rel : ItSCaseRel where
  Kc _ _ _ _ K w D := w = .nat 0 ∧ D ⊆ itSBase K ∧ D.Nonempty
  Rb _ _ _ _ K b bst D sb _ := bst = .list [K.v, stTv b, .nat 0] ∧ D ⊆ itSBase K ∧ D.Nonempty ∧
    sb = fun Ag => (Ag.items b).script

/-- The weight bound of a branch state of Case 1. -/
def itSC1B (W₀ : ℕ) : ℕ := 2 * (itSVB W₀ + 5 * (2 * W₀ + 3 + 1) ^ 2 + 3) + 7

/-- **The bound of Case 1.** -/
def itSC1X (W₀ : ℕ) : ℕ := 3 * itSC1C (itSC1B W₀ + 2 * W₀ + 3) + itSC1B W₀ + 20

set_option maxHeartbeats 1000000 in
/-- **The Case 1 item meets its contract** `ItSCaseOK` for the case `.one`, with init `itSC1IF`
at `f0`, branch step `itSC1F` at `fb`, and the bound `itSC1X`. -/
theorem itS_c1_caseOK
    (I : Iface) {Pg : Program} {F : Funs} {f0 fb grp orb rb mp sf app : ℕ}
    {IC : ItC1Idx} (hf0 : Pg.funs[f0]? = some itSC1IF)
    (hfb : Pg.funs[fb]? = some (itSC1F grp orb IC.f))
    (hgrp : Pg.funs[grp]? = some (itGrpF rb mp app)) (hrb : Pg.HasAt rb (rangeFuns rb))
    (hmp : Pg.HasAt mp (mapFuns mp sf)) (hsf : Pg.funs[sf]? = some itSndF)
    (happ : Pg.HasAt app (appendFuns app)) (horb : Pg.HasAt orb (orbitFuns orb))
    (hc1 : ItC1Ok Pg IC) :
    ItSCaseOK I Pg F (· = .one) f0 fb itSC1X := by
  refine ⟨itSC1Rel, fun {Ω C k} e c S sv lv L hc K hK hcs => ?_⟩
  obtain ⟨hkq, hκ, hq, hq0, -, hκq⟩ := itS_size I Pg F hc
  have hvw := itS_vW I Pg F hc hK
  have htb : ∀ b : Fin (P₀.κ + 1) → Fin L.q, (stTv b).wt ≤ 5 * (2 * (I.inW .giant S) + 3 + 1) ^ 2 :=
    fun b => wt_stTv_le b (by omega) (by omega)
  have hbst : ∀ b : Fin (P₀.κ + 1) → Fin L.q,
      (Val.list [K.v, stTv b, .nat 0]).wt ≤ itSC1B (I.inW .giant S) := by
    intro b
    have h3 := wt_list3_le K.v (stTv b) (.nat 0)
    have := htb b
    have := wt_nat_le 0
    unfold itSC1B
    omega
  have hB1 : itSC1B (I.inW .giant S) + 10 ≤ itSC1X (I.inW .giant S) := by unfold itSC1X; omega
  have hCB : 3 * itSC1C (itSC1B (I.inW .giant S) + 2 * (I.inW .giant S) + 3) + 20 ≤
      itSC1X (I.inW .giant S) := by unfold itSC1X; omega
  refine ⟨?_, fun w D h => h.2.2, fun w D h => ?_, fun b w D h => ⟨by rw [h.1], h.2.1, h.2.2, rfl⟩,
    fun b bst D sb f h => ?_, fun b bst D sb f h => ?_⟩
  · -- init
    refine FunAll.mono (FunDet.intro hf0 (Det.nat 0)) fun w cost ⟨hw, hcost⟩ =>
      ⟨itSBase K, subset_rfl, ⟨hw, subset_rfl, itSBase_nonempty hK⟩, by omega⟩
  · -- the kept value
    rw [h.1]
    have := wt_nat_le 0
    omega
  · -- a branch state
    rw [h.1]
    have := hbst b
    omega
  · -- the step
    obtain ⟨rfl, hDb, hDn, rfl⟩ := h
    have hgx : gens (1 :: K.fx.map Prod.snd) = (itX0 K.Ag₀ K.J).grp := by
      rw [gens_cons_one]; exact it_gens_itX0 e K.Ag₀ hK.hfx K.J
    have hex : ∀ labX : Fin L.q → ℕ, ItcLab (1 :: K.fx.map Prod.snd) labX →
        ∃ a : Fin L.q, labX a ≠ a := fun labX hl => itc_exists_a hgx hl (by omega) hcs
    have ev : K.v = .list [.list [K.sv, .list [.nat k, .nat L.q], .list (K.ps.map pairV),
        .list (K.fx.map pairV), .list (K.fy.map pairV),
        stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)],
        .list [encKColoring K.d, encKColoring K.d'], .nat (AggCase.code K.case),
        natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))] := rfl
    have hM := hbst b
    rw [ev] at hM ⊢
    obtain ⟨labX, labY, hlX, hlY, a, ha, hp⟩ := it_sc1_prog hfb hgrp hrb hmp hsf happ horb hc1
      K.sv (.list (K.ps.map pairV)) (stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ))
      (.list [encKColoring K.d, encKColoring K.d']) (.nat (AggCase.code K.case))
      (natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))) (stTv b) (.nat 0) K.fx K.fy hex
      (evenStab (q := L.q) (labelOrbitPart (gens (K.fx.map Prod.snd))))
      (M := itSC1B (I.inW .giant S) + 2 * (I.inW .giant S) + 3) (by omega) (by omega)
    have hwo := FunDet.wt_lt hp
    refine FunAll.mono hp fun w cost ⟨hw, hcost⟩ => ⟨by omega, Or.inl ?_⟩
    subst hw
    -- the item of every round of the base set
    have hit : ∀ Ag ∈ itSBase K, ∃ ovs, (Ag.items b).script = .done ⟨[], ovs⟩ ∧
        List.Forall₂ (asOvAt L.toGiantLabels)
          (itcOsM hlX labY ha (evenStab (q := L.q) (labelOrbitPart (gens (K.fx.map Prod.snd))))
            (itcMs labX a)) ovs ∧
        ∀ o ∈ itcOsM hlX labY ha (evenStab (q := L.q) (labelOrbitPart (gens (K.fx.map Prod.snd))))
            (itcMs labX a), gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype := by
      intro Ag hAg
      obtain ⟨hX, hY⟩ := itS_grps hK hAg b
      have hX' : gens (1 :: K.fx.map Prod.snd) = (Ag.strX Ag.src).grp := by
        rw [gens_cons_one, hX]
      have hY' : gens (1 :: K.fy.map Prod.snd) = (Ag.strY b).grp := by
        rw [gens_cons_one, hY]
      obtain ⟨ovs, h1, h2, h3⟩ := it_c1_itemM (P := P₀) (S := S) L.toGiantLabels
        (Ag.strX Ag.src) (Ag.strY b) hX' hY' hlX hlY ha
      rw [hX] at h2 h3
      exact ⟨ovs, by rw [itS_items_one hK hAg hcs b]; exact h1, h2, h3⟩
    obtain ⟨Ag₁, hAg₁⟩ := hDn
    obtain ⟨ovs₁, h1, h2, h3⟩ := hit Ag₁ (hDb hAg₁)
    refine ⟨⟨[], ovs₁⟩, [], _, .nat 0, {Ag | Ag ∈ D ∧ (Ag.items b).script = .done ⟨[], ovs₁⟩},
      rfl, fun Ag h => h.1, fun Ag h => h.2, ⟨rfl, fun Ag h => hDb h.1, ⟨Ag₁, hAg₁, h1⟩⟩,
      ⟨h2, rfl, fun i h _ => absurd h (by simp), h3⟩, ?_⟩
    -- the weight of the output
    have w1 : (Val.list ((itcOsM hlX labY ha (evenStab (q := L.q)
        (labelOrbitPart (gens (K.fx.map Prod.snd)))) (itcMs labX a)).map
          fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)).wt <
        (Val.list [.list [], .list ((itcOsM hlX labY ha (evenStab (q := L.q)
        (labelOrbitPart (gens (K.fx.map Prod.snd)))) (itcMs labX a)).map
          fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2), .nat 0]).wt := wt_le_wt_list (by simp)
    have w2 : (Val.list [.list [], .list ((itcOsM hlX labY ha (evenStab (q := L.q)
        (labelOrbitPart (gens (K.fx.map Prod.snd)))) (itcMs labX a)).map
          fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2), .nat 0]).wt <
        (Val.list [.nat 0, .list [.list [], .list ((itcOsM hlX labY ha (evenStab (q := L.q)
        (labelOrbitPart (gens (K.fx.map Prod.snd)))) (itcMs labX a)).map
          fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2), .nat 0]]).wt := wt_le_wt_list (by simp)
    have w3 := wt_list2_le (.list []) (.list ((itcOsM hlX labY ha (evenStab (q := L.q)
        (labelOrbitPart (gens (K.fx.map Prod.snd)))) (itcMs labX a)).map
          fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2))
    have wn : (Val.list []).wt = 4 := wt_list_nil
    show (Val.list [.list [], _]).wt ≤ _
    omega

end GI.Impl
