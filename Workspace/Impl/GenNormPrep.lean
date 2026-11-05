module

public import Workspace.Impl.GenNormPrepData
public import Workspace.Impl.GenNormPoly

@[expose] public section

/-! # The computed preparation for a normalization step -/
namespace GI.Impl
open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encKSetTuples Preimage PointwiseStab Membership gens)

attribute [local irreducible] normGrow

open Classical in
set_option maxHeartbeats 4000000 in
/-- Preparation computes the normalized group, exact labels, orbit mode and coset list. -/
theorem normPrep_spec (hp : Preimage) (hst : PointwiseStab) (hm : Membership)
    {Pg : Program} (o : normOps Pg hp hst hm) {f : ℕ}
    (hf : Pg.funs[f]? = some (normPrepF o))
    {Ω C : Type} [Finite Ω] {n m k sz : ℕ} (en : Ω ≃ Fin n) (cc : C → ℕ) {S : State Ω C}
    {gv dv xv yv hv rv fv hh rep hv' : Val}
    (hcan : Canon en cc (.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz]) S)
    (Q : PrimitiveQuotient S) (htr : S.Transitive) (hne : S.dom.Nonempty)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)
    (hq : P₀.q₀ < m) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (hrep : normNumbered en Q rep) (hH : HierValC en hv' (Q.pre ++ Q.top :: Q.post)) :
    FunAll Pg f (.list [.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz], rep, hv',
      .nat m, .nat k, encKSetTuples e]) (fun w cost =>
      normPrepared en Q htr e hS hq hkc hkl
        (.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz]) hv' w ∧
      cost ≤ normPrepCost hp hst hm n m (Val.list
        [.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz], rep, hv',
          .nat m, .nat k, encKSetTuples e]).wt) := by
  haveI : Finite Ω := Finite.of_equiv _ en.symm
  obtain ⟨g0, d0, x0, y0, h0, r0, hgv, hdv, hxv, hyv, hhv, hrv, heq⟩ := hcan.val
  simp only [Val.list.injEq, List.cons.injEq] at heq
  obtain ⟨-, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -⟩ := heq
  obtain ⟨gs, rfl, hgs, hgl⟩ := hgv
  change dv = indVal en S.dom at hdv
  subst dv
  let sv := Val.list [.nat n, encGroup gs, indVal en S.dom, xv, yv, hv, rv, fv, hh, .nat sz]
  let a := Val.list [sv, rep, hv', .nat m, .nat k, encKSetTuples e]
  let T : ℕ → ℕ := fun i => (normGrow hp hst hm)^[i] (a.wt + n + m + 100)
  have hTi : Monotone T := normIter_mono hp hst hm _
  have hT0 : T 0 = a.wt + n + m + 100 := rfl
  have hTge (i : ℕ) : 100 ≤ T i := by have := hTi (Nat.zero_le i); omega
  have hn (i : ℕ) : n ≤ T i := by have := hTi (Nat.zero_le i); omega
  have hmT (i : ℕ) : m ≤ T i := by have := hTi (Nat.zero_le i); omega
  have hk (i : ℕ) : k ≤ T i := (Q.k_bounds e).2.le.trans (hmT i)
  have hnext (i : ℕ) : normGrow hp hst hm (T i) = T (i + 1) := by
    simp only [T, Function.iterate_succ_apply']
  have hen0 : normEnvBound (T 0) [a] := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    omega
  have hgen : gens (1 :: gs) = groupFin en S.G := by
    change genGroup (1 :: gs) = _
    rw [genGroup_one_cons, hgs]
  have hmem : ∀ g ∈ 1 :: gs, (toFin en).symm g ∈ S.G := by
    intro g hg
    exact normGroupFin_mem en S.G g |>.mp (hgen ▸ Subgroup.subset_closure hg)
  -- The exposed class numbers and ordered representatives.
  have ha1 : Det Pg [a] (mk2 (normInput 1) (normState 2))
      (.list [rep, indVal en S.dom]) (normArgBudget (T 0)) := by
    exact normArg_pack [(normInput 1, rep), (normState 2, indVal en S.dom)] (by norm_num) (by
      intro p hp'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
      rcases hp' with rfl | rfl
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen0 (slot := 0) rfl [1] rfl (by norm_num) (by norm_num) (hTge 0))
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen0 (slot := 0) rfl [0, 2] rfl (by norm_num) (by norm_num) (hTge 0)))
  have hc1 := normStage_call hp hst hm (R := fun w => ∃ (num : Fin n → ℕ)
      (reps : List ℕ) (rep' : Val), w = .list [encFun num, natList reps, rep'] ∧
        normBlockData en Q num reps ∧ ∀ i, num i = Q.labFin en i) ha1
    (FunAll.mono (normNumbering_spec o.hcls en Q hrep) (fun w c hw => by
      obtain ⟨num, reps, rep', hw, hd, hnq, hc⟩ := hw
      exact ⟨⟨num, reps, rep', hw, hd, hnq⟩, hc.trans (normBudget_cls hp hst hm (hn 0))⟩))
  refine FunAll.intro hf (EvalAll.letE hc1 fun w1 c1 hw1 => ?_)
  obtain ⟨⟨num, reps, rep', rfl, hd, hnq⟩, w1b, c1b⟩ := hw1
  rw [hnext] at w1b c1b
  change _ ≤ T 1 at w1b
  change _ ≤ 2 * T 1 at c1b
  have hen1 := normEnvBound_snoc hen0 (hTi (by omega : 0 ≤ 1)) w1b
  -- Recover the identities on blocks and on Cameron points.
  have ha2 : Det Pg [a, .list [encFun num, natList reps, rep']]
      (.length (normField 1 1)) (.nat Q.d) (normArgBudget (T 1)) := by
    have h := normArg_piece (normPiece_length (Pg := Pg) (normAtom_read (Pg := Pg) hen1 (slot := 1) rfl [1] rfl
      (by norm_num) (by norm_num) (hTge 1)))
    rw [natList, List.length_map, hd.2.2.1] at h
    exact h
  have hc2 := normStage_call hp hst hm ha2
    (FunAll.mono (GI.Lang.range_det o.hrange Q.d) (fun w c hw =>
      ⟨hw.1, hw.2.trans (normBudget_range hp hst hm ((Q.d_le_card en).trans (hn 1)))⟩))
  refine EvalAll.letE hc2 fun w2 c2 hw2 => ?_
  obtain ⟨rfl, w2b, c2b⟩ := hw2
  rw [hnext] at w2b c2b
  change _ ≤ T 2 at w2b
  change _ ≤ 2 * T 2 at c2b
  have hen2 := normEnvBound_snoc hen1 (hTi (by omega : 1 ≤ 2)) w2b
  have ha3 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d))]
      (normInput 3) (.nat m) (normArgBudget (T 2)) :=
    normArg_piece (normAtom_piece (normAtom_read (Pg := Pg) hen2 (slot := 0) rfl [3] rfl
      (by norm_num) (by norm_num) (hTge 2)))
  have hc3 := normStage_call hp hst hm ha3
    (FunAll.mono (GI.Lang.range_det o.hrange m) (fun w c hw =>
      ⟨hw.1, hw.2.trans (normBudget_range hp hst hm (hmT 2))⟩))
  refine EvalAll.letE hc3 fun w3 c3 hw3 => ?_
  obtain ⟨rfl, w3b, c3b⟩ := hw3
  rw [hnext] at w3b c3b
  change _ ≤ T 3 at w3b
  change _ ≤ 2 * T 3 at c3b
  have hen3 := normEnvBound_snoc hen2 (hTi (by omega : 2 ≤ 3)) w3b
  let ctx := Val.list [encFun num, natList reps, encKSetTuples e,
    encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))]
  let ps := (1 :: gs).map (normPairOf en Q e hS)
  have hps : normParentGens en Q e hS ps := normParentGens_map en Q e hS (1 :: gs) hgen
  have ha4 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))]
      (mk2 normPairContext normParentGenerators) (.list [ctx, .list ((1 :: gs).map encPerm)]) (normArgBudget (T 3)) := by
    exact normArg_pack [(normPairContext, ctx), (normParentGenerators, .list ((1 :: gs).map encPerm))] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact normPiece_pack [(normField 1 0, encFun num), (normField 1 1, natList reps), (normInput 5, encKSetTuples e), (.var 2, encPerm (1 : Perm (Fin Q.d))), (.var 3, encPerm (1 : Perm (Fin m)))] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact normAtom_read (Pg := Pg) hen3 (slot := 1) rfl [0] rfl (by norm_num) (by norm_num) (hTge 3)
      · exact normAtom_read (Pg := Pg) hen3 (slot := 1) rfl [1] rfl (by norm_num) (by norm_num) (hTge 3)
      · exact normAtom_read (Pg := Pg) hen3 (slot := 0) rfl [5] rfl (by norm_num) (by norm_num) (hTge 3)
      · exact normAtom_read (Pg := Pg) hen3 (slot := 2) rfl [] rfl (by norm_num) (by norm_num) (hTge 3)
      · exact normAtom_read (Pg := Pg) hen3 (slot := 3) rfl [] rfl (by norm_num) (by norm_num) (hTge 3)
)
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen3 (slot := 0) rfl [0, 1, 1] rfl (by norm_num) (by norm_num) (hTge 3))
)
  have hL4 : (1 :: gs).length ≤ T 3 := by
    have hw := (normAtom_read (Pg := Pg) hen3 (slot := 0) rfl [0, 1, 1]
      (show normReadVal a [0, 1, 1] = some (.list ((1 :: gs).map encPerm)) from rfl)
      (by norm_num) (by norm_num) (hTge 3)).1
    have hl := length_lt_wt_list ((1 :: gs).map encPerm)
    simp only [List.length_map] at hl
    omega
  have hctx4 : ctx.wt ≤ normArgBudget (T 3) :=
    (wt_le_wt_list (vs := [ctx, .list ((1 :: gs).map encPerm)]) (by simp)).le.trans (normDet_wt ha4)
  have hc4 := normStage_call hp hst hm ha4
    (FunAll.mono (o.pairs.spec en Q e hS num reps hd (1 :: gs) hmem) (fun w c hw =>
      ⟨hw.1, hw.2.trans (normBudget_parent hp hst hm (hn 3) (hmT 3) hL4 hctx4)⟩))
  refine EvalAll.letE hc4 fun w4 c4 hw4 => ?_
  obtain ⟨rfl, w4b, c4b⟩ := hw4
  rw [hnext] at w4b c4b
  change _ ≤ T 4 at w4b
  change _ ≤ 2 * T 4 at c4b
  have hen4 := normEnvBound_snoc hen3 (hTi (by omega : 3 ≤ 4)) w4b
  have ha5 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m)), .list (ps.map pairV)] (normInput 3) (.nat m) (normArgBudget (T 4)) :=
    normArg_piece (normAtom_piece (normAtom_read (Pg := Pg) hen4 (slot := 0) rfl [3] rfl (by norm_num) (by norm_num) (hTge 4)))
  have hc5 := normStage_call hp hst hm ha5
    (FunAll.mono (normAlt_spec o.halt o.hreplicate o.hcycles) (fun w c hw =>
      ⟨hw.1, hw.2.trans (normBudget_alt hp hst hm (hmT 4))⟩))
  refine EvalAll.letE hc5 fun w5 c5 hw5 => ?_
  obtain ⟨rfl, w5b, c5b⟩ := hw5
  rw [hnext] at w5b c5b
  change _ ≤ T 5 at w5b
  change _ ≤ 2 * T 5 at c5b
  have hen5 := normEnvBound_snoc hen4 (hTi (by omega : 4 ≤ 5)) w5b
  have ha6 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m)), .list (ps.map pairV), .list ((normAltGens m).map encPerm)]
      (Expr.mkList [mk2 (normState 0) (normInput 3), .var 4, .var 5]) (.list [.list [.nat n, .nat m], .list (ps.map pairV), .list ((normAltGens m).map encPerm)]) (normArgBudget (T 5)) := by
    exact normArg_pack [(mk2 (normState 0) (normInput 3), .list [.nat n, .nat m]), (.var 4, .list (ps.map pairV)), (.var 5, .list ((normAltGens m).map encPerm))] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact normPiece_pack [(normState 0, .nat n), (normInput 3, .nat m)] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact normAtom_read (Pg := Pg) hen5 (slot := 0) rfl [0, 0] rfl (by norm_num) (by norm_num) (hTge 5)
      · exact normAtom_read (Pg := Pg) hen5 (slot := 0) rfl [3] rfl (by norm_num) (by norm_num) (hTge 5)
)
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen5 (slot := 4) rfl [] rfl (by norm_num) (by norm_num) (hTge 5))
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen5 (slot := 5) rfl [] rfl (by norm_num) (by norm_num) (hTge 5))
)
  have hL6 : ps.length ≤ T 5 := by
    have hw := normEnvBound_get hen5 (slot := 4)
      (show [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)),
        encPerm (1 : Perm (Fin m)), .list (ps.map pairV),
        .list ((normAltGens m).map encPerm)][4]? = some (.list (ps.map pairV)) from rfl)
    have hl := length_lt_wt_list (ps.map pairV)
    simp only [List.length_map] at hl
    omega
  have hc6 := normStage_call hp hst hm (R := fun w =>
      ∃ qs : List (Perm (Fin n) × Perm (Fin m)), w = .list (qs.map pairV) ∧
        qs.length ≤ (n + m) ^ 2 ∧ Subgroup.closure {p | p ∈ qs} = normGraph en Q e hS) ha6
    (FunAll.mono (normGraphPre_spec en Q e hS hp o.hpre o.hjpre ps hps) (fun w c hw => by
      obtain ⟨qs, hw, hl, hg, hc⟩ := hw
      exact ⟨⟨qs, hw, hl, hg⟩, hc.trans ((normGraphCost_bound hp en Q e hS ps hps).trans
        (normBudget_graph hp hst hm (hn 5) (hmT 5) hL6))⟩))
  refine EvalAll.letE hc6 fun w6 c6 hw6 => ?_
  obtain ⟨⟨qs, rfl, hql, hqgen⟩, w6b, c6b⟩ := hw6
  rw [hnext] at w6b c6b
  change _ ≤ T 6 at w6b
  change _ ≤ 2 * T 6 at c6b
  have hen6 := normEnvBound_snoc hen5 (hTi (by omega : 5 ≤ 6)) w6b
  have ha7 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m)), .list (ps.map pairV), .list ((normAltGens m).map encPerm), .list (qs.map pairV)]
      (mk2 (normState 0) (.var 6)) (.list [.nat n, .list (qs.map pairV)]) (normArgBudget (T 6)) := by
    exact normArg_pack [(normState 0, .nat n), (.var 6, .list (qs.map pairV))] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen6 (slot := 0) rfl [0, 0] rfl (by norm_num) (by norm_num) (hTge 6))
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen6 (slot := 6) rfl [] rfl (by norm_num) (by norm_num) (hTge 6))
)
  have hL7 : qs.length ≤ T 6 := by
    have hw := w6b
    have hl := length_lt_wt_list (qs.map pairV)
    simp only [List.length_map] at hl
    omega
  have hc7 := normStage_call hp hst hm (R := fun w => ∃ (Kv : Val) (rs : List (Perm (Fin n))),
      w = .list [Kv, .list (rs.map encPerm)] ∧ GroupValC n Kv (groupFin en (Q.normGroup e hS)) ∧
        gens rs = groupFin en (Q.normGroup e hS) ∧ rs.length ≤ n ^ 2) ha7
    (FunAll.mono (normRawReduce_spec hst o.hraw o.hkr o.hjst en Q e hS qs hqgen)
      (fun w c hw => by
        obtain ⟨Kv, rs, hw, hKv, hrgen, hrl, hc⟩ := hw
        exact ⟨⟨Kv, rs, hw, hKv, hrgen, hrl⟩, hc.trans
          (normBudget_raw hp hst hm (hn 6) (hmT 6) hL7 (normDet_wt ha7))⟩))
  refine EvalAll.letE hc7 fun w7 c7 hw7 => ?_
  obtain ⟨⟨Kv, rs, rfl, hKv, hrgen, hrl⟩, w7b, c7b⟩ := hw7
  rw [hnext] at w7b c7b
  change _ ≤ T 7 at w7b
  change _ ≤ 2 * T 7 at c7b
  have hen7 := normEnvBound_snoc hen6 (hTi (by omega : 6 ≤ 7)) w7b
  let rps := rs.map (normPairOf en Q e hS)
  have hrmem : ∀ g ∈ rs, (toFin en).symm g ∈ S.G := by
    intro g hg
    exact Q.normGroup_le e hS ((normGroupFin_mem en (Q.normGroup e hS) g).mp
      (hrgen ▸ Subgroup.subset_closure hg))
  have ha8 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m)), .list (ps.map pairV), .list ((normAltGens m).map encPerm), .list (qs.map pairV), .list [Kv, .list (rs.map encPerm)]]
      (mk2 normPairContext (normField 7 1)) (.list [ctx, .list (rs.map encPerm)]) (normArgBudget (T 7)) := by
    exact normArg_pack [(normPairContext, ctx), (normField 7 1, .list (rs.map encPerm))] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact normPiece_pack [(normField 1 0, encFun num), (normField 1 1, natList reps), (normInput 5, encKSetTuples e), (.var 2, encPerm (1 : Perm (Fin Q.d))), (.var 3, encPerm (1 : Perm (Fin m)))] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact normAtom_read (Pg := Pg) hen7 (slot := 1) rfl [0] rfl (by norm_num) (by norm_num) (hTge 7)
      · exact normAtom_read (Pg := Pg) hen7 (slot := 1) rfl [1] rfl (by norm_num) (by norm_num) (hTge 7)
      · exact normAtom_read (Pg := Pg) hen7 (slot := 0) rfl [5] rfl (by norm_num) (by norm_num) (hTge 7)
      · exact normAtom_read (Pg := Pg) hen7 (slot := 2) rfl [] rfl (by norm_num) (by norm_num) (hTge 7)
      · exact normAtom_read (Pg := Pg) hen7 (slot := 3) rfl [] rfl (by norm_num) (by norm_num) (hTge 7)
)
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen7 (slot := 7) rfl [1] rfl (by norm_num) (by norm_num) (hTge 7))
)
  have hL8 : rs.length ≤ T 7 := by
    have hw := (normAtom_read (Pg := Pg) hen7 (slot := 7) rfl [1]
      (show normReadVal (.list [Kv, .list (rs.map encPerm)]) [1] =
        some (.list (rs.map encPerm)) from rfl) (by norm_num) (by norm_num) (hTge 7)).1
    have hl := length_lt_wt_list (rs.map encPerm)
    simp only [List.length_map] at hl
    omega
  have hctx8 : ctx.wt ≤ normArgBudget (T 7) :=
    (wt_le_wt_list (vs := [ctx, .list (rs.map encPerm)]) (by simp)).le.trans (normDet_wt ha8)
  have hc8 := normStage_call hp hst hm ha8
    (FunAll.mono (o.pairs.spec en Q e hS num reps hd rs hrmem) (fun w c hw =>
      ⟨hw.1, hw.2.trans (normBudget_parent hp hst hm (hn 7) (hmT 7) hL8 hctx8)⟩))
  refine EvalAll.letE hc8 fun w8 c8 hw8 => ?_
  obtain ⟨rfl, w8b, c8b⟩ := hw8
  rw [hnext] at w8b c8b
  change _ ≤ T 8 at w8b
  change _ ≤ 2 * T 8 at c8b
  have hen8 := normEnvBound_snoc hen7 (hTi (by omega : 7 ≤ 8)) w8b
  have ha9 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m)), .list (ps.map pairV), .list ((normAltGens m).map encPerm), .list (qs.map pairV), .list [Kv, .list (rs.map encPerm)], .list (rps.map pairV)]
      (mk2 (mk2 (normField 7 0) normPositionIds) normParentGenerators) (.list [.list [Kv, encPerm (1 : Perm (Fin n))], .list ((1 :: gs).map encPerm)]) (normArgBudget (T 8)) := by
    exact normArg_pack [(mk2 (normField 7 0) normPositionIds, .list [Kv, encPerm (1 : Perm (Fin n))]), (normParentGenerators, .list ((1 :: gs).map encPerm))] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact normPiece_pack [(normField 7 0, Kv), (normPositionIds, encPerm (1 : Perm (Fin n)))] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact normAtom_read (Pg := Pg) hen8 (slot := 7) rfl [0] rfl (by norm_num) (by norm_num) (hTge 8)
      · exact normAtom_read (Pg := Pg) hen8 (slot := 0) rfl [0, 1, 1, 0] rfl (by norm_num) (by norm_num) (hTge 8)
)
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen8 (slot := 0) rfl [0, 1, 1] rfl (by norm_num) (by norm_num) (hTge 8))
)
  have hc9 := normStage_call hp hst hm ha9
    (FunAll.mono (normCosets_spec hm o.hcosets o.houtsideFilter o.houtside o.hjm
      en Q e hS (1 :: gs) hgen hKv) (fun w c hw =>
      ⟨hw.1, hw.2.trans (normBudget_cosets hp hst hm (hn 8)
        (hL4.trans (hTi (by omega : 3 ≤ 8)))
        ((wt_le_wt_list (vs := [.list [Kv, encPerm (1 : Perm (Fin n))],
          .list ((1 :: gs).map encPerm)]) (by simp)).le.trans (normDet_wt ha9)))⟩))
  refine EvalAll.letE hc9 fun w9 c9 hw9 => ?_
  obtain ⟨⟨D, ts, rfl, htsl, htst⟩, w9b, c9b⟩ := hw9
  rw [hnext] at w9b c9b
  change _ ≤ T 9 at w9b
  change _ ≤ 2 * T 9 at c9b
  have hen9 := normEnvBound_snoc hen8 (hTi (by omega : 8 ≤ 9)) w9b
  have ha10 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m)), .list (ps.map pairV), .list ((normAltGens m).map encPerm), .list (qs.map pairV), .list [Kv, .list (rs.map encPerm)], .list (rps.map pairV), .list (ts.map encPerm)]
      (mk2 (normState 2) (normInput 2)) (.list [indVal en S.dom, hv']) (normArgBudget (T 9)) := by
    exact normArg_pack [(normState 2, indVal en S.dom), (normInput 2, hv')] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen9 (slot := 0) rfl [0, 2] rfl (by norm_num) (by norm_num) (hTge 9))
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen9 (slot := 0) rfl [2] rfl (by norm_num) (by norm_num) (hTge 9))
)
  have hc10 := normStage_call hp hst hm ha10
    (FunAll.mono (normSelection_spec o.hselection o.hcls en Q hne hH) (fun w c hw =>
      ⟨hw.1, hw.2.trans (normBudget_selection hp hst hm (normDet_wt ha10))⟩))
  refine EvalAll.letE hc10 fun w10 c10 hw10 => ?_
  obtain ⟨rfl, w10b, c10b⟩ := hw10
  rw [hnext] at w10b c10b
  change _ ≤ T 10 at w10b
  change _ ≤ 2 * T 10 at c10b
  have hen10 := normEnvBound_snoc hen9 (hTi (by omega : 9 ≤ 10)) w10b
  have ha11 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m)), .list (ps.map pairV), .list ((normAltGens m).map encPerm), .list (qs.map pairV), .list [Kv, .list (rs.map encPerm)], .list (rps.map pairV), .list (ts.map encPerm), .nat Q.pre.length]
      (mk2 (.nat 0) (normField 1 0)) (.list [.nat 0, encFun num]) (normArgBudget (T 10)) := by
    exact normArg_pack [(.nat 0, .nat 0), (normField 1 0, encFun num)] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact normAtom_piece (normAtom_nat (by have := hTge 10; omega))
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen10 (slot := 1) rfl [0] rfl (by norm_num) (by norm_num) (hTge 10))
)
  have hc11 := normStage_call hp hst hm ha11
    (FunAll.mono (normFiber_spec o.hcount en Q num hnq) (fun w c hw =>
      ⟨hw.1, hw.2.trans (normBudget_count hp hst hm (hn 10))⟩))
  refine EvalAll.letE hc11 fun w11 c11 hw11 => ?_
  obtain ⟨rfl, w11b, c11b⟩ := hw11
  rw [hnext] at w11b c11b
  change _ ≤ T 11 at w11b
  change _ ≤ 2 * T 11 at c11b
  have hen11 := normEnvBound_snoc hen10 (hTi (by omega : 10 ≤ 11)) w11b
  have ha12 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m)), .list (ps.map pairV), .list ((normAltGens m).map encPerm), .list (qs.map pairV), .list [Kv, .list (rs.map encPerm)], .list (rps.map pairV), .list (ts.map encPerm), .nat Q.pre.length, .nat (Nat.card {v : S.dom // Q.blk v.1 = ⟨0, by have := Q.two_le; omega⟩})]
      (mk2 (Expr.mkList [normInput 5, normField 1 0, normState 2, .var 3, normFlip]) normPositionIds) (.list [.list [encKSetTuples e, encFun num, indVal en S.dom, encPerm (1 : Perm (Fin m)), boolVal (decide (m < 2 * k))], encPerm (1 : Perm (Fin n))]) (normArgBudget (T 11)) := by
    exact normArg_pack [(Expr.mkList [normInput 5, normField 1 0, normState 2, .var 3, normFlip], .list [encKSetTuples e, encFun num, indVal en S.dom, encPerm (1 : Perm (Fin m)), boolVal (decide (m < 2 * k))]), (normPositionIds, encPerm (1 : Perm (Fin n)))] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact normPiece_pack [(normInput 5, encKSetTuples e), (normField 1 0, encFun num), (normState 2, indVal en S.dom), (.var 3, encPerm (1 : Perm (Fin m))), (normFlip, boolVal (decide (m < 2 * k)))] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact normAtom_read (Pg := Pg) hen11 (slot := 0) rfl [5] rfl (by norm_num) (by norm_num) (hTge 11)
      · exact normAtom_read (Pg := Pg) hen11 (slot := 1) rfl [0] rfl (by norm_num) (by norm_num) (hTge 11)
      · exact normAtom_read (Pg := Pg) hen11 (slot := 0) rfl [0, 2] rfl (by norm_num) (by norm_num) (hTge 11)
      · exact normAtom_read (Pg := Pg) hen11 (slot := 3) rfl [] rfl (by norm_num) (by norm_num) (hTge 11)
      · exact normAtom_flip
          (normRead_one hen11 (slot := 0) rfl (j := 3) rfl (by norm_num) (hTge 11))
          (normRead_one hen11 (slot := 0) rfl (j := 4) rfl (by norm_num) (hTge 11)) (hk 11) (hTge 11)
)
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen11 (slot := 0) rfl [0, 1, 1, 0] rfl (by norm_num) (by norm_num) (hTge 11))
)
  have hc12 := normStage_call hp hst hm ha12
    (FunAll.mono (normBlockMap_spec o.hblockmap o.hcell o.hbits o.hbit o.hmem en Q D.choice num hnq)
      (fun w c hw => ⟨hw.1, hw.2.trans (normBudget_blocks hp hst hm (hn 11) (hmT 11)
        ((wt_le_wt_list (vs := [.list [encKSetTuples e, encFun num, indVal en S.dom,
          encPerm (1 : Perm (Fin m)), boolVal (decide (m < 2 * k))],
            encPerm (1 : Perm (Fin n))]) (by exact List.mem_cons_self)).le.trans (normDet_wt ha12)))⟩))
  refine EvalAll.letE hc12 fun w12 c12 hw12 => ?_
  obtain ⟨rfl, w12b, c12b⟩ := hw12
  rw [hnext] at w12b c12b
  change _ ≤ T 12 at w12b
  change _ ≤ 2 * T 12 at c12b
  have hen12 := normEnvBound_snoc hen11 (hTi (by omega : 11 ≤ 12)) w12b
  have ha13 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m)), .list (ps.map pairV), .list ((normAltGens m).map encPerm), .list (qs.map pairV), .list [Kv, .list (rs.map encPerm)], .list (rps.map pairV), .list (ts.map encPerm), .nat Q.pre.length, .nat (Nat.card {v : S.dom // Q.blk v.1 = ⟨0, by have := Q.two_le; omega⟩}), normBlockMapVal en Q D.choice]
      (Expr.mkList [normInput 3, normInput 4, .var 8, .var 10, .var 11, .var 12]) (.list [.nat m, .nat k, .list (rps.map pairV), .nat Q.pre.length, .nat (Nat.card {v : S.dom // Q.blk v.1 = ⟨0, by have := Q.two_le; omega⟩}), normBlockMapVal en Q D.choice]) (normArgBudget (T 12)) := by
    exact normArg_pack [(normInput 3, .nat m), (normInput 4, .nat k), (.var 8, .list (rps.map pairV)), (.var 10, .nat Q.pre.length), (.var 11, .nat (Nat.card {v : S.dom // Q.blk v.1 = ⟨0, by have := Q.two_le; omega⟩})), (.var 12, normBlockMapVal en Q D.choice)] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen12 (slot := 0) rfl [3] rfl (by norm_num) (by norm_num) (hTge 12))
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen12 (slot := 0) rfl [4] rfl (by norm_num) (by norm_num) (hTge 12))
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen12 (slot := 8) rfl [] rfl (by norm_num) (by norm_num) (hTge 12))
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen12 (slot := 10) rfl [] rfl (by norm_num) (by norm_num) (hTge 12))
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen12 (slot := 11) rfl [] rfl (by norm_num) (by norm_num) (hTge 12))
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen12 (slot := 12) rfl [] rfl (by norm_num) (by norm_num) (hTge 12))
)
  have hc13 := normStage_call hp hst hm ha13
    (FunAll.mono (normLabelBuild_exact o.hlabels en Q D.choice rps) (fun w c hw =>
      ⟨hw.1, hw.2.trans (normBudget_labels hp hst hm (hmT 12) (hk 12) (normDet_wt ha13))⟩))
  refine EvalAll.letE hc13 fun w13 c13 hw13 => ?_
  obtain ⟨rfl, w13b, c13b⟩ := hw13
  rw [hnext] at w13b c13b
  change _ ≤ T 13 at w13b
  change _ ≤ 2 * T 13 at c13b
  have hen13 := normEnvBound_snoc hen12 (hTi (by omega : 12 ≤ 13)) w13b
  have ha14 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m)), .list (ps.map pairV), .list ((normAltGens m).map encPerm), .list (qs.map pairV), .list [Kv, .list (rs.map encPerm)], .list (rps.map pairV), .list (ts.map encPerm), .nat Q.pre.length, .nat (Nat.card {v : S.dom // Q.blk v.1 = ⟨0, by have := Q.two_le; omega⟩}), normBlockMapVal en Q D.choice, normLabelVal en Q D.choice rps]
      (mk2 (normField 7 0) (normState 2)) (.list [Kv, indVal en S.dom]) (normArgBudget (T 13)) := by
    exact normArg_pack [(normField 7 0, Kv), (normState 2, indVal en S.dom)] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen13 (slot := 7) rfl [0] rfl (by norm_num) (by norm_num) (hTge 13))
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen13 (slot := 0) rfl [0, 2] rfl (by norm_num) (by norm_num) (hTge 13))
)
  let childBase := S.restrict (Q.normGroup e hS) (Q.normGroup_le e hS) S.x S.y
    (Q.pre ++ Q.top :: Q.post)
  have hc14 := normStage_call hp hst hm ha14
    (FunAll.mono (normOrbit_spec o.horbit o.hlo o.hmax en childBase hne hKv) (fun w c hw =>
      ⟨hw.1, hw.2.trans (normBudget_orbit hp hst hm (hn 13) (normDet_wt ha14))⟩))
  refine EvalAll.letE hc14 fun w14 c14 hw14 => ?_
  obtain ⟨rfl, w14b, c14b⟩ := hw14
  rw [hnext] at w14b c14b
  change _ ≤ T 14 at w14b
  change _ ≤ 2 * T 14 at c14b
  have hen14 := normEnvBound_snoc hen13 (hTi (by omega : 13 ≤ 14)) w14b
  have ha15 : Det Pg [a, .list [encFun num, natList reps, rep'], encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m)), .list (ps.map pairV), .list ((normAltGens m).map encPerm), .list (qs.map pairV), .list [Kv, .list (rs.map encPerm)], .list (rps.map pairV), .list (ts.map encPerm), .nat Q.pre.length, .nat (Nat.card {v : S.dom // Q.blk v.1 = ⟨0, by have := Q.two_le; omega⟩}), normBlockMapVal en Q D.choice, normLabelVal en Q D.choice rps, boolVal (decide childBase.Transitive)]
      (Expr.mkList [Expr.mkList [normInput 0, normField 7 0, normInput 2, .var 13, .var 14], .var 9]) (.list [.list [sv, Kv, hv', normLabelVal en Q D.choice rps, boolVal (decide childBase.Transitive)], .list (ts.map encPerm)]) (normArgBudget (T 14)) := by
    exact normArg_pack [(Expr.mkList [normInput 0, normField 7 0, normInput 2, .var 13, .var 14], .list [sv, Kv, hv', normLabelVal en Q D.choice rps, boolVal (decide childBase.Transitive)]), (.var 9, .list (ts.map encPerm))] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact normPiece_pack [(normInput 0, sv), (normField 7 0, Kv), (normInput 2, hv'), (.var 13, normLabelVal en Q D.choice rps), (.var 14, boolVal (decide childBase.Transitive))] (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact normAtom_read (Pg := Pg) hen14 (slot := 0) rfl [0] rfl (by norm_num) (by norm_num) (hTge 14)
      · exact normAtom_read (Pg := Pg) hen14 (slot := 7) rfl [0] rfl (by norm_num) (by norm_num) (hTge 14)
      · exact normAtom_read (Pg := Pg) hen14 (slot := 0) rfl [2] rfl (by norm_num) (by norm_num) (hTge 14)
      · exact normAtom_read (Pg := Pg) hen14 (slot := 13) rfl [] rfl (by norm_num) (by norm_num) (hTge 14)
      · exact normAtom_read (Pg := Pg) hen14 (slot := 14) rfl [] rfl (by norm_num) (by norm_num) (hTge 14)
)
      · exact normAtom_piece (normAtom_read (Pg := Pg) hen14 (slot := 9) rfl [] rfl (by norm_num) (by norm_num) (hTge 14))
)
  have hprepared : normPrepared en Q htr e hS hq hkc hkl sv hv'
      (.list [.list [sv, Kv, hv', normLabelVal en Q D.choice rps,
        boolVal (decide childBase.Transitive)], .list (ts.map encPerm)]) := by
    refine ⟨D, Kv, normLabelVal en Q D.choice rps, decide childBase.Transitive, ts,
      rfl, hKv, ?_, htsl, htst, ?_⟩
    · exact normReducedLabels en Q D.choice htr hq hkc hkl rs hrl hrgen
    · apply normMode_spec
      change decide childBase.Transitive = true ↔ childBase.Transitive
      exact decide_eq_true_iff
  have hwout := normDet_wt ha15
  have harg14 : normArgBudget (T 14) ≤ T 15 := by
    rw [← hnext 14]
    exact normGrow_args hp hst hm _
  refine ha15.post fun cost hc => ⟨hprepared, ?_⟩
  change c1 + (c2 + (c3 + (c4 + (c5 + (c6 + (c7 + (c8 + (c9 + (c10 +
    (c11 + (c12 + (c13 + (c14 + cost + _ + 1) + _ + 1) + _ + 1) + _ + 1) + _ + 1) +
    _ + 1) + _ + 1) + _ + 1) + _ + 1) + _ + 1) + _ + 1) + _ + 1) + _ + 1) + _ + 1 ≤
      normPrepCost hp hst hm n m a.wt
  have hfinal : 100 ≤ T 15 := hTge 15
  have hc1f : c1 ≤ 2 * T 15 := c1b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 1 ≤ 15)))
  have hc2f : c2 ≤ 2 * T 15 := c2b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 2 ≤ 15)))
  have hc3f : c3 ≤ 2 * T 15 := c3b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 3 ≤ 15)))
  have hc4f : c4 ≤ 2 * T 15 := c4b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 4 ≤ 15)))
  have hc5f : c5 ≤ 2 * T 15 := c5b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 5 ≤ 15)))
  have hc6f : c6 ≤ 2 * T 15 := c6b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 6 ≤ 15)))
  have hc7f : c7 ≤ 2 * T 15 := c7b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 7 ≤ 15)))
  have hc8f : c8 ≤ 2 * T 15 := c8b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 8 ≤ 15)))
  have hc9f : c9 ≤ 2 * T 15 := c9b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 9 ≤ 15)))
  have hc10f : c10 ≤ 2 * T 15 := c10b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 10 ≤ 15)))
  have hc11f : c11 ≤ 2 * T 15 := c11b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 11 ≤ 15)))
  have hc12f : c12 ≤ 2 * T 15 := c12b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 12 ≤ 15)))
  have hc13f : c13 ≤ 2 * T 15 := c13b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 13 ≤ 15)))
  have hc14f : c14 ≤ 2 * T 15 := c14b.trans (Nat.mul_le_mul_left 2 (hTi (by omega : 14 ≤ 15)))
  change _ ≤ 100 * T 15
  omega

end GI.Impl
