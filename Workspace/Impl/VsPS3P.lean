import Workspace.Impl.VsPS4P
import Workspace.Lang.Prims.BlockHom

/-!
# The pairing stage

On `[ctx, input, ⟨ns₂⟩, [x₂, r]]` with `N̄₂` not abelian: a non-commuting pair `a, b` of
`1 :: ns₂`, `c0 = ⁅a, b⁆`, the powers `Zp` of `ζ = ρ c0`, the radical stage; if a relation word
`z` is outside `L`, grow with `z`, else go on with the last stage (`vsPS3_spec`).
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)
open scoped commutatorElement

variable {I : VecStabInst}

/-- On `[ctx, input, ⟨ns₂⟩, [x₂, r]]`: the pairing stage. -/
def vsPS3E (pair comm zp tl rad grow s4 : ℕ) : Expr :=
  .letE (.call pair (mk2 (arg 0) (arg 2)))
  (.letE (.get (arg 2) (.nat 1))
  (.letE (.call comm (mk2 (.get (.var 2) (.get (.var 1) (.nat 0))) (.get (.var 2) (.get (.var 1) (.nat 1)))))
  (.letE (.call zp (mk3 (arg 0) (.var 3) (.get (arg 3) (.nat 1))))
  (.letE (.call tl (.var 2))
  (.letE (mk3 (arg 0) (.var 5) (.var 4))
  (.letE (mk4 (arg 0) (.var 5) (.get (.var 2) (.nat 0)) (.length (.var 5)))
  (.letE (.call rad (mk3 (.var 6) (.var 7) (.get (arg 3) (.nat 1))))
  (.ite (.get (.var 8) (.nat 0))
      (mk2 (.nat 0) (.call grow (mk3 (arg 0) (.get (arg 1) (.nat 1)) (mk1 (.get (.var 8) (.nat 1))))))
      (.call s4 (mk4 (arg 0) (arg 1) (.var 6) (arg 3)))))))))))

/-- The function indices of the pairing stage. -/
structure VsPS3X where
  (x4 : VsPS4X) (s4 pair comm zp zmp zit tl rad gmp ker rfnd rp word : ℕ)

/-- The layout of the pairing stage. -/
structure VsPS3Lay (P : Program) (hn : NormalClosure) (x : VsPS3X) : Prop where
  L4 : VsPS4Lay P hn x.x4
  hs4 : P.funs[x.s4]? = some (vsPS4E x.x4.desc x.x4.fin x.x4.grow)
  hpair : P.funs[x.pair]? = some (vsPPairE x.x4.fo x.x4.fi)
  hcomm : P.funs[x.comm]? = some (vsPCommE x.x4.d.o.comp x.x4.d.o.inv)
  hzp : P.funs[x.zp]? = some (vsPZpE x.zmp x.x4.e.rng)
  hzmp : P.HasAt x.zmp (mapFuns x.zmp x.zit)
  hzit : P.funs[x.zit]? = some (vsPZItemE x.x4.e.pow x.x4.d.o.loc)
  htl : P.HasAt x.tl (tailFuns x.tl)
  hrad : P.funs[x.rad]? = some (vsPRadE x.gmp x.ker x.rfnd x.word)
  hgmp : P.HasAt x.gmp (mapFuns x.gmp x.x4.d.o.key)
  hker : P.HasAt x.ker (vsWKerFuns x.ker)
  hrfnd : P.HasAt x.rfnd (findFuns x.rfnd x.rp)
  hrp : P.funs[x.rp]? = some (vsPRadPredE x.word x.x4.d.nt)
  hword : P.HasAt x.word (vsPWordFuns x.word x.x4.d.o.comp x.x4.e.pow)

/-- The cost of the pairing stage. -/
noncomputable def vsPS3Cost (Cφ : ℕ) (hn : NormalClosure) (S : ℕ) : ℕ :=
  vsPPairCost Cφ (vsPN S) (vsPW6 S) + vsPCommCost (vsPN S) + vsPZpCost Cφ (vsPN S) (vsPW6 S) +
    vsPRadCost (I := I) Cφ (vsPN S) (vsPW6 S) + vsPS4Cost Cφ hn S + vsPGrowCost hn (vsPN S) (vsPW6 S) +
    10 ^ 4 * (vsPN S + 1) * (vsPW6 S + 100 * (vsPN S + 1) ^ 3)

set_option maxHeartbeats 4000000 in
/-- **The weight of an output.** -/
theorem VsPOut.wt_le [Fact I.p.Prime] {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ccs tcs : List (Perm (Fin I.n))}
    {w : Val} (h : VsPOut hs as Lb ccs tcs w) :
    w.wt ≤ 100 * (vsPIn s as Lb ccs tcs).wt + 1000 * S ^ 6 := by
  have hS1 := hS.one_le
  have hn6 : (I.n + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left hS.n 6
  have p6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ (by omega)
  rcases h with ⟨as', rfl, hout⟩ | ⟨ys, r, rfl, -, -, hyl, -, hrn, -⟩
  · have := wt_encGroup_le_sq hout.len
    have := wt_list2_le (Val.nat 0) (encGroup as')
    have := wt_nat_le 0
    omega
  · set A := vsPIn s as Lb ccs tcs
    set St := Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]
    set LC := Val.list [St, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat (vsQD s), vsFMatsVal (vsQMs s)]
    have wLC : LC.wt < A.wt := wt_le_wt_list (by simp [A, vsPIn, LC, St, vsQLCV, vsQStV])
    have wSt : St.wt < LC.wt := wt_le_wt_list (by simp [LC])
    have wG : (vsQGam I).wt < St.wt := wt_le_wt_list (by simp [St])
    have wHs : (encGroup s.hs).wt < St.wt := wt_le_wt_list (by simp [St])
    have wW' : (vsWVs s.ws').wt < St.wt := wt_le_wt_list (by simp [St])
    have wW : (vsWVs s.ws).wt < St.wt := wt_le_wt_list (by simp [St])
    have wFr : (vsWFrVal I.p I.d s.ws' (vsQCs s)).wt < LC.wt := wt_le_wt_list (by simp [LC])
    have wAs : (encGroup as).wt < A.wt := wt_le_wt_list (by simp [A, vsPIn])
    have wCc : (encGroup ccs).wt < A.wt := wt_le_wt_list (by simp [A, vsPIn])
    have wTc : (Val.list (tcs.map encPerm)).wt < A.wt := wt_le_wt_list (by simp [A, vsPIn])
    have wLb : (vsFMatsVal Lb).wt < A.wt := wt_le_wt_list (by simp [A, vsPIn])
    have hD := vsQD_le hs
    have hyl' : ys.length ≤ S ^ 2 := hyl.trans (Nat.pow_le_pow_left (by have := hS.d; omega) 2)
    have wys := vs_wt_list_le_of (ys.map encPerm) (c := 4 * S ^ 2) (by
      intro v hv; obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
      exact (wt_encPerm_le g).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS.n 2)))
    rw [List.length_map] at wys
    have h2 : ys.length * (2 * (4 * S ^ 2) + 1) ≤ S ^ 2 * (9 * S ^ 2) :=
      Nat.mul_le_mul hyl' (by have := Nat.one_le_pow 2 S (by omega); omega)
    have e4 : S ^ 2 * (9 * S ^ 2) = 9 * S ^ 4 := by ring
    have s4 : S ^ 4 ≤ S ^ 6 := hS.pow_le (by omega)
    have wr := wt_nat_le r
    have hrS : r ≤ S ^ 6 := by
      have : S ≤ S ^ 6 := by simpa using hS.pow_le (show 1 ≤ 6 by omega)
      have := hS.n; omega
    have wGI := wt_list_le [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
      vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs, .list (tcs.map encPerm),
      .list (ys.map encPerm), .nat r, vsFMatsVal Lb]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at wGI
    have eGI : (vsPGIn s as Lb ccs tcs ys r).wt = (Val.list [vsQGam I, encGroup s.hs,
      vsWVs s.ws', vsWVs s.ws, vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs,
      .list (tcs.map encPerm), .list (ys.map encPerm), .nat r, vsFMatsVal Lb]).wt := rfl
    have := wt_list2_le (Val.nat 1) (vsPGIn s as Lb ccs tcs ys r)
    have := wt_nat_le 1
    omega

set_option maxHeartbeats 16000000 in
/-- **The pairing stage.** -/
theorem vsPS3_spec [Fact I.p.Prime] {P : Program} {hn : NormalClosure} {f : ℕ} {x : VsPS3X}
    (hf : P.funs[f]? = some (vsPS3E x.pair x.comm x.zp x.tl x.rad x.x4.grow x.s4))
    (L : VsPS3Lay P hn x) {Cφ : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.x4.d.o.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ccs tcs : List (Perm (Fin I.n))}
    (hH : VsPHyp hs as Lb ccs) {gs : List (Perm (Fin I.n))} (hgl : gs.length ≤ I.n ^ 2)
    {r : ℕ} [hr : Fact r.Prime] (hrn : r ≤ I.n) (h2 : VsPN2 hs as gs r) {x2 : Perm (Fin I.n)}
    (hx2 : x2 ∈ vsPYs hs (vsPBar hs (gens gs)))
    (hx2b : vsPInLB I s.ws' (vsQCs s) (vsPRows I.p Lb) x2 = false)
    (hx2C : x2 ∈ gens ccs)
    (hnab : ¬ ∀ g ∈ 1 :: gs, ∀ h ∈ 1 :: gs,
      vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)) :
    FunAll P f (.list [vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs, vsPIn s as Lb ccs tcs,
        encGroup gs, .list [encPerm x2, .nat r]])
      (fun w c => VsPOut hs as Lb ccs tcs w ∧
        c ≤ vsPS3Cost (I := I) Cφ hn S + 10 ^ 5 * (vsPIn s as Lb ccs tcs).wt) := by
  haveI : NeZero r := ⟨hr.out.ne_zero⟩
  have hr2 := hr.out.two_le
  set N := vsPN S
  set W := vsPW6 S
  set rows := vsPRows I.p Lb
  set C := vsPCtx I s.ws' (vsQCs s) rows s.hs
  set A := vsPIn s as Lb ccs tcs
  set o := Val.list [encPerm x2, .nat r]
  set G2 := encGroup gs
  have hD := vsQD_le hs
  have hLbW : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M := fun M hM =>
    ⟨fun a ha => (hH.hLb M hM).rows a ha, (hH.hLb M hM).len⟩
  have hDDN : vsQD s * vsQD s + 1 ≤ N := by
    have : vsQD s * vsQD s ≤ S * S := Nat.mul_le_mul (by have := hS.d; omega) (by have := hS.d; omega)
    have := hS.one_le
    have hS2 : S * S = S ^ 2 := (sq S).symm
    have hS3 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ (by omega)
    show vsQD s * vsQD s + 1 ≤ 4 * S ^ 2
    omega
  have hLbN : Lb.length ≤ N := le_trans hH.hLbl (Nat.le_of_succ_le hDDN)
  have hgsI : ∀ g ∈ gs, g ∈ gens I.gs := fun g hg => hs.prob.le (h2.hgs g hg)
  have H := (vsPCtx_ok hS hs hLbW hLbN).mono_W (W' := W) (by simp only [W, vsPW6]; omega)
  -- the pair
  obtain ⟨i, j, hi, hj, hne, dP⟩ := vsPPair_spec L.hpair L.L4.hfo L.L4.hno L.L4.hfi L.L4.hnc
    L.L4.d.L.hcomp L.L4.d.L.hloc L.L4.d.L.hwl L.L4.d.L.heq hphi H hgsI hgl hnab
  set a := (1 :: gs)[i]
  set b := (1 :: gs)[j]
  have ha : a ∈ 1 :: gs := List.getElem_mem hi
  have hb : b ∈ 1 :: gs := List.getElem_mem hj
  obtain ⟨hc0, hP⟩ := vsP_N2_pair hH h2 ha hb hne
  set c0 := ⁅a, b⁆
  set Zp := vsPZp I s.ws' (vsQCs s) c0 r
  have OD := vsPOD_of hS hs hLbW hLbN h2.hgs hgl hr.out.pos hrn (c0 := c0)
  have hgN : ∀ g ∈ gs, vsPRho hs g ∈ vsPBar hs (gens gs) :=
    fun g hg => vsPRho_mem_vsPBar hs (Subgroup.subset_closure hg) (h2.hgs g hg)
  have hfitK : ∀ g ∈ gs, (∀ a ∈ vsPKey I s.ws' (vsQCs s) Zp gs g, a < r) ∧
      (vsPKey I s.ws' (vsQCs s) Zp gs g).length = gs.length :=
    fun g hg => vsPKey_fit hs hc0 hP h2.hgs hgN (h2.hgs g hg) (hgN g hg)
  set vs := [C, A, G2, o]
  set L2 := (1 :: gs).map encPerm
  set PV := Val.list [.nat i, .nat j]
  set ZV := Val.list (Zp.map vsWVs)
  set gV := Val.list (gs.map encPerm)
  set pc := vsPPc I s.ws' (vsQCs s) rows s.hs gs Zp
  set rc := vsPRc I s.ws' (vsQCs s) rows s.hs gs
  set RV := vsPRadV I s.ws' (vsQCs s) rows Zp gs r
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a2 : Det P [Val.list vs] (arg 2) G2 _ := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have dP' := Det.call (Det.mk2 a0 a2) dP
  -- `L2`
  have b2 : Det P [Val.list vs, PV] (arg 2) (.list [.nat I.n, .list L2]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [PV]) (j := 2) rfl
  have dL := Det.get' b2 (Det.nat 1) (show [Val.nat I.n, .list L2][1]? = some (.list L2) from rfl)
  -- `c0`
  set E2 := [Val.list vs, PV, Val.list L2]
  have v1 : Det P E2 (.var 1) (.list [.nat i, .nat j]) _ := Det.var' (P := P) (env := E2) (i := 1) rfl
  have v2 : Det P E2 (.var 2) (.list L2) _ := Det.var' (P := P) (env := E2) (i := 2) rfl
  have gi := Det.get' v1 (Det.nat 0) (show [Val.nat i, .nat j][0]? = some (.nat i) from rfl)
  have gj := Det.get' v1 (Det.nat 1) (show [Val.nat i, .nat j][1]? = some (.nat j) from rfl)
  have ga := Det.get' v2 gi (show L2[i]? = some (encPerm a) by
    simp only [L2, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl)
  have gb := Det.get' v2 gj (show L2[j]? = some (encPerm b) by
    simp only [L2, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl)
  have dc := Det.call (Det.mk2 ga gb) (vsPComm_spec L.hcomm L.L4.d.L.hcomp L.L4.d.L.hinv a b)
  -- `Zp`
  set E3 := [Val.list vs, PV, Val.list L2, encPerm c0]
  have c0' : Det P E3 (arg 0) C _ := Det.arg' (P := P) (vs := vs) (rest := [PV, .list L2, encPerm c0]) (j := 0) rfl
  have c3 : Det P E3 (arg 3) (.list [encPerm x2, .nat r]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [PV, .list L2, encPerm c0]) (j := 3) rfl
  have cr := Det.get' c3 (Det.nat 1) (show [encPerm x2, Val.nat r][1]? = some (.nat r) from rfl)
  have dZ := Det.call (Det.mk3 c0' (Det.var' (P := P) (env := E3) (i := 3) rfl) cr)
    (vsPZp_spec L.hzp L.hzmp L.hzit L.L4.e.hrng L.L4.e.hpow L.L4.d.L.hloc L.L4.d.L.hwl hphi H
      (hs.prob.le hc0) (r := r) (by have := OD.hrN; exact this))
  -- `gs`
  set E4 := [Val.list vs, PV, Val.list L2, encPerm c0, ZV]
  have dT := Det.call (Det.var' (P := P) (env := E4) (i := 2) rfl)
    (GI.Lang.tail_spec L.htl (encPerm 1) (gs.map encPerm))
  -- `pc`, `rc`
  set E5 := [Val.list vs, PV, Val.list L2, encPerm c0, ZV, gV]
  have e0 : Det P E5 (arg 0) C _ :=
    Det.arg' (P := P) (vs := vs) (rest := [PV, .list L2, encPerm c0, ZV, gV]) (j := 0) rfl
  have dpc := Det.mk3 e0 (Det.var' (P := P) (env := E5) (i := 5) rfl) (Det.var' (P := P) (env := E5) (i := 4) rfl)
  have epc : Val.list [C, gV, ZV] = pc := rfl
  rw [epc] at dpc
  set E6 := [Val.list vs, PV, Val.list L2, encPerm c0, ZV, gV, pc]
  have f0 : Det P E6 (arg 0) C _ :=
    Det.arg' (P := P) (vs := vs) (rest := [PV, .list L2, encPerm c0, ZV, gV, pc]) (j := 0) rfl
  have f5 : Det P E6 (.var 5) (.list (gs.map encPerm)) _ := Det.var' (P := P) (env := E6) (i := 5) rfl
  have f1 := Det.get' (Det.var' (P := P) (env := E6) (i := 2) rfl) (Det.nat 0)
    (show L2[0]? = some (encPerm (1 : Perm (Fin I.n))) from rfl)
  have fl := Det.length f5
  rw [List.length_map] at fl
  have drc := Det.mk4 f0 f5 f1 fl
  have erc : Val.list [C, gV, encPerm (1 : Perm (Fin I.n)), .nat gs.length] = rc := rfl
  rw [erc] at drc
  -- the radical stage
  set E7 := [Val.list vs, PV, Val.list L2, encPerm c0, ZV, gV, pc, rc]
  have g3 : Det P E7 (arg 3) (.list [encPerm x2, .nat r]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [PV, .list L2, encPerm c0, ZV, gV, pc, rc]) (j := 3) rfl
  have gr := Det.get' g3 (Det.nat 1) (show [encPerm x2, Val.nat r][1]? = some (.nat r) from rfl)
  have hS1 := hS.one_le
  have wC0 : C.wt ≤ 10 ^ 8 * S ^ 6 := (vsPCtx_ok hS hs hLbW hLbN).cw
  have wgV : gV.wt ≤ 13 * (I.n + 1) ^ 6 := wt_list_encPerms_le_sq hgl
  have hn6 : (I.n + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left hS.n 6
  have hn2 : (I.n + 1) ^ 2 ≤ S ^ 6 := (Nat.pow_le_pow_left hS.n 2).trans (hS.pow_le (by omega))
  have we1 : (encPerm (1 : Perm (Fin I.n))).wt ≤ 4 * (I.n + 1) ^ 2 := wt_encPerm_le _
  have wgl := wt_nat_le gs.length
  have hgl6 : gs.length ≤ S ^ 6 := by
    have : I.n ^ 2 ≤ (I.n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have wrc4 := wt_list_le [C, gV, encPerm (1 : Perm (Fin I.n)), .nat gs.length]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wrc4
  have hrc : rc.wt ≤ W := by
    have e : rc.wt = (Val.list [C, gV, encPerm (1 : Perm (Fin I.n)), .nat gs.length]).wt := rfl
    have p6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ (by omega)
    simp only [W, vsPW6]; omega
  have dR := Det.call (Det.mk3 (Det.var' (P := P) (env := E7) (i := 6) rfl)
    (Det.var' (P := P) (env := E7) (i := 7) rfl) gr)
    (vsPRad_spec L.hrad L.L4.d L.hgmp L.hker L.hrfnd L.hrp L.hword L.L4.e.hpow hphi OD
      (by omega) hrc hfitK)
  refine FunAll.intro hf (EvalAll.letE dP' fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.letE dL fun v2 c2 h2' => ?_
  obtain ⟨rfl, hc2⟩ := h2'
  refine EvalAll.letE dc fun v3 c3' h3 => ?_
  obtain ⟨rfl, hc3⟩ := h3
  refine EvalAll.letE dZ fun v4 c4 h4' => ?_
  obtain ⟨rfl, hc4⟩ := h4'
  refine EvalAll.letE dT fun v5 c5 h5 => ?_
  obtain ⟨rfl, hc5⟩ := h5
  refine EvalAll.letE dpc fun v6 c6 h6 => ?_
  obtain ⟨rfl, hc6⟩ := h6
  refine EvalAll.letE drc fun v7 c7 h7 => ?_
  obtain ⟨rfl, hc7⟩ := h7
  refine EvalAll.letE dR fun v8 c8 h8 => ?_
  obtain ⟨rfl, hc8⟩ := h8
  set E8 := [Val.list vs, PV, Val.list L2, encPerm c0, ZV, gV, pc, rc, RV]
  -- weights
  have wvs := wt_list_le vs
  simp only [vs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wvs
  have evs : (Val.list vs).wt = (Val.list [C, A, G2, o]).wt := rfl
  have wG2 : G2.wt ≤ 320 * (I.n + 1) ^ 6 := wt_encGroup_le_sq hgl
  have wo := wt_list2_le (encPerm x2) (.nat r)
  have eo : o.wt = (Val.list [encPerm x2, .nat r]).wt := rfl
  have wx2 : (encPerm x2).wt ≤ 4 * (I.n + 1) ^ 2 := wt_encPerm_le x2
  have wr := wt_nat_le r
  have hrS : r ≤ S ^ 6 := by
    have : S ≤ S ^ 6 := by simpa using hS.pow_le (show 1 ≤ 6 by omega)
    have := hS.n; omega
  have hi' : i ≤ S ^ 6 := by simp at hi; omega
  have hj' : j ≤ S ^ 6 := by simp at hj; omega
  have wPV := wt_list2_le (Val.nat i) (Val.nat j)
  have ePV : PV.wt = (Val.list [Val.nat i, Val.nat j]).wt := rfl
  have wi := wt_nat_le i
  have wj := wt_nat_le j
  have wL2 : (Val.list L2).wt < G2.wt := wt_le_wt_list (by simp [G2, encGroup, encPerms, L2])
  have wc0 : (encPerm c0).wt ≤ 4 * (I.n + 1) ^ 2 := wt_encPerm_le c0
  have wpc : pc.wt ≤ W := OD.hpc
  have wZV : ZV.wt < pc.wt := wt_le_wt_list (by simp [pc, vsPPc, ZV])
  have wRV : RV.wt ≤ 20 * (I.n + 1) ^ 2 + 20 := by
    show (vsPRadV I s.ws' (vsQCs s) rows Zp gs r).wt ≤ _
    unfold vsPRadV
    split_ifs
    · have := wt_list2_le (Val.nat 1) (encPerm (vsPW gs (vsWKer r (vsPGram I s.ws' (vsQCs s) Zp gs))[
          vsPRadJ I s.ws' (vsQCs s) rows Zp gs r]))
      have := wt_encPerm_le (vsPW gs (vsWKer r (vsPGram I s.ws' (vsQCs s) Zp gs))[
          vsPRadJ I s.ws' (vsQCs s) rows Zp gs r])
      have := wt_nat_le 1; omega
    · have := wt_list2_le (Val.nat 0) (encPerm (1 : Perm (Fin I.n)))
      have := wt_encPerm_le (1 : Perm (Fin I.n)); have := wt_nat_le 0; omega
  have wWS : W = 10 ^ 9 * S ^ 6 := rfl
  have hNS : N + 1 ≤ 5 * S ^ 6 := by
    have : S ^ 2 ≤ S ^ 6 := hS.pow_le (by omega)
    simp only [N, vsPN]; have := Nat.one_le_pow 6 S (by omega); omega
  have hglN : gs.length ≤ N := by
    have : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by have := hS.n; omega) 2
    simp only [N, vsPN]; omega
  set Y := (N + 1) * (W + 100 * (N + 1) ^ 3)
  have hY1 : W + 100 * (N + 1) ^ 3 ≤ Y := Nat.le_mul_of_pos_left _ (by omega)
  have hTl : loopModK * ((gs.map encPerm).length + 1) *
      (3 * (Val.list (encPerm (1 : Perm (Fin I.n)) :: gs.map encPerm)).wt + 1) ≤ 1000 * (4 * Y) := by
    have hA : 3 * (Val.list (encPerm (1 : Perm (Fin I.n)) :: gs.map encPerm)).wt + 1 ≤ 4 * (W + 100 * (N + 1) ^ 3) := by
      have e : (Val.list (encPerm (1 : Perm (Fin I.n)) :: gs.map encPerm)).wt = (Val.list L2).wt := rfl
      have p6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ (by omega)
      omega
    have e1 : (N + 1) * (4 * (W + 100 * (N + 1) ^ 3)) = 4 * Y := by simp only [Y]; ring
    calc loopModK * ((gs.map encPerm).length + 1) * (3 * (Val.list (encPerm (1 : Perm (Fin I.n)) :: gs.map encPerm)).wt + 1)
        ≤ loopModK * (N + 1) * (4 * (W + 100 * (N + 1) ^ 3)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by rw [List.length_map]; omega)) hA
      _ = 1000 * (4 * Y) := by rw [mul_assoc, e1]; rfl
  have eY : 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3) = 10 ^ 4 * Y := by rw [mul_assoc]
  have lPair : vsPPairCost Cφ (vsPN S) W = vsPPairCost Cφ (vsPN S) (vsPW6 S) := rfl
  have lZp : vsPZpCost Cφ (vsPN S) W = vsPZpCost Cφ (vsPN S) (vsPW6 S) := rfl
  have lGrow : vsPGrowCost hn N W = vsPGrowCost hn (vsPN S) (vsPW6 S) := rfl
  have lComm : vsPCommCost I.n ≤ vsPCommCost (vsPN S) := by
    unfold vsPCommCost
    have : I.n ≤ vsPN S := by
      have := hS.n; have : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _; simp only [vsPN]; omega
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have lc0 : (encPerm ⁅a, b⁆).wt = (encPerm c0).wt := rfl
  have lZV : (Val.list (List.map vsWVs (vsPZp I s.ws' (vsQCs s) c0 r))).wt = ZV.wt := rfl
  have lRV : (vsPRadV I s.ws' (vsQCs s) rows Zp gs r).wt = RV.wt := rfl
  have lA : (Val.list [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ccs,
      Val.list (List.map encPerm tcs)]).wt = A.wt := rfl
  have lgV : (Val.list (List.map encPerm gs)).wt = gV.wt := rfl
  have wa := wt_encPerm_le a
  have wb := wt_encPerm_le b
  have wab := wt_list2_le (encPerm a) (encPerm b)
  have wCc := wt_list3_le C (encPerm c0) (Val.nat r)
  have wpr := wt_list3_le pc rc (Val.nat r)
  have wCG := wt_list2_le C G2
  have hpl : (1 :: gs).length ≤ S ^ 6 := by
    have : (I.n + 1) ^ 2 = I.n ^ 2 + 2 * I.n + 1 := by ring
    simp only [List.length_cons]; omega
  have hpre : c1 + c2 + c3' + c4 + c5 + c6 + c7 + c8 ≤ vsPPairCost Cφ (vsPN S) (vsPW6 S) +
      vsPCommCost (vsPN S) + vsPZpCost Cφ (vsPN S) (vsPW6 S) + vsPRadCost (I := I) Cφ (vsPN S) (vsPW6 S) +
      4000 * Y + 100 * (Val.list vs).wt + 100 * W + 1000 * S ^ 6 := by
    omega
  set K := vsWKer r (vsPGram I s.ws' (vsQCs s) Zp gs)
  set J := vsPRadJ I s.ws' (vsQCs s) rows Zp gs r
  have h1i : Det P E8 (arg 1) A _ :=
    Det.arg' (P := P) (vs := vs) (rest := [PV, .list L2, encPerm c0, ZV, gV, pc, rc, RV]) (j := 1) rfl
  have h0i : Det P E8 (arg 0) C _ :=
    Det.arg' (P := P) (vs := vs) (rest := [PV, .list L2, encPerm c0, ZV, gV, pc, rc, RV]) (j := 0) rfl
  have h3i : Det P E8 (arg 3) o _ :=
    Det.arg' (P := P) (vs := vs) (rest := [PV, .list L2, encPerm c0, ZV, gV, pc, rc, RV]) (j := 3) rfl
  by_cases hJ : J < K.length
  · -- a relation word outside `L`: grow
    set z := vsPW gs K[J]
    have eRV : RV = .list [.nat 1, encPerm z] := by
      show vsPRadV I s.ws' (vsQCs s) rows Zp gs r = _; unfold vsPRadV; rw [dif_pos hJ]
    have dT8 : Det P E8 (.get (.var 8) (.nat 0)) (.nat 1) _ :=
      Det.get' (Det.var' (P := P) (env := E8) (i := 8) (v := .list [.nat 1, encPerm z]) (by
        rw [← eRV]; rfl)) (Det.nat 0) rfl
    refine EvalAll.ite dT8 (fun vc cc h => ⟨_, h.1⟩) fun xb cc hcc => ?_
    obtain ⟨hxb, hcc⟩ := hcc
    cases hxb
    rw [if_neg one_ne_zero]
    have hz8 : Det P E8 (.get (.var 8) (.nat 1)) (encPerm z) _ :=
      Det.get' (Det.var' (P := P) (env := E8) (i := 8) (v := .list [.nat 1, encPerm z]) (by
        rw [← eRV]; rfl)) (Det.nat 1) rfl
    have g1 := Det.get' h1i (Det.nat 1) (show [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ccs,
      Val.list (tcs.map encPerm)][1]? = some (encGroup as) from rfl)
    have gx : Det P E8 (mk1 (.get (.var 8) (.nat 1))) (.list ([z].map encPerm)) _ := Det.mk1 hz8
    have hzK : K[J] ∈ K := List.getElem_mem hJ
    have hzb : vsPInLB I s.ws' (vsQCs s) rows z = false := by
      have := List.findIdx_getElem (w := hJ)
      simpa using this
    have hn2' := hH.two_le_n
    have hxl : [z].length ≤ I.n ^ 2 := by
      show 1 ≤ I.n ^ 2; exact Nat.one_le_pow _ _ (by omega)
    have wAl : A.wt < (Val.list vs).wt :=
      wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self (a := A) (l := vs.tail.tail)))
    have wC0' : C.wt < (Val.list vs).wt := wt_le_wt_list (List.mem_cons_self (a := C) (l := vs.tail))
    have wAs : (encGroup as).wt < A.wt := wt_le_wt_list (by simp [A, vsPIn])
    have wz := wt_encPerm_le z
    have w1z := wt_list1_le (encPerm z)
    have e1z : Val.list ([z].map encPerm) = Val.list [encPerm z] := rfl
    have w3a := wt_list3_le C (encGroup as) (Val.list [encPerm z])
    have wA1 : (Val.list [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ccs,
        Val.list (tcs.map encPerm)]).wt = A.wt := rfl
    have wRV1 : (Val.list [Val.nat 1, encPerm z]).wt = RV.wt := by rw [eRV]
    obtain ⟨KA, hKA, dA⟩ : ∃ K, K = _ ∧ Det P E8 _ _ K := ⟨_, rfl, Det.mk3 h0i g1 gx⟩
    refine (EvalAll.mk2_last (Det.nat (P := P) (env := E8) 0)
      (EvalAll.call_funAll dA (Q := fun w cb => ∃ as' : List (Perm (Fin I.n)),
        w = encGroup as' ∧ VsPGrowOut hs as as' ∧
          cb ≤ KA + vsPGrowCost hn N W + w.wt + 1)
        fun v ca hv => ?_)).mono ?_
    · obtain ⟨rfl, hca⟩ := hv
      refine (vsPGrow_spec hn L.L4.hgrow L.L4.hap L.L4.hmkg L.L4.hncp H hs.hsl hH.hal hxl).mono ?_
      rintro w cb ⟨as', rfl, hl, he, hcb⟩
      have hcb' : cb ≤ vsPGrowCost hn N W := hcb
      exact ⟨as', rfl, vsP_rad_grow hH h2 hc0 hP hH.ib hzK hzb hl he, by omega⟩
    · rintro w cw ⟨vb, cb, ⟨as', rfl, hout, hcb⟩, rfl, hcw⟩
      refine ⟨Or.inl ⟨as', rfl, hout⟩, ?_⟩
      have wa' : (encGroup as').wt ≤ 320 * (I.n + 1) ^ 6 := wt_encGroup_le_sq hout.len
      have w02 := wt_list2_le (Val.nat 0) (encGroup as')
      have w0 := wt_nat_le 0
      have hn6' : (I.n + 1) ^ 6 ≤ S ^ 6 := hn6
      have lz : (Val.list [C, encGroup as, Val.list (List.map encPerm [z])]).wt =
        (Val.list [C, encGroup as, Val.list [encPerm z]]).wt := rfl
      have w11 := wt_nat_le 1
      have hKAb : KA ≤ 20 * (Val.list vs).wt + 100 * S ^ 6 + 200 := by omega
      have hc3b : (Val.list [Val.nat 0, encGroup as']).wt ≤ 640 * S ^ 6 + 20 := by omega
      have hccb : cc ≤ 20 * (Val.list vs).wt + 200 * S ^ 6 + 300 := by omega
      have hcwb : cw ≤ vsPGrowCost hn (vsPN S) (vsPW6 S) + 20 * (Val.list vs).wt + 2000 * S ^ 6 + 400 := by
        omega
      have hbr : cc + cw + 9 * (Val.list [Val.nat 0, encGroup as']).wt ≤
          vsPGrowCost hn (vsPN S) (vsPW6 S) + 50 * (Val.list vs).wt + 10 ^ 4 * S ^ 6 + 1000 := by
        omega
      unfold vsPS3Cost
      rw [eY]
      omega
  · -- the radical lies in `S`: the last stage
    have eRV : RV = .list [.nat 0, encPerm (1 : Perm (Fin I.n))] := by
      show vsPRadV I s.ws' (vsQCs s) rows Zp gs r = _; unfold vsPRadV; rw [dif_neg hJ]
    have dT8 : Det P E8 (.get (.var 8) (.nat 0)) (.nat 0) _ :=
      Det.get' (Det.var' (P := P) (env := E8) (i := 8) (v := .list [.nat 0, encPerm 1]) (by
        rw [← eRV]; rfl)) (Det.nat 0) rfl
    refine EvalAll.ite dT8 (fun vc cc h => ⟨_, h.1⟩) fun xb cc hcc => ?_
    obtain ⟨hxb, hcc⟩ := hcc
    cases hxb
    rw [if_pos rfl]
    have hall : ∀ t ∈ K, vsPInLB I s.ws' (vsQCs s) rows (vsPW gs t) = true := by
      have hJe : J = K.length := le_antisymm List.findIdx_le_length (by omega)
      have := List.findIdx_eq_length.1 hJe
      intro t ht
      simpa using this t ht
    have hrad := vsP_rad_of_prog h2 hc0 hP hH.ib hall
    have h4 : VsPS4 hs as gs r c0 :=
      ⟨fun a ha b hb => (Subgroup.mem_centralizer_iff.1 (hH.habl hb) a ha), hH.hdom, h2.hgs, h2.hNC,
        h2.hNn, h2.hc, h2.hpow, hc0, hP, hrad⟩
    have d6 : Det P E8 (.var 6) pc _ := Det.var' (P := P) (env := E8) (i := 6) rfl
    refine EvalAll.call_funAll (Det.mk4 h0i h1i d6 h3i) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (vsPS4_spec L.hs4 L.L4 hphi hS hs hH hgl hrn h4 hx2 hx2b hx2C).mono ?_
    rintro w cw ⟨hout, hcw⟩
    refine ⟨hout, ?_⟩
    have hwt := VsPOut.wt_le hS hs hout
    have w4 := wt_list4_le C A pc o
    have wAl : A.wt < (Val.list vs).wt :=
      wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self (a := A) (l := vs.tail.tail)))
    have wRV0 : (Val.list [Val.nat 0, encPerm (1 : Perm (Fin I.n))]).wt = RV.wt := by rw [eRV]
    have w00 := wt_nat_le 0
    have lAA : A.wt = (vsPIn s as Lb ccs tcs).wt := rfl
    unfold vsPS3Cost
    rw [eY]
    omega

end GI.Impl
