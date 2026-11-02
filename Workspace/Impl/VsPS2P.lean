import Workspace.Impl.VsPS3P

/-!
# From `N₀` to `N₂`

On `[ctx, input, ⟨ns₀⟩]` with `N̄₀` not abelian: a generator `x` of `N₀` outside `L`, the element
`x₂ ∈ ⟨x⟩` of prime order `r` modulo `S` (`vsPOrd`), `N₂ = ⟨x₂⟩^H` (normal closure); if `N̄₂` is
abelian, grow with `ns₂`, else go on with the pairing stage (`vsPS2_spec`).
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)
open scoped commutatorElement

variable {I : VecStabInst}

/-- On `[ctx, input, ⟨ns₀⟩]`: from `N₀` to `N₂`. -/
def vsPS2E (fnd2 ord mkg grow ab tl s3 : ℕ) : Expr :=
  .letE (.call fnd2 (mk2 (arg 0) (.get (arg 2) (.nat 1))))
  (.letE (.get (.get (arg 2) (.nat 1)) (.var 1))
  (.letE (.call ord (mk2 (arg 0) (.var 2)))
  (.letE (.call mkg (mk2 (.get (arg 0) (.nat 6)) .nil))
  (.letE (.call grow (mk3 (arg 0) (.var 4) (mk1 (.get (.var 3) (.nat 0)))))
    (.ite (.call ab (mk2 (arg 0) (.var 5)))
      (mk2 (.nat 0) (.call grow (mk3 (arg 0) (.get (arg 1) (.nat 1)) (.call tl (.get (.var 5) (.nat 1))))))
      (.call s3 (mk4 (arg 0) (arg 1) (.var 5) (.var 3))))))))

/-- The function indices of this stage. -/
structure VsPS2X where
  (x3 : VsPS3X) (s3 fnd2 ord : ℕ)

/-- The layout of this stage. -/
structure VsPS2Lay (P : Program) (hn : NormalClosure) (x : VsPS2X) : Prop where
  L3 : VsPS3Lay P hn x.x3
  hs3 : P.funs[x.s3]? = some (vsPS3E x.x3.pair x.x3.comm x.x3.zp x.x3.tl x.x3.rad x.x3.x4.grow x.x3.s4)
  hfnd2 : P.HasAt x.fnd2 (findFuns x.fnd2 x.x3.x4.d.nt)
  hord : P.HasAt x.ord (vsPOrdFuns x.ord x.x3.x4.d.o.phi)

/-- The cost of this stage. -/
noncomputable def vsPS2Cost (Cφ : ℕ) (hn : NormalClosure) (S : ℕ) : ℕ :=
  (vsPN S + 1) * (vsPInLPCost Cφ (vsPN S) (vsPW6 S) + 20 * vsPW6 S + 100 + 100 * (vsPN S + 1) ^ 2) +
    vsPOrdCost Cφ (vsPN S) (vsPW6 S) + mkGroupK * (2 * (vsPN S + 1)) ^ 3 +
    2 * vsPGrowCost hn (vsPN S) (vsPW6 S) + vsPAbCost Cφ (vsPN S) (vsPW6 S) +
    vsPS3Cost (I := I) Cφ hn S + 10 ^ 4 * (vsPN S + 1) * (vsPW6 S + 100 * (vsPN S + 1) ^ 3)

set_option maxHeartbeats 16000000 in
/-- **From `N₀` to `N₂`.** -/
theorem vsPS2_spec [Fact I.p.Prime] {P : Program} {hn : NormalClosure} {f : ℕ} {x : VsPS2X}
    (hf : P.funs[f]? = some (vsPS2E x.fnd2 x.ord x.x3.x4.mkg x.x3.x4.grow x.x3.x4.ab x.x3.tl x.s3))
    (L : VsPS2Lay P hn x) {Cφ : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.x3.x4.d.o.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ccs tcs : List (Perm (Fin I.n))}
    (hH : VsPHyp hs as Lb ccs) {ns0 : List (Perm (Fin I.n))} (hl0 : ns0.length ≤ I.n ^ 2) {j0 : ℕ}
    (hgen : gens ns0 = vsPDer (gens ccs) j0) (hj : vsPDer (gens ccs) (j0 + 1) ≤ vsPSp hs as)
    (hout0 : ¬ gens ns0 ≤ vsPSp hs as)
    (hnab0 : ¬ ∀ g ∈ 1 :: ns0, ∀ h ∈ 1 :: ns0,
      vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)) :
    FunAll P f (.list [vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs, vsPIn s as Lb ccs tcs,
        encGroup ns0])
      (fun w c => VsPOut hs as Lb ccs tcs w ∧
        c ≤ vsPS2Cost (I := I) Cφ hn S + 10 ^ 6 * (vsPIn s as Lb ccs tcs).wt) := by
  set N := vsPN S
  set W := vsPW6 S
  set rows := vsPRows I.p Lb
  set C := vsPCtx I s.ws' (vsQCs s) rows s.hs
  set A := vsPIn s as Lb ccs tcs
  set ib := vsPInLB I s.ws' (vsQCs s) rows
  set L0 := 1 :: ns0
  have hS1 := hS.one_le
  have hD := vsQD_le hs
  have hLbW : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M := fun M hM =>
    ⟨fun a ha => (hH.hLb M hM).rows a ha, (hH.hLb M hM).len⟩
  have hDDN : vsQD s * vsQD s + 1 ≤ N := by
    have : vsQD s * vsQD s ≤ S * S := Nat.mul_le_mul (by have := hS.d; omega) (by have := hS.d; omega)
    have hS2 : S * S = S ^ 2 := (sq S).symm
    have hS3 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ (by omega)
    show vsQD s * vsQD s + 1 ≤ 4 * S ^ 2
    omega
  have hLbN : Lb.length ≤ N := le_trans hH.hLbl (Nat.le_of_succ_le hDDN)
  have hC0 := vsPCtx_ok hS hs hLbW hLbN
  have H := hC0.mono_W (W' := W) (by simp only [W, vsPW6]; omega)
  have hib := hH.ib
  obtain ⟨hN0, hN0n, hN0C, hN0c⟩ := hH.N0 hj
  rw [← hgen] at hN0 hN0n hN0C hN0c
  have hL0 : ∀ g ∈ L0, g ∈ gens ns0 := by
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact one_mem _
    · exact Subgroup.subset_closure hg
  have hn2 := hH.two_le_n
  have hnN : I.n + 2 ≤ N := by
    have := hS.n; have : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
    show I.n + 2 ≤ 4 * S ^ 2; omega
  -- the generator outside `L`
  set k := L0.findIdx (fun g => !ib g)
  have hk : k < L0.length := by
    obtain ⟨y, hy, hyS⟩ := vsP_exists_gen_not_mem hout0
    have hyg := hN0 (Subgroup.subset_closure hy)
    refine List.findIdx_lt_length_of_exists ⟨y, List.mem_cons_of_mem _ hy, ?_⟩
    have : ib y = false := by
      cases e : ib y
      · rfl
      · exact absurd ((vsPSp_iff hs as hyg).2 ((hib y hyg).1 e)) hyS
    simp [this]
  set xg := L0[k]
  have hxb : ib xg = false := by
    have := List.findIdx_getElem (w := hk)
    simpa using this
  have hxN0 : xg ∈ gens ns0 := hL0 _ (List.getElem_mem hk)
  have hxg : xg ∈ gens s.hs := hN0 hxN0
  have h1 : ib 1 = true := (hib 1 (one_mem _)).2 (by rw [vsPRho_one]; exact one_mem _)
  obtain ⟨hx2z, hrp, hrn, hx2b, hx2r, -⟩ := vsPOrd_out hxb h1 hn2
  set x2 := vsPOrdX I s.ws' (vsQCs s) rows xg
  set r := vsPOrdR I s.ws' (vsQCs s) rows xg
  haveI : Fact r.Prime := ⟨hrp⟩
  have hx2N0 : x2 ∈ gens ns0 := Subgroup.zpowers_le.2 hxN0 hx2z
  have hx2g : x2 ∈ gens s.hs := hN0 hx2N0
  have hx2rS : vsPRho hs (x2 ^ r) ∈ vsMScal (vsPBar hs (gens as)) :=
    (hib _ (pow_mem hx2g r)).1 hx2r
  have hx2S : vsPRho hs x2 ∉ vsMScal (vsPBar hs (gens as)) := fun h' => by
    rw [← hib x2 hx2g] at h'; rw [h'] at hx2b; exact Bool.noConfusion hx2b
  -- the program
  set G0 := encGroup ns0
  set vs := [C, A, G0]
  set LV := L0.map encPerm
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a2 : Det P [Val.list vs] (arg 2) (.list [.nat I.n, .list LV]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have gL := Det.get' a2 (Det.nat 1) (show [Val.nat I.n, .list LV][1]? = some (.list LV) from rfl)
  have hpred : ∀ v ∈ LV, FunDet P x.x3.x4.d.nt (.list [C, v]) (boolVal (vsPQN ib v))
      (vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2) := by
    intro v hv
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hv
    exact vsPNotIn_spec L.L3.L4.d.hnt L.L3.L4.d.hinl hphi H (hs.prob.le (hN0 (hL0 g hg)))
  have hkv : LV.findIdx (vsPQN ib) = k := by
    rw [vsP_findIdx_map]; congr 1; funext g; simp only [Function.comp, vsPQN_enc]
  have hLVl : LV.length ≤ N := by
    simp only [LV, List.length_map, L0, List.length_cons]
    have : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by have := hS.n; omega) 2
    show ns0.length + 1 ≤ 4 * S ^ 2; have := Nat.one_le_pow 2 S (by omega); omega
  obtain ⟨Kf, hKf, dF⟩ : ∃ K, K = (LV.length * (vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2) +
      loopModK * (LV.length + 1) * ((Val.list [C, .list LV]).wt + 2 * LV.length + 3)) ∧
      FunDet P x.fnd2 (.list [C, .list LV]) (.nat k) K := by
    refine ⟨_, rfl, (find_spec L.hfnd2 hpred).mono fun w c h => ⟨by rw [h.1, hkv], ?_⟩⟩
    have h2 := h.2
    have e1 : (LV.map fun _ => vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2).sum =
        LV.length * (vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2) := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul]
    rw [e1] at h2; exact h2
  have d1 := Det.call (Det.mk2 a0 gL) dF
  set E1 := [Val.list vs, Val.nat k]
  have b2 : Det P E1 (arg 2) (.list [.nat I.n, .list LV]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [.nat k]) (j := 2) rfl
  have dx := Det.get' (Det.get' b2 (Det.nat 1) (show [Val.nat I.n, .list LV][1]? = some (.list LV) from rfl))
    (Det.var' (P := P) (env := E1) (i := 1) rfl)
    (show LV[k]? = some (encPerm xg) by
      simp only [LV, List.getElem?_map, List.getElem?_eq_getElem hk]; rfl)
  set E2 := [Val.list vs, Val.nat k, encPerm xg]
  have c0 : Det P E2 (arg 0) C _ := Det.arg' (P := P) (vs := vs) (rest := [.nat k, encPerm xg]) (j := 0) rfl
  have dO := Det.call (Det.mk2 c0 (Det.var' (P := P) (env := E2) (i := 2) rfl))
    (vsPOrd_spec L.hord hphi H hn2 hnN (hs.prob.le hxg) hxb h1)
  set OV := Val.list [encPerm x2, .nat r]
  set E3 := [Val.list vs, Val.nat k, encPerm xg, OV]
  have e0 : Det P E3 (arg 0) (.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
      .list (rows.map VsRow.val), natList (vsWZ ((vsQCs s).length * (vsQCs s).length)), encGroup s.hs,
      .nat I.n]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [.nat k, encPerm xg, OV]) (j := 0) rfl
  have en := Det.get' e0 (Det.nat 6) rfl
  have dM := Det.call (Det.mk2 en (Det.nil (P := P) (env := E3)))
    (mkGroup_spec L.L3.L4.hmkg ([] : List (Perm (Fin I.n))))
  set E4 := [Val.list vs, Val.nat k, encPerm xg, OV, encGroup ([] : List (Perm (Fin I.n)))]
  have f0 : Det P E4 (arg 0) C _ :=
    Det.arg' (P := P) (vs := vs) (rest := [.nat k, encPerm xg, OV, encGroup []]) (j := 0) rfl
  have f4 := Det.var' (P := P) (env := E4) (i := 4) (v := encGroup ([] : List (Perm (Fin I.n)))) rfl
  have f3 := Det.get' (Det.var' (P := P) (env := E4) (i := 3) (v := OV) rfl) (Det.nat 0)
    (show [encPerm x2, Val.nat r][0]? = some (encPerm x2) from rfl)
  have fx : Det P E4 (mk1 (.get (.var 3) (.nat 0))) (.list ([x2].map encPerm)) _ := Det.mk1 f3
  have hxl1 : [x2].length ≤ I.n ^ 2 := by show 1 ≤ I.n ^ 2; exact Nat.one_le_pow _ _ (by omega)
  obtain ⟨KA, hKA, dA⟩ : ∃ K, K = _ ∧ Det P E4 _ _ K := ⟨_, rfl, Det.mk3 f0 f4 fx⟩
  refine FunAll.intro hf (EvalAll.letE d1 fun v1 c1 h1' => ?_)
  obtain ⟨rfl, hc1⟩ := h1'
  refine EvalAll.letE dx fun v2 c2 h2' => ?_
  obtain ⟨rfl, hc2⟩ := h2'
  refine EvalAll.letE dO fun v3 c3 h3' => ?_
  obtain ⟨rfl, hc3⟩ := h3'
  refine EvalAll.letE dM fun v4 c4 h4' => ?_
  obtain ⟨rfl, hc4⟩ := h4'
  refine EvalAll.letE (EvalAll.call_funAll dA (Q := fun w c => ∃ ns2 : List (Perm (Fin I.n)),
      w = encGroup ns2 ∧ ns2.length ≤ I.n ^ 2 ∧ gens ns2 = vsPNcl (gens s.hs) [x2] ∧
      c ≤ KA + vsPGrowCost hn N W + w.wt + 1) fun v ca hv => ?_) fun v5 c5 h5' => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (vsPGrow_spec hn L.L3.L4.hgrow L.L3.L4.hap L.L3.L4.hmkg L.L3.L4.hncp H hs.hsl
      (as := []) (by simp) hxl1).mono ?_
    rintro w cb ⟨ns2, rfl, hl2, he2, hcb⟩
    have hcb' : cb ≤ vsPGrowCost hn N W := hcb
    refine ⟨ns2, rfl, hl2, ?_, by omega⟩
    rw [he2]; simp [vsPNcl]
  obtain ⟨ns2, rfl, hl2, hg2, hc5⟩ := h5'
  obtain ⟨h2, hle2⟩ := vsP_N2_of hH hN0 hN0n hN0C hN0c hx2N0 hx2rS hg2
  have hx2in : x2 ∈ gens ns2 := by rw [hg2]; exact vsPNcl_mem (by simp)
  have hx2Y : x2 ∈ vsPYs hs (vsPBar hs (gens ns2)) :=
    vsPYs_iff.2 ⟨hx2g, vsPRho_mem_vsPBar hs hx2in hx2g⟩
  have hns2I : ∀ h ∈ ns2, h ∈ gens I.gs := fun h hh => hs.prob.le (h2.hgs h hh)
  set E5 := [Val.list vs, Val.nat k, encPerm xg, OV, encGroup ([] : List (Perm (Fin I.n))), encGroup ns2]
  have g0 : Det P E5 (arg 0) C _ :=
    Det.arg' (P := P) (vs := vs) (rest := [.nat k, encPerm xg, OV, encGroup [], encGroup ns2]) (j := 0) rfl
  have dT := Det.call (Det.mk2 g0 (Det.var' (P := P) (env := E5) (i := 5) rfl))
    (vsPAb_spec L.L3.L4.hab L.L3.L4.hfo L.L3.L4.hno L.L3.L4.hfi L.L3.L4.hnc L.L3.L4.d.L.hcomp
      L.L3.L4.d.L.hloc L.L3.L4.d.L.hwl L.L3.L4.d.L.heq hphi H hns2I hl2)
  -- weights
  have wC : C.wt ≤ W := H.cw
  have hn6 : (I.n + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left hS.n 6
  have p6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hn2' : (I.n + 1) ^ 2 ≤ S ^ 6 := (Nat.pow_le_pow_left hS.n 2).trans (hS.pow_le (by omega))
  have wWS : W = 10 ^ 9 * S ^ 6 := rfl
  have wG0 : G0.wt ≤ 320 * (I.n + 1) ^ 6 := wt_encGroup_le_sq hl0
  have wG2 : (encGroup ns2).wt ≤ 320 * (I.n + 1) ^ 6 := wt_encGroup_le_sq hl2
  have wE0 : (encGroup ([] : List (Perm (Fin I.n)))).wt ≤ 320 * (I.n + 1) ^ 6 :=
    wt_encGroup_le_sq (by simp)
  have wvs := wt_list3_le C A G0
  have evs : (Val.list vs).wt = (Val.list [C, A, G0]).wt := rfl
  have wLV : (Val.list LV).wt < G0.wt := wt_le_wt_list (by simp [G0, encGroup, encPerms, LV, L0])
  have wLVn : (Val.list [Val.nat I.n, Val.list LV]).wt = G0.wt := rfl
  have wCL := wt_list2_le C (Val.list LV)
  have wk := wt_nat_le k
  have hkS : k ≤ 4 * S ^ 6 := by
    have h1 : LV.length ≤ 4 * S ^ 2 := hLVl
    have h2 := hS.pow_le (show 2 ≤ 6 by omega)
    have h3 : LV.length = L0.length := List.length_map _
    omega
  have wxg := wt_encPerm_le xg
  have wx2 := wt_encPerm_le x2
  have wr := wt_nat_le r
  have hrS : r ≤ S ^ 6 := by
    have : S ≤ S ^ 6 := by simpa using hS.pow_le (show 1 ≤ 6 by omega)
    have := hS.n; omega
  have wOV := wt_list2_le (encPerm x2) (Val.nat r)
  have eOV : OV.wt = (Val.list [encPerm x2, Val.nat r]).wt := rfl
  have wCx := wt_list2_le C (encPerm xg)
  have wnn := wt_nat_le I.n
  have hnS6 : I.n ≤ S ^ 6 := by
    have : S ≤ S ^ 6 := by simpa using hS.pow_le (show 1 ≤ 6 by omega)
    have := hS.n; omega
  have wnl := wt_list2_le (Val.nat I.n) (Val.list [])
  have wCE := wt_list2_le C (encGroup ([] : List (Perm (Fin I.n))))
  have w1x := wt_list1_le (encPerm x2)
  have e1x : Val.list ([x2].map encPerm) = Val.list [encPerm x2] := rfl
  have wCE2 := wt_list3_le C (encGroup ([] : List (Perm (Fin I.n)))) (Val.list [encPerm x2])
  have wCG2 := wt_list2_le C (encGroup ns2)
  have hNS : N + 1 ≤ 5 * S ^ 6 := by
    have : S ^ 2 ≤ S ^ 6 := hS.pow_le (by omega)
    show 4 * S ^ 2 + 1 ≤ 5 * S ^ 6; omega
  have hmk : mkGroupK * ((([] : List (Perm (Fin I.n))).length + 2) * (I.n + 1)) ^ 3 ≤
      mkGroupK * (2 * (N + 1)) ^ 3 := by
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 3)
    simp only [List.length_nil, zero_add]; omega
  set Y := (N + 1) * (W + 100 * (N + 1) ^ 3)
  have hY1 : W + 100 * (N + 1) ^ 3 ≤ Y := Nat.le_mul_of_pos_left _ (by omega)
  have hLoop : loopModK * (LV.length + 1) * ((Val.list [C, .list LV]).wt + 2 * LV.length + 3) ≤
      1000 * (4 * Y) := by
    have hA : (Val.list [C, .list LV]).wt + 2 * LV.length + 3 ≤ 4 * (W + 100 * (N + 1) ^ 3) := by
      omega
    have e1 : (N + 1) * (4 * (W + 100 * (N + 1) ^ 3)) = 4 * Y := by simp only [Y]; ring
    calc loopModK * (LV.length + 1) * ((Val.list [C, .list LV]).wt + 2 * LV.length + 3)
        ≤ loopModK * (N + 1) * (4 * (W + 100 * (N + 1) ^ 3)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hA
      _ = 1000 * (4 * Y) := by rw [mul_assoc, e1]; rfl
  have hFind : LV.length * (vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2) ≤
      (N + 1) * (vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have eY : 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3) = 10 ^ 4 * Y := by rw [mul_assoc]
  have lGrow : vsPGrowCost hn N W = vsPGrowCost hn (vsPN S) (vsPW6 S) := rfl
  have lOrd : vsPOrdCost Cφ (vsPN S) W = vsPOrdCost Cφ N W := rfl
  have wnil : (Val.list ([] : List Val)).wt ≤ 10 := by decide
  have lc1 : (N + 1) * (vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2) =
    (vsPN S + 1) * (vsPInLPCost Cφ (vsPN S) (vsPW6 S) + 20 * vsPW6 S + 100 + 100 * (vsPN S + 1) ^ 2) := rfl
  have lc2 : vsPOrdCost Cφ N W = vsPOrdCost Cφ (vsPN S) (vsPW6 S) := rfl
  have lc3 : mkGroupK * (2 * (N + 1)) ^ 3 = mkGroupK * (2 * (vsPN S + 1)) ^ 3 := rfl
  have lc4 : vsPAbCost Cφ (vsPN S) W = vsPAbCost Cφ (vsPN S) (vsPW6 S) := rfl
  have lc5 : (Val.list [Val.nat I.n, Val.list (List.map encPerm (1 :: ns2))]).wt = (encGroup ns2).wt := rfl
  have wCvs : C.wt < (Val.list vs).wt := wt_le_wt_list (List.mem_cons_self (a := C) (l := vs.tail))
  have wAvs : A.wt < (Val.list vs).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self (a := A) (l := vs.tail.tail)))
  have wGvs : G0.wt < (Val.list vs).wt := wt_le_wt_list (by simp [vs])
  have hpre : c1 + c2 + c3 + c4 + c5 ≤
      (N + 1) * (vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2) + 4000 * Y +
      vsPOrdCost Cφ N W + mkGroupK * (2 * (N + 1)) ^ 3 + vsPGrowCost hn N W +
      100 * (Val.list vs).wt + 10 ^ 4 * S ^ 6 := by
    rw [e1x] at hKA
    omega
  refine EvalAll.ite dT (fun vc cc h => ⟨_, h.1⟩) fun xb cc hcc => ?_
  obtain ⟨hxb', hcc⟩ := hcc
  have g1 : Det P E5 (arg 1) A _ :=
    Det.arg' (P := P) (vs := vs) (rest := [.nat k, encPerm xg, OV, encGroup [], encGroup ns2]) (j := 1) rfl
  by_cases hab : ∀ g ∈ 1 :: ns2, ∀ h ∈ 1 :: ns2,
      vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)
  · -- abelian: grow with `ns₂`
    have hx : xb = 1 := by
      have e : boolVal (decide (∀ g ∈ 1 :: ns2, ∀ h ∈ 1 :: ns2,
        vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g))) = .nat 1 := by
        rw [decide_eq_true hab]; rfl
      rw [e] at hxb'; injection hxb'
    subst hx
    rw [if_neg one_ne_zero]
    have gas := Det.get' g1 (Det.nat 1) (show [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ccs,
      Val.list (tcs.map encPerm)][1]? = some (encGroup as) from rfl)
    have g5 : Det P E5 (.get (.var 5) (.nat 1)) (.list (encPerm 1 :: ns2.map encPerm)) _ :=
      Det.get' (Det.var' (P := P) (env := E5) (i := 5) rfl) (Det.nat 1) rfl
    have gt := Det.call g5 (GI.Lang.tail_spec L.L3.htl (encPerm (1 : Perm (Fin I.n))) (ns2.map encPerm))
    obtain ⟨KB, hKB, dB⟩ : ∃ K, K = _ ∧ Det P E5 _ _ K := ⟨_, rfl, Det.mk3 g0 gas gt⟩
    have hgs2 : gens ns2 ≤ gens s.hs := (Subgroup.closure_le _).2 fun g hg => h2.hgs g hg
    have hyH : gens [x2] ≤ gens s.hs := (Subgroup.closure_le _).2 fun y hy => by
      simp at hy; rw [hy]; exact hx2g
    have hn2' : VsPNormd (gens s.hs) (gens ns2) := by rw [hg2]; exact vsPNcl_normd hyH
    have hout2 : ¬ gens ns2 ≤ vsPSp hs as := fun h' =>
      hx2S ((vsPSp_iff hs as hx2g).1 (h' hx2in))
    refine (EvalAll.mk2_last (Det.nat (P := P) (env := E5) 0)
      (EvalAll.call_funAll dB (Q := fun w cb => ∃ as' : List (Perm (Fin I.n)),
        w = encGroup as' ∧ VsPGrowOut hs as as' ∧ cb ≤ KB + vsPGrowCost hn N W + w.wt + 1)
        fun v ca hv => ?_)).mono ?_
    · obtain ⟨rfl, hca⟩ := hv
      refine (vsPGrow_spec hn L.L3.L4.hgrow L.L3.L4.hap L.L3.L4.hmkg L.L3.L4.hncp H hs.hsl hH.hal
        hl2).mono ?_
      rintro w cb ⟨as', rfl, hl, he, hcb⟩
      have hcb' : cb ≤ vsPGrowCost hn N W := hcb
      exact ⟨as', rfl, hH.grow_abel hgs2 hn2' h2.hNC hab hout2 hl he, by omega⟩
    · rintro w cw ⟨vb, cb, ⟨as', rfl, hout, hcb⟩, rfl, hcw⟩
      refine ⟨Or.inl ⟨as', rfl, hout⟩, ?_⟩
      have wa' : (encGroup as').wt ≤ 320 * (I.n + 1) ^ 6 := wt_encGroup_le_sq hout.len
      have w02 := wt_list2_le (Val.nat 0) (encGroup as')
      have w0 := wt_nat_le 0
      have wl2 : (Val.list (encPerm (1 : Perm (Fin I.n)) :: ns2.map encPerm)).wt < (encGroup ns2).wt :=
        wt_le_wt_list (by simp [encGroup, encPerms])
      have hTl : loopModK * ((ns2.map encPerm).length + 1) *
          (3 * (Val.list (encPerm (1 : Perm (Fin I.n)) :: ns2.map encPerm)).wt + 1) ≤ 1000 * (4 * Y) := by
        have hA : 3 * (Val.list (encPerm (1 : Perm (Fin I.n)) :: ns2.map encPerm)).wt + 1 ≤
            4 * (W + 100 * (N + 1) ^ 3) := by omega
        have e1 : (N + 1) * (4 * (W + 100 * (N + 1) ^ 3)) = 4 * Y := by simp only [Y]; ring
        have hl2N : (ns2.map encPerm).length ≤ N := by
          rw [List.length_map]
          have : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by have := hS.n; omega) 2
          show ns2.length ≤ 4 * S ^ 2; omega
        calc loopModK * ((ns2.map encPerm).length + 1) *
              (3 * (Val.list (encPerm (1 : Perm (Fin I.n)) :: ns2.map encPerm)).wt + 1)
            ≤ loopModK * (N + 1) * (4 * (W + 100 * (N + 1) ^ 3)) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hA
          _ = 1000 * (4 * Y) := by rw [mul_assoc, e1]; rfl
      have was : (encGroup as).wt < A.wt := wt_le_wt_list (by simp [A, vsPIn])
      have wn2l : (Val.list (ns2.map encPerm)).wt ≤ 13 * (I.n + 1) ^ 6 := wt_list_encPerms_le_sq hl2
      have w3b := wt_list3_le C (encGroup as) (Val.list (ns2.map encPerm))
      have lA : (Val.list [vsQLCV s, encGroup as, vsFMatsVal Lb, encGroup ccs,
        Val.list (List.map encPerm tcs)]).wt = A.wt := rfl
      have lAA : A.wt = (vsPIn s as Lb ccs tcs).wt := rfl
      have wb := wt_boolVal_le (decide (∀ g ∈ 1 :: ns2, ∀ h ∈ 1 :: ns2,
        vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)))
      unfold vsPS2Cost
      rw [eY]
      omega
  · -- not abelian: the pairing stage
    have hx : xb = 0 := by
      have e : boolVal (decide (∀ g ∈ 1 :: ns2, ∀ h ∈ 1 :: ns2,
        vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g))) = .nat 0 := by
        rw [decide_eq_false hab]; rfl
      rw [e] at hxb'; injection hxb'
    subst hx
    rw [if_pos rfl]
    have g3 := Det.var' (P := P) (env := E5) (i := 3) (v := OV) rfl
    have g5 := Det.var' (P := P) (env := E5) (i := 5) (v := encGroup ns2) rfl
    refine EvalAll.call_funAll (Det.mk4 g0 g1 g5 g3) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (vsPS3_spec L.hs3 L.L3 hphi hS hs hH hl2 hrn h2 hx2Y hx2b
      (vsPDer_le (gens ccs) j0 (hgen ▸ hx2N0)) hab).wt_lt.mono ?_
    rintro w cw ⟨⟨hout, hcw⟩, -⟩
    refine ⟨hout, ?_⟩
    have hwt := VsPOut.wt_le hS hs hout
    have w4 := wt_list4_le C A (encGroup ns2) OV
    have lAA : A.wt = (vsPIn s as Lb ccs tcs).wt := rfl
    have wb := wt_boolVal_le (decide (∀ g ∈ 1 :: ns2, ∀ h ∈ 1 :: ns2,
      vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)))
    unfold vsPS2Cost
    rw [eY]
    omega

end GI.Impl
