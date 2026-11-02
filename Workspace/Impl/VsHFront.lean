import Workspace.Impl.VsHQ

/-!
# The front of the hard case

On the hand-off value `vsPGIn s as Lb ccs tcs ys r`, the program `vsHFrontE` builds the context,
the numbers `Q` and `dv`, the basis `B` of `Ȳ/S` (`vsHB`), its words `E` (`vsHE`), and the
isotropic family `K` (`vsHK`). It returns `[[ctx, r, Q, dv], B, K]` (`vsHFront_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The front, on the hand-off value. -/
def vsHFrontE (ctx c2 bas en iso : ℕ) : Expr :=
  .letE (.call ctx (.var 0))
  (.letE (.call c2 (mk2 (.var 1) (arg 9)))
  (.letE (.call bas (mk2 (mk2 (.var 1) (arg 9)) (arg 8)))
  (.letE (.call en (mk3 (arg 9) (.get (.var 1) (.nat 6)) (.var 3)))
  (.letE (.call iso (mk2 (.var 2) (.var 4)))
    (mk3 (.var 2) (.var 3) (.var 5))))))

/-- The indices of the front. -/
structure VsHFX where
  (i : VsHIX) (ctx flm fit fl rws rep c2 itq stq bas fob stb iso foi sti : ℕ)

/-- The layout of the front. -/
structure VsHFLay (P : Program) (x : VsHFX) : Prop where
  i : VsHILay P x.i
  hctx : P.funs[x.ctx]? = some (vsHCtxE x.flm x.rws x.rep)
  hflm : P.HasAt x.flm (mapFuns x.flm x.fit)
  hfit : P.funs[x.fit]? = some (vsPFlItemE x.fl)
  hfl : P.HasAt x.fl (vsWFlatFuns x.fl)
  hrws : P.HasAt x.rws (vsWRowsFuns x.rws)
  hrep : P.HasAt x.rep (replicateFuns x.rep)
  hc2 : P.funs[x.c2]? = some (vsHC2E x.itq)
  hitq : P.HasAt x.itq (iterFuns x.itq x.stq)
  hstq : P.funs[x.stq]? = some vsHMulE
  hbas : P.funs[x.bas]? = some (vsHBasE x.fob)
  hfob : P.HasAt x.fob (foldlFuns x.fob x.stb)
  hstb : P.funs[x.stb]? = some (vsHBStepE x.i.m.mem)
  hiso : P.funs[x.iso]? = some (vsHIsoE x.foi)
  hfoi : P.HasAt x.foi (foldlFuns x.foi x.sti)
  hsti : P.funs[x.sti]? = some (vsHIStepE x.i.good x.i.no x.i.m.mem)

/-- The cost of the front. -/
def vsHFrontCost (Cφ N W : ℕ) : ℕ :=
  vsPCtxPCost N W + vsHC2Cost N W + vsHBasCost Cφ N W + vsPEnumCost N + vsHIsoCost Cφ N W +
    10 ^ 3 * W + 10 ^ 4 * (N + 1) ^ 3

section

variable {s : VsQSt I} [Fact I.p.Prime] {hs : VsQStOK s} {as : List (Perm (Fin I.n))}
  {Lb : List (List (List ℕ))} {ys : List (Perm (Fin I.n))} {r : ℕ}

set_option maxHeartbeats 8000000 in
/-- **The front of the hard case.** -/
theorem vsHFront_spec {P : Program} {f : ℕ} {x : VsHFX}
    (hf : P.funs[f]? = some (vsHFrontE x.ctx x.c2 x.bas x.i.m.e.en x.iso)) (L : VsHFLay P x)
    {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.i.m.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (h : VsHHyp hs as Lb ys r) {ccs tcs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs)
    (hA : (vsPGIn s as Lb ccs tcs ys r).wt ≤ W) (hD : vsQD s ^ 2 + 1 ≤ N)
    (hyl : ys.length + 1 ≤ N) (hr : r ≤ N) (hLbl : Lb.length ≤ N) :
    FunDet P f (vsPGIn s as Lb ccs tcs ys r)
      (.list [vsHGc (vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs) r
          (I.p ^ (vsPRows I.p Lb).length - 1) (decide (r ∣ I.p ^ (vsPRows I.p Lb).length - 1)),
        .list ((vsHB s Lb r ys).map encPerm), .list ((vsHK s Lb r ys).map encPerm)])
      (vsHFrontCost Cφ N W) := by
  set A := vsPGIn s as Lb ccs tcs ys r
  set C := vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs
  set rows := vsPRows I.p Lb
  set Q := I.p ^ rows.length - 1
  set dv := decide (r ∣ Q)
  set B := vsHB s Lb r ys
  set E := vsHE s Lb r ys
  set K := vsHK s Lb r ys
  have hr1 : 1 ≤ r := h.hard.2.2.2.1.one_lt.le
  have hDD : vsQD s * vsQD s ≤ N := by nlinarith
  have hLbW : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M := fun M hM =>
    ⟨fun a ha => (h.hLb M hM).rows a ha, (h.hLb M hM).len⟩
  have hgI : ∀ g ∈ gens s.hs, g ∈ gens I.gs := fun g hg => hs.prob.le hg
  -- the context
  have dC := Det.call (Det.var' (P := P) (env := [A]) (i := 0) rfl)
    (vsHCtx_spec L.hctx L.hflm L.hfit L.hfl L.hrws L.hrep H.sz.pN hDD hLbW hLbl hA)
  -- `Q` and `dv`
  have hQ : GI.Machine.len Q ≤ (N + 1) ^ 2 :=
    (GI.Machine.len_sub_le _ _).trans (vsH_len_pow H.sz.pN H.rl)
  set E1 := [A, C]
  have a9 : ∀ rest : List Val, Det P (A :: rest) (arg 9) (.nat r) (2 * A.wt + 9 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
      vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs, Val.list (tcs.map encPerm),
      Val.list (ys.map encPerm), .nat r, vsFMatsVal Lb]) (rest := rest) (j := 9) rfl
  have a8 : ∀ rest : List Val, Det P (A :: rest) (arg 8) (.list (ys.map encPerm)) (2 * A.wt + 8 + 5) :=
    fun rest => Det.arg' (P := P) (vs := [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
      vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs, Val.list (tcs.map encPerm),
      Val.list (ys.map encPerm), .nat r, vsFMatsVal Lb]) (rest := rest) (j := 8) rfl
  have dQ := Det.call (Det.mk2 (Det.var' (P := P) (env := E1) (i := 1) rfl) (a9 [C]))
    (vsHC2_spec L.hc2 L.hitq L.hstq H hr)
  -- the basis
  set c2 := vsHGc C r Q dv
  set E2 := [A, C, c2]
  have hbB := h.bas
  have dB := Det.call (Det.mk2 (Det.mk2 (Det.var' (P := P) (env := E2) (i := 1) rfl) (a9 [C, c2]))
    (a8 [C, c2]))
    (vsHBas_prog L.hbas L.hfob L.hstb L.i.m hphi H hr1 hr hyl (fun g hg => hgI g (h.hys g hg))
      (fun i hi => (hbB.2.2.2 i hi).trans (by nlinarith)))
  -- the words
  set E3 := [A, C, c2, Val.list (B.map encPerm)]
  have dn : Det P E3 (.get (.var 1) (.nat 6)) (.nat I.n) _ :=
    Det.get' (Det.var' (P := P) (env := E3) (i := 1) rfl) (Det.nat 6) rfl
  have hBl : B.length ≤ N := by
    have := (vsHGreedy_sublist (vsHBT I s.ws' (vsQCs s) rows r) ys).length_le
    have e : B = vsHGreedy (vsHBT I s.ws' (vsQCs s) rows r) ys := rfl
    rw [e]; omega
  have hBr : r ^ B.length ≤ N := by
    have : r ^ B.length ≤ vsQD s ^ 2 := hbB.2.2.1
    omega
  have dE := Det.call (Det.mk3 (a9 [C, c2, Val.list (B.map encPerm)]) dn
    (Det.var' (P := P) (env := E3) (i := 3) rfl))
    (vsPEnum_spec L.i.m.e.hf L.i.m.e.hfo L.i.m.e.hst L.i.m.e.hmpM L.i.m.e.hmid L.i.m.e.hmp
      L.i.m.e.hit L.i.m.e.hpow L.i.m.e.hcomp L.i.m.e.hcat L.i.m.e.hrng H.n hr1 hr hBr hBl)
  -- the isotropic family
  set E4 := [A, C, c2, Val.list (B.map encPerm), Val.list (E.map encPerm)]
  have hEl : E.length + 1 ≤ N := by
    have : E.length ≤ vsQD s ^ 2 := h.E_length
    omega
  have dK := Det.call (Det.mk2 (Det.var' (P := P) (env := E4) (i := 2) rfl)
    (Det.var' (P := P) (env := E4) (i := 4) rfl))
    (vsHIso_prog L.hiso L.hfoi L.hsti L.i hphi H hr1 hr hQ dv hEl
      (fun g hg => hgI g (h.inE g hg).1)
      (fun i _ => (h.iso_bound (E.take i) fun y hy => h.inE y (List.mem_of_mem_take hy)).trans
        (by nlinarith)))
  set E5 := [A, C, c2, Val.list (B.map encPerm), Val.list (E.map encPerm), Val.list (K.map encPerm)]
  have dO := Det.mk3 (Det.var' (P := P) (env := E5) (i := 2) rfl)
    (Det.var' (P := P) (env := E5) (i := 3) rfl) (Det.var' (P := P) (env := E5) (i := 5) rfl)
  refine FunDet.intro hf ((Det.letE dC (Det.letE dQ (Det.letE dB (Det.letE dE (Det.letE dK dO))))).mono ?_)
  have hn := H.n
  have wC : C.wt ≤ W := H.cw
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have wr := wt_nat_le r
  have wn := wt_nat_le I.n
  have wQ : (Val.nat Q).wt ≤ (N + 1) ^ 2 + 2 := by rw [wt_nat']; omega
  have wdv := wt_boolVal_le dv
  have w4 := wt_list_le [C, Val.nat r, Val.nat Q, boolVal dv]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w4
  have ec2 : c2.wt = (Val.list [C, Val.nat r, Val.nat Q, boolVal dv]).wt := rfl
  have wB := vsP_wt_perms H.n B (by omega)
  have wE := vsP_wt_perms H.n E (by omega)
  have hKl : K.length ≤ E.length := (vsHGreedy_sublist _ _).length_le
  have wK := vsP_wt_perms H.n K (by omega)
  have l1 := wt_list2_le C (.nat r)
  have l2 := wt_list2_le (Val.list [C, .nat r]) (.list (ys.map encPerm))
  have wys := vsP_wt_perms H.n ys (by omega)
  have l3 := wt_list3_le (.nat r) (.nat I.n) (.list (B.map encPerm))
  have l4 := wt_list2_le c2 (.list (E.map encPerm))
  have l5 := wt_list3_le c2 (.list (B.map encPerm)) (.list (K.map encPerm))
  have l6 := wt_list2_le C (.nat r)
  have hm6 : (Val.nat I.n).wt < C.wt := wt_le_wt_list (by simp)
  have r1 : (vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs).wt = C.wt := rfl
  have r2 : (Val.list ((vsHGreedy (vsHBT I s.ws' (vsQCs s) rows r) ys).map encPerm)).wt =
      (Val.list (B.map encPerm)).wt := rfl
  have r3 : (Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), Val.nat I.p,
      Val.list (List.map VsRow.val (vsPRows I.p Lb)),
      natList (vsWZ ((vsQCs s).length * (vsQCs s).length)), encGroup s.hs, Val.nat I.n]).wt =
      C.wt := rfl
  have r4 : (Val.list ((vsPEnum r B).map encPerm)).wt = (Val.list (E.map encPerm)).wt := rfl
  have r5 : (Val.list ((vsHGreedy (vsHIT I s.ws' (vsQCs s) rows r Q dv) E).map encPerm)).wt =
      (Val.list (K.map encPerm)).wt := rfl
  unfold vsHFrontCost
  omega

end

end GI.Impl
