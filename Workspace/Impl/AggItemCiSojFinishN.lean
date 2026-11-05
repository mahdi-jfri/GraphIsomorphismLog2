module

public import Workspace.Impl.AggItemCiSojFinish

@[expose] public section

/-! # The nonempty branch of the rectangle finalizer -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

set_option maxHeartbeats 400000 in
/-- The actual finalizer composes the established row projection, filtering,
representative map, generator constructor, and overcoset map. All structural
argument and result weights are discharged from their proved callee bounds. -/
theorem itcs_finish_nonempty {Pg : Program} {f rows flt fst gb ovs Cr Cf Cp Cg Co : ℕ}
    (hf : Pg.funs[f]? = some (itcsFinishF rows flt fst gb ovs))
    (qv av fix ctx twists answers r₀ qg source reps gens ov : Val)
    (raw more : List Val)
    (hr : FunDet Pg rows (.list [.list [qv,av,fix,ctx,twists],answers]) (.list raw) Cr)
    (hflt : FunDet Pg flt (.list [.nat 0,.list raw]) (.list (.list [r₀,.list [qg,source]]::more)) Cf)
    (hp : FunDet Pg fst (.list [.nat 0,.list (.list [r₀,.list [qg,source]]::more)]) reps Cp)
    (hg : FunDet Pg gb (.list [reps,source,fix]) gens Cg)
    (ho : FunDet Pg ovs (.list [.list [av,gens],reps]) ov Co) :
    let v := Val.list [.list [qv,av,fix,ctx,twists],answers]
    FunDet Pg f v (itcsResV ov)
      (200*(100*(v.wt+Cr+Cf+Cp+Cg+Co+100)+1)+Cr+Cf+Cp+Cg+Co) := by
  dsimp only
  let payload : Val := .list [qv,av,fix,ctx,twists]
  let v : Val := .list [payload,answers]
  let filtered : Val := .list (.list [r₀,.list [qg,source]]::more)
  let Bw:=100*(v.wt+Cr+Cf+Cp+Cg+Co+100)
  have budget : 10*v.wt+10*Cr+10*Cf+10*Cp+10*Cg+10*Co+1000≤Bw := by dsimp only [Bw]; omega
  have wr:=itcs_det_weight hr
  have wf : filtered.wt≤Cf := itcs_det_weight hflt
  have wp:=itcs_det_weight hp
  have wg:=itcs_det_weight hg
  have wo:=itcs_det_weight ho
  have wpay : payload.wt≤v.wt := st_wt_mem (List.mem_cons_self ..)
  have wal : av.wt≤v.wt := (st_wt_mem (by simp : av∈[qv,av,fix,ctx,twists])).trans wpay
  have wfix : fix.wt≤v.wt := (st_wt_mem (by simp : fix∈[qv,av,fix,ctx,twists])).trans wpay
  have whead : (Val.list [r₀,.list [qg,source]]).wt≤Cf :=
    (st_wt_mem (List.mem_cons_self ..)).trans wf
  have wgroup : (Val.list [qg,source]).wt≤Cf :=
    (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans whead
  have wsource : source.wt≤Cf := (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans wgroup
  have wres : (itcsResV ov).wt≤Bw := (itcs_res_weight ov).trans (by omega)
  have wfltin : (Val.list [.nat 0,.list raw]).wt≤Bw := by
    have h:=wt_list2_le (.nat 0) (.list raw)
    have hz:=wt_nat_le 0
    omega
  have wfstin : (Val.list [.nat 0,filtered]).wt≤Bw := by
    have h:=wt_list2_le (.nat 0) filtered
    have hz:=wt_nat_le 0
    omega
  have wgbin : (Val.list [reps,source,fix]).wt≤Bw := by
    have h:=wt_list3_le reps source fix
    omega
  have wovctx:=wt_list2_le av gens
  have wovin : (Val.list [.list [av,gens],reps]).wt≤Bw := by
    have h:=wt_list2_le (.list [av,gens]) reps
    omega
  have wi : v.wt ≤ Bw := by omega
  have v0 : StDC Pg [v] (.var 0) v 1 0 Bw := StDC.var' rfl (by omega)
  have rc:=StDC.call v0 hr (wr.trans (by omega))
  have r1 : StDC Pg [v,.list raw] (.var 1) (.list raw) 1 0 Bw := StDC.var' rfl (wr.trans (by omega))
  have fc:=StDC.call (StDC.mk2 (StDC.nat 0 (by omega)) r1 wfltin (by omega)) hflt (wf.trans (by omega))
  have getPay {rest : List Val} {i : ℕ} {x : Val}
      (hi : [qv,av,fix,ctx,twists][i]?=some x) (hii:i+2≤Bw) :
      StDC Pg (v::rest) (itcsFinPayload i) x 5 0 Bw :=
    (StDC.get (StDC.arg (P:=Pg) (rest:=rest) (j:=0) rfl wi (by omega) (wpay.trans (by omega)))
      (StDC.nat i hii) hi ((st_wt_mem (List.mem_of_getElem? hi)).trans (wpay.trans (by omega)))).mono (by omega) (by omega)
  have f2 : StDC Pg [v,.list raw,filtered] (.var 2) filtered 1 0 Bw := StDC.var' rfl (wf.trans (by omega))
  have pc:=StDC.call (StDC.mk2 (StDC.nat 0 (by omega)) f2 wfstin (by omega)) hp (wp.trans (by omega))
  have f2' : StDC Pg [v,.list raw,filtered,reps] (.var 2) filtered 1 0 Bw := StDC.var' rfl (wf.trans (by omega))
  have r3 : StDC Pg [v,.list raw,filtered,reps] (.var 3) reps 1 0 Bw := StDC.var' rfl (wp.trans (by omega))
  have first:=StDC.get f2' (StDC.nat 0 (by omega)) rfl (whead.trans (by omega))
  have group:=StDC.get first (StDC.nat 1 (by omega)) rfl (wgroup.trans (by omega))
  have src:=StDC.get group (StDC.nat 1 (by omega)) rfl (wsource.trans (by omega))
  have gc:=StDC.call (StDC.mk3 r3 src (getPay (i:=2) rfl (by omega)) wgbin (by omega)) hg (wg.trans (by omega))
  have r3' : StDC Pg [v,.list raw,filtered,reps,gens] (.var 3) reps 1 0 Bw := StDC.var' rfl (wp.trans (by omega))
  have g4 : StDC Pg [v,.list raw,filtered,reps,gens] (.var 4) gens 1 0 Bw := StDC.var' rfl (wg.trans (by omega))
  have oc:=StDC.call (StDC.mk2 (StDC.mk2 (getPay (i:=1) rfl (by omega)) g4 (by omega) (by omega)) r3' wovin (by omega)) ho (wo.trans (by omega))
  have o5 : StDC Pg [v,.list raw,filtered,reps,gens,ov] (.var 5) ov 1 0 Bw := StDC.var' rfl (wo.trans (by omega))
  have res:=itcs_res_dc o5 wres (by omega)
  have nonempty:=StDC.letE pc (StDC.letE gc (StDC.letE oc res wres) wres) wres
  have hlen : more.length+1+2≤Bw := by
    have h:=length_lt_wt_list (.list [r₀,.list [qg,source]]::more)
    change more.length+1 < filtered.wt at h
    omega
  have len : StDC Pg [v,.list raw,filtered] (.length (.var 2)) (.nat (more.length+1)) 2 0 Bw :=
    StDC.length f2 hlen
  have tail:=StDC.ite (e:=itcsResE .nil) (nt:=100) (ne:=11) (Et:=Cp+Cg+Co) (Ee:=0) len
    (fun _=>nonempty.mono (by omega) (by omega)) (fun h=>by omega) wres
  have body:=StDC.letE rc (StDC.letE fc tail wres) wres
  clear budget wr wf wp wg wo wpay wal wfix whead wgroup wsource wres wfltin wfstin wgbin wovctx wovin v0 rc r1 fc getPay f2 pc f2' r3 first group src gc r3' g4 oc o5 res nonempty hlen len tail
  exact StDC.funDet hf body (by dsimp only [Bw,v,payload] at *; omega)

end GI.Impl
