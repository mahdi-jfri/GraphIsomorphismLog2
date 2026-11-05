module

public import Workspace.Impl.AggItemCiSojFrameBuild

@[expose] public section

/-! # Weights of the actual rectangle query arguments -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)
open Classical

variable {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- The cell table is retained verbatim in the paid representation value. -/
theorem itcs_frame_cells_weight (F : itcsQFrame e S L) {n : ℕ}
    (h : (rcRepVal e F.rep F.hs).wt ≤ n) :
    (encFun fun i => rcCellCode (F.rep.cell (e.symm i))).wt ≤ n :=
  (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans h

/-- Both pulled-back color tables have values in `{0,1,2}`, independently of
which canonical representative is returned by a recursive query. -/
theorem itcs_frame_colors_weight (F : itcsQFrame e S L) (t : permitted F.W F.R) :
    (encFun fun i => itcsQCode (F.rep.colors F.M (e.symm i))).wt ≤ 9*k+4 ∧
    (encFun fun i => itcsQCode (F.rep.colors (RectRep.twistMat t F.N) (e.symm i))).wt ≤ 9*k+4 := by
  constructor
  · simpa only [Nat.mul_comm] using
      wt_encFun_le (fun i => itcsQCode (F.rep.colors F.M (e.symm i))) (fun _ => itcs_qcode_le _)
  · simpa only [Nat.mul_comm] using
      wt_encFun_le (fun i => itcsQCode (F.rep.colors (RectRep.twistMat t F.N) (e.symm i)))
        (fun _ => itcs_qcode_le _)

/-- All five state-constructor arguments have a uniform bound before any
recursive answer arrives. -/
theorem itcs_frame_state_cost (F : itcsQFrame e S L) (sv : Val) {n : ℕ}
    (hs : sv.wt ≤ n) (hg : (encGroup (F.hs.map Prod.fst)).wt ≤ n)
    (hd : (encFun fun i => if e.symm i∈F.rep.Δ then 1 else 0).wt ≤ n) (hk : k ≤ n)
    (t : permitted F.W F.R) :
    itcsStateC sv (encGroup (F.hs.map Prod.fst))
      (encFun fun i => if e.symm i∈F.rep.Δ then 1 else 0)
      (encFun fun i => itcsQCode (F.rep.colors F.M (e.symm i)))
      (encFun fun i => itcsQCode (F.rep.colors (RectRep.twistMat t F.N) (e.symm i))) ≤ 10^9*(n+100) := by
  obtain ⟨hx,hy⟩ := itcs_frame_colors_weight F t
  have hh := itcs_wt_list5 sv (encGroup (F.hs.map Prod.fst))
    (encFun fun i => if e.symm i∈F.rep.Δ then 1 else 0)
    (encFun fun i => itcsQCode (F.rep.colors F.M (e.symm i)))
    (encFun fun i => itcsQCode (F.rep.colors (RectRep.twistMat t F.N) (e.symm i)))
  unfold itcsStateC
  omega

/-- Uniform weight bound for the ten actual query or ask arguments. -/
theorem itcs_list10_scalar (a b c d e f g h i j : Val) {n : ℕ}
    (ha : a.wt≤ n) (hb : b.wt≤ n) (hc : c.wt≤ n) (hd : d.wt≤ n) (he : e.wt≤ n)
    (hf : f.wt≤ n) (hg : g.wt≤ n) (hh : h.wt≤ n) (hi : i.wt≤ n) (hj : j.wt≤ n) :
    (Val.list [a,b,c,d,e,f,g,h,i,j]).wt≤10^9*(n+100) := by
  have hw := wt_list_le [a,b,c,d,e,f,g,h,i,j]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hw
  omega

/-- Every field of a physical query's ten-field argument is covered by the
parent, source tables, paid representation, and paid physical-data value. -/
theorem itcs_frame_query_input_weight (F : itcsQFrame e S L) (sv xt yt v : Val) {n : ℕ}
    (hs : sv.wt ≤ n) (hx : xt.wt ≤ n) (hy : yt.wt ≤ n) (hv : v.wt ≤ n)
    (hq : (Val.nat L.q).wt ≤ n) (hp : 4*(L.q+1)^2 ≤ n)
    (hr : (rcRepVal e F.rep F.hs).wt ≤ n)
    (hdata : (Val.list [encGroup (F.hs.map Prod.fst),
      encFun (fun i => if e.symm i∈F.rep.Δ then 1 else 0),liftLabCtx L.q k (F.hs.map Prod.swap)]).wt ≤ n)
    (t : permitted F.W F.R) :
    (Val.list [sv,encGroup (F.hs.map Prod.fst),
      encFun (fun i => if e.symm i∈F.rep.Δ then 1 else 0),xt,yt,v,.nat L.q,
      encFun (fun i => rcCellCode (F.rep.cell (e.symm i))),encPerm F.a₀.val,encPerm t.val.val]).wt ≤
        10^9*(n+100) := by
  have hg : (encGroup (F.hs.map Prod.fst)).wt ≤ n := (st_wt_mem (vs:=[encGroup (F.hs.map Prod.fst),encFun (fun i => if e.symm i∈F.rep.Δ then 1 else 0),liftLabCtx L.q k (F.hs.map Prod.swap)]) (List.mem_cons_self ..)).trans hdata
  have hd : (encFun fun i => if e.symm i∈F.rep.Δ then 1 else 0).wt ≤ n :=
    (st_wt_mem (vs:=[encGroup (F.hs.map Prod.fst),encFun (fun i => if e.symm i∈F.rep.Δ then 1 else 0),liftLabCtx L.q k (F.hs.map Prod.swap)]) (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans hdata
  have hc := itcs_frame_cells_weight F hr
  have ha : (encPerm F.a₀.val).wt ≤ n := (wt_encPerm_le _).trans hp
  have ht : (encPerm t.val.val).wt ≤ n := (wt_encPerm_le _).trans hp
  exact itcs_list10_scalar _ _ _ _ _ _ _ _ _ _ hs hg hd hx hy hv hq hc ha ht

end GI.Impl
