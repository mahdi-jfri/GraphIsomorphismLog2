import Workspace.Impl.AggItemCiSojFinalRows

/-! # Paid-for intermediate data of the nonempty rectangle finalizer -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Filtering the actual projected rows meets its exact typed encoding and
local polynomial cost, and bounds the number of surviving occurrences. -/
theorem itcs_final_filter_stage {Pg : Program} {rf flt ne Cr : ℕ}
    (hflt : Pg.HasAt flt (filterFuns flt ne)) (hne : Pg.funs[ne]? = some itcsRowNE)
    (pf : Prim) (rep : RectRep P₀ S L W R)
    (rows : List (permitted W R × itcsProcessRow rep)) (inp : Val)
    (hr : FunDet Pg rf inp (.list (rows.map fun r => itcsProcessRowVal rep r.1 r.2)) Cr)
    (hCr : Cr≤ itcsRowsBound pf inp.wt) :
    FunDet Pg flt (.list [.nat 0,.list (rows.map fun r => itcsProcessRowVal rep r.1 r.2)])
      (.list ((itcsNonemptyRows rep rows).map fun r =>
        .list [encPerm r.1.val.val,encGroup (r.2.map fun g => g.val.val)]))
      (itcsFilterB (itcsFinalU0 pf inp.wt)) ∧
      (itcsNonemptyRows rep rows).length≤ itcsFinalU0 pf inp.wt := by
  let raw := rows.map fun r => itcsProcessRowVal rep r.1 r.2
  have wr : (Val.list raw).wt ≤ itcsRowsBound pf inp.wt := (itcs_det_weight hr).trans hCr
  have hn : rows.length≤ itcsRowsBound pf inp.wt := by
    have hh := (length_lt_wt_list raw).le.trans wr
    simpa only [raw,List.length_map] using hh
  have hR0 := (itcs_final_envelopes pf inp.wt).2.1
  have wfi : (Val.list [.nat 0,.list raw]).wt≤ itcsFinalU0 pf inp.wt := by
    have hh := wt_list2_le (.nat 0) (.list raw)
    have hz := wt_nat_le 0
    change (Val.list [.nat 0,.list raw]).wt≤10*(inp.wt+itcsRowsBound pf inp.wt+100)
    omega
  exact ⟨(itcs_processed_filter hflt hne rep rows).mono (itcs_filter_bound (hn.trans hR0) wfi),
    (itcs_nonempty_length_le rep rows).trans (hn.trans hR0)⟩

/-- The complete first-field map is paid for by the next local stage. -/
theorem itcs_final_firsts_stage {Pg : Program} {mp f : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]? = some krFstF)
    (pf : Prim) (IW : ℕ) (ps : List (permitted W R × List (permitted W R)))
    (hn : ps.length≤ itcsFinalU0 pf IW)
    (hw : (Val.list (ps.map fun p =>
      .list [encPerm p.1.val.val,encGroup (p.2.map fun g => g.val.val)])).wt≤ itcsFilterB (itcsFinalU0 pf IW)) :
    FunDet Pg mp (.list [.nat 0,.list (ps.map fun p =>
      .list [encPerm p.1.val.val,encGroup (p.2.map fun g => g.val.val)])])
      (.list (ps.map fun p => encPerm p.1.val.val)) (itcsFirstB (itcsFinalU1 pf IW)) := by
  have hp := itcs_pad_bounds (itcsFinalU0 pf IW) (itcsFilterB (itcsFinalU0 pf IW))
  have hi : (Val.list [.nat 0,.list (ps.map fun p =>
      .list [encPerm p.1.val.val,encGroup (p.2.map fun g => g.val.val)])]).wt≤ itcsFinalU1 pf IW := by
    have hh := wt_list2_le (.nat 0) (.list (ps.map fun p =>
      .list [encPerm p.1.val.val,encGroup (p.2.map fun g => g.val.val)]))
    have hz := wt_nat_le 0
    unfold itcsFinalU1
    omega
  exact itcs_typed_firsts hm hf ps (hn.trans hp.1) hi

/-- The first typed source list, including its leading identity, is bounded by
the encoded surviving list that the filter actually returned. -/
theorem itcs_typed_source_length (ps : List (permitted W R × List (permitted W R)))
    (p₀ : permitted W R) (sg₀ : List (permitted W R)) (tail : List (permitted W R × List (permitted W R)))
    (he : ps=(p₀,sg₀)::tail) :
    (1::sg₀).length≤(Val.list (ps.map fun p =>
      .list [encPerm p.1.val.val,encGroup (p.2.map fun g => g.val.val)])).wt := by
  rw [he]
  have hh := itcs_first_group_length p₀.val.val (sg₀.map fun g => g.val.val)
    (tail.map fun p => .list [encPerm p.1.val.val,encGroup (p.2.map fun g => g.val.val)])
  simpa only [List.map_cons,List.length_cons,List.length_map] using hh

/-- Four paid-for list sizes bound the group constructor's scalar parameter. -/
theorem itcs_group_size_bound {q r s fs n : ℕ} (hq : q≤ n) (hr : r≤ n) (hs : s≤ n) (hf : fs≤ n) :
    q+r+s+fs+2≤10*n+10 := by omega

/-- The overcoset mapper's nested argument fits the next paid-for stage. -/
theorem itcs_over_input_pad (a b c : Val) {n Cg : ℕ}
    (ha : a.wt≤ n) (hb : b.wt≤ Cg) (hc : c.wt≤ n) :
    (Val.list [.list [a,b],c]).wt≤10*(n+Cg+100) := by
  have h1 := wt_list2_le a b
  have h2 := wt_list2_le (.list [a,b]) c
  omega

end GI.Impl
