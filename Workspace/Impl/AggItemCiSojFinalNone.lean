import Workspace.Impl.AggItemCiSojFinalW
import Workspace.Impl.AggItemCiSojModelOut

/-! # The full finalizer when all exact rectangle answers are empty -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Every processed row retains the emptiness or physical membership of its
exact query answer. -/
theorem itcs_processed_physical_valid (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (rows : List (permitted W R × itcsProcessRow rep))
    (hv : ∀ row ∈ rows, itcsProcessValid rep M N row.1 row.2) :
    ∀ row ∈ rows, match row.2 with
      | none => (rep.state M N row.1).answer = ∅
      | some (g,_) => g.val ∈ (rep.state M N row.1).answer := by
  rintro ⟨t,r⟩ hr
  have hh := hv (t,r) hr
  cases r with
  | none => exact hh
  | some r => exact hh.1

set_option maxHeartbeats 400000 in
/-- The actual finalizer filters the projected rows and returns the exact empty
model item, with a polynomial bound on its actual encoded input weight. -/
theorem itcs_finalize_none {Pg : Program} {f rf flt ne fst gb ovs Cr : ℕ}
    (hf : Pg.funs[f]? = some (itcsFinishF rf flt fst gb ovs))
    (hflt : Pg.HasAt flt (filterFuns flt ne)) (hne : Pg.funs[ne]? = some itcsRowNE)
    (pf : Prim) (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q))
    (rows : List (permitted W R × itcsProcessRow rep))
    (hv : ∀ row ∈ rows, itcsProcessValid rep M N row.1 row.2)
    (inp : Val)
    (hr : FunDet Pg rf inp (.list (rows.map fun r => itcsProcessRowVal rep r.1 r.2)) Cr)
    (hCr : Cr ≤ itcsRowsBound pf inp.wt) (hempty : itcsNonemptyRows rep rows = []) :
    FunDet Pg f inp (itcsResV (itciOV ([] : List (LcOver L.q)))) (itcsFinalC pf inp.wt) ∧
      ItSOut e L (itcsRowsModel rep M N a₀ rows) [] [] := by
  let raw := rows.map fun r => itcsProcessRowVal rep r.1 r.2
  let WI := inp.wt
  let Crows := itcsRowsBound pf WI
  let U0 := itcsFinalU0 pf WI
  have rowsDet : FunDet Pg rf inp (.list raw) Crows := hr.mono hCr
  have wr : (Val.list raw).wt ≤ Crows := itcs_det_weight rowsDet
  have hn : rows.length ≤ Crows := by
    have hh := (length_lt_wt_list raw).le.trans wr
    simpa only [raw,List.length_map] using hh
  rcases itcs_final_envelopes pf WI with ⟨hW0,hR0,h01,hF1,h12,hP2,h23,hG3,h34,hO4⟩
  have wfi : (Val.list [.nat 0,.list raw]).wt ≤ U0 := by
    have hh := wt_list2_le (.nat 0) (.list raw)
    have hz := wt_nat_le 0
    change (Val.list [.nat 0,.list raw]).wt ≤ 10*(WI+Crows+100)
    omega
  have filterDet := itcs_processed_filter hflt hne rep rows
  rw [hempty,List.map_nil] at filterDet
  have fb := itcs_filter_bound (hn.trans hR0) wfi
  have filterB : FunDet Pg flt (.list [.nat 0,.list raw]) (.list []) (itcsFilterB U0) :=
    filterDet.mono fb
  have result := itcs_finish_empty hf inp raw rowsDet filterB
  have hW4 := hW0.trans (h01.trans (h12.trans (h23.trans h34)))
  have hR4 := hR0.trans (h01.trans (h12.trans (h23.trans h34)))
  have hF4 := hF1.trans (h12.trans (h23.trans h34))
  refine ⟨result.mono (itcs_finish_empty_bound hW4 hR4 hF4),?_⟩
  have ho := itcs_rows_out e rep M N a₀ rows (itcs_processed_physical_valid rep M N rows hv) []
    (by intro h; exact False.elim (h hempty))
  simpa only [itcsRowsOut,hempty,List.map_nil] using ho

end GI.Impl
