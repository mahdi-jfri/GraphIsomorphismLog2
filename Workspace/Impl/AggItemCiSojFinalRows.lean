module

public import Workspace.Impl.AggItemCiSojFinalNone

@[expose] public section

/-! # Reading the surviving typed rows with the actual list programs -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)

/-- Taking the first field of every encoded row has bounded output weight. -/
theorem itcs_first_output_weight {q n : ℕ} (ps : List (Perm (Fin q) × List (Perm (Fin q))))
    (hl : ps.length≤ n) (hw : (Val.list (ps.map fun p => itcsRowVal (some p))).wt≤ n) :
    (Val.list (ps.map fun p => encPerm p.1)).wt≤ n*(2*n+1)+4 := by
  have he (p : Perm (Fin q) × List (Perm (Fin q))) (hp : p∈ps) : (encPerm p.1).wt≤ n :=
    (st_wt_mem (List.mem_cons_self ..)).trans
      ((st_wt_mem (List.mem_map.2 ⟨p,hp,rfl⟩)).trans hw)
  exact (wt_list_map_le ps (fun p => encPerm p.1) he).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 4)

/-- The permutation-list field of the first encoded group records its complete
leading-identity generator list. -/
theorem itcs_first_group_length {q : ℕ} (r : Perm (Fin q)) (sg : List (Perm (Fin q))) (more : List Val) :
    (1::sg).length≤(Val.list (.list [encPerm r,encGroup sg]::more)).wt := by
  have hl := (length_lt_wt_list ((1::sg).map encPerm)).le
  simp only [List.length_map] at hl
  have hg : (Val.list ((1::sg).map encPerm)).wt≤(encGroup sg).wt :=
    st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hr : (encGroup sg).wt≤(Val.list [encPerm r,encGroup sg]).wt :=
    st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact hl.trans (hg.trans (hr.trans (st_wt_mem (List.mem_cons_self ..))))

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- The same leading identity is present after coercing the typed source list. -/
theorem itcs_source_code_typed (sg : List (permitted W R)) :
    encGroup (sg.map fun g => g.val.val) =
      .list [.nat L.q,.list (((1::sg).map fun g => g.val.val).map encPerm)] := rfl

/-- The first-field map on typed surviving rows, with all row and output-weight
premises discharged from the actual input. -/
theorem itcs_typed_firsts {Pg : Program} {mp f n : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]? = some krFstF)
    (ps : List (permitted W R × List (permitted W R)))
    (hn : ps.length≤ n)
    (hi : (Val.list [.nat 0,.list (ps.map fun p =>
      .list [encPerm p.1.val.val,encGroup (p.2.map fun g => g.val.val)])]).wt≤ n) :
    FunDet Pg mp (.list [.nat 0,.list (ps.map fun p =>
      .list [encPerm p.1.val.val,encGroup (p.2.map fun g => g.val.val)])])
      (.list (ps.map fun p => encPerm p.1.val.val)) (itcsFirstB n) := by
  let raw := ps.map fun p => (p.1.val.val,p.2.map fun g => g.val.val)
  have hir : (Val.list [.nat 0,.list (raw.map fun p => itcsRowVal (some p))]).wt ≤ n := by
    simpa only [raw,List.map_map,Function.comp_def,itcsRowVal] using hi
  have hw : (Val.list (raw.map fun p => itcsRowVal (some p))).wt ≤ n :=
    (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans hir
  have hl : raw.length≤ n := by simpa only [raw,List.length_map] using hn
  have ho := itcs_first_output_weight raw hl hw
  have hp := itcs_row_firsts hm hf raw
  have hb := itcs_first_bound hl hir ho
  simpa only [raw,List.map_map,Function.comp_def,itcsRowVal,List.length_map] using hp.mono hb

end GI.Impl
