module

public import Workspace.Impl.AggItemCiSojRows

@[expose] public section

/-! # Collecting representatives from the nonempty projected answer rows -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {q : ℕ}

/-- The first-field map returns precisely the projected representatives. -/
theorem itcs_row_firsts {Pg : Program} {mp f : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]? = some krFstF)
    (ps : List (Perm (Fin q) × List (Perm (Fin q)))) :
    let inp := Val.list [.nat 0,.list (ps.map fun p=>itcsRowVal (some p))]
    FunDet Pg mp inp (.list (ps.map fun p=>encPerm p.1))
      (ps.length*(100*(4*inp.wt+20))+mapK*(ps.length+1)*
        (inp.wt+(Val.list (ps.map fun p=>encPerm p.1)).wt+1)) := by
  dsimp only
  let inp : Val := .list [.nat 0,.list (ps.map fun p=>itcsRowVal (some p))]
  have hh := mapList_spec hm ps (fun p=>itcsRowVal (some p)) (fun p=>encPerm p.1)
    (c:=.nat 0) (B:=100*(4*inp.wt+20))
    (fun a _ b _ h=>by
      change Val.list [encPerm a.1,GI.Cited.encGroup a.2]=.list [encPerm b.1,GI.Cited.encGroup b.2] at h
      simp only [Val.list.injEq,List.cons.injEq,and_true] at h
      exact h.1)
    (fun p hp=>by
      have wrowList : (itcsRowVal (some p)).wt ≤ (Val.list (ps.map fun p=>itcsRowVal (some p))).wt :=
        st_wt_mem (List.mem_map.2 ⟨p,hp,rfl⟩)
      have wlist : (Val.list (ps.map fun p=>itcsRowVal (some p))).wt ≤ inp.wt :=
        st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have wrow := wrowList.trans wlist
      have w0:=wt_nat_le 0
      have wa:=wt_list2_le (.nat 0) (itcsRowVal (some p))
      exact (itcs_fst_row_spec hf p).mono (by omega))
  exact hh

end GI.Impl
