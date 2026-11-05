module

public import Workspace.Impl.AggItemCiSojPR
public import Workspace.Impl.AggKerRed
public import Workspace.Lang.Lib.SmallGroup

@[expose] public section

/-!
# Keeping the nonempty projected answers

Rows retain their projected representative and full source generators. Filter
only the empty rows, preserving query order, then collect their representatives.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)

variable {q : ℕ}

/-- One complete projected answer, with the empty answer represented by `[]`. -/
def itcsRowVal : Option (Perm (Fin q) × List (Perm (Fin q))) → Val
  | none => .list []
  | some (r,gs) => .list [encPerm r,encGroup gs]

/-- The row-empty test on a map/filter input `[c,row]`. -/
def itcsRowNE : Expr := .arith .lt (.nat 0) (.length (arg 1))

/-- Every projected row is a list of length zero or two. -/
theorem itcs_row_ne_spec {Pg : Program} {f : ℕ} (hf : Pg.funs[f]? = some itcsRowNE)
    (c : Val) (r : Option (Perm (Fin q) × List (Perm (Fin q)))) :
    FunDet Pg f (.list [c,itcsRowVal r]) (boolVal r.isSome)
      (20*((Val.list [c,itcsRowVal r]).wt+10)) := by
  let Bw := (Val.list [c,itcsRowVal r]).wt+10
  have hin : (Val.list [c,itcsRowVal r]).wt≤Bw := by omega
  cases r with
  | none =>
    have gr : StDC Pg [.list [c,itcsRowVal (q:=q) none]] (arg 1) (.list []) 3 0 Bw :=
      StDC.arg rfl hin (by dsimp [Bw]; omega) ((st_wt_mem (by simp [itcsRowVal])).trans hin)
    have len := StDC.length gr (by dsimp [Bw]; simp)
    have test := StDC.arith' (StDC.nat 0 (by dsimp [Bw]; omega)) len (op:=.lt) (z:=0) rfl (by dsimp [Bw]; omega)
    exact StDC.funDet hf test (by dsimp [Bw]; omega)
  | some p =>
    have gr : StDC Pg [.list [c,itcsRowVal (some p)]] (arg 1) (.list [encPerm p.1,encGroup p.2]) 3 0 Bw :=
      StDC.arg rfl hin (by dsimp [Bw]; omega) ((st_wt_mem (by simp [itcsRowVal])).trans hin)
    have len := StDC.length gr (by dsimp [Bw]; simp)
    have test := StDC.arith' (StDC.nat 0 (by dsimp [Bw]; omega)) len (op:=.lt) (z:=1) rfl (by dsimp [Bw]; omega)
    exact StDC.funDet hf test (by dsimp [Bw]; omega)

/-- The filter predicate on arbitrary byte values. -/
def itcsRowQ : Val → Bool
  | .list [] => false
  | .list (_::_) => true
  | _ => false

/-- Filtering rows is precisely dropping the empty query answers. -/
theorem itcs_rows_filter (rows : List (Option (Perm (Fin q) × List (Perm (Fin q))))) :
    (rows.map itcsRowVal).filter itcsRowQ =
      rows.reduceOption.map (fun p=>itcsRowVal (some p)) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    cases r with
    | none => simpa [itcsRowVal, itcsRowQ] using ih
    | some p =>
      rw [List.map_cons, List.reduceOption_cons_of_some, List.map_cons, ← ih]; rfl

/-- The actual filter keeps exactly the nonempty projected rows. -/
theorem itcs_row_filter {Pg : Program} {flt f : ℕ}
    (hh : Pg.HasAt flt (filterFuns flt f)) (hf : Pg.funs[f]? = some itcsRowNE)
    (rows : List (Option (Perm (Fin q) × List (Perm (Fin q))))) :
    let inp := Val.list [.nat 0,.list (rows.map itcsRowVal)]
    FunDet Pg flt inp (.list (rows.reduceOption.map fun p=>itcsRowVal (some p)))
      (rows.length*(100*(inp.wt+10))+loopModK*(rows.length+1)*(2*inp.wt+rows.length+1)) := by
  dsimp only
  let inp : Val := .list [.nat 0,.list (rows.map itcsRowVal)]
  have hc {r : Option (Perm (Fin q) × List (Perm (Fin q)))} (hr : r∈rows) :
      (Val.list [.nat 0,itcsRowVal r]).wt≤4*inp.wt+10 := by
    have w0 := (wt_nat_le 0)
    have wr : (itcsRowVal r).wt≤ inp.wt :=
      (st_wt_mem (List.mem_map.2 ⟨r,hr,rfl⟩)).trans (st_wt_mem (by simp))
    have h:=wt_list2_le (.nat 0) (itcsRowVal r)
    omega
  have hh' := filter_spec hh (c:=.nat 0) (xs:=rows.map itcsRowVal) (q:=itcsRowQ)
    (B:=fun _=>100*(inp.wt+10)) (fun v hv=>by
      obtain ⟨r,hr,rfl⟩:=List.mem_map.1 hv
      have ht := itcs_row_ne_spec hf (.nat 0) r
      have he : itcsRowQ (itcsRowVal r)=r.isSome := by cases r <;> rfl
      rw [he]
      exact ht.mono (by
        have h:=hc hr
        change 20*((Val.list [.nat 0,itcsRowVal r]).wt+10)≤100*(inp.wt+10)
        omega))
  rw [itcs_rows_filter] at hh'
  have wout : (Val.list (rows.reduceOption.map fun p=>itcsRowVal (some p))).wt≤ inp.wt := by
    rw [←itcs_rows_filter]
    exact (wt_list_sublist List.filter_sublist).trans (st_wt_mem (by simp))
  refine FunAll.mono hh' fun w cost ⟨hw,hcost⟩=>⟨hw,?_⟩
  rw [hw] at hcost
  simp only [List.map_map,Function.comp_def,List.map_const',List.sum_replicate,List.length_map] at hcost
  dsimp only [inp] at *
  exact hcost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)

/-- The established first-field reader also reads representatives of projected rows. -/
theorem itcs_fst_row_spec {Pg : Program} {f : ℕ} (hf : Pg.funs[f]? = some krFstF)
    (p : Perm (Fin q) × List (Perm (Fin q))) :
    FunDet Pg f (.list [.nat 0,itcsRowVal (some p)]) (encPerm p.1)
      (100*((Val.list [.nat 0,itcsRowVal (some p)]).wt+10)) := by
  let Bw := (Val.list [.nat 0,itcsRowVal (some p)]).wt+10
  have hin : (Val.list [.nat 0,itcsRowVal (some p)]).wt≤Bw := by omega
  have wr : (itcsRowVal (some p)).wt≤Bw := (st_wt_mem (by simp [itcsRowVal])).trans hin
  have wp : (encPerm p.1).wt≤Bw := (st_wt_mem (List.mem_cons_self ..)).trans wr
  have ga : StDC Pg [.list [.nat 0,itcsRowVal (some p)]] (arg 1) (itcsRowVal (some p)) 3 0 Bw :=
    StDC.arg rfl hin (by dsimp [Bw]; omega) wr
  have body := StDC.get ga (StDC.nat 0 (by dsimp [Bw]; omega)) rfl wp
  exact StDC.funDet hf body (by dsimp [Bw]; omega)

end GI.Impl
