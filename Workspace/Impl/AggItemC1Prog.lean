module

public import Workspace.Impl.AggItemC1Top

@[expose] public section

/-!
# Case 1 as a program: the functions in one place

`ItC1Idx` lists the function indices of the Case 1 item and its callees, and `ItC1Ok P I` says
that the program `P` has the right bodies there. `it_c1_prog` is `it_c1_spec` with all callee
specs discharged. No primitive is called: the item uses only the list library.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

/-- The function indices of the Case 1 item. -/
structure ItC1Idx where
  (f dat chk fnd ft swt sb gen sch cmp par : ℕ)
  (rng mpS sz cnt mpP pb flt kb inv : ℕ)
  (al ct : ℕ)
  (mpT trB mpG gb bs bb app : ℕ)
  (mpS' sb' : ℕ)
  (mpI ib fltI it fld st : ℕ)

/-- The program has the bodies of the Case 1 item at the indices `I`. -/
structure ItC1Ok (P : Program) (I : ItC1Idx) : Prop where
  f : P.funs[I.f]? = some (itC1F I.dat I.chk I.fnd I.swt I.gen I.sch I.cmp I.par)
  rng : P.HasAt I.rng (rangeFuns I.rng)
  dat : P.funs[I.dat]? = some (itDatF I.rng I.mpS I.mpP I.inv)
  mpS : P.HasAt I.mpS (mapFuns I.mpS I.sz)
  sz : P.funs[I.sz]? = some (itSzB I.cnt)
  cnt : P.HasAt I.cnt (countFuns I.cnt)
  mpP : P.HasAt I.mpP (mapFuns I.mpP I.pb)
  pb : P.funs[I.pb]? = some (itPosB I.flt)
  flt : P.HasAt I.flt (filterFuns I.flt I.kb)
  kb : P.funs[I.kb]? = some itKeyB
  inv : P.HasAt I.inv (invFuns I.inv)
  chk : P.funs[I.chk]? = some (itChkF I.rng I.al)
  al : P.HasAt I.al (allFuns I.al I.ct)
  ct : P.funs[I.ct]? = some (itCntT I.cnt)
  fnd : P.HasAt I.fnd (findFuns I.fnd I.ft)
  ft : P.funs[I.ft]? = some itFixT
  swt : P.HasAt I.swt (mapFuns I.swt I.sb)
  sb : P.funs[I.sb]? = some itSwB
  gen : P.funs[I.gen]? = some (itGensF I.mpT I.rng I.mpG I.app)
  mpT : P.HasAt I.mpT (mapFuns I.mpT I.trB)
  trB : P.funs[I.trB]? = some (itTrB I.swt)
  mpG : P.HasAt I.mpG (mapFuns I.mpG I.gb)
  gb : P.funs[I.gb]? = some (itGenB I.bs)
  bs : P.HasAt I.bs (mapFuns I.bs I.bb)
  bb : P.funs[I.bb]? = some itBsB
  app : P.HasAt I.app (appendFuns I.app)
  sch : P.funs[I.sch]? = some (itSchF I.rng I.mpS')
  mpS' : P.HasAt I.mpS' (mapFuns I.mpS' I.sb')
  sb' : P.funs[I.sb']? = some (itSchB I.par I.cmp)
  cmp : P.HasAt I.cmp (composeFuns I.cmp)
  par : P.funs[I.par]? = some (itParF I.rng I.mpI I.fld)
  mpI : P.HasAt I.mpI (mapFuns I.mpI I.ib)
  ib : P.funs[I.ib]? = some (itInvB I.fltI)
  fltI : P.HasAt I.fltI (filterFuns I.fltI I.it)
  it : P.funs[I.it]? = some itInvT
  fld : P.HasAt I.fld (foldlFuns I.fld I.st)
  st : P.funs[I.st]? = some itParS

variable {q : ℕ}

/-- **The Case 1 item as a program**, with its functions at `I`: on orbit labels `labX`, `labY`
(as `orbits_spec` returns them) with a point `a` that is not least in its orbit, the program
returns the overcosets `itcOsM … (itcMs labX a)` in cost `itC1C q = 10¹⁰ (q+1)⁶`. -/
theorem it_c1_prog {P : Program} {I : ItC1Idx} (h : ItC1Ok P I)
    {gx gy : List (Perm (Fin q))} {labX labY : Fin q → ℕ} (hlX : ItcLab gx labX)
    (hlY : ItcLab gy labY) (hex : ∃ a : Fin q, labX a ≠ a)
    (E₀ : Subgroup (alternatingGroup (Fin q))) :
    ∃ (a : Fin q) (ha : labX a ≠ a), FunDet P I.f (.list [encFun labX, encFun labY])
      (.list ((itcOsM hlX labY ha E₀ (itcMs labX a)).map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2))
      (itC1C q) := by
  classical
  have hpar : ∀ σ : Perm (Fin q), FunDet P I.par (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q) :=
    fun σ => it_par_spec h.par h.rng h.mpI h.ib h.fltI h.it h.fld h.st σ
  refine it_c1_spec h.f (fun lab hlt => it_dat_spec h.dat h.rng h.mpS h.sz h.cnt h.mpP h.pb h.flt
    h.kb h.inv hlt) (fun labX labY => ?_) h.fnd h.ft (fun u v => it_swTab_spec h.swt h.sb u v)
    (fun hl => it_gens_spec h.gen h.mpT h.trB h.swt h.sb h.rng h.mpG h.gb h.bs h.bb h.app hl)
    (fun t S hS => it_sch_spec h.sch h.rng h.mpS' h.sb' hpar h.cmp t hS) h.cmp hpar hlX hlY hex E₀
  convert it_chk_spec h.chk h.rng h.al h.ct h.cnt labX labY

end GI.Impl
