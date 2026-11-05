module

public import Workspace.Impl.AggItemCiPartF
public import Workspace.Impl.AggItemC1Prog

@[expose] public section

/-!
# The colored-partition item: the function table and the item

`ItciOk P I` says that the program has the functions of the colored-partition item at the
indices `I`; it reuses the functions of the Case 1 item (`ItC1Ok`) for ranges, positions,
inverses, products, transpositions, the Schreier list and the parity. `itci_prog` is the program
on `[encFun fX, encFun fY]`, and `itci_classPart` is the model's item for two vertex-class
partitions (Case 3(a)) with the program's list standing for it.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

/-- The function indices of the colored-partition item. -/
structure ItciIdx where
  c1 : ItC1Idx
  (f fa all chk fg mpC cb fnd t : ℕ)

/-- The program has the bodies of the colored-partition item at the indices `I`. -/
structure ItciOk (P : Program) (I : ItciIdx) : Prop where
  c1 : ItC1Ok P I.c1
  f : P.funs[I.f]? = some (itciF I.c1.rng I.fa I.all I.fg I.c1.par I.c1.cmp)
  fa : P.funs[I.fa]? = some (itciAF I.c1.rng I.c1.mpP I.c1.inv I.c1.cmp)
  all : P.HasAt I.all (allFuns I.all I.chk)
  chk : P.funs[I.chk]? = some itciChkT
  fg : P.funs[I.fg]? = some (itciGF I.mpC I.c1.fnd I.c1.mpT I.c1.swt I.c1.sch)
  mpC : P.HasAt I.mpC (mapFuns I.mpC I.cb)
  cb : P.funs[I.cb]? = some (itciCB I.fnd)
  fnd : P.HasAt I.fnd (findFuns I.fnd I.t)
  t : P.funs[I.t]? = some itciEqT

variable {q : ℕ}

/-- **The colored-partition item as a program**, with its functions at `I`: on two colorings
whose values weigh at most `M`, the program's overcosets in cost `itciFC M = 10¹² (M+2)⁶`. -/
theorem itci_prog {P : Program} {I : ItciIdx} (h : ItciOk P I) (fX fY : Fin q → ℕ) {M : ℕ}
    (hMX : (encFun fX).wt ≤ M) (hMY : (encFun fY).wt ≤ M)
    (E₀ : Subgroup (alternatingGroup (Fin q))) :
    FunDet P I.f (.list [encFun fX, encFun fY]) (itciOV (itciOs fX fY (itciOt fX) E₀))
      (itciFC M) := by
  have h1 := h.c1
  have hpar : ∀ σ : Perm (Fin q), FunDet P I.c1.par (encPerm σ) (.nat (itpNInv σ % 2))
      (itParC q) :=
    fun σ => it_par_spec h1.par h1.rng h1.mpI h1.ib h1.fltI h1.it h1.fld h1.st σ
  exact itci_f_spec h.f h1.rng h.all h.chk h1.cmp hpar fX fY hMX hMY
    (itci_al_spec h.fa h1.rng h1.mpP h1.pb h1.flt h1.kb h1.inv h1.cmp fX fY hMX hMY)
    (itci_g_spec h.fg h.mpC h.cb h.fnd h.t h1.fnd h1.ft h1.mpT h1.trB h1.swt h1.sb h1.swt
      h1.sch h1.rng h1.mpS' h1.sb' hpar h1.cmp fX hMX) E₀

variable {Ω C : Type} {P : Params} {S : State Ω C}

/-- **The item of two vertex-class partitions** (Case 3(a)), with the program's list. -/
theorem itci_classPart (L : GiantLabels S) (fX fY : Fin L.q → ℕ) :
    ∃ ovs, (objItem (P := P) (classPart fX) (classPart fY) : AuxItem P S L).script =
        Script.done ⟨[], ovs⟩ ∧
      List.Forall₂ (asOvAt L) (itciOs fX fY (itciOt fX) (evenStab (q := L.q) (classPart fX)))
        ovs ∧
      ∀ o ∈ itciOs fX fY (itciOt fX) (evenStab (q := L.q) (classPart fX)),
        gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype :=
  itci_item L _ _ (fun σ => itci_classPart_iff σ fX fY) (fun σ => itci_classPart_iff σ fX fX)
    (itciOt_spec fX)

end GI.Impl
