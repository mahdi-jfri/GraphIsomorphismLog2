module

public import Workspace.Impl.AggItemCiCfgFin

@[expose] public section

/-!
# The configuration branch: the program table

`itcqProgs_of`: if the program table holds the start program `itcqStF`, the step program
`itcqSkF` and the functions they call (`ItcqTab`), among them the sort of the outer points by
color `itcqDsF` and the alignment test `itcqAlF`, then the contracts `ItcqProgs` hold, so
`itcq_cfgSpec` applies (`itcq_cfgSpec_of`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

/-- The function indices of the configuration branch. -/
structure ItcqIdx where
  fs : ℕ
  fk : ℕ
  -- the start
  fl : ℕ
  fr : ℕ
  ff : ℕ
  fb : ℕ
  fa : ℕ
  fcl : ℕ
  fmp : ℕ
  fpc : ℕ
  fap : ℕ
  ffb : ℕ
  fe : ℕ
  fcdi : ℕ
  fcd : ℕ
  fg : ℕ
  fgm : ℕ
  fgg : ℕ
  fgm' : ℕ
  fsw : ℕ
  fd : ℕ
  f1 : ℕ
  -- the step
  fB : ℕ
  fdl : ℕ
  ff2 : ℕ
  fn : ℕ
  finv : ℕ
  flf : ℕ
  fmb : ℕ
  frh : ℕ
  fcmp : ℕ
  flm : ℕ
  fcs : ℕ
  fcm : ℕ
  fcb : ℕ
  fsm : ℕ
  fsw2 : ℕ
  fou : ℕ
  ffnd : ℕ
  fo : ℕ
  fpar : ℕ
  fpm : ℕ
  fib : ℕ
  fflt : ℕ
  fit : ℕ
  fpfl : ℕ
  fst : ℕ
  fsch : ℕ
  fsmp : ℕ
  fssb : ℕ
  -- the outer points by color, and the alignment test
  fdr : ℕ
  frm : ℕ
  frb : ℕ
  flq : ℕ
  flt : ℕ
  fam : ℕ
  fat : ℕ
  fal : ℕ
  fcm2 : ℕ
  fco : ℕ
  feq : ℕ

/-- **The program table of the configuration branch** at the indices `x`. -/
structure ItcqTab (P : Program) (x : ItcqIdx) : Prop where
  st : P.funs[x.fs]? = some (itcqStF x.fl x.fa)
  fl : P.funs[x.fl]? = some (itcqFlF x.fr x.ff)
  fr : P.HasAt x.fr (rangeFuns x.fr)
  ff : P.HasAt x.ff (filterFuns x.ff x.fb)
  fb : P.funs[x.fb]? = some itcqFbT
  fa : P.funs[x.fa]? = some (itcqArgF x.fr x.fcl x.fcd x.fg x.fd)
  fcl : P.funs[x.fcl]? = some (itcqClF x.fmp x.fap)
  fmp : P.HasAt x.fmp (mapFuns x.fmp x.fpc)
  fpc : P.funs[x.fpc]? = some itcqPcF
  fap : P.HasAt x.fap (appendFuns x.fap)
  ffb : P.HasAt x.ffb (findFuns x.ffb x.fe)
  fe : P.funs[x.fe]? = some eqTestF
  fcdi : P.funs[x.fcdi]? = some (itcqCdF x.fpc x.ffb)
  fcd : P.HasAt x.fcd (mapFuns x.fcd x.fcdi)
  fg : P.funs[x.fg]? = some (itcqGrpF x.fr x.fgm x.fap)
  fgm : P.HasAt x.fgm (mapFuns x.fgm x.fgg)
  fgg : P.funs[x.fgg]? = some (itcqGenF x.fgm')
  fgm' : P.HasAt x.fgm' (mapFuns x.fgm' x.fsw)
  fsw : P.funs[x.fsw]? = some itcqSwF
  fd : P.HasAt x.fd (mapFuns x.fd x.f1)
  f1 : P.funs[x.f1]? = some itcqOneF
  sk : P.funs[x.fk]? = some (itcqSkF x.fB x.fal)
  fB : P.funs[x.fB]? = some (itcqSbF x.fr x.fdl x.fap x.finv x.flf x.flm x.fcs x.fou)
  fdl : P.funs[x.fdl]? = some (itcqDsF x.fdr x.frm x.fr x.fam)
  ff2 : P.HasAt x.ff2 (filterFuns x.ff2 x.fn)
  fn : P.funs[x.fn]? = some (itcqNfT x.fb)
  finv : P.HasAt x.finv (invFuns x.finv)
  flf : P.funs[x.flf]? = some (itcqLfB x.fmb x.fcmp)
  fmb : P.HasAt x.fmb (mapFuns x.fmb x.frh)
  frh : P.funs[x.frh]? = some itcqRhB
  fcmp : P.HasAt x.fcmp (composeFuns x.fcmp)
  flm : P.HasAt x.flm (mapFuns x.flm x.flf)
  fcs : P.funs[x.fcs]? = some (itcqCsF x.fr x.fcm)
  fcm : P.HasAt x.fcm (mapFuns x.fcm x.fcb)
  fcb : P.funs[x.fcb]? = some (itcqCsB x.fsm)
  fsm : P.HasAt x.fsm (mapFuns x.fsm x.fsw2)
  fsw2 : P.funs[x.fsw2]? = some itcqSwB
  fou : P.funs[x.fou]? = some (itcqOuF x.ffnd x.fpar x.fcmp x.fsch)
  ffnd : P.HasAt x.ffnd (findFuns x.ffnd x.fo)
  fo : P.funs[x.fo]? = some (itcqOdT x.fpar)
  fpar : P.funs[x.fpar]? = some (itParF x.fr x.fpm x.fpfl)
  fpm : P.HasAt x.fpm (mapFuns x.fpm x.fib)
  fib : P.funs[x.fib]? = some (itInvB x.fflt)
  fflt : P.HasAt x.fflt (filterFuns x.fflt x.fit)
  fit : P.funs[x.fit]? = some itInvT
  fpfl : P.HasAt x.fpfl (foldlFuns x.fpfl x.fst)
  fst : P.funs[x.fst]? = some itParS
  fsch : P.funs[x.fsch]? = some (itSchF x.fr x.fsmp)
  fsmp : P.HasAt x.fsmp (mapFuns x.fsmp x.fssb)
  fssb : P.funs[x.fssb]? = some (itSchB x.fpar x.fcmp)
  fdr : P.funs[x.fdr]? = some (itcqFlF x.fr x.ff2)
  frm : P.HasAt x.frm (mapFuns x.frm x.frb)
  frb : P.funs[x.frb]? = some (itcqRkB x.flq)
  flq : P.HasAt x.flq (filterFuns x.flq x.flt)
  flt : P.funs[x.flt]? = some itcqLtT
  fam : P.HasAt x.fam (mapFuns x.fam x.fat)
  fat : P.funs[x.fat]? = some (itcqAtB x.ffb)
  fal : P.funs[x.fal]? = some (itcqAlF x.fdl x.fcm2 x.feq)
  fcm2 : P.HasAt x.fcm2 (mapFuns x.fcm2 x.fco)
  fco : P.funs[x.fco]? = some itcqCoB
  feq : P.HasAt x.feq (eqNatsFuns x.feq)

variable {P : Program}

/-- **The program contracts from the table.** -/
theorem itcqProgs_of {x : ItcqIdx} (h : ItcqTab P x) : ItcqProgs P x.fs x.fk := by
  have hpar : ∀ {q : ℕ} (σ : Perm (Fin q)), FunDet P x.fpar (encPerm σ) (.nat (itpNInv σ % 2))
      (itParC q) := fun σ =>
    it_par_spec h.fpar h.fr h.fpm h.fib h.fflt h.fit h.fpfl h.fst σ
  have hds : ∀ {q : ℕ} (Z : PairCfg q) (z₀ : Fin q) {W : ℕ}, (rcCertIn Z z₀).wt ≤ W →
      FunDet P x.fdl (rcCertIn Z z₀) (itcqDV Z) (itcqDsC W) := fun Z z₀ _ hW =>
    itcq_dsF_spec h.fdl h.fdr h.fr h.ff2 h.fn h.fb h.frm h.frb h.flq h.flt h.fam h.fat h.ffb
      h.fe Z z₀ hW
  have hB : ∀ {q : ℕ} (X : PairCfg q) (x₀ : Fin q) (Y : PairCfg q) (y₀ : Fin q) (w : Val)
      (p₁ : Perm (Fin X.fiber.card)) (gs : List (Perm (Fin (X.fiber.card * X.fiber.card)))),
      (∀ g ∈ gs, itciD _ (itciDec g) = g) → ∀ {M : ℕ}, q + 1 ≤ M →
      (Val.list [itcqKs X x₀ Y y₀ w, .list [encPerm (itciD _ p₁), encGroup gs]]).wt ≤ M →
      FunDet P x.fB (.list [itcqKs X x₀ Y y₀ w, .list [encPerm (itciD _ p₁), encGroup gs]])
        (itciRes (itciOV (itcqOs X (itciExt X Y p₁) (itcqSg X gs))) w) (itcqSbC M) :=
    fun X x₀ Y y₀ w p₁ gs hgD _ hq hM =>
      itcq_sbF_spec h.fB h.fr
        hds h.fap h.finv
        (fun X α β a _ hq hM => itcq_lfB_spec h.flf h.fmb h.frh h.fcmp X α β a hq hM) h.flm
        (fun X x₀ _ hq hV => itcq_csF_spec h.fcs h.fr h.fcm h.fcb h.fsm h.fsw2 X x₀ hq hV)
        (fun X σ₀ S w _ hq hM => itcq_ouF_spec h.fou h.ffnd h.fo hpar h.fcmp h.fsch h.fr
          h.fsmp h.fssb X σ₀ S w hq hM)
        X x₀ Y y₀ w p₁ gs hgD hq hM
  have hal : ∀ {q : ℕ} (X : PairCfg q) (x₀ : Fin q) (Y : PairCfg q) (y₀ : Fin q) (w u : Val)
      {M : ℕ}, (Val.list [itcqKs X x₀ Y y₀ w, u]).wt ≤ M →
      FunDet P x.fal (.list [itcqKs X x₀ Y y₀ w, u]) (boolVal (decide
        (((itciFo X).map fun a => X.col a a) = (itciFo Y).map fun a => Y.col a a)))
        (itcqAlC M) := fun X x₀ Y y₀ w u _ hM =>
    itcq_alF_spec h.fal hds h.fcm2 h.fco h.feq X x₀ Y y₀ w u hM
  refine ⟨fun Kv tb w X x₀ Y y₀ _ hW => ?_, fun X x₀ Y y₀ w _ hM => ?_,
    fun X x₀ Y y₀ w p₁ gs hgD ha _ hq hM => ?_, fun X x₀ Y y₀ w x G ha _ hM => ?_⟩
  · exact itcq_stF_spec h.st h.fl h.fr h.ff h.fb
      (fun X Y hc _ hW => itcq_argF_spec h.fa h.fr h.fcl h.fmp h.fpc h.fap h.ffb h.fe h.fcdi
        h.fcd h.fg h.fgm h.fgg h.fgm' h.fsw h.fd h.f1 X Y hc hW) Kv tb w X x₀ Y y₀ hW
  · exact itcq_skF_emp h.sk X x₀ Y y₀ w hM
  · have h1 := hal X x₀ Y y₀ w (.list [encPerm (itciD _ p₁), encGroup gs]) hM
    rw [decide_eq_true (show _ = _ from ha)] at h1
    exact itcq_skF_ne h.sk (hB X x₀ Y y₀ w p₁ gs hgD hq hM) h1 hM
  · have h1 := hal X x₀ Y y₀ w (.list [x, G]) hM
    rw [decide_eq_false (show ¬ (_ = _) from ha)] at h1
    exact itcq_skF_nal h.sk X x₀ Y y₀ w h1 hM

/-- **The configuration branch from the program table.** -/
theorem itcq_cfgSpec_of {I : Iface} {F : Funs} {x : ItcqIdx} (h : ItcqTab P x) :
    ItciCfgSpec I P F x.fs x.fk itcqXc :=
  itcq_cfgSpec (itcqProgs_of h)

end GI.Impl
