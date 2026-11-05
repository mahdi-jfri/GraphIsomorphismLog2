module

public import Workspace.Impl.TermJHCoef
public import Workspace.Impl.TermJProgLoc
public import Workspace.Impl.AggItemC1Par

@[expose] public section

/-!
# The transporter of one label: the layout

The per-label program has thirteen own functions at `p.b, …, p.b + 12` (`tmJHFuns`). The other
positions in `TmJHPos` are library blocks and cited primitives. `TmJHAt P p` says that all of
them sit where `p` says.

* `tmJHMainF` (at `p.b`), on `[ctx, encPerm h]`: the lift `g` of `(h; 1)` (NormalizedFactor in
  `⟨G|_dom, N^q⟩`), the local transporter `z` (`tmJLF`), `u = z⁻¹ g`, then `tmJHTailF`.
* `tmJHTailF` (at `p.b + 1`), on `[ctx, encPerm z, encPerm u]`: decode `u = (d, π)`, solve for
  `c`, compute the parity of `π`, and return `z · tmJCorrE Tl odd lg c`.
-/

namespace GI.Impl

open GI.Lang

/-- The positions of the per-label program. `b` is the own block. -/
structure TmJHPos where
  b : ℕ
  iv : ℕ
  rep : ℕ
  pr : ℕ
  prg : ℕ
  prt : ℕ
  prte : ℕ
  rg : ℕ
  comp : ℕ
  tbR : ℕ
  tbE : ℕ
  tbP : ℕ
  dc : ℕ
  pp : ℕ
  fld : ℕ
  locA : ℕ
  dsA : ℕ
  tbA : ℕ
  tbe : ℕ
  swS : ℕ
  tbD : ℕ
  swDE : ℕ
  tbP2 : ℕ
  swPE : ℕ
  sol : ℕ
  jh : ℕ
  vsum : ℕ
  jm : ℕ
  zm : ℕ
  par : ℕ
  rng : ℕ
  mp : ℕ
  ib : ℕ
  flt : ℕ
  it : ℕ
  fld2 : ℕ
  st : ℕ
  L : ℕ
  ap : ℕ
  en : ℕ
  mR : ℕ
  mB : ℕ
  mP : ℕ
  fR : ℕ
  fC : ℕ
  mD : ℕ
  jmem : ℕ
  jf : ℕ

/-- **The main function**, on `[ctx, encPerm h]`. -/
def tmJHMainF (p : TmJHPos) : Expr :=
  .letE (.call (p.b + 2) (mk2 (arg 1) (.get (arg 0) (.nat 10))))
  (.letE (.prim p.jf (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.var 1)))
  (.letE (.call p.L (.snoc (mk4 (arg 1) (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 3))
      (.get (.get (arg 0) (.nat 10)) (.nat 2))) (.get (.get (arg 0) (.nat 10)) (.nat 3))))
  (.call (p.b + 1) (mk3 (arg 0) (.var 3)
    (.call p.comp (mk2 (.call p.iv (.var 3)) (.get (.var 2) (.nat 0))))))))

/-- **The tail**, on `[ctx, encPerm z, encPerm u]`. -/
def tmJHTailF (p : TmJHPos) : Expr :=
  .letE (.call (p.b + 3) (mk2 (arg 2) (.get (arg 0) (.nat 10))))
  (.letE (.call (p.b + 11) (mk2 (arg 0) (.get (.var 1) (.nat 0))))
  (.call p.comp (mk2 (arg 1) (.call (p.b + 10) (mk4 (.get (arg 0) (.nat 7))
    (.get (arg 0) (.nat 10)) (.call p.par (.get (.var 1) (.nat 1)))
    (.call (p.b + 9) (mk3 (.get (arg 0) (.nat 6)) (.get (.var 2) (.nat 1))
      (.get (arg 0) (.nat 10)))))))))

/-- **The own functions** of the per-label program, at `p.b, …, p.b + 12`. -/
def tmJHFuns (p : TmJHPos) : List Expr :=
  [tmJHMainF p, tmJHTailF p, tmJHCstF p.iv p.rep p.pr, tmJHDecF p.rg p.tbR p.tbP,
    tmJHDecRF p.tbE, tmJHDecEF, tmJHDecPF, tmJHPowF p.dc p.pp p.iv,
    tmJHLamSF (p.b + 7) p.locA p.comp, tmJHLamF p.fld p.rg, tmJHCorrF p.swS p.rg p.comp,
    tmJHCoefF p.sol p.vsum p.zm, tmJHZeroF]

theorem tmJHFuns_length (p : TmJHPos) : (tmJHFuns p).length = 13 := rfl

/-- **Where the per-label program sits**: its own functions and the library blocks. -/
structure TmJHAt (P : Program) (p : TmJHPos) : Prop where
  hfuns : P.HasAt p.b (tmJHFuns p)
  hiv : P.HasAt p.iv (invFuns p.iv)
  hrep : P.HasAt p.rep (replicateFuns p.rep)
  hpr : TmJPairAt P p.pr p.prg p.prt p.prte
  hrg : P.HasAt p.rg (rangeFuns p.rg)
  hcomp : P.HasAt p.comp (composeFuns p.comp)
  htbR : P.HasAt p.tbR (mapFuns p.tbR (p.b + 4))
  htbE : P.HasAt p.tbE (mapFuns p.tbE (p.b + 5))
  htbP : P.HasAt p.tbP (mapFuns p.tbP (p.b + 6))
  hdc : P.funs[p.dc]? = some (linBitsDecodeF p.dc)
  hpp : P.funs[p.pp]? = some (linPermPowF p.pp p.comp)
  hfld : P.HasAt p.fld (foldlFuns p.fld (p.b + 8))
  hlocA : P.funs[p.locA]? = some (tmJLocAF p.dsA p.pr)
  hds : P.funs[p.dsA]? = some (tmJDsAF p.rg p.tbA)
  htbA : P.HasAt p.tbA (mapFuns p.tbA p.tbe)
  htbe : P.funs[p.tbe]? = some tmJDsAEF
  hswS : P.funs[p.swS]? = some (tmJSwSF p.iv p.tbD p.tbP2 p.pr)
  htbD : P.HasAt p.tbD (mapFuns p.tbD p.swDE)
  hswDE : P.funs[p.swDE]? = some tmJSwDEF
  htbP2 : P.HasAt p.tbP2 (mapFuns p.tbP2 p.swPE)
  hswPE : P.funs[p.swPE]? = some tmJSwPEF
  hsol : P.HasAt p.sol (tmJSolFuns p.sol p.jh)
  hvsum : P.HasAt p.vsum (tmJVSumFuns p.vsum p.jm)
  hzm : P.HasAt p.zm (mapFuns p.zm (p.b + 12))
  hpar : P.funs[p.par]? = some (itParF p.rng p.mp p.fld2)
  hrng : P.HasAt p.rng (rangeFuns p.rng)
  hmp : P.HasAt p.mp (mapFuns p.mp p.ib)
  hib : P.funs[p.ib]? = some (itInvB p.flt)
  hflt : P.HasAt p.flt (filterFuns p.flt p.it)
  hit : P.funs[p.it]? = some itInvT
  hfld2 : P.HasAt p.fld2 (foldlFuns p.fld2 p.st)
  hst : P.funs[p.st]? = some itParS
  hL : TmJLAt P p.L p.rg p.ap p.comp p.iv p.en p.mR p.mB p.mP p.fR p.fC p.mD p.pr p.prg p.prt
    p.prte p.jmem p.jf

namespace TmJHAt

variable {P : Program} {p : TmJHPos} (hA : TmJHAt P p)
include hA

theorem hmain : P.funs[p.b]? = some (tmJHMainF p) := by
  simpa [tmJHFuns] using hA.hfuns 0 (by simp [tmJHFuns])
theorem htail : P.funs[p.b + 1]? = some (tmJHTailF p) := hA.hfuns 1 (by simp [tmJHFuns])
theorem hcst : P.funs[p.b + 2]? = some (tmJHCstF p.iv p.rep p.pr) := hA.hfuns 2 (by simp [tmJHFuns])
theorem hdec : P.funs[p.b + 3]? = some (tmJHDecF p.rg p.tbR p.tbP) := hA.hfuns 3 (by simp [tmJHFuns])
theorem hdecR : P.funs[p.b + 4]? = some (tmJHDecRF p.tbE) := hA.hfuns 4 (by simp [tmJHFuns])
theorem hdecE : P.funs[p.b + 5]? = some tmJHDecEF := hA.hfuns 5 (by simp [tmJHFuns])
theorem hdecP : P.funs[p.b + 6]? = some tmJHDecPF := hA.hfuns 6 (by simp [tmJHFuns])
theorem hpow : P.funs[p.b + 7]? = some (tmJHPowF p.dc p.pp p.iv) := hA.hfuns 7 (by simp [tmJHFuns])
theorem hlamS : P.funs[p.b + 8]? = some (tmJHLamSF (p.b + 7) p.locA p.comp) := hA.hfuns 8 (by simp [tmJHFuns])
theorem hlam : P.funs[p.b + 9]? = some (tmJHLamF p.fld p.rg) := hA.hfuns 9 (by simp [tmJHFuns])
theorem hcorr : P.funs[p.b + 10]? = some (tmJHCorrF p.swS p.rg p.comp) := hA.hfuns 10 (by simp [tmJHFuns])
theorem hcoef : P.funs[p.b + 11]? = some (tmJHCoefF p.sol p.vsum p.zm) := hA.hfuns 11 (by simp [tmJHFuns])
theorem hzero : P.funs[p.b + 12]? = some tmJHZeroF := hA.hfuns 12 (by simp [tmJHFuns])

theorem lamAt : TmJHLamAt P (p.b + 9) p.fld (p.b + 8) (p.b + 7) p.dc p.pp p.comp p.iv p.locA p.dsA
    p.rg p.tbA p.tbe p.pr p.prg p.prt p.prte :=
  ⟨hA.hlam, hA.hfld, hA.hlamS, hA.hpow, hA.hdc, hA.hpp, hA.hcomp, hA.hiv, hA.hlocA, hA.hds,
    hA.hrg, hA.htbA, hA.htbe, hA.hpr⟩

theorem corrAt : TmJHCorrAt P (p.b + 10) p.swS p.rg p.comp p.iv p.tbD p.swDE p.tbP2 p.swPE p.pr
    p.prg p.prt p.prte :=
  ⟨hA.hcorr, hA.hswS, hA.hiv, hA.htbD, hA.hswDE, hA.htbP2, hA.hswPE, hA.hpr, hA.hrg, hA.hcomp⟩

theorem coefAt : TmJHCoefAt P (p.b + 11) p.sol p.jh p.vsum p.jm p.zm (p.b + 12) :=
  ⟨hA.hcoef, hA.hsol, hA.hvsum, hA.hzm, hA.hzero⟩

end TmJHAt

end GI.Impl
