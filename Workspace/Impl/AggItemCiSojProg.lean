module

public import Workspace.Impl.AggItemCiSojSourceRun
public import Workspace.Impl.AggItemCiSojFinalProg
public import Workspace.Impl.AggItemCiSojStep

@[expose] public section

/-! # The complete first-rectangle item program contract -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (NormalizedFactor)

/-- Public init/start/step indices and all installed subprogram indices. -/
structure itcsSojIdx where
  init : ℕ
  step : ℕ
  source : itcsSourceIdx
  finalizer : itcsFinalIdx

/-- The item uses the actual source program, actual saved-answer finalizer, empty
init, and exact at-most-two-query queue. All library obligations are body or
standard-library installation facts. -/
structure itcsSojOk (Pg : Program) (A : itcsSojIdx) (hfac : NormalizedFactor) : Prop where
  init : Pg.funs[A.init]?=some Expr.nil
  step : Pg.funs[A.step]?=some (itcsQueueF A.finalizer.f)
  source : itcsSourceOk Pg A.source
  finalizer : itcsFinalOk Pg A.finalizer hfac

/-- The full `sojItem` contract for every interface. The only cited rectangle
contracts are certificate construction and representation construction. Their
context, palette and size preconditions, and every recursive query precondition,
are discharged in the init/start/step proofs used here. -/
theorem itcs_soj_spec (I : Iface) {Pg : Program} (F : Funs) {A : itcsSojIdx} {hfac : NormalizedFactor}
    (h : itcsSojOk Pg A hfac) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (hc : RcCertSpec Pg A.source.cert Bc) (hr : RcRepSpec Pg A.source.rect.rep Br) :
    ItciSojSpec I Pg F A.init A.source.f A.step (itcsXs (normalizedFactorPrim hfac) Bc Br hBc hBr) := by
  obtain ⟨cf,hcf⟩ := itcs_cert_fixed hc
  let pf := normalizedFactorPrim hfac
  have hfinal : itcsFinalSpec Pg A.finalizer.f pf := itcs_final_ok_spec h.finalizer
  refine ⟨itcsRel I Pg A.source.rect.rep Br cf pf Bc hBc hBr,?_⟩
  intro Ω C k e c S sv lv L hcall K hK hcase
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact itcs_init_xs I hcall K hK cf pf Bc Br hBc hBr h.init hr
  · intro w E hKeep
    exact itcs_keep_ne (c:=c) hKeep
  · intro w E hKeep
    exact itcs_keep_weight_xs (c:=c) hKeep pf Bc hBc hBr (I.inW .giant S)
  · intro b X x₀ Y y₀ w E ho hlarge hKeep
    exact itcs_source_run I h.source hcall K hK hcase pf Bc Br hBc hBr cf hcf b X Y x₀ y₀ ho hlarge w E hKeep
  · intro b oX oY ist E sb f hRi
    exact itcs_rel_wtR I pf hBc hBr hRi
  · intro b oX oY ist E sb f hRi
    exact itcs_rel_step I pf hBc hBr h.step hfinal e c S L K hK hcall.good b oX oY ist E sb f hRi
  · exact itcs_xs_objW I hcall K pf Bc Br hBc hBr

/-- The same actual programs meet the contract with one global uniform
polynomial bound on init/start/step costs, all kept and continuation values,
outputs, recursive query states, and bounded pair-object encodings. -/
theorem itcs_soj_spec_pbu (I : Iface) {Pg : Program} (F : Funs) {A : itcsSojIdx} {hfac : NormalizedFactor}
    (h : itcsSojOk Pg A hfac) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (hc : RcCertSpec Pg A.source.cert Bc) (hr : RcRepSpec Pg A.source.rect.rep Br) :
    ItciSojSpec I Pg F A.init A.source.f A.step (itcsXs (normalizedFactorPrim hfac) Bc Br hBc hBr) ∧
      PBU (fun _ W _ => itcsXs (normalizedFactorPrim hfac) Bc Br hBc hBr W) :=
  ⟨itcs_soj_spec I F h Bc Br hBc hBr hc hr,itcs_xs_pbu _ _ _ hBc hBr⟩

end GI.Impl
