import Workspace.Impl.AggItemCiSojMath

/-! # One certificate function fixed by the cited certificate program -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance

/-- The cited certificate program fixes one function of the source object for
all item branches. The existence proof is supplied at each actual call. -/
def itcsCertFnOK (Pg : Program) (fc : ℕ) (Bc : ℕ → ℕ) (cf : RcCertFn) : Prop :=
  ∀ {q : ℕ} (X : PairCfg q) (x₀ : Fin q) (hx : x₀∈X.fiber)
    (hcert : Nonempty (RectangleCertificate X.coloring false (X.idx hx) etaB)),
    FunAll Pg fc (rcCertIn X x₀) fun w cost => w=rcCertVal X (X.idx hx) (cf X (X.idx hx) hcert) ∧
      cost≤ Bc (rcCertIn X x₀).wt ∧ w.wt≤ Bc (rcCertIn X x₀).wt

/-- The required fixed function follows from the existing certificate contract. -/
theorem itcs_cert_fixed {Pg : Program} {fc : ℕ} {Bc : ℕ → ℕ} (hc : RcCertSpec Pg fc Bc) :
    ∃ cf : RcCertFn, itcsCertFnOK Pg fc Bc cf := itcs_cert_call hc

end GI.Impl
