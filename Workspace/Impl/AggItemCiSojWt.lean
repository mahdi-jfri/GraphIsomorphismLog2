module

public import Workspace.Impl.AggStructDC

@[expose] public section

/-! # A deterministic output fits its proved time budget -/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- The evaluation semantics charges for every output. A deterministic callee's
proved cost bound therefore also bounds the weight of its fixed result. -/
theorem itcs_det_weight {Pg : Program} {f : ℕ} {v w : Val} {B : ℕ}
    (h : FunDet Pg f v w B) : w.wt ≤ B := by
  obtain ⟨body, -, hb⟩ := h
  obtain ⟨w', cost, he, hw, hc⟩ := hb.exists_eval
  subst w'
  exact he.wt_lt.le.trans hc

end GI.Impl
