module

public import Workspace.Impl.AggItemCfDeg

@[expose] public section

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited Equiv Equiv.Perm

/-- Keep just the degree returned by the stabilizer-chain program. -/
def itCfRDegreeF (dg : ℕ) : Expr :=
  .letE (.call dg (.var 0)) (.get (.var 1) (.nat 1))

/-- Extracting the degree is deterministic even when stabilizer generators vary. -/
theorem itCfR_degree_spec (hps : PointwiseStab) {P : Program} {f dg jps : ℕ}
    (hf : P.funs[f]? = some (itCfRDegreeF dg))
    (hdg : P.HasAt dg (itCfDegFuns dg jps))
    (hj : P.prims[jps]? = some (pointwiseStabPrim hps))
    {q : ℕ} (hs : List (Perm (Fin q))) (Φ : Finset (Fin q)) (xs : List (Fin q))
    (hpres : ∀ h ∈ gens hs, ∀ a ∈ Φ, h a ∈ Φ) (hnd : xs.Nodup)
    (hmem : ∀ b, b ∈ xs ↔ b ∈ Φ) :
    FunDet P f (.list [encGroup hs, encPts xs]) (.nat (transDeg (gens hs) Φ))
      (10 * ((Val.list [encGroup hs, encPts xs]).wt +
        itCfDegC hps (.list [encGroup hs, encPts xs]) (encGroup hs) q xs.length + q + 10)) := by
  set a : Val := .list [encGroup hs, encPts xs]
  set B := itCfDegC hps a (encGroup hs) q xs.length
  have hdeg := (itCf_deg_spec hps hdg hj hs Φ xs hpres hnd hmem).wt_lt
  change FunAll P dg a (fun w cost =>
    (∃ (gs : List (Perm (Fin q))) (fl : ℕ),
      w = .list [encGroup gs, .nat (transDeg (gens hs) Φ), .nat fl] ∧ cost ≤ B) ∧
      w.wt < cost) at hdeg
  have hc : EvalAll P [a] (.call dg (.var 0)) (fun w c =>
      (∃ gs fl, w = .list [encGroup gs, .nat (transDeg (gens hs) Φ), .nat fl]) ∧
      w.wt ≤ B ∧ c ≤ a.wt + 2 * B + 2) :=
    EvalAll.call_funAll (Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl) fun v cv hv => by
      obtain ⟨hv, hcv⟩ := hv
      subst v
      exact hdeg.mono fun w cw ⟨⟨gs, fl, hw, hcw⟩, hww⟩ =>
        ⟨⟨gs, fl, hw⟩, by omega, by
          omega⟩
  have hdq : transDeg (gens hs) Φ ≤ q :=
    (transDeg_spec _ _).2.trans (Finset.card_le_univ _ |>.trans_eq (Fintype.card_fin q))
  have hdw := wt_nat_le (transDeg (gens hs) Φ)
  refine FunDet.intro hf (EvalAll.letE hc ?_)
  rintro w cw ⟨⟨gs, fl, rfl⟩, hww, hcw⟩
  have gv := Det.var' (P := P)
    (env := [a, .list [encGroup gs, .nat (transDeg (gens hs) Φ), .nat fl]]) (i := 1) rfl
  have gg := Det.get' gv (Det.nat 1) (v := .nat (transDeg (gens hs) Φ)) rfl
  refine gg.post fun c hc => ⟨rfl, ?_⟩
  change cw + c + (Val.nat (transDeg (gens hs) Φ)).wt + 1 ≤
    10 * (a.wt + B + q + 10)
  omega

end GI.Impl
