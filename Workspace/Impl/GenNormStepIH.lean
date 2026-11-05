module

public import Workspace.Impl.GenNormIH
public import Workspace.Impl.GenNormInput

@[expose] public section

/-! # The normalization specification under the measured recursive induction hypothesis -/
namespace GI.Impl
open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encKSetTuples Preimage PointwiseStab Membership)

/-- The complete normalization branch under the usual recursive induction hypothesis.
The failed integer small test proves that the computed Cameron degree exceeds `q₀`. -/
theorem normStep_spec_of_IH (R : Rest) (hp : Preimage) (hst : PointwiseStab) (hm : Membership)
    {Pg : Program} {F : Funs} (o : normOps Pg hp hst hm) (t : normTailAt Pg F hm)
    {f prep : ℕ} (hf : Pg.funs[f]? = some (normStepF prep t.tail))
    (hprep : Pg.funs[prep]? = some (normPrepF o))
    {Ω C : Type} [Finite Ω] {n m k sz : ℕ} (en : Ω ≃ Fin n) (cc : C → ℕ)
    (hcc : Function.Injective cc) {S : State Ω C} (hgood : Good P₀ .cont S)
    (ih : R.iface.IH Pg F .cont S) {gv dv xv yv hv rv fv hh rep hv' : Val}
    (hcan : Canon en cc (.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz]) S)
    (hs : (S.N : ℝ) ^ P₀.γ < S.size) (htr : S.Transitive) (hfl : ¬ S.FloorEntered)
    (Q : PrimitiveQuotient S) (hsm : ¬ Q.SmallZ P₀.smallExp)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)
    (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (hrep : normNumbered en Q rep) (hH : HierValC en hv' (Q.pre ++ Q.top :: Q.post)) :
    FunAll Pg f (.list [.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz], rep, hv',
      .nat m, .nat k, encKSetTuples e]) (fun u cost =>
      ∃ (A : Set (Perm Ω)) (r : Run P₀ .cont S none A), r.kind = .normalize ∧ AnsC en u A ∧
        (cost : ℝ) ≤ normStepCost hp hst hm n m (Val.list
          [.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz], rep, hv',
            .nat m, .nat k, encKSetTuples e]).wt + R.iface.childCost r) := by
  have hq := Q.q₀_lt_of_single P₀_enumeratesBounded hsm e hS
  exact normStep_spec R hp hst hm o t hf hprep en cc hcan hs htr hfl Q hsm e hS hq hkc hkl
    hrep hH (fun D b hmode lv hL j val hval =>
      normChild_fromIH R hcc hgood ih hs htr Q D.choice hq hkc hkl b hmode hL j hval)

/-- On the canonical input produced by exposure and single-factor recognition, one uniform
`E_N` bound pays for the branch's own work. This is the normalization contribution to
`Wgeneral` in `Rest.Req`. -/
theorem normStep_own_le_expLogSq (hp : Preimage) (hst : PointwiseStab) (hm : Membership) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω C : Type} (S : State Ω C) {n m k : ℕ} (en : Ω ≃ Fin n)
      (cc : C → ℕ) {sv rep hv : Val}, Canon en cc sv S →
      ∀ (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)),
        Q.ProductStructure m k 1 e → normNumbered en Q rep →
        HierValC en hv (Q.pre ++ Q.top :: Q.post) →
        (normStepCost hp hst hm n m
          (Val.list [sv, rep, hv, .nat m, .nat k, encKSetTuples e]).wt : ℝ) ≤ expLogSq A S.N := by
  obtain ⟨A, hA, h⟩ := normStepCost_le_expLogSq hp hst hm (10 ^ 6) 6
  refine ⟨A, hA, ?_⟩
  intro Ω C S n m k en cc sv rep hv hcan Q e hS hr hh
  exact h _ _ _ _ hcan.fits ((normDegree_le en Q e hS).trans (by have := hcan.fits; omega))
    (normInput_wt en cc hcan Q e hS hr hh)

end GI.Impl
