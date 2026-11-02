import Workspace.Impl.GenNormPrep
import Workspace.Impl.GenNormTail

/-! # The normalization branch of the general dispatcher -/
namespace GI.Impl
open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encKSetTuples Preimage PointwiseStab Membership)

/-- Installed code for the normalization child map and answer combination. -/
structure normTailAt (Pg : Program) (F : Funs) (hm : Membership) where
  tail : ℕ
  map : ℕ
  child : ℕ
  gather : ℕ
  combine : ℕ
  step : ℕ
  compose : ℕ
  inverse : ℕ
  append : ℕ
  nf : ℕ
  membership : ℕ
  htail : Pg.funs[tail]? = some (tailF map combine nf)
  hmap : Pg.HasAt map (mapFuns map child)
  hchild : Pg.funs[child]? = some (normChildF F gather)
  hgather : Pg.HasAt gather (gatherFuns gather)
  hcombine : Pg.HasAt combine (foldlFuns combine step)
  hstep : Pg.funs[step]? = some (combStep compose inverse append)
  hcompose : Pg.HasAt compose (composeFuns compose)
  hinverse : Pg.HasAt inverse (invFuns inverse)
  happend : Pg.HasAt append (appendFuns append)
  hnf : Pg.HasAt nf (cosetNFFuns nf membership)
  hmembership : Pg.prims[membership]? = some (membershipPrim hm)

/-- The branch prepares its normalization data and then executes the child map. -/
def normStepF (prep tail : ℕ) : Expr :=
  .letE (.call prep (.var 0)) (.call tail (.var 1))

theorem normTailCost_mono (hm : Membership) (k : ℕ) {W W' : ℕ} (h : W ≤ W') :
    normTailCost hm k W ≤ normTailCost hm k W' := by
  have hp : piecesW k W ≤ piecesW k W' := by
    unfold piecesW; have := Nat.mul_le_mul_right (2 * pieceW k + 1) h; omega
  have hc : combInW k W ≤ combInW k W' := by unfold combInW; omega
  have ho : combOutW k W ≤ combOutW k W' := by
    unfold combOutW
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (by omega)) 2)
  have h1 := Nat.mul_le_mul h (normChildB_mono (Z := 10 * W + ansW k + 20 * (k + 1) ^ 2 + 40)
    (Z' := 10 * W' + ansW k + 20 * (k + 1) ^ 2 + 40) (by omega))
  have h2 : mapQK * (W + 1) * (W + piecesW k W + 1) ≤ mapQK * (W' + 1) * (W' + piecesW k W' + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have h3 := combCost_mono k hc
  have h4 := cosetNFCost_mono hm k ho
  unfold normTailCost
  omega

/-- Polynomial own work of the complete normalization branch. -/
noncomputable def normStepCost (hp : Preimage) (hst : PointwiseStab) (hm : Membership)
    (n m W : ℕ) : ℕ :=
  let K := normPrepCost hp hst hm n m W
  W + 4 * K + normTailCost hm n K + 10 * ansW n + 100

attribute [local irreducible] normGrow normPrepCost in
open Classical in
set_option maxHeartbeats 2000000 in
/-- The normalization branch computes a canonical answer of `Run.normalize`. Its own work
is polynomial, and all recursive work is charged to the children actually called. -/
theorem normStep_spec (R : Rest) (hp : Preimage) (hst : PointwiseStab) (hm : Membership)
    {Pg : Program} {F : Funs} (o : normOps Pg hp hst hm) (t : normTailAt Pg F hm)
    {f prep : ℕ} (hf : Pg.funs[f]? = some (normStepF prep t.tail))
    (hprep : Pg.funs[prep]? = some (normPrepF o))
    {Ω C : Type} [Finite Ω] {n m k sz : ℕ} (en : Ω ≃ Fin n) (cc : C → ℕ) {S : State Ω C}
    {gv dv xv yv hv rv fv hh rep hv' : Val}
    (hcan : Canon en cc (.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz]) S)
    (hs : (S.N : ℝ) ^ P₀.γ < S.size) (htr : S.Transitive) (hfl : ¬ S.FloorEntered)
    (Q : PrimitiveQuotient S) (hsm : ¬ Q.SmallZ P₀.smallExp)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)
    (hq : P₀.q₀ < m) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (hrep : normNumbered en Q rep) (hH : HierValC en hv' (Q.pre ++ Q.top :: Q.post))
    (hcall : ∀ (D : normCosetData Q e hS) (b : Bool),
      (∀ j, (normMode b = .cont ∧ ¬ ((Q.normAboveOf D.choice htr hq hkc hkl).child j).Transitive) ∨
        (normMode b = .giant ∧ ((Q.normAboveOf D.choice htr hq hkc hkl).child j).Transitive)) →
      ∀ (lv : Val), (∀ j, LabValStd en ((Q.normAboveOf D.choice htr hq hkc hkl).child j) lv
        ((Q.normAboveOf D.choice htr hq hkc hkl).childLabels j)) →
      ∀ j val, Canon en cc val ((Q.normAboveOf D.choice htr hq hkc hkl).child j) →
        FunAll Pg (F.get (normMode b)) (if b then .list [val, lv] else val)
          (R.iface.Post (normMode b) ((Q.normAboveOf D.choice htr hq hkc hkl).child j) en
            (if b then .list [val, lv] else val))) :
    FunAll Pg f (.list [.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz], rep, hv',
      .nat m, .nat k, encKSetTuples e]) (fun u cost =>
      ∃ (A : Set (Perm Ω)) (r : Run P₀ .cont S none A), r.kind = .normalize ∧ AnsC en u A ∧
        (cost : ℝ) ≤ normStepCost hp hst hm n m (Val.list
          [.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz], rep, hv',
            .nat m, .nat k, encKSetTuples e]).wt + R.iface.childCost r) := by
  let sv := Val.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz]
  let input := Val.list [sv, rep, hv', .nat m, .nat k, encKSetTuples e]
  let K := normPrepCost hp hst hm n m input.wt
  have hpr := normPrep_spec hp hst hm o hprep en cc hcan Q htr (dom_nonempty_of_large hs)
    e hS hq hkc hkl hrep hH
  have hpre := normBound_call (Det.var' (P := Pg) (env := [input]) (i := 0) rfl) hpr
  refine FunAll.intro hf (EvalAll.letE hpre fun pv cp hpv => ?_)
  obtain ⟨⟨D, Kv, lv, b, ts, rfl, hK, hL, hlen, hτ, hmode⟩, wp, cpr⟩ := hpv
  have hts := normTail_spec R hm t.htail t.hmap t.hchild t.hgather t.hcombine t.hstep
    t.hcompose t.hinverse t.happend t.hnf t.hmembership hcan hs htr hfl Q hsm
    D.choice hq hkc hkl b hmode hK hH hL ts hlen hτ (hcall D b hmode lv hL)
  refine EvalAll.call_funAll (Det.var' (i := 1) rfl) fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine hts.mono fun u cost hu => ?_
  obtain ⟨A, r, hk, hA, hc⟩ := hu
  refine ⟨A, r, hk, hA, ?_⟩
  have hu := hA.wt_le
  have ht := normTailCost_mono hm n wp
  have hown : cp + (ca + u.wt + 1) + u.wt + 1 +
      normTailCost hm n (Val.list [.list [sv, Kv, hv', lv, boolVal b],
        .list (ts.map encPerm)]).wt ≤ normStepCost hp hst hm n m input.wt := by
    change _ ≤ input.wt + 4 * K + normTailCost hm n K + 10 * ansW n + 100
    change (Val.list [.list [sv, Kv, hv', lv, boolVal b], .list (ts.map encPerm)]).wt ≤ K at wp
    change ca ≤ (Val.list [.list [sv, Kv, hv', lv, boolVal b], .list (ts.map encPerm)]).wt + 1 at hca
    change normTailCost hm n (Val.list [.list [sv, Kv, hv', lv, boolVal b],
      .list (ts.map encPerm)]).wt ≤ normTailCost hm n K at ht
    change cp ≤ input.wt + 1 + 2 * K + 1 at cpr
    omega
  have hown' := (Nat.cast_le (α := ℝ)).mpr hown
  push_cast at hown' ⊢
  linarith

end GI.Impl
