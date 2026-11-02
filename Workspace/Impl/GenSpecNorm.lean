import Workspace.Impl.GenSpecStep
import Workspace.Impl.GenNormStepIH
import Workspace.Impl.GenNormStepCost

/-!
# The normalization branch of the general dispatcher

The branch (`branchE`) calls the normalization on `[v, x, w]`, where `x` is the output of the
exposure and `w = [1, m, l, 1, E]` the output of the case decision. The normalization program of
`GenNormStep.lean` (`normStepF`, `normStep_spec_of_IH`) takes `[v, rep, h', m, l, E]`. The adapter
`gsNormE` reads these six entries and calls it.

The own cost of the normalization, `normStepCost n m W'`, depends on the number of points `n`, the
point degree `m` of the factor and the input weight `W'`. `NormSpec` asks for a cost `Cn n W` in
the number of points and the weight `W` of `[v, x, w]` only. Here `m ≤ d ≤ n` and `W' ≤ 2 W + 10`,
so `gsCn n W`, which adds `normStepCost n m W'` over all such `m` and `W'`, bounds it. It is
monotone in `W` and uniformly polynomial (`gsCn_poly`).

`gs_normSpec`: `NormSpec` for the concrete interface `R.iface` of any `Rest` (the normalization
calls its children through `R.iface.IH`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encKSetTuples Preimage Membership PointwiseStab)

/-- The adapter: on `[v, x, w]`, call `fn` on `[v, x₁, x₂, w₁, w₂, w₄]`. -/
def gsNormE (fn : ℕ) : Expr :=
  .call fn (.snoc (.snoc (mk4 (arg 0) (.get (arg 1) (.nat 1)) (.get (arg 1) (.nat 2))
    (.get (arg 2) (.nat 1))) (.get (arg 2) (.nat 2))) (.get (arg 2) (.nat 4)))

/-- The normalization cost over all point degrees `m ≤ n + 2` and input weights `W' ≤ 2 W + 10`. -/
noncomputable def gsNormSum (hp : Preimage) (hst : PointwiseStab) (hm : Membership) (n W : ℕ) :
    ℕ :=
  ∑ m ∈ Finset.range (n + 3), ∑ W' ∈ Finset.range (2 * W + 11), normStepCost hp hst hm n m W'

/-- **The own cost of the normalization branch** as `NormSpec` takes it. -/
noncomputable def gsCn (hp : Preimage) (hst : PointwiseStab) (hm : Membership) (n W : ℕ) : ℕ :=
  gsNormSum hp hst hm n W + 100 * W + 2 * ansW n + 1000

theorem gsCn_mono (hp : Preimage) (hst : PointwiseStab) (hm : Membership) {n W W' : ℕ}
    (h : W ≤ W') : gsCn hp hst hm n W ≤ gsCn hp hst hm n W' := by
  have hs : gsNormSum hp hst hm n W ≤ gsNormSum hp hst hm n W' :=
    Finset.sum_le_sum fun m _ => Finset.sum_le_sum_of_subset
      (Finset.range_subset_range.2 (by omega))
  unfold gsCn
  omega

theorem gs_normStepCost_le (hp : Preimage) (hst : PointwiseStab) (hm : Membership) {n m W W' : ℕ}
    (hm' : m ≤ n + 2) (hW : W' ≤ 2 * W + 10) :
    normStepCost hp hst hm n m W' ≤ gsNormSum hp hst hm n W := by
  have h1 : normStepCost hp hst hm n m W' ≤
      ∑ W'' ∈ Finset.range (2 * W + 11), normStepCost hp hst hm n m W'' :=
    Finset.single_le_sum (f := fun W'' => normStepCost hp hst hm n m W'') (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (by omega))
  have h2 : ∑ W'' ∈ Finset.range (2 * W + 11), normStepCost hp hst hm n m W'' ≤
      gsNormSum hp hst hm n W :=
    Finset.single_le_sum (f := fun m => ∑ W'' ∈ Finset.range (2 * W + 11),
      normStepCost hp hst hm n m W'') (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  omega

/-- **`gsCn` is uniformly polynomial**: each of its at most `(n + 3)(2 W + 11)` terms is at most
`C (3 W + n + 15)^D` (`normStepCost_poly`). -/
theorem gsCn_poly (hp : Preimage) (hst : PointwiseStab) (hm : Membership) :
    PBU fun n W _ => gsCn hp hst hm n W := by
  obtain ⟨C, D, h⟩ := normStepCost_poly hp hst hm
  have hg : PBU fun n W _ => (n + 3) * ((2 * W + 11) * (C * (3 * W + 2 * n + 15) ^ D)) :=
    PBU.mul (PBU.addc PBU.k 3) (PBU.mul (PBU.addc (PBU.smul 2 PBU.W) 11)
      (PBU.smul C (PBU.pow (PBU.addc (PBU.add (PBU.smul 3 PBU.W) (PBU.smul 2 PBU.k)) 15) D)))
  have hpA : PBU (fun n _ _ => ansW n) := by unfold ansW groupW; norm_poly
  refine PBU.addc (PBU.add (PBU.add (PBU.mono hg fun n W _ => ?_) (PBU.smul 100 PBU.W))
    (PBU.smul 2 hpA)) 1000
  unfold gsNormSum
  have hterm : ∀ m ∈ Finset.range (n + 3), ∑ W' ∈ Finset.range (2 * W + 11),
      normStepCost hp hst hm n m W' ≤ (2 * W + 11) * (C * (3 * W + 2 * n + 15) ^ D) := by
    intro m hm'
    have := Finset.sum_le_card_nsmul (Finset.range (2 * W + 11))
      (fun W' => normStepCost hp hst hm n m W') (C * (3 * W + 2 * n + 15) ^ D) (by
        intro W' hW'
        have hb : normStepCost hp hst hm n m W' ≤ C * (W' + m + n + 2) ^ D := h n W' m
        refine hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ D))
        have := Finset.mem_range.1 hW'
        have := Finset.mem_range.1 hm'
        omega)
    simpa using this
  have := Finset.sum_le_card_nsmul (Finset.range (n + 3)) _ _ hterm
  simpa using this

/-- **`NormSpec` for the concrete interface**, from the normalization program
(`normStep_spec_of_IH`) behind the adapter `gsNormE`. -/
theorem gs_normSpec (R : Rest) (hp : Preimage) (hst : PointwiseStab) (hm : Membership)
    {Pg : Program} {F : Funs} (o : normOps Pg hp hst hm) (t : normTailAt Pg F hm)
    {fn prep fad : ℕ} (hfn : Pg.funs[fn]? = some (normStepF prep t.tail))
    (hprep : Pg.funs[prep]? = some (normPrepF o)) (had : Pg.funs[fad]? = some (gsNormE fn)) :
    NormSpec R.iface Pg F fad (gsCn hp hst hm) := by
  intro Ω C k e c hc gv dv xv yv hv rv fv hh N S hcan hgood hs htr hfl hIH Q hkc hkl x hx m l E
    hS hnz
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨gv', rep, hv', rfl, -, -, hnum, hH⟩ := hx
  set v := Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] with hvdef
  set x := Val.list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length] with hxdef
  set z := Val.list [.nat 1, .nat m, .nat l, .nat 1, encKSetTuples E] with hzdef
  set a := Val.list [v, x, z] with ha
  have wa := sum_wt_lt_wt_list [v, x, z]
  have wx := sum_wt_lt_wt_list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length]
  have wz := sum_wt_lt_wt_list [Val.nat 1, .nat m, .nat l, .nat 1, encKSetTuples E]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at wa wx wz
  have ex : (Val.list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length]).wt = x.wt := rfl
  have ez : (Val.list [Val.nat 1, .nat m, .nat l, .nat 1, encKSetTuples E]).wt = z.wt := rfl
  have ea : (Val.list [v, x, z]).wt = a.wt := rfl
  have d0 : Det Pg [a] (arg 0) v (2 * a.wt + 0 + 5) := Det.arg' rfl
  have d1 : Det Pg [a] (.get (arg 1) (.nat 1)) rep (2 * a.wt + 1 + 5 + (1 + 3) + rep.wt + 1) :=
    Det.get' (Det.arg' (j := 1) rfl) (Det.nat 1) rfl
  have d2 : Det Pg [a] (.get (arg 1) (.nat 2)) hv' (2 * a.wt + 1 + 5 + (2 + 3) + hv'.wt + 1) :=
    Det.get' (Det.arg' (j := 1) rfl) (Det.nat 2) rfl
  have d3 : Det Pg [a] (.get (arg 2) (.nat 1)) (.nat m)
      (2 * a.wt + 2 + 5 + (1 + 3) + (Val.nat m).wt + 1) :=
    Det.get' (Det.arg' (j := 2) rfl) (Det.nat 1) rfl
  have d4 : Det Pg [a] (.get (arg 2) (.nat 2)) (.nat l)
      (2 * a.wt + 2 + 5 + (2 + 3) + (Val.nat l).wt + 1) :=
    Det.get' (Det.arg' (j := 2) rfl) (Det.nat 2) rfl
  have d5 : Det Pg [a] (.get (arg 2) (.nat 4)) (encKSetTuples E)
      (2 * a.wt + 2 + 5 + (4 + 3) + (encKSetTuples E).wt + 1) :=
    Det.get' (Det.arg' (j := 2) rfl) (Det.nat 4) rfl
  have dargs := Det.snoc (Det.snoc (Det.mk4 d0 d1 d2 d3) d4) d5
  have winp : (Val.list [v, rep, hv', .nat m, .nat l, encKSetTuples E]).wt ≤ 2 * a.wt + 8 := by
    have := wt_list_le [v, rep, hv', .nat m, .nat l, encKSetTuples E]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    omega
  have w4 : (Val.list [v, rep, hv', .nat m]).wt ≤ (Val.list [v, rep, hv', .nat m, .nat l, encKSetTuples E]).wt :=
    wt_list_mono ⟨[.nat l, encKSetTuples E], rfl⟩
  have w5 : (Val.list ([v, rep, hv', .nat m] ++ [.nat l])).wt ≤ (Val.list [v, rep, hv', .nat m, .nat l, encKSetTuples E]).wt :=
    wt_list_mono ⟨[encKSetTuples E], rfl⟩
  have w6 : (Val.list ([v, rep, hv', .nat m] ++ [.nat l] ++ [encKSetTuples E])).wt = (Val.list [v, rep, hv', .nat m, .nat l, encKSetTuples E]).wt := rfl
  have hmk : m ≤ k + 2 := by
    obtain ⟨-, -, hmd, -⟩ := gs_kset_bounds Q E
    have := Q.d_le_card e
    omega
  refine FunAll.intro had (EvalAll.call_funAll dargs fun a' ca h => ?_)
  obtain ⟨rfl, hca⟩ := h
  refine (normStep_spec_of_IH R hp hst hm o t hfn hprep e c hc hgood hIH hcan hs htr hfl Q hnz
    E hS hkc hkl hnum hH).mono ?_
  rintro u cost ⟨A, rn, hk, hAu, hcost⟩
  refine ⟨A, rn, hk, hAu, ?_⟩
  have hn := gs_normStepCost_le hp hst hm (n := k) (W := a.wt) hmk (by omega : (Val.list [v, rep, hv', .nat m, .nat l, encKSetTuples E]).wt ≤ 2 * a.wt + 10)
  have hu := hAu.wt_le
  have := wt_nat_le m
  have := wt_nat_le l
  have key : ca + normStepCost hp hst hm k m (Val.list [v, rep, hv', .nat m, .nat l, encKSetTuples E]).wt + u.wt + 1 ≤ gsCn hp hst hm k a.wt := by
    unfold gsCn
    omega
  have key' := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at key' hcost ⊢
  linarith

end GI.Impl
