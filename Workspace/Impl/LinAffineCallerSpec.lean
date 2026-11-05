module

public import Workspace.Impl.LinAffineCallerMainSpec

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 24000

private theorem linAffineCallerTopCollect {W M S C cc1 cc2 cb out : ℕ}
    (h1 : cc1 ≤ 1000 * (W + 1)) (h2 : cc2 ≤ 1000 * (W + 1))
    (hC : C ≤ M + S) (hb : cb ≤ W + 2 * C + 2) (hw : out ≤ C) :
    cc1 + (cc2 + cb + out + 1) + out + 1 ≤ 10000000 * (W + M + S + 1) := by omega

private theorem linAffineCaller_top_call {P : Program} {f n : ℕ} {a : Val} {T : Set (Equiv.Perm (Fin n))}
    {M S C cc1 cc2 : ℕ} (h1 : cc1 ≤ 1000 * (a.wt + 1)) (h2 : cc2 ≤ 1000 * (a.wt + 1))
    (hC : C ≤ M + S) (hchild : FunAll P f a (fun out cost => CosetC n out T ∧ cost ≤ C)) :
    EvalAll P [a] (.call f (.var 0)) (fun out cost => CosetC n out T ∧
      cc1 + (cc2 + cost + out.wt + 1) + out.wt + 1 ≤ 10000000 * (a.wt + M + S + 1)) := by
  have hcall := normBound_call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hchild
  refine hcall.mono fun out cost ho => ⟨ho.1, ?_⟩
  have hc : cost ≤ a.wt + 2 * C + 2 := by have hh := ho.2.2; omega
  exact linAffineCallerTopCollect h1 h2 hC hc ho.2.1

set_option maxHeartbeats 1500000 in
theorem linAffineTransportAll_spec (hmem : Membership) (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jmem jm jv n d : ℕ} (hat : linAffineTransportAllAt P b jmem jm jv hmem hm hv)
    (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (v w : linFiniteVec m) (hs : IsSolvable ρ.range) (hmpos : ∀ i, 0 < m i)
    (hprime : ∀ i p, p.Prime → p ∣ m i → p ≤ max n 2)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g) :
    let a := tmGLAffIn gs m ρ c v w
    FunAll P b a (fun out cost => CosetC n out (tmGLAffTrans gs ρ c v w) ∧
      cost ≤ linAffineCallerCost hmem hm hv a.wt) := by
  let a := tmGLAffIn gs m ρ c v w
  let W := a.wt
  let M := linAffineCallerMainCost hmem hm hv W
  let S := linAffineCallerSmallCost W
  have hsource := linAffineCaller_source_bounds gs m ρ c v w
  have hn : n ≤ W := hsource.1
  have hlen : gs.length ≤ W := hsource.2.2.1
  have wg : (encGroup gs).wt < W := wt_le_wt_list (by simp [a, W, tmGLAffIn])
  have wl : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt := wt_le_wt_list (by simp [encGroup])
  have wn := wt_nat_le n
  have w0 : (Val.nat 0).wt = 2 := rfl
  have w1 : (Val.nat 1).wt = 3 := rfl
  have dvar := Det.var' (P := P) (env := [a]) (i := 0) rfl
  have dg := Det.get' dvar (Det.nat 0) (v := encGroup gs) rfl
  have dn := Det.get' dg (Det.nat 0) (v := .nat n) rfl
  have dgs := Det.get' dg (Det.nat 1) (v := .list ((1 :: gs).map encPerm)) rfl
  have dl := Det.length dgs
  simp only [List.length_map, List.length_cons] at dl
  have hsmall (hbot : gens gs = ⊥) : FunAll P (b + 2) a
      (fun out cost => CosetC n out (tmGLAffTrans gs ρ c v w) ∧ cost ≤ S) := by
    refine FunAll.mono (linAffineCallerSmall_spec hmem hm hv hat gs m hmpos ρ c v w) ?_
    intro out cost ho
    refine ⟨?_, ho.2⟩
    rw [ho.1]
    exact linAffineTrivial_coset gs m ρ c hc hbot v w
  apply FunAll.intro hat.top
  by_cases hn2 : 2 ≤ n
  · have dt0 := Det.arith' (op := .lt) (Det.nat 1) dn (z := 1) (by simp [GI.Machine.BinOp.eval]; omega)
    have dt := dt0.mono (show _ ≤ 1000 * (W + 1) by omega)
    apply EvalAll.ite dt (fun v cost ho => ⟨1, ho.1⟩)
    intro q cc1 hq
    obtain ⟨hq, hcc1⟩ := hq
    have hq' : q = 1 := Val.nat.inj hq
    subst q
    by_cases hgs : gs = []
    · have hlen0 : gs.length = 0 := by simp [hgs]
      have du0 := Det.arith' (op := .lt) (Det.nat 1) dl (z := 0) (by simp [GI.Machine.BinOp.eval, hlen0])
      have du := du0.mono (show _ ≤ 1000 * (W + 1) by omega)
      apply EvalAll.ite du (fun v cost ho => ⟨0, ho.1⟩)
      intro q cc2 hq
      obtain ⟨hq, hcc2⟩ := hq
      have hq' : q = 0 := Val.nat.inj hq
      subst q
      have hbot : gens gs = ⊥ := by simp [hgs, gens]
      exact linAffineCaller_top_call (M := M) (S := S) hcc1 hcc2 (Nat.le_add_left S M) (hsmall hbot)
    · have hlenpos : 0 < gs.length := List.length_pos_iff.mpr hgs
      have du0 := Det.arith' (op := .lt) (Det.nat 1) dl (z := 1) (by simp [GI.Machine.BinOp.eval]; omega)
      have du := du0.mono (show _ ≤ 1000 * (W + 1) by omega)
      apply EvalAll.ite du (fun v cost ho => ⟨1, ho.1⟩)
      intro q cc2 hq
      obtain ⟨hq, hcc2⟩ := hq
      have hq' : q = 1 := Val.nat.inj hq
      subst q
      have hprimeN : ∀ i p, p.Prime → p ∣ m i → p ≤ n := by
        intro i p hp hpm
        simpa only [max_eq_left hn2] using hprime i p hp hpm
      exact linAffineCaller_top_call (M := M) (S := S) hcc1 hcc2 (Nat.le_add_right M S)
        (linAffineCallerMain_spec hmem hm hv hat gs hgs hn2 m hmpos ρ c hc hs hprimeN v w)
  · have dt0 := Det.arith' (op := .lt) (Det.nat 1) dn (z := 0) (by simp [GI.Machine.BinOp.eval]; omega)
    have dt := dt0.mono (show _ ≤ 1000 * (W + 1) by omega)
    apply EvalAll.ite dt (fun v cost ho => ⟨0, ho.1⟩)
    intro q cc1 hq
    obtain ⟨hq, hcc1⟩ := hq
    have hq' : q = 0 := Val.nat.inj hq
    subst q
    have hbot := linAffineSmallCover_bot gs (show n ≤ 1 by omega)
    have hh := linAffineCaller_top_call (M := M) (S := S) (cc2 := 0) hcc1 (by omega)
      (Nat.le_add_left S M) (hsmall hbot)
    refine hh.mono fun out cost ho => ⟨ho.1, ?_⟩
    have hb := ho.2
    change _ ≤ linAffineCallerCost hmem hm hv W
    unfold linAffineCallerCost
    change _ ≤ 10000000 * (W + M + S + 1)
    omega

end GI.Impl
