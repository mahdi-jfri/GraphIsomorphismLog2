module

public import Workspace.Impl.TermChainKer
public import Workspace.Impl.GMPRepsCost
public import Workspace.Impl.TermConj

@[expose] public section

/-!
# Single Step of the Top-Down Nonabelian-Chief Chain

Given `N ≤ U ≤ H ≤ Perm (Fin n)` where `H` normalizes `N` and `U` and `N` acts transitively on
`Fin n`, this file implements a single top-down step `tcStepBody` producing `N ≤ V ≤ U` normalized
by `H` such that:
- if `U = N`, then `V = N`;
- if `N < U` and `¬ (U ≤ ⁅U, U⁆ ⊔ N)`, then `V = ⁅U, U⁆ ⊔ N < U` (an abelian step);
- if `N < U` and `U ≤ ⁅U, U⁆ ⊔ N`, then:
  1. `obEntry` (`TermChainKer.lean`) produces `N ≤ Y < U` normalized by `U` of index
     `[U : Y] ≤ max (24!) (n ^ (1 + log₂ n)) * n ^ (1 + log₂ n)`;
  2. `tcGreedyEntry` with `A = U` produces a maximal proper `U`-normalized subgroup `M` of `U`
     containing `Y`, so `U / M` is nonabelian simple (`simple_and_noncomm_of_maximal`);
  3. `tcConjEntry` intersects `H`-conjugates of `M` until `H`-normalized, producing `N ≤ W < U`
     normalized by `H` with `[U : W] ≤ n ^ (1 + log₂ n)` (`isSimpleInter_index_le`);
  4. `tcGreedyEntry` with `A = H` produces a maximal proper `H`-normalized subgroup `V` of `U`
     containing `W` (a nonabelian chief step of `H`).
-/

set_option autoImplicit false

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)
open scoped commutatorElement

variable {n : ℕ}

/-! ### 1. Group-theoretic and cost monotonicity helpers -/

theorem comm_normalized_of_normalized {H U : Subgroup (Perm (Fin n))}
    (hnU : ∀ g ∈ H, ∀ x ∈ U, g * x * g⁻¹ ∈ U) :
    ∀ g ∈ H, ∀ x ∈ ⁅U, U⁆, g * x * g⁻¹ ∈ ⁅U, U⁆ := by
  intro g hg
  have hle : ⁅U, U⁆ ≤ ⁅U, U⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    change g * ⁅a, b⁆ * g⁻¹ ∈ ⁅U, U⁆
    have h1 : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact Subgroup.commutator_mem_commutator (hnU g hg a ha) (hnU g hg b hb)
  intro x hx
  exact hle hx

theorem comm_self_le (U : Subgroup (Perm (Fin n))) : ⁅U, U⁆ ≤ U := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact U.mul_mem (U.mul_mem (U.mul_mem hx hy) (U.inv_mem hx)) (U.inv_mem hy)

theorem sup_normalized_of_both {H A B : Subgroup (Perm (Fin n))}
    (hnA : ∀ g ∈ H, ∀ x ∈ A, g * x * g⁻¹ ∈ A)
    (hnB : ∀ g ∈ H, ∀ x ∈ B, g * x * g⁻¹ ∈ B) :
    ∀ g ∈ H, ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ A ⊔ B :=
  fun g hg x hx => sup_normalized_of_normalized le_rfl hnB hnA g (Subgroup.mem_sup_left hg) x hx

theorem gens_snoc_eq (vs : List (Perm (Fin n))) (r : Perm (Fin n)) :
    gens (vs ++ [r]) = gens vs ⊔ Subgroup.closure {r} := by
  apply le_antisymm
  · unfold gens
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure hx)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
  · refine sup_le (fun x hx => ?_) ?_
    · refine Subgroup.closure_mono (fun y hy => ?_) hx
      exact List.mem_append_left [r] hy
    · rw [Subgroup.closure_le, Set.singleton_subset_iff]
      exact Subgroup.subset_closure (List.mem_append_right vs (List.mem_singleton.mpr rfl))

theorem greedyMaxFold_snoc (A U W : Subgroup (Perm (Fin n)))
    (xs : List (Perm (Fin n))) (r : Perm (Fin n)) :
    greedyMaxFold A U W (xs ++ [r]) = greedyMaxStep A U (greedyMaxFold A U W xs) r := by
  simp [greedyMaxFold, List.foldl_append]

theorem gens_map_conj (h : Perm (Fin n)) (ws : List (Perm (Fin n))) :
    gens (ws.map (fun x => h * x * h⁻¹)) = conjSub h (gens ws) := by
  apply le_antisymm
  · unfold gens
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact mem_conjSub_iff.mpr ⟨y, Subgroup.subset_closure hy, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_conjSub_iff.mp hx
    have hle : gens ws ≤ (gens (ws.map (fun z => h * z * h⁻¹))).comap
        (MulAut.conj h).toMonoidHom := by
      unfold gens
      rw [Subgroup.closure_le]
      intro z hz
      change h * z * h⁻¹ ∈ gens (ws.map (fun w => h * w * h⁻¹))
      exact Subgroup.subset_closure (List.mem_map.mpr ⟨z, hz, rfl⟩)
    exact hle hy

theorem isSimpleInter_conjSub {H U N W : Subgroup (Perm (Fin n))}
    (hnU : ∀ g ∈ H, ∀ x ∈ U, g * x * g⁻¹ ∈ U)
    (hnN : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    {h : Perm (Fin n)} (hh : h ∈ H) (hW : IsSimpleInter U N W) :
    IsSimpleInter U N (conjSub h W) := by
  obtain ⟨Ms, hne, rfl, hMs⟩ := hW
  have hh_inv : h⁻¹ ∈ H := H.inv_mem hh
  have hU1 : ∀ x ∈ U, h * x * h⁻¹ ∈ U := hnU h hh
  have hU2 : ∀ x ∈ U, h⁻¹ * x * h ∈ U :=
    fun x hx => by simpa [mul_assoc] using hnU h⁻¹ hh_inv x hx
  refine ⟨Ms.map (conjSub h), by simp [hne], conjSub_foldr_inf hU1 hU2 Ms, ?_⟩
  intro M hM
  obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.mp hM
  exact isNonabelianSimpleNormal_conjSub hnU hnN hh (hMs M₀ hM₀)

theorem conjPass_snoc (W : Subgroup (Perm (Fin n)))
    (xs : List (Perm (Fin n))) (h : Perm (Fin n)) :
    conjPass W (xs ++ [h]) = conjStep (conjPass W xs) h := by
  simp [conjPass, List.foldl_append]

/-! ### 2. Greedy Maximalization (`tcGreedyStep` and `tcGreedyEntry`) -/

/-- **One step of greedy maximalization** on `[[encGroup as, encGroup us], encGroup vs, encPerm r]`. -/
def tcGreedyStep (mg le jnc : ℕ) : Expr :=
  .letE (mk2 (.get (arg 1) (.nat 0)) (.snoc (.get (arg 1) (.nat 1)) (arg 2)))
  (.letE (.prim jnc (mk2 (.get (arg 0) (.nat 0)) (.var 1)))
  (.letE (.call mg (mk2 (.get (arg 1) (.nat 0)) (.var 2)))
  (.letE (.call le (mk2 (.var 3) (.get (arg 0) (.nat 1))))
    (.ite (.var 4) (arg 1) (.var 3)))))

/-- **Entry of greedy maximalization** on `[encGroup as, encGroup us, encGroup ws]`. -/
def tcGreedyEntry (gr fl : ℕ) : Expr :=
  .letE (.call gr (mk2 (arg 2) (.get (arg 1) (.nat 1))))
    (.call fl (mk3 (mk2 (arg 0) (arg 1)) (.var 1) (arg 2)))

/-- Where `tcGreedyEntry` and its subroutines sit in the program. -/
structure TcGreedyAt (P : Program) (f gr fl gs mg le jnc jmem : ℕ)
    (hnc : NormalClosure) (hmem : Membership) : Prop where
  entry : P.funs[f]? = some (tcGreedyEntry gr fl)
  reps : GmpRepsAt P hmem gr jmem
  fold : P.HasAt fl (foldlFuns fl gs)
  step : P.funs[gs]? = some (tcGreedyStep mg le jnc)
  mg : P.HasAt mg (mkGroupFuns mg)
  le : P.HasAt le (leFuns le jmem)
  jnc_eq : P.prims[jnc]? = some (normalClosurePrim hnc)
  jmem_eq : P.prims[jmem]? = some (membershipPrim hmem)

/-- Cost of a single `tcGreedyStep` call on degree `n` with `≤ n ^ 2` generators. -/
noncomputable def tcGreedyStepCost (hnc : NormalClosure) (hmem : Membership) (n : ℕ) : ℕ :=
  (normalClosurePrim hnc).boundSize (10 ^ 4 * (n + 1) ^ 6) +
    10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) +
    10 ^ 19 * (n + 1) ^ 18

/-- Postcondition of `tcGreedyStep`. -/
def TcGreedyStepOut (A U V : Subgroup (Perm (Fin n))) (r : Perm (Fin n)) (w : Val) : Prop :=
  ∃ vs' : List (Perm (Fin n)), w = encGroup vs' ∧ vs'.length ≤ n ^ 2 ∧
    gens vs' = greedyMaxStep A U V r

theorem TcGreedyStepOut.wt_le {A U V : Subgroup (Perm (Fin n))} {r : Perm (Fin n)} {w : Val}
    (h : TcGreedyStepOut A U V r w) : w.wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨vs', rfl, hl, -⟩ := h
  exact wt_encGroup_le_sq hl

/-- **Specification of `tcGreedyStep`.** -/
theorem tcGreedyStep_spec {hnc : NormalClosure} {hmem : Membership} {P : Program}
    {gs mg le jnc jmem : ℕ}
    (hstep : P.funs[gs]? = some (tcGreedyStep mg le jnc))
    (hmg : P.HasAt mg (mkGroupFuns mg))
    (hle : P.HasAt le (leFuns le jmem))
    (hjnc : P.prims[jnc]? = some (normalClosurePrim hnc))
    (hjmem : P.prims[jmem]? = some (membershipPrim hmem))
    {as us vs : List (Perm (Fin n))} (r : Perm (Fin n))
    (hVU : gens vs ≤ gens us) (hUA : gens us ≤ gens as) (hrU : r ∈ gens us)
    (hl_as : as.length ≤ n ^ 2) (hl_us : us.length ≤ n ^ 2) (hl_vs : vs.length ≤ n ^ 2) :
    FunAll P gs (.list [.list [encGroup as, encGroup us], encGroup vs, encPerm r])
      (fun w c => TcGreedyStepOut (gens as) (gens us) (gens vs) r w ∧
        c ≤ tcGreedyStepCost hnc hmem n) := by
  classical
  set ctx := Val.list [encGroup as, encGroup us]
  set inp := Val.list [ctx, encGroup vs, encPerm r]
  have was := wt_encGroup_le_sq hl_as
  have wus := wt_encGroup_le_sq hl_us
  have wvs := wt_encGroup_le_sq hl_vs
  have wr := wt_encPerm_le r
  have wn := wt_nat_le n
  have wctx := wt_list2_le (encGroup as) (encGroup us)
  have winp := wt_list3_le ctx (encGroup vs) (encPerm r)
  have p12 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p69 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have p918 : (n + 1) ^ 9 ≤ (n + 1) ^ 18 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  -- step 1: `v1 = encGroup (vs ++ [r])`
  have dvs0 := Det.arg' (P := P) (vs := [ctx, encGroup vs, encPerm r]) (rest := []) (j := 1) rfl
  have dn0 := Det.get' dvs0 (Det.nat 0) (v := .nat n)
    (show [Val.nat n, Val.list ((1 :: vs).map encPerm)][0]? = some (.nat n) from rfl)
  have dvsL := Det.get' dvs0 (Det.nat 1) (v := .list ((1 :: vs).map encPerm))
    (show [Val.nat n, Val.list ((1 :: vs).map encPerm)][1]? = some _ from rfl)
  have dr0 := Det.arg' (P := P) (vs := [ctx, encGroup vs, encPerm r]) (rest := []) (j := 2) rfl
  have dv1_raw := Det.mk2 dn0 (Det.snoc dvsL dr0)
  rw [← encGroup_snoc vs r] at dv1_raw
  have hS_rvs : ((vs ++ [r]).length + 2) * (n + 1) ≤ 4 * (n + 1) ^ 3 := by
    have : (vs ++ [r]).length + 2 ≤ 4 * (n + 1) ^ 2 := by
      simp only [List.length_append, List.length_singleton]
      have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega
    calc ((vs ++ [r]).length + 2) * (n + 1) ≤ 4 * (n + 1) ^ 2 * (n + 1) :=
          Nat.mul_le_mul_right _ this
      _ = 4 * (n + 1) ^ 3 := by ring
  have wv1 : (encGroup (vs ++ [r])).wt ≤ 1300 * (n + 1) ^ 6 := by
    have w1 := wt_encGroup_le (vs ++ [r])
    have hS2 : (((vs ++ [r]).length + 2) * (n + 1)) ^ 2 ≤ 16 * (n + 1) ^ 6 := by
      calc (((vs ++ [r]).length + 2) * (n + 1)) ^ 2 ≤ (4 * (n + 1) ^ 3) ^ 2 :=
            Nat.pow_le_pow_left hS_rvs 2
        _ = 16 * (n + 1) ^ 6 := by ring
    omega
  have w_vsL : (Val.list ((1 :: vs).map encPerm)).wt < (encGroup vs).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: vs).map encPerm)]) (by simp)
  have w_snoc := wt_list_snoc_le ((1 :: vs).map encPerm) (encPerm r)
  have dv1 : Det P [inp]
      (mk2 (.get (arg 1) (.nat 0)) (.snoc (.get (arg 1) (.nat 1)) (arg 2)))
      (encGroup (vs ++ [r])) (10 ^ 8 * (n + 1) ^ 9) := by
    refine dv1_raw.mono ?_
    have e_inp : (Val.list [ctx, encGroup vs, encPerm r]).wt = inp.wt := rfl
    have e_ctx : (Val.list [encGroup as, encGroup us]).wt = ctx.wt := rfl
    clear_value ctx inp
    omega
  set v1 := encGroup (vs ++ [r])
  -- step 2: `v2 = normalClosurePrim` on `[encGroup as, v1]`
  have dctx1 := Det.arg' (P := P) (vs := [ctx, encGroup vs, encPerm r])
    (rest := [v1]) (j := 0) rfl
  have das1 := Det.get' dctx1 (Det.nat 0) (v := encGroup as) rfl
  have dv1_var := Det.var' (P := P) (env := [inp, v1]) (i := 1) (v := v1) rfl
  have dnc_arg := Det.mk2 das1 dv1_var
  have hK_eq : gens (vs ++ [r]) = gens vs ⊔ Subgroup.closure {r} :=
    gens_snoc_eq vs r
  have hKA : gens vs ⊔ Subgroup.closure {r} ≤ gens as := by
    refine sup_le (hVU.trans hUA) ?_
    rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact hUA hrU
  have hnc_raw := normalClosure_call hnc hjnc dnc_arg ⟨as, rfl, rfl⟩
  rw [camNormClosure_eq_of_gens hK_eq hKA] at hnc_raw
  have sv2 : EvalAll P [inp, v1] (.prim jnc (mk2 (.get (arg 0) (.nat 0)) (.var 1)))
      (fun v2 c => GensVal n v2 (camNormClosure (gens as) (gens vs ⊔ Subgroup.closure {r})) ∧
        c ≤ (normalClosurePrim hnc).boundSize (10 ^ 4 * (n + 1) ^ 6) + 10 ^ 5 * (n + 1) ^ 6) := by
    refine hnc_raw.mono fun v2 c hv2 => ⟨hv2.1, ?_⟩
    clear hnc_raw dnc_arg dv1_var das1 dctx1 dv1
    have w2 := wt_list2_le (encGroup as) v1
    have hsz : (Val.list [encGroup as, v1]).size ≤ 10 ^ 4 * (n + 1) ^ 6 :=
      (Val.size_le_wt _).trans (by omega)
    have hb := (normalClosurePrim hnc).bound_le hsz
    have hc := hv2.2
    have e_inp : (Val.list [ctx, encGroup vs, encPerm r]).wt = inp.wt := rfl
    have e_ctx : (Val.list [encGroup as, encGroup us]).wt = ctx.wt := rfl
    have e_nc : (normalClosurePrim hnc).bound (Val.list [encGroup as, encGroup (vs ++ [r])]) =
      (normalClosurePrim hnc).bound (Val.list [encGroup as, v1]) := rfl
    clear_value ctx inp v1
    omega
  -- steps 3..5 inside `ob_letAll`
  have s3_5 : ∀ v2, GensVal n v2 (camNormClosure (gens as) (gens vs ⊔ Subgroup.closure {r})) →
      EvalAll P ([inp, v1] ++ [v2])
        (.letE (.call mg (mk2 (.get (arg 1) (.nat 0)) (.var 2)))
        (.letE (.call le (mk2 (.var 3) (.get (arg 0) (.nat 1))))
          (.ite (.var 4) (arg 1) (.var 3))))
        (fun w c => TcGreedyStepOut (gens as) (gens us) (gens vs) r w ∧
          c ≤ 10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) +
            2 * 10 ^ 17 * (n + 1) ^ 18) := by
    intro v2 hv2
    obtain ⟨vs', rfl, hl_vs', hmg_vs', hG_vs', wvs'⟩ := mkGroup_gensVal hmg hv2
    have hgens_vs' : gens vs' = camNormClosure (gens as) (gens vs ⊔ Subgroup.closure {r}) := by
      obtain ⟨_, h1, h2⟩ := hG_vs'
      rw [← h2, encGroup_injective h1]
    set env2 := [inp, v1, .list (vs'.map encPerm)]
    have dvs2 := Det.arg' (P := P) (vs := [ctx, encGroup vs, encPerm r])
      (rest := [v1, .list (vs'.map encPerm)]) (j := 1) rfl
    have dn2 := Det.get' dvs2 (Det.nat 0) (v := .nat n)
      (show [Val.nat n, Val.list ((1 :: vs).map encPerm)][0]? = some (.nat n) from rfl)
    have dv2_var := Det.var' (P := P) (env := env2) (i := 2) (v := .list (vs'.map encPerm)) rfl
    have dv3_raw := Det.call (Det.mk2 dn2 dv2_var) hmg_vs'
    have w_vs'L : (Val.list (vs'.map encPerm)).wt ≤ (encGroup vs').wt := wt_gens_le_encGroup vs'
    have w2_v3 := wt_list2_le (.nat n) (.list (vs'.map encPerm))
    have dv3 : Det P env2 (.call mg (mk2 (.get (arg 1) (.nat 0)) (.var 2)))
        (encGroup vs') (10 ^ 7 * (n + 1) ^ 9) := by
      refine dv3_raw.mono ?_
      have e_inp : (Val.list [ctx, encGroup vs, encPerm r]).wt = inp.wt := rfl
      have e_ctx : (Val.list [encGroup as, encGroup us]).wt = ctx.wt := rfl
      simp only [mkGroupK] at *
      clear_value ctx inp v1 env2
      omega
    set v3 := encGroup vs'
    set env3 := env2 ++ [v3]
    have dv3_var := Det.var' (P := P) (env := env3) (i := 3) (v := v3) rfl
    have dctx3 := Det.arg' (P := P) (vs := [ctx, encGroup vs, encPerm r])
      (rest := [v1, .list (vs'.map encPerm), v3]) (j := 0) rfl
    have dus3 := Det.get' dctx3 (Det.nat 1) (v := encGroup us) rfl
    have dv4 := ob_le_det hmem hle hjmem hG_vs' us dv3_var dus3
      (by omega) (by omega)
    set b := decide (gens us ≤ camNormClosure (gens as) (gens vs ⊔ Subgroup.closure {r}))
    set env4 := env3 ++ [boolVal b]
    have dv4_var := Det.var' (P := P) (env := env4) (i := 4) (v := boolVal b) rfl
    have db_eq : boolVal b = .nat (if b then 1 else 0) := by cases b <;> rfl
    rw [db_eq] at dv4_var
    have hite : EvalAll P env4 (.ite (.var 4) (arg 1) (.var 3))
        (fun w c => TcGreedyStepOut (gens as) (gens us) (gens vs) r w ∧
          c ≤ 10 ^ 5 * (n + 1) ^ 6) := by
      refine (sup_ite dv4_var
        (R := fun w ce => TcGreedyStepOut (gens as) (gens us) (gens vs) r w ∧
          ce ≤ 2 * 10 ^ 4 * (n + 1) ^ 6)
        (fun ht => ?_) (fun he => ?_)).mono fun w c h => ?_
      · have hb_true : gens us ≤ camNormClosure (gens as) (gens vs ⊔ Subgroup.closure {r}) := by
          by_contra hnot; simp [b, hnot] at ht
        have darg1 := Det.arg' (P := P) (vs := [ctx, encGroup vs, encPerm r])
          (rest := [v1, .list (vs'.map encPerm), v3, boolVal b]) (j := 1) rfl
        refine darg1.post fun c hc => ⟨⟨vs, rfl, hl_vs, ?_⟩, ?_⟩
        · simp [greedyMaxStep, hb_true]
        · have e_inp : (Val.list [ctx, encGroup vs, encPerm r]).wt = inp.wt := rfl
          have e_ctx : (Val.list [encGroup as, encGroup us]).wt = ctx.wt := rfl
          clear_value ctx inp v1 v3 b env2 env3 env4
          omega
      · have hb_false : ¬ (gens us ≤ camNormClosure (gens as) (gens vs ⊔ Subgroup.closure {r})) := by
          intro hle'; simp [b, hle'] at he
        have dv3' := Det.var' (P := P) (env := env4) (i := 3) (v := v3) rfl
        refine dv3'.post fun c hc => ⟨⟨vs', rfl, hl_vs', ?_⟩, ?_⟩
        · simp [greedyMaxStep, hb_false, hgens_vs']
        · have ev3 : v3.wt = (encGroup vs').wt := rfl
          clear_value ctx inp v1 v3 b env2 env3 env4
          omega
      · obtain ⟨ce, ⟨hout, hce⟩, htot⟩ := h
        have hw_out := hout.wt_le
        have wb : (Val.nat (if b = true then 1 else 0)).wt ≤ 3 := by
          split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
        have e_inp : (Val.list [ctx, encGroup vs, encPerm r]).wt = inp.wt := rfl
        have e_ctx : (Val.list [encGroup as, encGroup us]).wt = ctx.wt := rfl
        refine ⟨hout, ?_⟩
        clear_value ctx inp v1 v3 b env2 env3 env4
        omega
    refine (ob_letDet TcGreedyStepOut.wt_le dv3
      (ob_letDet TcGreedyStepOut.wt_le dv4 hite)).mono fun w c h => ?_
    obtain ⟨hout, hc⟩ := h
    refine ⟨hout, ?_⟩
    have e_inp : (Val.list [ctx, encGroup vs, encPerm r]).wt = inp.wt := rfl
    have e_ctx : (Val.list [encGroup as, encGroup us]).wt = ctx.wt := rfl
    clear_value ctx inp v1 v3 b env2 env3 env4
    generalize 10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) = MB at *
    omega
  refine FunAll.intro hstep
    ((ob_letDet TcGreedyStepOut.wt_le dv1 (ob_letAll TcGreedyStepOut.wt_le sv2 s3_5)).mono
      fun w c h => ?_)
  clear s3_5 sv2 hnc_raw dnc_arg dv1_var das1 dctx1 dv1 dv1_raw dr0 dvsL dn0 dvs0
  obtain ⟨hout, hc⟩ := h
  refine ⟨hout, ?_⟩
  unfold tcGreedyStepCost
  clear_value ctx inp v1
  generalize (normalClosurePrim hnc).boundSize (10 ^ 4 * (n + 1) ^ 6) = NC at *
  generalize 10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) = MB at *
  omega

/-- Loop invariant for `foldlFuns` in `tcGreedyEntry`. -/
def TcGreedyInv (A U W : Subgroup (Perm (Fin n))) (rs : List (Perm (Fin n)))
    (i : ℕ) (acc : Val) : Prop :=
  ∃ vs : List (Perm (Fin n)), acc = encGroup vs ∧ vs.length ≤ n ^ 2 ∧
    gens vs = greedyMaxFold A U W (rs.take i)

theorem TcGreedyInv.wt_le {A U W : Subgroup (Perm (Fin n))} {rs : List (Perm (Fin n))}
    {i : ℕ} {acc : Val} (h : TcGreedyInv A U W rs i acc) : acc.wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨vs, rfl, hl, -⟩ := h
  exact wt_encGroup_le_sq hl

/-- Cost bound of `tcGreedyEntry` when `[U : W] ≤ q`. -/
noncomputable def tcGreedyCost (hnc : NormalClosure) (hmem : Membership) (n q : ℕ) : ℕ :=
  gmpRepsCost hmem (2000 * (n + 1) ^ 6) q +
    (q + 1) * tcGreedyStepCost hnc hmem n +
    10 ^ 10 * ((q + 1) ^ 2 * (n + 1) ^ 6)

/-- **Specification of `tcGreedyEntry`.** -/
theorem tcGreedyEntry_spec {hnc : NormalClosure} {hmem : Membership} {P : Program}
    {f gr fl gs mg le jnc jmem : ℕ}
    (hP : TcGreedyAt P f gr fl gs mg le jnc jmem hnc hmem)
    {as us ws : List (Perm (Fin n))} {q : ℕ}
    (hWU : gens ws ≤ gens us) (hUA : gens us ≤ gens as) (hnot : ¬ (gens us ≤ gens ws))
    (hnU : ∀ g ∈ gens as, ∀ x ∈ gens us, g * x * g⁻¹ ∈ gens us)
    (hnW : ∀ g ∈ gens as, ∀ x ∈ gens ws, g * x * g⁻¹ ∈ gens ws)
    (hq : ((gens ws).subgroupOf (gens us)).index ≤ q)
    (hl_as : as.length ≤ n ^ 2) (hl_us : us.length ≤ n ^ 2) (hl_ws : ws.length ≤ n ^ 2) :
    FunAll P f (.list [encGroup as, encGroup us, encGroup ws])
      (fun w c =>
        (∃ vs : List (Perm (Fin n)), w = encGroup vs ∧ vs.length ≤ n ^ 2 ∧
          gens ws ≤ gens vs ∧ gens vs ≤ gens us ∧ ¬ (gens us ≤ gens vs) ∧
          (∀ g ∈ gens as, ∀ x ∈ gens vs, g * x * g⁻¹ ∈ gens vs) ∧
          (∀ K : Subgroup (Perm (Fin n)), gens vs ≤ K → K ≤ gens us →
            (∀ g ∈ gens as, ∀ x ∈ K, g * x * g⁻¹ ∈ K) → K = gens vs ∨ K = gens us)) ∧
        c ≤ tcGreedyCost hnc hmem n q) := by
  set inp := Val.list [encGroup as, encGroup us, encGroup ws]
  have was := wt_encGroup_le_sq hl_as
  have wus := wt_encGroup_le_sq hl_us
  have wws := wt_encGroup_le_sq hl_ws
  have winp := wt_list3_le (encGroup as) (encGroup us) (encGroup ws)
  have w_usL : (Val.list ((1 :: us).map encPerm)).wt < (encGroup us).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: us).map encPerm)]) (by simp)
  have p12 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  -- step 1: `gmpRepsFuns` on `[encGroup ws, .list ((1 :: us).map encPerm)]`
  have dws0 := Det.arg' (P := P) (vs := [encGroup as, encGroup us, encGroup ws])
    (rest := []) (j := 2) rfl
  have dus0 := Det.arg' (P := P) (vs := [encGroup as, encGroup us, encGroup ws])
    (rest := []) (j := 1) rfl
  have dusL := Det.get' dus0 (Det.nat 1) (v := .list ((1 :: us).map encPerm))
    (show [Val.nat n, Val.list ((1 :: us).map encPerm)][1]? = some _ from rfl)
  have dgr_arg := Det.mk2 dws0 dusL
  have hgr_raw := gmpReps_spec hP.reps ws (1 :: us)
  rw [gens_cons_one] at hgr_raw
  have w_gr_arg := wt_list2_le (encGroup ws) (.list ((1 :: us).map encPerm))
  have s1 : EvalAll P [inp] (.call gr (mk2 (arg 2) (.get (arg 1) (.nat 1))))
      (fun v1 c1 =>
        (∃ rs : List (Perm (Fin n)), v1 = .list (rs.map encPerm) ∧
          GmpCosetReps (gens us) (gens ws) rs) ∧
        c1 ≤ gmpRepsCost hmem (2000 * (n + 1) ^ 6) q + 10 ^ 6 * ((q + 1) * (n + 1) ^ 6)) := by
    refine EvalAll.call_funAll dgr_arg fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine hgr_raw.mono fun w cb hw => ?_
    obtain ⟨rs, rfl, hrs, hcb⟩ := hw
    refine ⟨⟨rs, rfl, hrs⟩, ?_⟩
    clear hgr_raw dgr_arg dusL dus0 dws0
    have hgm := gmpRepsCost_mono hmem
      (show (Val.list [encGroup ws, .list ((1 :: us).map encPerm)]).wt ≤ 2000 * (n + 1) ^ 6 by omega)
      hq
    have hrs_len : rs.length ≤ q := hrs.length.le.trans hq
    have wrs := GI.Lang.wt_list_le_of (rs.map encPerm) (c := 4 * (n + 1) ^ 2) (by
      intro v hv; obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hv; exact wt_encPerm_le σ)
    simp only [List.length_map] at wrs
    have hqn : (n + 1) ^ 6 ≤ (q + 1) * (n + 1) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
    have hrs_wt : rs.length * (2 * (4 * (n + 1) ^ 2) + 1) ≤ 9 * ((q + 1) * (n + 1) ^ 6) := by
      calc rs.length * (2 * (4 * (n + 1) ^ 2) + 1) ≤ (q + 1) * (9 * (n + 1) ^ 6) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 9 * ((q + 1) * (n + 1) ^ 6) := by ring
    have hq1 : 1 ≤ (q + 1) * (n + 1) ^ 6 := Nat.mul_pos (by omega) (by omega)
    have e_inp : (Val.list [encGroup as, encGroup us, encGroup ws]).wt = inp.wt := rfl
    clear_value inp
    generalize gmpRepsCost hmem (2000 * (n + 1) ^ 6) q = GRC at *
    generalize gmpRepsCost hmem (Val.list [encGroup ws, .list ((1 :: us).map encPerm)]).wt
      (((gens ws).subgroupOf (gens us)).index) = GRC0 at *
    omega
  -- step 2: `foldlFuns` over `rs`
  refine FunAll.intro hP.entry
    (EvalAll.letE (Ra := fun v1 c1 =>
      (∃ rs : List (Perm (Fin n)), v1 = .list (rs.map encPerm) ∧
        GmpCosetReps (gens us) (gens ws) rs) ∧
      c1 ≤ gmpRepsCost hmem (2000 * (n + 1) ^ 6) q + 10 ^ 6 * ((q + 1) * (n + 1) ^ 6))
      s1 fun v1 c1 hv1 => ?_)
  clear s1 hgr_raw dgr_arg dusL dus0 dws0
  obtain ⟨⟨rs, rfl, hrs⟩, hc1⟩ := hv1
  have hrs_len : rs.length ≤ q := hrs.length.le.trans hq
  set c_fl := Val.list [encGroup as, encGroup us]
  have h0 : TcGreedyInv (gens as) (gens us) (gens ws) rs 0 (encGroup ws) :=
    ⟨ws, rfl, hl_ws, rfl⟩
  have hstep_fl : ∀ i acc (hi : i < (rs.map encPerm).length),
      TcGreedyInv (gens as) (gens us) (gens ws) rs i acc →
      FunAll P gs (.list [c_fl, acc, (rs.map encPerm)[i]])
        (fun w cost => TcGreedyInv (gens as) (gens us) (gens ws) rs (i + 1) w ∧
          cost ≤ tcGreedyStepCost hnc hmem n) := by
    intro i acc hi hinv
    simp only [List.length_map] at hi
    obtain ⟨vs, rfl, hl_vs, hgens_vs⟩ := hinv
    have h_elem : (rs.map encPerm)[i]'(by simp [hi]) = encPerm (rs[i]'hi) := List.getElem_map ..
    rw [h_elem]
    have hrs_take : ∀ r ∈ rs.take i, r ∈ gens us :=
      fun r hr => hrs.sub r (List.mem_of_mem_take hr)
    have hVU : gens vs ≤ gens us := by
      rw [hgens_vs]
      exact (greedyMaxFold_props hWU hnot hnU hnW hrs_take).2.1
    have hrU : rs[i]'hi ∈ gens us := hrs.sub _ (List.getElem_mem hi)
    refine (tcGreedyStep_spec hP.step hP.mg hP.le hP.jnc_eq hP.jmem_eq (rs[i]'hi)
      hVU hUA hrU hl_as hl_us hl_vs).mono fun w cost hw => ⟨?_, hw.2⟩
    obtain ⟨vs', rfl, hl_vs', hgens_vs'⟩ := hw.1
    refine ⟨vs', rfl, hl_vs', ?_⟩
    rw [hgens_vs', hgens_vs, List.take_add_one, List.getElem?_eq_getElem hi,
      Option.toList_some, greedyMaxFold_snoc]
  have hfl := foldl_spec hP.fold (c := c_fl) (xs := rs.map encPerm) (acc0 := encGroup ws)
    (M := 320 * (n + 1) ^ 6) (B := fun _ => tcGreedyStepCost hnc hmem n)
    h0 (fun _ _ _ hinv => hinv.wt_le) hstep_fl
  set env1 := [inp, .list (rs.map encPerm)]
  have das1 := Det.arg' (P := P) (vs := [encGroup as, encGroup us, encGroup ws])
    (rest := [.list (rs.map encPerm)]) (j := 0) rfl
  have dus1 := Det.arg' (P := P) (vs := [encGroup as, encGroup us, encGroup ws])
    (rest := [.list (rs.map encPerm)]) (j := 1) rfl
  have dv1_var := Det.var' (P := P) (env := env1) (i := 1) (v := .list (rs.map encPerm)) rfl
  have dws1 := Det.arg' (P := P) (vs := [encGroup as, encGroup us, encGroup ws])
    (rest := [.list (rs.map encPerm)]) (j := 2) rfl
  have dfl_arg := Det.mk3 (Det.mk2 das1 dus1) dv1_var dws1
  refine EvalAll.call_funAll dfl_arg fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine hfl.mono fun w cb hw => ?_
  obtain ⟨⟨vs, rfl, hl_vs, hgens_vs⟩, hcb⟩ := hw
  simp only [List.length_map, List.take_length] at hgens_vs hcb
  obtain ⟨hWV, hVU, hnotV, hnV, hmaxV⟩ :=
    greedyMaxFold_maximal hWU hnot hnU hnW hrs.sub hrs.cover
  rw [← hgens_vs] at hWV hVU hnotV hnV hmaxV
  refine ⟨⟨vs, rfl, hl_vs, hWV, hVU, hnotV, hnV, hmaxV⟩, ?_⟩
  clear hfl hstep_fl dfl_arg dws1 dv1_var dus1 das1
  have wvs := wt_encGroup_le_sq hl_vs
  have wc_fl := wt_list2_le (encGroup as) (encGroup us)
  have wrs := GI.Lang.wt_list_le_of (rs.map encPerm) (c := 4 * (n + 1) ^ 2) (by
    intro v hv; obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hv; exact wt_encPerm_le σ)
  simp only [List.length_map] at wrs
  have hqn : (n + 1) ^ 6 ≤ (q + 1) * (n + 1) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
  have hrs_qn : rs.length ≤ (q + 1) * (n + 1) ^ 6 := by
    calc rs.length ≤ q + 1 := by omega
      _ ≤ (q + 1) * (n + 1) ^ 6 := Nat.le_mul_of_pos_right _ p1
  have hrs_wt : rs.length * (2 * (4 * (n + 1) ^ 2) + 1) ≤ 9 * ((q + 1) * (n + 1) ^ 6) := by
    calc rs.length * (2 * (4 * (n + 1) ^ 2) + 1) ≤ (q + 1) * (9 * (n + 1) ^ 6) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 9 * ((q + 1) * (n + 1) ^ 6) := by ring
  have hq1 : 1 ≤ (q + 1) * (n + 1) ^ 6 := Nat.mul_pos (by omega) (by omega)
  have hq2 : (q + 1) * (n + 1) ^ 6 ≤ (q + 1) ^ 2 * (n + 1) ^ 6 :=
    Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
  have hq2_1 : 1 ≤ (q + 1) ^ 2 * (n + 1) ^ 6 := le_trans hq1 hq2
  have w3_fl := wt_list3_le c_fl (.list (rs.map encPerm)) (encGroup ws)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcb
  have hsum : rs.length * tcGreedyStepCost hnc hmem n ≤
      (q + 1) * tcGreedyStepCost hnc hmem n :=
    Nat.mul_le_mul_right _ (by omega)
  have e_cfl : (Val.list [encGroup as, encGroup us]).wt = c_fl.wt := rfl
  have hloop : loopModK * (rs.length + 1) *
      ((Val.list [c_fl, .list (rs.map encPerm), encGroup ws]).wt + rs.length +
        320 * (n + 1) ^ 6 + 1) ≤
      loopModK * (q + 1) * (5000 * ((q + 1) * (n + 1) ^ 6)) := by
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_
    clear_value c_fl
    omega
  have hloop' : loopModK * (q + 1) * (5000 * ((q + 1) * (n + 1) ^ 6)) =
      5 * 10 ^ 6 * ((q + 1) ^ 2 * (n + 1) ^ 6) := by
    simp only [loopModK]; ring
  have e_inp : (Val.list [encGroup as, encGroup us, encGroup ws]).wt = inp.wt := rfl
  have e_w3 : (Val.list [Val.list [encGroup as, encGroup us], .list (rs.map encPerm),
      encGroup ws]).wt =
    (Val.list [c_fl, .list (rs.map encPerm), encGroup ws]).wt := rfl
  unfold tcGreedyCost
  clear_value inp c_fl env1
  generalize gmpRepsCost hmem (2000 * (n + 1) ^ 6) q = GRC at *
  generalize (q + 1) * tcGreedyStepCost hnc hmem n = QGSC at *
  generalize rs.length * tcGreedyStepCost hnc hmem n = RGSC at *
  generalize (q + 1) ^ 2 * (n + 1) ^ 6 = Q2N6 at *
  generalize (q + 1) * (n + 1) ^ 6 = Q1N6 at *
  omega

/-! ### 3. Conjugate-Intersection Loop (`tcConjStep`, `tcConjPass`, `tcConjEntry`) -/

/-- **One generator step of conjugate-intersection** on `[.nat n, encGroup ws, encPerm h]`. -/
def tcConjStep (iv mc mg le jni : ℕ) : Expr :=
  .letE (.call iv (arg 2))
  (.letE (mk2 (arg 0) (.call mc (mk2 (mk2 (arg 2) (.var 1)) (.get (arg 1) (.nat 1)))))
  (.letE (.call le (mk2 (arg 1) (.var 2)))
    (.ite (.var 3) (arg 1)
      (.letE (.prim jni (mk2 (arg 1) (.var 2)))
        (.call mg (mk2 (arg 0) (.var 4)))))))

/-- **One pass of conjugate-intersection** on `[encGroup hs, .nat i, encGroup ws]`. -/
def tcConjPass (flc : ℕ) : Expr :=
  .call flc (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 2))

/-- **Entry of conjugate-intersection** on `[encGroup hs, encGroup ms]`. -/
def tcConjEntry (itc : ℕ) : Expr :=
  .call itc (mk3 (arg 0)
    (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0)))
    (arg 1))

/-- Where `tcConjEntry` and its subroutines sit in the program. -/
structure TcConjAt (P : Program) (f itc cjp flc cjs iv mc cj cp mg le jni jmem : ℕ)
    (hni : NormalizedIntersection) (hmem : Membership) : Prop where
  entry : P.funs[f]? = some (tcConjEntry itc)
  iter : P.HasAt itc (iterFuns itc cjp)
  pass : P.funs[cjp]? = some (tcConjPass flc)
  fold : P.HasAt flc (foldlFuns flc cjs)
  step : P.funs[cjs]? = some (tcConjStep iv mc mg le jni)
  iv : P.HasAt iv (invFuns iv)
  mc : P.HasAt mc (mapFuns mc cj)
  cj : P.funs[cj]? = some (supConjF cp)
  cp : P.HasAt cp (composeFuns cp)
  mg : P.HasAt mg (mkGroupFuns mg)
  le : P.HasAt le (leFuns le jmem)
  jni_eq : P.prims[jni]? = some (normalizedIntersectionPrim hni)
  jmem_eq : P.prims[jmem]? = some (membershipPrim hmem)

/-- Cost of a single `tcConjStep` call on degree `n` with `≤ n ^ 2` generators. -/
noncomputable def tcConjStepCost (hni : NormalizedIntersection) (hmem : Membership) (n : ℕ) : ℕ :=
  (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) +
    10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) +
    10 ^ 19 * (n + 1) ^ 18

/-- Postcondition of `tcConjStep`. -/
def TcConjStepOut (W : Subgroup (Perm (Fin n))) (h : Perm (Fin n)) (w : Val) : Prop :=
  ∃ ws' : List (Perm (Fin n)), w = encGroup ws' ∧ ws'.length ≤ n ^ 2 ∧
    gens ws' = conjStep W h

theorem TcConjStepOut.wt_le {W : Subgroup (Perm (Fin n))} {h : Perm (Fin n)} {w : Val}
    (hout : TcConjStepOut W h w) : w.wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨ws', rfl, hl, -⟩ := hout
  exact wt_encGroup_le_sq hl

/-- **Specification of `tcConjStep`.** -/
theorem tcConjStep_spec {hni : NormalizedIntersection} {hmem : Membership} {P : Program}
    {cjs iv mc cj cp mg le jni jmem : ℕ}
    (hstep : P.funs[cjs]? = some (tcConjStep iv mc mg le jni))
    (hiv : P.HasAt iv (invFuns iv))
    (hmc : P.HasAt mc (mapFuns mc cj))
    (hcj : P.funs[cj]? = some (supConjF cp))
    (hcp : P.HasAt cp (composeFuns cp))
    (hmg : P.HasAt mg (mkGroupFuns mg))
    (hle : P.HasAt le (leFuns le jmem))
    (hjni : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    (hjmem : P.prims[jmem]? = some (membershipPrim hmem))
    {H U N : Subgroup (Perm (Fin n))} {ws : List (Perm (Fin n))} (h : Perm (Fin n))
    (hnU : ∀ g ∈ H, ∀ x ∈ U, g * x * g⁻¹ ∈ U)
    (hnN : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (hh : h ∈ H) (hW : IsSimpleInter U N (gens ws)) (hl_ws : ws.length ≤ n ^ 2) :
    FunAll P cjs (.list [.nat n, encGroup ws, encPerm h])
      (fun w c => TcConjStepOut (gens ws) h w ∧ c ≤ tcConjStepCost hni hmem n) := by
  classical
  set inp := Val.list [.nat n, encGroup ws, encPerm h]
  have wn := wt_nat_le n
  have wws := wt_encGroup_le_sq hl_ws
  have wh := wt_encPerm_le h
  have whi := wt_encPerm_le h⁻¹
  have winp := wt_list3_le (.nat n) (encGroup ws) (encPerm h)
  have p12 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have p34 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have p46 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p36 : (n + 1) ^ 3 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have p89 : (n + 1) ^ 8 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have p918 : (n + 1) ^ 9 ≤ (n + 1) ^ 18 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  -- step 1: `v1 = encPerm h⁻¹`
  have dh0 := Det.arg' (P := P) (vs := [.nat n, encGroup ws, encPerm h]) (rest := []) (j := 2) rfl
  have dv1_raw := Det.call dh0 (inv_spec hiv h)
  have dv1 : Det P [inp] (.call iv (arg 2)) (encPerm h⁻¹) (2 * 10 ^ 5 * (n + 1) ^ 6) := by
    refine dv1_raw.mono ?_
    have e_inp : (Val.list [.nat n, encGroup ws, encPerm h]).wt = inp.wt := rfl
    simp only [invK] at *
    clear_value inp
    omega
  -- step 2: `v2 = encGroup (ws.map (fun x => h * x * h⁻¹))`
  set wsc := ws.map (fun x => h * x * h⁻¹)
  have hl_wsc : wsc.length ≤ n ^ 2 := by simp [wsc, hl_ws]
  have wwsc := wt_encGroup_le_sq hl_wsc
  set env1 := [inp, encPerm h⁻¹]
  have dn1 := Det.arg' (P := P) (vs := [.nat n, encGroup ws, encPerm h])
    (rest := [encPerm h⁻¹]) (j := 0) rfl
  have dh1 := Det.arg' (P := P) (vs := [.nat n, encGroup ws, encPerm h])
    (rest := [encPerm h⁻¹]) (j := 2) rfl
  have dv1_var := Det.var' (P := P) (env := env1) (i := 1) (v := encPerm h⁻¹) rfl
  have dws1 := Det.arg' (P := P) (vs := [.nat n, encGroup ws, encPerm h])
    (rest := [encPerm h⁻¹]) (j := 1) rfl
  have dwsL := Det.get' dws1 (Det.nat 1) (v := .list ((1 :: ws).map encPerm))
    (show [Val.nat n, Val.list ((1 :: ws).map encPerm)][1]? = some _ from rfl)
  have dmc := Det.call (Det.mk2 (Det.mk2 dh1 dv1_var) dwsL)
    (supConjMap_det hcp hcj hmc h hl_ws)
  change Det P env1 _ (.list ((1 :: wsc).map encPerm)) _ at dmc
  have dv2_raw := Det.mk2 dn1 dmc
  have hv2_eq : Val.list [.nat n, .list ((1 :: wsc).map encPerm)] = encGroup wsc := rfl
  rw [hv2_eq] at dv2_raw
  have w_wsL : (Val.list ((1 :: ws).map encPerm)).wt < (encGroup ws).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: ws).map encPerm)]) (by simp)
  have w_wscL : (Val.list ((1 :: wsc).map encPerm)).wt < (encGroup wsc).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: wsc).map encPerm)]) (by simp)
  have w_hh := wt_list2_le (encPerm h) (encPerm h⁻¹)
  have w_mc_arg := wt_list2_le (.list [encPerm h, encPerm h⁻¹]) (.list ((1 :: ws).map encPerm))
  have dv2 : Det P env1
      (mk2 (arg 0) (.call mc (mk2 (mk2 (arg 2) (.var 1)) (.get (arg 1) (.nat 1)))))
      (encGroup wsc) (2 * 10 ^ 8 * (n + 1) ^ 8) := by
    refine dv2_raw.mono ?_
    have e_inp : (Val.list [.nat n, encGroup ws, encPerm h]).wt = inp.wt := rfl
    have e_wsc : (Val.list [.nat n, .list ((1 :: wsc).map encPerm)]).wt = (encGroup wsc).wt := rfl
    have e_wscL : (Val.list ((1 :: ws.map (fun x => h * x * h⁻¹)).map encPerm)).wt =
      (Val.list ((1 :: wsc).map encPerm)).wt := rfl
    clear_value inp wsc env1
    omega
  -- step 3: `v3 = le` on `[encGroup ws, encGroup wsc]`
  set env2 := env1 ++ [encGroup wsc]
  have dws2 := Det.arg' (P := P) (vs := [.nat n, encGroup ws, encPerm h])
    (rest := [encPerm h⁻¹, encGroup wsc]) (j := 1) rfl
  have dv2_var := Det.var' (P := P) (env := env2) (i := 2) (v := encGroup wsc) rfl
  have dv3 := ob_le_det hmem hle hjmem ⟨ws, rfl, rfl⟩ wsc dws2 dv2_var (by omega) (by omega)
  have hgens_wsc : gens wsc = conjSub h (gens ws) := gens_map_conj h ws
  set b := decide (gens wsc ≤ gens ws)
  set env3 := env2 ++ [boolVal b]
  have dv3_var := Det.var' (P := P) (env := env3) (i := 3) (v := boolVal b) rfl
  have db_eq : boolVal b = .nat (if b then 1 else 0) := by cases b <;> rfl
  rw [db_eq] at dv3_var
  -- step 4: `.ite (.var 3) ...`
  have hite : EvalAll P env3
      (.ite (.var 3) (arg 1)
        (.letE (.prim jni (mk2 (arg 1) (.var 2)))
          (.call mg (mk2 (arg 0) (.var 4)))))
      (fun w c => TcConjStepOut (gens ws) h w ∧
        c ≤ (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          10 ^ 8 * (n + 1) ^ 9) := by
    refine (sup_ite dv3_var
      (R := fun w ce => TcConjStepOut (gens ws) h w ∧
        ce ≤ (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          5 * 10 ^ 7 * (n + 1) ^ 9)
      (fun ht => ?_) (fun he => ?_)).mono fun w c h_ite => ?_
    · have hb_true : conjSub h (gens ws) ≤ gens ws := by
        rw [← hgens_wsc]
        by_contra hnot; simp [b, hnot] at ht
      have dws3 := Det.arg' (P := P) (vs := [.nat n, encGroup ws, encPerm h])
        (rest := [encPerm h⁻¹, encGroup wsc, boolVal b]) (j := 1) rfl
      refine dws3.post fun c hc => ⟨⟨ws, rfl, hl_ws, ?_⟩, ?_⟩
      · simp [conjStep, hb_true]
      · have e_inp : (Val.list [.nat n, encGroup ws, encPerm h]).wt = inp.wt := rfl
        clear_value inp wsc b env1 env2 env3
        generalize (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) = NI at *
        omega
    · have hb_false : ¬ (conjSub h (gens ws) ≤ gens ws) := by
        rw [← hgens_wsc]
        intro hle'; simp [b, hle'] at he
      have hWU : gens ws ≤ U := (isSimpleInter_props hW).2.1
      have hW_conj : IsSimpleInter U N (conjSub h (gens ws)) :=
        isSimpleInter_conjSub hnU hnN hh hW
      have hn_wsc : ∀ g ∈ U, ∀ x ∈ conjSub h (gens ws), g * x * g⁻¹ ∈ conjSub h (gens ws) :=
        (isSimpleInter_props hW_conj).2.2.2.1
      have hnorm_wsc : Normalizes (gens ws) (conjSub h (gens ws)) :=
        fun g hg x hx => hn_wsc g (hWU hg) x hx
      have dws3 := Det.arg' (P := P) (vs := [.nat n, encGroup ws, encPerm h])
        (rest := [encPerm h⁻¹, encGroup wsc, boolVal b]) (j := 1) rfl
      have dv2_3 := Det.var' (P := P) (env := env3) (i := 2) (v := encGroup wsc) rfl
      have dni_arg := Det.mk2 dws3 dv2_3
      have hni_raw := normalizedIntersection_call hni hjni dni_arg
        ⟨ws, rfl, rfl⟩ ⟨wsc, rfl, hgens_wsc⟩ hnorm_wsc
      have sv4 : EvalAll P env3 (.prim jni (mk2 (arg 1) (.var 2)))
          (fun v4 c => GensVal n v4 (gens ws ⊓ conjSub h (gens ws)) ∧
            c ≤ (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) +
              10 ^ 5 * (n + 1) ^ 6) := by
        refine hni_raw.mono fun v4 c hv4 => ⟨hv4.1, ?_⟩
        clear hni_raw dni_arg dv2_3 dws3
        have w2_ni := wt_list2_le (encGroup ws) (encGroup wsc)
        have hsz : (Val.list [encGroup ws, encGroup wsc]).size ≤ 10 ^ 4 * (n + 1) ^ 6 :=
          (Val.size_le_wt _).trans (by omega)
        have hb := (normalizedIntersectionPrim hni).bound_le hsz
        have hc := hv4.2
        have e_inp : (Val.list [.nat n, encGroup ws, encPerm h]).wt = inp.wt := rfl
        clear_value inp wsc b env1 env2 env3
        omega
      have s_mg : ∀ v4, GensVal n v4 (gens ws ⊓ conjSub h (gens ws)) →
          EvalAll P (env3 ++ [v4]) (.call mg (mk2 (arg 0) (.var 4)))
            (fun w c => TcConjStepOut (gens ws) h w ∧ c ≤ 10 ^ 7 * (n + 1) ^ 9) := by
        intro v4 hv4
        obtain ⟨ws', rfl, hl_ws', hmg_ws', hG_ws', wws'⟩ := mkGroup_gensVal hmg hv4
        have hgens_ws' : gens ws' = gens ws ⊓ conjSub h (gens ws) := by
          obtain ⟨_, h1, h2⟩ := hG_ws'
          rw [← h2, encGroup_injective h1]
        have dn4 := Det.arg' (P := P) (vs := [.nat n, encGroup ws, encPerm h])
          (rest := [encPerm h⁻¹, encGroup wsc, boolVal b, .list (ws'.map encPerm)]) (j := 0) rfl
        have dv4_var := Det.var' (P := P) (env := env3 ++ [.list (ws'.map encPerm)])
          (i := 4) (v := .list (ws'.map encPerm)) rfl
        have dmg := Det.call (Det.mk2 dn4 dv4_var) hmg_ws'
        have w_ws'L : (Val.list (ws'.map encPerm)).wt ≤ (encGroup ws').wt := wt_gens_le_encGroup ws'
        have w2_mg := wt_list2_le (.nat n) (.list (ws'.map encPerm))
        refine dmg.post fun c hc => ⟨⟨ws', rfl, hl_ws', ?_⟩, ?_⟩
        · simp [conjStep, hb_false, hgens_ws']
        · have e_inp : (Val.list [.nat n, encGroup ws, encPerm h]).wt = inp.wt := rfl
          simp only [mkGroupK] at *
          clear_value inp wsc b env1 env2 env3
          omega
      refine (ob_letAll TcConjStepOut.wt_le sv4 s_mg).mono fun w c h => ?_
      obtain ⟨hout, hc⟩ := h
      refine ⟨hout, ?_⟩
      clear s_mg sv4 hni_raw dni_arg dv2_3 dws3
      clear_value inp wsc b env1 env2 env3
      generalize (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) = NI at *
      omega
    · obtain ⟨ce, ⟨hout, hce⟩, htot⟩ := h_ite
      have hw_out := hout.wt_le
      have wb : (Val.nat (if b = true then 1 else 0)).wt ≤ 3 := by
        split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
      have e_inp : (Val.list [.nat n, encGroup ws, encPerm h]).wt = inp.wt := rfl
      refine ⟨hout, ?_⟩
      clear_value inp wsc b env1 env2 env3
      generalize (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) = NI at *
      omega
  refine FunAll.intro hstep
    ((ob_letDet TcConjStepOut.wt_le dv1
      (ob_letDet TcConjStepOut.wt_le dv2
        (ob_letDet TcConjStepOut.wt_le dv3 hite))).mono fun w c h => ?_)
  clear hite dv3_var dv3 dv2_var dws2 dv2 dv2_raw dmc dwsL dws1 dv1_var dh1 dn1 dv1 dv1_raw dh0
  obtain ⟨hout, hc⟩ := h
  refine ⟨hout, ?_⟩
  unfold tcConjStepCost
  clear_value inp wsc b env1 env2 env3
  generalize (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (n + 1) ^ 6) = NI at *
  generalize 10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) = MB at *
  omega

/-- Loop invariant for `foldlFuns` in `tcConjPass`. -/
def TcConjPassInv (W : Subgroup (Perm (Fin n))) (gs : List (Perm (Fin n)))
    (i : ℕ) (acc : Val) : Prop :=
  ∃ ws : List (Perm (Fin n)), acc = encGroup ws ∧ ws.length ≤ n ^ 2 ∧
    gens ws = conjPass W (gs.take i)

theorem TcConjPassInv.wt_le {W : Subgroup (Perm (Fin n))} {gs : List (Perm (Fin n))}
    {i : ℕ} {acc : Val} (h : TcConjPassInv W gs i acc) : acc.wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨ws, rfl, hl, -⟩ := h
  exact wt_encGroup_le_sq hl

/-- Cost bound of a single `tcConjPass` call on degree `n` with `≤ n ^ 2` generators. -/
noncomputable def tcConjPassCost (hni : NormalizedIntersection) (hmem : Membership) (n : ℕ) : ℕ :=
  2 * (n + 1) ^ 2 * tcConjStepCost hni hmem n + 10 ^ 9 * (n + 1) ^ 8

/-- **Specification of `tcConjPass`.** -/
theorem tcConjPass_spec {hni : NormalizedIntersection} {hmem : Membership} {P : Program}
    {cjp flc cjs iv mc cj cp mg le jni jmem : ℕ}
    (hpass : P.funs[cjp]? = some (tcConjPass flc))
    (hfold : P.HasAt flc (foldlFuns flc cjs))
    (hstep : P.funs[cjs]? = some (tcConjStep iv mc mg le jni))
    (hiv : P.HasAt iv (invFuns iv))
    (hmc : P.HasAt mc (mapFuns mc cj))
    (hcj : P.funs[cj]? = some (supConjF cp))
    (hcp : P.HasAt cp (composeFuns cp))
    (hmg : P.HasAt mg (mkGroupFuns mg))
    (hle : P.HasAt le (leFuns le jmem))
    (hjni : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    (hjmem : P.prims[jmem]? = some (membershipPrim hmem))
    {U N : Subgroup (Perm (Fin n))} {hs ws : List (Perm (Fin n))} (i : ℕ)
    (hnU : ∀ g ∈ gens hs, ∀ x ∈ U, g * x * g⁻¹ ∈ U)
    (hnN : ∀ g ∈ gens hs, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (hW : IsSimpleInter U N (gens ws))
    (hl_hs : hs.length ≤ n ^ 2) (hl_ws : ws.length ≤ n ^ 2) :
    FunAll P cjp (.list [encGroup hs, .nat i, encGroup ws])
      (fun w c =>
        (∃ ws' : List (Perm (Fin n)), w = encGroup ws' ∧ ws'.length ≤ n ^ 2 ∧
          gens ws' = conjPass (gens ws) (1 :: hs)) ∧
        c ≤ tcConjPassCost hni hmem n + 20 * (Val.nat i).wt) := by
  set inp := Val.list [encGroup hs, .nat i, encGroup ws]
  set gs := 1 :: hs
  have whs := wt_encGroup_le_sq hl_hs
  have wws := wt_encGroup_le_sq hl_ws
  have wn := wt_nat_le n
  have winp := wt_list3_le (encGroup hs) (.nat i) (encGroup ws)
  have w_gsL : (Val.list (gs.map encPerm)).wt < (encGroup hs).wt :=
    wt_le_wt_list (vs := [.nat n, .list (gs.map encPerm)]) (by simp)
  have hl_gs : gs.length ≤ 2 * (n + 1) ^ 2 := by
    simp only [gs, List.length_cons]
    have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  have p12 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h0 : TcConjPassInv (gens ws) gs 0 (encGroup ws) := ⟨ws, rfl, hl_ws, rfl⟩
  have hgs_mem : ∀ h ∈ gs, h ∈ gens hs := by
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh'
    · exact one_mem _
    · exact Subgroup.subset_closure hh'
  have hstep_fl : ∀ j acc (hj : j < (gs.map encPerm).length),
      TcConjPassInv (gens ws) gs j acc →
      FunAll P cjs (.list [.nat n, acc, (gs.map encPerm)[j]])
        (fun w cost => TcConjPassInv (gens ws) gs (j + 1) w ∧
          cost ≤ tcConjStepCost hni hmem n) := by
    intro j acc hj hinv
    simp only [List.length_map] at hj
    obtain ⟨ws_j, rfl, hl_wsj, hgens_wsj⟩ := hinv
    have h_elem : (gs.map encPerm)[j]'(by simp [hj]) = encPerm (gs[j]'hj) := List.getElem_map ..
    rw [h_elem]
    have hgs_take : ∀ h ∈ gs.take j, h ∈ gens hs :=
      fun h hh => hgs_mem h (List.mem_of_mem_take hh)
    have hWj : IsSimpleInter U N (gens ws_j) := by
      rw [hgens_wsj]
      exact isSimpleInter_conjPass hnU hnN hgs_take hW
    have hhj : gs[j]'hj ∈ gens hs := hgs_mem _ (List.getElem_mem hj)
    refine (tcConjStep_spec hstep hiv hmc hcj hcp hmg hle hjni hjmem (gs[j]'hj)
      hnU hnN hhj hWj hl_wsj).mono fun w cost hw => ⟨?_, hw.2⟩
    obtain ⟨ws', rfl, hl_ws', hgens_ws'⟩ := hw.1
    refine ⟨ws', rfl, hl_ws', ?_⟩
    rw [hgens_ws', hgens_wsj, List.take_add_one, List.getElem?_eq_getElem hj,
      Option.toList_some, conjPass_snoc]
  have hfl := foldl_spec hfold (c := .nat n) (xs := gs.map encPerm) (acc0 := encGroup ws)
    (M := 320 * (n + 1) ^ 6) (B := fun _ => tcConjStepCost hni hmem n)
    h0 (fun _ _ _ hinv => hinv.wt_le) hstep_fl
  have dhs0 := Det.arg' (P := P) (vs := [encGroup hs, .nat i, encGroup ws])
    (rest := []) (j := 0) rfl
  have dn0 := Det.get' dhs0 (Det.nat 0) (v := .nat n)
    (show [Val.nat n, Val.list (gs.map encPerm)][0]? = some (.nat n) from rfl)
  have dgs0 := Det.get' dhs0 (Det.nat 1) (v := .list (gs.map encPerm))
    (show [Val.nat n, Val.list (gs.map encPerm)][1]? = some _ from rfl)
  have dws0 := Det.arg' (P := P) (vs := [encGroup hs, .nat i, encGroup ws])
    (rest := []) (j := 2) rfl
  have dfl_arg := Det.mk3 dn0 dgs0 dws0
  refine FunAll.intro hpass (EvalAll.call_funAll dfl_arg fun v ca hv => ?_)
  obtain ⟨rfl, hca⟩ := hv
  refine hfl.mono fun w cb hw => ?_
  obtain ⟨⟨ws', rfl, hl_ws', hgens_ws'⟩, hcb⟩ := hw
  simp only [List.length_map, List.take_length] at hgens_ws' hcb
  refine ⟨⟨ws', rfl, hl_ws', hgens_ws'⟩, ?_⟩
  clear hfl hstep_fl dfl_arg dws0 dgs0 dn0 dhs0
  have wws' := wt_encGroup_le_sq hl_ws'
  have w3_fl := wt_list3_le (.nat n) (.list (gs.map encPerm)) (encGroup ws)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcb
  have hsum : gs.length * tcConjStepCost hni hmem n ≤
      2 * (n + 1) ^ 2 * tcConjStepCost hni hmem n :=
    Nat.mul_le_mul_right _ hl_gs
  have hloop : loopModK * (gs.length + 1) *
      ((Val.list [.nat n, .list (gs.map encPerm), encGroup ws]).wt + gs.length +
        320 * (n + 1) ^ 6 + 1) ≤
      loopModK * (3 * (n + 1) ^ 2) * (5000 * (n + 1) ^ 6) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hloop' : loopModK * (3 * (n + 1) ^ 2) * (5000 * (n + 1) ^ 6) =
      15 * 10 ^ 6 * (n + 1) ^ 8 := by simp only [loopModK]; ring
  have e_inp : (Val.list [encGroup hs, .nat i, encGroup ws]).wt = inp.wt := rfl
  unfold tcConjPassCost
  clear_value inp gs
  generalize 2 * (n + 1) ^ 2 * tcConjStepCost hni hmem n = N2CSC at *
  generalize gs.length * tcConjStepCost hni hmem n = GCSC at *
  omega

/-- Loop invariant for `iterFuns` in `tcConjEntry`. -/
def TcConjLoopInv (H U N : Subgroup (Perm (Fin n))) (i : ℕ) (acc : Val) : Prop :=
  ∃ ws : List (Perm (Fin n)), acc = encGroup ws ∧ ws.length ≤ n ^ 2 ∧
    IsSimpleInter U N (gens ws) ∧
    ((∀ g ∈ H, ∀ x ∈ gens ws, g * x * g⁻¹ ∈ gens ws) ∨
      2 ^ i * Nat.card (gens ws) ≤ Nat.card U)

theorem TcConjLoopInv.wt_le {H U N : Subgroup (Perm (Fin n))} {i : ℕ} {acc : Val}
    (h : TcConjLoopInv H U N i acc) : acc.wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨ws, rfl, hl, -⟩ := h
  exact wt_encGroup_le_sq hl

/-- Cost bound of `tcConjEntry` on degree `n` with `≤ n ^ 2` generators. -/
noncomputable def tcConjCost (hni : NormalizedIntersection) (hmem : Membership) (n : ℕ) : ℕ :=
  (n + 1) ^ 2 * tcConjPassCost hni hmem n + 10 ^ 9 * (n + 1) ^ 8

/-- **Specification of `tcConjEntry`.**
On `[encGroup hs, encGroup ms]` where `1 ≤ n`, `N ≤ U ≤ H = gens hs` (`H` normalizes `N` and `U`,
`N` transitive on `Fin n`), and `IsNonabelianSimpleNormal U N (gens ms)`, returns `encGroup ws`
(`ws.length ≤ n ^ 2`) with `N ≤ gens ws < U`, `H` normalizes `gens ws`, and
`((gens ws).subgroupOf U).index ≤ n ^ (1 + Nat.log 2 n)`. -/
theorem tcConjEntry_spec
    {hni : NormalizedIntersection} {hmem : Membership} {P : Program}
    {f itc cjp flc cjs iv mc cj cp mg le jni jmem : ℕ}
    (hP : TcConjAt P f itc cjp flc cjs iv mc cj cp mg le jni jmem hni hmem)
    {U N : Subgroup (Perm (Fin n))} {hs ms : List (Perm (Fin n))} (hn1 : 1 ≤ n)
    (hUH : U ≤ gens hs)
    (hnU : ∀ g ∈ gens hs, ∀ x ∈ U, g * x * g⁻¹ ∈ U)
    (hnN : ∀ g ∈ gens hs, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (htrN : MulAction.IsPretransitive N (Fin n))
    (hM : IsNonabelianSimpleNormal U N (gens ms))
    (hl_hs : hs.length ≤ n ^ 2) (hl_ms : ms.length ≤ n ^ 2) :
    FunAll P f (.list [encGroup hs, encGroup ms])
      (fun w c =>
        (∃ ws : List (Perm (Fin n)), w = encGroup ws ∧ ws.length ≤ n ^ 2 ∧
          N ≤ gens ws ∧ gens ws ≤ U ∧ ¬ (U ≤ gens ws) ∧
          (∀ g ∈ gens hs, ∀ x ∈ gens ws, g * x * g⁻¹ ∈ gens ws) ∧
          ((gens ws).subgroupOf U).index ≤ n ^ (1 + Nat.log 2 n)) ∧
        c ≤ tcConjCost hni hmem n) := by
  set inp := Val.list [encGroup hs, encGroup ms]
  set k := n * n
  have hk_eq : k = n ^ 2 := (sq n).symm
  have whs := wt_encGroup_le_sq hl_hs
  have wms := wt_encGroup_le_sq hl_ms
  have wn := wt_nat_le n
  have wk := wt_nat_le k
  have winp := wt_list2_le (encGroup hs) (encGroup ms)
  have hk2 : k ≤ (n + 1) ^ 2 := by
    have : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    omega
  have p12 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p24 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have p46 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  -- initial invariant at `i = 0`
  have h0 : TcConjLoopInv (gens hs) U N 0 (encGroup ms) := by
    refine ⟨ms, rfl, hl_ms, isSimpleInter_singleton hM, Or.inr ?_⟩
    simp [Subgroup.card_le_of_le hM.2.1]
  -- step bound
  set B := tcConjPassCost hni hmem n + 60 * (n + 1) ^ 2
  have hgs_mem : ∀ h ∈ (1 :: hs : List (Perm (Fin n))), h ∈ gens hs := by
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh'
    · exact one_mem _
    · exact Subgroup.subset_closure hh'
  have hstep : ∀ i acc, i < k → TcConjLoopInv (gens hs) U N i acc →
      FunAll P cjp (.list [encGroup hs, .nat i, acc])
        (fun w cost => TcConjLoopInv (gens hs) U N (i + 1) w ∧ cost ≤ B) := by
    intro i acc hi hinv
    obtain ⟨ws, rfl, hl_ws, hW, hbr⟩ := hinv
    refine (tcConjPass_spec hP.pass hP.fold hP.step hP.iv hP.mc hP.cj hP.cp hP.mg hP.le
      hP.jni_eq hP.jmem_eq i hnU hnN hW hl_hs hl_ws).mono fun w cost hw => ⟨?_, ?_⟩
    · obtain ⟨ws', rfl, hl_ws', hgens_ws'⟩ := hw.1
      have hW' : IsSimpleInter U N (gens ws') := by
        rw [hgens_ws']
        exact isSimpleInter_conjPass hnU hnN hgs_mem hW
      refine ⟨ws', rfl, hl_ws', hW', ?_⟩
      rcases conjPass_normalizes_or_card_lt (gens ws) (1 :: hs) with ⟨heq, hnorm⟩ | hcard_lt
      · left
        rw [hgens_ws', heq]
        rwa [gens_cons_one] at hnorm
      · rcases hbr with hnorm_ws | hcard_i
        · left
          have hall : ∀ h ∈ (1 :: hs : List (Perm (Fin n))), conjSub h (gens ws) ≤ gens ws := by
            intro h hh x hx
            obtain ⟨y, hy, rfl⟩ := mem_conjSub_iff.mp hx
            exact hnorm_ws h (hgs_mem h hh) y hy
          have hnorm' := normalizes_gens_of_forall_conjSub_le hall
          rw [gens_cons_one] at hnorm'
          have heq : conjPass (gens ws) (1 :: hs) = gens ws := by
            refine le_antisymm (conjPass_le _ _) ?_
            by_contra hnot_le
            have hlt : conjPass (gens ws) (1 :: hs) < gens ws :=
              lt_of_le_of_ne (conjPass_le _ _) fun h => hnot_le h.symm.le
            -- wait: if `hall` holds, `conjPass (gens ws) (1 :: hs) = gens ws` directly!
            exact hnot_le (by
              have : ∀ gs' : List (Perm (Fin n)),
                  (∀ h ∈ gs', conjSub h (gens ws) ≤ gens ws) →
                  conjPass (gens ws) gs' = gens ws := by
                intro gs' hgs'
                induction gs' with
                | nil => rfl
                | cons h gs' ih =>
                  have hh : conjSub h (gens ws) ≤ gens ws := hgs' h List.mem_cons_self
                  have hs_eq : conjStep (gens ws) h = gens ws := by
                    classical simp [conjStep, hh]
                  simp only [conjPass, List.foldl_cons, hs_eq]
                  exact ih (fun x hx => hgs' x (List.mem_cons_of_mem h hx))
              rw [this (1 :: hs) hall])
          rw [hgens_ws', heq]
          exact hnorm_ws
        · right
          rw [hgens_ws']
          calc 2 ^ (i + 1) * Nat.card (conjPass (gens ws) (1 :: hs))
              = 2 ^ i * (2 * Nat.card (conjPass (gens ws) (1 :: hs))) := by ring
            _ ≤ 2 ^ i * Nat.card (gens ws) := Nat.mul_le_mul_left _ hcard_lt
            _ ≤ Nat.card U := hcard_i
    · have wi := wt_nat_le i
      have := hw.2
      omega
  have hit := iter_spec hP.iter (c := encGroup hs) (k := k) (M := 320 * (n + 1) ^ 6) h0
    (fun _ _ _ hinv => hinv.wt_le) hstep
  have dhs0 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ms]) (rest := []) (j := 0) rfl
  have dn0 := Det.get' dhs0 (Det.nat 0) (v := .nat n)
    (show [Val.nat n, Val.list ((1 :: hs).map encPerm)][0]? = some (.nat n) from rfl)
  have dk := Det.arith' (z := k) (op := .mul) dn0 dn0 rfl
  have dms0 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ms]) (rest := []) (j := 1) rfl
  have darg := Det.mk3 dhs0 dk dms0
  refine FunAll.intro hP.entry (EvalAll.call_funAll darg fun v ca hv => ?_)
  obtain ⟨rfl, hca⟩ := hv
  refine hit.mono fun w cb hw => ?_
  obtain ⟨⟨ws, rfl, hl_ws, hW, hbr⟩, hcb⟩ := hw
  have hnW : ∀ g ∈ gens hs, ∀ x ∈ gens ws, g * x * g⁻¹ ∈ gens ws := by
    rcases hbr with hnW | hcard
    · exact hnW
    · rw [hk_eq] at hcard
      exact absurd hcard (not_two_pow_sq_mul_card_le hn1 (gens ws) U)
  obtain ⟨hNW, hWU, hnotW, -, -⟩ := isSimpleInter_props hW
  have hindW := isSimpleInter_index_le hUH hnN htrN hW
  refine ⟨⟨ws, rfl, hl_ws, hNW, hWU, hnotW, hnW, hindW⟩, ?_⟩
  clear hit hstep darg dms0 dk dn0 dhs0
  have wws := wt_encGroup_le_sq hl_ws
  have w3 := wt_list3_le (encGroup hs) (.nat k) (encGroup ms)
  have w_hsL : (Val.list ((1 :: hs).map encPerm)).wt < (encGroup hs).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: hs).map encPerm)]) (by simp)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcb
  have hkb : k * B ≤ (n + 1) ^ 2 * tcConjPassCost hni hmem n + 60 * (n + 1) ^ 4 := by
    calc k * B ≤ (n + 1) ^ 2 * (tcConjPassCost hni hmem n + 60 * (n + 1) ^ 2) :=
          Nat.mul_le_mul_right _ hk2
      _ = (n + 1) ^ 2 * tcConjPassCost hni hmem n + 60 * (n + 1) ^ 4 := by ring
  have hloop : loopModK * (k + 1) *
      ((Val.list [encGroup hs, .nat k, encGroup ms]).wt + k + 320 * (n + 1) ^ 6 + 1) ≤
      loopModK * (2 * (n + 1) ^ 2) * (5000 * (n + 1) ^ 6) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hloop' : loopModK * (2 * (n + 1) ^ 2) * (5000 * (n + 1) ^ 6) =
      10 ^ 7 * (n + 1) ^ 8 := by simp only [loopModK]; ring
  have e_inp : (Val.list [encGroup hs, encGroup ms]).wt = inp.wt := rfl
  unfold tcConjCost
  clear_value inp k B
  generalize (n + 1) ^ 2 * tcConjPassCost hni hmem n = N2CPC at *
  omega

/-! ### 4. Single Nonabelian-Chief Step (`tcStepBody`) -/

/-- **One step of the top-down nonabelian-chief chain** on `[encGroup hs, encGroup ns, encGroup us]`. -/
def tcStepBody (ap mg le red ob grd cnj jder : ℕ) : Expr :=
  .letE (.call le (mk2 (arg 1) (arg 2)))
  (.ite (.var 1) (arg 1)
    (.letE (.prim jder (arg 2))
    (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 2)))
    (.letE (.call red (mk2 (.get (arg 0) (.nat 0))
      (.call ap (mk2 (.get (.var 3) (.nat 1)) (.get (arg 1) (.nat 1))))))
    (.letE (.call le (mk2 (.var 4) (arg 2)))
      (.ite (.var 5)
        (.letE (.call ob (mk2 (arg 2) (arg 1)))
        (.letE (.call grd (mk3 (arg 2) (arg 2) (.var 6)))
        (.letE (.call cnj (mk2 (arg 0) (.var 7)))
          (.call grd (mk3 (arg 0) (arg 2) (.var 8))))))
        (.var 4)))))))

/-- Where `tcStepBody` and all its submodules sit in the program. -/
structure TcStepAt (P : Program)
    (f ap mg le red
     ob it_ob g_ob obk rep lo dom cls ker
     grd gr fl_g gs_g
     cnj itc cjp flc cjs iv mc cj cp
     jmb jpre jmem jnc jni jder : ℕ)
    (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup) : Prop where
  entry : P.funs[f]? = some (tcStepBody ap mg le red ob grd cnj jder)
  hap : P.HasAt ap (appendFuns ap)
  hmg : P.HasAt mg (mkGroupFuns mg)
  hle : P.HasAt le (leFuns le jmem)
  hred : P.HasAt red (reduceFuns red jmem)
  hob : ObAt P ob it_ob g_ob ap le red obk rep lo dom mg cls ker jmb jpre jmem hmb hpre hmem
  hgrd : TcGreedyAt P grd gr fl_g gs_g mg le jnc jmem hnc hmem
  hcnj : TcConjAt P cnj itc cjp flc cjs iv mc cj cp mg le jni jmem hni hmem
  jder_eq : P.prims[jder]? = some (derivedSubgroupPrim hder)

/-- Relation between consecutive terms `U` and `V` of the top-down chain from `H` to `N`. -/
def TcStepRel (H N U V : Subgroup (Perm (Fin n))) : Prop :=
  N ≤ V ∧ V ≤ U ∧ (∀ g ∈ H, ∀ x ∈ V, g * x * g⁻¹ ∈ V) ∧
  (U ≤ N ∨ 2 * Nat.card V ≤ Nat.card U) ∧
  (¬ ⁅U, U⁆ ≤ N ⊔ V →
    ∀ M : Subgroup (Perm (Fin n)), N ⊔ V ≤ M → M ≤ N ⊔ U →
      (∀ g ∈ H, ∀ x ∈ M, g * x * g⁻¹ ∈ M) → M = N ⊔ V ∨ M = N ⊔ U)

/-- Postcondition of `tcStepBody`. -/
def TcStepOut (H N U : Subgroup (Perm (Fin n))) (w : Val) : Prop :=
  ∃ vs : List (Perm (Fin n)), w = encGroup vs ∧ vs.length ≤ n ^ 2 ∧
    TcStepRel H N U (gens vs)

theorem TcStepOut.wt_le {H N U : Subgroup (Perm (Fin n))} {w : Val}
    (h : TcStepOut H N U w) : w.wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨vs, rfl, hl, -⟩ := h
  exact wt_encGroup_le_sq hl

/-- Index bound `q₁(n) = max (24!) (n ^ (1 + log₂ n)) * n ^ (1 + log₂ n)` from `obEntry`. -/
def tcObIndexBd (n : ℕ) : ℕ :=
  max (Nat.factorial 24) (n ^ (1 + Nat.log 2 n)) * n ^ (1 + Nat.log 2 n)

/-- Index bound `q₂(n) = n ^ (1 + log₂ n)` from `tcConjEntry`. -/
def tcConjIndexBd (n : ℕ) : ℕ :=
  n ^ (1 + Nat.log 2 n)

/-- Cost bound of a single `tcStepBody` call on degree `n` with `≤ n ^ 2` generators. -/
noncomputable def tcStepCost (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup) (n : ℕ) : ℕ :=
  (derivedSubgroupPrim hder).boundSize (10 ^ 4 * (n + 1) ^ 6) +
    reduceCost hmem n (3 * (n + 1) ^ 2) +
    2 * (10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6)) +
    obCost hmb hpre hmem n +
    tcGreedyCost hnc hmem n (tcObIndexBd n) +
    tcConjCost hni hmem n +
    tcGreedyCost hnc hmem n (tcConjIndexBd n) +
    10 ^ 20 * (n + 1) ^ 18

/-- **Specification of `tcStepBody`.** -/
theorem tcStep_spec (hMa : MarotiPrimitive)
    {hmb : MinimalBlocks} {hpre : Preimage} {hmem : Membership}
    {hnc : NormalClosure} {hni : NormalizedIntersection} {hder : DerivedSubgroup}
    {P : Program}
    {f ap mg le red
     ob it_ob g_ob obk rep lo dom cls ker
     grd gr fl_g gs_g
     cnj itc cjp flc cjs iv mc cj cp
     jmb jpre jmem jnc jni jder : ℕ}
    (hP : TcStepAt P f ap mg le red ob it_ob g_ob obk rep lo dom cls ker
      grd gr fl_g gs_g cnj itc cjp flc cjs iv mc cj cp
      jmb jpre jmem jnc jni jder hmb hpre hmem hnc hni hder)
    {hs ns us : List (Perm (Fin n))}
    (hNU : gens ns ≤ gens us) (hUH : gens us ≤ gens hs)
    (hnU : ∀ g ∈ gens hs, ∀ x ∈ gens us, g * x * g⁻¹ ∈ gens us)
    (hnN : ∀ g ∈ gens hs, ∀ x ∈ gens ns, g * x * g⁻¹ ∈ gens ns)
    (htrN : 1 ≤ n → MulAction.IsPretransitive (gens ns) (Fin n))
    (hl_hs : hs.length ≤ n ^ 2) (hl_ns : ns.length ≤ n ^ 2) (hl_us : us.length ≤ n ^ 2) :
    FunAll P f (.list [encGroup hs, encGroup ns, encGroup us])
      (fun w c => TcStepOut (gens hs) (gens ns) (gens us) w ∧
        c ≤ tcStepCost hmb hpre hmem hnc hni hder n) := by
  classical
  set inp := Val.list [encGroup hs, encGroup ns, encGroup us]
  have whs := wt_encGroup_le_sq hl_hs
  have wns := wt_encGroup_le_sq hl_ns
  have wus := wt_encGroup_le_sq hl_us
  have wn := wt_nat_le n
  have winp := wt_list3_le (encGroup hs) (encGroup ns) (encGroup us)
  have p12 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have p89 : (n + 1) ^ 8 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have p918 : (n + 1) ^ 9 ≤ (n + 1) ^ 18 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  -- step 1: `v1 = boolVal (decide (gens us ≤ gens ns))`
  have dns0 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
    (rest := []) (j := 1) rfl
  have dus0 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
    (rest := []) (j := 2) rfl
  have dv1 := ob_le_det hmem hP.hle hP.hob.obk.jmem_eq ⟨ns, rfl, rfl⟩ us dns0 dus0
    (by omega) (by omega)
  set b1 := decide (gens us ≤ gens ns)
  set env1 := [inp, boolVal b1]
  have dv1_var := Det.var' (P := P) (env := env1) (i := 1) (v := boolVal b1) rfl
  have db1_eq : boolVal b1 = .nat (if b1 then 1 else 0) := by cases b1 <;> rfl
  rw [db1_eq] at dv1_var
  -- outer `.ite (.var 1) (arg 1) ...`
  have hite1 : EvalAll P env1
      (.ite (.var 1) (arg 1)
        (.letE (.prim jder (arg 2))
        (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 2)))
        (.letE (.call red (mk2 (.get (arg 0) (.nat 0))
          (.call ap (mk2 (.get (.var 3) (.nat 1)) (.get (arg 1) (.nat 1))))))
        (.letE (.call le (mk2 (.var 4) (arg 2)))
          (.ite (.var 5)
            (.letE (.call ob (mk2 (arg 2) (arg 1)))
            (.letE (.call grd (mk3 (arg 2) (arg 2) (.var 6)))
            (.letE (.call cnj (mk2 (arg 0) (.var 7)))
              (.call grd (mk3 (arg 0) (arg 2) (.var 8))))))
            (.var 4)))))))
      (fun w c => TcStepOut (gens hs) (gens ns) (gens us) w ∧
        c ≤ (derivedSubgroupPrim hder).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          reduceCost hmem n (3 * (n + 1) ^ 2) +
          10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          obCost hmb hpre hmem n +
          tcGreedyCost hnc hmem n (tcObIndexBd n) +
          tcConjCost hni hmem n +
          tcGreedyCost hnc hmem n (tcConjIndexBd n) +
          5 * 10 ^ 19 * (n + 1) ^ 18) := by
    refine (sup_ite dv1_var
      (R := fun w ce => TcStepOut (gens hs) (gens ns) (gens us) w ∧
        ce ≤ (derivedSubgroupPrim hder).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          reduceCost hmem n (3 * (n + 1) ^ 2) +
          10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          obCost hmb hpre hmem n +
          tcGreedyCost hnc hmem n (tcObIndexBd n) +
          tcConjCost hni hmem n +
          tcGreedyCost hnc hmem n (tcConjIndexBd n) +
          4 * 10 ^ 19 * (n + 1) ^ 18)
      (fun ht => ?_) (fun he => ?_)).mono fun w c h_ite1 => ?_
    · -- branch `b1 = true`: `gens us ≤ gens ns`
      have hb1_true : gens us ≤ gens ns := by
        by_contra hnot; simp [b1, hnot] at ht
      have dns1 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
        (rest := [boolVal b1]) (j := 1) rfl
      refine dns1.post fun c hc => ⟨⟨ns, rfl, hl_ns, le_rfl, hNU, hnN, Or.inl hb1_true, ?_⟩, ?_⟩
      · intro hna
        exfalso
        apply hna
        exact (comm_self_le _).trans (hb1_true.trans le_sup_left)
      · have e_inp : (Val.list [encGroup hs, encGroup ns, encGroup us]).wt = inp.wt := rfl
        clear_value inp b1 env1
        generalize (derivedSubgroupPrim hder).boundSize (10 ^ 4 * (n + 1) ^ 6) = DER at *
        generalize reduceCost hmem n (3 * (n + 1) ^ 2) = RC at *
        generalize 10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) = MB at *
        generalize obCost hmb hpre hmem n = OBC at *
        generalize tcGreedyCost hnc hmem n (tcObIndexBd n) = GC1 at *
        generalize tcConjCost hni hmem n = CC at *
        generalize tcGreedyCost hnc hmem n (tcConjIndexBd n) = GC2 at *
        omega
    · -- branch `b1 = false`: `¬ (gens us ≤ gens ns)`
      have hb1_false : ¬ (gens us ≤ gens ns) := by
        intro hle'; simp [b1, hle'] at he
      have hn1 : 1 ≤ n := one_le_of_not_le hb1_false
      have dus1 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
        (rest := [boolVal b1]) (j := 2) rfl
      have hder_raw := derivedSubgroup_call hder hP.jder_eq dus1 ⟨us, rfl, rfl⟩
      have sv2 : EvalAll P env1 (.prim jder (arg 2))
          (fun v2 c => GensVal n v2 ⁅gens us, gens us⁆ ∧
            c ≤ (derivedSubgroupPrim hder).boundSize (10 ^ 4 * (n + 1) ^ 6) +
              10 ^ 5 * (n + 1) ^ 6) := by
        refine hder_raw.mono fun v2 c hv2 => ⟨hv2.1, ?_⟩
        clear hder_raw dus1
        have hsz : (encGroup us).size ≤ 10 ^ 4 * (n + 1) ^ 6 :=
          (Val.size_le_wt _).trans (by omega)
        have hb := (derivedSubgroupPrim hder).bound_le hsz
        have hc := hv2.2
        have e_inp : (Val.list [encGroup hs, encGroup ns, encGroup us]).wt = inp.wt := rfl
        clear_value inp b1 env1
        omega
      have s3_end : ∀ v2, GensVal n v2 ⁅gens us, gens us⁆ →
          EvalAll P (env1 ++ [v2])
            (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 2)))
            (.letE (.call red (mk2 (.get (arg 0) (.nat 0))
              (.call ap (mk2 (.get (.var 3) (.nat 1)) (.get (arg 1) (.nat 1))))))
            (.letE (.call le (mk2 (.var 4) (arg 2)))
              (.ite (.var 5)
                (.letE (.call ob (mk2 (arg 2) (arg 1)))
                (.letE (.call grd (mk3 (arg 2) (arg 2) (.var 6)))
                (.letE (.call cnj (mk2 (arg 0) (.var 7)))
                  (.call grd (mk3 (arg 0) (arg 2) (.var 8))))))
                (.var 4)))))
            (fun w c => TcStepOut (gens hs) (gens ns) (gens us) w ∧
              c ≤ reduceCost hmem n (3 * (n + 1) ^ 2) +
                10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) +
                obCost hmb hpre hmem n +
                tcGreedyCost hnc hmem n (tcObIndexBd n) +
                tcConjCost hni hmem n +
                tcGreedyCost hnc hmem n (tcConjIndexBd n) +
                3 * 10 ^ 19 * (n + 1) ^ 18) := by
        intro v2 hv2
        obtain ⟨ds, rfl, hl_ds, hmg_ds, hG_ds, wds⟩ := mkGroup_gensVal hP.hmg hv2
        have hgens_ds : gens ds = ⁅gens us, gens us⁆ := by
          obtain ⟨_, h1, h2⟩ := hG_ds
          rw [← h2, encGroup_injective h1]
        set env2 := env1 ++ [.list (ds.map encPerm)]
        have dhs2 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
          (rest := [boolVal b1, .list (ds.map encPerm)]) (j := 0) rfl
        have dn2 := Det.get' dhs2 (Det.nat 0) (v := .nat n)
          (show [Val.nat n, Val.list ((1 :: hs).map encPerm)][0]? = some (.nat n) from rfl)
        have dv2_var := Det.var' (P := P) (env := env2) (i := 2) (v := .list (ds.map encPerm)) rfl
        have dv3_raw := Det.call (Det.mk2 dn2 dv2_var) hmg_ds
        have w_dsL : (Val.list (ds.map encPerm)).wt ≤ (encGroup ds).wt := wt_gens_le_encGroup ds
        have w_hsL : (Val.list ((1 :: hs).map encPerm)).wt < (encGroup hs).wt :=
          wt_le_wt_list (vs := [.nat n, .list ((1 :: hs).map encPerm)]) (by simp)
        have w2_v3 := wt_list2_le (.nat n) (.list (ds.map encPerm))
        have dv3 : Det P env2 (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 2)))
            (encGroup ds) (10 ^ 7 * (n + 1) ^ 9) := by
          refine dv3_raw.mono ?_
          have e_inp : (Val.list [encGroup hs, encGroup ns, encGroup us]).wt = inp.wt := rfl
          simp only [mkGroupK] at *
          clear_value inp b1 env1 env2
          omega
        set v3 := encGroup ds
        set env3 := env2 ++ [v3]
        -- step 4: `v4 = encGroup (keepList (ds ++ 1 :: ns))`
        have dhs3 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
          (rest := [boolVal b1, .list (ds.map encPerm), v3]) (j := 0) rfl
        have dn3 := Det.get' dhs3 (Det.nat 0) (v := .nat n)
          (show [Val.nat n, Val.list ((1 :: hs).map encPerm)][0]? = some (.nat n) from rfl)
        have dv3_var := Det.var' (P := P) (env := env3) (i := 3) (v := v3) rfl
        have ddsL := Det.get' dv3_var (Det.nat 1) (v := .list ((1 :: ds).map encPerm))
          (show [Val.nat n, Val.list ((1 :: ds).map encPerm)][1]? = some _ from rfl)
        have dns3 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
          (rest := [boolVal b1, .list (ds.map encPerm), v3]) (j := 1) rfl
        have dnsL := Det.get' dns3 (Det.nat 1) (v := .list ((1 :: ns).map encPerm))
          (show [Val.nat n, Val.list ((1 :: ns).map encPerm)][1]? = some _ from rfl)
        obtain ⟨du, wu⟩ := ob_union_det hP.hap dn3 ddsL dnsL hl_ds hl_ns
        have dred_raw := Det.call du (reduce_spec hmem hP.hred hP.hob.obk.jmem_eq (ds ++ 1 :: ns))
        set us' := keepList (ds ++ 1 :: ns)
        have hl_us' : us'.length ≤ n ^ 2 := length_keepList_le _
        have wus' := wt_encGroup_le_sq hl_us'
        have hgens_us' : gens us' = ⁅gens us, gens us⁆ ⊔ gens ns := by
          rw [gens_keepList, ob_gens_ns_one_js, hgens_ds]
        have hlen_dn : (ds ++ 1 :: ns).length ≤ 3 * (n + 1) ^ 2 := by
          simp only [List.length_append, List.length_cons]
          have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
          omega
        have hrc := reduceCost_mono hmem n hlen_dn
        have w_ds1L : (Val.list ((1 :: ds).map encPerm)).wt < (encGroup ds).wt :=
          wt_le_wt_list (vs := [.nat n, .list ((1 :: ds).map encPerm)]) (by simp)
        have w_ns1L : (Val.list ((1 :: ns).map encPerm)).wt < (encGroup ns).wt :=
          wt_le_wt_list (vs := [.nat n, .list ((1 :: ns).map encPerm)]) (by simp)
        have dv4 : Det P env3
            (.call red (mk2 (.get (arg 0) (.nat 0))
              (.call ap (mk2 (.get (.var 3) (.nat 1)) (.get (arg 1) (.nat 1))))))
            (encGroup us')
            (reduceCost hmem n (3 * (n + 1) ^ 2) + 2 * 10 ^ 8 * (n + 1) ^ 8) := by
          refine dred_raw.mono ?_
          have e_inp : (Val.list [encGroup hs, encGroup ns, encGroup us]).wt = inp.wt := rfl
          have ev3 : v3.wt = (encGroup ds).wt := rfl
          clear_value inp b1 v3 us' env1 env2 env3
          generalize reduceCost hmem n (3 * (n + 1) ^ 2) = RC at *
          generalize reduceCost hmem n (ds ++ 1 :: ns).length = RC0 at *
          omega
        set v4 := encGroup us'
        set env4 := env3 ++ [v4]
        -- step 5: `v5 = le` on `[v4, encGroup us]`
        have dv4_var := Det.var' (P := P) (env := env4) (i := 4) (v := v4) rfl
        have dus4 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
          (rest := [boolVal b1, .list (ds.map encPerm), v3, v4]) (j := 2) rfl
        have ev4_wt : v4.wt = (encGroup us').wt := rfl
        have dv5 := ob_le_det hmem hP.hle hP.hob.obk.jmem_eq ⟨us', rfl, rfl⟩ us dv4_var dus4
          (by omega) (by omega)
        set b2 := decide (gens us ≤ gens us')
        set env5 := env4 ++ [boolVal b2]
        have dv5_var := Det.var' (P := P) (env := env5) (i := 5) (v := boolVal b2) rfl
        have db2_eq : boolVal b2 = .nat (if b2 then 1 else 0) := by cases b2 <;> rfl
        rw [db2_eq] at dv5_var
        -- inner `.ite (.var 5) <nonabelian-branch> (.var 4)`
        have hite2 : EvalAll P env5
            (.ite (.var 5)
              (.letE (.call ob (mk2 (arg 2) (arg 1)))
              (.letE (.call grd (mk3 (arg 2) (arg 2) (.var 6)))
              (.letE (.call cnj (mk2 (arg 0) (.var 7)))
                (.call grd (mk3 (arg 0) (arg 2) (.var 8))))))
              (.var 4))
            (fun w c => TcStepOut (gens hs) (gens ns) (gens us) w ∧
              c ≤ obCost hmb hpre hmem n +
                tcGreedyCost hnc hmem n (tcObIndexBd n) +
                tcConjCost hni hmem n +
                tcGreedyCost hnc hmem n (tcConjIndexBd n) +
                2 * 10 ^ 19 * (n + 1) ^ 18) := by
          refine (sup_ite dv5_var
            (R := fun w ce => TcStepOut (gens hs) (gens ns) (gens us) w ∧
              ce ≤ obCost hmb hpre hmem n +
                tcGreedyCost hnc hmem n (tcObIndexBd n) +
                tcConjCost hni hmem n +
                tcGreedyCost hnc hmem n (tcConjIndexBd n) +
                10 ^ 19 * (n + 1) ^ 18)
            (fun ht2 => ?_) (fun he2 => ?_)).mono fun w c h_ite2 => ?_
          · -- nonabelian branch `b2 = true`: `gens us ≤ ⁅gens us, gens us⁆ ⊔ gens ns`
            have hb2_true : gens us ≤ ⁅gens us, gens us⁆ ⊔ gens ns := by
              rw [← hgens_us']
              by_contra hnot; simp [b2, hnot] at ht2
            -- call 1: `obEntry` on `[encGroup us, encGroup ns]`
            have dus5 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
              (rest := [boolVal b1, .list (ds.map encPerm), v3, v4, boolVal b2]) (j := 2) rfl
            have dns5 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
              (rest := [boolVal b1, .list (ds.map encPerm), v3, v4, boolVal b2]) (j := 1) rfl
            have dob_arg := Det.mk2 dus5 dns5
            have hob_raw := obEntry_spec hMa hP.hob hn1 hUH hNU hb1_false hnN (htrN hn1) hl_us hl_ns
            have sv6 : EvalAll P env5 (.call ob (mk2 (arg 2) (arg 1)))
                (fun v6 c =>
                  (∃ ys : List (Perm (Fin n)), v6 = encGroup ys ∧ ys.length ≤ n ^ 2 ∧
                    gens ns ≤ gens ys ∧ gens ys ≤ gens us ∧ ¬ (gens us ≤ gens ys) ∧
                    (∀ g ∈ gens us, ∀ x ∈ gens ys, g * x * g⁻¹ ∈ gens ys) ∧
                    ((gens ys).subgroupOf (gens us)).index ≤ tcObIndexBd n) ∧
                  c ≤ obCost hmb hpre hmem n + 10 ^ 6 * (n + 1) ^ 6) := by
              refine EvalAll.call_funAll dob_arg fun v ca hv => ?_
              obtain ⟨rfl, hca⟩ := hv
              refine hob_raw.mono fun w cb hw => ?_
              obtain ⟨⟨ys, rfl, hl_ys, hNY, hYU, hnotY, hnY, hindY⟩, hcb⟩ := hw
              refine ⟨⟨ys, rfl, hl_ys, hNY, hYU, hnotY, hnY, hindY⟩, ?_⟩
              clear hob_raw dob_arg dns5 dus5
              have wys := wt_encGroup_le_sq hl_ys
              have w2_ob := wt_list2_le (encGroup us) (encGroup ns)
              have e_inp : (Val.list [encGroup hs, encGroup ns, encGroup us]).wt = inp.wt := rfl
              clear_value inp b1 v3 us' v4 b2 env1 env2 env3 env4 env5
              generalize obCost hmb hpre hmem n = OBC at *
              omega
            -- steps 7..9 inside `ob_letAll`
            have s7_9 : ∀ v6,
                (∃ ys : List (Perm (Fin n)), v6 = encGroup ys ∧ ys.length ≤ n ^ 2 ∧
                  gens ns ≤ gens ys ∧ gens ys ≤ gens us ∧ ¬ (gens us ≤ gens ys) ∧
                  (∀ g ∈ gens us, ∀ x ∈ gens ys, g * x * g⁻¹ ∈ gens ys) ∧
                  ((gens ys).subgroupOf (gens us)).index ≤ tcObIndexBd n) →
                EvalAll P (env5 ++ [v6])
                  (.letE (.call grd (mk3 (arg 2) (arg 2) (.var 6)))
                  (.letE (.call cnj (mk2 (arg 0) (.var 7)))
                    (.call grd (mk3 (arg 0) (arg 2) (.var 8)))))
                  (fun w c => TcStepOut (gens hs) (gens ns) (gens us) w ∧
                    c ≤ tcGreedyCost hnc hmem n (tcObIndexBd n) +
                      tcConjCost hni hmem n +
                      tcGreedyCost hnc hmem n (tcConjIndexBd n) +
                      5 * 10 ^ 18 * (n + 1) ^ 18) := by
              intro v6 hv6
              obtain ⟨ys, rfl, hl_ys, hNY, hYU, hnotY, hnY, hindY⟩ := hv6
              have wys := wt_encGroup_le_sq hl_ys
              set env6 := env5 ++ [encGroup ys]
              -- call 2: `tcGreedyEntry` with `A = U` on `[encGroup us, encGroup us, encGroup ys]`
              have dus6 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
                (rest := [boolVal b1, .list (ds.map encPerm), v3, v4, boolVal b2, encGroup ys])
                (j := 2) rfl
              have dv6_var := Det.var' (P := P) (env := env6) (i := 6) (v := encGroup ys) rfl
              have dgrd1_arg := Det.mk3 dus6 dus6 dv6_var
              have hgrd1_raw := tcGreedyEntry_spec hP.hgrd hYU le_rfl hnotY
                (fun g hg x hx => (gens us).mul_mem ((gens us).mul_mem hg hx) ((gens us).inv_mem hg))
                hnY hindY hl_us hl_us hl_ys
              have sv7 : EvalAll P env6 (.call grd (mk3 (arg 2) (arg 2) (.var 6)))
                  (fun v7 c =>
                    (∃ ms : List (Perm (Fin n)), v7 = encGroup ms ∧ ms.length ≤ n ^ 2 ∧
                      IsNonabelianSimpleNormal (gens us) (gens ns) (gens ms)) ∧
                    c ≤ tcGreedyCost hnc hmem n (tcObIndexBd n) + 10 ^ 6 * (n + 1) ^ 6) := by
                refine EvalAll.call_funAll dgrd1_arg fun v ca hv => ?_
                obtain ⟨rfl, hca⟩ := hv
                refine hgrd1_raw.mono fun w cb hw => ?_
                obtain ⟨⟨ms, rfl, hl_ms, hYM, hMU, hnotM, hnM, hmaxM⟩, hcb⟩ := hw
                have hNM : gens ns ≤ gens ms := hNY.trans hYM
                obtain ⟨hsimpleM, hncM⟩ :=
                  simple_and_noncomm_of_maximal hNM hMU hnotM hb2_true hnM hmaxM
                have hM_norm : ((gens ms).subgroupOf (gens us)).Normal := rad_subgroupOf_normal hnM
                refine ⟨⟨ms, rfl, hl_ms, hNM, hMU, hnM, hM_norm, hsimpleM, hncM⟩, ?_⟩
                clear hgrd1_raw dgrd1_arg dv6_var dus6
                have wms := wt_encGroup_le_sq hl_ms
                have w3_g1 := wt_list3_le (encGroup us) (encGroup us) (encGroup ys)
                have e_inp : (Val.list [encGroup hs, encGroup ns, encGroup us]).wt = inp.wt := rfl
                clear_value inp b1 v3 us' v4 b2 env1 env2 env3 env4 env5 env6
                generalize tcGreedyCost hnc hmem n (tcObIndexBd n) = GC1 at *
                omega
              -- steps 8..9 inside `ob_letAll`
              have s8_9 : ∀ v7,
                  (∃ ms : List (Perm (Fin n)), v7 = encGroup ms ∧ ms.length ≤ n ^ 2 ∧
                    IsNonabelianSimpleNormal (gens us) (gens ns) (gens ms)) →
                  EvalAll P (env6 ++ [v7])
                    (.letE (.call cnj (mk2 (arg 0) (.var 7)))
                      (.call grd (mk3 (arg 0) (arg 2) (.var 8))))
                    (fun w c => TcStepOut (gens hs) (gens ns) (gens us) w ∧
                      c ≤ tcConjCost hni hmem n +
                        tcGreedyCost hnc hmem n (tcConjIndexBd n) +
                        10 ^ 18 * (n + 1) ^ 18) := by
                intro v7 hv7
                obtain ⟨ms, rfl, hl_ms, hM_simple⟩ := hv7
                have wms := wt_encGroup_le_sq hl_ms
                set env7 := env6 ++ [encGroup ms]
                -- call 3: `tcConjEntry` on `[encGroup hs, encGroup ms]`
                have dhs7 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
                  (rest := [boolVal b1, .list (ds.map encPerm), v3, v4, boolVal b2,
                    encGroup ys, encGroup ms]) (j := 0) rfl
                have dv7_var := Det.var' (P := P) (env := env7) (i := 7) (v := encGroup ms) rfl
                have dcnj_arg := Det.mk2 dhs7 dv7_var
                have hcnj_raw := tcConjEntry_spec hP.hcnj hn1 hUH hnU hnN (htrN hn1)
                  hM_simple hl_hs hl_ms
                have sv8 : EvalAll P env7 (.call cnj (mk2 (arg 0) (.var 7)))
                    (fun v8 c =>
                      (∃ ws : List (Perm (Fin n)), v8 = encGroup ws ∧ ws.length ≤ n ^ 2 ∧
                        gens ns ≤ gens ws ∧ gens ws ≤ gens us ∧ ¬ (gens us ≤ gens ws) ∧
                        (∀ g ∈ gens hs, ∀ x ∈ gens ws, g * x * g⁻¹ ∈ gens ws) ∧
                        ((gens ws).subgroupOf (gens us)).index ≤ tcConjIndexBd n) ∧
                      c ≤ tcConjCost hni hmem n + 10 ^ 6 * (n + 1) ^ 6) := by
                  refine EvalAll.call_funAll dcnj_arg fun v ca hv => ?_
                  obtain ⟨rfl, hca⟩ := hv
                  refine hcnj_raw.mono fun w cb hw => ?_
                  obtain ⟨⟨ws, rfl, hl_ws, hNW, hWU, hnotW, hnW, hindW⟩, hcb⟩ := hw
                  refine ⟨⟨ws, rfl, hl_ws, hNW, hWU, hnotW, hnW, hindW⟩, ?_⟩
                  clear hcnj_raw dcnj_arg dv7_var dhs7
                  have wws := wt_encGroup_le_sq hl_ws
                  have w2_cnj := wt_list2_le (encGroup hs) (encGroup ms)
                  have e_inp : (Val.list [encGroup hs, encGroup ns, encGroup us]).wt = inp.wt := rfl
                  clear_value inp b1 v3 us' v4 b2 env1 env2 env3 env4 env5 env6 env7
                  generalize tcConjCost hni hmem n = CC at *
                  omega
                -- step 9: `tcGreedyEntry` with `A = H` on `[encGroup hs, encGroup us, encGroup ws]`
                have s9 : ∀ v8,
                    (∃ ws : List (Perm (Fin n)), v8 = encGroup ws ∧ ws.length ≤ n ^ 2 ∧
                      gens ns ≤ gens ws ∧ gens ws ≤ gens us ∧ ¬ (gens us ≤ gens ws) ∧
                      (∀ g ∈ gens hs, ∀ x ∈ gens ws, g * x * g⁻¹ ∈ gens ws) ∧
                      ((gens ws).subgroupOf (gens us)).index ≤ tcConjIndexBd n) →
                    EvalAll P (env7 ++ [v8]) (.call grd (mk3 (arg 0) (arg 2) (.var 8)))
                      (fun w c => TcStepOut (gens hs) (gens ns) (gens us) w ∧
                        c ≤ tcGreedyCost hnc hmem n (tcConjIndexBd n) + 10 ^ 6 * (n + 1) ^ 6) := by
                  intro v8 hv8
                  obtain ⟨ws, rfl, hl_ws, hNW, hWU, hnotW, hnW, hindW⟩ := hv8
                  have wws := wt_encGroup_le_sq hl_ws
                  set env8 := env7 ++ [encGroup ws]
                  have dhs8 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
                    (rest := [boolVal b1, .list (ds.map encPerm), v3, v4, boolVal b2,
                      encGroup ys, encGroup ms, encGroup ws]) (j := 0) rfl
                  have dus8 := Det.arg' (P := P) (vs := [encGroup hs, encGroup ns, encGroup us])
                    (rest := [boolVal b1, .list (ds.map encPerm), v3, v4, boolVal b2,
                      encGroup ys, encGroup ms, encGroup ws]) (j := 2) rfl
                  have dv8_var := Det.var' (P := P) (env := env8) (i := 8) (v := encGroup ws) rfl
                  have dgrd2_arg := Det.mk3 dhs8 dus8 dv8_var
                  have hgrd2_raw := tcGreedyEntry_spec hP.hgrd hWU hUH hnotW hnU hnW hindW
                    hl_hs hl_us hl_ws
                  refine EvalAll.call_funAll dgrd2_arg fun v ca hv => ?_
                  obtain ⟨rfl, hca⟩ := hv
                  refine hgrd2_raw.mono fun w cb hw => ?_
                  obtain ⟨⟨vs, rfl, hl_vs, hWV, hVU, hnotV, hnV, hmaxV⟩, hcb⟩ := hw
                  have hNV : gens ns ≤ gens vs := hNW.trans hWV
                  have hltV : gens vs < gens us :=
                    lt_of_le_of_ne hVU fun heq => hnotV heq.symm.le
                  refine ⟨⟨vs, rfl, hl_vs, hNV, hVU, hnV,
                    Or.inr (GI.CitedChecks.two_mul_card_le_of_lt hltV), ?_⟩, ?_⟩
                  · intro _ M hMV hMU hnM
                    rw [sup_eq_right.mpr hNV] at hMV ⊢
                    rw [sup_eq_right.mpr hNU] at hMU ⊢
                    exact hmaxV M hMV hMU hnM
                  · clear hgrd2_raw dgrd2_arg dv8_var dus8 dhs8
                    have wvs := wt_encGroup_le_sq hl_vs
                    have w3_g2 := wt_list3_le (encGroup hs) (encGroup us) (encGroup ws)
                    have e_inp : (Val.list [encGroup hs, encGroup ns, encGroup us]).wt = inp.wt := rfl
                    clear_value inp b1 v3 us' v4 b2 env1 env2 env3 env4 env5 env6 env7 env8
                    generalize tcGreedyCost hnc hmem n (tcConjIndexBd n) = GC2 at *
                    omega
                refine (ob_letAll TcStepOut.wt_le sv8 s9).mono fun w c h => ⟨h.1, ?_⟩
                have hc := h.2
                clear s9 sv8 hcnj_raw dcnj_arg dv7_var dhs7
                clear_value inp b1 v3 us' v4 b2 env1 env2 env3 env4 env5 env6 env7
                generalize tcConjCost hni hmem n = CC at *
                generalize tcGreedyCost hnc hmem n (tcConjIndexBd n) = GC2 at *
                omega
              refine (ob_letAll TcStepOut.wt_le sv7 s8_9).mono fun w c h => ⟨h.1, ?_⟩
              have hc := h.2
              clear s8_9 sv7 hgrd1_raw dgrd1_arg dv6_var dus6
              clear_value inp b1 v3 us' v4 b2 env1 env2 env3 env4 env5 env6
              generalize tcGreedyCost hnc hmem n (tcObIndexBd n) = GC1 at *
              generalize tcConjCost hni hmem n = CC at *
              generalize tcGreedyCost hnc hmem n (tcConjIndexBd n) = GC2 at *
              omega
            refine (ob_letAll TcStepOut.wt_le sv6 s7_9).mono fun w c h => ⟨h.1, ?_⟩
            have hc := h.2
            clear s7_9 sv6 hob_raw dob_arg dns5 dus5
            clear_value inp b1 v3 us' v4 b2 env1 env2 env3 env4 env5
            generalize obCost hmb hpre hmem n = OBC at *
            generalize tcGreedyCost hnc hmem n (tcObIndexBd n) = GC1 at *
            generalize tcConjCost hni hmem n = CC at *
            generalize tcGreedyCost hnc hmem n (tcConjIndexBd n) = GC2 at *
            omega
          · -- abelian branch `b2 = false`: `¬ (gens us ≤ ⁅gens us, gens us⁆ ⊔ gens ns)`
            have hb2_false : ¬ (gens us ≤ gens us') := by
              intro hle'; simp [b2, hle'] at he2
            have dv4' := Det.var' (P := P) (env := env5) (i := 4) (v := v4) rfl
            have hN_us' : gens ns ≤ gens us' := by
              rw [hgens_us']; exact le_sup_right
            have hU'_U : gens us' ≤ gens us := by
              rw [hgens_us']
              exact sup_le (comm_self_le _) hNU
            have hlt_us' : gens us' < gens us :=
              lt_of_le_of_ne hU'_U fun heq => hb2_false heq.symm.le
            have hn_us' : ∀ g ∈ gens hs, ∀ x ∈ gens us', g * x * g⁻¹ ∈ gens us' := by
              rw [hgens_us']
              exact sup_normalized_of_both (comm_normalized_of_normalized hnU) hnN
            refine dv4'.post fun c hc => ⟨⟨us', rfl, hl_us', hN_us', hU'_U, hn_us',
              Or.inr (GI.CitedChecks.two_mul_card_le_of_lt hlt_us'), ?_⟩, ?_⟩
            · intro hna
              exfalso
              apply hna
              rw [hgens_us']
              exact le_sup_left.trans le_sup_right
            · have ev4 : v4.wt = (encGroup us').wt := rfl
              clear_value inp b1 v3 us' v4 b2 env1 env2 env3 env4 env5
              generalize obCost hmb hpre hmem n = OBC at *
              generalize tcGreedyCost hnc hmem n (tcObIndexBd n) = GC1 at *
              generalize tcConjCost hni hmem n = CC at *
              generalize tcGreedyCost hnc hmem n (tcConjIndexBd n) = GC2 at *
              omega
          · obtain ⟨ce, ⟨hout, hce⟩, htot⟩ := h_ite2
            have hw_out := hout.wt_le
            have wb2 : (Val.nat (if b2 = true then 1 else 0)).wt ≤ 3 := by
              split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
            have e_inp : (Val.list [encGroup hs, encGroup ns, encGroup us]).wt = inp.wt := rfl
            refine ⟨hout, ?_⟩
            clear_value inp b1 v3 us' v4 b2 env1 env2 env3 env4 env5
            generalize obCost hmb hpre hmem n = OBC at *
            generalize tcGreedyCost hnc hmem n (tcObIndexBd n) = GC1 at *
            generalize tcConjCost hni hmem n = CC at *
            generalize tcGreedyCost hnc hmem n (tcConjIndexBd n) = GC2 at *
            omega
        refine (ob_letDet TcStepOut.wt_le dv3
          (ob_letDet TcStepOut.wt_le dv4
            (ob_letDet TcStepOut.wt_le dv5 hite2))).mono fun w c h => ?_
        obtain ⟨hout, hc⟩ := h
        refine ⟨hout, ?_⟩
        clear hite2 dv5_var dv5 dv4_var dus4 dv4 dred_raw du dnsL dns3 ddsL dv3_var dn3 dhs3 dv3 dv3_raw dv2_var dn2 dhs2
        clear_value inp b1 v3 us' v4 b2 env1 env2 env3 env4 env5
        generalize reduceCost hmem n (3 * (n + 1) ^ 2) = RC at *
        generalize 10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) = MB at *
        generalize obCost hmb hpre hmem n = OBC at *
        generalize tcGreedyCost hnc hmem n (tcObIndexBd n) = GC1 at *
        generalize tcConjCost hni hmem n = CC at *
        generalize tcGreedyCost hnc hmem n (tcConjIndexBd n) = GC2 at *
        omega
      refine (ob_letAll TcStepOut.wt_le sv2 s3_end).mono fun w c h => ⟨h.1, ?_⟩
      have hc := h.2
      clear s3_end sv2 hder_raw dus1
      clear_value inp b1 env1
      generalize (derivedSubgroupPrim hder).boundSize (10 ^ 4 * (n + 1) ^ 6) = DER at *
      generalize reduceCost hmem n (3 * (n + 1) ^ 2) = RC at *
      generalize 10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) = MB at *
      generalize obCost hmb hpre hmem n = OBC at *
      generalize tcGreedyCost hnc hmem n (tcObIndexBd n) = GC1 at *
      generalize tcConjCost hni hmem n = CC at *
      generalize tcGreedyCost hnc hmem n (tcConjIndexBd n) = GC2 at *
      omega
    · obtain ⟨ce, ⟨hout, hce⟩, htot⟩ := h_ite1
      have hw_out := hout.wt_le
      have wb1 : (Val.nat (if b1 = true then 1 else 0)).wt ≤ 3 := by
        split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
      have e_inp : (Val.list [encGroup hs, encGroup ns, encGroup us]).wt = inp.wt := rfl
      refine ⟨hout, ?_⟩
      clear_value inp b1 env1
      generalize (derivedSubgroupPrim hder).boundSize (10 ^ 4 * (n + 1) ^ 6) = DER at *
      generalize reduceCost hmem n (3 * (n + 1) ^ 2) = RC at *
      generalize 10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) = MB at *
      generalize obCost hmb hpre hmem n = OBC at *
      generalize tcGreedyCost hnc hmem n (tcObIndexBd n) = GC1 at *
      generalize tcConjCost hni hmem n = CC at *
      generalize tcGreedyCost hnc hmem n (tcConjIndexBd n) = GC2 at *
      omega
  refine FunAll.intro hP.entry
    ((ob_letDet TcStepOut.wt_le dv1 hite1).mono fun w c h => ?_)
  clear hite1 dv1_var dv1 dus0 dns0
  obtain ⟨hout, hc⟩ := h
  refine ⟨hout, ?_⟩
  unfold tcStepCost
  clear_value inp b1 env1
  generalize (derivedSubgroupPrim hder).boundSize (10 ^ 4 * (n + 1) ^ 6) = DER at *
  generalize reduceCost hmem n (3 * (n + 1) ^ 2) = RC at *
  generalize 10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) = MB at *
  generalize obCost hmb hpre hmem n = OBC at *
  generalize tcGreedyCost hnc hmem n (tcObIndexBd n) = GC1 at *
  generalize tcConjCost hni hmem n = CC at *
  generalize tcGreedyCost hnc hmem n (tcConjIndexBd n) = GC2 at *
  omega

end GI.Impl
