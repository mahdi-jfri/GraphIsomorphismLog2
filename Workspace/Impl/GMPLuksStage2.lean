module

public import Workspace.Impl.GMPLuksStage1
public import Workspace.Impl.GMPFactorKernel
public import Workspace.Impl.NIntInter
public import Workspace.Lang.Lib.Fold
public import Workspace.Proved.SSMembership
public import Workspace.Proved.SSPointwiseStab
public import Workspace.Proved.NClPreimage

@[expose] public section

/-!
# Stage 2 of Luks's normal-subgroup centralizer and `GI.Proved.gmpNormalCentralizer`

Starting from Stage 1's kernel `K₁` (`Workspace/Impl/GMPLuksStage1.lean`), Stage 2 iterates
`i = 0, ..., n - 1`: at step `i`, `A_i ≤ K₁` normalizes both `N` and `pointwiseStab N [i]`
(`gmpFirstStageKer_normalizes_stab`), and `pointwiseStab N [i]` has index at most `n` in `N`
(`gmpPointwiseStab_index_le`), so `gmpFactorKernelFuns` (`Workspace/Impl/GMPFactorKernel.lean`)
computes `{h ∈ A_i : ∀ u ∈ N, h * u * h⁻¹ * u⁻¹ ∈ pointwiseStab N [i]}` in polynomial time.
After `n` steps, `A_n = C_H(N)` (`gmpSecondStage_mem_iff`). A final pointwise-stabilizer call on the
empty point list returns at most `n²` generators (`GensOf`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n : ℕ}

@[simp] theorem length_gmpFactorKernelFuns (b jm jpre : ℕ) :
    (gmpFactorKernelFuns b jm jpre).length = 77 := rfl

@[simp] theorem length_mkGroupFuns (b : ℕ) : (mkGroupFuns b).length = 7 := rfl

@[simp] theorem length_iterFuns (b g : ℕ) : (iterFuns b g).length = 3 := rfl

/-! ### Stage 2 loop invariant and step -/

/-- Loop invariant after `i` steps of Stage 2: `acc` encodes `{h ∈ K₁ : ∀ j < i, [h, N] ≤ N_j}`
with weight at most `320 * (n + 1) ^ 6`. -/
def GMPStage2Inv (K₁ N : Subgroup (Perm (Fin n))) (i : ℕ) (acc : Val) : Prop :=
  ∃ A : Subgroup (Perm (Fin n)),
    GroupVal n acc A ∧ acc.wt ≤ 320 * (n + 1) ^ 6 ∧
    ∀ h, h ∈ A ↔ h ∈ K₁ ∧
      ∀ j : Fin n, (j : ℕ) < i → ∀ u ∈ N, h * u * h⁻¹ * u⁻¹ ∈ pointwiseStab N [j]

theorem gmpStage2Inv_zero {K₁ N : Subgroup (Perm (Fin n))} {kv₁ : Val}
    (hK₁ : GroupVal n kv₁ K₁) (hkw : kv₁.wt ≤ 320 * (n + 1) ^ 6) :
    GMPStage2Inv K₁ N 0 kv₁ :=
  ⟨K₁, hK₁, hkw, fun _ => ⟨fun hh => ⟨hh, fun _ hj => False.elim (Nat.not_lt_zero _ hj)⟩,
    fun hh => hh.1⟩⟩

theorem gmpStage2Inv_wt {K₁ N : Subgroup (Perm (Fin n))} {i : ℕ} {acc : Val}
    (hinv : GMPStage2Inv K₁ N i acc) : acc.wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨_, -, hw, -⟩ := hinv
  exact hw

/-- Step of Stage 2: on `[[nv, ws], .nat i, acc]`, call `gmpFactorKernelFuns` at `fk` on
`[acc, nv, ws[i]]` and wrap the resulting generators into a group value using `mkGroupFuns` at `mg`. -/
def gmpStage2Step (fk mg : ℕ) : Expr :=
  .letE (.call fk (mk3 (arg 2) (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1))))
    (.call mg (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.var 1)))

/-- Cost bound for one step of Stage 2. -/
noncomputable def gmpStage2StepCost (hm : Membership) (hpre : Preimage) (T n : ℕ) : ℕ :=
  gmpFactorKernelCost hm hpre (2 * T + 1300 * (n + 1) ^ 6) n +
    10 ^ 10 * (T + (n + 1) ^ 9)

theorem gmpStage2Step_spec (hm : Membership) (hpre : Preimage)
    {P : Program} {b fk mg jm jpre : ℕ}
    (hstep : P.funs[b]? = some (gmpStage2Step fk mg))
    (hfk : GmpFactorKernelAt P hm hpre fk jm jpre)
    (hmg : P.HasAt mg (mkGroupFuns mg))
    {H N K₁ : Subgroup (Perm (Fin n))} {nv acc : Val} {ws : List Val} {T i : ℕ}
    (hHN : Normalizes H N) (hK₁H : K₁ ≤ H)
    (hK₁ : ∀ h ∈ K₁, ∀ j : Fin n, pointwiseStab N [h j] = pointwiseStab N [j])
    (hN : GroupVal n nv N) (hnv_wt : nv.wt ≤ T) (hws : GMPStabList N ws)
    (hi : i < n) (hinv : GMPStage2Inv K₁ N i acc) :
    FunAll P b (.list [.list [nv, .list ws], .nat i, acc]) (fun w cost =>
      GMPStage2Inv K₁ N (i + 1) w ∧ cost ≤ gmpStage2StepCost hm hpre T n) := by
  obtain ⟨A, hA, hacc_wt, hA_mem⟩ := hinv
  have hAK₁ : A ≤ K₁ := fun h hh => ((hA_mem h).mp hh).1
  have hnN_A : GI.Multicoset.Normalizes A N := fun h hh => hHN h (hK₁H (hAK₁ hh))
  have hnStab_A : GI.Multicoset.Normalizes A (pointwiseStab N [⟨i, hi⟩]) :=
    gmpFirstStageKer_normalizes_stab hHN hK₁H hK₁ hAK₁ ⟨i, hi⟩
  have hws' := hws
  obtain ⟨f, hws_eq, hf⟩ := hws
  have hlen : ws.length = n := by simp [hws_eq]
  have hws_get : ws[i]? = some (f ⟨i, hi⟩) := by
    rw [List.getElem?_eq_getElem (by omega)]
    simp [hws_eq]
  have hfi_G : GroupVal n (f ⟨i, hi⟩) (pointwiseStab N [⟨i, hi⟩]) := (hf ⟨i, hi⟩).1
  have hfi_wt : (f ⟨i, hi⟩).wt ≤ 320 * (n + 1) ^ 6 := (hf ⟨i, hi⟩).2
  have hN' := hN
  obtain ⟨ns, rfl, -⟩ := hN'
  let c := Val.list [encGroup ns, .list ws]
  let step_in := Val.list [c, .nat i, acc]
  have d_c0 := Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := []) (j := 0) rfl
  have d_i := Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := []) (j := 1) rfl
  have d_acc := Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := []) (j := 2) rfl
  have d_nv := Det.get' d_c0 (Det.nat 0)
    (show [encGroup ns, Val.list ws][0]? = some (encGroup ns) from rfl)
  have d_ws := Det.get' d_c0 (Det.nat 1)
    (show [encGroup ns, Val.list ws][1]? = some (.list ws) from rfl)
  have d_fi := Det.get' d_ws d_i hws_get
  have d_fk_arg := Det.mk3 d_acc d_nv d_fi
  have hw_fk_in : (Val.list [acc, encGroup ns, f ⟨i, hi⟩]).wt ≤ 2 * T + 1300 * (n + 1) ^ 6 := by
    have := wt_list3_le acc (encGroup ns) (f ⟨i, hi⟩)
    have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨ca, da, hca⟩ : ∃ ca, Det P [step_in]
      (mk3 (arg 2) (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1)))
      (.list [acc, encGroup ns, f ⟨i, hi⟩]) ca ∧
      ca ≤ 50 * T + 50000 * (n + 1) ^ 7 := by
    refine ⟨_, d_fk_arg, ?_⟩
    have hw_ws := hws'.wt_le
    have hw_c := wt_list2_le (encGroup ns) (.list ws)
    have hw_in := wt_list3_le c (.nat i) acc
    have hw_i := wt_nat_le i
    have h6_7 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1_7 : n + 1 ≤ (n + 1) ^ 7 := Nat.le_self_pow (by omega) _
    generalize (n + 1) ^ 7 = Q7 at hw_ws h6_7 h1_7 ⊢
    generalize (n + 1) ^ 6 = Q6 at hacc_wt hfi_wt hw_fk_in h6_7
    dsimp only [c, step_in] at *
    omega
  have hfk_spec := gmpFactorKernel_spec hfk hA hN hfi_G hnN_A hnStab_A hw_fk_in
  have c_fk := EvalAll.call_funAll (f := fk) da
    (Q := fun w1 c1 => (∃ C : Subgroup (Perm (Fin n)), GensVal n w1 C ∧
        ∀ h, h ∈ C ↔ h ∈ A ∧ ∀ u ∈ N, h * u * h⁻¹ * u⁻¹ ∈ pointwiseStab N [⟨i, hi⟩]) ∧
      c1 ≤ ca + gmpFactorKernelCost hm hpre (2 * T + 1300 * (n + 1) ^ 6)
        (((pointwiseStab N [⟨i, hi⟩]).subgroupOf N).index) + w1.wt + 1)
    fun v ca' hv' => by
      obtain ⟨rfl, hca'⟩ := hv'
      exact hfk_spec.mono fun w1 cb ⟨hC, hcb⟩ => ⟨hC, by omega⟩
  refine FunAll.intro hstep (EvalAll.letE c_fk fun w1 c1 hw1 => ?_)
  obtain ⟨⟨A', hA'_gens, hA'_mem⟩, hc1⟩ := hw1
  have hw1_wt : w1.wt ≤ 13 * (n + 1) ^ 6 := GensVal.wt_le hA'_gens
  obtain ⟨hs', rfl, hhs'_len, hmg_call, hA'_group, hA'_wt⟩ := mkGroup_gensVal hmg hA'_gens
  have d_c0' := Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := [.list (hs'.map encPerm)]) (j := 0) rfl
  have d_nv' := Det.get' d_c0' (Det.nat 0)
    (show [encGroup ns, Val.list ws][0]? = some (encGroup ns) from rfl)
  have d_n := Det.encPerms_size d_nv'
  have d_w1 := Det.var' (P := P) (env := [step_in, .list (hs'.map encPerm)]) (i := 1) rfl
  have d_mg := Det.call (Det.mk2 d_n d_w1) hmg_call
  refine d_mg.post fun c2 hc2 => ⟨⟨A', hA'_group, hA'_wt, fun h => ?_⟩, ?_⟩
  · rw [hA'_mem, hA_mem]
    refine ⟨fun ⟨⟨hhK₁, hlt⟩, heq⟩ => ⟨hhK₁, fun j hj => ?_⟩,
      fun ⟨hhK₁, hall⟩ => ⟨⟨hhK₁, fun j hj => hall j (Nat.lt_succ_of_lt hj)⟩,
        hall ⟨i, hi⟩ (Nat.lt_succ_self i)⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt_i | heq_i
    · exact hlt j hlt_i
    · have hj_eq : j = ⟨i, hi⟩ := Fin.ext heq_i
      rw [hj_eq]
      exact heq
  · have hidx := gmpPointwiseStab_index_le N ⟨i, hi⟩
    have hfk_mono : gmpFactorKernelCost hm hpre (2 * T + 1300 * (n + 1) ^ 6)
        (((pointwiseStab N [⟨i, hi⟩]).subgroupOf N).index) ≤
        gmpFactorKernelCost hm hpre (2 * T + 1300 * (n + 1) ^ 6) n :=
      gmpFactorKernelCost_mono hm hpre le_rfl hidx
    have hw_ws := hws'.wt_le
    have hw_c := wt_list2_le (encGroup ns) (.list ws)
    have hw_in := wt_list3_le c (.nat i) acc
    have hw_i := wt_nat_le i
    have hw_n := wt_nat_le n
    have hw_mg_in := wt_list2_le (.nat n) (.list (hs'.map encPerm))
    have hmk_eq : 8 * mkGroupK * (n + 1) ^ 9 = 800000 * (n + 1) ^ 9 := by simp [mkGroupK]
    have h6_7 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1_7 : n + 1 ≤ (n + 1) ^ 7 := Nat.le_self_pow (by omega) _
    have h7_9 : (n + 1) ^ 7 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have h6_9 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1_9 : n + 1 ≤ (n + 1) ^ 9 := Nat.le_self_pow (by omega) _
    unfold gmpStage2StepCost
    generalize gmpFactorKernelCost hm hpre (2 * T + 1300 * (n + 1) ^ 6) n = FKC at hfk_mono ⊢
    generalize gmpFactorKernelCost hm hpre (2 * T + 1300 * (n + 1) ^ 6)
      (((pointwiseStab N [⟨i, hi⟩]).subgroupOf N).index) = FKC0 at hfk_mono hc1
    generalize 8 * mkGroupK * (n + 1) ^ 9 = MKC at hmk_eq hc2
    generalize (n + 1) ^ 9 = Q9 at hmk_eq h7_9 h6_9 h1_9 ⊢
    generalize (n + 1) ^ 7 = Q7 at hca hw_ws h6_7 h1_7 h7_9
    generalize (n + 1) ^ 6 = Q6 at hacc_wt hfi_wt hw_fk_in hw1_wt hA'_wt h6_7 h6_9
    dsimp only [c, step_in] at *
    omega

/-! ### Complete two-stage normal-subgroup centralizer -/

/-- On `[hv, nv]`: run Stage 1 (`s1`), then Stage 2 (`it` for `n` steps), then call `pointwiseStab`
at `jp` on `[acc_n, []]` to output at most `n²` generators. -/
def gmpNormalCentralizerEntry (s1 it jp : ℕ) : Expr :=
  .letE (.call s1 (.var 0))
    (.letE (.call it (mk3 (mk2 (arg 1) (.get (.var 1) (.nat 1)))
        (.get (arg 1) (.nat 0)) (.get (.var 1) (.nat 0))))
      (.prim jp (mk2 (.var 2) .nil)))

/-- Luks's two-stage normal-subgroup centralizer, at base `b` (138 functions), with membership at
`jm`, pointwise stabilizer at `jp`, and preimage at `jpre`. -/
def gmpNormalCentralizerFuns (b jm jp jpre : ℕ) : List Expr :=
  [gmpNormalCentralizerEntry (b + 1) (b + 50) jp] ++
    gmpStage1Funs (b + 1) jm jp jpre ++
    iterFuns (b + 50) (b + 53) ++
    [gmpStage2Step (b + 54) (b + 131)] ++
    gmpFactorKernelFuns (b + 54) jm jpre ++
    mkGroupFuns (b + 131)

/-- Total cost bound for `gmpNormalCentralizerFuns` on an input `[hv, nv]` of weight `T`. -/
noncomputable def gmpNormalCentralizerCost (hm : Membership) (hps : PointwiseStab)
    (hpre : Preimage) (T : ℕ) : ℕ :=
  gmpStage1Cost hm hps hpre T T +
    (T + 1) * gmpStage2StepCost hm hpre T T +
    (pointwiseStabPrim hps).boundSize (320 * (T + 1) ^ 6 + 10) +
    10 ^ 20 * (T + 1) ^ 18

theorem gmpEqGroupCost_mono (hm : Membership) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    gmpEqGroupCost hm n₁ ≤ gmpEqGroupCost hm n₂ := by
  unfold gmpEqGroupCost
  have h6 : (n₁ + 1) ^ 6 ≤ (n₂ + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have h18 : (n₁ + 1) ^ 18 ≤ (n₂ + 1) ^ 18 := Nat.pow_le_pow_left (by omega) 18
  have hbs : (membershipPrim hm).boundSize (700 * (n₁ + 1) ^ 6) ≤
      (membershipPrim hm).boundSize (700 * (n₂ + 1) ^ 6) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul h6 hbs)) (Nat.mul_le_mul_left _ h18)

theorem gmpFindStabCost_mono (hm : Membership) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    gmpFindStabCost hm n₁ ≤ gmpFindStabCost hm n₂ := by
  unfold gmpFindStabCost
  exact Nat.add_le_add (Nat.mul_le_mul (by omega) (gmpEqGroupCost_mono hm hn))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 8))

theorem gmpStabReprCost_mono (hm : Membership) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    gmpStabReprCost hm n₁ ≤ gmpStabReprCost hm n₂ := by
  unfold gmpStabReprCost
  exact Nat.add_le_add (Nat.mul_le_mul (by omega) (gmpFindStabCost_mono hm hn))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 8))

theorem gmpStage1Cost_mono_n (hm : Membership) (hps : PointwiseStab) (hpre : Preimage)
    (T : ℕ) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    gmpStage1Cost hm hps hpre T n₁ ≤ gmpStage1Cost hm hps hpre T n₂ := by
  unfold gmpStage1Cost gmpStabListCost
  have h1 : (n₁ + 1) * gmpStabOneCost hps T + 10 ^ 10 * (T + (n₁ + 1) ^ 8) ≤
      (n₂ + 1) * gmpStabOneCost hps T + 10 ^ 10 * (T + (n₂ + 1) ^ 8) :=
    Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.pow_le_pow_left (by omega) 8) _))
  have h2 := gmpStabReprCost_mono hm hn
  have h2_pow : (n₁ + 1) ^ 2 ≤ (n₂ + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : (preimagePrim hpre).boundSize (10 * T + 50 * (n₁ + 1) ^ 2) ≤
      (preimagePrim hpre).boundSize (10 * T + 50 * (n₂ + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have h4 : 10 ^ 20 * (T + n₁ + 1) ^ 18 ≤ 10 ^ 20 * (T + n₂ + 1) ^ 18 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 18)
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2) h3) h4

theorem gmpStage2StepCost_mono_n (hm : Membership) (hpre : Preimage)
    (T : ℕ) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    gmpStage2StepCost hm hpre T n₁ ≤ gmpStage2StepCost hm hpre T n₂ := by
  unfold gmpStage2StepCost
  have h6 : (n₁ + 1) ^ 6 ≤ (n₂ + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have h9 : (n₁ + 1) ^ 9 ≤ (n₂ + 1) ^ 9 := Nat.pow_le_pow_left (by omega) 9
  exact Nat.add_le_add (gmpFactorKernelCost_mono hm hpre (by omega) hn)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left h9 _))

theorem gmpNormalCentralizer_spec (hm : Membership) (hps : PointwiseStab) (hpre : Preimage)
    {P : Program} {b jm jp jpre : ℕ}
    (hb : P.HasAt b (gmpNormalCentralizerFuns b jm jp jpre))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjps : P.prims[jp]? = some (pointwiseStabPrim hps))
    (hjpre : P.prims[jpre]? = some (preimagePrim hpre))
    {hv nv : Val} {H N : Subgroup (Perm (Fin n))}
    (hH : GroupVal n hv H) (hN : GroupVal n nv N) (hHN : Normalizes H N) :
    FunAll P b (.list [hv, nv]) (fun w cost =>
      GMPNormCentOut H N w ∧
      cost ≤ gmpNormalCentralizerCost hm hps hpre (Val.list [hv, nv]).wt) := by
  simp only [gmpNormalCentralizerFuns] at hb
  have hentry : P.funs[b]? = some (gmpNormalCentralizerEntry (b + 1) (b + 50) jp) :=
    hb.left.left.left.left.left.single
  have hs1 : P.HasAt (b + 1) (gmpStage1Funs (b + 1) jm jp jpre) := by
    simpa using hb.left.left.left.left.right
  have hit : P.HasAt (b + 50) (iterFuns (b + 50) (b + 53)) := by
    simpa [Nat.add_assoc] using hb.left.left.left.right
  have hstep : P.funs[b + 53]? = some (gmpStage2Step (b + 54) (b + 131)) := by
    simpa [Nat.add_assoc] using hb.left.left.right.single
  have hfk_hasAt : P.HasAt (b + 54) (gmpFactorKernelFuns (b + 54) jm jpre) := by
    simpa [Nat.add_assoc] using hb.left.right
  have hfk : GmpFactorKernelAt P hm hpre (b + 54) jm jpre :=
    gmpFactorKernelAt_of hfk_hasAt hjm hjpre
  have hmg : P.HasAt (b + 131) (mkGroupFuns (b + 131)) := by
    simpa [Nat.add_assoc] using hb.right
  have hN' := hN
  obtain ⟨ns, rfl, -⟩ := hN'
  set T := (Val.list [hv, encGroup ns]).wt with hT_def
  have hhv_lt : hv.wt < T := wt_le_wt_list (by simp)
  have hnv_lt : (encGroup ns).wt < T := wt_le_wt_list (by simp)
  have hS := S_le_wt_encGroup ns
  obtain ⟨-, hnS⟩ := le_S ns.length n
  have hn_T : n + 1 ≤ T := by omega
  -- Step 1: call `gmpStage1Funs` on `[hv, encGroup ns]`
  have d_in := Det.var' (P := P) (env := [Val.list [hv, encGroup ns]]) (i := 0) rfl
  have c_s1 := EvalAll.call_funAll (f := b + 1) d_in
    (Q := fun w1 c1 => ∃ kv₁ ws K₁, w1 = .list [kv₁, .list ws] ∧
      GroupVal n kv₁ K₁ ∧ kv₁.wt ≤ 320 * (n + 1) ^ 6 ∧
      (∀ h, h ∈ K₁ ↔ h ∈ H ∧ ∀ i : Fin n, pointwiseStab N [h i] = pointwiseStab N [i]) ∧
      GMPStabList N ws ∧
      c1 ≤ (T + 1) + gmpStage1Cost hm hps hpre T n + w1.wt + 1)
    fun v ca hv' => by
      obtain ⟨rfl, hca⟩ := hv'
      exact (gmpStage1_spec hm hps hpre hs1 hjm hjps hjpre hH hN hHN).mono
        fun w1 cb ⟨kv₁, ws, K₁, hw1, hK₁, hkw, hK₁_mem, hws, hcb⟩ =>
          ⟨kv₁, ws, K₁, hw1, hK₁, hkw, hK₁_mem, hws, by rw [← hT_def] at hcb; omega⟩
  refine FunAll.intro hentry (EvalAll.letE c_s1 fun w1 c1 hw1 => ?_)
  obtain ⟨kv₁, ws, K₁, rfl, hK₁, hkw, hK₁_mem, hws, hc1⟩ := hw1
  have hK₁H : K₁ ≤ H := fun h hh => ((hK₁_mem h).mp hh).1
  have hK₁_stab : ∀ h ∈ K₁, ∀ j : Fin n, pointwiseStab N [h j] = pointwiseStab N [j] :=
    fun h hh => ((hK₁_mem h).mp hh).2
  -- Step 2: call `iterFuns` on `[[encGroup ns, ws], .nat n, kv₁]`
  have d_nv := Det.arg' (P := P) (vs := [hv, encGroup ns]) (rest := [.list [kv₁, .list ws]]) (j := 1) rfl
  have d_w1 := Det.var' (P := P) (env := [Val.list [hv, encGroup ns], .list [kv₁, .list ws]]) (i := 1) rfl
  have d_ws := Det.get' d_w1 (Det.nat 1)
    (show [kv₁, Val.list ws][1]? = some (.list ws) from rfl)
  have d_n := Det.encPerms_size d_nv
  have d_kv₁ := Det.get' d_w1 (Det.nat 0)
    (show [kv₁, Val.list ws][0]? = some kv₁ from rfl)
  have d_it_arg := Det.mk3 (Det.mk2 d_nv d_ws) d_n d_kv₁
  let it_in := Val.list [.list [encGroup ns, .list ws], .nat n, kv₁]
  obtain ⟨ca2, da2, hca2⟩ : ∃ ca2, Det P [Val.list [hv, encGroup ns], .list [kv₁, .list ws]]
      (mk3 (mk2 (arg 1) (.get (.var 1) (.nat 1)))
        (.get (arg 1) (.nat 0)) (.get (.var 1) (.nat 0)))
      it_in ca2 ∧ ca2 ≤ 50 * T + 50000 * (n + 1) ^ 7 := by
    refine ⟨_, d_it_arg, ?_⟩
    have hw_ws := hws.wt_le
    have hw_w1 := wt_list2_le kv₁ (.list ws)
    have hw_c := wt_list2_le (encGroup ns) (.list ws)
    have hw_it := wt_list3_le (.list [encGroup ns, .list ws]) (.nat n) kv₁
    have hw_n := wt_nat_le n
    have h6_7 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1_7 : n + 1 ≤ (n + 1) ^ 7 := Nat.le_self_pow (by omega) _
    generalize (n + 1) ^ 7 = Q7 at hw_ws h6_7 h1_7 ⊢
    generalize (n + 1) ^ 6 = Q6 at hkw h6_7
    omega
  have hiter := iter_spec hit (c := .list [encGroup ns, .list ws]) (k := n) (acc0 := kv₁)
    (Inv := GMPStage2Inv K₁ N) (M := 320 * (n + 1) ^ 6)
    (B := fun _ => gmpStage2StepCost hm hpre T n)
    (gmpStage2Inv_zero hK₁ hkw)
    (fun _ _ _ hinv => gmpStage2Inv_wt hinv)
    (fun i acc hi hinv =>
      gmpStage2Step_spec hm hpre hstep hfk hmg hHN hK₁H hK₁_stab hN hnv_lt.le hws hi hinv)
  have c_it := EvalAll.call_funAll (f := b + 50) da2
    (Q := fun acc_n c2 => GMPStage2Inv K₁ N n acc_n ∧
      c2 ≤ ca2 + (∑ _i ∈ Finset.range n, gmpStage2StepCost hm hpre T n +
        loopModK * (n + 1) * (it_in.wt + n + 320 * (n + 1) ^ 6 + 1)) + acc_n.wt + 1)
    fun v ca' hv' => by
      obtain ⟨rfl, hca'⟩ := hv'
      exact hiter.mono fun acc_n cb ⟨hinv, hcb⟩ => ⟨hinv, by dsimp only [it_in] at *; omega⟩
  refine EvalAll.letE c_it fun acc_n c2 hacc_n => ?_
  obtain ⟨⟨A_n, hAn_G, hAn_wt, hAn_mem⟩, hc2⟩ := hacc_n
  -- Step 3: final `.prim jp (mk2 (.var 2) .nil)` call to extract `GensVal n w A_n`
  have d_acc_n := Det.var' (P := P)
    (env := [Val.list [hv, encGroup ns], .list [kv₁, .list ws], acc_n]) (i := 2) rfl
  have d_final := Det.mk2 d_acc_n Det.nil
  have hnil : Val.list [] = encPts ([] : List (Fin n)) := rfl
  rw [hnil] at d_final
  have c_ps := pointwiseStab_call hps hjps d_final hAn_G
  refine c_ps.mono ?_
  rintro w c3 ⟨hgens, hc3⟩
  rw [nint_pointwiseStab_nil] at hgens
  have hAn_cent : ∀ h, h ∈ A_n ↔ h ∈ H ∧ ∀ u ∈ N, h * u * h⁻¹ * u⁻¹ ∈ (⊥ : Subgroup (Perm (Fin n))) := by
    have hiff := gmpSecondStage_mem_iff hK₁_mem
      (fun h => (hAn_mem h).trans (and_congr_right fun _ =>
        ⟨fun hall j => hall j j.isLt, fun hall j _ => hall j⟩))
    intro h
    rw [hiff h]
    simp only [Subgroup.mem_bot]
  refine ⟨⟨A_n, hgens, hAn_cent⟩, ?_⟩
  -- Cost bound arithmetic
  have hsum : (∑ _i ∈ Finset.range n, gmpStage2StepCost hm hpre T n) =
      n * gmpStage2StepCost hm hpre T n := by
    simp
  rw [hsum] at hc2
  have hn_le_T : n ≤ T := by omega
  have hs1_mono : gmpStage1Cost hm hps hpre T n ≤ gmpStage1Cost hm hps hpre T T :=
    gmpStage1Cost_mono_n hm hps hpre T hn_le_T
  have hstep_mono : n * gmpStage2StepCost hm hpre T n ≤
      (T + 1) * gmpStage2StepCost hm hpre T T :=
    Nat.mul_le_mul (by omega) (gmpStage2StepCost_mono_n hm hpre T hn_le_T)
  have hsz_ps : (Val.list [acc_n, encPts ([] : List (Fin n))]).size ≤
      320 * (T + 1) ^ 6 + 10 := by
    rw [size_list2, ← hnil]
    have e : (Val.list []).size ≤ 4 := (Val.list []).size_le_wt
    have e2 : (Val.list []).wt = 4 := rfl
    have h1 := acc_n.size_le_wt
    have h2 : (n + 1) ^ 6 ≤ (T + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    omega
  have hps_bd := (pointwiseStabPrim hps).bound_le hsz_ps
  have hw_ws := hws.wt_le
  have hw_w1 := wt_list2_le kv₁ (.list ws)
  have hw_c := wt_list2_le (encGroup ns) (.list ws)
  have hw_it := wt_list3_le (.list [encGroup ns, .list ws]) (.nat n) kv₁
  have hw_n := wt_nat_le n
  have hw_ps_in : (Val.list [acc_n, encPts ([] : List (Fin n))]).wt ≤
      640 * (n + 1) ^ 6 + 20 := by
    rw [← hnil]
    have := wt_list2_le acc_n (.list [])
    have : (Val.list []).wt = 4 := rfl
    omega
  have hw_out : w.wt ≤ 13 * (n + 1) ^ 6 := GensVal.wt_le hgens
  have h6_7 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1_7 : n + 1 ≤ (n + 1) ^ 7 := Nat.le_self_pow (by omega) _
  have hloop_it : loopModK * (n + 1) * (it_in.wt + n + 320 * (n + 1) ^ 6 + 1) ≤
      10 ^ 10 * (T + 1) ^ 18 := by
    have hit_le : it_in.wt + n + 320 * (n + 1) ^ 6 + 1 ≤ 5000 * (T + 1) ^ 7 := by
      have hT7 : T ≤ (T + 1) ^ 7 := (by omega : T ≤ T + 1).trans (Nat.le_self_pow (by omega) _)
      have hn7 : (n + 1) ^ 7 ≤ (T + 1) ^ 7 := Nat.pow_le_pow_left (by omega) 7
      have h1 : 1 ≤ (T + 1) ^ 7 := Nat.one_le_pow _ _ (by omega)
      dsimp only [it_in] at *
      omega
    calc loopModK * (n + 1) * (it_in.wt + n + 320 * (n + 1) ^ 6 + 1)
        ≤ 1000 * (T + 1) * (5000 * (T + 1) ^ 7) :=
          Nat.mul_le_mul (by simp [loopModK]; omega) hit_le
      _ = 5000000 * (T + 1) ^ 8 := by ring
      _ ≤ 10 ^ 10 * (T + 1) ^ 18 :=
          Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right (by omega) (by omega))
  have h7_18 : (n + 1) ^ 7 ≤ (T + 1) ^ 18 :=
    (Nat.pow_le_pow_left (by omega : n + 1 ≤ T + 1) 7).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have h6_18 : (n + 1) ^ 6 ≤ (T + 1) ^ 18 :=
    (Nat.pow_le_pow_left (by omega : n + 1 ≤ T + 1) 6).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hT_18 : T ≤ (T + 1) ^ 18 :=
    (by omega : T ≤ T + 1).trans (Nat.le_self_pow (by omega) _)
  have h1_18 : 1 ≤ (T + 1) ^ 18 := Nat.one_le_pow _ _ (by omega)
  unfold gmpNormalCentralizerCost
  generalize gmpStage1Cost hm hps hpre T T = S1C at hs1_mono ⊢
  generalize gmpStage1Cost hm hps hpre T n = S1C0 at hs1_mono hc1
  generalize (T + 1) * gmpStage2StepCost hm hpre T T = S2C at hstep_mono ⊢
  generalize n * gmpStage2StepCost hm hpre T n = S2C0 at hstep_mono hc2
  generalize (pointwiseStabPrim hps).boundSize (320 * (T + 1) ^ 6 + 10) = PSB at hps_bd ⊢
  generalize (pointwiseStabPrim hps).bound (.list [acc_n, encPts ([] : List (Fin n))]) = PSB0 at hps_bd hc3
  generalize loopModK * (n + 1) * (it_in.wt + n + 320 * (n + 1) ^ 6 + 1) = LIT at hloop_it hc2
  generalize (T + 1) ^ 18 = Q18 at hloop_it h7_18 h6_18 hT_18 h1_18 ⊢
  generalize (n + 1) ^ 7 = Q7 at hca2 hw_ws h6_7 h1_7 h7_18
  generalize (n + 1) ^ 6 = Q6 at hkw hAn_wt hw_ps_in hw_out hc3 h6_7 h6_18
  omega

/-! ### Polynomial cost bound and `GI.Proved.gmpNormalCentralizer` -/

theorem gmpBoundSize_poly (p : Prim) {B : ℕ → ℕ → ℕ → ℕ} (hB : PBU B) :
    PBU (fun n W I => p.boundSize (B n W I)) :=
  ((hB.addc 2).pow p.k).smul p.c

theorem gmpEqGroupCost_poly (hm : Membership) :
    PBU (fun _ T _ => gmpEqGroupCost hm T) := by
  have h6 : PBU (fun _ T _ => (T + 1) ^ 6) := (PBU.W.addc 1).pow 6
  have hbs := gmpBoundSize_poly (membershipPrim hm) (h6.smul 700)
  exact ((h6.mul hbs).smul 2600).add (((PBU.W.addc 1).pow 18).smul (10 ^ 14))

theorem gmpFindStabCost_poly (hm : Membership) :
    PBU (fun _ T _ => gmpFindStabCost hm T) :=
  ((PBU.W.addc 1).mul (gmpEqGroupCost_poly hm)).add (((PBU.W.addc 1).pow 8).smul (10 ^ 10))

theorem gmpStabReprCost_poly (hm : Membership) :
    PBU (fun _ T _ => gmpStabReprCost hm T) :=
  ((PBU.W.addc 1).mul (gmpFindStabCost_poly hm)).add (((PBU.W.addc 1).pow 8).smul (10 ^ 10))

theorem gmpStabOneCost_poly (hps : PointwiseStab) :
    PBU (fun _ T _ => gmpStabOneCost hps T) :=
  (gmpBoundSize_poly (pointwiseStabPrim hps) (PBU.W.addc 10)).add
    (((PBU.W.addc 3).pow 9).smul (10 ^ 16))

theorem gmpStabListCost_poly (hps : PointwiseStab) :
    PBU (fun _ T _ => gmpStabListCost hps T T) :=
  ((PBU.W.addc 1).mul (gmpStabOneCost_poly hps)).add
    ((PBU.W.add ((PBU.W.addc 1).pow 8)).smul (10 ^ 10))

theorem gmpStage1Cost_poly (hm : Membership) (hps : PointwiseStab) (hpre : Preimage) :
    PBU (fun _ T _ => gmpStage1Cost hm hps hpre T T) := by
  have hsl := gmpStabListCost_poly hps
  have hsr := gmpStabReprCost_poly hm
  have hpre_in : PBU (fun _ T _ => 10 * T + 50 * (T + 1) ^ 2) :=
    (PBU.W.smul 10).add (((PBU.W.addc 1).pow 2).smul 50)
  have hpre_bd := gmpBoundSize_poly (preimagePrim hpre) hpre_in
  have hrem : PBU (fun _ T _ => 10 ^ 20 * (T + T + 1) ^ 18) :=
    (((PBU.W.add PBU.W).addc 1).pow 18).smul (10 ^ 20)
  exact ((hsl.add hsr).add hpre_bd).add hrem

theorem gmpStage2StepCost_poly (hm : Membership) (hpre : Preimage) :
    PBU (fun _ T _ => gmpStage2StepCost hm hpre T T) := by
  have hW : PBU (fun _ T _ => 2 * T + 1300 * (T + 1) ^ 6) :=
    (PBU.W.smul 2).add (((PBU.W.addc 1).pow 6).smul 1300)
  have hfk := gmpPBU_comp (gmpFactorKernelCost_poly hm hpre) PBU.W hW (PBU.const 0)
  have hrem : PBU (fun _ T _ => 10 ^ 10 * (T + (T + 1) ^ 9)) :=
    (PBU.W.add ((PBU.W.addc 1).pow 9)).smul (10 ^ 10)
  exact hfk.add hrem

theorem gmpNormalCentralizerCost_poly (hm : Membership) (hps : PointwiseStab) (hpre : Preimage) :
    PBU (fun _ T _ => gmpNormalCentralizerCost hm hps hpre T) := by
  have hs1 := gmpStage1Cost_poly hm hps hpre
  have hs2 := (PBU.W.addc 1).mul (gmpStage2StepCost_poly hm hpre)
  have hps_bd := gmpBoundSize_poly (pointwiseStabPrim hps)
    ((((PBU.W.addc 1).pow 6).smul 320).addc 10)
  have hrem := ((PBU.W.addc 1).pow 18).smul (10 ^ 20)
  exact ((hs1.add hs2).add hps_bd).add hrem

/-- Standalone `Program` for `GMPNormalCentralizerTask`. -/
noncomputable def gmpNormalCentralizerProgram
    (hm : Membership) (hps : PointwiseStab) (hpre : Preimage) : Program :=
  ⟨gmpNormalCentralizerFuns 0 0 1 2,
    [membershipPrim hm, pointwiseStabPrim hps, preimagePrim hpre]⟩

theorem gmpNormalCentralizerProgram_hasAt
    (hm : Membership) (hps : PointwiseStab) (hpre : Preimage) :
    (gmpNormalCentralizerProgram hm hps hpre).HasAt 0 (gmpNormalCentralizerFuns 0 0 1 2) := by
  simpa [gmpNormalCentralizerProgram] using
    Program.hasAt_append [] (gmpNormalCentralizerFuns 0 0 1 2) []
      [membershipPrim hm, pointwiseStabPrim hps, preimagePrim hpre]

/-- **Normal-subgroup centralizer in polynomial time**, from membership, pointwise stabilizer,
and preimage. -/
theorem gmpNormalCentralizer_of
    (hm : Membership) (hps : PointwiseStab) (hpre : Preimage) : GMPNormalCentralizer := by
  obtain ⟨K, D, hK⟩ := nint_poly_bound (gmpNormalCentralizerCost_poly hm hps hpre)
  refine polyTimeAt_ofVal_of_lang_cells (gmpNormalCentralizerProgram hm hps hpre)
    0 K D 1 1 nint_inter_cells fun I => ?_
  have hH : GroupVal I.n (encGroup I.gs) (gens I.gs) := ⟨I.gs, rfl, rfl⟩
  have hN : GroupVal I.n (encGroup I.ns) (gens I.ns) := ⟨I.ns, rfl, rfl⟩
  have hHN : Normalizes (gens I.gs) (gens I.ns) := by
    have hnorm := nint_normalizer I.normalizes
    intro g hg x hx
    exact (Subgroup.mem_normalizer_iff.mp (hnorm hg) x).mp hx
  have hspec := gmpNormalCentralizer_spec hm hps hpre
    (gmpNormalCentralizerProgram_hasAt hm hps hpre) rfl rfl rfl hH hN hHN
  refine hspec.mono fun v c ⟨⟨C, hCg, hCm⟩, hc⟩ => ⟨?_, hc.trans (hK _)⟩
  have hC_eq : C = gmpNormalCentralizerSubgroup I := by
    ext y
    rw [hCm y]
    simp only [Subgroup.mem_bot]
    rfl
  rwa [← hC_eq]

end GI.Impl

namespace GI.Proved

/-- **Normal-subgroup centralizer in polynomial time** (Luks 1993, Proposition 7.3;
[LM, Theorem 3.1(viii)(a)]). -/
theorem gmpNormalCentralizer : GMPNormalCentralizer :=
  GI.Impl.gmpNormalCentralizer_of
    GI.Proved.membership GI.Proved.pointwiseStab GI.Proved.preimage

end GI.Proved
