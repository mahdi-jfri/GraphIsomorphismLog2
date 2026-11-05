module

public import Workspace.Impl.GMPListedKernel
public import Workspace.Proved.GMPListedKernel

@[expose] public section

/-!
# Computing the kernel of conjugation on a subgroup factor

Given group encodings `[hv, uv, vv]` of `H`, `U`, `V ≤ Sym(n)` where `H` normalizes `U` and `V`,
`gmpFactorKernelFuns` enumerates right coset representatives of `V` in `U` using `gmpRepsFuns`
and then takes the kernel of the conjugation action of `H` on those cosets using
`gmpListedKernelFuns`. The resulting generator list generates `{h ∈ H : ∀ u ∈ U, [h, u] ∈ V}`,
in time polynomial in the input weight and the index `[U : U ∩ V] = (V.subgroupOf U).index`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

theorem gmp_gens_cons_one {n : ℕ} (us : List (Perm (Fin n))) : gens (1 :: us) = gens us := by
  unfold gens
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure hx
  · exact Subgroup.closure_mono fun x hx => List.mem_cons_of_mem _ hx

/-- On `[hv, uv, vv]`, enumerate cosets of `V` in `U` and compute the kernel of `H` on them. -/
def gmpFactorKernelEntryF (reps lk : ℕ) : Expr :=
  .letE (.call reps (mk2 (arg 2) (.get (arg 1) (.nat 1))))
    (.call lk (mk4 (.get (arg 0) (.nat 0)) (arg 2) (.var 1) (.get (arg 0) (.nat 1))))

def gmpFactorKernelFuns (b jm jpre : ℕ) : List Expr :=
  [gmpFactorKernelEntryF (b + 1) (b + 28)] ++
    gmpRepsFuns (b + 1) jm ++ gmpListedKernelFuns (b + 28) jm jpre

structure GmpFactorKernelAt (P : Program) (hm : Membership) (hp : Preimage)
    (b jm jpre : ℕ) : Prop where
  entry : P.funs[b]? = some (gmpFactorKernelEntryF (b + 1) (b + 28))
  reps : GmpRepsAt P hm (b + 1) jm
  lk : GmpListedKernelAt P hm hp (b + 28) jm jpre

theorem gmpFactorKernelAt_of {P : Program} {hm : Membership} {hp : Preimage} {b jm jpre : ℕ}
    (h : P.HasAt b (gmpFactorKernelFuns b jm jpre))
    (hj : P.prims[jm]? = some (membershipPrim hm))
    (hpre : P.prims[jpre]? = some (preimagePrim hp)) :
    GmpFactorKernelAt P hm hp b jm jpre :=
  ⟨(h.block 0 (gs := [gmpFactorKernelEntryF (b + 1) (b + 28)]) rfl).single,
    gmpRepsAt_of (h.block 1 rfl) hj,
    gmpListedKernelAt_of (h.block 28 rfl) hj hpre⟩

theorem tmRpPredC_mono (hm : Membership) {Y₁ Y₂ : ℕ} (hY : Y₁ ≤ Y₂) :
    tmRpPredC hm Y₁ ≤ tmRpPredC hm Y₂ :=
  Nat.add_le_add (Nat.mul_le_mul_left _ hY)
    (tmPrimC_mono (membershipPrim hm) (Nat.mul_le_mul_left 20 hY))

theorem tmRpTestC_mono (hm : Membership) {Y₁ Y₂ L₁ L₂ : ℕ} (hY : Y₁ ≤ Y₂) (hL : L₁ ≤ L₂) :
    tmRpTestC hm Y₁ L₁ ≤ tmRpTestC hm Y₂ L₂ :=
  Nat.add_le_add (Nat.mul_le_mul hL (tmRpPredC_mono hm hY))
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul hL hL) hY))

theorem tmRpRoundC_mono (hm : Membership) {Y₁ Y₂ L₁ L₂ : ℕ} (hY : Y₁ ≤ Y₂) (hL : L₁ ≤ L₂) :
    tmRpRoundC hm Y₁ L₁ ≤ tmRpRoundC hm Y₂ L₂ :=
  Nat.add_le_add (Nat.mul_le_mul hY (tmRpTestC_mono hm hY hL))
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul hY (Nat.mul_le_mul hL hY)))

theorem gmpRepsWeight_mono {W₁ W₂ : ℕ} (hW : W₁ ≤ W₂) :
    gmpRepsWeight W₁ ≤ gmpRepsWeight W₂ :=
  Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (Nat.add_le_add_right hW 1) 4)

theorem gmpRepsCost_mono (hm : Membership) {W₁ W₂ q₁ q₂ : ℕ} (hW : W₁ ≤ W₂) (hq : q₁ ≤ q₂) :
    gmpRepsCost hm W₁ q₁ ≤ gmpRepsCost hm W₂ q₂ := by
  have hY := gmpRepsWeight_mono hW
  have hq2 : q₁ + 2 ≤ q₂ + 2 := Nat.add_le_add_right hq 2
  have hqY : (q₁ + 2) * gmpRepsWeight W₁ ≤ (q₂ + 2) * gmpRepsWeight W₂ :=
    Nat.mul_le_mul hq2 hY
  have hr := tmRpRoundC_mono hm hY hq2
  unfold gmpRepsCost
  refine Nat.add_le_add (Nat.mul_le_mul (Nat.add_le_add_right hq 1) (Nat.add_le_add hr ?_))
    (Nat.mul_le_mul_left 10000 hqY)
  exact Nat.mul_le_mul_left tmRpWK
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hY hq) (Nat.mul_le_mul_left 10 hqY)) 10)

theorem gmpIndexCost_mono (hm : Membership) {Y₁ Y₂ L₁ L₂ : ℕ} (hY : Y₁ ≤ Y₂) (hL : L₁ ≤ L₂) :
    gmpIndexCost hm Y₁ L₁ ≤ gmpIndexCost hm Y₂ L₂ :=
  Nat.add_le_add (Nat.mul_le_mul hL (tmRpPredC_mono hm hY))
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hL 1) 2))
      (Nat.add_le_add_right hY 1))

theorem gmpConjIndexCost_mono (hm : Membership) {Y₁ Y₂ L₁ L₂ : ℕ} (hY : Y₁ ≤ Y₂) (hL : L₁ ≤ L₂) :
    gmpConjIndexCost hm Y₁ L₁ ≤ gmpConjIndexCost hm Y₂ L₂ :=
  Nat.add_le_add (gmpIndexCost_mono hm hY hL) (Nat.mul_le_mul_left _ hY)

theorem gmpConjRowStepCost_mono (hm : Membership) {Y₁ Y₂ L₁ L₂ : ℕ} (hY : Y₁ ≤ Y₂) (hL : L₁ ≤ L₂) :
    gmpConjRowStepCost hm Y₁ L₁ ≤ gmpConjRowStepCost hm Y₂ L₂ :=
  Nat.add_le_add (gmpConjIndexCost_mono hm (Nat.mul_le_mul_left 100 hY) hL)
    (Nat.mul_le_mul_left _ hY)

theorem gmpConjRowCost_mono (hm : Membership) {Y₁ Y₂ L₁ L₂ : ℕ} (hY : Y₁ ≤ Y₂) (hL : L₁ ≤ L₂) :
    gmpConjRowCost hm Y₁ L₁ ≤ gmpConjRowCost hm Y₂ L₂ := by
  have hL1 : L₁ + 1 ≤ L₂ + 1 := Nat.add_le_add_right hL 1
  exact Nat.add_le_add (Nat.mul_le_mul hL (gmpConjRowStepCost_mono hm hY hL))
    (Nat.mul_le_mul (Nat.mul_le_mul_left mapK hL1)
      (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 10 hY)
        (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left hL1 2))) 10))

theorem gmpConjTableStepCost_mono (hm : Membership) {Y₁ Y₂ L₁ L₂ : ℕ} (hY : Y₁ ≤ Y₂) (hL : L₁ ≤ L₂) :
    gmpConjTableStepCost hm Y₁ L₁ ≤ gmpConjTableStepCost hm Y₂ L₂ :=
  Nat.add_le_add (gmpConjRowCost_mono hm (Nat.mul_le_mul_left 100 hY) hL)
    (Nat.mul_le_mul_left _ (Nat.add_le_add hY (Nat.pow_le_pow_left (Nat.add_le_add_right hL 1) 2)))

theorem gmpGraphRowCost_mono (hm : Membership) {Y₁ Y₂ L₁ L₂ : ℕ} (hY : Y₁ ≤ Y₂) (hL : L₁ ≤ L₂) :
    gmpGraphRowCost hm Y₁ L₁ ≤ gmpGraphRowCost hm Y₂ L₂ :=
  Nat.add_le_add (gmpConjTableStepCost_mono hm hY hL)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add hY hL) 1) 3))

theorem gmpGraphRowsCost_mono (hm : Membership) {Y₁ Y₂ L₁ L₂ S₁ S₂ : ℕ}
    (hY : Y₁ ≤ Y₂) (hL : L₁ ≤ L₂) (hS : S₁ ≤ S₂) :
    gmpGraphRowsCost hm Y₁ L₁ S₁ ≤ gmpGraphRowsCost hm Y₂ L₂ S₂ := by
  have hS1 : S₁ + 1 ≤ S₂ + 1 := Nat.add_le_add_right hS 1
  have hYL : Y₁ + L₁ + 1 ≤ Y₂ + L₂ + 1 := Nat.add_le_add_right (Nat.add_le_add hY hL) 1
  exact Nat.add_le_add
    (Nat.mul_le_mul hS (gmpGraphRowCost_mono hm (Nat.mul_le_mul_left 100 hY) hL))
    (Nat.mul_le_mul (Nat.mul_le_mul_left mapK hS1)
      (Nat.add_le_add_right (Nat.add_le_add hY
        (Nat.mul_le_mul_left 20 (Nat.mul_le_mul hS1 (Nat.pow_le_pow_left hYL 2)))) 10))

theorem gmpListedKernelCost_mono (hm : Membership) (hp : Preimage) {Y₁ Y₂ L₁ L₂ S₁ S₂ : ℕ}
    (hY : Y₁ ≤ Y₂) (hL : L₁ ≤ L₂) (hS : S₁ ≤ S₂) :
    gmpListedKernelCost hm hp Y₁ L₁ S₁ ≤ gmpListedKernelCost hm hp Y₂ L₂ S₂ := by
  have hT : (S₁ + 2) * (Y₁ + L₁ + 1) ≤ (S₂ + 2) * (Y₂ + L₂ + 1) :=
    Nat.mul_le_mul (Nat.add_le_add_right hS 2) (Nat.add_le_add_right (Nat.add_le_add hY hL) 1)
  have hg := gmpGraphRowsCost_mono hm (Nat.mul_le_mul_left 100 hY) hL hS
  have hm1 := Nat.mul_le_mul_left mkGroupK (Nat.pow_le_pow_left hT 3)
  have hm2 := Nat.mul_le_mul_left mkGroupK
    (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hL 1)) 3)
  have hpr := tmPrimC_mono (preimagePrim hp)
    (Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left hT 2))
  have ht6 := Nat.mul_le_mul_left (10 ^ 9) (Nat.pow_le_pow_left hT 6)
  unfold gmpListedKernelCost
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hg hm1) hm2) hpr) ht6

noncomputable def gmpFactorKernelCost (hm : Membership) (hp : Preimage) (W q : ℕ) : ℕ :=
  let Y := 100 * ((q + 2) * gmpRepsWeight (5 * W + 5))
  gmpRepsCost hm (5 * W + 5) q + gmpListedKernelCost hm hp Y q W + 1000 * Y + 50 * (W + 1) ^ 6

theorem gmpFactorKernelCost_mono (hm : Membership) (hp : Preimage) {W₁ W₂ q₁ q₂ : ℕ}
    (hW : W₁ ≤ W₂) (hq : q₁ ≤ q₂) :
    gmpFactorKernelCost hm hp W₁ q₁ ≤ gmpFactorKernelCost hm hp W₂ q₂ := by
  have hW5 : 5 * W₁ + 5 ≤ 5 * W₂ + 5 := by omega
  have hY : 100 * ((q₁ + 2) * gmpRepsWeight (5 * W₁ + 5)) ≤
      100 * ((q₂ + 2) * gmpRepsWeight (5 * W₂ + 5)) :=
    Nat.mul_le_mul_left 100 (Nat.mul_le_mul (Nat.add_le_add_right hq 2) (gmpRepsWeight_mono hW5))
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (gmpRepsCost_mono hm hW5 hq) (gmpListedKernelCost_mono hm hp hY hq hW))
      (Nat.mul_le_mul_left 1000 hY))
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hW 1) 6))

/-- Given group encodings of `H`, `U`, `V` with `U` and `V` normalized by `H`,
`gmpFactorKernelFuns` computes generators of `{h ∈ H : ∀ u ∈ U, [h, u] ∈ V}`. -/
theorem gmpFactorKernel_spec {P : Program} {hm : Membership} {hp : Preimage} {b jm jpre n : ℕ}
    (ha : GmpFactorKernelAt P hm hp b jm jpre)
    {H U V : Subgroup (Perm (Fin n))} {hv uv vv : Val}
    (hH : GroupVal n hv H) (hU : GroupVal n uv U) (hV : GroupVal n vv V)
    (hnU : GI.Multicoset.Normalizes H U) (hnV : GI.Multicoset.Normalizes H V)
    {W : ℕ} (hW : (Val.list [hv, uv, vv]).wt ≤ W) :
    FunAll P b (.list [hv, uv, vv]) (fun w c =>
      (∃ C : Subgroup (Perm (Fin n)), GensVal n w C ∧
        ∀ h, h ∈ C ↔ h ∈ H ∧ ∀ u ∈ U, h * u * h⁻¹ * u⁻¹ ∈ V) ∧
      c ≤ gmpFactorKernelCost hm hp W ((V.subgroupOf U).index)) := by
  obtain ⟨hs, rfl, rfl⟩ := hH
  obtain ⟨us, rfl, rfl⟩ := hU
  obtain ⟨vs, rfl, rfl⟩ := hV
  have hhv : (encGroup hs).wt < (Val.list [encGroup hs, encGroup us, encGroup vs]).wt :=
    wt_le_wt_list (by simp)
  have huv : (encGroup us).wt < (Val.list [encGroup hs, encGroup us, encGroup vs]).wt :=
    wt_le_wt_list (by simp)
  have hvv : (encGroup vs).wt < (Val.list [encGroup hs, encGroup us, encGroup vs]).wt :=
    wt_le_wt_list (by simp)
  have hnW : n + 1 ≤ W := by
    have hsize := S_le_wt_encGroup hs
    have hbase : n + 1 ≤ (hs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hus1 : (Val.list ((1 :: us).map encPerm)).wt < (encGroup us).wt :=
    wt_le_wt_list (by simp)
  have hhs1 : (Val.list ((1 :: hs).map encPerm)).wt < (encGroup hs).wt :=
    wt_le_wt_list (by simp)
  have hnw : (Val.nat n).wt < (encGroup hs).wt :=
    wt_le_wt_list (by simp)
  have hshs : (1 :: hs).length ≤ W := by
    have hl := length_lt_wt_list ((1 :: hs).map encPerm)
    simp only [List.length_map] at hl
    omega
  have hrep_in : (Val.list [encGroup vs, .list ((1 :: us).map encPerm)]).wt ≤ 5 * W + 5 := by
    have hw2 := wt_list2_le (encGroup vs) (.list ((1 :: us).map encPerm))
    omega
  have hWY : (5 * W + 5) + 1 ≤ gmpRepsWeight (5 * W + 5) := by
    have hp := Nat.le_self_pow (by decide : 4 ≠ 0) ((5 * W + 5) + 1)
    dsimp [gmpRepsWeight]
    omega
  have hnY0 : (n + 1) ^ 4 ≤ gmpRepsWeight (5 * W + 5) := by
    have hp := Nat.pow_le_pow_left (show n + 1 ≤ (5 * W + 5) + 1 by omega) 4
    dsimp [gmpRepsWeight]
    omega
  have hY0q : gmpRepsWeight (5 * W + 5) ≤
      (((gens vs).subgroupOf (gens us)).index + 2) * gmpRepsWeight (5 * W + 5) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hnY : (n + 1) ^ 4 ≤
      100 * ((((gens vs).subgroupOf (gens us)).index + 2) * gmpRepsWeight (5 * W + 5)) :=
    hnY0.trans (hY0q.trans (Nat.le_mul_of_pos_left _ (by decide)))
  have darg0 (rest : List Val) := Det.arg' (P := P)
    (vs := [encGroup hs, encGroup us, encGroup vs]) (rest := rest) (j := 0) rfl
  have darg1 (rest : List Val) := Det.arg' (P := P)
    (vs := [encGroup hs, encGroup us, encGroup vs]) (rest := rest) (j := 1) rfl
  have darg2 (rest : List Val) := Det.arg' (P := P)
    (vs := [encGroup hs, encGroup us, encGroup vs]) (rest := rest) (j := 2) rfl
  have dus1 := Det.get' (darg1 []) (Det.nat 1)
    (show [Val.nat n, Val.list ((1 :: us).map encPerm)][1]? =
      some (.list ((1 :: us).map encPerm)) from rfl)
  have dreps_arg := Det.mk2 (darg2 []) dus1
  have hreps := gmpReps_spec ha.reps vs (1 :: us)
  rw [gmp_gens_cons_one us] at hreps
  refine FunAll.intro ha.entry
    (EvalAll.letE (Ra := fun w c => (∃ rs : List (Perm (Fin n)), w = .list (rs.map encPerm) ∧
      GmpCosetReps (gens us) (gens vs) rs) ∧
      c ≤ gmpRepsCost hm (5 * W + 5) (((gens vs).subgroupOf (gens us)).index) +
        100 * ((((gens vs).subgroupOf (gens us)).index + 2) * gmpRepsWeight (5 * W + 5)))
      (EvalAll.call_funAll dreps_arg fun v ca hv => ?_) fun v1 c1 h1 => ?_)
  · obtain ⟨rfl, hca⟩ := hv
    refine hreps.mono fun w cb ⟨rs, hw, hrs, hcb⟩ => ⟨⟨rs, hw, hrs⟩, ?_⟩
    subst w
    have hcb' := hcb.trans (gmpRepsCost_mono hm hrep_in le_rfl)
    have hwr := tmRp_wt_reps (L := ((gens vs).subgroupOf (gens us)).index + 2) hnY0 rs
      (by have := hrs.length; omega)
    have hn1 := wt_nat_le 1
    omega
  obtain ⟨⟨rs, rfl, hrs⟩, hc1⟩ := h1
  have hwr := tmRp_wt_reps (L := ((gens vs).subgroupOf (gens us)).index + 2) hnY0 rs (by
    have hlen := hrs.length
    omega)
  have dn := Det.get' (darg0 [.list (rs.map encPerm)]) (Det.nat 0)
    (show [Val.nat n, Val.list ((1 :: hs).map encPerm)][0]? = some (.nat n) from rfl)
  have dhs1 := Det.get' (darg0 [.list (rs.map encPerm)]) (Det.nat 1)
    (show [Val.nat n, Val.list ((1 :: hs).map encPerm)][1]? =
      some (.list ((1 :: hs).map encPerm)) from rfl)
  have drs := Det.var' (P := P)
    (env := [.list [encGroup hs, encGroup us, encGroup vs], .list (rs.map encPerm)]) (i := 1) rfl
  have dlk_arg := Det.mk4 dn (darg2 [.list (rs.map encPerm)]) drs dhs1
  have hlk_in : (Val.list [.nat n, encGroup vs, .list (rs.map encPerm),
      .list ((1 :: hs).map encPerm)]).wt ≤
      100 * ((((gens vs).subgroupOf (gens us)).index + 2) * gmpRepsWeight (5 * W + 5)) := by
    have hw4 := wt_list4_le (.nat n) (encGroup vs) (.list (rs.map encPerm))
      (.list ((1 :: hs).map encPerm))
    omega
  have hhs_mem : ∀ h ∈ (1 :: hs), h ∈ gens hs := by
    intro h hh
    rw [← gmp_gens_cons_one hs]
    exact Subgroup.subset_closure hh
  have hlk := gmpListedKernel_spec ha.lk ⟨vs, rfl, rfl⟩ hrs hnU hnV (1 :: hs) hhs_mem hnY hlk_in
  refine EvalAll.call_funAll dlk_arg fun v ca2 hv => ?_
  obtain ⟨rfl, hca2⟩ := hv
  refine hlk.mono fun w cb2 ⟨hw, hcb2⟩ => ⟨⟨_, hw, fun g => ?_⟩, ?_⟩
  · refine (gmpGraphKernelInst_mem (gens hs) (gmpConjLabelAction hrs hnU hnV) (1 :: hs) hhs_mem g).trans ?_
    constructor
    · rintro ⟨hg, hk⟩
      have hg' : g ∈ gens hs := by rwa [gmp_gens_cons_one hs] at hg
      exact ⟨hg', (gmpConjLabelAction_mem_ker hrs hnU hnV ⟨g, hg'⟩).mp hk⟩
    · rintro ⟨hg, hcomm⟩
      have hg' : g ∈ gens (1 :: hs) := by rwa [gmp_gens_cons_one hs]
      exact ⟨hg', (gmpConjLabelAction_mem_ker hrs hnU hnV ⟨g, hg⟩).mpr hcomm⟩
  · have hww : w.wt ≤ 13 * (W + 1) ^ 6 :=
      (GensVal.wt_le hw).trans (Nat.mul_le_mul_left 13 (Nat.pow_le_pow_left (by omega) 6))
    have hcb2' : gmpListedKernelCost hm hp
        (100 * ((((gens vs).subgroupOf (gens us)).index + 2) * gmpRepsWeight (5 * W + 5)))
        rs.length (1 :: hs).length ≤
        gmpListedKernelCost hm hp
          (100 * ((((gens vs).subgroupOf (gens us)).index + 2) * gmpRepsWeight (5 * W + 5)))
          (((gens vs).subgroupOf (gens us)).index) W := by
      rw [hrs.length]
      exact gmpListedKernelCost_mono hm hp le_rfl le_rfl hshs
    have hn0 := wt_nat_le 0
    have hn1 := wt_nat_le 1
    unfold gmpFactorKernelCost
    dsimp only
    omega

theorem gmpFactorKernelCost_poly (hm : Membership) (hp : Preimage) :
    PBU (fun q W _ => gmpFactorKernelCost hm hp W q) := by
  have hW5 : PBU (fun _ W _ => 5 * W + 5) := (PBU.W.smul 5).addc 5
  have hY0 : PBU (fun _ W _ => gmpRepsWeight (5 * W + 5)) :=
    ((hW5.addc 1).pow 4).smul 100
  have hY : PBU (fun q W _ => 100 * ((q + 2) * gmpRepsWeight (5 * W + 5))) :=
    ((PBU.k.addc 2).mul hY0).smul 100
  have hreps := gmpPBU_comp (gmpRepsCost_poly hm) PBU.k hW5 (PBU.const 0)
  have hlk := gmpPBU_comp (gmpListedKernelCost_poly hm hp) PBU.k hY PBU.W
  exact ((hreps.add hlk).add (hY.smul 1000)).add (((PBU.W.addc 1).pow 6).smul 50)

theorem gmpFactorKernelCost_le (hm : Membership) (hp : Preimage) :
    ∃ C D : ℕ, ∀ W q : ℕ, gmpFactorKernelCost hm hp W q ≤ C * (W + q + 2) ^ D := by
  obtain ⟨C, D, h⟩ := gmpFactorKernelCost_poly hm hp
  exact ⟨C, D, fun W q => by simpa only [PB, Nat.add_zero] using h q W 0⟩

/-- A synthetic `Prim` whose `boundSize` bounds `gmpFactorKernelCost hm hp W q` at `W + q`. -/
noncomputable def gmpFactorKernelPrim (hm : Membership) (hp : Preimage) : Prim where
  Pre := fun _ => False
  Post := fun _ _ => True
  c := (gmpFactorKernelCost_le hm hp).choose
  k := (gmpFactorKernelCost_le hm hp).choose_spec.choose
  prog := (membershipPrim hm).prog
  spec := fun x => x.2.elim

theorem gmpFactorKernelCost_le_boundSize (hm : Membership) (hp : Preimage) (W q : ℕ) :
    gmpFactorKernelCost hm hp W q ≤ (gmpFactorKernelPrim hm hp).boundSize (W + q) :=
  (gmpFactorKernelCost_le hm hp).choose_spec.choose_spec W q

end GI.Impl
