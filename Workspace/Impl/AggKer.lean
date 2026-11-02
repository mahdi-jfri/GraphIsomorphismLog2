import Workspace.Impl.AggTupProg

/-!
# The pointwise stabilizer of any points of a graph group, and the kernel `ker(φ_T|_A)`

`graphStabP_spec`: the stabilizer module of `AggStab.lean` (`graphStabFuns`) on any list of
points of `Fin (k + q)`, not only points of the first part. On the label points `k + c` of a
test set `T` it gives the graph form of the kernel `ker(φ_T|_A)` (`pairGens_kernelIn`): the
elements of `A` whose label permutation fixes `T` pointwise. This is the paper's "Compute
`ker π` using the simultaneous action on `Ω ⊔ Γ` and a pointwise stabilizer" (proof of
Proposition A.1), for the action on `T`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens sumToFin pointwiseStab PointwiseStab)

variable {k q : ℕ}

/-- The pairs whose encoding fixes every point of `X`. -/
def fixPts (k q : ℕ) (X : List (Fin (k + q))) : Subgroup (Perm (Fin k) × Perm (Fin q)) where
  carrier := {p | ∀ i ∈ X, encPair p i = i}
  one_mem' := fun i _ => by simp [encPair]
  mul_mem' := fun {a b} ha hb i hi => by
    show encPairHom k q (a * b) i = i
    rw [map_mul, Perm.mul_apply]
    exact (congrArg _ (hb i hi)).trans (ha i hi)
  inv_mem' := fun {a} ha i hi => by
    show encPairHom k q a⁻¹ i = i
    rw [map_inv, Perm.inv_eq_iff_eq]
    exact (ha i hi).symm

/-- The size parameter of a stabilizer call. -/
def stabPM (k q : ℕ) (ps : List (Perm (Fin k) × Perm (Fin q))) (X : List (Fin (k + q))) : ℕ :=
  k + q + ps.length + X.length + 2

/-- **The pointwise stabilizer of any points, on a list of pairs.** -/
theorem graphStabP_spec (h : PointwiseStab) {P : Program} {b jp : ℕ}
    (hb : P.HasAt b (graphStabFuns b jp)) (hj : P.prims[jp]? = some (pointwiseStabPrim h))
    (ps : List (Perm (Fin k) × Perm (Fin q))) (X : List (Fin (k + q))) :
    FunAll P b (.list [.list [.nat k, .nat q], .list (ps.map pairV), encPts X])
      (fun w c => ∃ qs : List (Perm (Fin k) × Perm (Fin q)), w = .list (qs.map pairV) ∧
        qs.length ≤ (k + q) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓ fixPts k q X ∧
        c ≤ (pointwiseStabPrim h).bound (.list [encGroup (ps.map encPair), encPts X]) +
          graphStabK * stabPM k q ps X ^ 8) := by
  have hentry : P.funs[b]? = some (graphStabEntry b jp) := by
    simpa using (hb.block 0 (gs := [graphStabEntry b jp]) (by rfl)).single
  have hen : P.HasAt (b + 1) (pEncMapFuns (b + 1)) := hb.block 1 (by rfl)
  have hmk : P.HasAt (b + 14) (mkGroupFuns (b + 14)) := hb.block 14 (by rfl)
  have hrg : P.HasAt (b + 15) (rangeFuns (b + 15)) := hmk.block 1 (by rfl)
  have hsp : P.HasAt (b + 21) (pSplitMapFuns (b + 21)) := hb.block 21 (by rfl)
  set A : Val := .list [.list [.nat k, .nat q], .list (ps.map pairV), encPts X] with hA
  set E : Val := .list (ps.map fun p => encPerm (encPair p)) with hE
  set GD : Val := encGroup (ps.map encPair) with hGD
  have gk : ∀ rest : List Val, Det P (A :: rest) (.get (arg 0) (.nat 0)) (.nat k) _ :=
    fun rest => Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
      encPts X]) (rest := rest) (j := 0) rfl) (Det.nat 0) (v := .nat k) rfl
  have gq : ∀ rest : List Val, Det P (A :: rest) (.get (arg 0) (.nat 1)) (.nat q) _ :=
    fun rest => Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
      encPts X]) (rest := rest) (j := 0) rfl) (Det.nat 1) (v := .nat q) rfl
  have d1 := Det.call (Det.mk2 (gk []) (Det.arg' (P := P) (vs := [.list [.nat k, .nat q],
    .list (ps.map pairV), encPts X]) (rest := []) (j := 1) rfl)) (pEncMap_spec hen ps)
  have hG2 := mkGroup_spec hmk (ps.map encPair)
  have eE : Val.list ((ps.map encPair).map encPerm) = E := by simp [hE]
  rw [eE] at hG2
  have d2 := Det.call (Det.mk2 (Det.arith' (op := .add) (gk [E]) (gq [E]) (z := k + q) rfl)
    (Det.var' (P := P) (env := [A, E]) (i := 1) rfl)) hG2
  have dI := Det.mk2 (Det.var' (P := P) (env := [A, E, GD]) (i := 2) rfl)
    (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV), encPts X])
      (rest := [E, GD]) (j := 2) rfl)
  have hGv : GroupVal (k + q) GD (gens (ps.map encPair)) := ⟨ps.map encPair, rfl, rfl⟩
  have hspec := pointwiseStabPrim_spec h hGv X
  have hP := EvalAll.prim_spec_le hj dI hspec
    fun w hw => GensVal.wt_le hw
  refine FunAll.intro hentry (EvalAll.letE d1 fun _ _ h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.letE d2 fun _ _ h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  refine EvalAll.letE hP fun w3 c3 h3 => ?_
  obtain ⟨⟨hs, rfl, hl, hgen⟩, hc3⟩ := h3
  have hsub : pointwiseStab (gens (ps.map encPair)) X =
      (Subgroup.closure {p | p ∈ ps} ⊓ fixPts k q X).map (encPairHom k q) := by
    ext x
    show (x ∈ gens (ps.map encPair) ∧ ∀ i ∈ X, x i = i) ↔ _
    rw [mem_gens_encPair]
    simp only [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hX⟩
      exact ⟨p, ⟨hp, hX⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hX⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, hX⟩
  obtain ⟨qs, rfl, hqs⟩ := exists_pairs_of_gens (hgen.trans hsub)
  set H : Val := .list ((qs.map encPair).map encPerm) with hH
  have hsplit := pSplitMap_spec hsp qs
  have eH : Val.list (qs.map fun p => encPerm (encPair p)) = H := by simp [hH]
  rw [eH] at hsplit
  have dr1 := Det.call (gk [E, GD, H]) (range_det hrg k)
  have dr2 := Det.call (gq [E, GD, H]) (range_det hrg q)
  have dctx := Det.mk2 (gk [E, GD, H]) (Det.mk2 dr1 dr2)
  have ectx : Val.list [.nat k, .list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))]] =
      pSplitCtx k q := rfl
  rw [ectx] at dctx
  have d4 := Det.call (Det.mk2 dctx (Det.var' (P := P) (env := [A, E, GD, H]) (i := 3) rfl))
    hsplit
  have hlq : qs.length ≤ (k + q) ^ 2 := by
    have e : (qs.map (encPair (k := k) (q := q))).length = qs.length := List.length_map _
    have hl' : (qs.map (encPair (k := k) (q := q))).length ≤ (k + q) ^ 2 := hl
    omega
  refine d4.post fun c hc => ⟨qs, rfl, hlq, hqs, ?_⟩
  -- the cost
  set M := stabPM k q ps X with hM
  have hMd : k + q + ps.length + X.length + 2 = M := rfl
  have m2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have m3 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have m4 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have m6 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have m8 : M ^ 6 ≤ M ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have sq : ∀ x, x ≤ M → x ^ 2 ≤ M ^ 2 := fun x hx => Nat.pow_le_pow_left hx 2
  have pw : ∀ x n, x ≤ M → x ^ n ≤ M ^ n := fun x n hx => Nat.pow_le_pow_left hx n
  have bps : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := by
    have := wt_pairList_le ps
    have h3 := pw (pM k q ps) 3 (by unfold pM; omega)
    omega
  have bX : (encPts X).wt ≤ 3 * M ^ 2 + 4 := by
    have h1 := wt_list_map_le X (fun i : Fin (k + q) => Val.nat i.val) (W := k + q + 2)
      fun i _ => by
      show (Val.nat (i : ℕ)).wt ≤ k + q + 2; have := wt_nat_le (i : ℕ); have := i.isLt; omega
    have h2 : X.length * (2 * (k + q + 2) + 1) ≤ M * (3 * M) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : M * (3 * M) = 3 * M ^ 2 := by ring
    rw [encPts_eq]
    omega
  have bkq := wt_list2_le (.nat k) (.nat q)
  have wk := wt_nat_le k
  have wq := wt_nat_le q
  have wkq := wt_nat_le (k + q)
  have bA := wt_list3_le (.list [.nat k, .nat q]) (.list (ps.map pairV)) (encPts X)
  have bA1 := wt_list2_le (.nat k) (.list (ps.map pairV))
  have bE : E.wt ≤ 9 * M ^ 3 + 4 := by
    have h1 := wt_list_map_le ps (fun p => encPerm (encPair p))
      (W := 4 * (k + q + 1) ^ 2) fun p _ => wt_encPerm_le _
    have h2 : ps.length * (2 * (4 * (k + q + 1) ^ 2) + 1) ≤ M * (9 * M ^ 2) :=
      Nat.mul_le_mul (by omega) (by have := sq (k + q + 1) (by omega); omega)
    have h3 : M * (9 * M ^ 2) = 9 * M ^ 3 := by ring
    rw [hE]; omega
  have bE1 := wt_list2_le (.nat (k + q)) E
  have cE : ps.length * pEncCost k q ≤ natStepK * M ^ 4 := by
    have h2 : ps.length * pEncCost k q ≤ M * (natStepK * M ^ 3) :=
      Nat.mul_le_mul (by omega) (by
        show natStepK * (k + q + 1) ^ 3 ≤ _; exact Nat.mul_le_mul_left _ (pw _ 3 (by omega)))
    have e2 : M * (natStepK * M ^ 3) = natStepK * M ^ 4 := by ring
    omega
  have cE2 : mapK * (ps.length + 1) * ((Val.list [.nat k, .list (ps.map pairV)]).wt + E.wt + 1)
      ≤ mapK * M * (1000 * M ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have sGD2 : ((ps.map encPair).length + 2) * (k + q + 1) ≤ M ^ 2 := by
    have := Nat.mul_le_mul (show (ps.map encPair).length + 2 ≤ M by simp; omega)
      (show k + q + 1 ≤ M by omega)
    have e : M * M = M ^ 2 := by ring
    omega
  have bGD : GD.wt ≤ 40 * M ^ 4 := by
    have h1 := wt_encGroup_le (ps.map encPair)
    have h2 := Nat.pow_le_pow_left sGD2 2
    have e : (M ^ 2) ^ 2 = M ^ 4 := by ring
    rw [hGD]; omega
  have cGD : mkGroupK * (((ps.map encPair).length + 2) * (k + q + 1)) ^ 3 ≤ mkGroupK * M ^ 6 := by
    have h2 := Nat.pow_le_pow_left sGD2 3
    have e : (M ^ 2) ^ 3 = M ^ 6 := by ring
    exact Nat.mul_le_mul_left _ (e ▸ h2)
  have bI := wt_list2_le GD (encPts X)
  have bIn : 13 * (k + q + 1) ^ 6 ≤ 13 * M ^ 6 := Nat.mul_le_mul_left _ (pw _ 6 (by omega))
  have hq2 : qs.length ≤ M ^ 2 := le_trans hlq (sq _ (by omega))
  have bH : H.wt ≤ 9 * M ^ 4 + 4 := by
    have h1 := wt_list_map_le (qs.map encPair) encPerm (W := 4 * (k + q + 1) ^ 2)
      fun p _ => wt_encPerm_le p
    have h2 : (qs.map encPair).length * (2 * (4 * (k + q + 1) ^ 2) + 1) ≤ M ^ 2 * (9 * M ^ 2) :=
      Nat.mul_le_mul (by simp; omega) (by have := sq (k + q + 1) (by omega); omega)
    have h3 : M ^ 2 * (9 * M ^ 2) = 9 * M ^ 4 := by ring
    rw [hH]; omega
  have bQ : (Val.list (qs.map pairV)).wt ≤ 400 * M ^ 6 := by
    have h1 := wt_pairList_le qs
    have h2 : pM k q qs ≤ 2 * M ^ 2 := by unfold pM; omega
    have h3 := Nat.pow_le_pow_left h2 3
    have e : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
    omega
  have b1k := wt_encPerm_le (1 : Perm (Fin k))
  have b1q := wt_encPerm_le (1 : Perm (Fin q))
  have b11 := wt_list2_le (encPerm (1 : Perm (Fin k))) (encPerm (1 : Perm (Fin q)))
  have bC := wt_list2_le (.nat k) (.list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))])
  have eC : (pSplitCtx k q).wt =
      (Val.list [.nat k, .list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))]]).wt := rfl
  have bCH := wt_list2_le (pSplitCtx k q) H
  have sk := sq (k + 1) (by omega)
  have sq' := sq (q + 1) (by omega)
  have ck : 8000 * (k + 1) ^ 3 ≤ 8000 * M ^ 3 := Nat.mul_le_mul_left _ (pw _ 3 (by omega))
  have cq : 8000 * (q + 1) ^ 3 ≤ 8000 * M ^ 3 := Nat.mul_le_mul_left _ (pw _ 3 (by omega))
  have cS : qs.length * pSplitCost k q ≤ 10 ^ 11 * M ^ 8 := by
    have h1 : pSplitCost k q ≤ 10 ^ 11 * M ^ 6 :=
      Nat.mul_le_mul_left _ (pw _ 6 (by omega))
    have h2 := Nat.mul_le_mul hq2 h1
    have e : M ^ 2 * (10 ^ 11 * M ^ 6) = 10 ^ 11 * M ^ 8 := by ring
    omega
  have cS2 : mapK * (qs.length + 1) * ((Val.list [pSplitCtx k q, H]).wt +
      (Val.list (qs.map pairV)).wt + 1) ≤ mapK * (2 * M ^ 2) * (1000 * M ^ 6) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e1 : mapK * M * (1000 * M ^ 3) = 10 ^ 6 * M ^ 4 := by simp only [mapK]; ring
  have e2 : mapK * (2 * M ^ 2) * (1000 * M ^ 6) = 2 * 10 ^ 6 * M ^ 8 := by simp only [mapK]; ring
  rw [← hE] at hc1
  rw [← hGD] at hc2
  simp only [graphStabK, natStepK, mkGroupK] at *
  omega


/-! ### The kernel `ker(φ_T|_A)` in graph form -/

section Kernel

open GI.LocalGroups GI.Endpoint

variable {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

theorem mem_fixPts_labPts {p : Perm (Fin k) × Perm (Fin q)} {t : List (Fin q)} :
    p ∈ fixPts k q (labPts k t) ↔ ∀ c ∈ t, p.2 c = c := by
  show (∀ i ∈ labPts k t, encPair p i = i) ↔ _
  simp only [labPts, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    encPair_natAdd]
  exact forall₂_congr fun c _ => ⟨fun h => Fin.ext (by simpa using congrArg Fin.val h),
    fun h => by rw [h]⟩

variable (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- **The graph of the lift of the kernel**: the pairs of the graph of the lift of `A` whose
label part fixes `T` pointwise. -/
theorem graphOf_lift_kernelIn (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
    {T : Finset (Fin L.q)} {A : Subgroup (Perm S.dom)} (hA : A ≤ Pgrp S.domGroup πd T) :
    graphOf e L (S.liftGroup (kernelIn (phiT S.domGroup πd T) A)) =
      graphOf e L (S.liftGroup A) ⊓ fixPts k L.q (labPts k (tlist T)) := by
  ext p
  rw [Subgroup.mem_inf, mem_graphOf, mem_graphOf, mem_fixPts_labPts]
  have key : ∀ g (hg : g ∈ S.G), S.domHom ⟨g, hg⟩ ∈ A →
      ((S.domHom ⟨g, hg⟩ ∈ kernelIn (phiT S.domGroup πd T) A) ↔
        ∀ c ∈ T, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) c = c) := by
    intro g hg ha
    have hP := hA ha
    rw [mem_kernelIn]
    have hdom : S.domHom ⟨g, hg⟩ ∈ S.domGroup := ⟨⟨g, hg⟩, rfl⟩
    constructor
    · rintro ⟨-, h, h1⟩ c hc
      have := congrArg (fun ρ : alternatingGroup T => ((ρ : Perm T) ⟨c, hc⟩ : Fin L.q)) h1
      simp only [phiT_apply, OneMemClass.coe_one, Perm.one_apply] at this
      rwa [lab_of_mem hdom, hπ ⟨g, hg⟩] at this
    · intro h
      refine ⟨ha, hP, Subtype.ext (Equiv.ext fun ⟨c, hc⟩ => Subtype.ext ?_)⟩
      rw [phiT_apply, lab_of_mem hdom, hπ ⟨g, hg⟩]
      exact h c hc
  constructor
  · rintro ⟨g, hg, hN, h1, h2⟩
    obtain ⟨hg', hN'⟩ := State.mem_liftGroup.1 hN
    have hA' : S.domHom ⟨g, hg⟩ ∈ A := (mem_kernelIn _).1 hN' |>.1
    refine ⟨⟨g, hg, State.mem_liftGroup.2 ⟨hg, hA'⟩, h1, h2⟩, fun c hc => ?_⟩
    rw [← h2]
    exact (key g hg hA').1 hN' c (mem_tlist.1 hc)
  · rintro ⟨⟨g, hg, hA', h1, h2⟩, hfix⟩
    obtain ⟨hg', hA''⟩ := State.mem_liftGroup.1 hA'
    refine ⟨g, hg, State.mem_liftGroup.2 ⟨hg, (key g hg hA'').2 fun c hc => ?_⟩, h1, h2⟩
    rw [h2]
    exact hfix c (mem_tlist.2 hc)

/-- **The stabilizer of the label points of `T` gives the kernel in graph form.** -/
theorem pairGens_kernelIn (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
    {T : Finset (Fin L.q)} {A : Subgroup (Perm S.dom)} (hA : A ≤ Pgrp S.domGroup πd T)
    {ps qs : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L (S.liftGroup A) ps)
    (h : Subgroup.closure {p | p ∈ qs} =
      Subgroup.closure {p | p ∈ ps} ⊓ fixPts k L.q (labPts k (tlist T))) :
    PairGens e L (S.liftGroup (kernelIn (phiT S.domGroup πd T) A)) qs := by
  unfold PairGens at *
  rw [h, hps, graphOf_lift_kernelIn πd hπ hA]

end Kernel

end GI.Impl
