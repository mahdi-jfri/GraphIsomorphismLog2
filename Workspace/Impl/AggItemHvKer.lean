import Workspace.Impl.AggItemHvLift
import Workspace.Impl.AggKer
import Workspace.Impl.AggInc

/-!
# Case 2a: the group value of the kernel `K`

The three calls of the halving item run under `K = π⁻¹(1_Φ × Alt(C))` (`itHvKer`, the group of
`Halving.kerState`). A canonical value of such a call needs a group value of `K` with at most `k²`
generators. The program gets it in three steps (Lemma A.11; the proof of Proposition A.1:
"Compute `ker π` using the simultaneous action on `Ω ⊔ Γ` and a pointwise stabilizer"):

1. the label points `k + c` for `c ∈ Φ` (a map adding `k`);
2. the pointwise stabilizer of these points in the graph group of `G` (`graphStabP_spec`, one
   **PointwiseStab** call); its pairs are graph pairs of `K` (`it_hv_ker_graph`);
3. the first parts, cut to at most `k²` generators (the module of `LcKrOK`), which generate the
   group of `K` on positions (`it_hv_ker_groupVal`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab)

variable {Ω C : Type} {k : ℕ}

section Val

variable {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- **The generators of `K` on positions**: the first parts of graph pairs of `K`, cut to at most
`k²` entries by the module of `LcKrOK`, give a canonical group value of `K`. -/
theorem it_hv_ker_groupVal {Φ : Finset (Fin L.q)} {qs : List (Perm (Fin k) × Perm (Fin L.q))}
    (hq : PairGens e L (itHvKer L Φ) qs) {hs : List (Perm (Fin k))}
    (hhs : gens hs = gens (qs.map Prod.fst)) (hl : hs.length ≤ k ^ 2) :
    GroupValC k (encGroup hs) (groupFin e (itHvKer L Φ)) := by
  refine ⟨hs, rfl, ?_, hl⟩
  rw [hhs]
  ext a
  rw [mem_gens_fst hq a]
  constructor
  · rintro ⟨g, -, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, L.lift_le _ hg, hg, rfl⟩

end Val

/-! ### The label points -/

theorem itHv_labPts_enc {q : ℕ} (l : List (Fin q)) :
    encPts (labPts k l) = .list (l.map fun i : Fin q => Val.nat ((i : ℕ) + k)) := by
  rw [itHv_encPts, natList, labPts, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp [Fin.natAdd, Nat.add_comm]

/-- **The label points of a list**, by a map adding `k`. -/
theorem it_hvLp_spec {P : Program} {am ak : ℕ} (ham : P.HasAt am (mapFuns am ak))
    (hak : P.funs[ak]? = some addKF) {q : ℕ} (l : List (Fin q)) (hl : l.length ≤ q) :
    FunDet P am (.list [.nat k, encPts l]) (encPts (labPts k l)) (10 ^ 5 * (k + q + 1) ^ 3) := by
  have hm := mapList_spec ham l (fun i : Fin q => Val.nat (i : ℕ)) (fun i : Fin q => Val.nat ((i : ℕ) + k)) (c := .nat k)
    (B := 100 * (k + q + 1)) (fun a _ a' _ h => by
      simp only [Val.nat.injEq] at h ⊢; omega)
    (fun i _ => by
      have g0 := Det.arg' (P := P) (vs := [.nat k, .nat i]) (rest := []) (j := 0) rfl
      have g1 := Det.arg' (P := P) (vs := [.nat k, .nat i]) (rest := []) (j := 1) rfl
      refine FunDet.intro hak ((Det.arith' (op := .add) g1 g0 (z := (i : ℕ) + k) rfl).mono ?_)
      have := wt_list2_le (.nat k) (.nat (i : ℕ))
      have := wt_nat_le k
      have := wt_nat_le (i : ℕ)
      have := wt_nat_le ((i : ℕ) + k)
      have := i.isLt
      omega)
  have e1 : Val.list (l.map fun i : Fin q => Val.nat (i : ℕ)) = encPts l := by
    rw [itHv_encPts, natList, List.map_map]; rfl
  rw [e1, ← itHv_labPts_enc] at hm
  refine hm.mono ?_
  have w1 : (encPts l).wt ≤ 5 * (k + q + 1) ^ 2 := wt_encPts_le_sq (by omega) (by omega)
  have w2 : (encPts (labPts k l)).wt ≤ 5 * (k + q + 1) ^ 2 :=
    wt_encPts_le_sq (by omega) (by simp only [labPts, List.length_map]; omega)
  have w3 := wt_list2_le (.nat k) (encPts l)
  have wk := wt_nat_le k
  have hD1 : 1 ≤ k + q + 1 := by omega
  have p12 : k + q + 1 ≤ (k + q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : (k + q + 1) ^ 2 ≤ (k + q + 1) ^ 3 := Nat.pow_le_pow_right hD1 (by omega)
  have a1 : l.length * (100 * (k + q + 1)) ≤ (k + q + 1) * (100 * (k + q + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have e2 : (k + q + 1) * (100 * (k + q + 1)) = 100 * (k + q + 1) ^ 2 := by ring
  have a2 : (l.length + 1) * ((Val.list [.nat k, encPts l]).wt + (encPts (labPts k l)).wt + 1) ≤
      (k + q + 1) * (30 * (k + q + 1) ^ 2) := Nat.mul_le_mul (by omega) (by omega)
  have e3 : (k + q + 1) * (30 * (k + q + 1) ^ 2) = 30 * (k + q + 1) ^ 3 := by ring
  have hmk : mapK = 1000 := rfl
  rw [hmk, Nat.mul_assoc]
  generalize l.length * (100 * (k + q + 1)) = A at *
  generalize (l.length + 1) * ((Val.list [.nat k, encPts l]).wt + (encPts (labPts k l)).wt + 1) = B at *
  generalize (k + q + 1) * (100 * (k + q + 1)) = A' at *
  generalize (k + q + 1) * (30 * (k + q + 1) ^ 2) = B' at *
  omega

/-! ### The program -/

/-- On `[[k, q], ⟨ps⟩, encPts Φ.sort]`: a group value of `K` with at most `k²` generators. -/
def itHvKgF (am stab kr : ℕ) : Expr :=
  .letE (.call am (mk2 (.get (arg 0) (.nat 0)) (arg 2)))
  (.letE (.call stab (mk3 (arg 0) (arg 1) (.var 1)))
    (.call kr (mk2 (.get (arg 0) (.nat 0)) (.var 2))))

/-- The cost bound of `itHvKgF` at `M = pM k q ps`, with the stabilizer primitive `pst` and the
cost `krC` of the reduction module. -/
def itHvKgC (pst : Prim) (krC : ℕ → ℕ) (M : ℕ) : ℕ :=
  pst.c * (200 * M ^ 4 + 2) ^ pst.k + graphStabK * (2 * M) ^ 8 + krC (M ^ 2) + 2 * 10 ^ 7 * M ^ 6

theorem itHvKgC_mono (pst : Prim) {krC : ℕ → ℕ} (hkr : Monotone krC) {a b : ℕ} (h : a ≤ b) :
    itHvKgC pst krC a ≤ itHvKgC pst krC b := by
  unfold itHvKgC
  have h2 := Nat.pow_le_pow_left h 2
  have h4 := Nat.pow_le_pow_left h 4
  have h6 := Nat.pow_le_pow_left h 6
  have h8 := Nat.pow_le_pow_left (show 2 * a ≤ 2 * b by omega) 8
  have hp := Nat.pow_le_pow_left (show 200 * a ^ 4 + 2 ≤ 200 * b ^ 4 + 2 by omega) pst.k
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hp)
    (Nat.mul_le_mul_left _ h8)) (hkr h2)) (Nat.mul_le_mul_left _ h6)

/-- `pM` of a list of at most `(k + q)²` pairs is at most `M²` for `M ≥ k + q + 2`. -/
theorem itHv_pM_sq {q : ℕ} {qs : List (Perm (Fin k) × Perm (Fin q))} (hl : qs.length ≤ (k + q) ^ 2)
    {M : ℕ} (hM : k + q + 2 ≤ M) : pM k q qs ≤ M ^ 2 := by
  have h1 : (k + q + 2) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hM 2
  have e : (k + q + 2) ^ 2 = (k + q) ^ 2 + 4 * (k + q) + 4 := by ring
  unfold pM
  omega

/-- The weight of at most `(k + q)²` pairs, at `M ≥ k + q + 2`. -/
theorem itHv_wt_qs {q : ℕ} {qs : List (Perm (Fin k) × Perm (Fin q))} (hql : qs.length ≤ (k + q) ^ 2)
    {M : ℕ} (hM : k + q + 2 ≤ M) : (Val.list (qs.map pairV)).wt ≤ 50 * M ^ 6 := by
  have h1 := wt_pairList_le qs
  have h3 : pM k q qs ^ 3 ≤ (M ^ 2) ^ 3 := Nat.pow_le_pow_left (itHv_pM_sq hql hM) 3
  have e : (M ^ 2) ^ 3 = M ^ 6 := by ring
  omega

set_option maxHeartbeats 2000000 in
/-- **The group value of `K` as a program** (one **PointwiseStab** call, then the reduction
module of `LcKrOK`). -/
theorem it_hvKg_spec (hst : PointwiseStab) {P : Program} {f am ak stab jp kr : ℕ} {krC : ℕ → ℕ}
    (hf : P.funs[f]? = some (itHvKgF am stab kr)) (ham : P.HasAt am (mapFuns am ak))
    (hak : P.funs[ak]? = some addKF) (hstab : P.HasAt stab (graphStabFuns stab jp))
    (hj : P.prims[jp]? = some (pointwiseStabPrim hst)) (hkr : LcKrOK P kr krC)
    (hkrm : Monotone krC) {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    (Φ : Finset (Fin L.q)) :
    FunAll P f (.list [.list [.nat k, .nat L.q], .list (ps.map pairV), encPts (Φ.sort (· ≤ ·))])
      (fun w c => GroupValC k w (groupFin e (itHvKer L Φ)) ∧ w.wt ≤ 320 * (k + 1) ^ 6 ∧
        c ≤ itHvKgC (pointwiseStabPrim hst) krC (pM k L.q ps)) := by
  obtain ⟨M, hM⟩ : ∃ M, M = pM k L.q ps := ⟨_, rfl⟩
  rw [← hM]
  have hMd : k + L.q + ps.length + 2 = M := by rw [hM]; rfl
  have hM1 : 1 ≤ M := by omega
  have m12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have m23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM1 (by omega)
  have m34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by omega)
  have hkq2 : (k + L.q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hkq3 : (k + L.q + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left (by omega) 3
  obtain ⟨W, hW⟩ : ∃ W, W = 1000 * M ^ 4 := ⟨_, rfl⟩
  have hW4 : 4 ≤ W := by omega
  set l := Φ.sort (· ≤ ·) with hl
  have hll : l.length ≤ L.q := by
    rw [hl, Finset.length_sort (· ≤ ·)]; simpa using Finset.card_le_univ Φ
  have hXl : (labPts k l).length ≤ L.q := by rw [labPts, List.length_map]; exact hll
  -- weights
  have wps : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := hM ▸ wt_pairList_le ps
  have wG : (encGroup (ps.map encPair)).wt ≤ 40 * M ^ 4 := hM ▸ wt_encGroup_pairs_le ps
  have wl : (encPts l).wt ≤ 5 * (k + L.q + 1) ^ 2 := wt_encPts_le_sq (by omega) (by omega)
  have wX : (encPts (labPts k l)).wt ≤ 5 * (k + L.q + 1) ^ 2 := wt_encPts_le_sq (by omega) (by omega)
  have wk := wt_nat_le k
  have wq := wt_nat_le L.q
  have wkq := wt_list2_le (.nat k) (.nat L.q)
  have w3 := wt_list3_le (.list [.nat k, .nat L.q]) (.list (ps.map pairV)) (encPts l)
  have w3' := wt_list3_le (.list [.nat k, .nat L.q]) (.list (ps.map pairV)) (encPts (labPts k l))
  have w2 := wt_list2_le (.nat k) (encPts l)
  have hinW : (Val.list [.list [.nat k, .nat L.q], .list (ps.map pairV), encPts l]).wt ≤ W := by
    omega
  set inp : Val := .list [.list [.nat k, .nat L.q], .list (ps.map pairV), encPts l] with hinp
  have ga : ∀ (env : List Val), env[0]? = some inp → ∀ (j : ℕ) (v : Val),
      [Val.list [.nat k, .nat L.q], .list (ps.map pairV), encPts l][j]? = some v → j + 2 ≤ W →
      v.wt ≤ W → StDC P env (arg j) v 3 0 W := fun env h0 j v hv hj hw =>
    (StDC.get (StDC.var' h0 hinW) (StDC.nat j hj) hv hw).mono (by omega) le_rfl
  have gk : ∀ (env : List Val), env[0]? = some inp →
      StDC P env (.get (arg 0) (.nat 0)) (.nat k) 5 0 W := fun env h0 =>
    StDC.get (ga env h0 0 (.list [.nat k, .nat L.q]) rfl (by omega) (by omega)) (StDC.nat 0 (by omega))
      (v := .nat k) rfl (by omega)
  -- step 1: the label points
  have d1 := StDC.call (StDC.mk2 (gk [inp] rfl) (ga [inp] rfl 2 (encPts l) rfl (by omega) (by omega))
    (by omega) hW4) (it_hvLp_spec (k := k) ham hak l hll) (by omega)
  refine FunAll.intro hf (EvalAll.letE d1.det fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- step 2: the pointwise stabilizer
  set E1 : List Val := [inp, encPts (labPts k l)]
  have d2 := (StDC.mk3 (ga E1 rfl 0 _ rfl (by omega) (by omega)) (ga E1 rfl 1 _ rfl (by omega)
    (by omega)) (StDC.var' (W := W) (env := E1) (i := 1) rfl (by omega)) (by omega) hW4).det
  have hpb : (pointwiseStabPrim hst).bound (.list [encGroup (ps.map encPair), encPts (labPts k l)]) ≤
      (pointwiseStabPrim hst).c * (200 * M ^ 4 + 2) ^ (pointwiseStabPrim hst).k :=
    prim_bound_le_wt _ (by have := wt_list2_le (encGroup (ps.map encPair)) (encPts (labPts k l)); omega)
  have hsb : graphStabK * stabPM k L.q ps (labPts k l) ^ 8 ≤ graphStabK * (2 * M) ^ 8 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold stabPM; omega) 8)
  obtain ⟨W2, hW2⟩ : ∃ W2, W2 = 1000 * M ^ 6 := ⟨_, rfl⟩
  have m46 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right hM1 (by omega)
  have hWW : W ≤ W2 := by omega
  refine EvalAll.letE (Ra := fun w cw => ∃ qs : List (Perm (Fin k) × Perm (Fin L.q)),
      w = .list (qs.map pairV) ∧ qs.length ≤ (k + L.q) ^ 2 ∧
      Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓ fixPts k L.q (labPts k l) ∧
      cw ≤ 13 * (W + 1) + (pointwiseStabPrim hst).c * (200 * M ^ 4 + 2) ^ (pointwiseStabPrim hst).k +
        graphStabK * (2 * M) ^ 8 + 50 * M ^ 6)
    (EvalAll.call_funAll d2 fun v ca h => ?_) fun v2 c2 h2 => ?_
  · obtain ⟨rfl, hca⟩ := h
    refine (graphStabP_spec hst hstab hj ps (labPts k l)).mono fun w cw hw => ?_
    obtain ⟨qs, rfl, hql, hqs, hcw⟩ := hw
    have := itHv_wt_qs (M := M) hql (by omega)
    exact ⟨qs, rfl, hql, hqs, by omega⟩
  obtain ⟨qs, rfl, hql, hqs, hc2⟩ := h2
  have hK := it_hv_ker_graph (l := l) (fun a => by rw [hl, Finset.mem_sort]) hps hqs
  -- step 3: the reduction to at most `k²` generators
  have hpq : pM k L.q qs ≤ M ^ 2 := itHv_pM_sq hql (by omega)
  have wqs := itHv_wt_qs (M := M) hql (by omega)
  set E2 : List Val := [inp, encPts (labPts k l), .list (qs.map pairV)]
  have gk2 : StDC P E2 (.get (arg 0) (.nat 0)) (.nat k) 5 0 W2 :=
    StDC.get (StDC.get (StDC.var' (W := W2) (env := E2) (i := 0) rfl (hinW.trans hWW))
      (StDC.nat 0 (by omega)) (v := .list [.nat k, .nat L.q]) rfl (by omega))
      (StDC.nat 0 (by omega)) (v := .nat k) rfl (by omega)
  have z2 : StDC P E2 (.var 2) (.list (qs.map pairV)) 1 0 W2 := StDC.var' rfl (by omega)
  have w2q := wt_list2_le (.nat k) (.list (qs.map pairV))
  have d3 := (StDC.mk2 gk2 z2 (by omega) (by omega)).det
  refine EvalAll.call_funAll d3 fun v ca h => ?_
  obtain ⟨rfl, hca⟩ := h
  refine (hkr k L.q qs).mono fun w cw hw => ?_
  obtain ⟨hs, rfl, hhs, hsl, hcw⟩ := hw
  refine ⟨it_hv_ker_groupVal hK hhs hsl, wt_encGroup_le_sq hsl, ?_⟩
  have hkc : krC (pM k L.q qs) ≤ krC (M ^ 2) := hkrm hpq
  have m6 : 1 ≤ M ^ 6 := Nat.one_le_pow _ _ hM1
  have hk6 : (k + 1) ^ 6 ≤ M ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have wo := wt_encGroup_le_sq hsl
  have hW8 : 13 * (W + 1) + 8 * (W2 + 1) ≤ 10 ^ 7 * M ^ 6 := by omega
  unfold itHvKgC
  omega

end GI.Impl
