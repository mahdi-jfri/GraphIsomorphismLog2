module

public import Workspace.Impl.AggCmpSetup
public import Workspace.Impl.AggCertWt
public import Workspace.Impl.GenNormPoly

@[expose] public section

/-!
# `CmRunOK` and `AsCompOK`: the comparison program meets its contract

`cm_setup_spec` runs the comparison phase for any sizes `W`, `Bw` that are large enough. Here we
choose these sizes from the input weight `W₀ = inW .giant S` alone, so that the cost and the
output weight are at most a polynomial `cmRunX` in `W₀`.

The sizes come from four facts about a call.
* The state value weighs at most `W₀`, so `k ≤ W₀`, and `q ≤ k + 2` (`GiantLabels.q_le`).
  We write `K = 2 W₀ + 3`, so `k + q + 1 ≤ K`.
* There are at most `2 q^κ ≤ 2 K^64` test tuples (`cmTups`), and `|dom| ≤ k`.
* There are `q.choose κ ≤ K^64` logs, and each log has `|dom|` stages of bounded size
  (`CmLogsOK`), so `cp_wt_logs` bounds their weight.
* The result list `a` of a run has one entry for each pair of tuples (`st_compTable`).

Then `cm_runOK` gives `CmRunOK`, and `cm_asCompOK` gives `AsCompOK` by `asCompOK_of_run`. The
bound `cmRunX` is polynomial (`cm_runX_pbu`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups GI.LocalCertificates Equiv
  Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-! ### The sizes, as functions of `K = 2 W₀ + 3` -/

/-- The bound on the number of test tuples. -/
def cmNb (K : ℕ) : ℕ := 2 * K ^ 64

/-- The bound on the measure `M₀` of the phase. -/
def cmMb (K : ℕ) : ℕ := 2 * (cmNb K * cmNb K * (K + 2) + 1)

/-- The bound on the weight of the parent data `cmParV`. -/
def cmPb (K : ℕ) : ℕ := 9 * (2 * (10 ^ 5 * (K + 1) ^ 70) + 1) + 4

/-- The bound on the weight of the output `cmOutV`. -/
def cmOutB (K : ℕ) : ℕ := 6 * (2 * (2 * cmPb K + 14 * (cmNb K * cmNb K) + 20) + 1) + 4

/-- The weight bound of the program states. -/
def cmBwU (K : ℕ) : ℕ := cmBw (cmPb K) K K (cmMb K) (cmNb K * cmNb K)

/-- The size `W` of the phase. -/
def cmWU (K : ℕ) : ℕ := 100 * cmBwU K + 10 ^ 10 * (2 * K + 1) ^ 12 + 2 * K ^ 64 + 2 * K + 1000

/-- **The phase bound of the comparison program** at input weight `W₀`. -/
noncomputable def cmRunX (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) (W₀ : ℕ) : ℕ :=
  cmSetC (cmWU (2 * W₀ + 3)) + 3 * cmOutB (2 * W₀ + 3) +
    (cmNb (2 * W₀ + 3) * cmNb (2 * W₀ + 3) * (2 * W₀ + 3 + 2) + 2) *
      (runK * (((cmMb (2 * W₀ + 3) + 1) * cpLoopC (cmMvCost hm (cmWU (2 * W₀ + 3))
        (cmStCost hst hpre hm (cmWU (2 * W₀ + 3))) (cmClCost hst hpre hm (cmWU (2 * W₀ + 3))))
        (cmBwU (2 * W₀ + 3)) + cmBwU (2 * W₀ + 3)) + 1))

/-- The phase bound is polynomial. -/
theorem cm_runX_pbu (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) :
    PBU fun _ W _ => cmRunX hst hpre hm W := by
  simp only [cmRunX, cmSetC, cmWU, cmBwU, cmBw, ansW, groupW, cmOutB, cmPb, cmNb, cmMb, cpLoopC,
    cmMvCost, cmStCost, cmClCost, cmAnsCost, cmFindCost, cmTestCost, cpG, cardCost, ckFindCost,
    ckTestCost, Prim.boundSize]
  norm_poly

/-! ### Weight bounds -/

section Wt

variable {k q : ℕ}

/-- The logs as the logs of the certificate phase. -/
theorem cm_logs_eq (logs : List (CmLog k q)) :
    logs.map cmLogV = (logs.map fun l => (l.T, l.lx, l.ly)).map cpLogV := by
  rw [List.map_map]; rfl

/-- **The weight of the parent data.** -/
theorem cm_wt_par {κ : ℕ} {sv : Val} {ps fx fy : GPairs k q} {logs : List (CmLog k q)}
    {tt : List (TestTuple q κ)} {n K : ℕ} (hsv : sv.wt ≤ K) (hK : k + q + 1 ≤ K)
    (hps : ps.length ≤ (k + q) ^ 2) (hfx : fx.length ≤ (k + q) ^ 2)
    (hfy : fy.length ≤ (k + q) ^ 2) (hll : logs.length ≤ K ^ 64)
    (hlg : ∀ l ∈ logs, CpLgLen l.lx ∧ CpLgLen l.ly) (htl : tt.length ≤ cmNb K) (hκ : κ ≤ K)
    (hn : n ≤ K) : (cmParV sv ps fx fy logs tt n).wt ≤ cmPb K := by
  have p1 : 1 ≤ (K + 1) ^ 70 := Nat.one_le_pow _ _ (by omega)
  have p6 : (k + q + 1) ^ 6 ≤ (K + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have p4 : (k + q + 1) ^ 4 ≤ (K + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 4).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have p64 : K ^ 64 ≤ (K + 1) ^ 64 := Nat.pow_le_pow_left (by omega) 64
  have p2 : (K + 1) ^ 2 ≤ (K + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have e70 : (K + 1) ^ 64 * (K + 1) ^ 6 = (K + 1) ^ 70 := by ring
  have hK1 : K + 1 ≤ (K + 1) ^ 6 := by
    have := Nat.pow_le_pow_right (n := K + 1) (by omega) (show 1 ≤ 6 by omega)
    rwa [pow_one] at this
  have h670 : (K + 1) ^ 6 ≤ (K + 1) ^ 70 := Nat.pow_le_pow_right (by omega) (by omega)
  have hK70 : K + 1 ≤ (K + 1) ^ 70 := by
    have := Nat.pow_le_pow_right (n := K + 1) (by omega) (show 1 ≤ 70 by omega)
    rwa [pow_one] at this
  set A := 10 ^ 5 * (K + 1) ^ 70 with hA
  refine (wt_list_le_of _ (c := A) ?_).trans
    (by simp only [List.length_cons, List.length_nil]; unfold cmPb; omega)
  have hgp : ∀ r : GPairs k q, r.length ≤ (k + q) ^ 2 → (Val.list (r.map pairV)).wt ≤ A := by
    intro r hr
    have := cp_wt_gp hr
    unfold gpV at this
    omega
  intro v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · have := wt_list2_le (.nat k) (.nat q)
    have := wt_nat_le k
    have := wt_nat_le q
    omega
  · exact hgp ps hps
  · exact hgp fx hfx
  · exact hgp fy hfy
  · rw [cm_logs_eq]
    have h := cp_wt_logs (NT := K ^ 64) (ls := logs.map fun l => (l.T, l.lx, l.ly))
      (by rw [List.length_map]; exact hll) (by
        simp only [List.mem_map]
        rintro _ ⟨l, hl, rfl⟩
        exact hlg l hl)
    have : K ^ 64 * (2801 * (k + q + 1) ^ 6) ≤ (K + 1) ^ 64 * (2801 * (K + 1) ^ 6) :=
      Nat.mul_le_mul p64 (Nat.mul_le_mul_left _ p6)
    have : (K + 1) ^ 64 * (2801 * (K + 1) ^ 6) = 2801 * (K + 1) ^ 70 := by rw [← e70]; ring
    omega
  · have h := wt_list_le_of (tt.map stTT) (c := 25 * (K + 1) ^ 2) (by
      simp only [List.mem_map]
      rintro _ ⟨a, -, rfl⟩
      exact wt_stTT_le a (by omega) hκ)
    rw [List.length_map] at h
    have : tt.length * (2 * (25 * (K + 1) ^ 2) + 1) ≤ (2 * (K + 1) ^ 64) * (51 * (K + 1) ^ 6) :=
      Nat.mul_le_mul (by unfold cmNb at htl; omega) (by omega)
    have : (2 * (K + 1) ^ 64) * (51 * (K + 1) ^ 6) = 102 * (K + 1) ^ 70 := by rw [← e70]; ring
    omega
  · have := wt_nat_le n
    omega
  · have := wt_nat_le tt.length
    have : 2 * K ^ 64 ≤ 2 * (K + 1) ^ 70 := by
      have : (K + 1) ^ 64 ≤ (K + 1) ^ 70 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    unfold cmNb at htl
    omega

/-- **The weight of the output**, for a result list with one entry for each pair of tuples. -/
theorem cm_wt_out {κ : ℕ} {sv : Val} {ps fx fy : GPairs k q} {logs : List (CmLog k q)}
    {tt : List (TestTuple q κ)} {n K : ℕ} {a : List Bool}
    (hP : (cmParV sv ps fx fy logs tt n).wt ≤ cmPb K) (htl : tt.length ≤ cmNb K)
    (ha : a.length = tt.length * tt.length) :
    (cmOutV sv k ps fx fy tt a).wt ≤ cmOutB K := by
  set c := 2 * cmPb K + 14 * (cmNb K * cmNb K) + 20 with hc
  have hm : ∀ (j : ℕ) (x : Val), [sv, .list [.nat k, .nat q], .list (ps.map pairV),
      .list (fx.map pairV), .list (fy.map pairV), .list (logs.map cmLogV), .list (tt.map stTT),
      .nat n, .nat tt.length][j]? = some x → x.wt ≤ cmPb K :=
    fun _ _ h => (wt_le_wt_list (List.mem_of_getElem? h)).le.trans hP
  have h0 := hm 0 _ rfl
  have h1 := hm 1 _ rfl
  have h2 := hm 2 _ rfl
  have h3 := hm 3 _ rfl
  have h4 := hm 4 _ rfl
  have hT := hm 6 _ rfl
  have hA : (Val.list (a.map boolVal)).wt ≤ 7 * (cmNb K * cmNb K) + 4 := by
    have h := wt_list_le_of (a.map boolVal) (c := 3) (by
      simp only [List.mem_map]
      rintro _ ⟨b, -, rfl⟩
      have := wt_boolVal_le b
      omega)
    rw [List.length_map, ha] at h
    have : tt.length * tt.length ≤ cmNb K * cmNb K := Nat.mul_le_mul htl htl
    omega
  refine (wt_list_le_of _ (c := c) ?_).trans
    (by simp only [List.length_cons, List.length_nil]; unfold cmOutB; omega)
  intro v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · have := wt_list2_le (.list (tt.map stTT)) (.list (a.map boolVal))
    omega

end Wt

/-! ### The contract -/

variable (I : Iface) (Pg : Program) (F : Funs)

/-- The result list of a run has one entry for each pair of tuples. -/
theorem cm_res_length {Ω C : Type} {S : State Ω C} {L : SuppliedLabels S}
    {Ag : Aggregation P₀ S L.toGiantLabels} {a : List Bool} (ex : Exec P₀ Ag.compScript a) :
    a.length = Ag.tests.tuples.length * Ag.tests.tuples.length := by
  have ha := ex.exact
  rw [st_compTable] at ha
  rw [ha, List.length_flatMap]
  simp only [List.length_map]
  rw [List.map_const', List.sum_replicate, smul_eq_mul]

set_option maxHeartbeats 4000000 in
/-- **The comparison program meets `CmRunOK`** with the polynomial bound `cmRunX`. -/
theorem cm_runOK (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)
    {fm b d stp tb jm jp : ℕ} (hset : CmSetAt Pg F hst hm fm b d stp tb jm jp) :
    CmRunOK I Pg F (cmRunX hst hpre hm) fm := by
  intro Ω C k e c S sv' lv L hcall Cs Ag₀ hAg₀ hsub hcl sv ps fx fy logs hcan hps hfx hfy hpl
    hfxl hfyl hlogs
  haveI := Ag₀.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  -- the input sizes
  set W₀ := I.inW .giant S with hW₀
  set K := 2 * W₀ + 3 with hK
  have hsvW : sv.wt ≤ W₀ := by
    have := Canon.wt_le hcan
    simp only [hW₀, Iface.inW, Iface.card_eq e]
    omega
  have hk : k ≤ sv.wt := StateVal.k_le_wt hcan.stateVal
  have hqk := GiantLabels.q_le e L.toGiantLabels
  have hq0 : 0 < L.q := by have := hcall.q₀; omega
  have hκ : P₀.κ = 64 := rfl
  have hqb : P₀.κ ≤ L.q := by
    have := hcall.q₀
    have : P₀.q₀ = 2064 := rfl
    omega
  have hkq : k + L.q + 1 ≤ K := by omega
  have hq64 : L.q ^ P₀.κ ≤ K ^ 64 := by rw [hκ]; exact Nat.pow_le_pow_left (by omega) 64
  set O := cmTupOrder L.q P₀.κ hq0 with hO
  set N := O.tuples.length with hN
  have hNb : N ≤ cmNb K := by
    have : N ≤ 2 * L.q ^ P₀.κ := by
      have := List.length_filterMap_le (cmTupOf (κ := P₀.κ) hq0) (List.range (2 * L.q ^ P₀.κ))
      rw [List.length_range] at this
      exact this
    unfold cmNb; omega
  set n := Fintype.card S.dom with hn
  have hnk : n ≤ k := by rw [hn, ← cm_card_dom e S]; exact length_domNat_le e S.dom
  -- the logs
  have hlogs' := hlogs
  obtain ⟨⟨OS, hOS⟩, hl⟩ := hlogs'
  have hll : logs.length ≤ K ^ 64 := by
    have h1 : logs.length = OS.sets.length := by rw [← hOS, List.length_map]
    rw [h1, TestSetOrder.length_eq]
    exact (Nat.choose_le_pow _ _).trans hq64
  have hstg : ∀ (T : Finset (Fin L.q)) (z : Ω → C) (ls : List (CmStage k L.q)),
      CmStgs e Ag₀.πd T z ls → CpLgLen ls := by
    intro T z ls ⟨hlen, hst'⟩
    refine ⟨by omega, fun dd hd => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hd
    obtain ⟨-, h1, incl, hnd, -, h2⟩ := hst' j hj
    refine ⟨h1, ?_⟩
    rw [h2, List.length_map]
    exact hnd.length_le_card.trans hnk
  have hlg : ∀ l ∈ logs, CpLgLen l.lx ∧ CpLgLen l.ly := fun l hl' =>
    ⟨hstg _ _ _ (hl l hl').1, hstg _ _ _ (hl l hl').2⟩
  -- the sizes of the phase
  have hP : (cmParV sv ps fx fy logs O.tuples n).wt ≤ cmPb K :=
    cm_wt_par (by omega) hkq hpl hfxl hfyl hll hlg hNb (by omega) (by omega)
  have hBw : cmBw (cmParV sv ps fx fy logs O.tuples n).wt k L.q (2 * (N * N * (n + 2) + 1))
      (N * N) ≤ cmBwU K := by
    have hNN : N * N ≤ cmNb K * cmNb K := Nat.mul_le_mul hNb hNb
    have hM : 2 * (N * N * (n + 2) + 1) ≤ cmMb K := by
      unfold cmMb
      have := Nat.mul_le_mul hNN (show n + 2 ≤ K + 2 by omega)
      omega
    have hA : ansW k ≤ ansW K := by
      unfold ansW groupW
      have h1 : (k + 1) ^ 2 ≤ (K + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h2 : ((k ^ 2 + 2) * (k + 1)) ^ 2 ≤ ((K ^ 2 + 2) * (K + 1)) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul (by
          have := Nat.pow_le_pow_left (show k ≤ K by omega) 2; omega) (by omega)) 2
      omega
    have h6 : (k + L.q + 1) ^ 6 ≤ (K + K + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have h3 : 10 ^ 4 * (2 * (N * N * (n + 2) + 1) + N * N + 1) * (k + L.q + 1) ^ 6 ≤
        10 ^ 4 * (cmMb K + cmNb K * cmNb K + 1) * (K + K + 1) ^ 6 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) h6
    unfold cmBwU cmBw
    omega
  set W := cmWU K with hWd
  have hW : 100 * cmBwU K + 1000 ≤ W := by unfold cmWU at hWd; omega
  have hW2 : 10 ^ 10 * (k + L.q + 1) ^ 12 ≤ W := by
    have : (k + L.q + 1) ^ 12 ≤ (2 * K + 1) ^ 12 := Nat.pow_le_pow_left (by omega) 12
    unfold cmWU at hWd; omega
  have hY : 2 * L.q ^ P₀.κ + L.q + P₀.κ + 10 ≤ W := by unfold cmWU at hWd; omega
  -- the run
  have htr : S.Transitive := hcall.good.2.2.1
  refine (cm_setup_spec I Pg F hst hpre hm hset hcall.inj hcan hcall.good htr hAg₀ hsub hcl
    hcall.ih.below hq0 hps hpl hlogs hBw hW hW2 hY).mono ?_
  rintro w cost ⟨Ag, hAg, a, ex, rfl, hcalls, hc⟩
  have ha : a.length = N * N := by
    rw [cm_res_length ex, hAg.2.2.1]
  have hwt := cm_wt_out (k := k) (sv := sv) (ps := ps) (fx := fx) (fy := fy) hP hNb ha
  have hcalls' : ex.calls.length ≤ N * N * (n + 2) + 1 := hcalls
  have eO : (cmOutV sv k ps fx fy O.tuples a).wt =
      (cmOutV sv k ps fx fy (cmTupOrder L.q P₀.κ hq0).tuples a).wt := rfl
  refine ⟨O, Ag, hAg, a, ex, rfl, ?_, ?_⟩
  · -- the cost
    set R := runK * (((2 * (N * N * (n + 2) + 1) + 1) * cpLoopC (cmMvCost hm W
      (cmStCost hst hpre hm W) (cmClCost hst hpre hm W)) (cmBwU K) + cmBwU K) + 1) with hR
    set R' := runK * (((cmMb K + 1) * cpLoopC (cmMvCost hm W (cmStCost hst hpre hm W)
      (cmClCost hst hpre hm W)) (cmBwU K) + cmBwU K) + 1) with hR'
    have hRR : R ≤ R' := by
      have hM : 2 * (N * N * (n + 2) + 1) ≤ cmMb K := by
        unfold cmMb
        have := Nat.mul_le_mul (Nat.mul_le_mul hNb hNb) (show n + 2 ≤ K + 2 by omega)
        omega
      rw [hR, hR']
      gcongr
    have hcl' : ex.calls.length + 1 ≤ cmNb K * cmNb K * (K + 2) + 2 := by
      have := Nat.mul_le_mul (Nat.mul_le_mul hNb hNb) (show n + 2 ≤ K + 2 by omega)
      omega
    have hnat : cmSetC W + 3 * (cmOutV sv k ps fx fy O.tuples a).wt +
        (ex.calls.length + 1) * R ≤ cmRunX hst hpre hm W₀ := by
      have := Nat.mul_le_mul hcl' hRR
      unfold cmRunX
      rw [← hK, ← hWd, ← hR']
      omega
    have hnat' : ((cmSetC W + 3 * (cmOutV sv k ps fx fy O.tuples a).wt : ℕ) : ℝ) +
        ((ex.calls.length : ℝ) + 1) * (R : ℝ) ≤ (cmRunX hst hpre hm W₀ : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).2 hnat
      push_cast at this ⊢
      linarith
    rw [hR] at hnat'
    push_cast at hc hnat' ⊢
    linarith
  · -- the weight
    unfold cmRunX
    rw [← hK]
    omega

/-- **`AsCompOK` for the comparison program**, for any hand-over whose relation `comp` gives
`CmHand` and whose relation `items` contains `ItHand`. -/
theorem cm_asCompOK (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) (H : AsHand)
    {fm b d stp tb jm jp : ℕ} (hset : CmSetAt Pg F hst hm fm b d stp tb jm jp)
    (hc : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, H.comp e c S L Cs st → CmHand e c S L Cs st)
    (hi : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, ItHand e c S L Cs st → H.items e c S L Cs st) :
    AsCompOK I Pg F H (cmRunX hst hpre hm) fm :=
  asCompOK_of_run I Pg F H _ fm hc hi (cm_runOK I Pg F hst hpre hm hset)

end GI.Impl
