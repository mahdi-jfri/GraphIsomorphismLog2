module

public import Workspace.Impl.TermRadLoop
public import Workspace.Impl.TermChain
public import Workspace.Impl.TermHyp
public import Workspace.Cited.Facts

@[expose] public section

/-!
# T2: the radical preimage as a program

The paragraph after Lemma A.21: "Construct a normal chain from `H` to `N` whose nonabelian steps
are chief factors of `H` … For each nonabelian image factor `U/V`, compute the preimage of
`C_{H/V}(U/V)` … all these preimages are normal, so their intersection is a normalized-subgroup
intersection. Their intersection is precisely the radical preimage."

The function `radEntry`, on `[gens H, gens N]`:
1. a nonabelian-chief normal chain `C₀ = H ≥ ⋯ ≥ C_L ≤ N` from `H` to `N` (`tcChainEntry`,
   `tcChain_spec` in `TermChain.lean`);
2. the loop over the factors `j < L` (`iterFuns`, step `radStepBody`, `radStep_spec`), starting
   from `H`: it keeps `A ∩ C_j` for every nonabelian factor `N C_j / N C_{j+1}`;
3. the generators of the result, cut to at most `m²` by one call of
   **NormalizedIntersection** on `A ∩ A` (the output form of the cited tasks, `GensOf`).
The result is `radicalPreimage H N` by `nonabelianChief_rad_mem_iff` (`NonabelianChief.lean`).

Cost (`rad_spec`): the nonabelian-chief chain, `L ≤ m²` steps of `radStepCost`, and the final
intersection; all polynomial in the weight of the input plus `radQ n` (`radCost_le`,
`rad_termRadSpec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- **The radical program** on `[gens H, gens N]`. Environment `[a, chain, A]`. -/
def radEntry (it tc jni : ℕ) : Expr :=
  .letE (.call tc (.var 0))
  (.letE (.call it (mk3 (mk3 (arg 0) (arg 1) (.var 1))
      (.arith .sub (.length (.var 1)) (.nat 1)) (arg 0)))
    (.prim jni (mk2 (.var 2) (.var 2))))

/-- `TcChainAt` at the standard offsets of `tcChainFuns b`. -/
abbrev TcChainBundleAt (P : Program) (b jmb jpre jmem jnc jni jder : ℕ)
    (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup) : Prop :=
  TcChainAt P b (b + 12) (b + 1) (b + 2) (b + 15) (b + 18) (b + 25) (b + 30)
    (b + 3) (b + 35) (b + 4) (b + 5) (b + 38) (b + 172) (b + 96) (b + 121) (b + 145)
    (b + 6) (b + 69) (b + 41) (b + 7)
    (b + 8) (b + 44) (b + 9) (b + 47) (b + 10) (b + 50) (b + 62) (b + 11) (b + 65)
    jmb jpre jmem jnc jni jder hmb hpre hmem hnc hni hder

/-- Where the radical program and its modules sit. -/
structure RadAt (P : Program) (f it g ap mg le tc fk jmb jpre jmem jnc jni jder : ℕ)
    (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup) : Prop where
  entry : P.funs[f]? = some (radEntry it tc jni)
  iter : P.HasAt it (iterFuns it g)
  step : RadStepAt P g ap mg le jder jni fk jmem jpre hder hni hmem hpre
  tc : TcChainBundleAt P tc jmb jpre jmem jnc jni jder hmb hpre hmem hnc hni hder

theorem rad_stepCost_mono (pd pq pi pm : Prim) {W W' : ℕ} (h : W ≤ W') :
    radStepCost pd pq pi pm W ≤ radStepCost pd pq pi pm W' := by
  have hY : 1000 * (W + 1) ^ 6 ≤ 1000 * (W' + 1) ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  unfold radStepCost
  have := rad_boundSize_mono pd hY
  have := rad_boundSize_mono pq hY
  have := rad_boundSize_mono pi hY
  have := Nat.mul_le_mul hY (rad_boundSize_mono pm hY)
  have := Nat.pow_le_pow_left hY 3
  omega

/-- The cost bound of the radical program, for an input of weight `T`. -/
def radCost (pc pd pq pi pm : Prim) (T : ℕ) : ℕ :=
  pc.boundSize T + pi.boundSize (2000 * (T + 1) ^ 8) +
    200 * (T + 1) ^ 8 * radStepCost pd pq pi pm (2000 * (T + 1) ^ 8) + 10 ^ 10 * (T + 1) ^ 16

/-- **T2: the radical preimage** (paragraph after Lemma A.21). On `[gens H, gens N]`, with
`N ≤ H` normalized by `H` and `N` transitive on `Fin n`, the program returns generators of
`radicalPreimage H N`, at cost at most `radCost` of the weight of the input plus `radQ n`. -/
theorem rad_spec (hMa : MarotiPrimitive) {hmb : MinimalBlocks} {hpre : Preimage}
    {hmem : Membership} {hnc : NormalClosure} {hni : NormalizedIntersection}
    {hder : DerivedSubgroup}
    {P : Program} {f it g ap mg le tc fk jmb jpre jmem jnc jni jder : ℕ}
    (hP : RadAt P f it g ap mg le tc fk jmb jpre jmem jnc jni jder
      hmb hpre hmem hnc hni hder)
    (gs ns : List (Perm (Fin n))) (hNH : gens ns ≤ gens gs)
    (hn : GI.Multicoset.Normalizes (gens gs) (gens ns))
    [MulAction.IsPretransitive (gens ns) (Fin n)] :
    FunAll P f (.list [encGroup gs, encGroup ns]) (fun u cost =>
      GensOf (GI.Multicoset.radicalPreimage (gens gs) (gens ns)) u ∧
      cost ≤ radCost (tcChainPrim hmb hpre hmem hnc hni hder) (derivedSubgroupPrim hder)
        (gmpFactorKernelPrim hmem hpre) (normalizedIntersectionPrim hni) (membershipPrim hmem)
        ((Val.list [encGroup gs, encGroup ns]).wt + radQ n)) := by
  set T := (Val.list [encGroup gs, encGroup ns]).wt + radQ n with hT
  have hgT : (encGroup gs).wt < T := (wt_le_wt_list (by simp)).trans_le (Nat.le_add_right _ _)
  have hnT : (encGroup ns).wt < T := (wt_le_wt_list (by simp)).trans_le (Nat.le_add_right _ _)
  have hnW : n + 1 ≤ T := by
    have := S_le_wt_encGroup gs
    have : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hn_wt : n ≤ (Val.list [encGroup gs, encGroup ns]).wt := by
    have := S_le_wt_encGroup gs
    have : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have : (encGroup gs).wt < (Val.list [encGroup gs, encGroup ns]).wt := wt_le_wt_list (by simp)
    omega
  have hT8 : T + 1 ≤ (T + 1) ^ 8 := Nat.le_self_pow (by norm_num) _
  have hn8 : (n + 1) ^ 8 ≤ (T + 1) ^ 8 := Nat.pow_le_pow_left (by omega) _
  have hn6 : (n + 1) ^ 6 ≤ (T + 1) ^ 8 :=
    (Nat.pow_le_pow_left (show n + 1 ≤ T + 1 by omega) 6).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have dinp := Det.var' (P := P) (env := [.list [encGroup gs, encGroup ns]]) (i := 0) rfl
  have htc_spec := tcChain_spec hMa hP.tc gs ns hNH hn (fun _ => inferInstance)
  refine FunAll.intro hP.entry (EvalAll.letE
    (Ra := fun v1 c1 => (∃ Hs, SeriesVal n v1 Hs ∧ IsNonabelianChiefChain (gens gs) (gens ns) Hs) ∧
      c1 ≤ (tcChainPrim hmb hpre hmem hnc hni hder).boundSize T +
        2 * T + 100 * (n + 1) ^ 8 + 10)
    (EvalAll.call_funAll dinp fun v ca hv => ?_) fun v1 c1 h1 => ?_)
  · obtain ⟨rfl, hca⟩ := hv
    refine htc_spec.mono fun v1 cb ⟨⟨Hs, hSv, hs⟩, hcb⟩ => ⟨⟨Hs, hSv, hs⟩, ?_⟩
    have hb1 : cb ≤ (tcChainPrim hmb hpre hmem hnc hni hder).boundSize T :=
      hcb.trans (tcChainCost_le_boundSize hmb hpre hmem hnc hni hder hn_wt)
    have hw1 := SeriesVal.wt_le hSv
    have hWT : (Val.list [encGroup gs, encGroup ns]).wt ≤ T := Nat.le_add_right _ _
    clear * - hca hb1 hw1 hWT
    omega
  obtain ⟨⟨Hs, ⟨L, rfl, hLl, hl, rfl⟩, hs⟩, hc1⟩ := h1
  -- the loop
  set cs := radCsVal L with hcsdef
  have hcsw : cs.wt ≤ 100 * (n + 1) ^ 8 := SeriesVal.wt_le ⟨L, rfl, hLl, hl, rfl⟩
  have hLc : L.length < cs.wt := by
    have h1 := length_lt_wt_list (L.map fun hs => Val.list (hs.map encPerm))
    simp only [List.length_map] at h1
    exact h1
  set c := Val.list [encGroup gs, encGroup ns, cs] with hc
  have hcw : c.wt ≤ 2 * ((encGroup gs).wt + (encGroup ns).wt + cs.wt) + 7 :=
    wt_list3_le (encGroup gs) (encGroup ns) cs
  set M := (encGroup gs).wt + 320 * (n + 1) ^ 6 with hM
  set k := L.length - 1 with hk
  have hstep : ∀ i acc, i < k → RadInv (gens gs) (gens ns) (L.map gens) (encGroup gs) i acc →
      FunAll P g (.list [c, .nat i, acc]) (fun w cost =>
        RadInv (gens gs) (gens ns) (L.map gens) (encGroup gs) (i + 1) w ∧
        cost ≤ radStepCost (derivedSubgroupPrim hder) (gmpFactorKernelPrim hmem hpre)
          (normalizedIntersectionPrim hni) (membershipPrim hmem) (2000 * (T + 1) ^ 8)) := by
    intro i acc hi hinv
    refine (radStep_spec hP.step hNH hn hs hl (by omega) hinv).mono fun w cost h => ⟨h.1, ?_⟩
    refine h.2.trans (rad_stepCost_mono _ _ _ _ ?_)
    obtain ⟨A, -, -, hAw⟩ := hinv
    have h3 := wt_list3_le c (.nat i) acc
    have h4 := wt_nat_le i
    have h5 : (encGroup gs).wt + (encGroup ns).wt < (Val.list [encGroup gs, encGroup ns]).wt := by
      simp [Val.wt]
      omega
    show (Val.list [c, .nat i, acc]).wt + radQ n ≤ _
    omega
  have h0 : RadInv (gens gs) (gens ns) (L.map gens) (encGroup gs) 0 (encGroup gs) :=
    ⟨gens gs, ⟨gs, rfl, rfl⟩, fun h => ⟨fun hh => ⟨hh, fun j hj => absurd hj (by omega)⟩,
      fun hh => hh.1⟩, by omega⟩
  have hit := iter_spec hP.iter (c := c) (k := k) (M := M) h0
    (fun i acc _ hinv => by obtain ⟨A, -, -, hAw⟩ := hinv; omega) hstep
  -- the argument of the loop
  have dcs := Det.var' (P := P) (env := [.list [encGroup gs, encGroup ns], cs]) (i := 1) rfl
  have d0' := Det.arg' (P := P) (vs := [encGroup gs, encGroup ns]) (rest := [cs]) (j := 0) rfl
  have dc := Det.mk3 d0' (Det.arg' (P := P) (vs := [encGroup gs, encGroup ns]) (rest := [cs])
    (j := 1) rfl) dcs
  have dk := Det.arith' (z := k) (P := P) (op := .sub) (Det.length dcs) (Det.nat 1)
    (by simp [BinOp.eval, hk])
  have darg := Det.mk3 dc dk (Det.arg' (P := P) (vs := [encGroup gs, encGroup ns]) (rest := [cs])
    (j := 0) rfl)
  have hkc : k ≤ 100 * (T + 1) ^ 8 := by omega
  have hw3 := wt_list3_le c (.nat k) (encGroup gs)
  have hwk := wt_nat_le k
  have hcsT : cs.wt ≤ 100 * (T + 1) ^ 8 := by omega
  have darg' := darg.mono (c' := 100 * (T + 1) ^ 8 * 100) (by
    have := wt_list2_le (encGroup gs) (encGroup ns)
    have := wt_list1_le cs
    have := wt_nat_le L.length
    have e1 : (Val.list [encGroup gs, encGroup ns, cs]).wt = c.wt := rfl
    have e2 : (Val.list [Val.list [encGroup gs, encGroup ns, cs], .nat k, encGroup gs]).wt =
      (Val.list [c, .nat k, encGroup gs]).wt := rfl
    have e3 : (List.map (fun hs => Val.list (List.map encPerm hs)) L).length = L.length := by simp
    omega)
  set B := radStepCost (derivedSubgroupPrim hder) (gmpFactorKernelPrim hmem hpre)
    (normalizedIntersectionPrim hni) (membershipPrim hmem) (2000 * (T + 1) ^ 8) with hB
  set I := k * B + loopModK * (k + 1) * ((Val.list [c, .nat k, encGroup gs]).wt + k + M + 1)
    with hI
  have hit' : FunAll P it (.list [c, .nat k, encGroup gs]) (fun w cost =>
      RadInv (gens gs) (gens ns) (L.map gens) (encGroup gs) k w ∧ cost ≤ I) :=
    hit.mono fun w cost h => ⟨h.1, by
      have := h.2
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
      exact this⟩
  refine EvalAll.letE (Ra := fun w cost => RadInv (gens gs) (gens ns) (L.map gens) (encGroup gs) k w ∧
      cost ≤ 100 * (T + 1) ^ 8 * 100 + I + M + 1)
    (EvalAll.call_funAll darg' fun v ca hv => ?_) fun v2 c2 h2 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hit'.mono fun w cb h => ⟨h.1, ?_⟩
    obtain ⟨A, -, -, hAw⟩ := h.1
    have := h.2
    omega
  obtain ⟨A, hA, hAm, hAw⟩ := h2.1
  have hc2 := h2.2
  -- the final intersection `A ∩ A`
  have dA := Det.var' (P := P) (env := [.list [encGroup gs, encGroup ns], cs, v2]) (i := 2) rfl
  have hAA := wt_list2_le v2 v2
  have hAs : (Val.list [v2, v2]).size ≤ 2000 * (T + 1) ^ 8 := (Val.size_le_wt _).trans (by omega)
  refine (normalizedIntersection_call hni hP.step.ji (Det.mk2 dA dA) hA hA
    (fun x hx y hy => A.mul_mem (A.mul_mem hx hy) (A.inv_mem hx))).mono fun u cu h => ⟨?_, ?_⟩
  · obtain ⟨hu, -⟩ := h
    rw [inf_idem] at hu
    have hR : A = GI.Multicoset.radicalPreimage (gens gs) (gens ns) := by
      ext h
      rw [hAm, nonabelianChief_rad_mem_iff hNH hn hs, List.length_map]
    rw [← hR]
    exact hu
  · obtain ⟨hu0, hcu⟩ := h
    have huw := GensVal.wt_le hu0
    have hb2 := (normalizedIntersectionPrim hni).bound_le hAs
    have hu := hcu
    unfold radCost
    have eB : 200 * (T + 1) ^ 8 * radStepCost (derivedSubgroupPrim hder) (gmpFactorKernelPrim hmem hpre)
      (normalizedIntersectionPrim hni) (membershipPrim hmem) (2000 * (T + 1) ^ 8) =
      200 * (T + 1) ^ 8 * B := rfl
    rw [eB]
    -- the loop overhead
    have hI' : I ≤ 100 * (T + 1) ^ 8 * B + 10 ^ 9 * (T + 1) ^ 16 := by
      have h1 : k * B ≤ 100 * (T + 1) ^ 8 * B := Nat.mul_le_mul_right _ hkc
      have h2 : loopModK * (k + 1) * ((Val.list [c, .nat k, encGroup gs]).wt + k + M + 1) ≤
          loopModK * (200 * (T + 1) ^ 8) * (2000 * (T + 1) ^ 8) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      have e : loopModK * (200 * (T + 1) ^ 8) * (2000 * (T + 1) ^ 8) = 400000000 * (T + 1) ^ 16 := by
        simp only [loopModK]; ring
      omega
    have h16 : (T + 1) ^ 8 ≤ (T + 1) ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
    have hB2 : 100 * (T + 1) ^ 8 * B ≤ 200 * (T + 1) ^ 8 * B :=
      Nat.mul_le_mul_right _ (by omega)
    have h13 : 13 * (n + 1) ^ 6 ≤ 13 * (T + 1) ^ 16 := by omega
    clear_value I B M k c cs T
    omega

/-! ### The polynomial bound -/

/-- A bound `B ≤ a X^d` gives `p.boundSize B ≤ p.c (a + 2)^k X^(d k)`. -/
theorem rad_bS_le (p : Prim) {B a d X : ℕ} (hX : 1 ≤ X) (h : B ≤ a * X ^ d) :
    p.boundSize B ≤ p.c * (a + 2) ^ p.k * X ^ (d * p.k) := by
  unfold Prim.boundSize
  have h1 : B + 2 ≤ (a + 2) * X ^ d := by
    have : 1 ≤ X ^ d := Nat.one_le_pow _ _ hX
    nlinarith
  calc p.c * (B + 2) ^ p.k ≤ p.c * ((a + 2) * X ^ d) ^ p.k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = p.c * (a + 2) ^ p.k * X ^ (d * p.k) := by rw [mul_pow, ← pow_mul]; ring

theorem rad_pow_le {X e D : ℕ} (hX : 1 ≤ X) (h : e ≤ D) : X ^ e ≤ X ^ D :=
  Nat.pow_le_pow_right hX h

/-- The constant `1000 · 2001⁶` that bounds `Y / X⁴⁸` in the step. -/
def radY0 : ℕ := 1000 * 2001 ^ 6

/-- The exponent of the polynomial bound. -/
def radD (pc pd pq pi pm : Prim) : ℕ := 200 + 48 * (pc.k + pd.k + pq.k + pi.k + pm.k)

/-- The constant of the polynomial bound. -/
def radK (pc pd pq pi pm : Prim) : ℕ :=
  pc.c * 3 ^ pc.k + pi.c * 2002 ^ pi.k + 200 * (pd.c * (radY0 + 2) ^ pd.k +
    pq.c * (radY0 + 2) ^ pq.k + pi.c * (radY0 + 2) ^ pi.k + radY0 * (pm.c * (radY0 + 2) ^ pm.k) +
    10 ^ 8 * radY0 ^ 3) + 10 ^ 10

/-- **The radical program is polynomial**: `radCost ≤ radK (T + 1)^radD`. -/
theorem radCost_le (pc pd pq pi pm : Prim) (T : ℕ) :
    radCost pc pd pq pi pm T ≤ radK pc pd pq pi pm * (T + 1) ^ radD pc pd pq pi pm := by
  set X := T + 1 with hXdef
  have hX : 1 ≤ X := by omega
  set D := radD pc pd pq pi pm with hD
  -- the step at `W = 2000 X⁸`
  have hY : 1000 * (2000 * X ^ 8 + 1) ^ 6 ≤ radY0 * X ^ 48 := by
    have h1 : 2000 * X ^ 8 + 1 ≤ 2001 * X ^ 8 := by
      have : 1 ≤ X ^ 8 := Nat.one_le_pow _ _ hX
      omega
    calc 1000 * (2000 * X ^ 8 + 1) ^ 6 ≤ 1000 * (2001 * X ^ 8) ^ 6 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
      _ = radY0 * X ^ 48 := by simp only [radY0]; ring
  have sd := rad_bS_le pd hX hY
  have sq := rad_bS_le pq hX hY
  have si := rad_bS_le pi hX hY
  have sm := rad_bS_le pm hX hY
  have sY3 : (1000 * (2000 * X ^ 8 + 1) ^ 6) ^ 3 ≤ radY0 ^ 3 * X ^ 144 := by
    calc (1000 * (2000 * X ^ 8 + 1) ^ 6) ^ 3 ≤ (radY0 * X ^ 48) ^ 3 := Nat.pow_le_pow_left hY 3
      _ = radY0 ^ 3 * X ^ 144 := by ring
  have sYm := Nat.mul_le_mul hY sm
  -- all exponents below `D - 8`
  have e1 : X ^ (48 * pd.k) ≤ X ^ (D - 8) := rad_pow_le hX (by simp only [hD, radD]; omega)
  have e2 : X ^ (48 * pq.k) ≤ X ^ (D - 8) := rad_pow_le hX (by simp only [hD, radD]; omega)
  have e3 : X ^ (48 * pi.k) ≤ X ^ (D - 8) := rad_pow_le hX (by simp only [hD, radD]; omega)
  have e4 : X ^ 48 * X ^ (48 * pm.k) ≤ X ^ (D - 8) := by
    rw [← pow_add]; exact rad_pow_le hX (by simp only [hD, radD]; omega)
  have e5 : X ^ 144 ≤ X ^ (D - 8) := rad_pow_le hX (by simp only [hD, radD]; omega)
  have hstep : radStepCost pd pq pi pm (2000 * X ^ 8) ≤
      (pd.c * (radY0 + 2) ^ pd.k + pq.c * (radY0 + 2) ^ pq.k + pi.c * (radY0 + 2) ^ pi.k +
        radY0 * (pm.c * (radY0 + 2) ^ pm.k) + 10 ^ 8 * radY0 ^ 3) * X ^ (D - 8) := by
    unfold radStepCost
    have f1 := Nat.mul_le_mul_left (pd.c * (radY0 + 2) ^ pd.k) e1
    have f2 := Nat.mul_le_mul_left (pq.c * (radY0 + 2) ^ pq.k) e2
    have f3 := Nat.mul_le_mul_left (pi.c * (radY0 + 2) ^ pi.k) e3
    have f4 := Nat.mul_le_mul_left (radY0 * (pm.c * (radY0 + 2) ^ pm.k)) e4
    have f5 := Nat.mul_le_mul_left (10 ^ 8 * radY0 ^ 3) e5
    have g4 : radY0 * X ^ 48 * (pm.c * (radY0 + 2) ^ pm.k * X ^ (48 * pm.k)) =
        radY0 * (pm.c * (radY0 + 2) ^ pm.k) * (X ^ 48 * X ^ (48 * pm.k)) := by ring
    have g5 : 10 ^ 8 * (radY0 ^ 3 * X ^ 144) = 10 ^ 8 * radY0 ^ 3 * X ^ 144 := by ring
    have g3 := Nat.mul_le_mul_left (10 ^ 8) sY3
    rw [g4] at sYm
    rw [g5] at g3
    rw [add_mul, add_mul, add_mul, add_mul]
    omega
  have hs8 : 200 * X ^ 8 * radStepCost pd pq pi pm (2000 * X ^ 8) ≤
      200 * (pd.c * (radY0 + 2) ^ pd.k + pq.c * (radY0 + 2) ^ pq.k + pi.c * (radY0 + 2) ^ pi.k +
        radY0 * (pm.c * (radY0 + 2) ^ pm.k) + 10 ^ 8 * radY0 ^ 3) * X ^ D := by
    have := Nat.mul_le_mul_left (200 * X ^ 8) hstep
    have e : X ^ 8 * X ^ (D - 8) = X ^ D := by
      rw [← pow_add]; congr 1; simp only [hD, radD]; omega
    calc 200 * X ^ 8 * radStepCost pd pq pi pm (2000 * X ^ 8) ≤ _ := this
      _ = _ := by rw [← e]; ring
  -- the other terms
  have hc := rad_bS_le pc hX (show T ≤ 1 * X ^ 1 by simp [hXdef])
  have hi := rad_bS_le pi hX (show 2000 * (T + 1) ^ 8 ≤ 2000 * X ^ 8 from le_rfl)
  have ec : X ^ (1 * pc.k) ≤ X ^ D := rad_pow_le hX (by simp only [hD, radD]; omega)
  have ei : X ^ (8 * pi.k) ≤ X ^ D := rad_pow_le hX (by simp only [hD, radD]; omega)
  have e16 : X ^ 16 ≤ X ^ D := rad_pow_le hX (by simp only [hD, radD]; omega)
  have fc := Nat.mul_le_mul_left (pc.c * (1 + 2) ^ pc.k) ec
  have fi := Nat.mul_le_mul_left (pi.c * (2000 + 2) ^ pi.k) ei
  have f16 := Nat.mul_le_mul_left (10 ^ 10) e16
  unfold radCost radK
  rw [add_mul, add_mul, add_mul]
  have hc' : pc.boundSize T ≤ pc.c * 3 ^ pc.k * X ^ (1 * pc.k) := by simpa using hc
  have hi' : pi.boundSize (2000 * X ^ 8) ≤ pi.c * 2002 ^ pi.k * X ^ (8 * pi.k) := by simpa using hi
  norm_num at fc fi
  rw [one_mul] at hc'
  rw [← hXdef]
  clear_value X D
  clear * - hc' hi' fc fi f16 hs8
  omega

theorem radQ_le_ceil_expLogSq (m : ℕ) : radQ m ≤ ⌈expLogSq 3 m⌉₊ := by
  apply Nat.ceil_mono
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have := tm_one_le_expLogSq (a := 3) (by norm_num) 0
    simpa [Real.logb_zero] using this
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have hlog : 0 ≤ Real.logb 2 m := Real.logb_nonneg (by norm_num) hm1
    exact (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)).trans (tm_rpow_le_expLogSq le_rfl)

end GI.Impl
