import Workspace.Impl.TermSupDesc
import Workspace.Impl.TermRad

/-!
# T4: the solvable supplement as a program (Lemma A.19)

Lemma A.19 ("Constructive solvable supplement"): if `R/N` is solvable, a solvable `S ≤ R` with
`S N = R` can be found deterministically in polynomial time. The proof is the Frattini reduction:
"Start with `S = H` and `K = N`. If `K` is not nilpotent, choose a nonnormal Sylow subgroup `P`
of `K`. … Replace `(S, K)` by `(S₁, K₁)`. … There are at most `log₂ |N|` proper descents. At
termination `K` is nilpotent and `S/K ≅ H/N` is solvable; hence `S` is solvable."

The function `supEntry`, on `[gens R, gens N]`:
1. `S = R`, with its generators cut to at most `m²` by one call of **NormalizedIntersection** on
   `R ∩ R` (the output form of the cited tasks);
2. `m² + 1` steps of the descent (`iterFuns`, step `supDescBody`, `supDesc_step`). A step after
   the end of the descent changes nothing. Since `|N| < 2^(m² + 1)` and every proper descent halves
   `|S ∩ N|`, the descent has ended after these steps (`supDesc_done`); the paper's bound
   `log₂ |N|` on the number of proper descents is this count.
3. the generators of the final `S`.

`sup_spec`: the output is `GensOf S` with `S ≤ R`, `S ⊔ N = R`, and `S` solvable
(`sup_solvable`: `S ∩ N` is nilpotent and `R/N` is solvable). `supCost_le`: the cost is at most
`supK (w + 1)^supD`, with `w` the weight of the input. `sup_termSupSpec`: this is
`Iface.TermSupSpec`.

Cited: **NormalizedIntersection**, **SylowAlgo**, **SylowConjugate** (the steps the paper cites
from [LM, Theorem 3.1(viii),(xi)]), and **NormalClosure**, **GroupOrder**, **Membership** for the
test "is `K` nilpotent, and if not, which Sylow subgroup is not normal" (the paper's "If `K` is
not nilpotent, choose a nonnormal Sylow subgroup").
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- **The supplement program** on `[gens R, gens N]`. Environment `[a, gens R, final state]`. -/
def supEntry (it jni : ℕ) : Expr :=
  .letE (.prim jni (mk2 (arg 0) (arg 0)))
  (.letE (.call it (mk3 (.var 0)
      (.arith .add (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0))) (.nat 1))
      (mk2 (.nat 0) (.var 1))))
    (.get (.var 2) (.nat 1)))

/-- Where the supplement program and its modules sit. -/
structure SupAt (P : Program) (f it g mg jni fd mf fx itf gs le jsy jnc jord jm iv mc cj cp jsc : ℕ)
    (hni : NormalizedIntersection) (hsy : SylowAlgo) (hnc : NormalClosure) (hord : GroupOrder)
    (hmem : Membership) (hsc : SylowConjugate) : Prop where
  entry : P.funs[f]? = some (supEntry it jni)
  iter : P.HasAt it (iterFuns it g)
  desc : SupDescAt P g mg jni fd mf fx itf gs le jsy jnc jord jm iv mc cj cp jsc hni hsy hnc hord
    hmem hsc

/-- The cost bound of the supplement program, for an input of weight `T`. -/
def supCost (pni psy pnc pord pm psc : Prim) (n T : ℕ) : ℕ :=
  pni.boundSize (10 ^ 4 * (T + 1) ^ 6) + (n ^ 2 + 1) * supDescCost pni psy pnc pord pm psc n T +
    10 ^ 9 * (T + 1) ^ 9

/-- **T4: the solvable supplement** (Lemma A.19). -/
theorem sup_spec {hni : NormalizedIntersection} {hsy : SylowAlgo} {hnc : NormalClosure}
    {hord : GroupOrder} {hmem : Membership} {hsc : SylowConjugate} {P : Program}
    {f it g mg jni fd mf fx itf gs le jsy jnc jord jm iv mc cj cp jsc : ℕ}
    (hP : SupAt P f it g mg jni fd mf fx itf gs le jsy jnc jord jm iv mc cj cp jsc hni hsy hnc hord
      hmem hsc)
    (σR σN : List (Perm (Fin n))) (hNR : gens σN ≤ gens σR)
    [((gens σN).subgroupOf (gens σR)).Normal]
    (hR : IsSolvable ((gens σR) ⧸ (gens σN).subgroupOf (gens σR))) :
    FunAll P f (.list [encGroup σR, encGroup σN]) (fun u cost =>
      ∃ S : Subgroup (Perm (Fin n)), GensOf S u ∧ S ≤ gens σR ∧ IsSolvable S ∧
        S ⊔ gens σN = gens σR ∧
        cost ≤ supCost (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
          (groupOrderPrim hord) (membershipPrim hmem) (sylowConjugatePrim hsc) n
          (Val.list [encGroup σR, encGroup σN]).wt) := by
  set c := Val.list [encGroup σR, encGroup σN] with hc
  set T := c.wt with hT
  have hRw : (encGroup σR).wt < T := wt_le_wt_list (by simp)
  have hnT : n + 1 ≤ T := by
    have := S_le_wt_encGroup σR
    have : n + 1 ≤ (σR.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hT6 : (n + 1) ^ 6 ≤ (T + 1) ^ 6 := Nat.pow_le_pow_left (by omega) _
  have hT1 : T + 1 ≤ (T + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have hT69 : (T + 1) ^ 6 ≤ (T + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  -- `S = R` with at most `m²` generators
  have d0 := Det.arg' (P := P) (vs := [encGroup σR, encGroup σN]) (rest := []) (j := 0) rfl
  have hRR := wt_list2_le (encGroup σR) (encGroup σR)
  have hb0 := (normalizedIntersectionPrim hni).bound_le
    (show (Val.list [encGroup σR, encGroup σR]).size ≤ 10 ^ 4 * (T + 1) ^ 6 from
      (Val.size_le_wt _).trans (by omega))
  refine FunAll.intro hP.entry (EvalAll.letE (normalizedIntersection_call hni hP.desc.ni
    (Det.mk2 d0 d0) ⟨σR, rfl, rfl⟩ ⟨σR, rfl, rfl⟩ fun x hx y hy =>
      (gens σR).mul_mem ((gens σR).mul_mem hx hy) ((gens σR).inv_mem hx)) fun v1 c1 h1 => ?_)
  obtain ⟨⟨ss, rfl, hl, hss⟩, hc1⟩ := h1
  rw [inf_idem] at hss
  -- the descent
  have h0 : SupDescInv (gens σR) (gens σN) 0 (.list [.nat 0, supSv ss]) :=
    ⟨ss, hl, hss.le, by rw [hss]; exact sup_eq_left.mpr hNR, Or.inr ⟨rfl, by
      rw [pow_zero, one_mul]; exact Subgroup.card_le_of_le inf_le_right⟩⟩
  set k := n ^ 2 + 1 with hk
  set B := supDescCost (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
    (groupOrderPrim hord) (membershipPrim hmem) (sylowConjugatePrim hsc) n T with hB
  have hit := iter_spec hP.iter (c := c) (k := k) (M := 40 * (n + 1) ^ 6) (B := fun _ => B) h0
    (fun i acc _ h => sup_desc_wt h)
    (fun i acc hi h => supDesc_step hP.desc hNR (by omega) h)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hit
  -- the argument of the loop
  set env := [c, supSv ss] with henv
  have dc := Det.var' (P := P) (env := env) (i := 0) (v := c) rfl
  have dn := Det.get' (Det.arg' (P := P) (vs := [encGroup σR, encGroup σN]) (rest := [supSv ss])
    (j := 0) rfl) (Det.nat 0) (v := .nat n) rfl
  have dk := Det.arith' (op := .add) (Det.arith' (op := .mul) dn dn rfl) (Det.nat 1) (z := k)
    (by simp [BinOp.eval, hk, sq])
  have dacc := Det.mk2 (Det.nat (P := P) (env := env) 0)
    (Det.var' (P := P) (env := env) (i := 1) (v := supSv ss) rfl)
  have darg := Det.mk3 dc dk dacc
  refine EvalAll.letE (Ra := fun w cw => SupDescInv (gens σR) (gens σN) k w ∧
      cw ≤ k * B + 10 ^ 8 * (T + 1) ^ 8) (EvalAll.call_funAll darg fun v ca hv => ?_)
    fun v2 c2 h2 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hit.mono fun w cw h => ⟨h.1, ?_⟩
    have := sup_desc_wt h.1
    have hcw := h.2
    have hnT2 : (n + 1) ^ 2 ≤ (T + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
    have hn2e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    have hkT : k + 1 ≤ 2 * (T + 1) ^ 2 := by
      have : 1 ≤ (T + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    have hk6 : k ≤ (T + 1) ^ 6 := by
      have : (T + 1) ^ 2 ≤ (T + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have h0w := sup_desc_wt h0
    have hw3 := wt_list3_le c (.nat k) (.list [.nat 0, supSv ss])
    have hkw := wt_nat_le k
    have hL : loopModK * (k + 1) * ((Val.list [c, .nat k, .list [.nat 0, supSv ss]]).wt + k +
        40 * (n + 1) ^ 6 + 1) ≤ 10 ^ 7 * (T + 1) ^ 8 := by
      calc _ ≤ loopModK * (2 * (T + 1) ^ 2) * (300 * (T + 1) ^ 6) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hkT) (by omega)
        _ = 6 * 10 ^ 5 * (T + 1) ^ 8 := by simp only [loopModK]; ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)
    have hsv : (supSv ss).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hl
    have h2w := wt_list2_le (.nat 0) (supSv ss)
    have h2w' := wt_list2_le c (supSv ss)
    have hnw := wt_nat_le n
    have hnn : n * n ≤ (T + 1) ^ 6 := by nlinarith
    have hmul : BinOp.mul.eval n n = n * n := rfl
    have hcc : (Val.list [encGroup σR, encGroup σN]).wt = c.wt := rfl
    have hT26 : (T + 1) ^ 2 ≤ (T + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have hT68 : (T + 1) ^ 6 ≤ (T + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have := wt_nat_le 0
    have e1 : (Val.list [Val.nat n, Val.list (List.map encPerm (1 :: σR))]).wt = (encGroup σR).wt :=
      rfl
    clear dc dn dk dacc darg hit
    omega
  -- the result
  obtain ⟨ts, htl, hle, hsup, rfl, hnil⟩ := supDesc_done h2.1
  have hc2 := h2.2
  refine (Det.get' (Det.var' (P := P) (env := env ++ [.list [.nat 1, supSv ts]]) (i := 2) rfl)
    (Det.nat 1) (v := supSv ts) rfl).post fun cu hcu => ?_
  beta_reduce
  refine ⟨gens ts, ⟨ts, rfl, htl, rfl⟩, hle, sup_solvable hR hle hnil, hsup, ?_⟩
  have htw : (supSv ts).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq htl
  have h2w := wt_list2_le (.nat 1) (supSv ts)
  have := wt_nat_le 1
  have hk1 : k ≤ n ^ 2 + 1 := le_rfl
  have hkB : k * B = (n ^ 2 + 1) * B := rfl
  have hT8 : (T + 1) ^ 8 ≤ (T + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have hcc : (Val.list [encGroup σR, encGroup σN]).wt = c.wt := rfl
  have hRR' : (Val.list [encGroup σR, encGroup σN]).wt = T := rfl
  unfold supCost
  rw [← hB]
  clear dc dn dk dacc darg hit
  omega

/-! ### The polynomial bound -/

/-- The sum of the exponents of the six primitives. -/
def supKs (pni psy pnc pord pm psc : Prim) : ℕ := pni.k + psy.k + pnc.k + pord.k + pm.k + psc.k

/-- The sum of the constants of the six primitives. -/
def supKp (pni psy pnc pord pm psc : Prim) : ℕ :=
  pni.c * 10002 ^ pni.k + psy.c * 10002 ^ psy.k + pnc.c * 10002 ^ pnc.k +
    pord.c * 10002 ^ pord.k + pm.c * 10002 ^ pm.k + psc.c * 10002 ^ psc.k

/-- The exponent of the polynomial bound. -/
def supD (pni psy pnc pord pm psc : Prim) : ℕ := 21 + 6 * supKs pni psy pnc pord pm psc

/-- The constant of the polynomial bound. -/
def supK (pni psy pnc pord pm psc : Prim) : ℕ := 10 ^ 6 * supKp pni psy pnc pord pm psc + 10 ^ 21

/-- One primitive at a size at most `10⁴ X⁶`. -/
theorem sup_bS_le (p : Prim) {B X e : ℕ} (hX : 1 ≤ X) (hB : B ≤ 10 ^ 4 * X ^ 6) (he : p.k ≤ e) :
    p.boundSize B ≤ p.c * 10002 ^ p.k * X ^ (6 * e) := by
  have h := rad_bS_le p hX hB
  refine h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by omega)))

/-- **The supplement program is polynomial**: `supCost ≤ supK (T + 1)^supD` when `n ≤ T`. -/
theorem supCost_le (pni psy pnc pord pm psc : Prim) {n T : ℕ} (hn : n ≤ T) :
    supCost pni psy pnc pord pm psc n T ≤
      supK pni psy pnc pord pm psc * (T + 1) ^ supD pni psy pnc pord pm psc := by
  set X := T + 1 with hXdef
  have hX : 1 ≤ X := by omega
  have hnX : n + 1 ≤ X := by omega
  set Ks := supKs pni psy pnc pord pm psc with hKs
  set Kp := supKp pni psy pnc pord pm psc with hKp
  set Q := Kp * X ^ (6 * Ks) with hQ
  -- every primitive costs at most `Q`
  have hY : 10 ^ 4 * (n + 1) ^ 6 ≤ 10 ^ 4 * X ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnX _)
  have hY' : 10 ^ 4 * (T + 1) ^ 6 ≤ 10 ^ 4 * X ^ 6 := le_rfl
  have qni := sup_bS_le pni hX hY' (e := Ks) (by simp only [hKs, supKs]; omega)
  have qni' : pni.boundSize (10 ^ 4 * X ^ 6) ≤ pni.c * 10002 ^ pni.k * X ^ (6 * Ks) := qni
  have qsy := sup_bS_le psy hX hY (e := Ks) (by simp only [hKs, supKs]; omega)
  have qnc := sup_bS_le pnc hX hY (e := Ks) (by simp only [hKs, supKs]; omega)
  have qord := sup_bS_le pord hX hY (e := Ks) (by simp only [hKs, supKs]; omega)
  have qm := sup_bS_le pm hX hY (e := Ks) (by simp only [hKs, supKs]; omega)
  have qsc := sup_bS_le psc hX hY (e := Ks) (by simp only [hKs, supKs]; omega)
  have hQs : Q = pni.c * 10002 ^ pni.k * X ^ (6 * Ks) + psy.c * 10002 ^ psy.k * X ^ (6 * Ks) +
      pnc.c * 10002 ^ pnc.k * X ^ (6 * Ks) + pord.c * 10002 ^ pord.k * X ^ (6 * Ks) +
      pm.c * 10002 ^ pm.k * X ^ (6 * Ks) + psc.c * 10002 ^ psc.k * X ^ (6 * Ks) := by
    simp only [hQ, hKp, supKp]; ring
  -- powers of `X`
  have p6 : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ hX
  have hXQ : ∀ a b, a ≤ b → X ^ a * Q ≤ X ^ b * Q := fun a b h =>
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hX h)
  have hXX : ∀ a b, a ≤ b → X ^ a ≤ X ^ b := fun a b h => Nat.pow_le_pow_right hX h
  -- the search step
  have hS : supSearchCost psy pnc pord pm n ≤ 4 * 10 ^ 4 * (X ^ 6 * Q) + 10 ^ 18 * X ^ 18 := by
    unfold supSearchCost
    have h1 : 10 ^ 4 * (n + 1) ^ 6 * pm.boundSize (10 ^ 4 * (n + 1) ^ 6) ≤ 10 ^ 4 * (X ^ 6 * Q) := by
      calc _ ≤ 10 ^ 4 * X ^ 6 * Q := Nat.mul_le_mul hY (by omega)
        _ = _ := by ring
    have h2 : 10 ^ 6 * (10 ^ 4 * (n + 1) ^ 6) ^ 3 ≤ 10 ^ 18 * X ^ 18 := by
      calc _ ≤ 10 ^ 6 * (10 ^ 4 * X ^ 6) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hY 3)
        _ = _ := by ring
    have h3 : Q ≤ X ^ 6 * Q := Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- the search
  have hF : supFindCost psy pnc pord pm n ≤ 8 * 10 ^ 4 * (X ^ 7 * Q) + 10 ^ 19 * X ^ 19 := by
    unfold supFindCost
    have h1 : (n + 2) * supSearchCost psy pnc pord pm n ≤
        2 * X * (4 * 10 ^ 4 * (X ^ 6 * Q) + 10 ^ 18 * X ^ 18) :=
      Nat.mul_le_mul (by omega) hS
    have e1 : 2 * X * (4 * 10 ^ 4 * (X ^ 6 * Q) + 10 ^ 18 * X ^ 18) =
        8 * 10 ^ 4 * (X ^ 7 * Q) + 2 * 10 ^ 18 * X ^ 19 := by ring
    have h2 : 10 ^ 9 * (n + 1) ^ 7 ≤ 10 ^ 9 * X ^ 19 :=
      Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hnX _).trans (hXX 7 19 (by omega)))
    omega
  -- one correction
  have hFx : (n + 1) ^ 2 * supFixCost psc n ≤ X ^ 2 * Q + 10 ^ 9 * X ^ 10 := by
    unfold supFixCost
    have h1 : (n + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hnX _
    calc _ ≤ X ^ 2 * (Q + 10 ^ 9 * X ^ 8) := Nat.mul_le_mul h1 (by
          have := Nat.mul_le_mul_left (10 ^ 9) (Nat.pow_le_pow_left hnX 8)
          omega)
      _ = _ := by ring
  -- one descent
  have hD : supDescCost pni psy pnc pord pm psc n T ≤ 10 ^ 5 * (X ^ 7 * Q) + 10 ^ 20 * X ^ 19 := by
    unfold supDescCost
    have a1 : Q ≤ X ^ 7 * Q := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hX)
    have a2 := hXQ 2 7 (by omega)
    have a3 := hXX 10 19 (by omega)
    have a4 := hXX 9 19 (by omega)
    have a5 : (T + 1) ^ 9 = X ^ 9 := rfl
    omega
  -- the whole program
  unfold supCost
  rw [← hXdef]
  have h1 : (n ^ 2 + 1) * supDescCost pni psy pnc pord pm psc n T ≤
      X ^ 2 * (10 ^ 5 * (X ^ 7 * Q) + 10 ^ 20 * X ^ 19) :=
    Nat.mul_le_mul (by
      have : (n + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hnX _
      have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega) hD
  have e1 : X ^ 2 * (10 ^ 5 * (X ^ 7 * Q) + 10 ^ 20 * X ^ 19) =
      10 ^ 5 * (X ^ 9 * Q) + 10 ^ 20 * X ^ 21 := by ring
  have a1 : Q ≤ X ^ 9 * Q := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hX)
  have a2 := hXX 9 21 (by omega)
  have hfin : X ^ 9 * Q = Kp * X ^ (9 + 6 * Ks) := by rw [hQ, pow_add]; ring
  have hD' : supD pni psy pnc pord pm psc = 21 + 6 * Ks := rfl
  have hK' : supK pni psy pnc pord pm psc = 10 ^ 6 * Kp + 10 ^ 21 := rfl
  have b1 : Kp * X ^ (9 + 6 * Ks) ≤ Kp * X ^ (21 + 6 * Ks) :=
    Nat.mul_le_mul_left _ (hXX _ _ (by omega))
  have b2 : X ^ 21 ≤ X ^ (21 + 6 * Ks) := hXX _ _ (by omega)
  rw [hD', hK']
  have b3 : (10 ^ 6 * Kp + 10 ^ 21) * X ^ (21 + 6 * Ks) =
      10 ^ 6 * (Kp * X ^ (21 + 6 * Ks)) + 10 ^ 21 * X ^ (21 + 6 * Ks) := by ring
  rw [b3]
  have b5 : Q ≤ Kp * X ^ (21 + 6 * Ks) := by
    rw [hQ]; exact Nat.mul_le_mul_left _ (hXX _ _ (by omega))
  have b6 : X ^ 9 ≤ X ^ (21 + 6 * Ks) := hXX _ _ (by omega)
  omega

/-- **T4 as the hypothesis of the terminal case** (`Iface.TermSupSpec`, `TermHyp.lean`): the
supplement program meets it with the constants `supK`, `supD` of the cited primitives. Cited:
**NormalizedIntersection**, **SylowAlgo**, **NormalClosure**, **GroupOrder**, **Membership**,
**SylowConjugate**. -/
theorem sup_termSupSpec {hni : NormalizedIntersection} {hsy : SylowAlgo} {hnc : NormalClosure}
    {hord : GroupOrder} {hmem : Membership} {hsc : SylowConjugate} {P : Program}
    {f it g mg jni fd mf fx itf gs le jsy jnc jord jm iv mc cj cp jsc : ℕ}
    (hP : SupAt P f it g mg jni fd mf fx itf gs le jsy jnc jord jm iv mc cj cp jsc hni hsy hnc hord
      hmem hsc) :
    Iface.TermSupSpec P
      (supK (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
        (groupOrderPrim hord) (membershipPrim hmem) (sylowConjugatePrim hsc))
      (supD (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
        (groupOrderPrim hord) (membershipPrim hmem) (sylowConjugatePrim hsc)) f := by
  intro m σR σN hle _ hR
  have hnT : m ≤ (Val.list [encGroup σR, encGroup σN]).wt := by
    have h1 : (encGroup σR).wt < (Val.list [encGroup σR, encGroup σN]).wt := wt_le_wt_list (by simp)
    have := S_le_wt_encGroup σR
    have : m + 1 ≤ (σR.length + 2) * (m + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  exact (sup_spec hP σR σN hle hR).mono fun u c h => by
    obtain ⟨S, h1, h2, h3, h4, h5⟩ := h
    exact ⟨S, h1, h2, h3, h4, h5.trans (supCost_le _ _ _ _ _ _ hnT)⟩

end GI.Impl
