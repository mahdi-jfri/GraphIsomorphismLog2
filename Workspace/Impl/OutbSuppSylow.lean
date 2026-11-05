module

public import Workspace.OutbSuppMath
public import Workspace.Lang.Prims.Reduce
public import Workspace.Lang.Prims.Ops

@[expose] public section

/-!
# Brute-force Sylow construction in `M / R`

Given group encodings `encGroup rs` (`R = gens rs`) and `encGroup ms` (`M = gens ms`) with
`rs.length ≤ n²`, `ms.length ≤ n²`, `R ≤ M ≤ E_H`, `(R.subgroupOf M).Normal`, a prime `p`, and a
list `reps` of coset representatives of `R` in `E_H` (`∀ x ∈ E_H, TmRpCov R reps x`), the function
`outbSylBody` computes a group encoding `encGroup ps` with `ps.length ≤ 2 * n²` and
`OutbSylowMod p R M (gens ps)`:

1. `outbPPartF` computes `B = p ^ ((|M| / |R|).factorization p) * |R|` from `[|M|, p, |R|]` by
   multiplying `|R|` by `p` as long as `p` divides `|M| / B` (`outbPPart_spec`).
2. `outbSylStepE` implements `outbSylStep M B ps e` using two **Membership** calls (`e ∈ M` and
   `e ∈ gens ps`) and one **GroupOrder** call (`|⟨ps ++ [e]⟩|`), returning
   `encGroup (outbSylStep M B ps e)` deterministically (`outbSylStep_spec`).
3. `outbSylPassE` folds `outbSylStepE` over `reps`, advancing `OutbSylInv` from `a` to
   `min (a + 1) v` (`outbSylPass_spec`).
4. `outbSylBody` iterates `outbSylPassE` `n² + 1` times starting from `encGroup rs`, producing
   `encGroup ps` with `ps.length ≤ 2 * n²` and `OutbSylowMod p R M (gens ps)` (`outbSyl_spec`).

Only **Membership** and **GroupOrder** are used.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### Weight and size helpers -/

theorem wt_encGroup_two_sq {kept : List (Perm (Fin n))} (hl : kept.length ≤ 2 * n ^ 2) :
    (encGroup kept).wt ≤ 640 * (n + 1) ^ 6 := by
  have h1 := wt_encGroup_le kept
  have h2 : (kept.length + 2) * (n + 1) ≤ 4 * (n + 1) ^ 3 := by
    have e : (n + 1) ^ 3 = (n + 1) ^ 2 * (n + 1) := by ring
    have e2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    rw [e]
    exact le_trans (Nat.mul_le_mul_right _ (show kept.length + 2 ≤ 4 * (n + 1) ^ 2 by omega))
      (by rw [Nat.mul_assoc])
  have h3 : ((kept.length + 2) * (n + 1)) ^ 2 ≤ (4 * (n + 1) ^ 3) ^ 2 := Nat.pow_le_pow_left h2 2
  have e : (4 * (n + 1) ^ 3) ^ 2 = 16 * (n + 1) ^ 6 := by ring
  omega

theorem outb_wt_nat_le {M : Subgroup (Perm (Fin n))} {r : ℕ} (h : r ≤ Nat.card M) :
    (Val.nat r).wt ≤ n ^ 2 + 3 := by
  have h1 := wt_card_le M
  rw [wt_nat] at h1 ⊢
  have := GI.Machine.len_mono h
  omega

theorem outb_mk_det {P : Program} {mg : ℕ} (hmg : P.HasAt mg (mkGroupFuns mg))
    {env : List Val} {nE lE : Expr} {cn cl : ℕ} {L : Val} {G : Subgroup (Perm (Fin n))}
    (dn : Det P env nE (.nat n) cn) (dl : Det P env lE L cl) (hL : GensVal n L G) :
    ∃ hs : List (Perm (Fin n)), hs.length ≤ n ^ 2 ∧ gens hs = G ∧
      Det P env (.call mg (mk2 nE lE)) (encGroup hs)
        (cn + cl + 2 * (Val.list [.nat n, L]).wt + 8 * mkGroupK * (n + 1) ^ 9 +
          320 * (n + 1) ^ 6 + 8) ∧
      (encGroup hs).wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨hs, rfl, hl, hf, ⟨_, he, hg⟩, hw⟩ := mkGroup_gensVal hmg hL
  obtain rfl := encGroup_injective he
  refine ⟨hs, hl, hg, (Det.call (Det.mk2 dn dl) hf).mono (by omega), hw⟩

theorem outb_bS_le (p : Prim) {B X e : ℕ} (hX : 1 ≤ X) (hB : B ≤ 10 ^ 4 * X ^ 6) (he : p.k ≤ e) :
    p.boundSize B ≤ p.c * 10002 ^ p.k * X ^ (6 * e) := by
  unfold Prim.boundSize
  have h1 : B + 2 ≤ 10002 * X ^ 6 := by
    have : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ hX
    omega
  calc p.c * (B + 2) ^ p.k ≤ p.c * (10002 * X ^ 6) ^ p.k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = p.c * 10002 ^ p.k * X ^ (6 * p.k) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ p.c * 10002 ^ p.k * X ^ (6 * e) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by omega))

theorem outb_wt_reps_le (reps : List (Perm (Fin n))) :
    (Val.list (reps.map encPerm)).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 := by
  have h1 := wt_list_encPerms_le reps
  have e : 13 * ((reps.length + 1) * (n + 1)) ^ 2 = 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 := by
    ring
  omega

theorem Det.arith_wt {P : Program} {env : List Val} {op : BinOp} {a b : Expr} {x y z ca cb : ℕ}
    (ha : Det P env a (.nat x) ca) (hb : Det P env b (.nat y) cb) (hz : op.eval x y = z) :
    Det P env (.arith op a b) (.nat z) (ca + cb + (Val.nat z).wt + 1) := by
  subst hz
  exact Det.arith ha hb

/-! ### The prime-part helper `outbPPartF` -/

/-- On `[|M|, p, B]`: multiply `B` by `p` while `p ∣ (|M| / B)`. -/
def outbPPartF (f : ℕ) : Expr :=
  .ite (.arith .eq (.arith .mod (.arith .div (arg 0) (arg 2)) (arg 1)) (.nat 0))
    (.call f (mk3 (arg 0) (arg 1) (.arith .mul (arg 1) (arg 2))))
    (arg 2)

theorem outbPPart_loop {P : Program} {f : ℕ} (hf : P.funs[f]? = some (outbPPartF f))
    {R M : Subgroup (Perm (Fin n))} (hRM : R ≤ M) {p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    ∀ k a, a ≤ (Nat.card M / Nat.card R).factorization p →
      (Nat.card M / Nat.card R).factorization p - a = k →
      FunDet P f (.list [.nat (Nat.card M), .nat p, .nat (p ^ a * Nat.card R)])
        (.nat (p ^ (Nat.card M / Nat.card R).factorization p * Nat.card R))
        ((k + 1) * (1000 * (n + 1) ^ 2))
  | 0, a, ha, hk => by
    set v := (Nat.card M / Nat.card R).factorization p with hv_def
    set B := p ^ a * Nat.card R
    have hav : a = v := by omega
    obtain ⟨hBM, hdvd_iff⟩ := outb_ppart_div_Step hRM hp ha
    have hndvd : ¬ p ∣ (Nat.card M / B) := fun hd => by
      have := hdvd_iff.mp hd; omega
    have hmod_ne : (Nat.card M / B) % p ≠ 0 := by
      intro h0; exact hndvd (Nat.dvd_of_mod_eq_zero h0)
    set vs : List Val := [.nat (Nat.card M), .nat p, .nat B]
    have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) (v := .nat (Nat.card M)) rfl
    have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) (v := .nat p) rfl
    have d2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) (v := .nat B) rfl
    have ddiv := Det.arith_wt (op := .div) d0 d2 (z := Nat.card M / B) rfl
    have dmod := Det.arith_wt (op := .mod) ddiv d1 (z := (Nat.card M / B) % p) rfl
    have deq := Det.arith' (op := .eq) dmod (Det.nat 0) (z := 0) (by
      simp [BinOp.eval, hmod_ne])
    have hBw : (Val.nat B).wt ≤ n ^ 2 + 3 := outb_wt_nat_le hBM
    have hBvw : (Val.nat (p ^ v * Nat.card R)).wt ≤ n ^ 2 + 3 :=
      outb_wt_nat_le (outb_ppart_div_Step hRM hp le_rfl).1
    have hMw : (Val.nat (Nat.card M)).wt ≤ n ^ 2 + 3 := wt_card_le M
    have hdivw : (Val.nat (Nat.card M / B)).wt ≤ n ^ 2 + 3 :=
      outb_wt_nat_le (Nat.div_le_self _ _)
    have hmodw : (Val.nat ((Nat.card M / B) % p)).wt ≤ n ^ 2 + 3 :=
      outb_wt_nat_le ((Nat.mod_le _ _).trans (Nat.div_le_self _ _))
    have hpw := wt_nat_le p
    have h0w := wt_nat_le 0
    have hw3 : (Val.list vs).wt ≤
        2 * ((Val.nat (Nat.card M)).wt + (Val.nat p).wt + (Val.nat B).wt) + 7 :=
      wt_list3_le (.nat (Nat.card M)) (.nat p) (.nat B)
    have hn2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    have d2' : Det P [.list vs] (arg 2) (.nat (p ^ v * Nat.card R))
        (2 * (Val.list vs).wt + 2 + 5) := by
      dsimp [B] at d2; rw [hav] at d2; exact d2
    refine FunDet.intro hf ((Det.ite_zero deq d2').mono ?_)
    omega
  | k + 1, a, ha, hk => by
    set v := (Nat.card M / Nat.card R).factorization p with hv_def
    set B := p ^ a * Nat.card R
    have hlt : a < v := by omega
    have ha1 : a + 1 ≤ v := by omega
    have hk1 : v - (a + 1) = k := by omega
    obtain ⟨hBM, hdvd_iff⟩ := outb_ppart_div_Step hRM hp ha
    obtain ⟨hB1M, _⟩ := outb_ppart_div_Step hRM hp ha1
    have hdvd : p ∣ (Nat.card M / B) := hdvd_iff.mpr hlt
    have hmod_eq : (Nat.card M / B) % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
    set vs : List Val := [.nat (Nat.card M), .nat p, .nat B]
    have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) (v := .nat (Nat.card M)) rfl
    have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) (v := .nat p) rfl
    have d2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) (v := .nat B) rfl
    have ddiv := Det.arith_wt (op := .div) d0 d2 (z := Nat.card M / B) rfl
    have dmod := Det.arith' (op := .mod) ddiv d1 (z := 0) (by simp [BinOp.eval, hmod_eq])
    have deq := Det.arith' (op := .eq) dmod (Det.nat 0) (z := 1) rfl
    have dmul := Det.arith_wt (op := .mul) d1 d2 (z := p ^ (a + 1) * Nat.card R) (by
      dsimp [BinOp.eval, B]; rw [pow_succ']; ring)
    have darg := Det.mk3 d0 d1 dmul
    have ih := outbPPart_loop hf hRM hp hpn k (a + 1) ha1 hk1
    rw [← hv_def] at ih
    have dcall := Det.call darg ih
    have hBw : (Val.nat B).wt ≤ n ^ 2 + 3 := outb_wt_nat_le hBM
    have hB1w : (Val.nat (p ^ (a + 1) * Nat.card R)).wt ≤ n ^ 2 + 3 := outb_wt_nat_le hB1M
    have hBvw : (Val.nat (p ^ v * Nat.card R)).wt ≤ n ^ 2 + 3 :=
      outb_wt_nat_le (outb_ppart_div_Step hRM hp le_rfl).1
    have hMw : (Val.nat (Nat.card M)).wt ≤ n ^ 2 + 3 := wt_card_le M
    have hdivw : (Val.nat (Nat.card M / B)).wt ≤ n ^ 2 + 3 :=
      outb_wt_nat_le (Nat.div_le_self _ _)
    have hpw := wt_nat_le p
    have h0w := wt_nat_le 0
    have h1w := wt_nat_le 1
    have hw3_vs : (Val.list vs).wt ≤
        2 * ((Val.nat (Nat.card M)).wt + (Val.nat p).wt + (Val.nat B).wt) + 7 :=
      wt_list3_le (.nat (Nat.card M)) (.nat p) (.nat B)
    have hw3 := wt_list3_le (.nat (Nat.card M)) (.nat p) (.nat (p ^ (a + 1) * Nat.card R))
    have hn2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    have hstep : (k + 1 + 1) * (1000 * (n + 1) ^ 2) =
        (k + 1) * (1000 * (n + 1) ^ 2) + 1000 * (n + 1) ^ 2 := by ring
    refine FunDet.intro hf ((Det.ite_pos deq one_ne_zero dcall).mono ?_)
    omega

/-- **Specification of `outbPPartF`**: starting from `B = |R|`, returns
`p ^ ((|M| / |R|).factorization p) * |R|` deterministically in cost `≤ 2000 (n + 1)⁴`. -/
theorem outbPPart_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some (outbPPartF f))
    {R M : Subgroup (Perm (Fin n))} (hRM : R ≤ M) {p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    FunDet P f (.list [.nat (Nat.card M), .nat p, .nat (Nat.card R)])
      (.nat (p ^ (Nat.card M / Nat.card R).factorization p * Nat.card R))
      (2000 * (n + 1) ^ 4) := by
  set v := (Nat.card M / Nat.card R).factorization p
  have hv : v ≤ n ^ 2 := outb_factorization_le_sq p
  have h0 : p ^ 0 * Nat.card R = Nat.card R := by simp
  have hloop := outbPPart_loop hf hRM hp hpn v 0 (Nat.zero_le v) (by omega)
  rw [h0] at hloop
  refine hloop.mono ?_
  have hv1 : v + 1 ≤ 2 * (n + 1) ^ 2 := by
    have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  calc (v + 1) * (1000 * (n + 1) ^ 2) ≤ 2 * (n + 1) ^ 2 * (1000 * (n + 1) ^ 2) :=
        Nat.mul_le_mul_right _ hv1
    _ = 2000 * (n + 1) ^ 4 := by ring

/-! ### One step of the Sylow pass `outbSylStepE` -/

/-- Expression for `encGroup (ps ++ [e])` on `[c, encGroup ps, encPerm e]`. -/
def outbSylAppE : Expr :=
  mk2 (.get (arg 1) (.nat 0)) (.snoc (.get (arg 1) (.nat 1)) (arg 2))

/-- Condition for `outbSylStep`: `e ∈ M ∧ e ∉ gens ps ∧ |⟨ps ++ [e]⟩| ∣ B`. -/
def outbSylCondE (jm jo : ℕ) : Expr :=
  .arith .mul
    (.prim jm (mk2 (.get (arg 0) (.nat 0)) (arg 2)))
    (.arith .mul
      (.arith .eq (.prim jm (mk2 (arg 1) (arg 2))) (.nat 0))
      (.arith .eq (.arith .mod (.get (arg 0) (.nat 1)) (.prim jo outbSylAppE)) (.nat 0)))

/-- **One step of the brute-force Sylow pass**, on `[[encGroup ms, .nat B], encGroup ps, encPerm e]`. -/
def outbSylStepE (jm jo : ℕ) : Expr :=
  .ite (outbSylCondE jm jo) outbSylAppE (arg 1)

/-- Cost bound of one step of the Sylow pass. -/
def outbSylStepCost (pm po : Prim) (n : ℕ) : ℕ :=
  2 * pm.boundSize (10 ^ 4 * (n + 1) ^ 6) + po.boundSize (10 ^ 4 * (n + 1) ^ 6) +
    10 ^ 5 * (n + 1) ^ 6

open Classical in
/-- **Specification of `outbSylStepE`**: deterministically computes
`encGroup (outbSylStep (gens ms) B ps e)`. -/
theorem outbSylStep_spec (hm : Membership) (ho : GroupOrder) {P : Program} {st jm jo : ℕ}
    (hst : P.funs[st]? = some (outbSylStepE jm jo))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjo : P.prims[jo]? = some (groupOrderPrim ho))
    {ms ps : List (Perm (Fin n))} (hml : ms.length ≤ n ^ 2) (hpl : ps.length ≤ 2 * n ^ 2)
    {B : ℕ} (hBM : B ≤ Nat.card (gens ms)) (e : Perm (Fin n)) :
    FunDet P st (.list [.list [encGroup ms, .nat B], encGroup ps, encPerm e])
      (encGroup (outbSylStep (gens ms) B ps e))
      (outbSylStepCost (membershipPrim hm) (groupOrderPrim ho) n) := by
  set c := Val.list [encGroup ms, .nat B]
  set A : List Val := [c, encGroup ps, encPerm e]
  set Y := 10 ^ 4 * (n + 1) ^ 6
  have dc := Det.arg' (P := P) (vs := A) (rest := []) (j := 0) (v := c) rfl
  have d1 := Det.arg' (P := P) (vs := A) (rest := []) (j := 1) (v := encGroup ps) rfl
  have d2 := Det.arg' (P := P) (vs := A) (rest := []) (j := 2) (v := encPerm e) rfl
  have dM := Det.get' dc (Det.nat 0) (v := encGroup ms) rfl
  have dB := Det.get' dc (Det.nat 1) (v := .nat B) rfl
  -- `outbSylAppE` evaluates to `encGroup (ps ++ [e])`
  have dn := Det.get' d1 (Det.nat 0)
    (show [Val.nat n, .list ((1 :: ps).map encPerm)][0]? = some (.nat n) from rfl)
  have dL := Det.get' d1 (Det.nat 1)
    (show [Val.nat n, .list ((1 :: ps).map encPerm)][1]? =
      some (.list ((1 :: ps).map encPerm)) from rfl)
  have dApp := Det.mk2 dn (Det.snoc dL d2)
  rw [← encGroup_snoc] at dApp
  -- primitive calls
  have dm1 := Det.prim (P := P) (env := [.list A]) hjm (Det.mk2 dM d2)
    (membershipPrim_spec hm ⟨ms, rfl, rfl⟩ e).1
    (w := .nat (if e ∈ gens ms then 1 else 0)) (fun w hw => by
      rcases (membershipPrim_spec hm ⟨ms, rfl, rfl⟩ e).2 w hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp [h])
  have dm2 := Det.prim (P := P) (env := [.list A]) hjm (Det.mk2 d1 d2)
    (membershipPrim_spec hm ⟨ps, rfl, rfl⟩ e).1
    (w := .nat (if e ∈ gens ps then 1 else 0)) (fun w hw => by
      rcases (membershipPrim_spec hm ⟨ps, rfl, rfl⟩ e).2 w hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp [h])
  have dord := groupOrder_call ho hjo dApp
    (⟨ps ++ [e], rfl, rfl⟩ : GroupVal n (encGroup (ps ++ [e])) (gens (ps ++ [e])))
  -- condition arithmetic
  set b1 : ℕ := if e ∈ gens ms then 1 else 0
  set b2 : ℕ := if (if e ∈ gens ps then 1 else 0) = 0 then 1 else 0
  set b3 : ℕ := if B % Nat.card (gens (ps ++ [e])) = 0 then 1 else 0
  have deq2 := Det.arith' (op := .eq) dm2 (Det.nat 0) (z := b2) rfl
  have dmod3 := Det.arith_wt (op := .mod) dB dord (z := B % Nat.card (gens (ps ++ [e]))) rfl
  have deq3 := Det.arith' (op := .eq) dmod3 (Det.nat 0) (z := b3) rfl
  have dmul23 := Det.arith' (op := .mul) deq2 deq3 (z := b2 * b3) rfl
  have dcond := Det.arith' (op := .mul) dm1 dmul23 (z := b1 * (b2 * b3)) rfl
  have hcond_iff : b1 * (b2 * b3) ≠ 0 ↔
      (e ∈ gens ms ∧ e ∉ gens ps ∧ Nat.card (gens (ps ++ [e])) ∣ B) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    dsimp only [b1, b2, b3]
    by_cases h1 : e ∈ gens ms <;> by_cases h2 : e ∈ gens ps <;>
      by_cases h3 : B % Nat.card (gens (ps ++ [e])) = 0 <;>
      simp only [h1, h2, h3, ↓reduceIte, mul_one, mul_zero, ne_eq,
        one_ne_zero, not_false_eq_true, not_true_eq_false, and_self, and_false, false_and]
  have dite := Det.ite dcond (v := encGroup (outbSylStep (gens ms) B ps e))
    (fun hx => by
      have hc := hcond_iff.mp hx
      unfold outbSylStep; simp only [hc]; exact dApp)
    (fun hx => by
      have hc : ¬ (e ∈ gens ms ∧ e ∉ gens ps ∧ Nat.card (gens (ps ++ [e])) ∣ B) :=
        fun h => (hcond_iff.mpr h) hx
      unfold outbSylStep; simp only [hc, ↓reduceIte]; exact d1)
  refine FunDet.intro hst (dite.mono ?_)
  clear dite dcond dmul23 deq3 dmod3 deq2 dord dm2 dm1 dApp dL dn dB dM d2 d1 dc
  -- weights and bounds
  have hMw := wt_encGroup_sq hml
  have hPw := wt_encGroup_two_sq hpl
  have hpe_len : (ps ++ [e]).length ≤ 2 * n ^ 2 + 1 := by simp [hpl]
  have hPew : (encGroup (ps ++ [e])).wt ≤ 1000 * (n + 1) ^ 6 := by
    have h1 := wt_encGroup_le (ps ++ [e])
    have h2 : ((ps ++ [e]).length + 2) * (n + 1) ≤ 5 * (n + 1) ^ 3 := by
      have e1 : (n + 1) ^ 3 = (n + 1) ^ 2 * (n + 1) := by ring
      have e2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      rw [e1]
      exact le_trans (Nat.mul_le_mul_right _
        (show (ps ++ [e]).length + 2 ≤ 5 * (n + 1) ^ 2 by omega)) (by rw [Nat.mul_assoc])
    have h3 := Nat.pow_le_pow_left h2 2
    have e3 : (5 * (n + 1) ^ 3) ^ 2 = 25 * (n + 1) ^ 6 := by ring
    omega
  have hew := wt_encPerm_le e
  have hBw := outb_wt_nat_le hBM
  have hcw : c.wt ≤ 2 * ((encGroup ms).wt + (Val.nat B).wt) + 6 :=
    wt_list2_le (encGroup ms) (.nat B)
  have hAw : (Val.list A).wt ≤ 2 * (c.wt + (encGroup ps).wt + (encPerm e).wt) + 7 :=
    wt_list3_le c (encGroup ps) (encPerm e)
  have hn2 : n ^ 2 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hn_le : n ≤ (n + 1) ^ 6 := (Nat.le_succ n).trans (Nat.le_self_pow (by norm_num) _)
  have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hnw := wt_nat_le n
  have hL_lt : (Val.list ((1 :: ps).map encPerm)).wt < (encGroup ps).wt :=
    wt_le_wt_list (by simp)
  have hsnocw := wt_list_snoc_le ((1 :: ps).map encPerm) (encPerm e)
  have heS : (Val.list [.nat n, .list ((1 :: ps).map encPerm ++ [encPerm e])]).wt =
      (encGroup (ps ++ [e])).wt := by rw [encGroup_snoc]
  have hm1w := wt_list2_le (encGroup ms) (encPerm e)
  have hm2w := wt_list2_le (encGroup ps) (encPerm e)
  have hbm1 := (membershipPrim hm).bound_le
    (show (Val.list [encGroup ms, encPerm e]).size ≤ Y from (Val.size_le_wt _).trans (by omega))
  have hbm2 := (membershipPrim hm).bound_le
    (show (Val.list [encGroup ps, encPerm e]).size ≤ Y from (Val.size_le_wt _).trans (by omega))
  have hbo := (groupOrderPrim ho).bound_le
    (show (encGroup (ps ++ [e])).size ≤ Y from (Val.size_le_wt _).trans (by omega))
  have hcardw := wt_card_le (gens (ps ++ [e]))
  have hmodw : (Val.nat (B % Nat.card (gens (ps ++ [e])))).wt ≤ n ^ 2 + 3 :=
    outb_wt_nat_le ((Nat.mod_le _ _).trans hBM)
  have hm2_res_w : (Val.nat (if e ∈ gens ps then 1 else 0)).wt ≤ 3 := by
    split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
  have hb2_le : b2 ≤ 1 := by dsimp [b2]; split_ifs <;> omega
  have hb3_le : b3 ≤ 1 := by dsimp [b3]; split_ifs <;> omega
  have hb23_le : b2 * b3 ≤ 1 := by dsimp [b2, b3]; split_ifs <;> omega
  have hb123_le : b1 * (b2 * b3) ≤ 1 := by dsimp [b1, b2, b3]; split_ifs <;> omega
  have hb1w : (Val.nat b1).wt ≤ 3 := by dsimp [b1]; split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
  have hb2w : (Val.nat b2).wt ≤ 3 := by dsimp [b2]; split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
  have hb3w : (Val.nat b3).wt ≤ 3 := by dsimp [b3]; split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
  have hb23w : (Val.nat (b2 * b3)).wt ≤ 3 := by
    dsimp [b2, b3]; split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
  have hb123w : (Val.nat (b1 * (b2 * b3))).wt ≤ 3 := by
    dsimp [b1, b2, b3]; split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
  have h0w := wt_nat_le 0
  have h1w := wt_nat_le 1
  have hstepw : (encGroup (outbSylStep (gens ms) B ps e)).wt ≤ 1000 * (n + 1) ^ 6 := by
    unfold outbSylStep; split_ifs <;> omega
  unfold outbSylStepCost
  change _ ≤ 2 * (membershipPrim hm).boundSize Y + (groupOrderPrim ho).boundSize Y +
    10 ^ 5 * (n + 1) ^ 6
  clear_value b1 b2 b3 c A Y
  omega

/-! ### One full pass `outbSylPassE` and the full Sylow construction `outbSylBody` -/

/-- One pass of `outbSylStepE` over `reps`, called by `iterFuns` on
`[[[encGroup ms, .nat B], .list (reps.map encPerm)], .nat i, encGroup ps]`. -/
def outbSylPassE (fd : ℕ) : Expr :=
  .call fd (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 2))

/-- Cost bound of one pass over `reps` of length `m`. -/
def outbSylPassCost (pm po : Prim) (n m : ℕ) : ℕ :=
  (m + 1) * outbSylStepCost pm po n + 10 ^ 7 * (m + 1) ^ 3 * (n + 1) ^ 6

open Classical in
/-- **One pass over `reps`** advances `OutbSylInv` from `a` to `min (a + 1) v`. -/
theorem outbSylPass_spec (hm : Membership) (ho : GroupOrder) {P : Program} {ps_fn fd st jm jo : ℕ}
    (hps : P.funs[ps_fn]? = some (outbSylPassE fd))
    (hfd : P.HasAt fd (foldlFuns fd st))
    (hst : P.funs[st]? = some (outbSylStepE jm jo))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjo : P.prims[jo]? = some (groupOrderPrim ho))
    {R E_H : Subgroup (Perm (Fin n))} {ms reps : List (Perm (Fin n))}
    [(R.subgroupOf (gens ms)).Normal] (hRM : R ≤ gens ms) (hME : gens ms ≤ E_H)
    (hml : ms.length ≤ n ^ 2) (hcov : ∀ x ∈ E_H, TmRpCov R reps x)
    {p i a : ℕ} (_hi : i ≤ n ^ 2) {acc : Val}
    (hinv : ∃ ps : List (Perm (Fin n)), acc = encGroup ps ∧
      OutbSylInv p R (gens ms) ((Nat.card (gens ms) / Nat.card R).factorization p) a ps)
    (hp : p.Prime) :
    let v := (Nat.card (gens ms) / Nat.card R).factorization p
    let B := p ^ v * Nat.card R
    let c_fold := Val.list [encGroup ms, .nat B]
    let c_iter := Val.list [c_fold, .list (reps.map encPerm)]
    FunAll P ps_fn (.list [c_iter, .nat i, acc]) (fun w cost =>
      (∃ ps' : List (Perm (Fin n)), w = encGroup ps' ∧
        OutbSylInv p R (gens ms) v (min (a + 1) v) ps') ∧
      cost ≤ outbSylPassCost (membershipPrim hm) (groupOrderPrim ho) n reps.length) := by
  intro v B c_fold c_iter
  obtain ⟨ps0, rfl, hinv0⟩ := hinv
  have hv_sq : v ≤ n ^ 2 := outb_factorization_le_sq p
  have hBM : B ≤ Nat.card (gens ms) := (outb_ppart_div_Step hRM hp le_rfl).1
  set xs := reps.map encPerm with hxs
  set S_cost := outbSylStepCost (membershipPrim hm) (groupOrderPrim ho) n with hS_cost
  -- fold invariant: partial fold over `reps.take j`
  have hfold := foldl_spec hfd (c := c_fold) (xs := xs) (acc0 := encGroup ps0)
    (Inv := fun j w => w = encGroup ((reps.take j).foldl (outbSylStep (gens ms) B) ps0) ∧
      OutbSylInv p R (gens ms) v a ((reps.take j).foldl (outbSylStep (gens ms) B) ps0))
    (M := 640 * (n + 1) ^ 6) (B := fun _ => S_cost)
    ⟨rfl, hinv0⟩
    (fun j w _ hw => by
      rw [hw.1]
      exact wt_encGroup_two_sq (outbSylInv_length_le hv_sq hw.2))
    (fun j w hj hw => by
      have hj' : j < reps.length := by simpa [hxs] using hj
      have hx : xs[j] = encPerm (reps[j]'hj') := by simp only [hxs, List.getElem_map]
      rw [hw.1, hx]
      have hpl := outbSylInv_length_le hv_sq hw.2
      refine FunAll.mono (outbSylStep_spec hm ho hst hjm hjo hml hpl hBM (reps[j]'hj'))
        fun w' cost' hw' => ⟨⟨?_, ?_⟩, hw'.2⟩
      · rw [hw'.1, List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
          List.foldl_append]
        rfl
      · rw [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
          List.foldl_append]
        exact outbSylStep_inv hp hw.2 (reps[j]'hj'))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hfold
  have hxs_len : xs.length = reps.length := by simp [hxs]
  rw [hxs_len, List.take_length] at hfold
  -- call `fd` from `outbSylPassE`
  have d0 := Det.arg' (P := P) (vs := [c_iter, .nat i, encGroup ps0]) (rest := [])
    (j := 0) (v := c_iter) rfl
  have d2 := Det.arg' (P := P) (vs := [c_iter, .nat i, encGroup ps0]) (rest := [])
    (j := 2) (v := encGroup ps0) rfl
  have dc0 := Det.get' d0 (Det.nat 0) (v := c_fold) rfl
  have dc1 := Det.get' d0 (Det.nat 1) (v := .list xs) rfl
  have darg := Det.mk3 dc0 dc1 d2
  refine FunAll.intro hps (EvalAll.call_funAll darg fun v_arg ca hv_arg => ?_)
  obtain ⟨rfl, hca⟩ := hv_arg
  refine hfold.mono fun w cw hw => ⟨?_, ?_⟩
  · refine ⟨reps.foldl (outbSylStep (gens ms) B) ps0, hw.1.1, ?_⟩
    exact outbSylPass_inv hp hME hcov hinv0
  · have hpl0 := outbSylInv_length_le hv_sq hinv0
    have hpl1 := outbSylInv_length_le hv_sq hw.1.2
    have hP0w := wt_encGroup_two_sq hpl0
    have hP1w := wt_encGroup_two_sq hpl1
    rw [hw.1.1] at *
    have hMw := wt_encGroup_sq hml
    have hBw := outb_wt_nat_le hBM
    have hcfw : c_fold.wt ≤ 2 * ((encGroup ms).wt + (Val.nat B).wt) + 6 :=
      wt_list2_le (encGroup ms) (.nat B)
    have hrepw : (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 :=
      outb_wt_reps_le reps
    have hciw : c_iter.wt ≤ 2 * (c_fold.wt + (Val.list xs).wt) + 6 :=
      wt_list2_le c_fold (.list xs)
    have hfargw := wt_list3_le c_fold (.list xs) (encGroup ps0)
    have hiw := wt_nat_le i
    have hiter_in_w := wt_list3_le c_iter (.nat i) (encGroup ps0)
    have hn2 : n ^ 2 ≤ (n + 1) ^ 6 :=
      (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have hn_le : n ≤ (n + 1) ^ 6 := (Nat.le_succ n).trans (Nat.le_self_pow (by norm_num) _)
    have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have hn16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have hm12 : reps.length + 1 ≤ (reps.length + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hm1_pos : 1 ≤ (reps.length + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    set Z2 := (reps.length + 1) ^ 2 * (n + 1) ^ 6 with hZ2
    set Z3 := (reps.length + 1) ^ 3 * (n + 1) ^ 6 with hZ3
    have hZ2_pos : 1 ≤ Z2 := Nat.mul_pos hm1_pos hn16
    have hZ23 : Z2 ≤ Z3 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hn6_Z2 : (n + 1) ^ 6 ≤ Z2 := by
      calc (n + 1) ^ 6 = 1 * (n + 1) ^ 6 := by ring
        _ ≤ Z2 := Nat.mul_le_mul_right _ hm1_pos
    have hrl_Z2 : reps.length ≤ Z2 := by
      calc reps.length ≤ (reps.length + 1) ^ 2 := by omega
        _ = (reps.length + 1) ^ 2 * 1 := by ring
        _ ≤ Z2 := Nat.mul_le_mul_left _ hn16
    have hrepw_Z2 : (Val.list xs).wt ≤ 13 * Z2 := by
      calc (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 := hrepw
        _ ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 6 := Nat.mul_le_mul_left _ hn26
        _ = 13 * Z2 := by rw [hZ2]; ring
    have htot_arg : (Val.list [c_fold, .list xs, encGroup ps0]).wt + reps.length +
        640 * (n + 1) ^ 6 + 1 ≤ 4000 * Z2 := by omega
    have hL : loopModK * (reps.length + 1) *
        ((Val.list [c_fold, .list xs, encGroup ps0]).wt + reps.length +
          640 * (n + 1) ^ 6 + 1) ≤ 4 * 10 ^ 6 * Z3 := by
      calc loopModK * (reps.length + 1) *
          ((Val.list [c_fold, .list xs, encGroup ps0]).wt + reps.length + 640 * (n + 1) ^ 6 + 1) ≤
          loopModK * (reps.length + 1) * (4000 * Z2) := Nat.mul_le_mul_left _ htot_arg
        _ = 4 * 10 ^ 6 * Z3 := by simp only [loopModK, hZ2, hZ3]; ring
    have hiter_in_Z2 : (Val.list [c_iter, .nat i, encGroup ps0]).wt ≤ 8000 * Z2 := by omega
    have hmulS : reps.length * S_cost ≤ (reps.length + 1) * S_cost :=
      Nat.mul_le_mul_right _ (by omega)
    have hgoal_eq : outbSylPassCost (membershipPrim hm) (groupOrderPrim ho) n reps.length =
        (reps.length + 1) * S_cost + 10 ^ 7 * Z3 := by
      simp only [outbSylPassCost, hS_cost, hZ3]; ring
    rw [hgoal_eq]
    clear d0 d2 dc0 dc1 darg hfold
    clear_value Z2 Z3 S_cost c_fold c_iter xs v B
    omega

/-- **The brute-force Sylow construction**, on
`[encGroup rs, encGroup ms, .nat p, .list (reps.map encPerm)]`. -/
def outbSylBody (pp it jord : ℕ) : Expr :=
  .letE (.call pp (mk3 (.prim jord (arg 1)) (arg 2) (.prim jord (arg 0))))
    (.call it (mk3
      (mk2 (mk2 (arg 1) (.var 1)) (arg 3))
      (.arith .add (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0))) (.nat 1))
      (arg 0)))

/-- Where the brute-force Sylow function and its modules sit. -/
structure OutbSylAt (P : Program) (sy pp it ps_fn fd st jm jo : ℕ)
    (hm : Membership) (ho : GroupOrder) : Prop where
  entry : P.funs[sy]? = some (outbSylBody pp it jo)
  ppart : P.funs[pp]? = some (outbPPartF pp)
  iter : P.HasAt it (iterFuns it ps_fn)
  pass : P.funs[ps_fn]? = some (outbSylPassE fd)
  fold : P.HasAt fd (foldlFuns fd st)
  step : P.funs[st]? = some (outbSylStepE jm jo)
  mem : P.prims[jm]? = some (membershipPrim hm)
  ord : P.prims[jo]? = some (groupOrderPrim ho)

/-- Cost bound of the brute-force Sylow construction for `reps` of length `m`. -/
def outbSylCost (pm po : Prim) (n m : ℕ) : ℕ :=
  (n ^ 2 + 2) * outbSylPassCost pm po n m + 2 * po.boundSize (10 ^ 4 * (n + 1) ^ 6) +
    10 ^ 8 * (m + 1) ^ 3 * (n + 1) ^ 8

open Classical in
/-- **Specification of `outbSylBody`**: produces `encGroup ps` with `ps.length ≤ 2 * n²` and
`OutbSylowMod p (gens rs) (gens ms) (gens ps)`. -/
theorem outbSyl_spec {hm : Membership} {ho : GroupOrder} {P : Program}
    {sy pp it ps_fn fd st jm jo : ℕ}
    (hP : OutbSylAt P sy pp it ps_fn fd st jm jo hm ho)
    {E_H : Subgroup (Perm (Fin n))} {rs ms reps : List (Perm (Fin n))}
    [((gens rs).subgroupOf (gens ms)).Normal]
    (hRM : gens rs ≤ gens ms) (hME : gens ms ≤ E_H)
    (hrl : rs.length ≤ n ^ 2) (hml : ms.length ≤ n ^ 2)
    (hcov : ∀ x ∈ E_H, TmRpCov (gens rs) reps x)
    {p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    FunAll P sy (.list [encGroup rs, encGroup ms, .nat p, .list (reps.map encPerm)])
      (fun w cost =>
        (∃ ps : List (Perm (Fin n)), w = encGroup ps ∧ ps.length ≤ 2 * n ^ 2 ∧
          OutbSylowMod p (gens rs) (gens ms) (gens ps)) ∧
        cost ≤ outbSylCost (membershipPrim hm) (groupOrderPrim ho) n reps.length) := by
  set R := gens rs
  set M := gens ms
  set v := (Nat.card M / Nat.card R).factorization p
  set B := p ^ v * Nat.card R
  set xs := reps.map encPerm with hxs
  set a_in : List Val := [encGroup rs, encGroup ms, .nat p, .list xs]
  set Y := 10 ^ 4 * (n + 1) ^ 6
  have hv_sq : v ≤ n ^ 2 := outb_factorization_le_sq p
  have hBM : B ≤ Nat.card M := (outb_ppart_div_Step hRM hp le_rfl).1
  -- step 1: compute `B` via `outbPPartF`
  have d0 := Det.arg' (P := P) (vs := a_in) (rest := []) (j := 0) (v := encGroup rs) rfl
  have d1 := Det.arg' (P := P) (vs := a_in) (rest := []) (j := 1) (v := encGroup ms) rfl
  have d2 := Det.arg' (P := P) (vs := a_in) (rest := []) (j := 2) (v := .nat p) rfl
  have dordM := groupOrder_call ho hP.ord d1 (⟨ms, rfl, rfl⟩ : GroupVal n (encGroup ms) M)
  have dordR := groupOrder_call ho hP.ord d0 (⟨rs, rfl, rfl⟩ : GroupVal n (encGroup rs) R)
  have dpp_arg := Det.mk3 dordM d2 dordR
  have dpp := Det.call dpp_arg (outbPPart_spec hP.ppart hRM hp hpn)
  refine FunAll.intro hP.entry (EvalAll.letE dpp fun vB c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- step 2: iterate `outbSylPassE` `k = n ^ 2 + 1` times
  set c_fold := Val.list [encGroup ms, .nat B] with hcf_def
  set c_iter := Val.list [c_fold, .list xs] with hci_def
  set k := n ^ 2 + 1 with hk
  set P_cost := outbSylPassCost (membershipPrim hm) (groupOrderPrim ho) n reps.length with hP_cost
  have h0 : ∃ ps : List (Perm (Fin n)), encGroup rs = encGroup ps ∧
      OutbSylInv p R M v (min 0 v) ps :=
    ⟨rs, rfl, outbSylInv_zero hrl hRM v⟩
  have hit := iter_spec hP.iter (c := c_iter) (k := k) (acc0 := encGroup rs)
    (Inv := fun i acc => ∃ ps : List (Perm (Fin n)), acc = encGroup ps ∧
      OutbSylInv p R M v (min i v) ps)
    (M := 640 * (n + 1) ^ 6) (B := fun _ => P_cost) h0
    (fun i acc _ ⟨ps, hacc, hinv⟩ => by
      rw [hacc]; exact wt_encGroup_two_sq (outbSylInv_length_le hv_sq hinv))
    (fun i acc hi hinv => by
      refine (outbSylPass_spec hm ho hP.pass hP.fold hP.step hP.mem hP.ord hRM hME hml hcov
        (by omega) hinv hp).mono fun w cw hw => ⟨?_, hw.2⟩
      obtain ⟨ps', rfl, hinv'⟩ := hw.1
      have hmin_step : min (min i v + 1) v = min (i + 1) v := by omega
      rw [hmin_step] at hinv'
      exact ⟨ps', rfl, hinv'⟩)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hit
  -- build argument of `it` in `env = [.list a_in, .nat B]`
  have d0' := Det.arg' (P := P) (vs := a_in) (rest := [.nat B]) (j := 0) (v := encGroup rs) rfl
  have d1' := Det.arg' (P := P) (vs := a_in) (rest := [.nat B]) (j := 1) (v := encGroup ms) rfl
  have d3' := Det.arg' (P := P) (vs := a_in) (rest := [.nat B]) (j := 3) (v := .list xs) rfl
  have dB' := Det.var' (P := P) (env := [.list a_in, .nat B]) (i := 1) (v := .nat B) rfl
  have dc_fold := Det.mk2 d1' dB'
  rw [← hcf_def] at dc_fold
  have d_citer := Det.mk2 dc_fold d3'
  rw [← hci_def] at d_citer
  have dn := Det.get' d0' (Det.nat 0) (v := .nat n) rfl
  have dk := Det.arith' (op := .add) (Det.arith' (op := .mul) dn dn rfl) (Det.nat 1) (z := k)
    (by simp [BinOp.eval, hk, sq])
  have dit_arg := Det.mk3 d_citer dk d0'
  refine EvalAll.call_funAll dit_arg fun v_it ca hv_it => ?_
  obtain ⟨rfl, hca⟩ := hv_it
  refine hit.mono fun w cw hw => ⟨?_, ?_⟩
  · obtain ⟨ps, rfl, hinv_k⟩ := hw.1
    exact ⟨ps, rfl, outbSylInv_length_le hv_sq hinv_k, outb_syl_done hinv_k⟩
  · obtain ⟨ps, hps_eq, hinv_k⟩ := hw.1
    have hpl_k := outbSylInv_length_le hv_sq hinv_k
    have hPkw := wt_encGroup_two_sq hpl_k
    rw [hps_eq] at *
    have hRw := wt_encGroup_sq hrl
    have hMw := wt_encGroup_sq hml
    have hBw := outb_wt_nat_le hBM
    have hMcardw := wt_card_le M
    have hRcardw := wt_card_le R
    have hpw := wt_nat_le p
    have hnw := wt_nat_le n
    have hkw := wt_nat_le k
    have h1w := wt_nat_le 1
    have hnnw := wt_nat_le (BinOp.mul.eval n n)
    have hmul_eq : BinOp.mul.eval n n = n * n := rfl
    have hn2 : n ^ 2 ≤ (n + 1) ^ 6 :=
      (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have hn_le : n ≤ (n + 1) ^ 6 := (Nat.le_succ n).trans (Nat.le_self_pow (by norm_num) _)
    have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have hn46 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have hn16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have hnn_le : n * n ≤ (n + 1) ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
    have hboM := (groupOrderPrim ho).bound_le
      (show (encGroup ms).size ≤ Y from (Val.size_le_wt _).trans (by omega))
    have hboR := (groupOrderPrim ho).bound_le
      (show (encGroup rs).size ≤ Y from (Val.size_le_wt _).trans (by omega))
    have hpp_argw := wt_list3_le (.nat (Nat.card M)) (.nat p) (.nat (Nat.card R))
    have hcfw : c_fold.wt ≤ 2 * ((encGroup ms).wt + (Val.nat B).wt) + 6 :=
      wt_list2_le (encGroup ms) (.nat B)
    have hrepw : (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 :=
      outb_wt_reps_le reps
    have hciw : c_iter.wt ≤ 2 * (c_fold.wt + (Val.list xs).wt) + 6 :=
      wt_list2_le c_fold (.list xs)
    have hainw : (Val.list a_in).wt ≤
        2 * ((encGroup rs).wt + (encGroup ms).wt + (Val.nat p).wt + (Val.list xs).wt) + 8 :=
      wt_list4_le (encGroup rs) (encGroup ms) (.nat p) (.list xs)
    have hit_argw := wt_list3_le c_iter (.nat k) (encGroup rs)
    have hm13 : 1 ≤ (reps.length + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have hm23 : (reps.length + 1) ^ 2 ≤ (reps.length + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    set Z3 := (reps.length + 1) ^ 3 * (n + 1) ^ 6 with hZ3
    set Z8 := (reps.length + 1) ^ 3 * (n + 1) ^ 8 with hZ8
    have hZ3_pos : 1 ≤ Z3 := Nat.mul_pos hm13 hn16
    have hZ38 : Z3 ≤ Z8 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hn6_Z3 : (n + 1) ^ 6 ≤ Z3 := by
      calc (n + 1) ^ 6 = 1 * (n + 1) ^ 6 := by ring
        _ ≤ Z3 := Nat.mul_le_mul_right _ hm13
    have hrepw_Z3 : (Val.list xs).wt ≤ 13 * Z3 := by
      calc (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 := hrepw
        _ ≤ 13 * (reps.length + 1) ^ 3 * (n + 1) ^ 6 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hm23) hn26
        _ = 13 * Z3 := by rw [hZ3]; ring
    have hit_tot : (Val.list [c_iter, .nat k, encGroup rs]).wt + k + 640 * (n + 1) ^ 6 + 1 ≤
        5000 * Z3 := by omega
    have hk_le : k + 1 ≤ 2 * (n + 1) ^ 2 := by
      have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega
    have hL : loopModK * (k + 1) *
        ((Val.list [c_iter, .nat k, encGroup rs]).wt + k + 640 * (n + 1) ^ 6 + 1) ≤
        10 ^ 7 * Z8 := by
      calc loopModK * (k + 1) *
          ((Val.list [c_iter, .nat k, encGroup rs]).wt + k + 640 * (n + 1) ^ 6 + 1) ≤
          loopModK * (2 * (n + 1) ^ 2) * (5000 * Z3) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hk_le) hit_tot
        _ = 10 ^ 7 * Z8 := by simp only [loopModK, hZ3, hZ8]; ring
    have hkP : k * P_cost ≤ (n ^ 2 + 2) * P_cost := Nat.mul_le_mul_right _ (by omega)
    have hB_eq : p ^ (Nat.card M / Nat.card R).factorization p * Nat.card R = B := rfl
    rw [hB_eq] at hc1
    have hgoal_eq : outbSylCost (membershipPrim hm) (groupOrderPrim ho) n reps.length =
        (n ^ 2 + 2) * P_cost + 2 * (groupOrderPrim ho).boundSize Y + 10 ^ 8 * Z8 := by
      simp only [outbSylCost, hP_cost, hZ8, Y]; ring
    rw [hgoal_eq]
    clear d0 d1 d2 dordM dordR dpp_arg dpp d0' d1' d3' dB' dc_fold d_citer dn dk dit_arg hit
      hcf_def hci_def
    clear_value Z3 Z8 P_cost c_fold c_iter xs a_in Y R M v B k
    omega

end GI.Impl
