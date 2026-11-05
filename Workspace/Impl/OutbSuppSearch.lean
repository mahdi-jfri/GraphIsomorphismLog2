module

public import Workspace.Impl.OutbSuppSylow

@[expose] public section

/-!
# Brute-force search for a nonnormal Sylow subgroup of `M / R`

Given group encodings `encGroup rs` (`R = gens rs`), `encGroup ms` (`M = gens ms`), and a list
`reps` of coset representatives of `R` in `E_H`, `outbFindBody` tests nilpotency of `M / R` by
iterating `outbSearchBody` over `i = 0, 1, …, n`, starting from
`acc0 = [.nat (|M| / |R|), .nat 0, .nat 0]`:

* At `i ≥ 2` with `i ∣ r`, `i` is prime (`outb_sieve_prime`) and divides `|M| / |R|`
  (`outb_sieve_dvd`).
* `outbPrimeE` calls `outbSylBody` to build `encGroup ps` with `OutbSylowMod i R M (gens ps)`,
  computes the normal closure of `gens ps` in `M` (**NormalClosure**), and tests whether it lies in
  `gens ps` (`le_spec`, **Membership**).
* If `M` normalizes `gens ps`, `r` is replaced by `r / (|P| / |R|)` (`outb_sieve_next`); otherwise
  the search records `[.nat 0, .nat 1, encGroup ps]`.
* At `i = n + 1`, either a nonnormal Sylow subgroup `P / R` was recorded, or `M / R` is nilpotent
  (`outb_sieve_end`).

Only **Membership**, **GroupOrder**, and **NormalClosure** are used.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### Normality test and search invariant -/

theorem outb_gens_conj (s : Perm (Fin n)) (ps : List (Perm (Fin n))) :
    gens (ps.map fun x => s * x * s⁻¹) = (gens ps).map (MulAut.conj s).toMonoidHom := by
  unfold gens
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp [MulAut.conj_apply]

/-- The normal closure of `P = ⟨ps⟩ ≤ M` in `M` lies in `P` iff `M` normalizes `P`. -/
theorem outb_normIn_iff {M : Subgroup (Perm (Fin n))} {ps cs : List (Perm (Fin n))}
    (hle : gens ps ≤ M)
    (hcs : gens cs = Subgroup.closure {x | ∃ g ∈ M ⊔ gens ps, ∃ y ∈ ps, x = g * y * g⁻¹}) :
    gens cs ≤ gens ps ↔ OutbNormIn M (gens ps) := by
  rw [hcs, sup_eq_left.mpr hle]
  constructor
  · intro h g hg x hx
    have hmap : (gens ps).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.closure {x | ∃ g ∈ M, ∃ y ∈ ps, x = g * y * g⁻¹} := by
      rw [← outb_gens_conj]
      refine Subgroup.closure_mono fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact ⟨g, hg, y, hy, rfl⟩
    exact h (hmap ⟨x, hx, by simp [MulAut.conj_apply]⟩)
  · intro h
    refine (Subgroup.closure_le _).mpr fun z hz => ?_
    obtain ⟨g, hg, y, hy, rfl⟩ := hz
    exact h g hg y (Subgroup.subset_closure hy)

/-- `if` with a deterministic condition and `EvalAll` branches. -/
theorem outb_ite {P : Program} {env : List Val} {c t e : Expr} {x cc : ℕ}
    (hc : Det P env c (.nat x) cc) {R : Val → ℕ → Prop} (ht : x ≠ 0 → EvalAll P env t R)
    (he : x = 0 → EvalAll P env e R) :
    EvalAll P env (.ite c t e) (fun w c' => ∃ ce, R w ce ∧ c' ≤ cc + ce + w.wt + 1) :=
  EvalAll.ite hc (fun _ _ h => ⟨x, h.1⟩) fun y cc' h => by
    obtain ⟨h1, h2⟩ := h
    cases h1
    by_cases hx : x = 0
    · simp only [hx, ↓reduceIte]
      exact (he hx).mono fun w ce hw => ⟨ce, hw, by omega⟩
    · simp only [hx, ↓reduceIte]
      exact (ht hx).mono fun w ce hw => ⟨ce, hw, by omega⟩

theorem Det.call_funAll {P : Program} {env : List Val} {f : ℕ} {a : Expr} {v : Val} {ca : ℕ}
    {Q : Val → ℕ → Prop} (ha : Det P env a v ca) (hf : FunAll P f v Q) :
    EvalAll P env (.call f a) (fun w c => ∃ cb, Q w cb ∧ c ≤ ca + cb + w.wt + 1) :=
  EvalAll.call_funAll ha fun _ _ ⟨rfl, hca'⟩ =>
    hf.mono fun w cb hQ => ⟨cb, hQ, by omega⟩

/-- The state of the search after the numbers below `i`. -/
def OutbSearchInv (R M : Subgroup (Perm (Fin n))) (i : ℕ) (acc : Val) : Prop :=
  (∃ r, acc = .list [.nat r, .nat 0, .nat 0] ∧ OutbSieve R M i r) ∨
  (∃ p ps, acc = .list [.nat 0, .nat 1, encGroup ps] ∧ ps.length ≤ 2 * n ^ 2 ∧ p.Prime ∧
    p ≤ n ∧ OutbSylowMod p R M (gens ps) ∧ ¬ OutbNormIn M (gens ps))

theorem outb_search_wt {R M : Subgroup (Perm (Fin n))} (hRM : R ≤ M) {i : ℕ} {acc : Val}
    (h : OutbSearchInv R M i acc) : acc.wt ≤ 1400 * (n + 1) ^ 6 := by
  have hn2 : n ^ 2 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hn1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h0 := wt_nat_le 0
  have h1 := wt_nat_le 1
  rcases h with ⟨r, rfl, hs⟩ | ⟨p, ps, rfl, hl, -⟩
  · have := outb_wt_nat_le (outb_sieve_le hRM hs)
    have := wt_list3_le (.nat r) (.nat 0) (.nat 0)
    omega
  · have := wt_encGroup_two_sq hl
    have := wt_list3_le (.nat 0) (.nat 1) (encGroup ps)
    omega

/-! ### The search step program and specification -/

/-- The part of the search step after a prime `i ∣ r` is found, on `[c, .nat i, acc]` where
`c = [encGroup rs, encGroup ms, .list (reps.map encPerm), .nat |R|]`. -/
def outbPrimeE (sy mg le jnc jord : ℕ) : Expr :=
  .letE (.call sy (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1)
      (.get (arg 0) (.nat 2))))
  (.letE (.prim jnc (mk2 (.get (arg 0) (.nat 1)) (.var 1)))
  (.ite (.call le (mk2 (.var 1) (.call mg (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.var 2)))))
    (mk3 (.arith .div (.get (arg 2) (.nat 0))
        (.arith .div (.prim jord (.var 1)) (.get (arg 0) (.nat 3))))
      (.nat 0) (.nat 0))
    (mk3 (.nat 0) (.nat 1) (.var 1))))

/-- **The search step** on `[c, .nat i, acc]`. -/
def outbSearchBody (sy mg le jnc jord : ℕ) : Expr :=
  .ite (.get (arg 2) (.nat 1)) (arg 2)
  (.ite (.arith .lt (arg 1) (.nat 2)) (arg 2)
  (.ite (.arith .mod (.get (arg 2) (.nat 0)) (arg 1)) (arg 2)
  (outbPrimeE sy mg le jnc jord)))

/-- Where the search step and its modules sit. -/
structure OutbSearchAt (P : Program) (g sy pp it_sy ps_fn fd_sy st_sy mg le jnc jord jm : ℕ)
    (hnc : NormalClosure) (hord : GroupOrder) (hmem : Membership) : Prop where
  step : P.funs[g]? = some (outbSearchBody sy mg le jnc jord)
  syl : OutbSylAt P sy pp it_sy ps_fn fd_sy st_sy jm jord hmem hord
  mg : P.HasAt mg (mkGroupFuns mg)
  le : P.HasAt le (leFuns le jm)
  nc : P.prims[jnc]? = some (normalClosurePrim hnc)
  ord : P.prims[jord]? = some (groupOrderPrim hord)
  mem : P.prims[jm]? = some (membershipPrim hmem)

/-- Cost bound of one search step for `reps` of length `m`. -/
def outbSearchCost (pnc pord pm : Prim) (n m : ℕ) : ℕ :=
  outbSylCost pm pord n m +
    pnc.boundSize (10 ^ 4 * (n + 1) ^ 6) +
    pord.boundSize (10 ^ 4 * (n + 1) ^ 6) +
    10 ^ 4 * (n + 1) ^ 6 * pm.boundSize (10 ^ 4 * (n + 1) ^ 6) +
    10 ^ 7 * (m + 1) ^ 3 * (10 ^ 4 * (n + 1) ^ 6) ^ 3

open Classical in
/-- The prime case of `outbSearchBody`: constructs a Sylow `i`-subgroup of `M / R`, tests
normality in `M`, and updates the sieve state. -/
theorem outb_search_prime {hnc : NormalClosure} {hord : GroupOrder} {hmem : Membership}
    {P : Program} {g sy pp it_sy ps_fn fd_sy st_sy mg le jnc jord jm : ℕ}
    (hP : OutbSearchAt P g sy pp it_sy ps_fn fd_sy st_sy mg le jnc jord jm hnc hord hmem)
    {E_H : Subgroup (Perm (Fin n))} {rs ms reps : List (Perm (Fin n))}
    [((gens rs).subgroupOf (gens ms)).Normal]
    (hRM : gens rs ≤ gens ms) (hME : gens ms ≤ E_H)
    (hrl : rs.length ≤ n ^ 2) (hml : ms.length ≤ n ^ 2)
    (hcov : ∀ x ∈ E_H, TmRpCov (gens rs) reps x)
    {i r : ℕ} (hi : i ≤ n) (hs : OutbSieve (gens rs) (gens ms) i r) (hi2 : 2 ≤ i) (hir : i ∣ r) :
    let c := Val.list [encGroup rs, encGroup ms, .list (reps.map encPerm),
      .nat (Nat.card (gens rs))]
    EvalAll P [.list [c, .nat i, .list [.nat r, .nat 0, .nat 0]]]
      (outbPrimeE sy mg le jnc jord)
      (fun w cost => OutbSearchInv (gens rs) (gens ms) (i + 1) w ∧
        cost ≤ outbSylCost (membershipPrim hmem) (groupOrderPrim hord) n reps.length +
          (normalClosurePrim hnc).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          (groupOrderPrim hord).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          10 ^ 6 * (reps.length + 1) ^ 3 * (10 ^ 4 * (n + 1) ^ 6) ^ 3) := by
  intro c
  unfold outbPrimeE
  set R := gens rs
  set M := gens ms
  set xs := reps.map encPerm with hxs
  set acc : Val := .list [.nat r, .nat 0, .nat 0]
  set Y := 10 ^ 4 * (n + 1) ^ 6 with hY
  have hp : i.Prime := outb_sieve_prime hi2 hir hs
  have hRw := wt_encGroup_sq hrl
  have hMw := wt_encGroup_sq hml
  have hrepw : (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 :=
    outb_wt_reps_le reps
  have hRcardw := wt_card_le R
  have hrM : r ≤ Nat.card M := outb_sieve_le hRM hs
  have hrw := outb_wt_nat_le hrM
  have h0w := wt_nat_le 0
  have h1w := wt_nat_le 1
  have hiw := wt_nat_le i
  have hnw := wt_nat_le n
  have hn16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn2 : n ^ 2 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left (Nat.le_succ n) 2).trans (Nat.pow_le_pow_right (Nat.succ_pos _) (by decide))
  have hn_le : n ≤ (n + 1) ^ 6 := (Nat.le_succ n).trans (Nat.le_self_pow (by decide) _)
  have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn36 : (n + 1) ^ 3 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hm13 : 1 ≤ (reps.length + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hm23 : (reps.length + 1) ^ 2 ≤ (reps.length + 1) ^ 3 :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hY_pos : 1 ≤ Y := by omega
  have hY_le_Y3 : Y ≤ Y ^ 3 := Nat.le_self_pow (by decide) Y
  have hY3_pos : 1 ≤ Y ^ 3 := Nat.one_le_pow _ _ hY_pos
  set Z := (reps.length + 1) ^ 3 * Y ^ 3 with hZ
  have hZ_pos : 1 ≤ Z := Nat.mul_pos hm13 hY3_pos
  have hY3_Z : Y ^ 3 ≤ Z := by
    calc Y ^ 3 = 1 * Y ^ 3 := (one_mul _).symm
      _ ≤ Z := Nat.mul_le_mul_right _ hm13
  have hn6_Y : (n + 1) ^ 6 ≤ Y := by omega
  have hn6_Z : (n + 1) ^ 6 ≤ Z := hn6_Y.trans (hY_le_Y3.trans hY3_Z)
  have hrepw_Z : (Val.list xs).wt ≤ 13 * Z := by
    calc (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 := hrepw
      _ ≤ 13 * (reps.length + 1) ^ 3 * Y ^ 3 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hm23) (hn26.trans (hn6_Y.trans hY_le_Y3))
      _ = 13 * Z := by rw [hZ]; ring
  have hmk_Z : 8 * mkGroupK * (n + 1) ^ 9 ≤ 80 * Z := by
    have h1 : 10 ^ 4 * (n + 1) ^ 3 ≤ Y := by rw [hY]; exact Nat.mul_le_mul_left _ hn36
    have h2 : (n + 1) ^ 6 ≤ Y ^ 2 := hn6_Y.trans (Nat.le_self_pow (by decide) Y)
    calc 8 * mkGroupK * (n + 1) ^ 9 = 80 * ((10 ^ 4 * (n + 1) ^ 3) * (n + 1) ^ 6) := by
          simp only [mkGroupK]; ring
      _ ≤ 80 * (Y * Y ^ 2) := Nat.mul_le_mul_left 80 (Nat.mul_le_mul h1 h2)
      _ = 80 * Y ^ 3 := by ring
      _ ≤ 80 * Z := Nat.mul_le_mul_left 80 hY3_Z
  have hcw : c.wt ≤ 2 * ((encGroup rs).wt + (encGroup ms).wt +
      (Val.list xs).wt + (Val.nat (Nat.card R)).wt) + 8 :=
    wt_list4_le (encGroup rs) (encGroup ms) (.list xs) (.nat (Nat.card R))
  have haccw : acc.wt ≤ 2 * ((Val.nat r).wt + (Val.nat 0).wt + (Val.nat 0).wt) + 7 :=
    wt_list3_le (.nat r) (.nat 0) (.nat 0)
  have hinw := wt_list3_le c (.nat i) acc
  have hsy_argw := wt_list4_le (encGroup rs) (encGroup ms) (.nat i) (.list xs)
  -- step 1: call `sy` (`outbSylBody`)
  have dc := Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := []) (j := 0) (v := c) rfl
  have di := Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := []) (j := 1) (v := .nat i) rfl
  have dc0 := Det.get' dc (Det.nat 0) (v := encGroup rs) rfl
  have dc1 := Det.get' dc (Det.nat 1) (v := encGroup ms) rfl
  have dc2 := Det.get' dc (Det.nat 2) (v := .list xs) rfl
  have dsy_arg := Det.mk4 dc0 dc1 di dc2
  refine EvalAll.letE
    (Det.call_funAll dsy_arg (outbSyl_spec hP.syl hRM hME hrl hml hcov hp hi))
    fun v1 c1 h1 => ?_
  clear dc di dc0 dc1 dc2 dsy_arg
  obtain ⟨cw1, ⟨⟨ps, rfl, hpl, hsyl⟩, hcw1⟩, hc1⟩ := h1
  -- step 2: normal closure of `gens ps` in `M`
  have dc_1 := Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := [encGroup ps])
    (j := 0) (v := c) rfl
  have dc1_1 := Det.get' dc_1 (Det.nat 1) (v := encGroup ms) rfl
  have dp_1 := Det.var' (P := P) (env := [.list [c, .nat i, acc], encGroup ps])
    (i := 1) (v := encGroup ps) rfl
  have hPw := wt_encGroup_two_sq hpl
  have hnca := wt_list2_le (encGroup ms) (encGroup ps)
  have hncs : (Val.list [encGroup ms, encGroup ps]).size ≤ Y := (Val.size_le_wt _).trans (by omega)
  refine EvalAll.letE (normalClosure_call hnc hP.nc (Det.mk2 dc1_1 dp_1) ⟨ms, rfl, rfl⟩)
    fun v2 c2 h2 => ?_
  clear dc_1 dc1_1 dp_1
  obtain ⟨hNC, hc2⟩ := h2
  have hbnc := (normalClosurePrim hnc).bound_le hncs
  have hv2w : v2.wt ≤ 13 * (n + 1) ^ 6 := GensVal.wt_le hNC
  -- step 3: normality test and branch
  set env2 := [Val.list [c, .nat i, acc], encGroup ps, v2]
  have dc_2 := Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := [encGroup ps, v2])
    (j := 0) (v := c) rfl
  have dc0_2 := Det.get' dc_2 (Det.nat 0) (v := encGroup rs) rfl
  have dn_2 := Det.get' dc0_2 (Det.nat 0) (v := .nat n) rfl
  have dv2 := Det.var' (P := P) (env := env2) (i := 2) (v := v2) rfl
  obtain ⟨cs, hcl, hcg, dC, hCw⟩ := outb_mk_det hP.mg dn_2 dv2 hNC
  have dp_2 := Det.var' (P := P) (env := env2) (i := 1) (v := encGroup ps) rfl
  have hle_call := le_spec hmem hP.le hP.mem
    (⟨ps, rfl, rfl⟩ : GroupVal n (encGroup ps) (gens ps)) cs
  have dt := Det.call (Det.mk2 dp_2 dC) hle_call
  -- branch 1 (normal) and branch 0 (nonnormal)
  have dacc_2 := Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := [encGroup ps, v2])
    (j := 2) (v := acc) rfl
  have dr := Det.get' dacc_2 (Det.nat 0) (v := .nat r) rfl
  have dordP := groupOrder_call hord hP.ord dp_2
    (⟨ps, rfl, rfl⟩ : GroupVal n (encGroup ps) (gens ps))
  have dc3_2 := Det.get' dc_2 (Det.nat 3) (v := .nat (Nat.card R)) rfl
  have dquotP := Det.arith_wt (op := .div) dordP dc3_2 (z := Nat.card (gens ps) / Nat.card R) rfl
  have ddiv_r := Det.arith_wt (op := .div) dr dquotP
    (z := r / (Nat.card (gens ps) / Nat.card R)) rfl
  have dnorm := Det.mk3 ddiv_r (Det.nat 0) (Det.nat 0)
  have dnn := Det.mk3 (Det.nat 0) (Det.nat 1) dp_2
  refine (Det.ite' dt dnorm dnn).post fun c3 hc3 => ⟨?_, ?_⟩
  · have hnc_iff : gens cs ≤ gens ps ↔ OutbNormIn M (gens ps) :=
      outb_normIn_iff hsyl.2.1 hcg
    by_cases hN : gens cs ≤ gens ps
    · simp only [hN, decide_true, Bool.toNat_true, one_ne_zero, ↓reduceIte]
      exact Or.inl ⟨_, rfl, outb_sieve_next hRM hp hir hs hsyl (hnc_iff.mp hN)⟩
    · simp only [hN, decide_false, Bool.toNat_false, ↓reduceIte]
      exact Or.inr ⟨i, ps, rfl, hpl, hp, hi, hsyl, fun h => hN (hnc_iff.mpr h)⟩
  · -- cost bound
    clear dc_2 dc0_2 dn_2 dv2 dC dp_2 hle_call dt dacc_2 dr dordP dc3_2 dquotP ddiv_r dnorm dnn
    have hPcardw := wt_card_le (gens ps)
    have hPM_card : Nat.card (gens ps) ≤ Nat.card M := Subgroup.card_le_of_le hsyl.2.1
    have hquotPw : (Val.nat (Nat.card (gens ps) / Nat.card R)).wt ≤ n ^ 2 + 3 :=
      outb_wt_nat_le ((Nat.div_le_self _ _).trans hPM_card)
    have hr'w : (Val.nat (r / (Nat.card (gens ps) / Nat.card R))).wt ≤ n ^ 2 + 3 :=
      outb_wt_nat_le ((Nat.div_le_self _ _).trans hrM)
    have hbw := wt_boolVal_le (decide (gens cs ≤ gens ps))
    have hboP := (groupOrderPrim hord).bound_le
      (show (encGroup ps).size ≤ Y from (Val.size_le_wt _).trans (by omega))
    have hmem1 : (Val.list [encGroup ps, encPerm (1 : Perm (Fin n))]).size ≤ Y := by
      have := wt_list2_le (encGroup ps) (encPerm (1 : Perm (Fin n)))
      have := wt_encPerm_le (1 : Perm (Fin n))
      exact (Val.size_le_wt _).trans (by omega)
    have hbm := (membershipPrim hmem).bound_le hmem1
    have hta := wt_list2_le (encGroup ps) (encGroup cs)
    have hT : (Val.list [encGroup ps, encGroup cs]).wt ≤ Y := by omega
    have hT3 : (Val.list [encGroup ps, encGroup cs]).wt ^ 3 ≤ Z :=
      (Nat.pow_le_pow_left hT 3).trans hY3_Z
    have hTm : (Val.list [encGroup ps, encGroup cs]).wt *
        (membershipPrim hmem).bound (.list [encGroup ps, encPerm (1 : Perm (Fin n))]) ≤
        Y * (membershipPrim hmem).boundSize Y := Nat.mul_le_mul hT hbm
    have hmg_argw := wt_list2_le (.nat n) v2
    have hnormw := wt_list3_le (.nat (r / (Nat.card (gens ps) / Nat.card R))) (.nat 0) (.nat 0)
    have hnnw := wt_list3_le (.nat 0) (.nat 1) (encGroup ps)
    have hmax1 : max
        (Val.list [.nat (r / (Nat.card (gens ps) / Nat.card R)), .nat 0, .nat 0]).wt
        (Val.list [.nat 0, .nat 1, encGroup ps]).wt ≤ 2000 * Z := by
      apply max_le <;> omega
    have hres : (if (decide (gens cs ≤ gens ps)).toNat = 0 then
        Val.list [.nat 0, .nat 1, encGroup ps] else
        Val.list [.nat (r / (Nat.card (gens ps) / Nat.card R)), .nat 0, .nat 0]).wt ≤
        2000 * Z := by
      split
      · exact (le_max_right _ _).trans hmax1
      · exact (le_max_left _ _).trans hmax1
    generalize (if (decide (gens cs ≤ gens ps)).toNat = 0 then
        Val.list [.nat 0, .nat 1, encGroup ps] else
        Val.list [.nat (r / (Nat.card (gens ps) / Nat.card R)), .nat 0, .nat 0]) = res at hres ⊢
    have hgoal_Z : 10 ^ 6 * (reps.length + 1) ^ 3 * Y ^ 3 = 10 ^ 6 * Z := by
      rw [hZ]; ring
    rw [hgoal_Z]
    clear hmax1 hgoal_Z
    clear_value Z Y c acc xs R M env2
    omega

/-- **One step of the search** preserves `OutbSearchInv` from `i` to `i + 1`. -/
theorem outbSearch_step {hnc : NormalClosure} {hord : GroupOrder} {hmem : Membership}
    {P : Program} {g sy pp it_sy ps_fn fd_sy st_sy mg le jnc jord jm : ℕ}
    (hP : OutbSearchAt P g sy pp it_sy ps_fn fd_sy st_sy mg le jnc jord jm hnc hord hmem)
    {E_H : Subgroup (Perm (Fin n))} {rs ms reps : List (Perm (Fin n))}
    [((gens rs).subgroupOf (gens ms)).Normal]
    (hRM : gens rs ≤ gens ms) (hME : gens ms ≤ E_H)
    (hrl : rs.length ≤ n ^ 2) (hml : ms.length ≤ n ^ 2)
    (hcov : ∀ x ∈ E_H, TmRpCov (gens rs) reps x)
    {i : ℕ} (hi : i ≤ n) {acc : Val} (hinv : OutbSearchInv (gens rs) (gens ms) i acc) :
    let c := Val.list [encGroup rs, encGroup ms, .list (reps.map encPerm),
      .nat (Nat.card (gens rs))]
    FunAll P g (.list [c, .nat i, acc]) (fun w cost =>
      OutbSearchInv (gens rs) (gens ms) (i + 1) w ∧
      cost ≤ outbSearchCost (normalClosurePrim hnc) (groupOrderPrim hord)
        (membershipPrim hmem) n reps.length) := by
  intro c
  set R := gens rs
  set M := gens ms
  set xs := reps.map encPerm with hxs
  set Y := 10 ^ 4 * (n + 1) ^ 6 with hY
  set Z := (reps.length + 1) ^ 3 * Y ^ 3 with hZ
  have hRw := wt_encGroup_sq hrl
  have hMw := wt_encGroup_sq hml
  have hrepw : (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 :=
    outb_wt_reps_le reps
  have hRcardw := wt_card_le R
  have haw := outb_search_wt hRM hinv
  have hiw := wt_nat_le i
  have hn2 : n ^ 2 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hn_le : n ≤ (n + 1) ^ 6 := (Nat.le_succ n).trans (Nat.le_self_pow (by norm_num) _)
  have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm13 : 1 ≤ (reps.length + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hm23 : (reps.length + 1) ^ 2 ≤ (reps.length + 1) ^ 3 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hn16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hY_pos : 1 ≤ Y := by omega
  have hY_le_Y3 : Y ≤ Y ^ 3 := Nat.le_self_pow (by norm_num) Y
  have hY3_pos : 1 ≤ Y ^ 3 := Nat.one_le_pow _ _ hY_pos
  have hZ_pos : 1 ≤ Z := Nat.mul_pos hm13 hY3_pos
  have hY3_Z : Y ^ 3 ≤ Z := by
    calc Y ^ 3 = 1 * Y ^ 3 := (one_mul _).symm
      _ ≤ Z := Nat.mul_le_mul_right _ hm13
  have hn6_Y : (n + 1) ^ 6 ≤ Y := by omega
  have hn6_Z : (n + 1) ^ 6 ≤ Z := hn6_Y.trans (hY_le_Y3.trans hY3_Z)
  have hrepw_Z : (Val.list xs).wt ≤ 13 * Z := by
    calc (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 := hrepw
      _ ≤ 13 * (reps.length + 1) ^ 3 * Y ^ 3 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hm23) (hn26.trans (hn6_Y.trans hY_le_Y3))
      _ = 13 * Z := by rw [hZ]; ring
  have hcw : c.wt ≤ 2 * ((encGroup rs).wt + (encGroup ms).wt +
      (Val.list xs).wt + (Val.nat (Nat.card R)).wt) + 8 :=
    wt_list4_le (encGroup rs) (encGroup ms) (.list xs) (.nat (Nat.card R))
  have hW3 := wt_list3_le c (.nat i) acc
  set W := (Val.list [c, .nat i, acc]).wt with hWdef
  have hWZ : 2 * W + 100 ≤ 10 ^ 5 * Z := by omega
  have dacc := Det.arg' (P := P) (vs := [c, .nat i, acc]) (rest := []) (j := 2) (v := acc) rfl
  have hsame : OutbSearchInv R M (i + 1) acc →
      EvalAll P [.list [c, .nat i, acc]] (arg 2)
        (fun w cost => OutbSearchInv R M (i + 1) w ∧ cost ≤ 10 ^ 5 * Z) := fun hI =>
    dacc.post fun cost hcost => ⟨hI, by omega⟩
  set B0 := outbSylCost (membershipPrim hmem) (groupOrderPrim hord) n reps.length +
      (normalClosurePrim hnc).boundSize Y +
      (groupOrderPrim hord).boundSize Y +
      Y * (membershipPrim hmem).boundSize Y +
      10 ^ 6 * Z with hB0
  have hZB0 : 10 ^ 5 * Z ≤ B0 := by omega
  have hB : B0 + 3 * (10 ^ 6 * Z) ≤ outbSearchCost (normalClosurePrim hnc) (groupOrderPrim hord)
      (membershipPrim hmem) n reps.length := by
    have hgoal_eq : outbSearchCost (normalClosurePrim hnc) (groupOrderPrim hord)
        (membershipPrim hmem) n reps.length =
        outbSylCost (membershipPrim hmem) (groupOrderPrim hord) n reps.length +
          (normalClosurePrim hnc).boundSize Y +
          (groupOrderPrim hord).boundSize Y +
          Y * (membershipPrim hmem).boundSize Y +
          10 ^ 7 * Z := by
      simp only [outbSearchCost, hY, hZ]; ring
    rw [hgoal_eq, hB0]
    omega
  refine FunAll.intro hP.step ?_
  unfold outbSearchBody
  rcases hinv with ⟨r, rfl, hs⟩ | ⟨p, ps, rfl, hl, hp, hpn, hsyl, hnn⟩
  · -- still searching
    have hrM := outb_sieve_le hRM hs
    have hrw := outb_wt_nat_le hrM
    have hr0 := Det.get' dacc (Det.nat 1) (v := .nat 0) rfl
    have hc0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    refine (outb_ite (R := fun w cost => OutbSearchInv R M (i + 1) w ∧ cost ≤ B0 + 2 * (10 ^ 6 * Z))
      hr0 (fun h => absurd rfl h) fun _ => ?_).mono fun w cost h => ?_
    rotate_left
    · obtain ⟨ce, ⟨hI, hce⟩, hcost⟩ := h
      refine ⟨hI, ?_⟩
      have := outb_search_wt hRM hI
      omega
    have d1 := Det.arg' (P := P) (vs := [c, .nat i, .list [.nat r, .nat 0, .nat 0]])
      (rest := []) (j := 1) (v := .nat i) rfl
    have dlt := Det.arith' (op := .lt) d1 (Det.nat 2) rfl
    have hlt1 : BinOp.lt.eval i 2 ≤ 1 := by simp only [BinOp.eval]; split <;> omega
    refine (outb_ite (R := fun w cost => OutbSearchInv R M (i + 1) w ∧ cost ≤ B0 + 10 ^ 6 * Z)
      dlt (fun hlt => (hsame (Or.inl ⟨r, rfl, outb_sieve_small
        (by by_contra h; simp [BinOp.eval, h] at hlt) hs⟩)).mono fun w cost h =>
          ⟨h.1, h.2.trans (by omega)⟩) fun hge => ?_).mono fun w cost h => ?_
    rotate_left
    · obtain ⟨ce, ⟨hI, hce⟩, hcost⟩ := h
      refine ⟨hI, ?_⟩
      have := outb_search_wt hRM hI
      omega
    have hi2 : 2 ≤ i := by
      by_contra h; simp [BinOp.eval, show i < 2 by omega] at hge
    have dr := Det.get' dacc (Det.nat 0) (v := .nat r) rfl
    have dmod := Det.arith' (op := .mod) dr d1 rfl
    have hm1 : BinOp.mod.eval r i < i := Nat.mod_lt _ (by omega)
    refine (outb_ite (R := fun w cost => OutbSearchInv R M (i + 1) w ∧ cost ≤ B0)
      dmod (fun hm => (hsame (Or.inl ⟨r, rfl, outb_sieve_skip
        (fun hd => hm (by simpa [BinOp.eval] using Nat.mod_eq_zero_of_dvd hd)) hs⟩)).mono
          fun w cost h => ⟨h.1, h.2.trans hZB0⟩) fun hm => ?_).mono fun w cost h => ?_
    rotate_left
    · obtain ⟨ce, ⟨hI, hce⟩, hcost⟩ := h
      refine ⟨hI, ?_⟩
      have := outb_search_wt hRM hI
      omega
    exact (outb_search_prime hP hRM hME hrl hml hcov hi hs hi2
      (Nat.dvd_of_mod_eq_zero (by simpa [BinOp.eval] using hm))).mono fun w cost h => by
      refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
      simp only [hB0, hY, hZ]; ring
  · -- already found
    have hr1 := Det.get' dacc (Det.nat 1) (v := .nat 1) rfl
    refine (Det.ite_pos hr1 one_ne_zero dacc).post fun cost hcost =>
      ⟨Or.inr ⟨p, ps, rfl, hl, hp, hpn, hsyl, hnn⟩, ?_⟩
    have := wt_nat_le 1
    omega

/-! ### The full search `outbFindBody` -/

/-- **The search for a nonnormal Sylow subgroup of `M / R`**, on
`[encGroup rs, encGroup ms, .list (reps.map encPerm)]`. -/
def outbFindBody (it jord : ℕ) : Expr :=
  .letE (.prim jord (arg 0))
  (.call it (mk3
    (mk4 (arg 0) (arg 1) (arg 2) (.var 1))
    (.arith .add (.get (arg 0) (.nat 0)) (.nat 1))
    (mk3 (.arith .div (.prim jord (arg 1)) (.var 1)) (.nat 0) (.nat 0))))

/-- Where the search function and its modules sit. -/
structure OutbFindAt (P : Program)
    (f it g sy pp it_sy ps_fn fd_sy st_sy mg le jnc jord jm : ℕ)
    (hnc : NormalClosure) (hord : GroupOrder) (hmem : Membership) : Prop where
  entry : P.funs[f]? = some (outbFindBody it jord)
  iter : P.HasAt it (iterFuns it g)
  step : OutbSearchAt P g sy pp it_sy ps_fn fd_sy st_sy mg le jnc jord jm hnc hord hmem

/-- Cost bound of `outbFindBody` for `reps` of length `m`. -/
def outbFindCost (pnc pord pm : Prim) (n m : ℕ) : ℕ :=
  (n + 2) * outbSearchCost pnc pord pm n m + 10 ^ 6 * (m + 1) ^ 3 * (10 ^ 4 * (n + 1) ^ 6) ^ 3

/-- **Specification of `outbFindBody`**: returns `w` satisfying
`OutbSearchInv (gens rs) (gens ms) (n + 1) w`. -/
theorem outbFind_spec {hnc : NormalClosure} {hord : GroupOrder} {hmem : Membership}
    {P : Program} {f it g sy pp it_sy ps_fn fd_sy st_sy mg le jnc jord jm : ℕ}
    (hP : OutbFindAt P f it g sy pp it_sy ps_fn fd_sy st_sy mg le jnc jord jm hnc hord hmem)
    {E_H : Subgroup (Perm (Fin n))} {rs ms reps : List (Perm (Fin n))}
    [((gens rs).subgroupOf (gens ms)).Normal]
    (hRM : gens rs ≤ gens ms) (hME : gens ms ≤ E_H)
    (hrl : rs.length ≤ n ^ 2) (hml : ms.length ≤ n ^ 2)
    (hcov : ∀ x ∈ E_H, TmRpCov (gens rs) reps x) :
    FunAll P f (.list [encGroup rs, encGroup ms, .list (reps.map encPerm)])
      (fun w cost => OutbSearchInv (gens rs) (gens ms) (n + 1) w ∧
        cost ≤ outbFindCost (normalClosurePrim hnc) (groupOrderPrim hord)
          (membershipPrim hmem) n reps.length) := by
  set R := gens rs
  set M := gens ms
  set xs := reps.map encPerm with hxs
  set a_in : List Val := [encGroup rs, encGroup ms, .list xs]
  set Y := 10 ^ 4 * (n + 1) ^ 6 with hY
  set Z := (reps.length + 1) ^ 3 * Y ^ 3 with hZ
  set B := outbSearchCost (normalClosurePrim hnc) (groupOrderPrim hord)
    (membershipPrim hmem) n reps.length with hB
  have hRw := wt_encGroup_sq hrl
  have hMw := wt_encGroup_sq hml
  have hn2 : n ^ 2 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hn_le : n ≤ (n + 1) ^ 6 := (Nat.le_succ n).trans (Nat.le_self_pow (by norm_num) _)
  have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm13 : 1 ≤ (reps.length + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hm23 : (reps.length + 1) ^ 2 ≤ (reps.length + 1) ^ 3 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hn16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hY_pos : 1 ≤ Y := by omega
  have hY_le_Y3 : Y ≤ Y ^ 3 := Nat.le_self_pow (by norm_num) Y
  have hY3_pos : 1 ≤ Y ^ 3 := Nat.one_le_pow _ _ hY_pos
  have hZ_pos : 1 ≤ Z := Nat.mul_pos hm13 hY3_pos
  have hY3_Z : Y ^ 3 ≤ Z := by
    calc Y ^ 3 = 1 * Y ^ 3 := (one_mul _).symm
      _ ≤ Z := Nat.mul_le_mul_right _ hm13
  have hn6_Y : (n + 1) ^ 6 ≤ Y := by omega
  have hn6_Z : (n + 1) ^ 6 ≤ Z := hn6_Y.trans (hY_le_Y3.trans hY3_Z)
  have hYB : 2 * (groupOrderPrim hord).boundSize Y ≤ B := by
    simp only [hB, outbSearchCost, outbSylCost, hY]
    omega
  -- step 1: compute `|R|`
  have d0 := Det.arg' (P := P) (vs := a_in) (rest := []) (j := 0) (v := encGroup rs) rfl
  have dordR := groupOrder_call hord hP.step.ord d0 (⟨rs, rfl, rfl⟩ : GroupVal n (encGroup rs) R)
  refine FunAll.intro hP.entry (EvalAll.letE dordR fun vR c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- step 2: build argument of `it` and run `iter_spec`
  set c := Val.list [encGroup rs, encGroup ms, .list xs, .nat (Nat.card R)] with hc_def
  set acc0 : Val := .list [.nat (Nat.card M / Nat.card R), .nat 0, .nat 0] with hacc0_def
  have d0' := Det.arg' (P := P) (vs := a_in) (rest := [.nat (Nat.card R)])
    (j := 0) (v := encGroup rs) rfl
  have d1' := Det.arg' (P := P) (vs := a_in) (rest := [.nat (Nat.card R)])
    (j := 1) (v := encGroup ms) rfl
  have d2' := Det.arg' (P := P) (vs := a_in) (rest := [.nat (Nat.card R)])
    (j := 2) (v := .list xs) rfl
  have dvR := Det.var' (P := P) (env := [.list a_in, .nat (Nat.card R)])
    (i := 1) (v := .nat (Nat.card R)) rfl
  have dc := Det.mk4 d0' d1' d2' dvR
  rw [← hc_def] at dc
  have dn := Det.get' d0' (Det.nat 0) (v := .nat n) rfl
  have dn1 := Det.arith' (op := .add) dn (Det.nat 1) (z := n + 1) rfl
  have dordM := groupOrder_call hord hP.step.ord d1' (⟨ms, rfl, rfl⟩ : GroupVal n (encGroup ms) M)
  have ddiv := Det.arith_wt (op := .div) dordM dvR (z := Nat.card M / Nat.card R) rfl
  have dacc0 := Det.mk3 ddiv (Det.nat 0) (Det.nat 0)
  rw [← hacc0_def] at dacc0
  have dit_arg := Det.mk3 dc dn1 dacc0
  have h0 : OutbSearchInv R M 0 acc0 := Or.inl ⟨_, rfl, outb_sieve_zero R M⟩
  have hit := iter_spec hP.iter (c := c) (k := n + 1) (acc0 := acc0)
    (Inv := fun i acc => OutbSearchInv R M i acc)
    (M := 1400 * (n + 1) ^ 6) (B := fun _ => B) h0
    (fun i acc _ h => outb_search_wt hRM h)
    (fun i acc hi h => outbSearch_step hP.step hRM hME hrl hml hcov (by omega) h)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hit
  refine EvalAll.call_funAll dit_arg fun v_it ca hv_it => ?_
  obtain ⟨rfl, hca⟩ := hv_it
  refine hit.mono fun w cw hw => ⟨hw.1, ?_⟩
  have hww := outb_search_wt hRM hw.1
  have hacc0w := outb_search_wt hRM h0
  have hboR := (groupOrderPrim hord).bound_le
    (show (encGroup rs).size ≤ Y from (Val.size_le_wt _).trans (by omega))
  have hboM := (groupOrderPrim hord).bound_le
    (show (encGroup ms).size ≤ Y from (Val.size_le_wt _).trans (by omega))
  have hrepw : (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 :=
    outb_wt_reps_le reps
  have hrepw_Z : (Val.list xs).wt ≤ 13 * Z := by
    calc (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 := hrepw
      _ ≤ 13 * (reps.length + 1) ^ 3 * Y ^ 3 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hm23) (hn26.trans (hn6_Y.trans hY_le_Y3))
      _ = 13 * Z := by rw [hZ]; ring
  have hRcardw := wt_card_le R
  have hMcardw := wt_card_le M
  have hquotw : (Val.nat (Nat.card M / Nat.card R)).wt ≤ n ^ 2 + 3 :=
    outb_wt_nat_le (Nat.div_le_self _ _)
  have h0w := wt_nat_le 0
  have h1w := wt_nat_le 1
  have hnw := wt_nat_le n
  have hn1w := wt_nat_le (n + 1)
  have hainw : (Val.list a_in).wt ≤
      2 * ((encGroup rs).wt + (encGroup ms).wt + (Val.list xs).wt) + 7 :=
    wt_list3_le (encGroup rs) (encGroup ms) (.list xs)
  have hcw : c.wt ≤
      2 * ((encGroup rs).wt + (encGroup ms).wt + (Val.list xs).wt +
        (Val.nat (Nat.card R)).wt) + 8 :=
    wt_list4_le (encGroup rs) (encGroup ms) (.list xs) (.nat (Nat.card R))
  have hacc0_w3 : acc0.wt ≤
      2 * ((Val.nat (Nat.card M / Nat.card R)).wt + (Val.nat 0).wt + (Val.nat 0).wt) + 7 :=
    wt_list3_le (.nat (Nat.card M / Nat.card R)) (.nat 0) (.nat 0)
  have hit_argw := wt_list3_le c (.nat (n + 1)) acc0
  have hit_tot : (Val.list [c, .nat (n + 1), acc0]).wt + (n + 1) + 1400 * (n + 1) ^ 6 + 1 ≤
      6000 * (reps.length + 1) ^ 3 * (n + 1) ^ 6 := by
    set Z6 := (reps.length + 1) ^ 3 * (n + 1) ^ 6 with hZ6
    have hZ6_pos : 1 ≤ Z6 := Nat.mul_pos hm13 hn16
    have hn6_Z6 : (n + 1) ^ 6 ≤ Z6 := by
      calc (n + 1) ^ 6 = 1 * (n + 1) ^ 6 := by ring
        _ ≤ Z6 := Nat.mul_le_mul_right _ hm13
    have hrepw_Z6 : (Val.list xs).wt ≤ 13 * Z6 := by
      calc (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 := hrepw
        _ ≤ 13 * (reps.length + 1) ^ 3 * (n + 1) ^ 6 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hm23) hn26
        _ = 13 * Z6 := by rw [hZ6]; ring
    have hgoal_Z6 : 6000 * (reps.length + 1) ^ 3 * (n + 1) ^ 6 = 6000 * Z6 := by
      rw [hZ6]; ring
    rw [hgoal_Z6]
    clear d0 dordR d0' d1' d2' dvR dc dn dn1 dordM ddiv dacc0 dit_arg hit hc_def hacc0_def
    clear_value Z6 Z Y B c acc0 a_in xs R M
    omega
  have hL : loopModK * (n + 1 + 1) *
      ((Val.list [c, .nat (n + 1), acc0]).wt + (n + 1) + 1400 * (n + 1) ^ 6 + 1) ≤
      1200 * Z := by
    have hn1_2 : n + 1 + 1 ≤ 2 * (n + 1) := by omega
    have h1 : 10 ^ 4 * (n + 1) ≤ Y := by
      rw [hY]; exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
    have h2 : (n + 1) ^ 6 ≤ Y ^ 2 := hn6_Y.trans (Nat.le_self_pow (by norm_num) Y)
    calc loopModK * (n + 1 + 1) *
        ((Val.list [c, .nat (n + 1), acc0]).wt + (n + 1) + 1400 * (n + 1) ^ 6 + 1) ≤
        loopModK * (2 * (n + 1)) * (6000 * (reps.length + 1) ^ 3 * (n + 1) ^ 6) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hn1_2) hit_tot
      _ = 1200 * ((reps.length + 1) ^ 3 * ((10 ^ 4 * (n + 1)) * (n + 1) ^ 6)) := by
          simp only [loopModK]; ring
      _ ≤ 1200 * ((reps.length + 1) ^ 3 * (Y * Y ^ 2)) :=
          Nat.mul_le_mul_left 1200 (Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2))
      _ = 1200 * Z := by rw [hZ]; ring
  have hgoal_eq : outbFindCost (normalClosurePrim hnc) (groupOrderPrim hord)
      (membershipPrim hmem) n reps.length =
      (n + 1) * B + B + 10 ^ 6 * Z := by
    simp only [outbFindCost, hB, ← hY, hZ]; ring
  rw [hgoal_eq]
  clear d0 dordR d0' d1' d2' dvR dc dn dn1 dordM ddiv dacc0 dit_arg hit hc_def hacc0_def
  clear_value Z Y B c acc0 a_in xs R M
  omega

end GI.Impl
