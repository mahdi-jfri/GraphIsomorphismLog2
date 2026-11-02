import Workspace.Impl.TermSupSearch

/-!
# T4, the search step: its specification

`supSearch_step`: one step of the search keeps `SupSearchInv` (moving from `i` to `i + 1`), at
cost at most `supSearchCost … n`, when `K` has at most `n²` generators and `i ≤ n`.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

open Classical in
/-- The part after a prime `i ∣ r` is found: Sylow subgroup, normality test, and the new
state. -/
theorem sup_search_prime {hsy : SylowAlgo} {hnc : NormalClosure} {hord : GroupOrder}
    {hmem : Membership} {P : Program} {g mg le jsy jnc jord jm : ℕ}
    (hP : SupSearchAt P g mg le jsy jnc jord jm hsy hnc hord hmem)
    {ks : List (Perm (Fin n))} (hkl : ks.length ≤ n ^ 2) {i r : ℕ} (hi : i ≤ n)
    (hs : SupSieve (gens ks) i r) (hi2 : 2 ≤ i) (hir : i ∣ r) :
    EvalAll P [.list [encGroup ks, .nat i, .list [.nat r, .nat 0, .nat 0, .nat 0]]]
      (supPrimeE mg le jsy jnc jord)
      (fun w c => SupSearchInv (gens ks) (i + 1) w ∧
        c ≤ (sylowPrim hsy).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          (normalClosurePrim hnc).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          (groupOrderPrim hord).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          10 ^ 4 * (n + 1) ^ 6 * (membershipPrim hmem).boundSize (10 ^ 4 * (n + 1) ^ 6) +
          10 ^ 5 * (10 ^ 4 * (n + 1) ^ 6) ^ 3) := by
  unfold supPrimeE
  set acc : Val := .list [.nat r, .nat 0, .nat 0, .nat 0] with hacc
  have hinv : SupSearchInv (gens ks) i acc := Or.inl ⟨r, rfl, hs⟩
  have hKw := wt_encGroup_le_sq hkl
  have haw := sup_search_wt hinv
  have hW3 := wt_list3_le (encGroup ks) (.nat i) acc
  have hiw := wt_nat_le i
  have hn1 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have hn9 : 8 * mkGroupK * (n + 1) ^ 9 ≤ (10 ^ 4 * (n + 1) ^ 6) ^ 2 := by
    have : (n + 1) ^ 9 ≤ (n + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
    have e : (10 ^ 4 * (n + 1) ^ 6) ^ 2 = 10 ^ 8 * (n + 1) ^ 12 := by ring
    simp only [mkGroupK]; omega
  set Y := 10 ^ 4 * (n + 1) ^ 6 with hY
  have hY1 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY2 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := (Val.list [encGroup ks, .nat i, acc]).wt with hWdef
  have hWY : 2 * W + 100 ≤ Y := by omega
  have hrw := sup_wt_nat_le (sup_sieve_le hs)
  have hp := sup_sieve_prime hi2 hir hs
  have hdvd := sup_sieve_dvd hir hs
  -- the Sylow subgroup
  have d0 := Det.arg' (P := P) (vs := [encGroup ks, .nat i, acc]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [encGroup ks, .nat i, acc]) (rest := []) (j := 1) rfl
  have hsa := wt_list2_le (encGroup ks) (.nat i)
  have hss : (Val.list [encGroup ks, .nat i]).size ≤ Y := (Val.size_le_wt _).trans (by omega)
  refine EvalAll.letE (sylow_call hsy hP.sy (Det.mk2 d0 d1) ⟨ks, rfl, rfl⟩ hp hdvd)
    fun v1 c1 h1 => ?_
  obtain ⟨⟨S, hS, hsyl⟩, hc1⟩ := h1
  have hb1 := (sylowPrim hsy).bound_le hss
  -- its group value
  have hnK : (Val.nat n).wt < (encGroup ks).wt := wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have dn1 := Det.get' (Det.arg' (P := P) (vs := [encGroup ks, .nat i, acc]) (rest := [v1])
    (j := 0) rfl) (Det.nat 0) (v := .nat n) rfl
  obtain ⟨ps, hpl, hpg, dP, hPw⟩ := rad_mk_det hP.mg dn1 (Det.var' (P := P) (i := 1) (v := v1) rfl) hS
  have hv1w : v1.wt ≤ 13 * (n + 1) ^ 6 := GensVal.wt_le hS
  have hm1 := wt_list2_le (.nat n) v1
  refine EvalAll.letE dP fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  subst hpg
  -- the normal closure
  have d0' := Det.arg' (P := P) (vs := [encGroup ks, .nat i, acc]) (rest := [v1, encGroup ps])
    (j := 0) rfl
  have hnca := wt_list2_le (encGroup ks) (encGroup ps)
  have hncs : (Val.list [encGroup ks, encGroup ps]).size ≤ Y := (Val.size_le_wt _).trans (by omega)
  refine EvalAll.letE (normalClosure_call hnc hP.nc (Det.mk2 d0' (Det.var' (P := P) (i := 2)
    (v := encGroup ps) rfl)) ⟨ks, rfl, rfl⟩) fun v3 c3 h3 => ?_
  obtain ⟨hNC, hc3⟩ := h3
  have hb3 := (normalClosurePrim hnc).bound_le hncs
  have hv3w : v3.wt ≤ 13 * (n + 1) ^ 6 := GensVal.wt_le hNC
  -- the test
  have dn3 := Det.get' (Det.arg' (P := P) (vs := [encGroup ks, .nat i, acc])
    (rest := [v1, encGroup ps, v3]) (j := 0) rfl) (Det.nat 0) (v := .nat n) rfl
  obtain ⟨cs, hcl, hcg, dC, hCw⟩ := rad_mk_det hP.mg dn3 (Det.var' (P := P) (i := 3) (v := v3) rfl)
    hNC
  have hm3 := wt_list2_le (.nat n) v3
  have hle := le_spec hmem hP.le hP.mem (⟨ps, rfl, rfl⟩ : GroupVal n (encGroup ps) (gens ps)) cs
  have dt := Det.call (Det.mk2 (Det.var' (P := P) (i := 2) (v := encGroup ps) rfl) dC) hle
  have hta := wt_list2_le (encGroup ps) (encGroup cs)
  have hmem1 : (Val.list [encGroup ps, encPerm (1 : Perm (Fin n))]).size ≤ Y := by
    have := wt_list2_le (encGroup ps) (encPerm (1 : Perm (Fin n)))
    have := wt_encPerm_le (1 : Perm (Fin n))
    have : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    exact (Val.size_le_wt _).trans (by omega)
  have hbm := (membershipPrim hmem).bound_le hmem1
  have hT : (Val.list [encGroup ps, encGroup cs]).wt ≤ Y := by omega
  have hT3 : (Val.list [encGroup ps, encGroup cs]).wt ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left hT 3
  have hTm : (Val.list [encGroup ps, encGroup cs]).wt *
      (membershipPrim hmem).bound (.list [encGroup ps, encPerm (1 : Perm (Fin n))]) ≤
      Y * (membershipPrim hmem).boundSize Y := Nat.mul_le_mul hT hbm
  -- the two results
  have d2 := Det.arg' (P := P) (vs := [encGroup ks, .nat i, acc]) (rest := [v1, encGroup ps, v3])
    (j := 2) rfl
  have dr := Det.get' d2 (Det.nat 0) (v := .nat r) rfl
  have dord := groupOrder_call hord hP.ord (Det.var' (P := P)
    (env := [Val.list [encGroup ks, .nat i, acc], v1, encGroup ps, v3]) (i := 2)
    (v := encGroup ps) rfl)
    (⟨ps, rfl, rfl⟩ : GroupVal n (encGroup ps) (gens ps))
  have hbo := (groupOrderPrim hord).bound_le (show (encGroup ps).size ≤ Y from
    (Val.size_le_wt _).trans (by omega))
  have dnorm := Det.mk4 (Det.arith (op := .div) dr dord) (Det.nat 0) (Det.nat 0) (Det.nat 0)
  have d1' := Det.arg' (P := P) (vs := [encGroup ks, .nat i, acc]) (rest := [v1, encGroup ps, v3])
    (j := 1) rfl
  have dnn := Det.mk4 (Det.nat 0) (Det.nat 1) d1' (Det.var' (P := P)
    (env := [Val.list [encGroup ks, .nat i, acc], v1, encGroup ps, v3]) (i := 2)
    (v := encGroup ps) rfl)
  have hrK : r / Nat.card (gens ps) ≤ Nat.card (gens ks) :=
    (Nat.div_le_self _ _).trans (sup_sieve_le hs)
  have hw4 := wt_list4_le (.nat (BinOp.div.eval r (Nat.card (gens ps)))) (.nat 0) (.nat 0) (.nat 0)
  have hw4' := wt_list4_le (.nat 0) (.nat 1) (.nat i) (encGroup ps)
  have hrw' : (Val.nat (BinOp.div.eval r (Nat.card (gens ps)))).wt ≤ n ^ 2 + 3 :=
    sup_wt_nat_le hrK
  have hbw := wt_boolVal_le (decide (gens cs ≤ gens ps))
  have h0w := wt_nat_le 0
  have h1w := wt_nat_le 1
  have hcw := wt_card_le (gens ps)
  have hn2 : n ^ 2 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  refine (Det.ite' dt dnorm dnn).post fun c hc => ⟨?_, ?_⟩
  · have hnc' : gens cs ≤ gens ps ↔ SupNormIn (gens ks) (gens ps) :=
      sup_normIn_iff (hsyl.1) hcg
    by_cases hN : gens cs ≤ gens ps
    · simp only [hN, decide_true, Bool.toNat_true, one_ne_zero, if_false]
      exact Or.inl ⟨_, rfl, sup_sieve_next hp hir hs hsyl (hnc'.mp hN)⟩
    · simp only [hN, decide_false, Bool.toNat_false, if_true]
      exact Or.inr ⟨i, ps, rfl, hpl, hp, hi, hsyl, fun h => hN (hnc'.mpr h)⟩
  · have hmax1 : max (Val.list [.nat (BinOp.div.eval r (Nat.card (gens ps))), .nat 0, .nat 0,
        .nat 0]).wt (Val.list [.nat 0, .nat 1, .nat i, encGroup ps]).wt ≤ Y := by
      apply max_le <;> omega
    have hres : (if (decide (gens cs ≤ gens ps)).toNat = 0 then
        Val.list [.nat 0, .nat 1, .nat i, encGroup ps] else
        Val.list [.nat (BinOp.div.eval r (Nat.card (gens ps))), .nat 0, .nat 0, .nat 0]).wt ≤ Y := by
      split
      · exact (le_max_right _ _).trans hmax1
      · exact (le_max_left _ _).trans hmax1
    generalize (if (decide (gens cs ≤ gens ps)).toNat = 0 then
        Val.list [.nat 0, .nat 1, .nat i, encGroup ps] else
        Val.list [.nat (BinOp.div.eval r (Nat.card (gens ps))), .nat 0, .nat 0, .nat 0]) = res at hres ⊢
    clear dP d0 d1 d0' dn1 dn3 dC dt dr dord dnorm d1' dnn d2 hle
    clear_value Y W
    omega

/-- **One step of the search** keeps `SupSearchInv`, from `i` to `i + 1`. -/
theorem supSearch_step {hsy : SylowAlgo} {hnc : NormalClosure} {hord : GroupOrder}
    {hmem : Membership} {P : Program} {g mg le jsy jnc jord jm : ℕ}
    (hP : SupSearchAt P g mg le jsy jnc jord jm hsy hnc hord hmem)
    {ks : List (Perm (Fin n))} (hkl : ks.length ≤ n ^ 2) {i : ℕ} (hi : i ≤ n) {acc : Val}
    (hinv : SupSearchInv (gens ks) i acc) :
    FunAll P g (.list [encGroup ks, .nat i, acc]) (fun w c => SupSearchInv (gens ks) (i + 1) w ∧
      c ≤ supSearchCost (sylowPrim hsy) (normalClosurePrim hnc) (groupOrderPrim hord)
        (membershipPrim hmem) n) := by
  have hKw := wt_encGroup_le_sq hkl
  have haw := sup_search_wt hinv
  have hW3 := wt_list3_le (encGroup ks) (.nat i) acc
  have hiw := wt_nat_le i
  have hn1 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  set Y := 10 ^ 4 * (n + 1) ^ 6 with hY
  have hY1 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY2 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  set W := (Val.list [encGroup ks, .nat i, acc]).wt with hWdef
  have hWY : 2 * W + 100 ≤ Y := by omega
  -- the returned accumulator, in the trivial branches
  have dacc := Det.arg' (P := P) (vs := [encGroup ks, .nat i, acc]) (rest := []) (j := 2) rfl
  have hsame : ∀ (cc : ℕ), cc ≤ 4 * W + 20 → SupSearchInv (gens ks) (i + 1) acc →
      EvalAll P [.list [encGroup ks, .nat i, acc]] (arg 2)
        (fun w c => SupSearchInv (gens ks) (i + 1) w ∧ c ≤ Y) := fun _ _ hI =>
    dacc.post fun c hc => ⟨hI, by omega⟩
  have hB : ∀ c, c ≤ (sylowPrim hsy).boundSize Y + (normalClosurePrim hnc).boundSize Y +
      (groupOrderPrim hord).boundSize Y + Y * (membershipPrim hmem).boundSize Y + 10 ^ 5 * Y ^ 3 →
      c + 3 * (2 * Y + 2) ≤ supSearchCost (sylowPrim hsy) (normalClosurePrim hnc)
        (groupOrderPrim hord) (membershipPrim hmem) n := by
    intro c hc
    unfold supSearchCost
    rw [← hY]
    omega
  set B0 := (sylowPrim hsy).boundSize Y + (normalClosurePrim hnc).boundSize Y +
      (groupOrderPrim hord).boundSize Y + Y * (membershipPrim hmem).boundSize Y + 10 ^ 5 * Y ^ 3
    with hB0
  have hYB : Y ≤ B0 := by omega
  refine FunAll.intro hP.step ?_
  unfold supSearchBody
  rcases hinv with ⟨r, rfl, hs⟩ | ⟨p, ps, rfl, hl, hp, hpn, hsyl, hnn⟩
  · -- still searching
    have hrK := sup_sieve_le hs
    have hrw := sup_wt_nat_le hrK
    have hr0 := Det.get' dacc (Det.nat 1) (v := .nat 0) rfl
    have hc0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    refine (sup_ite (R := fun w c => SupSearchInv (gens ks) (i + 1) w ∧ c ≤ B0 + 2 * (2 * Y + 2))
      hr0 (fun h => absurd rfl h) fun _ => ?_).mono fun w c h => ?_
    rotate_left
    · obtain ⟨ce, ⟨hI, hce⟩, hc⟩ := h
      refine ⟨hI, ?_⟩
      have := hB B0 le_rfl
      have := sup_search_wt hI
      omega
    have d1 := Det.arg' (P := P) (vs := [encGroup ks, .nat i, .list [.nat r, .nat 0, .nat 0, .nat 0]])
      (rest := []) (j := 1) rfl
    have dlt := Det.arith' (op := .lt) d1 (Det.nat (P := P)
      (env := [.list [encGroup ks, .nat i, .list [.nat r, .nat 0, .nat 0, .nat 0]]]) 2) rfl
    have hlt1 : BinOp.lt.eval i 2 ≤ 1 := by simp only [BinOp.eval]; split <;> omega
    refine (sup_ite (R := fun w c => SupSearchInv (gens ks) (i + 1) w ∧ c ≤ B0 + (2 * Y + 2))
      dlt (fun hlt => (hsame 0 (by omega) (Or.inl ⟨r, rfl, sup_sieve_small
        (by by_contra h; simp [BinOp.eval, h] at hlt) hs⟩)).mono fun w c h =>
          ⟨h.1, h.2.trans (by omega)⟩) fun hge => ?_).mono fun w c h => ?_
    rotate_left
    · obtain ⟨ce, ⟨hI, hce⟩, hc⟩ := h
      refine ⟨hI, ?_⟩
      have := sup_search_wt hI
      omega
    have hi2 : 2 ≤ i := by
      by_contra h; simp [BinOp.eval, show i < 2 by omega] at hge
    have dr := Det.get' dacc (Det.nat 0) (v := .nat r) rfl
    have dmod := Det.arith' (op := .mod) dr d1 rfl
    have hm1 : BinOp.mod.eval r i < i := Nat.mod_lt _ (by omega)
    have hn2 : n ^ 2 ≤ (n + 1) ^ 6 :=
      (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    refine (sup_ite (R := fun w c => SupSearchInv (gens ks) (i + 1) w ∧ c ≤ B0)
      dmod (fun hm => (hsame 0 (by omega) (Or.inl ⟨r, rfl, sup_sieve_skip
        (fun hd => hm (by simpa [BinOp.eval] using Nat.mod_eq_zero_of_dvd hd)) hs⟩)).mono
          fun w c h => ⟨h.1, h.2.trans hYB⟩) fun hm => ?_).mono fun w c h => ?_
    rotate_left
    · obtain ⟨ce, ⟨hI, hce⟩, hc⟩ := h
      refine ⟨hI, ?_⟩
      have := sup_search_wt hI
      omega
    exact (sup_search_prime hP hkl hi hs hi2
      (Nat.dvd_of_mod_eq_zero (by simpa [BinOp.eval] using hm))).mono fun w c h => ⟨h.1, h.2⟩
  · -- found
    have hr1 := Det.get' dacc (Det.nat 1) (v := .nat 1) rfl
    refine (Det.ite_pos hr1 one_ne_zero dacc).post fun c hc => ⟨Or.inr ⟨p, ps, rfl, hl, hp, hpn,
      hsyl, hnn⟩, ?_⟩
    have := hB 0 (Nat.zero_le _)
    have := wt_nat_le 1
    omega

end GI.Impl
