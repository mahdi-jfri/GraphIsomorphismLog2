module

public import Workspace.Impl.TermGlueLabPItem

@[expose] public section

/-!
# The list of one generator's offset (step 5, program)

Step 5 of the label program (proof of Theorem A.23). For a generator `g` of the
supplement, the offset `o(g) = u(g⁻¹)` is the class product of the list
`s_0, …, s_{q-1}, g y_0, …, g y_{q-1}` (`tmGLP_item_u`), where the `s_i` are the row
transporters of the offset program (entries `[j, s_i]`, `tmGLPOff_spec`) and `y` is a blockwise
lift of `g⁻¹` (`tmGLPL1_spec`). `tmGLPXsF ap mg mc` builds this list from
`[g, [[j_i, s_i]], [y_i]]`: a `map` that keeps entry `1`, a `map` that composes with `g` on the
left, and `append`. Cost `tmGLPXsC W = 10^8 (W + 1)^4`.
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encPerm encGroup gens)

variable {n : ℕ}

/-- Entry `1` of a pair, on `[c, x]`. -/
def tmGLPGet1F : Expr := .get (arg 1) (.nat 1)

/-- Composition `c x`, on `[c, x]`. -/
def tmGLPLCmpF (cp : ℕ) : Expr := .call cp (mk2 (arg 0) (arg 1))

/-- **The offset list**, on `[g, [[j_i, s_i]], [y_i]]`. -/
def tmGLPXsF (ap mg mc : ℕ) : Expr :=
  .call ap (mk2 (.call mg (mk2 (.nat 0) (arg 1))) (.call mc (mk2 (arg 0) (arg 2))))

/-- The cost bound. -/
def tmGLPXsC (W : ℕ) : ℕ := 10 ^ 8 * (W + 1) ^ 4

theorem tmGLP_n_lt_encPerm (g : Perm (Fin n)) : n < (encPerm g).wt := by
  have := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (g i))
  simpa [GI.Cited.encPerm] using this

private theorem tmGLP_mulY {a b d c Y k k' : ℕ} (ha : a ≤ d * Y) (hb : b ≤ c * Y ^ k)
    (hk : k + 1 = k') : a * b ≤ (d * c) * Y ^ k' := by
  subst hk
  exact (Nat.mul_le_mul ha hb).trans_eq (by ring)

private theorem tmGLP_pows {Y : ℕ} (hY : 1 ≤ Y) :
    Y ≤ Y ^ 2 ∧ Y ^ 2 ≤ Y ^ 3 ∧ Y ^ 3 ≤ Y ^ 4 ∧ 1 ≤ Y ^ 2 := by
  refine ⟨?_, Nat.pow_le_pow_right hY (by omega), Nat.pow_le_pow_right hY (by omega),
    Nat.one_le_pow _ _ hY⟩
  simpa using Nat.pow_le_pow_right hY (show 1 ≤ 2 by omega)

private theorem tmGLP_xs_ar1 {q W c : ℕ} (hq : q ≤ W)
    (hc : c ≤ q * (5 * W + 31) +
      1000 * (q + 1) * (2 * W + 10 + (2 * (q * (4 * (W + 1) ^ 2)) + q + 4) + 1)) :
    c ≤ 10 ^ 5 * (W + 1) ^ 4 := by
  obtain ⟨Y, hY⟩ : ∃ Y, W + 1 = Y := ⟨_, rfl⟩
  rw [hY] at hc ⊢
  obtain ⟨p1, p2, p3, p0⟩ := tmGLP_pows (show 1 ≤ Y by omega)
  have a1 : q * (5 * W + 31) ≤ (1 * 36) * Y ^ 2 :=
    tmGLP_mulY (by omega) (by rw [pow_one]; omega) rfl
  have a2 : q * (4 * Y ^ 2) ≤ (1 * 4) * Y ^ 3 := tmGLP_mulY (by omega) le_rfl rfl
  have hS : 2 * W + 10 + (2 * (q * (4 * Y ^ 2)) + q + 4) + 1 ≤ 26 * Y ^ 3 := by omega
  have a3 : 1000 * (q + 1) * (2 * W + 10 + (2 * (q * (4 * Y ^ 2)) + q + 4) + 1) ≤
      (1000 * 26) * Y ^ 4 := tmGLP_mulY (by omega) hS rfl
  omega

private theorem tmGLP_xs_ar2 {q W B c Y : ℕ} (hq : q ≤ W) (hY : Y = (W + 1) ^ 3)
    (hB : B ≤ 24 * W + 56 + 30000 * Y + 4 * (W + 1) ^ 2 + 1)
    (hc : c ≤ q * B + 1000 * (q + 1) * (2 * (W + W) + 6 + (2 * (q * (4 * (W + 1) ^ 2)) + q + 4) + 1)) :
    c ≤ 10 ^ 6 * (W + 1) ^ 4 := by
  subst hY
  obtain ⟨Y, hY⟩ : ∃ Y, W + 1 = Y := ⟨_, rfl⟩
  rw [hY] at hc hB ⊢
  obtain ⟨p1, p2, p3, p0⟩ := tmGLP_pows (show 1 ≤ Y by omega)
  have hB' : B ≤ 30085 * Y ^ 3 := by omega
  have a1 : q * B ≤ (1 * 30085) * Y ^ 4 := tmGLP_mulY (by omega) hB' rfl
  have a2 : q * (4 * Y ^ 2) ≤ (1 * 4) * Y ^ 3 := tmGLP_mulY (by omega) le_rfl rfl
  have hS : 2 * (W + W) + 6 + (2 * (q * (4 * Y ^ 2)) + q + 4) + 1 ≤ 30 * Y ^ 3 := by omega
  have a3 : 1000 * (q + 1) * (2 * (W + W) + 6 + (2 * (q * (4 * Y ^ 2)) + q + 4) + 1) ≤
      (1000 * 30) * Y ^ 4 := tmGLP_mulY (by omega) hS rfl
  omega

private theorem tmGLP_xs_ar3 {W q O1 O2 c1 c2 i1 i2 cb ww ca wa : ℕ} (hq : q ≤ W)
    (hO1 : O1 ≤ 2 * (q * (4 * (W + 1) ^ 2)) + q + 4)
    (hO2 : O2 ≤ 2 * (q * (4 * (W + 1) ^ 2)) + q + 4)
    (hi1 : i1 ≤ 10 * W + 40) (hi2 : i2 ≤ 20 * W + 40)
    (hc1 : c1 ≤ 10 ^ 5 * (W + 1) ^ 4) (hc2 : c2 ≤ 10 ^ 6 * (W + 1) ^ 4)
    (hwa : wa ≤ 2 * (O1 + O2) + 6)
    (hww : ww ≤ 2 * ((q + q) * (4 * (W + 1) ^ 2)) + (q + q) + 4)
    (hcb : cb ≤ 1000 * (q + 1) * (wa + q + (2 * ((q + q) * (4 * (W + 1) ^ 2)) + (q + q) + 4) + 1))
    (hca : ca ≤ i1 + 2 * c1 + 1 + (i2 + 2 * c2 + 1) + 2 * wa + 7) :
    ca + cb + ww + 1 ≤ tmGLPXsC W := by
  unfold tmGLPXsC
  obtain ⟨Y, hY⟩ : ∃ Y, W + 1 = Y := ⟨_, rfl⟩
  rw [hY] at hO1 hO2 hc1 hc2 hww hcb ⊢
  obtain ⟨p1, p2, p3, p0⟩ := tmGLP_pows (show 1 ≤ Y by omega)
  have a2 : q * (4 * Y ^ 2) ≤ (1 * 4) * Y ^ 3 := tmGLP_mulY (by omega) le_rfl rfl
  have a4 : (q + q) * (4 * Y ^ 2) ≤ (2 * 4) * Y ^ 3 := tmGLP_mulY (by omega) le_rfl rfl
  have hS : wa + q + (2 * ((q + q) * (4 * Y ^ 2)) + (q + q) + 4) + 1 ≤ 100 * Y ^ 3 := by omega
  have a3 : 1000 * (q + 1) * (wa + q + (2 * ((q + q) * (4 * Y ^ 2)) + (q + q) + 4) + 1) ≤
      (1000 * 100) * Y ^ 4 := tmGLP_mulY (by omega) hS rfl
  omega

/-- **The offset list.** -/
theorem tmGLPXs_spec {P : Program} {f ap mg g1 mc lc cp : ℕ}
    (hf : P.funs[f]? = some (tmGLPXsF ap mg mc)) (hap : P.HasAt ap (appendFuns ap))
    (hmg : P.HasAt mg (mapFuns mg g1)) (hg1 : P.funs[g1]? = some tmGLPGet1F)
    (hmc : P.HasAt mc (mapFuns mc lc)) (hlc : P.funs[lc]? = some (tmGLPLCmpF cp))
    (hcp : P.HasAt cp (composeFuns cp)) {q : ℕ} (g : Perm (Fin n)) (J : Fin q → ℕ)
    (s y : Fin q → Perm (Fin n)) :
    FunDet P f (.list [encPerm g, .list ((List.finRange q).map fun k => .list [.nat (J k), encPerm (s k)]),
        .list ((List.finRange q).map fun k => encPerm (y k))])
      (.list ((List.ofFn s ++ List.ofFn fun k => g * y k).map encPerm))
      (tmGLPXsC (Val.list [encPerm g,
        .list ((List.finRange q).map fun k => .list [.nat (J k), encPerm (s k)]),
        .list ((List.finRange q).map fun k => encPerm (y k))]).wt) := by
  set l1 : List Val := (List.finRange q).map fun k => .list [.nat (J k), encPerm (s k)] with hl1
  set l2 : List Val := (List.finRange q).map fun k => encPerm (y k) with hl2
  set a : Val := .list [encPerm g, .list l1, .list l2] with ha
  set W := a.wt with hW
  have wg : (encPerm g).wt < W := wt_le_wt_list (by simp)
  have w1 : (Val.list l1).wt < W := wt_le_wt_list (by simp)
  have w2 : (Val.list l2).wt < W := wt_le_wt_list (by simp)
  have hq1 : q < W := by
    have h1 := length_lt_wt_list l1
    have h2 : l1.length = q := by rw [hl1, List.length_map, List.length_finRange]
    omega
  have hnW : n < W := (tmGLP_n_lt_encPerm g).trans wg
  have gA : ∀ (j : ℕ) (v : Val), [encPerm g, .list l1, .list l2][j]? = some v →
      Det P [a] (arg j) v (2 * W + j + 5) := fun j v h => Det.arg' h
  clear_value l1 l2 a W
  -- the first map: entry `1` of every pair
  have hR1 : ∀ x ∈ l1, FunAll P g1 (.list [.nat 0, x]) (fun w cost =>
      (∀ j (t : Perm (Fin n)), x = .list [.nat j, encPerm t] → w = encPerm t) ∧ cost ≤ 5 * W + 31) := by
    intro x hx
    have hxw : x.wt < W := (wt_le_wt_list hx).trans w1
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp (hl1 ▸ hx)
    have wx : (encPerm (s k)).wt < (Val.list [.nat (J k), encPerm (s k)]).wt :=
      wt_le_wt_list (by simp)
    have w0 := wt_list2_le (.nat 0) (.list [.nat (J k), encPerm (s k)])
    have wn := wt_nat_le 0
    have d1 := Det.get' (Det.arg' (P := P) (vs := [.nat 0, .list [.nat (J k), encPerm (s k)]])
      (rest := []) (j := 1) rfl) (Det.nat 1) (vs := [.nat (J k), encPerm (s k)])
      (v := encPerm (s k)) rfl
    refine FunAll.intro hg1 (d1.post fun c hc => ⟨fun j t h => ?_, by omega⟩)
    simp only [Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at h
    rw [encPerm_injective h.2]
  have m1 := map_spec hmg hR1
  have e1 : ∀ ws, List.Forall₂ (fun x w => ∀ j (t : Perm (Fin n)), x = .list [.nat j, encPerm t] → w = encPerm t)
      l1 ws → ws = (List.finRange q).map fun k => encPerm (s k) := fun ws hws => by
    rw [hl1] at hws
    exact forall₂_map_eq (fun k _ w hw => hw _ _ rfl) hws
  -- the second map: compose with `g`
  have hR2 : ∀ x ∈ l2, FunAll P lc (.list [encPerm g, x]) (fun w cost =>
      (∀ t : Perm (Fin n), x = encPerm t → w = encPerm (g * t)) ∧
        cost ≤ 24 * W + 56 + permK * (W + 1) ^ 3 + 4 * (W + 1) ^ 2 + 1) := by
    intro x hx
    have hxw : x.wt < W := (wt_le_wt_list hx).trans w2
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp (hl2 ▸ hx)
    have w0 := wt_list2_le (encPerm g) (encPerm (y k))
    have d0 := Det.arg' (P := P) (vs := [encPerm g, encPerm (y k)]) (rest := []) (j := 0) rfl
    have d1 := Det.arg' (P := P) (vs := [encPerm g, encPerm (y k)]) (rest := []) (j := 1) rfl
    have dm := Det.mk2 d0 d1
    have dc := Det.call dm (compose_spec hcp g (y k))
    have hp : permK * (n + 1) ^ 3 ≤ permK * (W + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have hw := wt_encPerm_le (g * y k)
    have hp2 : 4 * (n + 1) ^ 2 ≤ 4 * (W + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    refine FunAll.intro hlc (dc.post fun c hc => ⟨fun t ht => ?_, by omega⟩)
    rw [encPerm_injective ht]
  have m2 := map_spec hmc hR2
  have e2 : ∀ ws, List.Forall₂ (fun x w => ∀ t : Perm (Fin n), x = encPerm t → w = encPerm (g * t))
      l2 ws → ws = (List.finRange q).map fun k => encPerm (g * y k) := fun ws hws => by
    rw [hl2] at hws
    exact forall₂_map_eq (fun k _ w hw => hw _ rfl) hws
  -- the two maps
  have hl1q : l1.length = q := by rw [hl1, List.length_map, List.length_finRange]
  have hl2q : l2.length = q := by rw [hl2, List.length_map, List.length_finRange]
  have hB2 : W ≤ 4 * (W + 1) ^ 2 := by nlinarith
  have wO1 : (Val.list ((List.finRange q).map fun k => encPerm (s k))).wt ≤
      2 * (q * (4 * (W + 1) ^ 2)) + q + 4 := by
    have := linWtList (vs := (List.finRange q).map fun k => encPerm (s k)) (B := 4 * (W + 1) ^ 2)
      (fun v hv => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hv
        have := (wt_encPerm_le (s k)).trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 2))
        exact this)
    simpa using this
  have wO2 : (Val.list ((List.finRange q).map fun k => encPerm (g * y k))).wt ≤
      2 * (q * (4 * (W + 1) ^ 2)) + q + 4 := by
    have := linWtList (vs := (List.finRange q).map fun k => encPerm (g * y k)) (B := 4 * (W + 1) ^ 2)
      (fun v hv => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hv
        exact (wt_encPerm_le _).trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 2)))
    simpa using this
  have f1 : FunDet P mg (.list [.nat 0, .list l1]) (.list ((List.finRange q).map fun k => encPerm (s k)))
      (10 ^ 5 * (W + 1) ^ 4) := by
    refine FunAll.mono m1 fun w c ⟨ws, hw, hws, hc⟩ => ?_
    have e := e1 ws hws
    subst e
    refine ⟨hw, tmGLP_xs_ar1 (q := q) hq1.le (hc.trans ?_)⟩
    rw [hw]
    have hsum : (l1.map fun _ => 5 * W + 31).sum = q * (5 * W + 31) := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul, hl1q]
    rw [hsum, hl1q, show mapK = 1000 from rfl]
    have := wt_list2_le (.nat 0) (.list l1)
    have := wt_nat_le 0
    refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
    omega
  have f2 : FunDet P mc (.list [encPerm g, .list l2])
      (.list ((List.finRange q).map fun k => encPerm (g * y k))) (10 ^ 6 * (W + 1) ^ 4) := by
    refine FunAll.mono m2 fun w c ⟨ws, hw, hws, hc⟩ => ?_
    have e := e2 ws hws
    subst e
    refine ⟨hw, tmGLP_xs_ar2 (q := q) hq1.le rfl le_rfl (hc.trans ?_)⟩
    rw [hw]
    have hsum : (l2.map fun _ => 24 * W + 56 + permK * (W + 1) ^ 3 + 4 * (W + 1) ^ 2 + 1).sum =
        q * (24 * W + 56 + 30000 * (W + 1) ^ 3 + 4 * (W + 1) ^ 2 + 1) := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul, hl2q]; rfl
    rw [hsum, hl2q, show mapK = 1000 from rfl]
    have := wt_list2_le (encPerm g) (.list l2)
    refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
    omega
  -- the program
  have d0 := Det.nat (P := P) (env := [a]) 0
  have da1 := gA 1 (.list l1) rfl
  have da2 := gA 2 (.list l2) rfl
  have da0 := gA 0 (encPerm g) rfl
  have i1 := Det.mk2 d0 da1
  have i2 := Det.mk2 da0 da2
  have wi1 := wt_list2_le (.nat 0) (.list l1)
  have wi2 := wt_list2_le (encPerm g) (.list l2)
  have wn := wt_nat_le 0
  have c1 := tmGLP_call_le i1 (A := 10 * W + 40) (by omega) f1 le_rfl
  have c2 := tmGLP_call_le i2 (A := 20 * W + 40) (by omega) f2 le_rfl
  have dm := Det.mk2 c1.1 c2.1
  have hcat := append_spec hap ((List.finRange q).map fun k => encPerm (s k))
    ((List.finRange q).map fun k => encPerm (g * y k))
  have ecat : ((List.finRange q).map fun k => encPerm (s k)) ++
      ((List.finRange q).map fun k => encPerm (g * y k)) =
      (List.ofFn s ++ List.ofFn fun k => g * y k).map encPerm := by
    rw [List.map_append, List.map_ofFn, List.map_ofFn, List.ofFn_eq_map, List.ofFn_eq_map]
    rfl
  rw [ecat] at hcat
  have wcat : (Val.list ((List.ofFn s ++ List.ofFn fun k => g * y k).map encPerm)).wt ≤
      2 * ((q + q) * (4 * (W + 1) ^ 2)) + (q + q) + 4 := by
    have := linWtList (vs := (List.ofFn s ++ List.ofFn fun k => g * y k).map encPerm)
      (B := 4 * (W + 1) ^ 2) (fun v hv => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.mp hv
        exact (wt_encPerm_le _).trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 2)))
    simpa [two_mul] using this
  have hcat' : FunDet P ap (.list [.list ((List.finRange q).map fun k => encPerm (s k)),
      .list ((List.finRange q).map fun k => encPerm (g * y k))])
      (.list ((List.ofFn s ++ List.ofFn fun k => g * y k).map encPerm))
      (1000 * (q + 1) * ((Val.list [.list ((List.finRange q).map fun k => encPerm (s k)),
        .list ((List.finRange q).map fun k => encPerm (g * y k))]).wt + q +
        (2 * ((q + q) * (4 * (W + 1) ^ 2)) + (q + q) + 4) + 1)) := by
    refine FunAll.mono hcat fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
    subst hw
    simp only [List.length_map, List.length_finRange, show loopModK = 1000 from rfl] at hc
    exact hc.trans (Nat.mul_le_mul_left _ (by omega))
  have dc := Det.call dm hcat'
  refine FunDet.intro hf (dc.mono ?_)
  exact tmGLP_xs_ar3 hq1.le wO1 wO2 le_rfl le_rfl le_rfl le_rfl
    ((wt_list2_le _ _).trans (by omega)) wcat le_rfl le_rfl
