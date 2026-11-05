module

public import Workspace.Impl.VsPBas
public import Workspace.Impl.VsWProgEig

@[expose] public section

/-!
# The elements `∏ b_l^{c_l}`, `c_l < r`

`vsPEnum r B` lists the products `b_0^{c_0} ⋯ b_{t-1}^{c_{t-1}}` for all `c ∈ [0, r)^t`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

/-- The enumeration. -/
def vsPEnum {n : ℕ} (r : ℕ) (B : List (Perm (Fin n))) : List (Perm (Fin n)) :=
  B.foldl (fun E b => E.flatMap fun e => (List.range r).map fun c => e * b ^ c) [1]

theorem vsPEnum_length {n : ℕ} (r : ℕ) (B : List (Perm (Fin n))) :
    (vsPEnum r B).length = r ^ B.length := by
  unfold vsPEnum
  have key : ∀ (E : List (Perm (Fin n))) (B : List (Perm (Fin n))),
      (B.foldl (fun E b => E.flatMap fun e => (List.range r).map fun c => e * b ^ c) E).length =
        E.length * r ^ B.length := by
    intro E B
    induction B generalizing E with
    | nil => simp
    | cons b B ih =>
      rw [List.foldl_cons, ih, List.length_flatMap]
      simp only [List.length_map, List.length_range, List.length_cons, pow_succ, List.map_const',
        List.sum_replicate, smul_eq_mul]
      ring
  rw [key]; simp

/-- On `[[e, b, 1], c]`: `e * b^c`. -/
def vsPEItemE (pow comp : ℕ) : Expr :=
  .call comp (mk2 (.get (arg 0) (.nat 0))
    (.call pow (mk4 (.nat 0) (.get (arg 0) (.nat 1)) (arg 1) (.get (arg 0) (.nat 2)))))

/-- On `[[b, 1, R], e]`: the list `[e * b^c]_{c < r}` (`R = range r`). -/
def vsPEMidE (mpI : ℕ) : Expr :=
  .call mpI (mk2 (mk3 (arg 1) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))) (.get (arg 0) (.nat 2)))

/-- On `[[1, R], E, b]`: the joined list. -/
def vsPEStepE (mpM cat : ℕ) : Expr :=
  .call cat (.call mpM (mk2 (mk3 (arg 2) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))) (arg 1)))

/-- On `[r, n, B]`: the enumeration. -/
def vsPEnumE (fo rng : ℕ) : Expr :=
  .letE (.call rng (arg 1))
  (.letE (.call rng (arg 0))
    (.call fo (mk3 (mk2 (.var 1) (.var 2)) (arg 2) (mk1 (.var 1)))))

theorem vsPEItem_spec {P : Program} {f pow comp : ℕ} (hf : P.funs[f]? = some (vsPEItemE pow comp))
    (hpow : P.HasAt pow (vsPPowFuns pow)) (hcomp : P.HasAt comp (composeFuns comp))
    {n N : ℕ} (hn : n ≤ N) (e b : Perm (Fin n)) {c : ℕ} (hc : c ≤ N) :
    FunDet P f (.list [.list [encPerm e, encPerm b, encPerm (1 : Perm (Fin n))], .nat c])
      (encPerm (e * b ^ c)) (10 ^ 7 * (N + 1) ^ 5) := by
  set vs := [Val.list [encPerm e, encPerm b, encPerm (1 : Perm (Fin n))], .nat c]
  have a0 : Det P [.list vs] (arg 0) (.list [encPerm e, encPerm b, encPerm (1 : Perm (Fin n))]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have de := Det.get' a0 (Det.nat 0) (show [encPerm e, encPerm b, encPerm (1 : Perm (Fin n))][0]? =
    some (encPerm e) from rfl)
  have db := Det.get' a0 (Det.nat 1) (show [encPerm e, encPerm b, encPerm (1 : Perm (Fin n))][1]? =
    some (encPerm b) from rfl)
  have d1 := Det.get' a0 (Det.nat 2) (show [encPerm e, encPerm b, encPerm (1 : Perm (Fin n))][2]? =
    some (encPerm (1 : Perm (Fin n))) from rfl)
  have dp := Det.call (Det.mk4 (Det.nat 0) db a1 d1) (vsPPow_spec hpow b 1 c)
  rw [mul_one] at dp
  have dc := Det.call (Det.mk2 de dp) (compose_spec hcomp e (b ^ c))
  refine FunDet.intro hf (dc.mono ?_)
  have hp2 : ∀ g : Perm (Fin n), (encPerm g).wt ≤ 4 * (N + 1) ^ 2 := fun g =>
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have w1 := hp2 e
  have w2 := hp2 b
  have w3 := hp2 1
  have w4 := hp2 (b ^ c)
  have w5 := hp2 (e * b ^ c)
  have wc := wt_nat_le c
  have wl3 := wt_list3_le (encPerm e) (encPerm b) (encPerm (1 : Perm (Fin n)))
  have wvs := wt_list2_le (.list [encPerm e, encPerm b, encPerm (1 : Perm (Fin n))]) (.nat c)
  have evs : (Val.list vs).wt = (Val.list [Val.list [encPerm e, encPerm b,
    encPerm (1 : Perm (Fin n))], .nat c]).wt := rfl
  have w4' := wt_list4_le (.nat 0) (encPerm b) (.nat c) (encPerm (1 : Perm (Fin n)))
  have w2' := wt_list2_le (encPerm e) (encPerm (b ^ c))
  have hpc := vsPPowCost_le (n := n) (e := c) (k := N) (by have := vsP_bits_le c; omega)
  have hn3 : (n + 1) ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hpc' : 10 ^ 6 * (N + 1) ^ 2 * (n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 5 := by
    calc 10 ^ 6 * (N + 1) ^ 2 * (n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 2 * (N + 1) ^ 3 :=
          Nat.mul_le_mul_left _ hn3
      _ = 10 ^ 6 * (N + 1) ^ 5 := by ring
  have hpk : permK * (n + 1) ^ 3 ≤ 30000 * (N + 1) ^ 3 := by
    rw [show permK = 30000 from rfl]; omega
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have w0 : (Val.nat 0).wt = 2 := rfl
  omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

theorem vsP_wt_perms {n N : ℕ} (hn : n ≤ N) (l : List (Perm (Fin n))) (hl : l.length ≤ N + 1) :
    (Val.list (l.map encPerm)).wt ≤ 20 * (N + 1) ^ 3 := by
  have hp2 : ∀ g : Perm (Fin n), (encPerm g).wt ≤ 4 * (N + 1) ^ 2 := fun g =>
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have h1 := vs_wt_list_le_of (l.map encPerm) (c := 4 * (N + 1) ^ 2) (by
    intro v hv; obtain ⟨g, -, rfl⟩ := List.mem_map.mp hv; exact hp2 g)
  rw [List.length_map] at h1
  have : l.length * (2 * (4 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (9 * (N + 1) ^ 2) :=
    Nat.mul_le_mul hl (by have := Nat.one_le_pow 2 (N + 1) (by omega); omega)
  have e : (N + 1) * (9 * (N + 1) ^ 2) = 9 * (N + 1) ^ 3 := by ring
  have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The cost of the middle map. -/
def vsPEMidCost (N : ℕ) : ℕ := (N + 1) * (10 ^ 7 * (N + 1) ^ 5) + 10 ^ 5 * (N + 1) ^ 4 +
  1000 * (N + 1) ^ 3

set_option maxHeartbeats 4000000 in
theorem vsPEMid_spec {P : Program} {f mpI it pow comp : ℕ} (hf : P.funs[f]? = some (vsPEMidE mpI))
    (hmp : P.HasAt mpI (mapFuns mpI it)) (hit : P.funs[it]? = some (vsPEItemE pow comp))
    (hpow : P.HasAt pow (vsPPowFuns pow)) (hcomp : P.HasAt comp (composeFuns comp))
    {n N r : ℕ} (hn : n ≤ N) (hr : r ≤ N) (e b : Perm (Fin n)) :
    FunDet P f (.list [.list [encPerm b, encPerm (1 : Perm (Fin n)), natList (List.range r)],
        encPerm e])
      (.list ((List.range r).map fun c => encPerm (e * b ^ c))) (vsPEMidCost N) := by
  set vs := [Val.list [encPerm b, encPerm (1 : Perm (Fin n)), natList (List.range r)], encPerm e]
  have a0 : Det P [.list vs] (arg 0)
      (.list [encPerm b, encPerm (1 : Perm (Fin n)), natList (List.range r)]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have db := Det.get' a0 (Det.nat 0) (show [encPerm b, encPerm (1 : Perm (Fin n)),
    natList (List.range r)][0]? = some (encPerm b) from rfl)
  have d1 := Det.get' a0 (Det.nat 1) (show [encPerm b, encPerm (1 : Perm (Fin n)),
    natList (List.range r)][1]? = some (encPerm (1 : Perm (Fin n))) from rfl)
  have dR := Det.get' a0 (Det.nat 2) (show [encPerm b, encPerm (1 : Perm (Fin n)),
    natList (List.range r)][2]? = some (.list ((List.range r).map Val.nat)) from rfl)
  have dm := Det.call (Det.mk2 (Det.mk3 a1 db d1) dR) (vsQ_map hmp (List.range r) Val.nat
    (fun c => encPerm (e * b ^ c)) (fun _ _ h => Val.nat.inj h)
    (c := .list [encPerm e, encPerm b, encPerm (1 : Perm (Fin n))])
    fun c hc => vsPEItem_spec hit hpow hcomp hn e b (by simp at hc; omega))
  refine FunDet.intro hf (dm.mono ?_)
  have hp2 : ∀ g : Perm (Fin n), (encPerm g).wt ≤ 4 * (N + 1) ^ 2 := fun g =>
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have wR : (natList (List.range r)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp; omega)
  have eR : (natList (List.range r)).wt = (Val.list ((List.range r).map Val.nat)).wt := rfl
  have wres : (Val.list ((List.range r).map fun c => encPerm (e * b ^ c))).wt ≤ 20 * (N + 1) ^ 3 := by
    have := vsP_wt_perms hn ((List.range r).map fun c => e * b ^ c) (by simp; omega)
    rw [List.map_map] at this; exact this
  have w1 := hp2 e
  have w2 := hp2 b
  have w3 := hp2 1
  have wl3 := wt_list3_le (encPerm b) (encPerm (1 : Perm (Fin n))) (natList (List.range r))
  have wvs := wt_list2_le (.list [encPerm b, encPerm (1 : Perm (Fin n)), natList (List.range r)])
    (encPerm e)
  have evs : (Val.list vs).wt = (Val.list [Val.list [encPerm b, encPerm (1 : Perm (Fin n)),
    natList (List.range r)], encPerm e]).wt := rfl
  have wc3 := wt_list3_le (encPerm e) (encPerm b) (encPerm (1 : Perm (Fin n)))
  have wc2 := wt_list2_le (.list [encPerm e, encPerm b, encPerm (1 : Perm (Fin n))])
    (.list ((List.range r).map Val.nat))
  have hsum : (List.range r).length * (10 ^ 7 * (N + 1) ^ 5) ≤ (N + 1) * (10 ^ 7 * (N + 1) ^ 5) :=
    Nat.mul_le_mul_right _ (by simp; omega)
  have hloop : mapK * ((List.range r).length + 1) * ((Val.list [Val.list [encPerm e, encPerm b,
      encPerm (1 : Perm (Fin n))], Val.list ((List.range r).map Val.nat)]).wt +
      (Val.list ((List.range r).map fun c => encPerm (e * b ^ c))).wt + 1) ≤
      10 ^ 5 * (N + 1) ^ 4 := by
    have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (Val.list [Val.list [encPerm e, encPerm b, encPerm (1 : Perm (Fin n))],
        Val.list ((List.range r).map Val.nat)]).wt +
        (Val.list ((List.range r).map fun c => encPerm (e * b ^ c))).wt + 1 ≤ 100 * (N + 1) ^ 3 := by
      omega
    calc mapK * ((List.range r).length + 1) * _ ≤ 1000 * (N + 1) * (100 * (N + 1) ^ 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (by simp; omega)) h2
      _ = 10 ^ 5 * (N + 1) ^ 4 := by ring
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q5 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hmk : mapK = 1000 := rfl
  unfold vsPEMidCost
  linarith

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

/-- One enumeration step. -/
def vsPEStep {n : ℕ} (r : ℕ) (E : List (Perm (Fin n))) (b : Perm (Fin n)) : List (Perm (Fin n)) :=
  E.flatMap fun e => (List.range r).map fun c => e * b ^ c

theorem vsP_flat_map {n r : ℕ} (E : List (Perm (Fin n))) (b : Perm (Fin n)) :
    (E.map fun e => (List.range r).map fun c => encPerm (e * b ^ c)).flatten =
      (E.flatMap fun e => (List.range r).map fun c => e * b ^ c).map encPerm := by
  induction E with
  | nil => rfl
  | cons e E ih => simp [List.flatMap_cons, ih, List.map_map, Function.comp]

/-- The cost of a step. -/
def vsPEStepCost (N : ℕ) : ℕ := (N + 1) * vsPEMidCost N + 2 * 10 ^ 6 * (N + 1) ^ 5 +
  10 ^ 8 * (N + 1) ^ 6 + 10 ^ 4 * (N + 1) ^ 4

set_option maxHeartbeats 4000000 in
theorem vsPEStep_spec {P : Program} {f mpM mid mpI it pow comp cat : ℕ}
    (hf : P.funs[f]? = some (vsPEStepE mpM cat)) (hmpM : P.HasAt mpM (mapFuns mpM mid))
    (hmid : P.funs[mid]? = some (vsPEMidE mpI))
    (hmp : P.HasAt mpI (mapFuns mpI it)) (hit : P.funs[it]? = some (vsPEItemE pow comp))
    (hpow : P.HasAt pow (vsPPowFuns pow)) (hcomp : P.HasAt comp (composeFuns comp))
    (hcat : P.HasAt cat (vsWFlatFuns cat))
    {n N r : ℕ} (hn : n ≤ N) (hr : r ≤ N) {E : List (Perm (Fin n))} (b : Perm (Fin n))
    (hE : E.length * r ≤ N) (hEl : E.length ≤ N) :
    FunDet P f (.list [.list [encPerm (1 : Perm (Fin n)), natList (List.range r)],
        .list (E.map encPerm), encPerm b])
      (.list ((vsPEStep r E b).map encPerm)) (vsPEStepCost N) := by
  set vs := [Val.list [encPerm (1 : Perm (Fin n)), natList (List.range r)], .list (E.map encPerm),
    encPerm b]
  have a0 : Det P [.list vs] (arg 0) (.list [encPerm (1 : Perm (Fin n)), natList (List.range r)]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have a2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have d1 := Det.get' a0 (Det.nat 0) (show [encPerm (1 : Perm (Fin n)), natList (List.range r)][0]? =
    some (encPerm (1 : Perm (Fin n))) from rfl)
  have dR := Det.get' a0 (Det.nat 1) (show [encPerm (1 : Perm (Fin n)), natList (List.range r)][1]? =
    some (natList (List.range r)) from rfl)
  have dm := Det.call (Det.mk2 (Det.mk3 a2 d1 dR) a1) (vsQ_map hmpM E encPerm
    (fun e => .list ((List.range r).map fun c => encPerm (e * b ^ c))) encPerm_injective
    (c := .list [encPerm b, encPerm (1 : Perm (Fin n)), natList (List.range r)])
    fun e _ => vsPEMid_spec hmid hmp hit hpow hcomp hn hr e b)
  set xss := E.map fun e => (List.range r).map fun c => encPerm (e * b ^ c)
  have exs : Val.list (E.map fun e => Val.list ((List.range r).map fun c => encPerm (e * b ^ c))) =
      Val.list (xss.map Val.list) := by simp [xss]
  rw [exs] at dm
  have hflat : xss.flatten = (vsPEStep r E b).map encPerm := vsP_flat_map E b
  have hlen : (vsPEStep r E b).length = E.length * r := by
    simp [vsPEStep, List.length_flatMap, List.map_const', List.sum_replicate]
  have wflat : (Val.list xss.flatten).wt ≤ 20 * (N + 1) ^ 3 := by
    rw [hflat]; exact vsP_wt_perms hn _ (by omega)
  have wxss : (Val.list (xss.map Val.list)).wt ≤ 100 * (N + 1) ^ 4 := by
    have h1 := vs_wt_list_le_of (xss.map Val.list) (c := 20 * (N + 1) ^ 3) (by
      intro v hv
      simp only [xss, List.map_map, List.mem_map, Function.comp] at hv
      obtain ⟨e, -, rfl⟩ := hv
      have := vsP_wt_perms hn ((List.range r).map fun c => e * b ^ c) (by simp; omega)
      rw [List.map_map] at this; exact this)
    rw [List.length_map] at h1
    have hxl : xss.length = E.length := by simp [xss]
    rw [hxl] at h1
    have : E.length * (2 * (20 * (N + 1) ^ 3) + 1) ≤ (N + 1) * (41 * (N + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 3 (N + 1) (by omega); omega)
    have e : (N + 1) * (41 * (N + 1) ^ 3) = 41 * (N + 1) ^ 4 := by ring
    have : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hq3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have dc := Det.call dm (vsWConcat_spec hcat xss (N := N) (by simp [xss]; omega)
    (fun xs hxs => by
      simp only [xss, List.mem_map] at hxs
      obtain ⟨e, -, rfl⟩ := hxs; simp; omega)
    (by omega) (by omega))
  rw [hflat] at dc
  refine FunDet.intro hf (dc.mono ?_)
  have hp2 : ∀ g : Perm (Fin n), (encPerm g).wt ≤ 4 * (N + 1) ^ 2 := fun g =>
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have wE := vsP_wt_perms hn E (by omega)
  have wR : (natList (List.range r)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp; omega)
  have wb := hp2 b
  have w1 := hp2 1
  have wc2 := wt_list2_le (encPerm (1 : Perm (Fin n))) (natList (List.range r))
  have wvs := wt_list3_le (.list [encPerm (1 : Perm (Fin n)), natList (List.range r)])
    (.list (E.map encPerm)) (encPerm b)
  have evs : (Val.list vs).wt = (Val.list [Val.list [encPerm (1 : Perm (Fin n)),
    natList (List.range r)], .list (E.map encPerm), encPerm b]).wt := rfl
  have wc3 := wt_list3_le (encPerm b) (encPerm (1 : Perm (Fin n))) (natList (List.range r))
  have wcc := wt_list2_le (.list [encPerm b, encPerm (1 : Perm (Fin n)), natList (List.range r)])
    (.list (E.map encPerm))
  have hsum : E.length * vsPEMidCost N ≤ (N + 1) * vsPEMidCost N :=
    Nat.mul_le_mul_right _ (by omega)
  have wres := vsP_wt_perms hn (vsPEStep r E b) (by omega)
  have hloop : mapK * (E.length + 1) * ((Val.list [Val.list [encPerm b,
      encPerm (1 : Perm (Fin n)), natList (List.range r)], .list (E.map encPerm)]).wt +
      (Val.list (xss.map Val.list)).wt + 1) ≤ 2 * 10 ^ 6 * (N + 1) ^ 5 := by
    have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (Val.list [Val.list [encPerm b, encPerm (1 : Perm (Fin n)), natList (List.range r)],
        .list (E.map encPerm)]).wt + (Val.list (xss.map Val.list)).wt + 1 ≤ 2000 * (N + 1) ^ 4 := by
      omega
    calc mapK * (E.length + 1) * _ ≤ 1000 * (N + 1) * (2000 * (N + 1) ^ 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (by omega)) h2
      _ = 2 * 10 ^ 6 * (N + 1) ^ 5 := by ring
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hmk : mapK = 1000 := rfl
  unfold vsPEStepCost

  linarith

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

theorem vsPEnum_take_succ {n r : ℕ} (B : List (Perm (Fin n))) (i : ℕ) (hi : i < B.length) :
    vsPEnum r (B.take (i + 1)) = vsPEStep r (vsPEnum r (B.take i)) B[i] := by
  unfold vsPEnum
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
  rfl

/-- The cost of the enumeration. -/
def vsPEnumCost (N : ℕ) : ℕ := (N + 1) * vsPEStepCost N + 10 ^ 6 * (N + 1) ^ 4 + 10 ^ 5 * (N + 1) ^ 3

set_option maxHeartbeats 4000000 in
theorem vsPEnum_spec {P : Program} {f fo st mpM mid mpI it pow comp cat rng : ℕ}
    (hf : P.funs[f]? = some (vsPEnumE fo rng)) (hfo : P.HasAt fo (foldlFuns fo st))
    (hst : P.funs[st]? = some (vsPEStepE mpM cat)) (hmpM : P.HasAt mpM (mapFuns mpM mid))
    (hmid : P.funs[mid]? = some (vsPEMidE mpI))
    (hmp : P.HasAt mpI (mapFuns mpI it)) (hit : P.funs[it]? = some (vsPEItemE pow comp))
    (hpow : P.HasAt pow (vsPPowFuns pow)) (hcomp : P.HasAt comp (composeFuns comp))
    (hcat : P.HasAt cat (vsWFlatFuns cat)) (hrng : P.HasAt rng (rangeFuns rng))
    {n N r : ℕ} (hn : n ≤ N) (hr1 : 1 ≤ r) (hr : r ≤ N) {B : List (Perm (Fin n))}
    (hB : r ^ B.length ≤ N) (hBl : B.length ≤ N) :
    FunDet P f (.list [.nat r, .nat n, .list (B.map encPerm)]) (.list ((vsPEnum r B).map encPerm))
      (vsPEnumCost N) := by
  have hpow' : ∀ i ≤ B.length, r ^ i ≤ N := fun i hi =>
    (Nat.pow_le_pow_right hr1 hi).trans hB
  have hlen : ∀ i, (vsPEnum r (B.take i)).length = r ^ (min i B.length) := by
    intro i; rw [vsPEnum_length, List.length_take]
  set c := Val.list [encPerm (1 : Perm (Fin n)), natList (List.range r)]
  have hM : ∀ i acc, i ≤ (B.map encPerm).length →
      acc = Val.list ((vsPEnum r (B.take i)).map encPerm) → acc.wt ≤ 20 * (N + 1) ^ 3 := by
    rintro i acc hi rfl
    rw [List.length_map] at hi
    have := hlen i
    rw [Nat.min_eq_left hi] at this
    exact vsP_wt_perms hn _ (by rw [this]; have := hpow' i hi; omega)
  have hstep : ∀ i acc (hi : i < (B.map encPerm).length),
      acc = Val.list ((vsPEnum r (B.take i)).map encPerm) →
      FunAll P st (.list [c, acc, (B.map encPerm)[i]]) (fun w cost =>
        w = Val.list ((vsPEnum r (B.take (i + 1))).map encPerm) ∧ cost ≤ vsPEStepCost N) := by
    rintro i acc hi rfl
    have hi' : i < B.length := by simpa using hi
    have e : (B.map encPerm)[i] = encPerm B[i] := by simp
    rw [e]
    have hl := hlen i
    rw [Nat.min_eq_left hi'.le] at hl
    have hE : (vsPEnum r (B.take i)).length * r ≤ N := by
      rw [hl, ← pow_succ]; exact hpow' (i + 1) hi'
    have hEl : (vsPEnum r (B.take i)).length ≤ N := by rw [hl]; exact hpow' i hi'.le
    refine FunAll.mono (vsPEStep_spec hst hmpM hmid hmp hit hpow hcomp hcat hn hr B[i] hE hEl)
      fun w cost hw => ⟨?_, hw.2⟩
    rw [hw.1, vsPEnum_take_succ B i hi']
  have hfold := foldl_spec hfo (c := c) (xs := B.map encPerm)
    (acc0 := Val.list [encPerm (1 : Perm (Fin n))])
    (Inv := fun i acc => acc = Val.list ((vsPEnum r (B.take i)).map encPerm))
    (M := 20 * (N + 1) ^ 3) (B := fun _ => vsPEStepCost N) (by simp [vsPEnum]) hM hstep
  set vs := [Val.nat r, .nat n, .list (B.map encPerm)]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have d1 := Det.call a1 (GI.Lang.range_det hrng n)
  have b0 := Det.arg' (P := P) (vs := vs) (rest := [encPerm (1 : Perm (Fin n))]) (j := 0) rfl
  have dR := Det.call b0 ((vsP_range_det hrng r).mono fun w c hw => ⟨hw.1, hw.2⟩)
  set E2 := [Val.list vs, encPerm (1 : Perm (Fin n)), natList (List.range r)]
  have c2 := Det.arg' (P := P) (vs := vs) (rest := [encPerm (1 : Perm (Fin n)),
    natList (List.range r)]) (j := 2) rfl
  have v1 := Det.var' (P := P) (env := E2) (i := 1) rfl
  have v2 := Det.var' (P := P) (env := E2) (i := 2) rfl
  have dF := Det.call (Det.mk3 (Det.mk2 v1 v2) c2 (Det.mk1 v1))
    ((hfold).mono fun w c hw => ⟨hw.1, hw.2⟩)
  rw [List.length_map, List.take_length] at dF
  refine FunDet.intro hf ((Det.letE d1 (Det.letE dR dF)).mono ?_)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map]
  have h1 : B.length * vsPEStepCost N ≤ (N + 1) * vsPEStepCost N := Nat.mul_le_mul_right _ (by omega)
  have hp2 : ∀ g : Perm (Fin n), (encPerm g).wt ≤ 4 * (N + 1) ^ 2 := fun g =>
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have wB := vsP_wt_perms hn B (by omega)
  have wR : (natList (List.range r)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp; omega)
  have w1 := hp2 1
  have wr := wt_nat_le r
  have wn := wt_nat_le n
  have wvs := wt_list3_le (.nat r) (.nat n) (.list (B.map encPerm))
  have evs : (Val.list vs).wt = (Val.list [Val.nat r, .nat n, .list (B.map encPerm)]).wt := rfl
  have wc := wt_list2_le (encPerm (1 : Perm (Fin n))) (natList (List.range r))
  have ec : c.wt = (Val.list [encPerm (1 : Perm (Fin n)), natList (List.range r)]).wt := rfl
  have w0 := wt_list1_le (encPerm (1 : Perm (Fin n)))
  have w3 := wt_list3_le c (.list (B.map encPerm)) (.list [encPerm (1 : Perm (Fin n))])
  have hres := vsP_wt_perms hn (vsPEnum r B) (by rw [vsPEnum_length]; omega)
  have hrng := vsP_rng_le (m := r) (N := N) hr
  have hr8 : 8000 * (n + 1) ^ 3 ≤ 8000 * (N + 1) ^ 3 := by
    have := Nat.pow_le_pow_left (show n + 1 ≤ N + 1 by omega) 3; omega
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hl2 : loopModK * (B.length + 1) * ((Val.list [c, .list (B.map encPerm),
      .list [encPerm (1 : Perm (Fin n))]]).wt + B.length + 20 * (N + 1) ^ 3 + 1) ≤
      10 ^ 6 * (N + 1) ^ 4 := by
    have h2 : (Val.list [c, .list (B.map encPerm), .list [encPerm (1 : Perm (Fin n))]]).wt +
        B.length + 20 * (N + 1) ^ 3 + 1 ≤ 1000 * (N + 1) ^ 3 := by omega
    calc loopModK * (B.length + 1) * _ ≤ 1000 * (N + 1) * (1000 * (N + 1) ^ 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (by omega)) h2
      _ = 10 ^ 6 * (N + 1) ^ 4 := by ring
  have hmk : loopModK = 1000 := rfl
  unfold vsPEnumCost
  linarith

end GI.Impl
