module

public import Workspace.Assembly.ConvertMath

@[expose] public section

/-!
# The parts of the converter

* `diagMapFuns`: on `[[n, x], [0, …, n - 1]]` with `x` a permutation of `Fin (n * n)`, the list
  of the numbers `proj x i = x (i, i) / n` (`diagMap_spec`, cost at most `100000 (n + 1)^5`).
* `projMapFuns`: on `[[n, [0, …, n - 1]], [g₁, …, g_k]]`, the list of the `proj gⱼ`
  (`projMap_spec`).
* `catFuns`: on `[c, [l₁, …, l_k], acc]` with lists of numbers, the list
  `acc ++ l₁ ++ … ++ l_k` (`cat_spec`).
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### The diagonal of one permutation -/

/-- On `[[n, x], i]`: `x (i + n i) / n`. -/
def diagF : Expr :=
  .arith .div (.get (.get (arg 0) (.nat 1))
      (.arith .add (arg 1) (.arith .mul (.get (arg 0) (.nat 0)) (arg 1))))
    (.get (arg 0) (.nat 0))

theorem diagF_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some diagF)
    (g : Perm (Fin (n * n))) (i : Fin n) :
    FunDet P f (.list [.list [.nat n, encPerm g], .nat i]) (.nat (proj g i))
      (2000 * (n + 1) ^ 4) := by
  set B := Val.list [.nat n, encPerm g] with hB
  set A := Val.list [B, .nat i] with hA
  have g0 : Det P [A] (.get (arg 0) (.nat 0)) (.nat n) _ :=
    Det.get' (Det.arg' (vs := [B, .nat i]) (rest := []) (j := 0) rfl) (Det.nat 0)
      (show [Val.nat n, encPerm g][0]? = some (.nat n) from rfl)
  have gx : Det P [A] (.get (arg 0) (.nat 1)) (encPerm g) _ :=
    Det.get' (Det.arg' (vs := [B, .nat i]) (rest := []) (j := 0) rfl) (Det.nat 1)
      (show [Val.nat n, encPerm g][1]? = some (encPerm g) from rfl)
  have hmul := Det.arith' (op := .mul) (z := n * i) g0
    (Det.arg' (P := P) (vs := [B, .nat i]) (rest := []) (j := 1) rfl) rfl
  have hidx := Det.arith' (op := .add) (z := ((pairEnum n (i, i) : Fin (n * n)) : ℕ))
    (Det.arg' (P := P) (vs := [B, .nat i]) (rest := []) (j := 1) rfl) hmul
    (by rw [pairEnum_val]; rfl)
  have hap := Det.applyPerm gx hidx
  refine FunDet.intro hf ((Det.arith' (op := .div) (z := proj g i) hap g0 rfl).mono ?_)
  have hi := i.isLt
  have hpe := (pairEnum n (i, i)).isLt
  have hge := (g (pairEnum n (i, i))).isLt
  have hpr := proj_le g i
  have w0 := wt_nat_le n
  have w1 := wt_nat_le (i : ℕ)
  have w2 := wt_nat_le (n * i)
  have w3 := wt_nat_le ((pairEnum n (i, i) : Fin (n * n)) : ℕ)
  have w4 := wt_nat_le ((g (pairEnum n (i, i)) : Fin (n * n)) : ℕ)
  have w5 := wt_nat_le (proj g i)
  have w6 := wt_encPerm_le g
  have wB := wt_list2_le (.nat n) (encPerm g)
  have wA := wt_list2_le B (.nat (i : ℕ))
  have eB : (Val.list [.nat n, encPerm g]).wt = B.wt := rfl
  have eA : (Val.list [B, .nat (i : ℕ)]).wt = A.wt := rfl
  have hsq := sq_le_pow n
  have hm2 : (n * n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    calc (n * n + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = (n + 1) ^ 4 := by ring
  have hni : n * i ≤ n * n := Nat.mul_le_mul_left _ hi.le
  have h24 := pow_le_pow_of_le n (show 2 ≤ 4 by omega)
  have hpe2 : ((pairEnum n (i, i) : Fin (n * n)) : ℕ) + 2 * n + 1 ≤ (n + 1) ^ 2 := by linarith
  have hge2 : ((g (pairEnum n (i, i)) : Fin (n * n)) : ℕ) + 2 * n + 1 ≤ (n + 1) ^ 2 := by
    linarith
  omega

/-- `map diagF`, at base `b` (four functions). -/
def diagMapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [diagF]

/-- **The diagonal of a permutation.** -/
theorem diagMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (diagMapFuns b))
    (g : Perm (Fin (n * n))) :
    FunDet P b (.list [.list [.nat n, encPerm g], encFun fun i : Fin n => (i : ℕ)])
      (encFun (proj g)) (100000 * (n + 1) ^ 5) := by
  have hf : P.funs[b + 3]? = some diagF := by
    simpa [diagMapFuns, mapFuns, loopFuns] using h.right.single
  refine (tabulate_spec h.left (F := fun i => .nat (proj g i))
    fun i => diagF_spec hf g i).mono ?_
  have e1 : (Val.list ((List.finRange n).map fun i => Val.nat (proj g i))).wt =
    (encFun (proj g)).wt := rfl
  rw [e1]
  have w1 := wt_encFun_le_sq (proj g) (proj_le g)
  have wi := wt_ids_le n
  have w0 := wt_nat_le n
  have w6 := wt_encPerm_le g
  have wB := wt_list2_le (.nat n) (encPerm g)
  have wA := wt_list2_le (.list [.nat n, encPerm g]) (encFun fun i : Fin n => (i : ℕ))
  have hsq := sq_le_pow n
  have hm2 : (n * n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    calc (n * n + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = (n + 1) ^ 4 := by ring
  have h24 := pow_le_pow_of_le n (show 2 ≤ 4 by omega)
  have h14 : n + 1 ≤ (n + 1) ^ 4 := Nat.le_self_pow (by omega) _
  have hY : (Val.list [.list [.nat n, encPerm g], encFun fun i : Fin n => (i : ℕ)]).wt +
      (encFun (proj g)).wt + 1 ≤ 80 * (n + 1) ^ 4 := by omega
  have hX := mul_pow_le (show n + 1 ≤ 1 * (n + 1) ^ 1 by simp) hY
  have hc1 : n * (2000 * (n + 1) ^ 4) ≤ 2000 * (n + 1) ^ 5 := by
    have := mul_pow_le (show n ≤ 1 * (n + 1) ^ 1 by simp)
      (show 2000 * (n + 1) ^ 4 ≤ 2000 * (n + 1) ^ 4 from le_rfl)
    simpa [Nat.add_comm 1 4] using this
  have e2 : mapK * (n + 1) * ((Val.list [.list [.nat n, encPerm g],
      encFun fun i : Fin n => (i : ℕ)]).wt + (encFun (proj g)).wt + 1) =
    1000 * ((n + 1) * ((Val.list [.list [.nat n, encPerm g],
      encFun fun i : Fin n => (i : ℕ)]).wt + (encFun (proj g)).wt + 1)) := by
    simp only [mapK]; ring
  rw [e2]
  simp only [one_mul, show 1 + 4 = 5 from rfl] at hX
  omega

/-! ### The diagonals of a list of permutations -/

/-- On `[[n, ids], x]`: the diagonal of `x`, by `diagMapFuns` at `dm`. -/
def projF (dm : ℕ) : Expr :=
  .call dm (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))

theorem projF_spec {P : Program} {f dm : ℕ} (hf : P.funs[f]? = some (projF dm))
    (hd : P.HasAt dm (diagMapFuns dm)) (g : Perm (Fin (n * n))) :
    FunDet P f (.list [.list [.nat n, encFun fun i : Fin n => (i : ℕ)], encPerm g])
      (encFun (proj g)) (120000 * (n + 1) ^ 5) := by
  set ids := encFun fun i : Fin n => (i : ℕ) with hids
  set B := Val.list [.nat n, ids] with hB
  set A := Val.list [B, encPerm g] with hA
  have g0 : Det P [A] (.get (arg 0) (.nat 0)) (.nat n) _ :=
    Det.get' (Det.arg' (vs := [B, encPerm g]) (rest := []) (j := 0) rfl) (Det.nat 0)
      (show [Val.nat n, ids][0]? = some (.nat n) from rfl)
  have g1 : Det P [A] (.get (arg 0) (.nat 1)) ids _ :=
    Det.get' (Det.arg' (vs := [B, encPerm g]) (rest := []) (j := 0) rfl) (Det.nat 1)
      (show [Val.nat n, ids][1]? = some ids from rfl)
  refine FunDet.intro hf ((Det.call (Det.mk2 (Det.mk2 g0
    (Det.arg' (P := P) (vs := [B, encPerm g]) (rest := []) (j := 1) rfl)) g1)
    (diagMap_spec hd g)).mono ?_)
  have w1 := wt_encFun_le_sq (proj g) (proj_le g)
  have wi : ids.wt ≤ 4 * (n + 1) ^ 2 := wt_ids_le n
  have w0 := wt_nat_le n
  have w6 := wt_encPerm_le g
  have wB := wt_list2_le (.nat n) ids
  have wA := wt_list2_le B (encPerm g)
  have w7 := wt_list2_le (.nat n) (encPerm g)
  have w8 := wt_list2_le (.list [.nat n, encPerm g]) ids
  have eB : (Val.list [.nat n, ids]).wt = B.wt := rfl
  have eA : (Val.list [B, encPerm g]).wt = A.wt := rfl
  have hsq := sq_le_pow n
  have hm2 : (n * n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    calc (n * n + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = (n + 1) ^ 4 := by ring
  have h24 := pow_le_pow_of_le n (show 2 ≤ 4 by omega)
  have h45 := pow_le_pow_of_le n (show 4 ≤ 5 by omega)
  have h14 : n + 1 ≤ (n + 1) ^ 4 := Nat.le_self_pow (by omega) _
  omega

/-- `map projF`, at base `b` (four functions); the diagonal map sits at `dm`. -/
def projMapFuns (b dm : ℕ) : List Expr := mapFuns b (b + 3) ++ [projF dm]

/-- **The diagonals of a list of permutations.** -/
theorem projMap_spec {P : Program} {b dm : ℕ} (h : P.HasAt b (projMapFuns b dm))
    (hd : P.HasAt dm (diagMapFuns dm)) (gs : List (Perm (Fin (n * n)))) :
    FunAll P b (.list [.list [.nat n, encFun fun i : Fin n => (i : ℕ)], .list (gs.map encPerm)])
      (fun w cost => w = .list (gs.map fun g => encFun (proj g)) ∧
        cost ≤ gs.length * (120000 * (n + 1) ^ 5) + mapK * (gs.length + 1) *
          ((Val.list [.list [.nat n, encFun fun i : Fin n => (i : ℕ)],
            .list (gs.map encPerm)]).wt + w.wt + 1)) := by
  have hf : P.funs[b + 3]? = some (projF dm) := by
    simpa [projMapFuns, mapFuns, loopFuns] using h.right.single
  have hM := map_spec (c := .list [.nat n, encFun fun i : Fin n => (i : ℕ)])
    (xs := gs.map encPerm) h.left
    (R := fun x w => ∀ g : Perm (Fin (n * n)), x = encPerm g → w = encFun (proj g))
    (B := fun _ => 120000 * (n + 1) ^ 5) (by
      intro x hx
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp hx
      refine FunAll.mono (projF_spec hf hd g) fun w c hw => ⟨fun g' hg' => ?_, hw.2⟩
      rw [hw.1, encPerm_injective hg'])
  refine FunAll.mono hM fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' : ws = gs.map fun g => encFun (proj g) :=
    forall₂_map_eq (h := hws) fun a _ w hw => hw a rfl
  subst hws'
  refine ⟨rfl, ?_⟩
  simp only [List.map_map, List.length_map, Function.comp_def, List.map_const',
    List.sum_replicate, smul_eq_mul] at hc
  exact hc

/-! ### Concatenation -/

/-- On `[c, acc, x]`: `acc ++ x`, by `appendFuns` at `ap`. -/
def appF (ap : ℕ) : Expr := .call ap (mk2 (arg 1) (arg 2))

theorem appF_spec {P : Program} {f ap : ℕ} (hf : P.funs[f]? = some (appF ap))
    (ha : P.HasAt ap (appendFuns ap)) (c : Val) (xs ys : List Val) :
    FunDet P f (.list [c, .list xs, .list ys]) (.list (xs ++ ys))
      (4000 * (ys.length + 1) * ((Val.list [c, .list xs, .list ys]).wt +
        (Val.list (xs ++ ys)).wt + 7)) := by
  have hA : FunDet P ap (.list [.list xs, .list ys]) (.list (xs ++ ys))
      (loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
        (Val.list (xs ++ ys)).wt + 1)) :=
    FunAll.mono (append_spec ha xs ys) fun w c hw => ⟨hw.1, by
      have := hw.2; rw [hw.1] at this; exact this⟩
  refine FunDet.intro hf ((Det.call (Det.mk2 (Det.arg' (P := P) (vs := [c, .list xs, .list ys])
    (rest := []) (j := 1) rfl) (Det.arg' (j := 2) rfl)) hA).mono ?_)
  have h1 := wt_list2_le (.list xs) (.list ys)
  have h2 : (Val.list xs).wt < (Val.list [c, .list xs, .list ys]).wt := wt_le_wt_list (by simp)
  have h3 : (Val.list ys).wt < (Val.list [c, .list xs, .list ys]).wt := wt_le_wt_list (by simp)
  have h4 := length_lt_wt_list ys
  have h5 := sum_wt_lt_wt_list [c, .list xs, .list ys]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h5
  generalize (Val.list [c, .list xs, .list ys]).wt = A at *
  generalize (Val.list (xs ++ ys)).wt = W at *
  generalize hZ : (Val.list [.list xs, .list ys]).wt + ys.length + W + 1 = Z at *
  have hZ' : Z ≤ 3 * A + W + 7 := by omega
  have hk : 0 < ys.length + 1 := by omega
  generalize ys.length + 1 = k at *
  have h6 : loopModK * k * Z ≤ 1000 * k * (3 * A + W + 7) := by
    rw [loopModK]; exact Nat.mul_le_mul_left _ hZ'
  have h7 : A + W + 7 ≤ k * (A + W + 7) := Nat.le_mul_of_pos_left _ hk
  nlinarith

/-- Appending two lists of values, as a function on values. -/
def appendV : Val → Val → Val
  | .list a, .list b => .list (a ++ b)
  | _, _ => .nat 0

theorem foldl_appendV (L : List (List ℕ)) (P0 : List ℕ) :
    (L.map fun l => Val.list (l.map .nat)).foldl appendV (.list (P0.map .nat)) =
      .list ((P0 ++ L.flatten).map .nat) := by
  induction L generalizing P0 with
  | nil => simp
  | cons l L ih =>
    simp only [List.map_cons, List.foldl_cons, appendV, ← List.map_append, ih, List.flatten_cons,
      List.append_assoc]

/-- `foldl appF`, at base `b` (four functions); `append` sits at `ap`. -/
def catFuns (b ap : ℕ) : List Expr := foldlFuns b (b + 3) ++ [appF ap]

/-- **Concatenation.** On `[c, [l₁, …, l_k], acc]` with lists of numbers of length `m` each, the
list `acc ++ l₁ ++ … ++ l_k`. -/
theorem cat_spec {P : Program} {b ap : ℕ} (h : P.HasAt b (catFuns b ap))
    (ha : P.HasAt ap (appendFuns ap)) (c : Val) (L : List (List ℕ)) (P0 : List ℕ) {m : ℕ}
    (hm : ∀ l ∈ L, l.length = m) :
    FunDet P b (.list [c, .list (L.map fun l => Val.list (l.map .nat)), .list (P0.map .nat)])
      (.list ((P0 ++ L.flatten).map .nat))
      (L.length * (4000 * (m + 1) * (2 * c.wt +
          2 * (Val.list (L.map fun l => Val.list (l.map .nat))).wt +
          3 * (Val.list ((P0 ++ L.flatten).map .nat)).wt + 20)) +
        loopModK * (L.length + 1) * ((Val.list [c, .list (L.map fun l => Val.list (l.map .nat)),
          .list (P0.map .nat)]).wt + L.length + (Val.list ((P0 ++ L.flatten).map .nat)).wt + 1)) := by
  have hf : P.funs[b + 3]? = some (appF ap) := by
    simpa [catFuns, foldlFuns, loopFuns] using h.right.single
  set xs := L.map fun l => Val.list (l.map .nat) with hxs
  set W := (Val.list ((P0 ++ L.flatten).map .nat)).wt with hW
  set XW := (Val.list xs).wt with hXW
  have hpart : ∀ i, (xs.take i).foldl appendV (.list (P0.map .nat)) =
      .list ((P0 ++ (L.take i).flatten).map .nat) := fun i => by
    rw [hxs, ← List.map_take, foldl_appendV]
  have hpre : ∀ i, (Val.list ((P0 ++ (L.take i).flatten).map .nat)).wt ≤ W := fun i => by
    refine wt_list_mono ?_
    refine List.IsPrefix.map _ ?_
    refine List.prefix_append_right_inj _ |>.mpr ?_
    have := List.take_append_drop i L
    conv_rhs => rw [← this]
    rw [List.flatten_append]
    exact List.prefix_append _ _
  have hlen : xs.length = L.length := by simp [hxs]
  have hfold := foldl_spec_fun (P := P) h.left (c := c) (xs := xs) (acc0 := .list (P0.map .nat))
    (G := appendV) (M := W)
    (B := fun _ => 4000 * (m + 1) * (2 * c.wt + 2 * XW + 3 * W + 20))
    (fun i _ => by rw [hpart]; exact hpre i) (fun i hi => by
      rw [hpart]
      have hxi : xs[i] = Val.list (L[i]'(by omega) |>.map .nat) := by simp [hxs]
      rw [hxi]
      refine (appF_spec hf ha c _ _).mono ?_
      have hl : (L[i]'(by omega)).length = m := hm _ (List.getElem_mem _)
      simp only [List.length_map, hl]
      refine Nat.mul_le_mul_left _ ?_
      have h1 := wt_list3_le c (.list ((P0 ++ (L.take i).flatten).map .nat))
        (.list ((L[i]'(by omega)).map .nat))
      have h2 := hpre i
      have h3 : (Val.list ((L[i]'(by omega)).map .nat)).wt ≤ XW := by
        have : xs[i] ∈ xs := List.getElem_mem _
        rw [hxi] at this
        exact (wt_le_wt_list this).le
      have h4 : (Val.list ((P0 ++ (L.take i).flatten).map .nat ++
          (L[i]'(by omega)).map .nat)).wt ≤ W := by
        have e : L.take i ++ [L[i]'(by omega)] = L.take (i + 1) := by
          rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
        rw [← List.map_append, List.append_assoc, ← List.flatten_concat, e]
        exact hpre (i + 1)
      omega)
  rw [foldl_appendV, hlen] at hfold
  refine hfold.mono ?_
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

end GI.Assembly
