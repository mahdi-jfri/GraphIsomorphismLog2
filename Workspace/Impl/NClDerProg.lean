module

public import Workspace.Impl.NClDerMath
public import Workspace.Lang.Prims.Reduce

@[expose] public section

/-!
# The derived subgroup as a program

The program `derFuns b j` (25 functions at base `b`, the normal closure algorithm as primitive
`j`) computes, on `encGroup gs`, the commutators `[a, b]` for `a, b ∈ 1 :: gs` (two nested
folds), and calls the normal closure on `[encGroup gs, encGroup (derComms gs)]`.

* `b`: the entry. `b + 1 … b + 3`: the outer fold, step `b + 4`. `b + 5 … b + 7`: the inner fold,
  step `b + 8` (one commutator). `b + 9 … b + 12`: composition. `b + 13 … b + 24`: inverse.

The costs are stated for a bound `Y` with `n + 1 ≤ Y`, `|1 :: gs| ≤ Y` and the weight of the
generator list at most `Y`.
-/

namespace GI.Impl

open GI.Cited GI.Lang Equiv
open scoped commutatorElement

variable {n : ℕ}

/-- One commutator, on `[encPerm a, L, encPerm b]`: `L` with `encPerm ((a b)(a⁻¹ b⁻¹))` added. -/
def derCommF (b : ℕ) : Expr :=
  .snoc (arg 1) (.call (b + 9) (mk2 (.call (b + 9) (mk2 (arg 0) (arg 2)))
    (.call (b + 9) (mk2 (.call (b + 13) (arg 0)) (.call (b + 13) (arg 2))))))

/-- The outer step, on `[xs, L, encPerm a]`: the inner fold on `[encPerm a, xs, L]`. -/
def derOuterF (b : ℕ) : Expr := .call (b + 5) (mk3 (arg 2) (arg 0) (arg 1))

/-- The entry, on `encGroup gs = [n, xs]`: fold over `xs` from `[xs[0]]`, then call the normal
closure on `[encGroup gs, [n, L]]`. -/
def derEntry (b j : ℕ) : Expr :=
  .letE (.call (b + 1) (mk3 (.get (.var 0) (.nat 1)) (.get (.var 0) (.nat 1))
      (mk1 (.get (.get (.var 0) (.nat 1)) (.nat 0)))))
    (.prim j (mk2 (.var 0) (mk2 (.get (.var 0) (.nat 0)) (.var 1))))

/-- **The program of the derived subgroup.** -/
def derFuns (b j : ℕ) : List Expr :=
  [derEntry b j] ++ foldlFuns (b + 1) (b + 4) ++ [derOuterF b] ++ foldlFuns (b + 5) (b + 8) ++
    [derCommF b] ++ composeFuns (b + 9) ++ invFuns (b + 13)

structure DerAt (P : Program) (b j : ℕ) (h : NormalClosure) : Prop where
  entry : P.funs[b]? = some (derEntry b j)
  outer : P.HasAt (b + 1) (foldlFuns (b + 1) (b + 4))
  ostep : P.funs[b + 4]? = some (derOuterF b)
  inner : P.HasAt (b + 5) (foldlFuns (b + 5) (b + 8))
  comm : P.funs[b + 8]? = some (derCommF b)
  comp : P.HasAt (b + 9) (composeFuns (b + 9))
  inv : P.HasAt (b + 13) (invFuns (b + 13))
  prim : P.prims[j]? = some (normalClosurePrim h)

theorem derAt_of {P : Program} {b j : ℕ} {h : NormalClosure} (hP : P.HasAt b (derFuns b j))
    (hj : P.prims[j]? = some (normalClosurePrim h)) : DerAt P b j h := by
  simp only [derFuns] at hP
  refine ⟨hP.left.left.left.left.left.left.single, ?_, ?_, ?_, ?_, ?_, ?_, hj⟩
  · simpa using hP.left.left.left.left.left.right
  · simpa [foldlFuns, loopFuns, Nat.add_assoc] using hP.left.left.left.left.right.single
  · simpa [foldlFuns, loopFuns, Nat.add_assoc] using hP.left.left.left.right
  · simpa [foldlFuns, loopFuns, Nat.add_assoc] using hP.left.left.right.single
  · simpa [foldlFuns, loopFuns, Nat.add_assoc] using hP.left.right
  · simpa [foldlFuns, loopFuns, composeFuns, mapFuns, Nat.add_assoc] using hP.right

/-- A list of at most `Y² + 1` permutations weighs at most `30 Y⁴`. -/
theorem der_wt_perms {Y : ℕ} (hn : n + 1 ≤ Y) {ps : List (Perm (Fin n))}
    (hl : ps.length ≤ Y ^ 2 + 1) : (Val.list (ps.map encPerm)).wt ≤ 30 * Y ^ 4 := by
  have h1 := wt_list_le (ps.map encPerm)
  have h2 : ((ps.map encPerm).map Val.wt).sum ≤ ps.length * (4 * Y ^ 2) := by
    have := List.sum_le_card_nsmul ((ps.map encPerm).map Val.wt) (4 * Y ^ 2) (by
      intro x hx
      simp only [List.map_map, List.mem_map, Function.comp] at hx
      obtain ⟨σ, -, rfl⟩ := hx
      exact (wt_encPerm_le σ).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2)))
    simpa using this
  have h3 : ps.length * (4 * Y ^ 2) ≤ (Y ^ 2 + 1) * (4 * Y ^ 2) := Nat.mul_le_mul_right _ hl
  have e : (Y ^ 2 + 1) * (4 * Y ^ 2) = 4 * Y ^ 4 + 4 * Y ^ 2 := by ring
  have y24 : Y ^ 2 ≤ Y ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have y1 : 1 ≤ Y ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [List.length_map] at h1
  omega

/-! ### One commutator -/

theorem derComm_spec {P : Program} {b j : ℕ} {h : NormalClosure} (hP : DerAt P b j h) {Y : ℕ}
    (hn : n + 1 ≤ Y) (a : Perm (Fin n)) {ps : List (Perm (Fin n))} (hl : ps.length ≤ Y ^ 2)
    (c : Perm (Fin n)) :
    FunDet P (b + 8) (.list [encPerm a, .list (ps.map encPerm), encPerm c])
      (.list ((ps ++ [⁅a, c⁆]).map encPerm)) (10 ^ 6 * Y ^ 4) := by
  set V : List Val := [encPerm a, .list (ps.map encPerm), encPerm c] with hV
  have d0 := Det.arg' (P := P) (vs := V) (rest := []) (j := 0) (v := encPerm a) rfl
  have d1 := Det.arg' (P := P) (vs := V) (rest := []) (j := 1) (v := .list (ps.map encPerm)) rfl
  have d2 := Det.arg' (P := P) (vs := V) (rest := []) (j := 2) (v := encPerm c) rfl
  have dac := Det.call (Det.mk2 d0 d2) (compose_spec hP.comp a c)
  have dia := Det.call d0 (inv_spec hP.inv a)
  have dic := Det.call d2 (inv_spec hP.inv c)
  have dii := Det.call (Det.mk2 dia dic) (compose_spec hP.comp a⁻¹ c⁻¹)
  have dx := Det.call (Det.mk2 dac dii) (compose_spec hP.comp (a * c) (a⁻¹ * c⁻¹))
  have dS := Det.snoc d1 dx
  have e : ps.map encPerm ++ [encPerm (a * c * (a⁻¹ * c⁻¹))] = (ps ++ [⁅a, c⁆]).map encPerm := by
    simp [commutatorElement_def, mul_assoc]
  rw [e] at dS
  refine FunDet.intro hP.comm (dS.mono ?_)
  clear dS dx dii dic dia dac d0 d1 d2
  have wa := wt_encPerm_le a
  have wc := wt_encPerm_le c
  have wai := wt_encPerm_le a⁻¹
  have wci := wt_encPerm_le c⁻¹
  have wac := wt_encPerm_le (a * c)
  have wii := wt_encPerm_le (a⁻¹ * c⁻¹)
  have wx := wt_encPerm_le (a * c * (a⁻¹ * c⁻¹))
  have wP := der_wt_perms hn (ps := ps) (by omega)
  have wP' := der_wt_perms hn (ps := ps ++ [⁅a, c⁆]) (by simp; omega)
  have wV := wt_list3_le (encPerm a) (.list (ps.map encPerm)) (encPerm c)
  have eV : (Val.list V).wt = (Val.list [encPerm a, .list (ps.map encPerm), encPerm c]).wt := rfl
  have w1 := wt_list2_le (encPerm a) (encPerm c)
  have w2 := wt_list2_le (encPerm a⁻¹) (encPerm c⁻¹)
  have w3 := wt_list2_le (encPerm (a * c)) (encPerm (a⁻¹ * c⁻¹))
  have p2 : (n + 1) ^ 2 ≤ Y ^ 4 :=
    (Nat.pow_le_pow_left hn 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have p3 : (n + 1) ^ 3 ≤ Y ^ 4 :=
    (Nat.pow_le_pow_left hn 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have p4 : (n + 1) ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left hn 4
  have y1 : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ (by omega)
  simp only [permK, invK]
  omega

/-! ### The inner fold: the commutators `[a, c]`, `c ∈ l` -/

theorem derInner_spec {P : Program} {b j : ℕ} {h : NormalClosure} (hP : DerAt P b j h) {Y : ℕ}
    (hn : n + 1 ≤ Y) (a : Perm (Fin n)) (l : List (Perm (Fin n)))
    (hW : (Val.list (l.map encPerm)).wt ≤ Y) {pre : List (Perm (Fin n))}
    (hpre : pre.length + l.length ≤ Y ^ 2) :
    FunDet P (b + 5) (.list [encPerm a, .list (l.map encPerm), .list (pre.map encPerm)])
      (.list ((pre ++ l.map fun c => ⁅a, c⁆).map encPerm)) (2 * 10 ^ 6 * Y ^ 5) := by
  set xs := l.map encPerm with hxs
  have hlen : xs.length = l.length := by simp [hxs]
  have hf := foldl_spec hP.inner (c := encPerm a) (xs := xs) (acc0 := .list (pre.map encPerm))
    (Inv := fun i acc => acc = .list ((pre ++ (l.take i).map fun c => ⁅a, c⁆).map encPerm))
    (M := 30 * Y ^ 4) (B := fun _ => 10 ^ 6 * Y ^ 4) (by simp)
    (fun i acc hi hacc => by
      rw [hacc]
      exact der_wt_perms hn (by simp; omega))
    (fun i acc hi hacc => by
      have hi' : i < l.length := by omega
      have hx : xs[i] = encPerm l[i] := by simp only [hxs, List.getElem_map]
      rw [hacc, hx]
      refine FunAll.mono (derComm_spec hP hn a (ps := pre ++ (l.take i).map fun c => ⁅a, c⁆)
        (by simp; omega) l[i]) fun w cost hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some]
      simp only [List.map_append, List.append_assoc, List.map_cons, List.map_nil])
  refine FunAll.mono hf fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1, hlen, List.take_length]
  · have hc := hw.2
    beta_reduce at hc
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    unfold loopModK at hc
    have hxl : xs.length < (Val.list xs).wt := length_lt_wt_list xs
    have w3 := wt_list3_le (encPerm a) (.list xs) (.list (pre.map encPerm))
    have wa := wt_encPerm_le a
    have wp := der_wt_perms hn (ps := pre) (by omega)
    have p2 : (n + 1) ^ 2 ≤ Y ^ 4 :=
      (Nat.pow_le_pow_left hn 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have y14 : Y ≤ Y ^ 4 := Nat.le_self_pow (by omega) _
    have y1 : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ (by omega)
    have k1 : xs.length * (10 ^ 6 * Y ^ 4) ≤ Y * (10 ^ 6 * Y ^ 4) := Nat.mul_le_mul_right _ (by omega)
    have k2 : (xs.length + 1) * ((Val.list [encPerm a, .list xs, .list (pre.map encPerm)]).wt +
        xs.length + 30 * Y ^ 4 + 1) ≤ (2 * Y) * (200 * Y ^ 4) := Nat.mul_le_mul (by omega) (by omega)
    have e1 : Y * (10 ^ 6 * Y ^ 4) = 10 ^ 6 * Y ^ 5 := by ring
    have e2 : (2 * Y) * (200 * Y ^ 4) = 400 * Y ^ 5 := by ring
    rw [Nat.mul_assoc] at hc
    omega

/-! ### The outer fold -/

/-- The commutators `[a, c]` for `a` in the first `k` entries of `l` and `c ∈ l`. -/
def derPart (l : List (Perm (Fin n))) (k : ℕ) : List (Perm (Fin n)) :=
  (l.take k).flatMap fun a => l.map fun c => ⁅a, c⁆

theorem length_derPart (l : List (Perm (Fin n))) (k : ℕ) :
    (derPart l k).length = min k l.length * l.length := by
  simp [derPart, List.length_flatMap]

theorem derOuter_spec {P : Program} {b j : ℕ} {h : NormalClosure} (hP : DerAt P b j h) {Y : ℕ}
    (hn : n + 1 ≤ Y) (l : List (Perm (Fin n))) (hW : (Val.list (l.map encPerm)).wt ≤ Y)
    (hlY : l.length + 1 ≤ Y) :
    FunDet P (b + 1) (.list [.list (l.map encPerm), .list (l.map encPerm),
        .list ([(1 : Perm (Fin n))].map encPerm)])
      (.list ((1 :: derPart l l.length).map encPerm)) (4 * 10 ^ 6 * Y ^ 6) := by
  set xs := l.map encPerm with hxs
  have hlen : xs.length = l.length := by simp [hxs]
  have hsq : 1 + l.length * l.length ≤ Y ^ 2 := by
    have := Nat.mul_le_mul hlY hlY
    rw [sq]; nlinarith
  have hpl : ∀ k ≤ l.length, (1 :: derPart l k).length ≤ Y ^ 2 + 1 := fun k hk => by
    rw [List.length_cons, length_derPart, min_eq_left hk]
    have := Nat.mul_le_mul_right l.length hk
    omega
  have hf := foldl_spec hP.outer (c := .list xs) (xs := xs) (acc0 := .list ([(1 : Perm (Fin n))].map encPerm))
    (Inv := fun k acc => acc = .list ((1 :: derPart l k).map encPerm))
    (M := 30 * Y ^ 4) (B := fun _ => 3 * 10 ^ 6 * Y ^ 5) (by simp [derPart])
    (fun k acc hk hacc => by
      rw [hacc]; exact der_wt_perms hn (hpl k (by omega)))
    (fun k acc hk hacc => by
      have hk' : k < l.length := by omega
      have hx : xs[k] = encPerm l[k] := by simp only [hxs, List.getElem_map]
      rw [hacc, hx]
      set V : List Val := [.list xs, .list ((1 :: derPart l k).map encPerm), encPerm l[k]]
      have d0 := Det.arg' (P := P) (vs := V) (rest := []) (j := 0) (v := .list xs) rfl
      have d1 := Det.arg' (P := P) (vs := V) (rest := []) (j := 1)
        (v := .list ((1 :: derPart l k).map encPerm)) rfl
      have d2 := Det.arg' (P := P) (vs := V) (rest := []) (j := 2) (v := encPerm l[k]) rfl
      have hpre : (1 :: derPart l k).length + l.length ≤ Y ^ 2 := by
        rw [List.length_cons, length_derPart, min_eq_left hk'.le]
        have := Nat.mul_le_mul_right l.length (show k + 1 ≤ l.length by omega)
        rw [Nat.add_mul, one_mul] at this
        omega
      have dc := Det.call (Det.mk3 d2 d0 d1) (derInner_spec hP hn l[k] l hW hpre)
      have e : (1 :: derPart l k) ++ l.map (fun c => ⁅l[k], c⁆) = 1 :: derPart l (k + 1) := by
        simp only [derPart, List.cons_append, List.take_add_one, List.getElem?_eq_getElem hk',
          Option.toList_some, List.flatMap_append, List.flatMap_singleton]
      rw [e] at dc
      refine (FunDet.intro hP.ostep dc).mono ?_
      have wP := wt_encPerm_le l[k]
      have wA := der_wt_perms hn (hpl k hk'.le)
      have wA' := der_wt_perms hn (hpl (k + 1) (by omega))
      have wV := wt_list3_le (.list xs) (.list ((1 :: derPart l k).map encPerm)) (encPerm l[k])
      have eV : (Val.list V).wt = (Val.list [.list xs, .list ((1 :: derPart l k).map encPerm),
        encPerm l[k]]).wt := rfl
      have w3 := wt_list3_le (encPerm l[k]) (.list xs) (.list ((1 :: derPart l k).map encPerm))
      have p2 : (n + 1) ^ 2 ≤ Y ^ 4 :=
        (Nat.pow_le_pow_left hn 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
      have y14 : Y ≤ Y ^ 4 := Nat.le_self_pow (by omega) _
      have y45 : Y ^ 4 ≤ Y ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
      have y1 : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ (by omega)
      beta_reduce
      omega)
  refine FunAll.mono hf fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1, hlen]
  · have hc := hw.2
    beta_reduce at hc
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    unfold loopModK at hc
    have hxl : xs.length < (Val.list xs).wt := length_lt_wt_list xs
    have w0 : (Val.list ([(1 : Perm (Fin n))].map encPerm : List Val)).wt ≤ 30 * Y ^ 4 :=
      der_wt_perms hn (ps := [(1 : Perm (Fin n))]) (by simp)
    have w3 := wt_list3_le (.list xs) (.list xs) (.list ([(1 : Perm (Fin n))].map encPerm : List Val))
    have y14 : Y ≤ Y ^ 4 := Nat.le_self_pow (by omega) _
    have y56 : Y ^ 5 ≤ Y ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have y1 : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ (by omega)
    have k1 : xs.length * (3 * 10 ^ 6 * Y ^ 5) ≤ Y * (3 * 10 ^ 6 * Y ^ 5) :=
      Nat.mul_le_mul_right _ (by omega)
    have k2 : (xs.length + 1) * ((Val.list [.list xs, .list xs, .list ([(1 : Perm (Fin n))].map encPerm : List Val)]).wt +
        xs.length + 30 * Y ^ 4 + 1) ≤ Y * (200 * Y ^ 4) := Nat.mul_le_mul (by omega) (by omega)
    have e1 : Y * (3 * 10 ^ 6 * Y ^ 5) = 3 * 10 ^ 6 * Y ^ 6 := by ring
    have e2 : Y * (200 * Y ^ 4) = 200 * Y ^ 5 := by ring
    rw [Nat.mul_assoc 1000] at hc
    omega

/-! ### The entry -/

theorem derComms_eq (gs : List (Perm (Fin n))) : derPart (1 :: gs) (1 :: gs).length = derComms gs := by
  simp only [derPart, List.take_length, derComms]

theorem ncl_gens_append (gs hs : List (Perm (Fin n))) : gens (gs ++ hs) = gens gs ⊔ gens hs := by
  unfold gens
  rw [← Subgroup.closure_union]
  congr 1; ext g; simp

/-- **The entry.** With `Y` the weight of `encGroup gs` plus one, the result generates `[G, G]`
at cost at most `10⁸ Y⁶ + c (200 Y⁴)^k`, for the constants `c, k` of the normal closure. -/
theorem derEntry_spec {P : Program} {b j : ℕ} {h : NormalClosure} (hP : DerAt P b j h)
    (gs : List (Perm (Fin n))) :
    FunAll P b (encGroup gs) (fun w c => GensVal n w ⁅gens gs, gens gs⁆ ∧
      c ≤ 10 ^ 8 * ((encGroup gs).wt + 1) ^ 6 +
        (normalClosurePrim h).c * (200 * ((encGroup gs).wt + 1) ^ 4) ^ (normalClosurePrim h).k) := by
  set xs := (1 :: gs).map encPerm with hxs
  set Y := (encGroup gs).wt + 1 with hY
  have eG : encGroup gs = .list [.nat n, .list xs] := rfl
  have hxw : (Val.list xs).wt < (encGroup gs).wt := by
    rw [eG]; exact wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hxl : xs.length < (Val.list xs).wt := length_lt_wt_list xs
  have hlx : xs.length = (1 :: gs).length := by simp [hxs]
  have hnG : n < (encGroup gs).wt := by
    have h1 : n < (encPerm (1 : Perm (Fin n))).wt := by
      have := length_lt_wt_list ((List.finRange n).map fun i => Val.nat ((1 : Perm (Fin n)) i))
      simpa [encPerm] using this
    have h2 : (encPerm (1 : Perm (Fin n))).wt < (Val.list xs).wt := wt_le_wt_list (by simp [hxs])
    omega
  have hn : n + 1 ≤ Y := by omega
  have hW : (Val.list ((1 :: gs).map encPerm)).wt ≤ Y := by rw [← hxs]; omega
  have hlY : (1 :: gs).length + 1 ≤ Y := by omega
  have dX := Det.get' (P := P) (env := [encGroup gs]) (Det.var' (i := 0) rfl) (Det.nat 1)
    (show [Val.nat n, .list xs][1]? = some (.list xs) from rfl)
  have d0 := Det.get' dX (Det.nat 0) (show xs[0]? = some (encPerm (1 : Perm (Fin n))) from rfl)
  have dA := Det.mk3 dX dX (Det.mk1 d0)
  have dF := Det.call dA (derOuter_spec hP hn (1 :: gs) hW hlY)
  rw [derComms_eq] at dF
  set Lv := Val.list ((1 :: derComms gs).map encPerm)
  refine FunAll.intro hP.entry (EvalAll.letE dF fun v ca hv => ?_)
  obtain ⟨rfl, hca⟩ := hv
  have dg := Det.var' (P := P) (env := [encGroup gs, Lv]) (i := 0) rfl
  have dn := Det.get' (Det.var' (P := P) (env := [encGroup gs, Lv]) (i := 0) rfl) (Det.nat 0)
    (show [Val.nat n, .list xs][0]? = some (.nat n) from rfl)
  have dL := Det.var' (P := P) (env := [encGroup gs, Lv]) (i := 1) rfl
  have da := Det.mk2 dg (Det.mk2 dn dL)
  have eH : Val.list [.nat n, Lv] = encGroup (derComms gs) := rfl
  rw [eH] at da
  refine (normalClosure_call h hP.prim da ⟨gs, rfl, rfl⟩).mono fun w c hw => ⟨?_, ?_⟩
  · have e := derived_eq_ncl gs
    unfold nclTarget at e
    rw [ncl_gens_append] at e
    rw [e]; exact hw.1
  · have hc := hw.2
    -- the weights
    have wL : Lv.wt ≤ 30 * Y ^ 4 := der_wt_perms hn (by
      rw [List.length_cons, ← derComms_eq, length_derPart, min_self]
      have := Nat.mul_le_mul (show (1 :: gs).length ≤ Y by omega) (show (1 :: gs).length ≤ Y by omega)
      rw [sq]; omega)
    have wn := wt_nat_le n
    have wH := wt_list2_le (.nat n) Lv
    have eH' : (encGroup (derComms gs)).wt = (Val.list [.nat n, Lv]).wt := rfl
    have wa := wt_list2_le (encGroup gs) (encGroup (derComms gs))
    have hsz := (Val.list [encGroup gs, encGroup (derComms gs)]).size_le_wt
    have y14 : Y ≤ Y ^ 4 := Nat.le_self_pow (by omega) _
    have y1 : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ (by omega)
    have y46 : Y ^ 4 ≤ Y ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have p6 : (n + 1) ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left hn 6
    have hb : (normalClosurePrim h).bound (.list [encGroup gs, encGroup (derComms gs)]) ≤
        (normalClosurePrim h).c * (200 * Y ^ 4) ^ (normalClosurePrim h).k := by
      unfold Prim.bound
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have wF : (Val.list ((1 :: derComms gs).map encPerm)).wt ≤ 30 * Y ^ 4 := wL
    have w1 := wt_list1_le (encPerm (1 : Perm (Fin n)))
    have wP1 := wt_encPerm_le (1 : Perm (Fin n))
    have p2 : (n + 1) ^ 2 ≤ Y ^ 4 :=
      (Nat.pow_le_pow_left hn 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have w3 := wt_list3_le (.list xs) (.list xs) (.list [encPerm (1 : Perm (Fin n))])
    have y56 : Y ^ 4 * 1 ≤ Y ^ 6 := by omega
    have ww := GensVal.wt_le hw.1
    have eG' : (Val.list [Val.nat n, Val.list (List.map encPerm (1 :: gs))]).wt = (encGroup gs).wt :=
      rfl
    omega

end GI.Impl
