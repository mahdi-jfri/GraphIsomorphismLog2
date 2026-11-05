module

public import Workspace.Assembly.BuildMath

@[expose] public section

/-!
# Building the generators of the pair state

The group of the pair state of Algorithm 1 is the diagonal action of `Sym(n)` on the positions
`Fin (n * n)`. A program builds it from the generators `pairGens n`, the diagonal images of all
transpositions `(i j)` (`gens_pairGens`, `Workspace/Assembly/BuildMath.lean`).

* `entF`: on `[[n, i, j], p]`, entry `p` of the generator of `(i j)`, that is
  `s (p % n) + n * s (p / n)` where `s` swaps `i` and `j`.
* `entMapFuns`: on `[[n, i, j], [0, …, n² - 1]]`, the generator of `(i j)`
  (`entMap_spec`, cost at most `80000 (n + 1)^6`).
* `genMapFuns`: on `[[n, ids], ids]` with `ids = [0, …, n² - 1]`, the list of all generators
  (`genMap_spec`, cost at most `200000 (n + 1)^8`).
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### A transposition on numbers, in the language -/

/-- `if x = i then j else if x = j then i else x`. -/
def swapE (x i j : Expr) : Expr := .ite (.arith .eq x i) j (.ite (.arith .eq x j) i x)

theorem Det.swapE {P : Program} {env : List Val} {x i j : Expr} {a ii jj ca ci cj : ℕ}
    (hx : Det P env x (.nat a) ca) (hi : Det P env i (.nat ii) ci)
    (hj : Det P env j (.nat jj) cj) :
    Det P env (swapE x i j) (.nat (swapNat ii jj a)) (3 * (ca + ci + cj) + 2 * (a + ii + jj) + 30) := by
  unfold GI.Assembly.swapE swapNat
  have w1 := wt_nat_le a
  have w2 := wt_nat_le ii
  have w3 := wt_nat_le jj
  by_cases h1 : a = ii
  · rw [if_pos h1]
    have ht := Det.arith' (op := .eq) (z := 1) hx hi (by simp [BinOp.eval, h1])
    exact (Det.ite_pos ht one_ne_zero hj).mono (by omega)
  · rw [if_neg h1]
    have ht := Det.arith' (op := .eq) (z := 0) hx hi (by simp [BinOp.eval, h1])
    by_cases h2 : a = jj
    · rw [if_pos h2]
      have ht' := Det.arith' (op := .eq) (z := 1) hx hj (by simp [BinOp.eval, h2])
      exact (Det.ite_zero ht (Det.ite_pos ht' one_ne_zero hi)).mono (by omega)
    · rw [if_neg h2]
      have ht' := Det.arith' (op := .eq) (z := 0) hx hj (by simp [BinOp.eval, h2])
      exact (Det.ite_zero ht (Det.ite_zero ht' hx)).mono (by omega)

/-! ### One entry of a generator -/

/-- On `[[n, i, j], p]`: entry `p` of the generator of `(i j)`. -/
def entF : Expr :=
  .letE (.arith .div (arg 1) (.get (arg 0) (.nat 0)))
    (.letE (.arith .mod (arg 1) (.get (arg 0) (.nat 0)))
      (.arith .add (swapE (.var 2) (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)))
        (.arith .mul (.get (arg 0) (.nat 0))
          (swapE (.var 1) (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2))))))

theorem entF_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some entF) (i j : Fin n)
    (p : Fin (n * n)) :
    FunDet P f (.list [.list [.nat n, .nat i, .nat j], .nat p]) (.nat (pairSwap i j p))
      (4000 * (n + 1) ^ 2) := by
  set B := Val.list [.nat n, .nat i, .nat j] with hB
  set A := Val.list [B, .nat p] with hA
  have g0 : ∀ rest, Det P (A :: rest) (.get (arg 0) (.nat 0)) (.nat n) _ := fun rest =>
    Det.get' (Det.arg' (vs := [B, .nat p]) (rest := rest) (j := 0) rfl) (Det.nat 0)
      (show [Val.nat n, .nat i, .nat j][0]? = some (.nat n) from rfl)
  have g1 : ∀ rest, Det P (A :: rest) (.get (arg 0) (.nat 1)) (.nat i) _ := fun rest =>
    Det.get' (Det.arg' (vs := [B, .nat p]) (rest := rest) (j := 0) rfl) (Det.nat 1)
      (show [Val.nat n, .nat i, .nat j][1]? = some (.nat i) from rfl)
  have g2 : ∀ rest, Det P (A :: rest) (.get (arg 0) (.nat 2)) (.nat j) _ := fun rest =>
    Det.get' (Det.arg' (vs := [B, .nat p]) (rest := rest) (j := 0) rfl) (Det.nat 2)
      (show [Val.nat n, .nat i, .nat j][2]? = some (.nat j) from rfl)
  have d1 := Det.arith' (op := .div) (z := (p : ℕ) / n)
    (Det.arg' (P := P) (vs := [B, .nat p]) (rest := []) (j := 1) rfl) (g0 []) rfl
  have d2 := Det.arith' (op := .mod) (z := (p : ℕ) % n)
    (Det.arg' (P := P) (vs := [B, .nat p]) (rest := [.nat ((p : ℕ) / n)]) (j := 1) rfl)
    (g0 _) rfl
  set rest := [Val.nat ((p : ℕ) / n), .nat ((p : ℕ) % n)] with hrest
  have s1 := Det.swapE (Det.var' (P := P) (env := A :: rest) (i := 2) rfl) (g1 rest) (g2 rest)
  have s2 := Det.swapE (Det.var' (P := P) (env := A :: rest) (i := 1) rfl) (g1 rest) (g2 rest)
  have hm := Det.arith' (op := .mul) (z := n * swapNat i j ((p : ℕ) / n)) (g0 rest) s2 rfl
  have ha := Det.arith' (op := .add) (z := pairSwap i j p) s1 hm
    (by simp [BinOp.eval, pairSwap_val])
  refine FunDet.intro hf ((Det.letE d1 (Det.letE d2 ha)).mono ?_)
  -- the cost
  have hi := i.isLt
  have hj := j.isLt
  have hp := p.isLt
  have hd : (p : ℕ) / n ≤ p := Nat.div_le_self _ _
  have hmo : (p : ℕ) % n ≤ p := Nat.mod_le _ _
  have hs1 : swapNat i j ((p : ℕ) % n) ≤ p + n := by unfold swapNat; split_ifs <;> omega
  have hs2 : swapNat i j ((p : ℕ) / n) ≤ p + n := by unfold swapNat; split_ifs <;> omega
  have hsw : (pairSwap i j p : ℕ) < n * n := (pairSwap i j p).isLt
  have hm2 : n * swapNat i j ((p : ℕ) / n) ≤ n * n := by
    rw [pairSwap_val] at hsw; omega
  have w0 := wt_nat_le n
  have w1 := wt_nat_le (i : ℕ)
  have w2 := wt_nat_le (j : ℕ)
  have w3 := wt_nat_le (p : ℕ)
  have w4 := wt_nat_le (pairSwap i j p : ℕ)
  have w5 := wt_nat_le ((p : ℕ) / n)
  have w6 := wt_nat_le ((p : ℕ) % n)
  have wB := wt_list3_le (.nat n) (.nat (i : ℕ)) (.nat (j : ℕ))
  have wA := wt_list2_le B (.nat (p : ℕ))
  have eB : (Val.list [.nat n, .nat (i : ℕ), .nat (j : ℕ)]).wt = B.wt := rfl
  have eA : (Val.list [B, .nat (p : ℕ)]).wt = A.wt := rfl
  have hsq := sq_le_pow n
  have hp2 : (p : ℕ) + 2 * n + 1 ≤ (n + 1) ^ 2 := by linarith
  have hsw2 : (pairSwap i j p : ℕ) + 2 * n + 1 ≤ (n + 1) ^ 2 := by linarith
  have hm3 : n * swapNat i j ((p : ℕ) / n) + 2 * n + 1 ≤ (n + 1) ^ 2 := by linarith
  omega

/-- `map entF`, at base `b` (four functions). -/
def entMapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [entF]

theorem entMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (entMapFuns b)) (i j : Fin n) :
    FunDet P b (.list [.list [.nat n, .nat i, .nat j], encFun fun p : Fin (n * n) => (p : ℕ)])
      (encPerm (pairSwap i j)) (80000 * (n + 1) ^ 6) := by
  have hf : P.funs[b + 3]? = some entF := by
    simpa [entMapFuns, mapFuns, loopFuns] using h.right.single
  refine (tabulate_spec h.left (F := fun p => .nat (pairSwap i j p))
    fun p => entF_spec hf i j p).mono ?_
  have e1 : (Val.list ((List.finRange (n * n)).map fun p => Val.nat (pairSwap i j p))).wt =
    (encPerm (pairSwap i j)).wt := rfl
  rw [e1]
  have w1 := wt_encPerm_le (pairSwap i j)
  have w2 := wt_ids_le (n * n)
  have w3 := wt_list2_le (.list [.nat n, .nat (i : ℕ), .nat (j : ℕ)])
    (encFun fun p : Fin (n * n) => (p : ℕ))
  have w4 := wt_list3_le (.nat n) (.nat (i : ℕ)) (.nat (j : ℕ))
  have := wt_nat_le n
  have := wt_nat_le (i : ℕ)
  have := wt_nat_le (j : ℕ)
  have := i.isLt
  have := j.isLt
  have hm : n * n + 1 ≤ 1 * (n + 1) ^ 2 := by have := sq_le_pow n; omega
  have hm2 : (n * n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    calc (n * n + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = (n + 1) ^ 4 := by ring
  have h4 : n + 1 ≤ (n + 1) ^ 4 := Nat.le_self_pow (by omega) _
  have hY : (Val.list [.list [.nat n, .nat (i : ℕ), .nat (j : ℕ)],
      encFun fun p : Fin (n * n) => (p : ℕ)]).wt + (encPerm (pairSwap i j)).wt + 1 ≤
      70 * (n + 1) ^ 4 := by omega
  have hX := mul_pow_le hm hY
  have hc1 : n * n * (4000 * (n + 1) ^ 2) ≤ 4000 * (n + 1) ^ 6 := by
    have := mul_pow_le (show n * n ≤ 1 * (n + 1) ^ 2 by omega)
      (show 4000 * (n + 1) ^ 2 ≤ 4000 * (n + 1) ^ 2 from le_rfl)
    have h46 := pow_le_pow_of_le n (show 4 ≤ 6 by omega)
    simp only [one_mul, show 2 + 2 = 4 from rfl] at this
    omega
  have e2 : mapK * (n * n + 1) * ((Val.list [.list [.nat n, .nat (i : ℕ), .nat (j : ℕ)],
      encFun fun p : Fin (n * n) => (p : ℕ)]).wt + (encPerm (pairSwap i j)).wt + 1) =
    1000 * ((n * n + 1) * ((Val.list [.list [.nat n, .nat (i : ℕ), .nat (j : ℕ)],
      encFun fun p : Fin (n * n) => (p : ℕ)]).wt + (encPerm (pairSwap i j)).wt + 1)) := by
    simp only [mapK]; ring
  rw [e2]
  simp only [one_mul, show 2 + 4 = 6 from rfl] at hX
  omega

/-! ### All generators -/

/-- On `[[n, ids], t]`: the generator of position `t = (t / n, t % n)`. -/
def genF (em : ℕ) : Expr :=
  .call em (mk2 (mk3 (.get (arg 0) (.nat 0)) (.arith .div (arg 1) (.get (arg 0) (.nat 0)))
    (.arith .mod (arg 1) (.get (arg 0) (.nat 0)))) (.get (arg 0) (.nat 1)))

theorem genF_spec {P : Program} {f em : ℕ} (hf : P.funs[f]? = some (genF em))
    (hm : P.HasAt em (entMapFuns em)) (t : Fin (n * n)) :
    FunDet P f (.list [.list [.nat n, encFun fun p : Fin (n * n) => (p : ℕ)], .nat t])
      (encPerm (pairSwap t.divNat t.modNat)) (90000 * (n + 1) ^ 6) := by
  set ids := encFun fun p : Fin (n * n) => (p : ℕ) with hids
  set B := Val.list [.nat n, ids] with hB
  set A := Val.list [B, .nat t] with hA
  have g0 : Det P [A] (.get (arg 0) (.nat 0)) (.nat n) _ :=
    Det.get' (Det.arg' (vs := [B, .nat t]) (rest := []) (j := 0) rfl) (Det.nat 0)
      (show [Val.nat n, ids][0]? = some (.nat n) from rfl)
  have g1 : Det P [A] (.get (arg 0) (.nat 1)) ids _ :=
    Det.get' (Det.arg' (vs := [B, .nat t]) (rest := []) (j := 0) rfl) (Det.nat 1)
      (show [Val.nat n, ids][1]? = some ids from rfl)
  have d1 := Det.arith' (op := .div) (z := (t.divNat : ℕ))
    (Det.arg' (P := P) (vs := [B, .nat t]) (rest := []) (j := 1) rfl) g0 rfl
  have d2 := Det.arith' (op := .mod) (z := (t.modNat : ℕ))
    (Det.arg' (P := P) (vs := [B, .nat t]) (rest := []) (j := 1) rfl) g0 rfl
  refine FunDet.intro hf ((Det.call (Det.mk2 (Det.mk3 g0 d1 d2) g1)
    (entMap_spec hm t.divNat t.modNat)).mono ?_)
  have := t.isLt
  have h1 : (t.divNat : ℕ) ≤ t := Nat.div_le_self _ _
  have h2 : (t.modNat : ℕ) ≤ t := Nat.mod_le _ _
  have w0 := wt_nat_le n
  have w1 := wt_nat_le (t : ℕ)
  have w2 := wt_nat_le (t.divNat : ℕ)
  have w3 := wt_nat_le (t.modNat : ℕ)
  have wi : ids.wt ≤ 4 * (n * n + 1) ^ 2 := wt_ids_le (n * n)
  have wB := wt_list2_le (.nat n) ids
  have wA := wt_list2_le B (.nat (t : ℕ))
  have w4 := wt_list3_le (.nat n) (.nat (t.divNat : ℕ)) (.nat (t.modNat : ℕ))
  have w5 := wt_list2_le (.list [.nat n, .nat (t.divNat : ℕ), .nat (t.modNat : ℕ)]) ids
  have w6 := wt_encPerm_le (pairSwap t.divNat t.modNat)
  have eB : (Val.list [.nat n, ids]).wt = B.wt := rfl
  have eA : (Val.list [B, .nat (t : ℕ)]).wt = A.wt := rfl
  have hsq := sq_le_pow n
  have hm2 : (n * n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    calc (n * n + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = (n + 1) ^ 4 := by ring
  have h46 := pow_le_pow_of_le n (show 4 ≤ 6 by omega)
  have h26 := pow_le_pow_of_le n (show 2 ≤ 6 by omega)
  have h14 : n + 1 ≤ (n + 1) ^ 4 := Nat.le_self_pow (by omega) _
  omega

/-- `map genF`, at base `b` (eight functions): the map, `genF`, and `entMapFuns`. -/
def genMapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [genF (b + 4)] ++ entMapFuns (b + 4)

theorem pairGens_map (n : ℕ) :
    (List.finRange (n * n)).map (fun t => encPerm (pairSwap t.divNat t.modNat)) =
      (pairGens n).map encPerm := by
  simp [pairGens, List.map_map, Function.comp_def]

theorem wt_pairGens_le (n : ℕ) :
    (Val.list ((pairGens n).map encPerm)).wt ≤ 13 * (n + 1) ^ 6 := by
  rw [← pairGens_map]
  have hsq := sq_le_pow n
  have hm2 : (n * n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    calc (n * n + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = (n + 1) ^ 4 := by ring
  have h1 := wt_listFin_le (fun t : Fin (n * n) => encPerm (pairSwap t.divNat t.modNat))
    (B := 4 * (n + 1) ^ 4) fun t => (wt_encPerm_le _).trans (by omega)
  have h2 : n * n * (2 * (4 * (n + 1) ^ 4) + 1) ≤ 9 * (n + 1) ^ 6 := by
    have := mul_pow_le (show n * n ≤ 1 * (n + 1) ^ 2 by omega)
      (show 2 * (4 * (n + 1) ^ 4) + 1 ≤ 9 * (n + 1) ^ 4 by
        have := one_le_pow_succ n 4; omega)
    simpa using this
  have := one_le_pow_succ n 6
  omega

/-- **All generators.** -/
theorem genMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (genMapFuns b)) :
    FunDet P b (.list [.list [.nat n, encFun fun p : Fin (n * n) => (p : ℕ)],
        encFun fun p : Fin (n * n) => (p : ℕ)])
      (.list ((pairGens n).map encPerm)) (200000 * (n + 1) ^ 8) := by
  simp only [genMapFuns] at h
  have hf : P.funs[b + 3]? = some (genF (b + 4)) := by
    simpa [mapFuns, loopFuns] using h.left.right.single
  have hm : P.HasAt (b + 4) (entMapFuns (b + 4)) := by
    simpa [mapFuns, loopFuns] using h.right
  rw [← pairGens_map]
  refine (tabulate_spec h.left.left (F := fun t => encPerm (pairSwap t.divNat t.modNat))
    fun t => genF_spec (n := n) hf hm t).mono ?_
  rw [pairGens_map]
  set ids := encFun fun p : Fin (n * n) => (p : ℕ) with hids
  have w0 := wt_nat_le n
  have wi : ids.wt ≤ 4 * (n * n + 1) ^ 2 := wt_ids_le (n * n)
  have wB := wt_list2_le (.nat n) ids
  have wA := wt_list2_le (.list [.nat n, ids]) ids
  have wg := wt_pairGens_le n
  have hsq := sq_le_pow n
  have hm2 : (n * n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    calc (n * n + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = (n + 1) ^ 4 := by ring
  have h48 := pow_le_pow_of_le n (show 4 ≤ 8 by omega)
  have h18 : n + 1 ≤ (n + 1) ^ 8 := Nat.le_self_pow (by omega) _
  have h68 := pow_le_pow_of_le n (show 6 ≤ 8 by omega)
  have hY : (Val.list [.list [.nat n, ids], ids]).wt + (Val.list ((pairGens n).map encPerm)).wt
      + 1 ≤ 100 * (n + 1) ^ 6 := by
    have := one_le_pow_succ n 6
    have h46 := pow_le_pow_of_le n (show 4 ≤ 6 by omega)
    have h16 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by omega) _
    omega
  have hm : n * n + 1 ≤ 1 * (n + 1) ^ 2 := by omega
  have hX := mul_pow_le hm hY
  have hc1 : n * n * (90000 * (n + 1) ^ 6) ≤ 90000 * (n + 1) ^ 8 := by
    have := mul_pow_le (show n * n ≤ 1 * (n + 1) ^ 2 by omega)
      (show 90000 * (n + 1) ^ 6 ≤ 90000 * (n + 1) ^ 6 from le_rfl)
    simpa using this
  have e2 : mapK * (n * n + 1) * ((Val.list [.list [.nat n, ids], ids]).wt +
      (Val.list ((pairGens n).map encPerm)).wt + 1) =
    1000 * ((n * n + 1) * ((Val.list [.list [.nat n, ids], ids]).wt +
      (Val.list ((pairGens n).map encPerm)).wt + 1)) := by
    simp only [mapK]; ring
  rw [e2]
  simp only [one_mul, show 2 + 6 = 8 from rfl] at hX
  have h8 := one_le_pow_succ n 8
  omega

end GI.Assembly
