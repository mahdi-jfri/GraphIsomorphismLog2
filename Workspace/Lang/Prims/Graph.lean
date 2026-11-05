/-
**Computing the action on blocks and its graph group** in `GI.Lang`.

The partition is given by representative labels, the value `encFun r` (`ReprVal`).
* `hatPtF`: on `[[r, g], y]`, the point `hatFun r g y`.
* `hatValFuns`: on `[encGroup gs, encFun r]`, the group value `encGroup (gs.map (hat r))` of
  `π(G)`, the action of `G = ⟨gs⟩` on the representatives.
* `graphValFuns`: on `[encGroup gs, encFun r]`, the value `encGroup ((gs.map (psi r)).map sumToFin)`
  of the graph group `{g ⊕ hat r g}` on `Fin (n + n)`, in the format of the preimage task.

Each point of `g ⊕ hat r g` is computed by `sumF` (one `if`), each generator by a `map` over the
points, and the list of generators by a `map` over the generators. For `m` generators the costs
are at most `hatValK * ((m + 2) * (n + 1)) ^ 3` and `graphValK * ((m + 2) * (n + 1)) ^ 3`.
-/
module

public import Workspace.Lang.Prims.BlockMath

@[expose] public section

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited
open Equiv

variable {n : ℕ}

/-! ### Values of points -/

theorem encFun_getElem?_nat (f : Fin n → ℕ) (x : ℕ) (h : x < n) :
    ((List.finRange n).map fun i => Val.nat (f i))[x]? = some (.nat (f ⟨x, h⟩)) := by
  simp [h]

theorem wt_encRepr_le (r : Fin n → Fin n) : (encFun fun i => (r i : ℕ)).wt ≤ 4 * (n + 1) ^ 2 :=
  wt_encFun_le_sq _ fun i => (r i).isLt.le

/-- The identity labels of `Fin N`. -/
abbrev idsVal (N : ℕ) : Val := encFun fun i : Fin N => (i : ℕ)

theorem idsVal_eq (N : ℕ) : idsVal N = encPerm (1 : Perm (Fin N)) := rfl

theorem wt_idsVal_le (N : ℕ) : (idsVal N).wt ≤ 4 * (N + 1) ^ 2 :=
  wt_encFun_le_sq _ fun i => i.isLt.le

/-- `if` on a known number, with the cost of both branches. -/
theorem Det.ite_sum {P : Program} {env : List Val} {c t e : Expr} {x : ℕ} {v1 v0 : Val}
    {cc ct ce : ℕ} (hc : Det P env c (.nat x) cc) (ht : Det P env t v1 ct)
    (he : Det P env e v0 ce) :
    Det P env (.ite c t e) (if x = 0 then v0 else v1) (cc + ct + ce + v1.wt + v0.wt + 1) :=
  (Det.ite' hc ht he).mono (by
    have h1 : max ct ce ≤ ct + ce := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    have h2 : max v1.wt v0.wt ≤ v1.wt + v0.wt := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    omega)

/-! ### One point of `hat r g` -/

/-- On `[[r, g], y]`: `r (g y)` if `y` is a representative, else `y`. -/
def hatPtF : Expr :=
  .ite (.arith .eq (.get (.get (arg 0) (.nat 0)) (arg 1)) (arg 1))
    (.get (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1)))
    (arg 1)

theorem hatPt_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some hatPtF) (r : Fin n → Fin n)
    (g : Perm (Fin n)) (y : Fin n) :
    FunDet P f (.list [.list [encFun fun i => (r i : ℕ), encPerm g], .nat y])
      (.nat (hatFun r g y)) (2000 * (n + 1) ^ 2) := by
  set L := encFun fun i => (r i : ℕ) with hL
  set A := Val.list [.list [L, encPerm g], .nat y] with hA
  have dL := Det.get' (P := P) (Det.arg' (vs := [.list [L, encPerm g], .nat y]) (rest := [])
    (j := 0) rfl) (Det.nat 0) (show [L, encPerm g][0]? = some L from rfl)
  have dG := Det.get' (P := P) (Det.arg' (vs := [.list [L, encPerm g], .nat y]) (rest := [])
    (j := 0) rfl) (Det.nat 1) (show [L, encPerm g][1]? = some (encPerm g) from rfl)
  have dY := Det.arg' (P := P) (vs := [.list [L, encPerm g], .nat y]) (rest := []) (j := 1) rfl
  have dry := Det.get' dL dY (encFun_getElem? (fun i => (r i : ℕ)) y)
  have dc := Det.arith' (op := .eq) dry dY rfl
  have dgy := Det.applyPerm dG dY
  have drgy := Det.get' dL dgy (encFun_getElem? (fun i => (r i : ℕ)) (g y))
  have hb := Det.ite_sum dc drgy dY
  have hv : (if BinOp.eval .eq (r y : ℕ) (y : ℕ) = 0 then Val.nat (y : ℕ)
      else Val.nat (r (g y) : ℕ)) = .nat (hatFun r g y) := by
    simp only [BinOp.eval, hatFun, Fin.val_inj]
    by_cases h : r y = y <;> simp [h]
  rw [hv] at hb
  refine FunDet.intro hf (hb.mono ?_)
  have w1 : L.wt ≤ 4 * (n + 1) ^ 2 := wt_encRepr_le r
  have w2 := wt_encPerm_le g
  have w3 := wt_list2_le L (encPerm g)
  have w4 := wt_list2_le (.list [L, encPerm g]) (.nat y)
  have w5 := wt_nat_le (y : ℕ)
  have w6 := wt_nat_le (r y : ℕ)
  have w7 := wt_nat_le (g y : ℕ)
  have w8 := wt_nat_le (r (g y) : ℕ)
  have w9 := wt_nat_le (hatFun r g y : ℕ)
  have w10 := wt_nat_le (BinOp.eval .eq (r y : ℕ) (y : ℕ))
  have := y.isLt
  have := (r y).isLt
  have := (g y).isLt
  have := (r (g y)).isLt
  have := (hatFun r g y).isLt
  have h8 : BinOp.eval .eq (r y : ℕ) (y : ℕ) ≤ 1 := by
    simp only [BinOp.eval]; split_ifs <;> omega
  have hN : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  omega

/-! ### One point of `g ⊕ hat r g` on `Fin (n + n)` -/

theorem sumToFin_sumCongr_apply (a b : Perm (Fin n)) (x : Fin (n + n)) :
    (sumToFin (Equiv.sumCongr a b) x : ℕ) =
      if h : (x : ℕ) < n then (a ⟨x, h⟩ : ℕ) else n + b ⟨x - n, by omega⟩ := by
  induction x using Fin.addCases with
  | left i => simp [sumToFin]
  | right j =>
    simp only [sumToFin, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
      Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right, Fin.val_natAdd]
    simp

/-- On `[[n, r, g], x]` with `x < n + n`: `g x` if `x < n`, else `n + hatFun r g (x - n)`. -/
def sumF (hp : ℕ) : Expr :=
  .ite (.arith .lt (arg 1) (.get (arg 0) (.nat 0))) (.get (.get (arg 0) (.nat 2)) (arg 1))
    (.arith .add (.get (arg 0) (.nat 0))
      (.call hp (mk2 (mk2 (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)))
        (.arith .sub (arg 1) (.get (arg 0) (.nat 0))))))

theorem sum_spec {P : Program} {f hp : ℕ} (hf : P.funs[f]? = some (sumF hp))
    (hhp : P.funs[hp]? = some hatPtF) {r : Fin n → Fin n} (hr : IsRepr r) {g : Perm (Fin n)}
    (hg : g ∈ presR r) (x : Fin (n + n)) :
    FunDet P f (.list [.list [.nat n, encFun fun i => (r i : ℕ), encPerm g], .nat x])
      (.nat (sumToFin (psi r g) x)) (10000 * (n + 1) ^ 2) := by
  set L := encFun fun i => (r i : ℕ) with hL
  set C := Val.list [.nat n, L, encPerm g] with hC
  have d0 := Det.arg' (P := P) (vs := [C, .nat x]) (rest := []) (j := 0) rfl
  have dX := Det.arg' (P := P) (vs := [C, .nat x]) (rest := []) (j := 1) rfl
  have dN := Det.get' d0 (Det.nat 0) (show [Val.nat n, L, encPerm g][0]? = some (.nat n) from rfl)
  have dL := Det.get' d0 (Det.nat 1) (show [Val.nat n, L, encPerm g][1]? = some L from rfl)
  have dG := Det.get' d0 (Det.nat 2)
    (show [Val.nat n, L, encPerm g][2]? = some (encPerm g) from rfl)
  have dc := Det.arith' (op := .lt) dX dN rfl
  have w1 : L.wt ≤ 4 * (n + 1) ^ 2 := wt_encRepr_le r
  have w2 := wt_encPerm_le g
  have w3 : C.wt ≤ 2 * ((Val.nat n).wt + L.wt + (encPerm g).wt) + 7 :=
    wt_list3_le (.nat n) L (encPerm g)
  have w4 := wt_list2_le C (.nat x)
  have w5 := wt_nat_le (x : ℕ)
  have w6 := wt_nat_le n
  have hx := x.isLt
  have hN : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hlt : BinOp.eval .lt (x : ℕ) n ≤ 1 := by simp only [BinOp.eval]; split_ifs <;> omega
  rw [psi, sumToFin_sumCongr_apply]
  by_cases hxn : (x : ℕ) < n
  · have dv := Det.get' dG dX (encFun_getElem?_nat (fun i => (g i : ℕ)) x hxn)
    have hb := Det.ite_pos dc (by simp [BinOp.eval, hxn]) dv (e := .arith .add
      (.get (arg 0) (.nat 0)) (.call hp (mk2 (mk2 (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)))
        (.arith .sub (arg 1) (.get (arg 0) (.nat 0))))))
    rw [dif_pos hxn]
    refine FunDet.intro hf (hb.mono ?_)
    have := wt_nat_le (g ⟨x, hxn⟩ : ℕ)
    have := (g ⟨x, hxn⟩).isLt
    omega
  · have hy : (x : ℕ) - n < n := by omega
    have dsub := Det.arith' (op := .sub) dX dN (z := (x : ℕ) - n) rfl
    have dH := Det.call (Det.mk2 (Det.mk2 dL dG) dsub) (hatPt_spec hhp r g ⟨(x : ℕ) - n, hy⟩)
    have dadd := Det.arith' (op := .add) dN dH (z := n + hatFun r g ⟨(x : ℕ) - n, hy⟩) rfl
    have hb := Det.ite_zero (t := .get (.get (arg 0) (.nat 2)) (arg 1))
      (by simpa [BinOp.eval, hxn] using dc) dadd
    rw [dif_neg hxn, hat_apply hr hg]
    refine FunDet.intro hf (hb.mono ?_)
    have := (hatFun r g ⟨(x : ℕ) - n, hy⟩).isLt
    have := wt_nat_le (n + hatFun r g ⟨(x : ℕ) - n, hy⟩ : ℕ)
    have := wt_nat_le ((x : ℕ) - n)
    have := wt_nat_le (hatFun r g ⟨(x : ℕ) - n, hy⟩ : ℕ)
    have := wt_list2_le L (encPerm g)
    have := wt_list2_le (.list [L, encPerm g]) (.nat ((x : ℕ) - n))
    omega

/-! ### One generator of the graph group -/

/-- On `[[n, r, ids], g]`, with `ids` the points of `Fin (n + n)`: the permutation
`sumToFin (g ⊕ hat r g)`, by a `map` of `sumF` over `ids`. -/
def graphF (im : ℕ) : Expr :=
  .call im (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1)) (.get (arg 0) (.nat 2)))

theorem sq_nn_le (n : ℕ) : (n + n + 1) ^ 2 ≤ 4 * (n + 1) ^ 2 := by
  calc (n + n + 1) ^ 2 ≤ (2 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = 4 * (n + 1) ^ 2 := by ring

theorem wt_encPerm_sum_le (σ : Perm (Fin (n + n))) : (encPerm σ).wt ≤ 16 * (n + 1) ^ 2 := by
  have := wt_encPerm_le σ
  have := sq_nn_le n
  omega

theorem graphF_spec {P : Program} {f im hp : ℕ} (hf : P.funs[f]? = some (graphF im))
    (hm : P.HasAt im (mapFuns im (im + 3))) (hs : P.funs[im + 3]? = some (sumF hp))
    (hhp : P.funs[hp]? = some hatPtF) {r : Fin n → Fin n} (hr : IsRepr r) {g : Perm (Fin n)}
    (hg : g ∈ presR r) :
    FunDet P f (.list [.list [.nat n, encFun fun i => (r i : ℕ), idsVal (n + n)], encPerm g])
      (encPerm (sumToFin (psi r g))) (300000 * (n + 1) ^ 3) := by
  generalize hL : (encFun fun i => (r i : ℕ)) = L
  have w1 : L.wt ≤ 4 * (n + 1) ^ 2 := hL ▸ wt_encRepr_le r
  have hM := mapList_spec hm (List.finRange (n + n)) (fun i => Val.nat (i : ℕ))
    (fun i => Val.nat (sumToFin (psi r g) i)) (c := .list [.nat n, L, encPerm g])
    (B := 10000 * (n + 1) ^ 2)
    (fun a _ a' _ he => by simp only [Val.nat.injEq] at he; rw [Fin.ext he])
    (fun i _ => hL ▸ sum_spec hs hhp hr hg i)
  have d0 := Det.arg' (P := P) (vs := [.list [.nat n, L, idsVal (n + n)], encPerm g]) (rest := [])
    (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [.nat n, L, idsVal (n + n)], encPerm g]) (rest := [])
    (j := 1) rfl
  have dN := Det.get' d0 (Det.nat 0)
    (show [Val.nat n, L, idsVal (n + n)][0]? = some (.nat n) from rfl)
  have dL := Det.get' d0 (Det.nat 1) (show [Val.nat n, L, idsVal (n + n)][1]? = some L from rfl)
  have dI := Det.get' d0 (Det.nat 2)
    (show [Val.nat n, L, idsVal (n + n)][2]? = some (idsVal (n + n)) from rfl)
  have dcall := Det.call (Det.mk2 (Det.mk3 dN dL d1) dI) hM
  refine FunDet.intro hf (dcall.mono ?_)
  have w2 := wt_encPerm_le g
  have w3 := wt_list3_le (.nat n) L (encPerm g)
  have w4 : (idsVal (n + n)).wt ≤ 16 * (n + 1) ^ 2 := by
    have := wt_idsVal_le (n + n); have := sq_nn_le n; omega
  have w5 := wt_list3_le (.nat n) L (idsVal (n + n))
  have w6 := wt_list2_le (.list [.nat n, L, idsVal (n + n)]) (encPerm g)
  have w7 := wt_list2_le (.list [.nat n, L, encPerm g]) (idsVal (n + n))
  have w8 := wt_encPerm_sum_le (sumToFin (psi r g))
  have w9 := wt_nat_le n
  have e1 : (Val.list ((List.finRange (n + n)).map fun i => Val.nat (sumToFin (psi r g) i))).wt =
    (encPerm (sumToFin (psi r g))).wt := congrArg Val.wt rfl
  have e2 : (Val.list [.list [.nat n, L, encPerm g],
      .list ((List.finRange (n + n)).map fun i : Fin (n + n) => Val.nat (i : ℕ))]).wt =
    (Val.list [.list [.nat n, L, encPerm g], idsVal (n + n)]).wt := congrArg Val.wt rfl
  rw [List.length_finRange]
  have hN : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have h1 : mapK * (n + n + 1) * ((Val.list [.list [.nat n, L, encPerm g],
      .list ((List.finRange (n + n)).map fun i : Fin (n + n) => Val.nat (i : ℕ))]).wt +
      (Val.list ((List.finRange (n + n)).map fun i => Val.nat (sumToFin (psi r g) i))).wt + 1) ≤
      mapK * (2 * (n + 1)) * (130 * (n + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e3 : mapK * (2 * (n + 1)) * (130 * (n + 1) ^ 2) = 260000 * (n + 1) ^ 3 := by
    simp only [mapK]; ring
  have h2 : (n + n) * (10000 * (n + 1) ^ 2) ≤ 20000 * (n + 1) ^ 3 := by nlinarith
  have h3 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-! ### The graph group -/

theorem sumToFin_one {n' : ℕ} : sumToFin (1 : Perm (Fin n ⊕ Fin n')) = 1 := by
  ext x; simp [sumToFin]

/-- On `[encGroup gs, encFun r]`: the graph group value. -/
def graphEntry (rg om : ℕ) : Expr :=
  .letE (.call rg (.arith .add (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0))))
    (mk2 (.arith .add (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0)))
      (.call om (mk2 (mk3 (.get (arg 0) (.nat 0)) (arg 1) (.var 1)) (.get (arg 0) (.nat 1)))))

/-- The graph group program, at base `b` (nine functions), with `range` at `rg` and `hatPtF` at
`hp`. -/
def graphValFuns (b rg hp : ℕ) : List Expr :=
  [graphEntry rg (b + 1)] ++ mapFuns (b + 1) (b + 4) ++ [graphF (b + 5)] ++ mapFuns (b + 5) (b + 8) ++
    [sumF hp]

/-- The constant of the graph group program. -/
def graphValK : ℕ := 1000000

/-- The value of the graph group, in the format of the preimage task. -/
theorem graphVal_eq {r : Fin n → Fin n} (hr : IsRepr r) (gs : List (Perm (Fin n))) :
    Val.list [.nat (n + n), .list ((1 :: gs).map fun g => encPerm (sumToFin (psi r g)))] =
      encGroup ((gs.map (psi r)).map sumToFin) := by
  simp [encGroup, encPerms, psi_one hr, sumToFin_one]

/-- **The graph group of the action on blocks.** On `[encGroup gs, encFun r]`, where every
generator preserves the partition, the result is the value of the graph group `{g ⊕ hat r g}`
on `Fin (n + n)`. -/
theorem graphVal_spec {P : Program} {b rg hp : ℕ} (h : P.HasAt b (graphValFuns b rg hp))
    (hrg : P.HasAt rg (rangeFuns rg)) (hhp : P.funs[hp]? = some hatPtF)
    {r : Fin n → Fin n} (hr : IsRepr r) {gs : List (Perm (Fin n))}
    (hgs : ∀ g ∈ gs, g ∈ presR r) :
    FunDet P b (.list [encGroup gs, encFun fun i => (r i : ℕ)])
      (encGroup ((gs.map (psi r)).map sumToFin)) (graphValK * ((gs.length + 2) * (n + 1)) ^ 3) := by
  simp only [graphValFuns] at h
  have hentry : P.funs[b]? = some (graphEntry rg (b + 1)) := h.left.left.left.left.single
  have hom : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := by simpa using h.left.left.left.right
  have hgf : P.funs[b + 4]? = some (graphF (b + 5)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.left.left.right.single
  have him : P.HasAt (b + 5) (mapFuns (b + 5) (b + 8)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.left.right
  have hsf : P.funs[b + 5 + 3]? = some (sumF hp) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.right.single
  set L := encFun fun i => (r i : ℕ) with hL
  set E := Val.list [encGroup gs, L] with hE
  have hgs1 : ∀ g ∈ 1 :: gs, g ∈ presR r := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact (presR r).one_mem
    · exact hgs g hg
  have hO := mapList_spec hom (1 :: gs) encPerm (fun g => encPerm (sumToFin (psi r g)))
    (c := .list [.nat n, L, idsVal (n + n)]) (B := 300000 * (n + 1) ^ 3)
    (fun a _ a' _ he => by rw [encPerm_injective he])
    (fun g hg => graphF_spec hgf him hsf hhp hr (hgs1 g hg))
  have d0 := Det.arg' (P := P) (vs := [encGroup gs, L]) (rest := []) (j := 0) rfl
  have dN := Det.get' (P := P) (env := [E]) d0 (Det.nat 0)
    (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][0]? = some (.nat n) from rfl)
  have dNN := Det.arith' (op := .add) dN dN (z := n + n) rfl
  have hR := Det.call dNN (range_det hrg (n + n))
  -- in the environment `[E, ids]`
  have d0' := Det.arg' (P := P) (vs := [encGroup gs, L]) (rest := [idsVal (n + n)]) (j := 0) rfl
  have d1' := Det.arg' (P := P) (vs := [encGroup gs, L]) (rest := [idsVal (n + n)]) (j := 1) rfl
  have dN' := Det.get' d0' (Det.nat 0)
    (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][0]? = some (.nat n) from rfl)
  have dNN' := Det.arith' (op := .add) dN' dN' (z := n + n) rfl
  have dG' := Det.get' d0' (Det.nat 1)
    (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][1]? =
      some (.list ((1 :: gs).map encPerm)) from rfl)
  have dV := Det.var' (P := P) (env := [E, idsVal (n + n)]) (i := 1) rfl
  have dC := Det.call (Det.mk2 (Det.mk3 dN' d1' dV) dG') hO
  have hB := Det.letE hR (Det.mk2 dNN' dC)
  rw [graphVal_eq hr] at hB
  refine FunDet.intro hentry (hB.mono ?_)
  -- the cost
  have w1 : L.wt ≤ 4 * (n + 1) ^ 2 := wt_encRepr_le r
  have w2 := wt_encGroup_le gs
  have w3 : (idsVal (n + n)).wt ≤ 16 * (n + 1) ^ 2 := by
    have := wt_idsVal_le (n + n); have := sq_nn_le n; omega
  have w4 := wt_list_encPerms_le (1 :: gs)
  have w5 : (Val.list ((1 :: gs).map fun g => encPerm (sumToFin (psi r g)))).wt ≤
      13 * ((gs.length + 2) * (n + n + 1)) ^ 2 := by
    have := wt_list_encPerms_le ((1 :: gs).map fun g => sumToFin (psi r g))
    simpa [List.map_map, Function.comp_def, Nat.add_assoc] using this
  have w6 : E.wt ≤ 2 * ((encGroup gs).wt + L.wt) + 6 := wt_list2_le _ _
  have w7 : (encGroup gs).wt < E.wt := wt_le_wt_list (by simp)
  have eE : E.wt = (Val.list [encGroup gs, L]).wt := rfl
  have w8 : (Val.list [.nat n, L, idsVal (n + n)]).wt ≤
      2 * ((Val.nat n).wt + L.wt + (idsVal (n + n)).wt) + 7 := wt_list3_le _ _ _
  have w9 : (Val.list [Val.list [.nat n, L, idsVal (n + n)], .list ((1 :: gs).map encPerm)]).wt ≤
      2 * ((Val.list [.nat n, L, idsVal (n + n)]).wt + (Val.list ((1 :: gs).map encPerm)).wt) + 6 :=
    wt_list2_le _ _
  have w10 : (encGroup ((gs.map (psi r)).map sumToFin)).wt ≤
      2 * ((Val.nat (n + n)).wt +
        (Val.list ((1 :: gs).map fun g => encPerm (sumToFin (psi r g)))).wt) + 6 := by
    rw [← graphVal_eq hr]; exact wt_list2_le _ _
  have w11 := wt_nat_le n
  have w12 := wt_nat_le (n + n)
  have w13 : (encPerm (1 : Perm (Fin (n + n)))).wt = (idsVal (n + n)).wt := rfl
  simp only [List.length_cons] at w4 w5 ⊢
  generalize hS : (gs.length + 2) * (n + 1) = S at *
  obtain ⟨hmS, hnS⟩ := le_S gs.length n
  rw [hS] at hmS hnS
  have hS1 : 1 ≤ S := by omega
  have e4 : ((gs.length + 1 + 1) * (n + 1)) ^ 2 = S ^ 2 := by rw [← hS]
  have e5 : ((gs.length + 2) * (n + n + 1)) ^ 2 ≤ 4 * S ^ 2 := by
    rw [← hS]; nlinarith
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hnS 2
  have hN3 : (n + 1) ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left hnS 3
  have hS12 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by omega)
  have hR3 : (n + n + 1) ^ 3 ≤ 8 * S ^ 3 := by
    have : n + n + 1 ≤ 2 * S := by omega
    calc (n + n + 1) ^ 3 ≤ (2 * S) ^ 3 := Nat.pow_le_pow_left this 3
      _ = 8 * S ^ 3 := by ring
  have h1 : (gs.length + 1) * (300000 * (n + 1) ^ 3) ≤ 300000 * S ^ 3 := by
    have : (gs.length + 1) * (n + 1) ^ 3 ≤ S ^ 3 := by
      rw [← hS, mul_pow]
      exact Nat.mul_le_mul_right _ (le_trans (by omega) (Nat.le_self_pow (by norm_num) _))
    nlinarith
  have h2 : mapK * (gs.length + 1 + 1) * ((Val.list [Val.list [.nat n, L, idsVal (n + n)],
      .list ((1 :: gs).map encPerm)]).wt +
      (Val.list ((1 :: gs).map fun g => encPerm (sumToFin (psi r g)))).wt + 1) ≤
      mapK * S * (300 * S ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e6 : mapK * S * (300 * S ^ 2) = 300000 * S ^ 3 := by simp only [mapK]; ring
  have h3 : 8000 * (n + n + 1) ^ 3 ≤ 64000 * S ^ 3 := by omega
  simp only [graphValK]
  omega

/-! ### The action on the representatives -/

/-- On `[[r, ids], g]`, with `ids` the points of `Fin n`: the permutation `hat r g`, by a `map` of
`hatPtF` over `ids`. -/
def hatF (im : ℕ) : Expr :=
  .call im (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))

theorem hatF_spec {P : Program} {f im hp : ℕ} (hf : P.funs[f]? = some (hatF im))
    (hm : P.HasAt im (mapFuns im hp)) (hhp : P.funs[hp]? = some hatPtF) {r : Fin n → Fin n}
    (hr : IsRepr r) {g : Perm (Fin n)} (hg : g ∈ presR r) :
    FunDet P f (.list [.list [encFun fun i => (r i : ℕ), idsVal n], encPerm g])
      (encPerm (hat r g)) (100000 * (n + 1) ^ 3) := by
  generalize hL : (encFun fun i => (r i : ℕ)) = L
  have w1 : L.wt ≤ 4 * (n + 1) ^ 2 := hL ▸ wt_encRepr_le r
  have hM := mapList_spec hm (List.finRange n) (fun i => Val.nat (i : ℕ))
    (fun i => Val.nat (hat r g i)) (c := .list [L, encPerm g])
    (B := 2000 * (n + 1) ^ 2)
    (fun a _ a' _ he => by simp only [Val.nat.injEq] at he; rw [Fin.ext he])
    (fun i _ => by beta_reduce; rw [hat_apply hr hg]; exact hL ▸ hatPt_spec hhp r g i)
  have d0 := Det.arg' (P := P) (vs := [.list [L, idsVal n], encPerm g]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [L, idsVal n], encPerm g]) (rest := []) (j := 1) rfl
  have dL := Det.get' d0 (Det.nat 0) (show [L, idsVal n][0]? = some L from rfl)
  have dI := Det.get' d0 (Det.nat 1) (show [L, idsVal n][1]? = some (idsVal n) from rfl)
  have dcall := Det.call (Det.mk2 (Det.mk2 dL d1) dI) hM
  refine FunDet.intro hf (dcall.mono ?_)
  have w2 := wt_encPerm_le g
  have w3 := wt_list2_le L (encPerm g)
  have w4 := wt_idsVal_le n
  have w5 := wt_list2_le L (idsVal n)
  have w6 := wt_list2_le (.list [L, idsVal n]) (encPerm g)
  have w7 := wt_list2_le (.list [L, encPerm g]) (idsVal n)
  have w8 := wt_encPerm_le (hat r g)
  have e1 : (Val.list ((List.finRange n).map fun i => Val.nat (hat r g i))).wt =
    (encPerm (hat r g)).wt := congrArg Val.wt rfl
  have e2 : (Val.list [.list [L, encPerm g],
      .list ((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ))]).wt =
    (Val.list [.list [L, encPerm g], idsVal n]).wt := congrArg Val.wt rfl
  rw [List.length_finRange]
  have hN : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have h1 : mapK * (n + 1) * ((Val.list [.list [L, encPerm g],
      .list ((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ))]).wt +
      (Val.list ((List.finRange n).map fun i => Val.nat (hat r g i))).wt + 1) ≤
      mapK * (n + 1) * (70 * (n + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have e3 : mapK * (n + 1) * (70 * (n + 1) ^ 2) = 70000 * (n + 1) ^ 3 := by
    simp only [mapK]; ring
  have h2 : n * (2000 * (n + 1) ^ 2) ≤ 2000 * (n + 1) ^ 3 := by nlinarith
  have h3 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- On `[encGroup gs, encFun r]`: the group value of `π(G)`. -/
def hatEntry (rg om : ℕ) : Expr :=
  .letE (.call rg (.get (arg 0) (.nat 0)))
    (mk2 (.get (arg 0) (.nat 0)) (.call om (mk2 (mk2 (arg 1) (.var 1)) (.get (arg 0) (.nat 1)))))

/-- The program of `π(G)`, at base `b` (eight functions), with `range` at `rg` and `hatPtF` at
`hp`. -/
def hatValFuns (b rg hp : ℕ) : List Expr :=
  [hatEntry rg (b + 1)] ++ mapFuns (b + 1) (b + 4) ++ [hatF (b + 5)] ++ mapFuns (b + 5) hp

/-- The constant of the program of `π(G)`. -/
def hatValK : ℕ := 500000

theorem hatVal_eq {r : Fin n → Fin n} (hr : IsRepr r) (gs : List (Perm (Fin n))) :
    Val.list [.nat n, .list ((1 :: gs).map fun g => encPerm (hat r g))] =
      encGroup (gs.map (hat r)) := by
  simp [encGroup, encPerms, hat_one hr]

/-- **The action on the representatives.** On `[encGroup gs, encFun r]`, where every generator
preserves the partition, the result is the group value of `π(G) = ⟨hat r g | g ∈ gs⟩`. -/
theorem hatVal_spec {P : Program} {b rg hp : ℕ} (h : P.HasAt b (hatValFuns b rg hp))
    (hrg : P.HasAt rg (rangeFuns rg)) (hhp : P.funs[hp]? = some hatPtF)
    {r : Fin n → Fin n} (hr : IsRepr r) {gs : List (Perm (Fin n))}
    (hgs : ∀ g ∈ gs, g ∈ presR r) :
    FunDet P b (.list [encGroup gs, encFun fun i => (r i : ℕ)])
      (encGroup (gs.map (hat r))) (hatValK * ((gs.length + 2) * (n + 1)) ^ 3) := by
  simp only [hatValFuns] at h
  have hentry : P.funs[b]? = some (hatEntry rg (b + 1)) := h.left.left.left.single
  have hom : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := by simpa using h.left.left.right
  have hhf : P.funs[b + 4]? = some (hatF (b + 5)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.left.right.single
  have him : P.HasAt (b + 5) (mapFuns (b + 5) hp) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using h.right
  generalize hL : (encFun fun i => (r i : ℕ)) = L
  have w1 : L.wt ≤ 4 * (n + 1) ^ 2 := hL ▸ wt_encRepr_le r
  have hgs1 : ∀ g ∈ 1 :: gs, g ∈ presR r := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact (presR r).one_mem
    · exact hgs g hg
  have hO := mapList_spec hom (1 :: gs) encPerm (fun g => encPerm (hat r g))
    (c := .list [L, idsVal n]) (B := 100000 * (n + 1) ^ 3)
    (fun a _ a' _ he => by rw [encPerm_injective he])
    (fun g hg => hL ▸ hatF_spec hhf him hhp hr (hgs1 g hg))
  have d0 := Det.arg' (P := P) (vs := [encGroup gs, L]) (rest := []) (j := 0) rfl
  have dN := Det.get' (P := P) d0 (Det.nat 0)
    (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][0]? = some (.nat n) from rfl)
  have hR := Det.call dN (range_det hrg n)
  have d0' := Det.arg' (P := P) (vs := [encGroup gs, L]) (rest := [idsVal n]) (j := 0) rfl
  have d1' := Det.arg' (P := P) (vs := [encGroup gs, L]) (rest := [idsVal n]) (j := 1) rfl
  have dN' := Det.get' d0' (Det.nat 0)
    (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][0]? = some (.nat n) from rfl)
  have dG' := Det.get' d0' (Det.nat 1)
    (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][1]? =
      some (.list ((1 :: gs).map encPerm)) from rfl)
  have dV := Det.var' (P := P) (env := [Val.list [encGroup gs, L], idsVal n]) (i := 1) rfl
  have dC := Det.call (Det.mk2 (Det.mk2 d1' dV) dG') hO
  have hB := Det.letE hR (Det.mk2 dN' dC)
  rw [hatVal_eq hr] at hB
  refine FunDet.intro hentry (hB.mono ?_)
  -- the cost
  have w2 := wt_encGroup_le gs
  have w3 := wt_idsVal_le n
  have w4 := wt_list_encPerms_le (1 :: gs)
  have w5 : (Val.list ((1 :: gs).map fun g => encPerm (hat r g))).wt ≤
      13 * ((gs.length + 2) * (n + 1)) ^ 2 := by
    have := wt_list_encPerms_le ((1 :: gs).map fun g => hat r g)
    simpa [List.map_map, Function.comp_def, Nat.add_assoc] using this
  have w6 := wt_list2_le (encGroup gs) L
  have w8 := wt_list2_le L (idsVal n)
  have w9 := wt_list2_le (.list [L, idsVal n]) (.list ((1 :: gs).map encPerm))
  have w10 : (encGroup (gs.map (hat r))).wt ≤
      2 * ((Val.nat n).wt + (Val.list ((1 :: gs).map fun g => encPerm (hat r g))).wt) + 6 := by
    rw [← hatVal_eq hr]; exact wt_list2_le _ _
  have w11 := wt_nat_le n
  have w13 : (encPerm (1 : Perm (Fin n))).wt = (idsVal n).wt := rfl
  simp only [List.length_cons] at w4 w5 ⊢
  generalize hS : (gs.length + 2) * (n + 1) = S at *
  obtain ⟨hmS, hnS⟩ := le_S gs.length n
  rw [hS] at hmS hnS
  have hS1 : 1 ≤ S := by omega
  have e4 : ((gs.length + 1 + 1) * (n + 1)) ^ 2 = S ^ 2 := by rw [← hS]
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hnS 2
  have hN3 : (n + 1) ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left hnS 3
  have hS12 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by omega)
  have h1 : (gs.length + 1) * (100000 * (n + 1) ^ 3) ≤ 100000 * S ^ 3 := by
    have : (gs.length + 1) * (n + 1) ^ 3 ≤ S ^ 3 := by
      rw [← hS, mul_pow]
      exact Nat.mul_le_mul_right _ (le_trans (by omega) (Nat.le_self_pow (by norm_num) _))
    nlinarith
  have h2 : mapK * (gs.length + 1 + 1) * ((Val.list [Val.list [L, idsVal n],
      .list ((1 :: gs).map encPerm)]).wt +
      (Val.list ((1 :: gs).map fun g => encPerm (hat r g))).wt + 1) ≤
      mapK * S * (100 * S ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e6 : mapK * S * (100 * S ^ 2) = 100000 * S ^ 3 := by simp only [mapK]; ring
  simp only [hatValK]
  omega

end GI.Lang
