import Workspace.Impl.GenProdMath
import Workspace.Impl.GenCls

/-!
# The product refinement: permutations of the pairs

The coset representatives and the generators of the coordinate group are computed on the pairs
of points (`Fin (k * k)`), where `g` acts as `g × g` (`sqPerm`). This file has the two
conversions as programs:

* `sqGens_spec`: the list of the `g × g`, on `[k, gens, [0, …, k² - 1]]`;
* `unsq_spec`: back from `g × g` to `g`, by `g p = (g × g)(k p) / k`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

/-- **A deterministic map.** -/
theorem map_det {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val} {xs : List Val}
    {F : Val → Val} {B : ℕ} (hf : ∀ x ∈ xs, FunDet P f (.list [c, x]) (F x) B) :
    FunDet P b (.list [c, .list xs]) (.list (xs.map F))
      (xs.length * B + mapK * (xs.length + 1) * ((Val.list [c, .list xs]).wt +
        (Val.list (xs.map F)).wt + 1)) := by
  refine (map_spec h (R := fun x w => w = F x) (B := fun _ => B) hf).mono fun w c hw => ?_
  obtain ⟨ws, rfl, hR, hc⟩ := hw
  rw [forall₂_eq_map hR] at hc ⊢
  refine ⟨rfl, ?_⟩
  simpa using hc

variable {k : ℕ}

/-- On `[[k, g], j]`: `g (j / k) · k + g (j mod k)`. -/
def sqEntF : Expr :=
  let K := Expr.get (arg 0) (.nat 0)
  let G := Expr.get (arg 0) (.nat 1)
  .arith .add (.arith .mul (.get G (.arith .div (arg 1) K)) K) (.get G (.arith .mod (arg 1) K))

/-- On `[[k, ids], g]`: `g × g`, by `map sqEntF` over the pairs `ids`. -/
def sqPermF (bm : ℕ) : Expr := .call bm (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))

/-- The constant of the squaring. -/
def sqK : ℕ := 10 ^ 9

set_option maxHeartbeats 1000000 in
theorem sqEnt_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some sqEntF) (g : Perm (Fin k))
    (j : Fin (k * k)) :
    FunDet P f (.list [.list [.nat k, encPerm g], .nat j]) (.nat (sqPerm g j))
      (1000 * ((encPerm g).wt + k * k + 10)) := by
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd j.2 (by simp [h])
    · exact h
  set A := Val.list [.list [.nat k, encPerm g], .nat j] with hA
  have dA := Det.arg' (P := P) (vs := [.list [.nat k, encPerm g], .nat j]) (rest := []) (j := 0) rfl
  have dJ := Det.arg' (P := P) (vs := [.list [.nat k, encPerm g], .nat j]) (rest := []) (j := 1) rfl
  have dK := Det.get' dA (Det.nat 0) (v := .nat k) rfl
  have dG := Det.get' dA (Det.nat 1) (v := encPerm g) rfl
  have hp : (j : ℕ) / k < k := Nat.div_lt_of_lt_mul j.2
  have hq : (j : ℕ) % k < k := Nat.mod_lt _ hk0
  have dP := Det.get' dG (Det.arith' (op := .div) dJ dK (z := j / k) rfl)
    (v := .nat (g ⟨j / k, hp⟩)) (by simp [encPerm, List.getElem?_map, hp])
  have dQ := Det.get' dG (Det.arith' (op := .mod) dJ dK (z := j % k) rfl)
    (v := .nat (g ⟨j % k, hq⟩)) (by simp [encPerm, List.getElem?_map, hq])
  have hval : (g ⟨j / k, hp⟩ : ℕ) * k + g ⟨j % k, hq⟩ = sqPerm g j := by
    rw [sqPerm_val]
    rfl
  have d := Det.arith' (op := .add) (Det.arith' (op := .mul) dP dK (z := g ⟨j / k, hp⟩ * k) rfl) dQ
    (z := sqPerm g j) (by rw [← hval]; rfl)
  refine FunDet.intro hf (d.mono ?_)
  have w1 := wt_list2_le (.list [.nat k, encPerm g]) (.nat j)
  have w2 := wt_list2_le (.nat k) (encPerm g)
  have w3 := wt_nat_le j
  have w4 := wt_nat_le k
  have w5 := wt_nat_le (g ⟨j / k, hp⟩)
  have w6 := wt_nat_le (g ⟨j % k, hq⟩)
  have w7 := (sqPerm g j).2
  have w8 := j.2
  have w9 := (g ⟨j / k, hp⟩).2
  have w10 := (g ⟨j % k, hq⟩).2
  have w11 : (g ⟨j / k, hp⟩ : ℕ) * k ≤ k * k := by nlinarith
  have w12 : (j : ℕ) / k ≤ k := hp.le
  have w13 : k ≤ k * k := Nat.le_mul_self k
  omega

/-- On `[[k, x], p]`: `x (k p) / k`. -/
def unsqEntF : Expr :=
  let K := Expr.get (arg 0) (.nat 0)
  .arith .div (.get (.get (arg 0) (.nat 1)) (.arith .mul K (arg 1))) K

set_option maxHeartbeats 1000000 in
theorem unsqEnt_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some unsqEntF) (t : Perm (Fin k))
    (p : Fin k) :
    FunDet P f (.list [.list [.nat k, encPerm (sqPerm t)], .nat p]) (.nat (t p))
      (1000 * ((encPerm (sqPerm t)).wt + k * k + 10)) := by
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd p.2 (by simp [h])
    · exact h
  have hkp : k * p < k * k := Nat.mul_lt_mul_of_pos_left p.2 hk0
  have dA := Det.arg' (P := P) (vs := [.list [.nat k, encPerm (sqPerm t)], .nat p]) (rest := []) (j := 0) rfl
  have dP := Det.arg' (P := P) (vs := [.list [.nat k, encPerm (sqPerm t)], .nat p]) (rest := []) (j := 1) rfl
  have dK := Det.get' dA (Det.nat 0) (v := .nat k) rfl
  have dX := Det.get' dA (Det.nat 1) (v := encPerm (sqPerm t)) rfl
  have dE := Det.get' dX (Det.arith' (op := .mul) dK dP (z := k * p) rfl)
    (v := .nat (sqPerm t ⟨k * p, hkp⟩)) (by simp [encPerm, List.getElem?_map, hkp])
  have hv : (sqPerm t ⟨k * p, hkp⟩ : ℕ) / k = t p := by
    have := unsq_val hk0 t p
    rw [unsq_sqPerm] at this
    exact this.symm
  have d := Det.arith' (op := .div) dE dK (z := t p) hv
  refine FunDet.intro hf (d.mono ?_)
  have w1 := wt_list2_le (.list [.nat k, encPerm (sqPerm t)]) (.nat p)
  have w2 := wt_list2_le (.nat k) (encPerm (sqPerm t))
  have w3 := wt_nat_le p
  have w4 := wt_nat_le k
  have w5 := wt_nat_le (sqPerm t ⟨k * p, hkp⟩)
  have w7 := (sqPerm t ⟨k * p, hkp⟩).2
  have w8 := p.2
  have w9 := (t p).2
  have w13 : k ≤ k * k := Nat.le_mul_self k
  omega

/-- On `[[k, ids], x]`: `map f` of `[k, x]` over `ids`. -/
def tabWrapF (bm : ℕ) : Expr :=
  .call bm (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))

/-- The constant of the conversions. -/
def sqConvK : ℕ := 10 ^ 8

set_option maxHeartbeats 1000000 in
/-- `g × g` from `g`. -/
theorem sqPerm_spec {P : Program} {f bm fe : ℕ} (hf : P.funs[f]? = some (tabWrapF bm))
    (hbm : P.HasAt bm (mapFuns bm fe)) (hfe : P.funs[fe]? = some sqEntF) (g : Perm (Fin k)) :
    FunDet P f (.list [.list [.nat k, encFun fun j : Fin (k * k) => (j : ℕ)], encPerm g])
      (encPerm (sqPerm g)) (sqConvK * (k + 1) ^ 6) := by
  have hT := tabulate_spec hbm (c := .list [.nat k, encPerm g]) (B := 1000 * ((encPerm g).wt + k * k + 10))
    (F := fun j : Fin (k * k) => .nat (sqPerm g j)) (fun j => sqEnt_spec hfe g j)
  set c0 := Val.list [.nat k, encFun fun j : Fin (k * k) => (j : ℕ)]
  set a := Val.list [c0, encPerm g]
  have dA := Det.arg' (P := P) (vs := [c0, encPerm g]) (rest := []) (j := 0) rfl
  have dG := Det.arg' (P := P) (vs := [c0, encPerm g]) (rest := []) (j := 1) rfl
  have dK := Det.get' dA (Det.nat 0) (v := .nat k) rfl
  have dI := Det.get' dA (Det.nat 1) (v := encFun fun j : Fin (k * k) => (j : ℕ)) rfl
  have d := Det.call (Det.mk2 (Det.mk2 dK dG) dI) hT
  refine FunDet.intro hf (d.mono ?_)
  have e1 : (Val.list ((List.finRange (k * k)).map fun j => Val.nat (sqPerm g j))) =
    encPerm (sqPerm g) := rfl
  rw [e1]
  have wg := wt_encPerm_le g
  have wsg := wt_encPerm_le (sqPerm g)
  have wid := wt_ids_le (k * k)
  have hkk : (k * k + 1) ≤ (k + 1) ^ 2 := by nlinarith
  have hkk2 : (k * k + 1) ^ 2 ≤ (k + 1) ^ 4 := by
    calc (k * k + 1) ^ 2 ≤ ((k + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hkk 2
      _ = (k + 1) ^ 4 := by ring
  have w1 := wt_list2_le c0 (encPerm g)
  have w2 := wt_list2_le (.nat k) (encFun fun j : Fin (k * k) => (j : ℕ))
  have w2' := wt_list2_le (.nat k) (encPerm g)
  have w2'' := wt_list2_le (Val.list [.nat k, encPerm g]) (encFun fun j : Fin (k * k) => (j : ℕ))
  have w4 := wt_nat_le k
  have wa : a.wt = (Val.list [c0, encPerm g]).wt := rfl
  have wc0 : c0.wt = (Val.list [.nat k, encFun fun j : Fin (k * k) => (j : ℕ)]).wt := rfl
  have hk1 : 1 ≤ k + 1 := by omega
  have p2 : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p4 : (k + 1) ^ 2 ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right hk1 (by norm_num)
  have p6 : (k + 1) ^ 4 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right hk1 (by norm_num)
  have m1 : k * k * (1000 * ((encPerm g).wt + k * k + 10)) ≤ (k + 1) ^ 2 * (1000 * (20 * (k + 1) ^ 4)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have m2 : mapK * (k * k + 1) * ((Val.list [Val.list [.nat k, encPerm g],
      encFun fun j : Fin (k * k) => (j : ℕ)]).wt + (encPerm (sqPerm g)).wt + 1) ≤
      1000 * (k + 1) ^ 2 * (100 * (k + 1) ^ 4) := by
    simp only [mapK]
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ hkk) ?_
    omega
  have e2 : (k + 1) ^ 2 * (1000 * (20 * (k + 1) ^ 4)) = 20000 * (k + 1) ^ 6 := by ring
  have e3 : 1000 * (k + 1) ^ 2 * (100 * (k + 1) ^ 4) = 100000 * (k + 1) ^ 6 := by ring
  simp only [sqConvK]
  omega

set_option maxHeartbeats 1000000 in
/-- `t` from `t × t`. -/
theorem unsqPerm_spec {P : Program} {f bm fe : ℕ} (hf : P.funs[f]? = some (tabWrapF bm))
    (hbm : P.HasAt bm (mapFuns bm fe)) (hfe : P.funs[fe]? = some unsqEntF) (t : Perm (Fin k)) :
    FunDet P f (.list [.list [.nat k, encFun fun j : Fin k => (j : ℕ)], encPerm (sqPerm t)])
      (encPerm t) (sqConvK * (k + 1) ^ 6) := by
  have hT := tabulate_spec hbm (c := .list [.nat k, encPerm (sqPerm t)])
    (B := 1000 * ((encPerm (sqPerm t)).wt + k * k + 10))
    (F := fun p : Fin k => .nat (t p)) (fun p => unsqEnt_spec hfe t p)
  set c0 := Val.list [.nat k, encFun fun j : Fin k => (j : ℕ)]
  set a := Val.list [c0, encPerm (sqPerm t)]
  have dA := Det.arg' (P := P) (vs := [c0, encPerm (sqPerm t)]) (rest := []) (j := 0) rfl
  have dG := Det.arg' (P := P) (vs := [c0, encPerm (sqPerm t)]) (rest := []) (j := 1) rfl
  have dK := Det.get' dA (Det.nat 0) (v := .nat k) rfl
  have dI := Det.get' dA (Det.nat 1) (v := encFun fun j : Fin k => (j : ℕ)) rfl
  have d := Det.call (Det.mk2 (Det.mk2 dK dG) dI) hT
  refine FunDet.intro hf (d.mono ?_)
  have e1 : (Val.list ((List.finRange k).map fun p => Val.nat (t p))) = encPerm t := rfl
  rw [e1]
  have wg := wt_encPerm_le t
  have wsg := wt_encPerm_le (sqPerm t)
  have wid := wt_ids_le k
  have hkk : (k * k + 1) ≤ (k + 1) ^ 2 := by nlinarith
  have hkk2 : (k * k + 1) ^ 2 ≤ (k + 1) ^ 4 := by
    calc (k * k + 1) ^ 2 ≤ ((k + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hkk 2
      _ = (k + 1) ^ 4 := by ring
  have w1 := wt_list2_le c0 (encPerm (sqPerm t))
  have w2 := wt_list2_le (.nat k) (encFun fun j : Fin k => (j : ℕ))
  have w2'' := wt_list2_le (Val.list [.nat k, encPerm (sqPerm t)]) (encFun fun j : Fin k => (j : ℕ))
  have w2' := wt_list2_le (.nat k) (encPerm (sqPerm t))
  have w4 := wt_nat_le k
  have wa : a.wt = (Val.list [c0, encPerm (sqPerm t)]).wt := rfl
  have wc0 : c0.wt = (Val.list [.nat k, encFun fun j : Fin k => (j : ℕ)]).wt := rfl
  have hk1 : 1 ≤ k + 1 := by omega
  have p2 : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p4 : (k + 1) ^ 2 ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right hk1 (by norm_num)
  have p6 : (k + 1) ^ 4 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right hk1 (by norm_num)
  have m1 : k * (1000 * ((encPerm (sqPerm t)).wt + k * k + 10)) ≤
      (k + 1) ^ 2 * (1000 * (20 * (k + 1) ^ 4)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have m2 : mapK * (k + 1) * ((Val.list [Val.list [.nat k, encPerm (sqPerm t)],
      encFun fun j : Fin k => (j : ℕ)]).wt + (encPerm t).wt + 1) ≤
      1000 * (k + 1) ^ 2 * (100 * (k + 1) ^ 4) := by
    simp only [mapK]
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ p2) ?_
    omega
  have e2 : (k + 1) ^ 2 * (1000 * (20 * (k + 1) ^ 4)) = 20000 * (k + 1) ^ 6 := by ring
  have e3 : 1000 * (k + 1) ^ 2 * (100 * (k + 1) ^ 4) = 100000 * (k + 1) ^ 6 := by ring
  simp only [sqConvK]
  omega

/-- **A map of a permutation conversion over a list.** -/
theorem mapConv_spec {P : Program} {b f : ℕ} (hb : P.HasAt b (mapFuns b f)) {c : Val} {n n' : ℕ}
    (conv : Perm (Fin n) → Perm (Fin n')) {B : ℕ}
    (gs : List (Perm (Fin n)))
    (hf : ∀ g ∈ gs, FunDet P f (.list [c, encPerm g]) (encPerm (conv g)) B) :
    FunDet P b (.list [c, .list (gs.map encPerm)]) (.list ((gs.map conv).map encPerm))
      (gs.length * B + mapK * (gs.length + 1) * ((Val.list [c, .list (gs.map encPerm)]).wt +
        (Val.list ((gs.map conv).map encPerm)).wt + 1)) := by
  refine (map_spec hb (R := fun x w => ∀ g, x = encPerm g → w = encPerm (conv g))
    (B := fun _ => B) (fun x hx => ?_)).mono fun w cost hw => ?_
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
    refine FunAll.mono (hf g hg) fun w c hw => ⟨fun g' hg' => ?_, hw.2⟩
    rw [encPerm_injective hg'.symm, hw.1]
  · obtain ⟨ws, hws, hR, hc⟩ := hw
    have e := forall₂_map_eq (l := gs) (f := encPerm) (g := fun g => encPerm (conv g))
      (fun a _ w h => h a rfl) hR
    rw [e] at hws
    subst hws
    have hs : ((gs.map encPerm).map fun _ => B).sum = gs.length * B := by
      rw [List.map_map]
      clear hR e hc hf
      induction gs with
      | nil => simp
      | cons g gs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Function.comp_apply]; ring
    rw [hs] at hc
    refine ⟨by rw [List.map_map]; rfl, ?_⟩
    have e2 : gs.map (fun g => encPerm (conv g)) = (gs.map conv).map encPerm := by
      rw [List.map_map]; rfl
    rw [e2] at hc
    simpa using hc

end GI.Impl
