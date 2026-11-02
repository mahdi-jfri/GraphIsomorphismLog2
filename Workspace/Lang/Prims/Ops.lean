/-
**Derived operations on groups**, written in `GI.Lang` from the primitives and the library.

* `mapList_spec`: `map f` over the values `xs.map enc`, when `f` sends `enc a` to `enc' a`.
* `mkGroupFuns`: from `[n, [h₁, …, h_m]]` (the output format, `GensVal`) to `encGroup hs` (the
  input format, `GroupVal`), by putting the identity in front. Cost at most
  `mkGroupK * ((m + 2) * (n + 1)) ^ 3`.
  On a primitive's output (at most `n²` generators, `mkGroup_gensVal`) the cost is at most
  `8 * mkGroupK * (n + 1) ^ 9`.
* `member_det`, `order_det`: membership and order, with determined results. The order is charged
  by its bit length, at most `n² + 1`, not by its value.
* `index_spec`: the index of a subgroup, from two orders, at cost polynomial in the input.
* `leFuns`: the test `H ≤ G`, by membership of the generators of `H`.
* `pstabFuns`: the pointwise stabilizer of a list of points, returned as a group value, so it can
  be passed to the next primitive.

Every cost bound is explicit and depends on the input alone: the bounds of the primitive calls
(`p.bound v`) plus a polynomial in the weight of the argument. This is possible because the tasks
bound the size of their outputs (`GI.Cited.GensOf`: at most `n²` generators), so the weight of a
primitive's result is at most a polynomial in `n`.
-/
import Workspace.Lang.Prims.PermGroups

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited
open Equiv

variable {n : ℕ}

/-! ### Map with known images -/

/-- **Map with known images.** If `f` sends `[c, enc a]` to `enc' a` at cost at most `B` for every
`a` in `xs`, then `map f` sends `[c, xs.map enc]` to `xs.map enc'`. -/
theorem mapList_spec {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {α : Type}
    (xs : List α) (enc enc' : α → Val) {c : Val} {B : ℕ}
    (hinj : ∀ a ∈ xs, ∀ a' ∈ xs, enc a = enc a' → enc' a = enc' a')
    (hf : ∀ a ∈ xs, FunDet P f (.list [c, enc a]) (enc' a) B) :
    FunDet P b (.list [c, .list (xs.map enc)]) (.list (xs.map enc'))
      (xs.length * B + mapK * (xs.length + 1) *
        ((Val.list [c, .list (xs.map enc)]).wt + (Val.list (xs.map enc')).wt + 1)) := by
  have hM := map_spec h (c := c) (xs := xs.map enc)
    (R := fun x w => ∀ a ∈ xs, x = enc a → w = enc' a) (B := fun _ => B) (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      refine FunAll.mono (hf a ha) fun w c hw => ⟨fun a' ha' he => ?_, hw.2⟩
      rw [hw.1]; exact hinj a ha a' ha' he)
  refine FunAll.mono hM fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' : ws = xs.map enc' := forall₂_map_eq (h := hws) fun a ha w hw => hw a ha rfl
  subst hws'
  refine ⟨rfl, ?_⟩
  rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
  exact hc

/-- `(m + 1) * B ≤ S * B` for the usual measure `S = (m + 2) * (n + 1)`. -/
theorem le_S (m n : ℕ) : m + 2 ≤ (m + 2) * (n + 1) ∧ n + 1 ≤ (m + 2) * (n + 1) :=
  ⟨Nat.le_mul_of_pos_right _ (by omega), Nat.le_mul_of_pos_left _ (by omega)⟩

/-! ### From generators to a group value -/

/-- On `[n, L]`: `[n, append [range n] L]`. -/
def mkGroupF (r ap : ℕ) : Expr :=
  mk2 (arg 0) (.call ap (mk2 (mk1 (.call r (arg 0))) (arg 1)))

/-- `mkGroup`, at base `b` (seven functions). -/
def mkGroupFuns (b : ℕ) : List Expr := [mkGroupF (b + 1) (b + 4)] ++ rangeFuns (b + 1) ++
  appendFuns (b + 4)

/-- The constant of `mkGroup`. -/
def mkGroupK : ℕ := 100000

/-- `range n` gives the identity of `Fin n`. -/
theorem range_det {P : Program} {b : ℕ} (h : P.HasAt b (rangeFuns b)) (n : ℕ) :
    FunDet P b (.nat n) (encPerm (1 : Perm (Fin n))) (8000 * (n + 1) ^ 3) := by
  refine FunAll.mono (range_spec h n) fun w c hw => ⟨?_, ?_⟩
  · rw [hw.1, range_eq_encPerm_one]
  · have hc := hw.2
    rw [hw.1, range_eq_encPerm_one] at hc
    have := wt_encPerm_le (1 : Perm (Fin n))
    have := wt_nat_le n
    have h1 : loopModK * (n + 1) * ((Val.nat n).wt + n + (encPerm (1 : Perm (Fin n))).wt
        + 1) ≤ loopModK * (n + 1) * (8 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
    have e : loopModK * (n + 1) * (8 * (n + 1) ^ 2) = 8000 * (n + 1) ^ 3 := by
      simp only [loopModK]; ring
    omega

/-- **From generators to a group value.** -/
theorem mkGroup_spec {P : Program} {b : ℕ} (h : P.HasAt b (mkGroupFuns b))
    (hs : List (Perm (Fin n))) :
    FunDet P b (.list [.nat n, .list (hs.map encPerm)]) (encGroup hs)
      (mkGroupK * ((hs.length + 2) * (n + 1)) ^ 3) := by
  simp only [mkGroupFuns] at h
  have hentry : P.funs[b]? = some (mkGroupF (b + 1) (b + 4)) := h.left.left.single
  have hrange : P.HasAt (b + 1) (rangeFuns (b + 1)) := by simpa using h.left.right
  have happ : P.HasAt (b + 4) (appendFuns (b + 4)) := by
    simpa [rangeFuns, loopFuns, Nat.add_assoc] using h.right
  set L := Val.list (hs.map encPerm) with hL
  set A := Val.list [.nat n, L] with hA
  have d0 := Det.arg' (P := P) (vs := [.nat n, L]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [.nat n, L]) (rest := []) (j := 1) rfl
  have dr := Det.call d0 (range_det hrange n)
  have hap := append_spec happ [encPerm (1 : Perm (Fin n))] (hs.map encPerm)
  have hapd : FunDet P (b + 4) (.list [.list [encPerm (1 : Perm (Fin n))], L])
      (.list ((1 :: hs).map encPerm)) (loopModK * (hs.length + 1) *
        ((Val.list [.list [encPerm (1 : Perm (Fin n))], L]).wt + hs.length +
          (Val.list ((1 :: hs).map encPerm)).wt + 1)) :=
    FunAll.mono hap fun w c hw => by
      obtain ⟨rfl, hc⟩ := hw
      exact ⟨by simp, by simpa using hc⟩
  have da := Det.call (Det.mk2 (Det.mk1 dr) d1) hapd
  refine FunDet.intro hentry ((Det.mk2 d0 da).mono ?_)
  -- the cost
  have w1 := wt_encPerm_le (1 : Perm (Fin n))
  have w2 := wt_list_encPerms_le hs
  have w3 := wt_list_encPerms_le (1 :: hs)
  have w4 := wt_list2_le (.nat n) L
  have w5 := wt_list1_le (encPerm (1 : Perm (Fin n)))
  have w6 := wt_list2_le (.list [encPerm (1 : Perm (Fin n))]) L
  have w7 := wt_list2_le (.nat n) (.list ((1 :: hs).map encPerm))
  have w8 := wt_nat_le n
  have eG : (encGroup hs).wt = (Val.list [.nat n, .list ((1 :: hs).map encPerm)]).wt := rfl
  have eL : L.wt = (Val.list (hs.map encPerm)).wt := rfl
  simp only [List.length_cons] at w3
  generalize hS : (hs.length + 2) * (n + 1) = S
  obtain ⟨hmS, hnS⟩ := le_S hs.length n
  rw [hS] at hmS hnS
  have hS1 : 1 ≤ S := by omega
  have h2 : ((hs.length + 1) * (n + 1)) ^ 2 ≤ S ^ 2 :=
    Nat.pow_le_pow_left (hS ▸ Nat.mul_le_mul_right _ (by omega)) 2
  have h3 : ((hs.length + 1 + 1) * (n + 1)) ^ 2 = S ^ 2 := by rw [← hS]
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hnS 2
  have hN3 : (n + 1) ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left hnS 3
  have hS12 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by omega)
  have h4 : loopModK * (hs.length + 1) * ((Val.list [.list [encPerm (1 : Perm (Fin n))], L]).wt +
      hs.length + (Val.list ((1 :: hs).map encPerm)).wt + 1) ≤ loopModK * S * (70 * S ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e4 : loopModK * S * (70 * S ^ 2) = 70000 * S ^ 3 := by simp only [loopModK]; ring
  simp only [mkGroupK]
  omega

/-- At most `n²` generators: the measure `(m + 2) (n + 1)` is at most `2 (n + 1)³`. -/
theorem measure_le_of_sq {m : ℕ} (hm : m ≤ n ^ 2) : (m + 2) * (n + 1) ≤ 2 * (n + 1) ^ 3 := by
  have : m + 2 ≤ 2 * (n + 1) ^ 2 := by
    have e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  calc (m + 2) * (n + 1) ≤ 2 * (n + 1) ^ 2 * (n + 1) := Nat.mul_le_mul_right _ this
    _ = 2 * (n + 1) ^ 3 := by ring

/-- A group value with at most `n²` generators weighs at most `320 (n + 1)⁶`. -/
theorem wt_encGroup_le_sq {hs : List (Perm (Fin n))} (hl : hs.length ≤ n ^ 2) :
    (encGroup hs).wt ≤ 320 * (n + 1) ^ 6 := by
  have h1 := wt_encGroup_le hs
  have h2 : ((hs.length + 2) * (n + 1)) ^ 2 ≤ 4 * (n + 1) ^ 6 :=
    calc ((hs.length + 2) * (n + 1)) ^ 2 ≤ (2 * (n + 1) ^ 3) ^ 2 :=
          Nat.pow_le_pow_left (measure_le_of_sq hl) 2
      _ = 4 * (n + 1) ^ 6 := by ring
  omega

/-- From a generator value to a group value: `mkGroup` on `[n, L]` with `GensVal n L G` gives a
group value of `G`, of weight at most `320 (n + 1)⁶`, at cost at most `8 mkGroupK (n + 1)⁹`. The
bounds hold because a generator value has at most `n²` generators. -/
theorem mkGroup_gensVal {P : Program} {b : ℕ} (h : P.HasAt b (mkGroupFuns b)) {L : Val}
    {G : Subgroup (Perm (Fin n))} (hL : GensVal n L G) :
    ∃ hs : List (Perm (Fin n)), L = .list (hs.map encPerm) ∧ hs.length ≤ n ^ 2 ∧
      FunDet P b (.list [.nat n, L]) (encGroup hs) (8 * mkGroupK * (n + 1) ^ 9) ∧
      GroupVal n (encGroup hs) G ∧ (encGroup hs).wt ≤ 320 * (n + 1) ^ 6 := by
  obtain ⟨hs, rfl, hl, rfl⟩ := hL
  refine ⟨hs, rfl, hl, (mkGroup_spec h hs).mono ?_, ⟨hs, rfl, rfl⟩, wt_encGroup_le_sq hl⟩
  calc mkGroupK * ((hs.length + 2) * (n + 1)) ^ 3 ≤ mkGroupK * (2 * (n + 1) ^ 3) ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (measure_le_of_sq hl) 3)
    _ = 8 * mkGroupK * (n + 1) ^ 9 := by ring

/-! ### Weights of group values -/

theorem wt_gens_le_encGroup (hs : List (Perm (Fin n))) :
    (Val.list (hs.map encPerm)).wt ≤ (encGroup hs).wt := by
  have h1 : (Val.list (hs.map encPerm)).wt ≤ (Val.list ((1 :: hs).map encPerm)).wt := by
    rw [wt_list_eq, wt_list_eq]
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_map]
    have := GI.Machine.len_mono (show hs.length ≤ hs.length + 1 by omega)
    have := GI.Machine.len_mono (show ((hs.map encPerm).map Val.size).sum ≤
      (encPerm (1 : Perm (Fin n))).size + ((hs.map encPerm).map Val.size).sum by omega)
    omega
  have h2 : (Val.list ((1 :: hs).map encPerm)).wt < (encGroup hs).wt :=
    wt_le_wt_list (vs := [.nat n, .list ((1 :: hs).map encPerm)]) (by simp)
  omega

/-- The measure `(m + 2) * (n + 1)` is at most the number of cells of the group value. -/
theorem S_le_size_encGroup (hs : List (Perm (Fin n))) :
    (hs.length + 2) * (n + 1) ≤ (encGroup hs).size := by
  rw [size_encGroup]; nlinarith

theorem S_le_wt_encGroup (hs : List (Perm (Fin n))) :
    (hs.length + 2) * (n + 1) ≤ (encGroup hs).wt :=
  (S_le_size_encGroup hs).trans (encGroup hs).size_le_wt

/-- The bound of a primitive depends only on the number of cells of its argument. -/
theorem Prim.bound_congr (p : Prim) {v v' : Val} (h : v.size = v'.size) :
    p.bound v = p.bound v' := by
  simp only [Prim.bound, h]

theorem size_list2_encPerm (a : Val) (σ τ : Perm (Fin n)) :
    (Val.list [a, encPerm σ]).size = (Val.list [a, encPerm τ]).size := by
  simp only [size_list, length_cellsList, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, size_encPerm]

/-! ### Membership and order -/

open Classical in
/-- **Membership**, with its result determined: `1` if `x ∈ G`, else `0`. -/
theorem member_det (h : Membership) {P : Program} {env : List Val} {j : ℕ} {a : Expr}
    {ca : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))} {x : Perm (Fin n)}
    (hj : P.prims[j]? = some (membershipPrim h)) (ha : Det P env a (.list [gv, encPerm x]) ca)
    (hG : GroupVal n gv G) :
    Det P env (.prim j a) (boolVal (decide (x ∈ G)))
      (ca + (membershipPrim h).bound (.list [gv, encPerm x]) + 4) := by
  refine (Det.prim_spec hj ha ((membershipPrim_spec h hG x).mono fun w hw => ?_)).mono
    (by have := wt_boolVal_le (decide (x ∈ G)); omega)
  rcases hw with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> simp [hx]

/-- **Order**, with its result determined. The cost counts the order by its bit length, at most
`n² + 1` (`wt_card_le`), not by its value, which can be as large as `n!`. -/
theorem order_det (h : GroupOrder) {P : Program} {env : List Val} {j : ℕ} {a : Expr}
    {ca : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hj : P.prims[j]? = some (groupOrderPrim h)) (ha : Det P env a gv ca) (hG : GroupVal n gv G) :
    Det P env (.prim j a) (.nat (Nat.card G)) (ca + (groupOrderPrim h).bound gv + n ^ 2 + 4) :=
  groupOrder_call h hj ha hG

/-- The index of `H` in `G`: on `[G, H]`, `|G| / |H|`. -/
def indexF (jo : ℕ) : Expr := .arith .div (.prim jo (arg 0)) (.prim jo (arg 1))

/-- **The index of a subgroup**, from two order calls. The cost is polynomial in the input: the
two orders and the index are read as values of at most `n² + 1` bits (`wt_card_le`), so the
division costs `O(n²)`, not `|G|`. -/
theorem index_spec (h : GroupOrder) {P : Program} {f jo : ℕ} (hf : P.funs[f]? = some (indexF jo))
    (hj : P.prims[jo]? = some (groupOrderPrim h)) {gv hv : Val} {G H : Subgroup (Perm (Fin n))}
    (hG : GroupVal n gv G) (hH : GroupVal n hv H) (hle : H ≤ G) :
    FunDet P f (.list [gv, hv]) (.nat (H.relIndex G))
      ((groupOrderPrim h).bound gv + (groupOrderPrim h).bound hv +
        3 * n ^ 2 + 5 * (Val.list [gv, hv]).wt + 30) := by
  have d1 := order_det h hj (Det.arg' (P := P) (vs := [gv, hv]) (rest := []) (j := 0) rfl) hG
  have d2 := order_det h hj (Det.arg' (P := P) (vs := [gv, hv]) (rest := []) (j := 1) rfl) hH
  have hidx : Nat.card G / Nat.card H = H.relIndex G := by
    have e := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (Perm (Fin n))) H G bot_le hle
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at e
    have hpos : 0 < Nat.card H := Nat.card_pos
    rw [← e, Nat.mul_div_cancel_left _ hpos]
  have hHG : Nat.card H ≤ Nat.card G := Subgroup.card_le_of_le hle
  have hiG : H.relIndex G ≤ Nat.card G := by
    rw [← hidx]; exact Nat.div_le_self _ _
  have e : BinOp.div.eval (Nat.card G) (Nat.card H) = H.relIndex G := by
    simp only [BinOp.eval, hidx]
  have d3 := Det.arith (op := .div) d1 d2
  rw [e] at d3
  -- the index is at most `|G|`, so it has at most `n² + 1` bits
  have hw : (Val.nat (H.relIndex G)).wt ≤ n ^ 2 + 3 := by
    rw [wt_nat]
    have := GI.Machine.len_le_iff.mpr (lt_of_le_of_lt hiG (GI.CitedChecks.card_lt_two_pow G))
    omega
  exact FunDet.intro hf (d3.mono (by omega))

/-! ### The test `H ≤ G` -/

/-- On `[gv, hv]`: whether every generator of `hv` lies in the group of `gv`. -/
def leEntry (al : ℕ) : Expr := .call al (mk2 (arg 0) (.get (arg 1) (.nat 1)))

/-- The subgroup test, at base `b` (five functions), with membership at primitive `jm`. -/
def leFuns (b jm : ℕ) : List Expr := [leEntry (b + 1)] ++ allFuns (b + 1) (b + 4) ++ [primF jm]

open Classical in
/-- The test "`v` encodes an element of `G`". -/
noncomputable def inGroupTest (G : Subgroup (Perm (Fin n))) (v : Val) : Bool :=
  decide (∀ σ : Perm (Fin n), v = encPerm σ → σ ∈ G)

open Classical in
/-- **The test `H ≤ G`.** On `[gv, hv]` with group values of `G` and `H`, the result is `1` if
`H ≤ G` and `0` otherwise. With `T` the weight of the argument, the cost is at most `T` times
the bound of one membership call plus `20000 * T ^ 3`. -/
theorem le_spec (h : Membership) {P : Program} {b jm : ℕ} (hb : P.HasAt b (leFuns b jm))
    (hj : P.prims[jm]? = some (membershipPrim h)) {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hG : GroupVal n gv G) (hs : List (Perm (Fin n))) :
    FunDet P b (.list [gv, encGroup hs]) (boolVal (decide (gens hs ≤ G)))
      ((Val.list [gv, encGroup hs]).wt *
          (membershipPrim h).bound (.list [gv, encPerm (1 : Perm (Fin n))]) +
        20000 * (Val.list [gv, encGroup hs]).wt ^ 3) := by
  simp only [leFuns] at hb
  have hentry : P.funs[b]? = some (leEntry (b + 1)) := hb.left.left.single
  have hall : P.HasAt (b + 1) (allFuns (b + 1) (b + 4)) := by simpa using hb.left.right
  have hp : P.funs[b + 4]? = some (primF jm) := by
    simpa [allFuns, loopFuns, Nat.add_assoc] using hb.right.single
  set T := (Val.list [gv, encGroup hs]).wt with hT
  set B1 := (membershipPrim h).bound (.list [gv, encPerm (1 : Perm (Fin n))]) with hB1
  have hgvT : gv.wt < T := wt_le_wt_list (by simp)
  have hET : (encGroup hs).wt < T := wt_le_wt_list (by simp)
  have hS := S_le_wt_encGroup hs
  obtain ⟨hmS, hnS⟩ := le_S hs.length n
  -- each membership call
  have hmem : ∀ x ∈ (1 :: hs).map encPerm, FunDet P (b + 4) (.list [gv, x])
      (boolVal (inGroupTest G x)) (B1 + 3 * T + 8 * (n + 1) ^ 2 + 20) := by
    intro x hx
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx
    have hq : inGroupTest G (encPerm σ) = decide (σ ∈ G) := by
      simp only [inGroupTest, decide_eq_decide]
      exact ⟨fun h => h σ rfl, fun h τ he => encPerm_injective he ▸ h⟩
    refine FunAll.mono (FunAll.prim_spec hp hj ((membershipPrim_spec h hG σ).mono
      (Out' := (· = boolVal (inGroupTest G (encPerm σ)))) fun w hw => ?_)) fun w c hw => ?_
    · rw [hq]; rcases hw with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> simp [hx]
    · refine ⟨hw.1, ?_⟩
      have e := (membershipPrim h).bound_congr (size_list2_encPerm gv σ 1)
      have h1 := wt_list2_le gv (encPerm σ)
      have h2 := wt_encPerm_le σ
      have h3 := wt_boolVal_le (inGroupTest G (encPerm σ))
      rw [hw.1] at hw
      have := hw.2
      omega
  have hA := all_spec hall hmem
  have da := Det.mk2 (Det.arg' (P := P) (vs := [gv, encGroup hs]) (rest := []) (j := 0) rfl)
    (Det.get' (Det.arg' (P := P) (vs := [gv, encGroup hs]) (rest := []) (j := 1) rfl) (Det.nat 1)
      (show [Val.nat n, Val.list ((1 :: hs).map encPerm)][1]? = some _ from rfl))
  have hall_eq : ((1 :: hs).map encPerm).all (inGroupTest G) = decide (gens hs ≤ G) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
    simp only [List.mem_map, List.mem_cons, forall_exists_index, and_imp]
    constructor
    · intro hall
      unfold gens
      rw [Subgroup.closure_le]
      intro g hg
      have := hall _ g (Or.inr hg) rfl
      simp only [inGroupTest, decide_eq_true_iff] at this
      exact this g rfl
    · intro hle x σ hσ hx
      subst hx
      simp only [inGroupTest, decide_eq_true_iff]
      intro τ he
      rw [← encPerm_injective he]
      rcases hσ with rfl | hσ
      · exact G.one_mem
      · exact hle (Subgroup.subset_closure hσ)
  refine FunDet.intro hentry ((Det.call da (FunAll.mono hA fun w c hw => ⟨?_, hw.2⟩)).mono ?_)
  · rw [hw.1, hall_eq]
  -- the cost
  · have w1 := wt_list2_le gv (.list ((1 :: hs).map encPerm))
    have w2 := wt_list_encPerms_le (1 :: hs)
    have w3 := wt_boolVal_le (decide (gens hs ≤ G))
    have eE : (encGroup hs).wt = (Val.list [.nat n, .list ((1 :: hs).map encPerm)]).wt := rfl
    have w4 : (Val.list ((1 :: hs).map encPerm)).wt < (encGroup hs).wt :=
      wt_le_wt_list (vs := [.nat n, .list ((1 :: hs).map encPerm)]) (by simp)
    simp only [List.length_cons, List.length_map, List.map_const', List.sum_replicate,
      smul_eq_mul] at w2 ⊢
    have hT2 : (hs.length + 2) * (n + 1) ≤ T := by omega
    have hT1 : 1 ≤ T := by omega
    have hn2 : 8 * (n + 1) ^ 2 ≤ 8 * T ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (le_trans hnS hT2) 2)
    have hTT : T ≤ T ^ 2 := Nat.le_self_pow (by omega) _
    have hT23 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right hT1 (by omega)
    have h5 : (hs.length + 1) * (B1 + 3 * T + 8 * (n + 1) ^ 2 + 20) ≤
        T * B1 + T * (3 * T + 8 * T ^ 2 + 20) := by
      have : hs.length + 1 ≤ T := by omega
      nlinarith
    have h6 : T * (3 * T + 8 * T ^ 2 + 20) ≤ 31 * T ^ 3 := by nlinarith
    have h7 : loopModK * (hs.length + 1 + 1) * ((Val.list [gv, .list ((1 :: hs).map encPerm)]).wt +
        (hs.length + 1) + 4) ≤ loopModK * T * (16 * T) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e7 : loopModK * T * (16 * T) = 16000 * T ^ 2 := by simp only [loopModK]; ring
    omega

/-! ### The pointwise stabilizer of a list of points, as a group value -/

/-- On `[gv, pts]`: the pointwise stabilizer, with the identity added to its generators. -/
def pstabF (jp mg : ℕ) : Expr :=
  .letE (.prim jp (.var 0)) (.call mg (mk2 (.get (.get (.var 0) (.nat 0)) (.nat 0)) (.var 1)))

/-- The pointwise stabilizer as a group value, at base `b` (eight functions), with the
pointwise-stabilizer primitive at index `jp`. -/
def pstabFuns (b jp : ℕ) : List Expr := [pstabF jp (b + 1)] ++ mkGroupFuns (b + 1)

/-- The constant of `pstabFuns`. -/
def pstabK : ℕ := 1000000

/-- **The pointwise stabilizer of a list of points, as a group value.** With `T` the weight of
the argument, the result weighs at most `320 (n + 1)⁶` and the cost is at most the bound of the
primitive call plus `pstabK * T ^ 9`. Both bounds come from the at most `n²` generators that
the primitive returns (`mkGroup_gensVal`); `n + 1 ≤ T`. -/
theorem pstab_spec (h : PointwiseStab) {P : Program} {b jp : ℕ} (hb : P.HasAt b (pstabFuns b jp))
    (hj : P.prims[jp]? = some (pointwiseStabPrim h)) {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hG : GroupVal n gv G) (S : List (Fin n)) :
    FunAll P b (.list [gv, encPts S]) (fun w c => GroupVal n w (pointwiseStab G S) ∧
      w.wt ≤ 320 * (n + 1) ^ 6 ∧
      c ≤ (pointwiseStabPrim h).bound (.list [gv, encPts S]) +
        pstabK * (Val.list [gv, encPts S]).wt ^ 9) := by
  simp only [pstabFuns] at hb
  have hentry : P.funs[b]? = some (pstabF jp (b + 1)) := hb.left.single
  have hmk : P.HasAt (b + 1) (mkGroupFuns (b + 1)) := hb.right
  set v := Val.list [gv, encPts S] with hv
  have hgv : gv.wt < v.wt := wt_le_wt_list (by simp)
  obtain ⟨gs, rfl, rfl⟩ := hG
  have hS0 := S_le_wt_encGroup gs
  have hP := EvalAll.prim_spec hj (Det.var' (P := P) (env := [v]) (i := 0) rfl)
    (pointwiseStabPrim_spec h ⟨gs, rfl, rfl⟩ S)
  refine FunAll.intro hentry (EvalAll.letE hP fun w0 c0 hw0 => ?_)
  obtain ⟨⟨hs, rfl, hl, hgen⟩, hc0⟩ := hw0
  have dn : Det P [v, .list (hs.map encPerm)] (.get (.get (.var 0) (.nat 0)) (.nat 0)) (.nat n) _ :=
    Det.get' (Det.get' (Det.var' rfl) (Det.nat 0) rfl) (Det.nat 0) rfl
  have dc := Det.call (Det.mk2 dn (Det.var' (P := P) (env := [v, .list (hs.map encPerm)]) (i := 1)
    rfl)) (mkGroup_spec hmk hs)
  have hW6 := wt_encGroup_le_sq hl
  refine dc.post fun c hc => ⟨⟨hs, rfl, hgen⟩, hW6, ?_⟩
  -- the cost
  have hS3 := measure_le_of_sq hl
  have w1 := wt_gens_le_encGroup hs
  have w2 := S_le_wt_encGroup hs
  have w3 := wt_list2_le (.nat n) (.list (hs.map encPerm))
  have w4 := wt_nat_le n
  have w5 : (encGroup gs).wt < v.wt := hgv
  have w6 : (encGroup gs).wt = (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt := rfl
  obtain ⟨-, hn⟩ := le_S gs.length n
  generalize hW : (encGroup hs).wt = W at *
  generalize hV : v.wt = V at *
  have hnV : n + 1 ≤ V := by omega
  have h1 : ((hs.length + 2) * (n + 1)) ^ 3 ≤ 8 * V ^ 9 :=
    calc ((hs.length + 2) * (n + 1)) ^ 3 ≤ (2 * (n + 1) ^ 3) ^ 3 := Nat.pow_le_pow_left hS3 3
      _ = 8 * (n + 1) ^ 9 := by ring
      _ ≤ 8 * V ^ 9 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnV 9)
  have h2 : (n + 1) ^ 6 ≤ V ^ 9 :=
    (Nat.pow_le_pow_left hnV 6).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h3 : V ≤ V ^ 9 := Nat.le_self_pow (by omega) _
  have h4 : mkGroupK * ((hs.length + 2) * (n + 1)) ^ 3 ≤ 800000 * V ^ 9 := by
    simp only [mkGroupK]; omega
  simp only [pstabK]
  omega

end GI.Lang
