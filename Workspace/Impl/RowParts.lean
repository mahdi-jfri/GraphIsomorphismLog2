import Workspace.Impl.RowA18Link
import Workspace.Impl.FreshColor

/-!
# The row-`0` part of a generator, in `GI.Lang`

`partsMapFuns` maps a list of pairs `[a, π a]` to the row-`0` parts of their first parts:
for the list `zs` of the positions of row `0`, the part of `a` lists, for each `β < |zs|`, the
index of `a (zs[β])` in `zs` (`partNat`, `Workspace/Impl/RowA18Link.lean`).

* `partStep_spec`: one entry, by `findEq` (`findEqW_spec`);
* `part_spec`: one permutation, a `map` over `range |zs|`;
* `partsMap_spec`: a list of pairs.

The cost is polynomial in `M = n + q + |ps| + 2`; it needs only that the positions in `zs` are
below `n` and that `|zs| ≤ n`. No cited task.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {n q : ℕ}

/-- On `[[a, zs], β]`: the index of `a (zs[β])` in `zs` (`findEq` at `fe`). -/
def partStepF (fe : ℕ) : Expr :=
  .call fe (mk2 (.get (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1)))
    (.get (arg 0) (.nat 1)))

/-- On `[zs, [a, b]]`: the row part of `a` (`map` at `b + 1`, `range` at `b + 5`, `findEq` at
`b + 8`). -/
def partF (b : ℕ) : Expr :=
  .call (b + 1) (mk2 (mk2 (.get (arg 1) (.nat 0)) (arg 0)) (.call (b + 5) (.length (arg 0))))

/-- The part module at `b` (twelve functions). -/
def partFuns (b : ℕ) : List Expr :=
  [partF b] ++ mapFuns (b + 1) (b + 4) ++ [partStepF (b + 8)] ++ rangeFuns (b + 5) ++
    findEqFuns (b + 8)

/-- `map partF` at `b` (fifteen functions). -/
def partsMapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ partFuns (b + 3)

/-- The positions are below `n`, and there are at most `n` of them. -/
structure ZsOK (n : ℕ) (zs : List ℕ) : Prop where
  lt : ∀ z ∈ zs, z < n
  len : zs.length ≤ n

theorem get_encPerm (a : Perm (Fin n)) {i : ℕ} (hi : i < n) :
    (List.map (fun j : Fin n => Val.nat (a j)) (List.finRange n))[i]? = some (.nat (permNat a i)) := by
  simp [permNat, hi]

theorem wt_zs_le {zs : List ℕ} (h : ZsOK n zs) : (natList zs).wt ≤ 7 * (n + 1) ^ 2 := by
  have := wt_natList_le_sq (B := n) (fun z hz => (h.lt z hz).le) h.len
  omega

/-- The cost constant of one entry. -/
def partStepK : ℕ := 10 ^ 8

theorem partStep_spec {P : Program} {f fe : ℕ} (hf : P.funs[f]? = some (partStepF fe))
    (hfe : P.HasAt fe (findEqFuns fe)) (a : Perm (Fin n)) {zs : List ℕ} (hz : ZsOK n zs)
    {β : ℕ} (hβ : β < zs.length) :
    FunDet P f (.list [.list [encPerm a, natList zs], .nat β])
      (.nat (zs.findIdx fun x => decide (x = permNat a (zs.getD β 0))))
      (partStepK * (n + 1) ^ 4) := by
  set c := Val.list [encPerm a, natList zs] with hc
  set A := Val.list [c, .nat β] with hA
  have g0 := Det.arg' (P := P) (vs := [c, .nat β]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [c, .nat β]) (rest := []) (j := 1) rfl
  have gz := Det.get' g0 (Det.nat 1) (v := natList zs) rfl
  have hzβ : zs.getD β 0 < n := by
    rw [List.getD_eq_getElem _ _ hβ]; exact hz.lt _ (List.getElem_mem hβ)
  have gzb := Det.get' gz g1 (v := .nat (zs.getD β 0)) (by
    simp [natList, hβ])
  have ga := Det.get' g0 (Det.nat 0) (v := encPerm a) rfl
  have gaz := Det.get' ga gzb (v := .nat (permNat a (zs.getD β 0))) (get_encPerm a hzβ)
  have d := Det.call (Det.mk2 gaz gz) (findEqW_spec hfe zs (permNat a (zs.getD β 0)))
  refine FunDet.intro hf (d.mono ?_)
  -- the cost
  have hpa : permNat a (zs.getD β 0) < n := by
    unfold permNat; rw [dif_pos hzβ]; exact (a _).2
  have wz := wt_zs_le hz
  have wa := wt_encPerm_le a
  have wc := wt_list2_le (encPerm a) (natList zs)
  have wβ := wt_nat_le β
  have wA := wt_list2_le c (.nat β)
  have w1 := wt_nat_le (zs.getD β 0)
  have w2 := wt_nat_le (permNat a (zs.getD β 0))
  have hfi : zs.findIdx (fun x => decide (x = permNat a (zs.getD β 0))) ≤ zs.length :=
    List.findIdx_le_length
  have w3 := wt_nat_le (zs.findIdx fun x => decide (x = permNat a (zs.getD β 0)))
  have w4 := wt_list2_le (.nat (permNat a (zs.getD β 0))) (natList zs)
  have hzl := hz.len
  have eA : (Val.list [c, .nat β]).wt = A.wt := rfl
  set N := n + 1 with hN
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hNN : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N
  have ec : (Val.list [encPerm a, natList zs]).wt = c.wt := rfl
  have hW : (Val.list [.nat (permNat a (zs.getD β 0)), natList zs]).wt + 1 ≤ 30 * N ^ 2 := by
    omega
  have hW2 : findEqWK * ((Val.list [.nat (permNat a (zs.getD β 0)), natList zs]).wt + 1) ^ 2 ≤
      findEqWK * (900 * N ^ 4) := by
    apply Nat.mul_le_mul_left
    calc _ ≤ (30 * N ^ 2) ^ 2 := Nat.pow_le_pow_left hW 2
      _ = 900 * N ^ 4 := by ring
  have hA4 : A.wt ≤ 100 * N ^ 4 := by omega
  have e1 : findEqWK = 10000 := rfl
  rw [e1] at hW2 ⊢
  simp only [partStepK]
  omega

/-- The cost constant of one part. -/
def partK : ℕ := 10 ^ 10

theorem natList_partNat (zs : List ℕ) (a : Perm (Fin n)) :
    natList (partNat zs a) = .list ((List.range zs.length).map fun β =>
      Val.nat (zs.findIdx fun x => decide (x = permNat a (zs.getD β 0)))) := by
  simp [natList, partNat]

theorem wt_partNat_le (zs : List ℕ) (hl : zs.length ≤ n) (a : Perm (Fin n)) :
    (natList (partNat zs a)).wt ≤ 7 * (n + 1) ^ 2 := by
  have := wt_natList_le_sq (xs := partNat zs a) (B := n) (fun x hx => by
    simp only [partNat, List.mem_map, List.mem_range] at hx
    obtain ⟨β, -, rfl⟩ := hx
    exact List.findIdx_le_length.trans hl) (by simp [partNat]; exact hl)
  omega

theorem part_spec {P : Program} {b : ℕ} (h : P.HasAt b (partFuns b)) {zs : List ℕ}
    (hz : ZsOK n zs) (p : Perm (Fin n) × Perm (Fin q)) :
    FunDet P b (.list [natList zs, pairV p]) (natList (partNat zs p.1))
      (partK * (n + q + 1) ^ 6) := by
  have hentry : P.funs[b]? = some (partF b) := by
    simpa using (h.block 0 (gs := [partF b]) (by rfl)).single
  have hmap : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.block 1 (by rfl)
  have hst : P.funs[b + 4]? = some (partStepF (b + 8)) := by
    simpa using (h.block 4 (gs := [partStepF (b + 8)]) (by rfl)).single
  have hrg : P.HasAt (b + 5) (rangeFuns (b + 5)) := h.block 5 (by rfl)
  have hfe : P.HasAt (b + 8) (findEqFuns (b + 8)) := h.block 8 (by rfl)
  set A := Val.list [natList zs, pairV p] with hA
  have g0 := Det.arg' (P := P) (vs := [natList zs, pairV p]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [natList zs, pairV p]) (rest := []) (j := 1) rfl
  have ga := Det.get' g1 (Det.nat 0) (v := encPerm p.1) rfl
  have hlen : (natList zs) = .list (zs.map Val.nat) := rfl
  have gl := Det.length (hlen ▸ g0)
  simp only [List.length_map] at gl
  have hr := range_det hrg zs.length
  rw [← range_eq_encPerm_one] at hr
  have dr := Det.call gl hr
  set c := Val.list [encPerm p.1, natList zs] with hc
  have dc := Det.mk2 ga g0
  have hm := mapList_spec hmap (List.range zs.length) Val.nat
    (fun β => Val.nat (zs.findIdx fun x => decide (x = permNat p.1 (zs.getD β 0))))
    (c := c) (B := partStepK * (n + 1) ^ 4)
    (fun a _ a' _ he => by simp only [Val.nat.injEq] at he; rw [he])
    (fun β hβ => partStep_spec hst hfe p.1 hz (List.mem_range.1 hβ))
  have hnl : Val.list ((List.range zs.length).map Val.nat) = natList (List.range zs.length) := rfl
  rw [hnl, ← natList_partNat] at hm
  have d := Det.call (Det.mk2 dc dr) hm
  refine FunDet.intro hentry (d.mono ?_)
  -- the cost
  clear d hm dc dr hr gl ga g0 g1 hmap hst hrg hfe hentry h
  have hzl := hz.len
  set N := n + q + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hn1 : n + 1 ≤ N := by omega
  have p2 : (n + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hn1 2
  have p4 : (n + 1) ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left hn1 4
  have q3 : (n + 1) ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left hn1 3
  have m24 : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by omega)
  have m34 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by omega)
  have m46 : N ^ 4 ≤ N ^ 6 := Nat.pow_le_pow_right hN1 (by omega)
  have m12 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN1
  have hNN : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N
  have wz := wt_zs_le hz
  have wa := wt_encPerm_le p.1
  have wb := wt_encPerm_le p.2
  have wp : (pairV p).wt ≤ 22 * N ^ 2 := wt_pairV_le p
  have wA := wt_list2_le (natList zs) (pairV p)
  have eA : (Val.list [natList zs, pairV p]).wt = A.wt := rfl
  have wc := wt_list2_le (encPerm p.1) (natList zs)
  have ec : (Val.list [encPerm p.1, natList zs]).wt = c.wt := rfl
  have wr : (natList (List.range zs.length)).wt ≤ 7 * (n + 1) ^ 2 := by
    have := wt_natList_le_sq (xs := List.range zs.length) (B := n)
      (fun x hx => by have := List.mem_range.1 hx; omega) (by simp; omega)
    omega
  have wcr := wt_list2_le c (natList (List.range zs.length))
  have wo := wt_partNat_le zs hzl p.1
  have wl := wt_nat_le zs.length
  have hrl : (List.range zs.length).length = zs.length := List.length_range
  rw [hrl]
  have t1 : zs.length * (partStepK * (n + 1) ^ 4) ≤ N * (partStepK * N ^ 4) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ p4)
  have t2 : N * (partStepK * N ^ 4) ≤ partStepK * N ^ 6 := by
    have : N * (partStepK * N ^ 4) = partStepK * (N * N ^ 4) := by ring
    rw [this]
    apply Nat.mul_le_mul_left
    calc N * N ^ 4 = N ^ 5 := by ring
      _ ≤ N ^ 6 := Nat.pow_le_pow_right hN1 (by omega)
  have t3 : mapK * (zs.length + 1) * ((Val.list [c, natList (List.range zs.length)]).wt +
      (natList (partNat zs p.1)).wt + 1) ≤ mapK * N * (200 * N ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have t4 : mapK * N * (200 * N ^ 2) = 200000 * N ^ 3 := by simp only [mapK]; ring
  have t5 : 8000 * (zs.length + 1) ^ 3 ≤ 8000 * N ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have e1 : partStepK = 100000000 := rfl
  have e2 : partK = 10000000000 := rfl
  have e3 : (Val.list [Val.list (List.map Val.nat zs), pairV p]).wt =
    (Val.list [natList zs, pairV p]).wt := rfl
  have e4 : (Val.list [Val.list [encPerm p.1, natList zs], natList (List.range zs.length)]).wt =
    (Val.list [c, natList (List.range zs.length)]).wt := rfl
  rw [e1] at t1 t2 ⊢
  rw [e2, e3, e4]
  linarith

/-- The cost constant of the parts map. -/
def partsK : ℕ := 10 ^ 12

/-- **The row-`0` parts of a list of pairs.** -/
theorem partsMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (partsMapFuns b)) {zs : List ℕ}
    (hz : ZsOK n zs) (ps : List (Perm (Fin n) × Perm (Fin q))) :
    FunDet P b (.list [natList zs, .list (ps.map pairV)])
      (.list (ps.map fun p => natList (partNat zs p.1))) (partsK * pM n q ps ^ 7) := by
  have hm := mapList_spec h.left ps pairV (fun p => natList (partNat zs p.1)) (c := natList zs)
    (B := partK * (n + q + 1) ^ 6)
    (fun a _ a' _ he => by rw [pairV_injective he])
    (fun p _ => part_spec (h.block 3 (by rfl)) hz p)
  refine hm.mono ?_
  set M := pM n q ps with hM
  have hM1 : 1 ≤ M := by simp only [hM, pM]; omega
  have hn : n + q + 1 ≤ M := by simp only [hM, pM]; omega
  have hl : ps.length + 1 ≤ M := by simp only [hM, pM]; omega
  have p6 : (n + q + 1) ^ 6 ≤ M ^ 6 := Nat.pow_le_pow_left hn 6
  have m12 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ hM1
  have m23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM1 (by omega)
  have m34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by omega)
  have m47 : M ^ 4 ≤ M ^ 7 := Nat.pow_le_pow_right hM1 (by omega)
  have wz := wt_zs_le hz
  have p2 : (n + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have wps := wt_pairs_le_of_len (ps := ps) (le_refl _)
  rw [← hM] at wps
  have wA := wt_list2_le (natList zs) (.list (ps.map pairV))
  have wo := wt_list_map_le ps (fun p => natList (partNat zs p.1)) (W := 7 * (n + 1) ^ 2)
    fun p _ => wt_partNat_le zs hz.len p.1
  have wo2 : ps.length * (2 * (7 * (n + 1) ^ 2) + 1) ≤ M * (15 * M ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have wo3 : M * (15 * M ^ 2) = 15 * M ^ 3 := by ring
  have t1 : ps.length * (partK * (n + q + 1) ^ 6) ≤ M * (partK * M ^ 6) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ p6)
  have t2 : M * (partK * M ^ 6) = partK * M ^ 7 := by ring
  have t3 : mapK * (ps.length + 1) * ((Val.list [natList zs, .list (ps.map pairV)]).wt +
      (Val.list (ps.map fun p => natList (partNat zs p.1))).wt + 1) ≤
      mapK * M * (200 * M ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hl) (by omega)
  have t4 : mapK * M * (200 * M ^ 3) = 200000 * M ^ 4 := by simp only [mapK]; ring
  have e1 : partK = 10000000000 := rfl
  have e2 : partsK = 1000000000000 := rfl
  rw [e1] at t1 t2 ⊢
  rw [e2]
  linarith

end GI.Impl
