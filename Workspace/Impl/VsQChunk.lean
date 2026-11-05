module

public import Workspace.Impl.VsQTr
public import Workspace.Lang.Lib.OrbitT

@[expose] public section

/-!
# Cutting a list into pieces

The small orbit transporter stores a point as a flat list of numbers. A tuple of subspaces is
stored by concatenating keys of the same length, so reading it back means cutting a list into
`m` pieces of length `k`.

* `vsQChunk k m vs`: the pieces (`vsQChunk_flatten`: it undoes `List.flatten`).
* `vsQChunkFuns b` (12 functions), `vsQChunk_spec`: on `[k, m, vs]` it returns the pieces.
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- The `m` pieces of length `k` of a list. -/
def vsQChunk {α : Type} (d : α) (k m : ℕ) (vs : List α) : List (List α) :=
  (List.range m).map fun i => (List.range k).map fun j => vs.getD (i * k + j) d

theorem vsQChunk_succ {α : Type} (d : α) (k m : ℕ) (vs : List α) :
    vsQChunk d k (m + 1) vs = ((List.range k).map fun j => vs.getD j d) ::
      vsQChunk d k m (vs.drop k) := by
  rw [vsQChunk, List.range_succ_eq_map, List.map_cons, vsQChunk, List.map_map]
  congr 1
  · simp
  · refine List.map_congr_left fun i _ => List.map_congr_left fun j _ => ?_
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2
    rw [Nat.succ_mul]; ring

theorem vsQ_range_getD {α : Type} (d : α) (x rest : List α) :
    ((List.range x.length).map fun j => (x ++ rest).getD j d) = x := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left]

/-- Cutting undoes concatenation of pieces of length `k`. -/
theorem vsQChunk_flatten {α : Type} (d : α) (k : ℕ) (xs : List (List α))
    (hx : ∀ x ∈ xs, x.length = k) : vsQChunk d k xs.length xs.flatten = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hxk := hx x (by simp)
    rw [List.length_cons, vsQChunk_succ, List.flatten_cons, List.drop_left' hxk,
      ih fun y hy => hx y (by simp [hy]), ← hxk, vsQ_range_getD]

/-- On `[k, m, vs]`: map the piece function over `range m`, with context the argument. -/
def vsQChunkF (b : ℕ) : Expr := .call (b + 3) (mk2 (.var 0) (.call (b + 9) (arg 1)))

/-- On `[a, i]`: piece `i`, by mapping the entry function over `range k`. -/
def vsQChunkRowF (b : ℕ) : Expr :=
  .call (b + 6) (mk2 (.var 0) (.call (b + 9) (.get (arg 0) (.nat 0))))

/-- On `[[a, i], j]`: entry `i k + j` of the list. -/
def vsQChunkEntF : Expr :=
  .get (.get (.get (arg 0) (.nat 0)) (.nat 2))
    (.arith .add (.arith .mul (.get (arg 0) (.nat 1)) (.get (.get (arg 0) (.nat 0)) (.nat 0))) (arg 1))

/-- The cutting program at base `b` (12 functions). -/
def vsQChunkFuns (b : ℕ) : List Expr :=
  [vsQChunkF b, vsQChunkRowF b, vsQChunkEntF] ++ mapFuns (b + 3) (b + 1) ++
    mapFuns (b + 6) (b + 2) ++ rangeFuns (b + 9)

theorem vsQChunkFuns_length (b : ℕ) : (vsQChunkFuns b).length = 12 := rfl

set_option maxHeartbeats 2000000 in
/-- **Cutting.** On `[k, m, vs]` with `k m ≤ |vs|`, the `m` pieces of length `k`, at cost at
most `10^8 (N + 1)^4 (W + (N + 1)^2)` when `k, m ≤ N` and `vs` weighs at most `W`. -/
theorem vsQChunk_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsQChunkFuns b)) {k m N W : ℕ}
    {vs : List Val} (hkm : k * m ≤ vs.length) (hk : k ≤ N) (hm : m ≤ N)
    (hW : (Val.list vs).wt ≤ W) :
    FunDet P b (.list [.nat k, .nat m, .list vs])
      (.list ((vsQChunk (.nat 0) k m vs).map Val.list)) (10 ^ 8 * (N + 1) ^ 4 * (W + (N + 1) ^ 2)) := by
  have h0 : P.funs[b]? = some (vsQChunkF b) := h.get (j := 0) (by rw [vsQChunkFuns_length]; omega)
  have h1 : P.funs[b + 1]? = some (vsQChunkRowF b) := h.get (j := 1) (by rw [vsQChunkFuns_length]; omega)
  have h2 : P.funs[b + 2]? = some vsQChunkEntF := h.get (j := 2) (by rw [vsQChunkFuns_length]; omega)
  have hm1 : P.HasAt (b + 3) (mapFuns (b + 3) (b + 1)) := h.block 3 rfl
  have hm2 : P.HasAt (b + 6) (mapFuns (b + 6) (b + 2)) := h.block 6 rfl
  have hr : P.HasAt (b + 9) (rangeFuns (b + 9)) := h.block 9 rfl
  set a := Val.list [.nat k, .nat m, .list vs] with ha
  set Q := W + (N + 1) ^ 2 with hQ
  have hQ1 : 1 ≤ N + 1 := by omega
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ Q := by omega
  have wa : a.wt ≤ 2 * W + 4 * N + 20 := by
    have h := wt_list_le [.nat k, .nat m, .list vs]
    have := wt_nat_le k; have := wt_nat_le m
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h
    show (Val.list [.nat k, .nat m, .list vs]).wt ≤ _
    omega
  have hvs : ∀ v ∈ vs, v.wt ≤ W := fun v hv => (wt_le_wt_list hv).le.trans hW
  -- the range
  have hrg : ∀ t ≤ N, FunDet P (b + 9) (.nat t) (natList (List.range t)) (10 ^ 4 * (N + 1) ^ 3) := by
    intro t ht
    refine (range_spec hr t).mono fun w c hw => ?_
    obtain ⟨rfl, hc⟩ := hw
    refine ⟨rfl, hc.trans ?_⟩
    have wr : (natList (List.range t)).wt ≤ 5 * (N + 1) ^ 2 :=
      wt_natList_le_sq (fun y hy => (List.mem_range.mp hy).le.trans ht) (by simp [ht])
    have wd := wt_nat_le t
    have c2 : (t + 1) * ((Val.nat t).wt + t + (natList (List.range t)).wt + 1) ≤
        10 * (N + 1) ^ 3 := vsQ_mulQ (k := 2) (by omega) (by omega)
    unfold loopModK
    nlinarith
  have wrg : ∀ t ≤ N, (natList (List.range t)).wt ≤ 5 * (N + 1) ^ 2 := fun t ht =>
    wt_natList_le_sq (fun y hy => (List.mem_range.mp hy).le.trans ht) (by simp [ht])
  -- the entry function
  have hent : ∀ i < m, ∀ j < k, FunDet P (b + 2) (.list [.list [a, .nat i], .nat j])
      (vs.getD (i * k + j) (.nat 0)) (1000 * Q) := by
    intro i hi j hj
    have hik : i * k + j < vs.length := by
      have : i * k + j < (i + 1) * k := by rw [Nat.succ_mul]; omega
      have : (i + 1) * k ≤ m * k := Nat.mul_le_mul_right _ hi
      rw [Nat.mul_comm] at hkm; omega
    have hik' : i * k ≤ N * N := by
      have := Nat.mul_le_mul (show i ≤ N by omega) hk; omega
    apply FunDet.intro h2
    set e := Val.list [.list [a, .nat i], .nat j]
    have g0 := Det.arg' (P := P) (rest := []) (vs := [.list [a, .nat i], .nat j]) (j := 0) rfl
    have g1 := Det.arg' (P := P) (rest := []) (vs := [.list [a, .nat i], .nat j]) (j := 1) rfl
    have da := Det.get' g0 (Det.nat 0) (show [a, .nat i][0]? = some a from rfl)
    have di := Det.get' g0 (Det.nat 1) (show [a, .nat i][1]? = some (.nat i) from rfl)
    have dvs := Det.get' da (Det.nat 2) (show [Val.nat k, .nat m, .list vs][2]? = some (.list vs) from rfl)
    have dk := Det.get' da (Det.nat 0) (show [Val.nat k, .nat m, .list vs][0]? = some (.nat k) from rfl)
    have dmul := Det.arith' (op := .mul) di dk (z := i * k) rfl
    have dadd := Det.arith' (op := .add) dmul g1 (z := i * k + j) rfl
    have dg := Det.get' dvs dadd (v := vs.getD (i * k + j) (.nat 0))
      (by rw [List.getD_eq_getElem _ _ hik]; exact List.getElem?_eq_getElem hik)
    refine dg.mono ?_
    have wv : (vs.getD (i * k + j) (.nat 0)).wt ≤ W := by
      rw [List.getD_eq_getElem _ _ hik]; exact hvs _ (List.getElem_mem hik)
    have we := wt_list2_le (.list [a, .nat i]) (.nat j)
    have we2 := wt_list2_le a (.nat i)
    have := wt_nat_le i; have := wt_nat_le j; have := wt_nat_le k
    have := wt_nat_le (i * k); have := wt_nat_le (i * k + j)
    have hNN : N * N ≤ (N + 1) ^ 2 := by nlinarith
    have hvsw : (Val.list vs).wt < a.wt := wt_le_wt_list (by simp)
    omega
  -- the piece function
  have hrow : ∀ i < m, FunDet P (b + 1) (.list [a, .nat i])
      (.list ((List.range k).map fun j => vs.getD (i * k + j) (.nat 0))) (10 ^ 6 * (N + 1) ^ 2 * Q) := by
    intro i hi
    have hmp := vsQ_map hm2 (c := .list [a, .nat i]) (List.range k) Val.nat
      (fun j => vs.getD (i * k + j) (.nat 0)) valNat_injective (B := 1000 * Q)
      (fun j hj => hent i hi j (List.mem_range.mp hj))
    apply FunDet.intro h1
    have g0 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i]) (j := 0) rfl
    have dk := Det.get' g0 (Det.nat 0) (show [Val.nat k, .nat m, .list vs][0]? = some (.nat k) from rfl)
    have dr := Det.call dk (hrg k hk)
    have dv := Det.var' (P := P) (env := [Val.list [a, .nat i]]) (i := 0) rfl
    have dc := Det.call (Det.mk2 dv dr) hmp
    refine dc.mono ?_
    have wout : (Val.list ((List.range k).map fun j => vs.getD (i * k + j) (.nat 0))).wt ≤
        (N + 1) * (2 * W + 1) + 4 := by
      have := GI.Lang.wt_list_le_of ((List.range k).map fun j => vs.getD (i * k + j) (.nat 0)) (c := W)
        (by
          intro v hv
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
          have hj := List.mem_range.mp hj
          have hik : i * k + j < vs.length := by
            have : i * k + j < (i + 1) * k := by rw [Nat.succ_mul]; omega
            have : (i + 1) * k ≤ m * k := Nat.mul_le_mul_right _ hi
            rw [Nat.mul_comm] at hkm; omega
          rw [List.getD_eq_getElem _ _ hik]; exact hvs _ (List.getElem_mem hik))
      have h2 : k * (2 * W + 1) ≤ (N + 1) * (2 * W + 1) := Nat.mul_le_mul_right _ (by omega)
      rw [List.length_map, List.length_range] at this
      omega
    have wr := wrg k hk
    have w2 := wt_list2_le a (.nat i)
    have w3 := wt_list2_le (.list [a, .nat i]) (natList (List.range k))
    have := wt_nat_le i
    have c1 : (List.range k).length * (1000 * Q) ≤ (N + 1) * (1000 * Q) :=
      Nat.mul_le_mul_right _ (by simp; omega)
    have hNQ : Q ≤ (N + 1) * Q := Nat.le_mul_of_pos_left _ (by omega)
    have c2 : mapK * ((List.range k).length + 1) * ((Val.list [.list [a, .nat i],
        .list ((List.range k).map Val.nat)]).wt +
        (Val.list ((List.range k).map fun j => vs.getD (i * k + j) (.nat 0))).wt + 1) ≤
        mapK * ((N + 1) * (200 * ((N + 1) * Q))) := by
      rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul (by simp; omega)
      simp only [natList] at *
      have h1 : (N + 1) * (2 * W + 1) ≤ (N + 1) * (2 * Q) := Nat.mul_le_mul_left _ (by omega)
      have e : (N + 1) * (2 * Q) = 2 * ((N + 1) * Q) := by ring
      have := wt_nat_le i
      have hz1 : 1 ≤ (N + 1) * Q := le_trans (by omega) hNQ
      omega
    have e1 : (N + 1) * (200 * ((N + 1) * Q)) = 200 * ((N + 1) ^ 2 * Q) := by ring
    have e2 : (N + 1) * (1000 * Q) = 1000 * ((N + 1) * Q) := by ring
    have e3 : 10 ^ 6 * (N + 1) ^ 2 * Q = 10 ^ 6 * ((N + 1) ^ 2 * Q) := by ring
    have hNQ2 : (N + 1) * Q ≤ (N + 1) ^ 2 * Q := by
      rw [pow_two, Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
    have hNQ3 : (N + 1) ^ 2 ≤ (N + 1) ^ 2 * Q := Nat.le_mul_of_pos_right _ (by omega)
    have hb3 : (N + 1) ^ 3 ≤ (N + 1) ^ 2 * Q := by
      rw [pow_succ]; exact Nat.mul_le_mul_left _ (by omega)
    have := wt_nat_le k
    have hq3 : (N + 1) * (2 * W + 1) ≤ 3 * ((N + 1) ^ 2 * Q) := by
      have : (N + 1) * (2 * W + 1) ≤ (N + 1) * (3 * Q) := Nat.mul_le_mul_left _ (by omega)
      have e : (N + 1) * (3 * Q) = 3 * ((N + 1) * Q) := by ring
      omega
    simp only [natList, mapK] at *
    omega
  -- the outer map
  have ho := vsQ_map hm1 (c := a) (List.range m) Val.nat
    (fun i => Val.list ((List.range k).map fun j => vs.getD (i * k + j) (.nat 0))) valNat_injective
    (B := 10 ^ 6 * (N + 1) ^ 2 * Q) (fun i hi => hrow i (List.mem_range.mp hi))
  have e : ((List.range m).map fun i => Val.list ((List.range k).map fun j =>
      vs.getD (i * k + j) (.nat 0))) = (vsQChunk (.nat 0) k m vs).map Val.list := by
    simp [vsQChunk, List.map_map, Function.comp_def]
  rw [e] at ho
  apply FunDet.intro h0
  have g1 := Det.arg' (P := P) (rest := []) (vs := [.nat k, .nat m, .list vs]) (j := 1) rfl
  have dr := Det.call g1 (hrg m hm)
  have dv := Det.var' (P := P) (env := [a]) (i := 0) rfl
  have dc := Det.call (Det.mk2 dv dr) ho
  refine dc.mono ?_
  have wout : (Val.list ((vsQChunk (.nat 0) k m vs).map Val.list)).wt ≤
      (N + 1) * (2 * ((N + 1) * (2 * W + 1) + 4) + 1) + 4 := by
    have := GI.Lang.wt_list_le_of ((vsQChunk (.nat 0) k m vs).map Val.list)
      (c := (N + 1) * (2 * W + 1) + 4) (by
        intro v hv
        rw [← e] at hv
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
        have hi := List.mem_range.mp hi
        have := GI.Lang.wt_list_le_of ((List.range k).map fun j => vs.getD (i * k + j) (.nat 0))
          (c := W) (by
            intro v hv
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
            have hj := List.mem_range.mp hj
            have hik : i * k + j < vs.length := by
              have : i * k + j < (i + 1) * k := by rw [Nat.succ_mul]; omega
              have : (i + 1) * k ≤ m * k := Nat.mul_le_mul_right _ hi
              rw [Nat.mul_comm] at hkm; omega
            rw [List.getD_eq_getElem _ _ hik]; exact hvs _ (List.getElem_mem hik))
        have h2 : k * (2 * W + 1) ≤ (N + 1) * (2 * W + 1) := Nat.mul_le_mul_right _ (by omega)
        rw [List.length_map, List.length_range] at this
        omega)
    have h2 : (vsQChunk (.nat 0) k m vs).length ≤ N + 1 := by simp [vsQChunk]; omega
    have h3 := Nat.mul_le_mul_right (2 * ((N + 1) * (2 * W + 1) + 4) + 1) h2
    rw [List.length_map] at this
    omega
  have wr := wrg m hm
  have w2 := wt_list2_le a (natList (List.range m))
  have hNQ : Q ≤ (N + 1) * Q := Nat.le_mul_of_pos_left _ (by omega)
  have hNQ2 : (N + 1) * Q ≤ (N + 1) ^ 2 * Q := by
    rw [pow_two, Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hNQ3 : (N + 1) ^ 2 * Q ≤ (N + 1) ^ 3 * Q :=
    Nat.mul_le_mul_right Q (Nat.pow_le_pow_right (by omega) (by omega))
  have hb3 : (N + 1) ^ 3 ≤ (N + 1) ^ 3 * Q := Nat.le_mul_of_pos_right _ (by omega)
  have hq3 : (N + 1) * (2 * W + 1) ≤ 3 * ((N + 1) ^ 2 * Q) := by
    have : (N + 1) * (2 * W + 1) ≤ (N + 1) * (3 * Q) := Nat.mul_le_mul_left _ (by omega)
    have e : (N + 1) * (3 * Q) = 3 * ((N + 1) * Q) := by ring
    omega
  have hw2 : (N + 1) * (2 * ((N + 1) * (2 * W + 1) + 4) + 1) ≤ 20 * ((N + 1) ^ 3 * Q) := by
    have : 2 * ((N + 1) * (2 * W + 1) + 4) + 1 ≤ 20 * ((N + 1) ^ 2 * Q) := by omega
    have := Nat.mul_le_mul_left (N + 1) this
    have e : (N + 1) * (20 * ((N + 1) ^ 2 * Q)) = 20 * ((N + 1) ^ 3 * Q) := by ring
    omega
  have c1 : (List.range m).length * (10 ^ 6 * (N + 1) ^ 2 * Q) ≤ 10 ^ 6 * ((N + 1) ^ 3 * Q) := by
    have := Nat.mul_le_mul_right (10 ^ 6 * (N + 1) ^ 2 * Q) (show (List.range m).length ≤ N + 1 by simp; omega)
    have e : (N + 1) * (10 ^ 6 * (N + 1) ^ 2 * Q) = 10 ^ 6 * ((N + 1) ^ 3 * Q) := by ring
    omega
  have c2 : mapK * ((List.range m).length + 1) * ((Val.list [a, .list ((List.range m).map Val.nat)]).wt +
      (Val.list ((vsQChunk (.nat 0) k m vs).map Val.list)).wt + 1) ≤
      mapK * ((N + 2) * (100 * ((N + 1) ^ 3 * Q))) := by
    rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left
    apply Nat.mul_le_mul (by rw [List.length_range]; omega)
    simp only [natList] at *
    have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have c3 : (N + 2) * (100 * ((N + 1) ^ 3 * Q)) ≤ 200 * ((N + 1) ^ 3 * Q) * (N + 1) := by
    have : N + 2 ≤ 2 * (N + 1) := by omega
    have := Nat.mul_le_mul_right (100 * ((N + 1) ^ 3 * Q)) this
    have e : 2 * (N + 1) * (100 * ((N + 1) ^ 3 * Q)) = 200 * ((N + 1) ^ 3 * Q) * (N + 1) := by ring
    omega
  have e4 : 200 * ((N + 1) ^ 3 * Q) * (N + 1) = 200 * ((N + 1) ^ 4 * Q) := by ring
  have h34 : (N + 1) ^ 3 * Q ≤ (N + 1) ^ 4 * Q :=
    Nat.mul_le_mul_right Q (Nat.pow_le_pow_right (by omega) (by omega))
  have eQ : 10 ^ 8 * (N + 1) ^ 4 * (W + (N + 1) ^ 2) = 10 ^ 8 * ((N + 1) ^ 4 * Q) := by
    rw [hQ]; ring
  rw [eQ]
  have := wt_nat_le m
  have ea : (Val.list [.nat k, .nat m, .list vs]).wt = a.wt := rfl
  simp only [natList, mapK] at *
  omega

end GI.Impl
