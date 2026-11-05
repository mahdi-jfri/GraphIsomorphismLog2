module

public import Workspace.Impl.VsFMatPow
public import Workspace.Impl.AggStructDC

@[expose] public section

/-!
# Transposing a matrix

Matrices are lists of rows. The vector stabilizer program stores the matrix of `φ(g)` transposed, so that applying
it to a row vector is the row-times-matrix product `vsFRowMul`. The input gives the matrices
untransposed; this file transposes them.

* `vsQTr A d`: the transpose (`d` columns read from the rows of `A`).
* `vsQTrFuns b` (12 functions), `vsQTr_spec`: on `[A, d]` it returns `vsQTr A d`.
* `vsQ_map_det`: a deterministic `map`.
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- **A deterministic map** over encoded items (the encoding injective). -/
theorem vsQ_map {α : Type} {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val}
    (l : List α) (enc g : α → Val) (hinj : Function.Injective enc) {B : ℕ}
    (hf : ∀ a ∈ l, FunDet P f (.list [c, enc a]) (g a) B) :
    FunDet P b (.list [c, .list (l.map enc)]) (.list (l.map g))
      (l.length * B + mapK * (l.length + 1) * ((Val.list [c, .list (l.map enc)]).wt +
        (Val.list (l.map g)).wt + 1)) := by
  refine (map_spec h (R := fun x w => ∀ a ∈ l, enc a = x → w = g a) (B := fun _ => B)
    ?_).mono fun w cost hw => ?_
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    refine FunAll.mono (hf a ha) fun w cost hw => ⟨fun a' _ he => ?_, hw.2⟩
    rw [hinj he, hw.1]
  · obtain ⟨ws, rfl, hR, hc⟩ := hw
    have e := forall₂_map_eq (fun a ha w hw => hw a ha rfl) hR
    subst e
    refine ⟨rfl, ?_⟩
    simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
    exact hc

/-- Cost arithmetic: one more factor `Q`. -/
theorem vsQ_mulQ {a X c Q k : ℕ} (ha : a ≤ Q) (hX : X ≤ c * Q ^ k) : a * X ≤ c * Q ^ (k + 1) :=
  calc a * X ≤ Q * (c * Q ^ k) := Nat.mul_le_mul ha hX
    _ = c * Q ^ (k + 1) := by ring

/-- Cost arithmetic: a lower power. -/
theorem vsQ_powle {c Q i k : ℕ} (hQ : 1 ≤ Q) (hik : i ≤ k) : c * Q ^ i ≤ c * Q ^ k :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hQ hik)

theorem vsQ_le_pow (N : ℕ) {k : ℕ} (hk : 1 ≤ k) : N + 1 ≤ (N + 1) ^ k :=
  Nat.le_self_pow (by omega) _

theorem vsQ_one_le_pow (N k : ℕ) : 1 ≤ (N + 1) ^ k := Nat.one_le_pow _ _ (by omega)

theorem vsQ_natList_injective : Function.Injective natList := fun _ _ h => vsFMat_natList_inj h

theorem valNat_injective : Function.Injective Val.nat := fun _ _ h => Val.nat.inj h

/-- The transpose of a `d`-column matrix. -/
def vsQTr (A : List (List ℕ)) (d : ℕ) : List (List ℕ) :=
  (List.range d).map fun j => A.map fun r => r.getD j 0

/-- On `[A, d]`: map the column function over `range d`, with context `A`. -/
def vsQTrF (b : ℕ) : Expr := .call (b + 1) (mk2 (arg 0) (.call (b + 9) (arg 1)))

/-- On `[A, j]`: column `j`, by mapping the entry function over the rows. -/
def vsQColF (b : ℕ) : Expr := .call (b + 5) (mk2 (arg 1) (arg 0))

/-- On `[j, r]`: entry `j` of the row. -/
def vsQEntF : Expr := .get (arg 1) (arg 0)

/-- The transpose at base `b` (12 functions). -/
def vsQTrFuns (b : ℕ) : List Expr :=
  [vsQTrF b] ++ mapFuns (b + 1) (b + 4) ++ [vsQColF b] ++ mapFuns (b + 5) (b + 8) ++
    [vsQEntF] ++ rangeFuns (b + 9)

theorem vsQTrFuns_length (b : ℕ) : (vsQTrFuns b).length = 12 := rfl

/-- Weight of a matrix with entries and row lengths at most `N`, and at most `N + 1` rows. -/
theorem vsQ_wt_mat {N : ℕ} {A : List (List ℕ)} (hB : ∀ r ∈ A, ∀ y ∈ r, y ≤ N)
    (lB : ∀ r ∈ A, r.length ≤ N) (hl : A.length ≤ N + 1) :
    (Val.list (A.map natList)).wt ≤ 11 * (N + 1) ^ 3 + 4 := wt_vsFMat_le hB lB hl

set_option maxHeartbeats 1000000 in
/-- **Transpose.** For a `d × d` matrix with entries below `p`, at cost at most
`10^6 (N + 1)^5`. -/
theorem vsQTr_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsQTrFuns b)) {p d N : ℕ}
    (hpN : p ≤ N) (hdN : d ≤ N) {A : List (List ℕ)} (hA : VsFSq p d A) :
    FunDet P b (.list [.list (A.map natList), .nat d]) (.list ((vsQTr A d).map natList))
      (10 ^ 6 * (N + 1) ^ 5) := by
  have h0 : P.funs[b]? = some (vsQTrF b) := h.get (j := 0) (by rw [vsQTrFuns_length]; omega)
  have hm1 : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.block 1 rfl
  have h4 : P.funs[b + 4]? = some (vsQColF b) := h.get (j := 4) (by rw [vsQTrFuns_length]; omega)
  have hm2 : P.HasAt (b + 5) (mapFuns (b + 5) (b + 8)) := h.block 5 rfl
  have h8 : P.funs[b + 8]? = some vsQEntF := h.get (j := 8) (by rw [vsQTrFuns_length]; omega)
  have hr : P.HasAt (b + 9) (rangeFuns (b + 9)) := h.block 9 rfl
  have hQ1 : 1 ≤ (N + 1) := by omega
  have hdQ : d + 1 ≤ (N + 1) := by omega
  have hrow : ∀ r ∈ A, (∀ y ∈ r, y < p) ∧ r.length = d := hA.rows
  have wA := vsQ_wt_mat (N := N) (A := A) (fun r hr y hy => ((hrow r hr).1 y hy).le.trans hpN)
    (fun r hr => ((hrow r hr).2).le.trans hdN) (by rw [hA.len]; omega)
  have hgd : ∀ j, ∀ r ∈ A, r.getD j 0 ≤ N := by
    intro j r hr
    rcases Nat.lt_or_ge j r.length with hjr | hjr
    · rw [List.getD_eq_getElem _ _ hjr]
      exact ((hrow r hr).1 _ (List.getElem_mem _)).le.trans hpN
    · rw [List.getD_eq_default _ _ hjr]; omega
  -- the entry function
  have hent : ∀ j < d, ∀ r ∈ A, FunDet P (b + 8) (.list [.nat j, natList r]) (.nat (r.getD j 0))
      (100 * (N + 1) ^ 2) := by
    intro j hj r hr
    obtain ⟨hr1, hr2⟩ := hrow r hr
    have hjr : j < r.length := hr2 ▸ hj
    have wr := wt_natList_le_sq (fun y hy => (hr1 y hy).le.trans hpN) (hr2.le.trans hdN)
    have wj := wt_nat_le j
    have wa := wt_list2_le (.nat j) (natList r)
    apply FunDet.intro h8
    have d1 := Det.arg (P := P) (vs := [.nat j, natList r]) (rest := []) (j := 1) (by simp)
    have d0 := Det.arg (P := P) (vs := [.nat j, natList r]) (rest := []) (j := 0) (by simp)
    have dg := Det.get' (x := j) d1 d0 (vs := r.map Val.nat) (v := .nat (r.getD j 0))
      (by simp [List.getD_eq_getElem _ _ hjr, hjr])
    refine dg.mono ?_
    have wv := wt_nat_le (r.getD j 0)
    have := hgd j r hr
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at *
    have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    omega
  -- the column function
  have hcol : ∀ j < d, FunDet P (b + 4) (.list [.list (A.map natList), .nat j])
      (natList (A.map fun r => r.getD j 0)) (2 * 10 ^ 5 * (N + 1) ^ 4) := by
    intro j hj
    have hm := vsQ_map hm2 (c := .nat j) A natList (fun r => .nat (r.getD j 0)) vsQ_natList_injective
      (B := 100 * (N + 1) ^ 2) (hent j hj)
    have e : (A.map fun r => Val.nat (r.getD j 0)) = (A.map fun r => r.getD j 0).map Val.nat := by
      simp [List.map_map, Function.comp_def]
    rw [e] at hm
    apply FunDet.intro h4
    have g0 := Det.arg (P := P) (vs := [.list (A.map natList), .nat j]) (rest := []) (j := 0)
      (by simp)
    have g1 := Det.arg (P := P) (vs := [.list (A.map natList), .nat j]) (rest := []) (j := 1)
      (by simp)
    have dc := Det.call (Det.mk2 g1 g0) hm
    refine dc.mono ?_
    have wcol : (natList (A.map fun r => r.getD j 0)).wt ≤ 5 * (N + 1) ^ 2 :=
      wt_natList_le_sq (fun y hy => by
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy; exact hgd j r hr)
        (by rw [List.length_map, hA.len]; exact hdN)
    have wj := wt_nat_le j
    have wa := wt_list2_le (.list (A.map natList)) (.nat j)
    have wb := wt_list2_le (.nat j) (.list (A.map natList))
    have c1 : A.length * (100 * (N + 1) ^ 2) ≤ 100 * (N + 1) ^ 3 := vsQ_mulQ (by rw [hA.len]; omega) le_rfl
    have q2 : 1 * (N + 1) ^ 2 ≤ 1 * (N + 1) ^ 3 := vsQ_powle hQ1 (by omega)
    have q1 := vsQ_le_pow N (k := 3) (by omega)
    have q3 : 1 * (N + 1) ^ 3 ≤ 1 * (N + 1) ^ 4 := vsQ_powle hQ1 (by omega)
    have q0 := vsQ_one_le_pow N 3
    have q5 := vsQ_le_pow N (k := 3) (by omega)
    have c2 : mapK * (A.length + 1) * ((Val.list [Val.nat j, Val.list (A.map natList)]).wt +
        (natList (A.map fun r => r.getD j 0)).wt + 1) ≤ mapK * (100 * (N + 1) ^ 4) := by
      rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left
      apply vsQ_mulQ (k := 3) (by rw [hA.len]; omega)
      simp only [natList] at *
      omega
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, natList, mapK] at *
    omega
  -- the range
  have wrg : (natList (List.range d)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => (List.mem_range.mp hy).le.trans hdN) (by simp [hdN])
  have hrg' : FunDet P (b + 9) (.nat d) (natList (List.range d)) (10 ^ 4 * (N + 1) ^ 3) := by
    refine (range_spec hr d).mono fun w c hw => ?_
    obtain ⟨rfl, hc⟩ := hw
    refine ⟨rfl, hc.trans ?_⟩
    have wd := wt_nat_le d
    have q2 := vsQ_le_pow N (k := 2) (by omega)
    have c2 : (d + 1) * ((Val.nat d).wt + d + (natList (List.range d)).wt + 1) ≤
        10 * (N + 1) ^ 3 := vsQ_mulQ (k := 2) hdQ (by omega)
    unfold loopModK
    nlinarith
  -- the outer map
  have ho := vsQ_map hm1 (c := .list (A.map natList)) (List.range d) Val.nat
    (fun j => natList (A.map fun r => r.getD j 0)) valNat_injective (B := 2 * 10 ^ 5 * (N + 1) ^ 4)
    (fun j hj => hcol j (List.mem_range.mp hj))
  have e : ((List.range d).map fun j => natList (A.map fun r => r.getD j 0)) =
      (vsQTr A d).map natList := by
    simp [vsQTr, List.map_map, Function.comp_def]
  rw [e] at ho
  apply FunDet.intro h0
  have g0 := Det.arg (P := P) (vs := [.list (A.map natList), .nat d]) (rest := []) (j := 0)
    (by simp)
  have g1 := Det.arg (P := P) (vs := [.list (A.map natList), .nat d]) (rest := []) (j := 1)
    (by simp)
  have dr := Det.call g1 hrg'
  have dc := Det.call (Det.mk2 g0 dr) ho
  refine dc.mono ?_
  have wout := vsQ_wt_mat (N := N) (A := vsQTr A d) (by
      intro r hr y hy
      simp only [vsQTr, List.mem_map, List.mem_range] at hr
      obtain ⟨j, hj, rfl⟩ := hr
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
      exact hgd j r hr)
    (by
      intro r hr
      simp only [vsQTr, List.mem_map, List.mem_range] at hr
      obtain ⟨j, hj, rfl⟩ := hr
      rw [List.length_map, hA.len]; exact hdN)
    (by simp [vsQTr]; omega)
  have wa := wt_list2_le (.list (A.map natList)) (.nat d)
  have wb := wt_list2_le (.list (A.map natList)) (natList (List.range d))
  have wd := wt_nat_le d
  have q2 : 1 * (N + 1) ^ 2 ≤ 1 * (N + 1) ^ 3 := vsQ_powle hQ1 (by omega)
  have q1 := vsQ_le_pow N (k := 3) (by omega)
  have q3 : 1 * (N + 1) ^ 3 ≤ 1 * (N + 1) ^ 5 := vsQ_powle hQ1 (by omega)
  have q4 : 1 * (N + 1) ^ 4 ≤ 1 * (N + 1) ^ 5 := vsQ_powle hQ1 (by omega)
  have c1 : (List.range d).length * (2 * 10 ^ 5 * (N + 1) ^ 4) ≤ 2 * 10 ^ 5 * (N + 1) ^ 5 :=
    vsQ_mulQ (k := 4) (by simp; omega) le_rfl
  have c2 : mapK * ((List.range d).length + 1) * ((Val.list [Val.list (A.map natList),
      Val.list ((List.range d).map Val.nat)]).wt + (Val.list ((vsQTr A d).map natList)).wt + 1)
      ≤ mapK * (200 * (N + 1) ^ 4) := by
    rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left
    have q0 := vsQ_one_le_pow N 3
    have q5 := vsQ_le_pow N (k := 3) (by omega)
    apply vsQ_mulQ (k := 3) (by simp; omega)
    simp only [natList] at *
    omega
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, natList, mapK] at *
  omega

end GI.Impl
