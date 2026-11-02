import Workspace.Impl.GiantSel

/-!
# The row partition of the row step, as a value

The column step stores the row record `⟨q, rowPart, some cols⟩` (`Run.rowColumns`), where the
row partition `ColumnPre.rowPart` is `S.domKer label` for the natural row labels `label`. Its
classes on the domain are the label fibers, and the points off the domain form one more class.

The row labels need not be computed from the row normal form: in the row case each Johnson
block is the singleton of the label (`blocks_eq_label`), so the block map of the label value
already gives the row of every point. This file computes the partition value

* `rowLab e J i = a` when position `i` lies in the domain with block `{a}`;
* `rowLab e J i = q` off the domain,

from the label value (`rowPart_det`), and proves that it is a partition value of the row
partition for any natural row labels (`rowPart_val`). The labels are below `k`: `a < q`, and a
point off the domain leaves at most `k - 1` points in the domain, which carry all `q` labels.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup gens sumToFin)

variable {Ω C : Type} {k : ℕ}

/-- The row label of a position: `(lblOf + q) mod (q + 1)`, which is `a` for a position in the
domain with block `{a}` (`lblOf = a + 1`) and `q` off the domain (`lblOf = 0`). -/
noncomputable def rowLab (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (J : JohnsonBlocks S L) (i : Fin k) : ℕ :=
  (lblOf e J i + L.q) % (L.q + 1)

theorem rowLab_off (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S} (J : JohnsonBlocks S L)
    {i : Fin k} (hi : e.symm i ∉ S.dom) : rowLab e J i = L.q := by
  unfold rowLab lblOf
  rw [dif_neg hi, zero_add, Nat.mod_eq_of_lt (by omega)]

theorem rowLab_on (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S} (J : JohnsonBlocks S L)
    {i : Fin k} (hi : e.symm i ∈ S.dom) {a : Fin L.q} (ha : J.p ⟨_, hi⟩ = {a}) :
    rowLab e J i = a := by
  unfold rowLab lblOf
  rw [dif_pos hi, ha]
  rw [findIdx_indicator a _ (fun t => by simp)]
  have ha' := a.2
  rw [show (a : ℕ) + 1 + L.q = a + (L.q + 1) by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- **The row partition value.** For natural row labels `label` (with `q ≥ 5`), `rowLab` is a
partition value, with labels below `k`, of the row partition `S.domKer label`. -/
theorem rowPart_val [Finite Ω] (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (J : JohnsonBlocks S L) (hq : 5 ≤ L.q) {label : Ω → Fin L.q} (hn : NaturalRows S L label) :
    PartitionValC e (encFun (rowLab e J)) (S.domKer fun v => label v) := by
  classical
  have hon : ∀ i (hi : e.symm i ∈ S.dom), rowLab e J i = label (e.symm i) := fun i hi =>
    rowLab_on e J hi (blocks_eq_label J hq hn ⟨_, hi⟩)
  refine ⟨rowLab e J, rfl, fun i => ?_, fun i j => ?_⟩
  · by_cases hi : e.symm i ∈ S.dom
    · rw [hon i hi]
      -- the labels take `q` values in the domain, so `q ≤ k`
      have hsurj : Function.Surjective fun v : S.dom => label v := fun a => by
        obtain ⟨v, hv, h⟩ := hn.onto a
        exact ⟨⟨v, hv⟩, h⟩
      have h1 := Nat.card_le_card_of_surjective _ hsurj
      have h2 : Nat.card S.dom ≤ k := by
        have := Nat.card_le_card_of_injective (fun v : S.dom => e v.1)
          (fun a b h => Subtype.ext (e.injective h))
        simp at this; exact this
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
      have := (label (e.symm i)).2
      omega
    · rw [rowLab_off e J hi]
      -- a point off the domain: the domain has at most `k - 1` points and carries all labels
      have hsurj : Function.Surjective fun v : S.dom => label v := fun a => by
        obtain ⟨v, hv, h⟩ := hn.onto a
        exact ⟨⟨v, hv⟩, h⟩
      have h1 := Nat.card_le_card_of_surjective _ hsurj
      have h2 : Nat.card S.dom < k := by
        have hinj : Function.Injective (fun v : S.dom => e v.1) :=
          fun a b h => Subtype.ext (e.injective h)
        have hns : ¬ Function.Surjective (fun v : S.dom => e v.1) := fun hs => by
          obtain ⟨v, hv⟩ := hs i
          exact hi (by rw [← hv]; simpa using v.2)
        haveI : Fintype S.dom := Fintype.ofFinite _
        have := Fintype.card_lt_of_injective_not_surjective _ hinj hns
        rw [Nat.card_eq_fintype_card]
        simp at this; exact this
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
      omega
  · by_cases hi : e.symm i ∈ S.dom <;> by_cases hj : e.symm j ∈ S.dom
    · rw [hon i hi, hon j hj, State.domKer_r_of_mem _ hi hj, Fin.val_inj]
    · rw [hon i hi, rowLab_off e J hj]
      have := (label (e.symm i)).2
      refine iff_of_false (by omega) fun h => ?_
      have h' : (if h : e.symm i ∈ S.dom then some (label (e.symm i)) else none) =
          (if h : e.symm j ∈ S.dom then some (label (e.symm j)) else none) := h
      rw [dif_pos hi, dif_neg hj] at h'
      exact absurd h' (by simp)
    · rw [hon j hj, rowLab_off e J hi]
      have := (label (e.symm j)).2
      refine iff_of_false (by omega) fun h => ?_
      have h' : (if h : e.symm i ∈ S.dom then some (label (e.symm i)) else none) =
          (if h : e.symm j ∈ S.dom then some (label (e.symm j)) else none) := h
      rw [dif_neg hi, dif_pos hj] at h'
      exact absurd h' (by simp)
    · rw [rowLab_off e J hi, rowLab_off e J hj]
      refine iff_of_true rfl ?_
      show (if h : e.symm i ∈ S.dom then some _ else none) =
        (if h : e.symm j ∈ S.dom then some _ else none)
      rw [dif_neg hi, dif_neg hj]

/-! ### The program -/

/-- On `[q, x]`: `(x + q) mod (q + 1)`. -/
def rowLabStepF : Expr :=
  .arith .mod (.arith .add (arg 1) (arg 0)) (.arith .add (arg 0) (.nat 1))

/-- The row partition functions at `r`: the step, then a `map` over it. -/
def rowPartFuns (r : ℕ) : List Expr := rowLabStepF :: mapFuns (r + 1) r

/-- The label map of the blocks (the map of `natFuns` at `b + 57`), on `[sv, lv]`. -/
def lblMapE (b : ℕ) : Expr := .call (b + 57) (mk2 (.nat 0) (.get natLV (.nat 5)))

/-- The row partition value, on `[sv, lv]`. -/
def rowPartE (b r : ℕ) : Expr := .call (r + 1) (mk2 natQ (lblMapE b))

theorem rowLabStep_spec {P : Program} {r : ℕ} (hf : P.funs[r]? = some rowLabStepF) (q x : ℕ) :
    FunDet P r (.list [.nat q, .nat x]) (.nat ((x + q) % (q + 1))) (100 * (x + q + 2)) := by
  have g0 := Det.arg' (P := P) (vs := [.nat q, .nat x]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [.nat q, .nat x]) (rest := []) (j := 1) rfl
  have d1 := Det.arith' (op := .add) g1 g0 (z := x + q) rfl
  have d2 := Det.arith' (op := .add) g0 (Det.nat 1) (z := q + 1) rfl
  have d3 := Det.arith' (op := .mod) d1 d2 (z := (x + q) % (q + 1)) rfl
  refine FunDet.intro hf (d3.mono ?_)
  have w := wt_list2_le (.nat q) (.nat x)
  have wq := wt_nat_le q
  have wx := wt_nat_le x
  have hm : (x + q) % (q + 1) ≤ q := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  omega

/-- The constant of the row partition value. -/
def rowPartK : ℕ := 10 ^ 13

theorem wt_encFun_lblOf (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (J : JohnsonBlocks S L) : (encFun (lblOf e J)).wt ≤ k * (2 * (L.q + 1) + 5) + 4 :=
  wt_encFun_le _ (lblOf_le e J)

/-- **The label map of the blocks**: on `[sv, lv]` (with `lv` a label value), the call
`lblMapE b` returns `encFun (lblOf e J)`. -/
theorem lblMap_det {P : Program} {b jpre : ℕ} (hb : NatAt P b jpre) (e : Ω ≃ Fin k)
    {S : State Ω C} (L : SuppliedLabels S) {sv lv : Val} (hlv : LabValStd e S lv L)
    (hq : 1 ≤ L.q) (rest : List Val) :
    Det P (.list [sv, lv] :: rest) (lblMapE b) (encFun (lblOf e L.con.blocks))
      (rowPartK * ((Val.list [sv, lv]).wt + k + L.q + 2) ^ 4) := by
  classical
  set J := L.con.blocks with hJ
  obtain ⟨ps, hlvE, -, -, -⟩ := hlv
  have dblk := natLVget_det (P := P) (sv := sv) rest hlvE (i := 5) (u := blkMapVal e J) rfl
  have hmap := mapList_spec hb.lblMap (List.finRange k)
    (fun i => if h : e.symm i ∈ S.dom then
      encFun (fun j : Fin L.q => if j ∈ J.p ⟨e.symm i, h⟩ then 1 else 0) else .list [])
    (fun i => .nat (lblOf e J i)) (c := .nat 0) (B := natStepK * (L.q + 2) ^ 3)
    (fun i _ i' _ he => by
      simp only [Val.nat.injEq]
      unfold lblOf
      by_cases hi : e.symm i ∈ S.dom <;> by_cases hi' : e.symm i' ∈ S.dom <;>
        simp only [hi, hi', dite_true, dite_false] at he ⊢
      · rw [encFun_injective he]
      · have := congrArg (fun v : Val => match v with | .list l => l.length | .nat _ => 0) he
        simp [encFun] at this; omega
      · have := congrArg (fun v : Val => match v with | .list l => l.length | .nat _ => 0) he
        simp [encFun] at this; omega)
    (fun i _ => by
      by_cases hi : e.symm i ∈ S.dom
      · simp only [hi, dite_true]
        have := lblStep_some hb.lblStep hb.findEq hq
          (fun j : Fin L.q => if j ∈ J.p ⟨e.symm i, hi⟩ then 1 else 0)
          (fun t => by dsimp only; split_ifs <;> omega)
        unfold lblOf; simp only [hi, dite_true]
        exact this
      · simp only [hi, dite_false]
        have := lblStep_none hb.lblStep
        unfold lblOf; simp only [hi, dite_false]
        refine this.mono ?_
        have : 1 ≤ (L.q + 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
        simp only [natStepK]; omega)
  have hblk : blkMapVal e J = .list ((List.finRange k).map fun i => if h : e.symm i ∈ S.dom then
      encFun (fun j : Fin L.q => if j ∈ J.p ⟨e.symm i, h⟩ then 1 else 0) else .list []) := rfl
  rw [hblk] at dblk
  have d2 := Det.call (Det.mk2 (Det.nat (P := P) (env := .list [sv, lv] :: rest) 0) dblk) hmap
  have hlblV : Val.list ((List.finRange k).map fun i => Val.nat (lblOf e J i)) =
    encFun (lblOf e J) := rfl
  rw [hlblV, ← hblk] at d2
  refine d2.mono ?_
  -- the cost
  clear d2 hmap dblk
  set A := Val.list [sv, lv] with hA
  set T := A.wt + k + L.q + 2 with hT
  have hbw : (blkMapVal e J).wt < A.wt := by
    have h1 : (blkMapVal e J).wt < lv.wt := by rw [hlvE]; exact wt_le_wt_list (by simp [hJ])
    have h2 : lv.wt < A.wt := wt_le_wt_list (by simp)
    omega
  have w1 := wt_encFun_lblOf e J
  have w2 := wt_list2_le (.nat 0) (blkMapVal e J)
  have w0 := wt_nat_le 0
  have hT1 : 1 ≤ T := by omega
  have p1 : T ≤ T ^ 4 := Nat.le_self_pow (by norm_num) _
  have hkq : k * (2 * (L.q + 1) + 5) ≤ 7 * T ^ 2 := by
    have : k * (2 * (L.q + 1) + 5) ≤ T * (7 * T) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have p24 : T ^ 2 ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by omega)
  have p12 : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num) _
  have p34 : T ^ 3 ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by omega)
  have m1 : k * (natStepK * (L.q + 2) ^ 3) ≤ natStepK * T ^ 4 :=
    mul_le_c_pow (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
  have m2 : (k + 1) * ((Val.list [.nat 0, blkMapVal e J]).wt + (encFun (lblOf e J)).wt + 1) ≤
      100 * T ^ 3 := by
    have : (Val.list [.nat 0, blkMapVal e J]).wt + (encFun (lblOf e J)).wt + 1 ≤ 50 * T ^ 2 := by
      omega
    calc _ ≤ T * (50 * T ^ 2) := Nat.mul_le_mul (by omega) this
      _ = 50 * T ^ 3 := by ring
      _ ≤ 100 * T ^ 3 := by omega
  have m3 := Nat.mul_le_mul_left mapK m2
  rw [List.length_finRange]
  rw [Nat.mul_assoc mapK]
  simp only [rowPartK, natStepK, mapK] at *
  omega

/-- **The row partition value is computed**: on `[sv, lv]` (with `lv` a label value),
`rowPartE b r` returns `encFun (rowLab e J)`, at cost at most `2 rowPartK T⁴` with
`T = wt [sv, lv] + k + q + 2`. -/
theorem rowPart_det {P : Program} {b jpre r : ℕ} (hb : NatAt P b jpre)
    (hr : P.HasAt r (rowPartFuns r)) (e : Ω ≃ Fin k)
    {S : State Ω C} (L : SuppliedLabels S) {sv lv : Val} (hlv : LabValStd e S lv L)
    (hq : 1 ≤ L.q) (rest : List Val) :
    Det P (.list [sv, lv] :: rest) (rowPartE b r) (encFun (rowLab e L.con.blocks))
      (2 * rowPartK * ((Val.list [sv, lv]).wt + k + L.q + 2) ^ 4) := by
  set J := L.con.blocks with hJ
  have hlv' := hlv
  obtain ⟨ps, hlvE, -, -, -⟩ := hlv
  have hst : P.funs[r]? = some rowLabStepF := by
    simpa [rowPartFuns] using hr 0 (by simp [rowPartFuns])
  have hm : P.HasAt (r + 1) (mapFuns (r + 1) r) := by
    have := hr.right (A := [rowLabStepF]) (B := mapFuns (r + 1) r)
    simpa [Nat.add_comm] using this
  have dQ := natLVget_det (P := P) (sv := sv) rest hlvE (i := 0) (u := .nat L.q) rfl
  have dL := lblMap_det (sv := sv) hb e L hlv' hq rest
  have hmap := mapList_spec hm (List.finRange k) (fun i => .nat (lblOf e J i))
    (fun i => .nat (rowLab e J i)) (c := .nat L.q) (B := 100 * (2 * L.q + 3))
    (fun i _ i' _ he => by
      simp only [Val.nat.injEq] at he ⊢
      unfold rowLab; rw [he])
    (fun i _ => (rowLabStep_spec hst L.q (lblOf e J i)).mono (by
      have := lblOf_le e J i; omega))
  have hlblV : Val.list ((List.finRange k).map fun i => Val.nat (lblOf e J i)) =
    encFun (lblOf e J) := rfl
  have hrowV : Val.list ((List.finRange k).map fun i => Val.nat (rowLab e J i)) =
    encFun (rowLab e J) := rfl
  rw [hlblV, hrowV] at hmap
  have d := Det.call (Det.mk2 dQ dL) hmap
  refine d.mono ?_
  clear d hmap dL dQ
  set A := Val.list [sv, lv] with hA
  set T := A.wt + k + L.q + 2 with hT
  have hT1 : 1 ≤ T := by omega
  have p1 : T ≤ T ^ 4 := Nat.le_self_pow (by norm_num) _
  have p12 : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num) _
  have p24 : T ^ 2 ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by omega)
  have p34 : T ^ 3 ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by omega)
  have hkq : k * (2 * (L.q + 1) + 5) ≤ 7 * T ^ 2 := by
    have : k * (2 * (L.q + 1) + 5) ≤ T * (7 * T) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hkq2 : k * (2 * L.q + 5) ≤ 7 * T ^ 2 := by
    have : k * (2 * L.q + 5) ≤ T * (7 * T) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have w1 := wt_encFun_lblOf e J
  have w2 : (encFun (rowLab e J)).wt ≤ k * (2 * L.q + 5) + 4 :=
    wt_encFun_le _ (fun i => Nat.le_of_lt_succ (Nat.mod_lt _ (by omega)))
  have w3 := wt_list2_le (.nat L.q) (encFun (lblOf e J))
  have wq := wt_nat_le L.q
  have m1 : k * (100 * (2 * L.q + 3)) ≤ 300 * T ^ 2 := by
    have : k * (100 * (2 * L.q + 3)) ≤ T * (300 * T) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have m2 : (k + 1) * ((Val.list [.nat L.q, encFun (lblOf e J)]).wt +
      (encFun (rowLab e J)).wt + 1) ≤ 100 * T ^ 3 := by
    have : (Val.list [.nat L.q, encFun (lblOf e J)]).wt + (encFun (rowLab e J)).wt + 1 ≤
        50 * T ^ 2 := by omega
    calc _ ≤ T * (50 * T ^ 2) := Nat.mul_le_mul (by omega) this
      _ = 50 * T ^ 3 := by ring
      _ ≤ 100 * T ^ 3 := by omega
  have m3 := Nat.mul_le_mul_left mapK m2
  have hsJ : (Val.list [.nat L.q, encFun (lblOf e L.con.blocks)]).wt =
      (Val.list [.nat L.q, encFun (lblOf e J)]).wt := rfl
  have hsJ' : (encFun (lblOf e L.con.blocks)).wt = (encFun (lblOf e J)).wt := rfl
  rw [List.length_finRange, Nat.mul_assoc mapK]
  simp only [rowPartK, mapK] at *
  omega

end GI.Impl
