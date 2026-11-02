import Workspace.Impl.SmallInv

/-!
# Canonical values of states and answers

The recursion of Section 6 makes many calls. The cost of a call depends on the weight of its
input value, and the work bound of Section 7.4 (`NodeBound'`) only allows a node a cost that
depends on the node. So the values passed between recursive calls must have a weight bounded by
a function of the state alone. A value of the state format (`GI.Assembly.StateVal`) does not have
this property: a group may be given by any number of generators, a partition by any labels and
the colors by any code.

A **canonical value** (`Canon e c v S`) is a state value with

* at most `k²` generators of the group (`k` positions), as the cited algorithms return them
  (`GI.Cited.GensOf`);
* partition labels below `k`;
* color codes below `2k`.

Its weight is at most `stateW k S` (`Canon.wt_le`), an explicit function of `k`, the numbers
stored in the state (the ratios, bounds and origins of the hierarchy, the row degree, `h` and
`N`) and the length of the hierarchy.

A **canonical answer** (`AnsC e u A`) is `[]` for the empty answer, or a coset value
`[x, encGroup gs]` with at most `k²` generators. Its weight is at most `ansW k` (`AnsC.wt_le`).

The first call, on the input of Algorithm 1, may have any value. `Solve` makes its values
canonical before it starts a phase (the joint color compression of Algorithm 5).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-! ### Canonical parts -/

/-- A group value with at most `k²` generators. -/
def GroupValC (k : ℕ) (v : Val) (G : Subgroup (Perm (Fin k))) : Prop :=
  ∃ gs : List (Perm (Fin k)), v = encGroup gs ∧ gens gs = G ∧ gs.length ≤ k ^ 2

theorem GroupValC.groupVal {v : Val} {G : Subgroup (Perm (Fin k))} (h : GroupValC k v G) :
    GroupVal k v G := by
  obtain ⟨gs, rfl, hg, -⟩ := h
  exact ⟨gs, rfl, hg⟩

/-- A partition value with labels below `k`. -/
def PartitionValC (e : Ω ≃ Fin k) (v : Val) (R : Setoid Ω) : Prop :=
  ∃ lab : Fin k → ℕ, v = encFun lab ∧ (∀ i, lab i < k) ∧
    ∀ i j, lab i = lab j ↔ R.r (e.symm i) (e.symm j)

theorem PartitionValC.partitionVal {e : Ω ≃ Fin k} {v : Val} {R : Setoid Ω}
    (h : PartitionValC e v R) : PartitionVal e v R := by
  obtain ⟨lab, rfl, -, hR⟩ := h
  exact ⟨lab, rfl, hR⟩

/-- `[partition, ratio, cap, origin]` with a canonical partition. -/
def IntervalValC (e : Ω ≃ Fin k) (v : Val) (I : Interval Ω) : Prop :=
  ∃ pv, PartitionValC e pv I.part ∧ v = .list [pv, .nat I.ratio, .nat I.cap, .nat I.origin]

/-- The hierarchy, with canonical partitions. -/
def HierValC (e : Ω ≃ Fin k) (v : Val) (l : List (Interval Ω)) : Prop :=
  ∃ vs : List Val, v = .list vs ∧ List.Forall₂ (IntervalValC e) vs l

/-- A row record, with canonical partitions. -/
def RowValC (e : Ω ≃ Fin k) (v : Val) (R : RowRecord Ω) : Prop :=
  ∃ rv cv, PartitionValC e rv R.rows ∧ OptVal (PartitionValC e) cv R.cols ∧
    v = .list [.nat R.m, rv, cv]

/-- **A canonical value of a state**: a state value (`StateVal`) whose group has at most `k²`
generators, whose partitions have labels below `k`, and whose color codes are below `2k`. It
also asks that the type has at most `N` points (`fits`). This holds inside a phase: a fresh
phase starts on the `N` points of the active domain, and the children of `Continue` and
`GiantStep` keep the type and `N`. Last, it asks the invariant `SmallInv` (`Workspace/Impl/SmallInv.lean`): nontrivial
intervals with numbers at most `N`, `ρ ≤ N`, and a row degree at most `N`. It implies `Small`
(`SmallInv.small`, `Canon.small'`), which bounds the numbers stored in the state. The last two
conditions keep the work of a node polynomial in `N`. -/
structure Canon (e : Ω ≃ Fin k) (c : C → ℕ) (v : Val) (S : State Ω C) : Prop where
  val : ∃ gv dv xv yv hv rv,
    GroupValC k gv (groupFin e S.G) ∧ DomVal e dv S.dom ∧ ColorVal e c xv S.x ∧
    ColorVal e c yv S.y ∧ HierValC e hv S.hier ∧ OptVal (RowValC e) rv S.rows ∧
    v = .list [.nat k, gv, dv, xv, yv, hv, rv, boolVal S.floor, .nat S.h, .nat S.N]
  colors : ∀ a, c (S.x a) < 2 * k ∧ c (S.y a) < 2 * k
  fits : k ≤ S.N
  small : SmallInv S

/-- The numbers stored in the state of a canonical value are small. -/
theorem Canon.small' {e : Ω ≃ Fin k} {c : C → ℕ} {v : Val} {S : State Ω C} (h : Canon e c v S) :
    Small S :=
  h.small.small

theorem OptVal.mono {α : Type} {Q Q' : Val → α → Prop} (hQ : ∀ u a, Q u a → Q' u a) {v : Val} :
    ∀ {o : Option α}, OptVal Q v o → OptVal Q' v o
  | none, h => h
  | some _, ⟨u, hu, hv⟩ => ⟨u, hQ _ _ hu, hv⟩

theorem HierValC.hierVal {e : Ω ≃ Fin k} {v : Val} {l : List (Interval Ω)}
    (h : HierValC e v l) : HierVal e v l := by
  obtain ⟨vs, rfl, h⟩ := h
  exact ⟨vs, rfl, h.imp fun u I ⟨pv, hp, hu⟩ => ⟨pv, hp.partitionVal, hu⟩⟩

theorem RowValC.rowVal {e : Ω ≃ Fin k} {v : Val} {R : RowRecord Ω} (h : RowValC e v R) :
    RowVal e v R := by
  obtain ⟨rv, cv, hr, hc, rfl⟩ := h
  exact ⟨rv, cv, hr.partitionVal, OptVal.mono (fun _ _ h => h.partitionVal) hc, rfl⟩

/-- A canonical value is a state value. -/
theorem Canon.stateVal {e : Ω ≃ Fin k} {c : C → ℕ} {v : Val} {S : State Ω C}
    (h : Canon e c v S) : StateVal e c v S := by
  obtain ⟨gv, dv, xv, yv, hv, rv, hg, hd, hx, hy, hh, hr, rfl⟩ := h.val
  exact ⟨gv, dv, xv, yv, hv, rv, hg.groupVal, hd, hx, hy, hh.hierVal,
    OptVal.mono (fun _ _ h => h.rowVal) hr, rfl⟩

/-! ### The weight bound of a canonical value -/

/-- The weight bound of a partition value with labels below `k`. -/
def partW (k : ℕ) : ℕ := k * (2 * k + 5) + 4

/-- The weight bound of an interval value. -/
def intervalW (k : ℕ) (I : Interval Ω) : ℕ :=
  2 * (partW k + (I.ratio + 2) + (I.cap + 2) + (I.origin + 2)) + 8

/-- The weight bound of a hierarchy value. -/
def hierW (k : ℕ) (l : List (Interval Ω)) : ℕ := 2 * (l.map (intervalW k)).sum + l.length + 4

/-- The weight bound of a row-record value. -/
def rowsW (k : ℕ) : Option (RowRecord Ω) → ℕ
  | none => 4
  | some R => 2 * (2 * ((R.m + 2) + partW k + (2 * partW k + 5)) + 7) + 5

/-- The weight bound of a group value with at most `k²` generators. -/
def groupW (k : ℕ) : ℕ := 40 * ((k ^ 2 + 2) * (k + 1)) ^ 2

/-- **The weight bound of a canonical state value.** -/
def stateW (k : ℕ) (S : State Ω C) : ℕ :=
  2 * ((k + 2) + groupW k + (k * 7 + 4) + 2 * (k * (2 * (2 * k) + 5) + 4) + hierW k S.hier +
    rowsW k S.rows + 3 + (S.h + 2) + (S.N + 2)) + 14

theorem PartitionValC.wt_le {e : Ω ≃ Fin k} {v : Val} {R : Setoid Ω}
    (h : PartitionValC e v R) : v.wt ≤ partW k := by
  obtain ⟨lab, rfl, hl, -⟩ := h
  exact wt_encFun_le lab (B := k) fun i => (hl i).le

theorem GroupValC.wt_le {v : Val} {G : Subgroup (Perm (Fin k))} (h : GroupValC k v G) :
    v.wt ≤ groupW k := by
  obtain ⟨gs, rfl, -, hl⟩ := h
  refine (wt_encGroup_le gs).trans ?_
  unfold groupW
  have : gs.length + 2 ≤ k ^ 2 + 2 := by omega
  have := Nat.mul_le_mul_right (k + 1) this
  have := Nat.pow_le_pow_left this 2
  omega

theorem IntervalValC.wt_le {e : Ω ≃ Fin k} {v : Val} {I : Interval Ω}
    (h : IntervalValC e v I) : v.wt ≤ intervalW k I := by
  obtain ⟨pv, hp, rfl⟩ := h
  have h1 := wt_list4_le pv (.nat I.ratio) (.nat I.cap) (.nat I.origin)
  have := hp.wt_le
  have := wt_nat_le I.ratio
  have := wt_nat_le I.cap
  have := wt_nat_le I.origin
  unfold intervalW
  omega

theorem HierValC.wt_le {e : Ω ≃ Fin k} {v : Val} {l : List (Interval Ω)}
    (h : HierValC e v l) : v.wt ≤ hierW k l := by
  obtain ⟨vs, rfl, h⟩ := h
  have h1 := wt_list_le vs
  have hlen := h.length_eq
  have hsum : (vs.map Val.wt).sum ≤ (l.map (intervalW k)).sum := by
    clear h1 hlen
    induction h with
    | nil => simp
    | cons hab _ ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add hab.wt_le ih
  unfold hierW
  omega

theorem RowValC.wt_le' {e : Ω ≃ Fin k} {v : Val} {R : RowRecord Ω} (h : RowValC e v R) :
    v.wt ≤ 2 * ((R.m + 2) + partW k + (2 * partW k + 5)) + 7 := by
  obtain ⟨rv, cv, hr, hc, rfl⟩ := h
  have h1 := wt_list3_le (.nat R.m) rv cv
  have := wt_nat_le R.m
  have := hr.wt_le
  have hcv : cv.wt ≤ 2 * partW k + 5 := by
    cases hco : R.cols with
    | none =>
      rw [hco] at hc
      change cv = .list [] at hc
      subst hc
      simp
    | some cols =>
      rw [hco] at hc
      obtain ⟨u, hu, rfl⟩ := hc
      have := wt_list1_le u
      have := hu.wt_le
      omega
  omega

theorem rows_wt_le {e : Ω ≃ Fin k} {v : Val} :
    ∀ {o : Option (RowRecord Ω)}, OptVal (RowValC e) v o → v.wt ≤ rowsW k o
  | none, h => by
    change v = .list [] at h
    subst h
    simp [rowsW]
  | some R, ⟨u, hu, hv⟩ => by
    subst hv
    have := wt_list1_le u
    have := hu.wt_le'
    simp only [rowsW]
    omega

theorem DomVal.wt_le {e : Ω ≃ Fin k} {v : Val} {D : Set Ω} (h : DomVal e v D) :
    v.wt ≤ k * 7 + 4 := by
  classical
  rw [h]
  refine (wt_encFun_le _ (B := 1) fun i => ?_).trans (by omega)
  split_ifs <;> omega

theorem ColorVal.wt_le {e : Ω ≃ Fin k} {c : C → ℕ} {v : Val} {x : Ω → C} (h : ColorVal e c v x)
    (hx : ∀ a, c (x a) < 2 * k) : v.wt ≤ k * (2 * (2 * k) + 5) + 4 := by
  rw [h]
  exact wt_encFun_le _ (B := 2 * k) fun i => (hx _).le

/-- **The weight of a canonical value** is at most `stateW k S`. -/
theorem Canon.wt_le {e : Ω ≃ Fin k} {c : C → ℕ} {v : Val} {S : State Ω C}
    (h : Canon e c v S) : v.wt ≤ stateW k S := by
  obtain ⟨gv, dv, xv, yv, hv, rv, hg, hd, hx, hy, hh, hr, rfl⟩ := h.val
  have h1 := wt_list_le [.nat k, gv, dv, xv, yv, hv, rv, boolVal S.floor, .nat S.h, .nat S.N]
  have e1 := wt_nat_le k
  have e2 := hg.wt_le
  have e3 := DomVal.wt_le hd
  have e4 := ColorVal.wt_le hx fun a => (h.colors a).1
  have e5 := ColorVal.wt_le hy fun a => (h.colors a).2
  have e6 := hh.wt_le
  have e7 := rows_wt_le hr
  have e8 := wt_boolVal_le S.floor
  have e9 := wt_nat_le S.h
  have e10 := wt_nat_le S.N
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at h1
  unfold stateW
  omega

open Classical in
/-- The number of positions is at most the weight of a state value: the domain indicator has
`k` entries. -/
theorem StateVal.k_le_wt {e : Ω ≃ Fin k} {c : C → ℕ} {v : Val} {S : State Ω C}
    (h : StateVal e c v S) : k ≤ v.wt := by
  obtain ⟨gv, dv, xv, yv, hv, rv, -, hd, -, -, -, -, rfl⟩ := h
  have h1 : dv.wt < (Val.list [.nat k, gv, dv, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]).wt := wt_le_wt_list (by simp)
  have h2 : k < dv.wt := by
    rw [hd]
    have := length_lt_wt_list ((List.finRange k).map fun i =>
      Val.nat (if e.symm i ∈ S.dom then 1 else 0))
    simpa [encFun] using this
  omega

/-! ### Canonical answers -/

/-- **A canonical answer value**: `[]` for the empty answer, or `[x, encGroup gs]` with at most
`k²` generators, whose coset is the image of the answer. -/
def AnsC (e : Ω ≃ Fin k) (u : Val) (A : Set (Perm Ω)) : Prop :=
  (u = .list [] ∧ A = ∅) ∨ ∃ (x : Perm (Fin k)) (gs : List (Perm (Fin k))),
    u = .list [encPerm x, encGroup gs] ∧ gs.length ≤ k ^ 2 ∧
      toFin e '' A = x • (gens gs : Set (Perm (Fin k)))

theorem AnsC.answerVal {e : Ω ≃ Fin k} {u : Val} {A : Set (Perm Ω)} (h : AnsC e u A) :
    AnswerVal e u A := by
  rcases h with h | ⟨x, gs, rfl, -, hA⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, gs, rfl, hA⟩

/-- The weight bound of a canonical answer. -/
def ansW (k : ℕ) : ℕ := 2 * (4 * (k + 1) ^ 2 + groupW k) + 6

theorem AnsC.wt_le {e : Ω ≃ Fin k} {u : Val} {A : Set (Perm Ω)} (h : AnsC e u A) :
    u.wt ≤ ansW k := by
  rcases h with ⟨rfl, -⟩ | ⟨x, gs, rfl, hl, -⟩
  · simp [ansW]
  · have h1 := wt_list2_le (encPerm x) (encGroup gs)
    have h2 := wt_encPerm_le x
    have h3 : GroupValC k (encGroup gs) (gens gs) := ⟨gs, rfl, rfl, hl⟩
    have := h3.wt_le
    unfold ansW
    omega

theorem ansW_mono {k k' : ℕ} (h : k ≤ k') : ansW k ≤ ansW k' := by
  unfold ansW groupW
  have h1 : (k + 1) ^ 2 ≤ (k' + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (k ^ 2 + 2) * (k + 1) ≤ (k' ^ 2 + 2) * (k' + 1) :=
    Nat.mul_le_mul (by have := Nat.pow_le_pow_left h 2; omega) (by omega)
  have h3 := Nat.pow_le_pow_left h2 2
  omega

/-- `ansW k ≤ 1000 (k + 1)⁶`. -/
theorem ansW_le (k : ℕ) : ansW k ≤ 1000 * (k + 1) ^ 6 := by
  unfold ansW groupW
  have h1 : (k ^ 2 + 2) * (k + 1) ≤ 2 * (k + 1) ^ 3 := by nlinarith
  have h2 : ((k ^ 2 + 2) * (k + 1)) ^ 2 ≤ 4 * (k + 1) ^ 6 := by
    calc ((k ^ 2 + 2) * (k + 1)) ^ 2 ≤ (2 * (k + 1) ^ 3) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 4 * (k + 1) ^ 6 := by ring
  have h3 : (k + 1) ^ 2 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : 1 ≤ (k + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  omega

end GI.Impl
