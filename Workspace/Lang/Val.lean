/-
Basic facts about the value format `GI.Cited.Val` of `Workspace.Cited.Encoding`.

* `Val.size v` is the number of cells of `v`, and `Val.wt v` is its weight: the sum over its
  cells of one plus the bit length of the cell. The language of `Workspace.Lang.Syntax` charges
  the weight of every value it builds, and copying a value on the machine costs about its weight.
* The cells of a list split into the header and the cells of the entries
  (`ValAt.list_iff`, `ValsAt.cons_iff`), so a program can walk through a list.
* The cells determine the value (`ValAt.unique`).
* `encPerm` and `encPerms` are injective.
-/
import Workspace.Machine.Layout
import Workspace.Cited.Encoding

namespace GI.Lang

open GI.Machine GI.Cited

/-! ### Cells -/

@[simp] theorem cells_nat (n : ℕ) : (Val.nat n).cells = [0, n] := by
  simp [Val.cells]

@[simp] theorem cells_list (vs : List Val) :
    (Val.list vs).cells = [1, vs.length, (Val.cellsList vs).length] ++ Val.cellsList vs := by
  simp [Val.cells]

@[simp] theorem cellsList_nil : Val.cellsList [] = [] := by simp [Val.cellsList]

@[simp] theorem cellsList_cons (v : Val) (vs : List Val) :
    Val.cellsList (v :: vs) = v.cells ++ Val.cellsList vs := by simp [Val.cellsList]

@[simp] theorem cellsList_append (vs ws : List Val) :
    Val.cellsList (vs ++ ws) = Val.cellsList vs ++ Val.cellsList ws := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp [ih]

/-- The number of cells of a value. -/
def _root_.GI.Cited.Val.size (v : Val) : ℕ := v.cells.length

theorem size_eq_length (v : Val) : v.size = v.cells.length := rfl

/-- The weight of a list of numbers: the sum of `len x + 1` over its entries. -/
def cellWt (l : List ℕ) : ℕ := (l.map fun x => len x + 1).sum

@[simp] theorem cellWt_nil : cellWt [] = 0 := rfl
@[simp] theorem cellWt_cons (x : ℕ) (l : List ℕ) : cellWt (x :: l) = len x + 1 + cellWt l := by
  simp [cellWt]
@[simp] theorem cellWt_append (l l' : List ℕ) : cellWt (l ++ l') = cellWt l + cellWt l' := by
  simp [cellWt]

theorem length_le_cellWt (l : List ℕ) : l.length ≤ cellWt l := by
  induction l with
  | nil => simp
  | cons x l ih => simp; omega

theorem len_le_cellWt {l : List ℕ} {x : ℕ} (hx : x ∈ l) : len x < cellWt l := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp; omega
    · have := ih hx; simp; omega

/-- The weight of a value: one plus the bit length of each of its cells, summed. -/
def _root_.GI.Cited.Val.wt (v : Val) : ℕ := cellWt v.cells

theorem _root_.GI.Cited.Val.size_le_wt (v : Val) : v.size ≤ v.wt := length_le_cellWt _

theorem _root_.GI.Cited.Val.len_lt_wt {v : Val} {x : ℕ} (hx : x ∈ v.cells) : len x < v.wt := len_le_cellWt hx

/-- Every cell of `v` is below `2 ^ wt v`. -/
theorem _root_.GI.Cited.Val.lt_two_pow_wt {v : Val} {x : ℕ} (hx : x ∈ v.cells) : x < 2 ^ v.wt :=
  len_le_iff.mp (Val.len_lt_wt hx).le

@[simp] theorem size_nat (n : ℕ) : (Val.nat n).size = 2 := by simp [size_eq_length]

theorem size_list (vs : List Val) :
    (Val.list vs).size = (Val.cellsList vs).length + 3 := by simp [size_eq_length]

theorem wt_nat (n : ℕ) : (Val.nat n).wt = len n + 2 := by
  show cellWt (Val.nat n).cells = _
  simp [len_zero]; omega

theorem _root_.GI.Cited.Val.two_le_size (v : Val) : 2 ≤ v.size := by
  cases v <;> simp [size_eq_length]

/-- The number of entries of a list is at most its number of cells. -/
theorem length_le_cellsList (vs : List Val) : 2 * vs.length ≤ (Val.cellsList vs).length := by
  induction vs with
  | nil => simp
  | cons v vs ih => have := v.two_le_size; simp [size_eq_length] at *; omega

/-- The bit length of the length of a list, and of the cell count `S`, are paid for in the
weight. -/
theorem wt_list (vs : List Val) :
    (Val.list vs).wt = 2 + (len vs.length + 1) + (len (Val.cellsList vs).length + 1) +
      cellWt (Val.cellsList vs) := by
  simp [Val.wt, len_one]; omega

/-! ### Values in memory -/

/-- The memory holds the values `vs`, one after another, from address `b`. -/
def ValsAt (mem : ℕ → ℕ) (b : ℕ) (vs : List Val) : Prop := BlockAt mem b (Val.cellsList vs)

theorem valAt_iff_blockAt {mem : ℕ → ℕ} {b : ℕ} {v : Val} : ValAt mem b v ↔ BlockAt mem b v.cells :=
  Iff.rfl

theorem blockAt_append {mem : ℕ → ℕ} {b : ℕ} {l l' : List ℕ} :
    BlockAt mem b (l ++ l') ↔ BlockAt mem b l ∧ BlockAt mem (b + l.length) l' := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by simp; omega)
      rw [this, List.getElem_append_left hi]
    · have := h (l.length + i) (by simp; omega)
      rw [← Nat.add_assoc] at this
      rw [this, List.getElem_append_right (by omega)]
      simp
  · rintro ⟨h1, h2⟩ i hi
    by_cases hil : i < l.length
    · rw [h1 i hil, List.getElem_append_left hil]
    · have := h2 (i - l.length) (by simp at hi; omega)
      rw [show b + l.length + (i - l.length) = b + i by omega] at this
      rw [this, List.getElem_append_right (by omega)]

@[simp] theorem blockAt_nil {mem : ℕ → ℕ} {b : ℕ} : BlockAt mem b [] ↔ True :=
  ⟨fun _ => trivial, fun _ _ hi => absurd hi (Nat.not_lt_zero _)⟩

theorem blockAt_cons {mem : ℕ → ℕ} {b x : ℕ} {l : List ℕ} :
    BlockAt mem b (x :: l) ↔ mem b = x ∧ BlockAt mem (b + 1) l := by
  rw [show x :: l = [x] ++ l from rfl, blockAt_append]
  simp only [List.length_singleton]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by simpa using h1 0 (by simp), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => by
      have : i = 0 := by simp at hi; omega
      subst this; simpa using h1, h2⟩

theorem _root_.GI.Cited.ValAt.nat_iff {mem : ℕ → ℕ} {b n : ℕ} :
    ValAt mem b (.nat n) ↔ mem b = 0 ∧ mem (b + 1) = n := by
  rw [valAt_iff_blockAt, cells_nat, blockAt_cons, blockAt_cons]
  simp

theorem _root_.GI.Cited.ValAt.list_iff {mem : ℕ → ℕ} {b : ℕ} {vs : List Val} :
    ValAt mem b (.list vs) ↔ mem b = 1 ∧ mem (b + 1) = vs.length ∧
      mem (b + 2) = (Val.cellsList vs).length ∧ ValsAt mem (b + 3) vs := by
  rw [valAt_iff_blockAt, cells_list, blockAt_append, blockAt_cons, blockAt_cons, blockAt_cons]
  simp [ValsAt, Nat.add_assoc, and_assoc]

@[simp] theorem ValsAt.nil_iff {mem : ℕ → ℕ} {b : ℕ} : ValsAt mem b [] ↔ True := by
  simp [ValsAt]

theorem ValsAt.cons_iff {mem : ℕ → ℕ} {b : ℕ} {v : Val} {vs : List Val} :
    ValsAt mem b (v :: vs) ↔ ValAt mem b v ∧ ValsAt mem (b + v.size) vs := by
  rw [ValsAt, cellsList_cons, blockAt_append]; rfl

theorem ValsAt.append_iff {mem : ℕ → ℕ} {b : ℕ} {vs ws : List Val} :
    ValsAt mem b (vs ++ ws) ↔
      ValsAt mem b vs ∧ ValsAt mem (b + (Val.cellsList vs).length) ws := by
  rw [ValsAt, cellsList_append, blockAt_append]; rfl

/-- Entry `k` of a list stored at `b` starts after the header and the first `k` entries. -/
theorem ValsAt.get {mem : ℕ → ℕ} {b : ℕ} {vs : List Val} (h : ValsAt mem b vs) (k : ℕ)
    (hk : k < vs.length) :
    ValAt mem (b + (Val.cellsList (vs.take k)).length) vs[k] := by
  have e : vs = vs.take k ++ vs[k] :: vs.drop (k + 1) := by simp
  rw [e, ValsAt.append_iff, ValsAt.cons_iff] at h
  have : (vs.take k ++ vs[k] :: vs.drop (k + 1))[k]'(by simp; omega) = vs[k] := by
    simp
  exact h.2.1

/-- A value held in memory depends only on its own cells. -/
theorem _root_.GI.Cited.ValAt.congr {mem mem' : ℕ → ℕ} {b : ℕ} {v : Val} (h : ValAt mem b v)
    (hm : ∀ x, b ≤ x → x < b + v.size → mem' x = mem x) : ValAt mem' b v :=
  BlockAt.congr h hm

theorem ValsAt.congr {mem mem' : ℕ → ℕ} {b : ℕ} {vs : List Val} (h : ValsAt mem b vs)
    (hm : ∀ x, b ≤ x → x < b + (Val.cellsList vs).length → mem' x = mem x) :
    ValsAt mem' b vs :=
  BlockAt.congr h hm

/-- A cell of a value held in memory is a cell of the value. -/
theorem _root_.GI.Cited.ValAt.mem_cells {mem : ℕ → ℕ} {b : ℕ} {v : Val} (h : ValAt mem b v) {i : ℕ}
    (hi : i < v.size) : mem (b + i) ∈ v.cells := by
  rw [h i hi]; exact List.getElem_mem hi

/-- The size of a value held in memory, read from its first cells: 2 for a number, and three
plus the count in its third cell for a list. -/
theorem _root_.GI.Cited.ValAt.size_eq {mem : ℕ → ℕ} {b : ℕ} {v : Val} (h : ValAt mem b v) :
    v.size = if mem b = 0 then 2 else mem (b + 2) + 3 := by
  cases v with
  | nat n => rw [ValAt.nat_iff] at h; simp [h.1]
  | list vs =>
    rw [ValAt.list_iff] at h
    rw [size_list, h.1, h.2.2.1]; simp

/-! ### The cells determine the value -/

mutual
theorem ValAt.unique_aux {mem : ℕ → ℕ} : ∀ (v w : Val) (b : ℕ), ValAt mem b v → ValAt mem b w → v = w
  | .nat n, .nat m, b, h1, h2 => by
    rw [ValAt.nat_iff] at h1 h2; rw [← h1.2, ← h2.2]
  | .nat n, .list ws, b, h1, h2 => by
    rw [ValAt.nat_iff] at h1; rw [ValAt.list_iff] at h2; omega
  | .list vs, .nat m, b, h1, h2 => by
    rw [ValAt.nat_iff] at h2; rw [ValAt.list_iff] at h1; omega
  | .list vs, .list ws, b, h1, h2 => by
    rw [ValAt.list_iff] at h1 h2
    rw [ValsAt.unique_aux vs ws (b + 3) (by omega) h1.2.2.2 h2.2.2.2]
theorem ValsAt.unique_aux {mem : ℕ → ℕ} : ∀ (vs ws : List Val) (b : ℕ), vs.length = ws.length →
    ValsAt mem b vs → ValsAt mem b ws → vs = ws
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | v :: vs, w :: ws, b, hl, h1, h2 => by
    rw [ValsAt.cons_iff] at h1 h2
    have hvw := ValAt.unique_aux v w b h1.1 h2.1
    subst hvw
    rw [ValsAt.unique_aux vs ws (b + v.size) (by simpa using hl) h1.2 h2.2]
end

/-- The cells determine the value. -/
theorem _root_.GI.Cited.ValAt.unique {mem : ℕ → ℕ} {b : ℕ} {v w : Val} (h1 : ValAt mem b v)
    (h2 : ValAt mem b w) : v = w :=
  GI.Lang.ValAt.unique_aux v w b h1 h2

/-- A value stored at `b` is a copy of any value whose cells it repeats. -/
theorem valAt_of_cells {mem : ℕ → ℕ} {b : ℕ} {v : Val} {l : List ℕ} (hv : v.cells = l)
    (h : BlockAt mem b l) : ValAt mem b v := by rw [valAt_iff_blockAt, hv]; exact h

/-- The cells of a value determine it, as lists. -/
theorem _root_.GI.Cited.Val.cells_injective : Function.Injective Val.cells := by
  intro v w h
  have hv : ValAt (fun i => v.cells.getD i 0) 0 v := fun i hi => by
    simp only [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  have hw : ValAt (fun i => v.cells.getD i 0) 0 w := fun i hi => by
    simp only [Nat.zero_add, h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  exact ValAt.unique hv hw

/-! ### Permutations -/

theorem encPerm_injective {n : ℕ} : Function.Injective (encPerm (n := n)) := by
  intro σ τ h
  simp only [encPerm, Val.list.injEq] at h
  rw [List.map_inj_left] at h
  ext i
  have := h i (List.mem_finRange i)
  simp only [Val.nat.injEq] at this
  rw [this]

theorem encPerms_injective {n : ℕ} : Function.Injective (encPerms (n := n)) := by
  intro gs hs h
  simp only [encPerms, Val.list.injEq, List.cons.injEq, true_and, and_true] at h
  exact (List.map_injective_iff.mpr encPerm_injective) h

end GI.Lang
