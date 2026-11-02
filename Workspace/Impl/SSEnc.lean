import Workspace.Proved.SSBuild
import Workspace.Impl.AggStructDC
import Workspace.Lang.Lib.Perm
import Workspace.Lang.Bridge

/-!
# Values of the Schreier–Sims program, and their sizes

The table, the program and the sifting accumulator as values (`ssEncTab`, `ssEncProg`,
`ssEncAcc`). The weights are bounded through a simpler measure: `SsSmall Z v` says that `v` has
at most `Z` cells and every cell is at most `Z`; then `v.wt ≤ Z * (Z + 1)` (`SsSmall.wt_le`).
Sizes add up along lists (`size_list_eq`), so `SsSmall` is easy to prove for nested values.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n : ℕ}

/-! ### Encodings -/

/-- A slot: `[]` if empty, `[t, k]` if it holds `(t, k)`. -/
def ssEncSlot : SsSlot n → Val
  | none => .list []
  | some e => .list [encPerm e.1, .nat e.2]

def ssEncTab (T : List (SsSlot n)) : Val := .list (T.map ssEncSlot)

def ssEncProg (p : List SlpInstr) : Val := .list (p.map encSlpInstr)

def ssEncSt (st : SsState n) : Val := .list [ssEncTab st.1, ssEncProg st.2]

/-- The accumulator of the sifting loop. -/
def ssEncAcc (a : Perm (Fin n) × List ℕ × ℕ) : Val := .list [encPerm a.1, natList a.2.1, .nat a.2.2]

/-- The base, as a list of numbers. -/
def ssEncB (B : List (Fin n)) : Val := natList (B.map Fin.val)

/-! ### Small values -/

/-- `v` has at most `Z` cells, and every cell is at most `Z`. -/
def SsSmall (Z : ℕ) (v : Val) : Prop := v.size ≤ Z ∧ ∀ a ∈ v.cells, a ≤ Z

theorem SsSmall.wt_le {Z : ℕ} {v : Val} (h : SsSmall Z v) : v.wt ≤ Z * (Z + 1) :=
  (wt_le_of_cells_le h.2).trans (Nat.mul_le_mul_right _ h.1)

theorem SsSmall.mono {Z Z' : ℕ} {v : Val} (h : SsSmall Z v) (hZ : Z ≤ Z') : SsSmall Z' v :=
  ⟨h.1.trans hZ, fun a ha => (h.2 a ha).trans hZ⟩

theorem size_list_eq (vs : List Val) : (Val.list vs).size = (vs.map Val.size).sum + 3 := by
  rw [size_list, length_cellsList]

theorem size_list_le {vs : List Val} {B : ℕ} (h : ∀ v ∈ vs, v.size ≤ B) :
    (Val.list vs).size ≤ vs.length * B + 3 := by
  rw [size_list_eq]
  have := List.sum_le_card_nsmul (vs.map Val.size) B (by
    intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; exact h v hv)
  simp only [List.length_map, smul_eq_mul] at this
  omega

theorem mem_cellsList {vs : List Val} {a : ℕ} (h : a ∈ Val.cellsList vs) :
    ∃ v ∈ vs, a ∈ v.cells := by
  induction vs with
  | nil => simp [Val.cellsList] at h
  | cons v vs ih =>
    simp only [Val.cellsList, List.mem_append] at h
    rcases h with h | h
    · exact ⟨v, by simp, h⟩
    · obtain ⟨w, hw, h⟩ := ih h; exact ⟨w, by simp [hw], h⟩

theorem ssSmall_nat {Z k : ℕ} (hk : k ≤ Z) (hZ : 2 ≤ Z) : SsSmall Z (.nat k) := by
  refine ⟨by simpa using hZ, fun a ha => ?_⟩
  simp only [Val.cells, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> omega

theorem ssSmall_list {Z : ℕ} {vs : List Val} (hs : (Val.list vs).size ≤ Z)
    (h : ∀ v ∈ vs, SsSmall Z v) : SsSmall Z (.list vs) := by
  refine ⟨hs, fun a ha => ?_⟩
  have h2 := length_le_cellsList vs
  have h3 : (Val.list vs).size = (Val.cellsList vs).length + 3 := size_list vs
  simp only [Val.cells, List.cons_append, List.mem_cons, List.nil_append] at ha
  rcases ha with rfl | rfl | rfl | ha
  · omega
  · omega
  · omega
  · obtain ⟨v, hv, ha⟩ := mem_cellsList ha
    exact (h v hv).2 a ha

theorem ssSmall_list_of {Z B : ℕ} {vs : List Val} (hB : ∀ v ∈ vs, v.size ≤ B)
    (h : ∀ v ∈ vs, SsSmall Z v) (hZ : vs.length * B + 3 ≤ Z) : SsSmall Z (.list vs) :=
  ssSmall_list ((size_list_le hB).trans hZ) h

/-! ### Sizes and smallness of the encodings -/

theorem size_encPerm (σ : Perm (Fin n)) : (encPerm σ).size = 2 * n + 3 := by
  rw [encPerm, size_list_eq]
  simp only [List.map_map, Function.comp_def, size_nat]
  simp [List.sum_replicate]; ring

theorem ssSmall_encPerm (σ : Perm (Fin n)) {Z : ℕ} (hZ : 2 * n + 3 ≤ Z) : SsSmall Z (encPerm σ) := by
  refine ssSmall_list (by rw [← encPerm, size_encPerm]; exact hZ) fun v hv => ?_
  simp only [List.mem_map, List.mem_finRange, true_and] at hv
  obtain ⟨i, rfl⟩ := hv
  exact ssSmall_nat (by have := (σ i).isLt; omega) (by omega)

theorem size_natList (l : List ℕ) : (natList l).size = 2 * l.length + 3 := by
  rw [natList, size_list_eq]
  simp only [List.map_map, Function.comp_def, size_nat]
  simp [List.sum_replicate]; ring

theorem ssSmall_natList {l : List ℕ} {Z : ℕ} (hl : ∀ x ∈ l, x ≤ Z) (hZ : 2 * l.length + 3 ≤ Z) :
    SsSmall Z (natList l) := by
  refine ssSmall_list (by rw [← natList, size_natList]; exact hZ) fun v hv => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
  exact ssSmall_nat (hl x hx) (by omega)

theorem size_ssEncSlot_le (s : SsSlot n) : (ssEncSlot s).size ≤ 2 * n + 8 := by
  cases s with
  | none => simp [ssEncSlot, size_list_eq]
  | some e => simp [ssEncSlot, size_list_eq, size_encPerm]

theorem ssSmall_slot {s : SsSlot n} {Z : ℕ} (hs : ∀ e, s = some e → e.2 ≤ Z) (hZ : 2 * n + 8 ≤ Z) :
    SsSmall Z (ssEncSlot s) := by
  cases s with
  | none => exact ssSmall_list (by simp [size_list_eq]; omega) (by simp)
  | some e =>
    refine ssSmall_list (by have := size_ssEncSlot_le (some e); simp only [ssEncSlot] at this; omega)
      fun v hv => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ssSmall_encPerm _ (by omega)
    · exact ssSmall_nat (hs e rfl) (by omega)

theorem ssSmall_tab {T : List (SsSlot n)} {Z : ℕ} (hs : ∀ s ∈ T, ∀ e, s = some e → e.2 ≤ Z)
    (hZ : T.length * (2 * n + 8) + 3 ≤ Z) (hZ' : 2 * n + 8 ≤ Z) : SsSmall Z (ssEncTab T) := by
  refine ssSmall_list_of (B := 2 * n + 8) (fun v hv => ?_) (fun v hv => ?_) (by simpa using hZ)
  · obtain ⟨s, -, rfl⟩ := List.mem_map.mp hv; exact size_ssEncSlot_le s
  · obtain ⟨s, hs', rfl⟩ := List.mem_map.mp hv
    exact ssSmall_slot (hs s hs') hZ'

theorem size_encSlpInstr_le (ins : SlpInstr) : (encSlpInstr ins).size ≤ 9 := by
  cases ins <;> simp [encSlpInstr, size_list_eq]

/-- The numbers of an instruction. -/
def ssInsMax : SlpInstr → ℕ
  | .gen i => i
  | .inv j => j
  | .mul j k => max j k

theorem ssSmall_instr {ins : SlpInstr} {Z : ℕ} (h : ssInsMax ins ≤ Z) (hZ : 9 ≤ Z) :
    SsSmall Z (encSlpInstr ins) := by
  have hs := size_encSlpInstr_le ins
  cases ins <;> simp only [encSlpInstr, ssInsMax] at hs h ⊢ <;> refine ssSmall_list (by omega) fun v hv => ?_ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  · rcases hv with rfl | rfl <;> exact ssSmall_nat (by omega) (by omega)
  · rcases hv with rfl | rfl <;> exact ssSmall_nat (by omega) (by omega)
  · rcases hv with rfl | rfl | rfl <;> exact ssSmall_nat (by omega) (by omega)

theorem ssSmall_prog {p : List SlpInstr} {Z : ℕ} (h : ∀ ins ∈ p, ssInsMax ins ≤ Z)
    (hZ : p.length * 9 + 3 ≤ Z) (hZ' : 9 ≤ Z) : SsSmall Z (ssEncProg p) := by
  refine ssSmall_list_of (B := 9) (fun v hv => ?_) (fun v hv => ?_) (by simpa using hZ)
  · obtain ⟨s, -, rfl⟩ := List.mem_map.mp hv; exact size_encSlpInstr_le s
  · obtain ⟨s, hs', rfl⟩ := List.mem_map.mp hv
    exact ssSmall_instr (h s hs') hZ'

end GI.Impl
