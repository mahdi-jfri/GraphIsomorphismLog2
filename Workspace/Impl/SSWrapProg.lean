import Workspace.Impl.SSWrapStart
import Workspace.Lang.Lib.Tabulate

/-!
# The layout of the wrapper programs

Each wrapper is the program `ssWrapProgram extra`: the core `ssFuns 0` (functions `0` to `46`),
then `range` (`47` to `49`), `ssStartF` (`50`) and `ssStSiftF` (`51`), then the wrapper's own
functions from `52` on. This file also proves the facts every bridge needs: the input bound
`Y = 3 (w + 1)` (`ss_wrap_Y`), the cost bound (`ss_wrap_cost`), and the cells of a list input
(`ss_list_cells`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n : ℕ}

/-- The functions shared by the wrappers, at `47` to `51`. -/
def ssCommonFuns : List Expr := rangeFuns 47 ++ [ssStartF 46, ssStSiftF 47 50 25]

/-- The program of a wrapper with its own functions `extra`, from `52` on. -/
def ssWrapProgram (extra : List Expr) : Program := ⟨ssFuns 0 ++ ssCommonFuns ++ extra, []⟩

/-- The shared parts of a wrapper program. -/
structure SsWrapAt (P : Program) : Prop where
  core : SsCoreAt P 0
  range : P.HasAt 47 (rangeFuns 47)
  start : P.funs[50]? = some (ssStartF 46)
  stsift : P.funs[51]? = some (ssStSiftF 47 50 25)

theorem ssWrapAt_of (extra : List Expr) : SsWrapAt (ssWrapProgram extra) := by
  have h := Program.hasAt_append [] (ssFuns 0 ++ ssCommonFuns) extra []
  simp only [List.nil_append, List.length_nil] at h
  have h1 := h.left
  have h2 := h.right
  rw [show 0 + (ssFuns 0).length = 47 from rfl] at h2
  have h3 := h2.right
  rw [show 47 + (rangeFuns 47).length = 50 from rfl] at h3
  exact ⟨SsCoreAt.of_hasAt h1, h2.left, h3.left.single, by simpa using h3 1 (by simp)⟩

theorem ssWrap_extra (extra : List Expr) : (ssWrapProgram extra).HasAt 52 extra := by
  have h := Program.hasAt_append (ssFuns 0 ++ ssCommonFuns) extra [] []
  rw [List.append_nil, show (ssFuns 0 ++ ssCommonFuns).length = 52 from rfl] at h
  exact h

/-- The input bound used by every wrapper. -/
theorem ss_wrap_Y {gs : List (Perm (Fin n))} {vs : List Val} (hv : encGroup gs ∈ vs) :
    n + n + gs.length + 2 ≤ 3 * ((Val.list vs).wt + 1) := by
  have h1 := ss_encGroup_wt gs
  have h2 := wt_le_wt_list hv
  omega

/-- Small numbers are below the cost of the core. -/
theorem ss_le_core {Y : ℕ} (hY : 2 ≤ Y) : Y + 1000 ≤ ssW Y ∧ ssW Y + 1 ≤ ssCoreCost Y := by
  obtain ⟨-, -, -, hY3, hZ⟩ := ss_Y_facts (n := 0) (L := 0) (G := 0) (by omega : 0 + 0 + 0 + 2 ≤ Y)
  have hZW := ssZ_le_ssW Y
  have h4 : ssW Y + 1 ≤ (ssW Y + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  unfold ssCoreCost
  constructor <;> omega

/-- **The cost of a wrapper is polynomial.** -/
theorem ss_wrap_cost {c w : ℕ} (hc : c ≤ 100 * ssCoreCost (3 * (w + 1))) :
    c ≤ 10 * ssPolyK * (w + 1) ^ 32 := by
  have := ss_poly (Y := 3 * (w + 1)) (w := w) (by omega) (by omega)
  unfold ssCoreCost at hc
  rw [Nat.mul_assoc]
  omega

theorem ss_size_le_list {vs : List Val} {v : Val} (hv : v ∈ vs) : v.size ≤ (Val.list vs).size := by
  rw [size_list_eq]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := Val.size) hv)
  omega

/-- The cells of a list input are at most its size plus one, when this holds for the cells of
its entries. -/
theorem ss_list_cells {vs : List Val} (h : ∀ v ∈ vs, ∀ a ∈ v.cells, a ≤ (Val.list vs).size + 1) :
    ∀ a ∈ (Val.list vs).cells, a ≤ 1 * ((Val.list vs).size + 1) ^ 1 := by
  intro a ha
  rw [one_mul, pow_one]
  have hs : (Val.list vs).size = 3 + (Val.cellsList vs).length := by
    rw [size_eq_length, cells_list]; simp; omega
  have hl := length_le_cellsList vs
  rw [cells_list] at ha
  simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | ha
  · omega
  · omega
  · omega
  · obtain ⟨v, hv, ha⟩ := cam_mem_cellsList ha
    exact h v hv a ha

/-- The cells of a group or a permutation are at most the size of a list that holds it, plus
one. -/
theorem ss_encGroup_cells_le {gs : List (Perm (Fin n))} {vs : List Val} (hv : encGroup gs ∈ vs) :
    ∀ a ∈ (encGroup gs).cells, a ≤ (Val.list vs).size + 1 := fun a ha => by
  have := cam_encGroup_cells gs a ha
  have := ss_size_le_list hv
  simp only [one_mul, pow_one] at *
  omega

theorem ss_encPerm_cells_le (x : Perm (Fin n)) {vs : List Val} (hv : encPerm x ∈ vs) :
    ∀ a ∈ (encPerm x).cells, a ≤ (Val.list vs).size + 1 := fun a ha => by
  have := cam_encPerm_cells x a ha
  have := ss_size_le_list hv
  rw [size_encPerm] at this
  omega

end GI.Impl
