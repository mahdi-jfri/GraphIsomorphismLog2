module

public import Workspace.Lang.Prims.LinMembership
public import Workspace.Impl.LinGroupSlp
public import Workspace.Impl.GenNormPoly
public import Workspace.Impl.Lift
public import Workspace.Impl.CamCells
public import Workspace.Lang.Lib.Tabulate
public import Workspace.Impl.LinIntSolverCost

@[expose] public section

/-!
# Small helpers for the programs of `NIntFac` and `NIntInter`

`append` and `replicate` with costs that depend only on the weight of the argument, the
monotonicity of the cost of the straight-line program evaluator, and the cell bound of
`polyTimeAt_ofVal_of_lang_cells` for lists of values.
-/

namespace GI.Impl

open GI.Cited GI.Lang

theorem nint_wt_append (xs ys : List Val) :
    (Val.list (xs ++ ys)).wt ≤ 3 * ((Val.list xs).wt + (Val.list ys).wt) + 4 := by
  have h1 := wt_list_le (xs ++ ys)
  have h2 := sum_wt_lt_wt_list xs
  have h3 := sum_wt_lt_wt_list ys
  have h4 := length_lt_wt_list xs
  have h5 := length_lt_wt_list ys
  simp only [List.map_append, List.sum_append, List.length_append] at h1
  omega

/-- The weight of `[.list xs, .list ys]` bounds the weights of `xs` and `ys` together. -/
theorem nint_wt_pair (a b : Val) : a.wt + b.wt < (Val.list [a, b]).wt := by
  have := sum_wt_lt_wt_list [a, b]
  simp at this
  omega

/-- **Append**, with a cost in terms of the weight `W` of the argument. -/
theorem nint_append {P : Program} {b : ℕ} (h : P.HasAt b (appendFuns b)) (xs ys : List Val) :
    FunDet P b (.list [.list xs, .list ys]) (.list (xs ++ ys))
      (5000 * ((Val.list [.list xs, .list ys]).wt + 1) ^ 2) := by
  refine (append_spec h xs ys).mono fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
  subst hw
  set W := (Val.list [.list xs, .list ys]).wt
  have h1 := nint_wt_append xs ys
  have h2 := nint_wt_pair (.list xs) (.list ys)
  have h3 := length_lt_wt_list ys
  have h4 : loopModK * (ys.length + 1) * (W + ys.length + (Val.list (xs ++ ys)).wt + 1) ≤
      1000 * (W + 1) * (5 * (W + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e : 1000 * (W + 1) * (5 * (W + 1)) = 5000 * (W + 1) ^ 2 := by ring
  omega

/-- **Replicate**, with a cost in terms of `k` and the weight of the argument. -/
theorem nint_replicate {P : Program} {b : ℕ} (h : P.HasAt b (replicateFuns b)) (k : ℕ) (v : Val) :
    FunDet P b (.list [.nat k, v]) (.list (List.replicate k v))
      (7000 * ((Val.list [.nat k, v]).wt + k + 1) ^ 3) := by
  refine (replicate_spec h k v).mono fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
  subst hw
  obtain ⟨A, hA⟩ : ∃ A, (Val.list [.nat k, v]).wt = A := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, (Val.list (List.replicate k v)).wt = R := ⟨_, rfl⟩
  rw [hA, hR] at hc; rw [hA]
  have h2 := nint_wt_pair (.nat k) v
  rw [hA] at h2
  have h1 := wt_list_le (List.replicate k v)
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul, List.length_replicate, hR] at h1
  have h5 : k * v.wt ≤ (A + k) * (A + k) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : (A + k + 1) ^ 2 = (A + k) * (A + k) + 2 * (A + k) + 1 := by ring
  have h6 : A + k + R + 1 ≤ 7 * (A + k + 1) ^ 2 := by omega
  have h4 : loopModK * (k + 1) * (A + k + R + 1) ≤ 1000 * (A + k + 1) * (7 * (A + k + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) h6
  have e : 1000 * (A + k + 1) * (7 * (A + k + 1) ^ 2) = 7000 * (A + k + 1) ^ 3 := by ring
  omega

theorem nint_slpCost_mono {W W' L L' B B' C C' : ℕ} (hW : W ≤ W') (hL : L ≤ L') (hB : B ≤ B')
    (hC : C ≤ C') : linGroupSlpCost W L B C ≤ linGroupSlpCost W' L' B' C' := by
  unfold linGroupSlpCost linGroupSlpLoopCost linGroupSlpLoopStepCost linGroupSlpStepCost
    linGroupSlpArg linVectorAccWt
  gcongr

/-- `(W + 1)^k ≤ c^k Y^k` when `W + 1 ≤ c Y`. -/
theorem nint_pow_le {W c Y : ℕ} (h : W + 1 ≤ c * Y) (k : ℕ) : (W + 1) ^ k ≤ c ^ k * Y ^ k := by
  rw [← mul_pow]; exact Nat.pow_le_pow_left h k

theorem nint_pow_mono {Y : ℕ} (hY : 1 ≤ Y) {i j : ℕ} (h : i ≤ j) : Y ^ i ≤ Y ^ j :=
  Nat.pow_le_pow_right hY h

/-! ### Cells -/

/-- Values whose cells are at most their size plus one. -/
def NIntCells (v : Val) : Prop := ∀ a ∈ v.cells, a ≤ v.size + 1

theorem nint_cells_list {vs : List Val} (h : ∀ v ∈ vs, NIntCells v) : NIntCells (.list vs) := by
  intro a ha
  rw [size_eq_length]
  simp only [cells_list, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, List.mem_cons] at ha ⊢
  have hlen := length_le_cellsList vs
  rcases ha with rfl | rfl | rfl | ha
  · omega
  · omega
  · omega
  · obtain ⟨v, hv, ha⟩ := cam_mem_cellsList ha
    have h1 := h v hv a ha
    have h2 : v.size ≤ (Val.cellsList vs).length := by
      rw [length_cellsList]
      exact List.le_sum_of_mem (List.mem_map_of_mem hv)
    omega

theorem nint_cells_group {n : ℕ} (gs : List (Equiv.Perm (Fin n))) : NIntCells (encGroup gs) := by
  intro a ha
  simpa using cam_encGroup_cells gs a ha

theorem nint_cells_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) : NIntCells (encPerm σ) := by
  intro a ha
  have := cam_encPerm_cells σ a ha
  have := cam_encPerm_size σ
  rw [size_eq_length]
  omega

end GI.Impl
