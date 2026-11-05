module

public import Workspace.Impl.SSCore
public import Workspace.Impl.CamCells
public import Workspace.Proved.SSWrapMath

@[expose] public section

/-!
# Common facts for the four wrappers

The costs of the core are polynomial in the input weight (`ss_poly`), the group encoding is
small (`ss_encGroup_small`), and the base `[0, …, n-1]` is the list `range n`
(`ssEncB_finRange`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n : ℕ}

/-- The constant of the polynomial bound. -/
def ssPolyK : ℕ := 10 ^ 9 * (3 * 10 ^ 6) ^ 4 * 4 ^ 32

theorem ssW_le_pow {Y : ℕ} (hY : 1 ≤ Y) : ssW Y + 1 ≤ 3 * 10 ^ 6 * Y ^ 8 := by
  unfold ssW ssZ
  have h1 : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ hY
  have e : Y ^ 8 = Y ^ 4 * Y ^ 4 := by ring
  rw [e]
  generalize Y ^ 4 = Q at *
  nlinarith

/-- **The costs are polynomial.** -/
theorem ss_poly {Y w : ℕ} (h1 : 1 ≤ Y) (hY : Y ≤ 4 * (w + 1)) :
    10 * (10 ^ 8 * (ssW Y + 1) ^ 4) ≤ ssPolyK * (w + 1) ^ 32 := by
  have a := ssW_le_pow h1
  have b : (ssW Y + 1) ^ 4 ≤ (3 * 10 ^ 6 * Y ^ 8) ^ 4 := Nat.pow_le_pow_left a 4
  have c : Y ^ 32 ≤ (4 * (w + 1)) ^ 32 := Nat.pow_le_pow_left hY 32
  have e1 : (3 * 10 ^ 6 * Y ^ 8) ^ 4 = (3 * 10 ^ 6) ^ 4 * Y ^ 32 := by ring
  have e2 : (4 * (w + 1)) ^ 32 = 4 ^ 32 * (w + 1) ^ 32 := by ring
  rw [e1] at b
  rw [e2] at c
  calc 10 * (10 ^ 8 * (ssW Y + 1) ^ 4) ≤ 10 * (10 ^ 8 * ((3 * 10 ^ 6) ^ 4 * Y ^ 32)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ b)
    _ ≤ 10 * (10 ^ 8 * ((3 * 10 ^ 6) ^ 4 * (4 ^ 32 * (w + 1) ^ 32))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ c))
    _ = ssPolyK * (w + 1) ^ 32 := by unfold ssPolyK; ring

theorem ssEncB_finRange : ssEncB (List.finRange n) = natList (List.range n) := by
  unfold ssEncB; rw [List.map_coe_finRange_eq_range]

theorem ssCtx_finRange (gs : List (Perm (Fin n))) :
    ssCtx (List.finRange n) gs =
      .list [.nat n, natList (List.range n), .list ((1 :: gs).map encPerm), .nat (n * n)] := by
  unfold ssCtx; rw [ssEncB_finRange, List.length_finRange]

theorem ss_encGroup_small {gs : List (Perm (Fin n))} {Y : ℕ} {L : ℕ}
    (hY : n + L + gs.length + 2 ≤ Y) : SsSmall (ssZ Y) (encGroup gs) := by
  obtain ⟨-, -, hG, hY3, hZ⟩ := ss_Y_facts hY
  have hgs : (Val.list ((1 :: gs).map encPerm)).size ≤ (gs.length + 1) * (2 * n + 3) + 3 := by
    refine (size_list_le (B := 2 * n + 3) fun v hv => ?_).trans (by simp)
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hv; rw [size_encPerm]
  have hgs' : (Val.list (encPerm 1 :: gs.map encPerm)).size ≤ (gs.length + 1) * (2 * n + 3) + 3 :=
    hgs
  have hP : SsSmall (ssZ Y) (.list ((1 :: gs).map encPerm)) := by
    refine ssSmall_list (by omega) fun v hv => ?_
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hv
    exact ssSmall_encPerm σ (by omega)
  refine ssSmall_list ?_ fun v hv => ?_
  · show (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).size ≤ _
    rw [size_list_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, size_nat]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ssSmall_nat (by omega) (by omega)
    · exact hP

/-- The degree and the number of generators are below the weight of the group. -/
theorem ss_encGroup_wt (gs : List (Perm (Fin n))) :
    n < (encGroup gs).wt ∧ gs.length + 1 < (encGroup gs).wt := by
  have h1 : (Val.nat n).wt < (encGroup gs).wt := wt_le_wt_list (by simp [encGroup, encPerms])
  have h2 : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (by simp [encGroup, encPerms])
  have h3 := length_lt_wt_list ((1 :: gs).map encPerm)
  have h5 : (encPerm (1 : Perm (Fin n))).wt < (Val.list ((1 :: gs).map encPerm)).wt :=
    wt_le_wt_list (by simp)
  have h6 := length_lt_wt_list ((List.finRange n).map fun i => Val.nat ((1 : Perm (Fin n)) i))
  have h7 : (encPerm (1 : Perm (Fin n))).wt =
      (Val.list ((List.finRange n).map fun i => Val.nat ((1 : Perm (Fin n)) i))).wt := rfl
  simp only [List.length_map, List.length_cons, List.length_finRange] at h3 h6
  omega

end GI.Impl
