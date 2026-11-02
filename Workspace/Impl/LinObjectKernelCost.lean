import Workspace.Impl.LinObjectKernel
import Workspace.Impl.LinObjectEvalBound

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectKernelAccWt (n : ℕ) : ℕ := 320 * (n + 1) ^ 6
def linObjectKernelReadWt (n W : ℕ) : ℕ := 100 * (W + linObjectKernelAccWt n + 1) ^ 2
def linObjectKernelPrimArg (n : ℕ) : ℕ := 10000 * (n + 1) ^ 6
noncomputable def linObjectKernelPrimBudget (hs : SolvableCosetIntersection) (n : ℕ) : ℕ :=
  (solvableCosetIntersectionPrim hs).boundSize (linObjectKernelPrimArg n)
noncomputable def linObjectKernelStepCost (hs : SolvableCosetIntersection) (n W : ℕ) : ℕ :=
  100000000 * (linObjectKernelReadWt n W + linObjectKernelPrimBudget hs n + 8 * mkGroupK * (n + 1) ^ 9 + 1) ^ 2
noncomputable def linObjectKernelCost (hs : SolvableCosetIntersection) (n W : ℕ) : ℕ :=
  100000000 * (W + 1) * (W + linObjectKernelAccWt n + linObjectKernelStepCost hs n W + 1) ^ 2

theorem linObjectKernelStepCost_poly (hs : SolvableCosetIntersection) :
    PBU (fun n W _ => linObjectKernelStepCost hs n W) := by
  unfold linObjectKernelStepCost linObjectKernelReadWt linObjectKernelAccWt linObjectKernelPrimBudget
    linObjectKernelPrimArg Prim.boundSize
  norm_poly

theorem linObjectKernelCost_poly (hs : SolvableCosetIntersection) : PBU (fun n W _ => linObjectKernelCost hs n W) := by
  unfold linObjectKernelCost linObjectKernelStepCost linObjectKernelReadWt linObjectKernelAccWt
    linObjectKernelPrimBudget linObjectKernelPrimArg Prim.boundSize
  norm_poly

theorem linObjectKernel_prim_wt {n : ℕ} {G K : Subgroup (Equiv.Perm (Fin n))} {gv kv : Val}
    (hg : GroupValC n gv G) (hk : GroupValC n kv K) :
    (Val.list [gv,kv,encPerm (1 : Equiv.Perm (Fin n))]).wt ≤ linObjectKernelPrimArg n := by
  have wg : gv.wt ≤ 320 * (n + 1) ^ 6 := by
    obtain ⟨gs,rfl,hgen,hlen⟩ := hg
    exact wt_encGroup_le_sq hlen
  have wk : kv.wt ≤ 320 * (n + 1) ^ 6 := by
    obtain ⟨ks,rfl,hgen,hlen⟩ := hk
    exact wt_encGroup_le_sq hlen
  have wi := wt_encPerm_le (1 : Equiv.Perm (Fin n))
  have hw := wt_list3_le gv kv (encPerm (1 : Equiv.Perm (Fin n)))
  have hp : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpos : 0 < (n + 1) ^ 6 := pow_pos (Nat.succ_pos n) 6
  unfold linObjectKernelPrimArg
  omega

theorem linObjectKernel_prim_bound (hs : SolvableCosetIntersection)
    {n : ℕ} {G K : Subgroup (Equiv.Perm (Fin n))} {gv kv : Val}
    (hg : GroupValC n gv G) (hk : GroupValC n kv K) :
    (solvableCosetIntersectionPrim hs).bound (.list [gv,kv,encPerm (1 : Equiv.Perm (Fin n))]) ≤
      linObjectKernelPrimBudget hs n :=
  Prim.bound_le _ (linObjectKernel_prim_wt hg hk)

theorem linObjectKernel_acc_wt {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))} {v : Val}
    (h : GroupValC n v G) : v.wt ≤ linObjectKernelAccWt n := by
  obtain ⟨gs,rfl,hg,hl⟩ := h
  exact wt_encGroup_le_sq hl

theorem linObjectKernel_read_bounds (n W : ℕ) :
    100 ≤ linObjectKernelReadWt n W ∧ W ≤ linObjectKernelReadWt n W ∧
      linObjectKernelAccWt n ≤ linObjectKernelReadWt n W := by
  have hp : W + linObjectKernelAccWt n + 1 ≤ (W + linObjectKernelAccWt n + 1) ^ 2 :=
    Nat.le_self_pow (by decide) _
  unfold linObjectKernelReadWt
  omega

theorem linObjectKernel_get_budget (T b : ℕ) (hb : b ≤ T) :
    linObjectEvalAtom T + linObjectEvalAtom T + b + 1 ≤ 2 * linObjectEvalAtom (T + 1) := by
  unfold linObjectEvalAtom
  nlinarith

theorem linObjectKernel_read_budget (T : ℕ) : linObjectEvalAtom T ≤ 2 * linObjectEvalAtom (T + 1) := by
  have hp : (T + 2) ^ 2 ≤ (T + 1 + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  unfold linObjectEvalAtom
  omega

theorem linObjectKernel_pack_bound (T PB G : ℕ) :
    2 * (100000 * (T + 3) ^ 2) + PB + G + 3 * T + 3 ≤ 100000000 * (T + PB + G + 1) ^ 2 := by
  let S := T + PB + G + 1
  have hs : S ≤ S ^ 2 := Nat.le_self_pow (by decide) _
  have hh : T + 3 ≤ 3 * S := by omega
  have hp := Nat.pow_le_pow_left hh 2
  have he : (3 * S) ^ 2 = 9 * S ^ 2 := by ring
  rw [he] at hp
  change _ ≤ 100000000 * S ^ 2
  omega

theorem linObjectKernel_loop_collect (W M D k : ℕ) (hk : k ≤ W) :
    k * D + loopModK * (k + 1) * (W + k + M + 1) ≤
      100000000 * (W + 1) * (W + M + D + 1) ^ 2 := by
  let S := W + M + D + 1
  have hs : S ≤ S ^ 2 := Nat.le_self_pow (by decide) _
  have hd : k * D ≤ (W + 1) * D := Nat.mul_le_mul_right D (by omega)
  have hl : loopModK * (k + 1) * (W + k + M + 1) ≤ loopModK * (W + 1) * (2 * W + M + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hb : D + loopModK * (2 * W + M + 1) ≤ 100000000 * S ^ 2 := by
    unfold loopModK
    omega
  calc
    _ ≤ (W + 1) * D + loopModK * (W + 1) * (2 * W + M + 1) := Nat.add_le_add hd hl
    _ = (W + 1) * (D + loopModK * (2 * W + M + 1)) := by ring
    _ ≤ (W + 1) * (100000000 * S ^ 2) := Nat.mul_le_mul_left _ hb
    _ = _ := by ring

theorem linObjectKernel_root_wt (input acc : Val) (i W M : ℕ)
    (hw : input.wt ≤ W) (ha : acc.wt ≤ M) (hi : i ≤ W) :
    (Val.list [input,.nat i,acc]).wt ≤ 100 * (W + M + 1) ^ 2 := by
  have hroot := wt_list3_le input (.nat i) acc
  have hn := wt_nat_le i
  have hp : W + M + 1 ≤ (W + M + 1) ^ 2 := Nat.le_self_pow (by decide) _
  omega

end GI.Impl
