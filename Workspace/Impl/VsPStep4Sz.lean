module

public import Workspace.Impl.VsPCtxP

@[expose] public section

/-!
# The sizes of step 4

At `N = vsPN S = 4 S²` and `W = vsPW6 S = 10^9 S^6`, the orbit data of step 4 satisfies `VsPOD`
(`vsPOD_of`): the context, the generators `gs` of `N₂`, the powers `Zp` of `ζ`, the generators of
`H`, `cap = F = D² + 1` and `r ≤ n`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The weight bound of step 4. -/
def vsPW6 (S : ℕ) : ℕ := 10 ^ 9 * S ^ 6

theorem VsPCtxOK.mono_W {N W W' : ℕ} {ws' cs : List (List ℕ)} {rows : List VsRow}
    {hs : List (Perm (Fin I.n))} (h : VsPCtxOK I N W ws' cs rows hs) (hW : W ≤ W') :
    VsPCtxOK I N W' ws' cs rows hs :=
  ⟨h.sz, h.gam, h.n, h.fr, h.dd, h.rf, h.rl, h.cw.trans hW⟩

set_option maxHeartbeats 4000000 in
/-- **The orbit data of step 4.** -/
theorem vsPOD_of {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {Lb : List (List (List ℕ))} (hLb : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M)
    (hLbl : Lb.length ≤ vsPN S) {gs : List (Perm (Fin I.n))} (hgs : ∀ g ∈ gs, g ∈ gens s.hs)
    (hgl : gs.length ≤ I.n ^ 2) {c0 : Perm (Fin I.n)} {r : ℕ} (hr : 0 < r) (hrn : r ≤ I.n) :
    VsPOD I (vsPN S) (vsPW6 S) s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs gs
      (vsPZp I s.ws' (vsQCs s) c0 r) (vsQD s * vsQD s + 1) (1 :: s.hs) (vsQD s * vsQD s + 1) r := by
  have hS1 := hS.one_le
  have hSn := hS.n; have hSd := hS.d; have hSp := hS.p
  have hD := vsQD_le hs
  have hC := vsPCtx_ok hS hs hLb hLbl
  have s6 : S ^ 2 ≤ S ^ 6 := hS.pow_le (by omega)
  have s4 : S ^ 4 ≤ S ^ 6 := hS.pow_le (by omega)
  have s3 : S ^ 3 ≤ S ^ 6 := hS.pow_le (by omega)
  have s1 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have p3 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ (by omega)
  have p6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hDD : vsQD s * vsQD s + 1 ≤ vsPN S := by
    have : vsQD s * vsQD s ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
    unfold vsPN; nlinarith
  have hn2 : I.n ^ 2 ≤ vsPN S := by
    have : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
    unfold vsPN; omega
  -- weights
  have wC : (vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs).wt ≤ 10 ^ 8 * S ^ 6 := hC.cw
  have wgs : (Val.list (gs.map encPerm)).wt ≤ 13 * (I.n + 1) ^ 6 := wt_list_encPerms_le_sq hgl
  have wgs' : 13 * (I.n + 1) ^ 6 ≤ 13 * S ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hSn 6)
  have hZw : ∀ v ∈ (vsPZp I s.ws' (vsQCs s) c0 r).map vsWVs, v.wt ≤ 100 * S ^ 3 := by
    intro v hv
    obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hv
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hA
    have hsq := vsPLocL_sq (I := I) (ws' := s.ws') (cs := vsQCs s) (c0 ^ t)
    exact vsQ_wt_loc hS hs hsq.1 (by rw [hsq.2]; exact hD)
  have wZ := vs_wt_list_le_of _ hZw
  have hZl : (vsPZp I s.ws' (vsQCs s) c0 r).length = r := by simp [vsPZp]
  rw [List.length_map, hZl] at wZ
  have wZ' : r * (2 * (100 * S ^ 3) + 1) ≤ S * (201 * S ^ 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e4 : S * (201 * S ^ 3) = 201 * S ^ 4 := by ring
  have wpc := wt_list_le [vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs, .list (gs.map encPerm),
    .list ((vsPZp I s.ws' (vsQCs s) c0 r).map vsWVs)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wpc
  have epc : (vsPPc I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs gs (vsPZp I s.ws' (vsQCs s) c0 r)).wt =
    (Val.list [vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs, .list (gs.map encPerm),
      .list ((vsPZp I s.ws' (vsQCs s) c0 r).map vsWVs)]).wt := rfl
  have wH := hS.wt_group hs.hsl
  have whs : (Val.list ((1 :: s.hs).map encPerm)).wt < (encGroup s.hs).wt :=
    wt_le_wt_list (by simp)
  have wcap := wt_nat_le (vsQD s * vsQD s + 1)
  have wr := wt_nat_le r
  set H1 := Val.list ((1 :: s.hs).map encPerm) with hH1
  have wQ := wt_list_le [vsPPc I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs gs (vsPZp I s.ws' (vsQCs s) c0 r),
    .nat (vsQD s * vsQD s + 1), H1, .nat (vsQD s * vsQD s + 1), .nat r]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wQ
  have eQ : (vsPQ I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs gs (vsPZp I s.ws' (vsQCs s) c0 r)
      (vsQD s * vsQD s + 1) (1 :: s.hs) (vsQD s * vsQD s + 1) r).wt =
    (Val.list [vsPPc I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs gs (vsPZp I s.ws' (vsQCs s) c0 r),
      .nat (vsQD s * vsQD s + 1), H1, .nat (vsQD s * vsQD s + 1),
      .nat r]).wt := rfl
  have hNS : vsPN S ≤ 4 * S ^ 6 := by unfold vsPN; omega
  have whs2 : (Val.list (List.map encPerm (1 :: s.hs))).wt ≤ 320 * S ^ 6 := by
    rw [← hH1]; omega
  refine ⟨hC.mono_W (by unfold vsPW6; omega), fun A hA => ?_, by rw [hZl]; unfold vsPN; omega,
    by unfold vsPW6; omega, fun g hg => hs.prob.le (hgs g hg), by omega,
    fun h hh => ?_, ?_, by unfold vsPW6; omega, by omega, hDD, hDD, hr, by unfold vsPN; omega,
    by unfold vsPW6; omega⟩
  · obtain ⟨t, -, rfl⟩ := List.mem_map.1 hA
    exact vsPLocL_sq (c0 ^ t)
  · rcases List.mem_cons.1 hh with rfl | hh
    · exact one_mem _
    · exact hs.prob.le (Subgroup.subset_closure hh)
  · have := hs.hsl
    simp only [List.length_cons]
    nlinarith

end GI.Impl
