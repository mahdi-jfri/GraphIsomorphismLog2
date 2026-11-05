module

public import Workspace.Impl.VsPDer

@[expose] public section

/-!
# The output "grow `A`"

`vsPGrowE` on `[ctx, ⟨as⟩, xs]` computes generators of the normal closure of `as ++ xs` in
`H = ⟨hs⟩` (one `NormalClosure` call, then `mkGroup`). The closure has at most `n²` generators.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- On `[ctx, ⟨as⟩, xs]`: the group value of the normal closure of `as ++ xs` in `⟨hs⟩`. -/
def vsPGrowE (ap mkg nc : ℕ) : Expr :=
  .call mkg (mk2 (vsPC 6) (.prim nc (mk2 (vsPC 5)
    (mk2 (vsPC 6) (.call ap (mk2 (.get (arg 1) (.nat 1)) (arg 2)))))))

/-- The bound of a call of the normal-closure primitive on a value of weight at most
`2000 (N + 1)^6`. -/
noncomputable def vsPNcB (hn : NormalClosure) (N : ℕ) : ℕ :=
  (normalClosurePrim hn).c * (2000 * (N + 1) ^ 6 + 2) ^ (normalClosurePrim hn).k

/-- The cost of the grow program. -/
noncomputable def vsPGrowCost (hn : NormalClosure) (N W : ℕ) : ℕ :=
  vsPNcB hn N + 10 ^ 9 * (N + 1) ^ 9 + 100 * W

theorem encGroup_append {n : ℕ} (as xs : List (Perm (Fin n))) :
    encGroup (as ++ xs) = .list [.nat n, .list ((1 :: as).map encPerm ++ xs.map encPerm)] := by
  simp only [encGroup, encPerms, List.map_cons, List.map_append, List.cons_append]

set_option maxHeartbeats 4000000 in
theorem vsPGrow_spec (hn : NormalClosure) {P : Program} {f ap mkg nc N W : ℕ}
    (hf : P.funs[f]? = some (vsPGrowE ap mkg nc)) (hap : P.HasAt ap (appendFuns ap))
    (hmk : P.HasAt mkg (mkGroupFuns mkg)) (hnc : P.prims[nc]? = some (normalClosurePrim hn))
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) (hhs : hs.length ≤ I.n ^ 2)
    {as xs : List (Perm (Fin I.n))} (hal : as.length ≤ I.n ^ 2) (hxl : xs.length ≤ I.n ^ 2) :
    FunAll P f (.list [vsPCtx I ws' cs rows hs, encGroup as, .list (xs.map encPerm)]) (fun w c =>
      ∃ as' : List (Perm (Fin I.n)), w = encGroup as' ∧ as'.length ≤ I.n ^ 2 ∧
        gens as' = Subgroup.closure {x | ∃ g ∈ gens hs ⊔ gens (as ++ xs), ∃ y ∈ as ++ xs,
          x = g * y * g⁻¹} ∧ c ≤ vsPGrowCost hn N W) := by
  set C := vsPCtx I ws' cs rows hs
  set cv := [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n] with hcv
  set A := Val.list [C, encGroup as, .list (xs.map encPerm)]
  set ys := (1 :: as).map encPerm
  have eas : encGroup as = .list [.nat I.n, .list ys] := rfl
  have a0 : Det P [A] (arg 0) (.list cv) _ :=
    Det.arg' (P := P) (vs := [C, encGroup as, .list (xs.map encPerm)]) (rest := []) (j := 0) rfl
  have a1 : Det P [A] (arg 1) (.list [.nat I.n, .list ys]) _ :=
    Det.arg' (P := P) (vs := [C, encGroup as, .list (xs.map encPerm)]) (rest := []) (j := 1) rfl
  have a2 := Det.arg' (P := P) (vs := [C, encGroup as, .list (xs.map encPerm)]) (rest := [])
    (j := 2) rfl
  have c5 := Det.get' a0 (Det.nat 5) (show cv[5]? = some (encGroup hs) from rfl)
  have c6 := Det.get' a0 (Det.nat 6) (show cv[6]? = some (.nat I.n) from rfl)
  have dl := Det.get' a1 (Det.nat 1) (show [Val.nat I.n, .list ys][1]? = some (.list ys) from rfl)
  have dap := Det.call (Det.mk2 dl a2) ((append_spec hap ys (xs.map encPerm)).mono
    (Q' := fun w c => w = .list (ys ++ xs.map encPerm) ∧ c ≤ loopModK * ((xs.map encPerm).length + 1) *
      ((Val.list [.list ys, .list (xs.map encPerm)]).wt + (xs.map encPerm).length +
        (Val.list (ys ++ xs.map encPerm)).wt + 1)) fun w c h => ⟨h.1, h.1 ▸ h.2⟩)
  have dgrp := Det.mk2 c6 dap
  rw [← encGroup_append] at dgrp
  have darg := Det.mk2 c5 dgrp
  have dprim := normalClosure_call hn hnc darg ⟨hs, rfl, rfl⟩
  have dmk := EvalAll.mk2_last c6 dprim
  apply FunAll.intro hf
  refine EvalAll.call_funAll dmk fun v ca hv => ?_
  obtain ⟨vb, cb, ⟨hG, hcb⟩, rfl, hca⟩ := hv
  obtain ⟨as', rfl, hl, hmkd, -, hwt⟩ := mkGroup_gensVal hmk hG
  refine FunAll.mono hmkd fun w c hw => ⟨as', hw.1, hl, ?_, ?_⟩
  · obtain ⟨hs', e, -, hgs⟩ := hG
    have : as' = hs' := (List.map_injective_iff.mpr encPerm_injective) (by simpa using e)
    rw [this, hgs]
  · have hnN := H.n
    have wC : C.wt ≤ W := H.cw
    have ecv : (Val.list cv).wt = C.wt := rfl
    have hn6 : (I.n + 1) ^ 6 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have hn9 : (I.n + 1) ^ 9 ≤ (N + 1) ^ 9 := Nat.pow_le_pow_left (by omega) 9
    have q1 : 1 ≤ (N + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have q2 : (N + 1) ^ 6 ≤ (N + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have q3 : N + 1 ≤ (N + 1) ^ 6 := Nat.le_self_pow (by omega) _
    have wa := wt_encGroup_le_sq hal
    have wh := wt_encGroup_le_sq hhs
    have hax : (as ++ xs).length + 2 ≤ 2 * (I.n + 1) ^ 2 := by
      rw [List.length_append]; nlinarith
    have wax : (encGroup (as ++ xs)).wt ≤ 160 * (I.n + 1) ^ 6 := by
      have := wt_encGroup_le (as ++ xs)
      have h2 : ((as ++ xs).length + 2) * (I.n + 1) ≤ 2 * (I.n + 1) ^ 3 := by
        calc ((as ++ xs).length + 2) * (I.n + 1) ≤ 2 * (I.n + 1) ^ 2 * (I.n + 1) :=
              Nat.mul_le_mul_right _ hax
          _ = 2 * (I.n + 1) ^ 3 := by ring
      have h3 : (((as ++ xs).length + 2) * (I.n + 1)) ^ 2 ≤ (2 * (I.n + 1) ^ 3) ^ 2 :=
        Nat.pow_le_pow_left h2 2
      have h4 : (2 * (I.n + 1) ^ 3) ^ 2 = 4 * (I.n + 1) ^ 6 := by ring
      omega
    have wxs : (Val.list (xs.map encPerm)).wt ≤ 13 * (I.n + 1) ^ 6 := wt_list_encPerms_le_sq hxl
    have wys : (Val.list ys).wt ≤ (encGroup as).wt := by
      rw [eas]; exact (wt_le_wt_list (show Val.list ys ∈ [Val.nat I.n, Val.list ys] by simp)).le
    have wysx : (Val.list (ys ++ xs.map encPerm)).wt ≤ (encGroup (as ++ xs)).wt := by
      rw [encGroup_append]
      exact (wt_le_wt_list (show Val.list (ys ++ xs.map encPerm) ∈
        [Val.nat I.n, Val.list (ys ++ xs.map encPerm)] by simp)).le
    have hxsl : (xs.map encPerm).length ≤ (N + 1) ^ 2 := by
      rw [List.length_map]; have : I.n ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have hap' : loopModK * ((xs.map encPerm).length + 1) *
        ((Val.list [.list ys, .list (xs.map encPerm)]).wt + (xs.map encPerm).length +
          (Val.list (ys ++ xs.map encPerm)).wt + 1) ≤ 10 ^ 7 * (N + 1) ^ 8 := by
      have w2 := wt_list2_le (.list ys) (.list (xs.map encPerm))
      have h1 : (xs.map encPerm).length + 1 ≤ 2 * (N + 1) ^ 2 := by
        have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      have h2 : (Val.list [.list ys, .list (xs.map encPerm)]).wt + (xs.map encPerm).length +
          (Val.list (ys ++ xs.map encPerm)).wt + 1 ≤ 5000 * (N + 1) ^ 6 := by
        have : (N + 1) ^ 2 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      calc loopModK * ((xs.map encPerm).length + 1) * _ ≤ 1000 * (2 * (N + 1) ^ 2) *
            (5000 * (N + 1) ^ 6) := Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
        _ = 10 ^ 7 * (N + 1) ^ 8 := by ring
    have q8 : (N + 1) ^ 8 ≤ (N + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have hbound : (normalClosurePrim hn).bound (.list [encGroup hs, encGroup (as ++ xs)]) ≤
        vsPNcB hn N := by
      unfold Prim.bound vsPNcB
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      have := (Val.list [encGroup hs, encGroup (as ++ xs)]).size_le_wt
      have := wt_list2_le (encGroup hs) (encGroup (as ++ xs))
      omega
    have hmkc : 8 * mkGroupK * (I.n + 1) ^ 9 ≤ 800000 * (N + 1) ^ 9 := by
      rw [show 8 * mkGroupK = 800000 from rfl]; omega
    have w1 := wt_list_encPerms_le_sq hl
    have wA := wt_list3_le C (encGroup as) (.list (xs.map encPerm))
    have eA : A.wt = (Val.list [C, encGroup as, .list (xs.map encPerm)]).wt := rfl
    have ea' : (Val.list [Val.nat I.n, Val.list ys]).wt = (encGroup as).wt := rfl
    have wn := wt_nat_le I.n
    have w5 := wt_list2_le (encGroup hs) (encGroup (as ++ xs))
    have w6 := wt_list2_le (Val.nat I.n) (Val.list (as'.map encPerm))
    have w7 := wt_list2_le (Val.list ys) (Val.list (xs.map encPerm))
    have w8 := wt_list2_le (Val.nat I.n) (Val.list (ys ++ xs.map encPerm))
    have e8 : (Val.list [Val.nat I.n, Val.list (ys ++ xs.map encPerm)]).wt =
        (encGroup (as ++ xs)).wt := by rw [encGroup_append]
    have hc := hw.2
    rw [hw.1]
    unfold vsPGrowCost
    omega

end GI.Impl
