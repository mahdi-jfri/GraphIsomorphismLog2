module

public import Workspace.Impl.LiftSpec

@[expose] public section

/-!
# Cutting a generating list to at most `n²` generators

The input of `Solve` may store any number of generators, and the restriction of `k²`
generators to the domain gives up to `k² + 1` generators on `s ≤ k` points. A fresh phase
needs at most `s²` (`GroupValC`). The cited task **PointwiseStab** with no points returns the
group itself, with at most `n²` generators ([LM, Theorem 3.1(iv)]; the output bound is part of
the task, `GI.Cited.GensOf`).

`redFuns b j` (8 functions at base `b`, the primitive at index `j`): on `[n, gv]` with
`GroupVal n gv G`, it returns `encGroup hs` with `gens hs = G` and `hs.length ≤ n²`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens PointwiseStab pointwiseStab encPts)

/-- The pointwise stabilizer of no points is the group. -/
theorem pointwiseStab_nil {n : ℕ} (G : Subgroup (Perm (Fin n))) : pointwiseStab G [] = G := by
  ext g; simp [pointwiseStab]

/-- On `[n, gv]`: `mkGroup [n, PointwiseStab [gv, []]]`. -/
def redEntry (b j : ℕ) : Expr := .call (b + 1) (mk2 (arg 0) (.prim j (mk2 (arg 1) .nil)))

/-- The reduction module at base `b` (8 functions). -/
def redFuns (b j : ℕ) : List Expr := [redEntry b j] ++ mkGroupFuns (b + 1)

theorem length_redFuns (b j : ℕ) : (redFuns b j).length = 8 := by
  simp [redFuns, mkGroupFuns, rangeFuns, appendFuns, loopFuns]

/-- **Cutting a generating list.** -/
theorem red_spec (hst : PointwiseStab) {P : Program} {b j : ℕ} (h : P.HasAt b (redFuns b j))
    (hj : P.prims[j]? = some (pointwiseStabPrim hst)) {n : ℕ} {gv : Val}
    {G : Subgroup (Perm (Fin n))} (hG : GroupVal n gv G) :
    FunAll P b (.list [.nat n, gv]) (fun w c => ∃ hs : List (Perm (Fin n)), w = encGroup hs ∧
      gens hs = G ∧ hs.length ≤ n ^ 2 ∧
      c ≤ (pointwiseStabPrim hst).bound (.list [gv, .list []]) + 20 * gv.wt +
        10 ^ 7 * (n + 1) ^ 9) := by
  have hentry : P.funs[b]? = some (redEntry b j) := by
    simpa using (h.block 0 (gs := [redEntry b j]) (by rfl)).single
  have hmk : P.HasAt (b + 1) (mkGroupFuns (b + 1)) := h.block 1 (by rfl)
  refine FunAll.intro hentry ?_
  have g0 := Det.arg' (P := P) (vs := [.nat n, gv]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [.nat n, gv]) (rest := []) (j := 1) rfl
  have dpre := Det.mk2 g1 (Det.nil (P := P) (env := [.list [.nat n, gv]]))
  have hst' := pointwiseStab_call hst hj (S := ([] : List (Fin n))) dpre hG
  rw [pointwiseStab_nil] at hst'
  refine EvalAll.call_funAll (EvalAll.mk2_last g0 hst') ?_
  rintro _ ca ⟨w, cw, ⟨hw, hcw⟩, rfl, hca⟩
  obtain ⟨hs, hL, hl, hfd, hgv, hwt⟩ := mkGroup_gensVal hmk hw
  refine FunAll.mono hfd fun u cu ⟨hu, hcu⟩ => ⟨hs, hu, ?_, hl, ?_⟩
  · obtain ⟨gs', he, hg'⟩ := hgv
    rw [hu] at *
    exact (encGroup_injective he ▸ hg')
  · subst hu
    have w1 := wt_list2_le (.nat n) gv
    have w2 := wt_list2_le gv (.list [])
    have w3 := wt_list2_le (.nat n) w
    have w4 := wt_nat_le n
    have w5 := GensVal.wt_le hw
    have w6 : (Val.list []).wt ≤ 5 := by decide
    have p1 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have p2 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    simp only [mkGroupK] at *
    have ebd : (pointwiseStabPrim hst).bound (.list [gv, encPts ([] : List (Fin n))]) =
        (pointwiseStabPrim hst).bound (.list [gv, .list []]) := rfl
    omega

end GI.Impl
