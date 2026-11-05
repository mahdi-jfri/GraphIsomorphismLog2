module

public import Workspace.Impl.GenNormBlockMap
public import Workspace.Impl.AggPre
public import Workspace.Impl.GenNormFiber
public import Workspace.Impl.GenNormSel

@[expose] public section

/-!
# Assembling the computed normalization label value

The preceding programs compute the graph pairs, selected interval, fiber size and block
indicators. This last piece inserts the Johnson subset size, choosing the complement size
when the Cameron subsets are larger than half the points.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

/-- On `[m,k,pairs,selector,fiber,blocks]`, assemble `[m,pairs,selector,h,fiber,blocks]`. -/
def normLabelBuildF : Expr := Expr.mkList [arg 0, arg 2, arg 3,
  .ite (.arith .lt (arg 0) (.arith .mul (.nat 2) (arg 1)))
    (.arith .sub (arg 0) (arg 1)) (arg 1), arg 4, arg 5]

/-- The final assembly uses only arithmetic and list construction. -/
theorem normLabelBuild_spec {Pg : Program} {f : ℕ} (hf : Pg.funs[f]? = some normLabelBuildF)
    (m k : ℕ) (pairs sel fiber blocks : Val) :
    FunDet Pg f (.list [.nat m, .nat k, pairs, sel, fiber, blocks])
      (.list [.nat m, pairs, sel, .nat (if 2 * k ≤ m then k else m - k), fiber, blocks])
      (10 ^ 6 * ((Val.list [.nat m, .nat k, pairs, sel, fiber, blocks]).wt + m + k + 1) ^ 2) := by
  let vs := [Val.nat m, .nat k, pairs, sel, fiber, blocks]
  let inp := Val.list vs
  let Z := inp.wt + m + k + 1
  let h := if 2 * k ≤ m then k else m - k
  have einp : (Val.list vs).wt = inp.wt := rfl
  have hZ : 1 ≤ Z := by dsimp only [Z]; omega
  have w0 : (Val.nat m).wt < inp.wt := wt_le_wt_list (by simp [vs])
  have wp : pairs.wt < inp.wt := wt_le_wt_list (by simp [vs])
  have ws : sel.wt < inp.wt := wt_le_wt_list (by simp [vs])
  have wf : fiber.wt < inp.wt := wt_le_wt_list (by simp [vs])
  have wb : blocks.wt < inp.wt := wt_le_wt_list (by simp [vs])
  have dh : h ≤ m + k := by dsimp only [h]; split_ifs <;> omega
  have wh := wt_nat_le h
  have dm : Det Pg [inp] (arg 0) (.nat m) (2 * inp.wt + 5) := Det.arg' rfl
  have dk : Det Pg [inp] (arg 1) (.nat k) (2 * inp.wt + 6) := Det.arg' rfl
  have dmul := Det.arith' (op := .mul) (Det.nat (P := Pg) (env := [inp]) 2) dk (z := 2 * k) rfl
  have dt := Det.arith' (op := .lt) dm dmul (z := if m < 2 * k then 1 else 0) rfl
  have ds := Det.arith' (op := .sub) dm dk (z := m - k) rfl
  have dhprog : Det Pg [inp]
      (.ite (.arith .lt (arg 0) (.arith .mul (.nat 2) (arg 1)))
        (.arith .sub (arg 0) (arg 1)) (arg 1)) (.nat h) (100 * Z) := by
    by_cases hlt : m < 2 * k
    · have hn : ¬ 2 * k ≤ m := by omega
      have dh' : h = m - k := if_neg hn
      rw [if_pos hlt] at dt
      rw [dh']
      refine (Det.ite_pos dt (by decide) ds).mono ?_
      have wsub := wt_nat_le (m - k)
      dsimp only [Z]
      omega
    · have hn : 2 * k ≤ m := by omega
      have dh' : h = k := if_pos hn
      rw [if_neg hlt] at dt
      rw [dh']
      refine (Det.ite_zero dt dk).mono ?_
      have wk := wt_nat_le k
      dsimp only [Z]
      omega
  have wout := wt_list_le [Val.nat m, pairs, sel, .nat h, fiber, blocks]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wout
  have dlist := Det.mkList (P := Pg) (env := [inp]) (c := 100 * Z)
    [(arg 0, .nat m), (arg 2, pairs), (arg 3, sel),
      (.ite (.arith .lt (arg 0) (.arith .mul (.nat 2) (arg 1)))
        (.arith .sub (arg 0) (arg 1)) (arg 1), .nat h), (arg 4, fiber), (arg 5, blocks)] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact dm.mono (by dsimp only [Z]; omega)
      · exact (Det.arg' (j := 2) rfl).mono (by dsimp only [Z]; omega)
      · exact (Det.arg' (j := 3) rfl).mono (by dsimp only [Z]; omega)
      · exact dhprog
      · exact (Det.arg' (j := 4) rfl).mono (by dsimp only [Z]; omega)
      · exact (Det.arg' (j := 5) rfl).mono (by dsimp only [Z]; omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at dlist
  refine FunDet.intro hf (dlist.mono ?_)
  have h12 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  change _ ≤ 10 ^ 6 * Z ^ 2
  dsimp only [Z] at h12
  dsimp only [Z]
  omega

/-- With the computed components, the assembler returns exactly `normLabelVal`. -/
theorem normLabelBuild_exact {Pg : Program} {f : ℕ} (hf : Pg.funs[f]? = some normLabelBuildF)
    {Ω C : Type} {S : State Ω C} {n : ℕ} (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S)
    (c : Q.NormChoice) (ps : List (Perm (Fin n) × Perm (Fin c.m))) :
    FunDet Pg f (.list [.nat c.m, .nat c.k, .list (ps.map pairV), .nat Q.pre.length,
      .nat (Nat.card {v : S.dom // Q.blk v.1 = ⟨0, by have := Q.two_le; omega⟩}),
      normBlockMapVal en Q c]) (normLabelVal en Q c ps)
      (10 ^ 6 * ((Val.list [.nat c.m, .nat c.k, .list (ps.map pairV), .nat Q.pre.length,
        .nat (Nat.card {v : S.dom // Q.blk v.1 = ⟨0, by have := Q.two_le; omega⟩}),
        normBlockMapVal en Q c]).wt + c.m + c.k + 1) ^ 2) := by
  exact normLabelBuild_spec hf c.m c.k _ _ _ _

end GI.Impl
