import Workspace.Impl.GenNormGraph

/-!
# A canonical normalized group and its raw generator list

The group value includes a leading identity. The label list must have at most `n²` entries,
so we also ask the pointwise-stabilizer task with no fixed points for a raw generator list.
Both lists generate the same normalized group. The pairing program can run on the raw list
and therefore keeps the label bound of `LabValStd`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm PointwiseStab)

/-- On `[n,pairs]`, return `[canonicalGroup,rawGenerators]`. -/
def normRawReduceF (kr jst : ℕ) : Expr :=
  .letE (.call kr (.var 0))
    (.letE (.prim jst (mk2 (.var 1) .nil)) (mk2 (.var 1) (.var 2)))

/-- A polynomial bound, with the two cited stabilizer bounds shown explicitly. -/
noncomputable def normRawReduceCost (hst : PointwiseStab) (n m L W : ℕ) : ℕ :=
  let M := n + m + L + 2
  (pointwiseStabPrim hst).boundSize (100 * M ^ 4) + krK * M ^ 9 +
    (pointwiseStabPrim hst).boundSize (2 * (groupW n + 4) + 6) +
      1000 * (W + groupW n + 13 * (n + 1) ^ 6 + 20)

/-- The raw list has at most `n²` entries and gives exactly the same normalized group as the
canonical group value. Both cited calls fix the empty list of points. -/
theorem normRawReduce_spec (hst : PointwiseStab) {Pg : Program} {f kr jst : ℕ}
    (hf : Pg.funs[f]? = some (normRawReduceF kr jst))
    (hkr : Pg.HasAt kr (krFuns kr jst)) (hj : Pg.prims[jst]? = some (pointwiseStabPrim hst))
    {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
    (hS : Q.ProductStructure m k 1 e) (ps : List (Perm (Fin n) × Perm (Fin m)))
    (hps : Subgroup.closure {p | p ∈ ps} = normGraph en Q e hS) :
    FunAll Pg f (.list [.nat n, .list (ps.map pairV)]) (fun w cost =>
      ∃ (gv : Val) (gs : List (Perm (Fin n))), w = .list [gv, .list (gs.map encPerm)] ∧
        GroupValC n gv (groupFin en (Q.normGroup e hS)) ∧
        GI.Cited.gens gs = groupFin en (Q.normGroup e hS) ∧ gs.length ≤ n ^ 2 ∧
        cost ≤ normRawReduceCost hst n m ps.length (Val.list [.nat n, .list (ps.map pairV)]).wt) := by
  let inp := Val.list [.nat n, .list (ps.map pairV)]
  have hcall : EvalAll Pg [inp] (.call kr (.var 0)) (fun w cost =>
      GroupValC n w (groupFin en (Q.normGroup e hS)) ∧
        cost ≤ inp.wt + 1 + (pointwiseStabPrim hst).boundSize (100 * pM n m ps ^ 4) +
          krK * pM n m ps ^ 9 + w.wt + 1) :=
    EvalAll.call_funAll (Det.var' (P := Pg) (env := [inp]) (i := 0) rfl)
    (fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      exact (normGraphReduce_spec en Q e hS hst hkr hj ps hps).mono
        fun w c hw => ⟨hw.1, by have := hw.2; omega⟩)
  refine FunAll.intro hf (EvalAll.letE hcall fun gv cg hgv => ?_)
  obtain ⟨hgv, hcg⟩ := hgv
  have wg := hgv.wt_le
  have dprim := pointwiseStab_call hst (S := ([] : List (Fin n))) hj
    (Det.mk2 (Det.var' (P := Pg) (env := [inp, gv]) (i := 1) rfl) Det.nil) hgv.groupVal
  rw [pointwiseStab_nil] at dprim
  refine EvalAll.letE dprim fun raw cr hraw => ?_
  obtain ⟨hraw, hcr⟩ := hraw
  have wraw := GensVal.wt_le hraw
  obtain ⟨gs, rfl, hlen, hgen⟩ := hraw
  have dret := Det.mk2
    (Det.var' (P := Pg) (env := [inp, gv, .list (gs.map encPerm)]) (i := 1) rfl)
    (Det.var' (P := Pg) (env := [inp, gv, .list (gs.map encPerm)]) (i := 2) rfl)
  refine dret.post fun c hc => ⟨gv, gs, rfl, hgv, hgen, hlen, ?_⟩
  have wp := wt_list2_le gv (.list (gs.map encPerm))
  have warg := wt_list2_le gv (.list [])
  have wnil : (Val.list []).wt = 4 := rfl
  have warg' := wt_list2_le gv (GI.Cited.encPts ([] : List (Fin n)))
  have wnil' : (GI.Cited.encPts ([] : List (Fin n))).wt = 4 := rfl
  have hp := prim_bound_le_wt (pointwiseStabPrim hst)
    (v := .list [gv, GI.Cited.encPts ([] : List (Fin n))])
    (show (Val.list [gv, GI.Cited.encPts ([] : List (Fin n))]).wt ≤ 2 * (groupW n + 4) + 6 by omega)
  change (pointwiseStabPrim hst).bound (.list [gv, GI.Cited.encPts ([] : List (Fin n))]) ≤
    (pointwiseStabPrim hst).boundSize (2 * (groupW n + 4) + 6) at hp
  change _ ≤ normRawReduceCost hst n m ps.length inp.wt
  unfold normRawReduceCost
  dsimp only
  have hM : pM n m ps = n + m + ps.length + 2 := rfl
  rw [hM] at hcg
  omega

end GI.Impl
