import Workspace.Impl.AggItemCiSojSG

/-!
# Building the whole component table

The program makes the two index ranges, materializes every edge exchange, and
passes their encoded list to the existing orbit-table program. The resulting
labels are the least points of the actual color components.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms)

variable {q : ℕ}

/-- Context for constructing all edge exchanges of a given color. -/
def itcsCompData (X : PairCfg q) (v : ℕ) : Val :=
  .list [rcColVal X, .nat X.j, .nat v, .nat q, natList (List.range q)]

/-- Constructed edge-list weight. -/
def itcsGenW (q : ℕ) : ℕ := q * q * (8 * (q + 1) ^ 2 + 1) + 4

/-- The whole list of edge permutations has this explicit weight bound. -/
theorem itcs_gen_weight (X : PairCfg q) (v : ℕ) :
    (Val.list ((itcsSqEdges X v).map encPerm)).wt ≤ itcsGenW q := by
  have h := wt_list_map_le (List.finRange (q * q)) (fun t => encPerm (itcsSqEdge X v t))
    (W := 4 * (q + 1) ^ 2) (fun t _ => wt_encPerm_le _)
  simpa only [itcsSqEdges, List.map_map, Function.comp_apply, List.length_finRange,
    show 2 * (4 * (q + 1) ^ 2) + 1 = 8 * (q + 1) ^ 2 + 1 by omega] using h

/-- Cost of the map that materializes all exchanges. -/
def itcsSqMapC (q W Cg : ℕ) : ℕ :=
  q * q * (100 * (W + 1) + Cg) + mapK * (q * q + 1) * (W + itcsGenW q + 1)

/-- The common weights needed by the table program. They are established from the
input palette bound separately, so the program proof only adds costs. -/
structure itcsCompBounds (X : PairCfg q) (v W : ℕ) : Prop where
  input : (Val.list [rcColVal X, .nat X.j, .nat v, .nat q]).wt ≤ W
  range : (natList (List.range q)).wt ≤ W
  square : (natList (List.range (q * q))).wt ≤ W
  data : (itcsCompData X v).wt ≤ W
  mapInput : (Val.list [itcsCompData X v, natList (List.range (q * q))]).wt ≤ W
  indexed : ∀ t : Fin (q * q), (Val.list [itcsCompData X v, .nat t]).wt ≤ W
  edge : ∀ a b : Fin q, (Val.list [.list [rcColVal X, .nat X.j, .nat v, .nat a, .nat b],
    natList (List.range q)]).wt ≤ W
  swap : ∀ a b : Fin q, (Val.list [.list [.nat a, .nat b], natList (List.range q)]).wt ≤ W
  perm : ∀ p : Perm (Fin q), (encPerm p).wt ≤ W
  generators : (Val.list ((itcsSqEdges X v).map encPerm)).wt ≤ W
  orbitInput : (encPerms (itcsSqEdges X v)).wt ≤ W
  labels : (encFun (itcsLab X v)).wt ≤ W
  qle : q + 10 ≤ W
  qsq : q * q + 2 ≤ W

/-- Materialize the square-indexed exchange list. -/
theorem itcs_sq_gen_map {Pg : Program} {mp fsq eg : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp fsq)) (hf : Pg.funs[fsq]? = some (itcsSqGF eg))
    (X : PairCfg q) (v : ℕ) {W Cg : ℕ} (hw : itcsCompBounds X v W)
    (hg : ∀ a b : Fin q, FunDet Pg eg
      (.list [.list [rcColVal X, .nat X.j, .nat v, .nat a, .nat b], natList (List.range q)])
      (encPerm (itcsEdge X v a b)) Cg) :
    FunDet Pg mp (.list [itcsCompData X v, natList (List.range (q * q))])
      (.list ((itcsSqEdges X v).map encPerm)) (itcsSqMapC q W Cg) := by
  rw [it_range_eq]
  have hm' := mapList_spec hm (List.finRange (q * q)) (fun t => Val.nat t.val)
    (fun t => encPerm (itcsSqEdge X v t)) (c := itcsCompData X v)
    (B := 100 * (W + 1) + Cg)
    (fun t _ s _ h => by cases Fin.ext (Val.nat.inj h); rfl)
    (fun t _ => itcs_sqG_spec hf X v t hg (hw.indexed t) hw.edge
      (fun a b => hw.perm _) hw.qle)
  have he : (Val.list ((List.finRange (q * q)).map fun t => encPerm (itcsSqEdge X v t))) =
      .list ((itcsSqEdges X v).map encPerm) := by
    simp only [itcsSqEdges, List.map_map]
    rfl
  rw [he] at hm'
  refine hm'.mono ?_
  simp only [List.length_finRange]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  have hin := hw.mapInput
  rw [it_range_eq] at hin
  have hout := itcs_gen_weight X v
  omega

/-- On `[table,j,v,q]`, construct the component labels. -/
def itcsCompF (rng mp orb : ℕ) : Expr :=
  .letE (.call rng (arg 3))
    (.letE (.call rng (.arith .mul (arg 3) (arg 3)))
      (.letE (itcsMk5 (arg 0) (arg 1) (arg 2) (arg 3) (.var 1))
        (.letE (.call mp (mk2 (.var 3) (.var 2)))
          (.call orb (mk2 (arg 3) (.var 4))))))

/-- The cost of the component table program. -/
def itcsCompC (q W Cg : ℕ) : ℕ :=
  100 * (W + 1) + 7000 * (q + 1) ^ 3 + 7000 * (q * q + 1) ^ 3 +
    itcsSqMapC q W Cg + orbitK * ((q * q + 1) * (q + 1)) ^ 5

/-- Full construction of the actual component labels, with its library functions installed. -/
theorem itcs_component_prog_full {Pg : Program} {f rng mp fsq eg fo : ℕ}
    (hf : Pg.funs[f]? = some (itcsCompF rng mp fo)) (hr : Pg.HasAt rng (rangeFuns rng))
    (hm : Pg.HasAt mp (mapFuns mp fsq)) (hsq : Pg.funs[fsq]? = some (itcsSqGF eg))
    (ho : Pg.HasAt fo (orbitFuns fo)) (X : PairCfg q) (v : ℕ) {W Cg : ℕ}
    (hw : itcsCompBounds X v W)
    (hg : ∀ a b : Fin q, FunDet Pg eg
      (.list [.list [rcColVal X, .nat X.j, .nat v, .nat a, .nat b], natList (List.range q)])
      (encPerm (itcsEdge X v a b)) Cg) :
    FunDet Pg f (.list [rcColVal X, .nat X.j, .nat v, .nat q])
      (encFun (itcsLab X v)) (itcsCompC q W Cg) := by
  let inp : Val := .list [rcColVal X, .nat X.j, .nat v, .nat q]
  have get (rest : List Val) {i : ℕ} {w : Val}
      (hi : [rcColVal X, .nat X.j, .nat v, .nat q][i]? = some w) (hiw : i + 2 ≤ W) :
      StDC Pg (inp :: rest) (arg i) w 3 0 W :=
    StDC.arg hi hw.input hiw ((st_wt_mem (List.mem_of_getElem? hi)).trans hw.input)
  have r1 := StDC.call (get [] (i := 3) rfl (by have := hw.qle; omega)) (range_det hr q) hw.range
  have sq := StDC.arith' (get [natList (List.range q)] (i := 3) rfl (by have := hw.qle; omega))
    (get [natList (List.range q)] (i := 3) rfl (by have := hw.qle; omega))
    (op := .mul) (z := q * q) rfl hw.qsq
  have r2 := StDC.call sq (range_det hr (q * q)) hw.square
  let R1 := natList (List.range q)
  let R2 := natList (List.range (q * q))
  have vr : StDC Pg (inp :: [R1, R2]) (.var 1) R1 1 0 W := StDC.var' rfl hw.range
  have dat := itcs_mk5 (get [R1, R2] (i := 0) rfl (by have := hw.qle; omega))
    (get [R1, R2] (i := 1) rfl (by have := hw.qle; omega))
    (get [R1, R2] (i := 2) rfl (by have := hw.qle; omega))
    (get [R1, R2] (i := 3) rfl (by have := hw.qle; omega)) vr hw.data (by have := hw.qle; omega)
  let env : List Val := inp :: [R1, R2, itcsCompData X v]
  have vd : StDC Pg env (.var 3) (itcsCompData X v) 1 0 W := StDC.var' rfl hw.data
  have vi : StDC Pg env (.var 2) R2 1 0 W := StDC.var' rfl hw.square
  have mpCall := StDC.call (StDC.mk2 vd vi hw.mapInput (by have := hw.qle; omega))
    (itcs_sq_gen_map hm hsq X v hw hg) hw.generators
  let gs := Val.list ((itcsSqEdges X v).map encPerm)
  have vg : StDC Pg (env ++ [gs]) (.var 4) gs 1 0 W := StDC.var' rfl hw.generators
  have qv := get [R1, R2, itcsCompData X v, gs] (i := 3) rfl (by have := hw.qle; omega)
  have orbCall := StDC.call (StDC.mk2 qv vg hw.orbitInput (by have := hw.qle; omega))
    (itcs_sq_table ho X v) hw.labels
  have body := StDC.letE r1 (StDC.letE r2 (StDC.letE dat
    (StDC.letE mpCall orbCall hw.labels) hw.labels) hw.labels) hw.labels
  exact StDC.funDet hf body (by unfold itcsCompC; omega)

end GI.Impl
