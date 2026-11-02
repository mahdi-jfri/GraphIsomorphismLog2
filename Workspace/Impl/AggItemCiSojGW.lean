import Workspace.Impl.AggItemCiSojGM

/-!
# Preserving the degree field when projecting an encoded group

`encGroup` contains a degree and a list of permutations with leading identity.
Map only that list and write the label degree in the returned group encoding.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encGroup)

/-- On `[lift context, physical group, label degree]`, map the generators and
rebuild the label-group value. -/
def itcsGroupMapF (mp : ℕ) : Expr :=
  mk2 (arg 2) (.call mp (mk2 (arg 0) (.get (arg 1) (.nat 1))))

/-- Common budget for projecting one encoded group. -/
def itcsGroupMapW (q : ℕ) (ctx gv out : Val) : ℕ :=
  100 * (ctx.wt + gv.wt + out.wt + q + 10)

/-- The wrapper preserves the leading identity and writes the actual new degree. -/
theorem itcs_group_map_spec {Pg : Program} {f mp Cg k q : ℕ} (ctx : Val)
    (gs : List (Perm (Fin k))) (ts : List (Perm (Fin q)))
    (hf : Pg.funs[f]? = some (itcsGroupMapF mp))
    (hm : FunDet Pg mp (.list [ctx, itcsGenList gs]) (itcsGenList ts) Cg) :
    FunDet Pg f (.list [ctx, encGroup gs, .nat q]) (encGroup ts)
      (50 * (itcsGroupMapW q ctx (encGroup gs) (itcsGenList ts) + 1) + Cg) := by
  let Bw := itcsGroupMapW q ctx (encGroup gs) (itcsGenList ts)
  have budget : 20 * ctx.wt + 20 * (encGroup gs).wt + 20 * (itcsGenList ts).wt +
      20 * q + 100 ≤ Bw := by dsimp only [Bw]; unfold itcsGroupMapW; omega
  have wg : (itcsGenList gs).wt ≤ (encGroup gs).wt :=
    st_wt_mem (by simp [encGroup, GI.Cited.encPerms, itcsGenList])
  have qn := wt_nat_le q
  have wi : (Val.list [ctx, encGroup gs, .nat q]).wt ≤ Bw := by
    have h := wt_list3_le ctx (encGroup gs) (.nat q)
    omega
  have wa : (Val.list [ctx, itcsGenList gs]).wt ≤ Bw := by
    have h := wt_list2_le ctx (itcsGenList gs)
    omega
  have wo : (encGroup ts).wt ≤ Bw := by
    have h := wt_list2_le (.nat q) (itcsGenList ts)
    change (Val.list [.nat q, itcsGenList ts]).wt ≤ Bw
    omega
  let env : List Val := [.list [ctx, encGroup gs, .nat q]]
  have get {i : ℕ} {v : Val} (hi : [ctx, encGroup gs, Val.nat q][i]? = some v)
      (hii : i + 2 ≤ Bw) : StDC Pg env (arg i) v 3 0 Bw :=
    StDC.arg hi wi hii ((st_wt_mem (List.mem_of_getElem? hi)).trans wi)
  have gc := get (i := 0) rfl (by omega)
  have gg := get (i := 1) rfl (by omega)
  have gq := get (i := 2) rfl (by omega)
  have gl := StDC.get gg (StDC.nat 1 (by omega)) rfl (wg.trans (by omega))
  have mapped := StDC.call (StDC.mk2 gc gl wa (by omega)) hm (by omega)
  have body := StDC.mk2 gq mapped wo (by omega)
  exact StDC.funDet hf body (by dsimp only [Bw]; omega)

end GI.Impl
