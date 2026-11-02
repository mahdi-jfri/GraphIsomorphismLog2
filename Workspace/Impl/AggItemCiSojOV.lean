import Workspace.Impl.AggItemCiSojGB
import Workspace.Impl.AggLiftChild

/-!
# Encoding the full-label rectangle overcosets

Left-multiply each projected matrix representative by the fixed even alignment
and attach the common, fully reconstructed source generator list.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {q : ℕ}

/-- On `[[alignment, generators], r]`, return `[alignment*r,generators]`. -/
def itcsOverF (cmp : ℕ) : Expr :=
  mk2 (.call cmp (mk2 (.get (arg 0) (.nat 0)) (arg 1))) (.get (arg 0) (.nat 1))

/-- A common budget for one overcoset entry. -/
def itcsOverW (q : ℕ) (ms : List (Perm (Fin q))) : ℕ :=
  100 * ((Val.list (ms.map encPerm)).wt + 12 * (q+1)^2 + 10)

/-- One encoded full-label overcoset entry. -/
theorem itcs_over_spec {Pg : Program} {f cmp : ℕ}
    (hf : Pg.funs[f]? = some (itcsOverF cmp)) (hc : Pg.HasAt cmp (composeFuns cmp))
    (a₀ r : Perm (Fin q)) (ms : List (Perm (Fin q))) :
    FunDet Pg f (.list [.list [encPerm a₀,.list (ms.map encPerm)],encPerm r])
      (lcOv (a₀*r) ms) (50*(itcsOverW q ms+1)+permK*(q+1)^3) := by
  let mv : Val := .list (ms.map encPerm)
  let ctx : Val := .list [encPerm a₀,mv]
  let Bw := itcsOverW q ms
  have budget : 20*mv.wt+100*(q+1)^2+100≤Bw := by dsimp only [Bw,mv]; unfold itcsOverW; omega
  have wa := wt_encPerm_le a₀
  have wr := wt_encPerm_le r
  have war := wt_encPerm_le (a₀*r)
  have h1 : 1≤(q+1)^2 := Nat.one_le_pow 2 (q+1) (by omega)
  have wc := wt_list2_le (encPerm a₀) mv
  have wi : (Val.list [ctx,encPerm r]).wt≤Bw := by
    have h:=wt_list2_le ctx (encPerm r)
    dsimp only [ctx] at h ⊢
    omega
  have wci : (Val.list [encPerm a₀,encPerm r]).wt≤Bw := by
    have h:=wt_list2_le (encPerm a₀) (encPerm r)
    omega
  have wo : (lcOv (a₀*r) ms).wt≤Bw := by
    have h:=wt_list2_le (encPerm (a₀*r)) mv
    change (Val.list [encPerm (a₀*r),mv]).wt≤Bw
    omega
  let env : List Val := [.list [ctx,encPerm r]]
  have c0 : StDC Pg env (arg 0) ctx 3 0 Bw :=
    StDC.arg rfl wi (by omega) (by dsimp only [ctx]; omega)
  have r1 : StDC Pg env (arg 1) (encPerm r) 3 0 Bw := StDC.arg rfl wi (by omega) (wr.trans (by omega))
  have ca := StDC.get c0 (StDC.nat 0 (by omega)) rfl (wa.trans (by omega))
  have cm := StDC.get c0 (StDC.nat 1 (by omega)) rfl (by omega)
  have comp := StDC.call (StDC.mk2 ca r1 wci (by omega)) (compose_spec hc a₀ r) (war.trans (by omega))
  have body := StDC.mk2 comp cm wo (by omega)
  exact StDC.funDet hf body (by dsimp only [Bw]; omega)

/-- Tabulate all nonempty-query overcosets in their original query order. -/
theorem itcs_over_table {Pg : Program} {mp f cmp : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]? = some (itcsOverF cmp))
    (hc : Pg.HasAt cmp (composeFuns cmp)) (a₀ : Perm (Fin q))
    (rs ms : List (Perm (Fin q))) :
    FunDet Pg mp (.list [.list [encPerm a₀,.list (ms.map encPerm)],.list (rs.map encPerm)])
      (.list (rs.map fun r=>lcOv (a₀*r) ms))
      (rs.length*(50*(itcsOverW q ms+1)+permK*(q+1)^3)+mapK*(rs.length+1)*
        ((Val.list [.list [encPerm a₀,.list (ms.map encPerm)],.list (rs.map encPerm)]).wt+
          (Val.list (rs.map fun r=>lcOv (a₀*r) ms)).wt+1)) :=
  mapList_spec hm rs encPerm (fun r=>lcOv (a₀*r) ms)
    (fun a _ b _ h=>by rw [encPerm_injective h]) (fun r _=>itcs_over_spec hf hc a₀ r ms)

end GI.Impl
