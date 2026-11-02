import Workspace.Impl.AggItemCiSojLeft
import Workspace.Impl.AggItemCiSojWt

/-!
# Computing the even pointwise-fixing subgroup generators

Run the established colored-partition item on a coloring against itself. The
alignment is identity, so extracting its group's generators gives exactly the
existing `itciMs` generators. On the left-side marker coloring these generate
the even permutations fixing the left side pointwise.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {q : ℕ}

/-- A coloring against itself has identity alignment and its usual even generators. -/
theorem itcs_self_os (lab : Fin q → ℕ) (E : Subgroup (alternatingGroup (Fin q))) :
    itciOs lab lab (itciOt lab) E = [(1, E, itciMs lab (itciOt lab))] := by
  classical
  have hal : itciAl lab lab = 1 := by simp only [itciAl, inv_mul_cancel]
  cases ht : itciOt lab with
  | none => simp only [itciOs, hal, Perm.one_apply, implies_true, if_true, ht, map_one, dif_pos, itciMs]
            rfl
  | some a => simp only [itciOs, hal, Perm.one_apply, implies_true, if_true, ht, map_one, dif_pos]
              rfl

/-- On a coloring table, return its even stabilizer's raw generator list. -/
def itcsFixGenF (part : ℕ) : Expr :=
  .get (.get (.call part (mk2 (.var 0) (.var 0))) (.nat 0)) (.nat 1)

/-- Bound for extracting the self-item's generator list. -/
def itcsFixGenC (M : ℕ) : ℕ :=
  itciFC M + 20 * (100 * (itciFC M + M + 10) + 1)

/-- The actual self-item extractor. -/
theorem itcs_fix_gen_prog {Pg : Program} {Ii : ItciIdx} {f M : ℕ}
    (hi : ItciOk Pg Ii) (hf : Pg.funs[f]? = some (itcsFixGenF Ii.f))
    (lab : Fin q → ℕ) (hw : (encFun lab).wt ≤ M) :
    FunDet Pg f (encFun lab) (.list ((itciMs lab (itciOt lab)).map encPerm)) (itcsFixGenC M) := by
  let Bw := 100 * (itciFC M + M + 10)
  have budget : 20 * itciFC M + 20 * M + 100 ≤ Bw := by dsimp only [Bw]; omega
  have hp := itci_prog hi lab lab hw hw ⊥
  rw [itcs_self_os] at hp
  have hov : (itciOV [(1, ⊥, itciMs lab (itciOt lab))]).wt ≤ itciFC M := itcs_det_weight hp
  have hpair : (lcOv (1 : Perm (Fin q)) (itciMs lab (itciOt lab))).wt ≤ itciFC M :=
    (st_wt_mem (List.mem_cons_self ..)).trans hov
  have hgs : (Val.list ((itciMs lab (itciOt lab)).map encPerm)).wt ≤ itciFC M :=
    (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans hpair
  have input : (Val.list [encFun lab, encFun lab]).wt ≤ Bw := by
    have h := wt_list2_le (encFun lab) (encFun lab)
    omega
  have v0 : StDC Pg [encFun lab] (.var 0) (encFun lab) 1 0 Bw := StDC.var' rfl (hw.trans (by omega))
  have pc := StDC.call (StDC.mk2 v0 v0 input (by omega)) hp (hov.trans (by omega))
  have op := StDC.get pc (StDC.nat 0 (by omega)) rfl (hpair.trans (by omega))
  have gs := StDC.get op (StDC.nat 1 (by omega)) rfl (hgs.trans (by omega))
  exact StDC.funDet hf gs (by unfold itcsFixGenC; dsimp only [Bw]; omega)

/-- Polynomial round cost for the marker-table size bound. -/
theorem itcs_fix_gen_pbu : PBU fun _ W _ => itcsFixGenC (5 * (2 * W + 4) ^ 2) := by
  simp only [itcsFixGenC,itciFC]
  norm_poly

end GI.Impl
