module

public import Workspace.Impl.GenNormLabels
public import Workspace.Impl.Orbit

@[expose] public section

/-!
# Keeping the supplied labels when reading a giant child's answer

The recursive specification returns a run on the labels encoded by the input. The uniqueness
of `LabValStd` identifies them with the normalization labels. Thus the run used to charge the
child's cost is a run on exactly the labels computed by the caller.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

/-- A recursive giant call has the exact supplied labels, not merely some label map on the
same group. Its excess cost is zero, as for `Continue`. -/
theorem normCall_giant (R : Rest) {Pg : Program} {F : Funs} {env : List Val} {expr : Expr}
    {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C}
    {sv lv : Val} {L : SuppliedLabels S} {cArg : ℕ}
    (ha : Det Pg env expr (.list [sv, lv]) cArg) (hl : LabValStd e S lv L)
    (hcall : FunAll Pg F.giant (.list [sv, lv])
      (R.iface.Post .giant S e (.list [sv, lv]))) :
    EvalAll Pg env (.call F.giant expr) (fun u cu =>
      ∃ (A : Set (Perm Ω)) (r : Run P₀ .giant S (some L) A) (cb : ℕ),
        AnsC e u A ∧ (cb : ℝ) ≤ r.total R.iface.work ∧
        cu ≤ cArg + cb + u.wt + 1) := by
  refine EvalAll.call_funAll ha fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine hcall.mono fun u cb ⟨A, Labs, r, hLabs, hA, hcb⟩ => ?_
  obtain ⟨sv', lv', L', heq, hl', hLabs⟩ := hLabs
  simp only [Val.list.injEq, List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hL : L' = L := LabValStd.unique hl' hl
  subst hL
  subst hLabs
  refine ⟨A, r, cb, hA, ?_, by omega⟩
  simpa [Iface.excess] using hcb

end GI.Impl
