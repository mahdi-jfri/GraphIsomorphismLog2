module

public import Workspace.Impl.ScriptRun

@[expose] public section

/-!
# Runs of a script that is a sequence of scripts

The script of an aggregation round is `certScript.bind (fun _ => compScript.bind (fun _ =>
itemsScript))`. The program runs the three parts one after the other, each through the script
runner, and so gets one run (`Exec`) of each part. This file glues runs of the parts into a run
of the whole script: `asExecBind` turns a run of `s` with result `a` and a run of `f a` into a
run of `s.bind f`. Its calls are the calls of the first run followed by the calls of the second
(`asExecBind_calls`), so the costs add up (`asExecBind_cost`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm

variable {P : Params}

/-- **A run of `s.bind f`** from a run of `s` with result `a` and a run of `f a`. -/
noncomputable def asExecBind {α β : Type} (f : α → Script β) {b : β} :
    (s : Script α) → {a : α} → Exec P s a → Exec P (f a) b → Exec P (s.bind f) b
  | .done _, _, .done _, e₂ => e₂
  | .ask _ _ k, _, .ask r e₁, e₂ => Exec.ask r (asExecBind f (k _) e₁ e₂)

theorem asExecBind_calls {α β : Type} (f : α → Script β) {b : β} :
    ∀ (s : Script α) {a : α} (e₁ : Exec P s a) (e₂ : Exec P (f a) b),
      (asExecBind f s e₁ e₂).calls = e₁.calls ++ e₂.calls
  | .done _, _, .done _, e₂ => rfl
  | .ask _ _ k, _, .ask r e₁, e₂ => by
    show _ :: (asExecBind f (k _) e₁ e₂).calls = (_ :: e₁.calls) ++ e₂.calls
    rw [asExecBind_calls f (k _) e₁ e₂, List.cons_append]

theorem asExecBind_cost (I : Iface) {α β : Type} (f : α → Script β) {b : β} (s : Script α)
    {a : α} (e₁ : Exec P₀ s a) (e₂ : Exec P₀ (f a) b) :
    I.execCost (asExecBind f s e₁ e₂) = I.execCost e₁ + I.execCost e₂ := by
  simp only [Iface.execCost, asExecBind_calls, List.map_append, List.sum_append]

end GI.Impl
