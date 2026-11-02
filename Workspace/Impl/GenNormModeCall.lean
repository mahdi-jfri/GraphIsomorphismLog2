import Workspace.Impl.GenNormCall
import Workspace.Impl.GenNormChild

/-! # Calling the mode selected by the normalization orbit test -/
namespace GI.Impl
open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

/-- Select the recursive procedure using the computed transitivity bit. -/
def normModeCall (F : Funs) (sv lv mode : Expr) : Expr :=
  .ite mode (.call F.giant (mk2 sv lv)) (.call F.cont sv)

/-- Both branches return a run on the supplied normalization labels. -/
theorem normModeCall_spec (R : Rest) {Pg : Program} {F : Funs} {env : List Val}
    {Ω C : Type} {n : ℕ} {en : Ω ≃ Fin n} {S : State Ω C} {L : SuppliedLabels S}
    {sv lv : Val} {b : Bool} {se le be : Expr} {cs cl cb : ℕ}
    (hs : Det Pg env se sv cs) (hl : Det Pg env le lv cl)
    (hb : Det Pg env be (boolVal b) cb) (hL : LabValStd en S lv L)
    (hcall : FunAll Pg (F.get (normMode b)) (if b then .list [sv, lv] else sv)
      (R.iface.Post (normMode b) S en (if b then .list [sv, lv] else sv))) :
    EvalAll Pg env (normModeCall F se le be) (fun u cost =>
      ∃ (A : Set (Perm Ω)) (r : Run P₀ (normMode b) S ((normMode b).labels L) A) (c : ℕ),
        AnsC en u A ∧ (c : ℝ) ≤ r.total R.iface.work ∧
        cost ≤ cb + cs + cl + 5 * (sv.wt + lv.wt + 10) + c + 2 * u.wt + 2) := by
  unfold normModeCall
  refine EvalAll.ite hb (fun _ _ h => ⟨b.toNat, h.1⟩) fun y cm hy => ?_
  obtain ⟨hy, hcm⟩ := hy
  change Val.nat y = boolVal b at hy
  have hy' : y = b.toNat := Val.nat.inj hy
  subst hy'
  cases b with
  | false =>
    simp only [Bool.toNat_false, if_pos rfl]
    change FunAll Pg F.cont sv (R.iface.Post .cont S en sv) at hcall
    refine (call_child R.iface hs hcall).mono fun u cu hu => ?_
    obtain ⟨A, r, c, hA, hc, hcu⟩ := hu
    exact ⟨A, r, c, hA, hc, by omega⟩
  | true =>
    simp only [Bool.toNat_true, Nat.one_ne_zero, if_false]
    change FunAll Pg F.giant (.list [sv, lv]) (R.iface.Post .giant S en (.list [sv, lv])) at hcall
    refine (normCall_giant R (Det.mk2 hs hl) hL hcall).mono fun u cu hu => ?_
    obtain ⟨A, r, c, hA, hc, hcu⟩ := hu
    have hw := wt_list2_le sv lv
    exact ⟨A, r, c, hA, hc, by omega⟩

end GI.Impl
