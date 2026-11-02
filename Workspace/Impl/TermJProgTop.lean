import Workspace.Impl.TermJProgNE

/-!
# The top function of the `J`-answer (program)

`tmJTopF`, on `[V, r, w]`: if the label answer `w` is empty, the answer is empty; otherwise
it is the value of `tmJNEF` on `[V, w]`. When the label coset is empty, so is the piece of
`T` above `R r` (`tmGl_cosetT_eq`), so the empty answer is correct.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val encPerm encGroup gens)

/-- On `[V, r, w]`. -/
def tmJTopF (ne : ℕ) : Expr :=
  .ite (.length (arg 2)) (.call ne (mk2 (arg 0) (arg 2))) .nil

/-- **The top function**: the empty answer for an empty label answer, the value of the
function `ne` on `[V, w]` otherwise. -/
theorem tmJ_topF_spec {P : Program} {f ne : ℕ} (hf : P.funs[f]? = some (tmJTopF ne))
    {m : ℕ} (V r : Val) (w : Val) (Q : Val → Prop) {B : ℕ}
    (hw : w = .list [] ∨ ∃ (h0 : Perm (Fin m)) (U : List (Perm (Fin m))),
      w = .list [encPerm h0, encGroup U])
    (hQ0 : w = .list [] → Q (.list []))
    (hne : w ≠ .list [] → FunAll P ne (.list [V, w]) (fun out c => Q out ∧ c ≤ B)) :
    FunAll P f (.list [V, r, w]) (fun out c =>
      Q out ∧ c ≤ 4 * B + 30 * (Val.list [V, r, w]).wt + 100) := by
  refine FunAll.intro hf ?_
  unfold tmJTopF
  obtain ⟨X, hX⟩ : ∃ X, (Val.list [V, r, w]).wt = X := ⟨_, rfl⟩
  rw [hX]
  have wV : V.wt < X := hX ▸ wt_le_wt_list (by simp)
  have ww : w.wt < X := hX ▸ wt_le_wt_list (by simp)
  rcases hw with rfl | ⟨h0, U, rfl⟩
  · have a2 := Det.arg' (P := P) (vs := [V, r, .list []]) (rest := []) (j := 2)
      (v := .list []) rfl
    refine EvalAll.mono (Det.ite_zero (Det.length a2) Det.nil) fun u c h => ⟨?_, ?_⟩
    · rw [h.1]; exact hQ0 rfl
    · have h2 := h.2
      have : (Val.list []).wt = 4 := by simp [Val.wt, GI.Lang.cellWt, GI.Machine.len_zero]
      simp only [List.length_nil] at h2
      rw [hX] at h2
      omega
  · have a0 := Det.arg' (P := P) (vs := [V, r, .list [encPerm h0, encGroup U]]) (rest := [])
      (j := 0) (v := V) rfl
    have a2 := Det.arg' (P := P) (vs := [V, r, .list [encPerm h0, encGroup U]]) (rest := [])
      (j := 2) (v := .list [encPerm h0, encGroup U]) rfl
    have hc := Det.length a2
    have hn := hne (by simp)
    have hcall := tmJ_lastCall (Det.mk2 a0 a2) hn
    refine EvalAll.ite hc (fun _ _ h => ⟨_, h.1⟩) fun y cc h => ?_
    obtain ⟨h1, h2⟩ := h
    injection h1 with h1
    subst h1
    rw [if_neg (by simp)]
    refine hcall.wt_lt.mono fun u c hu => ⟨hu.1.1, ?_⟩
    have := hu.1.2
    have := hu.2
    have := wt_list2_le V (.list [encPerm h0, encGroup U])
    have := wt_nat_le 2
    have := wt_nat_le 0
    simp only [List.length_cons, List.length_nil] at h2
    rw [hX] at h2
    omega

end GI.Impl
