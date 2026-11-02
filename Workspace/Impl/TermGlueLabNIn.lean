import Workspace.Impl.TermGlueLabNVec
import Workspace.Impl.TermCosetTop

/-!
# The label driver: facts about the input

Proof of Theorem A.23, the composition of the label driver. The driver must prove
the hypotheses of its callees from the input of `TmGLPNeSpec`. This file gives the ones that are
not a direct reading of the input.

* `tmGLN_w_cons`: a canonical answer `w ≠ []` of the residual set is `[τ, U]` with `τ` in the
  set and `|U| ≤ m²`.
* `tmGLN_row_iso`: when the residual set holds `τ`, every row `x_j` is `H`-isomorphic to some
  row `y_l`. The program-aligned target `y'` has the types of `x` (`tmGLN_align_types`), so
  `x_j` lies in the `N`-orbit of some `y'_l = y_l^{(y l)⁻¹}`, and `y l ∈ H`.
* The sizes `k`, `q`, `m` are below the weight of the input (`tmGLN_k_lt`, `tmGLN_q_lt`,
  `tmGLN_m_lt`), so the contracts' size hypotheses hold at every argument bound.
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Paper GI.Lang Equiv
open GI.Cited (Val encPerm encGroup gens)

attribute [local instance] stringRAct

/-- **A nonempty canonical answer.** -/
theorem tmGLN_w_cons {m : ℕ} {w : Val} {A : Set (Perm (Fin m))}
    (hw : AnsC (Equiv.refl (Fin m)) w A) (hne : w ≠ .list []) :
    ∃ (τ : Perm (Fin m)) (U : List (Perm (Fin m))), w = .list [encPerm τ, encGroup U] ∧
      U.length ≤ m ^ 2 ∧ τ ∈ A := by
  have hw' := hw
  rcases hw' with ⟨rfl, -⟩ | ⟨x, gs, rfl, hl, -⟩
  · exact absurd rfl hne
  · refine ⟨x, gs, rfl, hl, ?_⟩
    have hA := tmCs_ansC_cons hw rfl
    rw [hA]
    exact ⟨1, (gens gs).one_mem, mul_one x⟩

section Iso

variable {Ω C : Type} {Pp : Params} {S : State Ω C} {L : GiantLabels S}

/-- **Every row of `x` has an isomorphic row of `y`**, when the residual set holds `τ` and `y`
is a lift of `τ` with all rows in `H`. -/
theorem tmGLN_row_iso {I : RowTerminal Pp S L} {r τ : Perm I.B} (hτ : τ ∈ tmGlRes I r)
    {y : Fin L.q → Perm I.B} (hy : cleanRowPerm I.e y ∈ S.domGroup) (hy0 : y I.i0 = τ)
    (hyH : ∀ i, y i ∈ I.Hb) (j : Fin L.q) :
    ∃ l : Fin L.q, (Iso I.Hb (rowTuple I.e S.x j) (rowTuple I.e S.y l)).Nonempty := by
  have ht := tmGLN_align_types hτ hy hy0
  have hmem : orbitN I.Nb (rowTuple I.e S.x j) ∈
      types I.Nb (rowAct (fun i => (y i)⁻¹) 1 (rowTuple I.e S.y)) := by
    rw [ht]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)
  obtain ⟨l, -, hl⟩ := Multiset.mem_map.1 hmem
  have hx : rowTuple I.e S.x j ∈ orbitN I.Nb (rowTuple I.e S.x j) :=
    ⟨1, I.Nb.one_mem, act_one _⟩
  rw [← hl] at hx
  obtain ⟨n, hn, hnx⟩ := hx
  have hy' : rowAct (fun i => (y i)⁻¹) 1 (rowTuple I.e S.y) l =
      rowTuple I.e S.y l ↼ (y l)⁻¹ := rfl
  rw [hy'] at hnx
  refine ⟨l, ⟨n⁻¹ * y l, I.Hb.mul_mem (I.Hb.inv_mem (I.Nb_le hn)) (hyH l), ?_⟩⟩
  rw [← act_act, ← hnx, act_act_inv, act_inv_act]

end Iso

/-! ### Sizes below the input weight -/

theorem tmGLN_k_lt {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {sv : Val}
    {S : State Ω C} (hsv : Canon e c sv S) : k < sv.wt := by
  obtain ⟨gv, dv, xv, yv, hv, rv, -, hd, -, -, -, -, hsv'⟩ := hsv.val
  have hd' : dv = indVal e S.dom := DomVal.eq_indVal hd
  have hk1 : k < (indVal e S.dom).wt := by
    have := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (indF e S.dom i))
    simpa [indVal, encFun] using this
  have hk2 : (indVal e S.dom).wt < sv.wt := by
    rw [hsv', ← hd']; exact wt_le_wt_list (by simp)
  omega

theorem tmGLN_q_lt {Ω C : Type} {n q m : ℕ} (e : Ω ≃ Fin n) (S : State Ω C)
    (E : Fin m × Fin q ≃ S.dom) : q < (coordsVal e S E).wt := by
  have := length_lt_wt_list ((List.finRange q).map fun j =>
    natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin n) : ℕ)))
  simpa [coordsVal] using this

theorem tmGLN_m_lt {m : ℕ} (U : List (Perm (Fin m))) : m < (encGroup U).wt := by
  have h1 : m < (encPerm (1 : Perm (Fin m))).wt := by
    have := length_lt_wt_list ((List.finRange m).map fun i => Val.nat ((1 : Perm (Fin m)) i))
    simpa [encPerm] using this
  have h2 : (encPerm (1 : Perm (Fin m))).wt < (Val.list ((1 :: U).map encPerm)).wt :=
    wt_le_wt_list (by simp)
  have h3 : (Val.list ((1 :: U).map encPerm)).wt < (encGroup U).wt :=
    wt_le_wt_list (by simp [encGroup])
  omega

end GI.Impl
