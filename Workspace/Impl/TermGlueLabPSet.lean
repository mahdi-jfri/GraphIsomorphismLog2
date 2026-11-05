module

public import Workspace.Impl.TermGlueLabPGens
public import Workspace.Impl.TermGlueLabPInv
public import Workspace.Impl.TermGlueLabPE

@[expose] public section

/-!
# The coordinates of the label group: the setup program (step 5)

Step 5 of the label program (proof of Theorem A.23: the coordinates of
Theorem A.20 on the common quotient `A/B(x)`). The setup program computes the context
`[t, U, V, d]` that the matrices and offsets use. On `[gens N*, gens N, [b_j]]`, with `b_j` the
stored generators of the groups `Aut_N(x_i)`:

1. the presentation `M` of `N/N*` (`linAbelianCoordinates`, at `abel`);
2. the coordinate rows `Z_j` of the `b_j` (`linElementCoordinates` mapped, at `mec`);
3. the stacked matrix `[M; Z]` (`append` of the row lists, `tmGLP_enc_stack`);
4. the quotient program on `[M; Z]` (at `quo`): moduli `d` and `V` with `V` unimodular and
   `x ∈ rowspan [M; Z] ↔ d_i ∣ (x V)_i` (`TmGLQOut`);
5. `U = V⁻¹` (`tmGLPInvF`, at `inv`);
6. the context `[t, U, V, d]`.

`[M; Z]` has full column rank since `det M ≠ 0` (the presentation certificate) and
`tmGLQ_stack_inj`; this needs `0 < t`. The result facts are `TmGLPSetOut`; with them `tmGLPE`
gives the coordinates `E` of `A/B(x)`.
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encInt encIntMatrix encPerm encGroup gens FullRankInst fullRankInput)

variable {n : ℕ}

/-! ### The coordinate rows -/

/-- A list related entrywise by "is a coordinate vector of" is the encoding of a matrix. -/
theorem tmGLP_rows_mat {σN bs : List (Perm (Fin n))} {ws : List Val}
    (h : List.Forall₂ (fun b w => ∃ z : Fin σN.length → ℤ, TmGLPCoordOf σN b z ∧ w = linVecVal z)
      bs ws) :
    ∃ Z : Matrix (Fin bs.length) (Fin σN.length) ℤ, Val.list ws = encIntMatrix Z ∧
      ∀ j : Fin bs.length, TmGLPCoordOf σN (bs[j.val]'j.isLt) (Z j) := by
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h
  have hz : ∀ j : Fin bs.length, ∃ z : Fin σN.length → ℤ,
      TmGLPCoordOf σN (bs[j.val]'j.isLt) z ∧ ws[j.val]'(hlen ▸ j.isLt) = linVecVal z :=
    fun j => hget j.val j.isLt (hlen ▸ j.isLt)
  choose Z hZ hZw using hz
  refine ⟨Z, ?_, hZ⟩
  change Val.list ws = .list ((List.finRange bs.length).map fun j => linVecVal (Z j))
  congr 1
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_finRange]
  exact hZw ⟨i, by omega⟩

/-- **The encoding of the stacked matrix** is the append of the row lists. -/
theorem tmGLP_enc_stack {t s : ℕ} (M : Matrix (Fin t) (Fin t) ℤ) (Z : Matrix (Fin s) (Fin t) ℤ) :
    encIntMatrix (tmGLQStack M Z) =
      .list (((List.finRange t).map fun i => linVecVal (M i)) ++
        (List.finRange s).map fun j => linVecVal (Z j)) := by
  change Val.list ((List.finRange (t + s)).map fun i => linVecVal (tmGLQStack M Z i)) = _
  rw [← List.ofFn_eq_map, ← List.ofFn_eq_map, ← List.ofFn_eq_map, List.ofFn_add]
  congr 1
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine congrArg List.ofFn (funext fun i => ?_)
    exact congrArg linVecVal (Fin.append_left (fun i => M i) (fun j => Z j) i)
  · refine congrArg List.ofFn (funext fun i => ?_)
    exact congrArg linVecVal (Fin.append_right (fun i => M i) (fun j => Z j) i)

/-- **The coordinate rows of the stored generators**, by `map` of `linElementCoordinates`. -/
theorem tmGLPZRows_spec (hm : GI.Cited.ConstructiveMembership) {P : Program} {mec ec jm : ℕ}
    (hmec : P.HasAt mec (mapFuns mec ec)) (hec : linElementCoordinatesAt P ec jm hm)
    {Ce De : ℕ} (hEB : ∀ W, linElementBudget hm W ≤ Ce * (W + 2) ^ De)
    (σN bs : List (Perm (Fin n))) (hbs : ∀ b ∈ bs, b ∈ gens σN) :
    FunAll P mec (.list [encGroup σN, .list (bs.map encPerm)]) (fun w c =>
      ∃ Z : Matrix (Fin bs.length) (Fin σN.length) ℤ, w = encIntMatrix Z ∧
        (∀ j : Fin bs.length, TmGLPCoordOf σN (bs[j.val]'j.isLt) (Z j)) ∧
        c ≤ tmGLPItemsC (tmGLPBud Ce De) (Val.list [encGroup σN, .list (bs.map encPerm)]).wt) := by
  have hmono : Monotone (tmGLPBud Ce De) := fun a b h => by unfold tmGLPBud; gcongr
  refine FunAll.mono (tmGLPItems_spec hmec encPerm_injective bs hmono
    (R := fun b w => ∃ z : Fin σN.length → ℤ, TmGLPCoordOf σN b z ∧ w = linVecVal z)
    fun b hb => ?_) fun w c ⟨ws, hw, hws, hc⟩ => ?_
  · have wG : (encGroup σN).wt < (Val.list [encGroup σN, encPerm b]).wt :=
      wt_le_wt_list (by simp)
    have wb : (encPerm b).wt < (Val.list [encGroup σN, encPerm b]).wt := wt_le_wt_list (by simp)
    have hn := tmGLP_n_lt_wt b
    refine FunAll.mono (tmGLP_coord_call hm hec hEB σN wG.le (by omega) b (hbs b hb))
      fun w c ⟨z, hz, hw, hc, _⟩ => ⟨⟨z, hz, hw⟩, hc⟩
  · obtain ⟨Z, hZ, hZc⟩ := tmGLP_rows_mat hws
    exact ⟨Z, hw.trans hZ, hZc, hc⟩

end GI.Impl
