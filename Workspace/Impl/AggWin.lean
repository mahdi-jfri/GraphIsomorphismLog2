module

public import Workspace.Impl.AggClos
public import Workspace.Impl.FreshMath

@[expose] public section

/-!
# The value of a window call

A window call of the certificate phase asks `Continue` on the state
`windowCall S N V hV z τ`: the lift of the kernel `N` on the lifted window, with the colors
`z` and `z ∘ τ` of the domain, extended by one extra color `none` off the domain
(`Workspace/Algorithm/Certificates.lean`). The script runner needs a canonical value of this state
(`Canon`): color codes below `2k`. The colors live in `Option C`, which has one color more than
the parent's, so the parent's codes do not serve. As at a fresh call
(`Workspace/Impl/FreshMath.lean`), the program compresses them: it lists the raw codes
(`0` off the domain, the parent's code plus `1` on it) of both colorings, and replaces each raw
code by the position of its first occurrence in that list.

* `winRawX`, `winRawY`: the raw codes at the positions, computed from the domain indicator,
  the parent's codes of `z`, and the positions `a` of a lift of `τ`.
* `winCode`: the compressed code, injective (`winCode_injective`).
* `canon_window`: the value `[k, gv, dv, x', y', hv, [], 0, 2, N]` is a canonical value of the
  window state, for a group value `gv` of the lift of `N` with at most `k²` generators, the window
  indicator `dv`, and the parent's hierarchy value `hv`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)
open scoped Pointwise

variable {k : ℕ} {Ω C : Type}

/-- The raw code of a color of the window: `0` for the extra color, the parent's code plus `1`
otherwise. Injective when the parent's code is. -/
def optCode (c : C → ℕ) : Option C → ℕ
  | none => 0
  | some a => c a + 1

theorem optCode_injective {c : C → ℕ} (hc : Function.Injective c) :
    Function.Injective (optCode c) := by
  rintro (_ | a) (_ | b) h <;> simp only [optCode] at h
  · rfl
  · omega
  · omega
  · exact congrArg some (hc (by omega))

section Win

variable [DecidableEq Ω] (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) [Fintype S.dom]
  (z : Ω → C) (a : Perm (Fin k))

open Classical in
/-- The raw codes of the first coloring `liftColor z` at the positions. -/
noncomputable def winRawX (i : Fin k) : ℕ := if e.symm i ∈ S.dom then c (z (e.symm i)) + 1 else 0

open Classical in
/-- The raw codes of the second coloring `liftColor (z ∘ τ)`, with `a` the positions of a lift
of `τ`. -/
noncomputable def winRawY (i : Fin k) : ℕ :=
  if e.symm i ∈ S.dom then c (z (e.symm (a i))) + 1 else 0

/-- The list of the raw codes of both colorings. -/
noncomputable def winList : List ℕ :=
  (List.finRange k).map (winRawX e c S z) ++ (List.finRange k).map (winRawY e c S z a)

theorem length_winList : (winList e c S z a).length = 2 * k := by
  simp [winList]; ring

/-- **The compressed code of the window colors.** -/
noncomputable def winCode : Option C → ℕ := cmpCode (optCode c) (winList e c S z a) k

theorem winCode_injective (hc : Function.Injective c) :
    Function.Injective (winCode e c S z a) :=
  cmpCode_injective (optCode_injective hc) (length_winList e c S z a).le

/-- The compressed codes of the first coloring. -/
noncomputable def winCodesX : List ℕ :=
  (List.finRange k).map fun i => posOf (winList e c S z a) (winRawX e c S z i)

/-- The compressed codes of the second coloring. -/
noncomputable def winCodesY : List ℕ :=
  (List.finRange k).map fun i => posOf (winList e c S z a) (winRawY e c S z a i)

variable {e c S z a}

/-- The raw code of the first coloring at a position is its `optCode`. -/
theorem winRawX_eq (i : Fin k) :
    winRawX e c S z i = optCode c (liftColor S (dstr S z) (e.symm i)) := by
  classical
  unfold winRawX liftColor
  by_cases h : e.symm i ∈ S.dom
  · simp [h, optCode, dstr]
  · simp [h, optCode]

/-- The raw code of the second coloring at a position is its `optCode`, when `a` is the positions
of a lift `g ∈ G` of `τ`. -/
theorem winRawY_eq {g : Perm Ω} (hg : g ∈ S.G) (ha : toFin e g = a) (i : Fin k) :
    winRawY e c S z a i =
      optCode c (liftColor S (dstr S z ∘ S.domHom ⟨g, hg⟩) (e.symm i)) := by
  classical
  unfold winRawY liftColor
  by_cases h : e.symm i ∈ S.dom
  · simp only [h, dif_pos, if_true, optCode, Function.comp_apply, dstr]
    congr 2
    rw [State.domHom_apply, ← ha]
    simp [toFin, Equiv.permCongrHom, Equiv.permCongr_apply]
  · simp [h, optCode]

theorem winRawX_mem (i : Fin k) : winRawX e c S z i ∈ winList e c S z a :=
  List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange i))

theorem winRawY_mem (i : Fin k) : winRawY e c S z a i ∈ winList e c S z a :=
  List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange i))

/-- The values of the compressed colorings. -/
theorem colorVal_winX :
    ColorVal e (winCode e c S z a) (natList (winCodesX e c S z a)) (liftColor S (dstr S z)) := by
  unfold ColorVal
  simp only [encFun, natList, winCodesX, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, winCode]
  have hm : optCode c (liftColor S (dstr S z) (e.symm i)) ∈ winList e c S z a :=
    winRawX_eq (e := e) (c := c) (S := S) (z := z) i ▸ winRawX_mem i
  rw [cmpCode_of_mem hm, ← winRawX_eq]

theorem colorVal_winY {g : Perm Ω} (hg : g ∈ S.G) (ha : toFin e g = a) :
    ColorVal e (winCode e c S z a) (natList (winCodesY e c S z a))
      (liftColor S (dstr S z ∘ S.domHom ⟨g, hg⟩)) := by
  unfold ColorVal
  simp only [encFun, natList, winCodesY, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, winCode]
  have hm : optCode c (liftColor S (dstr S z ∘ S.domHom ⟨g, hg⟩) (e.symm i)) ∈ winList e c S z a :=
    winRawY_eq (e := e) (c := c) (S := S) (z := z) hg ha i ▸ winRawY_mem i
  rw [cmpCode_of_mem hm, ← winRawY_eq hg ha]

/-- The compressed codes are below `2k`. -/
theorem winCode_lt_X (v : Ω) : winCode e c S z a (liftColor S (dstr S z) v) < 2 * k := by
  have h := winRawX_eq (e := e) (c := c) (S := S) (z := z) (e v)
  simp only [Equiv.symm_apply_apply] at h
  have hm : optCode c (liftColor S (dstr S z) v) ∈ winList e c S z a := h ▸ winRawX_mem (e v)
  rw [winCode, cmpCode_of_mem hm, ← length_winList e c S z a]
  exact posOf_lt hm

theorem winCode_lt_Y {g : Perm Ω} (hg : g ∈ S.G) (ha : toFin e g = a) (v : Ω) :
    winCode e c S z a (liftColor S (dstr S z ∘ S.domHom ⟨g, hg⟩) v) < 2 * k := by
  have h := winRawY_eq (e := e) (c := c) (S := S) (z := z) hg ha (e v)
  simp only [Equiv.symm_apply_apply] at h
  have hm : optCode c (liftColor S (dstr S z ∘ S.domHom ⟨g, hg⟩) v) ∈ winList e c S z a :=
    h ▸ winRawY_mem (e v)
  rw [winCode, cmpCode_of_mem hm, ← length_winList e c S z a]
  exact posOf_lt hm

end Win

/-! ### The window value -/

/-- **The value of a window call**: `[k, gv, dv, x', y', hv, [], 0, 2, N]`. -/
def winVal' (k : ℕ) (gv dv xv yv hv : Val) (N : ℕ) : Val :=
  .list [.nat k, gv, dv, xv, yv, hv, .list [], boolVal false, .nat 2, .nat N]

variable [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} [Fintype S.dom]

/-- **The window value is canonical.** Let the parent have a canonical value with hierarchy
value `hv`. Let `gv` be a group value of the lift of `N` with at most `k²` generators, `dv` the
indicator of the lifted window, and `a` the positions of a lift `g ∈ G` of `τ`. Then the window
value with the compressed codes is a canonical value of the window state. -/
theorem canon_window {sv : Val} (hS : Canon e c sv S) {hv : Val} (hh : HierValC e hv S.hier)
    {N : Subgroup (Perm S.dom)} {V : Finset S.dom}
    (hV : GI.Algorithm.Invariant N (V : Set S.dom)) (z : Ω → C) {g : Perm Ω} (hg : g ∈ S.G)
    {a : Perm (Fin k)} (ha : toFin e g = a) {gv dv : Val}
    (hgv : GroupValC k gv (groupFin e (S.liftGroup N)))
    (hdv : DomVal e dv (Subtype.val '' (V : Set S.dom))) :
    Canon e (winCode e c S z a)
      (winVal' k gv dv (natList (winCodesX e c S z a)) (natList (winCodesY e c S z a)) hv S.N)
      (windowCall S N V hV (dstr S z) (S.domHom ⟨g, hg⟩)) where
  val := ⟨gv, dv, _, _, hv, .list [], hgv, hdv, colorVal_winX, colorVal_winY hg ha, hh, rfl, rfl⟩
  colors v := ⟨winCode_lt_X v, winCode_lt_Y hg ha v⟩
  fits := hS.fits
  small := ⟨hS.small.1, hS.small.2.1, fun R hR => by cases hR⟩

end GI.Impl

/-! ### The window calls are allowed calls -/

namespace GI.Impl

open GI.Algorithm GI.Assembly

/-- **A charged call of an aggregation round may be made**: it is `Good` for `Continue`, and its
measure is below that of the round (the argument of `exists_run_aux`, case `aggregate`: the
call has the same `N`, a domain at most as large, and if it is as large then it is intransitive
or its `σ` drops by `κ`). -/
theorem chargedCall_good_mlt {Ω C C' : Type} [Finite Ω] {S : State Ω C} {T : State Ω C'}
    (hgood : Good P₀ .giant S) (hch : ChargedCall P₀ S T) :
    Good P₀ .cont T ∧ MLt (measure P₀ .cont T) (measure P₀ .giant S) := by
  obtain ⟨hN, hsN, htr, hth, hhi, -⟩ := hgood
  have hP := P₀_terminating
  have hpos := size_pos_of_large hth
  have hκ := P₀_κ
  have htrS := trInd_of S htr
  have hTN : T.N = S.N := hch.N_eq
  have hsz : T.size ≤ S.size := size_le_of_subset hch.sub
  have key : T.size < S.size ∨ trInd T = 0 ∨ T.sigma P₀.κ < S.sigma P₀.κ := by
    by_cases hlt : T.size < S.size
    · exact Or.inl hlt
    by_cases htrT : T.Transitive
    · right; right
      have heq : T.size = S.size := by omega
      obtain ⟨v, hv⟩ : T.dom.Nonempty := by
        have : 0 < T.size := heq ▸ hpos
        exact Set.nonempty_coe_sort.1 (Nat.card_pos_iff.1 this).1
      rcases hch.types v hv with horb | hσ
      · exfalso
        have h1 := size_le_orb htrT hv
        have h2 : (T.size : ℝ) ≤ P₀.θ * S.size :=
          (by exact_mod_cast h1 : (T.size : ℝ) ≤ (Nat.card (orb T.G v) : ℝ)).trans horb
        rw [heq] at h2
        have h3 : (0 : ℝ) < S.size := by exact_mod_cast hpos
        nlinarith [hP.θ_lt]
      · rw [State.sigma_eq_point P₀.κ htrT hv]
        omega
    · exact Or.inr (Or.inl (trInd_of_not _ htrT))
  have htrT := trInd_le T
  have hinvT : T.HierInv := by
    show HierInv T.G T.dom T.hier
    rw [hch.hier_eq]
    exact HierInv.mono hhi hch.le hch.sub
  exact ⟨⟨show P₀.N₀ < T.N by omega, by omega, hinvT⟩, by mlt_tac⟩

end GI.Impl
