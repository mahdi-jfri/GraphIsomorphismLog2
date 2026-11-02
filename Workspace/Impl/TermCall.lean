import Workspace.Impl.FreshMath
import Workspace.Impl.ScriptRun
import Workspace.Impl.ScriptCont

/-!
# The calls of the row terminal (T1)

The row terminal (Theorem A.23, `RowTerminal.script`) asks `Solve` on two strings of one row
under a group `K ≤ Sym(B)`, with `B = Fin m` the row coordinates: first the `(2q)²` `N`-tests
(`typeCall`), then the `q²` cosets `Iso_H(x_i, y_j)` (`cosetCall`). Each call is the state
`rowState K z w`, a fresh state on all of `B` with no hierarchy and no row record.

This file gives what a program needs to ask these calls:

* the order of the calls (`tmTests`, `tmCosets`): the program asks them in this order, and
  `tmWithOrder` puts the same order into the terminal data, so that the script of the
  data asks exactly the program's calls;
* the value of a call (`tmRowVal`) and its proof of canonicity (`tm_canon_row`): the colors of
  the two strings are renamed to the position of their first occurrence in the list of the codes
  of both strings (`cmpCode`, as for a fresh phase), so they are below `2m`;
* the call is allowed: `Solve` needs nothing (`Good`), and the measure drops because a row has
  fewer than `N` points (`tm_mlt_row`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

/-! ### The order of the calls -/

/-- The `2q` rows: the rows of `x`, then the rows of `y`. -/
def tmRows (q : ℕ) : List (Fin q ⊕ Fin q) :=
  (List.finRange q).map Sum.inl ++ (List.finRange q).map Sum.inr

theorem tmRows_nodup (q : ℕ) : (tmRows q).Nodup := by
  unfold tmRows
  refine List.Nodup.append ((List.nodup_finRange q).map Sum.inl_injective)
    ((List.nodup_finRange q).map Sum.inr_injective) ?_
  intro a ha hb
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
  obtain ⟨j, -, h⟩ := List.mem_map.1 hb
  cases h

theorem mem_tmRows {q : ℕ} (a : Fin q ⊕ Fin q) : a ∈ tmRows q := by
  unfold tmRows
  rcases a with i | i
  · exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange i))
  · exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange i))

/-- **The order of the `N`-tests**: every ordered pair of the `2q` rows, the first row in the
outer loop. -/
def tmTests (q : ℕ) : List ((Fin q ⊕ Fin q) × (Fin q ⊕ Fin q)) := tmRows q ×ˢ tmRows q

theorem tmTests_nodup (q : ℕ) : (tmTests q).Nodup :=
  (tmRows_nodup q).product (tmRows_nodup q)

theorem mem_tmTests {q : ℕ} (ac : (Fin q ⊕ Fin q) × (Fin q ⊕ Fin q)) : ac ∈ tmTests q :=
  List.mem_product.2 ⟨mem_tmRows _, mem_tmRows _⟩

/-- **The order of the coset calls**: every pair of a row of `x` and a row of `y`. -/
def tmCosets (q : ℕ) : List (Fin q × Fin q) := List.finRange q ×ˢ List.finRange q

theorem tmCosets_nodup (q : ℕ) : (tmCosets q).Nodup :=
  (List.nodup_finRange q).product (List.nodup_finRange q)

theorem mem_tmCosets {q : ℕ} (ij : Fin q × Fin q) : ij ∈ tmCosets q :=
  List.mem_product.2 ⟨List.mem_finRange _, List.mem_finRange _⟩

/-- The terminal data with the call order of the program. Only the two order fields change, so
`tmWithOrder` keeps every theorem about the data (`RowTerminal.exact` holds for any order). -/
def tmWithOrder {Ω C : Type} {P : Params} {S : State Ω C} {L : GiantLabels S}
    (I : RowTerminal P S L) : RowTerminal P S L :=
  { I with
    tests := tmTests L.q
    tests_nodup := tmTests_nodup L.q
    mem_tests := mem_tmTests
    cosets := tmCosets L.q
    cosets_nodup := tmCosets_nodup L.q
    mem_cosets := mem_tmCosets }

theorem tmWithOrder_script {Ω C : Type} {P : Params} {S : State Ω C}
    {L : GiantLabels S} (I : RowTerminal P S L) :
    (tmWithOrder I).script =
      (Script.table I.typeCall (tmTests L.q)).bind fun TN =>
        (Script.table I.cosetCall (tmCosets L.q)).bind fun TH =>
          Script.done (I.assemble TN TH) := rfl

/-! ### The value of a call -/

variable {C : Type} {m : ℕ}

/-- The codes of the two strings of a call `rowState K z w`: those of `w` (the state's `x`),
then those of `z` (the state's `y`). -/
def tmCodeList (c : C → ℕ) (z w : Fin m → C) : List ℕ :=
  (List.finRange m).map (fun b => c (w b)) ++ (List.finRange m).map (fun b => c (z b))

theorem length_tmCodeList (c : C → ℕ) (z w : Fin m → C) :
    (tmCodeList c z w).length = 2 * m := by
  simp [tmCodeList]; ring

/-- The color code of a call: the position of the first occurrence in `tmCodeList`. -/
def tmCode (c : C → ℕ) (z w : Fin m → C) : C → ℕ := cmpCode c (tmCodeList c z w) m

theorem tmCode_injective {c : C → ℕ} (hc : Function.Injective c) (z w : Fin m → C) :
    Function.Injective (tmCode c z w) :=
  cmpCode_injective hc (length_tmCodeList c z w).le

/-- The compressed codes of one string `u ∈ {z, w}`. -/
def tmCmp (c : C → ℕ) (z w u : Fin m → C) : List ℕ :=
  (List.finRange m).map fun b => posOf (tmCodeList c z w) (c (u b))

/-- **The value of the call `rowState (gens gs) z w`.** -/
def tmRowVal (gs : List (Perm (Fin m))) (c : C → ℕ) (z w : Fin m → C) : Val :=
  freshVal m (encGroup gs) (natList (tmCmp c z w w)) (natList (tmCmp c z w z)) (.list [])

theorem groupFin_refl (G : Subgroup (Perm (Fin m))) : groupFin (Equiv.refl (Fin m)) G = G := by
  ext g
  simp only [groupFin, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    convert hh using 1
  · intro hg
    exact ⟨g, hg, by ext; rfl⟩

theorem mem_tmCodeList_w (c : C → ℕ) (z w : Fin m → C) (b : Fin m) :
    c (w b) ∈ tmCodeList c z w :=
  List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange b))

theorem mem_tmCodeList_z (c : C → ℕ) (z w : Fin m → C) (b : Fin m) :
    c (z b) ∈ tmCodeList c z w :=
  List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange b))

theorem tm_colorVal (c : C → ℕ) (z w u : Fin m → C)
    (hu : ∀ b, c (u b) ∈ tmCodeList c z w) :
    ColorVal (Equiv.refl (Fin m)) (tmCode c z w) (natList (tmCmp c z w u)) u := by
  unfold ColorVal
  simp only [encFun, natList, tmCmp, List.map_map, Equiv.refl_symm, Equiv.refl_apply]
  congr 1
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply, tmCode]
  exact congrArg Val.nat (cmpCode_of_mem (hu b)).symm

theorem tmCode_lt (c : C → ℕ) (z w : Fin m → C) {col : C} (h : c col ∈ tmCodeList c z w) :
    tmCode c z w col < 2 * m := by
  rw [tmCode, cmpCode_of_mem h, ← length_tmCodeList c z w]
  exact posOf_lt h

/-- **The value of a call is canonical** for the identity numbering of `Fin m` and the code
`tmCode`. -/
theorem tm_canon_row (gs : List (Perm (Fin m))) (hl : gs.length ≤ m ^ 2) (c : C → ℕ)
    (z w : Fin m → C) :
    Canon (Equiv.refl (Fin m)) (tmCode c z w) (tmRowVal gs c z w) (rowState (gens gs) z w) where
  val := by
    refine ⟨encGroup gs, _, _, _, .list [], .list [], ⟨gs, rfl, ?_, hl⟩, domVal_univ _,
      tm_colorVal c z w w (mem_tmCodeList_w c z w),
      tm_colorVal c z w z (mem_tmCodeList_z c z w), ⟨[], rfl, List.Forall₂.nil⟩, rfl, ?_⟩
    · exact (groupFin_refl _).symm
    · simp [tmRowVal, freshVal, rowState]
  colors a := ⟨tmCode_lt c z w (mem_tmCodeList_w c z w a), tmCode_lt c z w (mem_tmCodeList_z c z w a)⟩
  fits := by simp [rowState]
  small := smallInv_nil rfl fun R hR => by cases hR

/-- **A row call is below the giant step**: a row has fewer than `N` points. -/
theorem tm_mlt_row {Ω C' : Type} {S : State Ω C'} {B : Type} [Fintype B]
    (K : Subgroup (Perm B)) (z w : B → C) (hB : Fintype.card B < S.N) :
    MLt (measure P₀ .solve (rowState K z w)) (measure P₀ .giant S) := by
  rw [mlt_iff]
  left
  simp only [GI.Algorithm.measure, major, rowState_size]
  exact hB

/-! ### Unrolling a table of calls

A step function asks the calls of `Script.table st l` one at a time and keeps the answers so
far. `tmTabFrom st l acc K` is the rest of the script `(table st l₀).bind K` after the answers
`acc` (the latest first): the remaining calls `l`, then `K` on the table that the answers give
(`tmUpd`). -/

section Table

variable {ι : Type} [DecidableEq ι] {Ω' C' : Type} {β : Type}

/-- The table of the answers `acc`, the latest first, over `f`. -/
def tmUpd (f : ι → Set (Perm Ω')) : List (ι × Set (Perm Ω')) → ι → Set (Perm Ω')
  | [] => f
  | p :: ps => Function.update (tmUpd f ps) p.1 p.2

theorem tmUpd_update (f : ι → Set (Perm Ω')) (i : ι) (A : Set (Perm Ω')) :
    ∀ acc : List (ι × Set (Perm Ω')), tmUpd (Function.update f i A) acc = tmUpd f (acc ++ [(i, A)])
  | [] => rfl
  | p :: ps => by simp only [tmUpd, List.cons_append, tmUpd_update f i A ps]

/-- The rest of a table script after the answers `acc`. -/
def tmTabFrom (st : ι → State Ω' C') (l : List ι) (acc : List (ι × Set (Perm Ω')))
    (K : (ι → Set (Perm Ω')) → Script β) : Script β :=
  (Script.table st l).bind fun f => K (tmUpd f acc)

theorem tmTabFrom_start (st : ι → State Ω' C') (l : List ι) (K : (ι → Set (Perm Ω')) → Script β) :
    (Script.table st l).bind K = tmTabFrom st l [] K := rfl

/-- One more call: ask `st i`, and keep its answer. -/
theorem tmTabFrom_cons (st : ι → State Ω' C') (i : ι) (l : List ι)
    (acc : List (ι × Set (Perm Ω'))) (K : (ι → Set (Perm Ω')) → Script β) :
    tmTabFrom st (i :: l) acc K =
      Script.ask .solve (st i) fun A => tmTabFrom st l (acc ++ [(i, A)]) K := by
  simp only [tmTabFrom, Script.table, Script.bind]
  congr 1
  funext A
  rw [scr_bind_assoc]
  simp only [Script.bind, tmUpd_update]

/-- No call left: continue with the table of the answers. -/
theorem tmTabFrom_nil (st : ι → State Ω' C') (acc : List (ι × Set (Perm Ω')))
    (K : (ι → Set (Perm Ω')) → Script β) :
    tmTabFrom st [] acc K = K (tmUpd (fun _ => ∅) acc) := rfl

/-- The value of `tmUpd` at a key that occurs in the answers. -/
theorem tmUpd_of_mem (f : ι → Set (Perm Ω')) {g : ι → Set (Perm Ω')} :
    ∀ (acc : List (ι × Set (Perm Ω'))), (∀ p ∈ acc, p.2 = g p.1) →
      ∀ i ∈ acc.map Prod.fst, tmUpd f acc i = g i
  | [], _, _, h => absurd h List.not_mem_nil
  | p :: ps, hacc, i, hi => by
    simp only [tmUpd]
    by_cases hip : i = p.1
    · subst hip
      rw [Function.update_self]
      exact hacc p List.mem_cons_self
    · rw [Function.update_of_ne hip]
      refine tmUpd_of_mem f ps (fun q hq => hacc q (List.mem_cons_of_mem _ hq)) i ?_
      rcases List.mem_cons.1 hi with h | h
      · exact absurd h hip
      · exact h

/-- **Exact answers give the exact table**: if the answers are those of the calls `st i` for
every `i` of a complete list, the table is `fun i => (st i).answer`. -/
theorem tmUpd_exact (f : ι → Set (Perm Ω')) (st : ι → State Ω' C') (l : List ι)
    (hl : ∀ i, i ∈ l) :
    tmUpd f (l.map fun i => (i, (st i).answer)) = fun i => (st i).answer := by
  funext i
  refine tmUpd_of_mem f _ (g := fun i => (st i).answer) ?_ i ?_
  · intro p hp
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
    rfl
  · simp only [List.map_map, Function.comp_def, List.map_id']
    exact hl i

end Table

/-! ### The terminal script in unrolled form -/

section Script

variable {Ω C' : Type} {P : Params} {S : State Ω C'} {L : GiantLabels S}

/-- **The script of the terminal with the program's order**, as two unrolled tables: the
`N`-tests, then the cosets, then the assembly. A step function starts here with no answers. -/
theorem tm_script_unrolled (I : RowTerminal P S L) :
    (tmWithOrder I).script =
      tmTabFrom I.typeCall (tmTests L.q) [] fun TN =>
        tmTabFrom I.cosetCall (tmCosets L.q) [] fun TH => Script.done (I.assemble TN TH) := rfl

/-- **The assembly on exact tables is the answer of the state** (Theorem A.23, through
`RowTerminal.exact`). -/
theorem tm_assemble_exact (I : RowTerminal P S L) :
    I.assemble (fun ac => (I.typeCall ac).answer) (fun ij => (I.cosetCall ij).answer) =
      S.answer := by
  have h := I.exact
  simp only [RowTerminal.script, Script.evalExact_bind, Script.evalExact] at h
  have hTN : (Script.table I.typeCall I.tests).evalExact = fun ac => (I.typeCall ac).answer :=
    funext fun ac => Script.evalExact_table _ _ ac (I.mem_tests ac)
  have hTH : (Script.table I.cosetCall I.cosets).evalExact = fun ij => (I.cosetCall ij).answer :=
    funext fun ij => Script.evalExact_table _ _ ij (I.mem_cosets ij)
  rwa [hTN, hTH] at h

/-- After all answers, exact in the program's order, the step function must return the answer
of the state. -/
theorem tm_final_exact (I : RowTerminal P S L) :
    I.assemble
        (tmUpd (fun _ => ∅) ((tmTests L.q).map fun ac => (ac, (I.typeCall ac).answer)))
        (tmUpd (fun _ => ∅) ((tmCosets L.q).map fun ij => (ij, (I.cosetCall ij).answer))) =
      S.answer := by
  rw [tmUpd_exact _ _ _ mem_tmTests, tmUpd_exact _ _ _ mem_tmCosets]
  exact tm_assemble_exact I

end Script

end GI.Impl
