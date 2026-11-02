import Workspace.Impl.AggCmpHand
import Workspace.Impl.AggCertPos
import Workspace.Impl.ScriptCmp

/-!
# One call of the comparison phase

Each lockstep update of the comparison phase asks `Continue` on the state
`compareCall S N V hV x y g₀`: the lift of the stage kernel `N` on the lifted increment `V`, with
the colors `x` and `y ∘ g₀` of the domain, extended by one extra color off the domain. It is a
window call (`AggWin.lean`) with two strings in place of one. This file gives what the step
function needs to ask it.

* `cmCode`: the compressed color code, as `winCode` but over the raw codes of `x` and `y ∘ g₀`
  (`cmCode_injective`).
* `canon_compare`: the value `[k, gv, dv, x', y', hv, [], 0, 2, N]` is a canonical value of the
  state, for a group value `gv` of the lift of `N`, the indicator `dv` of the lifted increment,
  and the parent's hierarchy value `hv`.
* `cmCall_good`: the call may be made from a giant node (it is a charged call of Lemma 4.1).
* `cm_call_step`: one call for a set of candidate scripts that all ask it (`stepPostC_ask`),
  in the normal form `cmpFrom_succ_some`.
* `CmPicks rec`: the choices of representatives (`PickFn`) that agree with a record of the
  program's choices; nonempty for a consistent record (`cmPicks_nonempty`, by
  `PickFn.ofRecord`). The comparison phase keeps such a record, as the certificate phase keeps
  `Cands`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups GI.LocalCertificates
  Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)
open scoped Pointwise

variable {k : ℕ} {Ω C : Type}

/-! ### The colors of a comparison call -/

section Codes

variable [DecidableEq Ω] (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) [Fintype S.dom]
  (z z' : Ω → C) (a : Perm (Fin k))

open Classical in
/-- The raw codes of the second coloring `liftColor (z' ∘ g₀)`, with `a` the positions of a lift
of `g₀`. -/
noncomputable def cmRawY (i : Fin k) : ℕ :=
  if e.symm i ∈ S.dom then c (z' (e.symm (a i))) + 1 else 0

/-- The list of the raw codes of both colorings. -/
noncomputable def cmList : List ℕ :=
  (List.finRange k).map (winRawX e c S z) ++ (List.finRange k).map (cmRawY e c S z' a)

theorem cm_length_list : (cmList e c S z z' a).length = 2 * k := by
  simp [cmList]; ring

/-- **The compressed code of the colors of a comparison call.** -/
noncomputable def cmCode : Option C → ℕ := cmpCode (optCode c) (cmList e c S z z' a) k

theorem cmCode_injective (hc : Function.Injective c) :
    Function.Injective (cmCode e c S z z' a) :=
  cmpCode_injective (optCode_injective hc) (cm_length_list e c S z z' a).le

/-- The compressed codes of the first coloring. -/
noncomputable def cmCodesX : List ℕ :=
  (List.finRange k).map fun i => posOf (cmList e c S z z' a) (winRawX e c S z i)

/-- The compressed codes of the second coloring. -/
noncomputable def cmCodesY : List ℕ :=
  (List.finRange k).map fun i => posOf (cmList e c S z z' a) (cmRawY e c S z' a i)

variable {e c S z z' a}

theorem cm_rawY_eq {g : Perm Ω} (hg : g ∈ S.G) (ha : toFin e g = a) (i : Fin k) :
    cmRawY e c S z' a i =
      optCode c (liftColor S (dstr S z' ∘ S.domHom ⟨g, hg⟩) (e.symm i)) := by
  have := winRawY_eq (e := e) (c := c) (S := S) (z := z') hg ha i
  rw [← this]
  rfl

theorem cm_rawX_mem (i : Fin k) : winRawX e c S z i ∈ cmList e c S z z' a :=
  List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange i))

theorem cm_rawY_mem (i : Fin k) : cmRawY e c S z' a i ∈ cmList e c S z z' a :=
  List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange i))

theorem cm_colorVal_X :
    ColorVal e (cmCode e c S z z' a) (natList (cmCodesX e c S z z' a)) (liftColor S (dstr S z)) := by
  unfold ColorVal
  simp only [encFun, natList, cmCodesX, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, cmCode]
  have hm : optCode c (liftColor S (dstr S z) (e.symm i)) ∈ cmList e c S z z' a :=
    winRawX_eq (e := e) (c := c) (S := S) (z := z) i ▸ cm_rawX_mem i
  rw [cmpCode_of_mem hm, ← winRawX_eq]

theorem cm_colorVal_Y {g : Perm Ω} (hg : g ∈ S.G) (ha : toFin e g = a) :
    ColorVal e (cmCode e c S z z' a) (natList (cmCodesY e c S z z' a))
      (liftColor S (dstr S z' ∘ S.domHom ⟨g, hg⟩)) := by
  unfold ColorVal
  simp only [encFun, natList, cmCodesY, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, cmCode]
  have hm : optCode c (liftColor S (dstr S z' ∘ S.domHom ⟨g, hg⟩) (e.symm i)) ∈
      cmList e c S z z' a := cm_rawY_eq hg ha i ▸ cm_rawY_mem (z := z) i
  rw [cmpCode_of_mem hm, ← cm_rawY_eq hg ha]

theorem cmCode_lt_X (v : Ω) : cmCode e c S z z' a (liftColor S (dstr S z) v) < 2 * k := by
  have h := winRawX_eq (e := e) (c := c) (S := S) (z := z) (e v)
  simp only [Equiv.symm_apply_apply] at h
  have hm : optCode c (liftColor S (dstr S z) v) ∈ cmList e c S z z' a := h ▸ cm_rawX_mem (e v)
  rw [cmCode, cmpCode_of_mem hm, ← cm_length_list e c S z z' a]
  exact posOf_lt hm

theorem cmCode_lt_Y {g : Perm Ω} (hg : g ∈ S.G) (ha : toFin e g = a) (v : Ω) :
    cmCode e c S z z' a (liftColor S (dstr S z' ∘ S.domHom ⟨g, hg⟩) v) < 2 * k := by
  have h := cm_rawY_eq (e := e) (c := c) (S := S) (z' := z') hg ha (e v)
  simp only [Equiv.symm_apply_apply] at h
  have hm : optCode c (liftColor S (dstr S z' ∘ S.domHom ⟨g, hg⟩) v) ∈ cmList e c S z z' a :=
    h ▸ cm_rawY_mem (e v)
  rw [cmCode, cmpCode_of_mem hm, ← cm_length_list e c S z z' a]
  exact posOf_lt hm

end Codes

/-! ### The value of a comparison call -/

section Value

variable [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} [Fintype S.dom]

/-- **The value of a comparison call is canonical.** Let the parent have a canonical value with
hierarchy value `hv`. Let `gv` be a group value of the lift of `N` with at most `k²` generators,
`dv` the indicator of the lifted increment `V`, and `a` the positions of a lift `g ∈ G` of `g₀`.
Then `[k, gv, dv, x', y', hv, [], 0, 2, N]`, with the compressed codes `x'`, `y'` of the colors
`z` and `z' ∘ g₀`, is a canonical value of the state of the call. -/
theorem canon_compare {sv : Val} (hS : Canon e c sv S) {hv : Val} (hh : HierValC e hv S.hier)
    {N : Subgroup (Perm S.dom)} {V : Finset S.dom}
    (hV : GI.Algorithm.Invariant N (V : Set S.dom)) (z z' : Ω → C) {g : Perm Ω} (hg : g ∈ S.G)
    {a : Perm (Fin k)} (ha : toFin e g = a) {gv dv : Val}
    (hgv : GroupValC k gv (groupFin e (S.liftGroup N)))
    (hdv : DomVal e dv (Subtype.val '' (V : Set S.dom))) :
    Canon e (cmCode e c S z z' a)
      (winVal' k gv dv (natList (cmCodesX e c S z z' a)) (natList (cmCodesY e c S z z' a)) hv S.N)
      (compareCall S N V hV (dstr S z) (dstr S z') (S.domHom ⟨g, hg⟩)) where
  val := ⟨gv, dv, _, _, hv, .list [], hgv, hdv, cm_colorVal_X, cm_colorVal_Y hg ha, hh, rfl, rfl⟩
  colors v := ⟨cmCode_lt_X v, cmCode_lt_Y hg ha v⟩
  fits := hS.fits
  small := ⟨hS.small.1, hS.small.2.1, fun R hR => by cases hR⟩

end Value

/-! ### The call may be made -/

/-- **A comparison call is a charged call** of the aggregation round (Lemma 4.1, clause 2): it
runs under the lift of the stage kernel of `(z, T)` on its lifted increment. So it is `Good` for
`Continue`, and its measure is below that of the round. -/
theorem cmCall_good {Ω C C₀ : Type} [Finite Ω] [DecidableEq Ω] {S : State Ω C} [Fintype S.dom]
    {q : ℕ} (hgood : Good P₀ .giant S) (htr : S.Transitive)
    (πd : S.domGroup →* alternatingGroup (Fin q)) {κ : ℕ} (t : Fin κ → Fin q)
    (hk5 : 5 ≤ (tset t).card) (hκ : P₀.κ = (tset t).card) (hθ : 1 ≤ P₀.θ * (tset t).card)
    (z z' : S.dom → C₀) (j : ℕ) (g₀ : Perm S.dom) :
    let W := compareCall S (stageKer S πd z t j) (inc (phiT S.domGroup πd (tset t)) z j)
      (stageKer_invariant S πd z t j) z z' g₀
    Good P₀ .cont W ∧ MLt (measure P₀ .cont W) (measure P₀ .giant S) :=
  chargedCall_good_mlt hgood (ChargedCall.of_local_test htr πd z (tset t) hk5 hκ hθ j
    (State.queryChild_N _ _ _ _ _ _) (State.queryChild_hier _ _ _ _ _ _)
    (by rw [compareCall, State.queryChild_G]) (by rw [compareCall, State.queryChild_dom]))

/-! ### One call of the step function -/

/-- **One comparison call, for a set of candidates.** Let every candidate `ι ∈ Cs` be, at this
position, at stage `j` of the comparison of `(z, t)` with `(z', t')`, with the kept
representative `g₀` (the lift `g ∈ G` of `g₀`), followed by `K ι`. Then the step function may
return `[1, 1, arg, kst]` with the value `arg` of `canon_compare`, provided every canonical
answer leads to a program state of the continuations. -/
theorem cm_call_step {Ω C : Type} [Finite Ω] [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ}
    (hc : Function.Injective c) {S : State Ω C} [Fintype S.dom] {sv : Val} (hS : Canon e c sv S)
    {hv : Val} (hh : HierValC e hv S.hier) (hgood : Good P₀ .giant S) (htr : S.Transitive)
    {q κ : ℕ} (πd : S.domGroup →* alternatingGroup (Fin q)) (t : Fin κ → Fin q)
    (hk5 : 5 ≤ (tset t).card) (hκ : P₀.κ = (tset t).card) (hθ : 1 ≤ P₀.θ * (tset t).card)
    (z z' : Ω → C) (j m : ℕ) {g : Perm Ω} (hg : g ∈ S.G) {β ι : Type} {Cs : Set ι}
    (hCs : Cs.Nonempty) (Pk : ι → PickFn S.dom) (K : ι → Option (Perm S.dom) → Script β)
    {Out : β → Val → Prop} {Rep : Val → Set (Script β) → ℕ → Prop}
    {gv dv : Val}
    (hgv : GroupValC k gv (groupFin e (S.liftGroup (stageKer S πd (dstr S z) t j))))
    (hdv : DomVal e dv
      (Subtype.val '' (inc (phiT S.domGroup πd (tset t)) (dstr S z) j : Set S.dom)))
    {f : ℕ} (hf : 0 < f) {kst : Val}
    (hrep : ∀ u, AnsC e u (compareCall S (stageKer S πd (dstr S z) t j)
        (inc (phiT S.domGroup πd (tset t)) (dstr S z) j) (stageKer_invariant S πd (dstr S z) t j)
        (dstr S z) (dstr S z') (S.domHom ⟨g, hg⟩)).answer →
      Rep (.list [kst, u]) ((fun ι => (cmpFrom S πd (Pk ι) (dstr S z) (dstr S z') t (j + 1)
        ((Pk ι).pick (S.domHom ⟨g, hg⟩ • restrictAns S (compareCall S
          (stageKer S πd (dstr S z) t j) (inc (phiT S.domGroup πd (tset t)) (dstr S z) j)
          (stageKer_invariant S πd (dstr S z) t j) (dstr S z) (dstr S z')
          (S.domHom ⟨g, hg⟩)).answer)) m).bind (K ι)) '' Cs) (f - 1)) :
    Iface.StepPostC (measure P₀ .giant S) Out Rep
      ((fun ι => (cmpFrom S πd (Pk ι) (dstr S z) (dstr S z') t j (some (S.domHom ⟨g, hg⟩))
        (m + 1)).bind (K ι)) '' Cs) f
      (.list [.nat 1, .nat (modeCode .cont), winVal' k gv dv
        (natList (cmCodesX e c S z z' (toFin e g))) (natList (cmCodesY e c S z z' (toFin e g)))
        hv S.N, kst]) := by
  obtain ⟨hG, hlt⟩ := cmCall_good hgood htr πd t hk5 hκ hθ (dstr S z) (dstr S z') j
    (S.domHom ⟨g, hg⟩)
  refine stepPostC_ask hCs _ _ (fun ι B => (cmpFrom S πd (Pk ι) (dstr S z) (dstr S z') t (j + 1)
      ((Pk ι).pick (S.domHom ⟨g, hg⟩ • restrictAns S B)) m).bind (K ι))
    (fun ι _ => cmpFrom_succ_some S πd (Pk ι) (dstr S z) (dstr S z') t j m _ (K ι)) hf e
    (cmCode e c S z z' (toFin e g)) (cmCode_injective e c S z z' (toFin e g) hc) ?_ hG hlt hrep
  exact canon_compare hS hh (stageKer_invariant S πd (dstr S z) t j) z z' hg rfl hgv hdv


/-! ### Candidate representatives of the comparison cosets -/

section Picks

variable {V : Type}

/-- The choices of representatives that agree with a record of the program's choices. -/
def CmPicks (rec : List (Set (Perm V) × Option (Perm V))) : Set (PickFn V) :=
  {Pk | ∀ p ∈ rec, Pk.pick p.1 = p.2}

/-- A consistent and allowed record has a candidate (`PickFn.ofRecord`). -/
theorem cmPicks_nonempty {rec : List (Set (Perm V) × Option (Perm V))} (hok : RecordOK rec)
    (hQ : ∀ p ∈ rec, PickOK p.1 p.2) : (CmPicks rec).Nonempty :=
  ⟨PickFn.ofRecord rec hok hQ, fun _ hp => PickFn.ofRecord_pick rec hok hQ hp⟩

/-- A longer record has fewer candidates. -/
theorem cmPicks_cons {rec : List (Set (Perm V) × Option (Perm V))}
    (p : Set (Perm V) × Option (Perm V)) : CmPicks (p :: rec) ⊆ CmPicks rec :=
  fun _ hP r hr => hP r (List.mem_cons_of_mem _ hr)

/-- A candidate of a record makes the recorded choice. -/
theorem cmPicks_pick {rec : List (Set (Perm V) × Option (Perm V))} {Pk : PickFn V}
    (hP : Pk ∈ CmPicks rec) {A : Set (Perm V)} {o : Option (Perm V)} (h : (A, o) ∈ rec) :
    Pk.pick A = o :=
  hP _ h

end Picks

end GI.Impl
