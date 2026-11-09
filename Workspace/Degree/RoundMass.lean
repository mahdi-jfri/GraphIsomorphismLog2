module

public import Workspace.Algorithm.Aggregation
public import Workspace.Degree.Drops

@[expose] public section

/-!
# The calls of a round: mass and kind

A round makes about `q^(2κ) s` calls, so a bound on the number of calls is too weak: with `s` calls
of size `s` the weight would grow by a factor of `s`. Lemma 8.4 of the paper bounds the *mass*,
the sum of `s³` over the calls, by `poly(q) s³`. The reason is that the calls of one certificate
run over disjoint increments of a window: their sizes sum to at most `s`, so their cubes sum to at
most `s³`.

Main results:

* `Aggregation.script_mass_le`: the mass of a round.
* `Aggregation.script_roundCalls`: at a state with `q ≤ N^α`, each `Solve` call has at most `q²`
  positions, and each `Continue` call has no rows, no floor, and `h = 2`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Endpoint GI.LocalGroups GI.LocalCertificates
open scoped Pointwise

namespace Script

variable {α β : Type}

/-- The weight of one call in the mass: `max(1, s)³` for `Continue`, and nothing for `Solve`. -/
noncomputable def callMass {Ω C : Type} (m : Mode) (T : State Ω C) : ℝ :=
  if m = .cont then (max 1 (T.size : ℝ)) ^ 3 else 0

theorem callMass_nonneg {Ω C : Type} (m : Mode) (T : State Ω C) : 0 ≤ callMass m T := by
  unfold callMass
  split_ifs
  · positivity
  · exact le_rfl

/-- The mass of a script along the exact answers. -/
noncomputable def mass : Script α → ℝ
  | done _ => 0
  | ask m S k => callMass m S + (k S.answer).mass

theorem mass_nonneg : ∀ s : Script α, 0 ≤ s.mass
  | done _ => le_rfl
  | ask m S k => add_nonneg (callMass_nonneg m S) (mass_nonneg (k S.answer))

theorem mass_bind : ∀ (s : Script α) (f : α → Script β),
    (s.bind f).mass = s.mass + (f s.evalExact).mass
  | .done _, _ => by simp [bind, mass, evalExact]
  | .ask m _ k, f => by
    simp only [bind, mass, evalExact]
    rw [mass_bind (k _) f]
    ring

theorem mass_seqList : ∀ (l : List (Script α)), (seqList l).mass = (l.map mass).sum
  | [] => rfl
  | s :: ss => by
    simp only [seqList, mass_bind, List.map_cons, List.sum_cons, mass_seqList ss]
    simp [mass]

/-- A mass bound from the number of calls and a bound on their sizes. -/
theorem mass_le_of_calls {B : ℝ} (hB : 0 ≤ B)
    {s : Script α}
    (h : s.CallsExact fun m T => m = .cont → (max 1 (T.size : ℝ)) ^ 3 ≤ B) :
    s.mass ≤ s.numCont * B := by
  induction s with
  | done a => simp [mass, numCont]
  | ask m S k ih =>
    obtain ⟨h1, h2⟩ := h
    have h3 := ih S.answer h2
    by_cases hm : m = .cont
    · subst hm
      have h4 := h1 rfl
      have e : callMass .cont S = (max 1 (S.size : ℝ)) ^ 3 := if_pos rfl
      simp only [mass, numCont, e, if_true]
      push_cast
      linarith
    · have e : callMass m S = 0 := if_neg hm
      simp only [mass, numCont, e]
      rw [if_neg hm]
      simpa using h3

end Script

variable {Ω C : Type}

section Endpoint

variable [DecidableEq Ω] (S : State Ω C) [Fintype S.dom]

theorem size_image_val (V : Finset S.dom) {C' : Type} (T : State Ω C')
    (h : T.dom = Subtype.val '' (V : Set S.dom)) : T.size = V.card := by
  unfold State.size
  rw [h, _root_.Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_coe_finset]

theorem max_cube_le (n : ℕ) : (max 1 (n : ℝ)) ^ 3 ≤ (n : ℝ) ^ 3 + 1 := by
  rcases le_total 1 (n : ℝ) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]
    have : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    norm_num

theorem cube_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 3 + b ^ 3 ≤ (a + b) ^ 3 := by
  have := mul_nonneg ha hb
  nlinarith [mul_nonneg this ha, mul_nonneg this hb]

variable {Q C₀ : Type} [Group Q] {P' : Subgroup (Perm S.dom)}

/-- The windows grow by the increments, and an increment is disjoint from its window. -/
theorem win_card_succ (phi : P' →* Q) (x : S.dom → C₀) (t : ℕ) :
    (win phi x (t + 1)).card = (win phi x t).card + (inc phi x t).card := by
  classical
  have h : win phi x (t + 1) = win phi x t ∪ inc phi x t := rfl
  rw [h, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_right]
  exact fun v hv => increment_disjoint phi _ _ hv

/-- **The mass of a window check**: each coset representative makes one call on the increment. -/
theorem mass_checkNewWindowLift (R : CosetRepFn S.dom) (A N : Subgroup (Perm S.dom))
    (V : Finset S.dom) (x : S.dom → C₀) :
    (checkNewWindowLift S R A N V x).mass ≤ (R.reps A N).length * ((V.card : ℝ) ^ 3 + 1) := by
  classical
  unfold checkNewWindowLift
  split_ifs with hV
  · rw [Script.mass_bind, Script.mass_seqList, List.map_map]
    simp only [Script.mass, add_zero]
    have hone : ∀ τ : Perm S.dom, (Script.mass ∘ fun τ : Perm S.dom =>
        (Script.call .cont (windowCall S N V hV x τ)).bind
          fun B => Script.done (τ • restrictAns S B)) τ ≤ (V.card : ℝ) ^ 3 + 1 := by
      intro τ
      simp only [Function.comp, Script.mass_bind, Script.call, Script.mass, Script.callMass,
        ite_true, Script.evalExact, add_zero]
      have hs : (windowCall S N V hV x τ).size = V.card :=
        size_image_val S V _ rfl
      rw [hs]
      exact max_cube_le _
    have h := List.sum_le_length_nsmul ((R.reps A N).map (Script.mass ∘ fun τ : Perm S.dom =>
        (Script.call .cont (windowCall S N V hV x τ)).bind
          fun B => Script.done (τ • restrictAns S B))) ((V.card : ℝ) ^ 3 + 1) (by
      intro y hy
      obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hy
      exact hone τ)
    rw [List.length_map, nsmul_eq_mul] at h
    exact h
  · simp only [Script.mass]
    positivity

/-- **The mass of one endpoint procedure.** The increments are disjoint, so their cubes sum to
at most the cube of the window. -/
theorem mass_endpointScriptLift [Finite Q] (R : CosetRepFn S.dom) (phi : P' →* Q) (hP : P' ≤ S.domGroup)
    (x : S.dom → C₀) (t : ℕ) :
    (endpointScriptLift S R phi x t).mass ≤
      (Nat.card Q : ℝ) * (((win phi x t).card : ℝ) ^ 3 + t) := by
  classical
  induction t with
  | zero =>
    simp only [endpointScriptLift, Script.mass]
    positivity
  | succ t ih =>
    rw [endpointScriptLift, Script.mass_bind, endpointScriptLift_evalExact S R phi hP]
    have hc := win_card_succ S phi x t
    have hc' : ((win phi x (t + 1)).card : ℝ) = (win phi x t).card + (inc phi x t).card := by
      exact_mod_cast hc
    have hcube := cube_add_le (Nat.cast_nonneg (win phi x t).card : (0 : ℝ) ≤ _)
      (Nat.cast_nonneg (inc phi x t).card : (0 : ℝ) ≤ _)
    have hQ : (0 : ℝ) ≤ Nat.card Q := Nat.cast_nonneg _
    have hstep : (if increment phi (stage phi x t).1 (stage phi x t).2 = ∅ then
        Script.done (stage phi x t) else
        (checkNewWindowLift S R (stage phi x t).1 (kernelIn phi (stage phi x t).1)
          (increment phi (stage phi x t).1 (stage phi x t).2) x).bind
          fun B => Script.done (Subgroup.closure B, (stage phi x t).2 ∪
            increment phi (stage phi x t).1 (stage phi x t).2)).mass ≤
        (Nat.card Q : ℝ) * (((inc phi x t).card : ℝ) ^ 3 + 1) := by
      split_ifs
      · simp only [Script.mass]
        positivity
      · rw [Script.mass_bind]
        simp only [Script.mass, add_zero]
        refine (mass_checkNewWindowLift S R _ _ _ x).trans ?_
        have h1 : ((R.reps (stage phi x t).1 (kernelIn phi (stage phi x t).1)).length : ℝ) ≤
            Nat.card Q := by
          exact_mod_cast (R.length_le _ _).trans (kernelIn_index_le phi (grp_le phi x t))
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hsum : (Nat.card Q : ℝ) * (((win phi x t).card : ℝ) ^ 3 + t) +
        (Nat.card Q : ℝ) * (((inc phi x t).card : ℝ) ^ 3 + 1) ≤
        (Nat.card Q : ℝ) * (((win phi x (t + 1)).card : ℝ) ^ 3 + ((t + 1 : ℕ) : ℝ)) := by
      rw [hc', ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hQ
      push_cast
      linarith
    exact (add_le_add ih hstep).trans hsum

/-- At most `(2 κ!) (n³ + n)` on each test set: the two endpoint procedures. -/
theorem win_card_le (phi : P' →* Q) (x : S.dom → C₀) (t : ℕ) :
    (win phi x t).card ≤ Fintype.card S.dom := Finset.card_le_univ _

end Endpoint

section Phases

variable [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {q : ℕ}
  (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ)

/-- `n³ + n` for `n` the size of the domain. -/
noncomputable def massUnit (n : ℕ) : ℝ := (n : ℝ) ^ 3 + n

theorem massUnit_nonneg (n : ℕ) : 0 ≤ massUnit n := by unfold massUnit; positivity

theorem certPhase_mass_le (O : TestSetOrder q κ) (R : CosetRepFn S.dom) (x y : S.dom → C) :
    (certPhase S πd κ O R x y).mass ≤
      ((2 * q.choose κ * κ.factorial : ℕ) : ℝ) * massUnit (Fintype.card S.dom) := by
  set n := Fintype.card S.dom with hn
  unfold certPhase
  rw [Script.mass_seqList, List.map_map]
  have hone : ∀ T : Finset (Fin q), T.card = κ →
      (Script.mass ∘ fun T : Finset (Fin q) =>
        (endpointScriptLift S R (phiT S.domGroup πd T) x n).bind fun a =>
          (endpointScriptLift S R (phiT S.domGroup πd T) y n).bind fun b =>
            Script.done (a, b)) T ≤ 2 * (κ.factorial : ℝ) * massUnit n := by
    intro T hT
    have hQ : Nat.card (alternatingGroup T) ≤ κ.factorial := by
      calc Nat.card (alternatingGroup T) ≤ Nat.card (Perm T) :=
            Nat.card_le_card_of_injective _ Subtype.val_injective
        _ = κ.factorial := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe, hT]
    have hQ' : (Nat.card (alternatingGroup T) : ℝ) ≤ κ.factorial := by exact_mod_cast hQ
    have key : ∀ z : S.dom → C,
        (endpointScriptLift S R (phiT S.domGroup πd T) z n).mass ≤
          (κ.factorial : ℝ) * massUnit n := by
      intro z
      refine (mass_endpointScriptLift S R (phiT S.domGroup πd T) Pgrp_le z n).trans ?_
      have h1 : ((win (phiT S.domGroup πd T) z n).card : ℝ) ≤ n := by
        exact_mod_cast win_card_le S _ z n
      have h2 : ((win (phiT S.domGroup πd T) z n).card : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h1 3
      unfold massUnit
      exact mul_le_mul hQ' (by linarith) (by positivity) (by positivity)
    simp only [Function.comp, Script.mass_bind, Script.mass, add_zero]
    have := key x
    have := key y
    linarith
  have h := List.sum_le_length_nsmul (O.sets.map (Script.mass ∘ fun T : Finset (Fin q) =>
        (endpointScriptLift S R (phiT S.domGroup πd T) x n).bind fun a =>
          (endpointScriptLift S R (phiT S.domGroup πd T) y n).bind fun b =>
            Script.done (a, b))) (2 * (κ.factorial : ℝ) * massUnit n) (by
    intro z hz
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hz
    exact hone T ((O.mem T).1 hT))
  rw [List.length_map, O.length_eq, nsmul_eq_mul] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

variable {k : ℕ} (Pk : PickFn S.dom)

theorem mass_lockstep (φ : ℕ → Finset S.dom) (j : ℕ) (x y : S.dom → C) (t : Fin k → Fin q)
    (g₀ : Perm S.dom)
    (hφ : φ j = inc (phiT S.domGroup πd (tset t)) x j) (f : Set (Perm S.dom) → Option (Perm S.dom)) :
    ((lockstepStepLift S πd j x y t g₀).bind fun B => Script.done (f B)).mass ≤
      ((φ j).card : ℝ) ^ 3 + 1 := by
  change Script.callMass .cont (compareCall S (stageKer S πd x t j)
      (inc (phiT S.domGroup πd (tset t)) x j) (stageKer_invariant S πd x t j) x y g₀) + 0 ≤ _
  have hs : (compareCall S (stageKer S πd x t j)
      (inc (phiT S.domGroup πd (tset t)) x j) (stageKer_invariant S πd x t j) x y g₀).size =
        (φ j).card := by
    rw [hφ]
    exact size_image_val S _ _ rfl
  have e : ∀ {Ω' C' : Type} (T : State Ω' C'), Script.callMass .cont T =
      (max 1 (T.size : ℝ)) ^ 3 := fun _ => if_pos rfl
  rw [e, hs, add_zero]
  exact max_cube_le _

/-- **The mass of a lockstep run.** It asks one call per update, on the increments of `(x, t)`. -/
theorem mass_compareLoop (x y : S.dom → C) (t t' : Fin k → Fin q) (j : ℕ) :
    (compareLoop S πd Pk x y t t' j).mass ≤
      ((win (phiT S.domGroup πd (tset t)) x j).card : ℝ) ^ 3 + j := by
  induction j with
  | zero =>
    simp only [compareLoop, Script.mass]
    positivity
  | succ j ih =>
    set φ := phiT S.domGroup πd (tset t) with hφ
    rw [compareLoop, Script.mass_bind, compareLoop_evalExact]
    have hc := win_card_succ S φ x j
    have hc' : ((win φ x (j + 1)).card : ℝ) = (win φ x j).card + (inc φ x j).card := by
      exact_mod_cast hc
    have hcube := cube_add_le (Nat.cast_nonneg (win φ x j).card : (0 : ℝ) ≤ _)
      (Nat.cast_nonneg (inc φ x j).card : (0 : ℝ) ≤ _)
    have hinc : (0 : ℝ) ≤ ((inc φ x j).card : ℝ) ^ 3 := by positivity
    rw [hc']
    push_cast
    rcases ho : Pk.pick (lockstep S.domGroup πd j x t y t') with _ | g₀
    · change _ + (0 : ℝ) ≤ _
      linarith
    · have := mass_lockstep S πd (fun _ => inc φ x j) j x y t g₀ rfl Pk.pick
      change _ + ((lockstepStepLift S πd j x y t g₀).bind fun B => Script.done (Pk.pick B)).mass ≤ _
      linarith

theorem comparePhase_mass_le (O : TestTupleOrder q κ) (x y : S.dom → C) :
    (comparePhase S πd κ O Pk x y).mass ≤
      ((4 * q ^ (2 * κ) : ℕ) : ℝ) * massUnit (Fintype.card S.dom) := by
  set n := Fintype.card S.dom with hn
  rw [comparePhase, Script.mass_seqList]
  set L := O.tuples
  have h1 : ∀ s ∈ (L.flatMap fun a => L.map fun b =>
      compareScript S πd Pk (strOf S x y a.1) (strOf S x y b.1) a.2 b.2).map Script.mass,
      s ≤ massUnit n := by
    intro s hs
    obtain ⟨sc, hsc, rfl⟩ := List.mem_map.1 hs
    obtain ⟨a, -, hb⟩ := List.mem_flatMap.1 hsc
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
    rw [compareScript, Script.mass_bind]
    simp only [Script.mass, add_zero]
    refine (mass_compareLoop S πd Pk (strOf S x y a.1) (strOf S x y b.1) a.2 b.2 n).trans ?_
    have h2 : ((win (phiT S.domGroup πd (tset a.2)) (strOf S x y a.1) n).card : ℝ) ≤ n := by
      exact_mod_cast win_card_le S _ _ n
    have h3 := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 3
    unfold massUnit
    linarith
  have h := List.sum_le_length_nsmul _ _ h1
  rw [List.length_map, List.length_flatMap, nsmul_eq_mul] at h
  simp only [List.length_map, List.map_const', List.sum_replicate, smul_eq_mul] at h
  have hL : L.length ≤ 2 * q ^ κ := by
    rw [O.length_eq]
    exact Nat.mul_le_mul_left 2 (card_embedding_le κ)
  have hLL : L.length * L.length ≤ 4 * q ^ (2 * κ) := by
    calc L.length * L.length ≤ (2 * q ^ κ) * (2 * q ^ κ) := Nat.mul_le_mul hL hL
      _ = 4 * q ^ (2 * κ) := by ring
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (massUnit_nonneg n)
  exact_mod_cast hLL

end Phases

/-! ### The whole round -/

/-- The kind of an item: a query asks only `Solve` calls on at most `q²` positions. -/
def AuxItem.Plain {P : Params} {S : State Ω C} {L : GiantLabels S} : AuxItem P S L → Prop
  | .query Qs _ => ∀ Q ∈ Qs, Q.mode = .solve ∧ Q.T.size ≤ L.q ^ 2 ∧ Q.T.N ≤ L.q ^ 2
  | _ => True

/-- What is known of a call of a round at a state with `q ≤ N^α`. -/
def RoundCall (q : ℕ) {Ω' C' : Type} (m : Mode) (T : State Ω' C') : Prop :=
  (m = .solve ∧ T.size ≤ q ^ 2 ∧ T.N ≤ q ^ 2) ∨
    (m = .cont ∧ T.rows = none ∧ T.floor = false ∧ T.h = 2)

/-- A call of a round of `S` with labels on `q` points: `AggCall`, and `RoundCall` once `q ≤ N^α`. -/
def RoundP (P : Params) (S : State Ω C) (q : ℕ) {Ω' C' : Type} (m : Mode) (T : State Ω' C') : Prop :=
  AggCall P S m T ∧ ((q : ℝ) ≤ (S.N : ℝ) ^ P.α → RoundCall q m T)

section Items

variable {P : Params} {S : State Ω C} {L : GiantLabels S}

theorem AuxItem.Plain.calls {I : AuxItem P S L} (h : I.Plain) :
    I.script.CallsExact (RoundCall L.q) := by
  cases I with
  | none => trivial
  | overcoset => trivial
  | query Qs E₀ =>
    refine Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hs
    exact ⟨Or.inl (h Q hQ), trivial⟩
  | halving H =>
    have hq : ∀ z : Ω → C, RoundCall L.q .cont (H.kerState z) := fun z =>
      Or.inr ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨hq _, hq _, hq _, trivial⟩

theorem size_le_of_aggCall {Ω' C' : Type} {m : Mode} {T : State Ω' C'} [Finite Ω]
    (h : AggCall P S m T) (hm : m = .cont) : T.size ≤ S.size := by
  rcases h with ⟨h, -⟩ | ⟨-, e, h⟩
  · rw [hm] at h; cases h
  · subst e
    exact size_le_of_subset h.sub

end Items

section Scripts

variable [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {C₀ : Type}

theorem checkNewWindowLift_round (q : ℕ) (R : CosetRepFn S.dom) (A N : Subgroup (Perm S.dom))
    (V : Finset S.dom) (x : S.dom → C₀) :
    (checkNewWindowLift S R A N V x).CallsExact (RoundCall q) := by
  classical
  unfold checkNewWindowLift
  split_ifs with hV
  · refine Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hs
    exact Script.callsExact_bind _ _ ⟨Or.inr ⟨rfl, rfl, rfl, rfl⟩, trivial⟩ trivial
  · trivial

theorem endpointScriptLift_round (q : ℕ) {Q : Type} [Group Q] {P' : Subgroup (Perm S.dom)}
    (R : CosetRepFn S.dom) (phi : P' →* Q) (x : S.dom → C₀) (t : ℕ) :
    (endpointScriptLift S R phi x t).CallsExact (RoundCall q) := by
  classical
  induction t with
  | zero => trivial
  | succ t ih =>
    refine Script.callsExact_bind _ _ ih ?_
    split_ifs
    · trivial
    · exact Script.callsExact_bind _ _ (checkNewWindowLift_round S q R _ _ _ x) trivial

variable {q k : ℕ} (πd : S.domGroup →* alternatingGroup (Fin q)) (Pk : PickFn S.dom)

theorem compareLoop_round (q' : ℕ) (x y : S.dom → C₀) (t t' : Fin k → Fin q) (j : ℕ) :
    (compareLoop S πd Pk x y t t' j).CallsExact (RoundCall q') := by
  induction j with
  | zero => trivial
  | succ j ih =>
    refine Script.callsExact_bind _ _ ih ?_
    split
    · trivial
    · exact Script.callsExact_bind _ _
        (Script.callsExact_bind _ _ ⟨Or.inr ⟨rfl, rfl, rfl, rfl⟩, trivial⟩ trivial) trivial

end Scripts

namespace Aggregation

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : Aggregation P S L)

/-- **The items of a round are plain** when `q ≤ N^α`: the first-rectangle branch is dead code. -/
theorem items_plain (hq : (L.q : ℝ) ≤ (S.N : ℝ) ^ P.α) (b : Fin I.ℓ → Fin L.q) :
    (I.items b).Plain := by
  classical
  unfold items plan
  split
  · unfold caseOneItem invItem
    split_ifs <;> trivial
  · unfold halvingItem
    split_ifs <;> trivial
  all_goals
    unfold cfg cfgOutItem
    split
    · unfold objItem
      split_ifs <;> trivial
    · rw [if_pos hq]
      rename_i X _ Y _ _ _
      unfold cfgItem
      split_ifs with hc
      · intro Q hQ
        rw [List.mem_singleton] at hQ
        subst hQ
        refine ⟨rfl, ?_⟩
        show _ ∧ (pairState _ _ _).N ≤ _
        have h := pairState_size (C' := ℕ) X.fiber.card (pairCols X rfl) (pairCols Y hc.symm)
        have h2 : X.fiber.card ≤ L.q := by simpa using Finset.card_le_univ X.fiber
        have h3 : X.fiber.card * X.fiber.card ≤ L.q ^ 2 := by
          rw [pow_two]
          exact Nat.mul_le_mul h2 h2
        exact ⟨le_of_eq_of_le h h3, h3⟩
      · trivial
    · trivial

theorem itemsScript_round (hq : (L.q : ℝ) ≤ (S.N : ℝ) ^ P.α) :
    I.itemsScript.CallsExact (RoundCall L.q) := by
  refine Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hs
  exact (I.items_plain hq b).calls

theorem certScript_round : I.certScript.CallsExact (RoundCall L.q) := by
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  refine Script.callsExact_seqList _ fun s hs => ?_
  obtain ⟨T, -, rfl⟩ := List.mem_map.1 hs
  exact Script.callsExact_bind _ _ (endpointScriptLift_round S _ _ _ _ _)
    (Script.callsExact_bind _ _ (endpointScriptLift_round S _ _ _ _ _) trivial)

theorem compScript_round : I.compScript.CallsExact (RoundCall L.q) := by
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  refine Script.callsExact_seqList _ fun s hs => ?_
  obtain ⟨sc, hsc⟩ := List.mem_flatMap.1 hs
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hsc.2
  exact Script.callsExact_bind _ _ (compareLoop_round S _ _ _ _ _ _ _ _) trivial

/-- **Every call of a round is plain**: at a state with `q ≤ N^α`, a `Solve` call has at most `q²`
positions, and a `Continue` call clears the rows and the floor. -/
theorem script_roundCalls (hq : (L.q : ℝ) ≤ (S.N : ℝ) ^ P.α) :
    I.script.CallsExact (RoundCall L.q) :=
  Script.callsExact_bind _ _ I.certScript_round
    (Script.callsExact_bind _ _ I.compScript_round (I.itemsScript_round hq))

theorem itemsScript_calls : I.itemsScript.CallsExact (AggCall P S) :=
  Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hs
    exact (I.items b).calls (I.items_valid b)) trivial

theorem itemsScript_mass_le [Finite Ω] :
    I.itemsScript.mass ≤ ((3 * L.q ^ I.ℓ : ℕ) : ℝ) * (max 1 (S.size : ℝ)) ^ 3 := by
  have hcalls := I.itemsScript_calls
  have h := Script.mass_le_of_calls (s := I.itemsScript) (B := (max 1 (S.size : ℝ)) ^ 3)
    (by positivity) (hcalls.mono fun m T hc hm => by
      have h1 := size_le_of_aggCall hc hm
      have h2 : (T.size : ℝ) ≤ S.size := by exact_mod_cast h1
      exact pow_le_pow_left₀ (by positivity) (max_le_max le_rfl h2) 3)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact_mod_cast I.itemsScript_numCont_le

/-- **The local mass bound of Lemma 4.1**, on a round at a state with `s ≥ 1`. -/
theorem script_mass_le (hs : 1 ≤ S.size) :
    I.script.mass ≤ (((2 * L.q.choose P.κ * P.κ.factorial : ℕ) : ℝ) * 2 +
      ((4 * L.q ^ (2 * P.κ) : ℕ) : ℝ) * 2 + ((3 * L.q ^ I.ℓ : ℕ) : ℝ)) * (S.size : ℝ) ^ 3 := by
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  have hcard : Fintype.card S.dom = S.size := by
    rw [State.size, Nat.card_eq_fintype_card]
  have hs' : (1 : ℝ) ≤ S.size := by exact_mod_cast hs
  have hU : massUnit (Fintype.card S.dom) ≤ 2 * (S.size : ℝ) ^ 3 := by
    rw [hcard]
    unfold massUnit
    nlinarith [mul_nonneg (sub_nonneg.2 hs') (sub_nonneg.2 hs'),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hs') (sub_nonneg.2 hs')) (by linarith : 0 ≤ (S.size : ℝ))]
  have h1 : I.certScript.mass ≤ ((2 * L.q.choose P.κ * P.κ.factorial : ℕ) : ℝ) *
      massUnit (Fintype.card S.dom) := certPhase_mass_le S I.πd P.κ I.sets I.reps _ _
  have h2 : I.compScript.mass ≤ ((4 * L.q ^ (2 * P.κ) : ℕ) : ℝ) *
      massUnit (Fintype.card S.dom) := comparePhase_mass_le S I.πd P.κ I.pick I.tests _ _
  have h3 := I.itemsScript_mass_le
  rw [max_eq_right hs'] at h3
  have e : I.script.mass = I.certScript.mass + (I.compScript.mass + I.itemsScript.mass) := by
    unfold script
    rw [Script.mass_bind, Script.mass_bind]
  rw [e]
  have h4 := mul_le_mul_of_nonneg_left hU
    (Nat.cast_nonneg (2 * L.q.choose P.κ * P.κ.factorial) : (0 : ℝ) ≤ _)
  have h5 := mul_le_mul_of_nonneg_left hU
    (Nat.cast_nonneg (4 * L.q ^ (2 * P.κ)) : (0 : ℝ) ≤ _)
  nlinarith

theorem certScript_roundP : I.certScript.CallsExact (RoundP P S L.q) :=
  Script.CallsExact.and I.certScript_calls (I.certScript_round.mono fun _ _ h _ => h)

theorem compScript_roundP : I.compScript.CallsExact (RoundP P S L.q) :=
  Script.CallsExact.and I.compScript_calls (I.compScript_round.mono fun _ _ h _ => h)

theorem itemsScript_roundP : I.itemsScript.CallsExact (RoundP P S L.q) := by
  by_cases hq : (L.q : ℝ) ≤ (S.N : ℝ) ^ P.α
  · exact Script.CallsExact.and I.itemsScript_calls ((I.itemsScript_round hq).mono fun _ _ h _ => h)
  · exact Script.CallsExact.and I.itemsScript_calls
      (I.itemsScript_calls.mono fun _ _ _ hq' => absurd hq' hq)

end Aggregation

end GI.Algorithm
