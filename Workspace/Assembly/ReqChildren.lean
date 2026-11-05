module

public import Workspace.Impl.LayoutAsm
public import Workspace.Paper.ScriptCalls

@[expose] public section

/-!
# The children of the row and aggregation nodes

`Rest.Req` asks two things about the children of a node of kind `rowTerminal`, `rowColumns` or
`aggregate`: there are polynomially many, and every `Solve` child has a state of polynomial
canonical weight `stateW`. Both follow from the model of stage 1 alone, for every run, so no
step program is needed. This file proves them (`req_children`).

* **The number of children.** The script calls are counted in stage 1 (`Run.scriptCalls_le`):
  at most `N^a` when `s ≤ N`. A column step has one child. An aggregation round also has one
  continuation for each overcoset of its output, at most `q^a ≤ N^a` (`Aggregation.overs_count`,
  `Aggregation.q_le`).
* **The `Solve` children.** They are fresh calls: the row calls of the row terminal
  (`rowState`) and the configuration calls of an aggregation round (`pairState`). Such a state
  has no hierarchy, no row record, all of its positions as domain, and `N = s`
  (`reqFresh`). Its size is at most `N^{1-α}` or `N^{2α}`, both at most `N`, so its weight bound
  is at most `10⁴ (N + 2)⁶` (`stateW_le_of_small`).

The count of the row terminal uses `s ≤ N`, not only `|Ω| ≤ N`: for an infinite type `Ω` the
second bound says nothing, and the row terminal makes `5q²` calls with `q ≤ s`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Impl Equiv Equiv.Perm GI.CoherentEntrance GI.Rectangle

/-! ### Fresh calls -/

/-- A call is **fresh** if it is not a `Solve` call, or its state has no hierarchy, no row
record, all positions as domain, and phase size `N = s`. -/
def reqFresh {Ω' C' : Type} (m : Mode) (T : State Ω' C') : Prop :=
  m = .solve → T.hier = [] ∧ T.rows = none ∧ T.dom = Set.univ ∧ T.N = T.size

theorem reqFresh_cont {Ω' C' : Type} (T : State Ω' C') : reqFresh .cont T := fun h => by
  cases h

theorem reqFresh_rowState {B C' : Type} [Fintype B] (K : Subgroup (Perm B)) (z w : B → C') :
    reqFresh .solve (rowState K z w) := fun _ => by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [rowState_size]
  rfl

theorem reqFresh_pairState {C' : Type} (n : ℕ) (x y : Fin n × Fin n → C') :
    reqFresh .solve (pairState n x y) := fun _ => by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [pairState_size]
  rfl

/-- A script that asks only `Continue` makes only fresh calls. -/
theorem reqFresh_of_cont {α : Type} {s : Script α}
    (h : s.CallsExact fun m _ => m = .cont) : s.CallsExact reqFresh :=
  Script.CallsExact.mono (fun m T hm => by subst hm; exact reqFresh_cont T) h

/-! ### The row terminal -/

theorem reqFresh_rowTerminal {P : Params} {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
    (I : RowTerminal P S L) : I.script.CallsExact reqFresh := by
  refine Script.callsExact_bind _ _
    (Script.callsExact_table _ _ (fun ac => reqFresh_rowState _ _ _) _) ?_
  exact Script.callsExact_bind _ _
    (Script.callsExact_table _ _ (fun ij => reqFresh_rowState _ _ _) _) trivial

/-! ### The aggregation round -/

section Agg

variable {P : Params} {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- Every query of an item is fresh. -/
def reqItemOK : AuxItem P S L → Prop
  | .query Qs _ => ∀ Q ∈ Qs, reqFresh Q.mode Q.T
  | _ => True

theorem reqFresh_item (I : AuxItem P S L) (h : reqItemOK I) : I.script.CallsExact reqFresh := by
  cases I with
  | none => trivial
  | overcoset => trivial
  | query Qs E₀ =>
    refine Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hs
    exact ⟨h Q hQ, trivial⟩
  | halving H =>
    show H.script.CallsExact _
    exact ⟨reqFresh_cont _, reqFresh_cont _, reqFresh_cont _, trivial⟩

theorem reqItemOK_objItem {Z : Type} [MulAction (Perm (Fin L.q)) Z] (zX zY : Z) :
    reqItemOK (objItem (P := P) (S := S) (L := L) zX zY) := by
  classical
  unfold objItem
  split_ifs <;> trivial

/-- The queries of a rectangle oracle built from representations are `Continue` calls. -/
theorem reqFresh_rectQueries [Finite Ω]
    (rep : ∀ W R : Finset (Fin L.q), RectConds P S L W R → RectRep P S L W R)
    (W R : Finset (Fin L.q)) (M N : W → R → Bool) (a₀ : alternatingGroup (Fin L.q)) :
    ∀ Q ∈ (RectOracle.ofReps rep).queries W R M N a₀, reqFresh Q.mode Q.T := by
  classical
  intro Q hQ
  simp only [RectOracle.ofReps] at hQ
  split_ifs at hQ with hc
  · simp only [RectRep.queries, List.mem_cons] at hQ
    rcases hQ with rfl | hQ
    · exact reqFresh_cont _
    · cases ht : (rep W R hc).twist with
      | none => simp [ht] at hQ
      | some t =>
        simp only [ht, Option.map_some, Option.toList_some, List.mem_singleton] at hQ
        subst hQ
        exact reqFresh_cont _
  · simp at hQ

theorem reqItemOK_rectItem [Finite Ω]
    (rep : ∀ W R : Finset (Fin L.q), RectConds P S L W R → RectRep P S L W R) (ch : SojChoice)
    (X Y : PairCfg L.q) (y₀ : Fin L.q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) :
    reqItemOK (rectItem (RectOracle.ofReps rep) ch X Y y₀ i₀ cert) := by
  unfold rectItem
  dsimp only
  split
  · exact reqFresh_rectQueries rep _ _ _ _ _
  · trivial

theorem reqItemOK_sojItem [Finite Ω]
    (rep : ∀ W R : Finset (Fin L.q), RectConds P S L W R → RectRep P S L W R) (ch : SojChoice)
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q) :
    reqItemOK (sojItem (RectOracle.ofReps rep) ch X Y x₀ y₀) := by
  unfold sojItem
  split
  · split
    · split
      · exact reqItemOK_objItem _ _
      · split
        · exact reqItemOK_rectItem _ _ _ _ _ _ _
        · trivial
    · split
      · exact reqItemOK_objItem _ _
      · trivial
  · trivial

theorem reqItemOK_cfgItem (X Y : PairCfg L.q) : reqItemOK (cfgItem (P := P) (S := S) X Y) := by
  classical
  unfold cfgItem
  split_ifs
  · intro Q hQ
    rw [List.mem_singleton] at hQ
    subst hQ
    exact reqFresh_pairState _ _ _
  · trivial

theorem reqItemOK_cfgOutItem [Finite Ω]
    (rep : ∀ W R : Finset (Fin L.q), RectConds P S L W R → RectRep P S L W R) (ch : SojChoice)
    (oX oY : CfgOut L.q) : reqItemOK (cfgOutItem (RectOracle.ofReps rep) ch oX oY) := by
  classical
  cases oX <;> cases oY <;> simp only [cfgOutItem] <;> try trivial
  · exact reqItemOK_objItem _ _
  · split_ifs
    · exact reqItemOK_cfgItem _ _
    · exact reqItemOK_sojItem _ _ _ _ _ _

/-- **Every `Solve` call of an aggregation round is fresh**: the certificate and comparison
phases ask only `Continue`, and the items ask `Solve` only in the configuration query. -/
theorem reqFresh_agg (I : Aggregation P S L) : I.script.CallsExact reqFresh := by
  have hcert : I.certScript.CallsExact reqFresh := by
    haveI := I.fin
    letI : Fintype S.dom := Fintype.ofFinite _
    letI : DecidableEq Ω := Classical.decEq _
    exact reqFresh_of_cont (certPhase_cont _ _ _ _ _ _ _)
  have hcomp : I.compScript.CallsExact reqFresh := by
    haveI := I.fin
    letI : Fintype S.dom := Fintype.ofFinite _
    letI : DecidableEq Ω := Classical.decEq _
    exact reqFresh_of_cont (comparePhase_cont _ _ _ _ _ _ _)
  refine Script.callsExact_bind _ _ hcert (Script.callsExact_bind _ _ hcomp
    (Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial))
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hs
  refine reqFresh_item _ ?_
  haveI := I.fin
  unfold Aggregation.items plan
  split
  · unfold caseOneItem invItem
    split_ifs <;> trivial
  · unfold halvingItem
    split_ifs <;> trivial
  · exact reqItemOK_cfgOutItem _ _ _ _
  · exact reqItemOK_cfgOutItem _ _ _ _

end Agg

/-! ### The bounds -/

/-- From `x ≤ N^e` with `0 < e ≤ 1` follows `x ≤ N`. -/
theorem req_le_of_rpow {x N : ℕ} {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1)
    (h : (x : ℝ) ≤ (N : ℝ) ^ e) : x ≤ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Nat.cast_zero, Real.zero_rpow he0.ne'] at h
    exact_mod_cast h
  · have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h2 := Real.rpow_le_rpow_of_exponent_le h1 he1
    rw [Real.rpow_one] at h2
    exact_mod_cast h.trans h2

/-- **The weight bound of a fresh `Solve` state** of size at most `N`. -/
theorem req_stateW_fresh {Ω' C' : Type} {T : State Ω' C'} {N : ℕ} (h : reqFresh .solve T)
    (hs : T.size ≤ N) : stateW (Nat.card Ω') T ≤ 10 ^ 4 * (N + 2) ^ 6 := by
  obtain ⟨hh, hr, hd, hN⟩ := h rfl
  have hk : Nat.card Ω' = T.N := by
    rw [hN, State.size, hd, Nat.card_univ]
  have hsm : Small T := ⟨by rw [hh]; simp, by rw [hh]; simp, by rw [hr]; simp⟩
  refine (stateW_le_of_small hk.le hsm).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 6))
  omega

/-- `x ≤ N^a` at `P₀`, with `a = 36000`, as a bound in natural numbers. -/
theorem req_le_pow_a {N : ℕ} {x : ℝ} (h : x ≤ (N : ℝ) ^ P₀.a) :
    x ≤ ((N ^ 36000 : ℕ) : ℝ) := by
  rw [show P₀.a = ((36000 : ℕ) : ℝ) by norm_num [P₀], Real.rpow_natCast] at h
  exact_mod_cast h

/-- **The children of the row and aggregation nodes.** At a node of kind `rowTerminal`,
`rowColumns` or `aggregate` that is not a `Solve` node and has `s ≤ N`:

* it has at most `2 (N + 2)^36000` children (`36000 = a` at `P₀`): at most `N^a` script calls
  (`Run.scriptCalls_le`), and one column child or at most `q^a ≤ N^a` continuations;
* every `Solve` child is fresh (`reqFresh_rowTerminal`, `reqFresh_agg`) with at most
  `N^{1-α}` or `N^{2α}` positions, so its weight bound is at most `10⁴ (N + 2)⁶`. -/
theorem req_children (nd : Node P₀) (hm : nd.m ≠ .solve) (hsz : nd.S.size ≤ nd.S.N)
    (hk : nd.run.kind = .rowTerminal ∨ nd.run.kind = .rowColumns ∨
      nd.run.kind = .aggregate) :
    nd.run.children.length ≤ 2 * (nd.S.N + 2) ^ 36000 ∧
      ∀ c ∈ nd.run.children, c.m = .solve →
        stateW (Nat.card c.Ω) c.S ≤ 10 ^ 4 * (nd.S.N + 2) ^ 6 := by
  obtain ⟨m, Ω, C, S, L, A, r⟩ := nd
  simp only at hm hsz ⊢
  have ha : (5 : ℝ) ≤ P₀.a := by norm_num [P₀]
  have hcalls := r.scriptCalls_le ha hsz
  have hNpow : S.N ^ 36000 ≤ (S.N + 2) ^ 36000 := Nat.pow_le_pow_left (by omega) _
  cases r with
  | rowTerminal hs htr L' hrow I e =>
    have hc : ((e.calls.length : ℕ) : ℝ) ≤ ((S.N ^ 36000 : ℕ) : ℝ) := req_le_pow_a hcalls
    have hc' : e.calls.length ≤ S.N ^ 36000 := by exact_mod_cast hc
    refine ⟨by simp only [Run.children]; omega, fun c hc hcm => ?_⟩
    simp only [Run.children] at hc
    have hp := (Exec.calls_spec e _ ((reqFresh_rowTerminal I).and I.calls)).1 c hc
    rw [hcm] at hp
    exact req_stateW_fresh hp.1
      (req_le_of_rpow (by norm_num [P₀]) (by norm_num [P₀]) hp.2.2)
  | rowColumns =>
    have h1 : 1 ≤ (S.N + 2) ^ 36000 := Nat.one_le_pow _ _ (by omega)
    refine ⟨by simp only [Run.children, List.length_singleton]; omega, fun c hc hcm => ?_⟩
    simp only [Run.children, List.mem_singleton] at hc
    subst hc
    cases hcm
  | aggregate hs htr L' hnot hq₀ I hsel hcon b e τ hτ child hchild hN hhier hbk A' r' =>
    have hc : ((e.calls.length : ℕ) : ℝ) ≤ ((S.N ^ 36000 : ℕ) : ℝ) := req_le_pow_a hcalls
    have hc' : e.calls.length ≤ S.N ^ 36000 := by exact_mod_cast hc
    have hb : b = I.script.evalExact := e.exact
    have ho : (b.overs.length : ℝ) ≤ ((S.N ^ 36000 : ℕ) : ℝ) := by
      rw [hb]
      refine req_le_pow_a (I.overs_count.trans ?_)
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast I.q_le)
        (by norm_num [P₀])
    have ho' : b.overs.length ≤ S.N ^ 36000 := by exact_mod_cast ho
    refine ⟨?_, fun c hc hcm => ?_⟩
    · simp only [Run.children, List.length_append, List.length_ofFn]
      omega
    · simp only [Run.children, List.mem_append, List.mem_ofFn] at hc
      rcases hc with hc | ⟨j, rfl⟩
      · have hp := (Exec.calls_spec e _ ((reqFresh_agg I).and I.calls)).1 c hc
        rw [hcm] at hp
        have hs' : (c.S.size : ℝ) ≤ (S.N : ℝ) ^ (2 * P₀.α) := by
          rcases hp.2 with h | ⟨h, -⟩
          · exact h.2
          · cases h
        exact req_stateW_fresh hp.1 (req_le_of_rpow (by norm_num [P₀]) (by norm_num [P₀]) hs')
      · cases hcm
  | _ => simp [Run.kind] at hk

end GI.Assembly
