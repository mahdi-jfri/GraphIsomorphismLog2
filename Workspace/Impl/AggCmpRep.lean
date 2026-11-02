import Workspace.Impl.AggCmpKer
import Workspace.Impl.AggCmpPhase

/-!
# The program states of the comparison phase

The step function of the comparison phase keeps its data in one value. This file fixes the
layout of that value and says what it stands for (`CmRep`), as `AggCertRep.lean` does for the
certificate phase.

## Layout

A program state is `[kst, u]`, where `u` is the answer of the last call (anything when no answer
is waiting), and `kst = [par, j, o, cache, acc, fl]`:

* `par`: the data of the phase, fixed for the whole phase;
* `j`: the stage of the current pair;
* `o`: the kept representative, `[]` (empty coset) or `[encPerm a]`, with `a` the positions of a
  lift in `G`;
* `cache`: the entries `[encGroup gs, encPerm a]` of the pick cache, each a lifted group and the
  representative chosen for its coset (`CmEntOK`);
* `acc`: the results of the finished pairs; its length is the index of the current pair in
  `cmPairs O`;
* `fl`: `0` at the start of a pair, `1` at stage `j` with representative `o`, `2` just after the
  call of stage `j` from `o`, with its answer `u`.

## Positions

The walk `cmAt` (`AggCmpWalk.lean`) names the remaining script at each position. Just after a
call, the next coset `A` is known, but each candidate round keeps its own representative
`Pk.pick A` until the program consults the cache. So a program state stands for a position of
the walk or for such a pending stage (`CmPt.pend`).

`cmMs` is the measure of the move loop. A position counts twice its `cmMeas`, and a pending
stage one more than the stage it waits for: the call moves from stage `j` (`2 m`) to the pending
stage `j + 1` (`2 m - 1`), and the answer move to stage `j + 1` (`2 m - 2`). `cmMc` is `cmMeas`,
which bounds the remaining calls.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups GI.LocalCertificates
  Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)
open scoped Pointwise

/-! ### The pairs by index -/

theorem cm_flatMap_getElem {α β : Type} (l : List α) (m : List β) (p : ℕ)
    (hp : p < (l.flatMap fun a => m.map fun b => (a, b)).length) :
    ∃ (h1 : p / m.length < l.length) (h2 : p % m.length < m.length),
      (l.flatMap fun a => m.map fun b => (a, b))[p] = (l[p / m.length], m[p % m.length]) := by
  induction l generalizing p with
  | nil => simp at hp
  | cons a l ih =>
    have hm : 0 < m.length := by
      rcases Nat.eq_zero_or_pos m.length with h | h
      · simp [List.length_eq_zero_iff.1 h] at hp
      · exact h
    by_cases hpm : p < m.length
    · have hd : p / m.length = 0 := Nat.div_eq_of_lt hpm
      have hmod : p % m.length = p := Nat.mod_eq_of_lt hpm
      refine ⟨by simp [hd], by rw [hmod]; exact hpm, ?_⟩
      simp only [List.flatMap_cons]
      rw [List.getElem_append_left (by simpa using hpm)]
      simp [hd, hmod]
    · have hp' : p - m.length < (l.flatMap fun a => m.map fun b => (a, b)).length := by
        simp only [List.flatMap_cons, List.length_append, List.length_map] at hp
        omega
      obtain ⟨h1, h2, he⟩ := ih (p - m.length) hp'
      have hd : p / m.length = (p - m.length) / m.length + 1 :=
        Nat.div_eq_sub_div hm (by omega)
      have hmod : p % m.length = (p - m.length) % m.length := by
        conv_lhs => rw [← Nat.sub_add_cancel (show m.length ≤ p by omega)]
        exact Nat.add_mod_right _ _
      refine ⟨by simp [hd]; omega, by rw [hmod]; exact h2, ?_⟩
      simp only [List.flatMap_cons]
      rw [List.getElem_append_right (by simpa using hpm)]
      simp only [List.length_map]
      rw [he]
      simp [hd, hmod]

/-- **The pair at index `p`**: the pairs from index `p` on start with
`(tuples[p / N], tuples[p % N])`, `N` the number of tuples. -/
theorem cm_pairs_drop {q κ : ℕ} (O : TestTupleOrder q κ) {p : ℕ}
    (hp : p < O.tuples.length * O.tuples.length) :
    ∃ (h1 : p / O.tuples.length < O.tuples.length) (h2 : p % O.tuples.length < O.tuples.length),
      (cmPairs O).drop p =
        (O.tuples[p / O.tuples.length], O.tuples[p % O.tuples.length]) :: (cmPairs O).drop (p + 1) := by
  have hp' : p < (cmPairs O).length := by rw [cm_pairs_length]; exact hp
  obtain ⟨h1, h2, he⟩ := cm_flatMap_getElem O.tuples O.tuples p hp'
  refine ⟨h1, h2, ?_⟩
  rw [List.drop_eq_getElem_cons hp']
  congr 1

/-- No pair is left at index `N²`. -/
theorem cm_pairs_drop_end {q κ : ℕ} (O : TestTupleOrder q κ) {p : ℕ}
    (hp : O.tuples.length * O.tuples.length ≤ p) : (cmPairs O).drop p = [] :=
  List.drop_eq_nil_of_le (by rw [cm_pairs_length]; exact hp)

/-! ### Positions with a pending choice -/

section Pt

variable {Ω C : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {q κ : ℕ}

/-- **A position of the walk, or a pending stage**: stage `j` of the pair `ab`, whose coset `A`
is known while its representative is not yet chosen. -/
inductive CmPt (S : State Ω C) (q κ : ℕ) where
  | pos (p : CmPos S q κ)
  | pend (acc : List Bool) (ab : CmPair q κ) (ps : List (CmPair q κ)) (j : ℕ)
      (A : Set (Perm S.dom))

variable (πd : S.domGroup →* alternatingGroup (Fin q)) (x y : S.dom → C)

/-- The remaining script at a position, for the representatives `Pk`. -/
noncomputable def cmAtP (Pk : PickFn S.dom) : CmPt S q κ → Script (List Bool)
  | .pos p => cmAt S πd x y Pk p
  | .pend acc ab ps j A => cmAt S πd x y Pk (.stage acc ab ps j (Pk.pick A))

variable {S}

/-- The number of remaining calls is bounded by `cmMeas` (`cmMc`). -/
def cmMc (n : ℕ) : CmPt S q κ → ℕ
  | .pos p => cmMeas n p
  | .pend _ _ ps j _ => ps.length * (n + 2) + (n - j) + 2

/-- **The measure of the move loop.** -/
def cmMs (n : ℕ) : CmPt S q κ → ℕ
  | .pos p => 2 * cmMeas n p
  | .pend _ _ ps j _ => 2 * (ps.length * (n + 2) + (n - j) + 2) + 1

end Pt

/-! ### Values -/

section Values

variable {k : ℕ}

/-- The value of the kept representative. -/
def cmOV : Option (Perm (Fin k)) → Val
  | none => .list []
  | some a => .list [encPerm a]

/-- The value of a cache entry: the lifted group and the chosen representative. -/
def cmEntV (p : List (Perm (Fin k)) × Perm (Fin k)) : Val := .list [encGroup p.1, encPerm p.2]

/-- **The data of a program state.** -/
structure CmSt (k : ℕ) where
  j : ℕ
  o : Option (Perm (Fin k))
  cache : List (List (Perm (Fin k)) × Perm (Fin k))
  acc : List Bool
  fl : ℕ

/-- The value `kst` of a program state. -/
def CmSt.val (par : Val) (σ : CmSt k) : Val :=
  .list [par, .nat σ.j, cmOV σ.o, .list (σ.cache.map cmEntV), .list (σ.acc.map boolVal),
    .nat σ.fl]

/-- The state at the start of the phase. -/
def CmSt.init : CmSt k := ⟨0, none, [], [], 0⟩

end Values

/-! ### What a program state stands for -/

section Rep

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] (e : Ω ≃ Fin k) {S : State Ω C} [Fintype S.dom]

/-- **A kept representative on positions stands for one on the domain**: none for none, and
`a` for `g` when `a` is the positions of a lift of `g` in `G`. -/
def CmOK : Option (Perm (Fin k)) → Option (Perm S.dom) → Prop
  | none, none => True
  | some a, some g => (toFin e).symm a ∈ S.G ∧ domOfPos e S a = g
  | _, _ => False

variable {q κ : ℕ} (πd : S.domGroup →* alternatingGroup (Fin q))

/-- The string of a test tuple, on `Ω`. -/
abbrev cmZ (S : State Ω C) (b : Bool) : Ω → C := if b then S.y else S.x

omit [Fintype S.dom] in
theorem cm_strOf_dstr (b : Bool) :
    strOf S (dstr S S.x) (dstr S S.y) b = dstr S (cmZ S b) := by
  cases b <;> rfl

/-- **The call of stage `j` of the pair `ab`** from the representative with positions `a₀`. -/
noncomputable abbrev cmCall (ab : CmPair q κ) (j : ℕ) (a₀ : Perm (Fin k)) : State Ω (Option C) :=
  compareCall S (stageKer S πd (dstr S (cmZ S ab.1.1)) ab.1.2 j)
    (inc (phiT S.domGroup πd (tset ab.1.2)) (dstr S (cmZ S ab.1.1)) j)
    (stageKer_invariant S πd (dstr S (cmZ S ab.1.1)) ab.1.2 j) (dstr S (cmZ S ab.1.1))
    (dstr S (cmZ S ab.2.1)) (domOfPos e S a₀)

/-- **The data of the program state at a position.** -/
def CmAtOK (par : Val) (O : TestTupleOrder q κ) (σ : CmSt k) (st : Val) : CmPt S q κ → Prop
  | .pos (.fin _) => False
  | .pos (.pair acc ps) => σ.fl = 0 ∧ σ.acc = acc ∧ ps = (cmPairs O).drop acc.length ∧
      ∃ u, st = .list [σ.val par, u]
  | .pos (.stage acc ab ps j o) => σ.fl = 1 ∧ σ.acc = acc ∧
      (cmPairs O).drop acc.length = ab :: ps ∧ σ.j = j ∧ j ≤ Fintype.card S.dom ∧
      CmOK e σ.o o ∧ ∃ u, st = .list [σ.val par, u]
  | .pend acc ab ps j A => σ.fl = 2 ∧ σ.acc = acc ∧ (cmPairs O).drop acc.length = ab :: ps ∧
      σ.j + 1 = j ∧ j ≤ Fintype.card S.dom ∧ ∃ a₀ u, σ.o = some a₀ ∧ (toFin e).symm a₀ ∈ S.G ∧
      A = domOfPos e S a₀ • restrictAns S (cmCall e πd ab σ.j a₀).answer ∧
      AnsC e u (cmCall e πd ab σ.j a₀).answer ∧ st = .list [σ.val par, u]

/-- **What a program state stands for.** The candidates are those of `CmCands Cs Ag₀ O rec` for
the record `rec` of the cache; the scripts are the remaining scripts at the position `pt`. `Bw`
bounds the weights of program states, `M₀` the measure plus the cache length. -/
def CmRep {L : SuppliedLabels S} (par : Val) (Cs : Set (Aggregation P₀ S L.toGiantLabels))
    (Ag₀ : Aggregation P₀ S L.toGiantLabels) (O : TestTupleOrder L.q P₀.κ)
    (πd : S.domGroup →* alternatingGroup (Fin L.q)) (Bw M₀ : ℕ) (m : ℕ) (st : Val)
    (Ss : Set (Script (List Bool))) (f : ℕ) : Prop :=
  ∃ (pt : CmPt S L.q P₀.κ) (σ : CmSt k) (ents : List (CmEnt S.dom))
    (rec : List (Set (Perm S.dom) × Option (Perm S.dom))),
    m = cmMs (Fintype.card S.dom) pt ∧ cmMc (Fintype.card S.dom) pt ≤ f ∧ st.wt ≤ Bw ∧
    σ.cache.length + m ≤ M₀ ∧ CmCacheOK ents rec ∧ List.Forall₂ (CmEntOK e S) σ.cache ents ∧
    (∀ p ∈ σ.cache, p.1.length ≤ (k + L.q) ^ 2) ∧
    Ss = (fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick pt) '' CmCands Cs Ag₀ O rec ∧
    CmAtOK e πd par O σ st pt

/-- The measure is bounded. -/
theorem cmRep_le {L : SuppliedLabels S} {par : Val} {Cs : Set (Aggregation P₀ S L.toGiantLabels)}
    {Ag₀ : Aggregation P₀ S L.toGiantLabels} {O : TestTupleOrder L.q P₀.κ}
    {πd : S.domGroup →* alternatingGroup (Fin L.q)} {Bw M₀ m : ℕ} {st : Val}
    {Ss : Set (Script (List Bool))} {f : ℕ} (h : CmRep e par Cs Ag₀ O πd Bw M₀ m st Ss f) :
    m ≤ M₀ := by
  obtain ⟨-, σ, -, -, hm, -, -, hM, -⟩ := h
  omega

/-- The weight is bounded. -/
theorem cmRep_wt {L : SuppliedLabels S} {par : Val} {Cs : Set (Aggregation P₀ S L.toGiantLabels)}
    {Ag₀ : Aggregation P₀ S L.toGiantLabels} {O : TestTupleOrder L.q P₀.κ}
    {πd : S.domGroup →* alternatingGroup (Fin L.q)} {Bw M₀ m : ℕ} {st : Val}
    {Ss : Set (Script (List Bool))} {f : ℕ} (h : CmRep e par Cs Ag₀ O πd Bw M₀ m st Ss f) :
    st.wt ≤ Bw := by
  obtain ⟨-, -, -, -, -, -, hw, -⟩ := h
  exact hw

end Rep

/-! ### The start of the phase -/

section Init

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]

/-- **The comparison scripts of the candidates are the walk from its start**, for the `πd` of any
round of the labels. -/
theorem cm_compScript_at {L : SuppliedLabels S} {Cs : Set (Aggregation P₀ S L.toGiantLabels)}
    {Ag₀ : Aggregation P₀ S L.toGiantLabels} (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    {O : TestTupleOrder L.q P₀.κ} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    {Ag : Aggregation P₀ S L.toGiantLabels} (hAg : Ag ∈ CmCands Cs Ag₀ O rec) :
    Ag.compScript = cmAt S Ag₀.πd (dstr S S.x) (dstr S S.y) Ag.pick (.pair [] (cmPairs O)) := by
  rw [cm_compScript_eq Ag, hAg.2.2.1, it_πd_eq (hsub hAg.1) (hsub hAg₀)]
  congr 1 <;> exact Subsingleton.elim _ _

/-- **The start of the phase stands for the comparison scripts of the candidates.** -/
theorem cmRep_init {L : SuppliedLabels S} {Cs : Set (Aggregation P₀ S L.toGiantLabels)}
    {Ag₀ : Aggregation P₀ S L.toGiantLabels} (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (O : TestTupleOrder L.q P₀.κ) (par : Val) {Bw : ℕ}
    (hwt : (Val.list [(CmSt.init (k := k)).val par, .list []]).wt ≤ Bw) :
    CmRep e par Cs Ag₀ O Ag₀.πd Bw
      (2 * (O.tuples.length * O.tuples.length * (Fintype.card S.dom + 2) + 1))
      (2 * (O.tuples.length * O.tuples.length * (Fintype.card S.dom + 2) + 1))
      (.list [(CmSt.init (k := k)).val par, .list []])
      ((fun Ag => Ag.compScript) '' CmCands Cs Ag₀ O [])
      (O.tuples.length * O.tuples.length * (Fintype.card S.dom + 2) + 1) := by
  refine ⟨.pos (.pair [] (cmPairs O)), CmSt.init, [], [], ?_, ?_, hwt, ?_, CmCacheOK.nil,
    List.Forall₂.nil, by simp [CmSt.init], ?_, rfl, rfl, by simp, .list [], rfl⟩
  · simp only [cmMs]; rw [cmMeas_start]
  · simp only [cmMc]; rw [cmMeas_start]
  · simp [CmSt.init]
  · refine Set.image_congr fun Ag hAg => ?_
    exact cm_compScript_at hAg₀ hsub hAg

end Init

end GI.Impl
