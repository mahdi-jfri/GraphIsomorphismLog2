import Workspace.Impl.ScriptCmp

/-!
# The walk through the whole comparison phase

The step function of the comparison phase walks through the script `comparePhase` of the round.
This file names the remaining script at every position of that walk, as `AggCertWalk.lean` does
for the certificate phase, and gives the moves between positions.

* `CmPos`: the end (`fin`), the start of a pair (`pair`), and stage `j` of a pair with the kept
  representative `o` (`stage`). Each carries the results `acc` of the finished pairs.
* `cmAt Pk p`: the remaining script at `p`, for the representatives `Pk`.

The moves:
* `cmAt_start`: the phase is the start of the first pair;
* `cmAt_pair_nil`: no pair left, the end;
* `cmAt_pair_cons`: the start of a pair is its stage `0`, with the representative
  `Pk.pick (lockstep 0)` of the first coset;
* `cmAt_stage_end`: after stage `n = |dom|`, the result `o.isSome` of the pair, then the next pair;
* `cmAt_stage_none`: an empty coset stays empty, with no call (`cmpFrom_succ_none`);
* `cmAt_stage_some`: from a kept representative `g₀`, one call, whose answer gives the next
  representative (`cmpFrom_succ_some`).

`cmMeas n` decreases along every move (`cmMeas_*`). A pair counts for `n + 2` positions, so the
measure of the start, `|pairs| (n + 2) + 1`, also bounds the number of calls.
-/

namespace GI.Impl

open GI.Algorithm GI.Endpoint GI.LocalGroups GI.LocalCertificates Equiv Equiv.Perm
open scoped Pointwise

/-- A pair of ordered test tuples. -/
abbrev CmPair (q κ : ℕ) := TestTuple q κ × TestTuple q κ

/-- The pairs of an order of the test tuples, in the order of `comparePhase`. -/
def cmPairs {q κ : ℕ} (O : TestTupleOrder q κ) : List (CmPair q κ) :=
  O.tuples.flatMap fun a => O.tuples.map fun b => (a, b)

theorem cm_pairs_length {q κ : ℕ} (O : TestTupleOrder q κ) :
    (cmPairs O).length = O.tuples.length * O.tuples.length := by
  unfold cmPairs
  rw [List.length_flatMap]
  simp [List.map_const', List.sum_replicate]

/-- **The positions of the walk.** -/
inductive CmPos {Ω C : Type} (S : State Ω C) (q κ : ℕ) where
  /-- The end of the phase, with all results. -/
  | fin (acc : List Bool)
  /-- The start of the first pair of `ps`. -/
  | pair (acc : List Bool) (ps : List (CmPair q κ))
  /-- Stage `j` of the pair `ab`, with the kept representative `o`; `ps` are the pairs after
  `ab`. -/
  | stage (acc : List Bool) (ab : CmPair q κ) (ps : List (CmPair q κ)) (j : ℕ)
      (o : Option (Perm S.dom))

section Walk

variable {Ω C : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {q κ : ℕ}
  (πd : S.domGroup →* alternatingGroup (Fin q)) (x y : S.dom → C) (Pk : PickFn S.dom)

/-- The final continuation: the results `acc` of the finished pairs, then those of the others. -/
def cmKfin (acc : List Bool) : List Bool → Script (List Bool) := fun bs => Script.done (acc ++ bs)

/-- **The remaining script at a position.** -/
noncomputable def cmAt : CmPos S q κ → Script (List Bool)
  | .fin acc => Script.done acc
  | .pair acc ps => cmpPhaseFrom S πd Pk x y ps (cmKfin acc)
  | .stage acc ab ps j o =>
      (cmpFrom S πd Pk (strOf S x y ab.1.1) (strOf S x y ab.2.1) ab.1.2 j o
        (Fintype.card S.dom - j)).bind fun o' =>
        cmpPhaseFrom S πd Pk x y ps (cmKfin (acc ++ [o'.isSome]))

/-- **The phase is the start of the first pair.** -/
theorem cmAt_start (O : TestTupleOrder q κ) :
    comparePhase S πd κ O Pk x y = cmAt S πd x y Pk (.pair [] (cmPairs O)) := by
  rw [← scr_bind_done (comparePhase S πd κ O Pk x y), comparePhase_bind]
  rfl

theorem cmAt_pair_nil (acc : List Bool) :
    cmAt S πd x y Pk (.pair acc ([] : List (CmPair q κ))) = cmAt S πd x y Pk (.fin acc : CmPos S q κ) := by
  show cmKfin acc [] = Script.done acc
  simp [cmKfin]

/-- **The start of a pair is its stage `0`.** -/
theorem cmAt_pair_cons (acc : List Bool) (ab : CmPair q κ) (ps : List (CmPair q κ)) :
    cmAt S πd x y Pk (.pair acc (ab :: ps)) =
      cmAt S πd x y Pk (.stage acc ab ps 0 (Pk.pick (lockstep S.domGroup πd 0
        (strOf S x y ab.1.1) ab.1.2 (strOf S x y ab.2.1) ab.2.2))) := by
  show cmpPhaseFrom S πd Pk x y (ab :: ps) (cmKfin acc) = _
  rw [cmpPhase_cons]
  simp only [cmAt, Nat.sub_zero]
  refine scr_bind_congr _ fun o => ?_
  congr 1
  funext bs
  simp [cmKfin]

/-- **The end of a pair**: its result, then the next pair. -/
theorem cmAt_stage_end (acc : List Bool) (ab : CmPair q κ) (ps : List (CmPair q κ))
    (o : Option (Perm S.dom)) :
    cmAt S πd x y Pk (.stage acc ab ps (Fintype.card S.dom) o) =
      cmAt S πd x y Pk (.pair (acc ++ [o.isSome]) ps) := by
  simp only [cmAt, Nat.sub_self, cmpFrom_zero, scr_done_bind]

/-- **An empty coset stays empty**, with no call. -/
theorem cmAt_stage_none (acc : List Bool) (ab : CmPair q κ) (ps : List (CmPair q κ)) {j : ℕ}
    (hj : j < Fintype.card S.dom) :
    cmAt S πd x y Pk (.stage acc ab ps j none) = cmAt S πd x y Pk (.stage acc ab ps (j + 1) none) := by
  simp only [cmAt]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card S.dom - j = m + 1 := ⟨Fintype.card S.dom - j - 1, by omega⟩
  have hm' : Fintype.card S.dom - (j + 1) = m := by omega
  rw [hm, hm', cmpFrom_succ_none]

/-- **One update from a kept representative**: one call, whose translated restricted answer gives
the next representative. -/
theorem cmAt_stage_some (acc : List Bool) (ab : CmPair q κ) (ps : List (CmPair q κ)) {j : ℕ}
    (hj : j < Fintype.card S.dom) (g₀ : Perm S.dom) :
    cmAt S πd x y Pk (.stage acc ab ps j (some g₀)) =
      Script.ask .cont (compareCall S (stageKer S πd (strOf S x y ab.1.1) ab.1.2 j)
          (inc (phiT S.domGroup πd (tset ab.1.2)) (strOf S x y ab.1.1) j)
          (stageKer_invariant S πd (strOf S x y ab.1.1) ab.1.2 j) (strOf S x y ab.1.1)
          (strOf S x y ab.2.1) g₀)
        fun B => cmAt S πd x y Pk (.stage acc ab ps (j + 1) (Pk.pick (g₀ • restrictAns S B))) := by
  simp only [cmAt]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card S.dom - j = m + 1 := ⟨Fintype.card S.dom - j - 1, by omega⟩
  have hm' : Fintype.card S.dom - (j + 1) = m := by omega
  rw [hm, hm', cmpFrom_succ_some]

end Walk

/-! ### The measure -/

section Meas

variable {Ω C : Type} {S : State Ω C} {q κ : ℕ}

/-- **The measure of a position**: each pair counts for `n + 2` positions. -/
def cmMeas (n : ℕ) : CmPos S q κ → ℕ
  | .fin _ => 0
  | .pair _ ps => ps.length * (n + 2) + 1
  | .stage _ _ ps j _ => ps.length * (n + 2) + (n - j) + 2

theorem cmMeas_pair_nil (n : ℕ) (acc : List Bool) :
    cmMeas n (.fin acc : CmPos S q κ) < cmMeas n (.pair acc ([] : List (CmPair q κ)) : CmPos S q κ) := by
  simp [cmMeas]

theorem cmMeas_pair_cons (n : ℕ) (acc : List Bool) (ab : CmPair q κ) (ps : List (CmPair q κ))
    (o : Option (Perm S.dom)) :
    cmMeas n (.stage acc ab ps 0 o : CmPos S q κ) < cmMeas n (.pair acc (ab :: ps) : CmPos S q κ) := by
  simp only [cmMeas, List.length_cons, Nat.sub_zero]
  rw [Nat.add_mul]
  omega

theorem cmMeas_stage_end (n : ℕ) (acc : List Bool) (ab : CmPair q κ) (ps : List (CmPair q κ))
    (o : Option (Perm S.dom)) (b : Bool) :
    cmMeas n (.pair (acc ++ [b]) ps : CmPos S q κ) < cmMeas n (.stage acc ab ps n o : CmPos S q κ) := by
  simp only [cmMeas, Nat.sub_self]
  omega

theorem cmMeas_stage_succ (n : ℕ) (acc : List Bool) (ab : CmPair q κ) (ps : List (CmPair q κ))
    {j : ℕ} (hj : j < n) (o o' : Option (Perm S.dom)) :
    cmMeas n (.stage acc ab ps (j + 1) o' : CmPos S q κ) < cmMeas n (.stage acc ab ps j o : CmPos S q κ) := by
  simp only [cmMeas]
  omega

/-- The measure of the start. -/
theorem cmMeas_start (n : ℕ) (O : TestTupleOrder q κ) :
    cmMeas n (.pair [] (cmPairs O) : CmPos S q κ) =
      O.tuples.length * O.tuples.length * (n + 2) + 1 := by
  simp [cmMeas, cm_pairs_length]

end Meas

end GI.Impl
