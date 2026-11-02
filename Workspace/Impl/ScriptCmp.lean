import Workspace.Impl.ScriptCont

/-!
# The rest of the comparison phase, after some of its calls

The comparison phase (`comparePhase`, `Workspace/Algorithm/ComparisonPhase.lean`) runs, for every
pair of ordered test tuples, the lockstep loop `compareLoop`, which is nested to the left like the
endpoint loop. As for the certificate phase (`Workspace/Impl/ScriptCont.lean`), this file gives
the right-nested normal forms that a step function walks.

* `cmpStep j o`: one lockstep update at stage `j` from the kept representative `o`: nothing for
  `none`, else one `Continue` call (`compareCall`) and the representative `Pk.pick` of the
  translated restricted answer.
* `cmpFrom j o m`: `m` updates from stage `j`; `compareLoop_eq_cmpFrom`: the loop is `cmpFrom`
  from stage `0` and the representative of the initial coset.
* `cmpFrom_succ_none`, `cmpFrom_succ_some`: a finished comparison stays finished; otherwise the
  next update asks one call, and its answer gives the next representative.
* `cmpPhase_cons`: the comparison phase over a list of pairs starts with the first pair.

The representatives `Pk.pick` are a choice of the round (`Aggregation.pick`), which a program
meets with a cache, as for the coset representatives (`PickFn.ofRecord`). Two comparison
cosets `x H` and `x' H'` are equal exactly when `H = H'` and `x⁻¹ x' ∈ H`, so the cache test
needs the group test of `AggCache.lean` and one membership test.
-/

namespace GI.Impl

open GI.Algorithm GI.Endpoint GI.LocalGroups GI.LocalCertificates Equiv Equiv.Perm
open scoped Pointwise

section Loop

variable {Ω C C₀ : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {q k : ℕ}
  (πd : S.domGroup →* alternatingGroup (Fin q)) (Pk : PickFn S.dom) (x y : S.dom → C₀)
  (t t' : Fin k → Fin q)

/-- **One lockstep update** at stage `j` from the kept representative `o`. -/
noncomputable def cmpStep (j : ℕ) : Option (Perm S.dom) → Script (Option (Perm S.dom))
  | none => Script.done none
  | some g₀ => (lockstepStepLift S πd j x y t g₀).bind fun B => Script.done (Pk.pick B)

theorem compareLoop_succ (j : ℕ) :
    compareLoop S πd Pk x y t t' (j + 1) =
      (compareLoop S πd Pk x y t t' j).bind (cmpStep S πd Pk x y t j) := by
  rw [compareLoop]
  congr 1

/-- **`m` lockstep updates from stage `j`**, nested to the right. -/
noncomputable def cmpFrom : ℕ → Option (Perm S.dom) → ℕ → Script (Option (Perm S.dom))
  | _, o, 0 => Script.done o
  | j, o, m + 1 => (cmpStep S πd Pk x y t j o).bind fun o' => cmpFrom (j + 1) o' m

theorem cmpFrom_zero (j : ℕ) (o : Option (Perm S.dom)) :
    cmpFrom S πd Pk x y t j o 0 = Script.done o := rfl

theorem cmpFrom_succ (j : ℕ) (o : Option (Perm S.dom)) (m : ℕ) :
    cmpFrom S πd Pk x y t j o (m + 1) =
      (cmpStep S πd Pk x y t j o).bind fun o' => cmpFrom S πd Pk x y t (j + 1) o' m := rfl

/-- One more update at the end is one more update at the front. -/
theorem cmpFrom_bind_step (m : ℕ) : ∀ (j : ℕ) (o : Option (Perm S.dom)),
    (cmpFrom S πd Pk x y t j o m).bind (cmpStep S πd Pk x y t (j + m)) =
      cmpFrom S πd Pk x y t j o (m + 1) := by
  induction m with
  | zero =>
    intro j o
    rw [cmpFrom_zero, scr_done_bind, cmpFrom_succ]
    simp only [cmpFrom_zero, Nat.add_zero]
    exact (scr_bind_done _).symm
  | succ m ih =>
    intro j o
    rw [cmpFrom_succ, scr_bind_assoc, cmpFrom_succ]
    refine scr_bind_congr _ fun o' => ?_
    rw [← ih (j + 1) o']
    congr 2
    omega

/-- **The lockstep loop is `cmpFrom`** from stage `0` and the representative of the initial
coset. -/
theorem compareLoop_eq_cmpFrom (n : ℕ) :
    compareLoop S πd Pk x y t t' n =
      cmpFrom S πd Pk x y t 0 (Pk.pick (lockstep S.domGroup πd 0 x t y t')) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := cmpFrom_bind_step S πd Pk x y t n 0 (Pk.pick (lockstep S.domGroup πd 0 x t y t'))
    rw [Nat.zero_add] at h
    rw [compareLoop_succ, ih, h]

/-- **A finished comparison stays finished.** -/
theorem cmpFrom_succ_none {β : Type} (j m : ℕ) (K : Option (Perm S.dom) → Script β) :
    (cmpFrom S πd Pk x y t j none (m + 1)).bind K =
      (cmpFrom S πd Pk x y t (j + 1) none m).bind K := by
  rw [cmpFrom_succ, scr_bind_assoc]
  rfl

/-- **The next lockstep update** from a kept representative `g₀`: one call, whose translated
restricted answer gives the next representative. -/
theorem cmpFrom_succ_some {β : Type} (j m : ℕ) (g₀ : Perm S.dom)
    (K : Option (Perm S.dom) → Script β) :
    (cmpFrom S πd Pk x y t j (some g₀) (m + 1)).bind K =
      Script.ask .cont (compareCall S (stageKer S πd x t j)
          (inc (phiT S.domGroup πd (tset t)) x j) (stageKer_invariant S πd x t j) x y g₀)
        fun B => (cmpFrom S πd Pk x y t (j + 1) (Pk.pick (g₀ • restrictAns S B)) m).bind K := by
  rw [cmpFrom_succ, scr_bind_assoc]
  rfl

end Loop

section Phase

variable {Ω C : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {q κ : ℕ}
  (πd : S.domGroup →* alternatingGroup (Fin q)) (Pk : PickFn S.dom) (x y : S.dom → C)

/-- **The comparison phase over a list of pairs `ps`**, followed by `K`. -/
noncomputable def cmpPhaseFrom {β : Type} (ps : List (TestTuple q κ × TestTuple q κ))
    (K : List Bool → Script β) : Script β :=
  (Script.seqList (ps.map fun ab =>
    compareScript S πd Pk (strOf S x y ab.1.1) (strOf S x y ab.2.1) ab.1.2 ab.2.2)).bind K

theorem comparePhase_bind {β : Type} (O : TestTupleOrder q κ) (K : List Bool → Script β) :
    (comparePhase S πd κ O Pk x y).bind K =
      cmpPhaseFrom S πd Pk x y (O.tuples.flatMap fun a => O.tuples.map fun b => (a, b)) K := by
  unfold comparePhase cmpPhaseFrom
  congr 2
  rw [List.map_flatMap]
  congr 1
  funext a
  rw [List.map_map]
  rfl

/-- **The next pair**: the lockstep loop of the first pair from the initial representative, then
the other pairs, with the result of the first pair in front. -/
theorem cmpPhase_cons {β : Type} (ab : TestTuple q κ × TestTuple q κ)
    (ps : List (TestTuple q κ × TestTuple q κ)) (K : List Bool → Script β) :
    cmpPhaseFrom S πd Pk x y (ab :: ps) K =
      (cmpFrom S πd Pk (strOf S x y ab.1.1) (strOf S x y ab.2.1) ab.1.2 0
          (Pk.pick (lockstep S.domGroup πd 0 (strOf S x y ab.1.1) ab.1.2 (strOf S x y ab.2.1)
            ab.2.2)) (Fintype.card S.dom)).bind fun o =>
        cmpPhaseFrom S πd Pk x y ps fun bs => K (o.isSome :: bs) := by
  unfold cmpPhaseFrom
  rw [List.map_cons, scr_seqList_cons]
  unfold compareScript
  rw [compareLoop_eq_cmpFrom, scr_bind_assoc]
  rfl

theorem cmpPhase_nil {β : Type} (K : List Bool → Script β) :
    cmpPhaseFrom (q := q) (κ := κ) S πd Pk x y [] K = K [] := rfl

end Phase

end GI.Impl
