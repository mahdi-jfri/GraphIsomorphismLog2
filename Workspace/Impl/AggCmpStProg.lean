module

public import Workspace.Impl.AggCmpMvC
public import Workspace.Impl.AggSubProg

@[expose] public section

/-!
# The start of a pair: program text and facts on values

At the start of the pair `(t, t')` with index `p = |acc|`, the move must find the first coset
`lockstep 0` and choose its representative (`cm_pair_cons_rep`). The program does this in four
steps.

1. It reads `t = tuples[p / N]` and `t' = tuples[p % N]` (`cm_pairs_drop`) and computes the label
   points `k + t i` of each tuple, by a map that adds `k` to the digits (`sbSh_spec`).
2. It runs the orbit program on the label points of `t` under the graph pairs of `G`
   (`graphTup_spec`) and looks for the label points of `t'` among the points of the orbit (a
   search with the equality test of lists of numbers). If they are not there, the coset is
   empty (`cm_init_empty`).
3. Otherwise the transversal element `g` of that point maps the label points of `t` to those of
   `t'`. Its first part `a` (`gatherLeft_spec`) is the positions of a member of the coset
   (`cm_init_mem`). One **PointwiseStab** call gives the stabilizer of the label points of `t`
   in graph form (`graphStabP_spec`), and the group of its first parts is reduced to at most `k²`
   generators (`kr_spec`). The coset is the entry `(hs, a)` (`cm_zero_ent`).
4. It chooses the representative of that coset with the pick cache (`cmChF`, as the answer move
   does).

This file gives the program text, where it sits (`CmStAt`), and the facts on values that the
proofs use: the shifted digits are the label points (`cm_shift_eq`), the identity on positions is
`range k` (`cm_encPerm_one`), and the orbit has at most `N` points (`cm_orbit_le`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)

/-! ### The program text -/

section Funs

variable (b : ℕ)

/-- Base indices of the modules of the start of a pair. -/
def cmShM : ℕ := b + 100
def cmEqN : ℕ := b + 103
def cmKFd : ℕ := b + 106
def cmRng : ℕ := b + 109
def cmGat : ℕ := b + 112
def cmStab : ℕ := b + 120
def cmTup : ℕ := b + 200
def cmKr : ℕ := b + 240

/-- The label points of the tuple at index `i` of the tuples, as a list of numbers. -/
def cmLabE (i : Expr) : Expr :=
  .call (cmShM b) (mk2 (.get (cpPf 1) (.nat 0)) (.get (.get (cpPf 6) i) (.nat 1)))

/-- **The choice for a coset**, on `[kst, [gv, av]]` with `[gv, av]` the value of a cache entry:
the first cache value that passes `cmTest` gives the representative (a hit); otherwise the new
value is appended (a miss). The new program state is at stage `0` with `fl = 1`. -/
def cmChF : Expr :=
  .letE (.call (cmFind b) (mk2 cmU (cpKf 3)))
    (.ite (.arith .lt (.var 1) (.length (cpKf 3)))
      (cmRetE (Expr.mkList [cpKf 0, .nat 0, mk1 (.get (.get (cpKf 3) (.var 1)) (.nat 1)), cpKf 3,
        cpKf 4, .nat 1]))
      (cmRetE (Expr.mkList [cpKf 0, .nat 0, mk1 (.get cmU (.nat 1)), .snoc (cpKf 3) cmU, cpKf 4,
        .nat 1])))

/-- **The start of a pair**, on `[kst, u]`. -/
def cmStartF : Expr :=
  .letE (cmLabE b (.arith .div (.length (cpKf 4)) (cpPf 8)))
  (.letE (cmLabE b (.arith .mod (.length (cpKf 4)) (cpPf 8)))
  (.letE (.call (cmTup b) (mk4 (cpPf 1) (cpPf 2) (.var 1) (cpPf 8)))
  (.letE (.call (cmKFd b) (mk2 (.var 2) (.var 3)))
    (.ite (.arith .lt (.var 4) (.length (.var 3)))
      (.letE (.call (cmStab b) (mk3 (cpPf 1) (cpPf 2) (.var 1)))
      (.letE (.call (cmKr b) (mk2 (.get (cpPf 1) (.nat 0)) (.var 5)))
      (.letE (.call (cmGat b) (mk2 (.get (.get (.var 3) (.var 4)) (.nat 1))
          (.call (cmRng b) (.get (cpPf 1) (.nat 0)))))
        (.call (b + 8) (mk2 cpKs (mk2 (.var 6) (.var 7)))))))
      (cmRetE (Expr.mkList [cpKf 0, .nat 0, .nil, cpKf 3, cpKf 4, .nat 1]))))))

end Funs

open GI.Cited (PointwiseStab) in
/-- **Where the start of a pair and its modules sit.** -/
structure CmStAt (P : Program) (b jp : ℕ) : Prop where
  start : P.funs[b + 5]? = some (cmStartF b)
  add : P.funs[b + 6]? = some sbAddF
  tst : P.funs[b + 7]? = some (orbTestF (cmEqN b))
  ch : P.funs[b + 8]? = some (cmChF b)
  shM : P.HasAt (cmShM b) (mapFuns (cmShM b) (b + 6))
  eqN : P.HasAt (cmEqN b) (eqNatsFuns (cmEqN b))
  kfd : P.HasAt (cmKFd b) (findFuns (cmKFd b) (b + 7))
  rng : P.HasAt (cmRng b) (rangeFuns (cmRng b))
  gat : P.HasAt (cmGat b) (gatherFuns (cmGat b))
  stab : P.HasAt (cmStab b) (graphStabFuns (cmStab b) jp)
  tup : P.HasAt (cmTup b) (graphTupFuns (cmTup b))
  kr : P.HasAt (cmKr b) (krFuns (cmKr b) jp)

/-! ### Facts on values -/

section Vals

variable {k q κ : ℕ}

/-- **The shifted digits are the label points**: adding `k` to the digits of `t` gives the
numbers of the label points `k + t i`. -/
theorem cm_shift_eq (t : Fin κ → Fin q) :
    (stL fun i => ((t i : Fin q) : ℕ)).map (k + ·) = ptsKey (cmLabPts k t) := by
  simp [stL, ptsKey, cmLabPts, labPts, List.map_map, Function.comp_def]

/-- The label points as the value that the stabilizer program reads. -/
theorem cm_encPts_lab (t : Fin κ → Fin q) : encPts (cmLabPts k t) = natList (ptsKey (cmLabPts k t)) :=
  encPts_eq_natList _

/-- **The identity on positions** is the list `0, …, k - 1`. -/
theorem cm_encPerm_one : encPerm (1 : Perm (Fin k)) = natList (List.range k) := by
  simp only [encPerm, natList, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

/-- The number of test tuples is the number of all of them. -/
theorem cm_tuples_length (O : TestTupleOrder q κ) :
    O.tuples.length = Fintype.card (TestTuple q κ) := by
  rw [← List.toFinset_card_of_nodup O.nodup]
  congr 1
  exact Finset.eq_univ_iff_forall.2 fun a => List.mem_toFinset.2 (O.mem a)

/-- **The orbit of the label points of a tuple has at most `N` points**: each point is the
tuple of label points of another injective tuple `σ ∘ t`. -/
theorem cm_orbit_le (O : TestTupleOrder q κ) (ps : List (Perm (Fin k) × Perm (Fin q)))
    (t : Fin κ ↪ Fin q) :
    (actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g) (ps.map encPair)
      (cmLabPts k (t : Fin κ → Fin q))).ncard ≤ O.tuples.length := by
  have hsub : actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g) (ps.map encPair)
      (cmLabPts k (t : Fin κ → Fin q)) ⊆
      Set.range (fun t' : Fin κ ↪ Fin q => cmLabPts k (t' : Fin κ → Fin q)) := by
    intro y hy
    unfold cmLabPts at hy
    obtain ⟨σ, -, rfl⟩ := mem_tupOrbit.1 hy
    refine ⟨t.trans σ.toEmbedding, ?_⟩
    simp [cmLabPts, List.map_map, Function.comp_def]
  have h1 := Set.ncard_le_ncard hsub (Set.finite_range _)
  have h2 : (Set.range (fun t' : Fin κ ↪ Fin q => cmLabPts k (t' : Fin κ → Fin q))).ncard ≤
      Fintype.card (Fin κ ↪ Fin q) := by
    rw [← Set.image_univ]
    refine (Set.ncard_image_le Set.finite_univ).trans ?_
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  have h3 : Fintype.card (Fin κ ↪ Fin q) ≤ Fintype.card (TestTuple q κ) := by
    rw [Fintype.card_prod, Fintype.card_bool]
    omega
  rw [cm_tuples_length]
  omega

end Vals

end GI.Impl
