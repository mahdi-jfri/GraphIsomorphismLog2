module

public import Workspace.Impl.AggCertFxMath

@[expose] public section

/-!
# The graph forms of the certificate groups: the program and its invariant

After the runner of the certificate phase, the program knows, for each test set `T` and each
string `z`, the graph form of the lift of the final group `A_final(z, T)` (the results) and the
stage log (the logs). The comparison phase and the items need a graph form of the lift of
`F_z = ⟨K(T) : T full⟩` (`certGroup`). `cpFzFuns f b` computes it, on `[par, out, s]` with
`s = 0` for `x` and `s = 1` for `y`:

1. the graph form of `G_(dom)`, the pointwise stabilizer in `G` of all domain points
   (`graphStabP_spec`);
2. for each test set `T` in turn (an `iterate` loop, `f + 4`):
   * the points outside the final window, by removing the increments of the log one by one
     (a `foldl` of the filter of the move program, `f + 8`; `cp_mem_outF_win`);
   * the test "`T` is full": the order `|φ_T(A_final)|` (`imgCardDet` with no fixed points)
     against `|Alt(T)| = D` (`cp_isFull_iff`);
   * when `T` is full, the graph form of `K(T) = (A_final)_{(Ω \ W_final)}`
     (`graphStabP_spec`, `graphOf_lift_fix`), appended to the list of pairs;
3. the first parts of all collected pairs, and one closure call (`clos_spec`) on the graph form of
   `G` (`cp_pairGens_clos`).

The first parts of the collected pairs generate the lift of `F_z` on positions: the lift of a join
is the join of the lifts and of `G_(dom)` (`cp_lift_iSup₂`). This file gives the program and the
mathematics of its loop invariant (`cp_fz_final`). The program proofs are in `AggCertFzSpec.lean`.

The library modules come from the move program (`CpMvAt`): the stabilizer, the filter, the order
module inside the increment program, append, the map of first parts and the closure.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)

/-! ### The program -/

section Prog

variable (f b : ℕ)

/-- **The entry**, on `[par, out, s]`: the stabilizer of the domain points, the loop over the
test sets, the first parts, the closure. -/
def cpFzE : Expr :=
  .letE (.call (cpStab b) (mk3 (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2))
      (.get (arg 0) (.nat 5))))
  (.letE (.call (f + 1) (mk3 (.var 0) (.length (.get (arg 1) (.nat 0))) (.var 1)))
  (.letE (.call (cpMapFst b) (mk2 (.nat 0) (.var 2)))
    (.call (cpClos b) (mk3 (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)) (.var 3)))))

/-- **One test set**, on `[[par, out, s], i, acc]`: the final group `pz` of the string, the log,
the outside points, the order of the image, and when it is `D`, the stabilizer of the outside
points appended to `acc`. -/
def cpFzStepE : Expr :=
  .letE (.get (.get (.get (.get (arg 0) (.nat 1)) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 2)))
  (.letE (.get (.get (.get (arg 0) (.nat 1)) (.nat 1)) (arg 1))
  (.letE (.call (f + 5) (mk3 (.nat 0) (.get (.var 2) (.arith .add (.get (arg 0) (.nat 2)) (.nat 1)))
      (.get (.get (arg 0) (.nat 0)) (.nat 5))))
  (.letE (.call (cpInc b + 1) (mk5 (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.var 1) .nil
      (.get (.get (.var 2) (.nat 0)) (.nat 1)) (.get (.get (arg 0) (.nat 0)) (.nat 4))))
    (.ite (.arith .eq (.var 4) (.get (.get (arg 0) (.nat 0)) (.nat 4)))
      (.letE (.call (cpStab b) (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.var 1) (.var 3)))
        (.call (cpApp b) (mk2 (arg 2) (.var 5))))
      (arg 2)))))

/-- **One stage**, on `[c, os, stage]`: the points of `os` not in the increment of the stage. -/
def cpFzFiltE : Expr := .call (cpFilt b) (mk2 (.get (arg 2) (.nat 1)) (arg 1))

/-- **The functions of the program**, at base `f` (nine functions). -/
def cpFzFuns : List Expr :=
  [cpFzE f b] ++ iterFuns (f + 1) (f + 4) ++ [cpFzStepE f b] ++ foldlFuns (f + 5) (f + 8) ++
    [cpFzFiltE b]

/-- Where the program sits. -/
structure CpFzAt (P : Program) (f b : ℕ) : Prop where
  entry : P.funs[f]? = some (cpFzE f b)
  iter : P.HasAt (f + 1) (iterFuns (f + 1) (f + 4))
  step : P.funs[f + 4]? = some (cpFzStepE f b)
  fold : P.HasAt (f + 5) (foldlFuns (f + 5) (f + 8))
  filt : P.funs[f + 8]? = some (cpFzFiltE b)

theorem cpFzAt_of {P : Program} (h : P.HasAt f (cpFzFuns f b)) : CpFzAt P f b where
  entry := by simpa using (h.block 0 (gs := [cpFzE f b]) (by rfl)).single
  iter := h.block 1 (by rfl)
  step := by simpa using (h.block 4 (gs := [cpFzStepE f b]) (by rfl)).single
  fold := h.block 5 (by rfl)
  filt := by simpa using (h.block 8 (gs := [cpFzFiltE b]) (by rfl)).single

end Prog

/-! ### The mathematics of the loop -/

section Math

set_option linter.unusedSectionVars false

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : GiantLabels S} (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- The pointwise stabilizer of all points is trivial. -/
theorem cp_fix_univ (A : Subgroup (Perm S.dom)) : fix A Set.univ = ⊥ := by
  ext g
  rw [mem_fix, Subgroup.mem_bot]
  constructor
  · rintro ⟨-, h⟩
    exact Equiv.ext fun u => h u (Set.mem_univ u)
  · rintro rfl
    exact ⟨A.one_mem, fun _ _ => rfl⟩

/-- **The graph form of `G_(dom)`**: the pairs of the graph of `G` that fix every domain
position. -/
theorem cp_pairGens_ker {gp : GPairs k L.q} (hgp : PairGens e L S.G gp)
    {osL : List S.dom} (hall : ∀ v, v ∈ osL) {qs : GPairs k L.q}
    (hqs : Subgroup.closure {p | p ∈ qs} =
      Subgroup.closure {p | p ∈ gp} ⊓ fixPts k L.q (osL.map (domPos e L.q))) :
    PairGens e L (S.liftGroup ⊥) qs := by
  have hX : ∀ j, j ∈ osL.map (domPos e L.q) ↔
      ∃ u ∈ (Set.univ : Set S.dom), Fin.castAdd L.q (e (u : Ω)) = j := by
    intro j
    simp only [List.mem_map, Set.mem_univ, true_and]
    exact ⟨fun ⟨u, _, h⟩ => ⟨u, h⟩, fun ⟨u, h⟩ => ⟨u, hall u, h⟩⟩
  have h := graphOf_lift_fix (e := e) (L := L) S.domGroup hX
  rw [cp_fix_univ, S.liftGroup_domGroup] at h
  unfold PairGens at *
  rw [hqs, hgp, h]

/-- **The graph form of `K(T)`**: the pairs of the graph of the lift of the final group that fix
the positions of the points outside the final window. -/
theorem cp_pairGens_full {T : Finset (Fin L.q)} {z : Ω → C} {pz : GPairs k L.q}
    (hpz : PairGens e L (S.liftGroup (finalGrp (cpPhi S πd T) (dstr S z))) pz)
    {oL : List S.dom} (ho : ∀ v, v ∈ oL ↔ v ∉ finalWin (cpPhi S πd T) (dstr S z))
    {qs : GPairs k L.q}
    (hqs : Subgroup.closure {p | p ∈ qs} =
      Subgroup.closure {p | p ∈ pz} ⊓ fixPts k L.q (oL.map (domPos e L.q))) :
    PairGens e L (S.liftGroup (fullCert (cpPhi S πd T) (dstr S z))) qs := by
  have hX : ∀ j, j ∈ oL.map (domPos e L.q) ↔
      ∃ u ∈ outside (finalWin (cpPhi S πd T) (dstr S z)), Fin.castAdd L.q (e (u : Ω)) = j := by
    intro j
    simp only [List.mem_map, outside, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, h⟩; exact ⟨u, (ho u).1 hu, h⟩
    · rintro ⟨u, hu, h⟩; exact ⟨u, (ho u).2 hu, h⟩
  have h := graphOf_lift_fix (e := e) (L := L) (finalGrp (cpPhi S πd T) (dstr S z)) hX
  unfold PairGens at *
  rw [hqs, hpz, h]

/-- The first parts of a graph form are positions of elements of `G`. -/
theorem cp_fst_mem_G {A : Subgroup (Perm Ω)} {qs : GPairs k L.q} (hqs : PairGens e L A qs)
    {p : Perm (Fin k) × Perm (Fin L.q)} (hp : p ∈ qs) : ∃ g ∈ S.G, toFin e g = p.1 := by
  have h : p ∈ Subgroup.closure {p | p ∈ qs} := Subgroup.subset_closure hp
  rw [hqs, mem_graphOf] at h
  obtain ⟨g, hg, -, h1, -⟩ := h
  exact ⟨g, hg, h1⟩

/-- The first parts of the graph form of a lift generate the lift on positions. -/
theorem cp_gens_lift {A : Subgroup (Perm S.dom)} {qs : GPairs k L.q}
    (hqs : PairGens e L (S.liftGroup A) qs) :
    gens (qs.map Prod.fst) = (S.liftGroup A).map (toFin e).toMonoidHom := by
  rw [cp_gens_fst hqs, inf_eq_left.2 (S.liftGroup_le _)]

/-- **The group that the first parts generate after `i` test sets**: `G_(dom)` and the lifts of
the full certificates of the full test sets among the first `i`. -/
noncomputable def cpFzGrp (Ts : List (Finset (Fin L.q))) (z : Ω → C) (i : ℕ) :
    Subgroup (Perm (Fin k)) :=
  (S.liftGroup ⊥).map (toFin e).toMonoidHom ⊔
    ⨆ (j : ℕ) (_ : j < i ∧ IsFull (cpPhi S πd (Ts.getD j ∅)) (dstr S z)),
      (S.liftGroup (fullCert (cpPhi S πd (Ts.getD j ∅)) (dstr S z))).map (toFin e).toMonoidHom

/-- No test set yet: the lift of `G_(dom)`. -/
theorem cpFzGrp_zero (Ts : List (Finset (Fin L.q))) (z : Ω → C) :
    cpFzGrp (e := e) πd Ts z 0 = (S.liftGroup ⊥).map (toFin e).toMonoidHom := by
  unfold cpFzGrp
  simp

/-- One more test set that is not full. -/
theorem cpFzGrp_succ_not (Ts : List (Finset (Fin L.q))) (z : Ω → C) (i : ℕ)
    (h : ¬ IsFull (cpPhi S πd (Ts.getD i ∅)) (dstr S z)) :
    cpFzGrp (e := e) πd Ts z (i + 1) = cpFzGrp (e := e) πd Ts z i := by
  unfold cpFzGrp
  congr 1
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    have hji : j < i := by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj.1 with h' | rfl
      · exact h'
      · exact absurd hj.2 h
    exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : j < i ∧ IsFull (cpPhi S πd (Ts.getD j ∅))
      (dstr S z)) => (S.liftGroup (fullCert (cpPhi S πd (Ts.getD j ∅)) (dstr S z))).map
        (toFin e).toMonoidHom) j ⟨hji, hj.2⟩ le_rfl
  · refine iSup₂_le fun j hj => ?_
    exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : j < i + 1 ∧ IsFull (cpPhi S πd (Ts.getD j ∅))
      (dstr S z)) => (S.liftGroup (fullCert (cpPhi S πd (Ts.getD j ∅)) (dstr S z))).map
        (toFin e).toMonoidHom) j ⟨by omega, hj.2⟩ le_rfl

/-- One more test set that is full. -/
theorem cpFzGrp_succ_full (Ts : List (Finset (Fin L.q))) (z : Ω → C) (i : ℕ)
    (h : IsFull (cpPhi S πd (Ts.getD i ∅)) (dstr S z)) :
    cpFzGrp (e := e) πd Ts z (i + 1) = cpFzGrp (e := e) πd Ts z i ⊔
      (S.liftGroup (fullCert (cpPhi S πd (Ts.getD i ∅)) (dstr S z))).map
        (toFin e).toMonoidHom := by
  unfold cpFzGrp
  rw [sup_assoc]
  congr 1
  set F := fun (j : ℕ) => (S.liftGroup (fullCert (cpPhi S πd (Ts.getD j ∅)) (dstr S z))).map
    (toFin e).toMonoidHom with hF
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj.1 with h' | rfl
    · exact le_sup_of_le_left (le_iSup₂_of_le (f := fun (j : ℕ) (_ : j < i ∧
        IsFull (cpPhi S πd (Ts.getD j ∅)) (dstr S z)) => F j) j ⟨h', hj.2⟩ le_rfl)
    · exact le_sup_right
  · refine sup_le (iSup₂_le fun j hj => ?_) ?_
    · exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : j < i + 1 ∧
        IsFull (cpPhi S πd (Ts.getD j ∅)) (dstr S z)) => F j) j ⟨by omega, hj.2⟩ le_rfl
    · exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : j < i + 1 ∧
        IsFull (cpPhi S πd (Ts.getD j ∅)) (dstr S z)) => F j) i ⟨by omega, h⟩ le_rfl

/-- **After all test sets**, the group is the lift of `F_z` on positions, when the list lists
every `κ`-subset. -/
theorem cp_fz_final (Ts : List (Finset (Fin L.q))) (hTs : ∀ T, T ∈ Ts ↔ T.card = P₀.κ)
    (z : Ω → C) :
    cpFzGrp (e := e) πd Ts z Ts.length =
      (S.liftGroup (certGroup S πd P₀.κ (dstr S z))).map (toFin e).toMonoidHom := by
  have hle : ∀ T, fullCert (phiT S.domGroup πd T) (dstr S z) ≤ S.domGroup := fun T _ hg =>
    Pgrp_le ((fullCert_le_automorphisms _ (dstr S z)) hg).1
  have hlift := cp_lift_iSup₂ S (fun T : Finset (Fin L.q) => T.card = P₀.κ ∧
      IsFull (phiT S.domGroup πd T) (dstr S z))
    (fun T => fullCert (phiT S.domGroup πd T) (dstr S z)) hle
  unfold certGroup
  rw [hlift, Subgroup.map_sup]
  unfold cpFzGrp
  congr 1
  simp only [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    have hm : Ts.getD j ∅ ∈ Ts := by
      rw [List.getD_eq_getElem _ _ hj.1]; exact List.getElem_mem _
    exact le_iSup₂_of_le (f := fun (T : Finset (Fin L.q))
      (_ : T.card = P₀.κ ∧ IsFull (phiT S.domGroup πd T) (dstr S z)) =>
        (S.liftGroup (fullCert (phiT S.domGroup πd T) (dstr S z))).map (toFin e).toMonoidHom)
      (Ts.getD j ∅) ⟨(hTs _).1 hm, hj.2⟩ le_rfl
  · refine iSup₂_le fun T hT => ?_
    obtain ⟨j, hj, hjT⟩ := List.getElem_of_mem ((hTs T).2 hT.1)
    have hd : Ts.getD j ∅ = T := by rw [List.getD_eq_getElem _ _ hj, hjT]
    subst hd
    exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : j < Ts.length ∧
      IsFull (cpPhi S πd (Ts.getD j ∅)) (dstr S z)) =>
        (S.liftGroup (fullCert (cpPhi S πd (Ts.getD j ∅)) (dstr S z))).map
          (toFin e).toMonoidHom) j ⟨hj, hT.2⟩ le_rfl

/-- The generators of an appended list of pairs. -/
theorem cp_gens_fst_append (qs qs' : GPairs k L.q) :
    gens ((qs ++ qs').map Prod.fst) = gens (qs.map Prod.fst) ⊔ gens (qs'.map Prod.fst) := by
  rw [List.map_append, cp_gens_append]

end Math

end GI.Impl
