module

public import Workspace.Impl.AggCertHand
public import Workspace.Impl.AggSubProg
public import Workspace.Impl.RowProg
public import Workspace.Impl.DomRestrict

@[expose] public section

/-!
# The reading of the aggregation round, as a program

On the input `[sv, lv]` of a `GiantStep` call in the aggregation case, the reading builds the
start state of the certificate phase (`cpInitV`, the relation `CpHand` of
`Workspace/Impl/AggCertHand.lean`) and the context of `LiftAndContinue` (`lcCtx`). It reads
the number of positions `k` and the domain indicator from `sv`, and `q`, the graph pairs `ps` of
`G` and the selected interval from `lv`. Then it computes, in this order:

1. the positions of the domain (`domList_spec`); their number is `n = |dom|`;
2. the values of the test sets in the order `sbOrder q κ` (`sb_spec`), and the list without the
   first one (`tail_spec`);
3. the identities `[1_k, 1_q]` (`range_det`), for the split context `pSplitCtx k q`;
4. the groups `Ĥ` and `N̂` of the label lift (`grp_spec`, `fstMap_spec`);
5. the graph form of `P_T` for the first test set `T` (`ptGraph_spec`, one **Preimage** call).

The result is `[st, ctx]` with `st = cpInitV sv k q n ps osA T Ts p0` and
`ctx = lcCtx sv k q ps sel ⌊9q/10⌋` (`rd_out_eq`). The parent data `cpParV` of the phase hold
`D = κ!/2` as a number.

Layout of the module at base `b` (`rdFuns`): domain list at `b`, range at `b + 25`, tail at
`b + 28`, test sets at `b + 31`, `P_T` at `b + 63`, pair encoding at `b + 126`, `mkGroup` at
`b + 139`, the map `(a, b) ↦ (a, 1)` at `b + 146`, the group of pairs at `b + 150`.
The entry `rdF b` may sit anywhere.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)

/-! ### The program -/

/-- The functions of the reading at base `b`, with **Preimage** at `jpre`. -/
def rdFuns (b jpre : ℕ) : List Expr :=
  domFuns b ++ rangeFuns (b + 25) ++ tailFuns (b + 28) ++ sbFuns (b + 31) ++
    ptFuns (b + 63) jpre ++ pEncMapFuns (b + 126) ++ mkGroupFuns (b + 139) ++
    fstMapFuns (b + 146) ++ [grpF (b + 126) (b + 139)]

/-- The modules of the reading, at their places. -/
structure RdAt (P : Program) (b jpre : ℕ) : Prop where
  dom : DomAt P b
  rng : P.HasAt (b + 25) (rangeFuns (b + 25))
  tl : P.HasAt (b + 28) (tailFuns (b + 28))
  sb : P.HasAt (b + 31) (sbFuns (b + 31))
  pt : P.HasAt (b + 63) (ptFuns (b + 63) jpre)
  en : P.HasAt (b + 126) (pEncMapFuns (b + 126))
  mkg : P.HasAt (b + 139) (mkGroupFuns (b + 139))
  fm : P.HasAt (b + 146) (fstMapFuns (b + 146))
  gr : P.funs[b + 150]? = some (grpF (b + 126) (b + 139))

private theorem rd_hasAt_shift {P : Program} {b n m : ℕ} {fs : List Expr} (h : P.HasAt (b + n) fs)
    (hm : n = m) : P.HasAt (b + m) fs := hm ▸ h

theorem rdAt_of {P : Program} {b jpre : ℕ} (h : P.HasAt b (rdFuns b jpre)) : RdAt P b jpre := by
  have l1 : (domFuns b).length = 25 := rfl
  have l2 : (rangeFuns (b + 25)).length = 3 := rfl
  have l3 : (tailFuns (b + 28)).length = 3 := rfl
  have l4 : (sbFuns (b + 31)).length = 32 := rfl
  have l5 : (ptFuns (b + 63) jpre).length = 63 := rfl
  have l6 : (pEncMapFuns (b + 126)).length = 13 := rfl
  have l7 : (mkGroupFuns (b + 139)).length = 7 := rfl
  have l8 : (fstMapFuns (b + 146)).length = 4 := rfl
  unfold rdFuns at h
  have h8 := h.left
  have h7 := h8.left
  have h6 := h7.left
  have h5 := h6.left
  have h4 := h5.left
  have h3 := h4.left
  have h2 := h3.left
  have h1 : P.HasAt b (domFuns b) := h2.left
  refine ⟨domAt_of_hasAt h1, rd_hasAt_shift h2.right (by rw [l1]),
    rd_hasAt_shift h3.right (by rw [List.length_append, l1, l2]),
    rd_hasAt_shift h4.right (by simp only [List.length_append, l1, l2, l3]),
    rd_hasAt_shift h5.right (by simp only [List.length_append, l1, l2, l3, l4]),
    rd_hasAt_shift h6.right (by simp only [List.length_append, l1, l2, l3, l4, l5]),
    rd_hasAt_shift h7.right (by simp only [List.length_append, l1, l2, l3, l4, l5, l6]),
    rd_hasAt_shift h8.right (by simp only [List.length_append, l1, l2, l3, l4, l5, l6, l7]),
    (rd_hasAt_shift h.right
      (by simp only [List.length_append, l1, l2, l3, l4, l5, l6, l7, l8])).single⟩

/-- `sv`. -/
def rdSv : Expr := .get (.var 0) (.nat 0)
/-- `lv`. -/
def rdLv : Expr := .get (.var 0) (.nat 1)
/-- `k`. -/
def rdK : Expr := .get rdSv (.nat 0)
/-- `q`. -/
def rdQ : Expr := .get rdLv (.nat 0)
/-- The pairs of `lv`. -/
def rdPs : Expr := .get rdLv (.nat 1)
/-- `[k, q]`. -/
def rdKQ : Expr := mk2 rdK rdQ

/-- The number `D = κ!/2` of even permutations of a test set. -/
def rdD : ℕ := Nat.factorial 64 / 2

/-- The result, in the environment `[[sv, lv], dom, sets, tail, ids, Ĥ, N̂, p0]`. -/
def rdOutE : Expr :=
  mk2
    (mk2
      (Expr.mkList [
        Expr.mkList [rdSv, rdKQ, rdPs, .length (.var 1), .nat rdD, .var 1, mk2 rdK (.var 4),
          .arith .add rdK rdQ],
        .var 3, .nat 0, .nil, .nil, .var 7, .nil, .nat 0, .var 7, .var 1, .nil,
        .get (.var 2) (.nat 0), .nil, .nil, .nil])
      (.nat 0))
    (Expr.mkList [rdSv, rdKQ, rdPs, mk4 rdK (.var 5) (.var 6) (mk2 rdK (.var 4)),
      .get rdLv (.nat 2), .arith .div (.arith .mul (.nat 9) rdQ) (.nat 10)])

/-- **The reading**, on `[sv, lv]`, for the module `rdFuns b jpre`. -/
def rdF (b : ℕ) : Expr :=
  .letE (.call b (.get rdSv (.nat 2)))
  (.letE (.call (b + 31) (mk3 rdK rdQ (.nat 64)))
  (.letE (.call (b + 28) (.var 2))
  (.letE (mk2 (.call (b + 25) rdK) (.call (b + 25) rdQ))
  (.letE (.call (b + 150) (mk2 rdKQ rdPs))
  (.letE (.call (b + 150) (mk2 rdKQ (.call (b + 146) (mk2 (.get (.var 4) (.nat 1)) rdPs))))
  (.letE (.call (b + 63) (mk3 rdKQ rdPs (.get (.get (.var 2) (.nat 0)) (.nat 0))))
    rdOutE))))))

theorem rd_kappa : P₀.κ = 64 := rfl

theorem rdD_eq : rdD = P₀.κ.factorial / 2 := rfl

/-! ### The domain points -/

section Dom

variable {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (q : ℕ)

/-- The domain points as positions of `Fin (k + q)`. -/
noncomputable def rdOsA : List (Fin (k + q)) := (domFin e S.dom).map (Fin.castAdd q)

theorem rd_encPts_osA : encPts (rdOsA e S q) = natList (domNat e S.dom) := by
  unfold rdOsA natList domNat
  generalize domFin e S.dom = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encPts, List.map_cons] at ih ⊢
    simp_all

theorem rd_length_osA : (rdOsA e S q).length = (domNat e S.dom).length := by
  simp [rdOsA, domNat]

/-- **The domain points are the whole domain** (`CpAll`). -/
theorem rd_cpAll : CpAll e S q (rdOsA e S q) := by
  classical
  refine ⟨(domFin e S.dom).pmap (fun i h => (⟨e.symm i, h⟩ : S.dom))
    (fun i hi => mem_domFin.1 hi), ?_, ?_, ?_⟩
  · refine List.Nodup.pmap (fun a ha b hb h => ?_) nodup_domFin
    exact e.symm.injective (congrArg Subtype.val h)
  · intro v
    refine List.mem_pmap.2 ⟨e v, mem_domFin.2 (by simp), ?_⟩
    exact Subtype.ext (e.symm_apply_apply _)
  · rw [List.map_pmap]
    simp only [domPos, Equiv.apply_symm_apply]
    rw [List.pmap_eq_map]
    rfl

/-- **The number of domain points** is the size of the domain. -/
theorem rd_card_dom (q : ℕ) [Fintype S.dom] : Fintype.card S.dom = (domNat e S.dom).length := by
  classical
  obtain ⟨os, hnd, hall, hos⟩ := rd_cpAll e S q
  have h1 : os.length = Fintype.card S.dom := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext v; simp [hall v]
  have h2 : (rdOsA e S q).length = os.length := by rw [hos, List.length_map]
  rw [← h1, ← h2, rd_length_osA]

end Dom

/-! ### The result -/

/-- **The value of the result.** With `dom` the list of domain positions, the test sets
`T :: Ts`, the identities, the two groups and the pairs `p0`, the result expression gives the
start state of the certificate phase and the context of `LiftAndContinue`. -/
theorem rd_out_eq {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) {q : ℕ}
    (sv : Val) (ps : List (Perm (Fin k) × Perm (Fin q))) (T : Finset (Fin q))
    (Ts : List (Finset (Fin q))) (p0 : GPairs k q) (sel : ℕ) :
    Val.list [
      Val.list [Val.list [
        Val.list [sv, .list [.nat k, .nat q], .list (ps.map pairV),
          .nat (domNat e S.dom).length, .nat rdD, natList (domNat e S.dom),
          .list [.nat k, idsVal k q], .nat (k + q)],
        .list (Ts.map (tsV k)), .nat 0, .list [], .list [], .list (p0.map pairV), .list [], .nat 0,
        .list (p0.map pairV), natList (domNat e S.dom), .list [], tsV k T, .list [], .list [],
        .list []], .nat 0],
      Val.list [sv, .list [.nat k, .nat q], .list (ps.map pairV),
        .list [.nat k, encGroup (ps.map encPair), encGroup ((onePairs ps).map encPair),
          .list [.nat k, idsVal k q]], .nat sel, .nat (9 * q / 10)]] =
    Val.list [cpInitV sv k q (domNat e S.dom).length ps (rdOsA e S q) T Ts p0,
      lcCtx sv k q ps sel (9 * q / 10)] := by
  simp only [cpInitV, CpSt.init, CpSt.val, cpParV, lcCtx, liftLabCtx, pSplitCtx, gpV,
    rd_encPts_osA, rdD_eq, List.map_nil, boolVal, Bool.toNat_false]

end GI.Impl
