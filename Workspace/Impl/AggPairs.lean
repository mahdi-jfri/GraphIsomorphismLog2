import Workspace.Impl.AggGraph
import Workspace.Impl.Lift
import Workspace.Impl.GiantNat

/-!
# Splitting an encoded pair, in `GI.Lang`

The cited tasks return the graph form of a subgroup as permutations `a ⊕ b` of `Fin (k + q)`
(`encPair`, `Workspace/Impl/AggGraph.lean`). The program splits each into its two parts.

* `rightF` on `[[k, a ⊕ b], j]` returns `b j`: entry `k + j` of `a ⊕ b` is `k + b j`
  (`rightF_spec`).
* `pSplitFuns` on `[[k, x], [1_k, 1_q]]` (the identities give the position lists) returns
  `[a, b]` for `x = a ⊕ b` (`pSplit_spec`): the first `k` entries by `gather`, the rest by a map
  of `rightF`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm gens sumToFin)

variable {k q : ℕ}

/-- On `[[k, x], j]`: `x (k + j) - k`. -/
def rightF : Expr :=
  .arith .sub (.get (.get (arg 0) (.nat 1)) (.arith .add (.get (arg 0) (.nat 0)) (arg 1)))
    (.get (arg 0) (.nat 0))

/-- The cost constant of `rightF`. -/
def rightK : ℕ := 1000

theorem rightF_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some rightF)
    (p : Perm (Fin k) × Perm (Fin q)) (j : Fin q) :
    FunDet P f (.list [.list [.nat k, encPerm (encPair p)], .nat j]) (.nat (p.2 j))
      (rightK * (k + q + 1) ^ 2) := by
  set B := Val.list [.nat k, encPerm (encPair p)] with hB
  set A := Val.list [B, .nat j] with hA
  have g0 := Det.arg' (P := P) (vs := [B, .nat j]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [B, .nat j]) (rest := []) (j := 1) rfl
  have gk := Det.get' g0 (Det.nat 0) (v := .nat k) rfl
  have gx := Det.get' g0 (Det.nat 1) (v := encPerm (encPair p)) rfl
  have gi := Det.arith' (op := .add) gk g1 (z := k + j) rfl
  have hent : (encPerm (encPair p) : Val) =
      .list ((List.finRange (k + q)).map fun i => Val.nat (encPair p i)) := rfl
  have hidx : ((List.finRange (k + q)).map fun i => Val.nat (encPair p i))[k + (j : ℕ)]? =
      some (.nat (k + p.2 j)) := by
    have hlt : k + (j : ℕ) < k + q := by omega
    have := sumToFin_sumCongr_natAdd p.1 p.2 j
    have hl : k + (j : ℕ) < (List.finRange (k + q)).length := by simp
    rw [List.getElem?_map, List.getElem?_eq_getElem hl]
    simp only [Option.map_some, Option.some.injEq, Val.nat.injEq, List.getElem_finRange]
    rw [encPair_eq]
    exact this
  rw [hent] at gx
  have gv := Det.get' gx gi hidx
  have gs := Det.arith' (op := .sub) gv gk (z := p.2 j) (by simp [BinOp.eval])
  refine FunDet.intro hf (gs.mono ?_)
  have w1 := wt_encPerm_le (encPair p)
  have w2 := wt_list2_le (.nat k) (encPerm (encPair p))
  have w3 := wt_list2_le B (.nat j)
  have w4 := wt_nat_le k
  have w5 := wt_nat_le (j : ℕ)
  have w6 := wt_nat_le (k + (j : ℕ))
  have w7 := wt_nat_le (k + ((p.2 j : Fin q) : ℕ))
  have w8 := wt_nat_le ((p.2 j : Fin q) : ℕ)
  have hj := j.isLt
  have hpj := (p.2 j).isLt
  have hN : k + q + 1 ≤ (k + q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have eB : B.wt = (Val.list [.nat k, encPerm (encPair p)]).wt := rfl
  have ex : (Val.list ((List.finRange (k + q)).map fun i => Val.nat (encPair p i))).wt =
    (encPerm (encPair p)).wt := rfl
  simp only [rightK]
  omega

/-- `map rightF` at base `b` (four functions). -/
def rightMapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [rightF]

/-- The cost constant of the split. -/
def aggSplitK : ℕ := 10 ^ 9

theorem rightMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (rightMapFuns b))
    (p : Perm (Fin k) × Perm (Fin q)) :
    FunDet P b (.list [.list [.nat k, encPerm (encPair p)], encPerm (1 : Perm (Fin q))])
      (encPerm p.2) (aggSplitK * (k + q + 1) ^ 3) := by
  have hf : P.funs[b + 3]? = some rightF := by
    simpa [rightMapFuns, mapFuns, loopFuns] using h.right.single
  have hm := mapList_spec h.left (List.finRange q) (fun j : Fin q => Val.nat (j : ℕ)) (fun j : Fin q => Val.nat (p.2 j : ℕ))
    (c := .list [.nat k, encPerm (encPair p)]) (B := rightK * (k + q + 1) ^ 2)
    (fun a _ a' _ he => by
      simp only [Val.nat.injEq] at he
      rw [Fin.ext he])
    (fun j _ => rightF_spec hf p j)
  have e1 : Val.list ((List.finRange q).map fun j : Fin q => Val.nat (j : ℕ)) =
      encPerm (1 : Perm (Fin q)) := rfl
  have e2 : Val.list ((List.finRange q).map fun j : Fin q => Val.nat (p.2 j : ℕ)) = encPerm p.2 := rfl
  rw [e1, e2] at hm
  refine hm.mono ?_
  simp only [List.length_finRange]
  set N := k + q + 1 with hN
  have w1 := wt_encPerm_le (encPair p)
  have w2 := wt_encPerm_le (1 : Perm (Fin q))
  have w3 := wt_encPerm_le p.2
  have w4 := wt_list2_le (.nat k) (encPerm (encPair p))
  have w5 := wt_list2_le (.list [.nat k, encPerm (encPair p)]) (encPerm (1 : Perm (Fin q)))
  have w6 := wt_nat_le k
  have hq1 : q + 1 ≤ N := by omega
  have hk1 : k + q + 1 = N := rfl
  have e3 : (k + q + 1) ^ 2 = N ^ 2 := rfl
  have h4q : 4 * (q + 1) ^ 2 ≤ 4 * N ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq1 2)
  have h4kq : 4 * (k + q + 1) ^ 2 ≤ 4 * N ^ 2 := le_refl _
  have hW : (Val.list [Val.list [Val.nat k, encPerm (encPair p)], encPerm (1 : Perm (Fin q))]).wt
      + (encPerm p.2).wt + 1 ≤ 60 * N ^ 2 := by
    have hN2 : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have h1 : q * (rightK * N ^ 2) ≤ rightK * N ^ 3 := by
    have : q * (rightK * N ^ 2) ≤ N * (rightK * N ^ 2) := Nat.mul_le_mul_right _ (by omega)
    calc _ ≤ _ := this
      _ = rightK * N ^ 3 := by ring
  have h2 : mapK * (q + 1) * ((Val.list [Val.list [Val.nat k, encPerm (encPair p)],
      encPerm (1 : Perm (Fin q))]).wt + (encPerm p.2).wt + 1) ≤ mapK * N * (60 * N ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hq1) hW
  have h3 : mapK * N * (60 * N ^ 2) = 60000 * N ^ 3 := by simp only [mapK]; ring
  simp only [aggSplitK, rightK] at *
  omega

/-- The value of a pair: `[a, b]`. -/
def pairV (p : Perm (Fin k) × Perm (Fin q)) : Val := .list [encPerm p.1, encPerm p.2]

theorem pairV_injective : Function.Injective (pairV (k := k) (q := q)) := by
  intro p p' h
  simp only [pairV, Val.list.injEq, List.cons.injEq, and_true] at h
  exact Prod.ext (encPerm_injective h.1) (encPerm_injective h.2)

/-- The value `[1_k, 1_q]` of the position lists. -/
def idsVal (k q : ℕ) : Val := .list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))]

/-- The context of the split: `[k, [1_k, 1_q]]`. -/
def pSplitCtx (k q : ℕ) : Val := .list [.nat k, idsVal k q]

/-- On `[[k, [1_k, 1_q]], x]`: `[a, b]` for `x = a ⊕ b`. Gather sits at `b + 1`, the right map
at `b + 5`. -/
def pSplitF (b : ℕ) : Expr :=
  mk2 (.call (b + 1) (mk2 (arg 1) (.get (.get (arg 0) (.nat 1)) (.nat 0))))
    (.call (b + 5) (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (.get (arg 0) (.nat 1)) (.nat 1))))

/-- The split module at base `b` (nine functions). -/
def pSplitFuns (b : ℕ) : List Expr := [pSplitF b] ++ gatherFuns (b + 1) ++ rightMapFuns (b + 5)

/-- The cost bound of one split. -/
def pSplitCost (k q : ℕ) : ℕ := 10 ^ 11 * (k + q + 1) ^ 6

theorem pSplit_spec {P : Program} {b : ℕ} (h : P.HasAt b (pSplitFuns b))
    (p : Perm (Fin k) × Perm (Fin q)) :
    FunDet P b (.list [pSplitCtx k q, encPerm (encPair p)]) (pairV p) (pSplitCost k q) := by
  have hf : P.funs[b]? = some (pSplitF b) := by
    simpa [pSplitFuns] using (h.block 0 (gs := [pSplitF b]) (by rfl)).single
  have hg : P.HasAt (b + 1) (gatherFuns (b + 1)) := h.block 1 (by rfl)
  have hr : P.HasAt (b + 5) (rightMapFuns (b + 5)) := h.block 5 (by rfl)
  set A := Val.list [pSplitCtx k q, encPerm (encPair p)] with hA
  have g0 := Det.arg' (P := P) (vs := [pSplitCtx k q, encPerm (encPair p)])
    (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [pSplitCtx k q, encPerm (encPair p)])
    (rest := []) (j := 1) rfl
  have gk := Det.get' g0 (Det.nat 0) (v := .nat k) rfl
  have gI := Det.get' g0 (Det.nat 1) (v := idsVal k q) rfl
  have gik := Det.get' gI (Det.nat 0) (v := encPerm (1 : Perm (Fin k))) rfl
  have giq := Det.get' gI (Det.nat 1) (v := encPerm (1 : Perm (Fin q))) rfl
  have hl := gatherLeft_spec hg p.1 p.2
  rw [← encPair_eq] at hl
  have dl := Det.call (Det.mk2 g1 gik) hl
  have dr := Det.call (Det.mk2 (Det.mk2 gk g1) giq) (rightMap_spec hr p)
  refine FunDet.intro hf ((Det.mk2 dl dr).mono ?_)
  set N := k + q + 1 with hN
  have w1 := wt_encPerm_le (encPair p)
  have w2 := wt_encPerm_le (1 : Perm (Fin k))
  have w3 := wt_encPerm_le (1 : Perm (Fin q))
  have w4 := wt_encPerm_le p.1
  have w5 := wt_encPerm_le p.2
  have w6 := wt_list2_le (.nat k) (encPerm (encPair p))
  have w7 := wt_list2_le (encPerm (1 : Perm (Fin k))) (encPerm (1 : Perm (Fin q)))
  have w8 := wt_list2_le (pSplitCtx k q) (encPerm (encPair p))
  have w9 := wt_list2_le (encPerm (encPair p)) (encPerm (1 : Perm (Fin k)))
  have w10 := wt_list2_le (.list [.nat k, encPerm (encPair p)]) (encPerm (1 : Perm (Fin q)))
  have w11 := wt_list2_le (encPerm p.1) (encPerm p.2)
  have w13 := wt_list2_le (.nat k) (idsVal k q)
  have w12 := wt_nat_le k
  have hk1 : (k + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hq1 : (q + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hkq : (k + q + 1) ^ 2 = N ^ 2 := rfl
  have eI : (idsVal k q).wt =
      (Val.list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))]).wt := rfl
  have eC : (pSplitCtx k q).wt = (Val.list [.nat k, idsVal k q]).wt := rfl
  have eP : (pairV p).wt = (Val.list [encPerm p.1, encPerm p.2]).wt := rfl
  have hN1 : 1 ≤ N := by omega
  have hN2 : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) _
  have hN23 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right hN1 (by omega)
  have hN36 : N ^ 3 ≤ N ^ 6 := Nat.pow_le_pow_right hN1 (by omega)
  have hG : (40 * N ^ 2) ^ 3 = 64000 * N ^ 6 := by ring
  have hR6 : (k + q + 1) ^ 6 = N ^ 6 := rfl
  have hk2 : k ≤ N ^ 2 := le_trans (by omega) hN2
  have hI : (idsVal k q).wt ≤ 16 * N ^ 2 + 6 := by omega
  have hC : (pSplitCtx k q).wt ≤ 40 * N ^ 2 + 30 := by omega
  have hP : (encPerm (encPair p)).wt ≤ 4 * N ^ 2 := by
    have : (k + q + 1) ^ 2 = N ^ 2 := rfl
    omega
  have hWA : A.wt ≤ 200 * N ^ 2 := by
    have : A.wt = (Val.list [pSplitCtx k q, encPerm (encPair p)]).wt := rfl
    have : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN1
    omega
  simp only [pSplitCost, aggSplitK, gatherK] at *
  omega

/-- `map split` at base `b` (thirteen functions). -/
def pSplitMapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ pSplitFuns (b + 3)

/-- **Splitting a list of encoded pairs.** -/
theorem pSplitMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (pSplitMapFuns b))
    (ps : List (Perm (Fin k) × Perm (Fin q))) :
    FunDet P b (.list [pSplitCtx k q, .list (ps.map fun p => encPerm (encPair p))])
      (.list (ps.map pairV))
      (ps.length * pSplitCost k q + mapK * (ps.length + 1) *
        ((Val.list [pSplitCtx k q, .list (ps.map fun p => encPerm (encPair p))]).wt +
          (Val.list (ps.map pairV)).wt + 1)) :=
  mapList_spec h.left ps (fun p => encPerm (encPair p)) pairV
    (fun a _ a' _ he => by rw [encPair_injective (encPerm_injective he)])
    (fun p _ => pSplit_spec (h.block 3 (by rfl)) p)

/-! ### Encoding a list of pairs -/

/-- `map graphStep` at base `b` (thirteen functions): on `[k, [[a, b], …]]`, the list of the
`a ⊕ b`. Layout: map at `b`, a filler at `b + 3`, `shiftApp` at `b + 4`, append at `b + 5`,
the shift map at `b + 8`, `addK` at `b + 11`, `graphStep` at `b + 12`. -/
def pEncMapFuns (b : ℕ) : List Expr :=
  mapFuns b (b + 12) ++ [.nat 0] ++ [shiftAppF (b + 5) (b + 8)] ++ appendFuns (b + 5) ++
    mapFuns (b + 8) (b + 11) ++ [addKF] ++ [graphStepF (b + 4)]

/-- The cost bound of encoding one pair. -/
def pEncCost (k q : ℕ) : ℕ := natStepK * (k + q + 1) ^ 3

theorem pEncMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (pEncMapFuns b))
    (ps : List (Perm (Fin k) × Perm (Fin q))) :
    FunDet P b (.list [.nat k, .list (ps.map pairV)]) (.list (ps.map fun p => encPerm (encPair p)))
      (ps.length * pEncCost k q + mapK * (ps.length + 1) *
        ((Val.list [.nat k, .list (ps.map pairV)]).wt +
          (Val.list (ps.map fun p => encPerm (encPair p))).wt + 1)) := by
  have hsa : P.funs[b + 4]? = some (shiftAppF (b + 5) (b + 8)) := by
    simpa using (h.block 4 (gs := [shiftAppF (b + 5) (b + 8)]) (by rfl)).single
  have hap : P.HasAt (b + 5) (appendFuns (b + 5)) := h.block 5 (by rfl)
  have ham : P.HasAt (b + 8) (mapFuns (b + 8) (b + 11)) := h.block 8 (by rfl)
  have hadd : P.funs[b + 11]? = some addKF := by
    simpa using (h.block 11 (gs := [addKF]) (by rfl)).single
  have hgs : P.funs[b + 12]? = some (graphStepF (b + 4)) := by
    simpa using (h.block 12 (gs := [graphStepF (b + 4)]) (by rfl)).single
  refine mapList_spec (h.block 0 (by rfl)) ps pairV (fun p => encPerm (encPair p))
    (fun a _ a' _ he => by rw [pairV_injective he]) (fun p _ => ?_)
  have := graphStep_spec (b := b + 3) hsa hap ham hadd hgs p.1 p.2
  rw [← encPair_eq] at this
  exact this

end GI.Impl
