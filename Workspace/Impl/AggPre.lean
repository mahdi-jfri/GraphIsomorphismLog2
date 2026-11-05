module

public import Workspace.Impl.AggGraphOps

@[expose] public section

/-!
# The preimage call on a graph group, in `GI.Lang`

`graphPre` runs the cited task **Preimage** on the graph group `{(a, π a) ⊕ π a}` of a list of
label pairs, with generators `ms` of a subgroup `M ≤ π(A)`. By `pairGens_labPre` its output, read
back as pairs, is the graph form of `A ∩ π⁻¹(M)`.

The program has five stages.
1. From the pairs `[a, b]` to the pairs `[a ⊕ b, b]` (`dsMap_spec`).
2. Encode each pair `(a ⊕ b, b)` as one permutation of `k + q + q` points (`pEncMap_spec`).
3. Make the group values of these permutations and of `ms` (`mkGroup_spec`).
4. Call **Preimage** (`preimage_call`).
5. Split the output generators back into pairs (`pSplitMap_spec`).

`graphPre_spec` is the result used later.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens sumToFin)

variable {k q : ℕ}

/-- The size parameter of a list of pairs: `k + q + (number of pairs) + 2`. -/
def pM (k q : ℕ) (ps : List (Perm (Fin k) × Perm (Fin q))) : ℕ := k + q + ps.length + 2

theorem wt_pairV_le (p : Perm (Fin k) × Perm (Fin q)) :
    (pairV p).wt ≤ 22 * (k + q + 1) ^ 2 := by
  have h1 := wt_encPerm_le p.1
  have h2 := wt_encPerm_le p.2
  have h3 := wt_list2_le (encPerm p.1) (encPerm p.2)
  have e : (pairV p).wt = (Val.list [encPerm p.1, encPerm p.2]).wt := rfl
  have a1 : (k + 1) ^ 2 ≤ (k + q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have a2 : (q + 1) ^ 2 ≤ (k + q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have a3 : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem wt_pairList_le (ps : List (Perm (Fin k) × Perm (Fin q))) :
    (Val.list (ps.map pairV)).wt ≤ 50 * pM k q ps ^ 3 := by
  have h := wt_list_map_le ps pairV (W := 22 * (k + q + 1) ^ 2) fun p _ => wt_pairV_le p
  set M := pM k q ps with hM
  have a1 : (k + q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by rw [hM]; unfold pM; omega) 2
  have a2 : ps.length ≤ M := by rw [hM]; unfold pM; omega
  have a3 : ps.length * (2 * (22 * (k + q + 1) ^ 2) + 1) ≤ M * (45 * M ^ 2) :=
    Nat.mul_le_mul a2 (by have : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ (by rw [hM]; unfold pM; omega); omega)
  have a4 : M * (45 * M ^ 2) = 45 * M ^ 3 := by ring
  have a5 : 1 ≤ M ^ 3 := Nat.one_le_pow _ _ (by rw [hM]; unfold pM; omega)
  omega

/-- On `[k, [a, b]]`: `[a ⊕ b, b]` (with `graphStep` at `g`). -/
def dsStepF (g : ℕ) : Expr := mk2 (.call g (.var 0)) (.get (arg 1) (.nat 1))

/-- The pair `(a ⊕ b, b)`. -/
def dsPair (p : Perm (Fin k) × Perm (Fin q)) : Perm (Fin (k + q)) × Perm (Fin q) :=
  (encPair p, p.2)

/-- The cost constant of the first stage. -/
def dsK : ℕ := 10 ^ 10

/-- `map dsStep` at base `b`, with the encoding module `pEncMapFuns` at `b + 4`
(seventeen functions; `graphStep` sits at `b + 16`). -/
def dsMapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [dsStepF (b + 16)] ++ pEncMapFuns (b + 4)

theorem dsStep_spec {P : Program} {b : ℕ} (h : P.HasAt b (dsMapFuns b))
    (p : Perm (Fin k) × Perm (Fin q)) :
    FunDet P (b + 3) (.list [.nat k, pairV p]) (pairV (dsPair p)) (dsK * (k + q + 1) ^ 3) := by
  have hf : P.funs[b + 3]? = some (dsStepF (b + 16)) := by
    simpa using (h.block 3 (gs := [dsStepF (b + 16)]) (by rfl)).single
  have he : P.HasAt (b + 4) (pEncMapFuns (b + 4)) := h.block 4 (by rfl)
  have hsa : P.funs[b + 8]? = some (shiftAppF (b + 9) (b + 12)) := by
    simpa using (he.block 4 (gs := [shiftAppF (b + 4 + 5) (b + 4 + 8)]) (by rfl)).single
  have hap : P.HasAt (b + 9) (appendFuns (b + 9)) := he.block 5 (by rfl)
  have ham : P.HasAt (b + 12) (mapFuns (b + 12) (b + 15)) := he.block 8 (by rfl)
  have hadd : P.funs[b + 15]? = some addKF := by
    simpa using (he.block 11 (gs := [addKF]) (by rfl)).single
  have hgs : P.funs[b + 16]? = some (graphStepF (b + 8)) := by
    simpa using (he.block 12 (gs := [graphStepF (b + 4 + 4)]) (by rfl)).single
  have hG := graphStep_spec (b := b + 7) hsa hap ham hadd hgs p.1 p.2
  rw [← encPair_eq] at hG
  set A := Val.list [.nat k, pairV p] with hA
  have g0 := Det.var' (P := P) (env := [A]) (i := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [.nat k, pairV p]) (rest := []) (j := 1) rfl
  have db := Det.get' g1 (Det.nat 1) (v := encPerm p.2) rfl
  have dg := Det.call g0 hG
  refine FunDet.intro hf ((Det.mk2 dg db).mono ?_)
  have w1 := wt_pairV_le p
  have w2 := wt_list2_le (.nat k) (pairV p)
  have w3 := wt_nat_le k
  have w4 := wt_encPerm_le p.2
  have w5 := wt_encPerm_le (encPair p)
  have w6 := wt_list2_le (encPerm (encPair p)) (encPerm p.2)
  have e1 : (pairV (dsPair p)).wt = (Val.list [encPerm (encPair p), encPerm p.2]).wt := rfl
  set N := k + q + 1 with hN
  have a1 : (q + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have a2 : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) _
  have a3 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : (k + q + 1) ^ 2 = N ^ 2 := rfl
  have e3 : (k + q + 1) ^ 3 = N ^ 3 := rfl
  have eA : A.wt = (Val.list [.nat k, pairV p]).wt := rfl
  simp only [dsK, natStepK] at *
  omega

/-- **The first stage**: `[k, [[a, b], …]]` ↦ `[[a ⊕ b, b], …]`. -/
theorem dsMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (dsMapFuns b))
    (ps : List (Perm (Fin k) × Perm (Fin q))) :
    FunDet P b (.list [.nat k, .list (ps.map pairV)]) (.list (ps.map fun p => pairV (dsPair p)))
      (2 * dsK * pM k q ps ^ 4) := by
  have hm := mapList_spec (h.block 0 (by rfl)) ps pairV (fun p => pairV (dsPair p))
    (c := .nat k) (B := dsK * (k + q + 1) ^ 3)
    (fun a _ a' _ he => by rw [pairV_injective he]) (fun p _ => dsStep_spec h p)
  refine hm.mono ?_
  set M := pM k q ps with hM
  have hl : ps.length + 1 ≤ M := by rw [hM]; unfold pM; omega
  have hN : k + q + 1 ≤ M := by rw [hM]; unfold pM; omega
  have w1 := wt_pairList_le ps
  rw [← hM] at w1
  have w2 : (Val.list (ps.map fun p => pairV (dsPair p))).wt ≤ 400 * M ^ 3 := by
    have h1 := wt_pairList_le (ps.map dsPair)
    have e : (ps.map dsPair).map pairV = ps.map fun p => pairV (dsPair p) := by simp
    rw [e] at h1
    have h2 : pM (k + q) q (ps.map dsPair) ≤ 2 * M := by rw [hM]; unfold pM; simp; omega
    have h3 : pM (k + q) q (ps.map dsPair) ^ 3 ≤ (2 * M) ^ 3 := Nat.pow_le_pow_left h2 3
    have h4 : (2 * M) ^ 3 = 8 * M ^ 3 := by ring
    omega
  have w3 := wt_list2_le (.nat k) (.list (ps.map pairV))
  have w4 := wt_nat_le k
  have a1 : 1 ≤ M := by omega
  have a2 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right a1 (by omega)
  have a3 : (k + q + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left hN 3
  have a4 : ps.length * (dsK * (k + q + 1) ^ 3) ≤ M * (dsK * M ^ 3) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ a3)
  have a5 : M * (dsK * M ^ 3) = dsK * M ^ 4 := by ring
  have a6 : k ≤ M ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num : (3 : ℕ) ≠ 0) M)
  have a9 : 1 ≤ M ^ 3 := Nat.one_le_pow _ _ a1
  have a7 : mapK * (ps.length + 1) * ((Val.list [Val.nat k, Val.list (ps.map pairV)]).wt +
      (Val.list (ps.map fun p => pairV (dsPair p))).wt + 1) ≤ mapK * M * (600 * M ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hl) (by omega)
  have a8 : mapK * M * (600 * M ^ 3) = 600000 * M ^ 4 := by simp only [mapK]; ring
  simp only [dsK] at *
  omega

/-! ### The preimage call -/

open GI.Cited (Preimage preimageSet PreimageInst) in
/-- On `[[k, q], pairs, ms]`: the pairs of `A ∩ π⁻¹⟨ms⟩` (see the module docstring). The
environment after the `let`s: `[input, [a ⊕ b, b] list, encoded list, graph group, ms group,
preimage generators]`. -/
def graphPreEntry (b jpre : ℕ) : Expr :=
  let kE := Expr.get (arg 0) (.nat 0)
  let qE := Expr.get (arg 0) (.nat 1)
  .letE (.call (b + 1) (mk2 kE (arg 1)))
  (.letE (.call (b + 18) (mk2 (.arith .add kE qE) (.var 1)))
  (.letE (.call (b + 31) (mk2 (.arith .add (.arith .add kE qE) qE) (.var 2)))
  (.letE (.call (b + 31) (mk2 qE (arg 2)))
  (.letE (.prim jpre (mk3 (.arith .add kE qE) (.var 3) (.var 4)))
  (.call (b + 38) (mk2 (mk2 kE (mk2 (.call (b + 32) kE) (.call (b + 32) qE))) (.var 5)))))))

/-- The preimage module at base `b` (fifty functions), with the cited primitive at `jpre`. -/
def graphPreFuns (b jpre : ℕ) : List Expr :=
  [graphPreEntry b jpre] ++ dsMapFuns (b + 1) ++ pEncMapFuns (b + 18) ++ mkGroupFuns (b + 31) ++
    pSplitMapFuns (b + 38)

/-- The size parameter of a preimage call. -/
def preM (k q : ℕ) (ps : List (Perm (Fin k) × Perm (Fin q))) (ms : List (Perm (Fin q))) : ℕ :=
  k + q + ps.length + ms.length + 2

/-- The cost constant of the preimage module. -/
def graphPreK : ℕ := 10 ^ 14

open GI.Cited (Preimage preimageSet PreimageInst) in
/-- **The preimage call on a graph group.** For generators `ms` of a subgroup of the second
projection of the group of the pairs `ps`, the module returns pairs `qs` that generate the part of
that group whose second component lies in `⟨ms⟩`. -/
theorem graphPre_spec (h : Preimage) {P : Program} {b jpre : ℕ}
    (hb : P.HasAt b (graphPreFuns b jpre)) (hj : P.prims[jpre]? = some (preimagePrim h))
    (ps : List (Perm (Fin k) × Perm (Fin q))) (ms : List (Perm (Fin q)))
    (hms : ∀ m ∈ ms, ∃ p ∈ Subgroup.closure {p | p ∈ ps}, MonoidHom.snd _ _ p = m) :
    FunAll P b (.list [.list [.nat k, .nat q], .list (ps.map pairV), .list (ms.map encPerm)])
      (fun w c => ∃ qs : List (Perm (Fin k) × Perm (Fin q)), w = .list (qs.map pairV) ∧
        qs.length ≤ (k + q) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} =
          Subgroup.closure {p | p ∈ ps} ⊓ (gens ms).comap (MonoidHom.snd _ _) ∧
        c ≤ (preimagePrim h).bound (preimageEnc (pairInst (MonoidHom.snd _ _) ps ms hms)) +
          graphPreK * preM k q ps ms ^ 8) := by
  have hentry : P.funs[b]? = some (graphPreEntry b jpre) := by
    simpa using (hb.block 0 (gs := [graphPreEntry b jpre]) (by rfl)).single
  have hds : P.HasAt (b + 1) (dsMapFuns (b + 1)) := hb.block 1 (by rfl)
  have hen : P.HasAt (b + 18) (pEncMapFuns (b + 18)) := hb.block 18 (by rfl)
  have hmk : P.HasAt (b + 31) (mkGroupFuns (b + 31)) := hb.block 31 (by rfl)
  have hrg : P.HasAt (b + 32) (rangeFuns (b + 32)) := hmk.block 1 (by rfl)
  have hsp : P.HasAt (b + 38) (pSplitMapFuns (b + 38)) := hb.block 38 (by rfl)
  set I := pairInst (MonoidHom.snd _ _) ps ms hms with hI
  set A : Val := .list [.list [.nat k, .nat q], .list (ps.map pairV), .list (ms.map encPerm)]
    with hA
  set D : Val := .list (ps.map fun p => pairV (dsPair p)) with hD
  set E : Val := .list ((ps.map dsPair).map fun p => encPerm (encPair p)) with hE
  set GD : Val := encGroup ((ps.map dsPair).map encPair) with hGD
  set GM : Val := encGroup ms with hGM
  -- reading the input
  have gkq := Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
    .list (ms.map encPerm)]) (rest := []) (j := 0) rfl
  have gk : ∀ rest : List Val, Det P (A :: rest) (.get (arg 0) (.nat 0)) (.nat k) _ :=
    fun rest => Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
      .list (ms.map encPerm)]) (rest := rest) (j := 0) rfl) (Det.nat 0) (v := .nat k) rfl
  have gq : ∀ rest : List Val, Det P (A :: rest) (.get (arg 0) (.nat 1)) (.nat q) _ :=
    fun rest => Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV),
      .list (ms.map encPerm)]) (rest := rest) (j := 0) rfl) (Det.nat 1) (v := .nat q) rfl
  -- stage 1
  have d1 := Det.call (Det.mk2 (gk []) (Det.arg' (P := P) (vs := [.list [.nat k, .nat q],
    .list (ps.map pairV), .list (ms.map encPerm)]) (rest := []) (j := 1) rfl)) (dsMap_spec hds ps)
  -- stage 2
  have hE2 := pEncMap_spec hen (ps.map dsPair)
  have eD : Val.list ((ps.map dsPair).map pairV) = D := by simp [hD]
  rw [eD] at hE2
  have d2 := Det.call (Det.mk2 (Det.arith' (op := .add) (gk [D]) (gq [D]) (z := k + q) rfl)
    (Det.var' (P := P) (env := [A, D]) (i := 1) rfl)) hE2
  -- stage 3
  have hG3 := mkGroup_spec hmk ((ps.map dsPair).map encPair)
  have eE : Val.list (((ps.map dsPair).map encPair).map encPerm) = E := by simp [hE]
  rw [eE] at hG3
  have d3 := Det.call (Det.mk2 (Det.arith' (op := .add) (Det.arith' (op := .add) (gk [D, E])
    (gq [D, E]) (z := k + q) rfl) (gq [D, E]) (z := k + q + q) rfl)
    (Det.var' (P := P) (env := [A, D, E]) (i := 2) rfl)) hG3
  -- stage 4
  have d4 := Det.call (Det.mk2 (gq [D, E, GD]) (Det.arg' (P := P) (vs := [.list [.nat k, .nat q],
    .list (ps.map pairV), .list (ms.map encPerm)]) (rest := [D, E, GD]) (j := 2) rfl))
    (mkGroup_spec hmk ms)
  -- stage 5: the cited call
  have dI := Det.mk3 (Det.arith' (op := .add) (gk [D, E, GD, GM]) (gq [D, E, GD, GM])
    (z := k + q) rfl) (Det.var' (P := P) (env := [A, D, E, GD, GM]) (i := 3) rfl)
    (Det.var' (P := P) (env := [A, D, E, GD, GM]) (i := 4) rfl)
  have eds : I.ds.map sumToFin = (ps.map dsPair).map encPair := by
    show (ps.map fun p => Perm.sumCongr (encPair p) p.2).map sumToFin = _
    simp only [List.map_map]
    apply List.map_congr_left
    intro p _
    simp [dsPair, encPair_eq]
  have eI : Val.list [.nat (k + q), GD, GM] = preimageEnc I := by
    show _ = Val.list [.nat (k + q), encGroup (I.ds.map sumToFin), encGroup ms]
    rw [eds]; rfl
  rw [eI] at dI
  have hP := preimage_call h I hj dI
  refine FunAll.intro hentry (EvalAll.letE d1 fun _ _ h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.letE d2 fun _ _ h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  refine EvalAll.letE d3 fun _ _ h3 => ?_
  obtain ⟨rfl, hc3⟩ := h3
  refine EvalAll.letE d4 fun _ _ h4 => ?_
  obtain ⟨rfl, hc4⟩ := h4
  refine EvalAll.letE hP fun w5 c5 h5 => ?_
  obtain ⟨⟨hs, rfl, hl, hgen⟩, hc5⟩ := h5
  have hgen' : gens hs = (Subgroup.closure {p | p ∈ ps} ⊓
      (gens ms).comap (MonoidHom.snd _ _)).map (encPairHom k q) := by
    ext x
    rw [hgen]
    exact preimageSet_pairInst_eq _ ps ms hms x
  obtain ⟨qs, rfl, hqs⟩ := exists_pairs_of_gens hgen'
  set H : Val := .list ((qs.map encPair).map encPerm) with hH
  have hsplit := pSplitMap_spec hsp qs
  have eH : Val.list (qs.map fun p => encPerm (encPair p)) = H := by simp [hH]
  rw [eH] at hsplit
  have dr1 := Det.call (gk [D, E, GD, GM, H]) (range_det hrg k)
  have dr2 := Det.call (gq [D, E, GD, GM, H]) (range_det hrg q)
  have dctx := Det.mk2 (gk [D, E, GD, GM, H]) (Det.mk2 dr1 dr2)
  have ectx : Val.list [.nat k, .list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))]] =
      pSplitCtx k q := rfl
  rw [ectx] at dctx
  have d6 := Det.call (Det.mk2 dctx (Det.var' (P := P) (env := [A, D, E, GD, GM, H]) (i := 5) rfl))
    hsplit
  have hlq : qs.length ≤ (k + q) ^ 2 := by
    have e : (qs.map (encPair (k := k) (q := q))).length = qs.length := List.length_map _
    have hl' : (qs.map (encPair (k := k) (q := q))).length ≤ (k + q) ^ 2 := hl
    omega
  refine d6.post fun c hc => ⟨qs, rfl, hlq, hqs, ?_⟩
  -- the cost: every weight and cost is bounded by a power of `M`
  have eIw : (preimageEnc I).wt = (Val.list [.nat (k + q), GD, GM]).wt := by rw [eI]
  have eIn : I.n = k + q := rfl
  rw [eIn] at hc5
  set M := preM k q ps ms with hM
  have hMd : k + q + ps.length + ms.length + 2 = M := rfl
  have m1 : 2 ≤ M := by omega
  have m2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have m3 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have m4 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have m6 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have m8 : M ^ 6 ≤ M ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have sq : ∀ x, x ≤ M → x ^ 2 ≤ M ^ 2 := fun x hx => Nat.pow_le_pow_left hx 2
  have pw : ∀ x n, x ≤ M → x ^ n ≤ M ^ n := fun x n hx => Nat.pow_le_pow_left hx n
  -- weights of the input pieces
  have bps : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := by
    have := wt_pairList_le ps
    have h3 := pw (pM k q ps) 3 (by unfold pM; omega)
    omega
  have bms : (Val.list (ms.map encPerm)).wt ≤ 9 * M ^ 3 + 4 := by
    have h1 := wt_list_map_le ms encPerm (W := 4 * (q + 1) ^ 2) fun m _ => wt_encPerm_le m
    have h2 : ms.length * (2 * (4 * (q + 1) ^ 2) + 1) ≤ M * (9 * M ^ 2) :=
      Nat.mul_le_mul (by omega) (by have := sq (q + 1) (by omega); omega)
    have h3 : M * (9 * M ^ 2) = 9 * M ^ 3 := by ring
    omega
  have bkq := wt_list2_le (.nat k) (.nat q)
  have wk := wt_nat_le k
  have wq := wt_nat_le q
  have wkq := wt_nat_le (k + q)
  have wkqq := wt_nat_le (k + q + q)
  have bA := wt_list3_le (.list [.nat k, .nat q]) (.list (ps.map pairV)) (.list (ms.map encPerm))
  have bA1 := wt_list2_le (.nat k) (.list (ps.map pairV))
  -- stage 1 and 2
  have bD : D.wt ≤ 400 * M ^ 3 := by
    have h1 := wt_pairList_le (ps.map dsPair)
    have e : (ps.map dsPair).map pairV = ps.map fun p => pairV (dsPair p) := by simp
    rw [e] at h1
    have h2 : pM (k + q) q (ps.map dsPair) ≤ 2 * M := by unfold pM; simp; omega
    have h3 : pM (k + q) q (ps.map dsPair) ^ 3 ≤ (2 * M) ^ 3 := Nat.pow_le_pow_left h2 3
    have h4 : (2 * M) ^ 3 = 8 * M ^ 3 := by ring
    rw [hD]; omega
  have bD1 := wt_list2_le (.nat (k + q)) D
  have bE : E.wt ≤ 33 * M ^ 3 + 4 := by
    have h1 := wt_list_map_le (ps.map dsPair) (fun p => encPerm (encPair p))
      (W := 4 * (k + q + q + 1) ^ 2) fun p _ => wt_encPerm_le _
    have h2 : (ps.map dsPair).length * (2 * (4 * (k + q + q + 1) ^ 2) + 1) ≤ M * (33 * M ^ 2) :=
      Nat.mul_le_mul (by simp; omega) (by
        have : (k + q + q + 1) ^ 2 ≤ (2 * M) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have e : (2 * M) ^ 2 = 4 * M ^ 2 := by ring
        omega)
    have h3 : M * (33 * M ^ 2) = 33 * M ^ 3 := by ring
    rw [hE]; omega
  have bE1 := wt_list2_le (.nat (k + q + q)) E
  have cE : (ps.map dsPair).length * pEncCost (k + q) q ≤ 8 * natStepK * M ^ 4 := by
    have h1 : (k + q + q + 1) ^ 3 ≤ (2 * M) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have e : (2 * M) ^ 3 = 8 * M ^ 3 := by ring
    have h2 : (ps.map dsPair).length * pEncCost (k + q) q ≤ M * (natStepK * (8 * M ^ 3)) :=
      Nat.mul_le_mul (by simp; omega) (by show natStepK * (k + q + q + 1) ^ 3 ≤ _; exact Nat.mul_le_mul_left _ (by omega))
    have e2 : M * (natStepK * (8 * M ^ 3)) = 8 * natStepK * M ^ 4 := by ring
    omega
  have cE2 : mapK * ((ps.map dsPair).length + 1) * ((Val.list [.nat (k + q), D]).wt + E.wt + 1)
      ≤ mapK * M * (1000 * M ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by simp; omega)) (by omega)
  -- stage 3 and 4
  have sGD : ((ps.map dsPair).map encPair).length + 2 ≤ M := by simp; omega
  have sGD2 : (((ps.map dsPair).map encPair).length + 2) * (k + q + q + 1) ≤ 2 * M ^ 2 := by
    have := Nat.mul_le_mul sGD (show k + q + q + 1 ≤ 2 * M by omega)
    have e : M * (2 * M) = 2 * M ^ 2 := by ring
    omega
  have bGD : GD.wt ≤ 160 * M ^ 4 := by
    have h1 := wt_encGroup_le ((ps.map dsPair).map encPair)
    have h2 := Nat.pow_le_pow_left sGD2 2
    have e : (2 * M ^ 2) ^ 2 = 4 * M ^ 4 := by ring
    rw [hGD]; omega
  have cGD : mkGroupK * ((((ps.map dsPair).map encPair).length + 2) * (k + q + q + 1)) ^ 3 ≤
      8 * mkGroupK * M ^ 6 := by
    have h2 := Nat.pow_le_pow_left sGD2 3
    have e : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
    have := Nat.mul_le_mul_left mkGroupK h2
    rw [e] at this; linarith
  have sGM : (ms.length + 2) * (q + 1) ≤ M ^ 2 := by
    have := Nat.mul_le_mul (show ms.length + 2 ≤ M by omega) (show q + 1 ≤ M by omega)
    have e : M * M = M ^ 2 := by ring
    omega
  have bGM : GM.wt ≤ 40 * M ^ 4 := by
    have h1 := wt_encGroup_le ms
    have h2 := Nat.pow_le_pow_left sGM 2
    have e : (M ^ 2) ^ 2 = M ^ 4 := by ring
    rw [hGM]; omega
  have cGM : mkGroupK * ((ms.length + 2) * (q + 1)) ^ 3 ≤ mkGroupK * M ^ 6 := by
    have h2 := Nat.pow_le_pow_left sGM 3
    have e : (M ^ 2) ^ 3 = M ^ 6 := by ring
    exact Nat.mul_le_mul_left _ (e ▸ h2)
  have bGM1 := wt_list2_le (.nat q) (.list (ms.map encPerm))
  have bI := wt_list3_le (.nat (k + q)) GD GM
  have bIn : 13 * (k + q + 1) ^ 6 ≤ 13 * M ^ 6 := Nat.mul_le_mul_left _ (pw _ 6 (by omega))
  -- stage 6
  have hq2 : qs.length ≤ M ^ 2 := le_trans hlq (sq _ (by omega))
  have bH : H.wt ≤ 9 * M ^ 4 + 4 := by
    have h1 := wt_list_map_le (qs.map encPair) encPerm (W := 4 * (k + q + 1) ^ 2)
      fun p _ => wt_encPerm_le p
    have h2 : (qs.map encPair).length * (2 * (4 * (k + q + 1) ^ 2) + 1) ≤ M ^ 2 * (9 * M ^ 2) :=
      Nat.mul_le_mul (by simp; omega) (by have := sq (k + q + 1) (by omega); omega)
    have h3 : M ^ 2 * (9 * M ^ 2) = 9 * M ^ 4 := by ring
    rw [hH]; omega
  have bQ : (Val.list (qs.map pairV)).wt ≤ 400 * M ^ 6 := by
    have h1 := wt_pairList_le qs
    have h2 : pM k q qs ≤ 2 * M ^ 2 := by unfold pM; omega
    have h3 := Nat.pow_le_pow_left h2 3
    have e : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
    omega
  have b1k := wt_encPerm_le (1 : Perm (Fin k))
  have b1q := wt_encPerm_le (1 : Perm (Fin q))
  have b11 := wt_list2_le (encPerm (1 : Perm (Fin k))) (encPerm (1 : Perm (Fin q)))
  have bC := wt_list2_le (.nat k) (.list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))])
  have eC : (pSplitCtx k q).wt =
      (Val.list [.nat k, .list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))]]).wt := rfl
  have bCH := wt_list2_le (pSplitCtx k q) H
  have sk := sq (k + 1) (by omega)
  have sq' := sq (q + 1) (by omega)
  have ck : 8000 * (k + 1) ^ 3 ≤ 8000 * M ^ 3 := Nat.mul_le_mul_left _ (pw _ 3 (by omega))
  have cq : 8000 * (q + 1) ^ 3 ≤ 8000 * M ^ 3 := Nat.mul_le_mul_left _ (pw _ 3 (by omega))
  have cS : qs.length * pSplitCost k q ≤ 10 ^ 11 * M ^ 8 := by
    have h1 : pSplitCost k q ≤ 10 ^ 11 * M ^ 6 :=
      Nat.mul_le_mul_left _ (pw _ 6 (by omega))
    have h2 := Nat.mul_le_mul hq2 h1
    have e : M ^ 2 * (10 ^ 11 * M ^ 6) = 10 ^ 11 * M ^ 8 := by ring
    omega
  have cS2 : mapK * (qs.length + 1) * ((Val.list [pSplitCtx k q, H]).wt +
      (Val.list (qs.map pairV)).wt + 1) ≤ mapK * (2 * M ^ 2) * (1000 * M ^ 6) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have cD : 2 * dsK * pM k q ps ^ 4 ≤ 2 * dsK * M ^ 4 :=
    Nat.mul_le_mul_left _ (pw _ 4 (by unfold pM; omega))
  have e1 : mapK * M * (1000 * M ^ 3) = 10 ^ 6 * M ^ 4 := by simp only [mapK]; ring
  have e2 : mapK * (2 * M ^ 2) * (1000 * M ^ 6) = 2 * 10 ^ 6 * M ^ 8 := by simp only [mapK]; ring
  rw [← hD] at hc1
  rw [← hE] at hc2
  rw [← hGD] at hc3
  rw [← hGM] at hc4
  simp only [graphPreK, dsK, natStepK, mkGroupK] at *
  omega

end GI.Impl
