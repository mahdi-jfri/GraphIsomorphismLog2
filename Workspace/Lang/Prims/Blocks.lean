/-
**Kernels and block stabilizers by the preimage task.**

`G ≤ Sym(n)` is given by generators (`GroupVal`), and a `G`-invariant partition by representative
labels (`ReprVal`, a relation `R`).
* `kerFuns`: the kernel of the action of `G` on the classes, `{g ∈ G | g i ~ i for all i}`. The
  graph group `{g ⊕ hat r g}` is computed (`graphValFuns`) and the preimage task is called with
  no generators of `M`.
* `blkFuns`: the stabilizer of the class of a point `a`, `{g ∈ G | g a ~ a}`. The action `π(G)`
  on the representatives is computed (`hatValFuns`), then the stabilizer of the representative
  of `a` in `π(G)` by the pointwise-stabilizer task, then its preimage by the preimage task.

Both return group values, so their results can be passed on. The cost bounds use
`Prim.boundSize p B = p.c * (B + 2) ^ p.k`, the bound of a call of `p` on any argument of at
most `B` cells, plus a polynomial in the weight `T` of the argument (`kerK * T ^ 9`,
`blkK * T ^ 9`). They depend on the input alone, because the tasks bound the number of
generators of their outputs by `n²`.
-/
import Workspace.Lang.Prims.Graph

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited
open Equiv

variable {n : ℕ}

/-- The bound of a call of `p` on any argument of at most `B` cells. -/
def Prim.boundSize (p : Prim) (B : ℕ) : ℕ := p.c * (B + 2) ^ p.k

theorem Prim.bound_le (p : Prim) {v : Val} {B : ℕ} (h : v.size ≤ B) :
    p.bound v ≤ p.boundSize B :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem size_list3 (a b c : Val) : (Val.list [a, b, c]).size = a.size + b.size + c.size + 3 := by
  simp only [size_list, length_cellsList, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]; omega

theorem size_list2 (a b : Val) : (Val.list [a, b]).size = a.size + b.size + 3 := by
  simp only [size_list, length_cellsList, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]; omega

/-! ### The kernel of the action on the classes -/

/-- On `[gv, rv]`: the kernel, as a group value. -/
def kerEntry (b jpre : ℕ) : Expr :=
  .letE (.call (b + 5) (.var 0))
    (.letE (.prim jpre (mk3 (.get (arg 0) (.nat 0)) (.var 1)
        (mk2 (.get (arg 0) (.nat 0)) (mk1 (.call (b + 1) (.get (arg 0) (.nat 0)))))))
      (.call (b + 14) (mk2 (.get (arg 0) (.nat 0)) (.var 2))))

/-- The kernel program, at base `b` (21 functions), with the preimage primitive at `jpre`. -/
def kerFuns (b jpre : ℕ) : List Expr :=
  [kerEntry b jpre] ++ rangeFuns (b + 1) ++ [hatPtF] ++ graphValFuns (b + 5) (b + 1) (b + 4) ++
    mkGroupFuns (b + 14)

/-- The constant of the kernel program. -/
def kerK : ℕ := 10000000

/-- **The kernel of the action on the classes of an invariant partition.** With `T` the weight
of the argument, the result weighs at most `320 (n + 1)⁶`, and the cost is at most the bound of
one preimage call on at most `3 * T` cells plus `kerK * T ^ 9`. -/
theorem ker_spec (h : Preimage) {P : Program} {b jpre : ℕ} (hb : P.HasAt b (kerFuns b jpre))
    (hj : P.prims[jpre]? = some (preimagePrim h)) {gv rv : Val} {G : Subgroup (Perm (Fin n))}
    {R : Fin n → Fin n → Prop} (hG : GroupVal n gv G) (hR : ReprVal n rv R)
    (hpres : ∀ g ∈ G, ∀ i j, R (g i) (g j) ↔ R i j) :
    FunAll P b (.list [gv, rv]) (fun w c =>
      (∃ K, GroupVal n w K ∧ ∀ g, g ∈ K ↔ g ∈ G ∧ ∀ i, R (g i) i) ∧
      w.wt ≤ 320 * (n + 1) ^ 6 ∧
      c ≤ (preimagePrim h).boundSize (3 * (Val.list [gv, rv]).wt) +
        kerK * (Val.list [gv, rv]).wt ^ 9) := by
  simp only [kerFuns] at hb
  have hentry : P.funs[b]? = some (kerEntry b jpre) := hb.left.left.left.left.single
  have hrg : P.HasAt (b + 1) (rangeFuns (b + 1)) := by simpa using hb.left.left.left.right
  have hhp : P.funs[b + 4]? = some hatPtF := by
    simpa [rangeFuns, loopFuns, Nat.add_assoc] using hb.left.left.right.single
  have hgv : P.HasAt (b + 5) (graphValFuns (b + 5) (b + 1) (b + 4)) := by
    simpa [rangeFuns, loopFuns, Nat.add_assoc] using hb.left.right
  have hmk : P.HasAt (b + 14) (mkGroupFuns (b + 14)) := by
    simpa [rangeFuns, loopFuns, graphValFuns, mapFuns, Nat.add_assoc] using hb.right
  obtain ⟨gs, rfl, rfl⟩ := hG
  obtain ⟨r, rfl, hrR, hr⟩ := hR.elim
  have hgs : ∀ g ∈ gs, g ∈ presR r := fun g hg =>
    le_presR hrR hpres (Subgroup.subset_closure hg)
  generalize hL : (encFun fun i => (r i : ℕ)) = L
  -- the graph group
  have dG := Det.call (Det.var' (P := P) (env := [Val.list [encGroup gs, L]]) (i := 0) rfl)
    (hL ▸ graphVal_spec hgv hrg hhp hr hgs)
  -- the preimage call
  have dN := Det.get' (Det.arg' (P := P) (vs := [encGroup gs, L])
    (rest := [encGroup ((gs.map (psi r)).map sumToFin)]) (j := 0) rfl) (Det.nat 0)
    (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][0]? = some (.nat n) from rfl)
  have dE := Det.call dN (range_det hrg n)
  have dI := Det.mk3 dN (Det.var' (P := P) (env := [Val.list [encGroup gs, L],
    encGroup ((gs.map (psi r)).map sumToFin)]) (i := 1) rfl) (Det.mk2 dN (Det.mk1 dE))
  have hI : Val.list [.nat n, encGroup ((gs.map (psi r)).map sumToFin),
      .list [.nat n, .list [encPerm (1 : Perm (Fin n))]]] =
      preimageEnc (graphInst r gs [] (by simp)) := rfl
  rw [hI] at dI
  have hP := preimage_call h (graphInst r gs [] (by simp)) hj dI
  refine FunAll.intro hentry (EvalAll.letE dG fun gv' cg hg' => ?_)
  obtain ⟨rfl, hcg⟩ := hg'
  refine EvalAll.letE hP fun w0 c0 hw0 => ?_
  obtain ⟨hgen, hc0⟩ := hw0
  obtain ⟨hs, rfl, hl, hhs⟩ := hgen
  have dN' := Det.get' (Det.arg' (P := P) (vs := [encGroup gs, L])
    (rest := [encGroup ((gs.map (psi r)).map sumToFin), .list (hs.map encPerm)]) (j := 0) rfl)
    (Det.nat 0) (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][0]? = some (.nat n) from rfl)
  have dM := Det.call (Det.mk2 dN' (Det.var' (P := P) (env := [Val.list [encGroup gs, L],
    encGroup ((gs.map (psi r)).map sumToFin), .list (hs.map encPerm)]) (i := 2) rfl))
    (mkGroup_spec hmk hs)
  refine dM.post fun c hc => ⟨⟨gens hs, ⟨hs, rfl, rfl⟩, fun g => ?_⟩, wt_encGroup_le_sq hl, ?_⟩
  · have := hhs ▸ graphInst_kernel hr hgs g
    simpa only [hrR] using this
  -- the cost
  · have w1 : L.wt ≤ 4 * (n + 1) ^ 2 := hL ▸ wt_encRepr_le r
    have w2 := wt_encGroup_le gs
    have w3 := S_le_wt_encGroup gs
    have w4 : (Val.list [encGroup gs, L]).wt ≤ 2 * ((encGroup gs).wt + L.wt) + 6 := wt_list2_le _ _
    have w5 : (encGroup gs).wt < (Val.list [encGroup gs, L]).wt := wt_le_wt_list (by simp)
    have w6 : (encGroup ((gs.map (psi r)).map sumToFin)).wt ≤
        40 * ((gs.length + 2) * (n + n + 1)) ^ 2 := by
      have := wt_encGroup_le ((gs.map (psi r)).map sumToFin)
      simpa using this
    have w7 := wt_gens_le_encGroup hs
    have w8 := S_le_wt_encGroup hs
    have w9 := wt_encPerm_le (1 : Perm (Fin n))
    have w10 := wt_list1_le (encPerm (1 : Perm (Fin n)))
    have w11 := wt_list2_le (.nat n) (.list [encPerm (1 : Perm (Fin n))])
    have w12 := wt_list3_le (.nat n) (encGroup ((gs.map (psi r)).map sumToFin))
      (.list [.nat n, .list [encPerm (1 : Perm (Fin n))]])
    have w13 := wt_list2_le (.nat n) (.list (hs.map encPerm))
    have w14 := wt_nat_le n
    have e15 : (preimageEnc (graphInst r gs [] (by simp))).wt =
        (Val.list [.nat n, encGroup ((gs.map (psi r)).map sumToFin),
          .list [.nat n, .list [encPerm (1 : Perm (Fin n))]]]).wt := congrArg Val.wt rfl
    -- the size of the preimage instance
    have hsz : (preimageEnc (graphInst r gs [] (by simp))).size ≤
        3 * (Val.list [encGroup gs, L]).wt := by
      have e : (preimageEnc (graphInst r gs [] (by simp))).size =
          (Val.list [.nat n, encGroup ((gs.map (psi r)).map sumToFin),
            encGroup ([] : List (Perm (Fin n)))]).size := congrArg Val.size rfl
      rw [e, size_list3, size_encGroup, size_encGroup, size_nat]
      have := (Val.list [encGroup gs, L]).size_le_wt
      have h2 : (encGroup gs).size < (Val.list [encGroup gs, L]).size := by
        rw [size_list2]; have := L.two_le_size; omega
      rw [size_encGroup] at h2
      clear hl hhs hc hc0 hcg
      simp only [List.length_map, List.length_nil] at *
      nlinarith
    have hbd := (preimagePrim h).bound_le hsz
    have hW6 : (encGroup hs).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hl
    have hS3 := measure_le_of_sq (n := n) hl
    generalize hT : (Val.list [encGroup gs, L]).wt = T at *
    generalize hW : (encGroup hs).wt = W at *
    have hS : (gs.length + 2) * (n + 1) ≤ T := by omega
    have hn : n + 1 ≤ T := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hS
    have hm : gs.length + 2 ≤ T := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hS
    have hT1 : 1 ≤ T := by omega
    have hT39 : T ^ 3 ≤ T ^ 9 := Nat.pow_le_pow_right hT1 (by omega)
    have hX : T ≤ T ^ 9 := Nat.le_self_pow (by omega) _
    have hX2 : T ^ 2 ≤ T ^ 9 := Nat.pow_le_pow_right hT1 (by omega)
    have h6 : (n + 1) ^ 6 ≤ T ^ 9 :=
      (Nat.pow_le_pow_left hn 6).trans (Nat.pow_le_pow_right hT1 (by omega))
    have hXW : W ≤ 320 * T ^ 9 := by omega
    have h1 : graphValK * ((gs.length + 2) * (n + 1)) ^ 3 ≤ 1000000 * T ^ 9 :=
      Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 3).trans hT39)
    have h2 : mkGroupK * ((hs.length + 2) * ((graphInst r gs [] (by simp)).n + 1)) ^ 3 ≤
        800000 * T ^ 9 := by
      have : ((hs.length + 2) * (n + 1)) ^ 3 ≤ 8 * T ^ 9 :=
        calc ((hs.length + 2) * (n + 1)) ^ 3 ≤ (2 * (n + 1) ^ 3) ^ 3 := Nat.pow_le_pow_left hS3 3
          _ = 8 * (n + 1) ^ 9 := by ring
          _ ≤ 8 * T ^ 9 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 9)
      show mkGroupK * ((hs.length + 2) * (n + 1)) ^ 3 ≤ 800000 * T ^ 9
      simp only [mkGroupK]; omega
    have h3 : 8000 * (n + 1) ^ 3 ≤ 8000 * T ^ 9 :=
      Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hn 3).trans hT39)
    have h4 : ((gs.length + 2) * (n + n + 1)) ^ 2 ≤ 4 * T ^ 2 := by
      have : (gs.length + 2) * (n + n + 1) ≤ 2 * T := by
        calc (gs.length + 2) * (n + n + 1) ≤ (gs.length + 2) * (2 * (n + 1)) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = 2 * ((gs.length + 2) * (n + 1)) := by ring
          _ ≤ 2 * T := by omega
      calc ((gs.length + 2) * (n + n + 1)) ^ 2 ≤ (2 * T) ^ 2 := Nat.pow_le_pow_left this 2
        _ = 4 * T ^ 2 := by ring
    have h5 : (n + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hn 2
    have h7 : 13 * ((graphInst r gs [] (by simp)).n + 1) ^ 6 ≤ 13 * T ^ 9 := by
      show 13 * (n + 1) ^ 6 ≤ 13 * T ^ 9
      omega
    have k3 : kerK = 10000000 := rfl
    rw [k3]
    omega

/-! ### The stabilizer of a class -/

/-- On `[gv, rv, a]`: the stabilizer of the class of `a`, and the stabilizer of the
representative of `a` in the action on the representatives, as group values. -/
def blkEntry (b jps jpre : ℕ) : Expr :=
  .letE (.call (b + 5) (mk2 (arg 0) (arg 1)))
    (.letE (.prim jps (mk2 (.var 1) (mk1 (.get (arg 1) (arg 2)))))
      (.letE (.call (b + 22) (mk2 (.get (arg 0) (.nat 0)) (.var 2)))
        (.letE (.call (b + 13) (mk2 (arg 0) (arg 1)))
          (.letE (.prim jpre (mk3 (.get (arg 0) (.nat 0)) (.var 4) (.var 3)))
            (mk2 (.call (b + 22) (mk2 (.get (arg 0) (.nat 0)) (.var 5))) (.var 3))))))

/-- The program of the stabilizer of a class, at base `b` (29 functions), with the
pointwise-stabilizer primitive at `jps` and the preimage primitive at `jpre`. -/
def blkFuns (b jps jpre : ℕ) : List Expr :=
  [blkEntry b jps jpre] ++ rangeFuns (b + 1) ++ [hatPtF] ++ hatValFuns (b + 5) (b + 1) (b + 4) ++
    graphValFuns (b + 13) (b + 1) (b + 4) ++ mkGroupFuns (b + 22)

/-- The constant of the program of the stabilizer of a class. -/
def blkK : ℕ := 20000000

/-- **The stabilizer of a class of an invariant partition**, by the preimage task. The result is
a pair. Its first entry is the group value of `{g ∈ G | g a ~ a}`. Its second entry is the
generators (as a group value) that the pointwise-stabilizer task returned for the stabilizer of
the representative of `a` in the action on the representatives. (It was returned when the tasks
did not bound their outputs, so that the cost could be bounded by the weight of the result; it is
kept so that the program is unchanged.) With `T` the weight of the argument, the result weighs at
most `1300 (n + 1)⁶`, and the cost is at most one pointwise-stabilizer call on at most `T + 10`
cells, one preimage call on at most `3 * T + 1300 (n + 1)⁶` cells, and `blkK * T ^ 9`. -/
theorem blk_spec (hps : PointwiseStab) (h : Preimage) {P : Program} {b jps jpre : ℕ}
    (hb : P.HasAt b (blkFuns b jps jpre)) (hjs : P.prims[jps]? = some (pointwiseStabPrim hps))
    (hj : P.prims[jpre]? = some (preimagePrim h)) {gv rv : Val} {G : Subgroup (Perm (Fin n))}
    {R : Fin n → Fin n → Prop} (hG : GroupVal n gv G) (hR : ReprVal n rv R)
    (hpres : ∀ g ∈ G, ∀ i j, R (g i) (g j) ↔ R i j) (a : Fin n) :
    FunAll P b (.list [gv, rv, .nat a]) (fun w c =>
      (∃ v1 v2, w = .list [v1, v2] ∧ ∃ K, GroupVal n v1 K ∧ ∀ g, g ∈ K ↔ g ∈ G ∧ R (g a) a) ∧
      w.wt ≤ 1300 * (n + 1) ^ 6 ∧
      c ≤ (pointwiseStabPrim hps).boundSize ((Val.list [gv, rv, .nat a]).wt + 10) +
        (preimagePrim h).boundSize (3 * (Val.list [gv, rv, .nat a]).wt + 1300 * (n + 1) ^ 6) +
        blkK * (Val.list [gv, rv, .nat a]).wt ^ 9) := by
  simp only [blkFuns] at hb
  have hentry : P.funs[b]? = some (blkEntry b jps jpre) := hb.left.left.left.left.left.single
  have hrg : P.HasAt (b + 1) (rangeFuns (b + 1)) := by simpa using hb.left.left.left.left.right
  have hhp : P.funs[b + 4]? = some hatPtF := by
    simpa [rangeFuns, loopFuns, Nat.add_assoc] using hb.left.left.left.right.single
  have hhv : P.HasAt (b + 5) (hatValFuns (b + 5) (b + 1) (b + 4)) := by
    simpa [rangeFuns, loopFuns, Nat.add_assoc] using hb.left.left.right
  have hgv : P.HasAt (b + 13) (graphValFuns (b + 13) (b + 1) (b + 4)) := by
    simpa [rangeFuns, loopFuns, hatValFuns, mapFuns, Nat.add_assoc] using hb.left.right
  have hmk : P.HasAt (b + 22) (mkGroupFuns (b + 22)) := by
    simpa [rangeFuns, loopFuns, hatValFuns, graphValFuns, mapFuns, Nat.add_assoc] using hb.right
  obtain ⟨gs, rfl, rfl⟩ := hG
  obtain ⟨r, rfl, hrR, hr⟩ := hR.elim
  have hgs : ∀ g ∈ gs, g ∈ presR r := fun g hg =>
    le_presR hrR hpres (Subgroup.subset_closure hg)
  have hLa : ∃ ls, (encFun fun i => (r i : ℕ)) = .list ls ∧ ls[(a : ℕ)]? = some (.nat (r a)) :=
    ⟨_, rfl, by simp⟩
  have w1 := wt_encRepr_le r
  generalize hL : (encFun fun i => (r i : ℕ)) = L at hLa w1
  obtain ⟨ls, rfl, hls⟩ := hLa
  -- the action on the representatives
  have dH := Det.call (Det.mk2
    (Det.arg' (P := P) (vs := [encGroup gs, .list ls, .nat a]) (rest := []) (j := 0) rfl)
    (Det.arg' (P := P) (vs := [encGroup gs, .list ls, .nat a]) (rest := []) (j := 1) rfl))
    (hL ▸ hatVal_spec hhv hrg hhp hr hgs)
  refine FunAll.intro hentry (EvalAll.letE dH fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- the stabilizer of the representative of `a`
  have dRa := Det.get'
    (Det.arg' (P := P) (vs := [encGroup gs, .list ls, .nat a])
      (rest := [encGroup (gs.map (hat r))]) (j := 1) rfl)
    (Det.arg' (P := P) (vs := [encGroup gs, .list ls, .nat a])
      (rest := [encGroup (gs.map (hat r))]) (j := 2) rfl) hls
  have dIn := Det.mk2 (Det.var' (P := P) (env := [Val.list [encGroup gs, .list ls, .nat a],
    encGroup (gs.map (hat r))]) (i := 1) rfl) (Det.mk1 dRa)
  have hpts : Val.list [Val.nat (r a : ℕ)] = encPts [r a] := by rw [encPts_eq]; rfl
  have hpts' := hpts
  rw [hpts] at dIn
  have hPS := pointwiseStab_call hps hjs dIn ⟨gs.map (hat r), rfl, rfl⟩
  refine EvalAll.letE hPS fun v2 c2 h2 => ?_
  obtain ⟨⟨ms, rfl, hmsl, hms⟩, hc2⟩ := h2
  -- its group value
  have dM := Det.call (Det.mk2 (Det.get' (Det.arg' (P := P) (vs := [encGroup gs, .list ls, .nat a])
      (rest := [encGroup (gs.map (hat r)), .list (ms.map encPerm)]) (j := 0) rfl) (Det.nat 0)
      (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][0]? = some (.nat n) from rfl))
    (Det.var' (P := P) (env := [Val.list [encGroup gs, .list ls, .nat a],
      encGroup (gs.map (hat r)), .list (ms.map encPerm)]) (i := 2) rfl)) (mkGroup_spec hmk ms)
  refine EvalAll.letE dM fun v3 c3 h3 => ?_
  obtain ⟨rfl, hc3⟩ := h3
  -- the graph group
  have dG := Det.call (Det.mk2
    (Det.arg' (P := P) (vs := [encGroup gs, .list ls, .nat a])
      (rest := [encGroup (gs.map (hat r)), .list (ms.map encPerm), encGroup ms]) (j := 0) rfl)
    (Det.arg' (P := P) (vs := [encGroup gs, .list ls, .nat a])
      (rest := [encGroup (gs.map (hat r)), .list (ms.map encPerm), encGroup ms]) (j := 1) rfl))
    (hL ▸ graphVal_spec hgv hrg hhp hr hgs)
  refine EvalAll.letE dG fun v4 c4 h4 => ?_
  obtain ⟨rfl, hc4⟩ := h4
  -- the preimage
  have hms' := graphInst_ms_le hr hgs a hms
  have dI := Det.mk3 (Det.get' (Det.arg' (P := P) (vs := [encGroup gs, .list ls, .nat a])
      (rest := [encGroup (gs.map (hat r)), .list (ms.map encPerm), encGroup ms,
        encGroup ((gs.map (psi r)).map sumToFin)]) (j := 0) rfl) (Det.nat 0)
      (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][0]? = some (.nat n) from rfl))
    (Det.var' (P := P) (env := [Val.list [encGroup gs, .list ls, .nat a],
      encGroup (gs.map (hat r)), .list (ms.map encPerm), encGroup ms,
      encGroup ((gs.map (psi r)).map sumToFin)]) (i := 4) rfl)
    (Det.var' (P := P) (env := [Val.list [encGroup gs, .list ls, .nat a],
      encGroup (gs.map (hat r)), .list (ms.map encPerm), encGroup ms,
      encGroup ((gs.map (psi r)).map sumToFin)]) (i := 3) rfl)
  have hI : Val.list [.nat n, encGroup ((gs.map (psi r)).map sumToFin), encGroup ms] =
      preimageEnc (graphInst r gs ms hms') := rfl
  have hI' := hI
  rw [hI] at dI
  have hP := preimage_call h _ hj dI
  refine EvalAll.letE hP fun v5 c5 h5 => ?_
  obtain ⟨⟨hs, rfl, hhsl, hhs⟩, hc5⟩ := h5
  replace hhsl : hs.length ≤ n ^ 2 := hhsl
  -- the weight of the result: two group values of at most `n²` generators
  have hO : (Val.list [encGroup hs, encGroup ms]).wt ≤ 1300 * (n + 1) ^ 6 := by
    have h1 := wt_list2_le (encGroup hs) (encGroup ms)
    have h2 : (encGroup hs).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hhsl
    have h3 : (encGroup ms).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hmsl
    have h4 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    generalize (n + 1) ^ 6 = N at h2 h3 h4 ⊢
    omega
  -- the group value of the result
  have dF := Det.call (Det.mk2 (Det.get' (Det.arg' (P := P) (vs := [encGroup gs, .list ls, .nat a])
      (rest := [encGroup (gs.map (hat r)), .list (ms.map encPerm), encGroup ms,
        encGroup ((gs.map (psi r)).map sumToFin), .list (hs.map encPerm)]) (j := 0) rfl) (Det.nat 0)
      (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][0]? = some (.nat n) from rfl))
    (Det.var' (P := P) (env := [Val.list [encGroup gs, .list ls, .nat a],
      encGroup (gs.map (hat r)), .list (ms.map encPerm), encGroup ms,
      encGroup ((gs.map (psi r)).map sumToFin), .list (hs.map encPerm)]) (i := 5) rfl))
    (mkGroup_spec hmk hs)
  have dOut := Det.mk2 dF (Det.var' (P := P) (env := [Val.list [encGroup gs, .list ls, .nat a],
      encGroup (gs.map (hat r)), .list (ms.map encPerm), encGroup ms,
      encGroup ((gs.map (psi r)).map sumToFin), .list (hs.map encPerm)]) (i := 3) rfl)
  refine dOut.post fun c hc => ⟨⟨_, _, rfl, gens hs, ⟨hs, rfl, rfl⟩, fun g => ?_⟩, hO, ?_⟩
  · have := hhs ▸ graphInst_block hr hgs a hms g
    simpa only [hrR] using this
  · clear dH dRa dIn hPS dM dG dI hP dF dOut hhs hI hpts
    -- weights of the pieces
    have hA0 : (encGroup gs).wt < (Val.list [encGroup gs, .list ls, .nat a]).wt :=
      wt_le_wt_list (by simp)
    have hA1 : (Val.list ls).wt < (Val.list [encGroup gs, .list ls, .nat a]).wt :=
      wt_le_wt_list (by simp)
    have w2 := wt_encGroup_le gs
    have w3 := S_le_wt_encGroup gs
    have w4 : (encGroup (gs.map (hat r))).wt ≤ 40 * ((gs.length + 2) * (n + 1)) ^ 2 := by
      simpa using wt_encGroup_le (gs.map (hat r))
    have w5 := wt_list2_le (encGroup gs) (.list ls)
    have w6 : (encGroup ((gs.map (psi r)).map sumToFin)).wt ≤
        40 * ((gs.length + 2) * (n + n + 1)) ^ 2 := by
      simpa using wt_encGroup_le ((gs.map (psi r)).map sumToFin)
    have w7 := wt_gens_le_encGroup ms
    have w8 := S_le_wt_encGroup ms
    have w9 := wt_gens_le_encGroup hs
    have w10 := S_le_wt_encGroup hs
    have w11 := wt_list2_le (.nat n) (.list (ms.map encPerm))
    have w12 := wt_list2_le (.nat n) (.list (hs.map encPerm))
    have w13 := wt_nat_le n
    have w14 := wt_nat_le (r a : ℕ)
    have w15 : (encPts [r a]).wt ≤ 2 * (Val.nat (r a : ℕ)).wt + 5 := by
      rw [← hpts']; exact wt_list1_le _
    have w16 := wt_list2_le (encGroup (gs.map (hat r))) (encPts [r a])
    have w17 : (preimageEnc (graphInst r gs ms hms')).wt ≤ 2 * ((Val.nat n).wt +
        (encGroup ((gs.map (psi r)).map sumToFin)).wt + (encGroup ms).wt) + 7 := by
      rw [← hI']; exact wt_list3_le _ _ _
    have w18 : (encGroup hs).wt < (Val.list [encGroup hs, encGroup ms]).wt :=
      wt_le_wt_list (by simp)
    have w19 : (encGroup ms).wt < (Val.list [encGroup hs, encGroup ms]).wt :=
      wt_le_wt_list (by simp)
    have hra := (r a).isLt
    -- sizes of the arguments of the two primitive calls
    have hT := (Val.list [encGroup gs, .list ls, .nat a]).size_le_wt
    have hsA : (encGroup gs).size + 5 ≤ (Val.list [encGroup gs, .list ls, .nat a]).size := by
      rw [size_list3]; have := (Val.list ls).two_le_size; omega
    have hsz1 : (Val.list [encGroup (gs.map (hat r)), encPts [r a]]).size ≤
        (Val.list [encGroup gs, .list ls, .nat a]).wt + 10 := by
      rw [size_list2, ← hpts', size_encGroup]
      have e : (Val.list [Val.nat (r a : ℕ)]).size = 5 := by
        simp only [size_list, length_cellsList, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, size_nat]; omega
      rw [size_encGroup] at hsA
      rw [e, List.length_map]
      omega
    have hbd1 := (pointwiseStabPrim hps).bound_le hsz1
    have hsz2 : (preimageEnc (graphInst r gs ms hms')).size ≤
        3 * (Val.list [encGroup gs, .list ls, .nat a]).wt +
          (Val.list [encGroup hs, encGroup ms]).wt := by
      rw [← hI', size_list3, size_encGroup, size_nat, List.length_map, List.length_map]
      have := (encGroup ms).size_le_wt
      rw [size_encGroup] at hsA
      have e : (gs.length + 1) * (2 * (n + n) + 3) ≤ 2 * ((gs.length + 1) * (2 * n + 3)) := by
        calc (gs.length + 1) * (2 * (n + n) + 3) ≤ (gs.length + 1) * (2 * (2 * n + 3)) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = 2 * ((gs.length + 1) * (2 * n + 3)) := by ring
      omega
    have hsz2' : (preimageEnc (graphInst r gs ms hms')).size ≤
        3 * (Val.list [encGroup gs, .list ls, .nat a]).wt + 1300 * (n + 1) ^ 6 := by omega
    have hbd2 := (preimagePrim h).bound_le hsz2'
    have hSm := measure_le_of_sq (n := n) hmsl
    have hSh := measure_le_of_sq (n := n) hhsl
    clear hsz1 hsz2 hsz2' hsA hT
    generalize hT : (Val.list [encGroup gs, .list ls, .nat a]).wt = T at *
    generalize hO : (Val.list [encGroup hs, encGroup ms]).wt = O at *
    have hS : (gs.length + 2) * (n + 1) ≤ T := by omega
    have hn : n + 1 ≤ T := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hS
    have hT1 : 1 ≤ T := by omega
    have hT39 : T ^ 3 ≤ T ^ 9 := Nat.pow_le_pow_right hT1 (by omega)
    have hX : T ≤ T ^ 9 := Nat.le_self_pow (by omega) _
    have hX2 : T ^ 2 ≤ T ^ 9 := Nat.pow_le_pow_right hT1 (by omega)
    have h6' : (n + 1) ^ 6 ≤ T ^ 9 :=
      (Nat.pow_le_pow_left hn 6).trans (Nat.pow_le_pow_right hT1 (by omega))
    have hXO : O ≤ 1300 * T ^ 9 := by omega
    have h9 : ∀ m, (m + 2) * (n + 1) ≤ 2 * (n + 1) ^ 3 →
        mkGroupK * ((m + 2) * (n + 1)) ^ 3 ≤ 800000 * T ^ 9 := by
      intro m hm
      have : ((m + 2) * (n + 1)) ^ 3 ≤ 8 * T ^ 9 :=
        calc ((m + 2) * (n + 1)) ^ 3 ≤ (2 * (n + 1) ^ 3) ^ 3 := Nat.pow_le_pow_left hm 3
          _ = 8 * (n + 1) ^ 9 := by ring
          _ ≤ 8 * T ^ 9 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 9)
      simp only [mkGroupK]; omega
    have h1 : hatValK * ((gs.length + 2) * (n + 1)) ^ 3 ≤ 500000 * T ^ 9 :=
      Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 3).trans hT39)
    have h2 : graphValK * ((gs.length + 2) * (n + 1)) ^ 3 ≤ 1000000 * T ^ 9 :=
      Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 3).trans hT39)
    have h3 : mkGroupK * ((ms.length + 2) * (n + 1)) ^ 3 ≤ 800000 * T ^ 9 := h9 _ hSm
    have h4 : mkGroupK * ((hs.length + 2) * ((graphInst r gs ms hms').n + 1)) ^ 3 ≤
        800000 * T ^ 9 := h9 _ hSh
    have h8 : 13 * ((graphInst r gs ms hms').n + 1) ^ 6 ≤ 13 * T ^ 9 := by
      show 13 * (n + 1) ^ 6 ≤ 13 * T ^ 9
      omega
    have h5 : ((gs.length + 2) * (n + n + 1)) ^ 2 ≤ 4 * T ^ 2 := by
      have : (gs.length + 2) * (n + n + 1) ≤ 2 * T := by
        calc (gs.length + 2) * (n + n + 1) ≤ (gs.length + 2) * (2 * (n + 1)) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = 2 * ((gs.length + 2) * (n + 1)) := by ring
          _ ≤ 2 * T := by omega
      calc ((gs.length + 2) * (n + n + 1)) ^ 2 ≤ (2 * T) ^ 2 := Nat.pow_le_pow_left this 2
        _ = 4 * T ^ 2 := by ring
    have h6 : ((gs.length + 2) * (n + 1)) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hS 2
    have h7 : (n + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hn 2
    have k : blkK = 20000000 := rfl
    rw [k]
    omega

end GI.Lang
