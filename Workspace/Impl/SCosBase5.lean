import Workspace.Impl.SCosBase4

/-!
# The base case, the answer

Step 7 of `scosBaseF`: the test `idx < |L|`, and in the found case the two entries of the
answer, `x t` (`compose_spec`) and the stabilizer of `n + α` (`pstab_spec`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

section Steps

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-- The environment after step 6. -/
noncomputable abbrev scosBaseE6 (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n)
    (L : List (Fin (n + n) × Perm (Fin (n + n)))) (i : ℕ) : List Val :=
  [scosBaseV gs x a, .nat a, .nat n, .nat (n + a), .nat (scosBaseTau x a), encPairs ptKey L,
    .nat i]

/-- **The test** `idx < |L|`. -/
theorem scosBase_cond (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n)
    (L : List (Fin (n + n) × Perm (Fin (n + n)))) {i S : ℕ} (hi : i ≤ L.length)
    (hLw : (encPairs ptKey L).wt ≤ S) :
    Det (𝒫) (scosBaseE6 gs x a L i) (.arith .lt (.var 6) (.length (.var 5)))
      (.nat (if i < L.length then 1 else 0)) (4 * S + 20) := by
  have dv5 : Det (𝒫) (scosBaseE6 gs x a L i) (.var 5) (.list (L.map (GI.Lang.encPair ptKey))) _ :=
    Det.var' (i := 5) rfl
  have dl := Det.length dv5
  simp only [List.length_map] at dl
  have d := Det.arith' (op := .lt) (z := if i < L.length then 1 else 0)
    (Det.var' (P := 𝒫) (env := scosBaseE6 gs x a L i) (i := 6) rfl) dl rfl
  refine d.mono ?_
  have hlen : L.length < (encPairs ptKey L).wt := by
    have := length_lt_wt_list (L.map (GI.Lang.encPair ptKey))
    simpa [encPairs] using this
  have e0 : (encPairs ptKey L).wt = (Val.list (L.map (GI.Lang.encPair ptKey))).wt := rfl
  have w1 := wt_nat_le i
  have hz : (if i < L.length then 1 else 0) ≤ 1 := by split_ifs <;> omega
  omega

/-- **The first entry** of the answer: `x t`, with `t` the transversal element at `i`. -/
theorem scosBase_comp (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n)
    (L : List (Fin (n + n) × Perm (Fin (n + n)))) {i M S : ℕ} (hi : i < L.length)
    (hM : (scosBaseV gs x a).wt ≤ M) (hN : n + n + 1 ≤ M) (hLw : (encPairs ptKey L).wt ≤ S)
    (hMS : M ^ 3 ≤ S) :
    Det (𝒫) (scosBaseE6 gs x a L i)
      (.call 87 (mk2 (arg 1) (.get (.get (.var 5) (.var 6)) (.nat 1))))
      (encPerm (nintSum x * (L[i]'hi).2)) (100000 * S) := by
  have d1 : Det (𝒫) (scosBaseE6 gs x a L i) (arg 1) (encPerm (nintSum x)) _ :=
    Det.arg' (vs := [encGroup gs, encPerm (nintSum x), scosInd ({a} : Finset (Fin n))])
      (rest := [.nat a, .nat n, .nat (n + a), .nat (scosBaseTau x a), encPairs ptKey L, .nat i])
      (j := 1) rfl
  have dv5 : Det (𝒫) (scosBaseE6 gs x a L i) (.var 5) (.list (L.map (GI.Lang.encPair ptKey))) _ :=
    Det.var' (i := 5) rfl
  have dp := Det.get' dv5 (Det.var' (i := 6) rfl) (v := GI.Lang.encPair ptKey (L[i]'hi))
    (by rw [List.getElem?_map, List.getElem?_eq_getElem hi]; rfl)
  have dp' : Det (𝒫) (scosBaseE6 gs x a L i) (.get (.var 5) (.var 6))
      (.list [natList (ptKey (L[i]'hi).1), encPerm (L[i]'hi).2]) _ := dp
  have dt := Det.get' dp' (Det.nat 1) (v := encPerm (L[i]'hi).2) rfl
  have d := Det.call (Det.mk2 d1 dt)
    (compose_spec (scos_compose (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
      (nintSum x) (L[i]'hi).2)
  refine d.mono ?_
  have w5 : (Val.list [encGroup gs, encPerm (nintSum x),
    scosInd ({a} : Finset (Fin n))]).wt ≤ M := hM
  have hp : (GI.Lang.encPair ptKey (L[i]'hi)).wt < (encPairs ptKey L).wt := by
    have := wt_le_wt_list (vs := L.map (GI.Lang.encPair ptKey))
      (v := GI.Lang.encPair ptKey (L[i]'hi)) (List.mem_map_of_mem (List.getElem_mem hi))
    exact this
  have e0 : (encPairs ptKey L).wt = (Val.list (L.map (GI.Lang.encPair ptKey))).wt := rfl
  have e1 : (GI.Lang.encPair ptKey (L[i]'hi)).wt =
      (Val.list [natList (ptKey (L[i]'hi).1), encPerm (L[i]'hi).2]).wt := rfl
  have hpt : (encPerm (L[i]'hi).2).wt < (Val.list [natList (ptKey (L[i]'hi).1),
      encPerm (L[i]'hi).2]).wt := wt_le_wt_list (by simp)
  have w1 := wt_list2_le (encPerm (nintSum x)) (encPerm (L[i]'hi).2)
  have w2 := wt_encPerm_le (nintSum x)
  have w3 := wt_encPerm_le (nintSum x * (L[i]'hi).2)
  have w4 := wt_nat_le i
  have w6 : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
  have hlen : L.length < (encPairs ptKey L).wt := by
    have := length_lt_wt_list (L.map (GI.Lang.encPair ptKey))
    simpa [encPairs] using this
  have hx : (encPerm (nintSum x)).wt < (scosBaseV gs x a).wt := wt_le_wt_list (by simp)
  have p1 : (n + n + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left hN 3
  have p2 : (n + n + 1) ^ 2 ≤ (n + n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p3 : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) M
  have hK : permK = 30000 := rfl
  rw [hK]
  omega

/-- The cost of the stabilizer call. -/
noncomputable def scosBaseP (hps : PointwiseStab) (M : ℕ) : ℕ :=
  (pointwiseStabPrim hps).boundSize (30 * M) + pstabK * (30 * M) ^ 9 + 100 * M

/-- **The second entry** of the answer: the stabilizer of `n + α`. -/
theorem scosBase_stab (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n)
    (L : List (Fin (n + n) × Perm (Fin (n + n)))) {i M : ℕ}
    (hM : (scosBaseV gs x a).wt ≤ M) (hN : n + n + 1 ≤ M) (hW6 : 320 * (n + n + 1) ^ 6 ≤ M) :
    EvalAll (𝒫) (scosBaseE6 gs x a L i) (.call 117 (mk2 (arg 0) (mk1 (.var 3))))
      (fun w cost => GroupVal (n + n) w (pointwiseStab (gens gs) [Fin.natAdd n a]) ∧
        w.wt ≤ 320 * (n + n + 1) ^ 6 ∧ cost ≤ scosBaseP hps M) := by
  have d0 : Det (𝒫) (scosBaseE6 gs x a L i) (arg 0) (encGroup gs) _ :=
    Det.arg' (vs := [encGroup gs, encPerm (nintSum x), scosInd ({a} : Finset (Fin n))])
      (rest := [.nat a, .nat n, .nat (n + a), .nat (scosBaseTau x a), encPairs ptKey L, .nat i])
      (j := 0) rfl
  have dp : Det (𝒫) (scosBaseE6 gs x a L i) (mk1 (.var 3)) (encPts [Fin.natAdd n a]) _ :=
    Det.mk1 (Det.var' (i := 3) rfl)
  have darg := Det.mk2 d0 dp
  refine EvalAll.call_funAll darg fun v ca h => ?_
  obtain ⟨rfl, hca⟩ := h
  refine (pstab_spec hps (scos_pstab (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    scos_prim0 (G := gens gs) ⟨gs, rfl, rfl⟩ [Fin.natAdd n a]).mono fun w cb hw => ?_
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨h1, h2, ?_⟩
  have w5 : (Val.list [encGroup gs, encPerm (nintSum x),
    scosInd ({a} : Finset (Fin n))]).wt ≤ M := hM
  have hg : (encGroup gs).wt < (scosBaseV gs x a).wt := wt_le_wt_list (by simp)
  have e1 : (encPts [Fin.natAdd n a]).wt =
      (Val.list [.nat ((Fin.natAdd n a : Fin (n + n)) : ℕ)]).wt := rfl
  have e2 := wt_list1_le (.nat ((Fin.natAdd n a : Fin (n + n)) : ℕ))
  have e3 := wt_nat_le ((Fin.natAdd n a : Fin (n + n)) : ℕ)
  have e6 := (Fin.natAdd n a : Fin (n + n)).isLt
  have w1 := wt_list2_le (encGroup gs) (encPts [Fin.natAdd n a])
  have hW : (Val.list [encGroup gs, encPts [Fin.natAdd n a]]).wt ≤ 30 * M := by omega
  have hs : (Val.list [encGroup gs, encPts [Fin.natAdd n a]]).size ≤ 30 * M := by
    have := Val.size_le_wt (.list [encGroup gs, encPts [Fin.natAdd n a]])
    omega
  have b1 := GI.Lang.Prim.bound_le (pointwiseStabPrim hps) hs
  have b2 : (Val.list [encGroup gs, encPts [Fin.natAdd n a]]).wt ^ 9 ≤ (30 * M) ^ 9 :=
    Nat.pow_le_pow_left hW 9
  have b3 : pstabK * (Val.list [encGroup gs, encPts [Fin.natAdd n a]]).wt ^ 9 ≤
      pstabK * (30 * M) ^ 9 := Nat.mul_le_mul_left pstabK b2
  have w2 := wt_list2_le (encGroup gs) (encPts [Fin.natAdd n a])
  have e7 : ((fun i : ℕ => Val.nat i) ((Fin.natAdd n a : Fin (n + n)) : ℕ)).wt =
    (Val.nat ((Fin.natAdd n a : Fin (n + n)) : ℕ)).wt := rfl
  have e8 : (Val.list [(fun i : ℕ => Val.nat i) ((Fin.natAdd n a : Fin (n + n)) : ℕ)]).wt =
    (Val.list [Val.nat ((Fin.natAdd n a : Fin (n + n)) : ℕ)]).wt := rfl
  unfold scosBaseP
  omega

end Steps

end GI.Impl
