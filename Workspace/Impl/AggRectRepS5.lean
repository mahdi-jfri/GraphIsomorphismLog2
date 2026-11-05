module

public import Workspace.Impl.AggRectRepS4

@[expose] public section

/-!
# The pair steps of the representation program

* `rcR_out_spec`: `outFF` on `[[Lk, k, range q], h]` gives `[h, π(h)]`, with `π(h)` read from the
  table (`rcRPiN`) at each label.
* `rcR_ps_spec`: `psFF` on `[[rowT, keys, m, range m], (g, π)]` gives `(g, ρ ⊕ π)`, for the row
  action `ρ` that the program reads from the row numbers.
* `rcR_emb_spec`: `embFF` on `[[q, m, range m], σ]` gives `τ ⊕ σ`, for the row embedding `τ`.

Here the input weight `V` and all values stay below a bound `W` with `10 V + 100 ≤ W`, and the
cost is a constant times a power of `W + 1`.
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val encPerm)
open Equiv

theorem rcR_encPerm {n : ℕ} (σ : Perm (Fin n)) :
    encPerm σ = natList (rcRL fun i => (σ i : ℕ)) := by
  rw [encPerm_eq_encFun, encFun_eq_natList]

/-- **One sum of two permutations**, by `graphStep` at `pe + 12`. -/
theorem rcR_step_spec {P : Program} {pe : ℕ} (h : P.HasAt pe (pEncMapFuns pe)) {m q : ℕ}
    (g : Perm (Fin m)) (σ : Perm (Fin q)) :
    FunDet P (pe + 12) (.list [.nat m, .list [encPerm g, encPerm σ]]) (encPerm (encPair (g, σ)))
      (natStepK * (m + q + 1) ^ 3) := by
  have hsa : P.funs[pe + 4]? = some (shiftAppF (pe + 5) (pe + 8)) := by
    simpa using (h.block 4 (gs := [shiftAppF (pe + 5) (pe + 8)]) (by rfl)).single
  have hap : P.HasAt (pe + 5) (appendFuns (pe + 5)) := h.block 5 (by rfl)
  have ham : P.HasAt (pe + 8) (mapFuns (pe + 8) (pe + 11)) := h.block 8 (by rfl)
  have hadd : P.funs[pe + 11]? = some addKF := by
    simpa using (h.block 11 (gs := [addKF]) (by rfl)).single
  have hgs : P.funs[pe + 12]? = some (graphStepF (pe + 4)) := by
    simpa using (h.block 12 (gs := [graphStepF (pe + 4)]) (by rfl)).single
  have := graphStep_spec (b := pe + 3) hsa hap ham hadd hgs g σ
  rw [show Cited.sumToFin (Perm.sumCongr g σ) = encPair (g, σ) from (encPair_eq (g, σ)).symm]
    at this
  exact this

theorem rcR_sum2 (a b : Val) : a.wt + b.wt < (Val.list [a, b]).wt := by
  have := sum_wt_lt_wt_list [a, b]; simp at this; omega

theorem rcR_sum3 (a b c : Val) : a.wt + b.wt + c.wt < (Val.list [a, b, c]).wt := by
  have := sum_wt_lt_wt_list [a, b, c]; simp at this; omega

theorem rcR_sum4 (a b c d : Val) : a.wt + b.wt + c.wt + d.wt < (Val.list [a, b, c, d]).wt := by
  have := sum_wt_lt_wt_list [a, b, c, d]; simp at this; omega

theorem rcR_wt_encPerm_le {n W : ℕ} (σ : Perm (Fin n)) (h : 4 * (n + 1) ^ 2 ≤ W) :
    (encPerm σ).wt ≤ W := (wt_encPerm_le σ).trans h

theorem rcR_sq_le {a b : ℕ} (h : a ≤ b) : (a + 1) ^ 2 ≤ (b + 1) ^ 2 :=
  Nat.pow_le_pow_left (by omega) 2

theorem rcR_W1_pow {a W : ℕ} (h : a ≤ W) (d : ℕ) : (a + 1) ^ d ≤ (W + 1) ^ d :=
  Nat.pow_le_pow_left (by omega) d

theorem rcR_cube_cost {K a W : ℕ} (h : a + 10 ≤ 10 * (W + 1)) :
    K * (a + 10) ^ 3 ≤ (1000 * K) * (W + 1) ^ 3 := by
  have := Nat.pow_le_pow_left h 3
  rw [mul_pow] at this
  calc K * (a + 10) ^ 3 ≤ K * (10 ^ 3 * (W + 1) ^ 3) := Nat.mul_le_mul_left _ this
    _ = (1000 * K) * (W + 1) ^ 3 := by ring

section Pairs

variable {P : Program} {I : RcRIdx}

set_option maxHeartbeats 1000000 in
/-- **A generator with its label part.** -/
theorem rcR_out_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.outF]? = some I.outFF)
    (hm : P.HasAt I.mPi (mapFuns I.mPi I.piF)) (hpi : P.funs[I.piF]? = some I.piFF)
    (hl0 : P.funs[I.look]? = some I.lookF) (hl1 : P.funs[I.look1]? = some I.look1F)
    (hl2 : P.funs[I.look2]? = some I.look2F)
    (hf0 : P.HasAt I.fLk0 (findFuns I.fLk0 I.lk0P)) (hp0 : P.funs[I.lk0P]? = some I.lk0PF)
    (hf1 : P.HasAt I.fLk1 (findFuns I.fLk1 I.lk1P)) (hp1 : P.funs[I.lk1P]? = some I.lk1PF)
    (hf2 : P.HasAt I.fLk2 (findFuns I.fLk2 I.lk2P)) (hp2 : P.funs[I.lk2P]? = some I.lk2PF)
    (Lk : List (List ℕ)) (k q : ℕ) (hl : List ℕ) {W : ℕ}
    (hW : 10 * (Val.list [.list [rcTV Lk, .nat k, natList (List.range q)], natList hl]).wt + 100
      ≤ W)
    (hout : (Val.list [natList hl, natList ((List.range q).map
      (rcRPiN Lk k (fun v => hl.getD v 0)))]).wt ≤ W) :
    FunDet P I.outF (.list [.list [rcTV Lk, .nat k, natList (List.range q)], natList hl])
      (.list [natList hl, natList ((List.range q).map (rcRPiN Lk k (fun v => hl.getD v 0)))])
      (10 ^ 24 * (W + 1) ^ 5) := by
  obtain ⟨V, hV⟩ : ∃ V, V =
      (Val.list [.list [rcTV Lk, .nat k, natList (List.range q)], natList hl]).wt := ⟨_, rfl⟩
  rw [← hV] at hW
  have hC : (Val.list [rcTV Lk, .nat k, natList (List.range q)]).wt < V := by
    rw [hV]; exact wt_le_wt_list (by simp)
  have sV := rcR_sum2 (.list [rcTV Lk, .nat k, natList (List.range q)]) (natList hl)
  have sC := rcR_sum3 (rcTV Lk) (.nat k) (natList (List.range q))
  rw [← hV] at sV
  have hh : (natList hl).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have hT : (rcTV Lk).wt < (Val.list [rcTV Lk, .nat k, natList (List.range q)]).wt :=
    wt_le_wt_list (by simp)
  have hk : (Val.nat k).wt < (Val.list [rcTV Lk, .nat k, natList (List.range q)]).wt :=
    wt_le_wt_list (by simp)
  have hR : (natList (List.range q)).wt < (Val.list [rcTV Lk, .nat k,
    natList (List.range q)]).wt := wt_le_wt_list (by simp)
  have hPi : (natList ((List.range q).map (rcRPiN Lk k (fun v => hl.getD v 0)))).wt <
      (Val.list [natList hl, natList ((List.range q).map
        (rcRPiN Lk k (fun v => hl.getD v 0)))]).wt := wt_le_wt_list (by simp)
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.list [rcTV Lk, .nat k,
    natList (List.range q)], natList hl]) (W := W) (j := 0) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [.list [rcTV Lk, .nat k,
    natList (List.range q)], natList hl]) (W := W) (j := 1) (v := natList hl) (by omega) rfl
  have gL := rcRDW.get a0 (j := 0) (v := rcTV Lk) rfl
  have gk := rcRDW.get a0 (j := 1) (v := .nat k) rfl
  have gR := rcRDW.get a0 (j := 2) (v := natList (List.range q)) rfl
  have w3 := wt_list3_le (rcTV Lk) (.nat k) (natList hl)
  have m3 := rcRDW.mk3 gL gk a1 (by omega)
  have w2 := wt_list2_le (.list [rcTV Lk, .nat k, natList hl]) (natList (List.range q))
  have m2 := rcRDW.mk2 m3 gR (by omega)
  have hmap := rcR_mapN hm (c := .list [rcTV Lk, .nat k, natList hl]) (xs := List.range q)
    (g := fun j => .nat (rcRPiN Lk k (fun v => hl.getD v 0) j)) (K := 10 ^ 23) (d := 3) (W := W)
    (fun j hj => (rcR_pi_spec hgD hpi hl0 hl1 hl2 hf0 hp0 hf1 hp1 hf2 hp2 Lk k hl j).mono (by
      have h1 := rcR_wt_elemN (c := .list [rcTV Lk, .nat k, natList hl]) hj
      have := rcR_cube_cost (K := 10 ^ 20) (W := W)
        (a := (Val.list [.list [rcTV Lk, .nat k, natList hl], .nat j]).wt) (by omega)
      norm_num at this ⊢
      omega)) (by omega) (by
        rw [show (List.range q).map (fun j => Val.nat (rcRPiN Lk k (fun v => hl.getD v 0) j)) =
          ((List.range q).map (rcRPiN Lk k (fun v => hl.getD v 0))).map Val.nat by
          rw [List.map_map]; rfl]
        exact hPi.le.trans hout)
  rw [show (List.range q).map (fun j => Val.nat (rcRPiN Lk k (fun v => hl.getD v 0) j)) =
    ((List.range q).map (rcRPiN Lk k (fun v => hl.getD v 0))).map Val.nat by
    rw [List.map_map]; rfl] at hmap
  have cl := rcRDW.call m2 hmap (by exact hPi.le.trans hout)
  have r := rcRDW.mk2 a1 cl hout
  refine (rcRDW.fn hf r).mono ?_
  have p := rcR_W_le (W := W) (d := 5) (by norm_num)
  norm_num
  omega

set_option maxHeartbeats 1000000 in
/-- **A pair of the carrier case**: `(g, π) ↦ (g, ρ ⊕ π)`. -/
theorem rcR_ps_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.psF]? = some I.psFF)
    (hm : P.HasAt I.mRho (mapFuns I.mRho I.rhoF)) (hrho : P.funs[I.rhoF]? = some I.rhoFF)
    (hpe : P.HasAt I.pe (pEncMapFuns I.pe)) {k q m : ℕ}
    (rowT keys : List ℕ) (g : Perm (Fin k)) (π : Perm (Fin q)) (ρ : Perm (Fin m))
    (hρ : (List.range m).map (fun r => rowT.getD ((rcRL fun i => (g i : ℕ)).getD
      (keys.getD r 0) 0) 0) = rcRL fun r => (ρ r : ℕ)) {W : ℕ}
    (hW : 10 * (Val.list [.list [natList rowT, natList keys, .nat m, natList (List.range m)],
      pairV (g, π)]).wt + 100 * (k + m + q + 1) ^ 2 + 100 ≤ W) :
    FunDet P I.psF (.list [.list [natList rowT, natList keys, .nat m, natList (List.range m)],
      pairV (g, π)]) (pairV (g, encPair (ρ, π))) (10 ^ 10 * (W + 1) ^ 3) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.list [natList rowT, natList keys, .nat m,
    natList (List.range m)], pairV (g, π)]).wt := ⟨_, rfl⟩
  rw [← hV] at hW
  have hC : (Val.list [natList rowT, natList keys, .nat m, natList (List.range m)]).wt < V := by
    rw [hV]; exact wt_le_wt_list (by simp)
  have sV := rcR_sum2 (.list [natList rowT, natList keys, .nat m, natList (List.range m)])
    (pairV (g, π))
  have sC := rcR_sum4 (natList rowT) (natList keys) (.nat m) (natList (List.range m))
  have sP := rcR_sum2 (encPerm g) (encPerm π)
  rw [← hV] at sV
  have hp : (pairV (g, π)).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have hp' : (Val.list [encPerm g, encPerm π]).wt < V := hp
  have hg : (encPerm g).wt < (Val.list [encPerm g, encPerm π]).wt := wt_le_wt_list (by simp)
  have hπ : (encPerm π).wt < (Val.list [encPerm g, encPerm π]).wt := wt_le_wt_list (by simp)
  have hr : (natList rowT).wt < (Val.list [natList rowT, natList keys, .nat m,
    natList (List.range m)]).wt := wt_le_wt_list (by simp)
  have hks : (natList keys).wt < (Val.list [natList rowT, natList keys, .nat m,
    natList (List.range m)]).wt := wt_le_wt_list (by simp)
  have hmm : (Val.nat m).wt < (Val.list [natList rowT, natList keys, .nat m,
    natList (List.range m)]).wt := wt_le_wt_list (by simp)
  have hrm : (natList (List.range m)).wt < (Val.list [natList rowT, natList keys, .nat m,
    natList (List.range m)]).wt := wt_le_wt_list (by simp)
  have hρw := wt_encPerm_le ρ
  have hsw := wt_encPerm_le (encPair (ρ, π))
  have s1 := rcR_sq_le (show m ≤ k + m + q by omega)
  have s2 := rcR_sq_le (show m + q ≤ k + m + q by omega)
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList rowT, natList keys, .nat m,
    natList (List.range m)], pairV (g, π)]) (W := W) (j := 0) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList rowT, natList keys, .nat m,
    natList (List.range m)], pairV (g, π)]) (W := W) (j := 1) (v := .list [encPerm g, encPerm π])
    (by omega) rfl
  have gr := rcRDW.get a0 (j := 0) (v := natList rowT) rfl
  have gk := rcRDW.get a0 (j := 1) (v := natList keys) rfl
  have gR := rcRDW.get a0 (j := 3) (v := natList (List.range m)) rfl
  have gg := rcRDW.get a1 (j := 0) (v := encPerm g) rfl
  rw [rcR_encPerm g] at gg
  have hg' : (natList (rcRL fun i => (g i : ℕ))).wt < (Val.list [encPerm g, encPerm π]).wt := by
    rw [← rcR_encPerm]; exact hg
  have w3 := wt_list3_le (natList rowT) (natList keys) (natList (rcRL fun i => (g i : ℕ)))
  have m3 := rcRDW.mk3 gr gk gg (by omega)
  have w2 := wt_list2_le (.list [natList rowT, natList keys, natList (rcRL fun i => (g i : ℕ))])
    (natList (List.range m))
  have m2 := rcRDW.mk2 m3 gR (by omega)
  have hmap := rcR_mapN1 hm (c := .list [natList rowT, natList keys,
    natList (rcRL fun i => (g i : ℕ))]) (xs := List.range m)
    (g := fun r => .nat (rowT.getD ((rcRL fun i => (g i : ℕ)).getD (keys.getD r 0) 0) 0))
    (K := 20000) (W := W) (fun r _ => rcR_rho_spec hgD hrho rowT keys _ r) (by omega) (by
      rw [show (List.range m).map (fun r => Val.nat (rowT.getD ((rcRL fun i => (g i : ℕ)).getD
        (keys.getD r 0) 0) 0)) = ((List.range m).map (fun r => rowT.getD ((rcRL fun i =>
        (g i : ℕ)).getD (keys.getD r 0) 0) 0)).map Val.nat by rw [List.map_map]; rfl, hρ,
        show ((rcRL fun r => (ρ r : ℕ)).map Val.nat) = (List.finRange m).map
          (fun r => Val.nat (ρ r)) by rw [List.map_map]; rfl]
      exact hρw.trans (by omega))
  rw [show (List.range m).map (fun r => Val.nat (rowT.getD ((rcRL fun i => (g i : ℕ)).getD
    (keys.getD r 0) 0) 0)) = ((List.range m).map (fun r => rowT.getD ((rcRL fun i =>
    (g i : ℕ)).getD (keys.getD r 0) 0) 0)).map Val.nat by rw [List.map_map]; rfl, hρ,
    show ((rcRL fun r => (ρ r : ℕ)).map Val.nat) = (List.finRange m).map
      (fun r => Val.nat (ρ r)) by rw [List.map_map]; rfl] at hmap
  have eρ : (Val.list ((List.finRange m).map fun r => Val.nat (ρ r))).wt = (encPerm ρ).wt := rfl
  have cl := rcRDW.call m2 hmap (by omega)
  -- the body
  have v1 := rcRDW.var (P := P) (W := W) (env := [.list [.list [natList rowT, natList keys, .nat m,
    natList (List.range m)], pairV (g, π)], encPerm ρ]) (i := 1) rfl (by omega)
  have a0' := rcRDW.arg (P := P) (rest := [encPerm ρ]) (vs := [.list [natList rowT, natList keys,
    .nat m, natList (List.range m)], pairV (g, π)]) (W := W) (j := 0) (by omega) rfl
  have a1' := rcRDW.arg (P := P) (rest := [encPerm ρ]) (vs := [.list [natList rowT, natList keys,
    .nat m, natList (List.range m)], pairV (g, π)]) (W := W) (j := 1)
    (v := .list [encPerm g, encPerm π]) (by omega) rfl
  have gm := rcRDW.get a0' (j := 2) (v := .nat m) rfl
  have gg' := rcRDW.get a1' (j := 0) (v := encPerm g) rfl
  have gp' := rcRDW.get a1' (j := 1) (v := encPerm π) rfl
  have w4 := wt_list2_le (encPerm ρ) (encPerm π)
  have i2 := rcRDW.mk2 v1 gp' (by omega)
  have w5 := wt_list2_le (.nat m) (.list [encPerm ρ, encPerm π])
  have i3 := rcRDW.mk2 gm i2 (by omega)
  have st := rcRDW.call i3 (rcR_step_spec hpe ρ π) (by omega)
  have w6 := wt_list2_le (encPerm g) (encPerm (encPair (ρ, π)))
  have r := rcRDW.mk2 gg' st (by omega)
  have dall := rcRDW.letE cl r
  refine (rcRDW.fn hf dall).mono ?_
  have p := rcR_W_le (W := W) (d := 3) (by norm_num)
  have p2 := rcR_W1_pow (show m + q ≤ W by
    have : k + m + q + 1 ≤ (k + m + q + 1) ^ 2 := by nlinarith
    omega) 3
  have hK : natStepK = 10 ^ 9 := rfl
  rw [hK]
  norm_num
  omega

set_option maxHeartbeats 1000000 in
/-- **A generator of the carrier case**: `σ ↦ τ ⊕ σ` for the row embedding `τ`. -/
theorem rcR_emb_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.embF]? = some I.embFF)
    (hm : P.HasAt I.mEmbR (mapFuns I.mEmbR I.embRF)) (hr : P.funs[I.embRF]? = some I.embRFF)
    (hpe : P.HasAt I.pe (pEncMapFuns I.pe)) {q m : ℕ} (σ : Perm (Fin q)) (τ : Perm (Fin m))
    (hτ : (List.range m).map (fun j => if j < q then (rcRL fun i => (σ i : ℕ)).getD j 0 else j) =
      rcRL fun r => (τ r : ℕ)) {W : ℕ}
    (hW : 10 * (Val.list [.list [.nat q, .nat m, natList (List.range m)], encPerm σ]).wt +
      100 * (m + q + 1) ^ 2 + 100 ≤ W) :
    FunDet P I.embF (.list [.list [.nat q, .nat m, natList (List.range m)], encPerm σ])
      (encPerm (encPair (τ, σ))) (10 ^ 10 * (W + 1) ^ 3) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.list [.nat q, .nat m, natList (List.range m)],
    encPerm σ]).wt := ⟨_, rfl⟩
  rw [← hV] at hW
  have hC : (Val.list [.nat q, .nat m, natList (List.range m)]).wt < V := by
    rw [hV]; exact wt_le_wt_list (by simp)
  have sV := rcR_sum2 (.list [.nat q, .nat m, natList (List.range m)]) (encPerm σ)
  have sC := rcR_sum3 (.nat q) (.nat m) (natList (List.range m))
  rw [← hV] at sV
  have hs : (encPerm σ).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have hq : (Val.nat q).wt < (Val.list [.nat q, .nat m, natList (List.range m)]).wt :=
    wt_le_wt_list (by simp)
  have hmm : (Val.nat m).wt < (Val.list [.nat q, .nat m, natList (List.range m)]).wt :=
    wt_le_wt_list (by simp)
  have hrm : (natList (List.range m)).wt < (Val.list [.nat q, .nat m,
    natList (List.range m)]).wt := wt_le_wt_list (by simp)
  have hτw := wt_encPerm_le τ
  have hsw := wt_encPerm_le (encPair (τ, σ))
  have s1 := rcR_sq_le (show m ≤ m + q by omega)
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.list [.nat q, .nat m,
    natList (List.range m)], encPerm σ]) (W := W) (j := 0) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [.list [.nat q, .nat m,
    natList (List.range m)], encPerm σ]) (W := W) (j := 1) (v := encPerm σ) (by omega) rfl
  have gq := rcRDW.get a0 (j := 0) (v := .nat q) rfl
  have gm := rcRDW.get a0 (j := 1) (v := .nat m) rfl
  have gR := rcRDW.get a0 (j := 2) (v := natList (List.range m)) rfl
  have a1n := rcRDW.cast a1 (rcR_encPerm σ)
  have hs' : (natList (rcRL fun i => (σ i : ℕ))).wt < V := by rw [← rcR_encPerm]; exact hs
  have w1 := wt_list2_le (natList (rcRL fun i => (σ i : ℕ))) (.nat q)
  have i1 := rcRDW.mk2 a1n gq (by omega)
  have w2 := wt_list2_le (.list [natList (rcRL fun i => (σ i : ℕ)), .nat q])
    (natList (List.range m))
  have i2 := rcRDW.mk2 i1 gR (by omega)
  have hmap := rcR_mapN1 hm (c := .list [natList (rcRL fun i => (σ i : ℕ)), .nat q])
    (xs := List.range m)
    (g := fun j => .nat (if j < q then (rcRL fun i => (σ i : ℕ)).getD j 0 else j))
    (K := 5000) (W := W) (fun j _ => rcR_embR_spec hgD hr _ q j) (by omega) (by
      rw [show (List.range m).map (fun j => Val.nat (if j < q then (rcRL fun i => (σ i : ℕ)).getD
        j 0 else j)) = ((List.range m).map (fun j => if j < q then (rcRL fun i =>
        (σ i : ℕ)).getD j 0 else j)).map Val.nat by rw [List.map_map]; rfl, hτ,
        show ((rcRL fun r => (τ r : ℕ)).map Val.nat) = (List.finRange m).map
          (fun r => Val.nat (τ r)) by rw [List.map_map]; rfl]
      exact hτw.trans (by omega))
  rw [show (List.range m).map (fun j => Val.nat (if j < q then (rcRL fun i => (σ i : ℕ)).getD
    j 0 else j)) = ((List.range m).map (fun j => if j < q then (rcRL fun i =>
    (σ i : ℕ)).getD j 0 else j)).map Val.nat by rw [List.map_map]; rfl, hτ,
    show ((rcRL fun r => (τ r : ℕ)).map Val.nat) = (List.finRange m).map
      (fun r => Val.nat (τ r)) by rw [List.map_map]; rfl] at hmap
  have eτ : (Val.list ((List.finRange m).map fun r => Val.nat (τ r))).wt = (encPerm τ).wt := rfl
  have cl := rcRDW.cast (rcRDW.call i2 hmap (by omega))
    (show Val.list ((List.finRange m).map fun r => Val.nat (τ r)) = encPerm τ from rfl)
  have w4 := wt_list2_le (encPerm τ) (encPerm σ)
  have i3 := rcRDW.mk2 cl a1 (by omega)
  have w5 := wt_list2_le (.nat m) (.list [encPerm τ, encPerm σ])
  have i4 := rcRDW.mk2 gm i3 (by omega)
  have st := rcRDW.call i4 (rcR_step_spec hpe τ σ) (by omega)
  refine (rcRDW.fn hf st).mono ?_
  have p := rcR_W_le (W := W) (d := 3) (by norm_num)
  have p2 := rcR_W1_pow (show m + q ≤ W by
    have : m + q + 1 ≤ (m + q + 1) ^ 2 := by nlinarith
    omega) 3
  have hK : natStepK = 10 ^ 9 := rfl
  rw [hK]
  norm_num
  omega

end Pairs

end GI.Impl
