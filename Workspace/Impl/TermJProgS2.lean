import Workspace.Impl.TermJHProg2

/-!
# The kernel part of `Aut_J(X)` (program)

`tmJ_autJ_gens` generates `Aut_J(X)` from three sets. The second one is the set of local
products `tmJLam lg c` for the rows `c` of a kernel matrix of the sum map (paper, proof of
Theorem A.23: "the kernel of the sum map on the product of local stabilizer images").
The rows come from `tmJSol_ker_spec`. This file maps the local product `tmJH_lam_spec` over
them.

* `tmJS2EF lam`, on `[[lgVal, lc], linVecVal c]`: one product `tmJLam lg c`.
* `tmJS2F mp`, on `[lgVal, encIntMatrix K, lc]`: the products of all rows of `K`
  (`tmJ_s2_spec`), as `tmJPermsVal`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv
open GI.Cited (Val encPerm encGroup gens encIntMatrix)

variable {m q : ℕ}

/-- One row: on `[[lgVal, lc], linVecVal c]`, the product `tmJLam lg c`. -/
def tmJS2EF (lam : ℕ) : Expr :=
  .call lam (mk3 (.get (arg 0) (.nat 0)) (arg 1) (.get (arg 0) (.nat 1)))

/-- All rows: on `[lgVal, encIntMatrix K, lc]`. -/
def tmJS2F (mp : ℕ) : Expr :=
  .call mp (mk2 (mk2 (arg 0) (arg 2)) (arg 1))

/-- The cost of `tmJS2F` in the weight `W` of its input. -/
def tmJS2K (W : ℕ) : ℕ := 10 ^ 31 * (W + 1) ^ 20

/-- Where the pieces sit: the two functions at `f`, `f + 1`, the map at `mp`, the local
product at `lam`. -/
structure TmJS2At (P : Program) (f mp lam fld st pw dc pp comp iv locA dsA rg tbA tbe pr prg prt
    prte : ℕ) : Prop where
  hf : P.funs[f]? = some (tmJS2F mp)
  he : P.funs[f + 1]? = some (tmJS2EF lam)
  hmp : P.HasAt mp (mapFuns mp (f + 1))
  hlam : TmJHLamAt P lam fld st pw dc pp comp iv locA dsA rg tbA tbe pr prg prt prte

private theorem tmJS2_lt_wt {n : ℕ} (σ : Perm (Fin n)) : n < (encPerm σ).wt := by
  have h := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (σ i))
  simp only [List.length_map, List.length_finRange] at h
  exact h

/-- Arithmetic of one row. -/
private theorem tmJS2_row_le {W a b c Z L : ℕ} (hZ : Z ≤ 14 * (W + 1) ^ 2)
    (hL : L ≤ 10 ^ 17 * Z ^ 9) (ha : a ≤ 100 * (W + 1) ^ 2) (hb : b ≤ 4 * (W + 1) ^ 4)
    (hc : c ≤ a + L + b + 1) : c ≤ 10 ^ 28 * (W + 1) ^ 18 := by
  have h1 : Z ^ 9 ≤ (14 * (W + 1) ^ 2) ^ 9 := Nat.pow_le_pow_left hZ 9
  have e : (14 * (W + 1) ^ 2) ^ 9 = 14 ^ 9 * (W + 1) ^ 18 := by rw [mul_pow, ← pow_mul]
  have hX : 1 ≤ W + 1 := by omega
  have p2 : (W + 1) ^ 2 ≤ (W + 1) ^ 18 := Nat.pow_le_pow_right hX (by norm_num)
  have p4 : (W + 1) ^ 4 ≤ (W + 1) ^ 18 := Nat.pow_le_pow_right hX (by norm_num)
  have p0 : 1 ≤ (W + 1) ^ 18 := Nat.one_le_pow _ _ hX
  have hL' : L ≤ 10 ^ 17 * (14 ^ 9 * (W + 1) ^ 18) :=
    hL.trans (Nat.mul_le_mul_left _ (h1.trans e.le))
  generalize (W + 1) ^ 18 = X at *
  generalize (W + 1) ^ 2 = X2 at *
  generalize (W + 1) ^ 4 = X4 at *
  norm_num at hL'
  omega

/-- Arithmetic of the map. -/
private theorem tmJS2_map_le {W G B c v o : ℕ} (hG : G ≤ W) (hB : B ≤ 10 ^ 28 * (W + 1) ^ 18)
    (hv : v ≤ 4 * W + 6) (ho : o ≤ G * (8 * (W + 1) ^ 4 + 1) + 4)
    (hc : c ≤ G * B + 1000 * (G + 1) * (2 * (v + W) + 6 + o + 1)) : c ≤ 10 ^ 30 * (W + 1) ^ 20 := by
  have hX : 1 ≤ W + 1 := by omega
  have hG1 : G + 1 ≤ W + 1 := by omega
  have t1 : G * B ≤ (W + 1) * (10 ^ 28 * (W + 1) ^ 18) :=
    Nat.mul_le_mul (by omega) hB
  have e1 : (W + 1) * (10 ^ 28 * (W + 1) ^ 18) = 10 ^ 28 * (W + 1) ^ 19 := by ring
  have hto : o ≤ (W + 1) * (9 * (W + 1) ^ 4) + 4 :=
    ho.trans (Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by
      have := Nat.one_le_pow 4 (W + 1) hX; omega)) _)
  have e2 : (W + 1) * (9 * (W + 1) ^ 4) = 9 * (W + 1) ^ 5 := by ring
  have p1 : W + 1 ≤ (W + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
  have p0 : 1 ≤ (W + 1) ^ 5 := Nat.one_le_pow _ _ hX
  have t2 : 2 * (v + W) + 6 + o + 1 ≤ 50 * (W + 1) ^ 5 := by omega
  have t3 : 1000 * (G + 1) * (2 * (v + W) + 6 + o + 1) ≤ 1000 * (W + 1) * (50 * (W + 1) ^ 5) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hG1) t2
  have e3 : 1000 * (W + 1) * (50 * (W + 1) ^ 5) = 50000 * (W + 1) ^ 6 := by ring
  have p6 : (W + 1) ^ 6 ≤ (W + 1) ^ 20 := Nat.pow_le_pow_right hX (by norm_num)
  have p19 : (W + 1) ^ 19 ≤ (W + 1) ^ 20 := Nat.pow_le_pow_right hX (by norm_num)
  generalize (W + 1) ^ 20 = X at *
  generalize (W + 1) ^ 19 = X19 at *
  generalize (W + 1) ^ 6 = X6 at *
  omega

/-- **The products of the rows of a kernel matrix.** -/
theorem tmJ_s2_spec {P : Program} {f mp lam fld st pw dc pp comp iv locA dsA rg tbA tbe pr prg prt
    prte : ℕ} (hA : TmJS2At P f mp lam fld st pw dc pp comp iv locA dsA rg tbA tbe pr prg prt prte)
    (lg : List (Fin q × Perm (Fin m))) {G : ℕ} (K : Matrix (Fin G) (Fin lg.length) ℤ) :
    FunDet P f (.list [tmJLgVal lg, encIntMatrix K, tmJLocCtx m q])
      (tmJPermsVal ((List.finRange G).map fun i => tmJLam lg (K i)))
      (tmJS2K (Val.list [tmJLgVal lg, encIntMatrix K, tmJLocCtx m q]).wt) := by
  refine FunDet.intro hA.hf ?_
  unfold tmJS2F
  obtain ⟨W, hW⟩ : ∃ W, (Val.list [tmJLgVal lg, encIntMatrix K, tmJLocCtx m q]).wt = W :=
    ⟨_, rfl⟩
  rw [hW]
  have wlg : (tmJLgVal lg).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wK : (encIntMatrix K).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wlc : (tmJLocCtx m q).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wm1 : (encPerm (1 : Perm (Fin m))).wt < (tmJLocCtx m q).wt := wt_le_wt_list (by simp)
  have wq1 : (encPerm (1 : Perm (Fin q))).wt < (tmJLocCtx m q).wt := wt_le_wt_list (by simp)
  have hm1 : m + 1 ≤ W + 1 := by have := tmJS2_lt_wt (1 : Perm (Fin m)); omega
  have hq1 : q + 1 ≤ W + 1 := by have := tmJS2_lt_wt (1 : Perm (Fin q)); omega
  have hV : (m + 1) * (q + 1) ≤ (W + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul hm1 hq1
  have hn1 : m * q + 1 ≤ (W + 1) ^ 2 := by
    have e : (m + 1) * (q + 1) = m * q + m + q + 1 := by ring
    omega
  have hn2 : (m * q + 1) ^ 2 ≤ (W + 1) ^ 4 := by
    calc (m * q + 1) ^ 2 ≤ ((W + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hn1 2
      _ = (W + 1) ^ 4 := by rw [← pow_mul]
  have hp24 : (W + 1) ^ 2 ≤ (W + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hp12 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  -- the rows
  have wc : (Val.list [tmJLgVal lg, tmJLocCtx m q]).wt ≤ 4 * W + 6 := by
    have := wt_list2_le (tmJLgVal lg) (tmJLocCtx m q); omega
  have hrow : ∀ i ∈ List.finRange G, FunDet P (f + 1) (.list [(Val.list [tmJLgVal lg, tmJLocCtx m q]), linVecVal (K i)])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLam lg (K i))))
      (10 ^ 28 * (W + 1) ^ 18) := by
    intro i _
    refine FunDet.intro hA.he ?_
    unfold tmJS2EF
    have wr : (linVecVal (K i)).wt < (encIntMatrix K).wt := wt_le_wt_list (by
      simp only [List.mem_map, List.mem_finRange, true_and]
      exact ⟨i, rfl⟩)
    have a0 := Det.arg' (P := P) (vs := [(Val.list [tmJLgVal lg, tmJLocCtx m q]), linVecVal (K i)]) (rest := []) (j := 0) (v := (Val.list [tmJLgVal lg, tmJLocCtx m q])) rfl
    have a1 := Det.arg' (P := P) (vs := [(Val.list [tmJLgVal lg, tmJLocCtx m q]), linVecVal (K i)]) (rest := []) (j := 1)
      (v := linVecVal (K i)) rfl
    have g0 := Det.get' a0 (Det.nat 0) (vs := [tmJLgVal lg, tmJLocCtx m q]) (v := tmJLgVal lg) rfl
    have g1 := Det.get' a0 (Det.nat 1) (vs := [tmJLgVal lg, tmJLocCtx m q])
      (v := tmJLocCtx m q) rfl
    have cl := Det.call (Det.mk3 g0 a1 g1) (tmJH_lam_spec hA.hlam lg (K i))
    refine cl.mono ?_
    have w2 := wt_list2_le (Val.list [tmJLgVal lg, tmJLocCtx m q]) (linVecVal (K i))
    have w3 := wt_list3_le (tmJLgVal lg) (linVecVal (K i)) (tmJLocCtx m q)
    have wo := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
      (tmJLam lg (K i)))
    have hZ : (Val.list [tmJLgVal lg, linVecVal (K i), tmJLocCtx m q]).wt + (m + 1) * (q + 1) ≤
        14 * (W + 1) ^ 2 := by omega
    exact tmJS2_row_le hZ le_rfl (by omega) (wo.trans (by omega)) le_rfl
  have hM := mapList_spec hA.hmp (List.finRange G) (fun i => linVecVal (K i))
    (fun i => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLam lg (K i))))
    (c := (Val.list [tmJLgVal lg, tmJLocCtx m q])) (fun i _ i' _ he => by simp only at he ⊢; rw [linVecVal_injective he]) hrow
  have a0 := Det.arg' (P := P) (vs := [tmJLgVal lg, encIntMatrix K, tmJLocCtx m q]) (rest := [])
    (j := 0) (v := tmJLgVal lg) rfl
  have a1 := Det.arg' (P := P) (vs := [tmJLgVal lg, encIntMatrix K, tmJLocCtx m q]) (rest := [])
    (j := 1) (v := encIntMatrix K) rfl
  have a2 := Det.arg' (P := P) (vs := [tmJLgVal lg, encIntMatrix K, tmJLocCtx m q]) (rest := [])
    (j := 2) (v := tmJLocCtx m q) rfl
  have cl := Det.call (Det.mk2 (Det.mk2 a0 a2) a1) hM
  have hval : Val.list ((List.finRange G).map fun i =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLam lg (K i)))) =
      tmJPermsVal ((List.finRange G).map fun i => tmJLam lg (K i)) := by
    simp only [tmJPermsVal, List.map_map, Function.comp_def]
  rw [hval] at cl
  refine cl.mono ?_
  -- the cost
  have hKe : Val.list ((List.finRange G).map fun i => linVecVal (K i)) = encIntMatrix K := rfl
  rw [hKe] at *
  have hG : G ≤ W := by
    have := length_lt_wt_list ((List.finRange G).map fun i => linVecVal (K i))
    simp only [List.length_map, List.length_finRange] at this
    have e : (Val.list ((List.finRange G).map fun i => linVecVal (K i))).wt =
      (encIntMatrix K).wt := rfl
    omega
  have wo := wt_tmJPermsVal_le ((List.finRange G).map fun i => tmJLam (q := q) lg (K i))
  simp only [List.length_map, List.length_finRange] at wo
  have ho : (tmJPermsVal ((List.finRange G).map fun i => tmJLam (q := q) lg (K i))).wt ≤
      G * (8 * (W + 1) ^ 4 + 1) + 4 :=
    wo.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _)
  have wl1 := wt_list2_le (tmJLgVal lg) (tmJLocCtx m q)
  have wl3 := wt_list2_le (Val.list [tmJLgVal lg, tmJLocCtx m q]) (encIntMatrix K)
  have wa0 : 2 * W + 0 + 5 ≤ 2 * W + 5 := le_rfl
  have hC := tmJS2_map_le (c := G * (10 ^ 28 * (W + 1) ^ 18) + mapK * (G + 1) *
      ((Val.list [(Val.list [tmJLgVal lg, tmJLocCtx m q]), encIntMatrix K]).wt +
        (tmJPermsVal ((List.finRange G).map fun i => tmJLam (q := q) lg (K i))).wt + 1))
    hG le_rfl wc ho (by
      unfold mapK
      refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
      omega)
  unfold tmJS2K
  simp only [List.length_finRange]
  have hX : 1 ≤ W + 1 := by omega
  have p4 : (W + 1) ^ 4 ≤ (W + 1) ^ 20 := Nat.pow_le_pow_right hX (by norm_num)
  have p2 : (W + 1) ^ 2 ≤ (W + 1) ^ 20 := Nat.pow_le_pow_right hX (by norm_num)
  have p1 : W + 1 ≤ (W + 1) ^ 20 := Nat.le_self_pow (by norm_num) _
  have hGo : G * (8 * (W + 1) ^ 4 + 1) ≤ (W + 1) * (9 * (W + 1) ^ 4) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e5 : (W + 1) * (9 * (W + 1) ^ 4) = 9 * (W + 1) ^ 5 := by ring
  have p5 : (W + 1) ^ 5 ≤ (W + 1) ^ 20 := Nat.pow_le_pow_right hX (by norm_num)
  have wl4 := wt_list2_le (Val.list [tmJLgVal lg, tmJLocCtx m q]) (encIntMatrix K)
  generalize (W + 1) ^ 20 = X at *
  omega

end GI.Impl
