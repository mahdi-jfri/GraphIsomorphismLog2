import Workspace.Impl.TermJProgG
import Workspace.Impl.TermJProgNq
import Workspace.Impl.TermJPoly

/-!
# The groups `G|_dom` and `N^q` for the per-label program (program)

The per-label program factors `(h; 1)` in `⟨G|_dom⟩ ⟨N^q⟩` (paper, proof of Theorem A.18, lines
3556–3562). Its context holds both groups as group values on `Fin (m q)`. `tmJPrepAF`, on
`[sv, coordsVal e S E, σN]`, computes

1. the table `[ρ, ρ⁻¹]` of the numbering (`tmCs_tab_spec`), and from it the generators of
   `G|_dom` (`tmJ_g_spec`);
2. `q` and `m` from the shape of the coordinate table, and the local context
   `tmJLocCtx m q`;
3. the generators of `N^q` (`tmJ_nq_spec`);
4. both group values (`mkGroup_spec`).

It returns `[encGroup gsG, encGroup gsNq, tmJLocCtx m q]` (`tmJ_prepA_spec`). Every step is
deterministic.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val encPerm encGroup encPerms gens)

variable {Ω C : Type} {k : ℕ}

/-- On `[sv, cv, σN]`: `[encGroup gsG, encGroup gsNq, lc]`. -/
def tmJPrepAF (tab gg rg mk nq : ℕ) : Expr :=
  .letE (.call tab (mk2 (arg 0) (arg 1)))
  (.letE (.call gg (mk2 (arg 0) (.var 1)))
  (.letE (.length (arg 1))
  (.letE (.length (.get (arg 1) (.nat 0)))
  (.letE (mk4 (.call rg (.var 4)) (.call rg (.var 3)) (.var 3) (.var 4))
  (.letE (.arith .mul (.var 4) (.var 3))
  (.letE (.call nq (mk2 (arg 2) (.var 5)))
  (mk3 (.call mk (mk2 (.var 6) (.var 2))) (.call mk (mk2 (.var 6) (.var 7))) (.var 5))))))))

/-- Where the pieces of `tmJPrepAF` sit. -/
structure TmJPrepAAt (P : Program) (f tab gg rg mk nq : ℕ) : Prop where
  hf : P.funs[f]? = some (tmJPrepAF tab gg rg mk nq)
  htab : ∃ dom rg' tb tbe inv, TmCsTabAt P tab dom rg' tb tbe inv
  hgg : ∃ dom mpc cj cp, TmJGAt P gg dom mpc cj cp
  hrg : P.HasAt rg (rangeFuns rg)
  hmk : P.HasAt mk (mkGroupFuns mk)
  hnq : ∃ rg' tbR row mp locA dsA tbA tbe pr prg prt prte fl app,
    TmJNqAt P nq rg' tbR row mp locA dsA tbA tbe pr prg prt prte fl app

/-- The bound of `tmJPrepAF`, in the weight `W` of its input. -/
def tmJPrepAK (W : ℕ) : ℕ :=
  100000 * (W + tmCsTabK (2 * W) + tmJGK (5 * W + 2 * tmCsTabK (2 * W) + 6) +
    mkGroupK * ((tmJGK (5 * W + 2 * tmCsTabK (2 * W) + 6) + 2) * (W + 1) ^ 2) ^ 3 +
    tmJNqK (W + (W + 1) ^ 2) + mkGroupK * ((tmJNqK (W + (W + 1) ^ 2) + 2) * (W + 1) ^ 2) ^ 3 +
    16000 * (W + 1) ^ 3 + (W + 1) ^ 2 + 100)

theorem tmJPrepAK_poly : TmJPoly tmJPrepAK := by
  have hW : TmJPoly fun W => W := TmJPoly.id
  have hW1 : TmJPoly fun W => W + 1 := TmJPoly.add hW (TmJPoly.const 1)
  have hT : TmJPoly fun W => tmCsTabK (2 * W) := by
    unfold tmCsTabK; exact TmJPoly.comp (TmJPoly.smul 2 hW) _ _
  have hG : TmJPoly fun W => tmJGK (5 * W + 2 * tmCsTabK (2 * W) + 6) := by
    unfold tmJGK
    exact TmJPoly.comp (TmJPoly.add (TmJPoly.add (TmJPoly.smul 5 hW) (TmJPoly.smul 2 hT))
      (TmJPoly.const 6)) _ _
  have hQ : TmJPoly fun W => tmJNqK (W + (W + 1) ^ 2) := by
    unfold tmJNqK
    exact TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add hW (TmJPoly.pow hW1 2)) _)
  have hM : ∀ {F : ℕ → ℕ}, TmJPoly F →
      TmJPoly fun W => mkGroupK * ((F W + 2) * (W + 1) ^ 2) ^ 3 := fun hF =>
    TmJPoly.smul _ (TmJPoly.pow (TmJPoly.mul (TmJPoly.add hF (TmJPoly.const 2))
      (TmJPoly.pow hW1 2)) 3)
  unfold tmJPrepAK
  exact TmJPoly.smul _ (TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add
    (TmJPoly.add (TmJPoly.add (TmJPoly.add hW hT) hG) (hM hG)) hQ) (hM hQ))
    (TmJPoly.smul _ (TmJPoly.pow hW1 3))) (TmJPoly.pow hW1 2)) (TmJPoly.const 100))

private theorem tmJPA_lt_wt {n : ℕ} (σ : Equiv.Perm (Fin n)) : n < (encPerm σ).wt := by
  have h := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (σ i))
  simp only [List.length_map, List.length_finRange] at h
  exact h

/-- **The groups `G|_dom` and `N^q`.** -/
theorem tmJ_prepA_spec {P : Program} {f tab gg rg mk nq : ℕ}
    (hA : TmJPrepAAt P f tab gg rg mk nq) (e : Ω ≃ Fin k) (c : C → ℕ) {S : State Ω C}
    {sv : Val} (hsv : Canon e c sv S) {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (hs : (domFin e S.dom).length = m * q) (hq : 0 < q) (σN : List (Equiv.Perm (Fin m))) :
    ∃ gs : List (Equiv.Perm (Fin k)), gens gs = groupFin e S.G ∧
      FunDet P f (.list [sv, coordsVal e S E, .list (σN.map encPerm)])
        (.list [encGroup (tmJGList e S E gs),
          encGroup ((tmJNqList (q := q) σN).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))),
          tmJLocCtx m q])
        (tmJPrepAK (Val.list [sv, coordsVal e S E, .list (σN.map encPerm)]).wt) := by
  obtain ⟨dom, rg', tb, tbe, inv, hTab⟩ := hA.htab
  obtain ⟨dom', mpc, cj, cp, hG⟩ := hA.hgg
  obtain ⟨rg'', tbR, row, mp, locA, dsA, tbA, tbe', pr, prg, prt, prte, fl, app, hNq⟩ := hA.hnq
  have dT := tmCs_tab_spec hTab e c hsv E hs hq
  obtain ⟨gs, hgs, -, dG⟩ := tmJ_g_spec hG e c hsv E hs
  refine ⟨gs, hgs, FunDet.intro hA.hf ?_⟩
  unfold tmJPrepAF
  obtain ⟨W, hW⟩ : ∃ W, (Val.list [sv, coordsVal e S E, .list (σN.map encPerm)]).wt = W :=
    ⟨_, rfl⟩
  rw [hW]
  have hk : k ≤ sv.wt := StateVal.k_le_wt hsv.stateVal
  have wsv : sv.wt < W := hW ▸ wt_le_wt_list (by simp)
  have wcv : (coordsVal e S E).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wnl : (Val.list (σN.map encPerm)).wt < W := hW ▸ wt_le_wt_list (by simp)
  have w2 : (Val.list [sv, coordsVal e S E]).wt ≤ W :=
    hW ▸ wt_list_mono ⟨[.list (σN.map encPerm)], rfl⟩
  -- the shape of the coordinate table
  set rows := (List.finRange q).map fun j => natList ((List.finRange m).map
      fun β => ((e (E (β, j)).val : Fin k) : ℕ)) with hrows
  have hcvl : coordsVal e S E = .list rows := rfl
  have hr0 : rows[0]? = some (.list ((List.finRange m).map fun β =>
      Val.nat ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))) := by
    simp [hrows, natList, hq, Function.comp_def]
  have hrl : rows.length = q := by simp [hrows]
  have wq : q < W := by
    have := length_lt_wt_list rows; rw [hrl, ← hcvl] at this; omega
  have wr0 : (Val.list ((List.finRange m).map fun β =>
      Val.nat ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))).wt < W := by
    have := wt_le_wt_list (List.mem_of_getElem? hr0); rw [← hcvl] at this; omega
  have wm : m < W := by
    have := length_lt_wt_list ((List.finRange m).map fun β =>
      Val.nat ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))
    simp only [List.length_map, List.length_finRange] at this; omega
  -- the bounds
  obtain ⟨X2, hX2⟩ : ∃ X2, (W + 1) ^ 2 = X2 := ⟨_, rfl⟩
  obtain ⟨X3, hX3⟩ : ∃ X3, (W + 1) ^ 3 = X3 := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ : ∃ A1, tmCsTabK (2 * W) = A1 := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2, tmJGK (5 * W + 2 * A1 + 6) = A2 := ⟨_, rfl⟩
  obtain ⟨A4, hA4⟩ : ∃ A4, tmJNqK (W + X2) = A4 := ⟨_, rfl⟩
  obtain ⟨A3, hA3⟩ : ∃ A3, mkGroupK * ((A2 + 2) * X2) ^ 3 = A3 := ⟨_, rfl⟩
  obtain ⟨A5, hA5⟩ : ∃ A5, mkGroupK * ((A4 + 2) * X2) ^ 3 = A5 := ⟨_, rfl⟩
  have hK : tmJPrepAK W = 100000 * (W + A1 + A2 + A3 + A4 + A5 + 16000 * X3 + X2 + 100) := by
    unfold tmJPrepAK; rw [hX2, hX3, hA1, hA2, hA4, hA3, hA5]
  rw [hK]
  obtain ⟨Sb, hSb⟩ : ∃ Sb, W + A1 + A2 + A3 + A4 + A5 + 16000 * X3 + X2 + 100 = Sb := ⟨_, rfl⟩
  rw [hSb]
  have hX1 : 1 ≤ W + 1 := by omega
  have hp23 : X2 ≤ X3 := hX2 ▸ hX3 ▸ Nat.pow_le_pow_right hX1 (by norm_num)
  have hWX : W + 1 ≤ X2 := hX2 ▸ Nat.le_self_pow (by norm_num) _
  have hmq : m * q + 1 ≤ X2 := by
    have : m * q ≤ W * W := Nat.mul_le_mul wm.le wq.le
    have e : (W + 1) ^ 2 = W * W + 2 * W + 1 := by ring
    omega
  have hm1 : (m + 1) * (q + 1) ≤ X2 := by
    rw [← hX2, sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have hm3 : (m + 1) ^ 3 ≤ X3 := hX3 ▸ Nat.pow_le_pow_left (by omega) 3
  have hq3 : (q + 1) ^ 3 ≤ X3 := hX3 ▸ Nat.pow_le_pow_left (by omega) 3
  have e1m : (encPerm (1 : Equiv.Perm (Fin m))).wt ≤ 4 * X2 := by
    have := wt_encPerm_le (1 : Equiv.Perm (Fin m))
    have : (m + 1) ^ 2 ≤ X2 := hX2 ▸ Nat.pow_le_pow_left (by omega) 2
    omega
  have e1q : (encPerm (1 : Equiv.Perm (Fin q))).wt ≤ 4 * X2 := by
    have := wt_encPerm_le (1 : Equiv.Perm (Fin q))
    have : (q + 1) ^ 2 ≤ X2 := hX2 ▸ Nat.pow_le_pow_left (by omega) 2
    omega
  have wlc : (tmJLocCtx m q).wt ≤ 30 * X2 := by
    have h := wt_list4_le (encPerm (1 : Equiv.Perm (Fin m))) (encPerm (1 : Equiv.Perm (Fin q)))
      (.nat q) (.nat m)
    have := wt_nat_le m
    have := wt_nat_le q
    have : (tmJLocCtx m q).wt = (Val.list [encPerm (1 : Equiv.Perm (Fin m)),
      encPerm (1 : Equiv.Perm (Fin q)), .nat q, .nat m]).wt := rfl
    omega
  -- step 1: the table
  set tabV := Val.list [encPerm (tmCsRhoP e E hs), encPerm (tmCsRhoP e E hs)⁻¹] with htabV
  have a0 := Det.arg' (P := P) (vs := [sv, coordsVal e S E, .list (σN.map encPerm)]) (rest := [])
    (j := 0) (v := sv) rfl
  have a1 := Det.arg' (P := P) (vs := [sv, coordsVal e S E, .list (σN.map encPerm)]) (rest := [])
    (j := 1) (v := coordsVal e S E) rfl
  have wtab : tabV.wt < A1 := by
    have h := FunDet.wt_lt dT
    have : tmCsTabK ((Val.list [sv, coordsVal e S E]).wt + k) ≤ A1 := by
      rw [← hA1]; unfold tmCsTabK
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  have c1 := (Det.call (Det.mk2 a0 a1) dT).mono (c' := 20 * Sb) (by
    have h := wt_list2_le sv (coordsVal e S E)
    have : tmCsTabK ((Val.list [sv, coordsVal e S E]).wt + k) ≤ A1 := by
      rw [← hA1]; unfold tmCsTabK
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega)
  -- step 2: the generators of `G|_dom`
  set glV := Val.list ((tmJGList e S E gs).map encPerm) with hglV
  have b0 := Det.arg' (P := P) (vs := [sv, coordsVal e S E, .list (σN.map encPerm)])
    (rest := [tabV]) (j := 0) (v := sv) rfl
  have b1 := Det.var' (P := P) (env := [Val.list [sv, coordsVal e S E, .list (σN.map encPerm)], tabV]) (i := 1) (v := tabV) rfl
  have hGK : tmJGK ((Val.list [sv, tabV]).wt + k) ≤ A2 := by
    have := wt_list2_le sv tabV
    rw [← hA2]; unfold tmJGK
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have wgl : glV.wt < A2 := by have := FunDet.wt_lt dG; omega
  have c2 := (Det.call (Det.mk2 b0 b1) dG).mono (c' := 20 * Sb) (by
    have := wt_list2_le sv tabV
    omega)
  -- steps 3, 4: `q` and `m`
  have d1 := Det.arg' (P := P) (vs := [sv, coordsVal e S E, .list (σN.map encPerm)])
    (rest := [tabV, glV]) (j := 1) (v := coordsVal e S E) rfl
  rw [hcvl] at d1
  have c3 := (Det.length d1).mono (c' := 20 * Sb) (by rw [hrl, ← hcvl]; omega)
  rw [hrl] at c3
  have f1 := Det.arg' (P := P) (vs := [sv, coordsVal e S E, .list (σN.map encPerm)])
    (rest := [tabV, glV, .nat q]) (j := 1) (v := coordsVal e S E) rfl
  rw [hcvl] at f1
  have c4 := (Det.length (Det.get' f1 (Det.nat 0) hr0)).mono (c' := 20 * Sb) (by
    simp only [List.length_map, List.length_finRange]
    rw [← hcvl]; omega)
  rw [show ((List.finRange m).map fun β => Val.nat ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ)).length
    = m by simp] at c4
  -- step 5: the local context
  have g4 := Det.var' (P := P) (env := [Val.list [sv, coordsVal e S E, .list (σN.map encPerm)], tabV, glV, .nat q, .nat m]) (i := 4) (v := .nat m) rfl
  have g3 := Det.var' (P := P) (env := [Val.list [sv, coordsVal e S E, .list (σN.map encPerm)], tabV, glV, .nat q, .nat m]) (i := 3) (v := .nat q) rfl
  have c5 := (Det.mk4 (Det.call g4 (GI.Lang.range_det hA.hrg m))
    (Det.call g3 (GI.Lang.range_det hA.hrg q)) g3 g4).mono (c' := 20 * Sb) (by
    have := wt_nat_le m
    have := wt_nat_le q
    have : (tmJLocCtx m q).wt = (Val.list [encPerm (1 : Equiv.Perm (Fin m)),
      encPerm (1 : Equiv.Perm (Fin q)), .nat q, .nat m]).wt := rfl
    omega)
  -- step 6: `m q`
  set env5 := [Val.list [sv, coordsVal e S E, .list (σN.map encPerm)], tabV, glV, .nat q, .nat m, tmJLocCtx m q] with henv5
  have h4 := Det.var' (P := P) (env := env5) (i := 4) (v := .nat m) rfl
  have h3 := Det.var' (P := P) (env := env5) (i := 3) (v := .nat q) rfl
  have c6 := (Det.arith' (op := .mul) h4 h3 (z := m * q) rfl).mono (c' := 20 * Sb) (by
    have := wt_nat_le m
    have := wt_nat_le q
    have := wt_nat_le (m * q)
    omega)
  -- step 7: the generators of `N^q`
  set env6 := env5 ++ [.nat (m * q)] with henv6
  have i2 := Det.arg' (P := P) (vs := [sv, coordsVal e S E, .list (σN.map encPerm)])
    (rest := [tabV, glV, .nat q, .nat m, tmJLocCtx m q, .nat (m * q)]) (j := 2)
    (v := .list (σN.map encPerm)) rfl
  have i5 := Det.var' (P := P) (env := env6) (i := 5) (v := tmJLocCtx m q) rfl
  have hNK : tmJNqK ((tmJNqIn σN).wt + (m + 1) * (q + 1)) ≤ A4 := by
    have : (tmJNqIn σN).wt = (Val.list (σN.map encPerm)).wt := rfl
    rw [← hA4]; unfold tmJNqK
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have wnq : (tmJPermsVal (tmJNqList (q := q) σN)).wt < A4 := by
    have := FunDet.wt_lt (tmJ_nq_spec hNq σN (q := q)); omega
  have c7 := (Det.call (Det.mk2 i2 i5) (tmJ_nq_spec hNq σN (q := q))).mono (c' := 20 * Sb) (by
    have := wt_list2_le (Val.list (σN.map encPerm)) (tmJLocCtx m q)
    omega)
  -- the result
  set env7 := env6 ++ [(tmJPermsVal (tmJNqList (q := q) σN))] with henv7
  have hnq : (tmJPermsVal (tmJNqList (q := q) σN)) = Val.list (((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))).map encPerm) := by
    simp only [tmJPermsVal, List.map_map, Function.comp_def]
  have j6 := Det.var' (P := P) (env := env7) (i := 6) (v := .nat (m * q)) rfl
  have j2 := Det.var' (P := P) (env := env7) (i := 2) (v := glV) rfl
  have j7 := Det.var' (P := P) (env := env7) (i := 7) (v := (tmJPermsVal (tmJNqList (q := q) σN))) rfl
  have j5 := Det.var' (P := P) (env := env7) (i := 5) (v := tmJLocCtx m q) rfl
  have hlen1 : (tmJGList e S E gs).length < glV.wt := by
    have := length_lt_wt_list ((tmJGList e S E gs).map encPerm)
    simp only [List.length_map] at this; exact this
  have hlen2 : ((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))).length < (tmJPermsVal (tmJNqList (q := q) σN)).wt := by
    rw [hnq]
    have := length_lt_wt_list (((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))).map encPerm)
    simp only [List.length_map] at this ⊢; exact this
  have hB3 : mkGroupK * (((tmJGList e S E gs).length + 2) * (m * q + 1)) ^ 3 ≤ A3 := by
    rw [← hA3]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) hmq) 3)
  have hB5 : mkGroupK * ((((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))).length + 2) * (m * q + 1)) ^ 3 ≤
      A5 := by
    rw [← hA5]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) hmq) 3)
  have dk1 := mkGroup_spec hA.hmk (tmJGList e S E gs)
  have dk2 := mkGroup_spec hA.hmk ((tmJNqList (q := q) σN).map
    (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))))
  have wk1 := FunDet.wt_lt dk1
  have wk2 := FunDet.wt_lt dk2
  rw [← hnq] at dk2
  have k1 := (Det.call (Det.mk2 j6 j2) dk1).mono (c' := 20 * Sb) (by
    have := wt_list2_le (Val.nat (m * q)) glV
    have := wt_nat_le (m * q)
    omega)
  have k2 := (Det.call (Det.mk2 j6 j7) dk2).mono (c' := 20 * Sb) (by
    have := wt_list2_le (Val.nat (m * q)) (tmJPermsVal (tmJNqList (q := q) σN))
    have := wt_nat_le (m * q)
    omega)
  have wout := wt_list3_le (encGroup (tmJGList e S E gs)) (encGroup ((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))))) (tmJLocCtx m q)
  have cb := (Det.mk3 k1 k2 j5).mono (c' := 400 * Sb) (by omega)
  have hall := Det.letE c1 (Det.letE c2 (Det.letE c3 (Det.letE c4 (Det.letE c5
    (Det.letE c6 (Det.letE c7 cb))))))
  refine hall.mono ?_
  generalize (Val.list [encGroup (tmJGList e S E gs), encGroup ((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))), tmJLocCtx m q]).wt = O at *
  omega

end GI.Impl
