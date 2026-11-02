import Workspace.Impl.GenProdRows
import Workspace.Impl.GenCls

/-!
# The product refinement: the tables of the pairs

From the Cameron output `E`, the block numbers, `m`, `r` and `k`, `ptabs_spec` computes the
four tables the product step needs: the masks and the leading ones of the pairs of points
(`maskF`, `leadF`), and the identity tables of `Fin (k * k)` and of `Fin k`.

The masks are below `2 ^ (r + 1) ≤ k * k` (`two_pow_succ_le`), since `2 ^ r ≤ binom(m, l) ^ r`
is the number of blocks, which is at most `k`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

section bounds

variable {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) {m l r : ℕ}
  (E : Fin Q.d ≃ (Fin r → Product.KSet m l)) {k : ℕ} (e : Ω ≃ Fin k)

include Q E e in
theorem two_pow_succ_le : 2 ^ (r + 1) ≤ k * k := by
  have hd := Q.card_kset_pow E
  have hb := Q.two_le_choose E
  have hdk := Q.d_le_card e
  have h2 := Q.two_le
  have h3 : 2 ^ r ≤ m.choose l ^ r := Nat.pow_le_pow_left hb r
  have h4 : 2 ≤ k := by omega
  have h5 : 2 * k ≤ k * k := Nat.mul_le_mul_right k h4
  rw [pow_succ]
  omega

theorem maskF_le (j : Fin (k * k)) : maskF Q E e j ≤ k * k :=
  (pmask_lt Q E _ _).le.trans (two_pow_succ_le Q E e)

theorem leadF_le (j : Fin (k * k)) : leadF Q E e j ≤ k * k :=
  (leadN_le _ _ _).trans ((Nat.lt_two_pow_self).le.trans (two_pow_succ_le Q E e))

end bounds

/-- The identity table of `Fin n`, by `range`. -/
theorem ids_det {P : Program} {b : ℕ} (h : P.HasAt b (rangeFuns b)) (n : ℕ) :
    FunDet P b (.nat n) (encFun fun j : Fin n => (j : ℕ)) (7000 * (n + 1) ^ 3) :=
  (range_spec h n).mono fun w c hw => by
    obtain ⟨rfl, hc⟩ := hw
    refine ⟨natList_range_eq n, ?_⟩
    rw [natList_range_eq] at hc
    have h1 := wt_ids_le n
    have h2 := wt_nat_le n
    have h3 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h4 : (Val.nat n).wt + n + (encFun fun j : Fin n => (j : ℕ)).wt + 1 ≤ 7 * (n + 1) ^ 2 := by
      omega
    have h5 := Nat.mul_le_mul_left (loopModK * (n + 1)) h4
    have e1 : loopModK * (n + 1) * (7 * (n + 1) ^ 2) = 7000 * (n + 1) ^ 3 := by
      simp only [loopModK]; ring
    omega

/-- The tables of the product step, on `[E, block numbers, m, r, k]`: the rows of the points,
the two identity tables, and the masks and leading ones of the pairs. -/
def ptabsE (bprows brange bm0 bm1 : ℕ) : Expr :=
  .letE (.call bprows (mk4 (arg 0) (arg 1) (arg 2) (arg 3)))
  (.letE (.call brange (.arith .mul (arg 4) (arg 4)))
  (.letE (.call brange (arg 4))
  (.letE (mk3 (.var 1) (arg 4) (arg 3))
    (mk4 (.call bm0 (mk2 (.var 4) (.var 2))) (.call bm1 (mk2 (.var 4) (.var 2))) (.var 2)
      (.var 3)))))

def ptabsK : ℕ := 10 ^ 75

theorem ptabs_cost {X k r c1 c2 c3 c4 c5 rw cw i2 ik mw lw ow : ℕ}
    (hp : 2 ^ (r + 1) ≤ k * k)
    (h1 : c1 ≤ 4 * (2 * X + 8) + 4 * X + 9 + 10 ^ 14 * (X + 1) ^ 6 + rw + 1)
    (hrw : rw < 10 ^ 14 * (X + 1) ^ 6)
    (h2 : c2 ≤ 2 * (2 * X + 9) + k * k + 3 + 7000 * (k * k + 1) ^ 3 + i2 + 1)
    (h3 : c3 ≤ 2 * X + 9 + 7000 * (k + 1) ^ 3 + ik + 1)
    (h4 : c4 ≤ rw + 1 + 2 * X + 9 + 2 * X + 8 + 3 * cw + 8)
    (hcw : cw ≤ 2 * (rw + (k + 2) + (r + 2)) + 7)
    (h5 : c5 ≤ 2 * (cw + 1 + i2 + 1 + 2 * (2 * (cw + i2) + 6) + 7 +
        10 ^ 13 * (cw + k * k + 2 ^ (r + 1) + 1) ^ 4 + (mw + lw) + 1) + i2 + 1 + ik + 1 +
        4 * ow + 9)
    (hi2 : i2 ≤ 4 * (k * k + 1) ^ 2) (hik : ik ≤ 4 * (k + 1) ^ 2)
    (hmw : mw + lw ≤ 8 * (k * k + 1) ^ 2)
    (how : ow ≤ 2 * (mw + lw + i2 + ik) + 8) :
    c1 + (c2 + (c3 + (c4 + c5 + ow + 1) + ow + 1) + ow + 1) + ow + 1 ≤
      ptabsK * (X + k * k + 1) ^ 24 := by
  have hk : k ≤ k * k := Nat.le_mul_self k
  have hr : r + 1 < 2 ^ (r + 1) := Nat.lt_two_pow_self
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = X + k * k + 1 := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by omega
  have hX6 : (X + 1) ^ 6 ≤ Z ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hkk3 : (k * k + 1) ^ 3 ≤ Z ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hk3 : (k + 1) ^ 3 ≤ Z ^ 3 :=
    Nat.pow_le_pow_left (by have := Nat.le_mul_self k; omega) 3
  have hkk2 : (k * k + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hk2 : (k + 1) ^ 2 ≤ Z ^ 2 :=
    Nat.pow_le_pow_left (by have := Nat.le_mul_self k; omega) 2
  have p12 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have p36 : Z ^ 3 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have p624 : Z ^ 6 ≤ Z ^ 24 := Nat.pow_le_pow_right hZ1 (by norm_num)
  -- the weight of the context
  have hcw' : cw + k * k + 2 ^ (r + 1) + 1 ≤ 3 * 10 ^ 14 * Z ^ 6 := by omega
  have h4p := Nat.pow_le_pow_left hcw' 4
  have e4 : (3 * 10 ^ 14 * Z ^ 6) ^ 4 = 81 * 10 ^ 56 * Z ^ 24 := by ring
  rw [e4] at h4p
  have h4q := Nat.mul_le_mul_left (10 ^ 13) h4p
  have e5 : 10 ^ 13 * (81 * 10 ^ 56 * Z ^ 24) = 81 * 10 ^ 69 * Z ^ 24 := by ring
  rw [e5] at h4q
  rw [← hZ]
  unfold ptabsK
  generalize 10 ^ 13 * (cw + k * k + 2 ^ (r + 1) + 1) ^ 4 = T at *
  generalize (X + 1) ^ 6 = X6 at *
  generalize (k * k + 1) ^ 3 = A3 at *
  generalize (k + 1) ^ 3 = B3 at *
  generalize (k * k + 1) ^ 2 = A2 at *
  generalize (k + 1) ^ 2 = B2 at *
  generalize 2 ^ (r + 1) = R at *
  omega

open GI.Cited in
theorem ptabs_spec {P : Program} {f bprows bm fadd brep bga brange bm0 bm1 fs0 fs1 bl beq : ℕ}
    (hf : P.funs[f]? = some (ptabsE bprows brange bm0 bm1))
    (hprows : P.funs[bprows]? = some (prowsE bm brep bga)) (hbm : P.HasAt bm (mapFuns bm fadd))
    (hfadd : P.funs[fadd]? = some addOneF) (hrep : P.HasAt brep (replicateFuns brep))
    (hga : P.HasAt bga (gatherFuns bga)) (hrange : P.HasAt brange (rangeFuns brange))
    (hm0 : P.HasAt bm0 (mapFuns bm0 fs0)) (hfs0 : P.funs[fs0]? = some (pselF bl 0))
    (hm1 : P.HasAt bm1 (mapFuns bm1 fs1)) (hfs1 : P.funs[fs1]? = some (pselF bl 1))
    (hl : P.HasAt bl (pbFuns bl beq)) (heq : P.HasAt beq (eqNatsFuns beq))
    {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) {m l r : ℕ}
    (E : Fin Q.d ≃ (Fin r → Product.KSet m l)) {k : ℕ} (e : Ω ≃ Fin k) :
    FunDet P f (.list [encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r, .nat k])
      (.list [encFun (maskF Q E e), encFun (leadF Q E e), encFun (fun j : Fin (k * k) => (j : ℕ)),
        encFun fun j : Fin k => (j : ℕ)])
      (ptabsK * ((Val.list [encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r,
        .nat k]).wt + k * k + 1) ^ 24) := by
  set vs : List Val := [encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r, .nat k] with hvs
  set x := Val.list vs with hx
  obtain ⟨X, hX⟩ : ∃ X, X = x.wt := ⟨_, rfl⟩
  set y := Val.list [encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r] with hy
  have hyX : y.wt ≤ X := hX ▸ wt_list_mono ⟨[.nat k], rfl⟩
  have wk := wt_nat_le k
  have wr := wt_nat_le r
  have ha : ∀ (j : ℕ) (v : Val), vs[j]? = some v → ∀ rest : List Val,
      Det P (x :: rest) (arg j) v (2 * X + j + 5) := fun j v hj rest => by
    rw [hX]; exact Det.arg' hj
  -- the rows
  set rows := prodRows Q E e with hrows
  have pr := prows_spec hprows hbm hfadd hrep hga Q E e
  have hrw := FunDet.wt_lt pr
  have ey : (Val.list [encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r]).wt = y.wt := rfl
  have er : (rowsVal (prodRows Q E e)).wt = (rowsVal rows).wt := rfl
  have ey6 : prowsK * ((Val.list [encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r]).wt + 1) ^ 6
      = prowsK * (y.wt + 1) ^ 6 := rfl
  have d1 : Det P [x] (.call bprows (mk4 (arg 0) (arg 1) (arg 2) (arg 3))) (rowsVal rows)
      (4 * (2 * X + 8) + 4 * y.wt + 9 + prowsK * (y.wt + 1) ^ 6 + (rowsVal rows).wt + 1) :=
    (Det.call (Det.mk4 (ha 0 _ rfl []) (ha 1 _ rfl []) (ha 2 _ rfl []) (ha 3 _ rfl [])) pr).mono
      (by omega)
  -- the identity tables
  have d2 : Det P [x, rowsVal rows] (.call brange (.arith .mul (arg 4) (arg 4)))
      (encFun fun j : Fin (k * k) => (j : ℕ))
      (2 * (2 * X + 9) + k * k + 3 + 7000 * (k * k + 1) ^ 3 +
        (encFun fun j : Fin (k * k) => (j : ℕ)).wt + 1) :=
    (Det.call (Det.arith' (z := k * k) (ha 4 _ rfl _) (ha 4 _ rfl _) rfl) (ids_det hrange (k * k))).mono
      (by omega)
  have d3 : Det P [x, rowsVal rows, encFun fun j : Fin (k * k) => (j : ℕ)] (.call brange (arg 4))
      (encFun fun j : Fin k => (j : ℕ))
      (2 * X + 9 + 7000 * (k + 1) ^ 3 + (encFun fun j : Fin k => (j : ℕ)).wt + 1) :=
    (Det.call (ha 4 _ rfl _) (ids_det hrange k)).mono (by omega)
  set ids2 := encFun fun j : Fin (k * k) => (j : ℕ) with hids2
  set idsk := encFun fun j : Fin k => (j : ℕ) with hidsk
  set ctx := pbCtx rows r with hctx
  have ec : (Val.list [rowsVal rows, Val.nat k, Val.nat r]).wt = ctx.wt := rfl
  have d4 : Det P [x, rowsVal rows, ids2, idsk] (mk3 (.var 1) (arg 4) (arg 3)) ctx
      ((rowsVal rows).wt + 1 + (2 * X + 9) + (2 * X + 8) + 3 * ctx.wt + 8) :=
    (Det.mk3 (Det.var' rfl) (ha 4 _ rfl _) (ha 3 _ rfl _)).mono (by omega)
  -- the masks and the leading ones
  have hmask : pbSel rows r 0 = maskF Q E e := funext fun j => (pbSel_prodRows Q E e j).1
  have hlead : pbSel rows r 1 = leadF Q E e := funext fun j => (pbSel_prodRows Q E e j).2
  have t0 := pbTab_spec hm0 (sel := 0) (by norm_num) hfs0 hl heq rows (prodRows_length Q E e)
  have t1 := pbTab_spec hm1 (sel := 1) (by norm_num) hfs1 hl heq rows (prodRows_length Q E e)
  rw [hmask] at t0
  rw [hlead] at t1
  set env5 := [x, rowsVal rows, ids2, idsk, ctx] with henv5
  have dc : Det P env5 (mk2 (.var 4) (.var 2)) (.list [ctx, ids2])
      (ctx.wt + 1 + (ids2.wt + 1) + 2 * (Val.list [ctx, ids2]).wt + 7) :=
    Det.mk2 (Det.var' rfl) (Det.var' rfl)
  have d5 := Det.mk4 (Det.call dc t0) (Det.call dc t1) (Det.var' (P := P) (env := env5) (i := 2) rfl)
    (Det.var' (P := P) (env := env5) (i := 3) rfl)
  refine FunDet.intro hf ((Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4 d5)))).mono ?_)
  -- the cost
  have hp := two_pow_succ_le Q E e
  have wcw : ctx.wt ≤ 2 * ((rowsVal rows).wt + (k + 2) + (r + 2)) + 7 := by
    have := wt_list3_le (rowsVal rows) (.nat k) (.nat r)
    rw [hctx]; unfold pbCtx; omega
  have wci := wt_list2_le ctx ids2
  have hi2 : ids2.wt ≤ 4 * (k * k + 1) ^ 2 := wt_ids_le (k * k)
  have hik : idsk.wt ≤ 4 * (k + 1) ^ 2 := wt_ids_le k
  have ec4 : ((pbCtx rows r).wt + k * k + 2 ^ (r + 1) + 1) ^ 4 =
      (ctx.wt + k * k + 2 ^ (r + 1) + 1) ^ 4 := rfl
  have hmw := wt_encFun_le_sq (maskF Q E e) (maskF_le Q E e)
  have hlw := wt_encFun_le_sq (leadF Q E e) (leadF_le Q E e)
  have how := wt_list4_le (encFun (maskF Q E e)) (encFun (leadF Q E e)) ids2 idsk
  have hy6 : prowsK * (y.wt + 1) ^ 6 ≤ 10 ^ 14 * (X + 1) ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)
  rw [← hX]
  refine ptabs_cost (rw := (rowsVal rows).wt) (cw := ctx.wt) (i2 := ids2.wt) (ik := idsk.wt)
    (mw := (encFun (maskF Q E e)).wt) (lw := (encFun (leadF Q E e)).wt) hp ?_ ?_ le_rfl
    le_rfl ?_ wcw ?_ hi2 hik (by omega) how
  · have : y.wt + 1 ≤ X + 1 := by omega
    omega
  · exact hrw.trans_le hy6
  · omega
  · simp only [pbTabK] at *
    omega

end GI.Impl
