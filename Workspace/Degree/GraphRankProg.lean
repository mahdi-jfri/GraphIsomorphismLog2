module

public import Workspace.Degree.GraphRank
public import Workspace.Degree.GraphBase

/-!
# Matching the levels, as a program

`rankFuns b` on `[encFun lX, encFun lY, ids n, n]` returns `[encFun (rhoN lX lY), ok]`, where
`ok = 1` if some value is `n` and `ok = 0` otherwise (`rank_spec`).
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The test of `idx`, on `[[[L, ids], u], u']`. -/
def idxTestE : Expr :=
  let L := Expr.get (.get (arg 0) (.nat 0)) (.nat 0)
  let u := Expr.get (arg 0) (.nat 1)
  .ite (.arith .eq (.get L (arg 1)) (.get L u)) (.arith .lt (arg 1) u) (.nat 0)

/-- The test of `rhoN`, on `[[[LX, IX, LY, IY, ids], u], y]`. -/
def rhoTestE : Expr :=
  let c := Expr.get (arg 0) (.nat 0)
  let u := Expr.get (arg 0) (.nat 1)
  .ite (.arith .eq (.get (.get c (.nat 2)) (arg 1)) (.get (.get c (.nat 0)) u))
    (.arith .eq (.get (.get c (.nat 3)) (arg 1)) (.get (.get c (.nat 1)) u)) (.nat 0)

/-- The test of the check, on `[[R, n], u]`. -/
def chkTestE : Expr := .arith .eq (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1))

/-- An entry of a table of searches, on `[c, u]`. -/
def srchEntryE (f j : ℕ) (len : Bool) : Expr :=
  let e := Expr.call f (mk2 (mk2 (arg 0) (arg 1)) (.get (arg 0) (.nat j)))
  if len then .length e else e

/-- The main function. -/
def rankMainE (b : ℕ) : Expr :=
  .letE (.call (b + 1) (mk2 (mk2 (arg 0) (arg 2)) (arg 2)))
  (.letE (.call (b + 1) (mk2 (mk2 (arg 1) (arg 2)) (arg 2)))
  (.letE (.call (b + 9) (mk2 (mk5 (arg 0) (.var 1) (arg 1) (.var 2) (arg 2)) (arg 2)))
    (mk2 (.var 3) (.call (b + 17) (mk2 (mk2 (.var 3) (arg 3)) (arg 2))))))

/-- The functions. Twenty-one functions. -/
def rankFuns (b : ℕ) : List Expr :=
  [rankMainE b] ++ tabFuns (b + 1) (srchEntryE (b + 5) 1 true) ++ filterFuns (b + 5) (b + 8) ++
    [idxTestE] ++ tabFuns (b + 9) (srchEntryE (b + 13) 4 false) ++ findFuns (b + 13) (b + 16) ++
    [rhoTestE] ++ anyFuns (b + 17) (b + 20) ++ [chkTestE]

/-- The budget of a test. -/
def rkT (n : ℕ) : ℕ := 1000 * levB n

theorem idx_le (ℓ : Fin n → ℕ) (u : Fin n) : idx ℓ u ≤ n := by
  have := List.length_filter_le (fun u' => decide (ℓ u' = ℓ u ∧ u' < u)) (List.finRange n)
  simp only [List.length_finRange] at this
  unfold idx
  convert this

theorem rhoN_le (lX lY : Fin n → ℕ) (u : Fin n) : rhoN lX lY u ≤ n :=
  findIdx_finRange_le _

theorem boolVal_ite (p : Prop) [Decidable p] :
    boolVal (@decide p (Classical.propDecidable _)) = .nat (if p then 1 else 0) := by
  by_cases h : p <;> simp [h, boolVal]

set_option maxHeartbeats 1000000 in
theorem idxTest_lv {P : Program} {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) (u u' : Fin n) :
    Lv P [.list [.list [.list [encFun ℓ, ids n], .nat u], .nat u']] (rkT n) idxTestE
      (boolVal (@decide (ℓ u' = ℓ u ∧ u' < u) (Classical.propDecidable _))) 1000 := by
  have h0 := levB_pos n
  have h1 := le_levB n
  have wL : (encFun ℓ).wt ≤ levB n := wt_table_le hℓ
  have wi : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have wu : (Val.nat u).wt ≤ levB n := wt_nat_levB (by omega)
  have wu' : (Val.nat u').wt ≤ levB n := wt_nat_levB (by omega)
  have w1 : (Val.list [encFun ℓ, ids n]).wt ≤ 2 * (2 * levB n + 1) + 4 := wt_lit _ (by simp; omega)
  have w2 : (Val.list [.list [encFun ℓ, ids n], .nat u]).wt ≤
      2 * (2 * (2 * (2 * levB n + 1) + 4 + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have w3 : (Val.list [.list [.list [encFun ℓ, ids n], .nat u], .nat u']).wt ≤
      2 * (2 * (2 * (2 * (2 * (2 * levB n + 1) + 4 + levB n) + 1) + 4 + levB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have hT : rkT n = 1000 * levB n := rfl
  set E := [Val.list [.list [.list [encFun ℓ, ids n], .nat u], .nat u']] with hE
  have a0 : Lv P E (rkT n) (arg 0) (.list [.list [encFun ℓ, ids n], .nat u]) 1 :=
    Lv.arg rfl (by omega)
  have a1 : Lv P E (rkT n) (arg 1) (.nat u') 1 := Lv.arg rfl (by omega)
  have n0 : ∀ k, k ≤ 3 → Lv P E (rkT n) (.nat k) (.nat k) 1 := fun k hk => Lv.nat k (by omega)
  have c0 := Lv.get (vs := [.list [encFun ℓ, ids n], .nat u]) a0 (n0 0 (by omega)) rfl
  have cu := Lv.get (vs := [.list [encFun ℓ, ids n], .nat u]) a0 (n0 1 (by omega)) rfl
  have gL := Lv.get (vs := [encFun ℓ, ids n]) c0 (n0 0 (by omega)) rfl
  have l1 := Lv.tget gL a1
  have l2 := Lv.tget gL cu
  have e1 := Lv.arith (op := .eq) (z := if ℓ u' = ℓ u then 1 else 0) l1 l2 rfl (by split <;> omega)
  have e2 := Lv.arith (op := .lt) (z := if (u' : ℕ) < u then 1 else 0) a1 cu rfl (by split <;> omega)
  classical
  rw [boolVal_ite]
  by_cases h : ℓ u' = ℓ u
  · rw [if_pos h] at e1
    have e3 : (if ℓ u' = ℓ u ∧ u' < u then 1 else 0) = if (u' : ℕ) < u then 1 else 0 := by
      by_cases h2 : (u' : ℕ) < u
      · rw [if_pos ⟨h, h2⟩, if_pos h2]
      · rw [if_neg (fun h' => h2 h'.2), if_neg h2]
    rw [e3]
    exact Lv.mono (e := idxTestE) (Lv.ite_pos (e := .nat 0) e1 (by omega) e2) (by norm_num)
  · rw [if_neg h] at e1
    rw [if_neg (fun h' => h h'.1)]
    exact Lv.mono (e := idxTestE) (Lv.ite_zero (t := _) e1 (n0 0 (by omega))) (by norm_num)

/-- The context of `rhoN`. -/
noncomputable def rhoCtx (lX lY : Fin n → ℕ) : Val :=
  .list [encFun lX, encFun (idx lX), encFun lY, encFun (idx lY), ids n]

theorem rhoCtx_wt {lX lY : Fin n → ℕ} (hX : ∀ u, lX u ≤ n) (hY : ∀ u, lY u ≤ n) :
    (rhoCtx lX lY).wt ≤ 5 * (2 * levB n + 1) + 4 := by
  have : ∀ {f : Fin n → ℕ}, (∀ u, f u ≤ n) → (encFun f).wt ≤ levB n := fun hf => wt_table_le hf
  have wi : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  exact wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl)
    · exact this hX
    · exact this (idx_le lX)
    · exact this hY
    · exact this (idx_le lY)
    · exact wi)

set_option maxHeartbeats 1000000 in
theorem rhoTest_lv {P : Program} {lX lY : Fin n → ℕ} (hX : ∀ u, lX u ≤ n) (hY : ∀ u, lY u ≤ n)
    (u y : Fin n) :
    Lv P [.list [.list [rhoCtx lX lY, .nat u], .nat y]] (rkT n) rhoTestE
      (boolVal (@decide (lY y = lX u ∧ idx lY y = idx lX u) (Classical.propDecidable _))) 1000 := by
  have h0 := levB_pos n
  have h1 := le_levB n
  have wc := rhoCtx_wt hX hY
  have wu : (Val.nat u).wt ≤ levB n := wt_nat_levB (by omega)
  have wy : (Val.nat y).wt ≤ levB n := wt_nat_levB (by omega)
  set c := rhoCtx lX lY with hc
  have w2 : (Val.list [c, .nat u]).wt ≤ 2 * (2 * (c.wt + levB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w3 : (Val.list [.list [c, .nat u], .nat y]).wt ≤
      2 * (2 * ((Val.list [c, .nat u]).wt + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hT : rkT n = 1000 * levB n := rfl
  set E := [Val.list [.list [c, .nat u], .nat y]] with hE
  have a0 : Lv P E (rkT n) (arg 0) (.list [c, .nat u]) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (rkT n) (arg 1) (.nat y) 1 := Lv.arg rfl (by omega)
  have n0 : ∀ k, k ≤ 3 → Lv P E (rkT n) (.nat k) (.nat k) 1 := fun k hk => Lv.nat k (by omega)
  have c0 := Lv.get (vs := [c, .nat u]) a0 (n0 0 (by omega)) rfl
  have cu := Lv.get (vs := [c, .nat u]) a0 (n0 1 (by omega)) rfl
  have vs : c = .list [encFun lX, encFun (idx lX), encFun lY, encFun (idx lY), ids n] := rfl
  rw [vs] at c0
  have gX := Lv.get (vs := [encFun lX, encFun (idx lX), encFun lY, encFun (idx lY), ids n]) c0
    (n0 0 (by omega)) rfl
  have gIX := Lv.get (vs := [encFun lX, encFun (idx lX), encFun lY, encFun (idx lY), ids n]) c0
    (n0 1 (by omega)) rfl
  have gY := Lv.get (vs := [encFun lX, encFun (idx lX), encFun lY, encFun (idx lY), ids n]) c0
    (n0 2 (by omega)) rfl
  have gIY := Lv.get (vs := [encFun lX, encFun (idx lX), encFun lY, encFun (idx lY), ids n]) c0
    (n0 3 (by omega)) rfl
  have hIX := idx_le lX u
  have hIY := idx_le lY y
  have e1 := Lv.arith (op := .eq) (z := if lY y = lX u then 1 else 0) (Lv.tget gY a1)
    (Lv.tget gX cu) rfl (by split <;> omega)
  have e2 := Lv.arith (op := .eq) (z := if idx lY y = idx lX u then 1 else 0) (Lv.tget gIY a1)
    (Lv.tget gIX cu) rfl (by split <;> omega)
  classical
  rw [boolVal_ite]
  by_cases h : lY y = lX u
  · rw [if_pos h] at e1
    have e3 : (if lY y = lX u ∧ idx lY y = idx lX u then 1 else 0) =
        if idx lY y = idx lX u then 1 else 0 := by
      by_cases h2 : idx lY y = idx lX u
      · rw [if_pos ⟨h, h2⟩, if_pos h2]
      · rw [if_neg (fun h' => h2 h'.2), if_neg h2]
    rw [e3]
    exact Lv.mono (e := rhoTestE) (Lv.ite_pos (e := .nat 0) e1 (by omega) e2) (by norm_num)
  · rw [if_neg h] at e1
    rw [if_neg (fun h' => h h'.1)]
    exact Lv.mono (e := rhoTestE) (Lv.ite_zero (t := _) e1 (n0 0 (by omega))) (by norm_num)

theorem chkTest_lv {P : Program} {f : Fin n → ℕ} (hf : ∀ u, f u ≤ n) (u : Fin n) :
    Lv P [.list [.list [encFun f, .nat n], .nat u]] (rkT n) chkTestE
      (boolVal (@decide (f u = n) (Classical.propDecidable _))) 100 := by
  have h0 := levB_pos n
  have h1 := le_levB n
  have wf : (encFun f).wt ≤ levB n := wt_table_le hf
  have wu : (Val.nat u).wt ≤ levB n := wt_nat_levB (by omega)
  have wn : (Val.nat n).wt ≤ levB n := wt_nat_levB (by omega)
  have w2 : (Val.list [encFun f, .nat n]).wt ≤ 2 * (2 * levB n + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w3 : (Val.list [.list [encFun f, .nat n], .nat u]).wt ≤
      2 * (2 * ((Val.list [encFun f, .nat n]).wt + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hT : rkT n = 1000 * levB n := rfl
  set E := [Val.list [.list [encFun f, .nat n], .nat u]] with hE
  have a0 : Lv P E (rkT n) (arg 0) (.list [encFun f, .nat n]) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (rkT n) (arg 1) (.nat u) 1 := Lv.arg rfl (by omega)
  have gf := Lv.get (vs := [encFun f, .nat n]) a0 (Lv.nat 0 (by omega)) rfl
  have gn := Lv.get (vs := [encFun f, .nat n]) a0 (Lv.nat 1 (by omega)) rfl
  have hfu := hf u
  have e1 := Lv.arith (op := .eq) (z := if f u = n then 1 else 0) (Lv.tget gf a1) gn rfl
    (by split <;> omega)
  classical
  rw [boolVal_ite]
  exact Lv.mono (e := chkTestE) e1 (by norm_num)

/-- The cost of a search. -/
def srchC (n : ℕ) : ℕ := n * (1000 * rkT n) + loopModK * (n + 1) * rkT n

/-- The budget of an entry of a table of searches. -/
def rkT1 (n : ℕ) : ℕ := srchC n + rkT n

/-- The cost of a table of searches. -/
def rkTabC (n : ℕ) : ℕ := n * (1000 * rkT1 n) + mapK * (n + 1) * rkT n

/-- The budget of the main function. -/
def rkT2 (n : ℕ) : ℕ := 2 * rkTabC n + srchC n + rkT n

/-- The bound of `rank`. -/
def rankC (n : ℕ) : ℕ := 100000 * rkT2 n

theorem rankC_poly : PolyB rankC := by
  unfold rankC rkT2 rkTabC rkT1 srchC rkT levB
  poly

theorem flist_levB (l : List (Fin n)) (hl : l.length ≤ n) : (flist l).wt ≤ levB n := by
  have h1 := wt_natList_le_sq (xs := l.map fun z : Fin n => (z : ℕ)) (B := n)
    (by simp only [List.mem_map]; rintro _ ⟨z, -, rfl⟩; exact z.isLt.le) (by simpa using hl)
  have e : flist l = natList (l.map fun z : Fin n => (z : ℕ)) := by
    simp [flist, natList]
  rw [e]
  simp only [levB]
  omega

/-- **The table `idx`.** -/
theorem idx_spec {P : Program} {b : ℕ} (hT : P.HasAt b (tabFuns b (srchEntryE (b + 4) 1 true)))
    (hF : P.HasAt (b + 4) (filterFuns (b + 4) (b + 7))) (hP : P.funs[b + 7]? = some idxTestE)
    {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) :
    FunDet P b (.list [.list [encFun ℓ, ids n], ids n]) (encFun (idx ℓ)) (rkTabC n) := by
  classical
  have h0 := levB_pos n
  have h1 := le_levB n
  have wL : (encFun ℓ).wt ≤ levB n := wt_table_le hℓ
  have wi : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have wI : (encFun (idx ℓ)).wt ≤ levB n := wt_table_le (idx_le ℓ)
  have w1 : (Val.list [encFun ℓ, ids n]).wt ≤ 2 * (2 * levB n + 1) + 4 := wt_lit _ (by simp; omega)
  have w2 : (Val.list [.list [encFun ℓ, ids n], ids n]).wt ≤
      2 * (2 * (2 * (2 * levB n + 1) + 4 + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hTv : rkT n = 1000 * levB n := rfl
  have hT1 : rkT n ≤ rkT1 n := by simp only [rkT1]; omega
  refine (tabN_spec (T := rkT1 n) (K := 1000) (W := rkT n) hT (fun u => ?_) (by omega)).mono
    (by simp only [rkTabC]; omega)
  have wu : (Val.nat u).wt ≤ levB n := wt_nat_levB (by omega)
  have w3 : (Val.list [.list [encFun ℓ, ids n], .nat u]).wt ≤
      2 * (2 * (2 * (2 * levB n + 1) + 4 + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have w4 : (Val.list [.list [.list [encFun ℓ, ids n], .nat u], ids n]).wt ≤
      2 * (2 * (2 * (2 * (2 * (2 * levB n + 1) + 4 + levB n) + 1) + 4 + levB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  set q : Fin n → Prop := fun u' => ℓ u' = ℓ u ∧ u' < u with hq
  have hfl : (flist ((List.finRange n).filter fun z : Fin n =>
      @decide (q z) (Classical.propDecidable _))).wt ≤ levB n :=
    flist_levB _ (by
      have := List.length_filter_le (fun z : Fin n => @decide (q z) (Classical.propDecidable _))
        (List.finRange n)
      simpa using this)
  have hfi := filterFin_spec (c := .list [.list [encFun ℓ, ids n], .nat u]) (W := rkT n) hF q
    (B := 1000 * rkT n) (fun u' => funDet_of_lv hP (idxTest_lv hℓ u u')) (by omega)
  have hlen : ((List.finRange n).filter fun z : Fin n =>
      @decide (q z) (Classical.propDecidable _)).length = idx ℓ u := by
    unfold idx
    congr 1
    apply List.filter_congr
    intro z _
    exact decide_eq_decide.2 Iff.rfl
  set E := [Val.list [.list [encFun ℓ, ids n], .nat u]] with hE
  have a0 : Lv P E (rkT1 n) (arg 0) (.list [encFun ℓ, ids n]) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (rkT1 n) (arg 1) (.nat u) 1 := Lv.arg rfl (by omega)
  have gi := Lv.get (vs := [encFun ℓ, ids n]) a0 (Lv.nat 1 (by omega)) rfl
  have hc := Lv.call (Lv.mk2 (Lv.mk2 a0 a1 (by omega)) gi (by omega)) hfi
    (by simp only [rkT1, srchC]; omega)
  have hl := Lv.flen hc (by omega)
  rw [hlen] at hl
  exact Lv.mono (e := srchEntryE (b + 4) 1 true) hl (by norm_num)

/-- **The table `rhoN`.** -/
theorem rho_spec {P : Program} {b : ℕ} (hT : P.HasAt b (tabFuns b (srchEntryE (b + 4) 4 false)))
    (hF : P.HasAt (b + 4) (findFuns (b + 4) (b + 7))) (hP : P.funs[b + 7]? = some rhoTestE)
    {lX lY : Fin n → ℕ} (hX : ∀ u, lX u ≤ n)
    (hY : ∀ u, lY u ≤ n) :
    FunDet P b (.list [rhoCtx lX lY, ids n]) (encFun (rhoN lX lY)) (rkTabC n) := by
  classical
  have h0 := levB_pos n
  have h1 := le_levB n
  have wc := rhoCtx_wt hX hY
  have wi : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have wI : (encFun (rhoN lX lY)).wt ≤ levB n := wt_table_le (rhoN_le lX lY)
  set c := rhoCtx lX lY with hc
  have w2 : (Val.list [c, ids n]).wt ≤ 2 * (2 * (c.wt + levB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have hTv : rkT n = 1000 * levB n := rfl
  have hT1 : rkT n ≤ rkT1 n := by simp only [rkT1]; omega
  refine (tabN_spec (T := rkT1 n) (K := 1000) (W := rkT n) hT (fun u => ?_) (by omega)).mono
    (by simp only [rkTabC]; omega)
  have wu : (Val.nat u).wt ≤ levB n := wt_nat_levB (by omega)
  have w3 : (Val.list [c, .nat u]).wt ≤ 2 * (2 * (c.wt + levB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w4 : (Val.list [.list [c, .nat u], ids n]).wt ≤
      2 * (2 * ((Val.list [c, .nat u]).wt + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hfi := findFin_spec (c := .list [c, .nat u]) hF
    (fun y => lY y = lX u ∧ idx lY y = idx lX u)
    (B := 1000 * rkT n) (fun y => funDet_of_lv hP (rhoTest_lv hX hY u y))
  have hv : ((List.finRange n).findIdx fun y : Fin n =>
      @decide (lY y = lX u ∧ idx lY y = idx lX u) (Classical.propDecidable _)) = rhoN lX lY u := by
    unfold rhoN
    congr 1
    funext z
    exact decide_eq_decide.2 Iff.rfl
  rw [hv] at hfi
  set E := [Val.list [c, .nat u]] with hE
  have a0 : Lv P E (rkT1 n) (arg 0) c 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (rkT1 n) (arg 1) (.nat u) 1 := Lv.arg rfl (by omega)
  have a0' : Lv P E (rkT1 n) (arg 0)
      (.list [encFun lX, encFun (idx lX), encFun lY, encFun (idx lY), ids n]) 1 := a0
  have gi := Lv.get (vs := [encFun lX, encFun (idx lX), encFun lY, encFun (idx lY), ids n])
    a0' (Lv.nat 4 (by omega)) rfl
  have e2 : loopModK * (n + 1) * ((Val.list [Val.list [c, .nat u], ids n]).wt + 2 * n + 3) ≤
      loopModK * (n + 1) * rkT n := Nat.mul_le_mul_left _ (by omega)
  have hcl := Lv.call (Lv.mk2 (Lv.mk2 a0 a1 (by omega)) gi (by omega)) hfi
    (by simp only [rkT1, srchC]; omega)
  exact Lv.mono (e := srchEntryE (b + 4) 4 false) hcl (by norm_num)

set_option maxHeartbeats 2000000 in
/-- **Matching the levels.** -/
theorem rank_spec {P : Program} {b : ℕ} (h : P.HasAt b (rankFuns b)) {lX lY : Fin n → ℕ}
    (hX : ∀ u, lX u ≤ n) (hY : ∀ u, lY u ≤ n) :
    FunDet P b (.list [encFun lX, encFun lY, ids n, .nat n])
      (.list [encFun (rhoN lX lY),
        .nat (if ∃ u, rhoN lX lY u = n then 1 else 0)]) (rankC n) := by
  classical
  have hM : P.funs[b]? = some (rankMainE b) := h.left.left.left.left.left.left.left.left.single
  have h1 : P.HasAt (b + 1) (tabFuns (b + 1) (srchEntryE (b + 5) 1 true)) :=
    h.left.left.left.left.left.left.left.right
  have h2 : P.HasAt (b + 5) (filterFuns (b + 5) (b + 8)) := h.left.left.left.left.left.left.right
  have h3 : P.funs[b + 8]? = some idxTestE := h.left.left.left.left.left.right.single
  have h4 : P.HasAt (b + 9) (tabFuns (b + 9) (srchEntryE (b + 13) 4 false)) :=
    h.left.left.left.left.right
  have h5 : P.HasAt (b + 13) (findFuns (b + 13) (b + 16)) := h.left.left.left.right
  have h6 : P.funs[b + 16]? = some rhoTestE := h.left.left.right.single
  have h7 : P.HasAt (b + 17) (anyFuns (b + 17) (b + 20)) := h.left.right
  have h8 : P.funs[b + 20]? = some chkTestE := h.right.single
  have h0 := levB_pos n
  have hl := le_levB n
  have wX : (encFun lX).wt ≤ levB n := wt_table_le hX
  have wY : (encFun lY).wt ≤ levB n := wt_table_le hY
  have wIX : (encFun (idx lX)).wt ≤ levB n := wt_table_le (idx_le lX)
  have wIY : (encFun (idx lY)).wt ≤ levB n := wt_table_le (idx_le lY)
  have wR : (encFun (rhoN lX lY)).wt ≤ levB n := wt_table_le (rhoN_le lX lY)
  have wi : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have wn : (Val.nat n).wt ≤ levB n := wt_nat_levB (by omega)
  have wc := rhoCtx_wt hX hY
  have wA : (Val.list [encFun lX, encFun lY, ids n, .nat n]).wt ≤ 4 * (2 * levB n + 1) + 4 :=
    wt_lit _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl | rfl | rfl | rfl) <;> omega)
  have hTv : rkT n = 1000 * levB n := rfl
  have hT2 : rkT n + rkTabC n + srchC n ≤ rkT2 n := by simp only [rkT2]; omega
  set A := Val.list [encFun lX, encFun lY, ids n, .nat n] with hA
  set T := rkT2 n with hT
  have ga : ∀ rest {j : ℕ} {v : Val}, [encFun lX, encFun lY, ids n, .nat n][j]? = some v → j ≤ 3 →
      Lv P (A :: rest) T (arg j) v 1 := fun rest j v hv hj =>
    Lv.arg hv (by change 2 * A.wt + j + 5 ≤ T; omega)
  have cIX := Lv.call (Lv.mk2 (Lv.mk2 (ga [] (j := 0) rfl (by omega)) (ga [] (j := 2) rfl (by omega))
    (by omega)) (ga [] (j := 2) rfl (by omega)) (by omega)) (idx_spec h1 h2 h3 hX) (by omega)
  have cIY := Lv.call (Lv.mk2 (Lv.mk2 (ga [encFun (idx lX)] (j := 1) rfl (by omega))
    (ga _ (j := 2) rfl (by omega)) (by omega)) (ga _ (j := 2) rfl (by omega)) (by omega))
    (idx_spec h1 h2 h3 hY) (by omega)
  have cR := Lv.call (Lv.mk2 (Lv.mk5 (ga [encFun (idx lX), encFun (idx lY)] (j := 0) rfl (by omega))
    (Lv.var (env := [A, encFun (idx lX), encFun (idx lY)]) (i := 1) rfl (by omega))
    (ga _ (j := 1) rfl (by omega))
    (Lv.var (env := [A, encFun (idx lX), encFun (idx lY)]) (i := 2) rfl (by omega))
    (ga _ (j := 2) rfl (by omega)) (by omega)) (ga _ (j := 2) rfl (by omega)) (by omega))
    (rho_spec h4 h5 h6 hX hY) (by omega)
  set E := [A, encFun (idx lX), encFun (idx lY), encFun (rhoN lX lY)] with hE
  have v3 : Lv P E T (.var 3) (encFun (rhoN lX lY)) 1 := Lv.var rfl (by omega)
  have w2 : (Val.list [encFun (rhoN lX lY), .nat n]).wt ≤ 2 * (2 * levB n + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w3 : (Val.list [.list [encFun (rhoN lX lY), .nat n], ids n]).wt ≤
      2 * (2 * (2 * (2 * levB n + 1) + 4 + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hany := anyFin_spec (c := .list [encFun (rhoN lX lY), .nat n]) h7
    (fun u => rhoN lX lY u = n) (B := 100 * rkT n)
    (fun u => funDet_of_lv h8 (chkTest_lv (rhoN_le lX lY) u))
  have e2 : loopModK * (n + 1) * ((Val.list [.list [encFun (rhoN lX lY), .nat n], ids n]).wt + n + 4)
      ≤ loopModK * (n + 1) * rkT n := Nat.mul_le_mul_left _ (by omega)
  have e1 : n * (100 * rkT n) ≤ n * (1000 * rkT n) := Nat.mul_le_mul_left _ (by omega)
  have cK := Lv.call (Lv.mk2 (Lv.mk2 v3 (ga _ (j := 3) rfl (by omega)) (by omega))
    (ga _ (j := 2) rfl (by omega)) (by omega)) hany (by simp only [hT, rkT2, srchC]; omega)
  have o := Lv.mk2 v3 cK (by omega)
  have l3 := Lv.letE cR o
  have l2 := Lv.letE cIY l3
  have l1 := Lv.letE cIX l2
  have fin := funDet_of_lv hM (T := T) (m := 100000) (Lv.mono (e := rankMainE b) l1 (by norm_num))
  have e : (if ∃ u, rhoN lX lY u = n then 1 else 0) =
      @ite ℕ (∃ z, rhoN lX lY z = n) (@Nat.decidableExistsFin n (fun u => rhoN lX lY u = n)
        fun a => Classical.propDecidable (rhoN lX lY a = n)) 1 0 := by
    congr
  rw [e]
  exact fin

end GI.Degree
