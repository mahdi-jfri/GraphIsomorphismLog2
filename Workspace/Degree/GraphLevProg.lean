module

public import Workspace.Degree.GraphTab
public import Workspace.Degree.GraphLev

/-!
# The program for the distance levels

`levFuns b`: on `[adjVal X, n, ids n, v]`, the table of `lev X v`. Each round of the loop gives the
next layer. Its spec is `lev_spec`.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

open Classical in
/-- The levels after `r` rounds. -/
noncomputable def levAt (X : SimpleGraph (Fin n)) (v : Fin n) (r : ℕ) (u : Fin n) : ℕ :=
  if lev X v u ≤ r then lev X v u else n

theorem levAt_le (X : SimpleGraph (Fin n)) (v : Fin n) (r : ℕ) (u : Fin n) : levAt X v r u ≤ n := by
  unfold levAt
  have := lev_le X v u
  split <;> omega

theorem levAt_zero (X : SimpleGraph (Fin n)) (v u : Fin n) :
    levAt X v 0 u = if u = v then 0 else n := by
  have hr := (lev_hasLevels X v).root
  have h0 : lev X v v = 0 := by
    rw [lev_of_reach (SimpleGraph.Reachable.refl _)]; simp
  have h1 : lev X v u = 0 ↔ u = v := by
    constructor
    · intro h
      obtain ⟨o, ho⟩ := hr
      rw [(ho u).1 h, (ho v).1 h0]
    · rintro rfl; exact h0
  by_cases h : u = v
  · simp [levAt, h, h0]
  · have : ¬lev X v u ≤ 0 := fun h2 => h (h1.1 (by omega))
    simp [levAt, h, this]

open Classical in
/-- One round of the loop. -/
theorem levAt_succ (X : SimpleGraph (Fin n)) (v u : Fin n) {r : ℕ} (hr : r < n) :
    levAt X v (r + 1) u = if levAt X v r u < n then levAt X v r u else
      if ∃ z, levAt X v r z = r ∧ X.Adj z u then r + 1 else n := by
  have hL := lev_hasLevels X v
  have hlt : ∀ z, levAt X v r z < n ↔ lev X v z ≤ r := fun z => by
    unfold levAt
    split
    · rename_i h
      simp only [h, iff_true]
      omega
    · rename_i h
      simp [h]
  have heq : ∀ z, levAt X v r z = r ↔ lev X v z = r := fun z => by
    unfold levAt
    split
    · rfl
    · rename_i h
      constructor <;> omega
  by_cases h1 : lev X v u ≤ r
  · rw [if_pos ((hlt u).2 h1)]
    simp [levAt, h1, show lev X v u ≤ r + 1 by omega]
  rw [if_neg (fun h => h1 ((hlt u).1 h))]
  by_cases h2 : ∃ z, levAt X v r z = r ∧ X.Adj z u
  · rw [if_pos h2]
    obtain ⟨z, hz, ha⟩ := h2
    have h3 := (heq z).1 hz
    have h4 := hL.step z u ha (by omega)
    have h5 : lev X v u = r + 1 := by omega
    simp [levAt, h5]
  · rw [if_neg h2]
    unfold levAt
    split
    · rename_i h3
      have h5 : lev X v u = r + 1 := by omega
      by_cases h6 : r + 1 ≤ n - 1
      · obtain ⟨z, hz, he⟩ := hL.back u (by omega) (by omega)
        exact (h2 ⟨z, (heq z).2 (by omega), hz⟩).elim
      · have h7 := lev_le X v u
        have h8 : r + 1 = n := by omega
        have h9 : ¬ X.Reachable v u := fun h => by
          have := lev_lt_iff.2 h
          omega
        rw [h5, h8]
    · rfl

theorem levAt_top (X : SimpleGraph (Fin n)) (v : Fin n) : levAt X v n = lev X v := by
  funext u
  simp [levAt, lev_le]

/-- `A[z][u]`. -/
def adjE (a z u : Expr) : Expr := .get (.get a z) u

/-- The test of a round, on `[[[A, n, ids, r, t], u], z]`: `t z = r` and `A z u`. -/
def levTestE : Expr :=
  let ctx := Expr.get (arg 0) (.nat 0)
  .arith .mul (.arith .eq (.get (.get ctx (.nat 4)) (arg 1)) (.get ctx (.nat 3)))
    (adjE (.get ctx (.nat 0)) (arg 1) (.get (arg 0) (.nat 1)))

/-- An entry of a round, on `[[A, n, ids, r, t], u]`. -/
def levEntryE (anyB : ℕ) : Expr :=
  let ctx := arg 0
  .ite (.arith .lt (.get (.get ctx (.nat 4)) (arg 1)) (.get ctx (.nat 1)))
    (.get (.get ctx (.nat 4)) (arg 1))
    (.ite (.call anyB (mk2 (mk2 ctx (arg 1)) (.get ctx (.nat 2))))
      (.arith .add (.get ctx (.nat 3)) (.nat 1)) (.get ctx (.nat 1)))

/-- A round, on `[[A, n, ids], r, t]`. -/
def levStepE (tabB : ℕ) : Expr :=
  let c := arg 0
  .call tabB (mk2 (mk5 (.get c (.nat 0)) (.get c (.nat 1)) (.get c (.nat 2)) (arg 1) (arg 2))
    (.get c (.nat 2)))

/-- The table of the start, on `[[n, v], u]`. -/
def levInitE : Expr :=
  .ite (.arith .eq (arg 1) (.get (arg 0) (.nat 1))) (.nat 0) (.get (arg 0) (.nat 0))

/-- The entry of the level function, on `[A, n, ids, v]`. Called at `b`. -/
def levMainE (b : ℕ) : Expr :=
  .call (b + 1) (mk3 (mk3 (arg 0) (arg 1) (arg 2)) (arg 1)
    (.call (b + 5) (mk2 (mk2 (arg 1) (arg 3)) (arg 2))))

/-- The functions of the level program, at base `b`: entry, the iteration, the step, the start
table, the table of a round, the search of a round and its test. 17 functions. -/
def levFuns (b : ℕ) : List Expr :=
  [levMainE b] ++ iterFuns (b + 1) (b + 4) ++ [levStepE (b + 9)] ++ tabFuns (b + 5) levInitE ++
    tabFuns (b + 9) (levEntryE (b + 13)) ++ anyFuns (b + 13) (b + 16) ++ [levTestE]

/-- A bound on the weights of the program. -/
def levB (n : ℕ) : ℕ := 100 * (n + 1) ^ 2

theorem wt_adjVal_le (X : SimpleGraph (Fin n)) : (adjVal X).wt ≤ levB n := by
  classical
  have h1 : ∀ i : Fin n, (encFun fun j : Fin n => if X.Adj i j then 1 else 0).wt ≤ 7 * n + 4 := by
    intro i
    have := wt_encFun_le (fun j : Fin n => if X.Adj i j then 1 else 0) (B := 1) (by
      intro j
      split <;> omega)
    omega
  have h2 := wt_listFin_le (fun i : Fin n => encFun fun j : Fin n => if X.Adj i j then 1 else 0) h1
  have h3 : (adjVal X).wt = _ := rfl
  rw [h3]
  refine h2.trans ?_
  simp only [levB]
  nlinarith

theorem wt_table_le {f : Fin n → ℕ} (hf : ∀ i, f i ≤ n) : (encFun f).wt ≤ levB n := by
  have := wt_encFun_le_sq f hf
  simp only [levB]
  omega

theorem wt_nat_levB {k : ℕ} (hk : k ≤ n + 1) : (Val.nat k).wt ≤ levB n := by
  have := wt_nat_le k
  simp only [levB]
  nlinarith

/-- The budget of the test. -/
def levT (n : ℕ) : ℕ := 1000 * levB n

theorem levB_pos (n : ℕ) : 100 ≤ levB n := by
  have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [levB]
  omega

theorem le_levB (n : ℕ) : n + 1 ≤ levB n := by
  simp only [levB]
  nlinarith

open Classical in
theorem levTest_lv {P : Program} (X : SimpleGraph (Fin n)) (v : Fin n) {r : ℕ} (hr : r ≤ n)
    (u z : Fin n) :
    Lv P [.list [.list [.list [adjVal X, .nat n, ids n, .nat r, encFun (levAt X v r)], .nat u],
      .nat z]] (levT n) levTestE
      (boolVal (@decide (levAt X v r z = r ∧ X.Adj z u) (Classical.propDecidable _))) 300 := by
  set t := encFun (levAt X v r) with ht
  set ctx : Val := .list [adjVal X, .nat n, ids n, .nat r, t] with hctx
  set e : List Val := [.list [ctx, .nat u], .nat z] with he
  have hB := levB_pos n
  have hB' := le_levB n
  have w1 : (adjVal X).wt ≤ levB n := wt_adjVal_le X
  have w2 : (Val.nat n).wt ≤ levB n := wt_nat_levB (by omega)
  have w3 : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have w4 : (Val.nat r).wt ≤ levB n := wt_nat_levB (by omega)
  have w5 : t.wt ≤ levB n := wt_table_le (levAt_le X v r)
  have w6 : ctx.wt ≤ 5 * (2 * levB n + 1) + 4 :=
    wt_lit [adjVal X, .nat n, ids n, .nat r, t] (by simp [w1, w2, w3, w4, w5])
  have w7 := wt_nat_levB (n := n) (show (u : ℕ) ≤ n + 1 by have := u.isLt; omega)
  have w8 := wt_nat_levB (n := n) (show (z : ℕ) ≤ n + 1 by have := z.isLt; omega)
  have w9 : (Val.list [ctx, .nat (u : ℕ)]).wt ≤ 2 * (2 * (ctx.wt + levB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w10 : (Val.list e).wt ≤ 2 * (2 * ((Val.list [ctx, .nat (u : ℕ)]).wt + levB n) + 1) + 4 :=
    wt_lit e (by simp [he]; omega)
  have hT : 2 * (Val.list e).wt + 10 ≤ levT n := by
    have : levT n = 1000 * levB n := rfl
    omega
  have a0 : Lv P [.list e] (levT n) (arg 0) (.list [ctx, .nat u]) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P [.list e] (levT n) (arg 1) (.nat z) 1 := Lv.arg rfl (by omega)
  have n0 : ∀ k, k ≤ 4 → Lv P [.list e] (levT n) (.nat k) (.nat k) 1 := fun k hk =>
    Lv.nat k (by omega)
  have c0 := Lv.get a0 (n0 0 (by omega)) (show [ctx, Val.nat u][0]? = some ctx from rfl)
  have c1 := Lv.get a0 (n0 1 (by omega)) (show [ctx, Val.nat u][1]? = some (.nat u) from rfl)
  have g4 := Lv.get (vs := [adjVal X, .nat n, ids n, .nat r, t]) c0 (n0 4 (by omega)) rfl
  have g3 := Lv.get (vs := [adjVal X, .nat n, ids n, .nat r, t]) c0 (n0 3 (by omega)) rfl
  have g0 := Lv.get (vs := [adjVal X, .nat n, ids n, .nat r, t]) c0 (n0 0 (by omega)) rfl
  have tz := Lv.get (vs := (List.finRange n).map fun i => .nat (levAt X v r i)) g4 a1
    (listFin_get _ z)
  have hT4 : 4 ≤ levT n := by omega
  have hq := Lv.arith (op := .eq) tz g3 rfl (by simp only [BinOp.eval]; split <;> omega)
  have r1 := Lv.get (vs := (List.finRange n).map fun i : Fin n =>
    encFun fun j : Fin n => if X.Adj i j then 1 else 0) g0 a1 (listFin_get _ z)
  have r2 := Lv.get (vs := (List.finRange n).map fun j : Fin n =>
    .nat (if X.Adj z j then 1 else 0)) r1 c1 (listFin_get _ u)
  have hm := Lv.arith (op := .mul) (z := (@decide (levAt X v r z = r ∧ X.Adj z u) (Classical.propDecidable _)).toNat) hq r2 (by
    simp only [BinOp.eval]
    by_cases h1 : levAt X v r z = r <;> by_cases h2 : X.Adj z u <;> simp [h1, h2])
    (by have := Bool.toNat_le (@decide (levAt X v r z = r ∧ X.Adj z u) (Classical.propDecidable _)); omega)
  exact Lv.mono (e := levTestE) hm (by norm_num)

/-- The bound of a search of a round. -/
def levAnyC (n : ℕ) : ℕ := n * (300 * levT n) + loopModK * (n + 1) * (levT n + n + 4)

/-- The budget of an entry of a round. -/
def levT2 (n : ℕ) : ℕ := levAnyC n + levT n

/-- The bound of a round. -/
def levTabC (n : ℕ) : ℕ := n * (1000 * levT2 n) + mapK * (n + 1) * levT n

/-- The budget of the step. -/
def levT3 (n : ℕ) : ℕ := levTabC n + levT n

theorem levT_ge (n : ℕ) : levB n ≤ levT n := by
  simp only [levT]; omega

theorem levT_le_T2 (n : ℕ) : levT n ≤ levT2 n := by
  simp only [levT2]; omega

theorem levT_le_T3 (n : ℕ) : levT n ≤ levT3 n := by
  simp only [levT3]; omega

theorem levTabC_le_T3 (n : ℕ) : levTabC n ≤ levT3 n := by
  simp only [levT3]; omega

theorem wt_ctx_le (X : SimpleGraph (Fin n)) {t : Fin n → ℕ} (ht : ∀ u, t u ≤ n) {r : ℕ}
    (hr : r ≤ n) : (Val.list [adjVal X, .nat n, ids n, .nat r, encFun t]).wt ≤ 11 * levB n + 9 := by
  have hB := levB_pos n
  have hB' := le_levB n
  have w1 : (adjVal X).wt ≤ levB n := wt_adjVal_le X
  have w2 : (Val.nat n).wt ≤ levB n := wt_nat_levB (by omega)
  have w3 : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have w4 : (Val.nat r).wt ≤ levB n := wt_nat_levB (by omega)
  have w5 : (encFun t).wt ≤ levB n := wt_table_le ht
  have w6 : (Val.list [adjVal X, .nat n, ids n, .nat r, encFun t]).wt ≤ 5 * (2 * levB n + 1) + 4 :=
    wt_lit _ (by simp [w1, w2, w3, w4, w5])
  omega

open Classical in
/-- An entry of a round. -/
theorem levEntry_lv {P : Program} {a : ℕ} (hP : P.HasAt a (anyFuns a (a + 3)))
    (ht : P.funs[a + 3]? = some levTestE) (X : SimpleGraph (Fin n)) (v : Fin n) {r : ℕ} (hr : r < n)
    (u : Fin n) :
    Lv P [.list [.list [adjVal X, .nat n, ids n, .nat r, encFun (levAt X v r)], .nat u]] (levT2 n)
      (levEntryE a) (.nat (levAt X v (r + 1) u)) 800 := by
  set t := encFun (levAt X v r) with ht'
  set ctx : Val := .list [adjVal X, .nat n, ids n, .nat r, t] with hctx
  have hB := levB_pos n
  have hB' := le_levB n
  have hT0 := levT_ge n
  have hT2 := levT_le_T2 n
  have hTv : levT n = 1000 * levB n := rfl
  have w6 : ctx.wt ≤ 11 * levB n + 9 := wt_ctx_le X (levAt_le X v r) hr.le
  have w7 := wt_nat_levB (n := n) (show (u : ℕ) ≤ n + 1 by have := u.isLt; omega)
  have w8 : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have w9 : (Val.list [ctx, .nat (u : ℕ)]).wt ≤ 2 * (2 * (ctx.wt + levB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w10 : (Val.list [Val.list [ctx, .nat (u : ℕ)], ids n]).wt ≤
      2 * (2 * ((Val.list [ctx, .nat (u : ℕ)]).wt + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  set E := [Val.list [ctx, .nat (u : ℕ)]] with hE
  have hT : 2 * (Val.list [ctx, .nat (u : ℕ)]).wt + 10 ≤ levT2 n := by omega
  have a0 : Lv P E (levT2 n) (arg 0) ctx 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (levT2 n) (arg 1) (.nat u) 1 := Lv.arg rfl (by omega)
  have n0 : ∀ k, k ≤ 4 → Lv P E (levT2 n) (.nat k) (.nat k) 1 := fun k hk => Lv.nat k (by omega)
  have g1 := Lv.get (vs := [adjVal X, .nat n, ids n, .nat r, t]) a0 (n0 1 (by omega)) rfl
  have g2 := Lv.get (vs := [adjVal X, .nat n, ids n, .nat r, t]) a0 (n0 2 (by omega)) rfl
  have g3 := Lv.get (vs := [adjVal X, .nat n, ids n, .nat r, t]) a0 (n0 3 (by omega)) rfl
  have g4 := Lv.get (vs := [adjVal X, .nat n, ids n, .nat r, t]) a0 (n0 4 (by omega)) rfl
  have tu := Lv.get (vs := (List.finRange n).map fun i => .nat (levAt X v r i)) g4 a1
    (listFin_get _ u)
  have hcall := Lv.call (P := P) (T := levT2 n) (Lv.mk2 (Lv.mk2 a0 a1 (by omega)) g2 (by omega))
    (anyFin_spec (c := .list [ctx, .nat (u : ℕ)]) hP (fun z : Fin n => levAt X v r z = r ∧ X.Adj z u)
      (B := 300 * levT n) fun z => funDet_of_lv ht (levTest_lv X v hr.le u z))
    (by
      simp only [levT2, levAnyC]
      have : loopModK * (n + 1) * ((Val.list [Val.list [ctx, .nat (u : ℕ)], ids n]).wt + n + 4) ≤
          loopModK * (n + 1) * (levT n + n + 4) :=
        Nat.mul_le_mul_left _ (by omega)
      omega)
  have hsucc := levAt_succ X v u hr
  beta_reduce at hcall
  by_cases h1 : levAt X v r u < n
  · rw [if_pos h1] at hsucc
    rw [hsucc]
    have hlt := Lv.arith (op := .lt) (z := 1) tu g1 (by simp [BinOp.eval, h1]) (by omega)
    have := Lv.ite_pos (e := .ite (.call a (mk2 (mk2 (arg 0) (arg 1)) (.get (arg 0) (.nat 2))))
      (.arith .add (.get (arg 0) (.nat 3)) (.nat 1)) (.get (arg 0) (.nat 1))) hlt (by omega) tu
    exact Lv.mono (e := levEntryE a) this (by norm_num)
  · rw [if_neg h1] at hsucc
    have hlt := Lv.arith (op := .lt) (z := 0) tu g1 (by simp [BinOp.eval, h1]) (by omega)
    by_cases h2 : ∃ z, levAt X v r z = r ∧ X.Adj z u
    · rw [if_pos h2] at hsucc
      rw [hsucc]
      rw [if_pos h2] at hcall
      have hadd := Lv.arith (op := .add) (z := r + 1) g3 (n0 1 (by omega)) rfl (by omega)
      have h3 := Lv.ite_pos (e := .get (arg 0) (.nat 1)) hcall (by omega) hadd
      exact Lv.mono (e := levEntryE a) (Lv.ite_zero hlt h3) (by norm_num)
    · rw [if_neg h2] at hsucc
      rw [hsucc]
      rw [if_neg h2] at hcall
      have h3 := Lv.ite_zero (t := .arith .add (.get (arg 0) (.nat 3)) (.nat 1)) hcall g1
      exact Lv.mono (e := levEntryE a) (Lv.ite_zero hlt h3) (by norm_num)

/-- A round as a table. -/
theorem levRound_fun {P : Program} {a : ℕ} (h : P.HasAt a (tabFuns a (levEntryE (a + 4))))
    (hA : P.HasAt (a + 4) (anyFuns (a + 4) (a + 7))) (ht : P.funs[a + 7]? = some levTestE)
    (X : SimpleGraph (Fin n)) (v : Fin n) {r : ℕ} (hr : r < n) :
    FunDet P a (.list [.list [adjVal X, .nat n, ids n, .nat r, encFun (levAt X v r)], ids n])
      (encFun (levAt X v (r + 1))) (levTabC n) := by
  have hB := levB_pos n
  have w6 := wt_ctx_le X (levAt_le X v r) hr.le
  have w8 : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have w9 := wt_table_le (levAt_le X v (r + 1))
  have w10 : (Val.list [Val.list [adjVal X, .nat n, ids n, .nat r, encFun (levAt X v r)], ids n]).wt
      ≤ 2 * (2 * (11 * levB n + 9 + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hTv : levT n = 1000 * levB n := rfl
  exact (tabN_spec (W := levT n) h (fun u => levEntry_lv hA ht X v hr u) (by omega)).mono (by
    simp only [levTabC]
    have := Nat.mul_le_mul_left n (Nat.mul_le_mul_right (levT2 n) (show 800 ≤ 1000 by omega))
    omega)

/-- A step of the iteration. -/
theorem levStep_fun {P : Program} {a c : ℕ} (hc : P.funs[c]? = some (levStepE a))
    (h : P.HasAt a (tabFuns a (levEntryE (a + 4))))
    (hA : P.HasAt (a + 4) (anyFuns (a + 4) (a + 7))) (ht : P.funs[a + 7]? = some levTestE)
    (X : SimpleGraph (Fin n)) (v : Fin n) {r : ℕ} (hr : r < n) :
    FunDet P c (.list [.list [adjVal X, .nat n, ids n], .nat r, encFun (levAt X v r)])
      (encFun (levAt X v (r + 1))) (3000 * levT3 n) := by
  have hB := levB_pos n
  have hB' := le_levB n
  have hT1 := levT_le_T3 n
  have hTv : levT n = 1000 * levB n := rfl
  have w1 : (adjVal X).wt ≤ levB n := wt_adjVal_le X
  have w2 : (Val.nat n).wt ≤ levB n := wt_nat_levB (by omega)
  have w3 : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have w4 : (Val.nat r).wt ≤ levB n := wt_nat_levB (by omega)
  have w5 := wt_table_le (levAt_le X v r)
  set t := encFun (levAt X v r) with htd
  have w6 : (Val.list [adjVal X, .nat n, ids n]).wt ≤ 3 * (2 * levB n + 1) + 4 :=
    wt_lit _ (by simp [w1, w2, w3])
  set c0 : Val := .list [adjVal X, .nat n, ids n] with hc0
  have w7 : (Val.list [c0, .nat r, t]).wt ≤ 3 * (2 * (c0.wt + levB n + levB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  set E := [Val.list [c0, .nat r, t]] with hE
  have a0 : Lv P E (levT3 n) (arg 0) c0 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (levT3 n) (arg 1) (.nat r) 1 := Lv.arg rfl (by omega)
  have a2 : Lv P E (levT3 n) (arg 2) t 1 := Lv.arg rfl (by omega)
  have g : ∀ k, k ≤ 2 → ∀ w, [adjVal X, .nat n, ids n][k]? = some w →
      Lv P E (levT3 n) (.get (arg 0) (.nat k)) w 4 := fun k hk w hw =>
    Lv.mono (Lv.get (vs := [adjVal X, .nat n, ids n]) a0
      (Lv.nat k (show k + 3 ≤ levT3 n by omega)) hw) (by norm_num)
  have hcall := Lv.call (P := P) (T := levT3 n)
    (Lv.mk2 (Lv.mk5 (g 0 (by omega) _ rfl) (g 1 (by omega) _ rfl) (g 2 (by omega) _ rfl) a1 a2
      (by omega)) (g 2 (by omega) _ rfl) (by omega))
    (levRound_fun h hA ht X v hr) (levTabC_le_T3 n)
  exact funDet_of_lv hc (T := levT3 n) (m := 3000) (Lv.mono (e := levStepE a) hcall (by norm_num))

/-- The bound of the iteration. -/
def levIterC (n : ℕ) : ℕ :=
  n * (3000 * levT3 n) + loopModK * (n + 1) * (levT3 n + n + levB n + 1)

/-- The budget of the entry. -/
def levT4 (n : ℕ) : ℕ := levIterC n + levT n

/-- The bound of the whole level program. -/
def levC (n : ℕ) : ℕ := 100000 * levT4 n

/-- The start table. -/
theorem levInit_fun {P : Program} {a : ℕ} (h : P.HasAt a (tabFuns a levInitE))
    (X : SimpleGraph (Fin n)) (v : Fin n) :
    FunDet P a (.list [.list [.nat n, .nat v], ids n]) (encFun (levAt X v 0))
      (n * (100 * levT n) + mapK * (n + 1) * levT n) := by
  have hB := levB_pos n
  have hB' := le_levB n
  have hTv : levT n = 1000 * levB n := rfl
  have w1 : (Val.nat n).wt ≤ levB n := wt_nat_levB (by omega)
  have w2 := wt_nat_levB (n := n) (show (v : ℕ) ≤ n + 1 by have := v.isLt; omega)
  have w3 : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have w4 : (Val.list [.nat n, .nat (v : ℕ)]).wt ≤ 2 * (2 * levB n + 1) + 4 :=
    wt_lit _ (by simp [w1, w2])
  have w5 : (Val.list [Val.list [.nat n, .nat (v : ℕ)], ids n]).wt ≤
      2 * (2 * (2 * (2 * levB n + 1) + 4 + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have w6 := wt_table_le (levAt_le X v 0)
  refine tabN_spec (W := levT n) (K := 100) (T := levT n) h (fun u => ?_) (by omega)
  have w7 := wt_nat_levB (n := n) (show (u : ℕ) ≤ n + 1 by have := u.isLt; omega)
  have w8 : (Val.list [Val.list [.nat n, .nat (v : ℕ)], .nat (u : ℕ)]).wt ≤
      2 * (2 * (2 * (2 * levB n + 1) + 4 + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  set E := [Val.list [Val.list [.nat n, .nat (v : ℕ)], .nat (u : ℕ)]] with hE
  have a0 : Lv P E (levT n) (arg 0) (.list [.nat n, .nat v]) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (levT n) (arg 1) (.nat u) 1 := Lv.arg rfl (by omega)
  have g0 := Lv.get (vs := [.nat n, .nat v]) a0 (Lv.nat 0 (by omega)) rfl
  have g1 := Lv.get (vs := [.nat n, .nat v]) a0 (Lv.nat 1 (by omega)) rfl
  rw [levAt_zero]
  by_cases he : u = v
  · have h1 := Lv.arith (op := .eq) (z := 1) a1 g1 (by simp [BinOp.eval, he]) (by omega)
    have h2 := Lv.ite_pos (e := .get (arg 0) (.nat 0)) h1 (by omega)
      (Lv.nat 0 (env := E) (show 0 + 3 ≤ levT n by omega))
    rw [if_pos he]
    exact Lv.mono (e := levInitE) h2 (by norm_num)
  · have hne : (u : ℕ) ≠ v := fun h => he (Fin.ext h)
    have h1 := Lv.arith (op := .eq) (z := 0) a1 g1 (by simp [BinOp.eval, hne]) (by omega)
    have h2 := Lv.ite_zero (t := .nat 0) h1 g0
    rw [if_neg he]
    exact Lv.mono (e := levInitE) h2 (by norm_num)

/-- **The distance levels.** -/
theorem lev_spec {P : Program} {b : ℕ} (h : P.HasAt b (levFuns b)) (X : SimpleGraph (Fin n))
    (v : Fin n) :
    FunDet P b (.list [adjVal X, .nat n, ids n, .nat v]) (encFun (lev X v)) (levC n) := by
  have hmain : P.funs[b]? = some (levMainE b) := by
    simpa [levFuns] using h 0 (by simp [levFuns, iterFuns, loopFuns, tabFuns, mapFuns, anyFuns])
  have hiter : P.HasAt (b + 1) (iterFuns (b + 1) (b + 4)) := h.left.left.left.left.left.right
  have hstep : P.funs[b + 4]? = some (levStepE (b + 9)) := h.left.left.left.left.right.single
  have hinit : P.HasAt (b + 5) (tabFuns (b + 5) levInitE) := h.left.left.left.right
  have htab : P.HasAt (b + 9) (tabFuns (b + 9) (levEntryE (b + 13))) := h.left.left.right
  have hany : P.HasAt (b + 13) (anyFuns (b + 13) (b + 16)) := h.left.right
  have htest : P.funs[b + 16]? = some levTestE := h.right.single
  have hB := levB_pos n
  have hB' := le_levB n
  have hTv : levT n = 1000 * levB n := rfl
  have hT3 := levT_le_T3 n
  have w1 : (adjVal X).wt ≤ levB n := wt_adjVal_le X
  have w2 : (Val.nat n).wt ≤ levB n := wt_nat_levB (by omega)
  have w3 : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have w4 := wt_nat_levB (n := n) (show (v : ℕ) ≤ n + 1 by have := v.isLt; omega)
  have w5 : (Val.list [adjVal X, .nat n, ids n]).wt ≤ 3 * (2 * levB n + 1) + 4 :=
    wt_lit _ (by simp [w1, w2, w3])
  have hit : FunDet P (b + 1) (.list [.list [adjVal X, .nat n, ids n], .nat n, encFun (levAt X v 0)])
      (encFun (lev X v)) (levIterC n) := by
    have hw : ∀ i, (encFun (levAt X v i)).wt ≤ levB n := fun i => wt_table_le (levAt_le X v i)
    have hi := iter_spec (P := P) (c := .list [adjVal X, .nat n, ids n]) (k := n)
      (acc0 := encFun (levAt X v 0)) (M := levB n) (B := fun _ => 3000 * levT3 n)
      (Inv := fun i acc => acc = encFun (levAt X v i)) hiter rfl
      (fun i acc _ h => h ▸ hw i)
      (fun i acc hi hacc => by
        subst hacc
        exact levStep_fun hstep htab hany htest X v hi)
    refine hi.mono fun w c hc => ⟨?_, ?_⟩
    · rw [hc.1, levAt_top]
    · have h2 := hc.2
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
      have h3 : (Val.list [.list [adjVal X, .nat n, ids n], .nat n, encFun (levAt X v 0)]).wt ≤
          levT3 n := by
        have : (Val.list [.list [adjVal X, .nat n, ids n], .nat n, encFun (levAt X v 0)]).wt ≤
            3 * (2 * (3 * (2 * levB n + 1) + 4 + levB n + levB n) + 1) + 4 :=
          wt_lit _ (by have := hw 0; simp; omega)
        omega
      refine h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
      omega
  have hin := levInit_fun hinit X v
  have hTc : n * (100 * levT n) + mapK * (n + 1) * levT n ≤ levT4 n := by
    have h1 : mapK * (n + 1) * levT n ≤ loopModK * (n + 1) * (levT3 n + n + levB n + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : n * (100 * levT n) ≤ n * (3000 * levT3 n) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [levT4, levIterC]
    omega
  have hT4 : levT n ≤ levT4 n := by simp only [levT4]; omega
  have w6 : (Val.list [adjVal X, .nat n, ids n, .nat (v : ℕ)]).wt ≤ 4 * (2 * levB n + 1) + 4 :=
    wt_lit _ (by simp [w1, w2, w3, w4])
  set E := [Val.list [adjVal X, .nat n, ids n, .nat (v : ℕ)]] with hE
  have a0 : Lv P E (levT4 n) (arg 0) (adjVal X) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (levT4 n) (arg 1) (.nat n) 1 := Lv.arg rfl (by omega)
  have a2 : Lv P E (levT4 n) (arg 2) (ids n) 1 := Lv.arg rfl (by omega)
  have a3 : Lv P E (levT4 n) (arg 3) (.nat v) 1 := Lv.arg rfl (by omega)
  have c1 := Lv.call (Lv.mk2 (Lv.mk2 a1 a3 (by omega)) a2 (by omega)) hin hTc
  have c2 := Lv.call (Lv.mk3 (Lv.mk3 a0 a1 a2 (by omega)) a1 c1 (by omega)) hit
    (by simp only [levT4]; omega)
  exact funDet_of_lv hmain (T := levT4 n) (m := 100000) (Lv.mono (e := levMainE b) c2 (by norm_num))

theorem levC_poly : PolyB levC := by
  unfold levC levT4 levIterC levT3 levTabC levT2 levAnyC levT levB
  poly

end GI.Degree
