module

public import Workspace.Impl.RowProg

@[expose] public section

/-!
# The coordinates of Theorem A.17, as a program

Pieces of the coordinate program:

* `winTab_spec`: the window `winL q k x1 base s M` as a list value, by a table over `0, …, k - 1`;
* `comm_spec`: the commutator `h g h⁻¹ g⁻¹` of two permutation values;
* `zeroList_spec`: the positions of row `0`, by a filter.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup encPts gens)

/-! ### The window table -/

theorem rowsV_winL {q k x1 base s M : ℕ} (h : ∀ i < k, winF x1 base s M i < q) :
    rowsV (winL q k x1 base s M h) =
      .list ((List.finRange k).map fun i : Fin k => Val.nat (winF x1 base s M i)) := by
  simp [rowsV, natList, winL, List.ofFn_eq_map, List.map_map, Function.comp_def]

/-- The constant of the window table. -/
def winTabK : ℕ := 1000000

set_option maxRecDepth 10000 in
/-- **The window table**: on `[winPar x1 base s M, [0, …, k - 1]]`, the window as a list
value. -/
theorem winTab_spec {P : Program} {b f : ℕ} (hb : P.HasAt b (mapFuns b f))
    (hf : P.funs[f]? = some winStepF) {q k x1 base s M : ℕ}
    (h : ∀ i < k, winF x1 base s M i < q) (hkq : k ≤ q) :
    FunDet P b (.list [winPar x1 base s M, encPerm (1 : Perm (Fin k))])
      (rowsV (winL q k x1 base s M h)) (winTabK * (x1 + base + s + M + k + q + 10) ^ 3) := by
  have ht := tabulate_spec hb (m := k) (c := winPar x1 base s M)
    (F := fun i : Fin k => Val.nat (winF x1 base s M i)) (B := 200 * (x1 + base + s + M + k + 10))
    (fun i => (winStep_spec hf x1 base s M i).mono (by have := i.2; omega))
  rw [← natList_range_eq, range_eq_encPerm_one, ← rowsV_winL h] at ht
  refine ht.mono ?_
  set T := x1 + base + s + M + k + q + 10 with hT
  clear_value T
  have w1 : (winPar x1 base s M).wt ≤ 2 * T + 20 := by
    have := wt_list4_le (.nat x1) (.nat base) (.nat s) (.nat M)
    have := wt_nat_le x1; have := wt_nat_le base; have := wt_nat_le s; have := wt_nat_le M
    unfold winPar; omega
  have w2 := wt_encPerm_le (1 : Perm (Fin k))
  have w3 : (rowsV (winL q k x1 base s M h)).wt ≤ 5 * (q + 1) ^ 2 :=
    wt_rowsV_le _ (by rw [length_winL]; exact hkq)
  have w4 := wt_list2_le (winPar x1 base s M) (encPerm (1 : Perm (Fin k)))
  have hT1 : 10 ≤ T := by omega
  have e1 : (k + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e2 : (q + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e3 : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num) _
  have e4 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have c1 : k * (200 * (x1 + base + s + M + k + 10)) ≤ T * (200 * T) :=
    Nat.mul_le_mul (by omega) (by omega)
  have c2 : mapK * (k + 1) * ((Val.list [winPar x1 base s M, encPerm (1 : Perm (Fin k))]).wt +
      (rowsV (winL q k x1 base s M h)).wt + 1) ≤ mapK * T * (100 * T ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have c3 : T * (200 * T) = 200 * T ^ 2 := by ring
  have c4 : mapK * T * (100 * T ^ 2) = 100000 * T ^ 3 := by simp only [mapK]; ring
  clear ht hb hf
  generalize (winPar x1 base s M).wt = W1 at *
  generalize (rowsV (winL q k x1 base s M h)).wt = W3 at *
  generalize (encPerm (1 : Perm (Fin k))).wt = W2 at *
  generalize (Val.list [winPar x1 base s M, encPerm (1 : Perm (Fin k))]).wt = W4 at *
  simp only [winTabK]
  omega

/-! ### Commutators -/

/-- On `[g, h]`: `h g h⁻¹ g⁻¹`. Composition at `cp`, inverse at `iv`. -/
def commF (cp iv : ℕ) : Expr :=
  .call cp (mk2 (.call cp (mk2 (.call cp (mk2 (arg 1) (arg 0))) (.call iv (arg 1))))
    (.call iv (arg 0)))

/-- The constant of the commutator. -/
def commK : ℕ := 10000000

theorem comm_spec {P : Program} {f cp iv n : ℕ} (hf : P.funs[f]? = some (commF cp iv))
    (hcp : P.HasAt cp (composeFuns cp)) (hiv : P.HasAt iv (invFuns iv)) (g h : Perm (Fin n)) :
    FunDet P f (.list [encPerm g, encPerm h]) (encPerm (h * g * h⁻¹ * g⁻¹))
      (commK * (n + 1) ^ 4) := by
  have a0 := Det.arg' (P := P) (vs := [encPerm g, encPerm h]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [encPerm g, encPerm h]) (rest := []) (j := 1) rfl
  have d1 := Det.call (Det.mk2 a1 a0) (compose_spec hcp h g)
  have d2 := Det.call a1 (inv_spec hiv h)
  have d3 := Det.call (Det.mk2 d1 d2) (compose_spec hcp (h * g) h⁻¹)
  have d4 := Det.call a0 (inv_spec hiv g)
  have d5 := Det.call (Det.mk2 d3 d4) (compose_spec hcp (h * g * h⁻¹) g⁻¹)
  refine FunDet.intro hf (d5.mono ?_)
  have w : ∀ x : Perm (Fin n), (encPerm x).wt ≤ 4 * (n + 1) ^ 2 := fun x => wt_encPerm_le x
  have wi := wt_list2_le (encPerm g) (encPerm h)
  have wa := wt_list2_le (encPerm h) (encPerm g)
  have wb := wt_list2_le (encPerm (h * g)) (encPerm h⁻¹)
  have wc := wt_list2_le (encPerm (h * g * h⁻¹)) (encPerm g⁻¹)
  have := w g; have := w h; have := w (h * g); have := w h⁻¹; have := w (h * g * h⁻¹)
  have := w g⁻¹; have := w (h * g * h⁻¹ * g⁻¹)
  have e1 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have e0 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  simp only [commK, permK, invK]
  omega

/-! ### The positions of row `0` -/

/-- On `[rl, i]`: whether `rl[i] = 0`. -/
def zeroTestF : Expr := .arith .eq (.get (arg 0) (arg 1)) (.nat 0)

/-- The positions whose row label is `0`. -/
def zeroPts (rl : List ℕ) (k : ℕ) : List (Fin k) :=
  (List.finRange k).filter fun i => decide (rl.getD i 0 = 0)

/-- The test on values. -/
def zeroQ (rl : List ℕ) : Val → Bool
  | .nat i => decide (rl.getD i 0 = 0)
  | .list _ => false

theorem zeroTest_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some zeroTestF) (rl : List ℕ)
    (i : ℕ) (hi : i < rl.length) :
    FunDet P f (.list [natList rl, .nat i]) (boolVal (zeroQ rl (.nat i)))
      (10 * (Val.list [natList rl, .nat i]).wt + 20) := by
  have a0 := Det.arg' (P := P) (vs := [natList rl, .nat i]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [natList rl, .nat i]) (rest := []) (j := 1) rfl
  have hn : natList rl = .list (rl.map Val.nat) := rfl
  rw [hn] at a0
  have dg := Det.get' a0 a1 (v := .nat (rl.getD i 0)) (by
    rw [List.getElem?_map, List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]; rfl)
  have d := Det.arith' (op := .eq) dg (Det.nat 0) (z := if rl.getD i 0 = 0 then 1 else 0) rfl
  have hv : Val.nat (if rl.getD i 0 = 0 then 1 else 0) = boolVal (zeroQ rl (.nat i)) := by
    simp only [zeroQ, boolVal]
    rw [List.getD_eq_getElem?_getD]
    split_ifs with h' <;> simp [h']
  rw [hv] at d
  refine FunDet.intro hf (d.mono ?_)
  have w1 : (Val.nat (rl.getD i 0)).wt < (natList rl).wt := by
    rw [hn]; apply wt_le_wt_list
    rw [List.getD_eq_getElem _ _ hi]; exact List.mem_map_of_mem (List.getElem_mem hi)
  have w2 : (natList rl).wt < (Val.list [natList rl, .nat i]).wt := wt_le_wt_list (by simp)
  have e : (Val.list (rl.map Val.nat)).wt = (natList rl).wt := rfl
  have hb : (if rl.getD i 0 = 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have e2 : (Val.list [Val.list (rl.map Val.nat), .nat i]).wt = (Val.list [natList rl, .nat i]).wt :=
    rfl
  have w3 := wt_boolVal_le (zeroQ rl (.nat i))
  omega

theorem natList_zeroPts (rl : List ℕ) (k : ℕ) :
    natList ((zeroPts rl k).map Fin.val) =
      .list (((List.range k).map Val.nat).filter (zeroQ rl)) := by
  unfold natList zeroPts
  have e1 : (List.range k).map Val.nat = (List.finRange k).map (fun i : Fin k => Val.nat i.val) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]; rfl
  rw [e1, List.filter_map, List.map_map]
  rfl

/-- The constant of the row-`0` filter. -/
def zeroFK : ℕ := 10000

theorem zeroList_spec {P : Program} {b f : ℕ} (hb : P.HasAt b (filterFuns b f))
    (hf : P.funs[f]? = some zeroTestF) {k : ℕ} (rl : List ℕ) (hl : rl.length = k) :
    FunDet P b (.list [natList rl, encPerm (1 : Perm (Fin k))])
      (natList ((zeroPts rl k).map Fin.val))
      (zeroFK * ((Val.list [natList rl, encPerm (1 : Perm (Fin k))]).wt + 1) ^ 2) := by
  set A := (Val.list [natList rl, encPerm (1 : Perm (Fin k))]).wt
  have hxs : encPerm (1 : Perm (Fin k)) = .list ((List.range k).map Val.nat) := by
    rw [← range_eq_encPerm_one]; rfl
  have hcA : (natList rl).wt < A := wt_le_wt_list (by simp)
  have hnA : k < A := by
    have := length_lt_wt_list ((List.range k).map Val.nat)
    have h2 : (encPerm (1 : Perm (Fin k))).wt < A := wt_le_wt_list (by simp)
    rw [hxs] at h2
    simp only [List.length_map, List.length_range] at this
    omega
  have hF := filter_spec hb (c := natList rl) (xs := (List.range k).map Val.nat) (q := zeroQ rl)
    (B := fun _ => 10 * (4 * A + 10) + 20) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hik : i < k := List.mem_range.mp hi
      refine (zeroTest_spec hf rl i (by omega)).mono ?_
      have := wt_list2_le (natList rl) (.nat i)
      have := wt_nat_le i
      show _ ≤ 10 * (4 * A + 10) + 20
      omega)
  rw [← hxs] at hF
  refine FunAll.mono hF fun w cost ⟨hw, hc⟩ => ⟨?_, ?_⟩
  · rw [hw, natList_zeroPts]
  · simp only [List.map_map, List.map_const', List.sum_replicate, smul_eq_mul, List.length_map,
      List.length_range, Function.comp_def] at hc
    have eA : (Val.list [natList rl, encPerm (1 : Perm (Fin k))]).wt = A := rfl
    rw [eA] at hc
    have hww : w.wt ≤ A := by
      rw [hw]
      have h1 := wt_list_sublist (List.filter_sublist (p := zeroQ rl)
        (l := (List.range k).map Val.nat))
      have h2 : (encPerm (1 : Perm (Fin k))).wt < A := wt_le_wt_list (by simp)
      rw [hxs] at h2
      exact le_of_lt (lt_of_le_of_lt h1 h2)
    have h1 : k * (10 * (4 * A + 10) + 20) ≤ A * (40 * A + 120) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : loopModK * (k + 1) * (A + k + w.wt + 1) ≤ loopModK * (A + 1) * (4 * A + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have h3 : A * (40 * A + 120) + loopModK * (A + 1) * (4 * A + 1) ≤ zeroFK * (A + 1) ^ 2 := by
      simp only [zeroFK, loopModK]; ring_nf; nlinarith
    omega

/-! ### An `if` whose `else` branch has a specification -/

theorem EvalAll.ite_zero' {P : Program} {env : List Val} {c t e : Expr} {cc : ℕ}
    (hc : Det P env c (.nat 0) cc) {R : Val → ℕ → Prop} (he : EvalAll P env e R) :
    EvalAll P env (.ite c t e) (fun w c' => ∃ ce, R w ce ∧ c' ≤ cc + ce + w.wt + 1) :=
  EvalAll.ite hc (fun _ _ h => ⟨0, h.1⟩) fun y cc' h => by
    obtain ⟨h1, h2⟩ := h
    cases h1
    rw [if_pos rfl]
    exact he.mono fun w ce hw => ⟨ce, hw, by omega⟩

/-! ### One row of the coordinates -/

/-- `toFin` of a commutator. -/
theorem toFin_comm {Ω : Type} {n : ℕ} (e : Ω ≃ Fin n) (g h : Perm Ω) :
    toFin e (rightLocalCommutator g h) =
      toFin e h * toFin e g * (toFin e h)⁻¹ * (toFin e g)⁻¹ := by
  simp [rightLocalCommutator, map_mul, map_inv]

/-- The context of a row: `[ctx, [0, …, kk - 1], [c, c²], row 0]`. -/
def rowCtx (n q kk : ℕ) (rl : List ℕ) (ps : List (Perm (Fin n) × Perm (Fin q)))
    (c c2 : Perm (Fin n)) (r0 : List ℕ) : Val :=
  .list [winCtx n q rl ps, encPerm (1 : Perm (Fin kk)), .list [encPerm c, encPerm c2], natList r0]

/-- `ρⱼ` for `j < 3`: `1`, `c` or `c²`. -/
def smallE : Expr :=
  .ite (.arith .eq (arg 1) (.nat 0)) (.get (.get (arg 0) (.nat 0)) (.nat 6))
    (.ite (.arith .eq (arg 1) (.nat 1)) (.get (.get (arg 0) (.nat 2)) (.nat 0))
      (.get (.get (arg 0) (.nat 2)) (.nat 1)))

/-- `ρⱼ = [c, hⱼ]` for `j ≥ 3`, with `hⱼ` a lift of the window `winJ j`. -/
def bigE (lw wt cm : ℕ) : Expr :=
  .letE (.call lw (mk2 (.get (arg 0) (.nat 0)) (.call wt (mk2 (mk4 (arg 1) (.nat 3)
      (.arith .sub (arg 1) (.nat 2)) (.arith .sub (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 3)))
      (.get (arg 0) (.nat 1))))))
    (.call cm (mk2 (.get (.get (arg 0) (.nat 2)) (.nat 0)) (.var 1)))

/-- **One row**, on `[rowCtx, j]`: the positions `ρⱼ(row 0)`. -/
def rowF (lw wt cm ga : ℕ) : Expr :=
  .letE (.ite (.arith .lt (arg 1) (.nat 3)) smallE (bigE lw wt cm))
    (.call ga (mk2 (.var 1) (.get (arg 0) (.nat 3))))

/-- The cost bound of one row. -/
noncomputable def rowStepCost (hst : GI.Cited.PointwiseStab) (hfac : GI.Cited.NormalizedFactor)
    (M : ℕ) : ℕ :=
  liftWinCost hst hfac M + 10000000000000 * M ^ 6

section Row

variable {Ω C : Type} {n : ℕ} {e : Ω ≃ Fin n} {S : State Ω C} {L : GiantLabels S}
  {label : Ω → Fin L.q}

theorem wt_rowCtx_le {rl : List ℕ} (hl : rl.length = n) (hrl : ∀ r ∈ rl, r ≤ L.q)
    (ps : List (Perm (Fin n) × Perm (Fin L.q))) {kk : ℕ} (hkk : kk ≤ L.q) (c c2 : Perm (Fin n))
    (r0 : List ℕ) (hr0 : ∀ r ∈ r0, r ≤ n) (hr0l : r0.length ≤ n) :
    (rowCtx n L.q kk rl ps c c2 r0).wt ≤ 1000 * (n + L.q + ps.length + 2) ^ 3 := by
  have h1 := wt_winCtx_le hl hrl ps
  have h2 := wt_encPerm_le (1 : Perm (Fin kk))
  have h3 := wt_encPerm_le c
  have h4 := wt_encPerm_le c2
  have h5 := wt_list2_le (encPerm c) (encPerm c2)
  have h6 : (natList r0).wt ≤ 5 * (n + 1) ^ 2 := wt_natList_le_sq hr0 hr0l
  have h7 := wt_list4_le (winCtx n L.q rl ps) (encPerm (1 : Perm (Fin kk)))
    (.list [encPerm c, encPerm c2]) (natList r0)
  have hpM : pM n L.q ps = n + L.q + ps.length + 2 := rfl
  rw [hpM] at h1
  set M := n + L.q + ps.length + 2 with hM
  have b1 : (n + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have b2 : (kk + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have b3 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have b0 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold rowCtx
  omega

/-- The gathered row: the entries of `ρ` at the positions of row `0`. -/
theorem gather_zeroPts {n : ℕ} (rl : List ℕ) (ρ : Perm (Fin n)) :
    Val.list (((zeroPts rl n).map Fin.val).map fun i =>
      ((List.finRange n).map fun i => Val.nat (ρ i)).getD i (.nat 0)) =
      natList ((zeroPts rl n).map fun i => ((ρ i : Fin n) : ℕ)) := by
  unfold natList
  rw [List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

set_option maxHeartbeats 3200000 in
/-- **One row of the coordinates.** On `[rowCtx, j]` with `c = [g₁, h₁]` and `c²` in the
context, `rowF` returns the positions `ρⱼ(row 0)`, where `ρ₀ = 1`, `ρ₁ = c`, `ρ₂ = c²` and
`ρⱼ = [c, hⱼ]` for `j ≥ 3`, for a lift `hⱼ` of the window `winJ j` (`rhoOf`). -/
theorem rowStep_spec (hst : GI.Cited.PointwiseStab) (hfac : GI.Cited.NormalizedFactor)
    {P : Program} {f lw wt ws cm cp iv ga jp jf : ℕ}
    (hf : P.funs[f]? = some (rowF lw wt cm ga))
    (hlw : P.HasAt lw (liftWinFuns lw jp jf)) (hjp : P.prims[jp]? = some (pointwiseStabPrim hst))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    (hwt : P.HasAt wt (mapFuns wt ws)) (hws : P.funs[ws]? = some winStepF)
    (hcm : P.funs[cm]? = some (commF cp iv)) (hcp : P.HasAt cp (composeFuns cp))
    (hiv : P.HasAt iv (invFuns iv)) (hga : P.HasAt ga (gatherFuns ga))
    {ps : List (Perm (Fin n) × Perm (Fin L.q))} (hps : PairGens e L S.G ps) {rl : List ℕ}
    (hrl : RowLabs e S label rl) {kk : ℕ} (hk : WinLen L.q kk) (g1 h1 : Perm Ω) (j : Fin L.q)
    (hex : 3 ≤ (j : ℕ) → ∃ g, WinLift S L label (winJ hk j) g) :
    FunAll P f (.list [rowCtx n L.q kk rl ps (toFin e (cOf g1 h1))
        (toFin e (cOf g1 h1 * cOf g1 h1)) ((zeroPts rl n).map Fin.val), .nat j])
      (fun w c => ∃ hj : Perm Ω, (3 ≤ (j : ℕ) → WinLift S L label (winJ hk j) hj) ∧
        w = natList ((zeroPts rl n).map fun i =>
          ((toFin e (rhoOf g1 h1 (fun _ => hj) j) i : Fin n) : ℕ)) ∧
        c ≤ rowStepCost hst hfac (n + L.q + ps.length + 2)) := by
  classical
  set c := toFin e (cOf g1 h1) with hc
  set c2 := toFin e (cOf g1 h1 * cOf g1 h1) with hc2
  set r0 := (zeroPts rl n).map Fin.val with hr0
  set ctx := winCtx n L.q rl ps with hctx
  set rc := rowCtx n L.q kk rl ps c c2 r0 with hrc
  set inp := Val.list [rc, .nat j] with hinp
  set M := n + L.q + ps.length + 2 with hM
  have hkq : kk ≤ L.q := by have := hk.le; have := hk.five; omega
  have hr0b : ∀ r ∈ r0, r ≤ n := by
    intro r hr; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr; exact i.2.le
  have hr0l : r0.length ≤ n := by
    rw [hr0, List.length_map]; exact (List.length_filter_le _ _).trans (by simp)
  have hI : inp.wt ≤ 3000 * M ^ 3 := by
    have h1 := wt_rowCtx_le hrl.1 hrl.le ps hkq c c2 r0 hr0b hr0l
    have h2 := wt_list2_le rc (.nat j)
    have h3 := wt_nat_le j
    have h4 : (j : ℕ) + 2 ≤ M ^ 3 := by
      have : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) _
      have := j.2; omega
    have h5 : 1 ≤ M ^ 3 := Nat.one_le_pow _ _ (by omega)
    have e1 : (rowCtx n L.q kk rl ps c c2 r0).wt = rc.wt := rfl
    have e2 : (Val.list [rc, .nat j]).wt = inp.wt := rfl
    have e3 : (n + L.q + ps.length + 2) ^ 3 = M ^ 3 := rfl
    omega
  have hrcI : rc.wt < inp.wt := wt_le_wt_list (by simp only [List.mem_cons, true_or])
  have hctxI : ctx.wt < rc.wt := by
    show ctx.wt < (Val.list [ctx, encPerm (1 : Perm (Fin kk)), .list [encPerm c, encPerm c2],
      natList r0]).wt
    exact wt_le_wt_list (by simp)
  -- reads
  have rdR : ∀ (rest : List Val) (i : ℕ) (v : Val),
      [ctx, encPerm (1 : Perm (Fin kk)), .list [encPerm c, encPerm c2], natList r0][i]? = some v →
      Det P (inp :: rest) (.get (arg 0) (.nat i)) v (4 * inp.wt + 20) := by
    intro rest i v h
    have hv := List.mem_of_getElem? h
    have hi : i < 4 := by
      obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 h; simpa using hi
    have d := Det.get' (Det.arg' (P := P) (vs := [rc, .nat j]) (rest := rest) (j := 0) rfl)
      (Det.nat i) h
    refine d.mono ?_
    have h1 : v.wt < rc.wt := wt_le_wt_list hv
    have h3 : (Val.list [rc, .nat j]).wt = inp.wt := rfl
    omega
  have rdC : ∀ (rest : List Val) (i : ℕ) (v : Val),
      [.nat n, .nat L.q, natList rl, .list (ps.map pairV), pSplitCtx n L.q,
        encPerm (1 : Perm (Fin L.q)), encPerm (1 : Perm (Fin n))][i]? = some v →
      Det P (inp :: rest) (.get (.get (arg 0) (.nat 0)) (.nat i)) v (6 * inp.wt + 40) := by
    intro rest i v h
    have hv := List.mem_of_getElem? h
    have hi : i < 7 := by
      obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 h; simpa using hi
    have d := Det.get' (rdR rest 0 ctx rfl) (Det.nat i) h
    refine d.mono ?_
    have h1 : v.wt < ctx.wt := wt_le_wt_list hv
    omega
  have rdP : ∀ (rest : List Val) (i : ℕ) (v : Val), [encPerm c, encPerm c2][i]? = some v →
      Det P (inp :: rest) (.get (.get (arg 0) (.nat 2)) (.nat i)) v (6 * inp.wt + 40) := by
    intro rest i v h
    have hv := List.mem_of_getElem? h
    have hi : i < 2 := by
      obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 h; simpa using hi
    have d := Det.get' (rdR rest 2 _ rfl) (Det.nat i) h
    refine d.mono ?_
    have h1 : v.wt < (Val.list [encPerm c, encPerm c2]).wt := wt_le_wt_list hv
    have h2 : (Val.list [encPerm c, encPerm c2]).wt < rc.wt := by
      show _ < (Val.list [ctx, encPerm (1 : Perm (Fin kk)), .list [encPerm c, encPerm c2],
        natList r0]).wt
      exact wt_le_wt_list (by simp)
    omega
  have a1 : ∀ rest : List Val, Det P (inp :: rest) (arg 1) (.nat j) (2 * inp.wt + 6) := fun rest =>
    (Det.arg' (P := P) (vs := [rc, .nat j]) (rest := rest) (j := 1) rfl).mono (le_of_eq rfl)
  -- sizes
  have hM2 : 2 ≤ M := by omega
  have hnM : n + 1 ≤ M := by omega
  have hqM : L.q + 2 ≤ M := by omega
  have p12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have p34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have p46 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn2 : (n + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hnM 2
  have hn4 : (n + 1) ^ 4 ≤ M ^ 4 := Nat.pow_le_pow_left hnM 4
  have hjq := j.2
  set RB := liftWinCost hst hfac M + 1000000000 * M ^ 4 + 1000 * inp.wt with hRB
  refine FunAll.intro hf (EvalAll.letE (Ra := fun w cw => ∃ hj : Perm Ω,
      (3 ≤ (j : ℕ) → WinLift S L label (winJ hk j) hj) ∧
      w = encPerm (toFin e (rhoOf g1 h1 (fun _ => hj) j)) ∧ cw ≤ RB) ?_ fun v cv hv => ?_)
  · by_cases hj3 : (j : ℕ) < 3
    · have dlt := Det.arith' (op := .lt) (a1 []) (Det.nat (P := P) (env := [inp]) 3) (z := 1)
        (by simp [BinOp.eval, hj3])
      have de0 := Det.arith' (op := .eq) (a1 []) (Det.nat (P := P) (env := [inp]) 0)
        (z := if (j : ℕ) = 0 then 1 else 0) (by simp [BinOp.eval])
      have de1 := Det.arith' (op := .eq) (a1 []) (Det.nat (P := P) (env := [inp]) 1)
        (z := if (j : ℕ) = 1 then 1 else 0) (by simp [BinOp.eval])
      have wc := wt_encPerm_le c
      have wc2 := wt_encPerm_le c2
      have w1 := wt_encPerm_le (1 : Perm (Fin n))
      have dsm : Det P [inp] smallE (encPerm (toFin e (rhoOf g1 h1 (fun _ => 1) j)))
          (40 * inp.wt + 40 * M ^ 2 + 300) := by
        rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 by omega) with h0 | h0 | h0
        · rw [if_pos h0] at de0
          have hv : encPerm (toFin e (rhoOf g1 h1 (fun _ => 1) j)) = encPerm (1 : Perm (Fin n)) := by
            simp only [rhoOf, if_pos h0, map_one]
          rw [hv]
          refine (Det.ite_pos de0 one_ne_zero (rdC [] 6 _ rfl)).mono ?_
          omega
        · rw [if_neg (by omega)] at de0
          rw [if_pos h0] at de1
          have hv : encPerm (toFin e (rhoOf g1 h1 (fun _ => 1) j)) = encPerm c := by
            simp [rhoOf, h0, hc]
          rw [hv]
          refine (Det.ite_zero de0 (Det.ite_pos de1 one_ne_zero (rdP [] 0 _ rfl))).mono ?_
          omega
        · rw [if_neg (by omega)] at de0
          rw [if_neg (by omega)] at de1
          have hv : encPerm (toFin e (rhoOf g1 h1 (fun _ => 1) j)) = encPerm c2 := by
            simp [rhoOf, h0, hc2]
          rw [hv]
          refine (Det.ite_zero de0 (Det.ite_zero de1 (rdP [] 1 _ rfl))).mono ?_
          omega
      refine (Det.ite_pos dlt one_ne_zero dsm).post fun c' hc' =>
        ⟨1, fun h => absurd h (by omega), rfl, ?_⟩
      have := wt_encPerm_le (toFin e (rhoOf g1 h1 (fun _ => 1) j))
      have : 0 ≤ liftWinCost hst hfac M := Nat.zero_le _
      omega
    · have hj3' : 3 ≤ (j : ℕ) := by omega
      have dlt := Det.arith' (op := .lt) (a1 []) (Det.nat (P := P) (env := [inp]) 3) (z := 0)
        (by simp [BinOp.eval]; omega)
      obtain ⟨g0, hg0⟩ := hex hj3'
      have hwin := winTab_spec hwt hws (boundJ hk j) hkq
      have dpar := Det.mk4 (a1 []) (Det.nat (P := P) (env := [inp]) 3)
        (Det.arith' (op := .sub) (a1 []) (Det.nat (P := P) (env := [inp]) 2) (z := (j : ℕ) - 2) rfl)
        (Det.arith' (op := .sub) (rdC [] 1 _ rfl) (Det.nat (P := P) (env := [inp]) 3)
          (z := L.q - 3) rfl)
      have dw := Det.call (Det.mk2 dpar (rdR [] 1 _ rfl)) hwin
      have ewin : winL L.q kk j 3 (j - 2) (L.q - 3) (boundJ hk j) = winJ hk j := rfl
      rw [ewin] at dw
      have wpar := wt_list4_le (.nat j) (.nat 3) (.nat ((j : ℕ) - 2)) (.nat (L.q - 3))
      have wj := wt_nat_le j
      have wj2 := wt_nat_le ((j : ℕ) - 2)
      have wq3 := wt_nat_le (L.q - 3)
      have w3 := wt_nat_le 3
      have wkk := wt_encPerm_le (1 : Perm (Fin kk))
      have wkk2 : (kk + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have wpk := wt_list2_le (Val.list [.nat j, .nat 3, .nat ((j : ℕ) - 2), .nat (L.q - 3)])
        (encPerm (1 : Perm (Fin kk)))
      have wrow := wt_rowsV_le (winJ hk j) (by rw [length_winJ]; exact hkq)
      have hq2 : (L.q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have wT : winTabK * ((j : ℕ) + 3 + ((j : ℕ) - 2) + (L.q - 3) + kk + L.q + 10) ^ 3 ≤
          winTabK * (125 * M ^ 3) := by
        apply Nat.mul_le_mul_left
        calc _ ≤ (5 * M) ^ 3 := Nat.pow_le_pow_left (by omega) 3
          _ = 125 * M ^ 3 := by ring
      have wcr := wt_list2_le ctx (rowsV (winJ hk j))
      have hctxw : ctx.wt < inp.wt := by omega
      have eLW : liftWinCost hst hfac (n + L.q + ps.length + 2) = liftWinCost hst hfac M := rfl
      have dl := EvalAll.call_funAll (Q := fun w cw => ∃ hj : Perm Ω,
          WinLift S L label (winJ hk j) hj ∧ w = encPerm (toFin e hj) ∧
          cw ≤ 100 * inp.wt + 200 * M ^ 2 + winTabK * (125 * M ^ 3) + 500 +
            liftWinCost hst hfac M)
        (Det.mk2 (rdR [] 0 _ rfl) dw) fun v ca h => by
          obtain ⟨rfl, hca⟩ := h
          exact (liftWin_spec hst hfac hlw hjp hjf hps hrl (winJ hk j) (winJ_nodup hk j hj3')
            (by rw [length_winJ]; have := hk.five; omega) (by rw [length_winJ]; exact hkq)
            ⟨g0, hg0⟩).mono fun w cw ⟨g, hg, hw, hcw⟩ => ⟨g, hg, hw, by
              have := wt_encPerm_le (toFin e g)
              rw [hw]
              omega⟩
      have dbig : EvalAll P [inp] (bigE lw wt cm) (fun w cw => ∃ hj : Perm Ω,
          WinLift S L label (winJ hk j) hj ∧ w = encPerm (toFin e (dOf g1 h1 hj)) ∧
          cw ≤ 200 * inp.wt + 500 * M ^ 2 + winTabK * (125 * M ^ 3) + commK * M ^ 4 + 1000 +
            liftWinCost hst hfac M) :=
        EvalAll.letE dl fun v cv hv => by
          obtain ⟨hj, hjl, rfl, hcv⟩ := hv
          have dcm := Det.call (Det.mk2 (rdP [encPerm (toFin e hj)] 0 _ rfl)
            (Det.var' (P := P) (env := [inp, encPerm (toFin e hj)]) (i := 1) rfl))
            (comm_spec hcm hcp hiv c (toFin e hj))
          have hv' : encPerm (toFin e hj * c * (toFin e hj)⁻¹ * c⁻¹) =
              encPerm (toFin e (dOf g1 h1 hj)) := by
            rw [dOf, toFin_comm]
          rw [hv'] at dcm
          refine dcm.post fun c' hc' => ⟨hj, hjl, rfl, ?_⟩
          have := wt_encPerm_le (toFin e hj)
          have := wt_encPerm_le (toFin e (dOf g1 h1 hj))
          have := wt_list2_le (encPerm c) (encPerm (toFin e hj))
          have := Nat.mul_le_mul_left commK hn4
          have := wt_encPerm_le c
          omega
      refine (EvalAll.ite_zero' dlt dbig).mono fun w cw ⟨ce, ⟨hj, hjl, hw, hce⟩, hcw⟩ =>
        ⟨hj, fun _ => hjl, ?_, ?_⟩
      · have : rhoOf g1 h1 (fun _ => hj) j = dOf g1 h1 hj := by
          simp only [rhoOf]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rw [hw, this]
      · have := wt_encPerm_le (toFin e (dOf g1 h1 hj))
        rw [hw] at hcw
        simp only [winTabK, commK] at *
        omega
  · obtain ⟨hj, hjl, rfl, hcv⟩ := hv
    generalize hρ : toFin e (rhoOf g1 h1 (fun _ => hj) j) = ρ
    have hg := gather_spec hga (L := (List.finRange n).map fun i => Val.nat (ρ i)) (is := r0)
      (by
        intro i hi
        obtain ⟨x, -, rfl⟩ := List.mem_map.mp hi
        simp)
    have dg := Det.call (Det.mk2 (Det.var' (P := P) (env := [inp, encPerm ρ]) (i := 1) rfl)
      (rdR [encPerm ρ] 3 _ rfl)) hg
    have hval := gather_zeroPts rl ρ
    rw [← hr0] at hval
    rw [hval] at dg
    refine dg.post fun c' hc' => ⟨hj, hjl, by rw [hρ], ?_⟩
    have w1 := wt_encPerm_le ρ
    have w2 : (natList r0).wt ≤ 5 * (n + 1) ^ 2 := wt_natList_le_sq hr0b hr0l
    have w3 := wt_list2_le (encPerm ρ) (natList r0)
    have w4 : (natList ((zeroPts rl n).map fun i => ((ρ i : Fin n) : ℕ))).wt ≤ 5 * (n + 1) ^ 2 :=
      wt_natList_le_sq (by intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact (ρ i).2.le)
        (by rw [List.length_map]; rw [hr0, List.length_map] at hr0l; exact hr0l)
    have eL : Val.list ((List.finRange n).map fun i => Val.nat (ρ i)) = encPerm ρ := rfl
    rw [eL] at hc'
    have w5 : (Val.list [encPerm ρ, natList r0]).wt + 1 ≤ 22 * M ^ 2 := by omega
    have w6 : gatherK * ((Val.list [encPerm ρ, natList r0]).wt + 1) ^ 3 ≤
        gatherK * (10648 * M ^ 6) := by
      apply Nat.mul_le_mul_left
      calc _ ≤ (22 * M ^ 2) ^ 3 := Nat.pow_le_pow_left w5 3
        _ = 10648 * M ^ 6 := by ring
    have hcv' : cv ≤ liftWinCost hst hfac M + 1000000000 * M ^ 4 + 1000 * inp.wt := hcv
    have hgK : gatherK = 100000 := rfl
    rw [hgK] at w6 hc'
    unfold rowStepCost
    omega

end Row

end GI.Impl
