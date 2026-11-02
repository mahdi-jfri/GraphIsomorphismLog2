import Workspace.Impl.RowCoords

/-!
# The coordinate program (Theorem A.17)

The program computes pure coordinates for the rows of a giant step. It lifts two windows
(`win1`, `win2`) to `g₁, h₁`, takes the clean cycle `c = [g₁, h₁]`, numbers row `0` by position
and then builds each row `j` from `rhoOf j` (`rowStep_spec`). The result is `coords_spec`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup encPts gens)

/-! ### The coordinate program -/

/-- `kkOf q`, from the context. -/
def kkE : Expr :=
  let H := Expr.arith .div (.arith .add (cE 1) (.nat 1)) (.nat 2)
  .arith .add (.arith .sub H (.nat 1)) (.arith .mod H (.nat 2))

/-- **The coordinate program**, on `[ctx]`: the lifts `g₁, h₁` of the two first windows, the
clean cycle `c = [g₁, h₁]` and `c²`, the positions of row `0`, and then one row for each label
(`rowF`). -/
def coordF (b : ℕ) : Expr :=
  .letE kkE
  (.letE (.call (b + 1) (.var 1))
  (.letE (.call (b + 37) (mk2 (arg 0)
      (.call (b + 4) (mk2 (mk4 (.nat 2) (.nat 3) (.nat 0) (cE 1)) (.var 2)))))
  (.letE (.call (b + 37) (mk2 (arg 0)
      (.call (b + 4) (mk2 (mk4 (.nat 1) (.arith .add (.var 1) (.nat 1)) (.nat 0) (cE 1)) (.var 2)))))
  (.letE (.call (b + 8) (mk2 (.var 3) (.var 4)))
  (.letE (.call (b + 9) (mk2 (.var 5) (.var 5)))
  (.letE (.call (b + 25) (mk2 (cE 2) (cE 6)))
  (.call (b + 29) (mk2 (mk4 (arg 0) (.var 2) (mk2 (.var 5) (.var 6)) (.var 7)) (cE 5)))))))))

/-- The first part of the coordinate module (37 functions). -/
def coordA (b : ℕ) : List Expr :=
  [coordF b] ++ rangeFuns (b + 1) ++ mapFuns (b + 4) (b + 7) ++ [winStepF] ++
    [commF (b + 9) (b + 13)] ++ composeFuns (b + 9) ++ invFuns (b + 13) ++
    filterFuns (b + 25) (b + 28) ++ [zeroTestF] ++ mapFuns (b + 29) (b + 32) ++
    [rowF (b + 37) (b + 4) (b + 8) (b + 33)] ++ gatherFuns (b + 33)

theorem length_coordA (b : ℕ) : (coordA b).length = 37 := rfl

/-- **The coordinate module** at `b` (118 functions), with the cited primitives at `jp`
(PointwiseStab) and `jf` (NormalizedFactor). -/
def coordFuns (b jp jf : ℕ) : List Expr := coordA b ++ liftWinFuns (b + 37) jp jf

/-- The output: row `j` lists the positions `e (E (β, j))` for `β = 0, …, m - 1`. -/
def coordsVal {Ω C : Type} {n q : ℕ} (e : Ω ≃ Fin n) (S : State Ω C) {m : ℕ}
    (E : Fin m × Fin q ≃ S.dom) : Val :=
  .list ((List.finRange q).map fun j =>
    natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin n) : ℕ)))

/-- The cost bound of the coordinate program. -/
noncomputable def coordCost (hst : GI.Cited.PointwiseStab) (hfac : GI.Cited.NormalizedFactor)
    (M : ℕ) : ℕ :=
  (M + 2) * rowStepCost hst hfac M + 1000000000000000 * M ^ 6

section Coords

variable {Ω C : Type} {n : ℕ} {e : Ω ≃ Fin n} {S : State Ω C} {L : GiantLabels S}
  {label : Ω → Fin L.q}

theorem mem_zeroPts {rl : List ℕ} (hrl : RowLabs e S label rl) (hq : 1 ≤ L.q) (i : Fin n) :
    i ∈ zeroPts rl n ↔ ∃ _ : e.symm i ∈ S.dom, (label (e.symm i) : ℕ) = 0 := by
  classical
  have hr := hrl.2 i
  simp only [zeroPts, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  by_cases hi : e.symm i ∈ S.dom
  · rw [if_pos hi] at hr
    rw [hr]
    exact ⟨fun h => ⟨hi, h⟩, fun ⟨_, h⟩ => h⟩
  · rw [if_neg hi] at hr
    rw [hr]
    exact ⟨fun h => by omega, fun ⟨h, _⟩ => absurd h hi⟩

theorem zeroPts_nodup (rl : List ℕ) (n : ℕ) : (zeroPts rl n).Nodup :=
  (List.nodup_finRange n).filter _

/-- The positions of row `0`, numbered in increasing order. -/
noncomputable def row0Equiv {rl : List ℕ} (hrl : RowLabs e S label rl) (hq : 3 ≤ L.q) :
    Fin (zeroPts rl n).length ≃ {x : S.dom // domLab label x = ⟨0, by omega⟩} :=
  Equiv.ofBijective
    (fun β => ⟨⟨e.symm (zeroPts rl n)[β], ((mem_zeroPts hrl (by omega) _).1
        (List.getElem_mem β.2)).1⟩,
      Fin.ext ((mem_zeroPts hrl (by omega) _).1 (List.getElem_mem β.2)).2⟩)
    ⟨fun a b h => by
      have h1 : e.symm (zeroPts rl n)[a] = e.symm (zeroPts rl n)[b] :=
        congrArg (fun x : {x : S.dom // domLab label x = ⟨0, by omega⟩} => x.val.val) h
      exact Fin.ext ((zeroPts_nodup rl n).getElem_inj_iff.1 (e.symm.injective h1)),
    fun x => by
      have hm : e x.val.val ∈ zeroPts rl n := (mem_zeroPts hrl (by omega) _).2
        ⟨by rw [e.symm_apply_apply]; exact x.val.2, by
          rw [e.symm_apply_apply]; exact congrArg Fin.val x.2⟩
      obtain ⟨β, hβ, hβe⟩ := List.getElem_of_mem hm
      refine ⟨⟨β, hβ⟩, Subtype.ext (Subtype.ext ?_)⟩
      show e.symm (zeroPts rl n)[β] = x.val.val
      rw [hβe, e.symm_apply_apply]⟩

theorem row0Equiv_val {rl : List ℕ} (hrl : RowLabs e S label rl) (hq : 3 ≤ L.q)
    (β : Fin (zeroPts rl n).length) :
    ((row0Equiv hrl hq β).val.val : Ω) = e.symm (zeroPts rl n)[β] := rfl

end Coords

section Main

variable {Ω C : Type} {n : ℕ} {e : Ω ≃ Fin n} {S : State Ω C} {L : GiantLabels S}
  {label : Ω → Fin L.q}

theorem map_eq_finRange {α β : Type} (l : List α) (f : α → β) :
    l.map f = (List.finRange l.length).map fun i => f l[i] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem wt_rows_le {ws : List Val} {W : ℕ} (h : ∀ w ∈ ws, w.wt ≤ W) :
    (Val.list ws).wt ≤ 2 * (ws.length * W) + ws.length + 4 := by
  have h1 := wt_list_le ws
  have h2 : (ws.map Val.wt).sum ≤ ws.length * W := by
    have := List.sum_le_card_nsmul (ws.map Val.wt) W (by
      intro x hx; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact h w hw)
    simpa using this
  omega

set_option maxHeartbeats 3200000 in
/-- **The coordinate program.** If every window of length `kkOf q` without repeats has a lift,
the program returns the rows of pure coordinates `E` (Theorem A.17): row `j` lists the positions
`E (β, j)`. It calls **PointwiseStab** and **NormalizedFactor** once per window, `q` windows in
all. -/
theorem coords_spec (hst : GI.Cited.PointwiseStab) (hfac : GI.Cited.NormalizedFactor)
    {P : Program} {b jp jf : ℕ} (hb : P.HasAt b (coordFuns b jp jf))
    (hjp : P.prims[jp]? = some (pointwiseStabPrim hst))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {ps : List (Perm (Fin n) × Perm (Fin L.q))} (hps : PairGens e L S.G ps) {rl : List ℕ}
    (hrl : RowLabs e S label rl) (hnat : NaturalRows S L label) (hk : WinLen L.q (kkOf L.q))
    (hexW : ∀ t : List (Fin L.q), t.Nodup → t.length = kkOf L.q → ∃ g, WinLift S L label t g) :
    FunAll P b (.list [winCtx n L.q rl ps]) (fun w c =>
      ∃ E : Fin (zeroPts rl n).length × Fin L.q ≃ S.dom, PureCoords S L label E ∧
        w = coordsVal e S E ∧ c ≤ coordCost hst hfac (n + L.q + ps.length + 2)) := by
  classical
  -- the layout
  have hA : P.HasAt b (coordA b) := hb.left
  have hB : P.HasAt (b + 37) (liftWinFuns (b + 37) jp jf) := by
    have := hb.right; rwa [length_coordA] at this
  have hentry : P.funs[b]? = some (coordF b) := by
    simpa using (hA.block 0 (gs := [coordF b]) (by rfl)).single
  have hrg : P.HasAt (b + 1) (rangeFuns (b + 1)) := hA.block 1 (by rfl)
  have hwt : P.HasAt (b + 4) (mapFuns (b + 4) (b + 7)) := hA.block 4 (by rfl)
  have hws : P.funs[b + 7]? = some winStepF := (hA.block 7 (gs := [winStepF]) (by rfl)).single
  have hcm : P.funs[b + 8]? = some (commF (b + 9) (b + 13)) :=
    (hA.block 8 (gs := [commF (b + 9) (b + 13)]) (by rfl)).single
  have hcp : P.HasAt (b + 9) (composeFuns (b + 9)) := hA.block 9 (by rfl)
  have hiv : P.HasAt (b + 13) (invFuns (b + 13)) := hA.block 13 (by rfl)
  have hfi : P.HasAt (b + 25) (filterFuns (b + 25) (b + 28)) := hA.block 25 (by rfl)
  have hzt : P.funs[b + 28]? = some zeroTestF := (hA.block 28 (gs := [zeroTestF]) (by rfl)).single
  have hmp : P.HasAt (b + 29) (mapFuns (b + 29) (b + 32)) := hA.block 29 (by rfl)
  have hrw : P.funs[b + 32]? = some (rowF (b + 37) (b + 4) (b + 8) (b + 33)) :=
    (hA.block 32 (gs := [rowF (b + 37) (b + 4) (b + 8) (b + 33)]) (by rfl)).single
  have hga : P.HasAt (b + 33) (gatherFuns (b + 33)) := hA.block 33 (by rfl)
  -- names
  set kk := kkOf L.q with hkk
  set ctx := winCtx n L.q rl ps with hctx
  set inp := Val.list [ctx] with hinp
  set M := n + L.q + ps.length + 2 with hM
  have hq9 := hk.nine_le
  have hkq : kk ≤ L.q := by have := hk.le; have := hk.five; omega
  set cl : List Val := [.nat n, .nat L.q, natList rl, .list (ps.map pairV), pSplitCtx n L.q,
    encPerm (1 : Perm (Fin L.q)), encPerm (1 : Perm (Fin n))] with hcl
  have rd : ∀ (rest : List Val) (i : ℕ) (v : Val), cl[i]? = some v →
      Det P (inp :: rest) (cE i) v (4 * inp.wt + 20) := by
    intro rest i v h
    have hv : v ∈ cl := List.mem_of_getElem? h
    have hi : i < 7 := by
      obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 h
      simpa [hcl] using hi
    have d := Det.get' (Det.arg' (P := P) (vs := [ctx]) (rest := rest) (j := 0) rfl)
      (Det.nat i) h
    refine d.mono ?_
    have h1 : v.wt < (Val.list cl).wt := wt_le_wt_list hv
    have h1' : (Val.list cl).wt = ctx.wt := rfl
    have h2 : ctx.wt < inp.wt := wt_le_wt_list (by simp only [List.mem_cons, true_or])
    have h3 : (Val.list [ctx]).wt = inp.wt := rfl
    omega
  have a0 : ∀ rest : List Val, Det P (inp :: rest) (arg 0) ctx (2 * inp.wt + 5) := fun rest =>
    (Det.arg' (P := P) (vs := [ctx]) (rest := rest) (j := 0) rfl).mono (le_of_eq rfl)
  -- sizes
  have hIc : ctx.wt ≤ 300 * M ^ 3 := wt_winCtx_le hrl.1 hrl.le ps
  have hI : inp.wt ≤ 1000 * M ^ 3 := by
    have := wt_list1_le ctx
    have : 1 ≤ M ^ 3 := Nat.one_le_pow _ _ (by omega)
    have : (Val.list [ctx]).wt = inp.wt := rfl
    omega
  have hM2 : 2 ≤ M := by omega
  have hnM : n + 1 ≤ M := by omega
  have hqM : L.q + 2 ≤ M := by omega
  have p12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have p34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have p46 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn2 : (n + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hnM 2
  have hn3 : (n + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left hnM 3
  have hn4 : (n + 1) ^ 4 ≤ M ^ 4 := Nat.pow_le_pow_left hnM 4
  have hk2 : (kk + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hk3 : (kk + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hq2 : (L.q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have eLW : liftWinCost hst hfac (n + L.q + ps.length + 2) = liftWinCost hst hfac M := rfl
  have hctxI : ctx.wt < inp.wt := wt_le_wt_list (by simp only [List.mem_cons, true_or])
  -- step 0: the window length
  have dH := Det.arith' (op := .div) (Det.arith' (op := .add) (rd [] 1 _ rfl)
    (Det.nat (P := P) (env := [inp]) 1) (z := L.q + 1) rfl) (Det.nat (P := P) (env := [inp]) 2)
    (z := (L.q + 1) / 2) rfl
  have dkk := Det.arith' (op := .add)
    (Det.arith' (op := .sub) dH (Det.nat (P := P) (env := [inp]) 1) (z := (L.q + 1) / 2 - 1) rfl)
    (Det.arith' (op := .mod) dH (Det.nat (P := P) (env := [inp]) 2) (z := (L.q + 1) / 2 % 2) rfl)
    (z := kk) rfl
  refine FunAll.intro hentry (EvalAll.letE dkk fun _ _ h => ?_)
  obtain ⟨rfl, hc0⟩ := h
  -- step 1: `[0, …, kk - 1]`
  have d1 := Det.call (Det.var' (P := P) (env := [inp, .nat kk]) (i := 1) rfl) (range_det hrg kk)
  refine EvalAll.letE d1 fun _ _ h => ?_
  obtain ⟨rfl, hc1⟩ := h
  have wkk := wt_encPerm_le (1 : Perm (Fin kk))
  have wnk := wt_nat_le kk
  have wq := wt_nat_le L.q
  -- step 2: the lift `g₁` of the first window
  have dp1 := Det.mk4 (Det.nat (P := P) (env := [inp, .nat kk, encPerm (1 : Perm (Fin kk))]) 2)
    (Det.nat 3) (Det.nat 0) (rd [.nat kk, encPerm (1 : Perm (Fin kk))] 1 _ rfl)
  have dw1 := Det.call (Det.mk2 dp1 (Det.var' (P := P)
    (env := [inp, .nat kk, encPerm (1 : Perm (Fin kk))]) (i := 2) rfl))
    (winTab_spec hwt hws hk.bound1 hkq)
  have ew1 : winL L.q kk 2 3 0 L.q hk.bound1 = win1 hk := rfl
  rw [ew1] at dw1
  have hT1 : winTabK * (2 + 3 + 0 + L.q + kk + L.q + 10) ^ 3 ≤ winTabK * (125 * M ^ 3) := by
    apply Nat.mul_le_mul_left
    calc _ ≤ (5 * M) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 125 * M ^ 3 := by ring
  have wr1 := wt_rowsV_le (win1 hk) (by rw [length_win1]; exact hkq)
  have wp1 := wt_list4_le (.nat 2) (.nat 3) (.nat 0) (.nat L.q)
  have wp1' := wt_list2_le (Val.list [.nat 2, .nat 3, .nat 0, .nat L.q]) (encPerm (1 : Perm (Fin kk)))
  have wc1 := wt_list2_le ctx (rowsV (win1 hk))
  have w2 := wt_nat_le 2
  have w3 := wt_nat_le 3
  have w0 := wt_nat_le 0
  refine EvalAll.letE (Ra := fun w cw => ∃ g1 : Perm Ω, WinLift S L label (win1 hk) g1 ∧
      w = encPerm (toFin e g1) ∧
      cw ≤ 100 * inp.wt + 200 * M ^ 2 + winTabK * (125 * M ^ 3) + 500 + liftWinCost hst hfac M)
    (EvalAll.call_funAll (Det.mk2 (a0 _) dw1) fun v ca h => ?_) fun _ _ h => ?_
  · obtain ⟨rfl, hca⟩ := h
    exact (liftWin_spec hst hfac hB hjp hjf hps hrl (win1 hk) (win1_nodup hk)
      (by rw [length_win1]; have := hk.five; omega) (by rw [length_win1]; exact hkq)
      (hexW _ (win1_nodup hk) (length_win1 hk))).mono fun w cw ⟨g, hg, hw, hcw⟩ =>
        ⟨g, hg, hw, by have := wt_encPerm_le (toFin e g); rw [hw]; omega⟩
  obtain ⟨g1, hg1, rfl, hcg1⟩ := h
  -- step 3: the lift `h₁` of the second window
  set E3 : List Val := [inp, .nat kk, encPerm (1 : Perm (Fin kk)), encPerm (toFin e g1)] with hE3
  have dp2 := Det.mk4 (Det.nat (P := P) (env := E3) 1)
    (Det.arith' (op := .add) (Det.var' (P := P) (env := E3) (i := 1) (v := .nat kk) rfl)
      (Det.nat (P := P) (env := E3) 1) (z := kk + 1) rfl)
    (Det.nat 0) (rd [.nat kk, encPerm (1 : Perm (Fin kk)), encPerm (toFin e g1)] 1 _ rfl)
  have dw2 := Det.call (Det.mk2 dp2 (Det.var' (P := P) (env := E3) (i := 2) rfl))
    (winTab_spec hwt hws hk.bound2 hkq)
  have ew2 : winL L.q kk 1 (kk + 1) 0 L.q hk.bound2 = win2 hk := rfl
  rw [ew2] at dw2
  have hT2 : winTabK * (1 + (kk + 1) + 0 + L.q + kk + L.q + 10) ^ 3 ≤ winTabK * (125 * M ^ 3) := by
    apply Nat.mul_le_mul_left
    calc _ ≤ (5 * M) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 125 * M ^ 3 := by ring
  have wr2 := wt_rowsV_le (win2 hk) (by rw [length_win2]; exact hkq)
  have wp2 := wt_list4_le (.nat 1) (.nat (kk + 1)) (.nat 0) (.nat L.q)
  have wp2' := wt_list2_le (Val.list [.nat 1, .nat (kk + 1), .nat 0, .nat L.q])
    (encPerm (1 : Perm (Fin kk)))
  have wc2 := wt_list2_le ctx (rowsV (win2 hk))
  have w1 := wt_nat_le 1
  have wk1 := wt_nat_le (kk + 1)
  have wg1 := wt_encPerm_le (toFin e g1)
  refine EvalAll.letE (Ra := fun w cw => ∃ h1 : Perm Ω, WinLift S L label (win2 hk) h1 ∧
      w = encPerm (toFin e h1) ∧
      cw ≤ 100 * inp.wt + 200 * M ^ 2 + winTabK * (125 * M ^ 3) + 500 + liftWinCost hst hfac M)
    (EvalAll.call_funAll (Det.mk2 (a0 _) dw2) fun v ca h => ?_) fun _ _ h => ?_
  · obtain ⟨rfl, hca⟩ := h
    exact (liftWin_spec hst hfac hB hjp hjf hps hrl (win2 hk) (win2_nodup hk)
      (by rw [length_win2]; have := hk.five; omega) (by rw [length_win2]; exact hkq)
      (hexW _ (win2_nodup hk) (length_win2 hk))).mono fun w cw ⟨g, hg, hw, hcw⟩ =>
        ⟨g, hg, hw, by have := wt_encPerm_le (toFin e g); rw [hw]; omega⟩
  obtain ⟨h1, hh1, rfl, hch1⟩ := h
  -- step 4: `c = [g₁, h₁]`
  set E4 : List Val := E3 ++ [encPerm (toFin e h1)] with hE4
  have dc := Det.call (Det.mk2 (Det.var' (P := P) (env := E4) (i := 3) rfl)
    (Det.var' (P := P) (env := E4) (i := 4) rfl)) (comm_spec hcm hcp hiv (toFin e g1) (toFin e h1))
  have ec : encPerm (toFin e h1 * toFin e g1 * (toFin e h1)⁻¹ * (toFin e g1)⁻¹) =
      encPerm (toFin e (cOf g1 h1)) := by rw [cOf, toFin_comm]
  rw [ec] at dc
  refine EvalAll.letE dc fun _ _ h => ?_
  obtain ⟨rfl, hcc⟩ := h
  -- step 5: `c²`
  set E5 : List Val := E4 ++ [encPerm (toFin e (cOf g1 h1))] with hE5
  have dc2 := Det.call (Det.mk2 (Det.var' (P := P) (env := E5) (i := 5) rfl)
    (Det.var' (P := P) (env := E5) (i := 5) rfl)) (compose_spec hcp (toFin e (cOf g1 h1))
      (toFin e (cOf g1 h1)))
  rw [← map_mul] at dc2
  refine EvalAll.letE dc2 fun _ _ h => ?_
  obtain ⟨rfl, hcc2⟩ := h
  -- step 6: the positions of row `0`
  set E6 : List Val := E5 ++ [encPerm (toFin e (cOf g1 h1 * cOf g1 h1))] with hE6
  have dr0 := Det.call (Det.mk2 (rd (E6.drop 1) 2 _ rfl) (rd (E6.drop 1) 6 _ rfl))
    (zeroList_spec hfi hzt rl hrl.1)
  refine EvalAll.letE dr0 fun _ _ h => ?_
  obtain ⟨rfl, hcr0⟩ := h
  -- step 7: the rows
  set r0 := (zeroPts rl n).map Fin.val with hr0
  set E7 : List Val := E6 ++ [natList r0] with hE7
  have drc := Det.mk4 (a0 (E7.drop 1)) (Det.var' (P := P) (env := E7) (i := 2) rfl)
    (Det.mk2 (Det.var' (P := P) (env := E7) (i := 5) rfl)
      (Det.var' (P := P) (env := E7) (i := 6) rfl))
    (Det.var' (P := P) (env := E7) (i := 7) rfl)
  have darg := Det.mk2 drc (rd (E7.drop 1) 5 _ rfl)
  set rc := rowCtx n L.q kk rl ps (toFin e (cOf g1 h1)) (toFin e (cOf g1 h1 * cOf g1 h1)) r0
    with hrc
  have erc : Val.list [ctx, encPerm (1 : Perm (Fin kk)), .list [encPerm (toFin e (cOf g1 h1)),
      encPerm (toFin e (cOf g1 h1 * cOf g1 h1))], natList r0] = rc := rfl
  rw [erc] at darg
  refine EvalAll.call_funAll darg fun v ca h => ?_
  obtain ⟨rfl, hca⟩ := h
  have e1q : encPerm (1 : Perm (Fin L.q)) =
      .list ((List.finRange L.q).map fun j : Fin L.q => Val.nat j) := rfl
  rw [e1q]
  refine (map_spec hmp (c := rc) (xs := (List.finRange L.q).map fun j : Fin L.q => Val.nat j)
    (R := fun x w => ∀ j : Fin L.q, x = .nat j → ∃ hj : Perm Ω,
      (3 ≤ (j : ℕ) → WinLift S L label (winJ hk j) hj) ∧
      w = natList ((zeroPts rl n).map fun i =>
        ((toFin e (rhoOf g1 h1 (fun _ => hj) j) i : Fin n) : ℕ)))
    (B := fun _ => rowStepCost hst hfac M) ?_).mono ?_
  · intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    refine (rowStep_spec hst hfac hrw hB hjp hjf hwt hws hcm hcp hiv hga hps hrl hk g1 h1 j
      (fun h3 => hexW _ (winJ_nodup hk j h3) (length_winJ hk j))).mono
      fun w cw ⟨hj, hjl, hw, hcw⟩ => ⟨fun j' hj' => ?_, hcw⟩
    have : j' = j := Fin.ext (by injection hj' with h; exact h.symm)
    subst this
    exact ⟨hj, hjl, hw⟩
  rintro w cw ⟨ws, rfl, hR, hcw⟩
  have hlen : ws.length = L.q := by have := hR.length_eq; simpa using this.symm
  have hjx : ∀ j : Fin L.q, ∃ hj : Perm Ω, (3 ≤ (j : ℕ) → WinLift S L label (winJ hk j) hj) ∧
      ws[(j : ℕ)]'(by omega) = natList ((zeroPts rl n).map fun i =>
        ((toFin e (rhoOf g1 h1 (fun _ => hj) j) i : Fin n) : ℕ)) := by
    intro j
    have := hR.get (i := j) (by simp) (by omega)
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange, Fin.cast_mk] at this
    exact this j rfl
  choose hs hsl hsw using hjx
  have H : Lifts (S := S) (label := label) hk g1 h1 hs := ⟨hg1, hh1, hsl⟩
  have hq3 : 3 ≤ L.q := by omega
  set row0 := row0Equiv hrl hq3 with hrow0
  refine ⟨(H.cycleData hnat).coordsOf row0, H.pureCoords hnat row0, ?_, ?_⟩
  · -- the value
    unfold coordsVal
    congr 1
    apply List.ext_getElem (by simp [hlen])
    intro j hj1 hj2
    have hjq : j < L.q := by simpa using hj2
    simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
    rw [hsw ⟨j, hjq⟩]
    unfold natList
    congr 1
    rw [map_eq_finRange (zeroPts rl n), List.map_map, List.map_map]
    apply List.map_congr_left
    intro β _
    simp only [Function.comp_apply, Val.nat.injEq]
    rw [H.coords_val hnat row0 β ⟨j, hjq⟩, row0Equiv_val]
    have hr : rhoOf g1 h1 (fun _ => hs ⟨j, hjq⟩) ⟨j, hjq⟩ =
        rhoOf g1 h1 hs ⟨j, hjq⟩ := by simp only [rhoOf]
    rw [hr]
    simp [Equiv.permCongr_apply]
  · -- the cost
    have hr0b : ∀ r ∈ r0, r ≤ n := by
      intro r hr; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr; exact i.2.le
    have hr0l : r0.length ≤ n := by
      rw [hr0, List.length_map]; exact (List.length_filter_le _ _).trans (by simp)
    have hW : ∀ w ∈ ws, w.wt ≤ 5 * M ^ 2 := by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
      rw [hsw ⟨j, by omega⟩]
      refine (wt_natList_le_sq (B := n) ?_ ?_).trans (by omega)
      · intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact (Fin.isLt _).le
      · rw [List.length_map]; rw [hr0, List.length_map] at hr0l; exact hr0l
    have hWs : (Val.list ws).wt ≤ 20 * M ^ 3 := by
      have := wt_rows_le hW
      have : ws.length * (5 * M ^ 2) ≤ M * (5 * M ^ 2) := Nat.mul_le_mul (by omega) le_rfl
      have : M * (5 * M ^ 2) = 5 * M ^ 3 := by ring
      omega
    have hrcw : rc.wt ≤ 1000 * M ^ 3 :=
      wt_rowCtx_le hrl.1 hrl.le ps hkq _ _ r0 hr0b hr0l
    have w1q := wt_encPerm_le (1 : Perm (Fin L.q))
    have hxs : (Val.list ((List.finRange L.q).map fun j : Fin L.q => Val.nat j)).wt ≤ 4 * M ^ 2 := by
      have : (Val.list ((List.finRange L.q).map fun j : Fin L.q => Val.nat j)).wt =
        (encPerm (1 : Perm (Fin L.q))).wt := rfl
      omega
    have hmap : mapK * (((List.finRange L.q).map fun j : Fin L.q => Val.nat j).length + 1) *
        ((Val.list [rc, .list ((List.finRange L.q).map fun j : Fin L.q => Val.nat j)]).wt +
          (Val.list ws).wt + 1) ≤ mapK * M * (3000 * M ^ 3) := by
      have := wt_list2_le rc (.list ((List.finRange L.q).map fun j : Fin L.q => Val.nat j))
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by simp; omega)) (by omega)
    have hsum : (((List.finRange L.q).map fun j : Fin L.q => Val.nat j).map
        fun _ => rowStepCost hst hfac M).sum ≤ M * rowStepCost hst hfac M := by
      simp only [List.map_map, List.map_const', List.sum_replicate, smul_eq_mul,
        List.length_finRange, Function.comp_def]
      exact Nat.mul_le_mul_right _ (by omega)
    have hRS : rowStepCost hst hfac M = liftWinCost hst hfac M + 10000000000000 * M ^ 6 := rfl
    have hco : coordCost hst hfac M = M * rowStepCost hst hfac M + 2 * rowStepCost hst hfac M +
        1000000000000000 * M ^ 6 := by unfold coordCost; ring
    have hm1 : mapK * M * (3000 * M ^ 3) = 3000000 * M ^ 4 := by simp only [mapK]; ring
    -- the row-`0` filter
    have hz1 := wt_list2_le (natList rl) (encPerm (1 : Perm (Fin n)))
    have hz2 : (natList rl).wt < ctx.wt := wt_le_wt_list (by simp)
    have w1n := wt_encPerm_le (1 : Perm (Fin n))
    have hz3 : zeroFK * ((Val.list [natList rl, encPerm (1 : Perm (Fin n))]).wt + 1) ^ 2 ≤
        zeroFK * (491401 * M ^ 6) := by
      apply Nat.mul_le_mul_left
      calc _ ≤ (701 * M ^ 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 491401 * M ^ 6 := by ring
    have hz4 : (natList r0).wt ≤ 5 * M ^ 2 :=
      (wt_natList_le_sq hr0b hr0l).trans (by omega)
    -- the commutators
    have wc := wt_encPerm_le (toFin e (cOf g1 h1))
    have wc2 := wt_encPerm_le (toFin e (cOf g1 h1 * cOf g1 h1))
    have wh1 := wt_encPerm_le (toFin e h1)
    have l1 := wt_list2_le (encPerm (toFin e g1)) (encPerm (toFin e h1))
    have l2 := wt_list2_le (encPerm (toFin e (cOf g1 h1))) (encPerm (toFin e (cOf g1 h1)))
    have l3 := wt_list2_le (encPerm (toFin e (cOf g1 h1))) (encPerm (toFin e (cOf g1 h1 * cOf g1 h1)))
    have l4 := wt_list4_le ctx (encPerm (1 : Perm (Fin kk)))
      (.list [encPerm (toFin e (cOf g1 h1)), encPerm (toFin e (cOf g1 h1 * cOf g1 h1))])
      (natList r0)
    have l5 := wt_list2_le rc (encPerm (1 : Perm (Fin L.q)))
    have hcm4 := Nat.mul_le_mul_left commK hn4
    have hpm3 := Nat.mul_le_mul_left permK hn3
    have hrg3 := Nat.mul_le_mul_left 8000 hk3
    have hkk1 := wt_nat_le (L.q + 1)
    have hkk2 := wt_nat_le ((L.q + 1) / 2)
    have hkk3 := wt_nat_le ((L.q + 1) / 2 - 1)
    have hkk4 := wt_nat_le ((L.q + 1) / 2 % 2)
    have hkk5 : (L.q + 1) / 2 % 2 ≤ 1 := by omega
    rw [hco]
    simp only [winTabK, commK, permK, zeroFK, mapK] at *
    omega

/-- **The coordinate program at the threshold** (item 1 of `Iface.RowSpec`). If the row count
`q` is at least `2 max(8, 2 + log₂ s) + 3`, where `s` bounds the size `f > 0` of row `0`, every
window has a lift (`winLift_exists`, through the cited `TransitiveAffected`), so the program of
`coords_spec` returns pure coordinates. `RowForm.ofPure` turns them into a row form whose map is
the returned `E`. -/
theorem coords_spec_of_thr (hcite : GI.Cited.TransitiveAffected) [Finite Ω]
    (hst : GI.Cited.PointwiseStab) (hfac : GI.Cited.NormalizedFactor)
    {P : Program} {b jp jf : ℕ} (hb : P.HasAt b (coordFuns b jp jf))
    (hjp : P.prims[jp]? = some (pointwiseStabPrim hst))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {ps : List (Perm (Fin n) × Perm (Fin L.q))} (hps : PairGens e L S.G ps) {rl : List ℕ}
    (hrl : RowLabs e S label rl) (hnat : NaturalRows S L label) {f s : ℕ} (hfs : f ≤ s)
    (hfpos : 0 < f) (hthr : 2 * max 8 (2 + Real.logb 2 s) + 3 ≤ (L.q : ℝ))
    (hf : ∀ [Fintype S.dom], Fintype.card {x : S.dom // label x = ⟨0, by
      have := (kkOf_thr hfs hfpos hthr).1.nine_le; omega⟩} = f) :
    FunAll P b (.list [winCtx n L.q rl ps]) (fun w c =>
      ∃ E : Fin (zeroPts rl n).length × Fin L.q ≃ S.dom, PureCoords S L label E ∧
        w = coordsVal e S E ∧ c ≤ coordCost hst hfac (n + L.q + ps.length + 2)) := by
  obtain ⟨hk, hlt⟩ := kkOf_thr hfs hfpos hthr
  refine coords_spec hst hfac hb hjp hjf hps hrl hnat hk fun t hnd hlen => ?_
  have h9 := hk.nine_le
  exact winLift_exists hcite hnat (by omega) t hnd (hlen ▸ hk.five) (hlen ▸ hk.odd) f hf
    (by rw [hlen]; exact hlt)

end Main

end GI.Impl
