import Workspace.Impl.RowWin
import Workspace.Impl.AggStab

/-!
# Lifting a window, as a program

For a window `t` (a list of labels without repeats), the program `liftWinF` finds an element
`g ∈ G` whose label image is the cycle of `t` and which fixes every point of the domain whose
label is not in `t` (`WinLift`). The steps:

1. the cycle `σ` of `t`, as a permutation value (`cycTab_spec`);
2. the positions `X` of the domain whose label `σ` fixes (`outList_spec`);
3. the graph pairs of `G ∩ Fix(X)`, by one call of the cited task **PointwiseStab**
   (`graphStabL_spec`);
4. a lift of `σ` in that group, by one call of the cited task **NormalizedFactor**
   (`liftLab_spec`).

When some lift of `t` exists, every element of `G ∩ Fix(X)` with label image `σ` is a lift
(`liftWin_spec`). The existence comes from `winLift_exists` (Lemma LG2).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup encPts gens pointwiseStab PointwiseStab NormalizedFactor)

variable {k q : ℕ}

/-! ### Pairs `(a, 1)` -/

/-- On `[1_q, [a, b]]`: `[a, 1_q]`. -/
def fstStepF : Expr := mk2 (.get (arg 1) (.nat 0)) (arg 0)

theorem pairV_fstOne (p : Perm (Fin k) × Perm (Fin q)) :
    pairV (fstOne k q p) = .list [encPerm p.1, encPerm (1 : Perm (Fin q))] := rfl

theorem fstStep_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some fstStepF)
    (p : Perm (Fin k) × Perm (Fin q)) :
    FunDet P f (.list [encPerm (1 : Perm (Fin q)), pairV p]) (pairV (fstOne k q p))
      (20 * (Val.list [encPerm (1 : Perm (Fin q)), pairV p]).wt + 40) := by
  set inp := Val.list [encPerm (1 : Perm (Fin q)), pairV p]
  have g0 := Det.arg' (P := P) (vs := [encPerm (1 : Perm (Fin q)), pairV p]) (rest := []) (j := 0)
    rfl
  have g1 := Det.arg' (P := P) (vs := [encPerm (1 : Perm (Fin q)), pairV p]) (rest := []) (j := 1)
    rfl
  have ga := Det.get' g1 (Det.nat 0) (vs := [encPerm p.1, encPerm p.2]) (v := encPerm p.1) rfl
  have d := Det.mk2 ga g0
  rw [← pairV_fstOne] at d
  refine FunDet.intro hf (d.mono ?_)
  have w1 : (encPerm p.1).wt < (pairV p).wt := wt_le_wt_list (by simp [pairV])
  have w2 : (pairV p).wt < inp.wt := wt_le_wt_list (by simp [inp])
  have w3 : (encPerm (1 : Perm (Fin q))).wt < inp.wt := wt_le_wt_list (by simp [inp])
  have w4 := wt_list2_le (encPerm p.1) (encPerm (1 : Perm (Fin q)))
  have e4 : (pairV (fstOne k q p)).wt = (Val.list [encPerm p.1, encPerm (1 : Perm (Fin q))]).wt :=
    rfl
  have e5 : (Val.list [encPerm p.1, encPerm p.2]).wt = (pairV p).wt := rfl
  have e6 : (Val.list [encPerm (1 : Perm (Fin q)), pairV p]).wt = inp.wt := rfl
  omega

/-- `map fstStep` at `b` (four functions). -/
def fstMapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [fstStepF]

theorem fstMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (fstMapFuns b))
    (ps : List (Perm (Fin k) × Perm (Fin q))) :
    FunDet P b (.list [encPerm (1 : Perm (Fin q)), .list (ps.map pairV)])
      (.list ((onePairs ps).map pairV))
      (ps.length * (40 * (4 * (q + 1) ^ 2 + 22 * (k + q + 1) ^ 2) + 400) + mapK * (ps.length + 1) *
        ((Val.list [encPerm (1 : Perm (Fin q)), .list (ps.map pairV)]).wt +
          (Val.list ((onePairs ps).map pairV)).wt + 1)) := by
  have hf : P.funs[b + 3]? = some fstStepF := by
    simpa using (h.block 3 (gs := [fstStepF]) (by rfl)).single
  have := mapList_spec h.left ps pairV (fun p => pairV (fstOne k q p))
    (c := encPerm (1 : Perm (Fin q))) (B := 40 * (4 * (q + 1) ^ 2 + 22 * (k + q + 1) ^ 2) + 400)
    (fun a _ a' _ he => by rw [pairV_injective he]) (fun p _ => (fstStep_spec hf p).mono (by
      have h1 := wt_list2_le (encPerm (1 : Perm (Fin q))) (pairV p)
      have h2 := wt_encPerm_le (1 : Perm (Fin q))
      have h3 := wt_pairV_le p
      omega))
  have e : (ps.map fun p => pairV (fstOne k q p)) = (onePairs ps).map pairV := by
    simp [onePairs]
  rw [e] at this
  exact this

/-! ### The group value of a list of pairs -/

/-- On `[[k, q], pairs]`: the group value of the encoded pairs. `pEncMap` sits at `en`,
`mkGroup` at `mk`. -/
def grpF (en mk : ℕ) : Expr :=
  .call mk (mk2 (.arith .add (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)))
    (.call en (mk2 (.get (arg 0) (.nat 0)) (arg 1))))

/-- The cost constant of `grpF`. -/
def grpK : ℕ := 1000000000000

theorem wt_encGroup_pairs_le (ps : List (Perm (Fin k) × Perm (Fin q))) :
    (encGroup (ps.map encPair)).wt ≤ 40 * pM k q ps ^ 4 := by
  set M := pM k q ps with hM
  have sGD2 : ((ps.map encPair).length + 2) * (k + q + 1) ≤ M ^ 2 := by
    have := Nat.mul_le_mul (show (ps.map encPair).length + 2 ≤ M by
        simp only [List.length_map, hM, pM]; omega)
      (show k + q + 1 ≤ M by simp only [hM, pM]; omega)
    have e : M * M = M ^ 2 := by ring
    omega
  have h1 := wt_encGroup_le (ps.map encPair)
  have h2 := Nat.pow_le_pow_left sGD2 2
  have e : (M ^ 2) ^ 2 = M ^ 4 := by ring
  omega

theorem grp_spec {P : Program} {f en mk : ℕ} (hf : P.funs[f]? = some (grpF en mk))
    (hen : P.HasAt en (pEncMapFuns en)) (hmk : P.HasAt mk (mkGroupFuns mk))
    (ps : List (Perm (Fin k) × Perm (Fin q))) :
    FunDet P f (.list [.list [.nat k, .nat q], .list (ps.map pairV)]) (encGroup (ps.map encPair))
      (grpK * pM k q ps ^ 6) := by
  have gk : ∀ rest : List Val, Det P (Val.list [.list [.nat k, .nat q], .list (ps.map pairV)] :: rest) (.get (arg 0) (.nat 0)) (.nat k) _ :=
    fun rest => Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV)])
      (rest := rest) (j := 0) rfl) (Det.nat 0) (v := .nat k) rfl
  have gq : ∀ rest : List Val, Det P (Val.list [.list [.nat k, .nat q], .list (ps.map pairV)] :: rest) (.get (arg 0) (.nat 1)) (.nat q) _ :=
    fun rest => Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat q], .list (ps.map pairV)])
      (rest := rest) (j := 0) rfl) (Det.nat 1) (v := .nat q) rfl
  have d1 := Det.call (Det.mk2 (gk []) (Det.arg' (P := P) (vs := [.list [.nat k, .nat q],
    .list (ps.map pairV)]) (rest := []) (j := 1) rfl)) (pEncMap_spec hen ps)
  have hG2 := mkGroup_spec hmk (ps.map encPair)
  have eE : Val.list ((ps.map encPair).map encPerm) = Val.list (ps.map fun p => encPerm (encPair p)) := by simp
  rw [eE] at hG2
  have d2 := Det.call (Det.mk2 (Det.arith' (op := .add) (gk []) (gq []) (z := k + q) rfl) d1) hG2
  refine FunDet.intro hf (d2.mono ?_)
  -- the cost
  have bps : (Val.list (ps.map pairV)).wt ≤ 50 * pM k q ps ^ 3 := wt_pairList_le ps
  have bGD : (encGroup (ps.map encPair)).wt ≤ 40 * pM k q ps ^ 4 := wt_encGroup_pairs_le ps
  have hM2 : 2 ≤ pM k q ps := by simp only [pM]; omega
  have hkq : k + q + 1 ≤ pM k q ps := by simp only [pM]; omega
  have hpl : ps.length + 2 ≤ pM k q ps := by simp only [pM]; omega
  generalize pM k q ps = M at *
  have m2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have m3 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have m4 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have m6 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have wk := wt_nat_le k
  have wq := wt_nat_le q
  have bkq := wt_list2_le (.nat k) (.nat q)
  have bA := wt_list2_le (.list [.nat k, .nat q]) (.list (ps.map pairV))
  have bA1 := wt_list2_le (.nat k) (.list (ps.map pairV))
  have bE : (Val.list (ps.map fun p => encPerm (encPair p))).wt ≤ 9 * M ^ 3 + 4 := by
    have h1 := wt_list_map_le ps (fun p => encPerm (encPair p))
      (W := 4 * (k + q + 1) ^ 2) fun p _ => wt_encPerm_le _
    have h2 : ps.length * (2 * (4 * (k + q + 1) ^ 2) + 1) ≤ M * (9 * M ^ 2) :=
      Nat.mul_le_mul (by omega) (by have := Nat.pow_le_pow_left hkq 2; omega)
    have h3 : M * (9 * M ^ 2) = 9 * M ^ 3 := by ring
    omega
  have bE1 := wt_list2_le (.nat (k + q)) (Val.list (ps.map fun p => encPerm (encPair p)))
  have cE : ps.length * pEncCost k q ≤ natStepK * M ^ 4 := by
    have h2 : ps.length * pEncCost k q ≤ M * (natStepK * M ^ 3) :=
      Nat.mul_le_mul (by omega) (by
        show natStepK * (k + q + 1) ^ 3 ≤ _; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkq 3))
    have e2 : M * (natStepK * M ^ 3) = natStepK * M ^ 4 := by ring
    omega
  have cE2 : mapK * (ps.length + 1) * ((Val.list [.nat k, .list (ps.map pairV)]).wt + (Val.list (ps.map fun p => encPerm (encPair p))).wt + 1)
      ≤ mapK * M * (1000 * M ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have sGD2 : ((ps.map encPair).length + 2) * (k + q + 1) ≤ M ^ 2 := by
    have := Nat.mul_le_mul (show (ps.map encPair).length + 2 ≤ M by simp; omega) hkq
    have e : M * M = M ^ 2 := by ring
    omega
  have cGD : mkGroupK * (((ps.map encPair).length + 2) * (k + q + 1)) ^ 3 ≤ mkGroupK * M ^ 6 := by
    have h2 := Nat.pow_le_pow_left sGD2 3
    have e : (M ^ 2) ^ 3 = M ^ 6 := by ring
    exact Nat.mul_le_mul_left _ (e ▸ h2)
  have e1 : mapK * M * (1000 * M ^ 3) = 10 ^ 6 * M ^ 4 := by simp only [mapK]; ring
  have hl : (ps.map encPair).length = ps.length := List.length_map _
  have wkq := wt_nat_le (k + q)
  have hn : natStepK = 1000000000 := by simp [natStepK]
  have hn2 : (10:ℕ) ^ 6 = 1000000 := by norm_num
  rw [hn] at cE
  rw [hn2] at e1
  simp only [grpK, mkGroupK] at *
  omega

/-! ### The pairs of the label value are a graph form of `G` -/

section Graph

variable {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- Pairs `(g, π g)` whose first parts generate `G` generate the graph of `G`. -/
theorem pairGens_of_fst {ps : List (Perm (Fin k) × Perm (Fin L.q))}
    (hgen : gens (ps.map Prod.fst) = groupFin e S.G)
    (hπ : ∀ p ∈ ps, ∀ hg : (toFin e).symm p.1 ∈ S.G,
      ((L.π ⟨(toFin e).symm p.1, hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) = p.2) :
    PairGens e L S.G ps := by
  have hle : Subgroup.closure {p | p ∈ ps} ≤ graphOf e L S.G := by
    rw [Subgroup.closure_le]
    intro p hp
    have h1 : p.1 ∈ groupFin e S.G := hgen ▸ Subgroup.subset_closure (List.mem_map_of_mem hp)
    obtain ⟨g, hg, hgp⟩ := Subgroup.mem_map.1 h1
    have hs : (toFin e).symm p.1 = g := by rw [← hgp]; exact (toFin e).symm_apply_apply g
    have hg' : (toFin e).symm p.1 ∈ S.G := hs ▸ hg
    have h2 := hπ p hp hg'
    refine (mem_graphOf e L).2 ⟨(toFin e).symm p.1, hg', hg', (toFin e).apply_symm_apply p.1, h2⟩
  refine le_antisymm hle fun p hp => ?_
  obtain ⟨g, hg, -, h1, -⟩ := (mem_graphOf e L).1 hp
  have hfst : p.1 ∈ gens (ps.map Prod.fst) := hgen ▸ ⟨g, hg, h1⟩
  rw [gens_fst] at hfst
  obtain ⟨p', hp', hfst'⟩ := Subgroup.mem_map.1 hfst
  have := graph_fst_inj e L (hle hp') hp hfst'
  exact this ▸ hp'

end Graph

/-! ### Row labels as positions -/

section Labels

variable {Ω C : Type} (e : Ω ≃ Fin k) (S : State Ω C) {q : ℕ} (label : Ω → Fin q)

open Classical in
/-- `rl` lists the row label of each position: `label` on the domain, `q` off it. -/
def RowLabs (rl : List ℕ) : Prop :=
  rl.length = k ∧ ∀ i : Fin k, rl.getD i 0 = if e.symm i ∈ S.dom then (label (e.symm i) : ℕ) else q

variable {e S label}

open Classical in
theorem RowLabs.le {rl : List ℕ} (h : RowLabs e S label rl) : ∀ r ∈ rl, r ≤ q := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have := h.2 ⟨i, h.1 ▸ hi⟩
  rw [List.getD_eq_getElem _ _ hi] at this
  rw [this]
  split_ifs
  · exact (label _).2.le
  · exact le_rfl

open Classical in
/-- A position outside the window lies in the domain, with a label fixed by `σ`. -/
theorem mem_outPts {rl : List ℕ} (h : RowLabs e S label rl) (σ : Perm (Fin q)) (i : Fin k) :
    i ∈ outPts (n := k) rl σ ↔ ∃ hi : e.symm i ∈ S.dom, σ (label (e.symm i)) = label (e.symm i) := by
  have hr := h.2 i
  simp only [outPts, List.mem_filter, List.mem_finRange, true_and, outP]
  by_cases hi : e.symm i ∈ S.dom
  · rw [if_pos hi] at hr
    have hlt : rl.getD i 0 < q := by rw [hr]; exact (label _).2
    rw [dif_pos hlt]
    have heq : (⟨rl.getD i 0, hlt⟩ : Fin q) = label (e.symm i) := Fin.ext hr
    rw [heq, hr, decide_eq_true_iff]
    exact ⟨fun h' => ⟨hi, Fin.ext h'⟩, fun ⟨_, h'⟩ => congrArg Fin.val h'⟩
  · rw [if_neg hi] at hr
    have hlt : ¬ rl.getD i 0 < q := by omega
    rw [dif_neg hlt]
    simp only [Bool.false_eq_true, false_iff, not_exists]
    exact fun h' => absurd h' hi

theorem length_outPts (rl : List ℕ) (σ : Perm (Fin q)) : (outPts (n := k) rl σ).length ≤ k := by
  unfold outPts
  exact (List.length_filter_le _ _).trans (by simp)

end Labels

/-! ### The program -/

/-- The context of the window lifts: `[k, q, rl, pairs, splitCtx, 1_q, 1_k]`. -/
def winCtx (k q : ℕ) (rl : List ℕ) (ps : List (Perm (Fin k) × Perm (Fin q))) : Val :=
  .list [.nat k, .nat q, natList rl, .list (ps.map pairV), pSplitCtx k q,
    encPerm (1 : Perm (Fin q)), encPerm (1 : Perm (Fin k))]

/-- Entry `i` of the context (entry `0` of the argument). -/
def cE (i : ℕ) : Expr := .get (arg 0) (.nat i)

/-- **The window lift**, on `[ctx, t]`. -/
def liftWinF (b : ℕ) : Expr :=
  .letE (.call (b + 1) (mk2 (arg 1) (cE 5)))
  (.letE (.call (b + 9) (mk2 (mk2 (cE 2) (.var 1)) (cE 6)))
  (.letE (.call (b + 13) (mk3 (mk2 (cE 0) (cE 1)) (cE 3) (.var 2)))
  (.call (b + 70) (mk2 (mk4 (cE 0) (.call (b + 80) (mk2 (mk2 (cE 0) (cE 1)) (.var 3)))
      (.call (b + 80) (mk2 (mk2 (cE 0) (cE 1)) (.call (b + 66) (mk2 (cE 5) (.var 3)))))
      (cE 4)) (.var 1)))))

/-- The first part of the window lift module (46 functions). -/
def winA (b jp : ℕ) : List Expr :=
  [liftWinF b] ++ mapFuns (b + 1) (b + 4) ++ [cycStepF (b + 5)] ++ findEqFuns (b + 5) ++
    filterFuns (b + 9) (b + 12) ++ [outTestF] ++ graphStabFuns (b + 13) jp

/-- The second part of the window lift module (35 functions, from `b + 46`). -/
def winB (b jf : ℕ) : List Expr :=
  pEncMapFuns (b + 46) ++ mkGroupFuns (b + 59) ++ fstMapFuns (b + 66) ++
    [liftLabF (b + 49) (b + 71) jf] ++ pSplitFuns (b + 71) ++ [grpF (b + 46) (b + 59)]

theorem length_winA (b jp : ℕ) : (winA b jp).length = 46 := rfl

/-- The window lift module at `b` (81 functions), with the cited primitives at `jp`
(PointwiseStab) and `jf` (NormalizedFactor). -/
def liftWinFuns (b jp jf : ℕ) : List Expr := winA b jp ++ winB b jf

/-- The constant of the window lift. -/
def liftWinK : ℕ := 10 ^ 30

/-- The cost bound of the window lift, with `M = k + q + |ps| + 2`. -/
noncomputable def liftWinCost (hst : PointwiseStab) (hfac : NormalizedFactor) (M : ℕ) : ℕ :=
  (pointwiseStabPrim hst).c * (100 * M ^ 4 + 2) ^ (pointwiseStabPrim hst).k +
    liftLabCost (normalizedFactorPrim hfac) (2 * M ^ 2) + liftWinK * M ^ 12

theorem liftLabCost_mono (pf : Prim) {m m' : ℕ} (h : m ≤ m') :
    liftLabCost pf m ≤ liftLabCost pf m' := by
  unfold liftLabCost
  have h4 := Nat.pow_le_pow_left h 4
  have h6 := Nat.pow_le_pow_left h 6
  have := Nat.pow_le_pow_left (show 2000 * m ^ 4 + 2 ≤ 2000 * m' ^ 4 + 2 by omega) pf.k
  have := Nat.mul_le_mul_left pf.c this
  have := Nat.mul_le_mul_left liftLabK h6
  omega

theorem wt_encPts_le' {X : List (Fin k)} (hX : X.length ≤ k) : (encPts X).wt ≤ 3 * (k + 2) ^ 2 + 4 := by
  have h1 := wt_list_map_le X (fun i : Fin k => Val.nat i.val) (W := k + 2) fun i _ => by
    show (Val.nat (i : ℕ)).wt ≤ k + 2; have := wt_nat_le (i : ℕ); have := i.isLt; omega
  have h2 : X.length * (2 * (k + 2) + 1) ≤ (k + 2) * (3 * (k + 2)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : (k + 2) * (3 * (k + 2)) = 3 * (k + 2) ^ 2 := by ring
  have h4 : 1 ≤ (k + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [encPts_eq]
  omega

theorem wt_winCtx_le {rl : List ℕ} (hl : rl.length = k) (hrl : ∀ r ∈ rl, r ≤ q)
    (ps : List (Perm (Fin k) × Perm (Fin q))) :
    (winCtx k q rl ps).wt ≤ 300 * pM k q ps ^ 3 := by
  have hM2 : 2 ≤ pM k q ps := by simp only [pM]; omega
  have hkq : k + q + 1 ≤ pM k q ps := by simp only [pM]; omega
  have h1 : (natList rl).wt ≤ 5 * (k + q + 1) ^ 2 :=
    wt_natList_le_sq (fun r hr => (hrl r hr).trans (by omega)) (by omega)
  have h2 := wt_pairList_le ps
  have a3 := wt_encPerm_le (1 : Perm (Fin k))
  have a4 := wt_encPerm_le (1 : Perm (Fin q))
  have a1 := wt_list2_le (encPerm (1 : Perm (Fin k))) (encPerm (1 : Perm (Fin q)))
  have a2 := wt_list2_le (.nat k) (idsVal k q)
  have wk := wt_nat_le k
  have wq := wt_nat_le q
  have hc := wt_list_le [.nat k, .nat q, natList rl, .list (ps.map pairV), pSplitCtx k q,
    encPerm (1 : Perm (Fin q)), encPerm (1 : Perm (Fin k))]
  simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hc
  have e1 : (pSplitCtx k q).wt = (Val.list [.nat k, idsVal k q]).wt := rfl
  have e2 : (idsVal k q).wt =
    (Val.list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))]).wt := rfl
  generalize pM k q ps = M at *
  have b1 : (k + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have b2 : (q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have b3 : (k + q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have b4 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have b5 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold winCtx
  omega

section Lift

variable {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}

/-- The positions outside a window are fixed by every lift of the window. -/
theorem winLift_fixPos {rl : List ℕ} (hrl : RowLabs e S label rl) {t : List (Fin L.q)}
    (hnd : t.Nodup) (h2 : 2 ≤ t.length) {g : Perm Ω} (hg : WinLift S L label t g) :
    g ∈ fixPos (e := e) (outPts (n := k) rl t.formPerm) := by
  intro i hi
  obtain ⟨hd, hfix⟩ := (mem_outPts hrl _ i).1 hi
  have hnot : label (e.symm i) ∉ t := fun hm =>
    (formPerm_ne_iff t hnd h2 _).2 hm hfix
  have := hg.fix _ hd hnot
  show e (g (e.symm i)) = i
  rw [this, e.apply_symm_apply]

/-- An element of `G ∩ Fix(X)` whose label image is the window cycle is a lift. -/
theorem winLift_of_fixPos {rl : List ℕ} (hrl : RowLabs e S label rl) {t : List (Fin L.q)}
    {g : Perm Ω} (hg : g ∈ S.G)
    (hX : g ∈ fixPos (e := e) (outPts (n := k) rl t.formPerm))
    (htop : ((L.π ⟨g, hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) = t.formPerm) :
    WinLift S L label t g where
  mem := hg
  top := htop
  fix v hv hnot := by
    have hmem : e v ∈ outPts (n := k) rl t.formPerm := by
      refine (mem_outPts hrl _ (e v)).2 ⟨by simpa using hv, ?_⟩
      rw [e.symm_apply_apply]
      exact List.formPerm_apply_of_notMem hnot
    have := hX (e v) hmem
    change e (g (e.symm (e v))) = e v at this
    rw [e.symm_apply_apply] at this
    exact e.injective this

set_option maxHeartbeats 1600000 in
/-- **The window lift.** For a window `t` without repeats that has some lift, `liftWinF`
returns a lift. It calls **PointwiseStab** once and **NormalizedFactor** once. -/
theorem liftWin_spec (hst : PointwiseStab) (hfac : NormalizedFactor) {P : Program} {b jp jf : ℕ}
    (hb : P.HasAt b (liftWinFuns b jp jf)) (hjp : P.prims[jp]? = some (pointwiseStabPrim hst))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps) {rl : List ℕ}
    (hrl : RowLabs e S label rl) (t : List (Fin L.q)) (hnd : t.Nodup) (h2 : 2 ≤ t.length)
    (ht : t.length ≤ L.q) (hex : ∃ g, WinLift S L label t g) :
    FunAll P b (.list [winCtx k L.q rl ps, rowsV t]) (fun w c => ∃ g, WinLift S L label t g ∧
      w = encPerm (toFin e g) ∧ c ≤ liftWinCost hst hfac (k + L.q + ps.length + 2)) := by
  classical
  -- the layout
  have hA : P.HasAt b (winA b jp) := hb.left
  have hB : P.HasAt (b + 46) (winB b jf) := by
    have := hb.right; rwa [length_winA] at this
  have hentry : P.funs[b]? = some (liftWinF b) := by
    simpa using (hA.block 0 (gs := [liftWinF b]) (by rfl)).single
  have hcyc : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := hA.block 1 (by rfl)
  have hcs : P.funs[b + 4]? = some (cycStepF (b + 5)) :=
    (hA.block 4 (gs := [cycStepF (b + 5)]) (by rfl)).single
  have hfd : P.HasAt (b + 5) (findEqFuns (b + 5)) := hA.block 5 (by rfl)
  have hfi : P.HasAt (b + 9) (filterFuns (b + 9) (b + 12)) := hA.block 9 (by rfl)
  have hot : P.funs[b + 12]? = some outTestF :=
    (hA.block 12 (gs := [outTestF]) (by rfl)).single
  have hgs : P.HasAt (b + 13) (graphStabFuns (b + 13) jp) := hA.block 13 (by rfl)
  have hen : P.HasAt (b + 46) (pEncMapFuns (b + 46)) := by simpa using hB.block 0 (by rfl)
  have hmk : P.HasAt (b + 59) (mkGroupFuns (b + 59)) := hB.block 13 (by rfl)
  have hfm : P.HasAt (b + 66) (fstMapFuns (b + 66)) := hB.block 20 (by rfl)
  have hll : P.funs[b + 70]? = some (liftLabF (b + 49) (b + 71) jf) :=
    (hB.block 24 (gs := [liftLabF (b + 49) (b + 71) jf]) (by rfl)).single
  have hsp : P.HasAt (b + 71) (pSplitFuns (b + 71)) := hB.block 25 (by rfl)
  have hgr : P.funs[b + 80]? = some (grpF (b + 46) (b + 59)) :=
    (hB.block 34 (gs := [grpF (b + 46) (b + 59)]) (by rfl)).single
  have hsh : ShiftAt P (b + 49) :=
    ⟨by simpa using (hen.block 4 (gs := [shiftAppF (b + 46 + 5) (b + 46 + 8)]) (by rfl)).single,
      hen.block 5 (by rfl), hen.block 8 (by rfl),
      by simpa using (hen.block 11 (gs := [addKF]) (by rfl)).single⟩
  -- names
  set σ := t.formPerm with hσ
  set X := outPts (n := k) rl σ with hX
  set ctx := winCtx k L.q rl ps with hctx
  set inp := Val.list [ctx, rowsV t] with hinp
  set cl : List Val := [.nat k, .nat L.q, natList rl, .list (ps.map pairV), pSplitCtx k L.q,
    encPerm (1 : Perm (Fin L.q)), encPerm (1 : Perm (Fin k))] with hcl
  have rd : ∀ (rest : List Val) (i : ℕ) (v : Val), cl[i]? = some v →
      Det P (inp :: rest) (cE i) v (4 * inp.wt + 20) := by
    intro rest i v h
    have hv : v ∈ cl := List.mem_of_getElem? h
    have hi : i < 7 := by
      obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 h
      simpa [hcl] using hi
    have d := Det.get' (Det.arg' (P := P) (vs := [ctx, rowsV t]) (rest := rest) (j := 0) rfl)
      (Det.nat i) (vs := cl) h
    refine d.mono ?_
    have h1 : v.wt < ctx.wt := wt_le_wt_list hv
    have h2 : ctx.wt < inp.wt := wt_le_wt_list (by simp [hinp])
    have h3 : (Val.list [ctx, rowsV t]).wt = inp.wt := rfl
    omega
  -- step 1: the cycle
  have hc1 := cycTab_spec hcyc hcs hfd t hnd ht
  rw [range_eq_encPerm_one] at hc1
  have d1 := Det.call (Det.mk2 (Det.arg' (P := P) (vs := [ctx, rowsV t]) (rest := []) (j := 1) rfl)
    (rd [] 5 _ rfl)) hc1
  refine FunAll.intro hentry (EvalAll.letE d1 fun _ _ h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- step 2: the positions outside the window
  have ho := outList_spec hfi hot rl hrl.1 hrl.le σ
  rw [range_eq_encPerm_one] at ho
  have d2 := Det.call (Det.mk2 (Det.mk2 (rd [encPerm σ] 2 _ rfl)
    (Det.var' (P := P) (env := [inp, encPerm σ]) (i := 1) rfl)) (rd [encPerm σ] 6 _ rfl)) ho
  refine EvalAll.letE d2 fun _ _ h2' => ?_
  obtain ⟨rfl, hc2⟩ := h2'
  -- step 3: the graph pairs of `G ∩ Fix(X)`
  have a3 := Det.mk3 (Det.mk2 (rd [encPerm σ, encPts X] 0 _ rfl) (rd [encPerm σ, encPts X] 1 _ rfl))
    (rd [encPerm σ, encPts X] 3 _ rfl)
    (Det.var' (P := P) (env := [inp, encPerm σ, encPts X]) (i := 2) rfl)
  set A3 : Val := .list [.list [.nat k, .nat L.q], .list (ps.map pairV), encPts X] with hA3
  set STB := (pointwiseStabPrim hst).bound (.list [encGroup (ps.map encPair), encPts X]) +
    graphStabK * stabM k L.q ps X ^ 8 with hSTB
  refine EvalAll.letE (Ra := fun w c => ∃ qs : List (Perm (Fin k) × Perm (Fin L.q)),
      w = .list (qs.map pairV) ∧ qs.length ≤ (k + L.q) ^ 2 ∧
      Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓ fixFst k L.q X ∧
      c ≤ (4 * inp.wt + 20 + (4 * inp.wt + 20) + 2 * (Val.list [.nat k, .nat L.q]).wt + 7 +
        (4 * inp.wt + 20) + ((encPts X).wt + 1) + 3 * A3.wt + 8) + STB + w.wt + 1)
    (EvalAll.call_funAll a3 fun v ca h => ?_) fun w3 c3 h3 => ?_
  · obtain ⟨rfl, hca⟩ := h
    exact (graphStabL_spec hst hgs hjp ps X).mono fun w c ⟨qs, h1, h2, h3, h4⟩ =>
      ⟨qs, h1, h2, h3, by omega⟩
  obtain ⟨qs, rfl, hql, hqs, hc3⟩ := h3
  -- step 4: the lift
  set env4 : List Val := [inp, encPerm σ, encPts X, .list (qs.map pairV)] with henv4
  have dkq := Det.mk2 (rd [encPerm σ, encPts X, .list (qs.map pairV)] 0 _ rfl)
    (rd [encPerm σ, encPts X, .list (qs.map pairV)] 1 _ rfl)
  have v3 := Det.var' (P := P) (env := env4) (i := 3) (v := .list (qs.map pairV)) rfl
  have dH := Det.call (Det.mk2 dkq v3) (grp_spec hgr hen hmk qs)
  have dF := Det.call (Det.mk2 (rd [encPerm σ, encPts X, .list (qs.map pairV)] 5 _ rfl) v3)
    (fstMap_spec hfm qs)
  have dN := Det.call (Det.mk2 dkq dF) (grp_spec hgr hen hmk (onePairs qs))
  have d4 := Det.mk2 (Det.mk4 (rd [encPerm σ, encPts X, .list (qs.map pairV)] 0 _ rfl) dH dN
    (rd [encPerm σ, encPts X, .list (qs.map pairV)] 4 _ rfl))
    (Det.var' (P := P) (env := env4) (i := 1) (v := encPerm σ) rfl)
  have hpg : PairGens e L (S.G ⊓ fixPos (e := e) X) qs := pairGens_of_stab hps hqs
  have hσex : ∃ a, (a, σ) ∈ Subgroup.closure {p | p ∈ qs} := by
    obtain ⟨g0, hg0⟩ := hex
    refine ⟨toFin e g0, ?_⟩
    rw [hpg]
    exact (mem_graphOf e L).2 ⟨g0, hg0.mem, ⟨hg0.mem, winLift_fixPos hrl hnd h2 hg0⟩, rfl, hg0.top⟩
  refine EvalAll.call_funAll d4 fun v ca h => ?_
  obtain ⟨rfl, hca⟩ := h
  refine (liftLab_spec hfac hll hsh hsp hjf qs hσex).mono fun w c ⟨a, hw, ha, hc⟩ => ?_
  rw [hpg] at ha
  obtain ⟨g, hg, ⟨-, hgX⟩, h1, h2'⟩ := (mem_graphOf e L).1 ha
  refine ⟨g, winLift_of_fixPos hrl hg hgX h2', by rw [hw, h1], ?_⟩
  -- the cost
  clear dH dF dN d4 dkq v3 a3 d2 d1 ho hσex hgX ha h1 h2' hpg hqs
  have hlo : (onePairs qs).length = qs.length := List.length_map _
  have hX : X.length ≤ k := length_outPts rl σ
  have eI : (Val.list [ctx, rowsV t]).wt = inp.wt := rfl
  have eX : encPts (outPts (n := k) rl σ) = encPts X := rfl
  have eσ : encPerm t.formPerm = encPerm σ := rfl
  have eA3 : (Val.list [.list [.nat k, .nat L.q], .list (ps.map pairV), encPts X]).wt = A3.wt := rfl
  rw [eX] at hc2
  rw [eσ] at hc1
  -- the size
  have hpM : pM k L.q ps = k + L.q + ps.length + 2 := rfl
  have hIc := wt_winCtx_le hrl.1 hrl.le ps
  rw [hpM] at hIc
  set M := k + L.q + ps.length + 2 with hM
  have hM2 : 2 ≤ M := by omega
  have hkqM : k + L.q + 1 ≤ M := by omega
  have p12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have p34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have p46 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p68 : M ^ 6 ≤ M ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have p812 : M ^ 8 ≤ M ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have p2 : 2 ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hM2 2
  have hq1 : (L.q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hk1 : (k + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hk2 : (k + 2) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hkq1 : (k + L.q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  -- the input
  have hrt := wt_rowsV_le t ht
  have hIc' : ctx.wt ≤ 300 * M ^ 3 := hIc
  have hI : inp.wt ≤ 1000 * M ^ 3 := by
    have := wt_list2_le ctx (rowsV t)
    omega
  have hctxI : ctx.wt < inp.wt := wt_le_wt_list (by simp)
  have hrlc : (natList rl).wt < ctx.wt := wt_le_wt_list (by simp [hctx, winCtx])
  have hpsc : (pSplitCtx k L.q).wt < ctx.wt := wt_le_wt_list (by simp [hctx, winCtx])
  have hpsI : (Val.list (ps.map pairV)).wt < ctx.wt := wt_le_wt_list (by simp [hctx, winCtx])
  have w1q := wt_encPerm_le (1 : Perm (Fin L.q))
  have w1k := wt_encPerm_le (1 : Perm (Fin k))
  have wσ := wt_encPerm_le σ
  have wa := wt_encPerm_le a
  have wk := wt_nat_le k
  have wq := wt_nat_le L.q
  have wkq := wt_list2_le (.nat k) (.nat L.q)
  -- step 1
  have s1a := wt_list2_le (rowsV t) (encPerm (1 : Perm (Fin L.q)))
  have s1b : cycTabK * (L.q + 1) ^ 4 ≤ cycTabK * M ^ 4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  -- step 2
  have s2a := wt_list2_le (natList rl) (encPerm σ)
  have s2b := wt_list2_le (Val.list [natList rl, encPerm σ]) (encPerm (1 : Perm (Fin k)))
  have s2c : (Val.list [Val.list [natList rl, encPerm σ], encPerm (1 : Perm (Fin k))]).wt + L.q + 1
      ≤ 5000 * M ^ 3 := by omega
  have s2d : outFK * ((Val.list [Val.list [natList rl, encPerm σ], encPerm (1 : Perm (Fin k))]).wt +
      L.q + 1) ^ 2 ≤ outFK * (25000000 * M ^ 6) := by
    apply Nat.mul_le_mul_left
    calc _ ≤ (5000 * M ^ 3) ^ 2 := Nat.pow_le_pow_left s2c 2
      _ = 25000000 * M ^ 6 := by ring
  have s2e : (encPts X).wt ≤ 3 * M ^ 2 + 4 := (wt_encPts_le' hX).trans (by omega)
  -- step 3
  have s3a : A3.wt ≤ 2 * ((Val.list [.nat k, .nat L.q]).wt + (Val.list (ps.map pairV)).wt +
      (encPts X).wt) + 7 := wt_list3_le _ _ _
  have s3b : STB ≤ (pointwiseStabPrim hst).c * (100 * M ^ 4 + 2) ^ (pointwiseStabPrim hst).k +
      graphStabK * (256 * M ^ 8) := by
    have g1 : (encGroup (ps.map encPair)).wt ≤ 40 * M ^ 4 := wt_encGroup_pairs_le ps
    have g2 := wt_list2_le (encGroup (ps.map encPair)) (encPts X)
    have g3 := prim_bound_le_wt (pointwiseStabPrim hst)
      (show (Val.list [encGroup (ps.map encPair), encPts X]).wt ≤ 100 * M ^ 4 by omega)
    have g4 : graphStabK * stabM k L.q ps X ^ 8 ≤ graphStabK * (256 * M ^ 8) := by
      apply Nat.mul_le_mul_left
      calc stabM k L.q ps X ^ 8 ≤ (2 * M) ^ 8 := Nat.pow_le_pow_left (by unfold stabM; omega) 8
        _ = 256 * M ^ 8 := by ring
    rw [hSTB]; omega
  have hq2 : qs.length ≤ M ^ 2 := hql.trans (Nat.pow_le_pow_left (by omega) 2)
  have hpq : pM k L.q qs ≤ 2 * M ^ 2 := by unfold pM; omega
  have hpo : pM k L.q (onePairs qs) ≤ 2 * M ^ 2 := by unfold pM; omega
  have s3c : (Val.list (qs.map pairV)).wt ≤ 400 * M ^ 6 := by
    have h1 := wt_pairList_le qs
    have h3 := Nat.pow_le_pow_left hpq 3
    have e : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
    omega
  have s3d : (Val.list ((onePairs qs).map pairV)).wt ≤ 400 * M ^ 6 := by
    have h1 := wt_pairList_le (onePairs qs)
    have h3 := Nat.pow_le_pow_left hpo 3
    have e : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
    omega
  -- step 4
  have s4a : grpK * pM k L.q qs ^ 6 ≤ grpK * (64 * M ^ 12) := by
    apply Nat.mul_le_mul_left
    calc _ ≤ (2 * M ^ 2) ^ 6 := Nat.pow_le_pow_left hpq 6
      _ = 64 * M ^ 12 := by ring
  have s4b : grpK * pM k L.q (onePairs qs) ^ 6 ≤ grpK * (64 * M ^ 12) := by
    apply Nat.mul_le_mul_left
    calc _ ≤ (2 * M ^ 2) ^ 6 := Nat.pow_le_pow_left hpo 6
      _ = 64 * M ^ 12 := by ring
  have s4c : (encGroup (qs.map encPair)).wt ≤ 640 * M ^ 8 := by
    have h1 := wt_encGroup_pairs_le qs
    have h3 := Nat.pow_le_pow_left hpq 4
    have e : (2 * M ^ 2) ^ 4 = 16 * M ^ 8 := by ring
    omega
  have s4d : (encGroup ((onePairs qs).map encPair)).wt ≤ 640 * M ^ 8 := by
    have h1 := wt_encGroup_pairs_le (onePairs qs)
    have h3 := Nat.pow_le_pow_left hpo 4
    have e : (2 * M ^ 2) ^ 4 = 16 * M ^ 8 := by ring
    omega
  have s4e := wt_list2_le (Val.list [.nat k, .nat L.q]) (.list (qs.map pairV))
  have s4f := wt_list2_le (Val.list [.nat k, .nat L.q]) (.list ((onePairs qs).map pairV))
  have s4g := wt_list2_le (encPerm (1 : Perm (Fin L.q))) (.list (qs.map pairV))
  have s4h : qs.length * (40 * (4 * (L.q + 1) ^ 2 + 22 * (k + L.q + 1) ^ 2) + 400) ≤
      M ^ 2 * (1440 * M ^ 2) :=
    Nat.mul_le_mul hq2 (by omega)
  have s4i : mapK * (qs.length + 1) * ((Val.list [encPerm (1 : Perm (Fin L.q)),
      .list (qs.map pairV)]).wt + (Val.list ((onePairs qs).map pairV)).wt + 1) ≤
      mapK * (2 * M ^ 2) * (2000 * M ^ 6) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have s4j : M ^ 2 * (1440 * M ^ 2) = 1440 * M ^ 4 := by ring
  have s4k : mapK * (2 * M ^ 2) * (2000 * M ^ 6) = 4000000 * M ^ 8 := by simp only [mapK]; ring
  have s4l := wt_list4_le (.nat k) (encGroup (qs.map encPair)) (encGroup ((onePairs qs).map encPair))
    (pSplitCtx k L.q)
  have s4m := wt_list2_le (Val.list [.nat k, encGroup (qs.map encPair),
    encGroup ((onePairs qs).map encPair), pSplitCtx k L.q]) (encPerm σ)
  have s4n : liftLabCost (normalizedFactorPrim hfac) (qs.length + k + L.q + 2) ≤
      liftLabCost (normalizedFactorPrim hfac) (2 * M ^ 2) := liftLabCost_mono _ (by omega)
  rw [hw] at *
  unfold liftWinCost
  simp only [liftWinK, grpK, cycTabK, cycK, outFK, graphStabK, mapK] at *
  omega

end Lift

end GI.Impl
