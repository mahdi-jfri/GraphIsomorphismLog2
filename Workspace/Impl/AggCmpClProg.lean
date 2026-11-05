module

public import Workspace.Impl.AggCmpInd
public import Workspace.Impl.AggCmpStBud

@[expose] public section

/-!
# The call of a stage: program text and the log search

At stage `j` of the pair `(t, t')`, with the representative `a₀` of the current coset, the move
hands the window call of `compareCall` to the driver (`cm_stage_call`). The call needs the
canonical value of the window state: the stage kernel `N_j` of the test set `T = tset t` and the
string `z` of `t`, the increment `V_j`, and the codes of both colorings. The logs of the
certificate phase hold the graph form of the lift of `A_j` and the positions of `V_j`
(`CmLogsOK`), so the program does this.

1. It reads the tuple `t` and finds the log of `tset t` (`cmLogF`): it compares the indicator of
   the digits of `t` with the indicator `indT T` stored in each log (`cm_cl_log`).
2. It takes stage `j` of the string of `t` from that log.
3. The kernel `N_j = ker(φ_T|_{A_j})` is the stabilizer of the label points of `T` in `A_j`: one
   **PointwiseStab** call (`graphStabP_spec`), then the reduction `kr_spec` (`cmKerF`).
4. The indicator of the positions of `V_j` gives the domain of the window (`cm_ind_spec`).
5. The two-string window module gives the codes (`cmWp_spec`).

This file gives the program text, where it sits (`CmClAt`), and the log search.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups GI.LocalCertificates Equiv
  Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-! ### The program text -/

section Funs

variable (b : ℕ)

/-- Base indices of the modules of the call. -/
def cmLFd : ℕ := b + 500
def cmIMap : ℕ := b + 503
def cmCnt : ℕ := b + 510
def cmWpB : ℕ := b + 520
def cmDomB : ℕ := b + 540

/-- The test of the log search, on `[key, log]`: is the indicator `indT T` of the log `key`? -/
def cmLTstF : Expr := .call (cmEqN b) (mk2 (arg 0) (.get (.get (arg 1) (.nat 0)) (.nat 0)))

/-- **The log of a tuple**, on `[q, digits, logs]`. -/
def cmLogF : Expr :=
  .letE (.call (b + 11) (mk2 (arg 0) (arg 1)))
    (.letE (.call (cmLFd b) (mk2 (.var 1) (arg 2))) (.get (arg 2) (.var 2)))

/-- **The stage kernel**, on `[[k, q], stage, tsV T]`: the stabilizer of the label points of `T`
in the stage group, with at most `k²` generators. -/
def cmKerF : Expr :=
  .letE (.call (cmStab b) (mk3 (arg 0) (.get (arg 1) (.nat 0)) (.get (arg 2) (.nat 1))))
    (.call (cmKr b) (mk2 (.get (arg 0) (.nat 0)) (.var 1)))

/-- The bit of the tuple at the index `e` of the tuples. -/
def cmBitE (e : Expr) : Expr := .get (.get (cpPf 6) e) (.nat 0)

/-- **The call of a stage**, on `[kst, u]`. The new program state has `fl = 2`. -/
def cmCallF : Expr :=
  .letE (.get (cpPf 6) (.arith .div (.length (cpKf 4)) (cpPf 8)))
  (.letE (.call (b + 12) (mk3 (.get (cpPf 1) (.nat 1)) (.get (.var 1) (.nat 1)) (cpPf 5)))
  (.letE (.get (.get (.var 2) (.arith .add (.nat 1) (.get (.var 1) (.nat 0)))) (cpKf 1))
  (.letE (.call (b + 13) (mk3 (cpPf 1) (.var 3) (.get (.var 2) (.nat 0))))
  (.letE (.call (b + 11) (mk2 (.get (cpPf 1) (.nat 0)) (.get (.var 3) (.nat 1))))
  (.letE (.call (cmWpB b) (mk4 (.get (cpPf 0) (.nat 2))
      (.get (cpPf 0) (.arith .add (.nat 3) (.get (.var 1) (.nat 0))))
      (.get (cpPf 0) (.arith .add (.nat 3)
        (cmBitE (.arith .mod (.length (cpKf 4)) (cpPf 8)))))
      (.get (cpKf 2) (.nat 0))))
    (Expr.mkList [.nat 1, .nat 1,
      Expr.mkList [.get (cpPf 1) (.nat 0), .var 4, .var 5, .get (.var 6) (.nat 0),
        .get (.var 6) (.nat 1), .get (cpPf 0) (.nat 5), .nil, .nat 0, .nat 2,
        .get (cpPf 0) (.nat 9)],
      Expr.mkList [cpKf 0, cpKf 1, cpKf 2, cpKf 3, cpKf 4, .nat 2]]))))))

end Funs

/-- **Where the call of a stage and its modules sit.** The stabilizer, the reduction, the range
and the equality of lists are those of the start of a pair (`CmStAt`). -/
structure CmClAt (P : Program) (b : ℕ) : Prop where
  call : P.funs[b + 4]? = some (cmCallF b)
  ltst : P.funs[b + 9]? = some (cmLTstF b)
  istep : P.funs[b + 10]? = some (cmIndStepF (cmCnt b))
  ind : P.funs[b + 11]? = some (cmIndF (cmRng b) (cmIMap b))
  log : P.funs[b + 12]? = some (cmLogF b)
  ker : P.funs[b + 13]? = some (cmKerF b)
  lfd : P.HasAt (cmLFd b) (findFuns (cmLFd b) (b + 9))
  imap : P.HasAt (cmIMap b) (mapFuns (cmIMap b) (b + 10))
  cnt : P.HasAt (cmCnt b) (countFuns (cmCnt b))
  wp : P.HasAt (cmWpB b) (cmWpFuns (cmWpB b) (cmDomB b))
  dom : DomAt P (cmDomB b)

/-! ### Indicators of sets -/

section IndL

variable {q : ℕ}

/-- The indicator of a set of labels as a list of numbers. -/
def cmIndL (T : Finset (Fin q)) : List ℕ := (List.finRange q).map fun i => if i ∈ T then 1 else 0

theorem cm_indT_natList (T : Finset (Fin q)) : indT T = natList (cmIndL T) := by
  unfold indT cmIndL
  rw [encFun_eq_natList]

theorem cm_indL_inj {T T' : Finset (Fin q)} (h : cmIndL T = cmIndL T') : T = T' := by
  ext i
  have h1 := congrArg (fun l => l[(i : ℕ)]?) h
  simp only [cmIndL, List.getElem?_map] at h1
  rw [List.getElem?_eq_getElem (by simp), List.getElem_finRange] at h1
  simp only [Option.map_some, Option.some.injEq, Fin.cast_mk, Fin.eta] at h1
  constructor
  · intro hi; by_contra hn; simp [hi, hn] at h1
  · intro hi; by_contra hn; simp [hi, hn] at h1

theorem cm_indT_inj {T T' : Finset (Fin q)} (h : indT T = indT T') : T = T' := by
  rw [cm_indT_natList, cm_indT_natList] at h
  exact cm_indL_inj (natList_injective h)

end IndL

/-! ### The log search -/

section Log

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) {W : ℕ} {Pg : Program}
  {b jp : ℕ} (hsa : CmStAt Pg b jp) (hca : CmClAt Pg b) {k q κ : ℕ}

theorem cm_findIdx_congr {α : Type} {p p' : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, p x = p' x) → xs.findIdx p = xs.findIdx p'
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.findIdx_cons, List.findIdx_cons, h x (by simp),
      cm_findIdx_congr fun y hy => h y (by simp [hy])]

open Classical in
/-- The test of the log search, as a function on values. -/
noncomputable def cmLQ (logs : List (CmLog k q)) (T : Finset (Fin q)) (x : Val) : Bool :=
  decide (∃ l ∈ logs, x = cmLogV l ∧ l.T = T)

theorem cm_lq_eq {logs : List (CmLog k q)} {T : Finset (Fin q)} {l : CmLog k q} (hl : l ∈ logs) :
    cmLQ logs T (cmLogV l) = decide (l.T = T) := by
  unfold cmLQ
  refine decide_eq_decide.2 ⟨?_, fun h => ⟨l, hl, rfl, h⟩⟩
  rintro ⟨l', -, h1, h2⟩
  have h3 : tsV k l.T = tsV k l'.T := by
    unfold cmLogV at h1
    injection h1 with h1
    injection h1
  unfold tsV at h3
  injection h3 with h3
  injection h3 with h3
  rw [cm_indT_inj h3, h2]

include hsa hca in
/-- **The log of a tuple.** For an injective tuple `t`, `cmLogF` returns the log of `tset t`. -/
theorem cm_cl_log {logs : List (CmLog k q)} (hO : ∃ O' : TestSetOrder q κ, logs.map CmLog.T = O'.sets)
    (t : Fin κ ↪ Fin q)
    (hw : (Val.list [.nat q, stTv (t : Fin κ → Fin q), .list (logs.map cmLogV)]).wt ≤ W)
    (hW : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W) :
    CpFB Pg (b + 12) (.list [.nat q, stTv (t : Fin κ → Fin q), .list (logs.map cmLogV)]) W
      (cpG hst hpre hm W)
      (fun w => ∃ l ∈ logs, l.T = tset (t : Fin κ → Fin q) ∧ w = cmLogV l) := by
  classical
  set T := tset (t : Fin κ → Fin q) with hT
  set ds := stL fun i => ((t i : Fin q) : ℕ) with hds
  set V := Val.list [.nat q, stTv (t : Fin κ → Fin q), .list (logs.map cmLogV)] with hV
  have hκ : κ ≤ q := by simpa using Fintype.card_le_of_embedding t
  have hdl : ds.length ≤ q := by simp [hds, stL, hκ]
  have hdB : ∀ x ∈ ds, x ≤ q := by
    intro x hx
    simp only [hds, stL, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact (t i).isLt.le
  -- the log exists
  obtain ⟨O', hO'⟩ := hO
  have hTc : T.card = κ := by
    rw [hT, tset, Finset.card_image_of_injective _ (fun i j h => t.injective h)]
    simp
  have hTm : T ∈ logs.map CmLog.T := by rw [hO']; exact (O'.mem T).2 hTc
  obtain ⟨l₀, hl₀, hl₀T⟩ := List.mem_map.1 hTm
  set i := logs.findIdx (fun l => decide (l.T = T)) with hi
  have hil : i < logs.length := List.findIdx_lt_length_of_exists ⟨l₀, hl₀, by simp [hl₀T]⟩
  have hiT : logs[i].T = T := by simpa using List.findIdx_getElem (w := hil)
  -- the weights
  have hVW : V.wt ≤ W := hw
  have hLw : (Val.list (logs.map cmLogV)).wt < W :=
    lt_of_lt_of_le (cm_wt_lt_of_mem (vs := [.nat q, stTv _, .list (logs.map cmLogV)]) (by simp)) hw
  have hsw : (stTv (t : Fin κ → Fin q)).wt < W :=
    lt_of_lt_of_le (cm_wt_lt_of_mem (vs := [.nat q, stTv _, .list (logs.map cmLogV)]) (by simp)) hw
  have hlw : ∀ x ∈ logs.map cmLogV, x.wt < W := fun x hx => lt_trans (cm_wt_lt_of_mem hx) hLw
  obtain ⟨f1, f2, -, f24, f46, -, -, -, -, -⟩ := cp_pow_facts k q
  have h12 : (k + q + 1) ^ 6 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hqW : q + 1 ≤ W := by
    have : k + q + 1 ≤ (k + q + 1) ^ 2 := Nat.le_self_pow (by omega) _
    omega
  have hIw : (indT T).wt ≤ 7 * q + 4 := wt_indT_le T
  have hq100 : 100 * (q + 1) ≤ W := by
    have : k + q + 1 ≤ (k + q + 1) ^ 12 := Nat.le_self_pow (by omega) _
    omega
  -- the indicator
  have hI := cm_ind_spec hca.ind hsa.rng hca.imap hca.istep hca.cnt q ds hdB le_rfl hdl
  rw [hds, cm_indT_eq t, ← hT, ← hds] at hI
  have dI : Det Pg [V] (.call (b + 11) (mk2 (arg 0) (arg 1))) (indT T)
      (cmIndK * (q + 1) ^ 4 + 20 * W + 50) := by
    refine (Det.call (Det.mk2 (Det.arg' (rest := []) (j := 0) (v := .nat q) rfl)
      (Det.arg' (rest := []) (j := 1) (v := stTv (t : Fin κ → Fin q)) rfl))
      (FunAll.mono hI fun w c h => ⟨h.1, h.2⟩)).mono ?_
    have := wt_list2_le (.nat q) (stTv (t : Fin κ → Fin q))
    have := wt_nat_le q
    have : (Val.list [.nat q, natList ds]).wt = (Val.list [.nat q, stTv (t : Fin κ → Fin q)]).wt :=
      rfl
    have : V.wt = (Val.list [.nat q, stTv (t : Fin κ → Fin q), .list (logs.map cmLogV)]).wt := rfl
    have : (Val.list [.nat q, stTv (t : Fin κ → Fin q)]).wt ≤ V.wt := by
      have := wt_list_mono (show [Val.nat q, stTv (t : Fin κ → Fin q)] <+:
        [.nat q, stTv (t : Fin κ → Fin q), .list (logs.map cmLogV)] from ⟨_, rfl⟩)
      omega
    omega
  -- the search
  have htest : ∀ x ∈ logs.map cmLogV, FunDet Pg (b + 9) (.list [indT T, x])
      (boolVal (cmLQ logs T x)) (10 ^ 7 * (W + 1) ^ 2) := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    have hxw := hlw _ hx
    rw [cm_lq_eq hl]
    have h1 : (tsV k l.T).wt < (cmLogV l).wt := cm_wt_lt_of_mem (by simp [cmLogV])
    have h2 : (indT l.T).wt < (tsV k l.T).wt := cm_wt_lt_of_mem (by simp [tsV])
    have hE := eqNats_spec hsa.eqN (cmIndL T) (cmIndL l.T)
    have hdec : decide (cmIndL T = cmIndL l.T) = decide (l.T = T) :=
      decide_eq_decide.2 ⟨fun h => (cm_indL_inj h).symm, fun h => by rw [h]⟩
    rw [hdec, ← cm_indT_natList, ← cm_indT_natList] at hE
    refine FunDet.intro hca.ltst ((Det.call (Det.mk2 (Det.arg' (rest := []) (j := 0) rfl)
      (Det.get' (Det.get' (Det.arg' (rest := []) (j := 1) (v := cmLogV l) rfl) (Det.nat 0)
        (vs := [tsV k l.T, _, _]) rfl) (Det.nat 0) (vs := [indT l.T, _]) rfl)) hE).mono ?_)
    have hlen : (cmIndL T).length = q := by simp [cmIndL]
    rw [hlen]
    have := wt_list2_le (indT T) (indT l.T)
    have := wt_list2_le (indT T) (cmLogV l)
    have := wt_boolVal_le (decide (l.T = T))
    have := wt_indT_le l.T
    have hq1 : (q + 1) * ((Val.list [indT T, indT l.T]).wt + q + 4) ≤ (W + 1) * (8 * (W + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hl : loopModK * (q + 1) * ((Val.list [indT T, indT l.T]).wt + q + 4) ≤
        loopModK * 8 * (W + 1) ^ 2 := by
      calc _ = loopModK * ((q + 1) * ((Val.list [indT T, indT l.T]).wt + q + 4)) := by ring
        _ ≤ loopModK * ((W + 1) * (8 * (W + 1))) := Nat.mul_le_mul_left _ hq1
        _ = _ := by ring
    have : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have : (Val.list [indT l.T, natList (ptsKey (labPts k (tlist l.T)))]).wt = (tsV k l.T).wt :=
      rfl
    have hu : (cmLogV l).wt < W := hxw
    have hq : 100 * (q + 1) ≤ W := hq100
    simp only [loopModK] at hl ⊢
    omega
  have hF := find_spec hca.lfd (c := indT T) (xs := logs.map cmLogV) htest
  have hfind : (logs.map cmLogV).findIdx (cmLQ logs T) = i := by
    rw [List.findIdx_map, hi]
    exact cm_findIdx_congr fun l' hl' => cm_lq_eq hl'
  have hlen : (logs.map cmLogV).length ≤ W := by
    have := length_lt_wt_list (logs.map cmLogV)
    omega
  have dS : Det Pg [V, indT T] (.call (cmLFd b) (mk2 (.var 1) (arg 2))) (.nat i)
      ((10 * V.wt + 10 * (indT T).wt + 10 * W + 100) +
        (((logs.map cmLogV).map fun _ => 10 ^ 7 * (W + 1) ^ 2).sum +
          loopModK * ((logs.map cmLogV).length + 1) *
            ((Val.list [indT T, .list (logs.map cmLogV)]).wt + 2 * (logs.map cmLogV).length + 3)) +
        (Val.nat i).wt + 1) := by
    refine (Det.call (Det.mk2 (Det.var' (i := 1) (v := indT T) rfl)
      (Det.arg' (rest := [indT T]) (j := 2) (v := .list (logs.map cmLogV)) rfl))
      (FunAll.mono hF fun w c h => ⟨by rw [h.1, hfind], h.2⟩)).mono ?_
    have := wt_list2_le (indT T) (.list (logs.map cmLogV))
    have : (Val.list [Val.nat q, stTv (t : Fin κ → Fin q), Val.list (logs.map cmLogV)]).wt =
      V.wt := rfl
    omega
  have hget : (logs.map cmLogV)[i]? = some (cmLogV logs[i]) := by simp [hil]
  have dG : Det Pg [V, indT T, .nat i] (.get (arg 2) (.var 2)) (cmLogV logs[i])
      (2 * V.wt + 2 + 5 + ((Val.nat i).wt + 1) + (cmLogV logs[i]).wt + 1) :=
    (Det.get' (Det.arg' (rest := [indT T, .nat i]) (j := 2) (v := .list (logs.map cmLogV)) rfl)
      (Det.var' (i := 2) rfl) hget).mono le_rfl
  have hmem : cmLogV logs[i] ∈ logs.map cmLogV := List.mem_map.2 ⟨_, List.getElem_mem hil, rfl⟩
  refine CpFB.det (FunDet.intro hca.log (Det.letE dI (Det.letE dS dG))) ?_
    (le_of_lt (hlw _ hmem)) ⟨logs[i], List.getElem_mem hil, hiT, rfl⟩
  -- the cost
  have hlw' := hlw _ hmem
  have hiw := wt_nat_le i
  have hiL : i ≤ W := by
    have h1 := hlen
    rw [List.length_map] at h1
    omega
  rw [List.map_const', List.sum_replicate, smul_eq_mul]
  have w1 := wt_list2_le (indT T) (.list (logs.map cmLogV))
  have c1 : (logs.map cmLogV).length * (10 ^ 7 * (W + 1) ^ 2) ≤ 10 ^ 7 * (W + 1) ^ 3 := by
    have := Nat.mul_le_mul_right (10 ^ 7 * (W + 1) ^ 2) (show (logs.map cmLogV).length ≤ W + 1 by
      omega)
    have e : (W + 1) * (10 ^ 7 * (W + 1) ^ 2) = 10 ^ 7 * (W + 1) ^ 3 := by ring
    omega
  have hK : loopModK = 1000 := rfl
  have hI : cmIndK = 10 ^ 7 := rfl
  rw [hK, hI]
  have c2 : 1000 * ((logs.map cmLogV).length + 1) *
      ((Val.list [indT T, .list (logs.map cmLogV)]).wt + 2 * (logs.map cmLogV).length + 3) ≤
      20000 * (W + 1) ^ 2 := by
    calc _ ≤ 1000 * (W + 1) * (20 * (W + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = _ := by ring
  have c3 : 10 ^ 7 * (q + 1) ^ 4 ≤ 10 ^ 7 * (W + 1) ^ 4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have p1 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have p2 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have p3 : (W + 1) ^ 3 ≤ (W + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hp := cp_poly_le (W := W) (K := 10 ^ 9) (d := 4) (by norm_num) (by norm_num) (by omega)
  have := cpG_poly hst hpre hm (W := W)
  omega

end Log

end GI.Impl
