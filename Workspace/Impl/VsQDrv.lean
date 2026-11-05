module

public import Workspace.Impl.VsQDrvC

@[expose] public section

/-!
# The driver

The driver `vsQDrvE` asks the analysis for a leaf answer or a split. For a split it runs the coset
program `vsQTfE` on every coset representative `t` and pastes the answers. The coset program moves
the target to `φ(t)⁻¹ y` and runs the chain program on the chain of the split for the coset group
(`vsQTf_spec`). The driver spec `vsQDrv_spec` is proved by strong induction on the measure
`VsQSt.mu`: every chain step has a smaller measure than the node.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-! ### Small facts -/

/-- An answer of the coset problem `(C, W, W', x, φ(t)⁻¹ y)`, multiplied by `t` on the left. -/
theorem vsQ_cos_ans {H C : Subgroup (Perm (Fin I.n))} {W W' : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} (hP : VsQProb I H W W' x y) (hC : C ≤ H) {t : Perm (Fin I.n)} (ht : t ∈ H)
    {a : Option (Perm (Fin I.n) × List (Perm (Fin I.n)))} (h : VsQAnsOK (hP.coset hC ht) a) :
    VsQCosOK hP hC t (a.map fun r => (t * r.1, r.2)) := by
  cases a with
  | none => exact h
  | some r =>
    obtain ⟨g, ks⟩ := r
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨?_, h2, h3⟩
    simpa only [inv_mul_cancel_left] using h1

theorem VsQCosOK.len {H C : Subgroup (Perm (Fin I.n))} {W W' : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} {hP : VsQProb I H W W' x y} {hC : C ≤ H} {t : Perm (Fin I.n)}
    {a : Option (Perm (Fin I.n) × List (Perm (Fin I.n)))} (h : VsQCosOK hP hC t a) :
    ∀ r ∈ a, r.2.length ≤ I.n ^ 2 := by
  intro r hr
  cases a with
  | none => simp at hr
  | some a => simp only [Option.mem_def, Option.some.injEq] at hr; subst hr; exact h.2.2

/-- A list of answer values, entrywise related to a list, comes from a list of answers. -/
theorem vsQ_forall₂_ans {n : ℕ} {α : Type} {Q : α → Option (Perm (Fin n) × List (Perm (Fin n))) → Prop} :
    ∀ (xs : List α) (ws : List Val), List.Forall₂ (fun x w => ∃ a, w = vsQAnsV a ∧ Q x a) xs ws →
      ∃ rs, ws = rs.map vsQAnsV ∧ List.Forall₂ Q xs rs
  | [], [], _ => ⟨[], rfl, List.Forall₂.nil⟩
  | x :: xs, w :: ws, List.Forall₂.cons h hs => by
    obtain ⟨a, rfl, ha⟩ := h
    obtain ⟨rs, rfl, hrs⟩ := vsQ_forall₂_ans xs ws hs
    exact ⟨a :: rs, rfl, List.Forall₂.cons ha hrs⟩

/-- In a list of at least two positive numbers, each entry is below the sum. -/
theorem vsQ_lt_sum {ds : List ℕ} (h1 : ∀ e ∈ ds, 1 ≤ e) (h2 : 2 ≤ ds.length) {e : ℕ}
    (he : e ∈ ds) : e + 1 ≤ ds.sum := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem he
  have a1 := List.length_le_sum_of_one_le l1 fun i hi => h1 i (by simp [hi])
  have a2 := List.length_le_sum_of_one_le l2 fun i hi => h1 i (by simp [hi])
  simp only [List.length_append, List.length_cons] at h2
  simp only [List.sum_append, List.sum_cons]
  omega

/-- The driver bound is at least the overhead `Cn` of one node. -/
theorem vsQBd_ge {c Cn K D : ℕ} (hc : 10 * Cn ≤ c) (hK : 2 ≤ K) (ab : Prop) :
    Cn ≤ vsQBd c K D ab := by
  have h1 := vsQ_cost_leaf (D := max D 1) hc (le_max_right _ _)
  unfold vsQBd
  split_ifs
  · exact h1
  · exact h1.trans (vsQFa_le_Fn (le_max_right _ _) hK)

theorem VsQDSz.wt_split {S Tm : ℕ} (h : VsQDSz I S Tm) {s : VsQSt I} {E : ℕ}
    {ts cs : List (Perm (Fin I.n))} {lows : List (List (List ℕ))}
    (hsp : VsQSplitOK s E Tm ts cs lows) : (vsQSplitV ts cs lows).wt ≤ 2000 * S ^ 6 := by
  have hl : lows.length ≤ I.d := (vsQChain_length hsp.chain).trans (vsQRk_le _)
  have h1 := wt_list4_le (.nat 1) (.list (ts.map encPerm)) (encGroup cs) (vsQLowsV lows)
  have h2 := vs_wt_list_le_of (ts.map encPerm) (c := 4 * S ^ 2) (by
    intro v hv
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hv
    exact h.wt_perm t)
  rw [List.length_map] at h2
  have h3 : ts.length * (2 * (4 * S ^ 2) + 1) ≤ S * (9 * S ^ 2) :=
    Nat.mul_le_mul (by have := hsp.tl; have := h.t; omega)
      (by have := h.pow_le (show 0 ≤ 2 by omega); simp at this; omega)
  have e3 : S * (9 * S ^ 2) = 9 * S ^ 3 := by ring
  have := h.wt_group hsp.csl
  have := h.wt_lows hsp.fit hl
  have := wt_nat_le 1
  have := h.pow_le (show 3 ≤ 6 by omega)
  have := h.pow_le (show 4 ≤ 6 by omega)
  have := h.pow_le (show 0 ≤ 6 by omega)
  simp only [pow_zero] at *
  unfold vsQSplitV
  omega

/-! ### One coset -/

set_option maxHeartbeats 4000000 in
open Classical in
/-- **One coset.** On `[[state, split], t]` the coset program returns `t` times an answer of the
coset problem `(C, W, W', x, φ(t)⁻¹ y)`. -/
theorem vsQTf_spec {P : Program} {b ana ai cmp paste E Tm S CA CAI CP Cn c K : ℕ}
    (H : VsQDrvHyp P I b ana ai cmp paste E Tm S CA CAI CP Cn c K) {m : ℕ}
    (hD : ∀ (s : VsQSt I) (hs : VsQStOK s), s.mu < m → FunAll P b (vsQStV I s) (VsQDrvOK c K s hs))
    {s : VsQSt I} (hs : VsQStOK s) {ts cs : List (Perm (Fin I.n))} {lows : List (List (List ℕ))}
    (hsp : VsQSplitOK s E Tm ts cs lows)
    (hμ : ∀ e ∈ vsQDims I (s.ws :: lows),
      2 * e + (if VsQAb I (gens cs) (vsQSp I s.ws) (vsQSp I s.ws') then 0 else 1) < m)
    {t : Perm (Fin I.n)} (ht : t ∈ ts) :
    FunAll P (b + 2) (.list [.list [vsQStV I s, vsQSplitV ts cs lows], encPerm t])
      (fun w cost => ∃ a, w = vsQAnsV a ∧ VsQCosOK hs.prob hsp.cle t a ∧
        cost ≤ CAI + 10 ^ 7 * S ^ 6 + (Cn * (lows.length + 1) +
          ((vsQDims I (s.ws :: lows)).map fun e =>
            vsQBd c K e (VsQAb I (gens cs) (vsQSp I s.ws) (vsQSp I s.ws'))).sum)) := by
  have hS1 := H.sz.one_le
  have hf2 : P.funs[b + 2]? = some (vsQTfE (b + 1) ai cmp) :=
    H.funs.get (j := 2) (by simp [vsQDrvFuns, mapFuns, loopFuns])
  have htH : t ∈ gens s.hs := hsp.tmem t ht
  have htG : t ∈ gens I.gs := hs.prob.le htH
  have hl : lows.length ≤ I.d := (vsQChain_length hsp.chain).trans (vsQRk_le _)
  set abC := VsQAb I (gens cs) (vsQSp I s.ws) (vsQSp I s.ws') with habCdef
  set St := ((vsQDims I (s.ws :: lows)).map fun e => vsQBd c K e abC).sum with hSt
  set y' := vsQApp I t s.y with hy'
  have hfy' : VsWFit I.p I.d [y'] := vsQApp_fit hs.fy
  -- the problems
  have hPc := hs.prob.coset hsp.cle htH
  have hlastEq : vsQSp I ((s.ws :: lows.drop 0).getLast (List.cons_ne_nil _ _)) =
      vsQSp I s.ws' := by
    simp only [List.drop_zero]; rw [List.getLast_cons hsp.ne]; exact hsp.last
  have hP' : VsQProb I (gens cs) (vsQSp I s.ws) (vsQSp I s.ws') (vsWV I.p I.d s.x)
      (vsWV I.p I.d y') := by
    rw [hy', vsQApp_vsWV]; exact hPc
  have hP : VsQProb I (gens cs) (vsQSp I s.ws)
      (vsQSp I ((s.ws :: lows.drop 0).getLast (List.cons_ne_nil _ _))) (vsWV I.p I.d s.x)
      (vsWV I.p I.d y') := by
    rw [hlastEq]; exact hP'
  have htr : ∀ a, VsQAnsOK hP a → VsQAnsOK hPc a := fun a h =>
    VsQAnsOK.congr_y hP' hPc (vsQApp_vsWV _) (VsQAnsOK.congr hP hP' hlastEq h)
  have hC := vsQDrvC_spec H hD abC lows.length cs s.ws lows s.x y' 0 (Nat.sub_zero _)
    (Nat.zero_le _) hsp.csl hs.fit hs.wl hsp.fit hl hs.fx hfy' hP
    (by rw [List.drop_zero]; exact hsp.chain) (by rw [List.drop_zero]; exact hsp.inv)
    (by rw [hlastEq]; exact id) (by rw [List.drop_zero]; exact hμ)
  have eD : ((vsQDims I (s.ws :: lows.drop 0)).map fun e => vsQBd c K e abC).sum = St := by
    rw [List.drop_zero]
  -- the values
  set stV := Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
    natList s.y] with hstV
  set spV := Val.list [.nat 1, .list (ts.map encPerm), encGroup cs, vsQLowsV lows] with hspV
  set ctx := Val.list [stV, spV] with hctx
  set a := Val.list [ctx, encPerm t] with ha
  show FunAll P (b + 2) a _
  apply FunAll.intro hf2
  have wst : stV.wt ≤ 2000 * S ^ 6 := H.sz.wt_st hs
  have wsp : spV.wt ≤ 2000 * S ^ 6 := H.sz.wt_split hsp
  have wctx := wt_list2_le stV spV
  have wa := wt_list2_le ctx (encPerm t)
  have wtt := H.sz.wt_perm t
  have ea : a.wt = (Val.list [ctx, encPerm t]).wt := rfl
  have ectx : ctx.wt = (Val.list [stV, spV]).wt := rfl
  have est : stV.wt = (Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
    natList s.y]).wt := rfl
  have esp : spV.wt = (Val.list [.nat 1, .list (ts.map encPerm), encGroup cs,
    vsQLowsV lows]).wt := rfl
  have hES : ∀ v ∈ [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y],
      v.wt < stV.wt := fun v hv => wt_le_wt_list hv
  have hEP : ∀ v ∈ [Val.nat 1, .list (ts.map encPerm), encGroup cs, vsQLowsV lows],
      v.wt < spV.wt := fun v hv => wt_le_wt_list hv
  have p0 := H.sz.pow_le (show 0 ≤ 6 by omega)
  have p26 := H.sz.pow_le (show 2 ≤ 6 by omega)
  simp only [pow_zero] at p0
  have wS : 2 * a.wt + ctx.wt + stV.wt + spV.wt ≤ 50000 * S ^ 6 := by omega
  have dS : ∀ (rest : List Val) (k : ℕ) (v : Val),
      [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y][k]? = some v →
      Det P (a :: rest) (vsQS0 k) v (2 * a.wt + ctx.wt + stV.wt + v.wt + k + 20) :=
    fun rest k v hv => (Det.get' (Det.get' (Det.arg' (vs := [ctx, encPerm t]) (rest := rest)
      (j := 0) rfl) (Det.nat 0) (show [stV, spV][0]? = some stV from rfl)) (Det.nat k) hv).mono
        (by omega)
  have dA : ∀ (rest : List Val) (k : ℕ) (v : Val),
      [Val.nat 1, .list (ts.map encPerm), encGroup cs, vsQLowsV lows][k]? = some v →
      Det P (a :: rest) (vsQA0 k) v (2 * a.wt + ctx.wt + spV.wt + v.wt + k + 20) :=
    fun rest k v hv => (Det.get' (Det.get' (Det.arg' (vs := [ctx, encPerm t]) (rest := rest)
      (j := 0) rfl) (Det.nat 1) (show [stV, spV][1]? = some spV from rfl)) (Det.nat k) hv).mono
        (by omega)
  have dT : ∀ rest : List Val, Det P (a :: rest) (arg 1) (encPerm t) (2 * a.wt + 6) :=
    fun rest => (Det.arg' (vs := [ctx, encPerm t]) (rest := rest) (j := 1) rfl).mono (by omega)
  have hΓ := hES _ (by simp : vsQGam I ∈ _)
  have hyv := hES _ (by simp : natList s.y ∈ _)
  have hxv := hES _ (by simp : natList s.x ∈ _)
  have hwv := hES _ (by simp : vsWVs s.ws ∈ _)
  have hcv := hEP _ (by simp : encGroup cs ∈ _)
  have hlv := hEP _ (by simp : vsQLowsV lows ∈ _)
  have wy' := H.sz.wt_vec hfy'
  -- applying `φ(t)⁻¹`
  have dAI := (Det.call (Det.mk3 (dS [] 0 _ rfl) (dT []) (dS [] 5 _ rfl))
    (H.hai t htG s.y hs.fy)).mono (c' := CAI + 10 ^ 6 * S ^ 6) (by
      have := wt_list3_le (vsQGam I) (encPerm t) (natList s.y)
      have ey : (natList (vsQApp I t s.y)).wt = (natList y').wt := rfl
      omega)
  refine EvalAll.letE dAI fun yv cy hyv' => ?_
  obtain ⟨rfl, hcy⟩ := hyv'
  -- the chain
  have wcv := H.sz.wt_cv (i := 0) hsp.csl hs.fit hs.wl hsp.fit hl hs.fx hfy' (Nat.zero_le _)
  have dArg := Det.mk4 (dS [natList y'] 0 _ rfl) (dS [natList y'] 4 _ rfl) (dA [natList y'] 3 _ rfl)
    (Det.mk4 (dA [natList y'] 2 _ rfl) (dS [natList y'] 3 _ rfl)
      (Det.var' (P := P) (env := a :: [natList y']) (i := 1) rfl) (Det.nat 0))
  have eArg : Val.list [vsQGam I, natList s.x, vsQLowsV lows,
      .list [encGroup cs, vsWVs s.ws, natList y', .nat 0]] = vsQCV I cs s.ws lows s.x y' 0 := rfl
  rw [eArg] at dArg
  have dArg' := dArg.mono (c' := 10 ^ 6 * S ^ 6) (by
    have := wt_list4_le (encGroup cs) (vsWVs s.ws) (natList y') (.nat 0)
    have := wt_nat_le 0
    have ecv : (vsQCV I cs s.ws lows s.x y' 0).wt = (Val.list [vsQGam I, natList s.x,
        vsQLowsV lows, .list [encGroup cs, vsWVs s.ws, natList y', .nat 0]]).wt := rfl
    omega)
  refine EvalAll.letE (Ra := fun r cr => ∃ a2, r = vsQAnsV a2 ∧ VsQAnsOK hP a2 ∧
      cr ≤ 10 ^ 6 * S ^ 6 + (Cn * (lows.length + 1) + St) + 700 * S ^ 6 + 1)
    (EvalAll.call_funAll dArg' fun v ca hv => ?_) fun r cr hr => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hC.mono fun w cb hw => ?_
    obtain ⟨a2, rfl, hok2, hcb⟩ := hw
    refine ⟨a2, rfl, hok2, ?_⟩
    have := H.sz.wt_ans (VsQAnsOK.len (hP := hP) hok2)
    rw [eD] at hcb
    omega
  obtain ⟨a2, rfl, hok2, hcr⟩ := hr
  have wa2 := H.sz.wt_ans (VsQAnsOK.len (hP := hP) hok2)
  have hok2' := vsQ_cos_ans hs.prob hsp.cle htH (htr a2 hok2)
  cases a2 with
  | none =>
    have dt3 : Det P [a, natList y', vsQAnsV (n := I.n) none] (.get (.var 2) (.nat 0)) (.nat 0) _ :=
      Det.get' (Det.var' (i := 2) rfl) (Det.nat 0) (show [Val.nat 0][0]? = some (.nat 0) from rfl)
    refine (EvalAll.vsQ_ite_zero' dt3 (Det.mk1 (Det.nat (P := P)
      (env := [a, natList y', vsQAnsV (n := I.n) none]) 0))).mono ?_
    rintro w cb ⟨ce, ⟨rfl, hce⟩, hcb⟩
    refine ⟨none, rfl, hok2', ?_⟩
    have := wt_list1_le (.nat 0)
    have e0 : (vsQAnsV (n := I.n) none).wt = (Val.list [.nat 0]).wt := rfl
    have := wt_nat_le 0
    omega
  | some r2 =>
    obtain ⟨g, ks⟩ := r2
    set r2v := vsQAnsV (some (g, ks)) with hr2v
    have er2 : r2v = .list [.nat 1, encPerm g, encGroup ks] := rfl
    have dt3 : Det P [a, natList y', r2v] (.get (.var 2) (.nat 0)) (.nat 1) _ :=
      Det.get' (Det.var' (i := 2) rfl) (Det.nat 0) rfl
    have dres := Det.mk3 (Det.nat (P := P) (env := [a, natList y', r2v]) 1)
      (Det.call (Det.mk2 (dT [natList y', r2v]) (Det.get' (Det.var' (i := 2) rfl) (Det.nat 1)
        (show [Val.nat 1, encPerm g, encGroup ks][1]? = some (encPerm g) from rfl)))
        (compose_spec H.hcmp t g))
      (Det.get' (Det.var' (i := 2) rfl) (Det.nat 2)
        (show [Val.nat 1, encPerm g, encGroup ks][2]? = some (encGroup ks) from rfl))
    refine (EvalAll.vsQ_ite_pos' dt3 one_ne_zero dres).mono ?_
    rintro w cb ⟨ct, ⟨rfl, hct⟩, hcb⟩
    refine ⟨some (t * g, ks), rfl, hok2', ?_⟩
    have hkl : ks.length ≤ I.n ^ 2 := (VsQAnsOK.len (hP := hP) hok2) (g, ks) rfl
    have := H.sz.wt_ans (a := some (t * g, ks)) (fun q hq => by
      simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; exact hkl)
    have := H.sz.wt_perm g
    have := H.sz.wt_perm (t * g)
    have := H.sz.wt_group hkl
    have := wt_list2_le (encPerm t) (encPerm g)
    have := wt_list3_le (.nat 1) (encPerm g) (encGroup ks)
    have hn3 : (I.n + 1) ^ 3 ≤ S ^ 6 :=
      (Nat.pow_le_pow_left H.sz.n 3).trans (H.sz.pow_le (by omega))
    have eans : (vsQAnsV (some (t * g, ks))).wt =
      (Val.list [.nat 1, encPerm (t * g), encGroup ks]).wt := rfl
    rw [er2] at wa2
    have := wt_nat_le 1
    have := wt_nat_le 2
    have := wt_nat_le 0
    simp only [permK] at *
    omega

/-! ### The driver -/

set_option maxHeartbeats 8000000 in
open Classical in
/-- **One node of the driver**, given the driver on all states of smaller measure. -/
theorem vsQDrv_step {P : Program} {b ana ai cmp paste E Tm S CA CAI CP Cn c K : ℕ}
    (H : VsQDrvHyp P I b ana ai cmp paste E Tm S CA CAI CP Cn c K) {s : VsQSt I} (hs : VsQStOK s)
    (hD : ∀ (s' : VsQSt I) (hs' : VsQStOK s'), s'.mu < s.mu →
      FunAll P b (vsQStV I s') (VsQDrvOK c K s' hs')) :
    FunAll P b (vsQStV I s) (VsQDrvOK c K s hs) := by
  have hS1 := H.sz.one_le
  have hf0 : P.funs[b]? = some (vsQDrvE ana (b + 3) paste) :=
    H.funs.get (j := 0) (by simp [vsQDrvFuns, mapFuns, loopFuns])
  have hmap : P.HasAt (b + 3) (mapFuns (b + 3) (b + 2)) := H.funs.right
  apply FunAll.intro hf0
  set stV := vsQStV I s with hstV
  have wst : stV.wt ≤ 2000 * S ^ 6 := H.sz.wt_st hs
  have p0 := H.sz.pow_le (show 0 ≤ 6 by omega)
  have p69 := H.sz.pow_le (show 6 ≤ 9 by omega)
  simp only [pow_zero] at p0
  have hCn := H.hCn
  have hBd : Cn ≤ vsQBd c K s.dim s.Ab :=
    vsQBd_ge (by have := H.hc; omega) (by have := H.hK8; omega) _
  refine EvalAll.letE (Ra := fun w cw => VsQAnaOut hs E Tm w ∧ cw ≤ stV.wt + 1 + CA + w.wt + 1)
    (EvalAll.call_funAll (Det.var' (P := P) (env := [stV]) (i := 0) rfl) fun v ca hv => ?_)
    fun w cw hw => ?_
  · obtain ⟨rfl, hca⟩ := hv
    exact (H.hana s hs).mono fun w cb hw => ⟨hw.1, by omega⟩
  obtain ⟨hout, hcw⟩ := hw
  rcases hout with ⟨a, rfl, hok⟩ | ⟨ts, cs, lows, rfl, hsp⟩
  · -- a leaf
    have elf : (vsQLeafV a).wt = (Val.list [.nat 0, vsQAnsV a]).wt := rfl
    have dt : Det P [stV, vsQLeafV a] (.get (.var 1) (.nat 0)) (.nat 0) _ :=
      Det.get' (Det.var' (i := 1) rfl) (Det.nat 0)
        (show [Val.nat 0, vsQAnsV a][0]? = some (.nat 0) from rfl)
    have dr : Det P [stV, vsQLeafV a] (.get (.var 1) (.nat 1)) (vsQAnsV a) _ :=
      Det.get' (Det.var' (i := 1) rfl) (Det.nat 1)
        (show [Val.nat 0, vsQAnsV a][1]? = some (vsQAnsV a) from rfl)
    refine (EvalAll.vsQ_ite_zero' dt dr).mono ?_
    rintro w cb ⟨ce, ⟨rfl, hce⟩, hcb⟩
    refine ⟨a, rfl, hok, ?_⟩
    have wa := H.sz.wt_ans (VsQAnsOK.len (hP := hs.prob) hok)
    have := wt_list2_le (.nat 0) (vsQAnsV a)
    have := wt_nat_le 0
    have := wt_nat_le 1
    omega
  -- a split
  set abC := VsQAb I (gens cs) (vsQSp I s.ws) (vsQSp I s.ws') with habCdef
  set St := ((vsQDims I (s.ws :: lows)).map fun e => vsQBd c K e abC).sum with hSt
  have hdc := vsQDims_chain s.ws lows hsp.chain
  have hlen : (vsQDims I (s.ws :: lows)).length = lows.length := by rw [vsQDims_length]; simp
  have hsum : (vsQDims I (s.ws :: lows)).sum = s.dim := by
    have h2 := hdc.2
    have e1 : vsQRk I ((s.ws :: lows).getLast (List.cons_ne_nil _ _)) = vsQRk I s.ws' := by
      unfold vsQRk; rw [List.getLast_cons hsp.ne, hsp.last]
    unfold VsQSt.dim; omega
  have hμ : ∀ e ∈ vsQDims I (s.ws :: lows), 2 * e + (if abC then 0 else 1) < s.mu := by
    intro e he
    unfold VsQSt.mu
    rcases hsp.case with ⟨_, h2⟩ | ⟨_, h2, _⟩ | ⟨hab, h1, habC, _, _⟩
    · have := vsQ_lt_sum hdc.1 (by omega) he; split_ifs <;> omega
    · have := vsQ_lt_sum hdc.1 (by omega) he; split_ifs <;> omega
    · have hds : vsQDims I (s.ws :: lows) = [s.dim] := by
        obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp (hlen.trans h1)
        rw [hu] at hsum ⊢
        simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
        rw [hsum]
      rw [hds, List.mem_singleton] at he
      rw [if_pos habC, if_neg hab]
      omega
  set spV := vsQSplitV ts cs lows with hspV
  have wsp : spV.wt ≤ 2000 * S ^ 6 := H.sz.wt_split hsp
  have esp : spV.wt = (Val.list [.nat 1, .list (ts.map encPerm), encGroup cs,
    vsQLowsV lows]).wt := rfl
  have wL := wt_le_wt_list (show Val.list (ts.map encPerm) ∈ [.nat 1, .list (ts.map encPerm),
    encGroup cs, vsQLowsV lows] by simp)
  have dt : Det P [stV, spV] (.get (.var 1) (.nat 0)) (.nat 1) _ :=
    Det.get' (Det.var' (i := 1) rfl) (Det.nat 0)
      (show [Val.nat 1, .list (ts.map encPerm), encGroup cs, vsQLowsV lows][0]? = some (.nat 1)
        from rfl)
  have dArg := Det.mk2 (Det.mk2 (Det.var' (P := P) (env := [stV, spV]) (i := 0) rfl)
    (Det.var' (P := P) (env := [stV, spV]) (i := 1) rfl)) (Det.get' (Det.var' (i := 1) rfl)
      (Det.nat 1) (show [Val.nat 1, .list (ts.map encPerm), encGroup cs, vsQLowsV lows][1]? =
        some (.list (ts.map encPerm)) from rfl))
  have wctx := wt_list2_le stV spV
  have warg := wt_list2_le (.list [stV, spV]) (.list (ts.map encPerm))
  have dArg' := dArg.mono (c' := 10 ^ 5 * S ^ 6) (by have := wt_nat_le 1; omega)
  -- the cosets
  have hTF : ∀ x ∈ ts.map encPerm, FunAll P (b + 2) (.list [.list [stV, spV], x])
      (fun w cost => (∃ a, w = vsQAnsV a ∧ ∀ t', x = encPerm t' → VsQCosOK hs.prob hsp.cle t' a) ∧
        cost ≤ CAI + 10 ^ 7 * S ^ 6 + (Cn * (lows.length + 1) + St)) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    refine (vsQTf_spec H hD hs hsp hμ ht).mono fun w cost hw => ?_
    obtain ⟨a, rfl, hok, hc⟩ := hw
    exact ⟨⟨a, rfl, fun t' he => by cases encPerm_injective he; exact hok⟩, hc⟩
  have hM := map_spec hmap hTF
  have eB : ((ts.map encPerm).map fun _ => CAI + 10 ^ 7 * S ^ 6 + (Cn * (lows.length + 1) + St)).sum
      = ts.length * (CAI + 10 ^ 7 * S ^ 6 + (Cn * (lows.length + 1) + St)) := by
    rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul]
  have hTS : ts.length + 1 ≤ S := by have := hsp.tl; have := H.sz.t; omega
  have p67 := H.sz.pow_le (show 6 ≤ 7 by omega)
  have p78 := H.sz.pow_le (show 7 ≤ 8 by omega)
  have p89 := H.sz.pow_le (show 8 ≤ 9 by omega)
  have e7 : S * S ^ 6 = S ^ 7 := by ring
  have e8 : S * S ^ 7 = S ^ 8 := by ring
  set BT := CAI + 10 ^ 7 * S ^ 6 + (Cn * (lows.length + 1) + St) with hBT
  have hthen : EvalAll P [stV, spV]
      (.call paste (.call (b + 3) (mk2 (mk2 (.var 0) (.var 1)) (.get (.var 1) (.nat 1)))))
      (fun w c' => ∃ a, w = vsQAnsV a ∧ VsQAnsOK hs.prob a ∧
        c' ≤ CP + ts.length * BT + 10 ^ 9 * S ^ 9) := by
    refine EvalAll.call_funAll (Ra := fun v cr => ∃ rs, v = .list (rs.map vsQAnsV) ∧
        List.Forall₂ (fun t a => VsQCosOK hs.prob hsp.cle t a) ts rs ∧
        cr ≤ ts.length * BT + 10 ^ 8 * S ^ 8)
      (EvalAll.call_funAll dArg' fun v ca hv => ?_) fun v ca hv => ?_
    · obtain ⟨rfl, hca⟩ := hv
      refine hM.mono fun w cost hw => ?_
      obtain ⟨wsl, rfl, hR, hcost⟩ := hw
      obtain ⟨rs, rfl, hF⟩ := vsQ_forall₂_ans ts wsl (List.forall₂_map_left_iff.mp hR)
      have hF' : List.Forall₂ (fun t a => VsQCosOK hs.prob hsp.cle t a) ts rs :=
        hF.imp fun t a h => h t rfl
      refine ⟨rs, rfl, hF', ?_⟩
      have hrl := hF'.length_eq
      have wrs := vs_wt_list_le_of (rs.map vsQAnsV) (c := 700 * S ^ 6) (by
        intro v hv
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
        have := (List.forall₂_iff_get.mp hF').2 i (by omega) hi
        exact H.sz.wt_ans (VsQCosOK.len this))
      rw [List.length_map] at wrs
      rw [eB] at hcost
      have h1 : rs.length * (2 * (700 * S ^ 6) + 1) ≤ S * (1401 * S ^ 6) :=
        Nat.mul_le_mul (by omega) (by omega)
      have e1 : S * (1401 * S ^ 6) = 1401 * S ^ 7 := by rw [← e7]; ring
      have hX : (Val.list [.list [stV, spV], .list (ts.map encPerm)]).wt +
          (Val.list (rs.map vsQAnsV)).wt + 1 ≤ 30000 * S ^ 7 := by omega
      have h2 : ((ts.map encPerm).length + 1) * ((Val.list [.list [stV, spV],
          .list (ts.map encPerm)]).wt + (Val.list (rs.map vsQAnsV)).wt + 1) ≤
          S * (30000 * S ^ 7) := Nat.mul_le_mul (by simp; omega) hX
      have e2 : S * (30000 * S ^ 7) = 30000 * S ^ 8 := by rw [← e8]; ring
      have e3 : mapK * ((ts.map encPerm).length + 1) * ((Val.list [.list [stV, spV],
          .list (ts.map encPerm)]).wt + (Val.list (rs.map vsQAnsV)).wt + 1) =
          1000 * (((ts.map encPerm).length + 1) * ((Val.list [.list [stV, spV],
          .list (ts.map encPerm)]).wt + (Val.list (rs.map vsQAnsV)).wt + 1)) := by
        simp only [mapK]; ring
      omega
    · obtain ⟨rs, rfl, hF, hca⟩ := hv
      have hrl := hF.length_eq
      have hlens : ∀ a ∈ rs, ∀ r ∈ a, r.2.length ≤ I.n ^ 2 := by
        intro a ha
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
        exact VsQCosOK.len ((List.forall₂_iff_get.mp hF).2 i (by omega) hi)
      refine FunAll.mono (H.hpaste rs (by have := hsp.tl; omega) hlens) fun w cb hw => ?_
      obtain ⟨rfl, hcb⟩ := hw
      have hok := vsQ_paste hs.prob hsp.cle ts hsp.tmem hsp.cov rs hrl.symm
        (fun i hi => (List.forall₂_iff_get.mp hF).2 i hi (by omega))
      refine ⟨vsQPaste rs, rfl, hok, ?_⟩
      have := H.sz.wt_ans (VsQAnsOK.len (hP := hs.prob) hok)
      omega
  refine (EvalAll.vsQ_ite_pos' dt one_ne_zero hthen).mono ?_
  rintro w cb ⟨ct, ⟨a, rfl, hok, hct⟩, hcb⟩
  refine ⟨a, rfl, hok, ?_⟩
  have wa := H.sz.wt_ans (VsQAnsOK.len (hP := hs.prob) hok)
  have hnode := vsQ_node_cost H.hc H.hK H.hK8 (ds := vsQDims I (s.ws :: lows)) (ab := s.Ab)
    (abC := abC) (T := ts.length) hdc.1 hsum (fun h => h.mono hsp.cle le_rfl le_rfl)
    (by rw [hlen]; exact hsp.case)
  rw [hlen] at hnode
  have q1 : ts.length * BT = ts.length * (CAI + 10 ^ 7 * S ^ 6) +
      ts.length * (Cn * (lows.length + 1)) + ts.length * St := by rw [hBT]; ring
  have q2 : ts.length * (CAI + 10 ^ 7 * S ^ 6) ≤ ts.length * (Cn * (lows.length + 1)) :=
    Nat.mul_le_mul_left _ ((show CAI + 10 ^ 7 * S ^ 6 ≤ Cn by omega).trans
      (Nat.le_mul_of_pos_right _ (by omega)))
  have q3 : 2 * Cn * (1 + ts.length * (lows.length + 1)) =
      2 * Cn + 2 * (ts.length * (Cn * (lows.length + 1))) := by ring
  have q4 : ts.length * St = ts.length *
      ((vsQDims I (s.ws :: lows)).map fun e => vsQBd c K e abC).sum := rfl
  have := wt_nat_le 1
  omega

/-- **The driver.** On every valid state the driver returns a correct answer within the bound
`vsQBd c K D ab`. The proof is a strong induction on the measure `VsQSt.mu`. -/
theorem vsQDrv_spec {P : Program} {b ana ai cmp paste E Tm S CA CAI CP Cn c K : ℕ}
    (H : VsQDrvHyp P I b ana ai cmp paste E Tm S CA CAI CP Cn c K) (s : VsQSt I)
    (hs : VsQStOK s) : FunAll P b (vsQStV I s) (VsQDrvOK c K s hs) := by
  have key : ∀ k (s : VsQSt I) (hs : VsQStOK s), s.mu = k →
      FunAll P b (vsQStV I s) (VsQDrvOK c K s hs) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s hs hk
      exact vsQDrv_step H hs fun s' hs' h => ih s'.mu (hk ▸ h) s' hs' rfl
  exact key _ s hs rfl

end GI.Impl
