module

public import Workspace.Impl.VsQDrvDefs

@[expose] public section

/-!
# The chain of the driver

The chain program `vsQDrvCE` solves the problem `(K, U, W', x, y)` along a strict chain
`U > L_i > L_{i+1} > … > W'` of `K`-invariant subspaces: it calls the driver on the top step,
moves the target by the solution found, and calls itself on the rest with the stabilizer of the
top step (`vsQDrvC_spec`). The driver itself is a hypothesis here (`hD`), for all states of
measure below `m`; the induction on the measure is done in `Impl/VsQDrv.lean`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-! ### Helpers -/

theorem Det.mk6' {P : Program} {env : List Val} {a b c d e f : Expr} {va vb vc vd ve vf : Val}
    {ca cb cc cd ce cf : ℕ} (ha : Det P env a va ca) (hb : Det P env b vb cb)
    (hc : Det P env c vc cc) (hd : Det P env d vd cd) (he : Det P env e ve ce)
    (hf : Det P env f vf cf) :
    Det P env (mk6 a b c d e f) (.list [va, vb, vc, vd, ve, vf])
      (ca + cb + cc + cd + ce + cf + 6 * (Val.list [va, vb, vc, vd, ve, vf]).wt + 12) := by
  have h1 := wt_list_mono (show [va, vb, vc, vd] <+: [va, vb, vc, vd, ve, vf] from ⟨[ve, vf], rfl⟩)
  have h2 := wt_list_mono (show [va, vb, vc, vd, ve] <+: [va, vb, vc, vd, ve, vf] from ⟨[vf], rfl⟩)
  exact (Det.snoc (Det.snoc (Det.mk4 ha hb hc hd) he) hf).mono
    (by simp only [List.cons_append, List.nil_append] at *; omega)

theorem EvalAll.vsQ_ite_pos' {P : Program} {env : List Val} {c t e : Expr} {x cc : ℕ}
    {R : Val → ℕ → Prop} (hc : Det P env c (.nat x) cc) (hx : x ≠ 0) (ht : EvalAll P env t R) :
    EvalAll P env (.ite c t e) (fun w c' => ∃ ct, R w ct ∧ c' ≤ cc + ct + w.wt + 1) :=
  EvalAll.ite hc (fun _ _ h => ⟨x, h.1⟩) fun y cc' h => by
    obtain ⟨h1, h2⟩ := h
    cases h1
    rw [if_neg hx]
    exact ht.mono fun w ct hw => ⟨ct, hw, by omega⟩

theorem EvalAll.vsQ_ite_zero' {P : Program} {env : List Val} {c t e : Expr} {cc : ℕ}
    {R : Val → ℕ → Prop} (hc : Det P env c (.nat 0) cc) (he : EvalAll P env e R) :
    EvalAll P env (.ite c t e) (fun w c' => ∃ ce, R w ce ∧ c' ≤ cc + ce + w.wt + 1) :=
  EvalAll.ite hc (fun _ _ h => ⟨0, h.1⟩) fun y cc' h => by
    obtain ⟨h1, h2⟩ := h
    cases h1
    rw [if_pos rfl]
    exact he.mono fun w ct hw => ⟨ct, hw, by omega⟩

/-- In a strict chain the last space lies in the first. -/
theorem vsQChain_last_le : ∀ (a : List (List ℕ)) (L : List (List (List ℕ))), VsQChain I (a :: L) →
    vsQSp I ((a :: L).getLast (List.cons_ne_nil _ _)) ≤ vsQSp I a
  | a, [], _ => le_rfl
  | a, b :: L, h => by
    have h1 := (List.isChain_cons_cons.mp h).1
    have h2 := vsQChain_last_le b L (List.isChain_cons_cons.mp h).2
    rw [List.getLast_cons_cons]
    exact h2.trans h1.le

/-! ### Hypotheses of the driver -/

/-- The hypotheses of the driver: its program, the subprograms it calls with their costs, the
size bound and the constants of the cost bound. -/
structure VsQDrvHyp (P : Program) (I : VecStabInst) (b ana ai cmp paste E Tm S CA CAI CP Cn c K : ℕ) :
    Prop where
  funs : P.HasAt b (vsQDrvFuns b ana ai cmp paste)
  hcmp : P.HasAt cmp (composeFuns cmp)
  hai : ∀ t ∈ gens I.gs, ∀ y, VsWFit I.p I.d [y] →
    FunDet P ai (.list [vsQGam I, encPerm t, natList y]) (natList (vsQApp I t y)) CAI
  hpaste : ∀ rs : List (Option (Perm (Fin I.n) × List (Perm (Fin I.n)))), rs.length ≤ Tm →
    (∀ a ∈ rs, ∀ r ∈ a, r.2.length ≤ I.n ^ 2) →
    FunDet P paste (.list (rs.map vsQAnsV)) (vsQAnsV (vsQPaste rs)) CP
  hana : ∀ (s : VsQSt I) (hs : VsQStOK s),
    FunAll P ana (vsQStV I s) (fun w cost => VsQAnaOut hs E Tm w ∧ cost ≤ CA)
  sz : VsQDSz I S Tm
  hCn : CA + CP + CAI + 10 ^ 10 * S ^ 9 ≤ Cn
  hc : 20 * Cn ≤ c
  hK : 2 * E + 2 ≤ K
  hK8 : 8 ≤ K

/-- What the driver returns on a valid state. -/
def VsQDrvOK (c K : ℕ) (s : VsQSt I) (hs : VsQStOK s) (w : Val) (cost : ℕ) : Prop :=
  ∃ a, w = vsQAnsV a ∧ VsQAnsOK hs.prob a ∧ cost ≤ vsQBd c K s.dim s.Ab

theorem VsQAnsOK.len {H : Subgroup (Perm (Fin I.n))} {W W' : Submodule (ZMod I.p) (VsQV I)}
    {x y : VsQV I} {hP : VsQProb I H W W' x y} {a : Option (Perm (Fin I.n) × List (Perm (Fin I.n)))}
    (h : VsQAnsOK hP a) : ∀ r ∈ a, r.2.length ≤ I.n ^ 2 := by
  intro r hr
  cases a with
  | none => simp at hr
  | some a => simp only [Option.mem_def, Option.some.injEq] at hr; subst hr; exact h.2.2

open Classical in
/-- **The chain.** -/
theorem vsQDrvC_spec {P : Program} {b ana ai cmp paste E Tm S CA CAI CP Cn c K : ℕ}
    (H : VsQDrvHyp P I b ana ai cmp paste E Tm S CA CAI CP Cn c K) {m : ℕ}
    (hD : ∀ (s : VsQSt I) (hs : VsQStOK s), s.mu < m → FunAll P b (vsQStV I s) (VsQDrvOK c K s hs))
    (abC : Prop) :
    ∀ (k : ℕ) (ks : List (Perm (Fin I.n))) (upper : List (List ℕ)) (lows : List (List (List ℕ)))
      (x y : List ℕ) (i : ℕ), lows.length - i = k → i ≤ lows.length →
      ks.length ≤ I.n ^ 2 → VsWFit I.p I.d upper → upper.length ≤ I.d →
      (∀ u ∈ lows, VsWFit I.p I.d u ∧ u.length ≤ I.d) → lows.length ≤ I.d →
      VsWFit I.p I.d [x] → VsWFit I.p I.d [y] →
      ∀ hP : VsQProb I (gens ks) (vsQSp I upper)
        (vsQSp I ((upper :: lows.drop i).getLast (List.cons_ne_nil _ _)))
        (vsWV I.p I.d x) (vsWV I.p I.d y),
      VsQChain I (upper :: lows.drop i) →
      (∀ u ∈ lows.drop i, VsQInv I (gens ks) (vsQSp I u)) →
      (abC → VsQAb I (gens ks) (vsQSp I upper)
        (vsQSp I ((upper :: lows.drop i).getLast (List.cons_ne_nil _ _)))) →
      (∀ e ∈ vsQDims I (upper :: lows.drop i), 2 * e + (if abC then 0 else 1) < m) →
      FunAll P (b + 1) (vsQCV I ks upper lows x y i) (fun w cost => ∃ a, w = vsQAnsV a ∧
        VsQAnsOK hP a ∧ cost ≤ Cn * (k + 1) +
          ((vsQDims I (upper :: lows.drop i)).map fun e => vsQBd c K e abC).sum) := by
  have hS1 := H.sz.one_le
  have hSn := H.sz.n
  have hSd := H.sz.d
  have hf1 : P.funs[b + 1]? = some (vsQDrvCE b (b + 1) ai cmp) :=
    H.funs.get (j := 1) (by simp [vsQDrvFuns, mapFuns, loopFuns])
  intro k
  induction k with
  | zero =>
    intro ks upper lows x y i hk hi hks hu hul hf hl hx hy hP hch hinv habC hμ
    have hd : lows.drop i = [] := List.drop_eq_nil_of_le (by omega)
    have hil : i = lows.length := by omega
    apply FunAll.intro hf1
    set a := vsQCV I ks upper lows x y i with ha
    set cur := Val.list [encGroup ks, vsWVs upper, natList y, .nat i] with hcur
    have dA2 := Det.arg' (P := P) (vs := [vsQGam I, natList x, vsQLowsV lows, cur]) (rest := [])
      (j := 2) rfl
    have dA3 := Det.arg' (P := P) (vs := [vsQGam I, natList x, vsQLowsV lows, cur]) (rest := [])
      (j := 3) rfl
    have dt : Det P [a] (.arith .sub (.length (arg 2)) (vsQCur 3)) (.nat 0) _ :=
      Det.arith' (Det.length dA2) (Det.get' dA3 (Det.nat 3) rfl)
        (by simp [GI.Machine.BinOp.eval]; omega)
    have dG := Det.get' dA3 (Det.nat 0)
      (show [encGroup ks, vsWVs upper, natList y, Val.nat i][0]? = some (encGroup ks) from rfl)
    have d1 := Det.get' (Det.get' dG (Det.nat 1)
      (show [Val.nat I.n, .list ((1 :: ks).map encPerm)][1]? = some (.list ((1 :: ks).map encPerm))
        from rfl)) (Det.nat 0)
      (show ((1 :: ks).map encPerm)[0]? = some (encPerm (1 : Perm (Fin I.n))) from rfl)
    have dres := Det.mk3 (Det.nat (P := P) (env := [a]) 1) d1 dG
    refine (EvalAll.vsQ_ite_zero' dt dres).mono fun w cost hw => ?_
    obtain ⟨ce, ⟨rfl, hce⟩, hcost⟩ := hw
    have hP1 : VsQProb I (gens ks) (vsQSp I upper) (vsQSp I upper) (vsWV I.p I.d x)
        (vsWV I.p I.d y) := by
      have := hP; simp only [hd, List.getLast_singleton] at this; exact this
    refine ⟨some (1, ks), rfl, VsQAnsOK.congr hP1 hP (by simp [hd]) (vsQ_ans_top hP1 rfl hks), ?_⟩
    -- the cost
    have wa := H.sz.wt_cv (i := i) hks hu hul hf hl hx hy (by omega)
    have wG := H.sz.wt_group hks
    have w1 := H.sz.wt_perm (1 : Perm (Fin I.n))
    have w3 := wt_list3_le (.nat 1) (encPerm (1 : Perm (Fin I.n))) (encGroup ks)
    have wc := wt_le_wt_list (show cur ∈ [vsQGam I, natList x, vsQLowsV lows, cur] by simp)
    have wcG := wt_le_wt_list (show encGroup ks ∈ [encGroup ks, vsWVs upper, natList y, Val.nat i] by simp)
    have ea : a.wt = (Val.list [vsQGam I, natList x, vsQLowsV lows, cur]).wt := rfl
    have ea' : a.wt = (vsQCV I ks upper lows x y i).wt := rfl
    have ec' : cur.wt = (Val.list [encGroup ks, vsWVs upper, natList y, Val.nat i]).wt := rfl
    have hpl : (lows.map vsWVs).length ≤ S := by simp; omega
    have eG : (encGroup ks).wt = (Val.list [Val.nat I.n, .list ((1 :: ks).map encPerm)]).wt := rfl
    have wL := wt_le_wt_list (show Val.list ((1 :: ks).map encPerm) ∈
      [Val.nat I.n, .list ((1 :: ks).map encPerm)] by simp)
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 3
    have := wt_nat_le (vsQLowsV lows |> fun _ => lows.length)
    have hlS : lows.length ≤ S := by omega
    have p26 := H.sz.pow_le (show 2 ≤ 6 by omega)
    have p69 := H.sz.pow_le (show 6 ≤ 9 by omega)
    have p0 := H.sz.pow_le (show 0 ≤ 6 by omega)
    have p16 := H.sz.pow_le (show 1 ≤ 6 by omega)
    simp only [pow_zero, pow_one] at p0 p16
    have := wt_nat_le i
    have hC := H.hCn
    simp only [hd, vsQDims_single, List.map_nil, List.sum_nil, add_zero, zero_add, mul_one]
    have eL : ((lows.map vsWVs).length) = lows.length := by simp
    simp only [vsQLowsV] at *
    omega
  | succ k ih =>
    intro ks upper lows x y i hk hi hks hu hul hf hl hx hy hP hch hinv habC hμ
    have hiL : i < lows.length := by omega
    have hdrop : lows.drop i = lows[i] :: lows.drop (i + 1) := List.drop_eq_getElem_cons hiL
    set u := lows[i] with hudef
    have hum : u ∈ lows := List.getElem_mem hiL
    set rest := lows.drop (i + 1) with hrest
    rw [hdrop] at hch hinv hμ
    have hlast : vsQSp I ((u :: rest).getLast (List.cons_ne_nil _ _)) =
        vsQSp I ((upper :: lows.drop i).getLast (List.cons_ne_nil _ _)) := by
      simp only [hdrop, List.getLast_cons_cons]
    have hchu : VsQChain I (u :: rest) := (List.isChain_cons_cons.mp hch).2
    have hUlt : vsQSp I u < vsQSp I upper := (List.isChain_cons_cons.mp hch).1
    have hUW : vsQSp I u ≤ vsQSp I upper := hUlt.le
    have hWU : vsQSp I ((upper :: lows.drop i).getLast (List.cons_ne_nil _ _)) ≤ vsQSp I u := by
      rw [← hlast]; exact vsQChain_last_le u rest hchu
    have hU : VsQInv I (gens ks) (vsQSp I u) := hinv u (by simp)
    -- the child state
    set s' : VsQSt I := ⟨ks, u, upper, x, y⟩ with hs'def
    have hs' : VsQStOK s' :=
      ⟨hP.upper hUW hU, hks, hu, (hf u hum).1, hul, (hf u hum).2, hx, hy⟩
    set e := vsQRk I upper - vsQRk I u with he
    have hdims : vsQDims I (upper :: u :: rest) = e :: vsQDims I (u :: rest) := rfl
    have hμe := hμ e (by rw [hdims]; simp)
    have hmu : s'.mu < m := by
      unfold VsQSt.mu
      have hdim : s'.dim = e := rfl
      rw [hdim]
      by_cases hab : abC
      · have : s'.Ab := (habC hab).mono le_rfl le_rfl hWU
        rw [if_pos this]; rw [if_pos hab] at hμe; omega
      · rw [if_neg hab] at hμe; split_ifs <;> omega
    have hbd : vsQBd c K e s'.Ab ≤ vsQBd c K e abC :=
      vsQBd_mono (fun hab => (habC hab).mono le_rfl le_rfl hWU) (by have := H.hK8; omega)
    apply FunAll.intro hf1
    set a := vsQCV I ks upper lows x y i with ha
    set cur := Val.list [encGroup ks, vsWVs upper, natList y, .nat i] with hcur
    have dA0 := Det.arg' (P := P) (vs := [vsQGam I, natList x, vsQLowsV lows, cur]) (rest := [])
      (j := 0) rfl
    have dA1 := Det.arg' (P := P) (vs := [vsQGam I, natList x, vsQLowsV lows, cur]) (rest := [])
      (j := 1) rfl
    have dA2 := Det.arg' (P := P) (vs := [vsQGam I, natList x, vsQLowsV lows, cur]) (rest := [])
      (j := 2) rfl
    have dA3 := Det.arg' (P := P) (vs := [vsQGam I, natList x, vsQLowsV lows, cur]) (rest := [])
      (j := 3) rfl
    have dC : ∀ (j : ℕ) (v : Val), [encGroup ks, vsWVs upper, natList y, Val.nat i][j]? = some v →
        Det P [a] (vsQCur j) v _ := fun j v hv => Det.get' dA3 (Det.nat j) hv
    have dt : Det P [a] (.arith .sub (.length (arg 2)) (vsQCur 3)) (.nat (k + 1)) _ :=
      Det.arith' (Det.length dA2) (dC 3 _ rfl) (by simp [GI.Machine.BinOp.eval]; omega)
    have dU : Det P [a] (.get (arg 2) (vsQCur 3)) (vsWVs u) _ :=
      Det.get' dA2 (dC 3 _ rfl) (by
        simp only [vsQLowsV, List.getElem?_map]; rw [List.getElem?_eq_getElem hiL]; rfl)
    have dArg := Det.mk6' dA0 (dC 0 _ rfl) dU (dC 1 _ rfl) dA1 (dC 2 _ rfl)
    have eArg : Val.list [vsQGam I, encGroup ks, vsWVs u, vsWVs upper, natList x, natList y] =
      vsQStV I s' := rfl
    rw [eArg] at dArg
    -- weights and clean bounds
    have wa := H.sz.wt_cv (i := i) hks hu hul hf hl hx hy (by omega)
    have ea' : a.wt = (vsQCV I ks upper lows x y i).wt := rfl
    have ea : a.wt = (Val.list [vsQGam I, natList x, vsQLowsV lows, cur]).wt := rfl
    have wcur := wt_le_wt_list (show cur ∈ [vsQGam I, natList x, vsQLowsV lows, cur] by simp)
    have ecur : cur.wt = (Val.list [encGroup ks, vsWVs upper, natList y, Val.nat i]).wt := rfl
    have wst := H.sz.wt_st hs'
    have p0 := H.sz.pow_le (show 0 ≤ 6 by omega)
    have p16 := H.sz.pow_le (show 1 ≤ 6 by omega)
    have p26 := H.sz.pow_le (show 2 ≤ 6 by omega)
    have p69 := H.sz.pow_le (show 6 ≤ 9 by omega)
    simp only [pow_zero, pow_one] at p0 p16
    have hiS : i ≤ S := by omega
    have wi := wt_nat_le i
    have wi1 := wt_nat_le (i + 1)
    have w0 := wt_nat_le 0; have w1 := wt_nat_le 1; have w2 := wt_nat_le 2; have w3 := wt_nat_le 3
    have wk := wt_nat_le (k + 1)
    have hkS : k + 1 ≤ S := by omega
    have eaa : (Val.list [vsQGam I, natList x, vsQLowsV lows, cur]).wt = (Val.list [vsQGam I,
        natList x, vsQLowsV lows, Val.list [encGroup ks, vsWVs upper, natList y, Val.nat i]]).wt := rfl
    have hEnt : ∀ v ∈ [vsQGam I, natList x, vsQLowsV lows, cur], v.wt < a.wt :=
      fun v hv => wt_le_wt_list hv
    have hEntC : ∀ v ∈ [encGroup ks, vsWVs upper, natList y, Val.nat i], v.wt < cur.wt :=
      fun v hv => wt_le_wt_list hv
    have dArg' : Det P [a] (mk6 (arg 0) (vsQCur 0) (.get (arg 2) (vsQCur 3)) (vsQCur 1) (arg 1)
        (vsQCur 2)) (vsQStV I s') (10 ^ 5 * S ^ 6) := dArg.mono (by
      have := hEnt _ (by simp : vsQLowsV lows ∈ _)
      have := hEnt _ (by simp : vsQGam I ∈ _)
      have := hEnt _ (by simp : natList x ∈ _)
      have := hEntC _ (by simp : encGroup ks ∈ _)
      have := hEntC _ (by simp : vsWVs upper ∈ _)
      have := hEntC _ (by simp : natList y ∈ _)
      have hvu : (vsWVs u).wt < (vsQLowsV lows).wt := wt_le_wt_list (by
        simp only [List.mem_map]; exact ⟨u, hum, rfl⟩)
      have est : (vsQStV I s').wt =
        (Val.list [vsQGam I, encGroup ks, vsWVs u, vsWVs upper, natList x, natList y]).wt := rfl
      omega)
    have dt' : Det P [a] (.arith .sub (.length (arg 2)) (vsQCur 3)) (.nat (k + 1)) (10 ^ 5 * S ^ 6) :=
      dt.mono (by
        have := hEnt _ (by simp : vsQLowsV lows ∈ _)
        have hll : (lows.map vsWVs).length ≤ S := by simp; omega
        simp only [vsQLowsV] at *
        omega)
    have hzle : ∀ {zs : List (Perm (Fin I.n))} {z : Perm (Fin I.n)},
        VsQAnsOK hs'.prob (some (z, zs)) → gens zs ≤ gens ks := by
      intro zs z h; rw [h.2.1]; exact vsQStab_le
    set St := ((vsQDims I (u :: rest)).map fun e => vsQBd c K e abC).sum with hSt
    have hC := H.hCn
    refine (EvalAll.vsQ_ite_pos' (R := fun w c' => ∃ a, w = vsQAnsV a ∧ VsQAnsOK hP a ∧
        c' ≤ CAI + 10 ^ 7 * S ^ 6 + vsQBd c K e abC + (Cn * (k + 1) + St)) dt' (by omega) ?_).mono ?_
    rotate_left
    · rintro w cost ⟨ct, ⟨a', rfl, hok, hct⟩, hcost⟩
      refine ⟨a', rfl, hok, ?_⟩
      rw [hdrop, hdims]
      simp only [List.map_cons, List.sum_cons]
      have := H.sz.wt_ans (VsQAnsOK.len (hP := hP) hok)
      have : Cn * (k + 1 + 1) = Cn * (k + 1) + Cn := by ring
      omega
    -- the call on the top step
    refine EvalAll.letE (Ra := fun r cr => ∃ a1, r = vsQAnsV a1 ∧ VsQAnsOK hs'.prob a1 ∧
        cr ≤ 10 ^ 5 * S ^ 6 + vsQBd c K e s'.Ab + 700 * S ^ 6 + 1)
      (EvalAll.call_funAll dArg' fun v ca hv => ?_) fun r cr hr => ?_
    · obtain ⟨rfl, hca⟩ := hv
      refine (hD s' hs' hmu).mono fun w cb hw => ?_
      obtain ⟨a1, rfl, hok, hcb⟩ := hw
      refine ⟨a1, rfl, hok, ?_⟩
      have := H.sz.wt_ans (VsQAnsOK.len (hP := hs'.prob) hok)
      have hdim : s'.dim = e := rfl
      rw [hdim] at hcb
      omega
    obtain ⟨a1, rfl, hok1, hcr⟩ := hr
    have wr := H.sz.wt_ans (VsQAnsOK.len (hP := hs'.prob) hok1)
    cases a1 with
    | none =>
      have dt1 : Det P [a, vsQAnsV (n := I.n) none] (.get (.var 1) (.nat 0)) (.nat 0) _ :=
        Det.get' (Det.var' (i := 1) rfl) (Det.nat 0) (show [Val.nat 0][0]? = some (.nat 0) from rfl)
      refine (EvalAll.vsQ_ite_zero' dt1 (Det.mk1 (Det.nat (P := P) (env := [a, vsQAnsV (n := I.n) none]) 0))).mono ?_
      rintro w cb ⟨ce, ⟨rfl, hce⟩, hcb⟩
      refine ⟨none, rfl, vsQSol_chain_empty hWU hok1, ?_⟩
      have := wt_list1_le (.nat 0)
      have : vsQBd c K e s'.Ab ≤ vsQBd c K e abC := hbd
      have e0 : (vsQAnsV (n := I.n) none).wt = (Val.list [.nat 0]).wt := rfl
      omega
    | some r1 =>
      obtain ⟨z, zs⟩ := r1
      have hok1' := hok1
      obtain ⟨hz1, hzs, hzl⟩ := hok1'
      have hzG : z ∈ gens I.gs := hP.le hz1.1
      have hzle' : gens zs ≤ gens ks := hzle hok1
      obtain ⟨hP2, hcomb⟩ := vsQ_chain_ans hP hWU hUW hU hok1
      set y' := vsQApp I z y with hy'
      have hP4 : VsQProb I (gens zs) (vsQSp I u)
          (vsQSp I ((upper :: lows.drop i).getLast (List.cons_ne_nil _ _)))
          (vsWV I.p I.d x) (vsWV I.p I.d y') := by
        rw [hy', vsQApp_vsWV]; exact hP2
      have hP3 : VsQProb I (gens zs) (vsQSp I u)
          (vsQSp I ((u :: lows.drop (i + 1)).getLast (List.cons_ne_nil _ _)))
          (vsWV I.p I.d x) (vsWV I.p I.d y') := by
        rw [hlast]; exact hP4
      have htr : ∀ a2, VsQAnsOK hP3 a2 → VsQAnsOK hP2 a2 := fun a2 h =>
        VsQAnsOK.congr_y hP4 hP2 (vsQApp_vsWV y) (VsQAnsOK.congr hP3 hP4 hlast h)
      set r := vsQAnsV (some (z, zs)) with hr
      have er : r = .list [.nat 1, encPerm z, encGroup zs] := rfl
      have dt1 : Det P [a, r] (.get (.var 1) (.nat 0)) (.nat 1) _ :=
        Det.get' (Det.var' (i := 1) rfl) (Det.nat 0) rfl
      have dz : ∀ rest' : List Val, Det P (a :: r :: rest') (.get (.var 1) (.nat 1)) (encPerm z) _ :=
        fun rest' => Det.get' (Det.var' (i := 1) rfl) (Det.nat 1) rfl
      have dzs : ∀ rest' : List Val, Det P (a :: r :: rest') (.get (.var 1) (.nat 2)) (encGroup zs) _ :=
        fun rest' => Det.get' (Det.var' (i := 1) rfl) (Det.nat 2) rfl
      have dA : ∀ (rest' : List Val) (j : ℕ) (v : Val),
          [vsQGam I, natList x, vsQLowsV lows, cur][j]? = some v → Det P (a :: rest') (arg j) v _ :=
        fun rest' j v hv => Det.arg' hv
      have dCr : ∀ (rest' : List Val) (j : ℕ) (v : Val),
          [encGroup ks, vsWVs upper, natList y, Val.nat i][j]? = some v →
          Det P (a :: rest') (vsQCur j) v _ :=
        fun rest' j v hv => Det.get' (dA rest' 3 cur rfl) (Det.nat j) hv
      have wz := H.sz.wt_perm z
      have wzs := H.sz.wt_group hzl
      have wy' := H.sz.wt_vec (vsQApp_fit (t := z) hy)
      have wr' : r.wt ≤ 700 * S ^ 6 := wr
      -- applying `φ(z)⁻¹`
      have dAI := (Det.call (Det.mk3 (dA [r] 0 _ rfl) (dz []) (dCr [r] 2 _ rfl))
        (H.hai z hzG y hy)).mono (c' := CAI + 10 ^ 5 * S ^ 6) (by
          have := hEnt _ (by simp : vsQGam I ∈ _)
          have := hEntC _ (by simp : natList y ∈ _)
          have := wt_list3_le (vsQGam I) (encPerm z) (natList y)
          have := wt_le_wt_list (show encPerm z ∈ [Val.nat 1, encPerm z, encGroup zs] by simp)
          have := wt_le_wt_list (show cur ∈ [vsQGam I, natList x, vsQLowsV lows, cur] by simp)
          rw [er] at wr'
          omega)
      refine (EvalAll.vsQ_ite_pos' (R := fun w c' => ∃ a, w = vsQAnsV a ∧ VsQAnsOK hP a ∧
          c' ≤ CAI + 10 ^ 6 * S ^ 6 + (Cn * (k + 1) + St)) dt1 one_ne_zero
        (EvalAll.letE (Q := fun w c' => ∃ a, w = vsQAnsV a ∧ VsQAnsOK hP a ∧
          c' ≤ CAI + 10 ^ 6 * S ^ 6 + (Cn * (k + 1) + St)) dAI fun yv cy hyv => ?_)).mono ?_
      rotate_left
      · rintro w cb ⟨ct, ⟨a', rfl, hok, hct⟩, hcb⟩
        refine ⟨a', rfl, hok, ?_⟩
        have := H.sz.wt_ans (VsQAnsOK.len (hP := hP) hok)
        have := hbd
        rw [er] at wr'
        have := wt_le_wt_list (show Val.nat 1 ∈ [Val.nat 1, encPerm z, encGroup zs] by simp)
        omega
      · obtain ⟨rfl, hcy⟩ := hyv
        set E3 : List Val := [r, natList y'] with hE3
        have dU3 : Det P (a :: E3) (.get (arg 2) (vsQCur 3)) (vsWVs u) _ :=
          Det.get' (dA E3 2 _ rfl) (dCr E3 3 _ rfl) (by
            simp only [vsQLowsV, List.getElem?_map]; rw [List.getElem?_eq_getElem hiL]; rfl)
        have dI := Det.arith' (op := .add) (dCr E3 3 _ rfl) (Det.nat 1) (z := i + 1) rfl
        have dArgR := Det.mk4 (dA E3 0 _ rfl) (dA E3 1 _ rfl) (dA E3 2 _ rfl)
          (Det.mk4 (dzs [natList y']) dU3 (Det.var' (P := P) (env := a :: E3) (i := 2) rfl) dI)
        have eR : Val.list [vsQGam I, natList x, vsQLowsV lows,
            .list [encGroup zs, vsWVs u, natList y', .nat (i + 1)]] = vsQCV I zs u lows x y' (i + 1) :=
          rfl
        rw [eR] at dArgR
        have wcv := H.sz.wt_cv (i := i + 1) hzl (hf u hum).1 (hf u hum).2 hf hl hx
          (vsQApp_fit (t := z) hy) (by omega)
        have ey' : (natList y').wt = (natList (vsQApp I z y)).wt := rfl
        have ecv2 : (vsQCV I zs u lows x (vsQApp I z y) (i + 1)).wt =
          (vsQCV I zs u lows x y' (i + 1)).wt := rfl
        have dArgR' := dArgR.mono (c' := 10 ^ 5 * S ^ 6) (by
          have := hEnt _ (by simp : vsQLowsV lows ∈ _)
          have := hEnt _ (by simp : vsQGam I ∈ _)
          have := hEnt _ (by simp : natList x ∈ _)
          have := hEntC _ (by simp : Val.nat i ∈ _)
          have hvu : (vsWVs u).wt < (vsQLowsV lows).wt := wt_le_wt_list (by
            simp only [List.mem_map]; exact ⟨u, hum, rfl⟩)
          have := wt_le_wt_list (show encGroup zs ∈ [Val.nat 1, encPerm z, encGroup zs] by simp)
          have := wt_list4_le (encGroup zs) (vsWVs u) (natList y') (.nat (i + 1))
          have ecv : (vsQCV I zs u lows x y' (i + 1)).wt = (Val.list [vsQGam I, natList x,
              vsQLowsV lows, .list [encGroup zs, vsWVs u, natList y', .nat (i + 1)]]).wt := rfl
          rw [er] at wr'
          omega)
        have hIH := ih zs u lows x y' (i + 1) (by omega) (by omega) hzl (hf u hum).1 (hf u hum).2
          hf hl hx (vsQApp_fit (t := z) hy) hP3 hchu
          (fun w hw => (hinv w (List.mem_cons_of_mem _ hw)).mono hzle')
          (fun h => (habC h).mono hzle' hUW (le_of_eq hlast.symm))
          (fun e' he' => hμ e' (by rw [hdims]; exact List.mem_cons_of_mem _ he'))
        have eSt : St = ((vsQDims I (u :: lows.drop (i + 1))).map fun e => vsQBd c K e abC).sum :=
          rfl
        refine EvalAll.letE (Ra := fun r' cr' => ∃ a2, r' = vsQAnsV a2 ∧ VsQAnsOK hP3 a2 ∧
            cr' ≤ 10 ^ 5 * S ^ 6 + (Cn * (k + 1) + St) + 700 * S ^ 6 + 1)
          (EvalAll.call_funAll dArgR' fun v ca hv => ?_) fun r' cr' hr' => ?_
        · obtain ⟨rfl, hca⟩ := hv
          refine hIH.mono fun w cb hw => ?_
          obtain ⟨a2, rfl, hok2, hcb⟩ := hw
          refine ⟨a2, rfl, hok2, ?_⟩
          have := H.sz.wt_ans (VsQAnsOK.len (hP := hP3) hok2)
          omega
        obtain ⟨a2, rfl, hok2, hcr'⟩ := hr'
        have wa2 := H.sz.wt_ans (VsQAnsOK.len (hP := hP3) hok2)
        have hok2' := hcomb a2 (htr a2 hok2)
        cases a2 with
        | none =>
          have dt3 : Det P [a, r, natList y', vsQAnsV (n := I.n) none] (.get (.var 3) (.nat 0))
              (.nat 0) _ :=
            Det.get' (Det.var' (i := 3) rfl) (Det.nat 0) (show [Val.nat 0][0]? = some (.nat 0) from rfl)
          refine (EvalAll.vsQ_ite_zero' dt3 (Det.mk1 (Det.nat (P := P)
            (env := [a, r, natList y', vsQAnsV (n := I.n) none]) 0))).mono ?_
          rintro w cb ⟨ce, ⟨rfl, hce⟩, hcb⟩
          refine ⟨none, rfl, hok2', ?_⟩
          have := wt_list1_le (.nat 0)
          have e0 : (vsQAnsV (n := I.n) none).wt = (Val.list [.nat 0]).wt := rfl
          omega
        | some r2 =>
          obtain ⟨z', zs'⟩ := r2
          set r2v := vsQAnsV (some (z', zs')) with hr2v
          have er2 : r2v = .list [.nat 1, encPerm z', encGroup zs'] := rfl
          have dt3 : Det P [a, r, natList y', r2v] (.get (.var 3) (.nat 0)) (.nat 1) _ :=
            Det.get' (Det.var' (i := 3) rfl) (Det.nat 0) rfl
          have dres := Det.mk3 (Det.nat (P := P) (env := [a, r, natList y', r2v]) 1)
            (Det.call (Det.mk2 (dz [natList y', r2v]) (Det.get' (Det.var' (i := 3) rfl) (Det.nat 1)
              (show [Val.nat 1, encPerm z', encGroup zs'][1]? = some (encPerm z') from rfl)))
              (compose_spec H.hcmp z z'))
            (Det.get' (Det.var' (i := 3) rfl) (Det.nat 2)
              (show [Val.nat 1, encPerm z', encGroup zs'][2]? = some (encGroup zs') from rfl))
          refine (EvalAll.vsQ_ite_pos' dt3 one_ne_zero dres).mono ?_
          rintro w cb ⟨ct, ⟨rfl, hct⟩, hcb⟩
          refine ⟨some (z * z', zs'), rfl, hok2', ?_⟩
          have hzl' : zs'.length ≤ I.n ^ 2 := (VsQAnsOK.len (hP := hP3) hok2) (z', zs') rfl
          have := H.sz.wt_ans (a := some (z * z', zs')) (fun q hq => by
            simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; exact hzl')
          have := H.sz.wt_perm z'
          have := H.sz.wt_perm (z * z')
          have := H.sz.wt_group hzl'
          have := wt_list2_le (encPerm z) (encPerm z')
          have := wt_list3_le (.nat 1) (encPerm z') (encGroup zs')
          have := wt_le_wt_list (show encPerm z ∈ [Val.nat 1, encPerm z, encGroup zs] by simp)
          have hn3 : (I.n + 1) ^ 3 ≤ S ^ 6 :=
            (Nat.pow_le_pow_left H.sz.n 3).trans (H.sz.pow_le (by omega))
          have eans : (vsQAnsV (some (z * z', zs'))).wt =
            (Val.list [.nat 1, encPerm (z * z'), encGroup zs']).wt := rfl
          rw [er] at wr'
          rw [er2] at wa2
          simp only [permK] at *
          omega


end GI.Impl
