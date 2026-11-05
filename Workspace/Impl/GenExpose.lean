module

public import Workspace.Impl.GenExposeCand

@[expose] public section

/-!
# The exposure program

Algorithm 5 ("Expose the next primitive quotient above any retained column partition") as a
`GI.Lang` program. Its pieces:

* `hsplitFuns`: the index `t` of the first interval of the hierarchy whose partition holds the
  domain in one class (`hsplit_spec`). A partition holds the domain in one class exactly when the
  class numbering has one class (`Cls.Numbering.univOn_iff`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup gens)

variable {Ω C : Type} {k : ℕ}

/-! ### The split index -/

/-- The bit of an interval: `1` if its partition holds the domain in one class. -/
noncomputable def univBit (D : Set Ω) (I : Interval Ω) : ℕ :=
  open Classical in if UnivOn D I.part then 1 else 0

/-- The index of the split interval: the first interval whose partition holds the domain. -/
noncomputable def splitIdx (D : Set Ω) (l : List (Interval Ω)) : ℕ :=
  (l.map (univBit D)).findIdx fun x => decide (x = 1)

/-- On `[dm, iv]`: `1` if the numbering of the partition of `iv` has one class. -/
def univF (bcls : ℕ) : Expr :=
  .arith .eq (.length (.get (.call bcls (mk2 (.get (arg 1) (.nat 0)) (arg 0))) (.nat 1)))
    (.nat 1)

theorem univ_det {P : Program} {f bcls : ℕ} (hf : P.funs[f]? = some (univF bcls))
    (hcls : P.HasAt bcls (clsFuns bcls)) {e : Ω ≃ Fin k} {D : Set Ω} (hne : D.Nonempty)
    {iv : Val} {I : Interval Ω} (hI : IntervalValC e iv I) {X : ℕ}
    (hX : (Val.list [encFun (indF e D), iv]).wt ≤ X) :
    FunDet P f (.list [encFun (indF e D), iv]) (.nat (univBit D I))
      (3 * (clsK * (X + 1) ^ 4) + 40 * X + 40) := by
  obtain ⟨pv, ⟨lab, rfl, hlt, hR⟩, rfl⟩ := hI
  set dm := indF e D with hdm
  have hk : k ≤ X := by
    have h1 := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (dm i))
    have h2 := wt_le_wt_list (show encFun dm ∈ [encFun dm, Val.list [encFun lab, .nat I.ratio,
      .nat I.cap, .nat I.origin]] by simp)
    have h3 : (encFun dm).wt = (Val.list ((List.finRange k).map fun i => Val.nat (dm i))).wt :=
      rfl
    simp only [List.length_map, List.length_finRange] at h1
    omega
  have hdm1 : ∀ i, dm i ≤ 1 := fun i => by simp only [hdm, indF]; split_ifs <;> omega
  have hc := cls_spec hcls lab dm (X := X) (fun i => (hlt i).le.trans hk) hdm1 hk
  have h0 := Det.arg' (P := P) (vs := [encFun dm, .list [encFun lab, .nat I.ratio, .nat I.cap,
    .nat I.origin]]) (rest := []) (j := 0) rfl
  have h1 := Det.arg' (P := P) (vs := [encFun dm, .list [encFun lab, .nat I.ratio, .nat I.cap,
    .nat I.origin]]) (rest := []) (j := 1) rfl
  have hp := Det.get' h1 (Det.nat 0) (v := encFun lab) rfl
  have hcall := Det.call (Det.mk2 hp h0) hc
  have hr := Det.get' hcall (Det.nat 1)
    (v := natList (Cls.repsOf dm (Cls.keyOf lab dm))) rfl
  have hl := Det.length (vs := (Cls.repsOf dm (Cls.keyOf lab dm)).map Val.nat) hr
  rw [List.length_map] at hl
  have hn := Cls.numbering e D I.part lab hlt hR
  have hbit : BinOp.eval .eq (Cls.repsOf dm (Cls.keyOf lab dm)).length 1 = univBit D I := by
    classical
    simp only [BinOp.eval, univBit]
    rw [← hdm] at hn
    by_cases hu : UnivOn D I.part
    · rw [if_pos hu, if_pos ((hn.univOn_iff hne).1 hu)]
    · rw [if_neg hu, if_neg (fun h => hu ((hn.univOn_iff hne).2 h))]
  have hout := Det.arith' hl (Det.nat 1) hbit
  refine FunDet.intro hf (hout.mono ?_)
  have hb : univBit D I ≤ 1 := by unfold univBit; split_ifs <;> omega
  have wc := (FunDet.wt_lt hc)
  have := wt_list2_le (encFun lab) (encFun dm)
  have := wt_le_wt_list (show encFun lab ∈ [encFun lab, .nat I.ratio, .nat I.cap,
    .nat I.origin] by simp)
  have := wt_le_wt_list (show Val.list [encFun lab, .nat I.ratio, .nat I.cap, .nat I.origin] ∈
    [encFun dm, Val.list [encFun lab, .nat I.ratio, .nat I.cap, .nat I.origin]] by simp)
  have := wt_le_wt_list (show encFun dm ∈
    [encFun dm, Val.list [encFun lab, .nat I.ratio, .nat I.cap, .nat I.origin]] by simp)
  have hrw : (natList (Cls.repsOf dm (Cls.keyOf lab dm))).wt < (clsVal lab dm).wt :=
    wt_le_wt_list (by simp)
  have hRl : (Cls.repsOf dm (Cls.keyOf lab dm)).length ≤ k := Cls.repsOf_length_le _ _
  have h4 : 1 ≤ (X + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  clear hout hl hr hcall hp h0 h1 hc
  omega

/-- On `[dm, hv]`: the first index whose bit is `1`. -/
def hsplitE (bm bfe : ℕ) : Expr :=
  .call bfe (mk2 (.nat 1) (.call bm (mk2 (arg 0) (arg 1))))

/-- The split module at base `b` (9 functions), using the class numbering at `bcls`. -/
def hsplitFuns (b bcls : ℕ) : List Expr :=
  [hsplitE (b + 2) (b + 5), univF bcls] ++ mapFuns (b + 2) (b + 1) ++ findEqFuns (b + 5)

theorem length_hsplitFuns (b bcls : ℕ) : (hsplitFuns b bcls).length = 9 := by
  simp [hsplitFuns, mapFuns, findEqFuns, findFuns, loopFuns]

/-- The cost constant of the split module. -/
def hsplitK : ℕ := 10 ^ 14

theorem forall₂_exists_left {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {x}, x ∈ l₁ → ∃ y ∈ l₂, R x y
  | [], [], _, _, hx => absurd hx (List.not_mem_nil)
  | _ :: _, y :: _, .cons h t, _, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨y, List.mem_cons_self .., h⟩
    · obtain ⟨z, hz, hR⟩ := forall₂_exists_left t hx
      exact ⟨z, List.mem_cons_of_mem _ hz, hR⟩

theorem forall₂_bits {e : Ω ≃ Fin k} {D : Set Ω} :
    ∀ {vs ws : List Val} {l : List (Interval Ω)},
      List.Forall₂ (fun x w => ∀ I, IntervalValC e x I → w = .nat (univBit D I)) vs ws →
      List.Forall₂ (IntervalValC e) vs l → ws = (l.map (univBit D)).map Val.nat
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, .cons h1 t1, .cons h2 t2 => by
    rw [h1 _ h2, forall₂_bits t1 t2]; rfl

/-- **The split index.** -/
theorem hsplit_spec {P : Program} {b bcls : ℕ} (h : P.HasAt b (hsplitFuns b bcls))
    (hcls : P.HasAt bcls (clsFuns bcls)) {e : Ω ≃ Fin k} {D : Set Ω} (hne : D.Nonempty)
    {hv : Val} {l : List (Interval Ω)} (hH : HierValC e hv l) :
    FunDet P b (.list [encFun (indF e D), hv]) (.nat (splitIdx D l))
      (hsplitK * ((Val.list [encFun (indF e D), hv]).wt + 1) ^ 5) := by
  have hentry : P.funs[b]? = some (hsplitE (b + 2) (b + 5)) :=
    (h.block 0 rfl : P.HasAt (b + 0) _).single
  have hu : P.funs[b + 1]? = some (univF bcls) := (h.block 1 rfl : P.HasAt (b + 1) _).single
  have hm : P.HasAt (b + 2) (mapFuns (b + 2) (b + 1)) := h.block 2 rfl
  have hfe : P.HasAt (b + 5) (findEqFuns (b + 5)) := h.block 5 rfl
  obtain ⟨vs, rfl, hvs⟩ := hH
  set dv := encFun (indF e D) with hdv
  set W := (Val.list [dv, .list vs]).wt with hW
  have hM := map_spec hm (c := dv) (xs := vs)
    (R := fun x w => ∀ I, IntervalValC e x I → w = .nat (univBit D I))
    (B := fun _ => 3 * (clsK * (4 * W + 7) ^ 4) + 40 * (4 * W + 6) + 40) (by
      intro x hx
      obtain ⟨I, -, hI⟩ := forall₂_exists_left hvs hx
      have hxw : (Val.list [dv, x]).wt ≤ 4 * W + 6 := by
        have := wt_list2_le dv x
        have := wt_le_wt_list (show dv ∈ [dv, Val.list vs] by simp)
        have := wt_le_wt_list (show Val.list vs ∈ [dv, Val.list vs] by simp)
        have := wt_le_wt_list hx
        omega
      refine FunAll.mono (univ_det hu hcls hne hI hxw) fun w cost hw => ⟨fun I' hI' => ?_, ?_⟩
      · rw [hw.1]
        obtain ⟨pv, ⟨lab, rfl, -, hR⟩, rfl⟩ := hI
        obtain ⟨pv', ⟨lab', hpv, -, hR'⟩, hx'⟩ := hI'
        simp only [Val.list.injEq, List.cons.injEq] at hx'
        obtain ⟨hp, -⟩ := hx'
        subst hp
        have hl : lab' = lab := encFun_injective hpv.symm
        subst hl
        have hpart : I.part = I'.part := by
          ext v w
          rw [← e.symm_apply_apply v, ← e.symm_apply_apply w, ← hR, ← hR']
        rw [univBit, univBit, hpart]
      · exact hw.2.trans (le_of_eq (by ring)))
  have hW1 : 1 ≤ W := by
    have := (Val.list [dv, Val.list vs]).two_le_size
    have := (Val.list [dv, Val.list vs]).size_le_wt; omega
  have hb : ∀ x ∈ l.map (univBit D), x ≤ W := fun x hx => by
    obtain ⟨I, -, rfl⟩ := List.mem_map.1 hx
    have : univBit D I ≤ 1 := by unfold univBit; split_ifs <;> omega
    omega
  have hll : l.length = vs.length := (List.Forall₂.length_eq hvs).symm
  have hvW : vs.length < W := by
    have := length_lt_wt_list vs
    have := wt_le_wt_list (show Val.list vs ∈ [dv, Val.list vs] by simp)
    omega
  have hlW : (l.map (univBit D)).length ≤ W := by simp only [List.length_map]; omega
  have wb := wt_natList_le_sq hb hlW
  have hbits : FunDet P (b + 2) (.list [dv, .list vs]) (natList (l.map (univBit D)))
      (vs.length * (3 * (clsK * (4 * W + 7) ^ 4) + 40 * (4 * W + 6) + 40) +
        mapK * (vs.length + 1) * (W + 5 * (W + 1) ^ 2 + 1)) := by
    refine FunAll.mono hM fun w cost hw => ?_
    obtain ⟨ws, rfl, hws, hc⟩ := hw
    have hws' := forall₂_bits hws hvs
    subst hws'
    refine ⟨rfl, ?_⟩
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hc
    have e1 : (Val.list ((l.map (univBit D)).map Val.nat)).wt =
      (natList (l.map (univBit D))).wt := rfl
    rw [e1] at hc
    calc cost ≤ _ := hc
      _ ≤ _ := by
        gcongr
  have hF := findEq_spec hfe (xs := l.map (univBit D)) (j := 1) (B := W) hb hW1 hlW
  have h0 := Det.arg' (P := P) (vs := [dv, .list vs]) (rest := []) (j := 0) rfl
  have h1 := Det.arg' (P := P) (vs := [dv, .list vs]) (rest := []) (j := 1) rfl
  have hc1 := Det.call (Det.mk2 h0 h1) hbits
  have hc2 := Det.call (Det.mk2 (Det.nat 1) hc1) hF
  refine FunDet.intro hentry (hc2.mono ?_)
  have e2 : (l.map (univBit D)).findIdx (fun x => decide (x = 1)) = splitIdx D l := rfl
  rw [e2]
  have hsW : splitIdx D l ≤ W := by
    have := List.findIdx_le_length (p := fun x => decide (x = 1)) (xs := l.map (univBit D))
    rw [e2] at this; omega
  have := wt_nat_le (splitIdx D l)
  have w2 := wt_list2_le (Val.nat 1) (natList (l.map (univBit D)))
  have w3 := wt_list2_le dv (Val.list vs)
  have w4 : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
  have hY : (4 * W + 7) ^ 4 ≤ 7 ^ 4 * (W + 1) ^ 4 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) 4
  have p1 : vs.length * (3 * (clsK * (4 * W + 7) ^ 4) + 40 * (4 * W + 6) + 40) ≤
      (W + 1) * (3 * (clsK * (7 ^ 4 * (W + 1) ^ 4)) + 400 * (W + 1)) := by
    apply Nat.mul_le_mul (by omega)
    have : 3 * (clsK * (4 * W + 7) ^ 4) ≤ 3 * (clsK * (7 ^ 4 * (W + 1) ^ 4)) := by gcongr
    omega
  have p2 : (W + 1) * (3 * (clsK * (7 ^ 4 * (W + 1) ^ 4)) + 400 * (W + 1)) ≤
      8 * 10 ^ 12 * (W + 1) ^ 5 := by
    simp only [clsK]
    have h1 : (W + 1) ^ 2 ≤ (W + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    nlinarith
  have p3 : mapK * (vs.length + 1) * (W + 5 * (W + 1) ^ 2 + 1) ≤ 10 ^ 5 * (W + 1) ^ 5 := by
    simp only [mapK]
    have h1 : (W + 1) ^ 3 ≤ (W + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : vs.length + 1 ≤ W + 1 := by omega
    have h3 : W + 5 * (W + 1) ^ 2 + 1 ≤ 6 * (W + 1) ^ 2 := by nlinarith
    calc 1000 * (vs.length + 1) * (W + 5 * (W + 1) ^ 2 + 1)
        ≤ 1000 * (W + 1) * (6 * (W + 1) ^ 2) := by gcongr
      _ = 6000 * (W + 1) ^ 3 := by ring
      _ ≤ 10 ^ 5 * (W + 1) ^ 5 := by nlinarith
  have p4 : findEqK * (W + 1) ^ 3 ≤ 10 ^ 5 * (W + 1) ^ 5 := by
    simp only [findEqK]
    have h1 : (W + 1) ^ 3 ≤ (W + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have p5 : W + 1 ≤ (W + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
  have p6 : (natList (l.map (univBit D))).wt ≤ 5 * (W + 1) ^ 5 := by
    have : (W + 1) ^ 2 ≤ (W + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  simp only [hsplitK]
  clear hc2 hc1 hF hbits h0 h1 hM
  omega

/-! ### The base partition: the columns when they are coarser than `f` -/

/-- The test of a point: off the domain, or the column label of the point equals the column
label of its representative. -/
def chkQ (dm clab rep : Fin k → ℕ) : Val → Bool
  | .nat j => if h : j < k then decide (dm ⟨j, h⟩ = 0 ∨ clab ⟨j, h⟩ = funAt clab (rep ⟨j, h⟩))
      else true
  | _ => true

/-- On `[[clab, rep, dm], j]`: the test `chkQ`. -/
def chkF : Expr :=
  .ite (.get (.get (arg 0) (.nat 2)) (arg 1))
    (.arith .eq (.get (.get (arg 0) (.nat 0)) (arg 1))
      (.get (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1))))
    (.nat 1)

theorem chk_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some chkF) (dm clab rep : Fin k → ℕ)
    (hrep : ∀ i, rep i < k) (j : Fin k) :
    FunDet P f (.list [.list [encFun clab, encFun rep, encFun dm], .nat j])
      (boolVal (chkQ dm clab rep (.nat j)))
      (40 * (Val.list [.list [encFun clab, encFun rep, encFun dm], .nat j]).wt + 40) := by
  set c : Val := .list [encFun clab, encFun rep, encFun dm] with hc
  have h0 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 0) rfl
  have h1 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 1) rfl
  have hd := Det.get' (Det.get' h0 (Det.nat 2) (v := encFun dm) rfl) h1 (encFun_getElem? dm j)
  have hcl := Det.get' h0 (Det.nat 0) (v := encFun clab) rfl
  have hcj := Det.get' hcl h1 (encFun_getElem? clab j)
  have hrj := Det.get' (Det.get' h0 (Det.nat 1) (v := encFun rep) rfl) h1 (encFun_getElem? rep j)
  have hcr := Det.get' hcl hrj (show ((List.finRange k).map fun i => Val.nat (clab i))[rep j]? =
    some (.nat (clab ⟨rep j, hrep j⟩)) by simp [hrep j])
  have he := Det.arith' (op := .eq) hcj hcr
    (z := if clab j = clab ⟨rep j, hrep j⟩ then 1 else 0) (by simp [BinOp.eval])
  have hout := Det.ite' hd he (Det.nat 1)
  refine FunDet.intro hf (hout.post fun cost hcost => ⟨?_, ?_⟩)
  · have hf' : funAt clab (rep j) = clab ⟨rep j, hrep j⟩ := by simp [funAt, hrep j]
    simp only [chkQ, dif_pos j.isLt, hf']
    by_cases hz : dm j = 0
    · simp [hz]
    · by_cases h2 : clab j = clab ⟨rep j, hrep j⟩
      · simp [hz, h2]
      · simp [hz, h2]
  · have wa := wt_list2_le c (.nat j)
    have w1 : c.wt < (Val.list [c, .nat j]).wt := wt_le_wt_list (by simp)
    have w2 : (encFun dm).wt < c.wt := wt_le_wt_list (by simp [hc])
    have w3 : (encFun clab).wt < c.wt := wt_le_wt_list (by simp [hc])
    have w4 : (encFun rep).wt < c.wt := wt_le_wt_list (by simp [hc])
    have w5 : (Val.nat j).wt < (Val.list [c, .nat j]).wt := wt_le_wt_list (by simp)
    have w6 : (Val.nat (dm j)).wt < (encFun dm).wt := wt_le_wt_list (List.mem_map_of_mem
      (List.mem_finRange j))
    have w7 : (Val.nat (clab j)).wt < (encFun clab).wt := wt_le_wt_list (List.mem_map_of_mem
      (List.mem_finRange j))
    have w8 : (Val.nat (rep j)).wt < (encFun rep).wt := wt_le_wt_list (List.mem_map_of_mem
      (List.mem_finRange j))
    have w9 : (Val.nat (clab ⟨rep j, hrep j⟩)).wt < (encFun clab).wt :=
      wt_le_wt_list (List.mem_map_of_mem (List.mem_finRange _))
    have hb : (if clab j = clab ⟨rep j, hrep j⟩ then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega
    have := wt_nat_le (if clab j = clab ⟨rep j, hrep j⟩ then 1 else 0)
    have := wt_nat_le 1
    have hm : max (Val.nat (if clab j = clab ⟨rep j, hrep j⟩ then 1 else 0)).wt (Val.nat 1).wt
        ≤ 3 := max_le (by omega) (by omega)
    have := wt_nat_le 0
    have := wt_nat_le (clab j)
    have := wt_nat_le (clab ⟨rep j, hrep j⟩)
    clear hout he hcr hrj hcj hcl hd h0 h1
    omega

/-- The base labels: the column labels when the columns are stored and coarser than the fine end
on the domain (`chkQ` holds everywhere), else the labels of the fine end. -/
def baseSel (flab dm rep : Fin k → ℕ) : Option (Fin k → ℕ) → Fin k → ℕ
  | none => flab
  | some clab => if (List.finRange k).all (fun j => chkQ dm clab rep (.nat j)) then clab else flab

/-- The stored columns as a value: `[]`, or `[clab]`. -/
def colsVal : Option (Fin k → ℕ) → Val
  | none => .list []
  | some clab => .list [encFun clab]

/-- On `[rv, clsf, dm, flab]`: the base labels. -/
def baseF (ball brange : ℕ) : Expr :=
  .ite (.length (arg 0))
    (.ite (.length (.get (.get (arg 0) (.nat 0)) (.nat 2)))
      (.ite (.call ball (mk2 (mk3 (.get (.get (.get (arg 0) (.nat 0)) (.nat 2)) (.nat 0))
          (.get (arg 1) (.nat 2)) (arg 2)) (.call brange (.length (arg 2)))))
        (.get (.get (.get (arg 0) (.nat 0)) (.nat 2)) (.nat 0)) (arg 3))
      (arg 3))
    (arg 3)

/-- The base module at base `b` (8 functions). -/
def baseFuns (b : ℕ) : List Expr :=
  [baseF (b + 2) (b + 5), chkF] ++ allFuns (b + 2) (b + 1) ++ rangeFuns (b + 5)

theorem length_baseFuns (b : ℕ) : (baseFuns b).length = 8 := by
  simp [baseFuns, allFuns, rangeFuns, loopFuns]

/-- The test over all points, as a program. -/
theorem chkAll_det {P : Program} {b f : ℕ} (hall : P.HasAt b (allFuns b f))
    (hf : P.funs[f]? = some chkF) (dm clab rep : Fin k → ℕ) (hrep : ∀ i, rep i < k) {X : ℕ}
    (hX : (Val.list [encFun clab, encFun rep, encFun dm]).wt ≤ X) (hkX : k ≤ X) :
    FunDet P b (.list [.list [encFun clab, encFun rep, encFun dm], natList (List.range k)])
      (boolVal ((List.finRange k).all fun j => chkQ dm clab rep (.nat j)))
      (10 ^ 6 * (X + 1) ^ 3) := by
  set c : Val := .list [encFun clab, encFun rep, encFun dm] with hc
  have hA := all_spec hall (c := c) (xs := (List.range k).map Val.nat) (q := chkQ dm clab rep)
    (B := fun _ => 40 * (4 * X + 10) + 40) (by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      have hj' : j < k := List.mem_range.1 hj
      refine FunAll.mono (chk_det hf dm clab rep hrep ⟨j, hj'⟩) fun w cost hw => ⟨hw.1, ?_⟩
      have w1 : (Val.list [c, .nat j]).wt ≤ 2 * (c.wt + (Val.nat j).wt) + 6 := wt_list2_le c _
      have w2 := wt_nat_le j
      have h2 := hw.2
      have e0 : (Val.list [Val.list [encFun clab, encFun rep, encFun dm],
        Val.nat ((⟨j, hj'⟩ : Fin k) : ℕ)]).wt = (Val.list [c, .nat j]).wt := rfl
      rw [e0] at h2
      show cost ≤ 40 * (4 * X + 10) + 40
      omega)
  refine FunAll.mono hA fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1]
    have e1 : ((List.range k).map Val.nat).all (chkQ dm clab rep) =
        (List.finRange k).all fun j => chkQ dm clab rep (.nat j) := by
      rw [← List.map_coe_finRange_eq_range, List.map_map, List.all_map]; rfl
    rw [e1]
  · have hc' := hw.2
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map,
      List.length_range] at hc'
    have wI := wt_range_le k
    have e1 : (Val.list [c, .list ((List.range k).map Val.nat)]).wt =
      (Val.list [c, natList (List.range k)]).wt := rfl
    rw [e1] at hc'
    have w2 := wt_list2_le c (natList (List.range k))
    have hk2 : (k + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h1 : k * (40 * (4 * X + 10) + 40) ≤ 1000 * (X + 1) ^ 2 := by nlinarith
    have h2 : loopModK * (k + 1) * ((Val.list [c, natList (List.range k)]).wt + k + 4) ≤
        loopModK * (X + 1) * (20 * (X + 1) ^ 2) := by
      apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
      nlinarith
    have h3 : loopModK * (X + 1) * (20 * (X + 1) ^ 2) = 20000 * (X + 1) ^ 3 := by
      simp only [loopModK]; ring
    have h4 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega

/-- **The base labels.** On `[rv, [x₀, x₁, rep], dm, flab]`, where `rv` is `[]` or
`[[m, rows, cols]]` with `cols = colsVal ocl`, the module returns the base labels. -/
theorem base_spec {P : Program} {b : ℕ} (h : P.HasAt b (baseFuns b)) {rv x₀ x₁ : Val}
    (dm flab rep : Fin k → ℕ) (hrep : ∀ i, rep i < k) {ocl : Option (Fin k → ℕ)}
    (hrv : (rv = .list [] ∧ ocl = none) ∨ ∃ mv rowsv, rv = .list [.list [mv, rowsv, colsVal ocl]])
    {X : ℕ} (hX : (Val.list [rv, .list [x₀, x₁, encFun rep], encFun dm, encFun flab]).wt ≤ X) :
    FunDet P b (.list [rv, .list [x₀, x₁, encFun rep], encFun dm, encFun flab])
      (encFun (baseSel flab dm rep ocl)) (10 ^ 9 * (X + 1) ^ 3) := by
  have hentry : P.funs[b]? = some (baseF (b + 2) (b + 5)) :=
    (h.block 0 rfl : P.HasAt (b + 0) _).single
  have hchk : P.funs[b + 1]? = some chkF := (h.block 1 rfl : P.HasAt (b + 1) _).single
  have hall : P.HasAt (b + 2) (allFuns (b + 2) (b + 1)) := h.block 2 rfl
  have hrange : P.HasAt (b + 5) (rangeFuns (b + 5)) := h.block 5 rfl
  set cv : Val := .list [x₀, x₁, encFun rep] with hcv
  set a : Val := .list [rv, cv, encFun dm, encFun flab] with ha
  have wrv : rv.wt < a.wt := wt_le_wt_list (by simp [ha])
  have wcv : cv.wt < a.wt := wt_le_wt_list (by simp [ha])
  have wdm : (encFun dm).wt < a.wt := wt_le_wt_list (by simp [ha])
  have wfl : (encFun flab).wt < a.wt := wt_le_wt_list (by simp [ha])
  have wrep : (encFun rep).wt < cv.wt := wt_le_wt_list (by simp [hcv])
  have hk : k < a.wt := by
    have h1 := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (dm i))
    have h3 : (encFun dm).wt = (Val.list ((List.finRange k).map fun i => Val.nat (dm i))).wt :=
      rfl
    simp only [List.length_map, List.length_finRange] at h1
    omega
  have g0 := Det.arg' (P := P) (vs := [rv, cv, encFun dm, encFun flab]) (rest := []) (j := 0) rfl
  have g3 := Det.arg' (P := P) (vs := [rv, cv, encFun dm, encFun flab]) (rest := []) (j := 3) rfl
  have hX3 : (X + 1) ^ 1 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hfl : Det P [a] (arg 3) (encFun flab) (2 * a.wt + 3 + 5) := g3
  have hXa : a.wt ≤ X := hX
  -- The case without columns: the `else` branches.
  rcases hrv with ⟨rfl, rfl⟩ | ⟨mv, rowsv, rfl⟩
  · have hl := Det.length (vs := []) g0
    refine FunDet.intro hentry ((Det.ite_zero hl hfl).mono ?_)
    simp only [pow_one] at hX3
    have e0 : (Val.list [Val.list [], cv, encFun dm, encFun flab]).wt = a.wt := rfl
    simp only [List.length_nil, List.length_cons]
    omega
  set u : Val := .list [mv, rowsv, colsVal ocl] with hu
  have hl := Det.length (vs := [u]) g0
  have hu0 := Det.get' g0 (Det.nat 0) (v := u) rfl
  have hc2 := Det.get' hu0 (Det.nat 2) (v := colsVal ocl) rfl
  have wu : u.wt < (Val.list [u]).wt := wt_le_wt_list (by simp)
  have wc : (colsVal ocl).wt < u.wt := wt_le_wt_list (by simp [hu])
  cases ocl with
  | none =>
    have hl2 := Det.length (vs := []) hc2
    have hin := Det.ite_zero hl2 (t := .ite (.call (b + 2) (mk2 (mk3 (.get (.get (.get (arg 0)
      (.nat 0)) (.nat 2)) (.nat 0)) (.get (arg 1) (.nat 2)) (arg 2)) (.call (b + 5) (.length
      (arg 2))))) (.get (.get (.get (arg 0) (.nat 0)) (.nat 2)) (.nat 0)) (arg 3)) hfl
    refine FunDet.intro hentry ((Det.ite_pos hl (by simp) hin).mono ?_)
    simp only [pow_one] at hX3
    have e0 : (Val.list [Val.list [u], cv, encFun dm, encFun flab]).wt = a.wt := rfl
    simp only [List.length_nil, List.length_cons]
    clear hin hl2 hc2 hu0 hl g0 g3 hfl
    omega
  | some clab =>
    have hl2 := Det.length (vs := [encFun clab]) hc2
    have hcl := Det.get' hc2 (Det.nat 0) (v := encFun clab) rfl
    have wcl : (encFun clab).wt < (colsVal (some clab)).wt := wt_le_wt_list (by simp [colsVal])
    have g1 := Det.arg' (P := P) (vs := [Val.list [u], cv, encFun dm, encFun flab]) (rest := [])
      (j := 1) rfl
    have g2 := Det.arg' (P := P) (vs := [Val.list [u], cv, encFun dm, encFun flab]) (rest := [])
      (j := 2) rfl
    have hrp := Det.get' g1 (Det.nat 2) (v := encFun rep) rfl
    have hld := Det.length (vs := (List.finRange k).map fun i => Val.nat (dm i)) g2
    simp only [List.length_map, List.length_finRange] at hld
    have hrg := Det.call hld (range_det hrange k)
    have hX' : (Val.list [encFun clab, encFun rep, encFun dm]).wt ≤ 6 * X + 7 := by
      have := wt_list3_le (encFun clab) (encFun rep) (encFun dm)
      omega
    have hA := chkAll_det hall hchk dm clab rep hrep hX' (by omega)
    have htest := Det.call (Det.mk2 (Det.mk3 hcl hrp g2) hrg) hA
    set tb := (List.finRange k).all fun j => chkQ dm clab rep (.nat j) with htb
    have hin := Det.ite (v := encFun (baseSel flab dm rep (some clab))) htest
      (fun hx => by
        have ht : tb = true := by cases htb' : tb <;> simp_all
        simp only [baseSel, ← htb, ht, if_true]
        exact hcl)
      (fun hx => by
        have ht : tb = false := by cases htb' : tb <;> simp_all
        simp only [baseSel, ← htb, ht]
        exact hfl)
    have hmid := Det.ite_pos hl2 (by simp) hin (e := arg 3)
    refine FunDet.intro hentry ((Det.ite_pos hl (by simp) hmid).mono ?_)
    have wb : (encFun (baseSel flab dm rep (some clab))).wt ≤
        (encFun clab).wt + (encFun flab).wt := by
      simp only [baseSel]; split_ifs <;> omega
    have wbool : (boolVal tb).wt ≤ 3 := wt_boolVal_le _
    have wI := wt_range_le k
    have w5 := wt_list2_le (Val.list [encFun clab, encFun rep, encFun dm]) (natList (List.range k))
    have e0 : (Val.list [Val.list [u], cv, encFun dm, encFun flab]).wt = a.wt := rfl
    have hk3 : (k + 1) ^ 3 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hk2 : (k + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hX23 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h6 : 10 ^ 6 * (6 * X + 7 + 1) ^ 3 ≤ 10 ^ 6 * (512 * (X + 1) ^ 3) := by
      have : (6 * X + 7 + 1) ^ 3 ≤ (8 * (X + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      rw [mul_pow] at this; norm_num at this ⊢; omega
    simp only [List.length_nil, List.length_cons, pow_one] at hX3 ⊢
    clear hin hmid htest hA hrg hld hrp g1 g2 hcl hl2 hc2 hu0 hl g0 g3 hfl
    omega

/-! ### The base partition: the facts -/

section BaseMath

variable {e : Ω ≃ Fin k} {D : Set Ω}

theorem indF_ne_zero' (i : Fin k) : indF e D i ≠ 0 ↔ e.symm i ∈ D := by
  have := Cls.indF_ne_zero e D (e.symm i)
  rwa [Equiv.apply_symm_apply] at this

/-- **The column test** holds exactly when the columns are coarser than `f` on the domain. -/
theorem baseChk_iff {f c : Setoid Ω} {flab clab : Fin k → ℕ} (hflt : ∀ i, flab i < k)
    (hf : ∀ i j, flab i = flab j ↔ f.r (e.symm i) (e.symm j))
    (hc : ∀ i j, clab i = clab j ↔ c.r (e.symm i) (e.symm j)) :
    (List.finRange k).all (fun j => chkQ (indF e D) clab
      (Cls.repOf (Cls.keyOf flab (indF e D))) (.nat j)) = true ↔
      ∀ v ∈ D, ∀ w ∈ D, f.r v w → c.r v w := by
  set dm := indF e D with hdm
  set key := Cls.keyOf flab dm with hkey
  have hl : Cls.LabOK flab dm := fun i _ => hflt i
  have hfa : ∀ j : Fin k, funAt clab (Cls.repOf key j) = clab ⟨_, Cls.repOf_lt key j⟩ := by
    intro j; simp [funAt, Cls.repOf_lt key j]
  simp only [List.all_eq_true, List.mem_finRange, true_implies, chkQ, Fin.is_lt, dif_pos,
    Fin.eta, hfa, decide_eq_true_eq]
  constructor
  · intro ht v hv w hw hvw
    have hv' : dm (e v) ≠ 0 := (Cls.indF_ne_zero e D v).2 hv
    have hw' : dm (e w) ≠ 0 := (Cls.indF_ne_zero e D w).2 hw
    have hkeq : key (e v) = key (e w) := by
      simp only [hkey, Cls.keyOf, hv', hw', if_false]
      rw [hf]; simpa using hvw
    have hr : Cls.repOf key (e v) = Cls.repOf key (e w) := (Cls.repOf_eq_iff key _ _).2 hkeq
    have h1 := (ht (e v)).resolve_left hv'
    have h2 := (ht (e w)).resolve_left hw'
    have : clab (e v) = clab (e w) := by
      rw [h1, h2]; congr 2
    simpa using (hc _ _).1 this
  · intro hle j
    by_cases hj : dm j = 0
    · exact Or.inl hj
    refine Or.inr ((hc _ _).2 (hle _ ((indF_ne_zero' j).1 hj) _ ?_ ?_))
    · exact (indF_ne_zero' _).1 (Cls.dm_repOf hl hj)
    · have hk := Cls.key_repOf key j
      have hr := Cls.dm_repOf hl hj
      simp only [hkey, Cls.keyOf, hj, hr, if_false] at hk
      exact (hf _ _).1 hk.symm

/-- **The base partition.** From the stored rows, the program reads the optional column labels
`ocl`; its base labels `baseSel` are the labels of a partition `B` coarser than `f`, invariant,
not one class on the domain, and coarser than the retained columns when they are coarser than
`f`. -/
theorem base_props {S : State Ω C} (hinv : S.HierInv) {f : Setoid Ω} {flab : Fin k → ℕ}
    (hflt : ∀ i, flab i < k) (hf : ∀ i j, flab i = flab j ↔ f.r (e.symm i) (e.symm j))
    (hfinv : ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r (g v) (g w) ↔ f.r v w)
    (hfpr : ¬ UnivOn S.dom f) {rv : Val} (hrv : OptVal (RowValC e) rv S.rows) :
    ∃ ocl : Option (Fin k → ℕ),
      ((rv = .list [] ∧ ocl = none) ∨ ∃ mv rowsv, rv = .list [.list [mv, rowsv, colsVal ocl]]) ∧
      ∃ B : Setoid Ω,
        (∀ i, baseSel flab (indF e S.dom) (Cls.repOf (Cls.keyOf flab (indF e S.dom))) ocl i < k) ∧
        (∀ i j, baseSel flab (indF e S.dom) (Cls.repOf (Cls.keyOf flab (indF e S.dom))) ocl i =
          baseSel flab (indF e S.dom) (Cls.repOf (Cls.keyOf flab (indF e S.dom))) ocl j ↔
          B.r (e.symm i) (e.symm j)) ∧
        (∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r v w → B.r v w) ∧
        (∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom, B.r (g v) (g w) ↔ B.r v w) ∧
        ¬ UnivOn S.dom B ∧
        (∀ c, S.retainedCols = some c →
          (∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r v w → c.r v w) →
          ∀ v ∈ S.dom, ∀ w ∈ S.dom, c.r v w → B.r v w) := by
  set rep := Cls.repOf (Cls.keyOf flab (indF e S.dom)) with hrep
  -- The case where `B = f`.
  have hfcase : ∀ ocl : Option (Fin k → ℕ), baseSel flab (indF e S.dom) rep ocl = flab →
      (∀ c, S.retainedCols = some c → (∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r v w → c.r v w) →
        ∀ v ∈ S.dom, ∀ w ∈ S.dom, c.r v w → f.r v w) →
      ∃ B : Setoid Ω,
        (∀ i, baseSel flab (indF e S.dom) rep ocl i < k) ∧
        (∀ i j, baseSel flab (indF e S.dom) rep ocl i = baseSel flab (indF e S.dom) rep ocl j ↔
          B.r (e.symm i) (e.symm j)) ∧
        (∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r v w → B.r v w) ∧
        (∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom, B.r (g v) (g w) ↔ B.r v w) ∧
        ¬ UnivOn S.dom B ∧
        (∀ c, S.retainedCols = some c →
          (∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r v w → c.r v w) →
          ∀ v ∈ S.dom, ∀ w ∈ S.dom, c.r v w → B.r v w) := by
    intro ocl hb hc
    rw [hb]
    exact ⟨f, hflt, hf, fun _ _ _ _ h => h, hfinv, hfpr, hc⟩
  cases hR : S.rows with
  | none =>
    rw [hR] at hrv
    refine ⟨none, Or.inl ⟨hrv, rfl⟩, hfcase none rfl fun c hc => ?_⟩
    simp [State.retainedCols, hR] at hc
  | some R =>
    rw [hR] at hrv
    obtain ⟨u, ⟨rowsv, cv, -, hcv, rfl⟩, rfl⟩ := hrv
    cases hC : R.cols with
    | none =>
      rw [hC] at hcv
      refine ⟨none, Or.inr ⟨_, _, by rw [hcv]; rfl⟩, hfcase none rfl fun c hc => ?_⟩
      simp [State.retainedCols, hR, hC] at hc
    | some c =>
      rw [hC] at hcv
      obtain ⟨cp, ⟨clab, rfl, hclt, hcl⟩, rfl⟩ := hcv
      refine ⟨some clab, Or.inr ⟨_, _, rfl⟩, ?_⟩
      have hret : S.retainedCols = some c := by simp [State.retainedCols, hR, hC]
      by_cases ht : (List.finRange k).all (fun j => chkQ (indF e S.dom) clab rep (.nat j)) = true
      · have hb : baseSel flab (indF e S.dom) rep (some clab) = clab := by
          simp only [baseSel, ht, if_true]
        rw [hb]
        have hcc := S.colsComparable hinv hR hC
        refine ⟨c, hclt, hcl, (baseChk_iff hflt hf hcl).1 ht, hcc.inv, hcc.proper, ?_⟩
        intro c' hc' _ v _ w _ h
        rw [hret] at hc'
        cases hc'
        exact h
      · refine hfcase (some clab) (by simp only [baseSel, ht]; rfl) fun c' hc' hle => ?_
        rw [hret] at hc'
        cases hc'
        exact absurd ((baseChk_iff hflt hf hcl).2 hle) ht

theorem univBit_eq_one {I : Interval Ω} : univBit D I = 1 ↔ UnivOn D I.part := by
  unfold univBit; split_ifs with h <;> simp [h]

/-- **The split index** is the index of the first interval that holds the domain. -/
theorem splitIdx_props {S : State Ω C} (htr : S.Transitive) (hinv : S.HierInv)
    (h2 : ¬ UnivOn S.dom ⊥) :
    ∃ ht : splitIdx S.dom S.hier < S.hier.length,
      UnivOn S.dom S.hier[splitIdx S.dom S.hier].part ∧
      ∀ i (hi : i < splitIdx S.dom S.hier), ¬ UnivOn S.dom (S.hier[i]'(hi.trans ht)).part := by
  have htr' : ∀ v ∈ S.dom, ∀ w ∈ S.dom, w ∈ orb S.G v := fun v hv w hw => htr v hv w hw
  obtain ⟨pre, J, post, hl, -, hJ⟩ := exists_split htr' ⊥ S.hier hinv.top h2
  have hex : ∃ x ∈ S.hier.map (univBit S.dom), decide (x = 1) = true :=
    ⟨univBit S.dom J, List.mem_map_of_mem (by rw [hl]; simp), by simpa using univBit_eq_one.2 hJ⟩
  have hlt := List.findIdx_lt_length_of_exists hex
  rw [List.length_map] at hlt
  refine ⟨hlt, ?_, fun i hi => ?_⟩
  · have := List.findIdx_getElem (w := by rw [List.length_map]; exact hlt)
      (p := fun x => decide (x = 1)) (xs := S.hier.map (univBit S.dom))
    simp only [List.getElem_map, decide_eq_true_eq] at this
    exact univBit_eq_one.1 this
  · have := List.not_of_lt_findIdx (p := fun x => decide (x = 1))
      (xs := S.hier.map (univBit S.dom)) hi
    simp only [List.getElem_map, decide_eq_false_iff_not] at this
    exact fun h => this (univBit_eq_one.2 h)

/-- The fine end of a prefix of positive length is the partition of its last interval. -/
theorem fineEnd_take {l : List (Interval Ω)} {t : ℕ} (ht : t < l.length) (h0 : 0 < t) :
    fineEnd ⊥ (l.take t) = (l[t - 1]'(by omega)).part := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [List.take_succ, List.getElem?_eq_getElem (by omega), Option.toList_some, fineEnd_append]
  rfl

end BaseMath

/-! ### The exposed hierarchy -/

/-- The partial output of the hierarchy fold: the entries before `i`, with entry `t` replaced
by `ins`. -/
def outAt (xs : List Val) (t : ℕ) (ins : List Val) : ℕ → List Val
  | 0 => []
  | i + 1 => if i = t then outAt xs t ins i ++ ins else outAt xs t ins i ++ [xs.getD i (.nat 0)]

theorem outAt_closed (xs : List Val) (t : ℕ) (ins : List Val) :
    ∀ i, i ≤ xs.length → outAt xs t ins i =
      if i ≤ t then xs.take i else xs.take t ++ ins ++ (xs.take i).drop (t + 1)
  | 0, _ => by simp [outAt]
  | i + 1, hi => by
    rw [outAt, outAt_closed xs t ins i (by omega)]
    have hgi : xs.getD i (.nat 0) = xs[i] := List.getD_eq_getElem _ _ _
    have htk : xs.take (i + 1) = xs.take i ++ [xs[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
    rw [hgi, htk]
    by_cases h1 : i = t
    · subst h1
      rw [if_pos rfl, if_pos le_rfl, if_neg (by omega),
        List.drop_eq_nil_of_le (by simp), List.append_nil]
    · by_cases h2 : i < t
      · rw [if_neg h1, if_pos (by omega), if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega), if_neg (by omega),
          List.drop_append_of_le_length (by simp; omega)]
        simp

theorem outAt_length (xs : List Val) (t : ℕ) (ins : List Val) (ht : t < xs.length) :
    outAt xs t ins xs.length = xs.take t ++ ins ++ xs.drop (t + 1) := by
  rw [outAt_closed xs t ins _ le_rfl, if_neg (by omega), List.take_length]

theorem outAt_prefix (xs : List Val) (t : ℕ) (ins : List Val) :
    ∀ {i j}, i ≤ j → outAt xs t ins i <+: outAt xs t ins j
  | i, j, hij => by
    induction j with
    | zero => obtain rfl : i = 0 := by omega
              exact List.prefix_refl _
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · refine (ih (by omega)).trans ?_
        rw [outAt]; split_ifs <;> exact List.prefix_append _ _
      · obtain rfl : i = j + 1 := by omega
        exact List.prefix_refl _

theorem le_length_outAt (xs : List Val) (t : ℕ) {ins : List Val} (hins : ins ≠ []) :
    ∀ i, i ≤ (outAt xs t ins i).length
  | 0 => Nat.zero_le _
  | i + 1 => by
    have := le_length_outAt xs t hins i
    have : 1 ≤ ins.length := List.length_pos_iff.2 hins
    rw [outAt]; split_ifs <;> simp <;> omega

/-- The step of the hierarchy fold, on `[[t, flag, mid, top], [i, out], x]`. -/
def hstepF : Expr :=
  mk2 (.arith .add (.get (arg 1) (.nat 0)) (.nat 1))
    (.ite (.arith .eq (.get (arg 1) (.nat 0)) (.get (arg 0) (.nat 0)))
      (.ite (.get (arg 0) (.nat 1)) (.snoc (.get (arg 1) (.nat 1)) (.get (arg 0) (.nat 3)))
        (.snoc (.snoc (.get (arg 1) (.nat 1)) (.get (arg 0) (.nat 2))) (.get (arg 0) (.nat 3))))
      (.snoc (.get (arg 1) (.nat 1)) (arg 2)))

/-- The inserted intervals: `[top]` when `flag ≠ 0`, else `[mid, top]`. -/
def insList (flag : ℕ) (mid top : Val) : List Val := if flag = 0 then [mid, top] else [top]

theorem hstep_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some hstepF) (xs : List Val)
    (t flag : ℕ) (mid top : Val) (i : ℕ) (hi : i < xs.length) :
    FunDet P f (.list [.list [.nat t, .nat flag, mid, top],
        .list [.nat i, .list (outAt xs t (insList flag mid top) i)], xs[i]])
      (.list [.nat (i + 1), .list (outAt xs t (insList flag mid top) (i + 1))])
      (100 * ((Val.list [.list [.nat t, .nat flag, mid, top],
        .list [.nat i, .list (outAt xs t (insList flag mid top) i)], xs[i]]).wt +
        (Val.list [.nat (i + 1), .list (outAt xs t (insList flag mid top) (i + 1))]).wt + 10)) := by
  set c : Val := .list [.nat t, .nat flag, mid, top] with hc
  set out := outAt xs t (insList flag mid top) i with hout
  set acc : Val := .list [.nat i, .list out] with hacc
  set a : Val := .list [c, acc, xs[i]] with ha
  have g0 := Det.arg' (P := P) (vs := [c, acc, xs[i]]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [c, acc, xs[i]]) (rest := []) (j := 1) rfl
  have g2 := Det.arg' (P := P) (vs := [c, acc, xs[i]]) (rest := []) (j := 2) rfl
  have hi0 := Det.get' g1 (Det.nat 0) (v := .nat i) rfl
  have ho := Det.get' g1 (Det.nat 1) (v := .list out) rfl
  have ht0 := Det.get' g0 (Det.nat 0) (v := .nat t) rfl
  have hfl := Det.get' g0 (Det.nat 1) (v := .nat flag) rfl
  have hmid := Det.get' g0 (Det.nat 2) (v := mid) rfl
  have htop := Det.get' g0 (Det.nat 3) (v := top) rfl
  have hadd := Det.arith' (op := .add) hi0 (Det.nat 1) (z := i + 1) rfl
  have heq := Det.arith' (op := .eq) hi0 ht0 (z := if i = t then 1 else 0) (by simp [BinOp.eval])
  have hs1 := Det.snoc ho htop
  have hs2 := Det.snoc (Det.snoc ho hmid) htop
  have hs3 := Det.snoc ho g2
  have hins := Det.ite' hfl hs1 hs2
  have hbr := Det.ite' heq hins hs3
  have hval : (if (if i = t then 1 else 0) = 0 then Val.list (out ++ [xs[i]]) else
      (if flag = 0 then Val.list (out ++ [mid] ++ [top]) else Val.list (out ++ [top]))) =
      .list (outAt xs t (insList flag mid top) (i + 1)) := by
    have hgi : xs.getD i (.nat 0) = xs[i] := List.getD_eq_getElem _ _ _
    rw [outAt, ← hout, hgi]
    by_cases h1 : i = t <;> by_cases h2 : flag = 0 <;> simp [h1, h2, insList]
  rw [hval] at hbr
  have hout2 := Det.mk2 hadd hbr
  refine FunDet.intro hf (hout2.mono ?_)
  set out' := outAt xs t (insList flag mid top) (i + 1) with hout'
  have wc : c.wt < a.wt := wt_le_wt_list (by simp [ha])
  have wacc : acc.wt < a.wt := wt_le_wt_list (by simp [ha])
  have wx : xs[i].wt < a.wt := wt_le_wt_list (by simp [ha])
  have wo : (Val.list out).wt < acc.wt := wt_le_wt_list (by simp [hacc])
  have wi : (Val.nat i).wt < acc.wt := wt_le_wt_list (by simp [hacc])
  have wt0 : (Val.nat t).wt < c.wt := wt_le_wt_list (by simp [hc])
  have wf : (Val.nat flag).wt < c.wt := wt_le_wt_list (by simp [hc])
  have wm : mid.wt < c.wt := wt_le_wt_list (by simp [hc])
  have wtp : top.wt < c.wt := wt_le_wt_list (by simp [hc])
  have ws1 := wt_list_snoc_le out top
  have ws2 := wt_list_snoc_le (out ++ [mid]) top
  have ws2' := wt_list_snoc_le out mid
  have ws3 := wt_list_snoc_le out xs[i]
  have w1 := wt_nat_le (i + 1)
  have w2 := wt_nat_le i
  have wo' : (Val.list out').wt < (Val.list [.nat (i + 1), .list out']).wt :=
    wt_le_wt_list (by simp)
  have hb : (if i = t then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega
  have wb := wt_nat_le (if i = t then 1 else 0 : ℕ)
  have hlen' : i + 1 ≤ out'.length :=
    le_length_outAt xs t (by unfold insList; split_ifs <;> simp) (i + 1)
  have := length_lt_wt_list out'
  have hif : (if flag = 0 then Val.list (out ++ [mid] ++ [top]) else Val.list (out ++ [top])).wt ≤
      (Val.list (out ++ [mid] ++ [top])).wt + (Val.list (out ++ [top])).wt := by
    split_ifs <;> omega
  have ea : (Val.list [c, acc, xs[i]]).wt = a.wt := rfl
  clear hout2 hbr hins hs1 hs2 hs3 heq hadd htop hmid hfl ht0 ho hi0 g0 g1 g2
  omega

theorem wt_nat_mono {a b : ℕ} (h : a ≤ b) : (Val.nat a).wt ≤ (Val.nat b).wt := by
  rw [wt_nat, wt_nat]; exact Nat.add_le_add_right (GI.Machine.len_mono h) 2

/-- On `[hv, t, lab2, nf, d]`: the hierarchy with the interval `J = hv[t]` replaced by the
middle interval `[lab2, nf / d, min cap (nf / d), origin]` (only if `nf / d ≠ 1`) and the top
interval `[J₀, d, min cap d, origin]`. -/
def hierE (bf : ℕ) : Expr :=
  let J := Expr.get (arg 0) (arg 1)
  let cap := Expr.get J (.nat 2)
  let c₁ := Expr.arith .div (arg 3) (arg 4)
  let top := mk4 (.get J (.nat 0)) (arg 4) (.arith .sub cap (.arith .sub cap (arg 4)))
    (.get J (.nat 3))
  let mid := mk4 (arg 2) c₁ (.arith .sub cap (.arith .sub cap c₁)) (.get J (.nat 3))
  .get (.call bf (mk3 (mk4 (arg 1) (.arith .eq c₁ (.nat 1)) mid top) (arg 0)
    (mk2 (.nat 0) .nil))) (.nat 1)

/-- The hierarchy module at base `b` (5 functions). -/
def hierFuns (b : ℕ) : List Expr := [hierE (b + 2), hstepF] ++ foldlFuns (b + 2) (b + 1)

theorem length_hierFuns (b : ℕ) : (hierFuns b).length = 5 := by
  simp [hierFuns, foldlFuns, loopFuns]

/-- The top interval value. -/
def topVal (pv : Val) (d cap o : ℕ) : Val := .list [pv, .nat d, .nat (min cap d), .nat o]

/-- The new hierarchy value. -/
def hierOut (vs : List Val) (t : ℕ) (lab2 : Val) (nf d : ℕ) (pv : Val) (cap o : ℕ) : List Val :=
  vs.take t ++ insList (if nf / d = 1 then 1 else 0)
    (.list [lab2, .nat (nf / d), .nat (min cap (nf / d)), .nat o]) (topVal pv d cap o) ++
    vs.drop (t + 1)

/-- The cost constant of the hierarchy module. -/
def exHierK : ℕ := 10 ^ 7

theorem min_eq_sub (a b : ℕ) : a - (a - b) = min a b := by omega

/-- **The exposed hierarchy value.** -/
theorem exHier_spec {P : Program} {b : ℕ} (h : P.HasAt b (hierFuns b)) {vs : List Val} {t : ℕ}
    (ht : t < vs.length) {pv : Val} {r cap o : ℕ}
    (hJ : vs[t] = .list [pv, .nat r, .nat cap, .nat o]) (lab2 : Val) (nf d : ℕ) :
    FunDet P b (.list [.list vs, .nat t, lab2, .nat nf, .nat d])
      (.list (hierOut vs t lab2 nf d pv cap o))
      (exHierK * ((Val.list [.list vs, .nat t, lab2, .nat nf, .nat d]).wt + 1) ^ 2) := by
  have hentry : P.funs[b]? = some (hierE (b + 2)) := (h.block 0 rfl : P.HasAt (b + 0) _).single
  have hst : P.funs[b + 1]? = some hstepF := (h.block 1 rfl : P.HasAt (b + 1) _).single
  have hfold : P.HasAt (b + 2) (foldlFuns (b + 2) (b + 1)) := h.block 2 rfl
  set a : Val := .list [.list vs, .nat t, lab2, .nat nf, .nat d] with ha
  set W := a.wt with hW
  set c₁ := nf / d with hc₁
  set mid : Val := .list [lab2, .nat c₁, .nat (min cap c₁), .nat o] with hmid
  set top : Val := topVal pv d cap o with htop
  set flag : ℕ := if c₁ = 1 then 1 else 0 with hflag
  set ins := insList flag mid top with hins
  set ctx : Val := .list [.nat t, .nat flag, mid, top] with hctx
  -- weights
  have wvs : (Val.list vs).wt < W := wt_le_wt_list (by simp [ha])
  have wl2 : lab2.wt < W := wt_le_wt_list (by simp [ha])
  have wnf : (Val.nat nf).wt < W := wt_le_wt_list (by simp [ha])
  have wd : (Val.nat d).wt < W := wt_le_wt_list (by simp [ha])
  have wt' : (Val.nat t).wt < W := wt_le_wt_list (by simp [ha])
  have wJ : vs[t].wt < (Val.list vs).wt := wt_le_wt_list (List.getElem_mem ht)
  rw [hJ] at wJ
  have wpv : pv.wt < (Val.list [pv, .nat r, .nat cap, .nat o]).wt := wt_le_wt_list (by simp)
  have wcap : (Val.nat cap).wt < (Val.list [pv, .nat r, .nat cap, .nat o]).wt :=
    wt_le_wt_list (by simp)
  have wo : (Val.nat o).wt < (Val.list [pv, .nat r, .nat cap, .nat o]).wt :=
    wt_le_wt_list (by simp)
  have wc1 : (Val.nat c₁).wt ≤ (Val.nat nf).wt := wt_nat_mono (Nat.div_le_self _ _)
  have wm1 : (Val.nat (min cap c₁)).wt ≤ (Val.nat cap).wt := wt_nat_mono (min_le_left _ _)
  have wm2 : (Val.nat (min cap d)).wt ≤ (Val.nat cap).wt := wt_nat_mono (min_le_left _ _)
  have wmid : mid.wt ≤ 2 * (lab2.wt + (Val.nat c₁).wt + (Val.nat (min cap c₁)).wt +
      (Val.nat o).wt) + 8 := by
    have e : mid = .list [lab2, .nat c₁, .nat (min cap c₁), .nat o] := rfl
    rw [e]
    have := wt_list_le [lab2, .nat c₁, .nat (min cap c₁), .nat o]; simp at this; omega
  have wtop : top.wt ≤ 2 * (pv.wt + (Val.nat d).wt + (Val.nat (min cap d)).wt +
      (Val.nat o).wt) + 8 := by
    have e : top = .list [pv, .nat d, .nat (min cap d), .nat o] := rfl
    rw [e]
    have := wt_list_le [pv, .nat d, .nat (min cap d), .nat o]; simp at this; omega
  have hmidW : mid.wt ≤ 8 * W + 8 := by omega
  have htopW : top.wt ≤ 8 * W + 8 := by omega
  have wfl : (Val.nat flag).wt ≤ 3 := by
    have := wt_nat_le flag
    have : flag ≤ 1 := by simp only [hflag]; split_ifs <;> omega
    omega
  have wctx : ctx.wt ≤ 2 * ((Val.nat t).wt + (Val.nat flag).wt + mid.wt + top.wt) + 8 := by
    have e : ctx = .list [.nat t, .nat flag, mid, top] := rfl
    rw [e]
    have := wt_list_le [.nat t, .nat flag, mid, top]; simp at this; omega
  -- The final list and its weight.
  set fin := outAt vs t ins vs.length with hfin
  have hfin' : fin = hierOut vs t lab2 nf d pv cap o := by
    rw [hfin, outAt_length vs t ins ht]; rfl
  have wfin : (Val.list fin).wt ≤ 2 * ((Val.list vs).wt + mid.wt + top.wt) + vs.length + 10 := by
    rw [hfin, outAt_length vs t ins ht]
    have h1 := wt_list_le (vs.take t ++ ins ++ vs.drop (t + 1))
    have hsplit : vs = vs.take t ++ vs[t] :: vs.drop (t + 1) := by
      conv_lhs => rw [← List.take_append_drop t vs, List.drop_eq_getElem_cons ht]
    have hs : (vs.map Val.wt).sum = ((vs.take t).map Val.wt).sum + vs[t].wt +
        ((vs.drop (t + 1)).map Val.wt).sum := by
      conv_lhs => rw [hsplit]
      simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      omega
    have hsv := sum_wt_lt_wt_list vs
    have hins' : (ins.map Val.wt).sum ≤ mid.wt + top.wt := by
      simp only [hins, insList]; split_ifs <;> simp
    have hlen : (vs.take t ++ ins ++ vs.drop (t + 1)).length ≤ vs.length + 1 := by
      have : ins.length ≤ 2 := by simp only [hins, insList]; split_ifs <;> simp
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    simp only [List.map_append, List.sum_append] at h1
    omega
  have hlenW : vs.length < W := by
    have := length_lt_wt_list vs; omega
  -- The fold.
  set M := 2 * (vs.length + 2 + (Val.list fin).wt) + 6 with hM
  have hInvM : ∀ i, i ≤ vs.length → (Val.list [.nat i, .list (outAt vs t ins i)]).wt ≤ M := by
    intro i hi
    have h1 := wt_list2_le (.nat i) (.list (outAt vs t ins i))
    have h2 := wt_nat_le i
    have h3 : (Val.list (outAt vs t ins i)).wt ≤ (Val.list fin).wt :=
      wt_list_mono (outAt_prefix vs t ins hi)
    omega
  set Bf : ℕ → ℕ := fun i => 100 * ((Val.list [ctx, .list [.nat i, .list (outAt vs t ins i)],
    vs.getD i (.nat 0)]).wt + (Val.list [.nat (i + 1), .list (outAt vs t ins (i + 1))]).wt + 10)
    with hBf
  have hF := foldl_spec hfold (c := ctx) (xs := vs) (acc0 := .list [.nat 0, .list []])
    (Inv := fun i acc => acc = .list [.nat i, .list (outAt vs t ins i)]) (M := M) (B := Bf)
    rfl (fun i acc hi hacc => hacc ▸ hInvM i hi) (by
      intro i acc hi hacc
      subst hacc
      have hgd : vs.getD i (.nat 0) = vs[i] := List.getD_eq_getElem _ _ _
      refine FunAll.mono (hstep_det hst vs t flag mid top i hi) fun w cost hw => ⟨hw.1, ?_⟩
      simp only [hBf, hgd]
      exact hw.2)
  have hBi : ∀ i ∈ Finset.range vs.length, Bf i ≤ 100 * (2 * (ctx.wt + M + W) + 7 + M + 10) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hgd : vs.getD i (.nat 0) = vs[i]'hi' := List.getD_eq_getElem _ _ _
    simp only [hBf, hgd]
    have h1 := wt_list3_le ctx (.list [.nat i, .list (outAt vs t ins i)]) (vs[i]'hi')
    have h2 := hInvM i hi'.le
    have h3 := hInvM (i + 1) hi'
    have h4 : (vs[i]'hi').wt < (Val.list vs).wt := wt_le_wt_list (List.getElem_mem hi')
    omega
  have hsum := Finset.sum_le_card_nsmul _ _ _ hBi
  rw [Finset.card_range, smul_eq_mul] at hsum
  have hFD : FunDet P (b + 2) (.list [ctx, .list vs, .list [.nat 0, .list []]])
      (.list [.nat vs.length, .list fin])
      (vs.length * (100 * (2 * (ctx.wt + M + W) + 7 + M + 10)) + loopModK * (vs.length + 1) *
        ((Val.list [ctx, .list vs, .list [.nat 0, .list []]]).wt + vs.length + M + 1)) :=
    FunAll.mono hF fun w cost hw => ⟨hw.1, hw.2.trans (Nat.add_le_add_right hsum _)⟩
  -- The program.
  have g0 := Det.arg' (P := P) (vs := [.list vs, .nat t, lab2, .nat nf, .nat d]) (rest := [])
    (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [.list vs, .nat t, lab2, .nat nf, .nat d]) (rest := [])
    (j := 1) rfl
  have g2 := Det.arg' (P := P) (vs := [.list vs, .nat t, lab2, .nat nf, .nat d]) (rest := [])
    (j := 2) rfl
  have g3 := Det.arg' (P := P) (vs := [.list vs, .nat t, lab2, .nat nf, .nat d]) (rest := [])
    (j := 3) rfl
  have g4 := Det.arg' (P := P) (vs := [.list vs, .nat t, lab2, .nat nf, .nat d]) (rest := [])
    (j := 4) rfl
  have hJd := Det.get' g0 g1 (v := .list [pv, .nat r, .nat cap, .nat o])
    (by rw [List.getElem?_eq_getElem ht, hJ])
  have hcap := Det.get' hJd (Det.nat 2) (v := .nat cap) rfl
  have hpv := Det.get' hJd (Det.nat 0) (v := pv) rfl
  have ho := Det.get' hJd (Det.nat 3) (v := .nat o) rfl
  have hc1 := Det.arith (op := .div) g3 g4
  have hs1 := Det.arith (op := .sub) hcap (Det.arith (op := .sub) hcap g4)
  have hs2 := Det.arith (op := .sub) hcap (Det.arith (op := .sub) hcap hc1)
  have hfl := Det.arith (op := .eq) hc1 (Det.nat 1)
  rw [show BinOp.eval .div nf d = c₁ from rfl] at hc1 hs2 hfl
  rw [show BinOp.eval .sub cap (BinOp.eval .sub cap d) = min cap d from min_eq_sub _ _] at hs1
  rw [show BinOp.eval .sub cap (BinOp.eval .sub cap c₁) = min cap c₁ from min_eq_sub _ _] at hs2
  rw [show BinOp.eval .eq c₁ 1 = flag by simp [BinOp.eval, hflag]] at hfl
  have htopd := Det.mk4 hpv g4 hs1 ho
  have hmidd := Det.mk4 g2 hc1 hs2 ho
  have hctxd := Det.mk4 g1 hfl hmidd htopd
  have hacc0 := Det.mk2 (P := P) (env := [a]) (Det.nat 0) Det.nil
  have hcall := Det.call (Det.mk3 hctxd g0 hacc0) hFD
  have hres := Det.get' hcall (Det.nat 1) (v := .list fin) rfl
  refine FunDet.intro hentry ?_
  rw [← hfin']
  refine hres.mono ?_
  have ea : (Val.list [Val.list vs, Val.nat t, lab2, Val.nat nf, Val.nat d]).wt = W := rfl
  rw [ea]
  have em : (Val.list [lab2, Val.nat c₁, Val.nat (min cap c₁), Val.nat o]).wt = mid.wt := rfl
  have et : (Val.list [pv, Val.nat d, Val.nat (min cap d), Val.nat o]).wt = top.wt := rfl
  have ec : (Val.list [Val.nat t, Val.nat flag, Val.list [lab2, Val.nat c₁, Val.nat (min cap c₁),
    Val.nat o], Val.list [pv, Val.nat d, Val.nat (min cap d), Val.nat o]]).wt = ctx.wt := rfl
  have ec3 : (Val.list [Val.list [Val.nat t, Val.nat flag, Val.list [lab2, Val.nat c₁,
    Val.nat (min cap c₁), Val.nat o], Val.list [pv, Val.nat d, Val.nat (min cap d), Val.nat o]],
    Val.list vs, Val.list [Val.nat 0, Val.list []]]).wt =
    (Val.list [ctx, Val.list vs, Val.list [Val.nat 0, Val.list []]]).wt := rfl
  have ws1 : (Val.nat (BinOp.eval .sub cap c₁)).wt ≤ (Val.nat cap).wt :=
    wt_nat_mono (Nat.sub_le _ _)
  have ws2 : (Val.nat (BinOp.eval .sub cap d)).wt ≤ (Val.nat cap).wt :=
    wt_nat_mono (Nat.sub_le _ _)
  have w00 : (Val.list [.nat 0, .list []]).wt ≤ 30 := by
    have := wt_list2_le (.nat 0) (.list []); have := wt_nat_le 0
    have : (Val.list []).wt ≤ 4 := by rw [wt_list_eq]; simp [GI.Machine.len]
    omega
  have w3 := wt_list3_le ctx (.list vs) (.list [.nat 0, .list []])
  have w4 := wt_list2_le (.nat vs.length) (.list fin)
  have w5 := wt_nat_le vs.length
  have wlen := length_lt_wt_list fin
  have hflen : fin.length ≤ vs.length + 1 := by
    rw [hfin, outAt_length vs t ins ht]
    have : ins.length ≤ 2 := by simp only [hins, insList]; split_ifs <;> simp
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = W + 1 := ⟨_, rfl⟩
  have hQ : 100 * (2 * (ctx.wt + M + W) + 7 + M + 10) ≤ 50000 * Y := by omega
  have p1 : vs.length * (100 * (2 * (ctx.wt + M + W) + 7 + M + 10)) ≤ 50000 * Y ^ 2 := by
    calc _ ≤ Y * (50000 * Y) := Nat.mul_le_mul (by omega) hQ
      _ = 50000 * Y ^ 2 := by ring
  have hL : (Val.list [ctx, .list vs, .list [.nat 0, .list []]]).wt + vs.length + M + 1 ≤
      400 * Y := by omega
  have p2 : loopModK * (vs.length + 1) *
      ((Val.list [ctx, .list vs, .list [.nat 0, .list []]]).wt + vs.length + M + 1) ≤
      400000 * Y ^ 2 := by
    calc _ ≤ 1000 * Y * (400 * Y) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hL
      _ = 400000 * Y ^ 2 := by ring
  have hYY : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  rw [← hY]
  simp only [exHierK]
  clear hres hcall hacc0 hctxd hmidd htopd hfl hs2 hs1 hc1 ho hpv hcap hJd g0 g1 g2 g3 g4 hFD
    hF hsum hBi
  omega

/-! ### The exposure program, first part: up to the call of `MinimalBlocks` -/

/-- On the canonical state value `[k, gv, dv, xv, yv, hv, rv, …]`: the split index `t`, the class
numbering of the fine end `f`, the class numbering of the base partition, and the action on the
base classes, `[t, clsf, cls1, act1]`. -/
def prepE (bsplit brange bcls bbase bact : ℕ) : Expr :=
  .letE (.call bsplit (mk2 (arg 2) (arg 5)))
  (.letE (.ite (.var 1) (.get (.get (arg 5) (.arith .sub (.var 1) (.nat 1))) (.nat 0))
      (.call brange (arg 0)))
  (.letE (.call bcls (mk2 (.var 2) (arg 2)))
  (.letE (.call bbase (mk4 (arg 6) (.var 3) (arg 2) (.var 2)))
  (.letE (.call bcls (mk2 (.var 4) (arg 2)))
  (mk4 (.var 1) (.var 3) (.var 5)
    (.call bact (mk2 (mk2 (.get (.var 5) (.nat 0)) (.get (.var 5) (.nat 1))) (arg 1))))))))

/-- The labels of the fine end: the points when `t = 0`, else the labels stored in `vs[t - 1]`. -/
def FlabOK (vs : List Val) (t : ℕ) (flab : Fin k → ℕ) : Prop :=
  (t = 0 ∧ flab = fun i : Fin k => (i : ℕ)) ∨
    (0 < t ∧ ∃ (h : t - 1 < vs.length) (r cap o : ℕ),
      vs[t - 1] = .list [encFun flab, .nat r, .nat cap, .nat o])

/-- The base labels computed by the program. -/
def blabOf (flab dm : Fin k → ℕ) (ocl : Option (Fin k → ℕ)) : Fin k → ℕ :=
  baseSel flab dm (Cls.repOf (Cls.keyOf flab dm)) ocl

/-- The output of the first part. -/
def prepVal (t : ℕ) (flab dm : Fin k → ℕ) (ocl : Option (Fin k → ℕ)) (gs : List (Perm (Fin k))) :
    Val :=
  .list [.nat t, clsVal flab dm, clsVal (blabOf flab dm ocl) dm,
    actVal (Cls.numOf dm (Cls.keyOf (blabOf flab dm ocl) dm))
      (Cls.repsOf dm (Cls.keyOf (blabOf flab dm ocl) dm)) gs]

theorem prep_flab_det {P : Program} {brange : ℕ} (hrange : P.HasAt brange (rangeFuns brange))
    {env : List Val} {vs : List Val} {t : ℕ} {flab : Fin k → ℕ} (hfl : FlabOK vs t flab)
    {cs : List Val} (hcs5 : cs[5]? = some (.list vs)) (hcs0 : cs[0]? = some (.nat k))
    (henv : env[0]? = some (.nat t)) :
    Det P (.list cs :: env) (.ite (.var 1) (.get (.get (arg 5) (.arith .sub (.var 1) (.nat 1)))
      (.nat 0)) (.call brange (arg 0))) (encFun flab)
      (2 * (Val.list cs).wt + 10 * (Val.nat t).wt + 7000 * (k + 1) ^ 3 + 10 * (Val.list vs).wt +
        10 * (encFun flab).wt + 4 * (k + 1) ^ 2 + 50) := by
  have hv1 : (Val.list cs :: env)[1]? = some (.nat t) := henv
  have d1 := Det.var' (P := P) hv1
  rcases hfl with ⟨rfl, rfl⟩ | ⟨ht, hlt, r, cap, o, hvs⟩
  · have d0 := Det.arg' (P := P) (rest := env) hcs0
    have hr := Det.call d0 (range_det hrange k)
    rw [natList_range_eq] at hr
    refine (Det.ite_zero d1 hr).mono ?_
    have := wt_nat_le 0
    have := wt_nat_le k
    have : (Val.nat k).wt < (Val.list cs).wt := wt_le_wt_list (List.mem_of_getElem? hcs0)
    omega
  · have d5 := Det.arg' (P := P) (rest := env) hcs5
    have dsub := Det.arith (op := .sub) d1 (Det.nat 1)
    have dget := Det.get' d5 dsub (v := .list [encFun flab, .nat r, .nat cap, .nat o])
      (by rw [show BinOp.eval .sub t 1 = t - 1 from rfl, List.getElem?_eq_getElem hlt, hvs])
    have dfl := Det.get' dget (Det.nat 0) (v := encFun flab) rfl
    refine (Det.ite_pos d1 (by omega) dfl).mono ?_
    have h1 : (Val.list [encFun flab, .nat r, .nat cap, .nat o]).wt < (Val.list vs).wt := by
      rw [← hvs]; exact wt_le_wt_list (List.getElem_mem hlt)
    have h2 : (Val.nat (BinOp.eval .sub t 1)).wt ≤ (Val.nat t).wt := wt_nat_mono (Nat.sub_le _ _)
    have := wt_nat_le 1
    omega

/-- The cost constant of the first part. -/
def prepK : ℕ := 10 ^ 20

theorem blabOf_lt {flab dm : Fin k → ℕ} {ocl : Option (Fin k → ℕ)} (hflt : ∀ i, flab i < k)
    (hocl : ∀ clab, ocl = some clab → ∀ i, clab i < k) (i : Fin k) : blabOf flab dm ocl i < k := by
  cases ocl with
  | none => exact hflt i
  | some clab =>
    simp only [blabOf, baseSel]
    split_ifs
    exacts [hocl clab rfl i, hflt i]

/-- **The first part of the exposure program.** -/
theorem exPrep_spec {P : Program} {f bsplit brange bcls bbase bact : ℕ}
    (hf : P.funs[f]? = some (prepE bsplit brange bcls bbase bact))
    (hsplit : P.HasAt bsplit (hsplitFuns bsplit bcls)) (hrange : P.HasAt brange (rangeFuns brange))
    (hcls : P.HasAt bcls (clsFuns bcls)) (hbase : P.HasAt bbase (baseFuns bbase))
    (hact : P.HasAt bact (actFuns bact))
    {e : Ω ≃ Fin k} {D : Set Ω} (hne : D.Nonempty) {gs : List (Perm (Fin k))}
    (hgs : gs.length ≤ k ^ 2) {vs : List Val} {hier : List (Interval Ω)}
    (hH : HierValC e (.list vs) hier) {flab : Fin k → ℕ} (hfl : FlabOK vs (splitIdx D hier) flab)
    (hflt : ∀ i, flab i < k) {rv : Val} {ocl : Option (Fin k → ℕ)}
    (hrv : (rv = .list [] ∧ ocl = none) ∨ ∃ mv rowsv, rv = .list [.list [mv, rowsv, colsVal ocl]])
    (hblt : ∀ i, blabOf flab (indF e D) ocl i < k) (xv yv fv hh nN : Val) :
    FunDet P f (.list [.nat k, encGroup gs, encFun (indF e D), xv, yv, .list vs, rv, fv, hh, nN])
      (prepVal (splitIdx D hier) flab (indF e D) ocl gs)
      (prepK * ((Val.list [.nat k, encGroup gs, encFun (indF e D), xv, yv, .list vs, rv, fv, hh,
        nN]).wt + 1) ^ 8) := by
  set dm := indF e D with hdm
  set cs : List Val := [.nat k, encGroup gs, encFun dm, xv, yv, .list vs, rv, fv, hh, nN] with hcs
  set a : Val := .list cs with ha
  set W := a.wt with hW
  set t := splitIdx D hier with ht
  set blab := blabOf flab dm ocl with hblab
  have hdm1 : ∀ i, dm i ≤ 1 := fun i => by simp only [hdm, indF]; split_ifs <;> omega
  -- weights of the components
  have wmem : ∀ x ∈ cs, x.wt < W := fun x hx => wt_le_wt_list hx
  have wk : (Val.nat k).wt < W := wmem _ (by simp [hcs])
  have wg : (encGroup gs).wt < W := wmem _ (by simp [hcs])
  have wdm : (encFun dm).wt < W := wmem _ (by simp [hcs])
  have wvs : (Val.list vs).wt < W := wmem _ (by simp [hcs])
  have wrv : rv.wt < W := wmem _ (by simp [hcs])
  have hkW : k < W := by
    have h1 := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (dm i))
    have h3 : (encFun dm).wt = (Val.list ((List.finRange k).map fun i => Val.nat (dm i))).wt :=
      rfl
    simp only [List.length_map, List.length_finRange] at h1
    omega
  -- step 1: the split index
  have s1 : Det P [a] (.call bsplit (mk2 (arg 2) (arg 5))) (.nat t) _ :=
    Det.call (Det.mk2 (Det.arg' (vs := cs) (rest := []) (j := 2) rfl)
      (Det.arg' (vs := cs) (rest := []) (j := 5) rfl)) (hsplit_spec hsplit hcls hne hH)
  -- step 2: the labels of the fine end
  have s2 := prep_flab_det (P := P) hrange (env := [.nat t]) hfl (cs := cs) rfl rfl rfl
  -- step 3: the numbering of the fine end
  have s3 := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, .nat t, encFun flab]) (i := 2) rfl)
    (Det.arg' (vs := cs) (rest := [.nat t, encFun flab]) (j := 2) rfl))
    (cls_spec hcls flab dm (X := W) (fun i => (hflt i).le.trans hkW.le) hdm1 hkW.le)
  -- step 4: the base labels
  have s4 := Det.call (Det.mk4 (Det.arg' (vs := cs) (rest := [.nat t, encFun flab, clsVal flab dm])
      (j := 6) rfl)
    (Det.var' (P := P) (env := [a, .nat t, encFun flab, clsVal flab dm]) (i := 3) rfl)
    (Det.arg' (vs := cs) (rest := [.nat t, encFun flab, clsVal flab dm]) (j := 2) rfl)
    (Det.var' (P := P) (env := [a, .nat t, encFun flab, clsVal flab dm]) (i := 2) rfl))
    (base_spec hbase dm flab (Cls.repOf (Cls.keyOf flab dm)) (Cls.repOf_lt _) hrv le_rfl)
  -- step 5: the numbering of the base
  have s5 := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, .nat t, encFun flab, clsVal flab dm,
      encFun blab]) (i := 4) rfl)
    (Det.arg' (vs := cs) (rest := [.nat t, encFun flab, clsVal flab dm, encFun blab]) (j := 2) rfl))
    (cls_spec hcls blab dm (X := W) (fun i => (hblt i).le.trans hkW.le) hdm1 hkW.le)
  -- step 6: the action on the base classes
  set env6 : List Val := [a, .nat t, encFun flab, clsVal flab dm, encFun blab, clsVal blab dm]
    with henv6
  have hnum1 : ∀ i, Cls.numOf dm (Cls.keyOf blab dm) i ≤ W := fun i => (numOf_le _ _ i).trans hkW.le
  have hreps1 : ∀ r ∈ Cls.repsOf dm (Cls.keyOf blab dm), r < k := fun r hr => by
    obtain ⟨h, -⟩ := (Cls.mem_repsOf dm _).1 hr; exact h
  have hlen1 : (Cls.repsOf dm (Cls.keyOf blab dm)).length ≤ W :=
    (Cls.repsOf_length_le _ _).trans hkW.le
  have hgsW : gs.length ≤ W ^ 2 := hgs.trans (Nat.pow_le_pow_left hkW.le 2)
  have d5 := Det.var' (P := P) (env := env6) (i := 5) (v := clsVal blab dm) rfl
  have s6a := Det.call (Det.mk2 (Det.mk2 (Det.get' d5 (Det.nat 0)
      (v := encFun (Cls.numOf dm (Cls.keyOf blab dm))) rfl)
    (Det.get' d5 (Det.nat 1) (v := natList (Cls.repsOf dm (Cls.keyOf blab dm))) rfl))
    (Det.arg' (vs := cs) (rest := env6.tail) (j := 1) rfl))
    (act_spec hact (Cls.numOf dm (Cls.keyOf blab dm)) (Cls.repsOf dm (Cls.keyOf blab dm)) gs
      hnum1 hreps1 hlen1 hkW.le hgsW)
  have s6 := Det.mk4 (Det.var' (P := P) (env := env6) (i := 1) (v := .nat t) rfl)
    (Det.var' (P := P) (env := env6) (i := 3) (v := clsVal flab dm) rfl) d5 s6a
  refine FunDet.intro hf ((Det.letE s1 (Det.letE s2 (Det.letE s3 (Det.letE s4
    (Det.letE s5 s6))))).mono ?_)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = W + 1 := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by omega
  have ecs : (Val.list cs).wt = W := rfl
  have edm : (Val.list [encFun (indF e D), Val.list vs]).wt =
    (Val.list [encFun dm, Val.list vs]).wt := rfl
  have ecl : (Val.list [rv, Val.list [encFun (Cls.numOf dm (Cls.keyOf flab dm)),
      natList (Cls.repsOf dm (Cls.keyOf flab dm)), encFun (Cls.repOf (Cls.keyOf flab dm))],
      encFun dm, encFun flab]).wt = (Val.list [rv, clsVal flab dm, encFun dm, encFun flab]).wt :=
    rfl
  have ebl : (encFun (baseSel flab dm (Cls.repOf (Cls.keyOf flab dm)) ocl)).wt =
    (encFun blab).wt := rfl
  rw [ecs, edm, ecl, ebl]
  -- the split index is below the length
  have htl : t ≤ vs.length := by
    obtain ⟨ws, hws, hf2⟩ := hH
    cases hws
    have := List.findIdx_le_length (p := fun x => decide (x = 1)) (xs := hier.map (univBit D))
    rw [List.length_map, ← (List.Forall₂.length_eq hf2)] at this
    exact this
  have hvl : vs.length < W := by have := length_lt_wt_list vs; omega
  have wt_ := wt_nat_le t
  have hkY : k + 1 ≤ Y := by omega
  have hk2 : (k + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hkY 2
  have hk3 : (k + 1) ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left hkY 3
  have hWY2 : W ≤ Y ^ 2 := by nlinarith
  have hY23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY34 : Y ^ 3 ≤ Y ^ 4 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY45 : Y ^ 4 ≤ Y ^ 5 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY56 : Y ^ 5 ≤ Y ^ 6 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY68 : Y ^ 6 ≤ Y ^ 8 := Nat.pow_le_pow_right hY1 (by norm_num)
  have wfl : (encFun flab).wt ≤ 5 * Y ^ 2 := by
    have := wt_encFun_le' flab (B := W) (fun i => (hflt i).le.trans hkW.le) hkW.le; rw [← hY] at this; exact this
  have wbl : (encFun blab).wt ≤ 5 * Y ^ 2 := by
    have := wt_encFun_le' blab (B := W) (fun i => (hblt i).le.trans hkW.le) hkW.le; rw [← hY] at this; exact this
  have wcf : (clsVal flab dm).wt ≤ 40 * Y ^ 2 := (wt_clsVal_le flab dm).trans (by
    have := Nat.pow_le_pow_left hkY 2; omega)
  have wcb : (clsVal blab dm).wt ≤ 40 * Y ^ 2 := (wt_clsVal_le blab dm).trans (by
    have := Nat.pow_le_pow_left hkY 2; omega)
  have wnum : (encFun (Cls.numOf dm (Cls.keyOf blab dm))).wt ≤ 5 * Y ^ 2 := by
    have := wt_encFun_le' _ (B := W) hnum1 hkW.le; rw [← hY] at this; exact this
  have wreps : (natList (Cls.repsOf dm (Cls.keyOf blab dm))).wt ≤ 5 * Y ^ 2 := by
    have := wt_natList_le_sq (B := W) (fun x hx => (hreps1 x hx).le.trans hkW.le) hlen1; rw [← hY] at this; exact this
  have wact := wt_actVal_le (Cls.numOf dm (Cls.keyOf blab dm)) (Cls.repsOf dm (Cls.keyOf blab dm))
    gs hnum1 hlen1 hkW.le hgsW
  rw [← hY] at wact
  have w1 := wt_list2_le (encFun dm) (Val.list vs)
  have w2 := wt_list2_le (encFun flab) (encFun dm)
  have w3 := wt_list2_le (encFun blab) (encFun dm)
  have w4 := wt_list4_le rv (clsVal flab dm) (encFun dm) (encFun flab)
  have w5 := wt_list2_le (encFun (Cls.numOf dm (Cls.keyOf blab dm)))
    (natList (Cls.repsOf dm (Cls.keyOf blab dm)))
  have w6 := wt_list2_le (Val.list [encFun (Cls.numOf dm (Cls.keyOf blab dm)),
    natList (Cls.repsOf dm (Cls.keyOf blab dm))]) (encGroup gs)
  have w7 := wt_list4_le (.nat t) (clsVal flab dm) (clsVal blab dm)
    (actVal (Cls.numOf dm (Cls.keyOf blab dm)) (Cls.repsOf dm (Cls.keyOf blab dm)) gs)
  -- the split cost
  have hsp : hsplitK * ((Val.list [encFun dm, Val.list vs]).wt + 1) ^ 5 ≤ 10 ^ 19 * Y ^ 5 := by
    have : (Val.list [encFun dm, Val.list vs]).wt + 1 ≤ 7 * Y := by omega
    calc _ ≤ hsplitK * (7 * Y) ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 5)
      _ = 16807 * 10 ^ 14 * Y ^ 5 := by simp only [hsplitK]; ring
      _ ≤ 10 ^ 19 * Y ^ 5 := Nat.mul_le_mul_right _ (by norm_num)
  -- the base cost
  have hbs : 10 ^ 9 * ((Val.list [rv, clsVal flab dm, encFun dm, encFun flab]).wt + 1) ^ 3 ≤
      10 ^ 16 * Y ^ 6 := by
    have : (Val.list [rv, clsVal flab dm, encFun dm, encFun flab]).wt + 1 ≤ 120 * Y ^ 2 := by
      omega
    calc _ ≤ 10 ^ 9 * (120 * Y ^ 2) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 3)
      _ = 1728000 * 10 ^ 9 * Y ^ 6 := by ring
      _ ≤ 10 ^ 16 * Y ^ 6 := Nat.mul_le_mul_right _ (by norm_num)
  rw [← hY]
  simp only [prepK, clsK] at *
  clear s1 s2 s3 s4 s5 s6 s6a d5
  omega

end GI.Impl
