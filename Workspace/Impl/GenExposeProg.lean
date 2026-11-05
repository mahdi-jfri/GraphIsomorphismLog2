module

public import Workspace.Impl.GenNormNumbering
public import Workspace.Impl.GenExpose

@[expose] public section

/-!
# The exposure program

The full exposure step of Algorithm 5 as a `GI.Lang` program (`expose_spec`). The first part
(`exPrep_spec`) computes the split index, the class numbering of the fine end and of the base
partition, and the action on the base classes. This file adds the call of the cited
`MinimalBlocks`, the pull back of its labels to the points, the class numbering of the new
blocks, the action on them, and the exposed hierarchy. The math of the result is
`expose_quot`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup gens)

variable {Ω C : Type} {k : ℕ}

/-! ### Facts used by the program -/

theorem Cls.numOf_le_length (dm key : Fin k → ℕ) (i : Fin k) :
    Cls.numOf dm key i ≤ (Cls.repsOf dm key).length := by
  unfold Cls.numOf; split_ifs
  · exact le_rfl
  · exact List.findIdx_le_length

/-- A function on `Fin d`, read at a number, with `0` past the end. -/
def padF {d : ℕ} (lab : Fin d → ℕ) (x : ℕ) : ℕ := if h : x < d then lab ⟨x, h⟩ else 0

/-- The value of the gather step: the block labels pulled back to the points. -/
theorem gather_eq {d : ℕ} (lab : Fin d → ℕ) (num : Fin k → ℕ) :
    Val.list (((List.finRange k).map num).map fun i =>
      ((((List.finRange d).map fun j => Val.nat (lab j)) ++ [Val.nat 0]).getD i (.nat 0))) =
      encFun fun i => padF lab (num i) := by
  simp only [encFun, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, padF]
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega)]
    simp
  · by_cases h' : num i = d
    · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp [h']
    · rw [List.getD_eq_default _ _ (by simp; omega)]

/-- The labels of the fine end of the prefix before the split interval. -/
theorem exists_flab {e : Ω ≃ Fin k} {vs : List Val} {hier : List (Interval Ω)}
    (h : List.Forall₂ (IntervalValC e) vs hier) {t : ℕ} (ht : t < hier.length) :
    ∃ flab : Fin k → ℕ, FlabOK vs t flab ∧ (∀ i, flab i < k) ∧
      ∀ i j, flab i = flab j ↔ (fineEnd ⊥ (hier.take t)).r (e.symm i) (e.symm j) := by
  have hlen := h.length_eq
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · refine ⟨fun i => i, Or.inl ⟨rfl, rfl⟩, fun i => i.2, fun i j => ?_⟩
    change (i : ℕ) = j ↔ e.symm i = e.symm j
    rw [e.symm.injective.eq_iff, Fin.val_inj]
  · have h1 : t - 1 < vs.length := by omega
    obtain ⟨pv, ⟨lab, rfl, hlt, hR⟩, hv⟩ := List.forall₂_iff_get.1 h |>.2 (t - 1) h1 (by omega)
    refine ⟨lab, Or.inr ⟨h0, h1, _, _, _, hv⟩, hlt, fun i j => ?_⟩
    rw [fineEnd_take ht h0, hR]

/-- The partition of a labeling. -/
theorem partitionValC_ker (e : Ω ≃ Fin k) {lab : Fin k → ℕ} (hlt : ∀ i, lab i < k) :
    PartitionValC e (encFun lab) (Setoid.ker fun v => lab (e v)) :=
  ⟨lab, rfl, hlt, fun i j => by simp⟩

/-- **The exposed hierarchy value.** -/
theorem hierOut_val {e : Ω ≃ Fin k} {vs : List Val} {hier : List (Interval Ω)}
    (h : List.Forall₂ (IntervalValC e) vs hier) {t : ℕ} (ht : t < hier.length) {pv : Val}
    (hpv : PartitionValC e pv hier[t].part) {lab2 : Fin k → ℕ} (hlab : ∀ i, lab2 i < k)
    {nf d c₁ : ℕ} (hc : c₁ * d = nf) (hd : 0 < d) :
    HierValC e (.list (hierOut vs t (encFun lab2) nf d pv hier[t].cap hier[t].origin))
      ((if c₁ = 1 then hier.take t else hier.take t ++
          [⟨Setoid.ker fun v => lab2 (e v), c₁, min hier[t].cap c₁, hier[t].origin⟩]) ++
        ⟨hier[t].part, d, min hier[t].cap d, hier[t].origin⟩ :: hier.drop (t + 1)) := by
  have hdiv : nf / d = c₁ := by rw [← hc, Nat.mul_div_cancel _ hd]
  refine ⟨_, rfl, ?_⟩
  have htake := List.forall₂_take t h
  have hdrop := List.forall₂_drop (t + 1) h
  have htop : IntervalValC e (topVal pv d hier[t].cap hier[t].origin)
      ⟨hier[t].part, d, min hier[t].cap d, hier[t].origin⟩ := ⟨pv, hpv, rfl⟩
  have hmid : IntervalValC e (.list [encFun lab2, .nat (nf / d),
      .nat (min hier[t].cap (nf / d)), .nat hier[t].origin])
      ⟨Setoid.ker fun v => lab2 (e v), c₁, min hier[t].cap c₁, hier[t].origin⟩ :=
    ⟨_, partitionValC_ker e hlab, by rw [hdiv]⟩
  by_cases h1 : c₁ = 1
  · simp only [hierOut, insList, hdiv, h1, ↓reduceIte, one_ne_zero]
    have := List.rel_append (List.rel_append htake (.cons htop .nil)) hdrop
    simpa only [List.append_assoc, List.singleton_append] using this
  · simp only [hierOut, insList, hdiv, h1, ↓reduceIte, List.append_assoc, List.cons_append,
      List.nil_append]
    rw [hdiv] at hmid
    have := List.rel_append (List.rel_append htake (.cons hmid (.cons htop .nil))) hdrop
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using this

/-! ### The program -/

/-- The list `[a, b, c, d, e]`. -/
def exMk5 (a b c d e : Expr) : Expr := .snoc (mk4 a b c d) e

theorem Det.exMk5 {P : Program} {env : List Val} {a b c d e : Expr} {va vb vc vd ve : Val}
    {ca cb cc cd ce : ℕ} (ha : Det P env a va ca) (hb : Det P env b vb cb)
    (hc : Det P env c vc cc) (hd : Det P env d vd cd) (he : Det P env e ve ce) :
    Det P env (exMk5 a b c d e) (.list [va, vb, vc, vd, ve])
      (ca + cb + cc + cd + ce + 5 * (Val.list [va, vb, vc, vd, ve]).wt + 10) := by
  have h1 := wt_list_mono (show [va, vb, vc, vd] <+: [va, vb, vc, vd, ve] from ⟨[ve], rfl⟩)
  exact (Det.snoc (Det.mk4 ha hb hc hd) he).mono (by
    simp only [List.cons_append, List.nil_append]; omega)

/-- **The exposure step** on the canonical state value `[k, gv, dv, xv, yv, hv, rv, …]`. It
returns `[gv', rep, hv', lab, t]`: the action on the new blocks, the representatives of the
block relation on the points, the exposed hierarchy, the block numbers of the points (`d` off
the domain) and the index of the top interval in the exposed hierarchy. The steps after the first part
(`prepE`, at `bprep`): call `MinimalBlocks` on the action on the base classes, pull its labels
back to the points through the class numbers (`gather`, with `0` for the points off the
domain), number the new classes, and build the action and the hierarchy. -/
def exposeE (bprep jmb bgather bcls bact bhier : ℕ) : Expr :=
  .letE (.call bprep (.var 0))
  (.letE (.prim jmb (.get (.var 1) (.nat 3)))
  (.letE (.call bgather (mk2 (.snoc (.var 2) (.nat 0)) (.get (.get (.var 1) (.nat 2)) (.nat 0))))
  (.letE (.call bcls (mk2 (.var 3) (arg 2)))
  (exMk5 (.call bact (mk2 (mk2 (.get (.var 4) (.nat 0)) (.get (.var 4) (.nat 1))) (arg 1)))
    (.get (.var 4) (.nat 2))
    (.call bhier (exMk5 (arg 5) (.get (.var 1) (.nat 0)) (.var 3)
      (.length (.get (.get (.var 1) (.nat 1)) (.nat 1))) (.length (.get (.var 4) (.nat 1)))))
    (.get (.var 4) (.nat 0))
    (.arith .sub (.arith .add (.get (.var 1) (.nat 0)) (.nat 1))
      (.arith .eq (.arith .div (.length (.get (.get (.var 1) (.nat 1)) (.nat 1)))
        (.length (.get (.var 4) (.nat 1)))) (.nat 1)))))))

/-- The cost constant of the exposure step, besides the call of `MinimalBlocks`. -/
def exposeK : ℕ := 10 ^ 22

theorem mb_bound_le (p : Prim) {v : Val} {W : ℕ} (h : v.wt ≤ W) :
    p.bound v ≤ p.c * (W + 2) ^ p.k :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := v.size_le_wt; omega) _)

/-- The output of the exposure step for a primitive quotient `Q`. -/
def ExposeOut (e : Ω ≃ Fin k) {S : State Ω C} (Q : PrimitiveQuotient S) (w : Val) : Prop :=
  ∃ gv rep hv, w = .list [gv, rep, hv, encFun (Q.labFin e), .nat Q.pre.length] ∧
    GroupVal Q.d gv Q.ρ.range ∧
    ReprVal k rep (fun i j => Q.labFin e i = Q.labFin e j) ∧
    normNumbered e Q rep ∧ HierValC e hv (Q.pre ++ Q.top :: Q.post)

/-- **The exposure step.** On a transitive state with the hierarchy invariant, whose points are
not one class, the program returns the action, the block relation and the hierarchy of a
primitive quotient that kills the columns and keeps the levels. Its cost is polynomial in the
weight `W` of the input, plus the bound of one call of `MinimalBlocks` on an input of weight
at most `100 (W + 1)⁴`. -/
theorem expose_spec (hmb : GI.Cited.MinimalBlocks) {P : Program}
    {f bprep jmb bgather bcls bact bhier bsplit brange bbase : ℕ}
    (hf : P.funs[f]? = some (exposeE bprep jmb bgather bcls bact bhier))
    (hprep : P.funs[bprep]? = some (prepE bsplit brange bcls bbase bact))
    (hsplit : P.HasAt bsplit (hsplitFuns bsplit bcls)) (hrange : P.HasAt brange (rangeFuns brange))
    (hcls : P.HasAt bcls (clsFuns bcls)) (hbase : P.HasAt bbase (baseFuns bbase))
    (hact : P.HasAt bact (actFuns bact)) (hgather : P.HasAt bgather (gatherFuns bgather))
    (hhier : P.HasAt bhier (hierFuns bhier)) (hj : P.prims[jmb]? = some (minimalBlocksPrim hmb))
    [Finite Ω] {S : State Ω C} {e : Ω ≃ Fin k} (htr : S.Transitive) (hinv : S.HierInv)
    (h2 : ¬ UnivOn S.dom ⊥) {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e S.G)
    (hgsl : gs.length ≤ k ^ 2) {vs : List Val} (hH : HierValC e (.list vs) S.hier) {rv : Val}
    (hrv : OptVal (RowValC e) rv S.rows) (xv yv fv hh nN : Val) :
    FunAll P f (.list [.nat k, encGroup gs, encFun (indF e S.dom), xv, yv, .list vs, rv, fv, hh,
      nN]) (fun w c => ∃ Q : PrimitiveQuotient S, Q.KillsCols ∧ Q.KeepsLevels ∧ ExposeOut e Q w ∧
        c ≤ exposeK * ((Val.list [.nat k, encGroup gs, encFun (indF e S.dom), xv, yv, .list vs,
          rv, fv, hh, nN]).wt + 1) ^ 8 + (minimalBlocksPrim hmb).c *
          (100 * ((Val.list [.nat k, encGroup gs, encFun (indF e S.dom), xv, yv, .list vs, rv, fv,
            hh, nN]).wt + 1) ^ 4 + 2) ^ (minimalBlocksPrim hmb).k) := by
  have hF : List.Forall₂ (IntervalValC e) vs S.hier := by
    obtain ⟨vs', hvs', hF⟩ := hH
    rw [Val.list.inj hvs']; exact hF
  set dm := indF e S.dom with hdm
  set cs : List Val := [.nat k, encGroup gs, encFun dm, xv, yv, .list vs, rv, fv, hh, nN] with hcs
  set a : Val := .list cs with ha
  set W := a.wt with hW
  -- the split index and the fine end
  have hne : S.dom.Nonempty := by
    by_contra hc
    exact h2 fun v hv => (hc ⟨v, hv⟩).elim
  obtain ⟨ht, hJ, hbef⟩ := splitIdx_props htr hinv h2
  set t := splitIdx S.dom S.hier with htdef
  obtain ⟨flab, hfl, hflt, hfR⟩ := exists_flab hF ht
  have hfinv : ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom,
      (fineEnd ⊥ (S.hier.take t)).r (g v) (g w) ↔ (fineEnd ⊥ (S.hier.take t)).r v w := by
    have hch := hinv.chain
    rw [← List.take_append_drop t S.hier, chain_append] at hch
    exact Chain.fineEnd_inv hch.1 (bot_inv _ _)
  have hfpr : ¬ UnivOn S.dom (fineEnd ⊥ (S.hier.take t)) := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0, List.take_zero]; exact h2
    · rw [fineEnd_take ht h0]; exact hbef (t - 1) (by omega)
  -- the base partition
  obtain ⟨ocl, hrv', B, hblt, hB, hfB, hBinv, hBpr, hBcols⟩ :=
    base_props hinv hflt hfR hfinv hfpr hrv
  set blab := blabOf flab dm ocl with hblab
  have n1 := Cls.numbering e S.dom B blab hblt hB
  set num1 := Cls.numOf dm (Cls.keyOf blab dm) with hnum1
  set reps1 := Cls.repsOf dm (Cls.keyOf blab dm) with hreps1
  have hd1 : 0 < reps1.length := by
    obtain ⟨v, hv⟩ := hne; have := n1.lt v hv; omega
  have hd12 : 2 ≤ reps1.length := by
    have := (n1.univOn_iff hne).not.1 hBpr; omega
  obtain ⟨ρ1, hρ1, -⟩ := n1.exists_rho hd1 hBinv
  have hG1 : GroupVal reps1.length (actVal num1 reps1 gs) ρ1.range :=
    actVal_groupVal_of ρ1 (n1.toMap hd1) rfl (fun v hv => n1.toMap_val hd1 hv) hρ1
      (fun s hs => repsOf_rep (D := S.dom) (lab := blab) s hs) hgs
  have htr1 : ∀ i j : Fin reps1.length, ∃ g ∈ ρ1.range, g i = j := by
    intro i j
    obtain ⟨v, hv, rfl⟩ := n1.toMap_onto hd1 i
    obtain ⟨w, hw, rfl⟩ := n1.toMap_onto hd1 j
    obtain ⟨g, hg, rfl⟩ := htr v hv w hw
    exact ⟨ρ1 ⟨g, hg⟩, ⟨_, rfl⟩, hρ1 ⟨g, hg⟩ v hv⟩
  -- the first part of the program
  have hkW : k < W := by
    have h1 := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (dm i))
    have h3 : (encFun dm).wt = (Val.list ((List.finRange k).map fun i => Val.nat (dm i))).wt :=
      rfl
    have h4 : (encFun dm).wt < W := wt_le_wt_list (by simp [hcs])
    simp only [List.length_map, List.length_finRange] at h1
    omega
  have sp := exPrep_spec hprep hsplit hrange hcls hbase hact hne hgsl ⟨vs, rfl, hF⟩ hfl hflt hrv'
    hblt xv yv fv hh nN
  have s1 := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) sp
  refine FunAll.intro hf (EvalAll.letE s1 fun pv cp hp => ?_)
  obtain ⟨rfl, hcp⟩ := hp
  set pval := prepVal t flab dm ocl gs with hpval
  -- the call of `MinimalBlocks`
  have dact1 : Det P [a, pval] (.get (.var 1) (.nat 3)) (actVal num1 reps1 gs) _ :=
    Det.get' (Det.var' (P := P) (env := [a, pval]) (i := 1) rfl) (Det.nat 3) rfl
  refine EvalAll.letE (minimalBlocks_call hmb hj dact1 hG1 hd12 htr1) fun lv cl hl => ?_
  obtain ⟨⟨lab', rfl, hlab'lt, hmin⟩, hcl⟩ := hl
  -- the pull back
  set lab2 : Fin k → ℕ := fun i => padF lab' (num1 i) with hlab2def
  have hk : reps1.length ≤ k := Cls.repsOf_length_le _ _
  have hlab2 : ∀ i, lab2 i < k := fun i => by
    simp only [hlab2def, padF]; split_ifs
    · exact (hlab'lt _).trans_le hk
    · omega
  have h2' : ∀ v ∈ S.dom, lab2 (e v) = lab' (n1.toMap hd1 v) := fun v hv => by
    show padF lab' (num1 (e v)) = _
    unfold padF
    rw [dif_pos (n1.lt v hv)]
    exact congrArg lab' (Fin.ext (n1.toMap_val hd1 hv).symm)
  obtain ⟨Q, hQd, hQblk, hkc, hkl, c₁, hc₁, hpre, htop, hpost⟩ :=
    expose_quot htr hinv (pre := S.hier.take t) (J := S.hier[t]) (post := S.hier.drop (t + 1))
      (by rw [List.getElem_cons_drop, List.take_append_drop]) hJ hfB
      (fun c hc _ hfc => hBcols c hc hfc) n1 hd1 hρ1 hmin h2' hlab2
  -- the gather step
  have hdm1 : ∀ i, dm i ≤ 1 := fun i => by simp only [hdm, indF]; split_ifs <;> omega
  have dsn := Det.snoc (Det.var' (P := P) (env := [a, pval, encFun lab']) (i := 2)
    (v := .list ((List.finRange reps1.length).map fun j => Val.nat (lab' j))) rfl)
    (Det.nat (P := P) (env := [a, pval, encFun lab']) 0)
  have dcl1 : Det P [a, pval, encFun lab'] (.get (.var 1) (.nat 2)) (clsVal blab dm) _ :=
    Det.get' (Det.var' (P := P) (env := [a, pval, encFun lab']) (i := 1) rfl) (Det.nat 2) rfl
  have dnum1 := Det.get' dcl1 (Det.nat 0) (v := natList ((List.finRange k).map num1))
    (by show some (encFun num1) = some _; rw [GI.Lang.encFun_eq_natList])
  have hi : ∀ i ∈ (List.finRange k).map num1,
      i < (((List.finRange reps1.length).map fun j => Val.nat (lab' j)) ++ [Val.nat 0]).length := by
    intro i hi
    simp only [List.mem_map, List.mem_finRange, true_and] at hi
    obtain ⟨j, rfl⟩ := hi
    simp only [List.length_append, List.length_map, List.length_finRange, List.length_singleton]
    have : num1 j ≤ reps1.length := Cls.numOf_le_length _ _ j
    omega
  have dg := Det.call (Det.mk2 dsn dnum1) (gather_spec hgather hi)
  rw [gather_eq] at dg
  -- the numbering of the new classes
  set env4 : List Val := [a, pval, encFun lab', encFun lab2] with henv4
  have dcls2 := Det.call (Det.mk2 (Det.var' (P := P) (env := env4) (i := 3) rfl)
    (Det.arg' (vs := cs) (rest := env4.tail) (j := 2) rfl))
    (cls_spec hcls lab2 dm (X := W) (fun i => (hlab2 i).le.trans hkW.le) hdm1 hkW.le)
  -- the action on the new classes
  set env5 : List Val := [a, pval, encFun lab', encFun lab2, clsVal lab2 dm] with henv5
  set num2 := Cls.numOf dm (Cls.keyOf lab2 dm) with hnum2
  set reps2 := Cls.repsOf dm (Cls.keyOf lab2 dm) with hreps2
  have hnum2W : ∀ i, num2 i ≤ W := fun i => (numOf_le _ _ i).trans hkW.le
  have hreps2k : ∀ r ∈ reps2, r < k := fun r hr => by
    obtain ⟨h, -⟩ := (Cls.mem_repsOf dm _).1 hr; exact h
  have hlen2 : reps2.length ≤ W := (Cls.repsOf_length_le _ _).trans hkW.le
  have hgsW : gs.length ≤ W ^ 2 := hgsl.trans (Nat.pow_le_pow_left hkW.le 2)
  have d4 := Det.var' (P := P) (env := env5) (i := 4) (v := clsVal lab2 dm) rfl
  have dact2 := Det.call (Det.mk2 (Det.mk2 (Det.get' d4 (Det.nat 0) (v := encFun num2) rfl)
    (Det.get' d4 (Det.nat 1) (v := natList reps2) rfl))
    (Det.arg' (vs := cs) (rest := env5.tail) (j := 1) rfl))
    (act_spec hact num2 reps2 gs hnum2W hreps2k hlen2 hkW.le hgsW)
  have drep := Det.get' d4 (Det.nat 2) (v := encFun (Cls.repOf (Cls.keyOf lab2 dm))) rfl
  -- the exposed hierarchy
  have hvl : t < vs.length := by rw [hF.length_eq]; exact ht
  obtain ⟨pv, hpv, hvt⟩ := (List.forall₂_iff_get.1 hF).2 t hvl ht
  set repsf := Cls.repsOf dm (Cls.keyOf flab dm) with hrepsf
  have dvs := Det.arg' (P := P) (vs := cs) (rest := env5.tail) (j := 5) (v := .list vs) rfl
  have dt := Det.get' (Det.var' (P := P) (env := env5) (i := 1) (v := pval) rfl) (Det.nat 0)
    (v := .nat t) rfl
  have dlab2 := Det.var' (P := P) (env := env5) (i := 3) (v := encFun lab2) rfl
  have dnf := Det.length (Det.get' (Det.get' (Det.var' (P := P) (env := env5) (i := 1) (v := pval)
    rfl) (Det.nat 1) (v := clsVal flab dm) rfl) (Det.nat 1) (v := natList repsf) rfl)
  have dd2 := Det.length (Det.get' d4 (Det.nat 1) (v := natList reps2) rfl)
  rw [List.length_map] at dnf dd2
  have dh := Det.call (Det.exMk5 dvs dt dlab2 dnf dd2)
    (exHier_spec hhier hvl hvt (encFun lab2) repsf.length reps2.length)
  have dnum2 := Det.get' d4 (Det.nat 0) (v := encFun num2) rfl
  have didx := Det.arith' (op := .sub) (Det.arith' (op := .add) dt (Det.nat 1) (z := t + 1) rfl)
    (Det.arith' (op := .eq) (Det.arith' (op := .div) dnf dd2 (z := repsf.length / reps2.length) rfl)
      (Det.nat 1) (z := if repsf.length / reps2.length = 1 then 1 else 0) (by
        simp only [GI.Machine.BinOp.eval]))
    (z := t + 1 - (if repsf.length / reps2.length = 1 then 1 else 0)) rfl
  have nf0 := Cls.numbering e S.dom _ flab hflt hfR
  have hcc0 := nf0.classCount_eq
  have hlabQ : encFun num2 = encFun (Q.labFin e) := by
    have : num2 = Q.labFin e := funext fun i => (labFin_eq_numOf Q hQd hQblk i).symm
    rw [this]
  have hidxQ : t + 1 - (if repsf.length / reps2.length = 1 then 1 else 0) = Q.pre.length := by
    have hd0 : 0 < reps2.length := by rw [← hQd]; have := Q.two_le; omega
    have hdiv : repsf.length / reps2.length = c₁ := by
      rw [← hcc0, ← hc₁, hQd, Nat.mul_div_cancel _ hd0]
    rw [hdiv, hpre]
    split_ifs with h1 <;> simp [List.length_take, Nat.min_eq_left ht.le]
  rw [hlabQ] at dnum2
  rw [hidxQ] at didx
  have dall := Det.letE dg (Det.letE dcls2 (Det.exMk5 dact2 drep dh dnum2 didx))
  have hwall := Det.wt_lt dall
  have hhw := FunDet.wt_lt (exHier_spec hhier hvl hvt (encFun lab2) repsf.length reps2.length)
  refine EvalAll.mono dall fun w c hw => ?_
  obtain ⟨rfl, hc⟩ := hw
  refine ⟨Q, hkc, hkl, ⟨_, _, _, rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact actVal_groupVal Q hQd.symm hQblk (fun s hs => repsOf_rep (D := S.dom) (lab := lab2) s hs)
      hgs
  · exact reprVal_labFin Q (fun i _ => hlab2 i) hQd hQblk
  · exact normNumbered_of Q (fun i _ => hlab2 i) hQd hQblk
  · have nf := Cls.numbering e S.dom _ flab hflt hfR
    have hcc := nf.classCount_eq
    rw [hpre, htop, hpost, ← hQd]
    exact hierOut_val hF ht hpv hlab2 (by rw [hc₁, hcc]) (by have := Q.two_le; omega)
  · have epv : (Val.list [Val.nat t, clsVal flab dm, clsVal (blabOf flab dm ocl) dm,
        actVal (Cls.numOf dm (Cls.keyOf (blabOf flab dm ocl) dm))
          (Cls.repsOf dm (Cls.keyOf (blabOf flab dm ocl) dm)) gs]) = pval := rfl
    have ea : (Val.list [Val.nat k, encGroup gs, encFun (indF e S.dom), xv, yv, Val.list vs, rv,
      fv, hh, nN]).wt = W := rfl
    have ecs : (Val.list cs).wt = W := rfl
    have elab2 : (encFun fun i => padF lab' (num1 i)) = encFun lab2 := rfl
    rw [epv, elab2, ecs] at hc hwall
    rw [epv] at hcl
    rw [ea] at hcp
    clear dall dg dcls2 dact2 drep dh dnf dd2 dvs dt dlab2 d4 dnum1 dcl1 dsn dact1 s1 sp
    -- the weights of the pieces
    have hY1 : 1 ≤ W + 1 := by omega
    have hkY : k + 1 ≤ W + 1 := by omega
    have hk2 : (k + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left hkY 2
    have hWY2 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hY24 : (W + 1) ^ 2 ≤ (W + 1) ^ 4 := Nat.pow_le_pow_right hY1 (by norm_num)
    have hY46 : (W + 1) ^ 4 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right hY1 (by norm_num)
    have hY68 : (W + 1) ^ 6 ≤ (W + 1) ^ 8 := Nat.pow_le_pow_right hY1 (by norm_num)
    have wvs : (Val.list vs).wt < W := wt_le_wt_list (by simp [hcs])
    have wg : (encGroup gs).wt < W := wt_le_wt_list (by simp [hcs])
    have hvsl : vs.length < W := by have := length_lt_wt_list vs; omega
    have wt_ : (Val.nat t).wt ≤ 2 * W + 2 := by have := wt_nat_le t; omega
    have hr1 : reps1.length ≤ W := hk.trans hkW.le
    have hrf : repsf.length ≤ W := (Cls.repsOf_length_le _ _).trans hkW.le
    have wnf : (Val.nat repsf.length).wt ≤ 2 * W + 2 := by
      have := wt_nat_le repsf.length; omega
    have wn2 : (Val.nat reps2.length).wt ≤ 2 * W + 2 := by
      have := wt_nat_le reps2.length; omega
    have wcf : (clsVal flab dm).wt ≤ 40 * (W + 1) ^ 2 := (wt_clsVal_le flab dm).trans (by omega)
    have wcb : (clsVal blab dm).wt ≤ 40 * (W + 1) ^ 2 := (wt_clsVal_le blab dm).trans (by omega)
    have wc2 : (clsVal lab2 dm).wt ≤ 40 * (W + 1) ^ 2 := (wt_clsVal_le lab2 dm).trans (by omega)
    have wa1 : (actVal num1 reps1 gs).wt ≤ 100 * (W + 1) ^ 4 :=
      wt_actVal_le num1 reps1 gs (fun i => (numOf_le _ _ i).trans hkW.le) hr1 hkW.le hgsW
    have wa2 : (actVal num2 reps2 gs).wt ≤ 100 * (W + 1) ^ 4 :=
      wt_actVal_le num2 reps2 gs hnum2W hlen2 hkW.le hgsW
    have wpv : pval.wt ≤ 400 * (W + 1) ^ 4 :=
      calc pval.wt = (Val.list [.nat t, clsVal flab dm, clsVal blab dm,
            actVal num1 reps1 gs]).wt := rfl
        _ ≤ _ := wt_list4_le _ _ _ _
        _ ≤ _ := by omega
    have wl' : (Val.list ((List.finRange reps1.length).map fun j => Val.nat (lab' j))).wt ≤
        5 * (W + 1) ^ 2 :=
      wt_encFun_le' lab' (B := W) (fun i => ((hlab'lt i).le.trans hr1)) hr1
    have wl's := wt_list_snoc_le ((List.finRange reps1.length).map fun j => Val.nat (lab' j))
      (.nat 0)
    have w0 := wt_nat_le 0
    have wn1 : (natList ((List.finRange k).map num1)).wt ≤ 5 * (W + 1) ^ 2 := by
      rw [← GI.Lang.encFun_eq_natList]
      exact wt_encFun_le' num1 (B := W) (fun i => (numOf_le _ _ i).trans hkW.le) hkW.le
    have wl2 : (encFun lab2).wt ≤ 5 * (W + 1) ^ 2 :=
      wt_encFun_le' lab2 (B := W) (fun i => (hlab2 i).le.trans hkW.le) hkW.le
    have wdm : (encFun dm).wt < W := wt_le_wt_list (by simp [hcs])
    have wnum2 : (encFun num2).wt ≤ 5 * (W + 1) ^ 2 := wt_encFun_le' num2 (B := W) hnum2W hkW.le
    have wreps2 : (natList reps2).wt ≤ 5 * (W + 1) ^ 2 :=
      wt_natList_le_sq (fun x hx => (hreps2k x hx).le.trans hkW.le) hlen2
    have wrepsf : (natList repsf).wt ≤ 5 * (W + 1) ^ 2 :=
      wt_natList_le_sq (fun x hx => by
        obtain ⟨h, -⟩ := (Cls.mem_repsOf dm _).1 hx; omega) hrf
    have wrep2 : (encFun (Cls.repOf (Cls.keyOf lab2 dm))).wt ≤ 5 * (W + 1) ^ 2 :=
      wt_encFun_le' _ (B := W) (fun i => (Cls.repOf_lt _ i).le.trans hkW.le) hkW.le
    have m1 := wt_list2_le (Val.list (((List.finRange reps1.length).map fun j => Val.nat (lab' j)) ++
      [Val.nat 0])) (natList ((List.finRange k).map num1))
    have m2 := wt_list2_le (encFun lab2) (encFun dm)
    have m3 := wt_list2_le (encFun num2) (natList reps2)
    have m4 := wt_list2_le (Val.list [encFun num2, natList reps2]) (encGroup gs)
    have m5 : (Val.list [Val.list vs, Val.nat t, encFun lab2, Val.nat repsf.length,
        Val.nat reps2.length]).wt ≤ 2 * ((Val.list vs).wt + (Val.nat t).wt + (encFun lab2).wt +
          (Val.nat repsf.length).wt + (Val.nat reps2.length).wt) + 10 := by
      have := wt_list_le [Val.list vs, Val.nat t, encFun lab2, Val.nat repsf.length,
        Val.nat reps2.length]
      simp at this; omega
    have m6 := wt_list3_le (actVal num2 reps2 gs) (encFun (Cls.repOf (Cls.keyOf lab2 dm)))
      (Val.list (hierOut vs t (encFun lab2) repsf.length reps2.length pv
        (S.hier.get ⟨t, ht⟩).cap (S.hier.get ⟨t, ht⟩).origin))
    -- the gather and hierarchy costs
    have hgc : gatherK * ((Val.list [Val.list ((List.finRange reps1.length).map
        (fun j => Val.nat (lab' j)) ++ [Val.nat 0]), natList ((List.finRange k).map num1)]).wt + 1)
        ^ 3 ≤ 10 ^ 10 * (W + 1) ^ 6 := by
      have : (Val.list [Val.list ((List.finRange reps1.length).map
          (fun j => Val.nat (lab' j)) ++ [Val.nat 0]), natList ((List.finRange k).map num1)]).wt + 1
          ≤ 40 * (W + 1) ^ 2 := by omega
      calc _ ≤ gatherK * (40 * (W + 1) ^ 2) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 3)
        _ = 64000 * 10 ^ 5 * (W + 1) ^ 6 := by simp only [gatherK]; ring
        _ ≤ 10 ^ 10 * (W + 1) ^ 6 := Nat.mul_le_mul_right _ (by norm_num)
    have hhc : exHierK * ((Val.list [Val.list vs, Val.nat t, encFun lab2, Val.nat repsf.length,
        Val.nat reps2.length]).wt + 1) ^ 2 ≤ 10 ^ 12 * (W + 1) ^ 4 := by
      have : (Val.list [Val.list vs, Val.nat t, encFun lab2, Val.nat repsf.length,
          Val.nat reps2.length]).wt + 1 ≤ 30 * (W + 1) ^ 2 := by omega
      calc _ ≤ exHierK * (30 * (W + 1) ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 2)
        _ = 900 * 10 ^ 7 * (W + 1) ^ 4 := by simp only [exHierK]; ring
        _ ≤ 10 ^ 12 * (W + 1) ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
    have hmbb : (minimalBlocksPrim hmb).bound (actVal num1 reps1 gs) ≤
        (minimalBlocksPrim hmb).c * (100 * (W + 1) ^ 4 + 2) ^ (minimalBlocksPrim hmb).k :=
      mb_bound_le _ wa1
    have h7 : 7 * (reps1.length + 1) ^ 2 ≤ 7 * (W + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have wlabQ : (encFun (Q.labFin e)).wt ≤ 5 * (W + 1) ^ 2 := hlabQ ▸ wnum2
    have htl : t < vs.length := hvl
    have hpl : Q.pre.length ≤ t + 1 := by rw [← hidxQ]; omega
    have wpl := wt_nat_le Q.pre.length
    have wt1 := wt_nat_le (t + 1)
    have wn1' := wt_nat_le 1
    have hdv : repsf.length / reps2.length ≤ repsf.length := Nat.div_le_self _ _
    have wdv := wt_nat_le (repsf.length / reps2.length)
    have hif : (if repsf.length / reps2.length = 1 then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have wif := wt_nat_le (if repsf.length / reps2.length = 1 then 1 else 0)
    have m7 : (Val.list [actVal num2 reps2 gs, encFun (Cls.repOf (Cls.keyOf lab2 dm)),
        Val.list (hierOut vs t (encFun lab2) repsf.length reps2.length pv
          (S.hier.get ⟨t, ht⟩).cap (S.hier.get ⟨t, ht⟩).origin),
        encFun (Q.labFin e), Val.nat Q.pre.length]).wt ≤
        2 * ((actVal num2 reps2 gs).wt + (encFun (Cls.repOf (Cls.keyOf lab2 dm))).wt +
          (Val.list (hierOut vs t (encFun lab2) repsf.length reps2.length pv
            (S.hier.get ⟨t, ht⟩).cap (S.hier.get ⟨t, ht⟩).origin)).wt +
          (encFun (Q.labFin e)).wt + (Val.nat Q.pre.length).wt) + 9 := by
      have := wt_list_le [actVal num2 reps2 gs, encFun (Cls.repOf (Cls.keyOf lab2 dm)),
        Val.list (hierOut vs t (encFun lab2) repsf.length reps2.length pv
          (S.hier.get ⟨t, ht⟩).cap (S.hier.get ⟨t, ht⟩).origin),
        encFun (Q.labFin e), Val.nat Q.pre.length]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at this
      omega
    clear_value pval lab2 num1 reps1 num2 reps2 repsf blab dm cs a t
    simp only [exposeK, prepK, clsK] at *
    omega

/-- **The weight of the enumeration input.** For an output `[gv, rep, hv, lv, iv]` of the
exposure step, the input `[a, rep, hv, B]` of the enumeration (`enum_spec`) weighs at most a
constant times the weights of `a`, of the output and of `B`. The output weighs less than the cost
of the exposure step (`FunAll.wt_lt`), which `expose_spec` bounds by a polynomial in the weight
of `a` plus the bound of one `MinimalBlocks` call. -/
theorem enumInput_wt_le (a gv rep hv lv iv : Val) (B : ℕ) :
    (Val.list [a, rep, hv, .nat B]).wt ≤
      2 * (a.wt + 2 * (Val.list [gv, rep, hv, lv, iv]).wt + (Val.nat B).wt) + 8 := by
  have h1 := wt_list4_le a rep hv (.nat B)
  have h2 : rep.wt < (Val.list [gv, rep, hv, lv, iv]).wt := wt_le_wt_list (by simp)
  have h3 : hv.wt < (Val.list [gv, rep, hv, lv, iv]).wt := wt_le_wt_list (by simp)
  omega

end GI.Impl
