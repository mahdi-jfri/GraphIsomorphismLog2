module

public import Workspace.Impl.VsPStep4Sz
public import Workspace.Proved.VsPS1Math
public import Workspace.Impl.VsHContain

@[expose] public section

/-!
# The output, and the last stage program

* `vsPGIn`: the hand-off value (the input of the hard case).
* `VsPOut`: grow (`[0, ⟨as'⟩]` with `VsPGrowOut`) or hand-off (`[1, gIn]` with `VsMHard`).
* `vsPS4E`, `vsPS4_spec`: on `[ctx, input, pc, [x₂, r]]`, the descent from `x₂`, the final stage,
  and either grow with `x₀` (isotropic) or the hand-off.
-/

open Matrix

set_option backward.isDefEq.respectTransparency false

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {I : VecStabInst}

/-- The hand-off value. -/
noncomputable def vsPGIn (s : VsQSt I) (as : List (Perm (Fin I.n))) (Lb : List (List (List ℕ)))
    (ccs tcs ys : List (Perm (Fin I.n))) (r : ℕ) : Val :=
  .list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, vsWFrVal I.p I.d s.ws' (vsQCs s),
    encGroup as, encGroup ccs, .list (tcs.map encPerm), .list (ys.map encPerm), .nat r, vsFMatsVal Lb]

/-- **The output of step 4.** -/
def VsPOut [Fact I.p.Prime] {s : VsQSt I} (hs : VsQStOK s) (as : List (Perm (Fin I.n)))
    (Lb : List (List (List ℕ))) (ccs tcs : List (Perm (Fin I.n))) (w : Val) : Prop :=
  (∃ as' : List (Perm (Fin I.n)), w = .list [.nat 0, encGroup as'] ∧ VsPGrowOut hs as as') ∨
  (∃ (ys : List (Perm (Fin I.n))) (r : ℕ), w = .list [.nat 1, vsPGIn s as Lb ccs tcs ys r] ∧
    (∀ y ∈ ys, y ∈ gens s.hs) ∧ (∀ y ∈ ys, y ∈ gens ccs) ∧ ys.length ≤ vsQD s ^ 2 ∧ r.Prime ∧ r ≤ I.n ∧
    VsMHard (vsPBar hs (gens s.hs)) (vsPBar hs (gens as))
      (vsPBar hs (gens ys) ⊔ vsMScal (vsPBar hs (gens as))) r)

/-- A list of eleven values. -/
def vsPMk11 (a b c d e f g h i j k : Expr) : Expr :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc (mk4 a b c d) e) f) g) h) i) j) k

theorem Det.vsPMk11 {P : Program} {env : List Val} {a b c d e f g h i j k : Expr}
    {va vb vc vd ve vf vg vh vi vj vk : Val} {ca cb cc cd ce cf cg ch ci cj ck : ℕ}
    (ha : Det P env a va ca) (hb : Det P env b vb cb) (hc : Det P env c vc cc)
    (hd : Det P env d vd cd) (he : Det P env e ve ce) (hf : Det P env f vf cf)
    (hg : Det P env g vg cg) (hh : Det P env h vh ch) (hi : Det P env i vi ci)
    (hj : Det P env j vj cj) (hk : Det P env k vk ck) :
    Det P env (vsPMk11 a b c d e f g h i j k) (.list [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk])
      (ca + cb + cc + cd + ce + cf + cg + ch + ci + cj + ck +
        11 * (Val.list [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk]).wt + 40) := by
  have h0 := wt_list_mono (show [va, vb, vc, vd] <+: [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk] from ⟨[ve, vf, vg, vh, vi, vj, vk], rfl⟩)
  have h1 := wt_list_mono (show [va, vb, vc, vd, ve] <+: [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk] from ⟨[vf, vg, vh, vi, vj, vk], rfl⟩)
  have h2 := wt_list_mono (show [va, vb, vc, vd, ve, vf] <+: [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk] from ⟨[vg, vh, vi, vj, vk], rfl⟩)
  have h3 := wt_list_mono (show [va, vb, vc, vd, ve, vf, vg] <+: [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk] from ⟨[vh, vi, vj, vk], rfl⟩)
  have h4 := wt_list_mono (show [va, vb, vc, vd, ve, vf, vg, vh] <+: [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk] from ⟨[vi, vj, vk], rfl⟩)
  have h5 := wt_list_mono (show [va, vb, vc, vd, ve, vf, vg, vh, vi] <+: [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk] from ⟨[vj, vk], rfl⟩)
  have h6 := wt_list_mono (show [va, vb, vc, vd, ve, vf, vg, vh, vi, vj] <+: [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk] from ⟨[vk], rfl⟩)
  exact (Det.snoc (Det.snoc (Det.snoc (Det.snoc (Det.snoc (Det.snoc (Det.snoc
    (Det.mk4 ha hb hc hd) he) hf) hg) hh) hi) hj) hk).mono
    (by simp only [List.cons_append, List.nil_append]; omega)

/-! ### The last stage -/

/-- The cap `D² + 1`, from the context. -/
def vsPCapE : Expr := .arith .add (.length (.get (arg 0) (.nat 4))) (.nat 1)

/-- On `[ctx, input, pc, [x₂, r]]`: descent, final stage, and grow or hand-off. -/
def vsPS4E (desc fin grow : ℕ) : Expr :=
  .letE (vsPMk5 (arg 2) vsPCapE (.get (.get (arg 0) (.nat 5)) (.nat 1)) vsPCapE (.get (arg 3) (.nat 1)))
    (.letE (.call desc (mk3 (.var 1) (.get (arg 3) (.nat 0)) vsPCapE))
      (.letE (.call fin (mk2 (.var 1) (.var 2)))
        (.ite (.get (.var 3) (.nat 0))
          (mk2 (.nat 0) (.call grow (mk3 (arg 0) (.get (arg 1) (.nat 1)) (mk1 (.var 2)))))
          (mk2 (.nat 1) (vsPMk11 (.get (.get (.get (arg 1) (.nat 0)) (.nat 0)) (.nat 0))
            (.get (.get (.get (arg 1) (.nat 0)) (.nat 0)) (.nat 1))
            (.get (.get (.get (arg 1) (.nat 0)) (.nat 0)) (.nat 2))
            (.get (.get (.get (arg 1) (.nat 0)) (.nat 0)) (.nat 3))
            (.get (.get (arg 1) (.nat 0)) (.nat 1))
            (.get (arg 1) (.nat 1)) (.get (arg 1) (.nat 3)) (.get (arg 1) (.nat 4))
            (.get (.get (.var 3) (.nat 1)) (.nat 1)) (.get (arg 3) (.nat 1)) (.get (arg 1) (.nat 2)))))))

/-- The function indices of the last stage. -/
structure VsPS4X where
  (d : VsPDX) (e : VsPEX) (desc it st fnd pr fin mkg ab fo no fi nc grow ap ncp : ℕ)

/-- The layout of the last stage. -/
structure VsPS4Lay (P : Program) (hn : NormalClosure) (x : VsPS4X) : Prop where
  d : VsPDLay P x.d
  e : VsPELay P x.e
  hdesc : P.funs[x.desc]? = some (vsPDescE x.it)
  hit : P.HasAt x.it (iterFuns x.it x.st)
  hst : P.funs[x.st]? = some (vsPDsStepE x.d.dim x.e.en x.fnd)
  hfnd : P.HasAt x.fnd (findFuns x.fnd x.pr)
  hpr : P.funs[x.pr]? = some (vsPDPredE x.d.nt x.d.dim)
  hfin : P.funs[x.fin]? = some (vsPFinE x.d.dim x.mkg x.ab)
  hmkg : P.HasAt x.mkg (mkGroupFuns x.mkg)
  hab : P.funs[x.ab]? = some (vsPAbE x.fo)
  hfo : P.HasAt x.fo (findFuns x.fo x.no)
  hno : P.funs[x.no]? = some (vsPNoE x.fi)
  hfi : P.HasAt x.fi (findFuns x.fi x.nc)
  hnc : P.funs[x.nc]? = some (vsPNcE x.d.o.comp x.d.o.loc x.d.o.eqb)
  hgrow : P.funs[x.grow]? = some (vsPGrowE x.ap x.mkg x.ncp)
  hap : P.HasAt x.ap (appendFuns x.ap)
  hncp : P.prims[x.ncp]? = some (normalClosurePrim hn)

/-- A round stays in a set closed under the listed words. -/
theorem vsPDsStepF_mem {ws' cs : List (List ℕ)} {rows : List VsRow} {Zp : List (List (List ℕ))}
    {gs : List (Perm (Fin I.n))} {cap : ℕ} {hs1 : List (Perm (Fin I.n))} {F r : ℕ}
    {Y : Set (Perm (Fin I.n))} {y : Perm (Fin I.n)} (hy : y ∈ Y)
    (hE : ∀ z ∈ vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y), z ∈ Y) :
    vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y ∈ Y := by
  set E := vsPEnum r (vsPDim I ws' cs Zp gs cap hs1 F r y)
  set qq := vsPDQ I ws' cs rows Zp gs cap hs1 F r (vsPDim I ws' cs Zp gs cap hs1 F r y).length
  have hval : vsPDsStepF I ws' cs rows Zp gs cap hs1 F r y =
      if h : E.findIdx qq < E.length then E[E.findIdx qq] else y := rfl
  rw [hval]
  split_ifs with hj
  · exact hE _ (List.getElem_mem hj)
  · exact hy

/-- The cost of the last stage. -/
noncomputable def vsPS4Cost (Cφ : ℕ) (hn : NormalClosure) (S : ℕ) : ℕ :=
  vsPDescCost Cφ (vsPN S) (vsPW6 S) + vsPFinCost Cφ (vsPN S) (vsPW6 S) +
    vsPGrowCost hn (vsPN S) (vsPW6 S) + 1000 * vsPW6 S

set_option maxHeartbeats 8000000 in
/-- **The last stage.** -/
theorem vsPS4_spec [Fact I.p.Prime] {P : Program} {hn : NormalClosure} {f : ℕ} {x : VsPS4X}
    (hf : P.funs[f]? = some (vsPS4E x.desc x.fin x.grow)) (L : VsPS4Lay P hn x) {Cφ : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.d.o.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ccs tcs : List (Perm (Fin I.n))}
    (hH : VsPHyp hs as Lb ccs) {gs : List (Perm (Fin I.n))} (hgl : gs.length ≤ I.n ^ 2)
    {r : ℕ} [hr : Fact r.Prime] (hrn : r ≤ I.n) {c0 : Perm (Fin I.n)}
    (h4 : VsPS4 hs as gs r c0) {x2 : Perm (Fin I.n)}
    (hx2 : x2 ∈ vsPYs hs (vsPBar hs (gens gs)))
    (hx2b : vsPInLB I s.ws' (vsQCs s) (vsPRows I.p Lb) x2 = false)
    (hx2C : x2 ∈ gens ccs) :
    FunAll P f (.list [vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs, vsPIn s as Lb ccs tcs,
        vsPPc I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs gs (vsPZp I s.ws' (vsQCs s) c0 r),
        .list [encPerm x2, .nat r]])
      (fun w c => VsPOut hs as Lb ccs tcs w ∧ c ≤ vsPS4Cost Cφ hn S + 10 ^ 4 * (vsPIn s as Lb ccs tcs).wt) := by
  haveI : NeZero r := ⟨hr.out.ne_zero⟩
  have hr2 := hr.out.two_le
  have hS1 := hS.one_le
  set D := vsQD s with hDdef
  set cap := D * D + 1
  set N := vsPN S
  set W := vsPW6 S
  set rows := vsPRows I.p Lb
  set Zp := vsPZp I s.ws' (vsQCs s) c0 r
  set C := vsPCtx I s.ws' (vsQCs s) rows s.hs
  set A := vsPIn s as Lb ccs tcs
  set pc := vsPPc I s.ws' (vsQCs s) rows s.hs gs Zp
  set o := Val.list [encPerm x2, .nat r]
  set step := vsPDsStepF I s.ws' (vsQCs s) rows Zp gs cap (1 :: s.hs) cap r
  have hD := vsQD_le hs
  have hLbW : ∀ M ∈ Lb, VsWSq I.p D M := fun M hM =>
    ⟨fun a ha => (hH.hLb M hM).rows a ha, (hH.hLb M hM).len⟩
  have hDDN : D * D + 1 ≤ N := by
    have : D * D ≤ S * S := Nat.mul_le_mul (by have := hS.d; omega) (by have := hS.d; omega)
    simp only [N, vsPN]; nlinarith
  have hLbN : Lb.length ≤ N := le_trans hH.hLbl (Nat.le_of_succ_le hDDN)
  have OD := vsPOD_of hS hs hLbW hLbN h4.hgs hgl hr.out.pos hrn (c0 := c0)
  have hD2 : D ^ 2 = D * D := sq D
  have hcapD : D ^ 2 < cap := by omega
  have hDN : D ^ 2 ≤ N := by omega
  have hY := h4.desc_ok hcapD hDN cap
  -- the descended element
  set x0 := step^[cap] x2
  have hmemY : ∀ k, step^[k] x2 ∈ vsPYs hs (vsPBar hs (gens gs)) := by
    intro k
    induction k with
    | zero => exact hx2
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact vsPDsStepF_mem ih (hY _ ih).2
  have hx0 : x0 ∈ vsPYs hs (vsPBar hs (gens gs)) := hmemY cap
  have hx0b : vsPInLB I s.ws' (vsQCs s) rows x0 = false :=
    vsPDsStepF_iter_ib _ _ _ _ _ _ _ _ _ hx2b cap
  have hdim2 : (vsPDim I s.ws' (vsQCs s) Zp gs cap (1 :: s.hs) cap r x2).length < cap := by
    have h1 : r ^ (vsPDim I s.ws' (vsQCs s) Zp gs cap (1 :: s.hs) cap r x2).length ≤ vsQD s ^ 2 :=
      h4.pow_dim_le hcapD (vsPYs_iff.1 hx2).1 (vsPYs_iff.1 hx2).2 cap
    have h2 : (vsPDim I s.ws' (vsQCs s) Zp gs cap (1 :: s.hs) cap r x2).length <
        r ^ (vsPDim I s.ws' (vsQCs s) Zp gs cap (1 :: s.hs) cap r x2).length :=
      Nat.lt_pow_self (by omega)
    have h3 : vsQD s ^ 2 = vsQD s * vsQD s := sq _
    have h4' : cap = vsQD s * vsQD s + 1 := rfl
    omega
  have hfix : step x0 = x0 :=
    vsP_iter_fix step (fun y => (vsPDim I s.ws' (vsQCs s) Zp gs cap (1 :: s.hs) cap r y).length)
      (fun y hy => vsPDsStepF_lt _ _ _ _ _ _ _ _ _ y hy) x2 cap hdim2
  have hx0S : vsPRho hs x0 ∉ vsMScal (vsPBar hs (gens as)) := fun hS' => by
    rw [← hH.ib x0 (vsPYs_iff.1 hx0).1] at hS'
    rw [hS'] at hx0b; exact Bool.noConfusion hx0b
  set B := vsPDim I s.ws' (vsQCs s) Zp gs cap (1 :: s.hs) cap r x0
  have hx0g := (vsPYs_iff.1 hx0).1
  have hfit0 := h4.orb_fit hcapD hx0g (vsPYs_iff.1 hx0).2 cap
  have hconjC : ∀ g ∈ 1 :: s.hs, ∀ z ∈ gens ccs, g * z * g⁻¹ ∈ gens ccs := by
    intro g hg z hz
    apply hH.hccn g _ z hz
    rcases List.mem_cons.1 hg with rfl | hg
    · exact one_mem _
    · exact Subgroup.subset_closure hg
  have hdimC : ∀ y ∈ gens ccs,
      ∀ b ∈ vsPDim I s.ws' (vsQCs s) Zp gs cap (1 :: s.hs) cap r y, b ∈ gens ccs :=
    fun y hy => vsH_dim_mem _ _ _ _ _ _ (gens ccs : Set _) hconjC _ _ y hy
  have hstepC : ∀ y ∈ gens ccs, step y ∈ gens ccs := by
    intro y hy
    apply vsPDsStepF_mem hy
    intro z hz
    exact ((Subgroup.closure_le _).2 (hdimC y hy)) (vsPEnum_mem _ z hz)
  have hx0C : x0 ∈ gens ccs := by
    have hi : ∀ k, step^[k] x2 ∈ gens ccs := by
      intro k
      induction k with
      | zero => exact hx2C
      | succ k ih => simpa only [Function.iterate_succ_apply'] using hstepC _ ih
    exact hi cap
  have hBC := hdimC x0 hx0C
  have hB := h4.basis_mem hcapD hx0 (F := cap)
  -- the program
  set Cl := [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ ((vsQCs s).length * (vsQCs s).length)), encGroup s.hs, .nat I.n]
  set vs := [C, A, pc, o]
  set Qv := vsPQ I s.ws' (vsQCs s) rows s.hs gs Zp cap (1 :: s.hs) cap r
  have hcapv : ∀ rest : List Val, Det P (Val.list vs :: rest) vsPCapE (.nat cap)
      (5 * (Val.list vs).wt + 100) := by
    intro rest
    have a0 : Det P (Val.list vs :: rest) (arg 0) (.list Cl) _ :=
      Det.arg' (P := P) (vs := vs) (rest := rest) (j := 0) rfl
    have g4 := Det.get' a0 (Det.nat 4) (show Cl[4]? = some (natList (vsWZ ((vsQCs s).length *
      (vsQCs s).length))) from rfl)
    have hl := Det.length g4
    have hz := Det.arith' (op := .add) hl (Det.nat 1) rfl
    have e : Val.nat (BinOp.eval .add ((vsWZ ((vsQCs s).length * (vsQCs s).length)).map Val.nat).length 1)
        = .nat cap := by
      simp only [BinOp.eval, List.length_map, vsWZ, List.length_replicate]; rfl
    rw [e] at hz
    refine hz.mono ?_
    have w1 : (natList (vsWZ ((vsQCs s).length * (vsQCs s).length))).wt < (Val.list Cl).wt :=
      wt_le_wt_list (by simp [Cl])
    have w2 : (Val.list Cl).wt < (Val.list vs).wt :=
      wt_le_wt_list (List.mem_cons_self (a := Val.list Cl) (l := vs.tail))
    have w3 := length_lt_wt_list ((vsWZ ((vsQCs s).length * (vsQCs s).length)).map Val.nat)
    have e2 : (natList (vsWZ ((vsQCs s).length * (vsQCs s).length))).wt =
      (Val.list ((vsWZ ((vsQCs s).length * (vsQCs s).length)).map Val.nat)).wt := rfl
    simp only [BinOp.eval]
    omega
  have a0 : Det P [Val.list vs] (arg 0) (.list Cl) _ := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have a3 : Det P [Val.list vs] (arg 3) (.list [encPerm x2, .nat r]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 3) rfl
  have g5 : Det P [Val.list vs] (.get (arg 0) (.nat 5))
      (.list [.nat I.n, .list ((1 :: s.hs).map encPerm)]) _ := Det.get' a0 (Det.nat 5) rfl
  have ghs := Det.get' g5 (Det.nat 1) (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][1]? =
    some (.list ((1 :: s.hs).map encPerm)) from rfl)
  have gr := Det.get' a3 (Det.nat 1) (show [encPerm x2, Val.nat r][1]? = some (.nat r) from rfl)
  have dQ := Det.vsPMk5 a2 (hcapv []) ghs (hcapv []) gr
  have eQ : Val.list [pc, .nat cap, .list ((1 :: s.hs).map encPerm), .nat cap, .nat r] = Qv := rfl
  rw [eQ] at dQ
  refine FunAll.intro hf (EvalAll.letE dQ fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- the descent
  have b3 : Det P [Val.list vs, Qv] (arg 3) (.list [encPerm x2, .nat r]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [Qv]) (j := 3) rfl
  have bx := Det.get' b3 (Det.nat 0) (show [encPerm x2, Val.nat r][0]? = some (encPerm x2) from rfl)
  have dX := Det.call (Det.mk3 (Det.var' (P := P) (env := [Val.list vs, Qv]) (i := 1) rfl) bx
    (hcapv [Qv])) (vsPDesc_spec L.hdesc L.hit L.hst L.d L.e L.hfnd L.hpr hphi OD hY hx2
      (k := cap) (by omega))
  refine EvalAll.letE dX fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  -- the final stage
  have dF := Det.call (Det.mk2 (Det.var' (P := P) (env := [Val.list vs, Qv, encPerm x0]) (i := 1) rfl)
    (Det.var' (P := P) (env := [Val.list vs, Qv, encPerm x0]) (i := 2) rfl))
    (vsPFin_spec L.hfin L.d L.hmkg L.hab L.hfo L.hno L.hfi L.hnc hphi OD (hs.prob.le hx0g) hfit0 hgl)
  refine EvalAll.letE dF fun v3 c3 h3 => ?_
  obtain ⟨rfl, hc3⟩ := h3
  set Fv := Val.list [boolVal (vsPIso I s.ws' (vsQCs s) B), encGroup B]
  set E3 := [Val.list vs, Qv, encPerm x0, Fv]
  have dT : Det P E3 (.get (.var 3) (.nat 0)) (boolVal (vsPIso I s.ws' (vsQCs s) B)) _ :=
    Det.get' (Det.var' (P := P) (env := E3) (i := 3) rfl) (Det.nat 0) rfl
  refine EvalAll.ite dT (fun vc cc h => ⟨_, h.1⟩) fun xb cc hcc => ?_
  obtain ⟨hxb, hcc⟩ := hcc
  -- the parts of the input
  set St := Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]
  set LC := Val.list [St, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat D, vsFMatsVal (vsQMs s)]
  set Al := [LC, encGroup as, vsFMatsVal Lb, encGroup ccs, Val.list (tcs.map encPerm)]
  have c1 : Det P E3 (arg 1) (.list Al) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [Qv, encPerm x0, Fv]) (j := 1) rfl
  have c3 : Det P E3 (arg 3) (.list [encPerm x2, .nat r]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := [Qv, encPerm x0, Fv]) (j := 3) rfl
  -- weights
  have wvs := wt_list_le vs
  simp only [vs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wvs
  have wC : C.wt ≤ W := OD.H.cw
  have wpc : pc.wt ≤ W := OD.hpc
  have wQv : Qv.wt ≤ W := OD.hQ
  have wo := wt_list2_le (encPerm x2) (.nat r)
  have eo : o.wt = (Val.list [encPerm x2, .nat r]).wt := rfl
  have wx2 : (encPerm x2).wt ≤ 4 * (I.n + 1) ^ 2 := wt_encPerm_le x2
  have wx0' : (encPerm x0).wt ≤ 4 * (I.n + 1) ^ 2 := wt_encPerm_le x0
  have wrr := wt_nat_le r
  have hBn : B.length ≤ I.n ^ 2 := by
    have := vsPBasis_length_le (kf := vsPKf s c0 r gs) (r := r) (k := gs.length)
      (O := vsPOrbit (vsPKf s c0 r gs) cap (1 :: s.hs) cap x0)
      (fun p hp => ⟨((h4.orb_inv hcapD hx0g (vsPYs_iff.1 hx0).2 cap).1 p hp).1, hfit0 p hp⟩)
    exact this.trans hgl
  have wEB : (encGroup B).wt ≤ 320 * (I.n + 1) ^ 6 := wt_encGroup_le_sq hBn
  have wb := wt_boolVal_le (vsPIso I s.ws' (vsQCs s) B)
  have wFv := wt_list2_le (boolVal (vsPIso I s.ws' (vsQCs s) B)) (encGroup B)
  have eFv : Fv.wt = (Val.list [boolVal (vsPIso I s.ws' (vsQCs s) B), encGroup B]).wt := rfl
  have hnS : I.n + 1 ≤ S := hS.n
  have hn6 : (I.n + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left hnS 6
  have hn2' : (I.n + 1) ^ 2 ≤ S ^ 6 := (Nat.pow_le_pow_left hnS 2).trans (hS.pow_le (by omega))
  have hrS : r ≤ S ^ 6 := by
    have : S ≤ S ^ 6 := by simpa using hS.pow_le (show 1 ≤ 6 by omega)
    omega
  have hWS : W = 10 ^ 9 * S ^ 6 := rfl
  have evs : (Val.list vs).wt = (Val.list [C, A, pc, o]).wt := rfl
  have wHC : (encGroup s.hs).wt < C.wt := wt_le_wt_list (by simp [C, vsPCtx])
  have wHn : (Val.list [Val.nat I.n, Val.list (List.map encPerm (1 :: s.hs))]).wt < C.wt := wHC
  have wHp : (Val.list (List.map encPerm (1 :: s.hs))).wt <
      (Val.list [Val.nat I.n, Val.list (List.map encPerm (1 :: s.hs))]).wt := wt_le_wt_list (by simp)
  have wx0e : (encPerm (step^[cap] x2)).wt ≤ 4 * (I.n + 1) ^ 2 := wt_encPerm_le _
  have wx0f := wt_encPerm_le ((vsPDsStepF I s.ws' (vsQCs s) (vsPRows I.p Lb) (vsPZp I s.ws' (vsQCs s) c0 r)
    gs (vsQD s * vsQD s + 1) (1 :: s.hs) (vsQD s * vsQD s + 1) r)^[cap] x2)
  have wLC : LC.wt < A.wt := wt_le_wt_list (List.mem_cons_self (a := LC) (l := Al.tail))
  have wSt : St.wt < LC.wt := wt_le_wt_list (by simp [LC])
  have wG : (vsQGam I).wt < St.wt := wt_le_wt_list (by simp [St])
  have wHs : (encGroup s.hs).wt < St.wt := wt_le_wt_list (by simp [St])
  have wW' : (vsWVs s.ws').wt < St.wt := wt_le_wt_list (by simp [St])
  have wW : (vsWVs s.ws).wt < St.wt := wt_le_wt_list (by simp [St])
  have wFr : (vsWFrVal I.p I.d s.ws' (vsQCs s)).wt < LC.wt := wt_le_wt_list (by simp [LC])
  have wAs : (encGroup as).wt < A.wt := wt_le_wt_list (by simp [A, vsPIn])
  have wCc : (encGroup ccs).wt < A.wt := wt_le_wt_list (by simp [A, vsPIn])
  have wTc : (Val.list (tcs.map encPerm)).wt < A.wt := wt_le_wt_list (by simp [A, vsPIn])
  have wLb : (vsFMatsVal Lb).wt < A.wt := wt_le_wt_list (by simp [A, vsPIn])
  have wYs : (Val.list ((1 :: B).map encPerm)).wt < (encGroup B).wt := wt_le_wt_list (by simp [encGroup, encPerms])
  set YS := Val.list ((1 :: B).map encPerm) with hYS
  have wGI := wt_list_le [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
    vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs, .list (tcs.map encPerm),
    YS, .nat r, vsFMatsVal Lb]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wGI
  have eGI : (vsPGIn s as Lb ccs tcs (1 :: B) r).wt = (Val.list [vsQGam I, encGroup s.hs,
    vsWVs s.ws', vsWVs s.ws, vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs,
    .list (tcs.map encPerm), YS, .nat r, vsFMatsVal Lb]).wt := rfl
  have eYS : (Val.list (List.map encPerm (1 :: B))).wt = YS.wt := rfl
  have wGI2 := wt_list2_le (Val.nat 1) (vsPGIn s as Lb ccs tcs (1 :: B) r)
  have w1 := wt_nat_le 1
  have wq3 := wt_list3_le Qv (encPerm x2) (.nat cap)
  have wq2 := wt_list2_le Qv (encPerm x0)
  have wcap := wt_nat_le cap
  have hcapS : cap ≤ 4 * S ^ 6 := by
    have : N ≤ 4 * S ^ 6 := by
      simp only [N, vsPN]; have := hS.pow_le (show 2 ≤ 6 by omega); omega
    omega
  cases hiso : vsPIso I s.ws' (vsQCs s) B
  · -- the hand-off
    have hx : xb = 0 := by rw [hiso] at hxb; simpa using hxb
    subst hx
    rw [if_pos rfl]
    have cLC : Det P E3 (.get (arg 1) (.nat 0)) LC _ := Det.get' c1 (Det.nat 0) rfl
    have cSt : Det P E3 (.get (.get (arg 1) (.nat 0)) (.nat 0)) St _ := Det.get' cLC (Det.nat 0) rfl
    have k0 := Det.get' cSt (Det.nat 0) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
      natList s.x, natList s.y][0]? = some (vsQGam I) from rfl)
    have k1 := Det.get' cSt (Det.nat 1) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
      natList s.x, natList s.y][1]? = some (encGroup s.hs) from rfl)
    have k2 := Det.get' cSt (Det.nat 2) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
      natList s.x, natList s.y][2]? = some (vsWVs s.ws') from rfl)
    have k3 := Det.get' cSt (Det.nat 3) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
      natList s.x, natList s.y][3]? = some (vsWVs s.ws) from rfl)
    have k4 := Det.get' cLC (Det.nat 1) (show [St, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat D,
      vsFMatsVal (vsQMs s)][1]? = some (vsWFrVal I.p I.d s.ws' (vsQCs s)) from rfl)
    have k5 := Det.get' c1 (Det.nat 1) (show Al[1]? = some (encGroup as) from rfl)
    have k6 := Det.get' c1 (Det.nat 3) (show Al[3]? = some (encGroup ccs) from rfl)
    have k7 := Det.get' c1 (Det.nat 4) (show Al[4]? = some (Val.list (tcs.map encPerm)) from rfl)
    have kF : Det P E3 (.get (.var 3) (.nat 1)) (encGroup B) _ :=
      Det.get' (Det.var' (P := P) (env := E3) (i := 3) rfl) (Det.nat 1) rfl
    have k8 : Det P E3 (.get (.get (.var 3) (.nat 1)) (.nat 1)) (.list ((1 :: B).map encPerm)) _ :=
      Det.get' kF (Det.nat 1) rfl
    have k9 := Det.get' c3 (Det.nat 1) (show [encPerm x2, Val.nat r][1]? = some (.nat r) from rfl)
    have k10 := Det.get' c1 (Det.nat 2) (show Al[2]? = some (vsFMatsVal Lb) from rfl)
    have dG := Det.mk2 (Det.nat (P := P) (env := E3) 1)
      (Det.vsPMk11 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10)
    have eG : Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
        vsWFrVal I.p I.d s.ws' (vsQCs s), encGroup as, encGroup ccs, .list (tcs.map encPerm),
        .list ((1 :: B).map encPerm), .nat r, vsFMatsVal Lb] = vsPGIn s as Lb ccs tcs (1 :: B) r := rfl
    rw [eG] at dG
    refine dG.post fun cb hcb => ⟨Or.inr ⟨1 :: B, r, rfl, fun y hy => ?_, (by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact one_mem _
      · exact hBC y hy), ?_, hr.out, hrn, ?_⟩, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact one_mem _
      · exact (hB y hy).1
    · have h1 : r ^ B.length ≤ vsQD s ^ 2 :=
        h4.pow_dim_le hcapD hx0g (vsPYs_iff.1 hx0).2 cap
      have h2 : B.length < r ^ B.length := Nat.lt_pow_self (by omega)
      simp only [List.length_cons]; omega
    · have hfix' : vsPDsStepF I s.ws' (vsQCs s) (vsPRows I.p Lb) (vsPZp I s.ws' (vsQCs s) c0 r) gs cap
          (1 :: s.hs) cap r x0 = x0 := hfix
      exact h4.hard hH.hsolv hH.abNormal hH.ib hcapD (le_of_lt hcapD) hx0 hfix' hiso
    · unfold vsPS4Cost
      omega
  · -- grow with `x₀`
    have hx : xb = 1 := by rw [hiso] at hxb; simpa using hxb
    subst hx
    rw [if_neg one_ne_zero]
    have d0 : Det P E3 (arg 0) C _ := Det.arg' (P := P) (vs := vs) (rest := [Qv, encPerm x0, Fv]) (j := 0) rfl
    have g1 := Det.get' c1 (Det.nat 1) (show Al[1]? = some (encGroup as) from rfl)
    have gx : Det P E3 (mk1 (.var 2)) (.list ([x0].map encPerm)) _ :=
      Det.mk1 (Det.var' (P := P) (env := E3) (i := 2) rfl)
    have wAl : (Val.list Al).wt < (Val.list vs).wt :=
      wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self (a := Val.list Al) (l := vs.tail.tail)))
    have wC0 : C.wt < (Val.list vs).wt := wt_le_wt_list (List.mem_cons_self (a := C) (l := vs.tail))
    have was : (encGroup as).wt < (Val.list Al).wt := wt_le_wt_list (by simp [Al])
    have wx0 : (encPerm x0).wt ≤ 4 * (I.n + 1) ^ 2 := wt_encPerm_le x0
    have w1x := wt_list1_le (encPerm x0)
    have w3a := wt_list3_le C (encGroup as) (Val.list ([x0].map encPerm))
    have e1x : Val.list ([x0].map encPerm) = Val.list [encPerm x0] := rfl
    rw [e1x] at w3a
    have dA := (Det.mk3 d0 g1 gx).mono (c' := 20 * (Val.list vs).wt + 100 * (I.n + 1) ^ 2 + 100)
      (by rw [e1x]; omega)
    have hn2 := hH.two_le_n
    have hxl : [x0].length ≤ I.n ^ 2 := by
      show 1 ≤ I.n ^ 2; exact Nat.one_le_pow _ _ (by omega)
    refine (EvalAll.mk2_last (Det.nat (P := P) (env := E3) 0)
      (EvalAll.call_funAll dA (Q := fun w cb => ∃ as' : List (Perm (Fin I.n)), w = encGroup as' ∧
        VsPGrowOut hs as as' ∧ cb ≤ 20 * (Val.list vs).wt + 100 * (I.n + 1) ^ 2 + 100 + vsPGrowCost hn (vsPN S) (vsPW6 S) + w.wt + 1)
        fun v ca hv => ?_)).mono ?_
    · obtain ⟨rfl, hca⟩ := hv
      refine (vsPGrow_spec hn L.hgrow L.hap L.hmkg L.hncp OD.H hs.hsl hH.hal hxl).mono ?_
      rintro w cb ⟨as', rfl, hl, he, hcb⟩
      exact ⟨as', rfl, h4.iso_grow hH hcapD (le_of_lt hcapD) hx0 hx0S hiso hl he, by omega⟩
    · rintro w cw ⟨vb, cb, ⟨as', rfl, hout, hcb⟩, rfl, hcw⟩
      refine ⟨Or.inl ⟨as', rfl, hout⟩, ?_⟩
      have wa' : (encGroup as').wt ≤ 320 * (I.n + 1) ^ 6 := wt_encGroup_le_sq hout.len
      have w02 := wt_list2_le (Val.nat 0) (encGroup as')
      have w0 := wt_nat_le 0
      unfold vsPS4Cost
      omega

end GI.Impl
