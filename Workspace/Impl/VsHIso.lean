module

public import Workspace.Impl.VsHGood

@[expose] public section

/-!
# The greedy isotropic family

A pass over the cover list keeps `y` when `ȳ` is good, commutes with the kept elements (local
matrices), and is not in `⟨kept⟩ S`. The kept family satisfies `VsMIso` (`vsH_greedy_iso`).

* `vsHIStepE`, `vsHIStep_spec`: one step, on `[[ctx, r, Q, dv], kept, y]`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {I : VecStabInst}

/-- The test of the isotropic pass. -/
noncomputable def vsHIT (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow) (r Q : ℕ)
    (dv : Bool) (kept : List (Perm (Fin I.n))) (y : Perm (Fin I.n)) : Bool :=
  vsHGB I ws' cs rows r Q dv y && !(vsPQO I ws' cs kept (encPerm y)) &&
    !(vsHMemB I ws' cs rows r kept y)

/-- One step of the isotropic pass, on `[[ctx, r, Q, dv], kept, y]`. -/
def vsHIStepE (good no mem : ℕ) : Expr :=
  .ite (.call good (mk2 (arg 0) (arg 2)))
    (.ite (.call no (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (arg 2)))
      (arg 1)
      (.ite (.call mem (mk3 (mk2 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))) (arg 1) (arg 2)))
        (arg 1) (.snoc (arg 1) (arg 2))))
    (arg 1)

/-- The indices of the isotropic pass. -/
structure VsHIX where
  (m : VsHMX) (good no fi nc loc eq : ℕ)

/-- The layout of the isotropic pass. -/
structure VsHILay (P : Program) (x : VsHIX) : Prop where
  m : VsHMLay P x.m
  hgood : P.funs[x.good]? = some (vsHGoodE x.m.e.pow x.m.inl x.loc x.eq)
  hno : P.funs[x.no]? = some (vsPNoE x.fi)
  hfi : P.HasAt x.fi (findFuns x.fi x.nc)
  hnc : P.funs[x.nc]? = some (vsPNcE x.m.e.comp x.loc x.eq)
  hloc : P.funs[x.loc]? = some (vsPLocE x.m.phi (x.loc + 1))
  hwl : P.HasAt (x.loc + 1) (vsWLocFuns (x.loc + 1))
  heq : P.HasAt x.eq (vsPEqFuns x.eq)

/-- The cost of a step. -/
def vsHIStepCost (Cφ N W : ℕ) : ℕ :=
  vsHGoodCost Cφ N W + vsPNoCost Cφ N W + vsHMemCost Cφ N W + 10 ^ 3 * W + 10 ^ 4 * (N + 1) ^ 3

set_option maxHeartbeats 8000000 in
theorem vsHIStep_spec {P : Program} {f : ℕ} {x : VsHIX}
    (hf : P.funs[f]? = some (vsHIStepE x.good x.no x.m.mem)) (L : VsHILay P x) {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.m.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {r Q : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ N)
    (hQ : GI.Machine.len Q ≤ (N + 1) ^ 2) (dv : Bool)
    {K : List (Perm (Fin I.n))} (hK : r ^ K.length ≤ N) (hKl : K.length + 1 ≤ N)
    (hKs : ∀ g ∈ K, g ∈ gens I.gs) {y : Perm (Fin I.n)} (hy : y ∈ gens I.gs) :
    FunDet P f (.list [vsHGc (vsPCtx I ws' cs rows hs) r Q dv, .list (K.map encPerm), encPerm y])
      (.list ((if vsHIT I ws' cs rows r Q dv K y then K ++ [y] else K).map encPerm))
      (vsHIStepCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set c2 := [C, .nat r, .nat Q, boolVal dv]
  set vs := [Val.list c2, .list (K.map encPerm), encPerm y]
  have e0 : vsHGc C r Q dv = .list c2 := rfl
  rw [e0]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have a2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have g0 := Det.get' a0 (Det.nat 0) (show c2[0]? = some C from rfl)
  have g1 := Det.get' a0 (Det.nat 1) (show c2[1]? = some (.nat r) from rfl)
  have hn := H.n
  have wK := vsP_wt_perms H.n K (by omega)
  -- the three tests
  have dG := Det.call (Det.mk2 a0 a2) (vsHGood_spec (P := P) L.hgood L.m.e.hpow L.m.hinl L.hloc L.hwl
    L.heq hphi H hr hQ dv hy)
  have dN := Det.call (Det.mk2 (Det.mk2 g0 a1) a2) (vsPNo_spec L.hno L.hfi L.hnc L.m.e.hcomp L.hloc
    L.hwl L.heq hphi H hKs (by nlinarith) (by
      have : 20 * (N + 1) ^ 3 ≤ 400 * (N + 1) ^ 6 := by
        have : (N + 1) ^ 3 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      omega) hy)
  have dM := Det.call (Det.mk3 (Det.mk2 g0 g1) a1 a2) (vsHMem_spec L.m hphi H hr1 hr hK (by omega)
    hKs hy)
  have dS := Det.snoc a1 a2
  have dI3 := Det.vsHIte dM a1 dS
  have dI2 := Det.vsHIte dN a1 dI3
  have dI1 := Det.vsHIte dG dI2 a1
  refine FunDet.intro hf (dI1.post fun c hc => ⟨?_, ?_⟩)
  · unfold vsHIT
    cases vsHGB I ws' cs rows r Q dv y <;> cases vsPQO I ws' cs K (encPerm y) <;>
      cases vsHMemB I ws' cs rows r K y <;> simp
  · have wC : C.wt ≤ W := H.cw
    have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have wQ : (Val.nat Q).wt ≤ (N + 1) ^ 2 + 2 := by rw [wt_nat']; omega
    have wr := wt_nat_le r
    have wy := wt_encPerm_le y
    have wdv := wt_boolVal_le dv
    have wKy := vsP_wt_perms H.n (K ++ [y]) (by simp; omega)
    have ec2 : (Val.list c2).wt = (Val.list [C, .nat r, .nat Q, boolVal dv]).wt := rfl
    have wc2 := wt_list_le [C, Val.nat r, Val.nat Q, boolVal dv]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at wc2
    have evs : (Val.list vs).wt = (Val.list [Val.list c2, .list (K.map encPerm), encPerm y]).wt := rfl
    have wvs := wt_list3_le (Val.list c2) (.list (K.map encPerm)) (encPerm y)
    have l1 := wt_list2_le (Val.list c2) (encPerm y)
    have l2 := wt_list2_le C (.list (K.map encPerm))
    have l3 := wt_list2_le (Val.list [C, .list (K.map encPerm)]) (encPerm y)
    have l4 := wt_list2_le C (.nat r)
    have l5 := wt_list3_le (Val.list [C, .nat r]) (.list (K.map encPerm)) (encPerm y)
    have b1 := wt_boolVal_le (vsHGB I ws' cs rows r Q dv y)
    have b2 := wt_boolVal_le (vsPQO I ws' cs K (encPerm y))
    have b3 := wt_boolVal_le (vsHMemB I ws' cs rows r K y)
    have eKy : (Val.list (K.map encPerm ++ [encPerm y])).wt = (Val.list ((K ++ [y]).map encPerm)).wt := by
      simp
    have i3 : (if (vsHMemB I ws' cs rows r K y).toNat = 0 then Val.list (K.map encPerm ++ [encPerm y])
        else Val.list (K.map encPerm)).wt ≤ 20 * (N + 1) ^ 3 := by split <;> omega
    have i2 : (if (vsPQO I ws' cs K (encPerm y)).toNat = 0 then
        (if (vsHMemB I ws' cs rows r K y).toNat = 0 then Val.list (K.map encPerm ++ [encPerm y])
          else Val.list (K.map encPerm)) else Val.list (K.map encPerm)).wt ≤ 20 * (N + 1) ^ 3 := by
      split <;> omega
    have i1 : (if (vsHGB I ws' cs rows r Q dv y).toNat = 0 then Val.list (K.map encPerm) else
        (if (vsPQO I ws' cs K (encPerm y)).toNat = 0 then
        (if (vsHMemB I ws' cs rows r K y).toNat = 0 then Val.list (K.map encPerm ++ [encPerm y])
          else Val.list (K.map encPerm)) else Val.list (K.map encPerm))).wt ≤ 20 * (N + 1) ^ 3 := by
      split <;> omega
    unfold vsHIStepCost
    omega

/-- The isotropic pass, on `[[ctx, r, Q, dv], E]`. -/
def vsHIsoE (fo : ℕ) : Expr := .call fo (mk3 (arg 0) (arg 1) .nil)

/-- The cost of the isotropic pass. -/
def vsHIsoCost (Cφ N W : ℕ) : ℕ :=
  (N + 1) * vsHIStepCost Cφ N W + 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3)

set_option maxHeartbeats 4000000 in
/-- **The isotropic pass.** The bound `r ^ |kept| ≤ N` along the pass is a hypothesis; it comes
from the independence of the kept elements (`vsH_pow_le_index`). -/
theorem vsHIso_prog {P : Program} {f fo st : ℕ} {x : VsHIX} (hf : P.funs[f]? = some (vsHIsoE fo))
    (hfo : P.HasAt fo (foldlFuns fo st)) (hst : P.funs[st]? = some (vsHIStepE x.good x.no x.m.mem))
    (L : VsHILay P x) {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.m.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {r Q : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ N)
    (hQ : GI.Machine.len Q ≤ (N + 1) ^ 2) (dv : Bool)
    {ys : List (Perm (Fin I.n))} (hyl : ys.length + 1 ≤ N) (hys : ∀ g ∈ ys, g ∈ gens I.gs)
    (hb : ∀ i ≤ ys.length, r ^ (vsHGreedy (vsHIT I ws' cs rows r Q dv) (ys.take i)).length ≤ N) :
    FunAll P f (.list [vsHGc (vsPCtx I ws' cs rows hs) r Q dv, .list (ys.map encPerm)])
      (fun w c => w = .list ((vsHGreedy (vsHIT I ws' cs rows r Q dv) ys).map encPerm) ∧
        c ≤ vsHIsoCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set t := vsHIT I ws' cs rows r Q dv
  set vs := [vsHGc C r Q dv, .list (ys.map encPerm)]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  obtain ⟨KA, hKA, dA⟩ : ∃ KA, KA = _ ∧ Det P [Val.list vs] (mk3 (arg 0) (arg 1) .nil)
      (.list [vsHGc C r Q dv, .list (ys.map encPerm), .list []]) KA :=
    ⟨_, rfl, Det.mk3 a0 a1 Det.nil⟩
  have hsub : ∀ i, ∀ g ∈ vsHGreedy t (ys.take i), g ∈ ys := fun i g hg =>
    List.mem_of_mem_take ((vsHGreedy_sublist t _).subset hg)
  have hlen : ∀ i, (vsHGreedy t (ys.take i)).length ≤ ys.length := fun i =>
    ((vsHGreedy_sublist t _).length_le).trans (List.length_take_le' _ _)
  have hF := foldl_spec hfo (c := vsHGc C r Q dv) (xs := ys.map encPerm) (acc0 := .list [])
    (Inv := fun i acc => acc = .list ((vsHGreedy t (ys.take i)).map encPerm))
    (M := 20 * (N + 1) ^ 3) (B := fun _ => vsHIStepCost Cφ N W)
    (by simp [vsHGreedy])
    (fun i acc _ h => by rw [h]; exact vsP_wt_perms H.n _ (by have := hlen i; omega))
    (fun i acc hi h => by
      rw [List.length_map] at hi
      subst h
      rw [List.getElem_map]
      refine FunAll.mono (vsHIStep_spec hst L hphi H hr1 hr hQ dv (hb i (by omega)) (by have := hlen i; omega)
        (fun g hg => hys g (hsub i g hg)) (hys _ (List.getElem_mem hi)))
        fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, vsHGreedy_take_succ t ys i hi])
  refine FunAll.intro hf (EvalAll.call_funAll dA fun v ca hv => ?_)
  obtain ⟨rfl, hca⟩ := hv
  refine hF.mono fun w c hw => ⟨?_, ?_⟩
  · rw [hw.1, List.length_map, List.take_length]
  · obtain ⟨hw1, hc⟩ := hw
    rw [List.length_map] at hc
    have esum : ∑ i ∈ Finset.range ys.length, (fun _ => vsHIStepCost Cφ N W) i =
        ys.length * vsHIStepCost Cφ N W := by simp
    rw [esum] at hc
    have hn := H.n
    have wC : C.wt ≤ W := H.cw
    have wY := vsP_wt_perms H.n ys (by omega)
    have wG := vsP_wt_perms H.n (vsHGreedy t ys) (by
      have := (vsHGreedy_sublist t ys).length_le; omega)
    have q13 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
    have wr := wt_nat_le r
    have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have wQ : (Val.nat Q).wt ≤ (N + 1) ^ 2 + 2 := by rw [wt_nat']; omega
    have wdv := wt_boolVal_le dv
    have w1 := wt_list_le [C, Val.nat r, Val.nat Q, boolVal dv]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at w1
    have e1 : (vsHGc C r Q dv).wt = (Val.list [C, Val.nat r, Val.nat Q, boolVal dv]).wt := rfl
    have w3 := wt_list3_le (vsHGc C r Q dv) (.list (ys.map encPerm)) (.list [])
    have w2 := wt_list2_le (vsHGc C r Q dv) (.list (ys.map encPerm))
    have evs : (Val.list vs).wt = (Val.list [vsHGc C r Q dv, .list (ys.map encPerm)]).wt := rfl
    have w0 : (Val.list []).wt = 4 := wt_list_nil
    have hww : w.wt ≤ 20 * (N + 1) ^ 3 := by rw [hw1, List.length_map, List.take_length]; exact wG
    have hs1 : ys.length * vsHIStepCost Cφ N W ≤ (N + 1) * vsHIStepCost Cφ N W :=
      Nat.mul_le_mul_right _ (by omega)
    set X := (Val.list [vsHGc C r Q dv, Val.list (List.map encPerm ys), Val.list []]).wt +
      ys.length + 20 * (N + 1) ^ 3 + 1
    have hX : X ≤ 5 * (W + 100 * (N + 1) ^ 3) := by simp only [X]; omega
    have lk : loopModK = 1000 := rfl
    have hs2 : loopModK * (ys.length + 1) * X ≤ 1000 * (N + 1) * (5 * (W + 100 * (N + 1) ^ 3)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) hX
    have e3 : 1000 * (N + 1) * (5 * (W + 100 * (N + 1) ^ 3)) =
        5 * 10 ^ 3 * (N + 1) * (W + 100 * (N + 1) ^ 3) := by ring
    have hW1 : 5 * 10 ^ 3 * (W + 100 * (N + 1) ^ 3) ≤ 5 * 10 ^ 3 * (N + 1) * (W + 100 * (N + 1) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have e4 : 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3) =
        2 * (5 * 10 ^ 3 * (N + 1) * (W + 100 * (N + 1) ^ 3)) := by ring
    unfold vsHIsoCost
    omega

/-! ### What the isotropic test means -/

section Meaning

variable {s : VsQSt I} [Fact I.p.Prime]

omit [Fact I.p.Prime] in
/-- Equal local matrices of `gh` and `hg` mean commuting local units. -/
theorem vsH_loc_comm_iff (hs : VsQStOK s) {g h : Perm (Fin I.n)} (hg : g ∈ gens s.hs)
    (hh : h ∈ gens s.hs) :
    vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g) ↔
      vsPRho hs g * vsPRho hs h = vsPRho hs h * vsPRho hs g := by
  rw [vsPLocL_eq_iff hs, ← vsQRho_ext hs (mul_mem hg hh) (mul_mem hh hg), ← vsPRho_of hs,
    ← vsPRho_of hs, vsPRho_mul hs hg hh, vsPRho_mul hs hh hg]

/-- **The test of the isotropic pass.** -/
theorem vsHIT_test (hs : VsQStOK s) {as : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs)
    {Lb : List (List (List ℕ))} (hLb : ∀ M ∈ Lb, VsFSq I.p (vsQD s) M)
    (hspan : vsFMatSpan I.p (vsQD s) Lb = Subalgebra.toSubmodule
      (vsFAlgOf I.p (vsQD s) (as.map (vsPLocL I s.ws' (vsQCs s)))))
    [Nontrivial (Fin (vsQD s) → ZMod I.p)]
    (hA : ∀ a ∈ vsPBar hs (gens as), ∀ b ∈ vsPBar hs (gens as), a * b = b * a)
    (hdom : vsTDom (vsTAlg (vsPBar hs (gens as)))) {r : ℕ} (hr : r.Prime)
    {Y : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ}
    (hQ : VsPQuotHyp Y (vsMScal (vsPBar hs (gens as))) r) :
    ∀ kept y, (∀ e ∈ kept, VsHIn hs Y e) → VsHIn hs Y y →
      VsHTest (vsPRho hs) (vsMScal (vsPBar hs (gens as))) (vsMGood (vsPBar hs (gens as)) r)
        (vsHIT I s.ws' (vsQCs s) (vsPRows I.p Lb) r (I.p ^ (vsPRows I.p Lb).length - 1)
          (decide (r ∣ I.p ^ (vsPRows I.p Lb).length - 1))) kept y := by
  intro kept y hk hy
  unfold VsHTest vsHIT
  rw [Bool.and_eq_true, Bool.and_eq_true, vsHGB_iff hs has hLb hspan hA hdom hr hy.1,
    Bool.not_eq_true', Bool.not_eq_true', vsPQO_enc, decide_eq_false_iff_not,
    ← Bool.not_eq_true,
    vsHMemB_iff hs has hLb hspan hr.pos (fun g hg => (hk g hg).1) (hQ.mono (vsHBar_le hs hk)) hy.1,
    vsPBar_gens hs fun g hg => (hk g hg).1]
  have hc : (¬ ∃ h ∈ kept, vsPLocL I s.ws' (vsQCs s) (y * h) ≠ vsPLocL I s.ws' (vsQCs s) (h * y)) ↔
      ∀ e ∈ kept, vsPRho hs y * vsPRho hs e = vsPRho hs e * vsPRho hs y := by
    push Not
    exact forall₂_congr fun e he => vsH_loc_comm_iff hs hy.1 (hk e he).1
  rw [hc, and_assoc]
  rfl

end Meaning

end GI.Impl
