import Workspace.Impl.VsHMem

/-!
# A basis of `Ȳ` modulo `S`

A pass over `ys` keeps `y` when `ȳ ∉ ⟨kept⟩ S` (`vsHMem`). The kept list is independent modulo
`S` and spans `Ȳ` with `S` (`vsHBas_spec` in `Proved/VsHBasisMath`).

* `vsHBStepE`, `vsHBStep_spec`: one step, on `[[ctx, r], kept, y]`.
* `vsHBasE`, `vsHBas_prog`: the pass, on `[[ctx, r], ys]`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The test of the basis pass: keep `y` when it is not in `⟨kept⟩ S`. -/
noncomputable def vsHBT (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow) (r : ℕ)
    (kept : List (Perm (Fin I.n))) (y : Perm (Fin I.n)) : Bool :=
  !vsHMemB I ws' cs rows r kept y

/-- One step of the basis pass, on `[[ctx, r], kept, y]`. -/
def vsHBStepE (mem : ℕ) : Expr :=
  .ite (.call mem (mk3 (arg 0) (arg 1) (arg 2))) (arg 1) (.snoc (arg 1) (arg 2))

/-- The cost of a step. -/
def vsHBStepCost (Cφ N W : ℕ) : ℕ := vsHMemCost Cφ N W + 100 * W + 1000 * (N + 1) ^ 3

set_option maxHeartbeats 4000000 in
theorem vsHBStep_spec {P : Program} {f : ℕ} {x : VsHMX} (hf : P.funs[f]? = some (vsHBStepE x.mem))
    (L : VsHMLay P x) {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ N)
    {K : List (Perm (Fin I.n))} (hK : r ^ K.length ≤ N) (hKl : K.length + 1 ≤ N)
    (hKs : ∀ g ∈ K, g ∈ gens I.gs) {y : Perm (Fin I.n)} (hy : y ∈ gens I.gs) :
    FunAll P f (.list [.list [vsPCtx I ws' cs rows hs, .nat r], .list (K.map encPerm), encPerm y])
      (fun w c => w = .list ((if vsHBT I ws' cs rows r K y then K ++ [y] else K).map encPerm) ∧
        c ≤ vsHBStepCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set vs := [Val.list [C, .nat r], .list (K.map encPerm), encPerm y]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have a2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  obtain ⟨KA, hKA, dA⟩ : ∃ KA, KA = _ ∧ Det P [Val.list vs] (mk3 (arg 0) (arg 1) (arg 2))
      (.list [Val.list [C, .nat r], .list (K.map encPerm), encPerm y]) KA := ⟨_, rfl, Det.mk3 a0 a1 a2⟩
  set B := vsHMemB I ws' cs rows r K y
  have dT : EvalAll P [Val.list vs] (.call x.mem (mk3 (arg 0) (arg 1) (arg 2)))
      (fun w c => w = boolVal B ∧ c ≤ KA + vsHMemCost Cφ N W + 4) := by
    refine EvalAll.call_funAll dA fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (vsHMem_spec L hphi H hr1 hr hK (by omega) hKs hy).mono fun w cb hw => ⟨hw.1, ?_⟩
    have := wt_boolVal_le B
    rw [← hw.1] at this
    omega
  refine FunAll.intro hf (EvalAll.ite dT (fun vc cc h => ⟨_, h.1⟩) fun xb cc hcc => ?_)
  obtain ⟨hxb, hcc⟩ := hcc
  have hx : xb = B.toNat := by injection hxb
  have hn := H.n
  have wC : C.wt ≤ W := H.cw
  have wK := vsP_wt_perms H.n K (by omega)
  have wKy := vsP_wt_perms H.n (K ++ [y]) (by simp; omega)
  have wy := wt_encPerm_le y
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q13 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
  have wr := wt_nat_le r
  have w1 := wt_list2_le C (.nat r)
  have w2 := wt_list3_le (.list [C, .nat r]) (.list (K.map encPerm)) (encPerm y)
  have evs : (Val.list vs).wt = (Val.list [.list [C, .nat r], .list (K.map encPerm), encPerm y]).wt := rfl
  have w3 := wt_list3_le (.list [C, .nat r]) (.list (K.map encPerm)) (encPerm y)
  have eKA := hKA
  rw [show (Val.list [Val.list [C, .nat r], .list (K.map encPerm), encPerm y]).wt = (Val.list vs).wt
    from rfl] at eKA
  cases hB : B with
  | false =>
    have h0 : xb = 0 := by rw [hx, hB]; rfl
    subst h0
    rw [if_pos rfl]
    refine EvalAll.mono (Det.snoc a1 a2) fun w cb hw => ⟨?_, ?_⟩
    · rw [hw.1, vsHBT, show vsHMemB I ws' cs rows r K y = false from hB]
      simp
    · have e : (Val.list (List.map encPerm K ++ [encPerm y])).wt = (Val.list ((K ++ [y]).map encPerm)).wt := by
        simp
      rw [hw.1]
      have := hw.2
      unfold vsHBStepCost
      omega
  | true =>
    have h1 : xb = 1 := by rw [hx, hB]; rfl
    subst h1
    rw [if_neg (by omega)]
    refine EvalAll.mono a1 fun w cb hw => ⟨?_, ?_⟩
    · rw [hw.1, vsHBT, show vsHMemB I ws' cs rows r K y = true from hB]
      simp
    · rw [hw.1]
      have := hw.2
      unfold vsHBStepCost
      omega

/-- The kept list is a sublist of the input. -/
theorem vsHGreedy_sublist {α : Type*} (t : List α → α → Bool) (L : List α) :
    (vsHGreedy t L).Sublist L := by
  have key : ∀ (L acc : List α), ∃ l', L.foldl (fun kept y => if t kept y then kept ++ [y] else kept) acc =
      acc ++ l' ∧ l'.Sublist L := by
    intro L
    induction L with
    | nil => intro acc; exact ⟨[], by simp, List.Sublist.slnil⟩
    | cons y L ih =>
      intro acc
      rw [List.foldl_cons]
      by_cases hy : t acc y = true
      · rw [if_pos hy]
        obtain ⟨l', e, hl⟩ := ih (acc ++ [y])
        exact ⟨y :: l', by rw [e]; simp, hl.cons_cons y⟩
      · rw [if_neg hy]
        obtain ⟨l', e, hl⟩ := ih acc
        exact ⟨l', e, hl.cons y⟩
  obtain ⟨l', e, hl⟩ := key L []
  unfold vsHGreedy
  rw [e, List.nil_append]
  exact hl

theorem vsHGreedy_take_succ {α : Type*} (t : List α → α → Bool) (L : List α) (i : ℕ)
    (hi : i < L.length) :
    vsHGreedy t (L.take (i + 1)) =
      if t (vsHGreedy t (L.take i)) L[i] then vsHGreedy t (L.take i) ++ [L[i]]
      else vsHGreedy t (L.take i) := by
  unfold vsHGreedy
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
  rfl

/-- The basis pass, on `[[ctx, r], ys]`. -/
def vsHBasE (fo : ℕ) : Expr := .call fo (mk3 (arg 0) (arg 1) .nil)

/-- The cost of the basis pass. -/
def vsHBasCost (Cφ N W : ℕ) : ℕ :=
  (N + 1) * vsHBStepCost Cφ N W + 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3)

set_option maxHeartbeats 4000000 in
/-- **The basis pass.** The bound `r ^ |kept| ≤ N` along the pass is a hypothesis; it comes from
the independence of the kept elements (`vsH_pow_le_index'`). -/
theorem vsHBas_prog {P : Program} {f fo st : ℕ} {x : VsHMX} (hf : P.funs[f]? = some (vsHBasE fo))
    (hfo : P.HasAt fo (foldlFuns fo st)) (hst : P.funs[st]? = some (vsHBStepE x.mem))
    (L : VsHMLay P x) {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ N)
    {ys : List (Perm (Fin I.n))} (hyl : ys.length + 1 ≤ N) (hys : ∀ g ∈ ys, g ∈ gens I.gs)
    (hb : ∀ i ≤ ys.length, r ^ (vsHGreedy (vsHBT I ws' cs rows r) (ys.take i)).length ≤ N) :
    FunAll P f (.list [.list [vsPCtx I ws' cs rows hs, .nat r], .list (ys.map encPerm)])
      (fun w c => w = .list ((vsHGreedy (vsHBT I ws' cs rows r) ys).map encPerm) ∧
        c ≤ vsHBasCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set t := vsHBT I ws' cs rows r
  set vs := [Val.list [C, .nat r], .list (ys.map encPerm)]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  obtain ⟨KA, hKA, dA⟩ : ∃ KA, KA = _ ∧ Det P [Val.list vs] (mk3 (arg 0) (arg 1) .nil)
      (.list [Val.list [C, .nat r], .list (ys.map encPerm), .list []]) KA :=
    ⟨_, rfl, Det.mk3 a0 a1 Det.nil⟩
  have hsub : ∀ i, ∀ g ∈ vsHGreedy t (ys.take i), g ∈ ys := fun i g hg =>
    List.mem_of_mem_take ((vsHGreedy_sublist t _).subset hg)
  have hlen : ∀ i, (vsHGreedy t (ys.take i)).length ≤ ys.length := fun i =>
    ((vsHGreedy_sublist t _).length_le).trans (List.length_take_le' _ _)
  have hF := foldl_spec hfo (c := .list [C, .nat r]) (xs := ys.map encPerm) (acc0 := .list [])
    (Inv := fun i acc => acc = .list ((vsHGreedy t (ys.take i)).map encPerm))
    (M := 20 * (N + 1) ^ 3) (B := fun _ => vsHBStepCost Cφ N W)
    (by simp [vsHGreedy])
    (fun i acc _ h => by rw [h]; exact vsP_wt_perms H.n _ (by have := hlen i; omega))
    (fun i acc hi h => by
      rw [List.length_map] at hi
      subst h
      rw [List.getElem_map]
      refine (vsHBStep_spec hst L hphi H hr1 hr (hb i (by omega)) (by have := hlen i; omega)
        (fun g hg => hys g (hsub i g hg)) (hys _ (List.getElem_mem hi))).mono
        fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, vsHGreedy_take_succ t ys i hi])
  refine FunAll.intro hf (EvalAll.call_funAll dA fun v ca hv => ?_)
  obtain ⟨rfl, hca⟩ := hv
  refine hF.mono fun w c hw => ⟨?_, ?_⟩
  · rw [hw.1, List.length_map, List.take_length]
  · obtain ⟨hw1, hc⟩ := hw
    rw [List.length_map] at hc
    have esum : ∑ i ∈ Finset.range ys.length, (fun _ => vsHBStepCost Cφ N W) i =
        ys.length * vsHBStepCost Cφ N W := by simp
    rw [esum] at hc
    have hn := H.n
    have wC : C.wt ≤ W := H.cw
    have wY := vsP_wt_perms H.n ys (by omega)
    have wG := vsP_wt_perms H.n (vsHGreedy t ys) (by
      have := (vsHGreedy_sublist t ys).length_le; omega)
    have q13 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
    have wr := wt_nat_le r
    have w1 := wt_list2_le C (.nat r)
    have w2 := wt_list2_le (.list [C, .nat r]) (.list (ys.map encPerm))
    have w3 := wt_list3_le (.list [C, .nat r]) (.list (ys.map encPerm)) (.list [])
    have evs : (Val.list vs).wt = (Val.list [.list [C, .nat r], .list (ys.map encPerm)]).wt := rfl
    have w0 : (Val.list []).wt = 4 := wt_list_nil
    have hww : w.wt ≤ 20 * (N + 1) ^ 3 := by rw [hw1, List.length_map, List.take_length]; exact wG
    have hs1 : ys.length * vsHBStepCost Cφ N W ≤ (N + 1) * vsHBStepCost Cφ N W :=
      Nat.mul_le_mul_right _ (by omega)
    set X := (Val.list [Val.list [C, Val.nat r], Val.list (List.map encPerm ys), Val.list []]).wt +
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
    unfold vsHBasCost
    omega

/-! ### What the basis pass computes -/

section Meaning

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

/-- The hard case gives the quotient hypotheses for `Y` over `S`. -/
theorem vsH_quotHyp {H A Y : Subgroup (Module.End (ZMod p) V)ˣ} {r : ℕ} (h : VsMHard H A Y r) :
    VsPQuotHyp Y (vsMScal A) r :=
  ⟨fun t ht y hy => (vsM_comm_scal (h.2.2.2.2.2.1 hy) ht).symm, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1⟩

/-- In the hard case `V` is not zero (`Y` is not abelian). -/
theorem vsH_nontrivial {H A Y : Subgroup (Module.End (ZMod p) V)ˣ} {r : ℕ} (h : VsMHard H A Y r) :
    Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  obtain ⟨x, -, y, -, hne⟩ := h.2.2.2.2.2.2.2.2.2
  apply hne
  ext v
  exact Subsingleton.elim _ _

/-- `|Y : S| ≤ dim² ` in the hard case, for `V = 𝔽_p^D`. -/
theorem vsH_index_le_D {D : ℕ} {H A Y : Subgroup (Module.End (ZMod p) (Fin D → ZMod p))ˣ} {r : ℕ}
    (h : VsMHard H A Y r) : (vsMScal A).relIndex Y ≤ D ^ 2 := by
  haveI := vsH_nontrivial h
  have := vsH_index_le h
  rwa [Module.finrank_fin_fun] at this

end Meaning

section Meaning2

variable {s : VsQSt I} [Fact I.p.Prime]

/-- The membership in `Ȳ` and `⟨hs⟩` of the elements the passes see. -/
def VsHIn (hs : VsQStOK s) (Y : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ)
    (g : Perm (Fin I.n)) : Prop :=
  g ∈ gens s.hs ∧ vsPRho hs g ∈ Y

theorem vsHBar_le (hs : VsQStOK s) {Y : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ}
    {K : List (Perm (Fin I.n))} (hK : ∀ g ∈ K, VsHIn hs Y g) : vsPBar hs (gens K) ≤ Y := by
  rw [vsPBar_gens hs fun g hg => (hK g hg).1]
  exact (Subgroup.closure_le _).2 fun _ ⟨g, hg, e⟩ => e ▸ (hK g hg).2

/-- **The test of the basis pass.** -/
theorem vsHBT_test (hs : VsQStOK s) {as : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs)
    {Lb : List (List (List ℕ))} (hLb : ∀ M ∈ Lb, VsFSq I.p (vsQD s) M)
    (hspan : vsFMatSpan I.p (vsQD s) Lb = Subalgebra.toSubmodule
      (vsFAlgOf I.p (vsQD s) (as.map (vsPLocL I s.ws' (vsQCs s)))))
    {r : ℕ} (hr : 0 < r) {Y : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ}
    (hQ : VsPQuotHyp Y (vsMScal (vsPBar hs (gens as))) r) :
    ∀ kept y, (∀ e ∈ kept, VsHIn hs Y e) → VsHIn hs Y y →
      VsHBTest (vsPRho hs) (vsMScal (vsPBar hs (gens as))) (vsHBT I s.ws' (vsQCs s) (vsPRows I.p Lb) r)
        kept y := by
  intro kept y hk hy
  unfold VsHBTest vsHBT
  rw [Bool.not_eq_true', ← Bool.not_eq_true,
    vsHMemB_iff hs has hLb hspan hr (fun g hg => (hk g hg).1) (hQ.mono (vsHBar_le hs hk)) hy.1,
    vsPBar_gens hs fun g hg => (hk g hg).1]

/-- The image of a list, as a set. -/
theorem vsH_image_list {α β : Type*} (f : α → β) (l : List α) :
    f '' {e | e ∈ l} = {a | a ∈ l.map f} := by
  ext a; simp

/-- **The output of the basis pass.** It is independent modulo `S`, spans `Ȳ` with `S`, and
each prefix has `r ^ |kept| ≤ D²`. -/
theorem vsHBas_out (hs : VsQStOK s) {as : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs)
    {Lb : List (List (List ℕ))} (hLb : ∀ M ∈ Lb, VsFSq I.p (vsQD s) M)
    (hspan : vsFMatSpan I.p (vsQD s) Lb = Subalgebra.toSubmodule
      (vsFAlgOf I.p (vsQD s) (as.map (vsPLocL I s.ws' (vsQCs s)))))
    {ys : List (Perm (Fin I.n))} (hys : ∀ y ∈ ys, y ∈ gens s.hs) {r : ℕ}
    (hY : VsMHard (vsPBar hs (gens s.hs)) (vsPBar hs (gens as))
      (vsPBar hs (gens ys) ⊔ vsMScal (vsPBar hs (gens as))) r) (L : List (Perm (Fin I.n)))
    (hL : ∀ y ∈ L, VsHIn hs (vsPBar hs (gens ys) ⊔ vsMScal (vsPBar hs (gens as))) y) :
    let B := vsHGreedy (vsHBT I s.ws' (vsQCs s) (vsPRows I.p Lb) r) L
    (∀ e ∈ B, e ∈ L) ∧
    (∀ (i : ℕ) (hi : i < B.length), vsPRho hs B[i] ∉
      Subgroup.closure (vsPRho hs '' {e | e ∈ B.take i}) ⊔ vsMScal (vsPBar hs (gens as))) ∧
    Subgroup.closure (vsPRho hs '' {e | e ∈ L}) ⊔ vsMScal (vsPBar hs (gens as)) =
      Subgroup.closure (vsPRho hs '' {e | e ∈ B}) ⊔ vsMScal (vsPBar hs (gens as)) ∧
    r ^ B.length ≤ vsQD s ^ 2 := by
  intro B
  set Sc := vsMScal (vsPBar hs (gens as))
  set Y := vsPBar hs (gens ys) ⊔ Sc
  have hQ := vsH_quotHyp hY
  have hr := hY.2.2.2.1
  obtain ⟨h1, h2, h3⟩ := vsHBas_spec (f := vsPRho hs) (S := Sc) (VsHIn hs Y)
    (vsHBT_test hs has hLb hspan hr.pos hQ) L hL
  refine ⟨h1, h2, h3, ?_⟩
  have hBY : ∀ a ∈ B.map (vsPRho hs), a ∈ Y := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    exact (hL e (h1 e he)).2
  have hcl : Subgroup.closure {a | a ∈ B.map (vsPRho hs)} ≤ Y :=
    (Subgroup.closure_le _).2 fun a ha => hBY a ha
  haveI : Finite (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) := Module.finite_of_finite (ZMod I.p)
  haveI : Finite (Y ⧸ Sc.subgroupOf Y) := inferInstance
  have hpow := vsH_pow_le_index' hr (S := Sc) (Y := Y) (gs := B.map (vsPRho hs)) hBY
    (hQ.mono hcl) (fun i hi => by
      rw [List.length_map] at hi
      rw [List.getElem_map, ← List.map_take, ← vsH_image_list]
      exact h2 i hi)
  rw [List.length_map] at hpow
  exact hpow.trans (vsH_index_le_D hY)

end Meaning2

end GI.Impl
