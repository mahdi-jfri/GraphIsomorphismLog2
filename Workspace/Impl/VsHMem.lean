import Workspace.Impl.VsPStep4
import Workspace.Proved.VsHBasisMath

/-!
# Is `y` in `⟨K⟩ S`?

On `[[ctx, r], K, y]`, the program lists the words `w` of `K` with exponents below `r`
(`vsPEnum`) and asks whether some `w⁻¹ y` has its local matrix in `L`.

* `vsHMemItE`, `vsHMemIt_spec`: on `[[ctx, y], w]`, the test of `w⁻¹ y`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- On `[[ctx, y], w]`: is the local matrix of `w⁻¹ y` in the span of the rows? -/
def vsHMemItE (inv comp inl : ℕ) : Expr :=
  .call inl (mk2 (.get (arg 0) (.nat 0))
    (.call comp (mk2 (.call inv (arg 1)) (.get (arg 0) (.nat 1)))))

/-- The cost of an item. -/
def vsHMemItCost (Cφ N W : ℕ) : ℕ := vsPInLPCost Cφ N W + 10 ^ 6 * (N + 1) ^ 4 + 100 * W

set_option maxHeartbeats 4000000 in
theorem vsHMemIt_spec {P : Program} {f inv comp inl phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsHMemItE inv comp inl)) (hinv : P.HasAt inv (invFuns inv))
    (hcomp : P.HasAt comp (composeFuns comp)) (hinl : P.HasAt inl (vsPInLPFuns inl phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {y w : Perm (Fin I.n)} (hg : w⁻¹ * y ∈ gens I.gs) :
    FunDet P f (.list [.list [vsPCtx I ws' cs rows hs, encPerm y], encPerm w])
      (boolVal (vsPInLB I ws' cs rows (w⁻¹ * y))) (vsHMemItCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  have a0 := Det.arg' (P := P) (vs := [.list [C, encPerm y], encPerm w]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [.list [C, encPerm y], encPerm w]) (rest := []) (j := 1) rfl
  have dC := Det.get' a0 (Det.nat 0) (show [C, encPerm y][0]? = some C from rfl)
  have dy := Det.get' a0 (Det.nat 1) (show [C, encPerm y][1]? = some (encPerm y) from rfl)
  have di := Det.call a1 (inv_spec hinv w)
  have dc := Det.call (Det.mk2 di dy) (compose_spec hcomp w⁻¹ y)
  have dl := Det.call (Det.mk2 dC dc) (vsPInLP_spec hinl hphi H hg)
  refine FunDet.intro hf (dl.mono ?_)
  have hn := H.n
  have wC : C.wt ≤ W := H.cw
  have wy := wt_encPerm_le y
  have ww := wt_encPerm_le w
  have wi := wt_encPerm_le w⁻¹
  have wm := wt_encPerm_le (w⁻¹ * y)
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hn3 : (I.n + 1) ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hn4 : (I.n + 1) ^ 4 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have w2 := wt_list2_le C (encPerm y)
  have w2' := wt_list2_le (.list [C, encPerm y]) (encPerm w)
  have w3 := wt_list2_le (encPerm w⁻¹) (encPerm y)
  have w4 := wt_list2_le C (encPerm (w⁻¹ * y))
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have wb := wt_boolVal_le (vsPInLB I ws' cs rows (w⁻¹ * y))
  simp only [vsHMemItCost, invK, permK] at *
  omega

/-- The item test on values. -/
noncomputable def vsHMq (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (y : Perm (Fin I.n)) (v : Val) : Bool := by
  classical exact decide (∃ w : Perm (Fin I.n), v = encPerm w ∧
    vsPInLB I ws' cs rows (w⁻¹ * y) = true)

open Classical in
theorem vsHMq_enc (ws' cs : List (List ℕ)) (rows : List VsRow) (y w : Perm (Fin I.n)) :
    vsHMq I ws' cs rows y (encPerm w) = vsPInLB I ws' cs rows (w⁻¹ * y) := by
  unfold vsHMq
  have : (∃ w' : Perm (Fin I.n), encPerm w = encPerm w' ∧ vsPInLB I ws' cs rows (w'⁻¹ * y) = true) ↔
      vsPInLB I ws' cs rows (w⁻¹ * y) = true :=
    ⟨fun ⟨w', e, h⟩ => by rw [encPerm_injective e]; exact h, fun h => ⟨w, rfl, h⟩⟩
  rw [Bool.decide_congr this]
  cases vsPInLB I ws' cs rows (w⁻¹ * y) <;> rfl

/-- The value of the membership test. -/
noncomputable def vsHMemB (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow) (r : ℕ)
    (K : List (Perm (Fin I.n))) (y : Perm (Fin I.n)) : Bool :=
  (vsPEnum r K).any fun w => vsPInLB I ws' cs rows (w⁻¹ * y)

/-- On `[[ctx, r], K, y]`: is `y` in `⟨K⟩ S`? -/
def vsHMemE (en any : ℕ) : Expr :=
  .letE (.call en (mk3 (.get (arg 0) (.nat 1)) (.get (.get (arg 0) (.nat 0)) (.nat 6)) (arg 1)))
    (.call any (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 2)) (.var 1)))

/-- The indices of the membership test. -/
structure VsHMX where
  (e : VsPEX) (mem any mit inv inl phi : ℕ)

/-- The layout of the membership test. -/
structure VsHMLay (P : Program) (x : VsHMX) : Prop where
  e : VsPELay P x.e
  hmem : P.funs[x.mem]? = some (vsHMemE x.e.en x.any)
  hany : P.HasAt x.any (anyFuns x.any x.mit)
  hmit : P.funs[x.mit]? = some (vsHMemItE x.inv x.e.comp x.inl)
  hinv : P.HasAt x.inv (invFuns x.inv)
  hinl : P.HasAt x.inl (vsPInLPFuns x.inl x.phi)

/-- The cost of the membership test. -/
def vsHMemCost (Cφ N W : ℕ) : ℕ :=
  vsPEnumCost N + (N + 1) * vsHMemItCost Cφ N W + 2 * 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3)

set_option maxHeartbeats 4000000 in
/-- **The membership test.** -/
theorem vsHMem_spec {P : Program} {x : VsHMX} (L : VsHMLay P x) {Cφ N W : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ N)
    {K : List (Perm (Fin I.n))} (hK : r ^ K.length ≤ N) (hKl : K.length ≤ N)
    (hKs : ∀ g ∈ K, g ∈ gens I.gs) {y : Perm (Fin I.n)} (hy : y ∈ gens I.gs) :
    FunAll P x.mem (.list [.list [vsPCtx I ws' cs rows hs, .nat r], .list (K.map encPerm), encPerm y])
      (fun w c => w = boolVal (vsHMemB I ws' cs rows r K y) ∧ c ≤ vsHMemCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set cv := [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n] with hcv
  set vs := [Val.list [C, .nat r], .list (K.map encPerm), encPerm y]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have dr := Det.get' a0 (Det.nat 1) (show [C, Val.nat r][1]? = some (.nat r) from rfl)
  have dC := Det.get' a0 (Det.nat 0) (show [C, Val.nat r][0]? = some C from rfl)
  have dC' : Det P [Val.list vs] (.get (arg 0) (.nat 0)) (.list cv) _ := dC
  have dn := Det.get' dC' (Det.nat 6) (show cv[6]? = some (.nat I.n) from rfl)
  have dE := Det.call (Det.mk3 dr dn a1) (vsPEnum_spec L.e.hf L.e.hfo L.e.hst L.e.hmpM L.e.hmid
    L.e.hmp L.e.hit L.e.hpow L.e.hcomp L.e.hcat L.e.hrng H.n hr1 hr hK hKl)
  set E := vsPEnum r K
  set env := [Val.list vs, Val.list (E.map encPerm)]
  have b0 := Det.arg' (P := P) (vs := vs) (rest := [Val.list (E.map encPerm)]) (j := 0) rfl
  have b2 := Det.arg' (P := P) (vs := vs) (rest := [Val.list (E.map encPerm)]) (j := 2) rfl
  have bC := Det.get' b0 (Det.nat 0) (show [C, Val.nat r][0]? = some C from rfl)
  have bE := Det.var' (P := P) (env := env) (i := 1) rfl
  have hEl : E.length ≤ N := by rw [vsPEnum_length]; exact hK
  have hEs : ∀ w ∈ E, w ∈ gens I.gs := by
    intro w hw
    exact (Subgroup.closure_le (gens I.gs)).2 (fun g hg => hKs g hg) (vsPEnum_mem K w hw)
  have hit : ∀ v ∈ E.map encPerm, FunDet P x.mit (.list [.list [C, encPerm y], v])
      (boolVal (vsHMq I ws' cs rows y v)) (vsHMemItCost Cφ N W) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    rw [vsHMq_enc]
    exact vsHMemIt_spec L.hmit L.hinv L.e.hcomp L.hinl hphi H
      (mul_mem (inv_mem (hEs w hw)) hy)
  refine FunAll.intro L.hmem (EvalAll.letE dE fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.call_funAll (Det.mk2 (Det.mk2 bC b2) bE) fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine (any_spec L.hany hit).mono fun w cb hw => ⟨?_, ?_⟩
  · rw [hw.1, List.any_map]
    congr 1
    unfold vsHMemB
    congr 1
    funext w
    exact vsHMq_enc ws' cs rows y w
  · obtain ⟨hw1, hcb⟩ := hw
    have hn := H.n
    have wC : C.wt ≤ W := H.cw
    have wb : w.wt ≤ 3 := by rw [hw1]; exact wt_boolVal_le _
    have wK := vsP_wt_perms H.n K (by omega)
    have wE := vsP_wt_perms H.n E (by omega)
    have wy := wt_encPerm_le y
    have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have q13 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
    have wr := wt_nat_le r
    have wn := wt_nat_le I.n
    have w1 := wt_list2_le C (.nat r)
    have w2 := wt_list3_le (.list [C, .nat r]) (.list (K.map encPerm)) (encPerm y)
    have evs : (Val.list vs).wt = (Val.list [.list [C, .nat r], .list (K.map encPerm), encPerm y]).wt := rfl
    have w3 := wt_list3_le (.nat r) (.nat I.n) (.list (K.map encPerm))
    have w4 := wt_list2_le C (encPerm y)
    have w5 := wt_list2_le (.list [C, encPerm y]) (.list (E.map encPerm))
    have esum : (List.map (fun _ => vsHMemItCost Cφ N W) (List.map encPerm E)).sum =
        E.length * vsHMemItCost Cφ N W := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map]
    rw [esum, List.length_map] at hcb
    have hs1 : E.length * vsHMemItCost Cφ N W ≤ (N + 1) * vsHMemItCost Cφ N W :=
      Nat.mul_le_mul_right _ (by omega)
    set X := (Val.list [Val.list [C, encPerm y], Val.list (List.map encPerm E)]).wt + E.length + 4
    have hX : X ≤ 10 * (W + 100 * (N + 1) ^ 3) := by simp only [X]; omega
    have hs2 : loopModK * (E.length + 1) * X ≤ 1000 * (N + 1) * (10 * (W + 100 * (N + 1) ^ 3)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) hX
    have e3 : 1000 * (N + 1) * (10 * (W + 100 * (N + 1) ^ 3)) =
        10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3) := by ring
    have hW1 : 10 ^ 4 * (W + 100 * (N + 1) ^ 3) ≤ 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have e4 : 2 * 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3) =
        2 * (10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3)) := by ring
    have lk : loopModK = 1000 := rfl
    unfold vsHMemCost
    omega

/-! ### What the membership test means -/

section Meaning

variable {s : VsQSt I} [Fact I.p.Prime]

/-- **What the membership test means.** If `⟨K̄⟩` has commutators and `r`-th powers in `S`
(and commutes with `S`), the test on `y` holds iff `ȳ ∈ ⟨K̄⟩ S`. -/
theorem vsHMemB_iff (hs : VsQStOK s) {as : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs)
    {Lb : List (List (List ℕ))} (hLb : ∀ M ∈ Lb, VsFSq I.p (vsQD s) M)
    (hspan : vsFMatSpan I.p (vsQD s) Lb = Subalgebra.toSubmodule
      (vsFAlgOf I.p (vsQD s) (as.map (vsPLocL I s.ws' (vsQCs s)))))
    {r : ℕ} (hr : 0 < r) {K : List (Perm (Fin I.n))} (hK : ∀ g ∈ K, g ∈ gens s.hs)
    (hQ : VsPQuotHyp (vsPBar hs (gens K)) (vsMScal (vsPBar hs (gens as))) r)
    {y : Perm (Fin I.n)} (hy : y ∈ gens s.hs) :
    vsHMemB I s.ws' (vsQCs s) (vsPRows I.p Lb) r K y = true ↔
      vsPRho hs y ∈ vsPBar hs (gens K) ⊔ vsMScal (vsPBar hs (gens as)) := by
  have hKle : gens K ≤ gens s.hs := (Subgroup.closure_le _).2 fun g hg => hK g hg
  have hin : ∀ g ∈ gens s.hs, vsPInLB I s.ws' (vsQCs s) (vsPRows I.p Lb) g = true ↔
      vsPRho hs g ∈ vsMScal (vsPBar hs (gens as)) := fun g hg => by
    rw [vsPRho_of hs hg]; exact vsPInLB_iff hs has hLb hspan hg
  unfold vsHMemB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨w, hw, hwy⟩
    have hwK : w ∈ gens K := vsPEnum_mem K w hw
    have hws := hKle hwK
    rw [hin _ (mul_mem (inv_mem hws) hy), vsPRho_mul hs (inv_mem hws) hy, vsPRho_inv hs hws] at hwy
    have e : vsPRho hs y = vsPRho hs w * ((vsPRho hs w)⁻¹ * vsPRho hs y) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (vsPRho_mem_vsPBar hs hwK hws)) (Subgroup.mem_sup_right hwy)
  · intro hyS
    have hN : vsPBar hs (gens K) = Subgroup.closure {g | g ∈ K.map (vsPRho hs)} := by
      rw [vsPBar_gens hs hK]
      congr 1
      ext g
      simp
    obtain ⟨e, hel, her, he⟩ := vsH_cover_W hr hQ hN _ hyS
    rw [List.length_map] at hel
    refine ⟨vsPW K e, vsPEnum_W_mem K e hel her, ?_⟩
    have hws : vsPW K e ∈ gens s.hs := vsPW_mem hK e
    rw [hin _ (mul_mem (inv_mem hws) hy), vsPRho_mul hs (inv_mem hws) hy, vsPRho_inv hs hws,
      vsPRho_W hs hK]
    exact he

end Meaning

end GI.Impl
