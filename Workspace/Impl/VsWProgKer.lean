module

public import Workspace.Impl.VsWDefs
public import Workspace.Impl.VsQTr
public import Workspace.Proved.VsWLinMath

@[expose] public section

/-!
# The kernel program

* `wt_vsWVs_le`: the weight of a list of at most `N + 1` vectors whose numbers and lengths are
  at most `N`.
* `vsWUP_spec`: the unit-tag pair builder `vsUnitPairsFuns` of L0 again, with a cost bound
  `4 · 10^5 (N + 1)^4` in terms of one size bound `N` (the bound of `vsUnitPairs_spec` is in
  terms of the weight of the argument, which is too coarse here).
* `vsWKerFuns b` (36 functions), `vsWKer_spec`: on `[p, vsWVs us]` the value
  `vsWVs (vsWKer p us)`, cost `4 · 10^7 (N + 1)^5`.
  What it means: `GI.Proved.vsWKer_span` (`Proved/VsWLinMath.lean`).
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- A list of vectors whose numbers and lengths are at most `N`. -/
def VsWBnd (N : ℕ) (us : List (List ℕ)) : Prop := ∀ u ∈ us, (∀ y ∈ u, y ≤ N) ∧ u.length ≤ N

theorem wt_vsWVs_le {N : ℕ} {us : List (List ℕ)} (h : VsWBnd N us) (hl : us.length ≤ N + 1) :
    (vsWVs us).wt ≤ 11 * (N + 1) ^ 3 + 4 :=
  wt_vsFMat_le (fun r hr => (h r hr).1) (fun r hr => (h r hr).2) hl

theorem vsWUP_cost {m i N u : ℕ} (hm : m ≤ N) (hi : i ≤ N) (hu : u ≤ 5 * (m + 2) ^ 2) :
    loopModK * (m + 1) * ((Val.list [.nat m, .nat i]).wt + m + u + 1) ≤ 10 ^ 5 * (N + 1) ^ 3 := by
  have hK : loopModK = 1000 := rfl
  have w2 := wt_list2_le (.nat m) (.nat i)
  have wm := wt_nat_le m
  have wi := wt_nat_le i
  have h2 : 5 * (m + 2) ^ 2 ≤ 20 * (N + 1) ^ 2 := by
    have : (m + 2) ^ 2 ≤ (2 * (N + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have h1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hin : (Val.list [.nat m, .nat i]).wt + m + u + 1 ≤ 50 * (N + 1) ^ 2 := by omega
  rw [hK]
  calc 1000 * (m + 1) * ((Val.list [.nat m, .nat i]).wt + m + u + 1)
      ≤ 1000 * (N + 1) * (50 * (N + 1) ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hin
    _ = 50000 * (N + 1) ^ 3 := by ring
    _ ≤ 10 ^ 5 * (N + 1) ^ 3 := by omega

theorem wt_vsWUP_le {p N m : ℕ} (hp1 : 1 < p) (hpN : p ≤ N) (hm : m ≤ N) {vs : List (List ℕ)}
    (hvs : ∀ v ∈ vs, (∀ y ∈ v, y < p) ∧ v.length ≤ N) (hl : vs.length ≤ N) :
    (Val.list ((vsUnitPairs m vs).map vsPairVal)).wt ≤ 100 * (N + 1) ^ 3 := by
  have := vs_wt_list_le_of ((vsUnitPairs m vs).map vsPairVal) (c := 20 * (N + 1) ^ 2 + 6) (by
    simp only [vsUnitPairs, List.map_map, List.mem_map, List.mem_range, Function.comp_apply,
      forall_exists_index, and_imp]
    rintro _ i hi rfl
    have hv : vs.getD i [] ∈ vs := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact wt_vsPairVal_le hpN (hvs _ hv).1
      (fun y hy => lt_of_le_of_lt (vsUnit_le_one m i y hy) hp1)
      (hvs _ hv).2 (by simp [vsUnit_length, hm]))
  simp only [List.length_map, vsUnitPairs, List.length_range] at this
  have e : vs.length * (2 * (20 * (N + 1) ^ 2 + 6) + 1) ≤ (N + 1) * (60 * (N + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by
      have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega)
  have : (N + 1) * (60 * (N + 1) ^ 2) = 60 * (N + 1) ^ 3 := by ring
  have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  simp only [vsUnitPairs, List.length_map, List.length_range] at *
  omega

/-- **The unit-tag pairs**, with a cost in terms of one size bound. -/
theorem vsWUP_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsUnitPairsFuns b)) {p N m : ℕ}
    (hp1 : 1 < p) (hpN : p ≤ N) (hm : m ≤ N) {vs : List (List ℕ)}
    (hvs : ∀ v ∈ vs, (∀ y ∈ v, y < p) ∧ v.length ≤ N) (hl : vs.length ≤ N) :
    FunDet P b (.list [.nat m, .list (vs.map natList)])
      (.list ((vsUnitPairs m vs).map vsPairVal)) (4 * 10 ^ 5 * (N + 1) ^ 4) := by
  have h1 : 1 ≤ N := by omega
  have hl' : P.HasAt b (loopFuns b (.length (.get (.var 0) (.nat 1))) .nil (vsUnitPairsStep (b + 3))) :=
    h.block 0 rfl
  have hu : P.HasAt (b + 3) (vsUnitFuns (b + 3)) := h.block 3 rfl
  set a := Val.list [.nat m, .list (vs.map natList)]
  have hk := Det.length (Det.get' (P := P) (env := [a]) (Det.var' (i := 0) rfl) (Det.nat 1)
      (show [Val.nat m, .list (vs.map natList)][1]? = some (.list (vs.map natList)) from rfl))
  rw [List.length_map] at hk
  have ha' : (Val.list [.nat m, .list (vs.map natList)]).wt = a.wt := rfl
  have hma : (Val.nat m).wt < a.wt := wt_le_wt_list (by simp)
  have hva : (Val.list (vs.map natList)).wt < a.wt := wt_le_wt_list (by simp)
  have hnv := length_lt_wt_list (vs.map natList)
  rw [List.length_map] at hnv
  have hm' := wt_nat_le m
  refine FunAll.mono (loopMono_spec hl' hk Det.nil (by omega) (by simp)
    (Inv := fun j acc => acc = .list (((List.range j).map fun i => (vs.getD i [], vsUnit m i)).map
      vsPairVal))
    (by simp) (D := fun _ => 10 ^ 5 * (N + 1) ^ 3 + 1000) ?_) ?_
  · rintro i acc hi rfl
    set A := Val.list (((List.range i).map fun i => (vs.getD i [], vsUnit m i)).map vsPairVal)
    have d0 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, A]) (j := 0) rfl
    have d1 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, A]) (j := 1) rfl
    have d2 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, A]) (j := 2) rfl
    have hvi : (vs.map natList)[i]? = some (natList (vs.getD i [])) := by
      rw [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    have dv := Det.get' (Det.get' d0 (Det.nat 1)
      (show [Val.nat m, .list (vs.map natList)][1]? = some (.list (vs.map natList)) from rfl)) d1 hvi
    have dm := Det.get' d0 (Det.nat 0)
      (show [Val.nat m, .list (vs.map natList)][0]? = some (.nat m) from rfl)
    have du := Det.call (Det.mk2 dm d1) ((vsUnit_spec hu m i).mono fun w c hw => ⟨hw.1, by
      have := hw.2; rw [hw.1] at this; exact this⟩)
    refine (Det.snoc d2 (Det.mk2 dv du)).post fun c hc => ?_
    have hr : ((List.range (i + 1)).map fun i => (vs.getD i [], vsUnit m i)).map vsPairVal =
        ((List.range i).map fun i => (vs.getD i [], vsUnit m i)).map vsPairVal ++
          [Val.list [natList (vs.getD i []), natList (vsUnit m i)]] := by
      simp [List.range_succ, vsPairVal]
    refine ⟨by beta_reduce; rw [hr], ?_, ?_⟩
    · exact wt_list_mono (List.prefix_append _ _)
    · have wU := wt_vsUnit_le m i
      have wsa := wt_stepArg_le a i A
      have h1' := wt_list_mono (List.prefix_append
        (((List.range i).map fun i => (vs.getD i [], vsUnit m i)).map vsPairVal)
        [Val.list [natList (vs.getD i []), natList (vsUnit m i)]])
      have h2 := wt_le_wt_list (vs := ((List.range i).map fun i => (vs.getD i [], vsUnit m i)).map
        vsPairVal ++ [Val.list [natList (vs.getD i []), natList (vsUnit m i)]])
        (v := Val.list [natList (vs.getD i []), natList (vsUnit m i)]) (by simp)
      have h3 := wt_le_wt_list (vs := [natList (vs.getD i []), natList (vsUnit m i)])
        (v := natList (vs.getD i [])) (by simp)
      have h4 := wt_le_wt_list (vs := [natList (vs.getD i []), natList (vsUnit m i)])
        (v := natList (vsUnit m i)) (by simp)
      have hvw : (natList (vs.getD i [])).wt < (Val.list (vs.map natList)).wt := by
        have := wt_getElem_lt (vs.map natList) i (by rw [List.length_map]; exact hi)
        rwa [List.getElem_map, ← List.getD_eq_getElem (d := [])] at this
      have wi := wt_nat_le i
      have w2 := wt_list2_le (.nat m) (.nat i)
      have hcu := vsWUP_cost (u := (natList (vsUnit m i)).wt) hm (show i ≤ N by omega) wU
      have eA : A.wt = (Val.list (((List.range i).map fun i => (vs.getD i [], vsUnit m i)).map
        vsPairVal)).wt := rfl
      beta_reduce
      omega
  · rintro w cost ⟨hw, hc⟩
    refine ⟨hw.trans rfl, ?_⟩
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have hK : loopModK = 1000 := rfl
    rw [hK] at hc
    -- weights of the argument and the result
    have wvs := wt_vsWVs_le (N := N) (us := vs) (fun v hv => ⟨fun y hy =>
      ((hvs v hv).1 y hy).le.trans hpN, (hvs v hv).2⟩) (by omega)
    have wa : a.wt ≤ 40 * (N + 1) ^ 3 := by
      have := wt_list2_le (.nat m) (.list (vs.map natList))
      have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      have : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
      unfold vsWVs at wvs
      omega
    have ww : w.wt ≤ 100 * (N + 1) ^ 3 := by
      rw [hw]; exact wt_vsWUP_le hp1 hpN hm hvs hl
    have k1 : vs.length * (10 ^ 5 * (N + 1) ^ 3 + 1000) ≤ (N + 1) * (2 * 10 ^ 5 * (N + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) (by have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega); omega)
    have k2 : 1000 * (vs.length + 1) * (a.wt + vs.length + w.wt + 1) ≤
        1000 * (N + 1) * (100 * (N + 1) ^ 3 + 40 * (N + 1) ^ 3 + 2 * (N + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e1 : (N + 1) * (2 * 10 ^ 5 * (N + 1) ^ 3) = 2 * 10 ^ 5 * (N + 1) ^ 4 := by ring
    have e2 : 1000 * (N + 1) * (100 * (N + 1) ^ 3 + 40 * (N + 1) ^ 3 + 2 * (N + 1)) =
        140000 * (N + 1) ^ 4 + 2000 * (N + 1) ^ 2 := by ring
    have : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-! ### The kernel program -/

/-- The kernel, on `[p, vs]`: build the unit-tag pairs (at `up`), insert them (at `ins`), and
keep the relations. -/
def vsWKerF (up ins : ℕ) : Expr :=
  .get (.call ins (mk3 (arg 0) (.call up (mk2 (.length (arg 1)) (arg 1))) (mk2 .nil .nil)))
    (.nat 1)

/-- The kernel program at base `b` (36 functions). -/
def vsWKerFuns (b : ℕ) : List Expr :=
  [vsWKerF (b + 1) (b + 7)] ++ vsUnitPairsFuns (b + 1) ++ vsInsertAllFuns (b + 7)

theorem vsWKerFuns_length (b : ℕ) : (vsWKerFuns b).length = 36 := rfl

theorem VsWFit.bnd {p d N : ℕ} {us : List (List ℕ)} (h : GI.Proved.VsWFit p d us) (hpN : p ≤ N)
    (hdN : d ≤ N) : VsWBnd N us :=
  fun u hu => ⟨fun y hy => ((h u hu).1 y hy).le.trans hpN, (h u hu).2.le.trans hdN⟩

/-- **The kernel program.** -/
theorem vsWKer_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWKerFuns b)) {p N d : ℕ}
    (hp1 : 1 < p) (hpN : p ≤ N) (hdN : d ≤ N) {us : List (List ℕ)}
    (hus : GI.Proved.VsWFit p d us) (hl : us.length ≤ N) :
    FunDet P b (.list [.nat p, vsWVs us]) (vsWVs (vsWKer p us)) (4 * 10 ^ 7 * (N + 1) ^ 5) := by
  have h0 : P.funs[b]? = some (vsWKerF (b + 1) (b + 7)) := h.get (j := 0) (by simp [vsWKerFuns])
  have hup : P.HasAt (b + 1) (vsUnitPairsFuns (b + 1)) := h.block 1 rfl
  have hin : P.HasAt (b + 7) (vsInsertAllFuns (b + 7)) := h.block 7 rfl
  set A := Val.list [.nat p, vsWVs us]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, vsWVs us]) (j := 0) rfl
  have a1 : Det P [A] (arg 1) (.list (us.map natList)) _ :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, vsWVs us]) (j := 1) rfl
  have dl := Det.length a1
  rw [List.length_map] at dl
  have hok := GI.Proved.vsWUnitPairs_ok hus hp1
  have hvs : ∀ v ∈ us, (∀ y ∈ v, y < p) ∧ v.length ≤ N :=
    fun v hv => ⟨(hus v hv).1, (hus v hv).2.le.trans hdN⟩
  have dup := Det.call (Det.mk2 dl a1) (vsWUP_spec hup hp1 hpN hl hvs hl)
  have hL : ∀ xt ∈ vsUnitPairs us.length us,
      VsPairFits p N xt ∧ xt.1.length = d ∧ xt.2.length = us.length := fun xt hxt => by
    obtain ⟨h1, h2, h3, h4⟩ := hok xt hxt
    exact ⟨⟨h1, h2, by omega, by omega⟩, h3, h4⟩
  have hLl : (vsUnitPairs us.length us).length ≤ N := by simp [vsUnitPairs, hl]
  have dins := Det.call (Det.mk3 a0 dup (Det.mk2 Det.nil Det.nil))
    (vsInsertAll_spec hin (by omega) hpN hL hLl)
  have dget := Det.get' dins (Det.nat 1) (show [Val.list ((vsInsertAll p (vsUnitPairs us.length
    us)).1.map VsRow.val), .list ((vsInsertAll p (vsUnitPairs us.length us)).2.map natList)][1]? =
      some (vsWVs (vsWKer p us)) from rfl)
  refine FunDet.intro h0 (dget.mono ?_)
  -- weights
  have hfit := vsInsertAll_fits (by omega) hpN hL
  have wacc := wt_vsAccVal_le hpN (by omega) hfit
  have wus := wt_vsWVs_le (VsWFit.bnd hus hpN hdN) (show us.length ≤ N + 1 by omega)
  have wup := wt_vsWUP_le hp1 hpN hl hvs hl
  have wrel := wt_vsRels_le hpN hfit.rels (hfit.nrels.trans (by omega))
  have wp := wt_nat_le p
  have wl := wt_nat_le us.length
  have wA := wt_list2_le (.nat p) (vsWVs us)
  have w2 := wt_list2_le (.nat us.length) (.list (us.map natList))
  have w3 := wt_list3_le (.nat p) (.list ((vsUnitPairs us.length us).map vsPairVal))
    (.list [.list [], .list []])
  have wn : (Val.list [Val.list [], Val.list []]).wt ≤ 20 := by decide
  have q1 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have eA : A.wt = (Val.list [.nat p, vsWVs us]).wt := rfl
  have eU : (vsWVs us).wt = (Val.list (us.map natList)).wt := rfl
  have eR : (vsWVs (vsWKer p us)).wt =
    (Val.list ((vsInsertAll p (vsUnitPairs us.length us)).2.map natList)).wt := rfl
  have eAcc : (vsAccVal (vsInsertAll p (vsUnitPairs us.length us))).wt =
    (Val.list [Val.list ((vsInsertAll p (vsUnitPairs us.length us)).1.map VsRow.val),
      .list ((vsInsertAll p (vsUnitPairs us.length us)).2.map natList)]).wt := rfl
  have eAcc0 : vsAccVal ([], []) = Val.list [.list [], .list []] := rfl
  simp only [eAcc0] at *
  omega

end GI.Impl
