import Workspace.Impl.VsFAlgSpan
import Workspace.Impl.VsFAFlat

/-!
# One insertion of the algebra basis program

The step `vsFAInnerF` computes `vsFAInner` (`Impl/VsFAlgSpan.lean`): multiply `M` by the
generator `g`, flatten, insert with `vsAllStepF`, and append the product to the matrices when
the echelon basis grew. Argument `[[p, z, M], state, g]`.

* `vsFAVal st = [[rows, relations], matrices]`, `VsFAFits`: the size bounds of a state after at
  most `k` insertions.
* `vsFAInner_spec`: the step's value and cost `10^8 (N+1)^5`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- A list of matrices, each as the list of its rows. -/
def vsFMatsVal (Bm : List (List (List ℕ))) : Val := .list (Bm.map fun M => .list (M.map natList))

/-- The value of a state: `[[rows, relations], matrices]`. -/
def vsFAVal (st : (List VsRow × List (List ℕ)) × List (List (List ℕ))) : Val :=
  .list [vsAccVal st.1, vsFMatsVal st.2]

/-- The size bounds of a state after at most `k` insertions of `d × d` matrices. -/
structure VsFAFits (p N d k : ℕ) (st : (List VsRow × List (List ℕ)) × List (List (List ℕ))) :
    Prop where
  acc : VsAccFits p N (d * d) 0 k st.1
  sq : ∀ M ∈ st.2, VsFSq p d M
  nb : st.2.length ≤ k

theorem wt_vsFMatsVal_le {p d N : ℕ} (hpN : p ≤ N) (hdN : d ≤ N) {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, VsFSq p d M) (hl : Bm.length ≤ N + 1) :
    (vsFMatsVal Bm).wt ≤ 40 * (N + 1) ^ 4 := by
  have hw := vs_wt_list_le_of (Bm.map fun M => Val.list (M.map natList))
    (c := 11 * (N + 1) ^ 3 + 4) (by
      simp only [List.mem_map, forall_exists_index, and_imp]
      rintro _ M hM rfl
      exact wt_vsFSq_le hpN hdN (hB M hM))
  rw [List.length_map] at hw
  have h1 : Bm.length * (2 * (11 * (N + 1) ^ 3 + 4) + 1) ≤ (N + 1) * (31 * (N + 1) ^ 3) :=
    Nat.mul_le_mul hl (by have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega); omega)
  have e : (N + 1) * (31 * (N + 1) ^ 3) = 31 * (N + 1) ^ 4 := by ring
  have : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  simp only [vsFMatsVal]
  omega

theorem wt_vsFAVal_le {p d N k : ℕ} (hpN : p ≤ N) (hdN : d ≤ N) (hk : k ≤ N + 1)
    {st : (List VsRow × List (List ℕ)) × List (List (List ℕ))} (h : VsFAFits p N d k st) :
    (vsFAVal st).wt ≤ 600 * (N + 1) ^ 4 := by
  have h1 := wt_vsAccVal_le hpN hk h.acc
  have h2 := wt_vsFMatsVal_le hpN hdN h.sq (h.nb.trans hk)
  have := wt_list2_le (vsAccVal st.1) (vsFMatsVal st.2)
  have : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  simp only [vsFAVal]
  omega

theorem vsFAInner_fits {p N d k : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    {st : (List VsRow × List (List ℕ)) × List (List (List ℕ))} (h : VsFAFits p N d k st)
    {z : List ℕ} (hzb : ∀ y ∈ z, y < p) (hzl : z.length = d) (hdN : d * d ≤ N)
    {M g : List (List ℕ)} (hM : VsFSq p d M) :
    VsFAFits p N d (k + 1) (vsFAInner p z M st g) := by
  have hMg := vsFMatMulL_sq hp hM hzb hzl (X := g)
  have hfl : (vsFMatMulL p M g z).flatten.length = d * d := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => d) (fun r hr => (hMg.rows r hr).2),
      List.map_const', List.sum_replicate, hMg.len, smul_eq_mul]
  have hP : VsPairFits p N ((vsFMatMulL p M g z).flatten, []) :=
    ⟨fun y hy => by
      obtain ⟨r, hr, hyr⟩ := List.mem_flatten.mp hy
      exact (hMg.rows r hr).1 y hyr, by simp, by rw [hfl]; exact hdN, by simp⟩
  have ha := vsAllStep_fits hp hpN hP hfl rfl h.acc
  refine ⟨ha, fun M' hM' => ?_, ?_⟩
  · simp only [vsFAInner, vsFAUpd] at hM'
    split_ifs at hM'
    · simp only [List.mem_append, List.mem_singleton] at hM'
      rcases hM' with hM' | rfl
      · exact h.sq M' hM'
      · exact hMg
    · exact h.sq M' hM'
  · simp only [vsFAInner, vsFAUpd]
    have := h.nb
    split_ifs <;> simp <;> omega

/-- The step, on `[[p, z, M], state, g]`. -/
def vsFAInnerF (mm fl st : ℕ) : Expr :=
  .letE (.call mm (mk2 (mk3 (.get (arg 0) (.nat 0)) (arg 2) (.get (arg 0) (.nat 1)))
      (.get (arg 0) (.nat 2))))
    (.letE (.call fl (mk3 (.nat 0) (.var 1) .nil))
      (.letE (.call st (mk3 (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 0)) (mk2 (.var 2) .nil)))
        (mk2 (.var 3)
          (.ite (.arith .lt (.length (.get (.get (arg 1) (.nat 0)) (.nat 0)))
              (.length (.get (.var 3) (.nat 0))))
            (.snoc (.get (arg 1) (.nat 1)) (.var 1))
            (.get (arg 1) (.nat 1))))))

/-- The context of the step: `[p, z, M]`. -/
def vsFACtx (p : ℕ) (z : List ℕ) (M : List (List ℕ)) : Val :=
  .list [.nat p, natList z, .list (M.map natList)]

theorem vsFAInner_val (p : ℕ) (z : List ℕ) (M g : List (List ℕ))
    (st : (List VsRow × List (List ℕ)) × List (List (List ℕ))) :
    vsFAVal (vsFAInner p z M st g) = .list [vsAccVal (vsAllStep p st.1
      ((vsFMatMulL p M g z).flatten, [])),
      if st.1.1.length < (vsAllStep p st.1 ((vsFMatMulL p M g z).flatten, [])).1.length then
        .list ((st.2.map fun M => .list (M.map natList)) ++
          [.list ((vsFMatMulL p M g z).map natList)])
      else vsFMatsVal st.2] := by
  simp only [vsFAVal, vsFAInner, vsFAUpd]
  split_ifs <;> simp [vsFMatsVal]

theorem vsFAInner_cost {N c a b e w1 w2 : ℕ} (hN : 1 ≤ N + 1)
    (ha : a ≤ 6 * 10 ^ 6 * (N + 1) ^ 5) (hb : b ≤ 2 * 10 ^ 6 * (N + 1) ^ 4)
    (he : e ≤ 3 * 10 ^ 7 * (N + 1) ^ 4) (hw1 : w1 ≤ 10 ^ 5 * (N + 1) ^ 4)
    (hw2 : w2 ≤ 10 ^ 5 * (N + 1) ^ 4) (hc : c ≤ a + (b + (e + w1) + w2) + w2) :
    c ≤ 10 ^ 8 * (N + 1) ^ 5 := by
  have : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- **The step.** -/
theorem vsFAInner_spec {P : Program} {f mm fl sa : ℕ} (hf : P.funs[f]? = some (vsFAInnerF mm fl sa))
    (hmm : P.HasAt mm (vsFMatMulFuns mm)) (hfl : P.HasAt fl (vsFFlatFuns fl))
    (hsa : P.funs[sa]? = some (vsAllStepF (sa + 1))) (hin : P.HasAt (sa + 1) (vsInsertFuns (sa + 1)))
    {p N d k : ℕ} (hp : 0 < p) (hpN : p ≤ N) (hdN : d * d ≤ N) (hk : k ≤ N)
    {st : (List VsRow × List (List ℕ)) × List (List (List ℕ))} (hst : VsFAFits p N d k st)
    {z : List ℕ} (hzb : ∀ y ∈ z, y < p) (hzl : z.length = d)
    {M g : List (List ℕ)} (hM : VsFSq p d M) (hg : VsFSq p d g) :
    FunDet P f (.list [vsFACtx p z M, vsFAVal st, .list (g.map natList)])
      (vsFAVal (vsFAInner p z M st g)) (10 ^ 8 * (N + 1) ^ 5) := by
  have hd : d ≤ N := le_trans (Nat.le_mul_self d) hdN
  have hN1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hMg := vsFMatMulL_sq hp hM hzb hzl (X := g)
  set Mg := vsFMatMulL p M g z with hMgdef
  have hflen : Mg.flatten.length = d * d := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => d) (fun r hr => (hMg.rows r hr).2),
      List.map_const', List.sum_replicate, hMg.len, smul_eq_mul]
  set cV := vsFACtx p z M
  set sV := vsFAVal st
  set gV := Val.list (g.map natList)
  set A := Val.list [cV, sV, gV] with hA
  have wc : cV.wt ≤ 100 * (N + 1) ^ 3 := by
    have h1 := wt_vsFSq_le hpN hd hM
    have h2 := wt_natList_le_sq (fun y hy => (hzb y hy).le.trans hpN) (hzl.trans_le hd)
    have h3 := wt_list3_le (.nat p) (natList z) (.list (M.map natList))
    have h4 := wt_nat_le p
    have e : cV.wt = (Val.list [.nat p, natList z, .list (M.map natList)]).wt := rfl
    omega
  have ws : sV.wt ≤ 600 * (N + 1) ^ 4 := wt_vsFAVal_le hpN hd (by omega) hst
  have wg : gV.wt ≤ 11 * (N + 1) ^ 3 + 4 := wt_vsFSq_le hpN hd hg
  have wA : A.wt ≤ 2000 * (N + 1) ^ 4 := by
    have := wt_list3_le cV sV gV
    have e : A.wt = (Val.list [cV, sV, gV]).wt := rfl
    have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  -- step 1: the product
  have a0 := Det.arg' (P := P) (rest := []) (vs := [cV, sV, gV]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [cV, sV, gV]) (j := 1) rfl
  have a2 := Det.arg' (P := P) (rest := []) (vs := [cV, sV, gV]) (j := 2) rfl
  have cp := Det.get' a0 (Det.nat 0)
    (show [Val.nat p, natList z, .list (M.map natList)][0]? = some (.nat p) from rfl)
  have cz := Det.get' a0 (Det.nat 1)
    (show [Val.nat p, natList z, .list (M.map natList)][1]? = some (natList z) from rfl)
  have cM := Det.get' a0 (Det.nat 2)
    (show [Val.nat p, natList z, .list (M.map natList)][2]? = some (.list (M.map natList)) from rfl)
  have HB : VsFMatFits p N g z :=
    ⟨hzb, hzl.trans_le hd, fun r hr y hy => ((hg.rows r hr).1 y hy).le.trans hpN,
      fun r hr => (hg.rows r hr).2.trans_le hd, fun r hr => by rw [(hg.rows r hr).2, hzl],
      by rw [hg.len]; exact hd⟩
  have HA : ∀ a ∈ M, (∀ y ∈ a, y < p) ∧ a.length ≤ N ∧ g.length ≤ a.length := fun a ha =>
    ⟨(hM.rows a ha).1, (hM.rows a ha).2.trans_le hd, by rw [(hM.rows a ha).2, hg.len]⟩
  have hmul := vsFMatMul_spec hmm hp hpN HB HA (by rw [hM.len]; exact hd)
  have ev : (M.map fun a => natList (vsFRowMul p a g z)) = Mg.map natList := by
    simp [hMgdef, vsFMatMulL]
  rw [ev] at hmul
  have d1 := Det.call (Det.mk2 (Det.mk3 cp a2 cz) cM) hmul
  -- step 2: flatten
  set E1 := [A, Val.list (Mg.map natList)]
  have v1 := Det.var' (P := P) (env := E1) (i := 1) rfl
  have hfs := vsFFlat_spec hfl (N := N) (M := Mg)
    (fun r hr y hy => ((hMg.rows r hr).1 y hy).le.trans hpN) (fun r hr => (hMg.rows r hr).2.trans_le hd)
    (by rw [hMg.len]; exact hd) (by rw [hflen]; exact hdN)
  have d2 := Det.call (Det.mk3 (Det.nat (env := E1) (P := P) 0) v1 (Det.nil : Det P E1 .nil (natList []) 5)) hfs
  -- step 3: insertion
  set E2 := E1 ++ [natList Mg.flatten]
  have hP : VsPairFits p N (Mg.flatten, []) :=
    ⟨fun y hy => by
      obtain ⟨r, hr, hyr⟩ := List.mem_flatten.mp hy
      exact (hMg.rows r hr).1 y hyr, by simp, by rw [hflen]; exact hdN, by simp⟩
  have hall := vsAllStep_spec hsa hin hp hpN hP hflen rfl hk hst.acc
  have b0 := Det.arg' (P := P) (rest := [Val.list (Mg.map natList), natList Mg.flatten])
    (vs := [cV, sV, gV]) (j := 0) rfl
  have b1 := Det.arg' (P := P) (rest := [Val.list (Mg.map natList), natList Mg.flatten])
    (vs := [cV, sV, gV]) (j := 1) rfl
  have bp := Det.get' b0 (Det.nat 0)
    (show [Val.nat p, natList z, .list (M.map natList)][0]? = some (.nat p) from rfl)
  have bacc := Det.get' b1 (Det.nat 0)
    (show [vsAccVal st.1, vsFMatsVal st.2][0]? = some (vsAccVal st.1) from rfl)
  have v2 := Det.var' (P := P) (env := E2) (i := 2) rfl
  have dpair : Det P E2 (mk2 (.var 2) .nil) (vsPairVal (Mg.flatten, [])) _ :=
    Det.mk2 v2 (Det.nil : Det P E2 .nil (natList []) 5)
  have d3 := Det.call (Det.mk3 bp bacc dpair) hall
  -- step 4: the new state
  set a := vsAllStep p st.1 (Mg.flatten, [])
  set E3 := E2 ++ [vsAccVal a]
  have hfa := vsFAInner_fits hp hpN hst hzb hzl hdN hM (g := g)
  have wout := wt_vsFAVal_le hpN hd (by omega) hfa
  have v3 := Det.var' (P := P) (env := E3) (i := 3) rfl
  have c0 := Det.arg' (P := P) (rest := [Val.list (Mg.map natList), natList Mg.flatten, vsAccVal a])
    (vs := [cV, sV, gV]) (j := 1) rfl
  have cR := Det.get' (Det.get' c0 (Det.nat 0)
    (show [vsAccVal st.1, vsFMatsVal st.2][0]? = some (vsAccVal st.1) from rfl)) (Det.nat 0)
    (show [Val.list (st.1.1.map VsRow.val), .list (st.1.2.map natList)][0]? = some _ from rfl)
  have cR' := Det.get' v3 (Det.nat 0)
    (show [Val.list (a.1.map VsRow.val), .list (a.2.map natList)][0]? = some _ from rfl)
  have dlt := Det.arith' (op := .lt) (Det.length cR) (Det.length cR') rfl
  have cB := Det.get' c0 (Det.nat 1)
    (show [vsAccVal st.1, vsFMatsVal st.2][1]? = some (vsFMatsVal st.2) from rfl)
  have v1' := Det.var' (P := P) (env := E3) (i := 1) rfl
  have hval := vsFAInner_val p z M g st
  rw [← hMgdef] at hval
  rw [hval]
  rw [hval] at wout
  simp only [List.length_map] at dlt
  by_cases hlt : st.1.1.length < a.1.length
  · rw [if_pos hlt] at wout ⊢
    have dite := Det.ite_pos (e := .get (arg 1) (.nat 1)) dlt (by simp [hlt]) (Det.snoc cB v1')
    refine FunDet.intro hf ((Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.mk2 v3 dite)))).mono ?_)
    have wMg := wt_vsFSq_le hpN hd hMg
    have wfl := wt_natList_le_sq (xs := Mg.flatten) (fun y hy => (hP.hx y hy).le.trans hpN) hP.lx
    have wacc := wt_vsAccVal_le hpN (by omega) hst.acc
    have hfa' : VsAccFits p N (d * d) 0 (k + 1) a := vsAllStep_fits hp hpN hP hflen rfl hst.acc
    have wa := wt_vsAccVal_le hpN (by omega) hfa'
    have wB := wt_vsFMatsVal_le hpN hd hst.sq (hst.nb.trans (by omega))
    have wpv : (vsPairVal (Mg.flatten, [])).wt ≤ 2 * (5 * (N + 1) ^ 2) + 16 := by
      have := wt_list2_le (natList Mg.flatten) (natList []); have : (natList []).wt ≤ 5 := by decide
      have e : (vsPairVal (Mg.flatten, [])).wt = (Val.list [natList Mg.flatten, natList []]).wt := rfl
      omega
    have wR := wt_le_wt_list (vs := [Val.list (st.1.1.map VsRow.val), .list (st.1.2.map natList)])
      (v := Val.list (st.1.1.map VsRow.val)) (by simp)
    have wR' := wt_le_wt_list (vs := [Val.list (a.1.map VsRow.val), .list (a.2.map natList)])
      (v := Val.list (a.1.map VsRow.val)) (by simp)
    have ea1 : (vsAccVal st.1).wt = (Val.list [Val.list (st.1.1.map VsRow.val), .list (st.1.2.map natList)]).wt := rfl
    have ea2 : (vsAccVal a).wt = (Val.list [Val.list (a.1.map VsRow.val), .list (a.2.map natList)]).wt := rfl
    have es : sV.wt = (Val.list [vsAccVal st.1, vsFMatsVal st.2]).wt := rfl
    have ec : cV.wt = (Val.list [.nat p, natList z, .list (M.map natList)]).wt := rfl
    have wz := wt_natList_le_sq (fun y hy => (hzb y hy).le.trans hpN) (hzl.trans_le hd)
    have wMl := wt_vsFSq_le hpN hd hM
    have w1 := wt_list3_le (.nat p) gV (natList z)
    have w2 := wt_list2_le (Val.list [.nat p, gV, natList z]) (.list (M.map natList))
    have w3 := wt_list3_le (.nat 0) (.list (Mg.map natList)) (natList [])
    have w4 := wt_list3_le (.nat p) (vsAccVal st.1) (vsPairVal (Mg.flatten, []))
    have w5 := wt_list2_le (natList Mg.flatten) (natList [])
    have wn0 := wt_nat_le 0
    have wn1 := wt_nat_le 1
    have wn2 := wt_nat_le 2
    have wnp := wt_nat_le p
    have wl1 := wt_nat_le (if st.1.1.length < a.1.length then 1 else 0)
    have wnil : (natList []).wt ≤ 5 := by decide
    have hz1 : (if st.1.1.length < a.1.length then 1 else 0) ≤ 1 := by split <;> omega
    have hl1 : st.1.1.length ≤ N := hst.acc.nrows.trans hk
    have hl2 : a.1.length ≤ N + 1 := hfa'.nrows.trans (by omega)
    have wl2 := wt_nat_le st.1.1.length
    have wl3 := wt_nat_le a.1.length
    have eq1 : (Val.list [natList (Mg.flatten, []).1, natList (Mg.flatten, []).2]).wt =
      (vsPairVal (Mg.flatten, [])).wt := rfl
    have eq2 : (Val.list [Val.nat 0, Val.list (Mg.map natList), Val.list []]).wt =
      (Val.list [Val.nat 0, Val.list (Mg.map natList), natList []]).wt := rfl
    have eqA : A.wt = (Val.list [cV, sV, gV]).wt := rfl
    have hN4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
    have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have wX := wt_list2_le (vsAccVal a) (.list ((st.2.map fun M => .list (M.map natList)) ++
      [.list (Mg.map natList)]))
    have wnew := wt_vsFMatsVal_le hpN hd (Bm := st.2 ++ [Mg]) (fun M' hM' => by
      simp only [List.mem_append, List.mem_singleton] at hM'
      rcases hM' with hM' | rfl
      · exact hst.sq M' hM'
      · exact hMg) (by have := hst.nb; simp; omega)
    have enew : vsFMatsVal (st.2 ++ [Mg]) = .list ((st.2.map fun M => .list (M.map natList)) ++
      [.list (Mg.map natList)]) := by simp [vsFMatsVal]
    rw [enew] at wnew
    have hz2 : BinOp.lt.eval st.1.1.length a.1.length ≤ 1 := by
      rw [BinOp.eval_lt]; split <;> omega
    omega
  · rw [if_neg hlt] at wout ⊢
    have dite := Det.ite_zero (t := .snoc (.get (arg 1) (.nat 1)) (.var 1)) (by simpa [hlt] using dlt) cB
    refine FunDet.intro hf ((Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.mk2 v3 dite)))).mono ?_)
    have wMg := wt_vsFSq_le hpN hd hMg
    have wfl := wt_natList_le_sq (xs := Mg.flatten) (fun y hy => (hP.hx y hy).le.trans hpN) hP.lx
    have wacc := wt_vsAccVal_le hpN (by omega) hst.acc
    have hfa' : VsAccFits p N (d * d) 0 (k + 1) a := vsAllStep_fits hp hpN hP hflen rfl hst.acc
    have wa := wt_vsAccVal_le hpN (by omega) hfa'
    have wB := wt_vsFMatsVal_le hpN hd hst.sq (hst.nb.trans (by omega))
    have wpv : (vsPairVal (Mg.flatten, [])).wt ≤ 2 * (5 * (N + 1) ^ 2) + 16 := by
      have := wt_list2_le (natList Mg.flatten) (natList []); have : (natList []).wt ≤ 5 := by decide
      have e : (vsPairVal (Mg.flatten, [])).wt = (Val.list [natList Mg.flatten, natList []]).wt := rfl
      omega
    have wR := wt_le_wt_list (vs := [Val.list (st.1.1.map VsRow.val), .list (st.1.2.map natList)])
      (v := Val.list (st.1.1.map VsRow.val)) (by simp)
    have wR' := wt_le_wt_list (vs := [Val.list (a.1.map VsRow.val), .list (a.2.map natList)])
      (v := Val.list (a.1.map VsRow.val)) (by simp)
    have ea1 : (vsAccVal st.1).wt = (Val.list [Val.list (st.1.1.map VsRow.val), .list (st.1.2.map natList)]).wt := rfl
    have ea2 : (vsAccVal a).wt = (Val.list [Val.list (a.1.map VsRow.val), .list (a.2.map natList)]).wt := rfl
    have es : sV.wt = (Val.list [vsAccVal st.1, vsFMatsVal st.2]).wt := rfl
    have ec : cV.wt = (Val.list [.nat p, natList z, .list (M.map natList)]).wt := rfl
    have wz := wt_natList_le_sq (fun y hy => (hzb y hy).le.trans hpN) (hzl.trans_le hd)
    have wMl := wt_vsFSq_le hpN hd hM
    have w1 := wt_list3_le (.nat p) gV (natList z)
    have w2 := wt_list2_le (Val.list [.nat p, gV, natList z]) (.list (M.map natList))
    have w3 := wt_list3_le (.nat 0) (.list (Mg.map natList)) (natList [])
    have w4 := wt_list3_le (.nat p) (vsAccVal st.1) (vsPairVal (Mg.flatten, []))
    have w5 := wt_list2_le (natList Mg.flatten) (natList [])
    have wn0 := wt_nat_le 0
    have wn1 := wt_nat_le 1
    have wn2 := wt_nat_le 2
    have wnp := wt_nat_le p
    have wl1 := wt_nat_le (if st.1.1.length < a.1.length then 1 else 0)
    have wnil : (natList []).wt ≤ 5 := by decide
    have hz1 : (if st.1.1.length < a.1.length then 1 else 0) ≤ 1 := by split <;> omega
    have hl1 : st.1.1.length ≤ N := hst.acc.nrows.trans hk
    have hl2 : a.1.length ≤ N + 1 := hfa'.nrows.trans (by omega)
    have wl2 := wt_nat_le st.1.1.length
    have wl3 := wt_nat_le a.1.length
    have eq1 : (Val.list [natList (Mg.flatten, []).1, natList (Mg.flatten, []).2]).wt =
      (vsPairVal (Mg.flatten, [])).wt := rfl
    have eq2 : (Val.list [Val.nat 0, Val.list (Mg.map natList), Val.list []]).wt =
      (Val.list [Val.nat 0, Val.list (Mg.map natList), natList []]).wt := rfl
    have eqA : A.wt = (Val.list [cV, sV, gV]).wt := rfl
    have hN4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
    have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have wX := wt_list2_le (vsAccVal a) (vsFMatsVal st.2)
    omega

end GI.Impl
