import Workspace.Impl.VsFAlgSpanFold

/-!
# The algebra basis program

* `vsFAOuterF`: pass `i`, on `[[p, z, gs], i, state]`; `vsFAOuter_spec`.
* `vsFAlgSpanFuns b` (58 functions), `vsFAlgSpan_spec`: on `[p, gs, z, I]` the result is
  `vsFAVal (vsFAlgSpanL p z I gs (d * d))`, cost `10^9 (N+1)^7`, if `1 + d² |gs| ≤ N` (this
  bounds the number of insertions) and `p, d² ≤ N`.
  What the result means: `GI.Proved.vsFAlgSpanL_span` (`Proved/VsFAlgSpanMath.lean`).
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- Pass `i`, on `[[p, z, gs], i, state]`, calling the fold at `fo`. -/
def vsFAOuterF (fo : ℕ) : Expr :=
  .ite (.arith .lt (arg 1) (.length (.get (arg 2) (.nat 1))))
    (.call fo (mk3 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
        (.get (.get (arg 2) (.nat 1)) (arg 1)))
      (.get (arg 0) (.nat 2)) (arg 2)))
    (arg 2)

/-- The context of the passes: `[p, z, gs]`. -/
def vsFAOCtx (p : ℕ) (z : List ℕ) (gs : List (List (List ℕ))) : Val :=
  .list [.nat p, natList z, vsFMatsVal gs]

theorem vsFAOuter_fits {p N d k : ℕ} (hp : 0 < p) (hpN : p ≤ N) {z : List ℕ}
    (hzb : ∀ y ∈ z, y < p) (hzl : z.length = d) (hdN : d * d ≤ N) (gs : List (List (List ℕ)))
    {st : (List VsRow × List (List ℕ)) × List (List (List ℕ))} (h : VsFAFits p N d k st) (i : ℕ) :
    VsFAFits p N d (k + gs.length) (vsFAOuter p z gs st i) := by
  unfold vsFAOuter
  split_ifs with hi
  · have hM : VsFSq p d (st.2.getD i []) := h.sq _ (by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
    exact vsFAFold_fits hp hpN hzb hzl hdN hM gs k st h
  · exact h.mono (by omega)

/-- **A pass.** -/
theorem vsFAOuter_spec {P : Program} {f fo fs mm fl sa : ℕ}
    (hf : P.funs[f]? = some (vsFAOuterF fo)) (hfo : P.HasAt fo (foldlFuns fo fs))
    (hfs : P.funs[fs]? = some (vsFAInnerF mm fl sa))
    (hmm : P.HasAt mm (vsFMatMulFuns mm)) (hfl : P.HasAt fl (vsFFlatFuns fl))
    (hsa : P.funs[sa]? = some (vsAllStepF (sa + 1))) (hin : P.HasAt (sa + 1) (vsInsertFuns (sa + 1)))
    {p N d k : ℕ} (hp : 0 < p) (hpN : p ≤ N) (hdN : d * d ≤ N)
    {gs : List (List (List ℕ))} (hgs : ∀ g ∈ gs, VsFSq p d g) (hk : k + gs.length ≤ N)
    {st : (List VsRow × List (List ℕ)) × List (List (List ℕ))} (hst : VsFAFits p N d k st)
    {z : List ℕ} (hzb : ∀ y ∈ z, y < p) (hzl : z.length = d) {i : ℕ} (hi : i ≤ N) :
    FunDet P f (.list [vsFAOCtx p z gs, .nat i, vsFAVal st])
      (vsFAVal (vsFAOuter p z gs st i)) (3 * 10 ^ 8 * (N + 1) ^ 6) := by
  have hd : d ≤ N := le_trans (Nat.le_mul_self d) hdN
  have hN1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  set cV := vsFAOCtx p z gs
  set sV := vsFAVal st
  have wz := wt_natList_le_sq (fun y hy => (hzb y hy).le.trans hpN) (hzl.trans_le hd)
  have wg := wt_vsFMatsVal_le hpN hd hgs (by omega)
  have wc : cV.wt ≤ 100 * (N + 1) ^ 4 := by
    have h3 := wt_list3_le (.nat p) (natList z) (vsFMatsVal gs)
    have h4 := wt_nat_le p
    have e : cV.wt = (Val.list [.nat p, natList z, vsFMatsVal gs]).wt := rfl
    omega
  have ws : sV.wt ≤ 600 * (N + 1) ^ 4 := wt_vsFAVal_le hpN hd (by omega) hst
  have wi := wt_nat_le i
  have wA : (Val.list [cV, .nat i, sV]).wt ≤ 2000 * (N + 1) ^ 4 := by
    have := wt_list3_le cV (.nat i) sV; omega
  have a0 := Det.arg' (P := P) (rest := []) (vs := [cV, .nat i, sV]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [cV, .nat i, sV]) (j := 1) rfl
  have a2 := Det.arg' (P := P) (rest := []) (vs := [cV, .nat i, sV]) (j := 2) rfl
  have aB := Det.get' a2 (Det.nat 1)
    (show [vsAccVal st.1, vsFMatsVal st.2][1]? = some (vsFMatsVal st.2) from rfl)
  have dl := Det.length (vs := st.2.map fun M => Val.list (M.map natList)) aB
  rw [List.length_map] at dl
  have dlt := Det.arith' (op := .lt) a1 dl rfl
  have wB := wt_vsFMatsVal_le hpN hd hst.sq (hst.nb.trans (by omega))
  have wst := wt_le_wt_list (vs := [vsAccVal st.1, vsFMatsVal st.2]) (v := vsFMatsVal st.2) (by simp)
  have es : sV.wt = (Val.list [vsAccVal st.1, vsFMatsVal st.2]).wt := rfl
  have wl := wt_nat_le st.2.length
  have hl : st.2.length ≤ N := hst.nb.trans (by omega)
  by_cases hil : i < st.2.length
  · have hv : vsFAOuter p z gs st i = gs.foldl (vsFAInner p z (st.2.getD i [])) st := by
      rw [vsFAOuter, if_pos hil]
    rw [hv]
    have hM : VsFSq p d (st.2.getD i []) := hst.sq _ (by
      rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem hil)
    have hget : (st.2.map fun M => Val.list (M.map natList))[i]? =
        some (.list ((st.2.getD i []).map natList)) := by
      simp [List.getD_eq_getElem _ _ hil, hil]
    have aM := Det.get' aB a1 hget
    have cp := Det.get' a0 (Det.nat 0)
      (show [Val.nat p, natList z, vsFMatsVal gs][0]? = some (.nat p) from rfl)
    have cz := Det.get' a0 (Det.nat 1)
      (show [Val.nat p, natList z, vsFMatsVal gs][1]? = some (natList z) from rfl)
    have cg := Det.get' a0 (Det.nat 2)
      (show [Val.nat p, natList z, vsFMatsVal gs][2]? = some (vsFMatsVal gs) from rfl)
    have hfold := vsFAFold_spec hfo hfs hmm hfl hsa hin hp hpN hdN hgs hk hst hzb hzl hM
    have dc := Det.call (Det.mk3 (Det.mk3 cp cz aM) cg a2) hfold
    have dite := Det.ite_pos (e := arg 2) dlt (by simp [hil]) dc
    refine FunDet.intro hf (dite.mono ?_)
    have wM := wt_vsFSq_le hpN hd hM
    have wMs := wt_le_wt_list (vs := st.2.map fun M => Val.list (M.map natList))
      (v := .list ((st.2.getD i []).map natList)) (by
        simp only [List.mem_map]
        exact ⟨_, by rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem hil, rfl⟩)
    have eB : (vsFMatsVal st.2).wt = (Val.list (st.2.map fun M => Val.list (M.map natList))).wt := rfl
    have w3 := wt_list3_le (.nat p) (natList z) (.list ((st.2.getD i []).map natList))
    have e3 : (vsFACtx p z (st.2.getD i [])).wt =
      (Val.list [.nat p, natList z, .list ((st.2.getD i []).map natList)]).wt := rfl
    have w4 := wt_list3_le (Val.list [.nat p, natList z, .list ((st.2.getD i []).map natList)])
      (vsFMatsVal gs) sV
    have wo := wt_vsFAVal_le hpN hd (by omega) (vsFAFold_fits hp hpN hzb hzl hdN hM gs k st hst)
    have wp := wt_nat_le p
    have hz2 : BinOp.lt.eval i st.2.length ≤ 1 := by rw [BinOp.eval_lt]; split <;> omega
    have : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have hv : vsFAOuter p z gs st i = st := by rw [vsFAOuter, if_neg hil]
    rw [hv]
    have dite := Det.ite_zero (t := .call fo (mk3 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
        (.get (.get (arg 2) (.nat 1)) (arg 1))) (.get (arg 0) (.nat 2)) (arg 2)))
      (by simpa [hil] using dlt) a2
    refine FunDet.intro hf (dite.mono ?_)
    have : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega

theorem vsFAPasses_fits {p N d k : ℕ} (hp : 0 < p) (hpN : p ≤ N) {z : List ℕ}
    (hzb : ∀ y ∈ z, y < p) (hzl : z.length = d) (hdN : d * d ≤ N) (gs : List (List (List ℕ)))
    {st : (List VsRow × List (List ℕ)) × List (List (List ℕ))} (h : VsFAFits p N d k st) :
    ∀ i, VsFAFits p N d (k + i * gs.length) ((List.range i).foldl (vsFAOuter p z gs) st)
  | 0 => by simpa using h
  | i + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      show k + (i + 1) * gs.length = k + i * gs.length + gs.length by ring]
    exact vsFAOuter_fits hp hpN hzb hzl hdN gs (vsFAPasses_fits hp hpN hzb hzl hdN gs h i) i

/-- The main function, on `[p, gs, z, I]`: insert `I · I`, then run `|z|²` passes. -/
def vsFAMainF (fo it : ℕ) : Expr :=
  .letE (.call fo (mk3 (mk3 (arg 0) (arg 2) (arg 3)) (mk1 (arg 3)) (mk2 (mk2 .nil .nil) .nil)))
    (.call it (mk3 (mk3 (arg 0) (arg 2) (arg 1))
      (.arith .mul (.length (arg 2)) (.length (arg 2))) (.var 1)))

/-- The algebra basis program, at base `b` (58 functions). -/
def vsFAlgSpanFuns (b : ℕ) : List Expr :=
  [vsFAMainF (b + 1) (b + 5)] ++ foldlFuns (b + 1) (b + 4) ++ [vsFAInnerF (b + 9) (b + 25) (b + 32)] ++
    iterFuns (b + 5) (b + 8) ++ [vsFAOuterF (b + 1)] ++ vsFMatMulFuns (b + 9) ++
    vsFFlatFuns (b + 25) ++ [vsAllStepF (b + 33)] ++ vsInsertFuns (b + 33)

theorem vsFAlgSpanFuns_length (b : ℕ) : (vsFAlgSpanFuns b).length = 58 := rfl

/-- The input of the algebra basis program: `[p, gs, z, I]`. -/
def vsFAlgSpanArg (p : ℕ) (gs : List (List (List ℕ))) (z : List ℕ) (I : List (List ℕ)) : Val :=
  .list [.nat p, vsFMatsVal gs, natList z, .list (I.map natList)]

/-- **The algebra basis program.** On `[p, gs, z, I]`, for `d × d` matrices `gs` and `I` and a
vector `z` of length `d`, all with entries below `p`, the result is the state
`vsFAlgSpanL p z I gs (d * d)`. The bound `1 + d² |gs| ≤ N` covers all insertions. -/
theorem vsFAlgSpan_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsFAlgSpanFuns b))
    {p N d : ℕ} (hp : 0 < p) (hpN : p ≤ N) (hdN : d * d ≤ N)
    {gs : List (List (List ℕ))} (hgs : ∀ g ∈ gs, VsFSq p d g) (hN : 1 + d * d * gs.length ≤ N)
    (hgl : gs.length ≤ N)
    {z : List ℕ} (hzb : ∀ y ∈ z, y < p) (hzl : z.length = d) {I : List (List ℕ)}
    (hI : VsFSq p d I) :
    FunDet P b (vsFAlgSpanArg p gs z I) (vsFAVal (vsFAlgSpanL p z I gs (d * d)))
      (10 ^ 9 * (N + 1) ^ 7) := by
  have hf : P.funs[b]? = some (vsFAMainF (b + 1) (b + 5)) :=
    h.get (j := 0) (by simp [vsFAlgSpanFuns])
  have hfo : P.HasAt (b + 1) (foldlFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hfs : P.funs[b + 4]? = some (vsFAInnerF (b + 9) (b + 25) (b + 32)) :=
    h.get (j := 4) (by rw [vsFAlgSpanFuns_length]; omega)
  have hit : P.HasAt (b + 5) (iterFuns (b + 5) (b + 8)) := h.block 5 rfl
  have hout : P.funs[b + 8]? = some (vsFAOuterF (b + 1)) :=
    h.get (j := 8) (by rw [vsFAlgSpanFuns_length]; omega)
  have hmm : P.HasAt (b + 9) (vsFMatMulFuns (b + 9)) := h.block 9 rfl
  have hfl : P.HasAt (b + 25) (vsFFlatFuns (b + 25)) := h.block 25 rfl
  have hsa : P.funs[b + 32]? = some (vsAllStepF (b + 32 + 1)) :=
    h.get (j := 32) (by rw [vsFAlgSpanFuns_length]; omega)
  have hin : P.HasAt (b + 32 + 1) (vsInsertFuns (b + 32 + 1)) := h.block 33 rfl
  have hd : d ≤ N := le_trans (Nat.le_mul_self d) hdN
  have hN1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN4 : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN6 : (N + 1) ^ 6 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  set D := d * d with hD
  have h0 : VsFAFits p N d 0 (([], []), []) :=
    ⟨⟨by simp, by simp, by simp, by simp⟩, by simp, by simp⟩
  -- the first insertion
  have hfold0 := vsFAFold_spec hfo hfs hmm hfl hsa hin hp hpN hdN (gs := [I])
    (fun g hg => by rw [List.mem_singleton.mp hg]; exact hI) (by simp; omega) h0 hzb hzl hI
  set s0 := [I].foldl (vsFAInner p z I) (([], []), []) with hs0
  have hs0' : s0 = vsFAInner p z I (([], []), []) I := rfl
  have hf0 : VsFAFits p N d 1 s0 := by
    have := vsFAFold_fits hp hpN hzb hzl hdN hI [I] 0 _ h0
    simpa using this
  set A := vsFAlgSpanArg p gs z I
  have wz := wt_natList_le_sq (fun y hy => (hzb y hy).le.trans hpN) (hzl.trans_le hd)
  have wg := wt_vsFMatsVal_le hpN hd hgs (by omega)
  have wI := wt_vsFSq_le hpN hd hI
  have wp := wt_nat_le p
  have wA : A.wt ≤ 200 * (N + 1) ^ 4 := by
    have := wt_list_le [Val.nat p, vsFMatsVal gs, natList z, .list (I.map natList)]
    have e : A.wt = (Val.list [Val.nat p, vsFMatsVal gs, natList z, .list (I.map natList)]).wt := rfl
    simp at this
    omega
  have a0 := Det.arg' (P := P) (rest := [])
    (vs := [Val.nat p, vsFMatsVal gs, natList z, .list (I.map natList)]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := [])
    (vs := [Val.nat p, vsFMatsVal gs, natList z, .list (I.map natList)]) (j := 1) rfl
  have a2 := Det.arg' (P := P) (rest := [])
    (vs := [Val.nat p, vsFMatsVal gs, natList z, .list (I.map natList)]) (j := 2) rfl
  have a3 := Det.arg' (P := P) (rest := [])
    (vs := [Val.nat p, vsFMatsVal gs, natList z, .list (I.map natList)]) (j := 3) rfl
  have dnil := (Det.nil (P := P) (env := [A]))
  have dst0 : Det P [A] (mk2 (mk2 .nil .nil) .nil) (vsFAVal (([], []), [])) 200 :=
    (Det.mk2 (Det.mk2 dnil dnil) dnil).mono (by decide)
  have d1 := Det.call (Det.mk3 (Det.mk3 a0 a2 a3) (Det.mk1 a3) dst0) hfold0
  -- the passes
  have b0 := Det.arg' (P := P) (rest := [vsFAVal s0])
    (vs := [Val.nat p, vsFMatsVal gs, natList z, .list (I.map natList)]) (j := 0) rfl
  have b1 := Det.arg' (P := P) (rest := [vsFAVal s0])
    (vs := [Val.nat p, vsFMatsVal gs, natList z, .list (I.map natList)]) (j := 1) rfl
  have b2 := Det.arg' (P := P) (rest := [vsFAVal s0])
    (vs := [Val.nat p, vsFMatsVal gs, natList z, .list (I.map natList)]) (j := 2) rfl
  have bl := Det.length (vs := z.map Val.nat) b2
  have bm := Det.arith' (op := .mul) bl bl (z := D) (by simp [hzl, hD])
  have v1 := Det.var' (P := P) (env := [A, vsFAVal s0]) (i := 1) rfl
  have hpf : ∀ i, i ≤ D → VsFAFits p N d (1 + i * gs.length)
      ((List.range i).foldl (vsFAOuter p z gs) s0) := fun i _ =>
    vsFAPasses_fits hp hpN hzb hzl hdN gs hf0 i
  have hiD : ∀ i, i ≤ D → 1 + i * gs.length ≤ N := fun i hi =>
    le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) 1) hN
  have hiter := iter_spec hit (c := vsFAOCtx p z gs) (k := D) (acc0 := vsFAVal s0)
    (Inv := fun i acc => acc = vsFAVal ((List.range i).foldl (vsFAOuter p z gs) s0))
    (M := 600 * (N + 1) ^ 4) (B := fun _ => 3 * 10 ^ 8 * (N + 1) ^ 6) rfl
    (fun i acc hi hacc => by
      rw [hacc]; exact wt_vsFAVal_le hpN hd (by have := hiD i hi; omega) (hpf i hi))
    (fun i acc hi hacc => by
      rw [hacc]
      refine FunAll.mono (vsFAOuter_spec hout hfo hfs hmm hfl hsa hin hp hpN hdN hgs
        (by have := hiD (i + 1) hi; rw [Nat.succ_mul] at this; omega) (hpf i hi.le) hzb hzl
        (by omega)) fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil])
  have wc : (vsFAOCtx p z gs).wt ≤ 100 * (N + 1) ^ 4 := by
    have h3 := wt_list3_le (.nat p) (natList z) (vsFMatsVal gs)
    have e : (vsFAOCtx p z gs).wt = (Val.list [.nat p, natList z, vsFMatsVal gs]).wt := rfl
    omega
  have ws0 := wt_vsFAVal_le hpN hd (by omega) hf0
  have wD := wt_nat_le D
  have hiter' : FunAll P (b + 5) (.list [vsFAOCtx p z gs, .nat D, vsFAVal s0])
      (fun w c => w = vsFAVal ((List.range D).foldl (vsFAOuter p z gs) s0) ∧
        c ≤ 5 * 10 ^ 8 * (N + 1) ^ 7) := by
    refine hiter.mono fun w c hw => ⟨hw.1, ?_⟩
    have hc := hw.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have hK : loopModK = 1000 := rfl
    rw [hK] at hc
    have w3 := wt_list3_le (vsFAOCtx p z gs) (.nat D) (vsFAVal s0)
    have k1 : D * (3 * 10 ^ 8 * (N + 1) ^ 6) ≤ (N + 1) * (3 * 10 ^ 8 * (N + 1) ^ 6) :=
      Nat.mul_le_mul_right _ (by omega)
    have k2 : 1000 * (D + 1) * ((Val.list [vsFAOCtx p z gs, .nat D, vsFAVal s0]).wt + D +
        600 * (N + 1) ^ 4 + 1) ≤ 1000 * (N + 1) * (3000 * (N + 1) ^ 4) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e1 : (N + 1) * (3 * 10 ^ 8 * (N + 1) ^ 6) = 3 * 10 ^ 8 * (N + 1) ^ 7 := by ring
    have e2 : 1000 * (N + 1) * (3000 * (N + 1) ^ 4) = 3 * 10 ^ 6 * (N + 1) ^ 5 := by ring
    have : (N + 1) ^ 5 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have d2 := Det.call (Det.mk3 (Det.mk3 b0 b2 b1) bm v1) hiter'
  refine FunDet.intro hf ((Det.letE d1 d2).mono ?_)
  have wout := wt_vsFAVal_le hpN hd (by have := hiD D le_rfl; omega) (hpf D le_rfl)
  have wo0 := wt_vsFAVal_le hpN hd (by omega) hf0
  have w31 := wt_list3_le (Val.list [.nat p, natList z, .list (I.map natList)])
    (.list [Val.list (I.map natList)]) (vsFAVal (([], []), []))
  have w32 := wt_list3_le (.nat p) (natList z) (.list (I.map natList))
  have w33 := wt_list3_le (.nat p) (natList z) (vsFMatsVal gs)
  have w34 := wt_list3_le (Val.list [.nat p, natList z, vsFMatsVal gs]) (.nat D) (vsFAVal s0)
  have w1 : (Val.list [Val.list (I.map natList)]).wt ≤ 2 * (Val.list (I.map natList)).wt + 6 := by
    have := wt_list_le [Val.list (I.map natList)]; simp at this; omega
  have wnil : (vsFAVal (([], []), [])).wt ≤ 100 := by decide
  have wnl : (Val.list ([] : List Val)).wt ≤ 5 := by decide
  have wnn : (Val.list [Val.list ([] : List Val), Val.list []]).wt ≤ 20 := by decide
  have eA : A.wt = (Val.list [Val.nat p, vsFMatsVal gs, natList z, .list (I.map natList)]).wt := rfl
  have ezl : (z.map Val.nat).length = d := by rw [List.length_map, hzl]
  rw [ezl] at bl
  have e7 : (N + 1) ^ 7 = (N + 1) * (N + 1) ^ 6 := by ring
  have hD' : D ≤ N := hdN
  omega

end GI.Impl
