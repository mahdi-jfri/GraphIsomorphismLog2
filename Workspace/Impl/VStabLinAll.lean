module

public import Workspace.Impl.VStabLinInsert

@[expose] public section

/-!
# Inserting a list of vector pairs

We insert the pairs `(x_i, t_i)` of a list one after the other into an echelon basis that starts
empty. The accumulator holds the rows and the relations. When a pair sifts to a nonzero main
part it becomes a new row. When it sifts to zero, its sifted tag is a relation.

* `vsAllStep`, `vsInsertAll`: the mathematical fold.
* `vsAllStepF`: one step, on `[p, acc, (x, t)]`; `vsAllStep_spec`.
* `vsInsertAllFuns`: the fold, on `[p, pairs, acc0]`; `vsInsertAll_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- One insertion into the accumulator `(rows, relations)`. -/
def vsAllStep (p : ℕ) (acc : List VsRow × List (List ℕ)) (xt : List ℕ × List ℕ) :
    List VsRow × List (List ℕ) :=
  if vsNzIdx (vsSift p acc.1 xt).1 < (vsSift p acc.1 xt).1.length then
    (acc.1 ++ [vsNewRow p (vsSift p acc.1 xt) (vsNzIdx (vsSift p acc.1 xt).1)], acc.2)
  else (acc.1, acc.2 ++ [(vsSift p acc.1 xt).2])

/-- Insert all pairs of a list, starting from no rows and no relations. -/
def vsInsertAll (p : ℕ) (L : List (List ℕ × List ℕ)) : List VsRow × List (List ℕ) :=
  L.foldl (vsAllStep p) ([], [])

/-- The value of an accumulator: `[rows, relations]`. -/
def vsAccVal (acc : List VsRow × List (List ℕ)) : Val :=
  .list [.list (acc.1.map VsRow.val), .list (acc.2.map natList)]

theorem vsInsertAll_take_succ (p : ℕ) (L : List (List ℕ × List ℕ)) (i : ℕ) (hi : i < L.length) :
    vsInsertAll p (L.take (i + 1)) = vsAllStep p (vsInsertAll p (L.take i)) L[i] := by
  rw [vsInsertAll, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    List.foldl_append]
  rfl

/-- An accumulator after at most `k` insertions of pairs of lengths `lx` and `lt`. -/
structure VsAccFits (p N lx lt k : ℕ) (acc : List VsRow × List (List ℕ)) : Prop where
  rows : ∀ r ∈ acc.1, VsRowFits N lx lt r
  nrows : acc.1.length ≤ k
  rels : ∀ t ∈ acc.2, (∀ y ∈ t, y < p) ∧ t.length ≤ N
  nrels : acc.2.length ≤ k

theorem vsAllStep_fits {p N lx lt k : ℕ} (hp : 0 < p) (hpN : p ≤ N) {xt : List ℕ × List ℕ}
    (hP : VsPairFits p N xt) (hlx : xt.1.length = lx) (hlt : xt.2.length = lt)
    {acc : List VsRow × List (List ℕ)} (ha : VsAccFits p N lx lt k acc) :
    VsAccFits p N lx lt (k + 1) (vsAllStep p acc xt) := by
  have hy := vsSift_fits hp acc.1 hP
  obtain ⟨e1, e2⟩ := vsSift_length p acc.1 xt
  unfold vsAllStep
  split_ifs with hk
  · have hn := vsNewRow_fits hp hpN hy hk
    rw [e1, e2, hlx, hlt] at hn
    refine ⟨fun r hr => ?_, ?_, ha.rels, ?_⟩
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact ha.rows r hr
      · exact hn
    · dsimp only; simp only [List.length_append, List.length_singleton]; have := ha.nrows; omega
    · dsimp only; have := ha.nrels; omega
  · refine ⟨ha.rows, ?_, fun t ht => ?_, ?_⟩
    · dsimp only; have := ha.nrows; omega
    · simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact ha.rels t ht
      · exact ⟨hy.ht, hy.lt⟩
    · dsimp only; simp only [List.length_append, List.length_singleton]; have := ha.nrels; omega

theorem vsFoldAll_fits {p N lx lt : ℕ} (hp : 0 < p) (hpN : p ≤ N) :
    ∀ (L : List (List ℕ × List ℕ)) (k : ℕ) (acc : List VsRow × List (List ℕ)),
    (∀ xt ∈ L, VsPairFits p N xt ∧ xt.1.length = lx ∧ xt.2.length = lt) →
    VsAccFits p N lx lt k acc → VsAccFits p N lx lt (k + L.length) (L.foldl (vsAllStep p) acc)
  | [], k, acc, _, ha => ha
  | xt :: L, k, acc, hL, ha => by
    obtain ⟨h1, h2, h3⟩ := hL xt (List.mem_cons_self ..)
    have := vsFoldAll_fits hp hpN L (k + 1) (vsAllStep p acc xt)
      (fun y hy => hL y (List.mem_cons_of_mem _ hy)) (vsAllStep_fits hp hpN h1 h2 h3 ha)
    have e : k + (L.length + 1) = k + 1 + L.length := by omega
    rw [List.foldl_cons, List.length_cons, e]
    exact this

theorem vsInsertAll_fits {p N lx lt : ℕ} (hp : 0 < p) (hpN : p ≤ N) {L : List (List ℕ × List ℕ)}
    (hL : ∀ xt ∈ L, VsPairFits p N xt ∧ xt.1.length = lx ∧ xt.2.length = lt) :
    VsAccFits p N lx lt L.length (vsInsertAll p L) := by
  have := vsFoldAll_fits hp hpN L 0 ([], []) hL ⟨by simp, by simp, by simp, by simp⟩
  rw [Nat.zero_add] at this
  exact this

theorem wt_vsRels_le {p N : ℕ} (hpN : p ≤ N) {rels : List (List ℕ)}
    (h : ∀ t ∈ rels, (∀ y ∈ t, y < p) ∧ t.length ≤ N) (hl : rels.length ≤ N + 1) :
    (Val.list (rels.map natList)).wt ≤ 11 * (N + 1) ^ 3 + 4 := by
  have hw := vs_wt_list_le_of (rels.map natList) (c := 5 * (N + 1) ^ 2) (by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ t ht rfl
    exact wt_natList_le_sq (fun y hy => ((h t ht).1 y hy).le.trans hpN) (h t ht).2)
  rw [List.length_map] at hw
  have e : (N + 1) * (2 * (5 * (N + 1) ^ 2) + 1) ≤ 11 * (N + 1) ^ 3 := by
    have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e3 : (N + 1) ^ 3 = (N + 1) * (N + 1) ^ 2 := by ring
    rw [e3]; nlinarith
  have := Nat.mul_le_mul_right (2 * (5 * (N + 1) ^ 2) + 1) hl
  omega

theorem wt_vsAccVal_le {p N lx lt k : ℕ} (hpN : p ≤ N) (hk : k ≤ N + 1)
    {acc : List VsRow × List (List ℕ)} (ha : VsAccFits p N lx lt k acc) :
    (vsAccVal acc).wt ≤ 250 * (N + 1) ^ 3 := by
  have h1 := wt_vsRows_le ha.rows (ha.nrows.trans hk)
  have h2 := wt_vsRels_le hpN ha.rels (ha.nrels.trans hk)
  have := wt_list2_le (.list (acc.1.map VsRow.val)) (.list (acc.2.map natList))
  have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  simp only [vsAccVal]
  omega

/-- The step, on `[p, acc, (x, t)]`, calling the insertion at `ins`. -/
def vsAllStepF (ins : ℕ) : Expr :=
  .letE (.call ins (mk3 (arg 0) (.get (arg 1) (.nat 0)) (arg 2)))
    (.ite (.get (.var 1) (.nat 0))
      (mk2 (.get (.var 1) (.nat 1)) (.get (arg 1) (.nat 1)))
      (mk2 (.get (arg 1) (.nat 0)) (.snoc (.get (arg 1) (.nat 1)) (.get (.var 1) (.nat 1)))))

/-- **One step of the fold.** -/
theorem vsAllStep_spec {P : Program} {f ins : ℕ} (hf : P.funs[f]? = some (vsAllStepF ins))
    (hi : P.HasAt ins (vsInsertFuns ins)) {p N : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    {xt : List ℕ × List ℕ} (hP : VsPairFits p N xt) {lx lt k : ℕ} (hlx : xt.1.length = lx)
    (hlt : xt.2.length = lt) (hk : k ≤ N) {acc : List VsRow × List (List ℕ)}
    (ha : VsAccFits p N lx lt k acc) :
    FunDet P f (.list [.nat p, vsAccVal acc, vsPairVal xt]) (vsAccVal (vsAllStep p acc xt))
      (2 * 10 ^ 7 * (N + 1) ^ 4 + 100) := by
  have hN3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have wacc := wt_vsAccVal_le hpN (by omega) ha
  have wP := wt_vsPairVal_le hpN hP.hx hP.ht hP.lx hP.lt
  have wp := wt_nat_le p
  have wA : (Val.list [.nat p, vsAccVal acc, vsPairVal xt]).wt ≤ 1000 * (N + 1) ^ 3 := by
    have := wt_list3_le (.nat p) (vsAccVal acc) (vsPairVal xt)
    omega
  have wR : (Val.list (acc.1.map VsRow.val)).wt ≤ 200 * (N + 1) ^ 3 := by
    have := wt_vsRows_le ha.rows (by have := ha.nrows; omega); omega
  have hr : ∀ r ∈ acc.1, VsRowFits N xt.1.length xt.2.length r := by
    rw [hlx, hlt]; exact ha.rows
  have hrl : acc.1.length ≤ N := ha.nrows.trans hk
  -- the call of the insertion
  have d0 := Det.arg' (P := P) (rest := []) (vs := [.nat p, vsAccVal acc, vsPairVal xt]) (j := 0) rfl
  have d1 := Det.arg' (P := P) (rest := []) (vs := [.nat p, vsAccVal acc, vsPairVal xt]) (j := 1) rfl
  have d2 := Det.arg' (P := P) (rest := []) (vs := [.nat p, vsAccVal acc, vsPairVal xt]) (j := 2) rfl
  have dR := Det.get' d1 (Det.nat 0)
    (show [Val.list (acc.1.map VsRow.val), .list (acc.2.map natList)][0]? = some _ from rfl)
  have dm := Det.mk3 d0 dR d2
  have dins := Det.call dm (vsInsert_spec hi hp hpN hP hr hrl)
  have wm : (Val.list [.nat p, .list (acc.1.map VsRow.val), vsPairVal xt]).wt ≤ 1000 * (N + 1) ^ 3 := by
    have := wt_list3_le (.nat p) (.list (acc.1.map VsRow.val)) (vsPairVal xt)
    omega
  have hy := vsSift_fits hp acc.1 hP
  obtain ⟨e1, e2⟩ := vsSift_length p acc.1 xt
  have hstep := vsAllStep_fits hp hpN hP hlx hlt ha
  have wout := wt_vsAccVal_le hpN (by omega) hstep
  by_cases hkz : vsNzIdx (vsSift p acc.1 xt).1 < (vsSift p acc.1 xt).1.length
  · set rows' := acc.1 ++ [vsNewRow p (vsSift p acc.1 xt) (vsNzIdx (vsSift p acc.1 xt).1)]
      with hrows'
    have hv : vsInsertVal p acc.1 xt = .list [.nat 1, .list (rows'.map VsRow.val)] := by
      simp only [vsInsertVal, if_pos hkz, hrows']
    have hs : vsAllStep p acc xt = (rows', acc.2) := by
      simp only [vsAllStep, if_pos hkz, hrows']
    rw [hv] at dins
    rw [hs] at wout hstep ⊢
    have wR2 := wt_vsRows_le (rows := rows') hstep.rows (by have : rows'.length ≤ k + 1 := hstep.nrows; omega)
    have wI : (Val.list [.nat 1, .list (rows'.map VsRow.val)]).wt ≤ 250 * (N + 1) ^ 3 := by
      have := wt_list2_le (.nat 1) (.list (rows'.map VsRow.val))
      have := wt_nat_le 1
      have w2 : (vsAccVal (rows', acc.2)).wt =
        (Val.list [.list (rows'.map VsRow.val), .list (acc.2.map natList)]).wt := rfl
      have := wt_list2_le (.list (rows'.map VsRow.val)) (.list (acc.2.map natList))
      have := wt_le_wt_list (vs := [.list (rows'.map VsRow.val), .list (acc.2.map natList)])
        (v := .list (rows'.map VsRow.val)) (by simp)
      omega
    have dI := Det.var' (P := P) (env := [Val.list [.nat p, vsAccVal acc, vsPairVal xt], Val.list [.nat 1, .list (rows'.map VsRow.val)]])
      (i := 1) rfl
    have dfl := Det.get' dI (Det.nat 0)
      (show [Val.nat 1, .list (rows'.map VsRow.val)][0]? = some _ from rfl)
    have dI1 := Det.get' dI (Det.nat 1)
      (show [Val.nat 1, .list (rows'.map VsRow.val)][1]? = some _ from rfl)
    have d1' := Det.arg' (P := P) (rest := [Val.list [.nat 1, .list (rows'.map VsRow.val)]])
      (vs := [.nat p, vsAccVal acc, vsPairVal xt]) (j := 1) rfl
    have dT := Det.get' d1' (Det.nat 1)
      (show [Val.list (acc.1.map VsRow.val), .list (acc.2.map natList)][1]? = some _ from rfl)
    have dout := Det.ite_pos (e := mk2 (.get (arg 1) (.nat 0))
        (.snoc (.get (arg 1) (.nat 1)) (.get (.var 1) (.nat 1)))) dfl one_ne_zero (Det.mk2 dI1 dT)
    refine FunDet.intro hf ((Det.letE dins dout).mono ?_)
    have wT := wt_le_wt_list (vs := [.list (acc.1.map VsRow.val), .list (acc.2.map natList)])
      (v := .list (acc.2.map natList)) (by simp)
    have wacc' : (vsAccVal acc).wt =
      (Val.list [.list (acc.1.map VsRow.val), .list (acc.2.map natList)]).wt := rfl
    have w2 : (vsAccVal (rows', acc.2)).wt =
      (Val.list [.list (rows'.map VsRow.val), .list (acc.2.map natList)]).wt := rfl
    have wI1 := wt_le_wt_list (vs := [Val.nat 1, .list (rows'.map VsRow.val)])
      (v := .list (rows'.map VsRow.val)) (by simp)
    have w1 := wt_nat_le 1
    have w0 := wt_nat_le 0
    omega
  · have hv : vsInsertVal p acc.1 xt = .list [.nat 0, natList (vsSift p acc.1 xt).2] := by
      simp only [vsInsertVal, if_neg hkz]
    have hs : vsAllStep p acc xt = (acc.1, acc.2 ++ [(vsSift p acc.1 xt).2]) := by
      simp only [vsAllStep, if_neg hkz]
    rw [hv] at dins
    rw [hs] at wout ⊢
    set z := (vsSift p acc.1 xt).2 with hz
    have wz := wt_natList_le_sq (fun y hy' => (hy.ht y hy').le.trans hpN) hy.lt
    have ezw : (natList z).wt = (natList (vsSift p acc.1 xt).2).wt := rfl
    have wI : (Val.list [.nat 0, natList z]).wt ≤ 200 * (N + 1) ^ 3 := by
      have := wt_list2_le (.nat 0) (natList z)
      have := wt_nat_le 0
      omega
    have dI := Det.var' (P := P) (env := [Val.list [.nat p, vsAccVal acc, vsPairVal xt], Val.list [.nat 0, natList z]]) (i := 1) rfl
    have dfl := Det.get' dI (Det.nat 0) (show [Val.nat 0, natList z][0]? = some _ from rfl)
    have dI1 := Det.get' dI (Det.nat 1) (show [Val.nat 0, natList z][1]? = some _ from rfl)
    have d1' := Det.arg' (P := P) (rest := [Val.list [.nat 0, natList z]])
      (vs := [.nat p, vsAccVal acc, vsPairVal xt]) (j := 1) rfl
    have dR' := Det.get' d1' (Det.nat 0)
      (show [Val.list (acc.1.map VsRow.val), .list (acc.2.map natList)][0]? = some _ from rfl)
    have dT := Det.get' d1' (Det.nat 1)
      (show [Val.list (acc.1.map VsRow.val), .list (acc.2.map natList)][1]? = some _ from rfl)
    have dout := Det.ite_zero (t := mk2 (.get (.var 1) (.nat 1)) (.get (arg 1) (.nat 1))) dfl
      (Det.mk2 dR' (Det.snoc dT dI1))
    have em : (acc.2 ++ [z]).map natList = acc.2.map natList ++ [natList z] := by simp
    have hval : vsAccVal (acc.1, acc.2 ++ [z]) =
        .list [.list (acc.1.map VsRow.val), .list (acc.2.map natList ++ [natList z])] := by
      simp only [vsAccVal, em]
    rw [hval] at wout ⊢
    refine FunDet.intro hf ((Det.letE dins dout).mono ?_)
    have wT := wt_le_wt_list (vs := [.list (acc.1.map VsRow.val), .list (acc.2.map natList)])
      (v := .list (acc.2.map natList)) (by simp)
    have wR' := wt_le_wt_list (vs := [.list (acc.1.map VsRow.val), .list (acc.2.map natList)])
      (v := .list (acc.1.map VsRow.val)) (by simp)
    have wacc' : (vsAccVal acc).wt =
      (Val.list [.list (acc.1.map VsRow.val), .list (acc.2.map natList)]).wt := rfl
    have wS := wt_le_wt_list
      (vs := [.list (acc.1.map VsRow.val), .list (acc.2.map natList ++ [natList z])])
      (v := .list (acc.2.map natList ++ [natList z])) (by simp)
    have w0 := wt_nat_le 0
    omega

/-- The fold of insertions, at base `b` (29 functions). -/
def vsInsertAllFuns (b : ℕ) : List Expr :=
  foldlFuns b (b + 3) ++ [vsAllStepF (b + 4)] ++ vsInsertFuns (b + 4)

theorem vsInsertAllFuns_length (b : ℕ) : (vsInsertAllFuns b).length = 29 := rfl

/-- The arguments of the fold: `[p, pairs, acc0]` with the empty accumulator. -/
abbrev vsInsertAllArg (p : ℕ) (L : List (List ℕ × List ℕ)) : Val :=
  .list [.nat p, .list (L.map vsPairVal), vsAccVal ([], [])]

theorem vsInsertAll_cost {Q5 S a M L N : ℕ} (hL : L ≤ N) (hS : S ≤ N * (2 * 10 ^ 7 * Q5 + 100))
    (hk : 1000 * (L + 1) * (a + L + M + 1) ≤ 1000 * (N + 1) * (500 * Q5)) {c : ℕ}
    (hc : c ≤ S + 1000 * (L + 1) * (a + L + M + 1)) (hQ : N + 1 ≤ Q5) :
    c ≤ 3 * 10 ^ 7 * ((N + 1) * Q5) := by
  have : N * (2 * 10 ^ 7 * Q5 + 100) ≤ (N + 1) * (2 * 10 ^ 7 * Q5) := by nlinarith
  have : 1000 * (N + 1) * (500 * Q5) = 500000 * ((N + 1) * Q5) := by ring
  have : (N + 1) * (2 * 10 ^ 7 * Q5) = 2 * 10 ^ 7 * ((N + 1) * Q5) := by ring
  omega

/-- **Insertion of a list.** On `[p, pairs, [[], []]]`, with at most `N` pairs that fit, all of
the same lengths, the result is `vsAccVal (vsInsertAll p L)`. -/
theorem vsInsertAll_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsInsertAllFuns b)) {p N : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) {lx lt : ℕ} {L : List (List ℕ × List ℕ)}
    (hL : ∀ xt ∈ L, VsPairFits p N xt ∧ xt.1.length = lx ∧ xt.2.length = lt)
    (hLl : L.length ≤ N) :
    FunDet P b (vsInsertAllArg p L) (vsAccVal (vsInsertAll p L)) (3 * 10 ^ 7 * (N + 1) ^ 5) := by
  have hfl : P.HasAt b (foldlFuns b (b + 3)) := h.block 0 rfl
  have hst : P.funs[b + 3]? = some (vsAllStepF (b + 4)) :=
    h.get (j := 3) (by rw [vsInsertAllFuns_length]; omega)
  have hin : P.HasAt (b + 4) (vsInsertFuns (b + 4)) := h.block 4 rfl
  have hN3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hfit : ∀ i, i ≤ L.length → VsAccFits p N lx lt i (vsInsertAll p (L.take i)) := by
    intro i hi
    have := vsInsertAll_fits hp hpN (L := L.take i) (fun xt hx => hL xt (List.mem_of_mem_take hx))
    rwa [List.length_take, Nat.min_eq_left hi] at this
  have hM : ∀ i acc, i ≤ (L.map vsPairVal).length →
      acc = vsAccVal (vsInsertAll p (L.take i)) → acc.wt ≤ 250 * (N + 1) ^ 3 := by
    rintro i acc hi rfl
    rw [List.length_map] at hi
    exact wt_vsAccVal_le hpN (by omega) (hfit i hi)
  have hg : ∀ i acc (hi : i < (L.map vsPairVal).length),
      acc = vsAccVal (vsInsertAll p (L.take i)) →
      FunAll P (b + 3) (.list [.nat p, acc, (L.map vsPairVal)[i]]) (fun w cost =>
        w = vsAccVal (vsInsertAll p (L.take (i + 1))) ∧ cost ≤ 2 * 10 ^ 7 * (N + 1) ^ 4 + 100) := by
    rintro i acc hi rfl
    rw [List.length_map] at hi
    obtain ⟨h1, h2, h3⟩ := hL L[i] (List.getElem_mem hi)
    rw [List.getElem_map, vsInsertAll_take_succ p L i hi]
    exact vsAllStep_spec hst hin hp hpN h1 h2 h3 (by omega) (hfit i hi.le)
  refine ((foldl_spec hfl (c := .nat p) (acc0 := vsAccVal ([], [])) (M := 250 * (N + 1) ^ 3)
    (B := fun _ => 2 * 10 ^ 7 * (N + 1) ^ 4 + 100)
    (Inv := fun i acc => acc = vsAccVal (vsInsertAll p (L.take i))) (by simp [vsInsertAll])
    hM hg).mono fun w cost hw => ⟨?_, ?_⟩)
  · rw [hw.1, List.length_map, List.take_length]
  · have hc := hw.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map] at hc
    have wL := vs_wt_list_le_of (L.map vsPairVal) (c := 20 * (N + 1) ^ 2 + 6) (by
      simp only [List.mem_map, forall_exists_index, and_imp]
      rintro _ xt hx rfl
      have H := (hL xt hx).1
      exact wt_vsPairVal_le hpN H.hx H.ht H.lx H.lt)
    rw [List.length_map] at wL
    have k0 : L.length * (2 * (20 * (N + 1) ^ 2 + 6) + 1) ≤ N * (60 * (N + 1) ^ 2) :=
      Nat.mul_le_mul hLl (by omega)
    have k0' : N * (60 * (N + 1) ^ 2) ≤ 60 * (N + 1) ^ 3 := by
      have : (N + 1) ^ 3 = (N + 1) * (N + 1) ^ 2 := by ring
      rw [this]; nlinarith
    have w0 : (vsAccVal ([], [])).wt ≤ 20 := by decide
    have wp := wt_nat_le p
    have w3 := wt_list3_le (.nat p) (.list (L.map vsPairVal)) (vsAccVal ([], []))
    have ea : (vsInsertAllArg p L).wt =
      (Val.list [.nat p, .list (L.map vsPairVal), vsAccVal ([], [])]).wt := rfl
    have hS : L.length * (2 * 10 ^ 7 * (N + 1) ^ 4 + 100) ≤
        N * (2 * 10 ^ 7 * (N + 1) ^ 4 + 100) := Nat.mul_le_mul_right _ hLl
    have hk : loopModK * (L.length + 1) *
        ((Val.list [.nat p, .list (L.map vsPairVal), vsAccVal ([], [])]).wt + L.length +
          250 * (N + 1) ^ 3 + 1) ≤ 1000 * (N + 1) * (500 * (N + 1) ^ 4) :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
    have e5 : (N + 1) ^ 5 = (N + 1) * (N + 1) ^ 4 := by ring
    rw [e5]
    exact vsInsertAll_cost (Q5 := (N + 1) ^ 4) hLl hS hk hc (hN1.trans (hN2.trans hN3))

end GI.Impl
