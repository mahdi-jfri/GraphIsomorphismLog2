import Workspace.Impl.VsPOrb

/-!
# A basis of the span of the orbit keys

`vsPBasis r O` runs through the pairs `(z, κ)` and keeps `z` when `κ` is not in the span of the
keys kept so far (insertion into echelon rows over `𝔽_r`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

/-- One step of the greedy basis. -/
def vsPGStep {n : ℕ} (r : ℕ) (acc : List VsRow × List (Perm (Fin n))) (p : Perm (Fin n) × List ℕ) :
    List VsRow × List (Perm (Fin n)) :=
  if vsNzIdx (vsSift r acc.1 (p.2, [])).1 < (vsSift r acc.1 (p.2, [])).1.length then
    (acc.1 ++ [vsNewRow r (vsSift r acc.1 (p.2, [])) (vsNzIdx (vsSift r acc.1 (p.2, [])).1)],
      acc.2 ++ [p.1])
  else acc

/-- The greedy basis. -/
def vsPBasis {n : ℕ} (r : ℕ) (O : List (Perm (Fin n) × List ℕ)) :
    List VsRow × List (Perm (Fin n)) :=
  O.foldl (vsPGStep r) ([], [])

/-- The value of an accumulator. -/
def vsPGV {n : ℕ} (acc : List VsRow × List (Perm (Fin n))) : Val :=
  .list [.list (acc.1.map VsRow.val), .list (acc.2.map encPerm)]

/-- The step, on `[r, acc, (z, κ)]`. -/
def vsPGStepE (ins : ℕ) : Expr :=
  .letE (.call ins (mk3 (arg 0) (.get (arg 1) (.nat 0)) (mk2 (.get (arg 2) (.nat 1)) .nil)))
    (.ite (.get (.var 1) (.nat 0))
      (mk2 (.get (.var 1) (.nat 1)) (.snoc (.get (arg 1) (.nat 1)) (.get (arg 2) (.nat 0))))
      (arg 1))

theorem vsPGStep_fits {n : ℕ} {r N k : ℕ} (hr : 0 < r) (hrN : r ≤ N) {acc : List VsRow × List (Perm (Fin n))}
    (hacc : ∀ x ∈ acc.1, VsRowFits N k 0 x) {p : Perm (Fin n) × List ℕ}
    (hp : (∀ x ∈ p.2, x < r) ∧ p.2.length = k) (hk : k ≤ N) :
    ∀ x ∈ (vsPGStep r acc p).1, VsRowFits N k 0 x := by
  unfold vsPGStep
  split_ifs with h
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hacc x hx
    · simp at hx; subst hx
      have hP : VsPairFits r N (p.2, []) := ⟨hp.1, by simp, by rw [hp.2]; exact hk, by simp⟩
      have hS := vsSift_fits hr acc.1 hP
      obtain ⟨hl1, hl2⟩ := vsSift_length r acc.1 (p.2, [])
      have := vsNewRow_fits hr hrN hS h
      rw [hl1, hl2] at this
      simpa [hp.2] using this
  · exact hacc

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

set_option maxHeartbeats 4000000 in
theorem vsPGStep_spec {P : Program} {f ins : ℕ} (hf : P.funs[f]? = some (vsPGStepE ins))
    (hins : P.HasAt ins (vsInsertFuns ins)) {n r N k : ℕ} (hn : n ≤ N) (hr : 0 < r) (hrN : r ≤ N)
    (hk : k ≤ N) {acc : List VsRow × List (Perm (Fin n))}
    (hacc : ∀ x ∈ acc.1, VsRowFits N k 0 x) (hal : acc.1.length ≤ N) (hbl : acc.2.length ≤ N)
    {p : Perm (Fin n) × List ℕ} (hp : (∀ x ∈ p.2, x < r) ∧ p.2.length = k) :
    FunDet P f (.list [.nat r, vsPGV acc, vsPPV p]) (vsPGV (vsPGStep r acc p))
      (10 ^ 8 * (N + 1) ^ 4) := by
  set vs := [Val.nat r, vsPGV acc, vsPPV p]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 : Det P [.list vs] (arg 1) (.list [.list (acc.1.map VsRow.val), .list (acc.2.map encPerm)]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have a2 : Det P [.list vs] (arg 2) (.list [encPerm p.1, natList p.2]) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have drows := Det.get' a1 (Det.nat 0) (show [Val.list (acc.1.map VsRow.val),
    .list (acc.2.map encPerm)][0]? = some (.list (acc.1.map VsRow.val)) from rfl)
  have dkey := Det.get' a2 (Det.nat 1) (show [encPerm p.1, natList p.2][1]? = some (natList p.2)
    from rfl)
  have dpair := Det.mk2 dkey (Det.nil (P := P) (env := [.list vs]))
  have hP : VsPairFits r N (p.2, []) := ⟨hp.1, by simp, by rw [hp.2]; exact hk, by simp⟩
  have hacc' : ∀ x ∈ acc.1, VsRowFits N (p.2, ([] : List ℕ)).1.length
      (p.2, ([] : List ℕ)).2.length x := by
    intro x hx; simp only [hp.2, List.length_nil]; exact hacc x hx
  have dI := Det.call (Det.mk3 a0 drows dpair) (vsInsert_spec hins hr hrN hP hacc' hal)
  apply FunDet.intro hf
  set y := vsSift r acc.1 (p.2, [])
  -- weights
  have hp2 : ∀ g : Perm (Fin n), (encPerm g).wt ≤ 4 * (N + 1) ^ 2 := fun g =>
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have wperms : ∀ l : List (Perm (Fin n)), l.length ≤ N + 1 →
      (Val.list (l.map encPerm)).wt ≤ 20 * (N + 1) ^ 3 := by
    intro l hl
    have h1 := vs_wt_list_le_of (l.map encPerm) (c := 4 * (N + 1) ^ 2) (by
      intro v hv; obtain ⟨g, -, rfl⟩ := List.mem_map.mp hv; exact hp2 g)
    rw [List.length_map] at h1
    have : l.length * (2 * (4 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (9 * (N + 1) ^ 2) :=
      Nat.mul_le_mul hl (by have := Nat.one_le_pow 2 (N + 1) (by omega); omega)
    have e : (N + 1) * (9 * (N + 1) ^ 2) = 9 * (N + 1) ^ 3 := by ring
    have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have wR := wt_vsRows_le hacc (by omega)
  have wB := wperms acc.2 (by omega)
  have wB' := wperms (acc.2 ++ [p.1]) (by simp; omega)
  have wk := wt_natList_le_sq (B := N) (fun x hx => (hp.1 x hx).le.trans hrN) (by rw [hp.2]; exact hk)
  have w1 := hp2 p.1
  have wpv := wt_list2_le (encPerm p.1) (natList p.2)
  have wacc := wt_list2_le (.list (acc.1.map VsRow.val)) (.list (acc.2.map encPerm))
  have wvs := wt_list3_le (.nat r) (vsPGV acc) (vsPPV p)
  have evs : (Val.list vs).wt = (Val.list [.nat r, vsPGV acc, vsPPV p]).wt := rfl
  have eacc : (vsPGV acc).wt = (Val.list [.list (acc.1.map VsRow.val),
    .list (acc.2.map encPerm)]).wt := rfl
  have epv : (vsPPV p).wt = (Val.list [encPerm p.1, natList p.2]).wt := rfl
  have wr := wt_nat_le r
  have w2 := wt_list2_le (natList p.2) (.list [])
  have w3 := wt_list3_le (.nat r) (.list (acc.1.map VsRow.val)) (.list [natList p.2, .list []])
  have hS := vsSift_fits hr acc.1 (show VsPairFits r N (p.2, []) from hP)
  have wy := wt_vsPairVal_le hrN hS.hx hS.ht hS.lx hS.lt
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have wn0 : (Val.list []).wt ≤ 5 := by simp
  by_cases hc : vsNzIdx y.1 < y.1.length
  · have ev : vsInsertVal r acc.1 (p.2, []) =
        .list [.nat 1, .list ((acc.1 ++ [vsNewRow r y (vsNzIdx y.1)]).map VsRow.val)] := by
      unfold vsInsertVal; exact if_pos hc
    have hsv : vsPGStep r acc p = (acc.1 ++ [vsNewRow r y (vsNzIdx y.1)], acc.2 ++ [p.1]) := by
      unfold vsPGStep; exact if_pos hc
    rw [ev] at dI
    set V := Val.list [.nat 1, .list ((acc.1 ++ [vsNewRow r y (vsNzIdx y.1)]).map VsRow.val)]
    have b1 : Det P [Val.list vs, V] (arg 1)
        (.list [.list (acc.1.map VsRow.val), .list (acc.2.map encPerm)]) _ :=
      Det.arg' (P := P) (vs := vs) (rest := [V]) (j := 1) rfl
    have b2 : Det P [Val.list vs, V] (arg 2) (.list [encPerm p.1, natList p.2]) _ :=
      Det.arg' (P := P) (vs := vs) (rest := [V]) (j := 2) rfl
    have v1 := Det.var' (P := P) (env := [Val.list vs, V]) (i := 1) rfl
    have d0 := Det.get' v1 (Det.nat 0) (show [Val.nat 1, .list ((acc.1 ++ [vsNewRow r y (vsNzIdx y.1)]).map
      VsRow.val)][0]? = some (.nat 1) from rfl)
    have d1 := Det.get' v1 (Det.nat 1) (show [Val.nat 1, .list ((acc.1 ++ [vsNewRow r y (vsNzIdx y.1)]).map
      VsRow.val)][1]? = some (.list ((acc.1 ++ [vsNewRow r y (vsNzIdx y.1)]).map VsRow.val)) from rfl)
    have dl := Det.get' b1 (Det.nat 1) (show [Val.list (acc.1.map VsRow.val),
      .list (acc.2.map encPerm)][1]? = some (.list (acc.2.map encPerm)) from rfl)
    have dz := Det.get' b2 (Det.nat 0) (show [encPerm p.1, natList p.2][0]? = some (encPerm p.1)
      from rfl)
    have dsn := Det.snoc dl dz
    have dT := Det.mk2 d1 dsn
    rw [hsv]
    have eT : Val.list [Val.list ((acc.1 ++ [vsNewRow r y (vsNzIdx y.1)]).map VsRow.val),
        Val.list (acc.2.map encPerm ++ [encPerm p.1])] =
        vsPGV ((acc.1 ++ [vsNewRow r y (vsNzIdx y.1)], acc.2 ++ [p.1]) :
          List VsRow × List (Perm (Fin n))) := by simp [vsPGV]
    rw [eT] at dT
    refine (Det.letE dI (Det.ite_pos d0 one_ne_zero dT)).mono ?_
    have hfit' := vsPGStep_fits hr hrN hacc hp hk
    rw [hsv] at hfit'
    have wR' := wt_vsRows_le hfit' (by simp; omega)
    have wnew := wt_list2_le (.list ((acc.1 ++ [vsNewRow r y (vsNzIdx y.1)]).map VsRow.val))
      (.list ((acc.2 ++ [p.1]).map encPerm))
    have eG : (vsPGV ((acc.1 ++ [vsNewRow r y (vsNzIdx y.1)], acc.2 ++ [p.1]) :
        List VsRow × List (Perm (Fin n)))).wt = (Val.list [.list ((acc.1 ++
          [vsNewRow r y (vsNzIdx y.1)]).map VsRow.val), .list ((acc.2 ++ [p.1]).map encPerm)]).wt := rfl
    have eapp : Val.list (acc.2.map encPerm ++ [encPerm p.1]) = Val.list ((acc.2 ++ [p.1]).map encPerm) := by
      simp
    have w1' := wt_nat_le 1
    have wv := wt_list2_le (.nat 1) (.list ((acc.1 ++ [vsNewRow r y (vsNzIdx y.1)]).map VsRow.val))
    have eV : V.wt = (Val.list [.nat 1, .list ((acc.1 ++ [vsNewRow r y (vsNzIdx y.1)]).map
      VsRow.val)]).wt := rfl
    have ews : (Val.list (acc.2.map encPerm ++ [encPerm p.1])).wt =
        (Val.list ((acc.2 ++ [p.1]).map encPerm)).wt := by rw [eapp]
    have q5 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    linarith
  · have ev : vsInsertVal r acc.1 (p.2, []) = .list [.nat 0, natList y.2] := by
      unfold vsInsertVal; exact if_neg hc
    have hsv : vsPGStep r acc p = acc := by unfold vsPGStep; exact if_neg hc
    rw [ev] at dI
    set V := Val.list [.nat 0, natList y.2]
    have b1 : Det P [Val.list vs, V] (arg 1)
        (.list [.list (acc.1.map VsRow.val), .list (acc.2.map encPerm)]) _ :=
      Det.arg' (P := P) (vs := vs) (rest := [V]) (j := 1) rfl
    have v1 := Det.var' (P := P) (env := [Val.list vs, V]) (i := 1) rfl
    have d0 := Det.get' v1 (Det.nat 0) (show [Val.nat 0, natList y.2][0]? = some (.nat 0) from rfl)
    rw [hsv]
    refine (Det.letE dI (Det.ite_zero d0 b1)).mono ?_
    have eV : V.wt = (Val.list [.nat 0, natList y.2]).wt := rfl
    have wV := wt_list2_le (.nat 0) (natList y.2)
    have wy2 := wt_natList_le_sq (B := N) (fun x hx => (hS.ht x hx).le.trans hrN) hS.lt
    have w0 := wt_nat_le 0
    have q5 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    linarith

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

theorem vsPGStep_length {n r : ℕ} (acc : List VsRow × List (Perm (Fin n)))
    (p : Perm (Fin n) × List ℕ) :
    (vsPGStep r acc p).1.length ≤ acc.1.length + 1 ∧ (vsPGStep r acc p).2.length ≤ acc.2.length + 1 := by
  unfold vsPGStep; split_ifs <;> simp

theorem vsPBasis_take_inv {n r N k : ℕ} (hr : 0 < r) (hrN : r ≤ N) (hk : k ≤ N)
    {O : List (Perm (Fin n) × List ℕ)} (hO : ∀ p ∈ O, (∀ x ∈ p.2, x < r) ∧ p.2.length = k) :
    ∀ i, (∀ x ∈ ((O.take i).foldl (vsPGStep r) ([], [])).1, VsRowFits N k 0 x) ∧
      ((O.take i).foldl (vsPGStep r) ([], [])).1.length ≤ i ∧
      ((O.take i).foldl (vsPGStep r) ([], [])).2.length ≤ i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rcases Nat.lt_or_ge i O.length with hi | hi
    · rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      obtain ⟨ih1, ih2, ih3⟩ := ih
      refine ⟨vsPGStep_fits hr hrN ih1 (hO _ (List.getElem_mem hi)) hk, ?_, ?_⟩
      · have := (vsPGStep_length (r := r) ((O.take i).foldl (vsPGStep r) ([], [])) O[i]).1
        omega
      · have := (vsPGStep_length (r := r) ((O.take i).foldl (vsPGStep r) ([], [])) O[i]).2
        omega
    · rw [List.take_of_length_le (by omega)]
      have := ih; rw [List.take_of_length_le (by omega)] at this
      exact ⟨this.1, by omega, by omega⟩

/-- The cost of the basis. -/
def vsPBasisCost (N : ℕ) : ℕ := (N + 1) * (10 ^ 8 * (N + 1) ^ 4) + 10 ^ 7 * (N + 1) ^ 5

set_option maxHeartbeats 4000000 in
theorem vsPBasis_spec {P : Program} {b g ins : ℕ} (hb : P.HasAt b (foldlFuns b g))
    (hg : P.funs[g]? = some (vsPGStepE ins)) (hins : P.HasAt ins (vsInsertFuns ins))
    {n r N k : ℕ} (hn : n ≤ N) (hr : 0 < r) (hrN : r ≤ N) (hk : k ≤ N)
    {O : List (Perm (Fin n) × List ℕ)} (hO : ∀ p ∈ O, (∀ x ∈ p.2, x < r) ∧ p.2.length = k)
    (hOl : O.length ≤ N) :
    FunDet P b (.list [.nat r, .list (O.map vsPPV), vsPGV (([], []) : List VsRow × List (Perm (Fin n)))])
      (vsPGV (vsPBasis r O)) (vsPBasisCost N) := by
  have hinv := vsPBasis_take_inv hr hrN hk hO
  have hp2 : ∀ g : Perm (Fin n), (encPerm g).wt ≤ 4 * (N + 1) ^ 2 := fun g =>
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have wperms : ∀ l : List (Perm (Fin n)), l.length ≤ N + 1 →
      (Val.list (l.map encPerm)).wt ≤ 20 * (N + 1) ^ 3 := by
    intro l hl
    have h1 := vs_wt_list_le_of (l.map encPerm) (c := 4 * (N + 1) ^ 2) (by
      intro v hv; obtain ⟨g, -, rfl⟩ := List.mem_map.mp hv; exact hp2 g)
    rw [List.length_map] at h1
    have : l.length * (2 * (4 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (9 * (N + 1) ^ 2) :=
      Nat.mul_le_mul hl (by have := Nat.one_le_pow 2 (N + 1) (by omega); omega)
    have e : (N + 1) * (9 * (N + 1) ^ 2) = 9 * (N + 1) ^ 3 := by ring
    have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have hM : ∀ i acc, i ≤ (O.map vsPPV).length →
      acc = vsPGV ((O.take i).foldl (vsPGStep r) ([], [])) → acc.wt ≤ 300 * (N + 1) ^ 3 := by
    rintro i acc hi rfl
    rw [List.length_map] at hi
    obtain ⟨h1, h2, h3⟩ := hinv i
    have wR := wt_vsRows_le h1 (by omega)
    have wB := wperms ((O.take i).foldl (vsPGStep r) ([], [])).2 (by omega)
    have := wt_list2_le (.list (((O.take i).foldl (vsPGStep r) ([], [])).1.map VsRow.val))
      (.list (((O.take i).foldl (vsPGStep r) ([], [])).2.map encPerm))
    have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    show (Val.list [.list (((O.take i).foldl (vsPGStep r) ([], [])).1.map VsRow.val),
      .list (((O.take i).foldl (vsPGStep r) ([], [])).2.map encPerm)]).wt ≤ _
    omega
  have hstep : ∀ i acc (hi : i < (O.map vsPPV).length),
      acc = vsPGV ((O.take i).foldl (vsPGStep r) ([], [])) →
      FunAll P g (.list [.nat r, acc, (O.map vsPPV)[i]]) (fun w cost =>
        w = vsPGV ((O.take (i + 1)).foldl (vsPGStep r) ([], [])) ∧ cost ≤ 10 ^ 8 * (N + 1) ^ 4) := by
    rintro i acc hi rfl
    have hi' : i < O.length := by simpa using hi
    obtain ⟨h1, h2, h3⟩ := hinv i
    have e : (O.map vsPPV)[i] = vsPPV O[i] := by simp
    rw [e]
    refine FunAll.mono (vsPGStep_spec hg hins hn hr hrN hk h1 (by omega) (by omega)
      (hO _ (List.getElem_mem hi'))) fun w c hw => ⟨?_, hw.2⟩
    rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
      List.foldl_append]
    rfl
  have hf := foldl_spec hb (c := .nat r) (xs := O.map vsPPV) (acc0 := vsPGV (([], []) :
    List VsRow × List (Perm (Fin n)))) (Inv := fun i acc => acc = vsPGV ((O.take i).foldl
      (vsPGStep r) ([], []))) (M := 300 * (N + 1) ^ 3) (B := fun _ => 10 ^ 8 * (N + 1) ^ 4)
    (by simp) hM hstep
  refine FunAll.mono hf fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1, List.length_map, List.take_length]; rfl
  · have hc := hw.2
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map] at hc
    have h1 : O.length * (10 ^ 8 * (N + 1) ^ 4) ≤ (N + 1) * (10 ^ 8 * (N + 1) ^ 4) :=
      Nat.mul_le_mul_right _ (by omega)
    have wO := vsP_wt_pairs hn hOl (fun p hp => ⟨by rw [(hO p hp).2]; exact hk,
      fun x hx => ((hO p hp).1 x hx).le.trans hrN⟩)
    have wr := wt_nat_le r
    have w0 : (vsPGV (([], []) : List VsRow × List (Perm (Fin n)))).wt ≤ 20 := by
      simp only [vsPGV, List.map_nil]; decide
    have w3 := wt_list3_le (.nat r) (.list (O.map vsPPV)) (vsPGV (([], []) :
      List VsRow × List (Perm (Fin n))))
    have hl2 : loopModK * (O.length + 1) * ((Val.list [.nat r, .list (O.map vsPPV),
        vsPGV (([], []) : List VsRow × List (Perm (Fin n)))]).wt + O.length +
        300 * (N + 1) ^ 3 + 1) ≤ 10 ^ 7 * (N + 1) ^ 5 := by
      have q1 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
      have h2 : (Val.list [.nat r, .list (O.map vsPPV), vsPGV (([], []) :
          List VsRow × List (Perm (Fin n)))]).wt + O.length + 300 * (N + 1) ^ 3 + 1 ≤
          10000 * (N + 1) ^ 3 := by omega
      calc loopModK * (O.length + 1) * _ ≤ 1000 * (N + 1) * (10000 * (N + 1) ^ 3) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (by omega)) h2
        _ ≤ 10 ^ 7 * (N + 1) ^ 5 := by
          have : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
          nlinarith
    unfold vsPBasisCost
    omega

end GI.Impl
