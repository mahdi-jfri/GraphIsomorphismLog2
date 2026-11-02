import Workspace.Impl.SSWrapProg

/-!
# Counting the filled slots of a level

`ssCntStepF` adds one to a counter when slot `k n + j` of the table is filled
(`ssCntStepF_spec`). Iterated over `j < n`, it counts the filled slots of level `k`
(`ssCntLoop_spec`), which is `ssCnt T k` (`ssCnt_eq`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The number of filled slots `k n + q`, `q < j`. -/
def ssCntL (T : List (SsSlot n)) (k j : ℕ) : ℕ :=
  ((List.range j).filter fun q => ((T[k * n + q]?).join).isSome).length

theorem ssCntL_succ (T : List (SsSlot n)) (k j : ℕ) :
    ssCntL T k (j + 1) = ssCntL T k j + if ((T[k * n + j]?).join).isSome then 1 else 0 := by
  unfold ssCntL
  rw [List.range_succ, List.filter_append, List.length_append]
  split_ifs with h <;> simp [h]

theorem ssCntL_le (T : List (SsSlot n)) (k j : ℕ) : ssCntL T k j ≤ j :=
  (List.length_filter_le _ _).trans (by simp)

theorem ss_slot_len (s : SsSlot n) :
    ∃ vs, ssEncSlot s = .list vs ∧ vs.length = if s.isSome then 2 else 0 := by
  cases s <;> simp [ssEncSlot]

/-- One counting step: on `[[n, T, k], j, acc]`, add one if slot `k n + j` is filled. -/
def ssCntStepF : Expr :=
  .arith .add (arg 2) (.arith .lt (.nat 0)
    (.length (.get (.get (arg 0) (.nat 1))
      (.arith .add (.arith .mul (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 0))) (arg 1)))))

theorem ss_cnt_step_cost {X W : ℕ} (hW : W = 40 * X + 50) : 28 * (W + 1) + 0 ≤ 2000 * (X + 1) := by
  omega

/-- **One counting step.** -/
theorem ssCntStepF_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some ssCntStepF)
    {T : List (SsSlot n)} {k j acc X : ℕ} (hidx : k * n + j < T.length)
    (hT : (ssEncTab T).wt ≤ X) (hX : k * n + j + k + acc + n + 3 ≤ X) :
    FunDet P f (.list [.list [.nat n, ssEncTab T, .nat k], .nat j, .nat acc])
      (.nat (acc + if ((T[k * n + j]?).join).isSome then 1 else 0)) (2000 * (X + 1)) := by
  have hnw : ∀ m, m + 2 ≤ X → (Val.nat m).wt ≤ X := fun m h => (wt_nat_le m).trans h
  have hc : (Val.list [.nat n, ssEncTab T, .nat k]).wt ≤ 6 * X + 7 :=
    st_wt_list3 (hnw n (by omega)) hT (hnw k (by omega))
  have ha : (Val.list [.list [.nat n, ssEncTab T, .nat k], .nat j, .nat acc]).wt ≤
      6 * (6 * X + 7) + 7 :=
    st_wt_list3 hc ((hnw j (by omega)).trans (by omega)) ((hnw acc (by omega)).trans (by omega))
  set W := 40 * X + 50 with hW
  clear_value W
  set a := Val.list [.list [.nat n, ssEncTab T, .nat k], .nat j, .nat acc] with hadef
  have haW : a.wt ≤ W := by omega
  have dc : StDC P [a] (arg 0) (.list [.nat n, ssEncTab T, .nat k]) 3 0 W :=
    StDC.arg rfl haW (by omega) (by omega)
  have dn := StDC.get (x := 0) (v := .nat n) dc (StDC.nat 0 (by omega)) rfl
    ((hnw n (by omega)).trans (by omega))
  have dT := StDC.get (x := 1) (v := ssEncTab T) dc (StDC.nat 1 (by omega)) rfl (by omega)
  have dk := StDC.get (x := 2) (v := .nat k) dc (StDC.nat 2 (by omega)) rfl
    ((hnw k (by omega)).trans (by omega))
  have dm := StDC.arith (op := .mul) (z := k * n) dk dn rfl
    ((hnw _ (by omega)).trans (by omega))
  have dj : StDC P [a] (arg 1) (.nat j) 3 0 W := StDC.arg rfl haW (by omega)
    ((hnw j (by omega)).trans (by omega))
  have di := StDC.arith (op := .add) (z := k * n + j) dm dj rfl
    ((hnw _ (by omega)).trans (by omega))
  obtain ⟨vs, hvs, hlen⟩ := ss_slot_len (T[k * n + j]'hidx)
  have hsw : (ssEncSlot (T[k * n + j]'hidx)).wt < (ssEncTab T).wt :=
    wt_le_wt_list (List.mem_map_of_mem (List.getElem_mem hidx))
  rw [hvs] at hsw
  have ds := StDC.get (vs := T.map ssEncSlot) (x := k * n + j) (v := .list vs) dT di
    (by simp [hidx, hvs]) (by omega)
  have dl := StDC.length ds (by rw [hlen]; split_ifs <;> omega)
  have hsome : ((T[k * n + j]?).join).isSome = ((T[k * n + j]'hidx)).isSome := by
    rw [List.getElem?_eq_getElem hidx, Option.join_some]
  have dlt := StDC.arith (op := .lt) (z := if ((T[k * n + j]?).join).isSome then 1 else 0)
    (StDC.nat 0 (by omega)) dl (by
      show (if 0 < vs.length then 1 else 0) = _
      rw [hlen, hsome]; split_ifs <;> simp_all)
    ((hnw _ (by split_ifs <;> omega)).trans (by omega))
  have dacc : StDC P [a] (arg 2) (.nat acc) 3 0 W := StDC.arg rfl haW (by omega)
    ((hnw acc (by omega)).trans (by omega))
  have dadd := StDC.arith (op := .add)
    (z := acc + if ((T[k * n + j]?).join).isSome then 1 else 0) dacc dlt rfl
    ((hnw _ (by split_ifs <;> omega)).trans (by omega))
  exact StDC.funDet hf dadd (ss_cnt_step_cost hW)

theorem ss_cnt_loop_cost {n X A c : ℕ}
    (hc : c ≤ n * (2000 * (X + 1)) + 1000 * (n + 1) * (A + n + X + 1)) (hA : A ≤ 36 * X + 49)
    (hn : n ≤ X) : c ≤ 10 ^ 5 * (X + 1) ^ 2 := by
  have h1 : n * (2000 * (X + 1)) ≤ (X + 1) * (2000 * (X + 1)) := Nat.mul_le_mul_right _ (by omega)
  have h2 : 1000 * (n + 1) * (A + n + X + 1) ≤ 1000 * (X + 1) * (50 * (X + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e : (X + 1) * (2000 * (X + 1)) + 1000 * (X + 1) * (50 * (X + 1)) = 52000 * (X + 1) ^ 2 := by
    ring
  rw [Nat.mul_assoc] at h2 hc
  omega

theorem ss_idx_lt {k j : ℕ} (hk : k < n) (hj : j < n) : k * n + j < n * n :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk)

/-- **Counting the filled slots of level `k`.** -/
theorem ssCntLoop_spec {P : Program} {b : ℕ} (hit : P.HasAt b (iterFuns b (b + 3)))
    (hst : P.funs[b + 3]? = some ssCntStepF) {T : List (SsSlot n)} {k X : ℕ} (hk : k < n)
    (hTl : T.length = n * n) (hT : (ssEncTab T).wt ≤ X) (hX : n * n + 3 * n + 3 ≤ X) :
    FunDet P b (.list [.list [.nat n, ssEncTab T, .nat k], .nat n, .nat 0]) (.nat (ssCnt T k))
      (10 ^ 5 * (X + 1) ^ 2) := by
  have hnw : ∀ m, m + 2 ≤ X → (Val.nat m).wt ≤ X := fun m h => (wt_nat_le m).trans h
  have hc : (Val.list [.nat n, ssEncTab T, .nat k]).wt ≤ 6 * X + 7 :=
    st_wt_list3 (hnw n (by omega)) hT (hnw k (by omega))
  have ha : (Val.list [.list [.nat n, ssEncTab T, .nat k], .nat n, .nat 0]).wt ≤
      36 * X + 49 := by
    have := st_wt_list3 hc ((hnw n (by omega)).trans (by omega))
      ((hnw 0 (by omega)).trans (by omega))
    omega
  refine (iter_spec hit (Inv := fun j acc => acc = .nat (ssCntL T k j)) (M := X)
    (B := fun _ => 2000 * (X + 1)) (by simp [ssCntL]) (fun j acc hj h => by
      rw [h]; exact hnw _ (by have := ssCntL_le T k j; omega))
    (fun j acc hj h => by
      subst h
      have hidx := ss_idx_lt hk hj
      refine FunAll.mono (ssCntStepF_spec hst (by omega) hT
        (by have := ssCntL_le T k j; omega)) fun w c ⟨hw, hc⟩ => ⟨?_, hc⟩
      show _ = _
      rw [hw, ssCntL_succ])).mono fun w c ⟨hw, hc⟩ => ⟨?_, ?_⟩
  · rw [hw, ssCnt_eq]; rfl
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    unfold loopModK at hc
    exact ss_cnt_loop_cost hc ha (by omega)

end GI.Impl
