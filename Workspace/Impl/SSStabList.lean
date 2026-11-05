module

public import Workspace.Impl.SSOrderCnt

@[expose] public section

/-!
# Listing the entries of the high levels

`ssStabStepF` appends the entry of slot `k₀ n + q` to a list when the slot is filled
(`ssStabStepF_spec`). Iterated over `q < m` it lists `ssStabList T k₀ m` (`ssStabLoop_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

theorem ssStabList_succ (T : List (SsSlot n)) (k0 q : ℕ) :
    ssStabList T k0 (q + 1) =
      ssStabList T k0 q ++ (((T[k0 * n + q]?).join).map Prod.fst).toList := by
  unfold ssStabList
  rw [List.range_succ, List.filterMap_append]
  cases h : ((T[k0 * n + q]?).join).map Prod.fst <;> simp [h]

/-- The listed entries are small. -/
theorem ssSmall_stabList (T : List (SsSlot n)) (k0 q : ℕ) {Z : ℕ}
    (hZ : q * (2 * n + 3) + 3 ≤ Z) (hn : 2 * n + 3 ≤ Z) :
    SsSmall Z (.list ((ssStabList T k0 q).map encPerm)) := by
  refine ssSmall_list_of (B := 2 * n + 3) (fun v hv => ?_) (fun v hv => ?_) ?_
  · obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hv; rw [size_encPerm]
  · obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hv; exact ssSmall_encPerm σ hn
  · rw [List.length_map]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_right _ (length_ssStabList T k0 q)) 3).trans hZ

/-- One listing step: on `[[T, off], q, acc]`, append the entry of slot `off + q` if it is
filled. -/
def ssStabStepF : Expr :=
  .letE (.get (.get (arg 0) (.nat 0)) (.arith .add (.get (arg 0) (.nat 1)) (arg 1)))
    (.ite (.length (.var 1)) (.snoc (arg 2) (.get (.var 1) (.nat 0))) (arg 2))

theorem ss_small_cost {k X W : ℕ} (hk : k ≤ 50) (hW : W = 40 * X + 50) :
    k * (W + 1) + 0 ≤ 3000 * (X + 1) := by
  have := Nat.mul_le_mul_right (W + 1) hk
  omega

/-- **One listing step.** -/
theorem ssStabStepF_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some ssStabStepF)
    {T : List (SsSlot n)} {k0 q X : ℕ} (hidx : k0 * n + q < T.length)
    (hT : (ssEncTab T).wt ≤ X) (hX : k0 * n + q + 2 ≤ X)
    (hacc : (Val.list ((ssStabList T k0 q).map encPerm)).wt ≤ X)
    (hacc' : (Val.list ((ssStabList T k0 (q + 1)).map encPerm)).wt ≤ X) :
    FunDet P f (.list [.list [ssEncTab T, .nat (k0 * n)], .nat q,
        .list ((ssStabList T k0 q).map encPerm)])
      (.list ((ssStabList T k0 (q + 1)).map encPerm)) (3000 * (X + 1)) := by
  have hnw : ∀ m, m + 2 ≤ X → (Val.nat m).wt ≤ X := fun m h => (wt_nat_le m).trans h
  set L := (ssStabList T k0 q).map encPerm with hL
  have hc : (Val.list [ssEncTab T, .nat (k0 * n)]).wt ≤ 4 * X + 6 :=
    st_wt_list2 hT (hnw _ (by omega))
  have ha : (Val.list [.list [ssEncTab T, .nat (k0 * n)], .nat q, .list L]).wt ≤
      6 * (4 * X + 6) + 7 :=
    st_wt_list3 hc ((hnw q (by omega)).trans (by omega)) (hacc.trans (by omega))
  have hsucc := ssStabList_succ T k0 q
  rw [List.getElem?_eq_getElem hidx, Option.join_some] at hsucc
  have hsw : (ssEncSlot (T[k0 * n + q]'hidx)).wt < (ssEncTab T).wt :=
    wt_le_wt_list (List.mem_map_of_mem (List.getElem_mem hidx))
  have hget : (T.map ssEncSlot)[k0 * n + q]? = some (ssEncSlot (T[k0 * n + q]'hidx)) := by
    simp [hidx]
  set W := 40 * X + 50 with hW
  clear_value W
  set a := Val.list [.list [ssEncTab T, .nat (k0 * n)], .nat q, .list L] with hadef
  have haW : a.wt ≤ W := by omega
  have dc : StDC P [a] (arg 0) (.list [ssEncTab T, .nat (k0 * n)]) 3 0 W :=
    StDC.arg rfl haW (by omega) (by omega)
  have dT := StDC.get (x := 0) (v := ssEncTab T) dc (StDC.nat 0 (by omega)) rfl (by omega)
  have doff := StDC.get (x := 1) (v := .nat (k0 * n)) dc (StDC.nat 1 (by omega)) rfl
    ((hnw _ (by omega)).trans (by omega))
  have dq : StDC P [a] (arg 1) (.nat q) 3 0 W := StDC.arg rfl haW (by omega)
    ((hnw q (by omega)).trans (by omega))
  have di := StDC.arith (op := .add) (z := k0 * n + q) doff dq rfl
    ((hnw _ (by omega)).trans (by omega))
  have ds := StDC.get (vs := T.map ssEncSlot) (x := k0 * n + q) dT di hget (by omega)
  have dacc : ∀ v, StDC P [a, v] (arg 2) (.list L) 3 0 W := fun v =>
    StDC.arg rfl haW (by omega) (hacc.trans (by omega))
  rw [hsucc] at hacc' ⊢
  generalize T[k0 * n + q]'hidx = s at hsw ds hacc' ⊢
  cases s with
  | none =>
    simp only [Option.map_none, Option.toList_none, List.append_nil] at hacc' ⊢
    rw [show ssEncSlot (none : SsSlot n) = .list [] from rfl] at ds hsw
    have hnil : (Val.list []).wt ≤ W := by omega
    have dv : StDC P [a, Val.list []] (.var 1) (.list []) 1 0 W := StDC.var' rfl hnil
    have dl := StDC.length (vs := []) dv (by simp only [List.length_nil]; omega)
    exact StDC.funDet hf (StDC.letE ds (StDC.ite (nt := 0) (Et := 0) dl
      (fun h => absurd rfl h) (fun _ => dacc _) (hacc.trans (by omega)))
      (hacc.trans (by omega))) (ss_small_cost (by norm_num) hW)
  | some e =>
    simp only [Option.map_some, Option.toList_some, List.map_append, List.map_cons,
      List.map_nil] at hacc' ⊢
    have hS : ssEncSlot (some e) = .list [encPerm e.1, .nat e.2] := rfl
    rw [hS] at ds hsw
    have hpw : (encPerm e.1).wt < (Val.list [encPerm e.1, .nat e.2]).wt :=
      wt_le_wt_list (by simp)
    have dv : StDC P [a, .list [encPerm e.1, .nat e.2]] (.var 1)
        (.list [encPerm e.1, .nat e.2]) 1 0 W := StDC.var' rfl (by omega)
    have dl := StDC.length dv (by simp; omega)
    have dg := StDC.get (x := 0) (v := encPerm e.1) dv (StDC.nat 0 (by omega)) rfl (by omega)
    have dsn := StDC.snoc (dacc _) dg (hacc'.trans (by omega))
    exact StDC.funDet hf (StDC.letE ds (StDC.ite (ne := 0) (Ee := 0) dl
      (fun _ => dsn) (fun h => absurd h (by simp)) (hacc'.trans (by omega)))
      (hacc'.trans (by omega))) (ss_small_cost (by norm_num) hW)

theorem ss_stab_loop_cost {m X A c : ℕ}
    (hc : c ≤ m * (3000 * (X + 1)) + 1000 * (m + 1) * (A + m + X + 1)) (hA : A ≤ 36 * X + 49)
    (hm : m ≤ X) : c ≤ 10 ^ 5 * (X + 1) ^ 2 := by
  have h1 : m * (3000 * (X + 1)) ≤ (X + 1) * (3000 * (X + 1)) := Nat.mul_le_mul_right _ (by omega)
  have h2 : 1000 * (m + 1) * (A + m + X + 1) ≤ 1000 * (X + 1) * (50 * (X + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e : (X + 1) * (3000 * (X + 1)) + 1000 * (X + 1) * (50 * (X + 1)) = 53000 * (X + 1) ^ 2 := by
    ring
  rw [Nat.mul_assoc] at h2 hc
  omega

/-- **Listing the entries of the slots `k₀ n + q`, `q < m`.** -/
theorem ssStabLoop_spec {P : Program} {b : ℕ} (hit : P.HasAt b (iterFuns b (b + 3)))
    (hst : P.funs[b + 3]? = some ssStabStepF) {T : List (SsSlot n)} {k0 m X : ℕ}
    (hidx : k0 * n + m ≤ T.length) (hT : (ssEncTab T).wt ≤ X) (hX : k0 * n + m + 2 ≤ X)
    (hL : ∀ q ≤ m, (Val.list ((ssStabList T k0 q).map encPerm)).wt ≤ X) :
    FunDet P b (.list [.list [ssEncTab T, .nat (k0 * n)], .nat m, .list []])
      (.list ((ssStabList T k0 m).map encPerm)) (10 ^ 5 * (X + 1) ^ 2) := by
  have hnw : ∀ j, j + 2 ≤ X → (Val.nat j).wt ≤ X := fun j h => (wt_nat_le j).trans h
  have hc : (Val.list [ssEncTab T, .nat (k0 * n)]).wt ≤ 4 * X + 6 :=
    st_wt_list2 hT (hnw _ (by omega))
  have h0 := hL 0 (Nat.zero_le _)
  have e0 : ssStabList T k0 0 = [] := rfl
  rw [e0, List.map_nil] at h0
  have ha : (Val.list [.list [ssEncTab T, .nat (k0 * n)], .nat m, .list []]).wt ≤
      36 * X + 49 := by
    have := st_wt_list3 hc ((hnw m (by omega)).trans (by omega)) (h0.trans (by omega))
    omega
  refine (iter_spec hit (Inv := fun q acc => acc = .list ((ssStabList T k0 q).map encPerm))
    (M := X) (B := fun _ => 3000 * (X + 1)) (by rfl) (fun q acc hq h => by rw [h]; exact hL q hq)
    (fun q acc hq h => by
      subst h
      exact FunAll.mono (ssStabStepF_spec hst (by omega) hT (by omega) (hL q hq.le)
        (hL (q + 1) hq)) fun w c ⟨hw, hc⟩ => ⟨hw, hc⟩)).mono fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
  unfold loopModK at hc
  exact ss_stab_loop_cost hc ha (by omega)

end GI.Impl
