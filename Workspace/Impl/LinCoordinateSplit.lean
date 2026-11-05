module

public import Workspace.Impl.LinCoordinateCollect
public import Workspace.Impl.LinIntRelations

@[expose] public section

/-! Convert the collected order/coefficient pairs to the relation assembler's input. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linCoordinateSplitStep : Expr :=
  mk2 (.snoc (.get (arg 2) (.nat 0)) (.get (.get (arg 0) (arg 1)) (.nat 0)))
    (.snoc (.get (arg 2) (.nat 1)) (.get (.get (arg 0) (arg 1)) (.nat 1)))

def linCoordinateSplitFuns (b : ℕ) : List Expr :=
  loopFuns b (.length (.var 0)) (mk2 .nil .nil) linCoordinateSplitStep

def linCoordinateSplitAcc (W t : ℕ) : ℕ := 100 * (W + t + 1) ^ 2
def linCoordinateSplitCost (W t : ℕ) : ℕ :=
  10000 * (t + 1) * (W + t + linCoordinateSplitAcc W t + 1)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
theorem linCoordinateSplit_spec {P : Program} {b t : ℕ}
    (h : P.HasAt b (linCoordinateSplitFuns b)) (e : Fin t → ℕ)
    (C : Matrix (Fin t) (Fin t) ℤ) :
    let a := Val.list ((List.finRange t).map fun i => .list [encInt (e i : ℤ), linVecVal (C i)])
    FunDet P b a (.list [linVecVal (fun i => (e i : ℤ)), encIntMatrix C])
      (linCoordinateSplitCost a.wt t) := by
  let es := (List.finRange t).map fun i => encInt (e i : ℤ)
  let cs := (List.finRange t).map fun i => linVecVal (C i)
  let rs := (List.finRange t).map fun i => Val.list [encInt (e i : ℤ), linVecVal (C i)]
  let a := Val.list rs
  let W := a.wt
  let acc (k : ℕ) := Val.list [.list (es.take k), .list (cs.take k)]
  have wr (i : Fin t) : (Val.list [encInt (e i : ℤ), linVecVal (C i)]).wt ≤ W :=
    (wt_le_wt_list (vs := rs) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)).le
  have we (i : Fin t) : (encInt (e i : ℤ)).wt ≤ W :=
    (wt_le_wt_list (vs := [encInt (e i : ℤ), linVecVal (C i)]) (by simp)).le.trans (wr i)
  have wc (i : Fin t) : (linVecVal (C i)).wt ≤ W :=
    (wt_le_wt_list (vs := [encInt (e i : ℤ), linVecVal (C i)]) (by simp)).le.trans (wr i)
  have wacc (k : ℕ) : (acc k).wt ≤ linCoordinateSplitAcc W t := by
    have he := linWtList (vs := es.take k) (B := W) (by
      intro v hv; obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hv); exact we i)
    have hc := linWtList (vs := cs.take k) (B := W) (by
      intro v hv; obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hv); exact wc i)
    have hl₁ : (es.take k).length ≤ t := by simp [es]
    have hl₂ : (cs.take k).length ≤ t := by simp [cs]
    have hw := wt_list2_le (.list (es.take k)) (.list (cs.take k))
    unfold linCoordinateSplitAcc
    dsimp only [acc]
    nlinarith [Nat.mul_le_mul_right W hl₁, Nat.mul_le_mul_right W hl₂]
  have dk := Det.length (Det.var' (P := P) (env := [a]) (i := 0) rfl)
  simp only [rs, List.length_map, List.length_finRange] at dk
  have dz := Det.mk2 (P := P) (env := [a]) Det.nil Det.nil
  have hn : (acc 0) = .list [.list [], .list []] := by simp [acc]
  have loop := loopFuns_spec h dk dz
    (Inv := fun k v => v = acc k)
    (Step := fun _ _ _ cost => cost ≤ 1100 * (W + t + linCoordinateSplitAcc W t + 1))
    hn.symm (fun k v hk hv => ?_)
  · refine loop.mono fun out cost ho => ?_
    obtain ⟨cl, hloop, hcost⟩ := ho
    obtain ⟨hout, hcl⟩ := hloop.le (D := fun _ => 1100 * (W + t + linCoordinateSplitAcc W t + 1))
      (E := 0) (M := linCoordinateSplitAcc W t) (by intros; omega)
      (fun k v _ hv => hv ▸ wacc k)
    have hes : es.length = t := by simp [es]
    have hcs : cs.length = t := by simp [cs]
    have hfinal : acc t = .list [linVecVal (fun i => (e i : ℤ)), encIntMatrix C] := by
      change Val.list [.list (es.take t), .list (cs.take t)] = .list [.list es, .list cs]
      rw [show es.take t = es by simpa only [hes] using (List.take_length (l := es)),
        show cs.take t = cs by simpa only [hcs] using (List.take_length (l := cs))]
    refine ⟨hout.trans hfinal, ?_⟩
    have wout := hout ▸ wacc t
    have wzero := wacc 0
    have wa := wt_list4_le a (.nat t) (.nat 0) (.list [.list [], .list []])
    have wi := wt_nat_le t
    have wn : (Val.nat 0).wt = 2 := by decide
    have wz : (Val.list [Val.list [], Val.list []]).wt = 17 := by decide
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_zero, Nat.add_zero,
      linCoordinateSplitCost, loopK] at hcl ⊢
    dsimp only [W, a, rs] at *
    generalize linCoordinateSplitAcc (Val.list ((List.finRange t).map fun i =>
      Val.list [encInt (e i : ℤ), linVecVal (C i)])).wt t = M at *
    nlinarith only [hcost, hcl, wa, wi, wout, wzero, wz, wn]
  · subst v
    let i : Fin t := ⟨k, hk⟩
    have darg (j : ℕ) {v : Val} (hv : [a, .nat k, acc k][j]? = some v) :=
      Det.arg' (P := P) (vs := [a, .nat k, acc k]) (rest := []) (j := j) hv
    have dr := Det.get' (darg 0 rfl) (darg 1 rfl) (show rs[k]? =
        some (.list [encInt (e i : ℤ), linVecVal (C i)]) by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hk)]; simp [i])
    have de := Det.get' (darg 2 rfl) (Det.nat 0) rfl
    have dc := Det.get' (darg 2 rfl) (Det.nat 1) rfl
    have step := Det.mk2 (Det.snoc de (Det.get' dr (Det.nat 0) rfl))
      (Det.snoc dc (Det.get' dr (Det.nat 1) rfl))
    have het : es.take (k + 1) = es.take k ++ [encInt (e i : ℤ)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp [es]; exact hk)]; simp [es, i]
    have hct : cs.take (k + 1) = cs.take k ++ [linVecVal (C i)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp [cs]; exact hk)]; simp [cs, i]
    refine step.post fun cost hcost => ⟨by dsimp only [acc]; rw [het, hct], ?_⟩
    have wa := wt_list3_le a (.nat k) (acc k)
    have wi := wt_nat_le k
    have wold := wacc k
    have wnew := wacc (k + 1)
    dsimp only [acc] at wnew
    rw [het, hct] at wnew
    have wes : (Val.list (es.take k)).wt < (acc k).wt := wt_le_wt_list (by simp [acc])
    have wcs : (Val.list (cs.take k)).wt < (acc k).wt := wt_le_wt_list (by simp [acc])
    have wes' : (Val.list (es.take k ++ [encInt (e i : ℤ)])).wt ≤ linCoordinateSplitAcc W t := by
      rw [← het]; exact (wt_le_wt_list (by simp [acc])).le.trans (wacc (k + 1))
    have wcs' : (Val.list (cs.take k ++ [linVecVal (C i)])).wt ≤ linCoordinateSplitAcc W t := by
      rw [← hct]; exact (wt_le_wt_list (by simp [acc])).le.trans (wacc (k + 1))
    have wr' := wr i
    have we' := we i
    have wc' := wc i
    change _ ≤ 1100 * (W + t + linCoordinateSplitAcc W t + 1)
    dsimp only [W, a, acc] at *
    omega

end GI.Impl
