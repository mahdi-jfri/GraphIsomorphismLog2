import Workspace.Lang.Prims.Reduce
import Workspace.Impl.GenNormPoly

/-! Polynomial subgroup inclusion and equality tests for arbitrary encoded
permutation generator lists. These normalize the orbit-color interface. -/
namespace GI.Impl
open GI.Cited GI.Lang

private noncomputable def linPermRead (n : ℕ) (v : Val) : Equiv.Perm (Fin n) := by
  classical
  exact if h : ∃ x : Equiv.Perm (Fin n), encPerm x = v then h.choose else 1

private theorem linPermRead_enc {n : ℕ} (x : Equiv.Perm (Fin n)) : linPermRead n (encPerm x) = x := by
  classical
  have hx : ∃ y : Equiv.Perm (Fin n), encPerm y = encPerm x := ⟨x, rfl⟩
  simp only [linPermRead, dif_pos hx]
  exact encPerm_injective hx.choose_spec

def linGroupMemberF (j : ℕ) : Expr := .prim j (mk2 (arg 0) (arg 1))
def linGroupLeF (all : ℕ) : Expr := .call all (mk2 (arg 1) (.get (arg 0) (.nat 1)))
def linGroupLeFuns (b j : ℕ) : List Expr :=
  [linGroupLeF (b + 1)] ++ allFuns (b + 1) (b + 4) ++ [linGroupMemberF j]

theorem linGroupLeFuns_length (b j : ℕ) : (linGroupLeFuns b j).length = 5 := rfl

noncomputable def linGroupMemberCost (h : Membership) (W : ℕ) : ℕ :=
  (membershipPrim h).boundSize (10 * (W + 1)) + 1000 * (W + 1)
noncomputable def linGroupLeCost (h : Membership) (W : ℕ) : ℕ :=
  100000 * (W * linGroupMemberCost h W + (W + 1) ^ 3 + 1)

private theorem linGroupLe_iff {n : ℕ} (gs hs : List (Equiv.Perm (Fin n))) :
    gens gs ≤ gens hs ↔ ∀ x ∈ (1 :: gs), x ∈ gens hs := by
  constructor
  · intro h x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (gens hs).one_mem
    · exact h (Subgroup.subset_closure hx)
  · intro h
    apply (Subgroup.closure_le _).mpr
    intro x hx
    exact h x (List.mem_cons_of_mem _ hx)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
open Classical in
theorem linGroupLe_spec (hm : Membership) {P : Program} {b j n : ℕ}
    (hp : P.HasAt b (linGroupLeFuns b j))
    (hj : P.prims[j]? = some (membershipPrim hm))
    (gs hs : List (Equiv.Perm (Fin n))) :
    FunDet P b (.list [encGroup gs, encGroup hs]) (boolVal (decide (gens gs ≤ gens hs)))
      (linGroupLeCost hm (Val.list [encGroup gs, encGroup hs]).wt) := by
  classical
  let a := Val.list [encGroup gs, encGroup hs]
  let W := a.wt
  let xs := (1 :: gs).map encPerm
  let q (v : Val) := decide (linPermRead n v ∈ gens hs)
  have wg : (encGroup gs).wt < W := wt_le_wt_list (by simp [a, W])
  have wh : (encGroup hs).wt < W := wt_le_wt_list (by simp [a, W])
  have wx : (Val.list xs).wt < W := (wt_le_wt_list
    (by simp [encGroup, encPerms, xs] : Val.list xs ∈ [.nat n, .list xs])).trans wg
  have hl : xs.length ≤ W := (length_lt_wt_list xs).le.trans wx.le
  have hmember := (hp.block (gs := [linGroupMemberF j]) 4 rfl).single
  have hall : P.HasAt (b + 1) (allFuns (b + 1) (b + 4)) := hp.block 1 rfl
  have hh : ∀ v ∈ xs, FunDet P (b + 4) (.list [encGroup hs, v]) (boolVal (q v)) (linGroupMemberCost hm W) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    have xv : (encPerm x).wt < W := (wt_le_wt_list (List.mem_map.mpr ⟨x, hx, rfl⟩)).trans wx
    have warg := wt_list2_le (encGroup hs) (encPerm x)
    have warg' : (Val.list [encGroup hs, encPerm x]).wt ≤ 10 * (W + 1) := by omega
    have hprim := (membershipPrim hm).bound_le ((Val.list [encGroup hs, encPerm x]).size_le_wt.trans warg')
    have dp := membership_call hm hj (Det.mk2
      (Det.arg' (P := P) (vs := [encGroup hs, encPerm x]) (rest := []) (j := 0) rfl)
      (Det.arg' (P := P) (vs := [encGroup hs, encPerm x]) (rest := []) (j := 1) rfl)) ⟨hs, rfl, rfl⟩
    apply FunAll.intro hmember
    refine dp.mono fun out cost ho => ⟨?_, ?_⟩
    · simp only [q, linPermRead_enc]
      rcases ho.1 with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> simp [hx, boolVal]
    · unfold linGroupMemberCost
      omega
  have da := Det.call (Det.mk2
    (Det.arg' (P := P) (vs := [encGroup gs, encGroup hs]) (rest := []) (j := 1) rfl)
    (Det.get' (Det.arg' (P := P) (vs := [encGroup gs, encGroup hs]) (rest := []) (j := 0) rfl)
      (Det.nat 1) rfl)) (all_spec hall hh)
  have hout : xs.all q = decide (gens gs ≤ gens hs) := by
    simp only [xs, List.all_map, Function.comp_def, q, linPermRead_enc]
    apply Bool.eq_iff_iff.mpr
    simp [List.all_eq_true, linGroupLe_iff]
  have he := (hp.block (gs := [linGroupLeF (b + 1)]) 0 rfl).single
  apply FunAll.intro he
  refine da.post fun cost hcost => ⟨congrArg boolVal hout, ?_⟩
  have wa := wt_list2_le (encGroup hs) (.list xs)
  have ws := wt_list2_le (encGroup gs) (encGroup hs)
  have wb := wt_boolVal_le (xs.all q)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hcost
  have hmul := Nat.mul_le_mul_right (linGroupMemberCost hm W) hl
  have hor : loopModK * (xs.length + 1) * ((Val.list [encGroup hs, .list xs]).wt + xs.length + 4) ≤
      1000 * (W + 1) * (5 * W + 10) := by
    unfold loopModK
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_left _ (by omega)
    · omega
  change _ ≤ linGroupLeCost hm W
  unfold linGroupLeCost
  have hpow : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  dsimp only [W, a, xs] at *
  simp only [loopModK] at *
  nlinarith

def linGroupEqF (le : ℕ) : Expr :=
  .letE (.call le (.var 0)) (.ite (.var 1) (.call le (mk2 (arg 1) (arg 0))) (.nat 0))
def linGroupEqFuns (b j : ℕ) : List Expr := [linGroupEqF (b + 1)] ++ linGroupLeFuns (b + 1) j

theorem linGroupEqFuns_length (b j : ℕ) : (linGroupEqFuns b j).length = 6 := rfl

noncomputable def linGroupEqCost (h : Membership) (W : ℕ) : ℕ :=
  1000 * (W + linGroupLeCost h W + 1)

private theorem linPairWeight_swap (a b : Val) : (Val.list [a, b]).wt = (Val.list [b, a]).wt := by
  simp [wt_list_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

open Classical in
theorem linGroupEq_spec (hm : Membership) {P : Program} {b j n : ℕ}
    (hp : P.HasAt b (linGroupEqFuns b j))
    (hj : P.prims[j]? = some (membershipPrim hm)) (gs hs : List (Equiv.Perm (Fin n))) :
    FunDet P b (.list [encGroup gs, encGroup hs]) (boolVal (decide (gens gs = gens hs)))
      (linGroupEqCost hm (Val.list [encGroup gs, encGroup hs]).wt) := by
  let a := Val.list [encGroup gs, encGroup hs]
  let W := a.wt
  have hle : P.HasAt (b + 1) (linGroupLeFuns (b + 1) j) := hp.block 1 rfl
  have hs₁ := linGroupLe_spec hm hle hj gs hs
  have hs₂ := linGroupLe_spec hm hle hj hs gs
  rw [linPairWeight_swap (encGroup hs) (encGroup gs)] at hs₂
  have dc := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hs₁
  have dt := Det.call (Det.mk2
    (Det.arg' (P := P) (vs := [encGroup gs, encGroup hs]) (rest := [boolVal (decide (gens gs ≤ gens hs))]) (j := 1) rfl)
    (Det.arg' (P := P) (vs := [encGroup gs, encGroup hs]) (rest := [boolVal (decide (gens gs ≤ gens hs))]) (j := 0) rfl)) hs₂
  have dd := Det.var' (P := P) (env := [a, boolVal (decide (gens gs ≤ gens hs))]) (i := 1) rfl
  have body := Det.ite' dd dt (Det.nat 0)
  have hb : (if (decide (gens gs ≤ gens hs)).toNat = 0 then Val.nat 0 else boolVal (decide (gens hs ≤ gens gs))) =
      boolVal (decide (gens gs = gens hs)) := by
    by_cases h₁ : gens gs ≤ gens hs <;> by_cases h₂ : gens hs ≤ gens gs
    · have he := le_antisymm h₁ h₂
      simp [h₁, h₂, he, boolVal]
    · have he : gens gs ≠ gens hs := fun he => h₂ (he ▸ le_refl _)
      simp [h₁, h₂, he, boolVal]
    · have he : gens gs ≠ gens hs := fun he => h₁ (he ▸ le_refl _)
      simp [h₁, h₂, he, boolVal]
    · have he : gens gs ≠ gens hs := fun he => h₁ (he ▸ le_refl _)
      simp [h₁, h₂, he, boolVal]
  rw [hb] at body
  apply FunDet.intro (hp.block (gs := [linGroupEqF (b + 1)]) 0 rfl).single
  refine (Det.letE dc body).mono ?_
  have wg : (encGroup gs).wt < W := wt_le_wt_list (by simp [W, a])
  have wh : (encGroup hs).wt < W := wt_le_wt_list (by simp [W, a])
  have wi := wt_list2_le (encGroup hs) (encGroup gs)
  have wb₁ := wt_boolVal_le (decide (gens gs ≤ gens hs))
  have wb₂ := wt_boolVal_le (decide (gens hs ≤ gens gs))
  have w0 : (Val.nat 0).wt = 2 := by decide
  have wb₃ := wt_boolVal_le (decide (gens gs = gens hs))
  unfold linGroupEqCost
  dsimp only [W, a] at *
  simp only [max_def]
  split_ifs <;> omega



theorem linGroupEqCost_poly (h : Membership) : PBU (fun _ W _ => linGroupEqCost h W) := by
  simp only [linGroupEqCost, linGroupLeCost, linGroupMemberCost, Prim.boundSize]
  norm_poly

end GI.Impl
