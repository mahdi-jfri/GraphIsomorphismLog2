import Workspace.Impl.TermJSolSolve

/-!
# The coefficient kernel (specification)

`tmJSol_ker_spec`: on `[encIntMatrix M, encIntMatrix B]`, the entry `b + 1` of `tmJSolFuns b j`
returns `encIntMatrix K` for a `G × G` integer matrix `K` whose rows generate, as a subgroup of
`Fin G → ℤ`, exactly the coefficient kernel `{c | ∃ y, c ᵥ* B + y ᵥ* M = 0}`. The rows of `K`
are the last `G` coordinates of the last `G` rows of the Hermite multiplier `U` of `[M; B]`
(`tmJSolKer`, `tmJSol_kernel_closure`). The cost is at most `tmJSolKerBudget hH W` in the input
weight `W`, a fixed polynomial (`tmJSol_ker_spec_poly`).
-/

namespace GI.Impl
open GI.Lang
open GI.Cited (Val encInt encIntMatrix FullRankInst fullRankInput)
open _root_.Matrix
set_option maxHeartbeats 4000000

/-- The Hermite call costs at most this, for an input of weight at most `X`. -/
noncomputable def tmJSolHerCost (hH : GI.Cited.HermiteFullRank) (X : ℕ) : ℕ :=
  (linHermitePrim hH).boundSize X + X + linRowSolverHermiteBudget hH X + 2

theorem tmJSol_hermiteCost_le (hH : GI.Cited.HermiteFullRank) (I : FullRankInst) {X : ℕ}
    (hX : (fullRankInput I).wt ≤ X) : linHermiteCost hH I ≤ tmJSolHerCost hH X := by
  have wm : (encIntMatrix I.A).wt < (fullRankInput I).wt :=
    wt_le_wt_list (by simp [fullRankInput])
  have hr : I.r ≤ X := by
    have hl := length_lt_wt_list ((List.finRange I.r).map fun i => linVecVal (I.A i))
    simp only [List.length_map, List.length_finRange] at hl
    exact (hl.trans wm).le.trans hX
  have hc : I.c ≤ X := I.c_le.trans hr
  have hs : (fullRankInput I).cells.length ≤ X := (fullRankInput I).size_le_wt.trans hX
  have hbits : (fullRankInput I).cells.length ^ linHermiteDegree hH ≤ X ^ linHermiteDegree hH :=
    Nat.pow_le_pow_left hs _
  have hmat : linMatrixWt I.r I.r ((fullRankInput I).cells.length ^ linHermiteDegree hH) ≤
      linMatrixWt X X (X ^ linHermiteDegree hH) := by unfold linMatrixWt; gcongr
  have hmat' : linMatrixWt I.r I.c ((fullRankInput I).cells.length ^ linHermiteDegree hH) ≤
      linMatrixWt X X (X ^ linHermiteDegree hH) := by unfold linMatrixWt; gcongr
  have hh : linHermiteWt (linHermiteDegree hH) I ≤ linRowSolverHermiteBudget hH X := by
    unfold linHermiteWt linRowSolverHermiteBudget
    omega
  have hp := (linHermitePrim hH).bound_le hs
  unfold linHermiteCost tmJSolHerCost
  omega

/-! ### The cost budget, in the input weight `W` -/

/-- The Hermite cost. -/
noncomputable def tmJSolKerHB (hH : GI.Cited.HermiteFullRank) (W : ℕ) : ℕ :=
  tmJSolHerCost hH (tmJSolStackWt W)
/-- The weight of the input of each drop. -/
noncomputable def tmJSolKerDI (hH : GI.Cited.HermiteFullRank) (W : ℕ) : ℕ :=
  2 * (W + 2 + tmJSolKerHB hH W) + 6
/-- The weight of the output. -/
noncomputable def tmJSolKerOW (hH : GI.Cited.HermiteFullRank) (W : ℕ) : ℕ :=
  2 * (W * tmJSolKerHB hH W) + W + 4
/-- The cost of the map over the rows. -/
noncomputable def tmJSolKerMC (hH : GI.Cited.HermiteFullRank) (W : ℕ) : ℕ :=
  W * tmJSolDropCost (tmJSolKerDI hH W) +
    mapK * (W + 1) * (tmJSolKerDI hH W + tmJSolKerOW hH W + 1)

/-- The cost budget of the kernel computation. -/
noncomputable def tmJSolKerBudget (hH : GI.Cited.HermiteFullRank) (W : ℕ) : ℕ :=
  1000 * (W + tmJSolStackCost W + tmJSolStackWt W + tmJSolKerHB hH W + tmJSolKerDI hH W +
    tmJSolDropCost (tmJSolKerDI hH W) + tmJSolKerOW hH W + tmJSolKerMC hH W + 1)

/-- The answer of the kernel computation. -/
def tmJSolKerAnswer {t G : ℕ} (M : Matrix (Fin t) (Fin t) ℤ) (B : Matrix (Fin G) (Fin t) ℤ)
    (out : Val) : Prop :=
  ∃ K : Matrix (Fin G) (Fin G) ℤ, out = encIntMatrix K ∧
    (∀ c : Fin G → ℤ, c ∈ AddSubgroup.closure (Set.range K) ↔
      ∃ y : Fin t → ℤ, c ᵥ* B + y ᵥ* M = 0) ∧
    ∀ c : Fin G → ℤ, (∃ y : Fin t → ℤ, c ᵥ* B + y ᵥ* M = 0) ↔ ∃ x : Fin G → ℤ, x ᵥ* K = c

set_option maxRecDepth 20000 in
/-- **The coefficient kernel.** -/
theorem tmJSol_ker_spec (hH : GI.Cited.HermiteFullRank) {P : Program} {b j : ℕ}
    (hA : tmJSolAt P b j) (hj : P.prims[j]? = some (linHermitePrim hH))
    {t G : ℕ} (ht : 0 < t) (M : Matrix (Fin t) (Fin t) ℤ) (hM : M.det ≠ 0)
    (B : Matrix (Fin G) (Fin t) ℤ) :
    FunAll P (b + 1) (.list [encIntMatrix M, encIntMatrix B]) (fun out cost =>
      tmJSolKerAnswer M B out ∧
      cost ≤ tmJSolKerBudget hH (Val.list [encIntMatrix M, encIntMatrix B]).wt) := by
  let a := Val.list [encIntMatrix M, encIntMatrix B]
  let W := a.wt
  let I := tmJSolInst ht M B hM
  have hWa : (Val.list [encIntMatrix M, encIntMatrix B]).wt = W := rfl
  have wM : (encIntMatrix M).wt < W := wt_le_wt_list (by simp)
  have wB : (encIntMatrix B).wt < W := wt_le_wt_list (by simp)
  have lM := length_lt_wt_list (tmJSolRows M)
  have lB := length_lt_wt_list (tmJSolRows B)
  simp only [tmJSolRows_length] at lM lB
  have htW : t < W := lM.trans wM
  have hGW : G < W := lB.trans wB
  -- stacking
  have hst := tmJSolStack_spec hA.stack hA.app ht M B hM []
  have dst := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hst.1
  have wI : (fullRankInput I).wt ≤ tmJSolStackWt W := hst.2
  -- the Hermite call
  let e2 := [a, fullRankInput I]
  have hHB : linHermiteCost hH I ≤ tmJSolKerHB hH W := tmJSol_hermiteCost_le hH I wI
  have dher : EvalAll P e2 (.call (b + 10) (.var 1)) (fun v c =>
      linHermiteOut (linHermiteDegree hH) I v ∧ v.wt < tmJSolKerHB hH W ∧
        c ≤ tmJSolStackWt W + 3 * tmJSolKerHB hH W + 2) := by
    apply EvalAll.call_funAll (Det.var' (P := P) (env := e2) (i := 1) rfl)
    rintro v ca ⟨rfl, hca⟩
    refine (linHermite_spec hH hA.her hj I).wt_lt.mono fun out cost ho => ?_
    have h1 : cost ≤ linHermiteCost hH I := ho.1.2
    have h2 : out.wt < cost := ho.2
    have hca' : ca ≤ (fullRankInput I).wt + 1 := hca
    exact ⟨ho.1.1, by omega, by omega⟩
  -- assemble
  apply FunAll.intro hA.ker
  apply EvalAll.letE dst
  rintro v1 c1 ⟨rfl, hc1⟩
  have hc1' : c1 ≤ W + 1 + tmJSolStackCost W + (fullRankInput I).wt + 1 := hc1
  apply EvalAll.letE dher
  rintro v2 c2 ⟨⟨U, H, rfl, hU, hUM, hHerm, -, -⟩, wv2, hc2⟩
  change Matrix (Fin (t + G)) (Fin (t + G)) ℤ at U
  change Matrix (Fin (t + G)) (Fin t) ℤ at H
  have wv2' : (Val.list [encIntMatrix U, encIntMatrix H]).wt < tmJSolKerHB hH W := wv2
  let e3 := [a, fullRankInput I, .list [encIntMatrix U, encIntMatrix H]]
  have dv2 := Det.var' (P := P) (env := e3) (i := 2)
    (v := .list [encIntMatrix U, encIntMatrix H]) rfl
  have dU : Det P e3 (.get (.var 2) (.nat 0)) (.list (tmJSolRows U)) _ :=
    Det.get' dv2 (Det.nat 0) rfl
  have d0 : Det P e3 (arg 0) (.list (tmJSolRows M)) _ :=
    Det.arg' (P := P) (vs := [encIntMatrix M, encIntMatrix B])
      (rest := [fullRankInput I, .list [encIntMatrix U, encIntMatrix H]]) (j := 0) rfl
  have dl := Det.length d0
  simp only [tmJSolRows_length] at dl
  -- the last `G` rows of `U`
  let rows := (List.finRange G).map fun k => linVecVal (U (Fin.natAdd t k))
  have hdr : FunDet P (b + 3) (.list [.nat t, .list (tmJSolRows U)]) (.list rows)
      (tmJSolDropCost (Val.list [.nat t, .list (tmJSolRows U)]).wt) := by
    have h := tmJSolDrop_spec hA.drop t (tmJSolRows U)
    rw [show (tmJSolRows U).drop t = rows from tmJSolDrop_rows U] at h
    exact h
  have wdr := tmJSol_funDet_wt hdr
  have dcall := Det.call (Det.mk2 dl dU) hdr
  -- the last `G` coordinates of each row
  let K := tmJSolKer U
  have wU : (Val.list (tmJSolRows U)).wt < tmJSolKerHB hH W := by
    have : (encIntMatrix U).wt < (Val.list [encIntMatrix U, encIntMatrix H]).wt :=
      wt_le_wt_list (by simp)
    exact this.trans wv2'
  have wrows : (Val.list rows).wt ≤ (Val.list (tmJSolRows U)).wt := by
    show (Val.list ((List.finRange G).map fun k => linVecVal (U (Fin.natAdd t k)))).wt ≤
      (Val.list ((List.finRange (t + G)).map fun i => linVecVal (U i))).wt
    rw [← tmJSolDrop_rows U]
    exact wt_list_sublist (List.drop_sublist _ _)
  have wrow (k : Fin G) : (linVecVal (U (Fin.natAdd t k))).wt < tmJSolKerHB hH W := by
    have : (linVecVal (U (Fin.natAdd t k))).wt < (Val.list rows).wt :=
      wt_le_wt_list (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩)
    omega
  have hmap := map_spec hA.kmap (c := .nat t) (xs := rows)
    (R := fun x w => ∀ k : Fin G, x = linVecVal (U (Fin.natAdd t k)) → w = linVecVal (K k))
    (B := fun x => tmJSolDropCost (Val.list [.nat t, x]).wt) (by
      intro x hx
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
      refine FunAll.mono (tmJSolDrop_vec_spec hA.drop (U (Fin.natAdd t k))) fun w c hw => ⟨?_, hw.2⟩
      intro k' hk'
      have hrow := linVecVal_injective hk'
      rw [hw.1]
      congr 1
      funext i
      change U (Fin.natAdd t k) (Fin.natAdd t i) = U (Fin.natAdd t k') (Fin.natAdd t i)
      rw [hrow])
  have dm := EvalAll.call_funAll (f := b + 6) (Det.mk2 dl dcall)
    (Q := fun out cost => tmJSolKerAnswer M B out ∧
      c1 + c2 + cost + 2 * out.wt + 2 ≤ tmJSolKerBudget hH W)
    (by
      rintro v ca ⟨rfl, hca⟩
      refine hmap.mono fun w cost hw => ?_
      obtain ⟨ws, rfl, hws, hcost⟩ := hw
      have hws' : ws = (List.finRange G).map fun k => linVecVal (K k) :=
        forall₂_map_eq (fun k _ w hw => hw k rfl) hws
      subst hws'
      refine ⟨⟨K, rfl, fun c => tmJSol_kernel_closure M B U H hU hUM hHerm c,
        fun c => tmJSol_kernel_iff M B U H hU hUM hHerm c⟩, ?_⟩
      -- the cost
      have wK : (encIntMatrix K).wt ≤ tmJSolKerOW hH W := by
        have h := linWtList (vs := (List.finRange G).map fun k => linVecVal (K k))
          (B := tmJSolKerHB hH W) (by
            intro v hv
            obtain ⟨k, _, rfl⟩ := List.mem_map.mp hv
            have hs : (linVecVal (K k)).wt ≤ (linVecVal (U (Fin.natAdd t k))).wt := by
              have h' := (tmJSolDrop_vec (z := U (Fin.natAdd t k))).symm
              change (Val.list ((List.finRange G).map fun i =>
                encInt (U (Fin.natAdd t k) (Fin.natAdd t i)))).wt ≤ _
              rw [h']
              exact wt_list_sublist (List.drop_sublist _ _)
            have := wrow k
            omega)
        simp only [List.length_map, List.length_finRange] at h
        have hm := Nat.mul_le_mul_right (tmJSolKerHB hH W) hGW.le
        change (Val.list ((List.finRange G).map fun k => linVecVal (K k))).wt ≤ _
        unfold tmJSolKerOW
        omega
      have hDI : ∀ x ∈ rows, tmJSolDropCost (Val.list [.nat t, x]).wt ≤
          tmJSolDropCost (tmJSolKerDI hH W) := by
        intro x hx
        apply tmJSolDropCost_mono
        have hxw : x.wt < (Val.list rows).wt := wt_le_wt_list hx
        have := wt_list2_le (.nat t) x
        have := wt_nat_le t
        unfold tmJSolKerDI
        omega
      have hsum : (rows.map fun x => tmJSolDropCost (Val.list [.nat t, x]).wt).sum ≤
          W * tmJSolDropCost (tmJSolKerDI hH W) := by
        have h := List.sum_le_card_nsmul (rows.map fun x => tmJSolDropCost (Val.list [.nat t, x]).wt)
          (tmJSolDropCost (tmJSolKerDI hH W)) (by
            intro y hy
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
            exact hDI x hx)
        simp only [List.length_map, smul_eq_mul, rows, List.length_finRange] at h
        exact h.trans (Nat.mul_le_mul_right _ hGW.le)
      have hin : (Val.list [.nat t, .list rows]).wt ≤ tmJSolKerDI hH W := by
        have := wt_list2_le (.nat t) (.list rows)
        have := wt_nat_le t
        unfold tmJSolKerDI
        omega
      have hlen : rows.length = G := by simp [rows]
      have hmk := Nat.mul_le_mul (Nat.mul_le_mul_left mapK (show rows.length + 1 ≤ W + 1 by omega))
        (show (Val.list [.nat t, .list rows]).wt + (encIntMatrix K).wt + 1 ≤
          tmJSolKerDI hH W + tmJSolKerOW hH W + 1 by omega)
      have hMC : cost ≤ tmJSolKerMC hH W := by
        unfold tmJSolKerMC
        change cost ≤ _ + mapK * (rows.length + 1) *
          ((Val.list [.nat t, .list rows]).wt + (encIntMatrix K).wt + 1) at hcost
        omega
      have hdc := tmJSolDropCost_mono (show (Val.list [.nat t, .list (tmJSolRows U)]).wt ≤
        tmJSolKerDI hH W by
          have := wt_list2_le (.nat t) (.list (tmJSolRows U))
          have := wt_nat_le t
          unfold tmJSolKerDI
          omega)
      have wt0 := wt_nat_le t
      have wdin := wt_list2_le (.nat t) (.list rows)
      have wa2 := wt_list2_le (.nat t) (.list (tmJSolRows U))
      have hdi : tmJSolKerDI hH W = 2 * (W + 2 + tmJSolKerHB hH W) + 6 := rfl
      change c1 + c2 + (ca + cost + (encIntMatrix K).wt + 1) + 2 * (encIntMatrix K).wt + 2 ≤
        tmJSolKerBudget hH W
      unfold tmJSolKerBudget
      omega)
  refine dm.mono fun out cost ho => ⟨ho.1, ?_⟩
  have h2 := ho.2
  change c1 + (c2 + cost + out.wt + 1) + out.wt + 1 ≤ tmJSolKerBudget hH W
  omega

end GI.Impl
