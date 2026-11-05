module

public import Workspace.Impl.SCosTop1

@[expose] public section

/-!
# The top level, part 2 (the first steps of `scosTopF`)

The deterministic steps of the entry `scosTopF` up to the call of the recursion, each with a
cost bound in the weight `X` of the input `[encGroup gs, encGroup hs, encPerm x]`:
`n` (`scosTop_d1`), `encPerm 1` (`scosTop_d2`), the generators `g ⊕ 1`, `1 ⊕ h`
(`scosTop_d3`), the argument of the normalization (`scosTop_d4`), the pair `x⁻¹ ⊕ 1`
(`scosTop_d5`) and the problem `[gv, x⁻¹ ⊕ 1, ind]` (`scosTop_d6`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

/-- The weight facts of the input. -/
structure ScosTopW {n : ℕ} (gs hs : List (Perm (Fin n))) (x : Perm (Fin n)) (X : ℕ) : Prop where
  wG : (encGroup gs).wt + (encGroup hs).wt + (encPerm x).wt < X
  wA : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt
  wB : (Val.list ((1 :: hs).map encPerm)).wt < (encGroup hs).wt
  we1 : (encPerm (1 : Perm (Fin n))).wt < (Val.list ((1 :: gs).map encPerm)).wt
  hn : n < (encPerm (1 : Perm (Fin n))).wt
  hAl : ((1 :: gs).map encPerm).length < (Val.list ((1 :: gs).map encPerm)).wt
  hBl : ((1 :: hs).map encPerm).length < (Val.list ((1 :: hs).map encPerm)).wt
  wn : (Val.nat n).wt ≤ n + 2

theorem scosTopW_of {n : ℕ} (gs hs : List (Perm (Fin n))) (x : Perm (Fin n)) :
    ScosTopW gs hs x (Val.list [encGroup gs, encGroup hs, encPerm x]).wt where
  wG := by
    have := sum_wt_lt_wt_list [encGroup gs, encGroup hs, encPerm x]
    simp at this; omega
  wA := wt_le_wt_list (by simp)
  wB := wt_le_wt_list (by simp)
  we1 := wt_le_wt_list (by simp)
  hn := by
    have := length_lt_wt_list ((List.finRange n).map fun i => Val.nat ((1 : Perm (Fin n)) i))
    simpa [encPerm] using this
  hAl := length_lt_wt_list _
  hBl := length_lt_wt_list _
  wn := wt_nat_le n

theorem ScosTopW.n_lt {n : ℕ} {gs hs : List (Perm (Fin n))} {x : Perm (Fin n)} {X : ℕ}
    (hw : ScosTopW gs hs x X) : n < X := by
  have := hw.wG; have := hw.wA; have := hw.we1; have := hw.hn
  omega

/-- `scosW n` in terms of a bound `n < X`. -/
theorem scosW_le_X {n X : ℕ} (h : n < X) : scosW n ≤ 20480 * (X + 1) ^ 6 := by
  have p := nint_pow_le (W := n + n) (c := 2) (Y := X + 1) (by omega) 6
  unfold scosW
  omega

section Steps

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

/-- `P` for short. -/
local notation "𝒫" => scosProgram c hps hpre hmb

variable {n : ℕ} (gs hs : List (Perm (Fin n))) (x : Perm (Fin n))

/-- The input. -/
local notation "v₀" => Val.list [encGroup gs, encGroup hs, encPerm x]

/-- The generators `g ⊕ 1`, `1 ⊕ h`, as values. -/
noncomputable abbrev scosTopLv : Val :=
  .list ((1 :: gs).map (fun g => encPerm (nintSum (g, 1))) ++
    (1 :: hs).map (fun h => encPerm (nintSum (1, h))))

theorem scosTop_d1 {X : ℕ} (hw : ScosTopW gs hs x X) (hX : (v₀).wt = X) :
    Det (𝒫) [v₀] (.get (arg 0) (.nat 0)) (.nat n) (10 * (X + 1)) := by
  refine (Det.encPerms_size (gs := 1 :: gs) (Det.arg' (P := 𝒫)
    (vs := [encGroup gs, encGroup hs, encPerm x]) (rest := []) (j := 0) rfl)).mono ?_
  have := hw.wG; have := hw.wn; have := hw.hn; have := hw.we1; have := hw.wA
  omega

theorem scosTop_d2 {X : ℕ} (hw : ScosTopW gs hs x X) :
    Det (𝒫) [v₀, .nat n] (.call 72 (.var 1)) (encPerm (1 : Perm (Fin n)))
      (10 ^ 5 * (X + 1) ^ 3) := by
  have hv1 : Det (𝒫) [v₀, .nat n] (.var 1) (.nat n) _ := Det.var' rfl
  have hr : FunDet (𝒫) 72 (.nat n) (encPerm (1 : Perm (Fin n)))
      (loopModK * (n + 1) * ((Val.nat n).wt + n + (encPerm (1 : Perm (Fin n))).wt + 1)) :=
    (range_spec (scos_range (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)) n).mono
      fun w c ⟨hw, hc⟩ => by
        rw [range_eq_encPerm_one] at hw
        exact ⟨hw, hw ▸ hc⟩
  refine (Det.call hv1 hr).mono ?_
  have := hw.n_lt
  have := hw.wn
  have w1 := wt_encPerm_le (1 : Perm (Fin n))
  have q1 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q2 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have b : loopModK * (n + 1) * ((Val.nat n).wt + n + (encPerm (1 : Perm (Fin n))).wt + 1) ≤
      1000 * (X + 1) * (10 * (X + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul (by unfold loopModK; omega) (by omega)) (by omega)
  have e : 1000 * (X + 1) * (10 * (X + 1) ^ 2) = 10000 * (X + 1) ^ 3 := by ring
  have q3 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := nint_pow_mono (by omega) (by norm_num)
  omega

/-- Step 3: the generators of `G × H`. -/
theorem scosTop_d3 {X : ℕ} (hw : ScosTopW gs hs x X) (hX : (v₀).wt = X) :
    Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n))]
      (.call 250 (mk2 (.call 259 (mk2 (mk2 (.var 2) (.var 1)) (.get (arg 0) (.nat 1))))
        (.call 262 (mk2 (mk2 (.var 2) (.var 1)) (.get (arg 1) (.nat 1))))))
      (scosTopLv gs hs) (10 ^ 12 * (X + 1) ^ 6) := by
  have := hw.wG; have := hw.wA; have := hw.wB; have := hw.we1; have := hw.hn; have := hw.wn
  have := hw.hAl; have := hw.hBl
  have hv1 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n))] (.var 1) (.nat n) _ := Det.var' rfl
  have hv2 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n))] (.var 2)
    (encPerm (1 : Perm (Fin n))) _ := Det.var' rfl
  have hA := Det.encPerms_gens (gs := 1 :: gs) (Det.arg' (P := 𝒫)
    (vs := [encGroup gs, encGroup hs, encPerm x]) (rest := [.nat n, encPerm (1 : Perm (Fin n))])
    (j := 0) rfl)
  have hB := Det.encPerms_gens (gs := 1 :: hs) (Det.arg' (P := 𝒫)
    (vs := [encGroup gs, encGroup hs, encPerm x]) (rest := [.nat n, encPerm (1 : Perm (Fin n))])
    (j := 1) rfl)
  have inj : ∀ (f : Perm (Fin n) → Val) (l : List (Perm (Fin n))), ∀ a ∈ l, ∀ a' ∈ l,
      encPerm a = encPerm a' → f a = f a' := fun f l a _ a' _ h => by
    rw [nint_encPerm_injective h]
  have mg := mapList_spec (scos_g1Map (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (1 :: gs) encPerm (fun g => encPerm (nintSum (g, 1)))
    (c := .list [encPerm (1 : Perm (Fin n)), .nat n]) (inj _ _) (fun g _ => scosTop_g1_spec g)
  have mh := mapList_spec (scos_h1Map (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (1 :: hs) encPerm (fun h => encPerm (nintSum (1, h)))
    (c := .list [encPerm (1 : Perm (Fin n)), .nat n]) (inj _ _) (fun h _ => scosTop_h1_spec h)
  refine (Det.call (Det.mk2 (Det.call (Det.mk2 (Det.mk2 hv2 hv1) hA) mg)
    (Det.call (Det.mk2 (Det.mk2 hv2 hv1) hB) mh))
    (nint_append (scos_append2 (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
      ((1 :: gs).map (fun g => encPerm (nintSum (g, 1))))
      ((1 :: hs).map (fun h => encPerm (nintSum (1, h)))))).mono ?_
  -- weights of the two lists
  have wd : (Val.list ((1 :: gs).map (fun g => encPerm (nintSum (g, 1))))).wt ≤
      (1 :: gs).length * (2 * (16 * (n + 1) ^ 2) + 1) + 4 :=
    wt_list_map_le _ _ fun g _ => by
      have := wt_encPerm_le (nintSum (g, 1))
      have := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 2
      omega
  have wp : (Val.list ((1 :: hs).map (fun h => encPerm (nintSum (1, h))))).wt ≤
      (1 :: hs).length * (2 * (16 * (n + 1) ^ 2) + 1) + 4 :=
    wt_list_map_le _ _ fun h _ => by
      have := wt_encPerm_le (nintSum (1, h))
      have := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 2
      omega
  simp only [List.length_map] at *
  have hn2 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hn3 : (n + 1) ^ 3 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hn1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have la : (1 :: gs).length * (2 * (16 * (n + 1) ^ 2) + 1) ≤ 33 * (X + 1) ^ 3 := by
    have : (1 :: gs).length * (2 * (16 * (n + 1) ^ 2) + 1) ≤ (X + 1) * (33 * (X + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (X + 1) * (33 * (X + 1) ^ 2) = 33 * (X + 1) ^ 3 := by ring
    omega
  have lb : (1 :: hs).length * (2 * (16 * (n + 1) ^ 2) + 1) ≤ 33 * (X + 1) ^ 3 := by
    have : (1 :: hs).length * (2 * (16 * (n + 1) ^ 2) + 1) ≤ (X + 1) * (33 * (X + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (X + 1) * (33 * (X + 1) ^ 2) = 33 * (X + 1) ^ 3 := by ring
    omega
  have ca : (1 :: gs).length * (10 ^ 9 * (n + 1) ^ 3) ≤ 10 ^ 9 * (X + 1) ^ 4 := by
    have : (1 :: gs).length * (10 ^ 9 * (n + 1) ^ 3) ≤ (X + 1) * (10 ^ 9 * (X + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (X + 1) * (10 ^ 9 * (X + 1) ^ 3) = 10 ^ 9 * (X + 1) ^ 4 := by ring
    omega
  have cb : (1 :: hs).length * (10 ^ 9 * (n + 1) ^ 3) ≤ 10 ^ 9 * (X + 1) ^ 4 := by
    have : (1 :: hs).length * (10 ^ 9 * (n + 1) ^ 3) ≤ (X + 1) * (10 ^ 9 * (X + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (X + 1) * (10 ^ 9 * (X + 1) ^ 3) = 10 ^ 9 * (X + 1) ^ 4 := by ring
    omega
  have w6 := wt_list2_le (.list [encPerm (1 : Perm (Fin n)), .nat n])
    (.list ((1 :: gs).map encPerm))
  have w7 := wt_list2_le (.list [encPerm (1 : Perm (Fin n)), .nat n])
    (.list ((1 :: hs).map encPerm))
  have w7' := wt_list2_le (encPerm (1 : Perm (Fin n))) (.nat n)
  have w8 := wt_list2_le (.list ((1 :: gs).map (fun g => encPerm (nintSum (g, 1)))))
    (.list ((1 :: hs).map (fun h => encPerm (nintSum (1, h)))))
  have q1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := nint_pow_mono (by omega) (by norm_num)
  have q3 : (X + 1) ^ 3 ≤ (X + 1) ^ 4 := nint_pow_mono (by omega) (by norm_num)
  have q4 : (X + 1) ^ 4 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
  have ma : mapK * ((1 :: gs).length + 1) *
      ((Val.list [.list [encPerm (1 : Perm (Fin n)), .nat n], .list ((1 :: gs).map encPerm)]).wt +
        (Val.list ((1 :: gs).map (fun g => encPerm (nintSum (g, 1))))).wt + 1)
      ≤ mapK * (X + 2) * (100 * (X + 1) ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have mb : mapK * ((1 :: hs).length + 1) *
      ((Val.list [.list [encPerm (1 : Perm (Fin n)), .nat n], .list ((1 :: hs).map encPerm)]).wt +
        (Val.list ((1 :: hs).map (fun h => encPerm (nintSum (1, h))))).wt + 1)
      ≤ mapK * (X + 2) * (100 * (X + 1) ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e1 : mapK * (X + 2) * (100 * (X + 1) ^ 3) ≤ 200000 * (X + 1) ^ 4 := by
    have : mapK * (X + 2) * (100 * (X + 1) ^ 3) ≤ 1000 * (2 * (X + 1)) * (100 * (X + 1) ^ 3) :=
      Nat.mul_le_mul (by unfold mapK; omega) le_rfl
    have e : 1000 * (2 * (X + 1)) * (100 * (X + 1) ^ 3) = 200000 * (X + 1) ^ 4 := by ring
    omega
  have p := nint_pow_le (W := (Val.list [.list ((1 :: gs).map (fun g => encPerm (nintSum (g, 1)))),
      .list ((1 :: hs).map (fun h => encPerm (nintSum (1, h))))]).wt) (c := 200)
    (Y := (X + 1) ^ 3) (by omega) 2
  have e2 : ((X + 1) ^ 3) ^ 2 = (X + 1) ^ 6 := by rw [← pow_mul]
  rw [e2] at p
  have w9 := nint_wt_append ((1 :: gs).map (fun g => encPerm (nintSum (g, 1))))
    ((1 :: hs).map (fun h => encPerm (nintSum (1, h))))
  simp only [List.length_cons] at *
  omega

/-- Step 4: the argument of the normalization, `[encGroup (g ⊕ 1, 1 ⊕ h), []]`. -/
theorem scosTop_d4 {X : ℕ} (hw : ScosTopW gs hs x X) (hX : (v₀).wt = X) :
    Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs]
      (mk2 (mk2 (.arith .add (.var 1) (.var 1)) (.var 3)) .nil)
      (.list [encGroup (scosTopGens gs hs), encPts ([] : List (Fin (n + n)))])
      (10 ^ 14 * (X + 1) ^ 6) := by
  have := hw.n_lt
  have wK : (scosTopLv gs hs).wt < 10 ^ 12 * (X + 1) ^ 6 := (scosTop_d3 (c := c) (hps := hps)
    (hpre := hpre) (hmb := hmb) gs hs x hw hX).wt_lt
  rw [scosTop_encGroup]
  have e0 : encPts ([] : List (Fin (n + n))) = .list [] := rfl
  rw [e0]
  have hv1 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs] (.var 1)
    (.nat n) _ := Det.var' rfl
  have hv3 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs] (.var 3)
    (scosTopLv gs hs) _ := Det.var' rfl
  have hadd := Det.arith' (op := .add) hv1 hv1 (z := n + n) (by simp only [GI.Machine.BinOp.eval])
  refine (Det.mk2 (Det.mk2 hadd hv3) Det.nil).mono ?_
  have w4 := wt_list2_le (.nat (n + n)) (scosTopLv gs hs)
  have w5 := wt_list2_le (.list [.nat (n + n), scosTopLv gs hs]) (.list [])
  have w6 := wt_nat_le (n + n)
  have w7 := wt_nat_le n
  have q1 : X + 1 ≤ (X + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  simp only [wt_list_nil] at *
  omega

/-- Step 5: the pair `x⁻¹ ⊕ 1`. -/
theorem scosTop_d5 {X : ℕ} (hw : ScosTopW gs hs x X) (hX : (v₀).wt = X) (gv : Val) :
    Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv]
      (.call 16 (mk3 (.call 75 (arg 2)) (.var 2) (.var 1)))
      (encPerm (nintSum (x⁻¹, 1))) (10 ^ 9 * (X + 1) ^ 4) := by
  have := hw.n_lt
  have := hw.wG; have := hw.wA; have := hw.we1; have := hw.wn
  have hx := Det.arg' (P := 𝒫) (vs := [encGroup gs, encGroup hs, encPerm x])
    (rest := [.nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv]) (j := 2) rfl
  have hi := Det.call hx (inv_spec (scos_inv (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)) x)
  have hv1 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv] (.var 1)
    (.nat n) _ := Det.var' rfl
  have hv2 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv] (.var 2)
    (encPerm (1 : Perm (Fin n))) _ := Det.var' rfl
  have d := Det.call (Det.mk3 hi hv2 hv1)
    (scosTop_shift_spec (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) x⁻¹ (1 : Perm (Fin n)))
  refine d.mono ?_
  have w1 := wt_encPerm_le x⁻¹
  have w2 := wt_encPerm_le (1 : Perm (Fin n))
  have w3 := wt_encPerm_le (sumToFin (Perm.sumCongr x⁻¹ (1 : Perm (Fin n))))
  have w4 := wt_list3_le (encPerm x⁻¹) (encPerm (1 : Perm (Fin n))) (.nat n)
  have p1 := nint_pow_le (W := n + n) (c := 2) (Y := X + 1) (by omega) 3
  have p2 := nint_pow_le (W := n + n) (c := 2) (Y := X + 1) (by omega) 2
  have q0 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q00 : (n + 1) ^ 4 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have q1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := nint_pow_mono (by omega) (by norm_num)
  have q3 : (X + 1) ^ 3 ≤ (X + 1) ^ 4 := nint_pow_mono (by omega) (by norm_num)
  unfold shiftK invK
  omega

/-- Step 6: the problem `[gv, x⁻¹ ⊕ 1, ind]`. -/
theorem scosTop_d6 {X : ℕ} (hw : ScosTopW gs hs x X) (gv : Val) (hgv : gv.wt ≤ scosW n) :
    Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
        encPerm (nintSum (x⁻¹, 1))]
      (mk3 (.var 4) (.var 5)
        (.call 265 (mk2 (.var 1) (.call 72 (.arith .add (.var 1) (.var 1))))))
      (.list [gv, encPerm (nintSum (x⁻¹, 1)), scosInd (Finset.univ : Finset (Fin n))])
      (10 ^ 8 * (X + 1) ^ 6) := by
  have hn := hw.n_lt
  have hW := scosW_le_X hn
  rw [scosInd_univ]
  have hv1 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
      encPerm (nintSum (x⁻¹, 1))] (.var 1) (.nat n) _ := Det.var' rfl
  have hv4 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
      encPerm (nintSum (x⁻¹, 1))] (.var 4) gv _ := Det.var' rfl
  have hv5 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
      encPerm (nintSum (x⁻¹, 1))] (.var 5) (encPerm (nintSum (x⁻¹, 1))) _ := Det.var' rfl
  have hadd := Det.arith' (op := .add) hv1 hv1 (z := n + n) (by simp only [GI.Machine.BinOp.eval])
  have hr : FunDet (𝒫) 72 (.nat (n + n)) (natList (List.range (n + n)))
      (loopModK * (n + n + 1) * ((Val.nat (n + n)).wt + (n + n) +
        (natList (List.range (n + n))).wt + 1)) :=
    (range_spec (scos_range (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)) (n + n)).mono
      fun w c ⟨hw, hc⟩ => ⟨hw, hw ▸ hc⟩
  have hm := mapList_spec (scos_ltMap (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (List.range (n + n)) Val.nat (fun i => Val.nat (if i < n then 1 else 0))
    (c := .nat n) (B := 100 * (n + 1)) (fun j _ j' _ h => by
      simp only [Val.nat.injEq] at h ⊢; rw [h]) (fun i hi =>
      scosTop_lt_spec (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) n i
        (List.mem_range.mp hi))
  refine (Det.mk3 hv4 hv5 (Det.call (Det.mk2 hv1 (Det.call hadd hr)) hm)).mono ?_
  have e1 : natList (List.range (n + n)) = encPerm (1 : Perm (Fin (n + n))) := range_eq_encPerm_one
  have e1' : (natList (List.range (n + n))).wt = (encPerm (1 : Perm (Fin (n + n)))).wt := by
    rw [e1]
  have e1'' : (Val.list ((List.range (n + n)).map Val.nat)).wt =
      (encPerm (1 : Perm (Fin (n + n)))).wt := e1'
  have w1 := wt_encPerm_le (1 : Perm (Fin (n + n)))
  have w0 := wt_encPerm_le (nintSum (x⁻¹, 1))
  have w2 : (Val.list ((List.range (n + n)).map fun i => Val.nat (if i < n then 1 else 0))).wt ≤
      (List.range (n + n)).length * (2 * 3 + 1) + 4 :=
    wt_list_map_le _ _ fun j _ => by
      have := wt_nat_le (if j < n then 1 else 0); split_ifs at this ⊢ <;> omega
  simp only [List.length_range] at w2
  have w3 := wt_list2_le (.nat n) (.list ((List.range (n + n)).map Val.nat))
  have w3' := wt_list2_le (.nat n) (natList (List.range (n + n)))
  have w5 := wt_list3_le gv (encPerm (nintSum (x⁻¹, 1)))
    (.list ((List.range (n + n)).map fun i => Val.nat (if i < n then 1 else 0)))
  have w6 := wt_nat_le (n + n)
  have w7 := wt_nat_le n
  have p2 := nint_pow_le (W := n + n) (c := 2) (Y := X + 1) (by omega) 2
  have q1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := nint_pow_mono (by omega) (by norm_num)
  have q3 : (X + 1) ^ 3 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
  have b2 : (n + n) * (100 * (n + 1)) ≤ 200 * (X + 1) ^ 2 := by
    have : (n + n) * (100 * (n + 1)) ≤ (2 * (X + 1)) * (100 * (X + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (2 * (X + 1)) * (100 * (X + 1)) = 200 * (X + 1) ^ 2 := by ring
    omega
  have b3 : loopModK * (n + n + 1) * ((Val.nat (n + n)).wt + (n + n) +
      (natList (List.range (n + n))).wt + 1) ≤ 1000 * (2 * (X + 1)) * (20 * (X + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul (by unfold loopModK; omega) (by omega)) (by omega)
  have b4 : mapK * ((List.range (n + n)).length + 1) * ((Val.list [.nat n,
      .list ((List.range (n + n)).map Val.nat)]).wt +
      (Val.list ((List.range (n + n)).map fun i => Val.nat (if i < n then 1 else 0))).wt + 1) ≤
      1000 * (2 * (X + 1)) * (100 * (X + 1) ^ 2) := by
    simp only [List.length_range]
    exact Nat.mul_le_mul (Nat.mul_le_mul (by unfold mapK; omega) (by omega)) (by omega)
  have e3 : 1000 * (2 * (X + 1)) * (20 * (X + 1) ^ 2) = 40000 * (X + 1) ^ 3 := by ring
  have e4 : 1000 * (2 * (X + 1)) * (100 * (X + 1) ^ 2) = 200000 * (X + 1) ^ 3 := by ring
  simp only [List.length_range] at *
  omega

end Steps

end GI.Impl
