import Workspace.Impl.SCosTop3

/-!
# The top level, part 4 (the last step of `scosTopF`)

`scosTop_tail`: on the answer `w` of the recursion, the `if` at the end of `scosTopF` returns a
correct output of the task (`scosTopCorrect`), of weight at most `100 (X + 1)⁶`, at cost at most
`scosTopTailT hps X`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

/-- The cost bound of the last step. -/
noncomputable def scosTopTailT (hps : PointwiseStab) (X : ℕ) : ℕ :=
  10 ^ 18 * (X + 1) ^ 14 + (pointwiseStabPrim hps).boundSize (10 ^ 16 * (X + 1) ^ 14)

section Tail

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

/-- `P` for short. -/
local notation "𝒫" => scosProgram c hps hpre hmb

variable {n : ℕ} (gs hs : List (Perm (Fin n))) (x : Perm (Fin n))

/-- The input. -/
local notation "v₀" => Val.list [encGroup gs, encGroup hs, encPerm x]

/-- **The last step**: the output read off the answer. -/
theorem scosTop_tail {X : ℕ} (hw : ScosTopW gs hs x X) (gv w : Val)
    (hans : ScosAns n w (x⁻¹, 1) ((gens gs).prod (gens hs)) Finset.univ) :
    EvalAll (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
        encPerm (nintSum (x⁻¹, 1)), w]
      (.ite (.length (.var 6))
        (.letE (.call 253 (mk2 (.var 1) (.get (.var 6) (.nat 0))))
          (mk2 (.call 75 (.var 7))
            (.prim 0 (mk2 (mk2 (.var 1) (.call 256 (mk2 (.var 1)
              (.get (.get (.var 6) (.nat 1)) (.nat 1))))) .nil))))
        (.nat 0))
      (fun v cost => scosTopCorrect gs hs x v ∧ v.wt ≤ 100 * (X + 1) ^ 6 ∧
        cost ≤ scosTopTailT hps X) := by
  have hn := hw.n_lt
  have hwt := scosTop_ans_wt hn hans
  have q1 : 1 ≤ (X + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have q2 : (X + 1) ^ 6 ≤ (X + 1) ^ 14 := nint_pow_mono (by omega) (by norm_num)
  rcases hans with ⟨rfl, hemp⟩ | ⟨z, hz, lv, rfl, hlv, hlvw⟩
  · -- The subcoset is empty: the output is `0`.
    have hv6 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
        encPerm (nintSum (x⁻¹, 1)), .list []] (.var 6) (.list []) _ := Det.var' rfl
    have d := Det.ite_zero (t := .letE (.call 253 (mk2 (.var 1) (.get (.var 6) (.nat 0))))
          (mk2 (.call 75 (.var 7))
            (.prim 0 (mk2 (mk2 (.var 1) (.call 256 (mk2 (.var 1)
              (.get (.get (.var 6) (.nat 1)) (.nat 1))))) .nil))))
      (Det.length hv6) (Det.nat 0)
    refine d.post fun c hc => ⟨Or.inl ⟨rfl, ?_⟩, ?_, ?_⟩
    · exact scos_top_empty fun y' hy' => by rw [hemp] at hy'; exact hy'
    · have := wt_nat_le 0
      omega
    · have := wt_nat_le 0
      simp only [List.length_nil, wt_list_nil] at hc
      unfold scosTopTailT
      omega
  · -- A point `z` of the subcoset and the group `lv`.
    obtain ⟨ls, rfl, hls⟩ := hlv
    obtain ⟨us, rfl, hg⟩ := scosTop_ans_gens hls
    obtain ⟨hm1, hm2⟩ := scos_top_mem hz
    have hv6 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
        encPerm (nintSum (x⁻¹, 1)), .list [encPerm (nintSum z), encGroup (us.map nintSum)]]
        (.var 6) (.list [encPerm (nintSum z), encGroup (us.map nintSum)]) _ := Det.var' rfl
    refine EvalAll.ite (Det.length hv6) (fun vc cc h => ⟨_, h.1⟩) fun k cc hk => ?_
    obtain ⟨hk1, hkc⟩ := hk
    simp only [Val.nat.injEq, List.length_cons, List.length_nil] at hk1 hkc
    subst hk1
    rw [if_neg (by norm_num)]
    have t1 := scosTop_t1 (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs hs x hw gv
      (encGroup (us.map nintSum)) hlvw z
    refine EvalAll.letE t1 fun v7 k7 h7 => ?_
    obtain ⟨rfl, hk7⟩ := h7
    have t2 := scosTop_t2 (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs hs x hw gv
      (.list [encPerm (nintSum z), encGroup (us.map nintSum)]) z.1
    have t3 := scosTop_t3 (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs hs x hw gv
      (encPerm (nintSum z)) z.1 us hlvw hwt
    have wt3 := t3.wt_lt
    have c3 := pointwiseStab_call hps (scos_prim0 (c := c) (hps := hps) (hpre := hpre)
      (hmb := hmb)) t3 (G := gens (us.map Prod.fst)) ⟨_, rfl, rfl⟩
    refine (EvalAll.mk2_last t2 c3).mono fun v cv hv => ?_
    obtain ⟨vb, cb, ⟨hgv, hcb⟩, rfl, hcv⟩ := hv
    have hvb := GensVal.wt_le hgv
    refine ⟨Or.inr ⟨z.1⁻¹, hm1, hm2, vb, rfl, ?_⟩, ?_, ?_⟩
    · have h : GensOf (pointwiseStab (gens (us.map Prod.fst)) []) vb := hgv
      rwa [nint_pointwiseStab_nil, hg] at h
    · have w1 := wt_encPerm_le z.1⁻¹
      have w2 := wt_list2_le (encPerm z.1⁻¹) vb
      have q0 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have q6 : (n + 1) ^ 6 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      have q26 : (X + 1) ^ 2 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
      omega
    · have w1 := wt_encPerm_le z.1⁻¹
      have w2 := wt_list2_le (encPerm z.1⁻¹) vb
      have q0 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have q6 : (n + 1) ^ 6 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      have q26 : (X + 1) ^ 2 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
      have q4 : (X + 1) ^ 4 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
      have b : (pointwiseStabPrim hps).bound
          (.list [encGroup (us.map Prod.fst), encPts ([] : List (Fin n))]) ≤
          (pointwiseStabPrim hps).boundSize (10 ^ 16 * (X + 1) ^ 14) :=
        Prim.bound_le _ (by
          have := (Val.list [encGroup (us.map Prod.fst), encPts ([] : List (Fin n))]).size_le_wt
          omega)
      unfold scosTopTailT
      omega

end Tail

end GI.Impl
