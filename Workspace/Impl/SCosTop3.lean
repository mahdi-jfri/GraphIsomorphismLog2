module

public import Workspace.Impl.SCosTop2

@[expose] public section

/-!
# The top level, part 3 (reading the answer)

After the recursion returns an answer `w` for the problem of `G × H`, the pair `(x⁻¹, 1)` and
all points, the last step of `scosTopF` (`scosTop_tail`) reads the output of the task off it.

* `w = []`: the subcoset is empty, so `G x ∩ H = ∅` (`scos_top_empty`), and the output is `0`.
* `w = [z₁ ⊕ z₂, lv]`: `y = z₁⁻¹` lies in `G x ∩ H` (`scos_top_mem`). The generators of `lv` are
  `u₁ ⊕ u₂` for pairs `u` whose first coordinates generate `G ⊓ H` (`scosTop_ans_gens`). The
  program cuts each to its first `n` entries and calls the pointwise stabilizer of no points on
  them, which returns at most `n²` generators of the same group.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

/-- The correct outputs of `SolvableCosetIntersectionTask` (the predicate of the task). -/
def scosTopCorrect {n : ℕ} (gs hs : List (Perm (Fin n))) (x : Perm (Fin n)) (v : Val) : Prop :=
  (v = .nat 0 ∧ ∀ g ∈ gens gs, g * x ∉ gens hs) ∨
  ∃ y : Perm (Fin n), (∃ g ∈ gens gs, y = g * x) ∧ y ∈ gens hs ∧
    ∃ L : Val, v = .list [encPerm y, L] ∧ GensOf (gens gs ⊓ gens hs) L

/-- The weight of an answer of the recursion. -/
theorem scosTop_ans_wt {n X : ℕ} (hn : n < X) {w : Val} {x' : ScosPair n}
    {𝒢 : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} (h : ScosAns n w x' 𝒢 Φ) :
    w.wt ≤ 50000 * (X + 1) ^ 6 := by
  have q : 1 ≤ (X + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  rcases h with ⟨rfl, -⟩ | ⟨z, -, lv, rfl, -, hlv⟩
  · simp only [wt_list_nil]; omega
  · have hW := scosW_le_X hn
    have w1 := wt_encPerm_le (nintSum z)
    have w2 := wt_list2_le (encPerm (nintSum z)) lv
    have p2 := nint_pow_le (W := n + n) (c := 2) (Y := X + 1) (by omega) 2
    have q2 : (X + 1) ^ 2 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
    omega

/-- The group value `encGroup (us.map nintSum)`, written out. -/
theorem scosTop_encGroup_us {n : ℕ} (us : List (ScosPair n)) :
    encGroup (us.map nintSum) = .list [.nat (n + n),
      .list (((1, 1) :: us).map fun u => encPerm (nintSum u))] := by
  simp only [encGroup, encPerms, List.map_cons, List.map_map, Function.comp_def]
  rw [nintSum_one]

theorem scosTop_encGroup_fst {n : ℕ} (us : List (ScosPair n)) :
    Val.list [encGroup (us.map Prod.fst), encPts ([] : List (Fin n))] =
      .list [.list [.nat n, .list (((1, 1) :: us).map fun u => encPerm u.1)], .list []] := by
  simp [encGroup, encPerms, encPts, List.map_map, Function.comp_def]

/-- The product bound of the map over the generators. -/
theorem scosTop_map_arith {L B C Y : ℕ} (hL : L ≤ 20480 * Y ^ 6) (hY : 1 ≤ Y)
    (hB : B ≤ 250000 * Y ^ 8) (hC : C ≤ 10 ^ 10 * Y ^ 6) :
    L * C + 1000 * (L + 1) * B ≤ 10 ^ 15 * Y ^ 14 := by
  have h1 : L * C ≤ (20480 * Y ^ 6) * (10 ^ 10 * Y ^ 6) := Nat.mul_le_mul hL hC
  have h2 : 1000 * (L + 1) * B ≤ (1000 * (20481 * Y ^ 6)) * (250000 * Y ^ 8) := by
    have : L + 1 ≤ 20481 * Y ^ 6 := by have := Nat.one_le_pow 6 Y hY; omega
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ this) hB
  have e1 : (20480 * Y ^ 6) * (10 ^ 10 * Y ^ 6) = 204800000000000 * Y ^ 12 := by ring
  have e2 : (1000 * (20481 * Y ^ 6)) * (250000 * Y ^ 8) = 5120250000000 * Y ^ 14 := by ring
  have h3 : Y ^ 12 ≤ Y ^ 14 := Nat.pow_le_pow_right hY (by norm_num)
  omega

section Tail

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

/-- `P` for short. -/
local notation "𝒫" => scosProgram c hps hpre hmb

variable {n : ℕ} (gs hs : List (Perm (Fin n))) (x : Perm (Fin n))

/-- The input. -/
local notation "v₀" => Val.list [encGroup gs, encGroup hs, encPerm x]

/-- The cut of `z₁ ⊕ z₂` to `z₁`. -/
theorem scosTop_t1 {X : ℕ} (hw : ScosTopW gs hs x X) (gv lv : Val) (hlv : lv.wt ≤ scosW n)
    (z : ScosPair n) :
    Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
        encPerm (nintSum (x⁻¹, 1)), .list [encPerm (nintSum z), lv]]
      (.call 253 (mk2 (.var 1) (.get (.var 6) (.nat 0)))) (encPerm z.1)
      (10 ^ 12 * (X + 1) ^ 6) := by
  have hn := hw.n_lt
  have hv1 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
      encPerm (nintSum (x⁻¹, 1)), .list [encPerm (nintSum z), lv]] (.var 1) (.nat n) _ :=
    Det.var' rfl
  have hv6 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
      encPerm (nintSum (x⁻¹, 1)), .list [encPerm (nintSum z), lv]] (.var 6)
      (.list [encPerm (nintSum z), lv]) _ := Det.var' rfl
  have g0 := Det.get' hv6 (Det.nat 0) (v := encPerm (nintSum z)) rfl
  refine (Det.call (Det.mk2 hv1 g0)
    (scosTop_take_spec (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) z)).mono ?_
  have hW := scosW_le_X hn
  have w1 := wt_encPerm_le (nintSum z)
  have w1' := wt_encPerm_le z.1
  have w2 := wt_list2_le (encPerm (nintSum z)) lv
  have w3 := wt_list2_le (.nat n) (encPerm (nintSum z))
  have w4 := wt_nat_le n
  have p2 := nint_pow_le (W := n + n) (c := 2) (Y := X + 1) (by omega) 2
  have q0 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q6 : (n + 1) ^ 6 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have q1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (X + 1) ^ 2 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
  omega

/-- The inverse `z₁⁻¹`. -/
theorem scosTop_t2 {X : ℕ} (hw : ScosTopW gs hs x X) (gv w : Val) (z₁ : Perm (Fin n)) :
    Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
        encPerm (nintSum (x⁻¹, 1)), w, encPerm z₁]
      (.call 75 (.var 7)) (encPerm z₁⁻¹) (10 ^ 6 * (X + 1) ^ 4) := by
  have hn := hw.n_lt
  have hv7 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
      encPerm (nintSum (x⁻¹, 1)), w, encPerm z₁] (.var 7) (encPerm z₁) _ := Det.var' rfl
  refine (Det.call hv7
    (inv_spec (scos_inv (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)) z₁)).mono ?_
  have w1 := wt_encPerm_le z₁
  have w2 := wt_encPerm_le z₁⁻¹
  have q0 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q4 : (n + 1) ^ 4 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have q2 : (X + 1) ^ 2 ≤ (X + 1) ^ 4 := nint_pow_mono (by omega) (by norm_num)
  have := Nat.one_le_pow 4 (X + 1) (by omega)
  unfold invK
  omega

/-- The argument of the last call: the first coordinates of the generators, and no points. -/
theorem scosTop_t3 {X : ℕ} (hw : ScosTopW gs hs x X) (gv ez : Val) (z₁ : Perm (Fin n))
    (us : List (ScosPair n))
    (hlv : (encGroup (us.map nintSum)).wt ≤ scosW n)
    (hwz : (Val.list [ez, encGroup (us.map nintSum)]).wt ≤ 50000 * (X + 1) ^ 6) :
    Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
        encPerm (nintSum (x⁻¹, 1)), .list [ez, encGroup (us.map nintSum)], encPerm z₁]
      (mk2 (mk2 (.var 1) (.call 256 (mk2 (.var 1) (.get (.get (.var 6) (.nat 1)) (.nat 1)))))
        .nil)
      (.list [encGroup (us.map Prod.fst), encPts ([] : List (Fin n))])
      (10 ^ 16 * (X + 1) ^ 14) := by
  have hn := hw.n_lt
  rw [scosTop_encGroup_us] at hlv hwz ⊢
  rw [scosTop_encGroup_fst]
  have hv1 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
      encPerm (nintSum (x⁻¹, 1)), .list [ez, .list [.nat (n + n),
        .list (((1, 1) :: us).map fun u => encPerm (nintSum u))]], encPerm z₁]
      (.var 1) (.nat n) _ := Det.var' rfl
  have hv6 : Det (𝒫) [v₀, .nat n, encPerm (1 : Perm (Fin n)), scosTopLv gs hs, gv,
      encPerm (nintSum (x⁻¹, 1)), .list [ez, .list [.nat (n + n),
        .list (((1, 1) :: us).map fun u => encPerm (nintSum u))]], encPerm z₁]
      (.var 6) (.list [ez, .list [.nat (n + n),
        .list (((1, 1) :: us).map fun u => encPerm (nintSum u))]]) _ := Det.var' rfl
  have g1 := Det.get' hv6 (Det.nat 1) (v := .list [.nat (n + n),
        .list (((1, 1) :: us).map fun u => encPerm (nintSum u))]) rfl
  have g2 := Det.get' g1 (Det.nat 1)
    (v := .list (((1, 1) :: us).map fun u => encPerm (nintSum u))) rfl
  have hm := mapList_spec (scos_takeMap (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    ((1, 1) :: us) (fun u => encPerm (nintSum u)) (fun u => encPerm u.1) (c := .nat n)
    (fun a _ a' _ h => by rw [nintSum_injective (nint_encPerm_injective h)])
    (fun u _ => scosTop_take_spec u)
  refine (Det.mk2 (Det.mk2 hv1 (Det.call (Det.mk2 hv1 g2) hm)) Det.nil).mono ?_
  -- the weights
  have hW := scosW_le_X hn
  generalize hLm : (((1, 1) :: us).map fun u => encPerm (nintSum u)) = Lm at *
  have hL : (((1, 1) :: us).map fun u => encPerm (nintSum u)).length = us.length + 1 := by simp
  rw [hLm] at hL
  have l1 := length_lt_wt_list Lm
  have l2 : (Val.list Lm).wt < (Val.list [.nat (n + n), .list Lm]).wt := wt_le_wt_list (by simp)
  have l3 : (Val.list [.nat (n + n), .list Lm]).wt < (Val.list [ez, .list [.nat (n + n),
      .list Lm]]).wt := wt_le_wt_list (by simp)
  have wo : (Val.list (((1, 1) :: us).map fun u => encPerm u.1)).wt ≤
      (((1, 1) :: us)).length * (2 * (4 * (n + 1) ^ 2) + 1) + 4 :=
    wt_list_map_le _ _ fun u _ => wt_encPerm_le u.1
  simp only [List.length_cons] at wo
  generalize hO : (Val.list (((1, 1) :: us).map fun u => encPerm u.1)) = O at *
  have q0 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q6 : (n + 1) ^ 6 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have q1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q26 : (X + 1) ^ 2 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
  have q68 : (X + 1) ^ 6 ≤ (X + 1) ^ 8 := nint_pow_mono (by omega) (by norm_num)
  have q814 : (X + 1) ^ 8 ≤ (X + 1) ^ 14 := nint_pow_mono (by omega) (by norm_num)
  have hlen : us.length + 1 ≤ 20480 * (X + 1) ^ 6 := by omega
  have wo' : O.wt ≤ 200000 * (X + 1) ^ 8 := by
    have : (us.length + 1) * (2 * (4 * (n + 1) ^ 2) + 1) ≤
        (20480 * (X + 1) ^ 6) * (9 * (X + 1) ^ 2) := Nat.mul_le_mul hlen (by omega)
    have e : (20480 * (X + 1) ^ 6) * (9 * (X + 1) ^ 2) = 184320 * (X + 1) ^ 8 := by ring
    omega
  have w2 := wt_list2_le (.nat n) (.list Lm)
  have w3 := wt_list2_le (.nat n) O
  have w4 := wt_list2_le (.list [.nat n, O]) (.list [])
  have w5 := wt_nat_le n
  have wm : (Val.list [.nat n, .list Lm]).wt + O.wt + 1 ≤ 250000 * (X + 1) ^ 8 := by omega
  have hmap := scosTop_map_arith (L := us.length + 1) (C := 10 ^ 10 * (n + 1) ^ 6)
    (Y := X + 1) hlen (by omega) wm (Nat.mul_le_mul_left _ q6)
  simp only [List.length_cons, wt_list_nil] at *
  unfold mapK
  omega

end Tail

end GI.Impl
