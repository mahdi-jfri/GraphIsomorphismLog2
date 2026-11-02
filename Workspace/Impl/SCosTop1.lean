import Workspace.Impl.SCosSpec

/-!
# The top level, part 1 (mathematics and small functions)

The entry `scosTopF` (function `12` of `scosProgram`) turns the task input
`[encGroup gs, encGroup hs, encPerm x]` into the problem of the recursion for the group of pairs
`G × H` (`G = ⟨gs⟩`, `H = ⟨hs⟩`), the pair `(x⁻¹, 1)` and all points. Here we prove the facts
about groups and values that this needs, and the specifications of the helper functions
`13`, `14`, `15`, of `a ⊕ b` (`16`) and of the cut to the first `n` entries (`253`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

variable {n : ℕ}

/-! ### The group of pairs -/

/-- The pairs `(g, 1)` for `g ∈ gs` and `(1, h)` for `h ∈ 1 :: hs`. -/
def scosTopPairs (gs hs : List (Perm (Fin n))) : List (ScosPair n) :=
  gs.map (fun g => (g, 1)) ++ (1 :: hs).map (fun h => (1, h))

/-- The pairs `(g, 1)`, `(1, h)` as permutations of `Fin (n + n)`. -/
def scosTopGens (gs hs : List (Perm (Fin n))) : List (Perm (Fin (n + n))) :=
  (scosTopPairs gs hs).map nintSum

/-- The pairs `(g, 1)` and `(1, h)` generate `G × H`: a pair `(a, b)` is `(a, 1) (1, b)`. -/
theorem scosTop_closure_pairs (gs hs : List (Perm (Fin n))) :
    Subgroup.closure {u | u ∈ scosTopPairs gs hs} = (gens gs).prod (gens hs) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro u hu
    simp only [scosTopPairs, Set.mem_setOf_eq, List.mem_append, List.mem_map,
      List.mem_cons] at hu
    rcases hu with ⟨g, hg, rfl⟩ | ⟨h, hh, rfl⟩
    · exact Subgroup.mem_prod.mpr ⟨Subgroup.subset_closure hg, one_mem _⟩
    · refine Subgroup.mem_prod.mpr ⟨one_mem _, ?_⟩
      rcases hh with rfl | hh
      · exact one_mem _
      · exact Subgroup.subset_closure hh
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := Subgroup.mem_prod.mp hab
    have e : ((a, b) : ScosPair n) = MonoidHom.inl _ _ a * MonoidHom.inr _ _ b := by simp
    rw [e]
    refine mul_mem ?_ ?_
    · have hle : (gens gs).map (MonoidHom.inl (Perm (Fin n)) (Perm (Fin n))) ≤
          Subgroup.closure {u | u ∈ scosTopPairs gs hs} := by
        unfold gens
        rw [MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨g, hg, rfl⟩
        apply Subgroup.subset_closure
        simp only [scosTopPairs, Set.mem_setOf_eq, List.mem_append, List.mem_map]
        exact Or.inl ⟨g, hg, by simp⟩
      exact hle ⟨a, ha, rfl⟩
    · have hle : (gens hs).map (MonoidHom.inr (Perm (Fin n)) (Perm (Fin n))) ≤
          Subgroup.closure {u | u ∈ scosTopPairs gs hs} := by
        unfold gens
        rw [MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨h, hh, rfl⟩
        apply Subgroup.subset_closure
        simp only [scosTopPairs, Set.mem_setOf_eq, List.mem_append, List.mem_map,
          List.mem_cons]
        exact Or.inr ⟨h, Or.inr hh, by simp⟩
      exact hle ⟨b, hb, rfl⟩

/-- **The generators of the top problem** generate the image of `G × H`. -/
theorem scosTop_gens (gs hs : List (Perm (Fin n))) :
    gens (scosTopGens gs hs) = ((gens gs).prod (gens hs)).map nintSum := by
  rw [← scosTop_closure_pairs, MonoidHom.map_closure]
  unfold gens scosTopGens
  congr 1
  ext p
  simp

/-- The encoding of the generators, with the identity `nintSum (1, 1) = 1` in front. -/
theorem scosTop_encGroup (gs hs : List (Perm (Fin n))) :
    encGroup (scosTopGens gs hs) = .list [.nat (n + n),
      .list ((1 :: gs).map (fun g => encPerm (nintSum (g, 1))) ++
        (1 :: hs).map (fun h => encPerm (nintSum (1, h))))] := by
  simp only [encGroup, encPerms, scosTopGens, scosTopPairs, List.map_cons, List.map_append,
    List.map_map, List.cons_append, Function.comp_def]
  rw [nintSum_one]

/-- The first coordinates of `G × H` form `G`. -/
theorem scosTop_fst (G H : Subgroup (Perm (Fin n))) :
    (G.prod H).map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n))) = G := by
  ext a
  simp only [Subgroup.mem_map, MonoidHom.coe_fst]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (Subgroup.mem_prod.mp hu).1
  · intro ha
    exact ⟨(a, 1), Subgroup.mem_prod.mpr ⟨ha, one_mem _⟩, rfl⟩

/-- The indicator of all points of the first copy: entry `i` is `1` exactly when `i < n`. -/
theorem scosInd_univ (n : ℕ) : scosInd (Finset.univ : Finset (Fin n)) =
    .list ((List.range (n + n)).map fun i => Val.nat (if i < n then 1 else 0)) := by
  unfold scosInd indVal encFun indF scosPhiF
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Equiv.refl_symm, Equiv.refl_apply, Finset.coe_univ,
    Set.image_univ, Set.mem_range]
  congr 1
  by_cases hi : (i : ℕ) < n
  · rw [if_pos hi, if_pos ⟨⟨i, hi⟩, Fin.ext rfl⟩]
  · rw [if_neg hi, if_neg]
    rintro ⟨a, rfl⟩
    exact hi a.isLt

/-- Lifting a list whose entries lie in the image of `nintSum`. -/
theorem scosTop_lift {ls : List (Perm (Fin (n + n)))} (h : ∀ l ∈ ls, ∃ u, nintSum u = l) :
    ∃ us : List (ScosPair n), us.map nintSum = ls := by
  induction ls with
  | nil => exact ⟨[], rfl⟩
  | cons l ls ih =>
    obtain ⟨u, hu⟩ := h l (by simp)
    obtain ⟨us, hus⟩ := ih fun l' hl' => h l' (by simp [hl'])
    exact ⟨u :: us, by simp [hu, hus]⟩

/-- **The group of the answer.** If `ls` generates the image of `L(G × H, Ω)`, then `ls` is the
image of a list of pairs whose first coordinates generate `G ⊓ H` (`scos_top_gens`). -/
theorem scosTop_ans_gens {G H : Subgroup (Perm (Fin n))} {ls : List (Perm (Fin (n + n)))}
    (hls : gens ls = (scosL (G.prod H) Finset.univ).map nintSum) :
    ∃ us : List (ScosPair n), us.map nintSum = ls ∧ gens (us.map Prod.fst) = G ⊓ H := by
  obtain ⟨us, rfl⟩ := scosTop_lift (ls := ls) fun l hl => by
    have h : l ∈ gens ls := Subgroup.subset_closure hl
    rw [hls] at h
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.mp h
    exact ⟨u, hu⟩
  refine ⟨us, rfl, scos_top_gens us ?_⟩
  apply Subgroup.map_injective (nintSum_injective (n := n))
  rw [← hls, MonoidHom.map_closure]
  unfold gens
  congr 1
  ext p
  simp

/-! ### The helper functions -/

section Funs

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

/-- `P` for short. -/
local notation "𝒫" => scosProgram c hps hpre hmb

/-- `a ⊕ b` (function `16`). -/
theorem scosTop_shift_spec {n n' : ℕ} (a : Perm (Fin n)) (b : Perm (Fin n')) :
    FunDet (𝒫) 16 (.list [encPerm a, encPerm b, .nat n]) (encPerm (sumToFin (Perm.sumCongr a b)))
      (shiftK * (n + n' + 1) ^ 3) :=
  shiftApp_spec (b := 15) (scos_shift (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (scos_append1 (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (scos_shiftMap (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (scos_addK (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)) a b

/-- `g ↦ g ⊕ 1` (function `13`). -/
theorem scosTop_g1_spec (g : Perm (Fin n)) :
    FunDet (𝒫) 13 (.list [.list [encPerm (1 : Perm (Fin n)), .nat n], encPerm g])
      (encPerm (nintSum (g, 1))) (10 ^ 9 * (n + 1) ^ 3) := by
  have g0 := Det.arg' (P := 𝒫)
    (vs := [.list [encPerm (1 : Perm (Fin n)), .nat n], encPerm g]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := 𝒫)
    (vs := [.list [encPerm (1 : Perm (Fin n)), .nat n], encPerm g]) (rest := []) (j := 1) rfl
  have ge := Det.get' g0 (Det.nat 0) (v := encPerm (1 : Perm (Fin n))) rfl
  have gn := Det.get' g0 (Det.nat 1) (v := .nat n) rfl
  refine FunDet.intro scos_pairG1 ((Det.call (Det.mk3 g1 ge gn)
    (scosTop_shift_spec g 1)).mono ?_)
  have w0 := wt_encPerm_le (1 : Perm (Fin n))
  have w1 := wt_encPerm_le g
  have w2 := wt_encPerm_le (nintSum (g, 1))
  have w3 := wt_list2_le (.list [encPerm (1 : Perm (Fin n)), .nat n]) (encPerm g)
  have w3' := wt_list2_le (encPerm (1 : Perm (Fin n))) (.nat n)
  have w4 := wt_list3_le (encPerm g) (encPerm (1 : Perm (Fin n))) (.nat n)
  have w5 := wt_nat_le n
  have p1 := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 3
  have p2 := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 2
  have q1 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := nint_pow_mono (by omega) (by norm_num)
  change (encPerm (sumToFin (Perm.sumCongr g (1 : Perm (Fin n))))).wt ≤ _ at w2
  unfold shiftK
  omega

/-- `h ↦ 1 ⊕ h` (function `14`). -/
theorem scosTop_h1_spec (h : Perm (Fin n)) :
    FunDet (𝒫) 14 (.list [.list [encPerm (1 : Perm (Fin n)), .nat n], encPerm h])
      (encPerm (nintSum (1, h))) (10 ^ 9 * (n + 1) ^ 3) := by
  have g0 := Det.arg' (P := 𝒫)
    (vs := [.list [encPerm (1 : Perm (Fin n)), .nat n], encPerm h]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := 𝒫)
    (vs := [.list [encPerm (1 : Perm (Fin n)), .nat n], encPerm h]) (rest := []) (j := 1) rfl
  have ge := Det.get' g0 (Det.nat 0) (v := encPerm (1 : Perm (Fin n))) rfl
  have gn := Det.get' g0 (Det.nat 1) (v := .nat n) rfl
  refine FunDet.intro scos_pairH1 ((Det.call (Det.mk3 ge g1 gn)
    (scosTop_shift_spec 1 h)).mono ?_)
  have w0 := wt_encPerm_le (1 : Perm (Fin n))
  have w1 := wt_encPerm_le h
  have w2 := wt_encPerm_le (nintSum (1, h))
  have w3 := wt_list2_le (.list [encPerm (1 : Perm (Fin n)), .nat n]) (encPerm h)
  have w3' := wt_list2_le (encPerm (1 : Perm (Fin n))) (.nat n)
  have w4 := wt_list3_le (encPerm (1 : Perm (Fin n))) (encPerm h) (.nat n)
  have w5 := wt_nat_le n
  have p1 := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 3
  have p2 := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 2
  have q1 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := nint_pow_mono (by omega) (by norm_num)
  change (encPerm (sumToFin (Perm.sumCongr (1 : Perm (Fin n)) h))).wt ≤ _ at w2
  unfold shiftK
  omega

/-- `i ↦ [i < n]` (function `15`), for `i < n + n`. -/
theorem scosTop_lt_spec (n i : ℕ) (hi : i < n + n) :
    FunDet (𝒫) 15 (.list [.nat n, .nat i]) (.nat (if i < n then 1 else 0)) (100 * (n + 1)) := by
  have g0 := Det.arg' (P := 𝒫) (vs := [.nat n, .nat i]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := 𝒫) (vs := [.nat n, .nat i]) (rest := []) (j := 1) rfl
  refine FunDet.intro scos_ltStep ((Det.arith' (op := .lt) g1 g0
    (z := if i < n then 1 else 0) rfl).mono ?_)
  have := wt_list2_le (.nat n) (.nat i)
  have := wt_nat_le n
  have := wt_nat_le i
  split_ifs <;> omega

/-- The cut `a ⊕ b ↦ a` to the first `n` entries (function `253`). -/
theorem scosTop_take_spec (u : ScosPair n) :
    FunDet (𝒫) 253 (.list [.nat n, encPerm (nintSum u)]) (encPerm u.1)
      (10 ^ 10 * (n + 1) ^ 6) := by
  obtain ⟨a, b⟩ := u
  have hb : (Val.list [.nat n, encPerm (nintSum (a, b))]).wt + 1 ≤ 50 * (n + 1) ^ 2 := by
    have := wt_encPerm_le (nintSum (a, b))
    have := wt_list2_le (.nat n) (encPerm (nintSum (a, b)))
    have := wt_nat_le n
    have := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 2
    have : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  rw [nint_encPerm_sum_take] at hb ⊢
  have ht := linTake_spec (scos_take (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    ((List.finRange n).map (fun i => Val.nat (a i)) ++
      (List.finRange n).map (fun j => Val.nat (n + b j))) n (by simp)
  rw [List.take_left' (by simp)] at ht
  refine ht.mono ?_
  have p3 := nint_pow_le (W := (Val.list [.nat n, .list ((List.finRange n).map
      (fun i => Val.nat (a i)) ++ (List.finRange n).map (fun j => Val.nat (n + b j)))]).wt)
    (c := 50) (Y := (n + 1) ^ 2) hb 3
  have e : ((n + 1) ^ 2) ^ 3 = (n + 1) ^ 6 := by rw [← pow_mul]
  rw [e] at p3
  unfold linTakeCost
  omega

end Funs

end GI.Impl
