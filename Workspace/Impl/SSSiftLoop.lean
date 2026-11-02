import Workspace.Impl.SSSiftStep

/-!
# The sifting loop as a program

`iterFuns b (b + 3)` with the step `ssSiftStepF` sifts a permutation through the whole base
(`ssSiftLoop_spec`). Weights are bounded through `SsSmall` with the bound `ssZ Y = 1000 Y⁴`, for
any `Y ≥ n + |B| + 2` with table indices at most `3 Y³`; every value then weighs at most
`ssW Y = ssZ Y (ssZ Y + 1)`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n : ℕ}

/-- The bound on sizes and numbers. -/
def ssZ (Y : ℕ) : ℕ := 1000 * Y ^ 4

/-- The bound on weights. -/
def ssW (Y : ℕ) : ℕ := ssZ Y * (ssZ Y + 1)

theorem ss_pow_le {Y : ℕ} (hY : 1 ≤ Y) {i j : ℕ} (h : i ≤ j) : Y ^ i ≤ Y ^ j :=
  Nat.pow_le_pow_right hY h

theorem ssZ_le_ssW (Y : ℕ) : ssZ Y ≤ ssW Y := by
  unfold ssW; nlinarith

theorem SsSmall.wt_le_ssW {Y : ℕ} {v : Val} (h : SsSmall (ssZ Y) v) : v.wt ≤ ssW Y := h.wt_le

/-- The weight bound covers `n` and the table. -/
theorem ssW_ge {Y : ℕ} {L : ℕ} (hY : n + L + 2 ≤ Y) :
    30 * (n + 1) ^ 2 ≤ ssW Y ∧ L * n + 2 ≤ ssW Y ∧ (n + 1) ^ 4 ≤ ssW Y ∧ L + 2 ≤ ssW Y := by
  have h1 : 1 ≤ Y := by omega
  have hZ := ssZ_le_ssW Y
  have h4 : Y ≤ Y ^ 4 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ 4 := ss_pow_le h1 (by norm_num)
  have h2 : (n + 1) ^ 2 ≤ Y ^ 4 := (Nat.pow_le_pow_left (by omega) 2).trans (ss_pow_le h1 (by norm_num))
  have h4' : (n + 1) ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hLn : L * n ≤ Y ^ 4 := by
    calc L * n ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
      _ = Y ^ 2 := by ring
      _ ≤ Y ^ 4 := ss_pow_le h1 (by norm_num)
  unfold ssZ at hZ
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ### Facts about the accumulators of the loop -/

theorem ssGet_mem {T : List (SsSlot n)} {i : ℕ} {j : Fin n} {e : Perm (Fin n) × ℕ}
    (h : ssGet T i j = some e) : some e ∈ T := by
  unfold ssGet at h
  cases hq : T[i * n + (j : ℕ)]? with
  | none => rw [hq] at h; simp at h
  | some s =>
    rw [hq] at h
    simp only [Option.join_some] at h
    subst h
    exact List.mem_of_getElem? hq

/-- The accumulators of the sifting loop: few used indices, each from the table, and a small
stop flag. -/
theorem ssSift_acc_facts (B : List (Fin n)) (T : List (SsSlot n)) {Z0 : ℕ}
    (hidx : ∀ s ∈ T, ∀ e, s = some e → e.2 ≤ Z0) (g : Perm (Fin n)) :
    ∀ i, ((List.range i).foldl (ssSiftStep B T) (g, [], 0)).2.1.length ≤ i ∧
      (∀ k ∈ ((List.range i).foldl (ssSiftStep B T) (g, [], 0)).2.1, k ≤ Z0) ∧
      ((List.range i).foldl (ssSiftStep B T) (g, [], 0)).2.2 ≤ i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨h1, h2, h3⟩ := ih
    generalize (List.range i).foldl (ssSiftStep B T) (g, [], 0) = acc at h1 h2 h3
    obtain ⟨g', u, st⟩ := acc
    simp only at h1 h2 h3
    unfold ssSiftStep
    simp only
    split_ifs with hs
    · cases hb : B[i]? with
      | none => dsimp only; exact ⟨Nat.le_succ_of_le h1, h2, Nat.le_succ_of_le h3⟩
      | some b =>
        dsimp only
        split_ifs with hd
        · exact ⟨Nat.le_succ_of_le h1, h2, Nat.le_succ_of_le h3⟩
        · cases he : ssGet T i (g' b) with
          | none => dsimp only; exact ⟨Nat.le_succ_of_le h1, h2, le_rfl⟩
          | some e =>
            dsimp only
            refine ⟨by simp; omega, fun k hk => ?_, by simp⟩
            simp only [List.mem_append, List.mem_singleton] at hk
            rcases hk with hk | rfl
            · exact h2 k hk
            · exact hidx _ (ssGet_mem he) e rfl
    · exact ⟨Nat.le_succ_of_le h1, h2, Nat.le_succ_of_le h3⟩

/-! ### Smallness -/

theorem ssSmall_acc {Z : ℕ} (a : Perm (Fin n) × List ℕ × ℕ) (hu : ∀ k ∈ a.2.1, k ≤ Z)
    (hs : a.2.2 ≤ Z) (hZ : 2 * n + 2 * a.2.1.length + 20 ≤ Z) : SsSmall Z (ssEncAcc a) := by
  refine ssSmall_list ?_ fun v hv => ?_
  · rw [size_list_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, size_encPerm, size_natList,
      size_nat]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact ssSmall_encPerm _ (by omega)
    · exact ssSmall_natList hu (by omega)
    · exact ssSmall_nat hs (by omega)

theorem size_ssEncAcc (a : Perm (Fin n) × List ℕ × ℕ) :
    (ssEncAcc a).size = 2 * n + 2 * a.2.1.length + 11 := by
  rw [ssEncAcc, size_list_eq]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, size_encPerm, size_natList,
    size_nat]
  omega

theorem size_ssEncTab (T : List (SsSlot n)) : (ssEncTab T).size ≤ T.length * (2 * n + 8) + 3 := by
  unfold ssEncTab
  refine (size_list_le fun v hv => ?_).trans (by rw [List.length_map])
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hv
  exact size_ssEncSlot_le s

theorem ssSmall_tab' {T : List (SsSlot n)} {Z : ℕ} (hs : ∀ s ∈ T, ∀ e, s = some e → e.2 ≤ Z)
    (hZ : T.length * (2 * n + 8) + 2 * n + 11 ≤ Z) : SsSmall Z (ssEncTab T) :=
  ssSmall_tab hs (by omega) (by omega)

theorem ssSmall_ctx {Z : ℕ} (B : List (Fin n)) (T : List (SsSlot n))
    (hs : ∀ s ∈ T, ∀ e, s = some e → e.2 ≤ Z)
    (hZ : T.length * (2 * n + 8) + 2 * n + 2 * B.length + 20 ≤ Z) :
    SsSmall Z (ssSiftCtx B T) := by
  refine ssSmall_list ?_ fun v hv => ?_
  · rw [size_list_eq]
    have := size_ssEncTab T
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ssEncB, size_natList,
      size_nat, List.length_map]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact ssSmall_nat (by omega) (by omega)
    · refine ssSmall_natList (fun x hx => ?_) (by simp; omega)
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      have := y.isLt; omega
    · exact ssSmall_tab' hs (by omega)

theorem size_ssSiftCtx (B : List (Fin n)) (T : List (SsSlot n)) :
    (ssSiftCtx B T).size ≤ T.length * (2 * n + 8) + 2 * B.length + 11 := by
  rw [ssSiftCtx, size_list_eq]
  have := size_ssEncTab T
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ssEncB, size_natList,
    size_nat, List.length_map]
  omega

/-- The sizes in the sifting loop, as a function of `Y`. -/
theorem ss_sift_sizes {Y L : ℕ} (hY : n + L + 2 ≤ Y) :
    L * n * (2 * n + 8) + 2 * n + 2 * L + 2 * L + 60 ≤ ssZ Y := by
  have h1 : 1 ≤ Y := by omega
  have e : L * n * (2 * n + 8) ≤ 10 * Y ^ 3 := by
    calc L * n * (2 * n + 8) ≤ Y * Y * (10 * Y) := Nat.mul_le_mul (Nat.mul_le_mul (by omega)
          (by omega)) (by omega)
      _ = 10 * Y ^ 3 := by ring
  have h3 : Y ^ 3 ≤ Y ^ 4 := ss_pow_le h1 (by norm_num)
  have h4 : Y ≤ Y ^ 4 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ 4 := ss_pow_le h1 (by norm_num)
  unfold ssZ
  omega

/-- The parts of the sifting loop. -/
structure SsSiftAt (P : Program) (b comp inv : ℕ) : Prop where
  iter : P.HasAt b (iterFuns b (b + 3))
  step : P.funs[b + 3]? = some (ssSiftStepF comp inv)
  comp : P.HasAt comp (composeFuns comp)
  inv : P.HasAt inv (invFuns inv)

/-- The cost of sifting. -/
def ssSiftCost (Y : ℕ) : ℕ := 10 ^ 6 * (ssW Y + 1) ^ 2

theorem ss_sift_cost {n L W A c : ℕ}
    (hc : c ≤ L * (100 * (W + 1) + permK * (n + 1) ^ 3 + invK * (n + 1) ^ 4) +
      loopModK * (L + 1) * (A + L + W + 1))
    (hA : A ≤ W) (hn : (n + 1) ^ 4 ≤ W) (hL : L + 2 ≤ W) : c ≤ 10 ^ 6 * (W + 1) ^ 2 := by
  have h3 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e1 : 100 * (W + 1) + permK * (n + 1) ^ 3 + invK * (n + 1) ^ 4 ≤ 200000 * (W + 1) := by
    unfold permK invK; omega
  have e2 : L * (100 * (W + 1) + permK * (n + 1) ^ 3 + invK * (n + 1) ^ 4) ≤
      (W + 1) * (200000 * (W + 1)) := Nat.mul_le_mul (by omega) e1
  have e3 : loopModK * (L + 1) * (A + L + W + 1) ≤ 1000 * (W + 1) * (3 * (W + 1)) := by
    unfold loopModK
    exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) (by omega)
  have : (W + 1) * (200000 * (W + 1)) + 1000 * (W + 1) * (3 * (W + 1)) ≤ 10 ^ 6 * (W + 1) ^ 2 := by
    ring_nf; omega
  omega

/-- **Sifting.** -/
theorem ssSiftLoop_spec {P : Program} {b comp inv : ℕ} (hP : SsSiftAt P b comp inv)
    (B : List (Fin n)) (T : List (SsSlot n)) (hT : T.length = B.length * n) {Y : ℕ}
    (hY : n + B.length + 2 ≤ Y) (hidx : ∀ s ∈ T, ∀ e, s = some e → e.2 ≤ ssZ Y)
    (g : Perm (Fin n)) :
    FunAll P b (.list [ssSiftCtx B T, .nat B.length, ssEncAcc (g, [], 0)])
      (fun w c => w = ssEncAcc (ssSift B T g) ∧ c ≤ ssSiftCost Y) := by
  obtain ⟨hW3, hW4, hW5, hW6⟩ := ssW_ge (n := n) (L := B.length) hY
  have hsz := ss_sift_sizes (n := n) (L := B.length) hY
  set W := ssW Y with hWdef
  set Z := ssZ Y with hZdef
  have hZ1 : 1 ≤ Z := by omega
  have facts := ssSift_acc_facts B T hidx g
  -- weights
  have hctx : SsSmall Z (ssSiftCtx B T) := ssSmall_ctx B T hidx (by rw [hT]; omega)
  have hacc : ∀ i, i ≤ B.length →
      SsSmall Z (ssEncAcc ((List.range i).foldl (ssSiftStep B T) (g, [], 0))) := fun i hi =>
    ssSmall_acc _ (facts i).2.1 ((facts i).2.2.trans (by omega)) (by have := (facts i).1; omega)
  have harg : ∀ i j, i ≤ B.length → j ≤ B.length → SsSmall Z (.list [ssSiftCtx B T, .nat i,
      ssEncAcc ((List.range j).foldl (ssSiftStep B T) (g, [], 0))]) := fun i j hi hj => by
    refine ssSmall_list ?_ fun v hv => ?_
    · rw [size_list_eq]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, size_nat,
        size_ssEncAcc]
      have := size_ssSiftCtx B T
      have := (facts j).1
      rw [hT] at *
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact hctx
      · exact ssSmall_nat (by omega) (by omega)
      · exact hacc j hj
  have hstep : ∀ i acc, i < B.length →
      acc = ssEncAcc ((List.range i).foldl (ssSiftStep B T) (g, [], 0)) →
      FunAll P (b + 3) (.list [ssSiftCtx B T, .nat i, acc]) (fun w cost =>
        w = ssEncAcc ((List.range (i + 1)).foldl (ssSiftStep B T) (g, [], 0)) ∧
        cost ≤ 100 * (W + 1) + permK * (n + 1) ^ 3 + invK * (n + 1) ^ 4) := by
    rintro i acc hi rfl
    have hr : (List.range (i + 1)).foldl (ssSiftStep B T) (g, [], 0) =
        ssSiftStep B T ((List.range i).foldl (ssSiftStep B T) (g, [], 0)) i := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hr]
    refine FunAll.mono (ssSiftStepF_spec hP.step hP.comp hP.inv B T hT _ hi
      ((harg i i hi.le hi.le).wt_le) (by rw [← hr]; exact (hacc (i + 1) hi).wt_le) hW3 hW4)
      fun w c ⟨hw, hc⟩ => ⟨hw, hc⟩
  refine (iter_spec hP.iter (Inv := fun i acc =>
      acc = ssEncAcc ((List.range i).foldl (ssSiftStep B T) (g, [], 0))) (M := W)
    (B := fun _ => 100 * (W + 1) + permK * (n + 1) ^ 3 + invK * (n + 1) ^ 4)
    (by beta_reduce; rw [List.range_zero, List.foldl_nil])
    (fun i acc hi h => by rw [h]; exact (hacc i hi).wt_le) hstep).mono fun w c ⟨hw, hc⟩ => ?_
  refine ⟨by rw [hw, ssSift], ?_⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
  have ha0 := (harg B.length 0 le_rfl (Nat.zero_le _)).wt_le
  simp only [List.range_zero, List.foldl_nil] at ha0
  unfold ssSiftCost
  exact ss_sift_cost hc ha0 hW5 hW6

end GI.Impl
