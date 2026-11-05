module

public import Workspace.Impl.KRefMainSpec

@[expose] public section

/-!
# The task `KaryRefinementTask k` as a program fact

* `kref_cells`: every cell of the input `[0^n, c, c']` is at most its size plus one (the cell
  bound of the bridge `GI.Lang.polyTimeAt_ofVal_of_lang_cells`, with `A = E = 1`).
* `kref_main_spec`: the program `krefProg k` returns a correct output at cost at most
  `krefPolyK k * (wt + 1) ^ 36`, where `wt` is the weight of the input.

Correctness is `kref_joint` (`KRefStable.lean`), applied to the colorings after `2 n^k` rounds.
-/

namespace GI.Impl

open GI.Lang GI.Cited

variable {k : ℕ}

/-! ### Cells -/

theorem kref_cellsList_nat (L : List ℕ) :
    Val.cellsList (L.map Val.nat) = L.flatMap fun a => [0, a] := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem kref_length_cellsList_nat (L : List ℕ) :
    (Val.cellsList (L.map Val.nat)).length = 2 * L.length := by
  rw [kref_cellsList_nat]
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]; ring

theorem kref_mem_cells_natList {L : List ℕ} {a : ℕ} (ha : a ∈ (natList L).cells) :
    a ≤ 2 * L.length + 1 ∨ a ∈ L := by
  unfold natList at ha
  rw [cells_list, kref_length_cellsList_nat, kref_cellsList_nat] at ha
  simp only [List.length_map, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_flatMap] at ha
  rcases ha with rfl | rfl | rfl | ⟨b, hb, hab⟩
  · left; omega
  · left; omega
  · left; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
    rcases hab with rfl | rfl
    · left; omega
    · right; exact hb

theorem kref_size_natList (L : List ℕ) : (natList L).cells.length = 3 + 2 * L.length := by
  unfold natList
  rw [cells_list, List.length_append, kref_length_cellsList_nat]
  simp

/-- The input of the task. -/
def krefEnc (I : TwoColoringsInst k) : Val :=
  .list [.list (List.replicate I.n (.nat 0)), encKColoring I.c, encKColoring I.c']

theorem krefEnc_eq (I : TwoColoringsInst k) :
    krefEnc I = .list [natList (List.replicate I.n 0), natList ((krefTups I.n k).map I.c),
      natList ((krefTups I.n k).map I.c')] := by
  unfold krefEnc
  rw [kref_encK_eq, kref_encK_eq]
  simp [natList, List.map_replicate]

/-- **The cells of the input are at most its size plus one.** -/
theorem kref_cells (I : TwoColoringsInst k) :
    ∀ a ∈ (krefEnc I).cells, a ≤ 1 * ((krefEnc I).size + 1) ^ 1 := by
  intro a ha
  rw [one_mul, pow_one, size_eq_length]
  rw [krefEnc_eq] at ha ⊢
  set A := List.replicate I.n 0
  set B := (krefTups I.n k).map I.c
  set C := (krefTups I.n k).map I.c'
  have hlB : B.length = I.n ^ k := by simp [B, length_krefTups]
  have hlC : C.length = I.n ^ k := by simp [C, length_krefTups]
  have hsz : (Val.list [natList A, natList B, natList C]).cells.length =
      3 + ((natList A).cells.length + (natList B).cells.length + (natList C).cells.length) := by
    simp only [cells_list, cellsList_cons, cellsList_nil, List.length_append, List.length_cons,
      List.length_nil, List.append_nil]
    omega
  rw [hsz, kref_size_natList, kref_size_natList, kref_size_natList, hlB, hlC]
  simp only [cells_list, cellsList_cons, cellsList_nil, List.append_nil, List.length_cons,
    List.length_nil, List.length_append, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_append] at ha
  rw [kref_size_natList, kref_size_natList, kref_size_natList] at ha
  rcases ha with rfl | rfl | rfl | ha | ha | ha
  · omega
  · omega
  · omega
  · rcases kref_mem_cells_natList ha with h | h
    · omega
    · simp only [A, List.mem_replicate] at h; omega
  · rcases kref_mem_cells_natList ha with h | h
    · omega
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp h; have := I.c_le x; omega
  · rcases kref_mem_cells_natList ha with h | h
    · omega
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp h; have := I.c'_le x; omega

/-! ### The cost as a polynomial in the weight of the input -/

/-- The constant of the final cost bound. -/
def krefPolyK (k : ℕ) : ℕ := krefMainK * (1001 * (k ^ k + k + 4) ^ 4) ^ 9

theorem kref_X_le_wt (I : TwoColoringsInst k) :
    krefX I.n k ≤ (k ^ k + k + 4) * ((krefEnc I).wt + 1) := by
  have h1 : (Val.list (List.replicate I.n (.nat 0))).wt < (krefEnc I).wt :=
    wt_le_wt_list (by simp)
  have h2 : (encKColoring I.c).wt < (krefEnc I).wt := wt_le_wt_list (by simp)
  have h3 := length_lt_wt_list (List.replicate I.n (Val.nat 0))
  have h4 : (encKColoring I.c).wt > I.n ^ k := by
    unfold encKColoring
    have := length_lt_wt_list ((List.finRange (I.n ^ k)).map fun j =>
      Val.nat (I.c (finFunctionFinEquiv.symm j)))
    simpa using this
  rw [List.length_replicate] at h3
  have h5 : 4 * (krefEnc I).wt ≤ (k ^ k + k + 4) * (krefEnc I).wt :=
    Nat.mul_le_mul_right _ (by omega)
  have h6 : (k ^ k + k + 4) * ((krefEnc I).wt + 1) =
      (k ^ k + k + 4) * (krefEnc I).wt + (k ^ k + k + 4) := by ring
  unfold krefX
  omega

theorem kref_cost_poly (I : TwoColoringsInst k) :
    krefMainK * (krefZ I.n k + 1) ^ 9 ≤ krefPolyK k * ((krefEnc I).wt + 1) ^ 36 := by
  have hX := kref_X_le_wt I
  have hX1 : 1 ≤ krefX I.n k := le_trans (by norm_num) (@krefX_two I.n k)
  obtain ⟨W, hW⟩ : ∃ W, W = (krefEnc I).wt + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = k ^ k + k + 4 := ⟨_, rfl⟩
  rw [← hW, ← hc] at hX
  have h1 : krefZ I.n k + 1 ≤ 1001 * c ^ 4 * W ^ 4 := by
    unfold krefZ
    have h2 : krefX I.n k ^ 4 ≤ (c * W) ^ 4 := Nat.pow_le_pow_left hX 4
    have h3 : 1 ≤ krefX I.n k ^ 4 := Nat.one_le_pow _ _ hX1
    rw [mul_pow] at h2
    rw [Nat.mul_assoc]
    omega
  have h4 : (krefZ I.n k + 1) ^ 9 ≤ (1001 * c ^ 4 * W ^ 4) ^ 9 := Nat.pow_le_pow_left h1 9
  have e : (1001 * c ^ 4 * W ^ 4) ^ 9 = (1001 * c ^ 4) ^ 9 * W ^ 36 := by
    rw [mul_pow, ← pow_mul]
  rw [← hW]
  calc krefMainK * (krefZ I.n k + 1) ^ 9 ≤ krefMainK * (1001 * c ^ 4 * W ^ 4) ^ 9 :=
        Nat.mul_le_mul_left _ h4
    _ = krefPolyK k * W ^ 36 := by rw [e, ← mul_assoc, krefPolyK, hc]

/-! ### The specification -/

/-- **The program solves the task**, at cost `krefPolyK k * (wt + 1) ^ 36`. -/
theorem kref_main_spec (I : TwoColoringsInst k) :
    FunAll (krefProg k) 0 (krefEnc I) (fun v c =>
      (∃ d d' : (Fin k → Fin I.n) → ℕ, v = .list [encKColoring d, encKColoring d'] ∧
        (∀ x, d x < 2 * I.n ^ k) ∧ (∀ x, d' x < 2 * I.n ^ k) ∧ JointRefinement I.c I.c' d d') ∧
      c ≤ krefPolyK k * ((krefEnc I).wt + 1) ^ 36) := by
  have h := kref_main_det I.c I.c' I.c_le I.c'_le
  refine FunAll.mono h fun v c hv => ⟨?_, hv.2.trans (kref_cost_poly I)⟩
  obtain ⟨hd, hd', hJ⟩ := kref_joint I.c I.c' I.c_le I.c'_le
  refine ⟨_, _, ?_, hd, hd', hJ⟩
  rw [hv.1, kref_St_eq]

end GI.Impl
