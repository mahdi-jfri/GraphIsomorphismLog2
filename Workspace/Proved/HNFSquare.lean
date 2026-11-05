module

public import Workspace.Proved.HNFBareiss
public import Workspace.Proved.HNFMod
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

/-!
# Squaring up a matrix of full column rank

Bareiss elimination (`Workspace/Proved/HNFBareiss.lean`) gives `c` distinct rows `s` of the
`r × c` matrix `A` whose block `B = A[s, :]` has determinant `d ≠ 0`. We add `r - c` unit
columns: for each row `i ∉ s`, in increasing order, the column `e_i` (`hnfAp`). The square
matrix `A' = [A | E]` has two properties.

* Its determinant is nonzero (`hnfAp_det_ne`): a row vector `x` with `x A' = 0` vanishes off
  `s` because of the unit columns, and on `s` because `B` is nonsingular.
* `d e_j` lies in its row lattice for every `j` (`hnfAp_single_mem`). For `j < c` this is row `j`
  of `adj(B) B = d I`. For the unit column of a row `i ∉ s`, subtract from `d · (row i)` the
  combination `(A_i adj B)` of the rows in `s`.
-/

namespace GI.Proved

open Matrix GI.Cited

variable {r c : ℕ}

/-- The rows not in `s`, in increasing order. -/
def hnfCompl (s : List (Fin r)) : List (Fin r) := (List.finRange r).filter fun i => i ∉ s

theorem mem_hnfCompl {s : List (Fin r)} {i : Fin r} : i ∈ hnfCompl s ↔ i ∉ s := by
  simp [hnfCompl]

theorem hnfCompl_nodup (s : List (Fin r)) : (hnfCompl s).Nodup :=
  (List.nodup_finRange r).filter _

theorem hnfCompl_length {s : List (Fin r)} (hs : s.Nodup) :
    (hnfCompl s).length = r - s.length := by
  have h := (List.length_eq_length_filter_add (l := List.finRange r)
    (fun i => decide (i ∈ s))).symm
  have hperm : ((List.finRange r).filter fun i => decide (i ∈ s)).Perm s := by
    rw [List.perm_ext_iff_of_nodup ((List.nodup_finRange r).filter _) hs]
    intro i; simp
  rw [hperm.length_eq, List.length_finRange] at h
  have e : hnfCompl s = (List.finRange r).filter fun i => !decide (i ∈ s) := by
    simp [hnfCompl]
  rw [e]
  omega

/-- The square matrix `[A | E]`. -/
def hnfAp (A : Matrix (Fin r) (Fin c) ℤ) (s : List (Fin r)) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j => if h : (j : ℕ) < c then A i ⟨j, h⟩
    else if (hnfCompl s)[(j : ℕ) - c]? = some i then 1 else 0

/-- The block of `A` on the rows `s`. -/
def hnfB (A : Matrix (Fin r) (Fin c) ℤ) (s : List (Fin r)) (x : Fin r) :
    Matrix (Fin c) (Fin c) ℤ :=
  A.submatrix (hnfRowSel s x c) id

/-- The hypotheses on the chosen rows. -/
structure HnfRows (A : Matrix (Fin r) (Fin c) ℤ) (s : List (Fin r)) (x : Fin r) : Prop where
  len : s.length = c
  nodup : s.Nodup
  det_ne : (hnfB A s x).det ≠ 0

theorem hnfRowSel_injective {s : List (Fin r)} {x : Fin r} (hlen : s.length = c)
    (hs : s.Nodup) : Function.Injective (hnfRowSel s x c) := by
  intro a b hab
  simp only [hnfRowSel] at hab
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hab
  exact Fin.ext ((List.Nodup.getElem_inj_iff hs).mp hab)

theorem hnfRowSel_mem {s : List (Fin r)} {x : Fin r} (hlen : s.length = c) (a : Fin c) :
    hnfRowSel s x c a ∈ s := by
  simp only [hnfRowSel]
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

theorem hnfRowSel_surj {s : List (Fin r)} {x : Fin r} (hlen : s.length = c) {i : Fin r}
    (hi : i ∈ s) : ∃ a : Fin c, hnfRowSel s x c a = i := by
  obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hi
  refine ⟨⟨a, by omega⟩, ?_⟩
  simp only [hnfRowSel]
  rw [List.getD_eq_getElem _ _ ha]

/-- Entries of `A'` on a chosen row: the row of `A`, then zeros. -/
theorem hnfAp_row_mem {A : Matrix (Fin r) (Fin c) ℤ} {s : List (Fin r)} {i : Fin r}
    (hi : i ∈ s) (j : Fin r) :
    hnfAp A s i j = if h : (j : ℕ) < c then A i ⟨j, h⟩ else 0 := by
  unfold hnfAp
  split_ifs with h1 h2
  · rfl
  · exfalso
    have := List.mem_of_getElem? h2
    exact mem_hnfCompl.mp this hi
  · rfl

/-- A combination of the chosen rows of `A'`. -/
theorem hnfAp_comb {A : Matrix (Fin r) (Fin c) ℤ} {s : List (Fin r)} {x : Fin r}
    (hlen : s.length = c) (y : Fin c → ℤ) :
    ∑ a, y a • hnfAp A s (hnfRowSel s x c a) =
      fun j : Fin r => if h : (j : ℕ) < c then (y ᵥ* hnfB A s x) ⟨j, h⟩ else 0 := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hnfAp_row_mem (hnfRowSel_mem hlen _)]
  split_ifs with h
  · simp [vecMul, dotProduct, hnfB]
  · simp

/-- **`A'` is nonsingular.** -/
theorem hnfAp_det_ne {A : Matrix (Fin r) (Fin c) ℤ} {s : List (Fin r)} {x : Fin r}
    (h : HnfRows A s x) : (hnfAp A s).det ≠ 0 := by
  have hcr : c ≤ r := by
    have := h.nodup.length_le_card; have := h.len; simp only [Fintype.card_fin] at *; omega
  intro hdet
  obtain ⟨v, hv0, hv⟩ := exists_vecMul_eq_zero_iff.mpr hdet
  -- `v` vanishes off `s`
  have hoff : ∀ i, i ∉ s → v i = 0 := by
    intro i hi
    obtain ⟨t, ht, hti⟩ := List.mem_iff_getElem.mp (mem_hnfCompl.mpr hi)
    have hlt : c + t < r := by
      have := hnfCompl_length h.nodup (r := r); rw [h.len] at this; omega
    have := congrFun hv ⟨c + t, hlt⟩
    simp only [vecMul, dotProduct, Pi.zero_apply, hnfAp, show ¬ (c + t < c) by omega,
      dite_false, Nat.add_sub_cancel_left, List.getElem?_eq_getElem ht, hti, Option.some.injEq,
      mul_ite, mul_one, mul_zero] at this
    simpa [Finset.sum_ite_eq'] using this
  -- on `s` it is a left null vector of `B`
  have hB : (fun a => v (hnfRowSel s x c a)) ᵥ* hnfB A s x = 0 := by
    funext j
    have hj := congrFun hv ⟨j, by omega⟩
    simp only [vecMul, dotProduct, Pi.zero_apply] at hj ⊢
    rw [← hj]
    simp only [hnfAp, show (j : ℕ) < c from j.isLt, dite_true, hnfB, submatrix_apply, id]
    rw [← Finset.sum_image (f := fun i => v i * A i j)
      (fun a _ b _ hab => hnfRowSel_injective h.len h.nodup hab)]
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    have : i ∉ s := fun his => by
      obtain ⟨a, ha⟩ := hnfRowSel_surj (x := x) h.len his
      exact hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)
    simp [hoff i this]
  have hz : (fun a => v (hnfRowSel s x c a)) = 0 := by
    by_contra hne
    exact h.det_ne (exists_vecMul_eq_zero_iff.mp ⟨_, hne, hB⟩)
  apply hv0
  funext i
  by_cases his : i ∈ s
  · obtain ⟨a, rfl⟩ := hnfRowSel_surj (x := x) h.len his
    exact congrFun hz a
  · exact hoff i his

/-- **`d ℤ^r` lies in the row lattice of `A'`**, where `d = det B`. -/
theorem hnfAp_single_mem {A : Matrix (Fin r) (Fin c) ℤ} {s : List (Fin r)} {x : Fin r}
    (h : HnfRows A s x) (j : Fin r) :
    Pi.single j (hnfB A s x).det ∈ Submodule.span ℤ (Set.range (hnfAp A s)) := by
  set B := hnfB A s x with hBdef
  have hcomb : ∀ y : Fin c → ℤ, (fun j : Fin r => if h : (j : ℕ) < c then (y ᵥ* B) ⟨j, h⟩
      else 0) ∈ Submodule.span ℤ (Set.range (hnfAp A s)) := by
    intro y
    rw [← hnfAp_comb h.len y]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hadj : ∀ w : Fin c → ℤ, (w ᵥ* B.adjugate) ᵥ* B = B.det • w := by
    intro w
    rw [vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]
  by_cases hj : (j : ℕ) < c
  · have hm := hcomb (Pi.single ⟨j, hj⟩ 1 ᵥ* B.adjugate)
    rw [hadj] at hm
    convert hm using 1
    funext l
    by_cases hl : (l : ℕ) < c
    · simp only [hl, dite_true, Pi.smul_apply, smul_eq_mul]
      by_cases hlj : l = j
      · subst hlj; simp
      · have : (⟨l, hl⟩ : Fin c) ≠ ⟨j, hj⟩ := fun e => hlj (Fin.ext (by simpa using e))
        simp [hlj, this]
    · have : l ≠ j := fun e => hl (e ▸ hj)
      simp [hl, this]
  · have hcr : c ≤ r := by
      have := h.nodup.length_le_card; have := h.len; simp only [Fintype.card_fin] at *; omega
    have hlen := hnfCompl_length h.nodup (r := r)
    rw [h.len] at hlen
    have hjt : (j : ℕ) - c < (hnfCompl s).length := by omega
    set i0 := (hnfCompl s)[(j : ℕ) - c] with hi0
    have hm := Submodule.sub_mem _ (Submodule.smul_mem _ B.det
      (Submodule.subset_span (Set.mem_range_self i0)))
      (hcomb ((fun b => A i0 b) ᵥ* B.adjugate))
    rw [hadj] at hm
    convert hm using 1
    funext l
    by_cases hl : (l : ℕ) < c
    · have : l ≠ j := fun e => hj (e ▸ hl)
      simp [hl, this, hnfAp]
    · simp only [hl, dite_false, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_zero, hnfAp]
      have hlt : (l : ℕ) - c < (hnfCompl s).length := by omega
      simp only [List.getElem?_eq_getElem hlt, Option.some.injEq, hi0,
        List.Nodup.getElem_inj_iff (hnfCompl_nodup s)]
      by_cases hlj : l = j
      · subst hlj; simp
      · have : (l : ℕ) - c ≠ (j : ℕ) - c := fun e => hlj (Fin.ext (by omega))
        simp [hlj, this]

end GI.Proved
