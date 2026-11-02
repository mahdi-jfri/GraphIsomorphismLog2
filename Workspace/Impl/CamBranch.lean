import Workspace.Impl.CamHalf
import Workspace.Impl.CamSmallM
import Workspace.Lang.Prims.Other

/-!
# The normal form of a Maróti structure, and the two large-order answers

`cam_normal_form` collects steps 2–4 of the reduction of `camProg` (`CamProg.lean`): above the order
threshold, a primitive group of degree `n ≥ 25` has a Maróti structure with `m ≥ 5`, `k ≥ 1` and
`2k < m`. With `2k < m`, `min k (m - k) = k`, so the answers `[1, …]` and `[2]` of the task are
read off directly (`cam_out_one`, `cam_out_two`).
-/

namespace GI.Impl

open Equiv GI.Cited GI.Lang

variable {n : ℕ}

/-- **Normal form.** Above the order threshold, Maróti's theorem gives a structure with
`m ≥ 5`, `1 ≤ k` and `2k < m`. -/
theorem cam_normal_form (hMa : MarotiPrimitive) {G : Subgroup (Perm (Fin n))} (hn : 25 ≤ n)
    (hprim : MulAction.IsPreprimitive G (Fin n)) (hbig : n ^ (1 + Nat.log 2 n) ≤ Nat.card G) :
    ∃ (m k r : ℕ) (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
      MarotiStructure G e ∧ 5 ≤ m ∧ 1 ≤ k ∧ 2 * k < m := by
  rcases hMa n hn G hprim with h | ⟨m, k, r, e, hM⟩
  · omega
  have hM : MarotiStructure G e := hM
  have h5 := cam_five_le hM hn hbig
  have hne := cam_n_eq e
  have hkm : k ≤ m := by
    by_contra hk
    rw [Nat.choose_eq_zero_of_lt (by omega)] at hne
    rcases Nat.eq_zero_or_pos r with hr | hr
    · rw [hr] at hne; omega
    · rw [zero_pow (by omega)] at hne; omega
  obtain ⟨e', hM'⟩ := cam_maroti_min hkm hM
  have hne' := cam_n_eq e'
  refine ⟨m, min k (m - k), r, e', hM', h5, ?_, ?_⟩
  · by_contra h0
    rw [show min k (m - k) = 0 by omega, Nat.choose_zero_right, one_pow] at hne'
    omega
  · have := cam_two_mul_ne hprim (by omega) hM'
    omega

theorem cam_min_eq {m k : ℕ} (hk : 2 * k < m) : min k (m - k) = k := by omega

/-- **The answer `[2]`.** -/
theorem cam_out_two {G : Subgroup (Perm (Fin n))} {m k r : ℕ}
    {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})} (hM : MarotiStructure G e)
    (hk : 2 * k < m) (h : m + 2 ≤ (k + 1) ^ 2) : CameronOut G (.list [.nat 2]) :=
  Or.inr (Or.inr ⟨rfl, m, k, r, e, by rw [cam_min_eq hk]; exact h, hM⟩)

/-- **The answer `[1, m, k, r, E]`.** -/
theorem cam_out_one {G : Subgroup (Perm (Fin n))} {m k r : ℕ}
    {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})} (hM : MarotiStructure G e)
    (hk : 2 * k < m) (h : (k + 1) ^ 2 < m + 2) :
    CameronOut G (.list [.nat 1, .nat m, .nat k, .nat r, encKSetTuples e]) :=
  Or.inr (Or.inl ⟨m, k, r, e, by rw [cam_min_eq hk]; exact h, hM, rfl⟩)

end GI.Impl
