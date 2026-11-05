module

public import Workspace.Impl.CamXFactors
public import Workspace.Impl.CamXParams
public import Workspace.Lang.Prims.Repr

@[expose] public section

/-!
# Step 3 of `camProg`: the invariant of the factor loop

The loop splits the socle `N = camProd e univ` into its simple factors. After `i` rounds it holds
the current group `Cur` and the factors found so far, as pairs `(index, generators)`:
`Cur = camProd e S` for the indices `S` not found yet (`CamInv`). A round with `Cur ≠ 1` takes the
last nontrivial term `T = camProd e {i₀}` of a chief series of `Cur` (`camX_factor_chief_last`),
records it, and replaces `Cur` by its centralizer in `Cur`, `camProd e (S.erase i₀)`
(`camX_centralizer`). A round with `Cur = 1` changes nothing.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

variable {n m k r : ℕ}

/-- The indices of the factors found. -/
abbrev camFsts (ps : List (Fin r × List (Perm (Fin n)))) : List (Fin r) := ps.map Prod.fst

/-- The accumulator `[Cur, [T₀, T₁, …]]`. -/
def camAcc (cur : List (Perm (Fin n))) (ps : List (Fin r × List (Perm (Fin n)))) : Val :=
  .list [encGroup cur, .list (ps.map fun p => encGroup p.2)]

/-- **The invariant after `i` rounds.** -/
def CamInv (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) (i : ℕ) (acc : Val) :
    Prop :=
  ∃ (cur : List (Perm (Fin n))) (ps : List (Fin r × List (Perm (Fin n)))),
    acc = camAcc cur ps ∧ cur.length ≤ n ^ 2 ∧
    (∀ p ∈ ps, gens p.2 = camProd e {p.1} ∧ p.2.length ≤ n ^ 2) ∧ (camFsts ps).Nodup ∧
    gens cur = camProd e (Finset.univ \ (camFsts ps).toFinset) ∧ ps.length = min i r

theorem cam_card_fsts {ps : List (Fin r × List (Perm (Fin n)))} (h : (camFsts ps).Nodup) :
    ((camFsts ps).toFinset).card = ps.length := by
  rw [List.toFinset_card_of_nodup h]; simp

/-- When nothing is left, all `r` factors are found. -/
theorem cam_fsts_full {ps : List (Fin r × List (Perm (Fin n)))} (h : (camFsts ps).Nodup)
    (he : Finset.univ \ (camFsts ps).toFinset = ∅) : ps.length = r := by
  have hu : (camFsts ps).toFinset = Finset.univ := by
    rw [Finset.sdiff_eq_empty_iff_subset] at he
    exact Finset.eq_univ_of_forall fun x => he (Finset.mem_univ x)
  rw [← cam_card_fsts h, hu, Finset.card_univ, Fintype.card_fin]

/-- When something is left, fewer than `r` factors are found. -/
theorem cam_fsts_lt {ps : List (Fin r × List (Perm (Fin n)))} (h : (camFsts ps).Nodup)
    {i : Fin r} (hi : i ∈ Finset.univ \ (camFsts ps).toFinset) : ps.length < r := by
  rw [← cam_card_fsts h]
  have : (camFsts ps).toFinset ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun he => ?_⟩
    rw [he] at hi; simp at hi
  simpa using Finset.card_lt_card this

/-- The order of the current group: `1` exactly when nothing is left. -/
theorem cam_card_cur_eq_one (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}))
    (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hkm : k < m) (S : Finset (Fin r)) :
    Nat.card (camProd e S) = 1 ↔ S = ∅ := by
  rw [camX_card_prod (by omega) hk1 hkm]
  have h120 : 3 ≤ m.factorial / 2 := by
    have h5 : Nat.factorial 5 ≤ m.factorial := Nat.factorial_le hm
    have : Nat.factorial 5 = 120 := by decide
    omega
  constructor
  · intro h
    by_contra hS
    have hc : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    have : 3 ^ S.card ≤ (m.factorial / 2) ^ S.card := Nat.pow_le_pow_left h120 _
    have : 3 ≤ 3 ^ S.card := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ S.card := Nat.pow_le_pow_right (by norm_num) hc
    omega
  · rintro rfl; simp

/-- The centralizer of the found factor, as the output of the cited task. -/
theorem cam_cent_erase (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}))
    (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hkm : k < m) {S : Finset (Fin r)} {i : Fin r} (hi : i ∈ S)
    {C : Subgroup (Perm (Fin n))}
    (hC : ∀ y, y ∈ C ↔ y ∈ camProd e S ∧ ∀ x ∈ camProd e {i}, y * x * y⁻¹ * x⁻¹ ∈
      (⊥ : Subgroup (Perm (Fin n)))) :
    C = camProd e (S.erase i) := by
  ext y
  rw [hC y, ← SetLike.mem_coe (x := y) (p := camProd e (S.erase i)), ← camX_centralizer hm hk1 hkm hi]
  rfl

/-- `univ \ (fsts ++ [i]) = (univ \ fsts).erase i`. -/
theorem cam_sdiff_snoc (ps : List (Fin r × List (Perm (Fin n)))) (q : Fin r × List (Perm (Fin n))) :
    Finset.univ \ (camFsts (ps ++ [q])).toFinset =
      (Finset.univ \ (camFsts ps).toFinset).erase q.1 := by
  ext x
  simp only [camFsts, List.map_append, List.map_cons, List.map_nil, List.toFinset_append,
    Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, List.mem_toFinset,
    Finset.mem_erase]
  simp only [List.mem_singleton, List.mem_map]
  constructor <;> intro h <;> [exact ⟨fun h1 => h (Or.inr h1), fun h1 => h (Or.inl h1)⟩; exact fun h1 => h1.elim h.2 h.1]

end GI.Impl
