import Workspace.Impl.CamNormalizer
import Workspace.Cited.AlgoCameron

/-!
# Moving a Maróti structure along changes of coordinates

`MarotiStructure G e` says that, read through `e`, the group `G` lies in `Sym(m) wr Sym(r)` and
contains `Alt(m)^r`. We show that it survives two changes of `e`:
* applying a permutation `π i` of `Fin m` in each coordinate `i` (`cam_maroti_transport`);
* replacing each `k`-set by its complement (`cam_maroti_compl`).

With the second one, every Maróti structure can be taken with `k ≤ m - k` (`cam_maroti_min`).
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n m k r : ℕ}

theorem cam_kSetPerm_symm (π : Perm (Fin m)) (S : {A : Finset (Fin m) // A.card = k}) :
    (kSetPerm π).symm S = kSetPerm π⁻¹ S := rfl

/-- Conjugating the action of `h` by the action of `π`. -/
theorem cam_kSetPerm_conj (π h : Perm (Fin m)) (S : {A : Finset (Fin m) // A.card = k}) :
    (kSetPerm π).symm (kSetPerm h (kSetPerm π S)) = kSetPerm (π⁻¹ * h * π) S := by
  rw [cam_kSetPerm_symm, cam_kSetPerm_mul, cam_kSetPerm_mul]
  rfl

/-- **Transport along coordinatewise permutations.** -/
theorem cam_maroti_transport {G : Subgroup (Perm (Fin n))}
    {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})} (π : Fin r → Perm (Fin m))
    (hM : MarotiStructure G e) :
    MarotiStructure G (e.trans (Equiv.piCongrRight fun i => kSetPerm (π i))) := by
  obtain ⟨h1, h2⟩ := hM
  refine ⟨fun g hg => ?_, fun h hh => ?_⟩
  · obtain ⟨σ, h, hgh⟩ := h1 g hg
    refine ⟨σ, fun i => π i * h i * (π (σ i))⁻¹, fun x => ?_⟩
    funext i
    show kSetPerm (π i) (e (g x) i) =
      kSetPerm (π i * h i * (π (σ i))⁻¹) (kSetPerm (π (σ i)) (e x (σ i)))
    rw [hgh x, cam_kSetPerm_mul, cam_kSetPerm_mul]
    simp only [Equiv.Perm.mul_apply]
    rw [← cam_kSetPerm_symm, Equiv.symm_apply_apply]
  · have hmem := h2 (fun i => (π i)⁻¹ * h i * π i) fun i => by
      have := Subgroup.Normal.conj_mem (inferInstance : (alternatingGroup (Fin m)).Normal)
        (h i) (hh i) (π i)⁻¹
      simpa using this
    convert hmem using 1
    ext x
    simp only [Equiv.trans_apply, Equiv.symm_trans_apply]
    congr 2
    funext i
    exact cam_kSetPerm_conj (π i) (h i) (e x i)

/-- The complement of a `k`-set of `Fin m`. -/
def camCompl (hk : k ≤ m) :
    {A : Finset (Fin m) // A.card = k} ≃ {A : Finset (Fin m) // A.card = m - k} where
  toFun S := ⟨S.1ᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.2]⟩
  invFun S := ⟨S.1ᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.2]; omega⟩
  left_inv S := by simp
  right_inv S := by simp

/-- Complements commute with the action of `Sym(m)`. -/
theorem cam_compl_kSetPerm (hk : k ≤ m) (h : Perm (Fin m))
    (S : {A : Finset (Fin m) // A.card = k}) :
    camCompl hk (kSetPerm h S) = kSetPerm h (camCompl hk S) := by
  apply Subtype.ext
  ext y
  show y ∈ (S.1.map h.toEmbedding)ᶜ ↔ y ∈ S.1ᶜ.map h.toEmbedding
  rw [Finset.mem_compl, Finset.mem_map_equiv, Finset.mem_map_equiv, Finset.mem_compl]

theorem cam_compl_symm_kSetPerm (hk : k ≤ m) (h : Perm (Fin m))
    (S : {A : Finset (Fin m) // A.card = m - k}) :
    (camCompl hk).symm (kSetPerm h S) = kSetPerm h ((camCompl hk).symm S) := by
  apply Subtype.ext
  ext y
  show y ∈ (S.1.map h.toEmbedding)ᶜ ↔ y ∈ S.1ᶜ.map h.toEmbedding
  rw [Finset.mem_compl, Finset.mem_map_equiv, Finset.mem_map_equiv, Finset.mem_compl]

/-- **Transport along complements.** -/
theorem cam_maroti_compl {G : Subgroup (Perm (Fin n))}
    {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})} (hk : k ≤ m)
    (hM : MarotiStructure G e) :
    MarotiStructure G (e.trans (Equiv.piCongrRight fun _ => camCompl hk)) := by
  obtain ⟨h1, h2⟩ := hM
  refine ⟨fun g hg => ?_, fun h hh => ?_⟩
  · obtain ⟨σ, h, hgh⟩ := h1 g hg
    refine ⟨σ, h, fun x => ?_⟩
    funext i
    simp only [Equiv.trans_apply, Equiv.piCongrRight_apply, hgh x]
    exact cam_compl_kSetPerm hk _ _
  · convert h2 h hh using 1
    ext x
    simp only [Equiv.trans_apply, Equiv.symm_trans_apply]
    congr 2
    funext i
    show (camCompl hk).symm (kSetPerm (h i) (camCompl hk (e x i))) = kSetPerm (h i) (e x i)
    rw [cam_compl_symm_kSetPerm, Equiv.symm_apply_apply]

/-- Every Maróti structure can be taken with `k ≤ m - k`, that is, on `min k (m - k)`-sets. -/
theorem cam_maroti_min {G : Subgroup (Perm (Fin n))}
    {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})} (hk : k ≤ m)
    (hM : MarotiStructure G e) :
    ∃ e' : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = min k (m - k)}),
      MarotiStructure G e' := by
  rcases le_total k (m - k) with h | h
  · rw [Nat.min_eq_left h]
    exact ⟨e, hM⟩
  · rw [Nat.min_eq_right h]
    exact ⟨_, cam_maroti_compl hk hM⟩

end GI.Impl
