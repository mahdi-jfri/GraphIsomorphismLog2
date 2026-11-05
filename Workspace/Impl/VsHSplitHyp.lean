module

public import Workspace.Impl.VsHPcData

@[expose] public section

/-!
# The hard case with `k ≥ 1`

With the isotropic family `K` of the front, `|K| = k ≥ 1`: the pieces of `𝔽_p[A ∪ ρ K]` are
`r^k` pieces of a split (`VsHHyp.split`), and the orbit bound `|Ȳ : S|^69 r r^k` is at most
`(r^k + 1)^278` (`vsH_bound_le`).
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime] {hs : VsQStOK s}
  {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ys : List (Perm (Fin I.n))} {r : ℕ}

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-- The orbit bound of the hard case. -/
noncomputable def vsHBound (hs : VsQStOK s) (as ys : List (Perm (Fin I.n))) (r k : ℕ) : ℕ :=
  (vsHS hs as).relIndex (vsHY hs as ys) ^ 69 * r * r ^ k

theorem VsHHyp.split (h : VsHHyp hs as Lb ys r) :
    let K := vsHK s Lb r ys
    (∀ g ∈ K, g ∈ gens s.hs) ∧
    (∀ x ∈ as ++ K, ∀ y ∈ as ++ K, vsPRho hs x * vsPRho hs y = vsPRho hs y * vsPRho hs x) ∧
    (vsHS hs as).relIndex (vsHY hs as ys) ≤ r ^ (2 * K.length + 2) ∧
    VsMPiecesOut (vsPBar hs (gens s.hs)) (vsMAlgE (vsPBar hs (gens as)) (vsHEf hs K))
      (r ^ K.length) (vsHBound hs as ys r K.length) := by
  intro K
  haveI := vsH_nontrivial h.hard
  obtain ⟨hiso, hKE⟩ := h.iso
  have hKs : ∀ g ∈ K, g ∈ gens s.hs := fun g hg => (h.inE g (hKE g hg)).1
  have hKY : ∀ g ∈ K, vsPRho hs g ∈ vsHY hs as ys := fun g hg => (h.inE g (hKE g hg)).2
  obtain ⟨hidx, -, hpc⟩ := vsM_hard (p := I.p) (V := Fin (vsQD s) → ZMod I.p) _ _ _ r K.length
    (vsHEf hs K) h.hard hiso
  refine ⟨hKs, fun x hx y hy => ?_, hidx, hpc⟩
  have hA := h.hard.2.1.2.2
  have hYC := h.hard.2.2.2.2.2.1
  have hAs : ∀ a ∈ as, vsPRho hs a ∈ vsPBar hs (gens as) := fun a ha =>
    vsPRho_mem_vsPBar hs (Subgroup.subset_closure ha) (h.has (Subgroup.subset_closure ha))
  have hcK : ∀ x ∈ K, ∀ y ∈ K, vsPRho hs x * vsPRho hs y = vsPRho hs y * vsPRho hs x := by
    intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    exact hiso.2.2.1 ⟨i, hi⟩ ⟨j, hj⟩
  have hcAK : ∀ x ∈ as, ∀ y ∈ K, vsPRho hs x * vsPRho hs y = vsPRho hs y * vsPRho hs x := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.1 (hYC (hKY y hy)) _ (hAs x hx)
  rcases List.mem_append.1 hx with hx | hx <;> rcases List.mem_append.1 hy with hy | hy
  · exact hA _ (hAs x hx) _ (hAs y hy)
  · exact hcAK x hx y hy
  · exact (hcAK y hy x hx).symm
  · exact hcK x hx y hy

/-- **The bound.** -/
theorem vsH_bound_le {r k Yi : ℕ} (hr : 2 ≤ r) (hk : 1 ≤ k) (hY : Yi ≤ r ^ (2 * k + 2)) :
    Yi ^ 69 * r * r ^ k ≤ (r ^ k + 1) ^ 278 := by
  have h1 : Yi ^ 69 * r * r ^ k ≤ (r ^ (2 * k + 2)) ^ 69 * r * r ^ k :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hY 69))
  have h2 : (r ^ (2 * k + 2)) ^ 69 * r * r ^ k = r ^ (139 * k + 139) := by
    rw [← pow_mul, mul_assoc, ← pow_succ', ← pow_add]; congr 1; ring
  have h3 : r ^ (139 * k + 139) ≤ (r ^ k) ^ 278 := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by nlinarith)
  have h4 : (r ^ k) ^ 278 ≤ (r ^ k + 1) ^ 278 := Nat.pow_le_pow_left (by omega) _
  omega

end GI.Impl
