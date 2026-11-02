import Workspace.Impl.AggItemCiSojAut

/-!
# Extending the projected matrix group over the omitted labels

The paper projects to the left side and allows arbitrary permutations outside it,
with even parity imposed. Starting from the complete permitted matrix group, it
is enough to add the even permutations fixing the left side pointwise. We compute
these with the existing coloring stabilizer program: give each left point its own
color and give the omitted labels one common color.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm Finset
open GI.Cited (gens)

variable {q : ℕ} {W R : Finset (Fin q)}

/-- Individual colors on the left side, one common color on its complement. -/
def itcsFixColor (W : Finset (Fin q)) (a : Fin q) : ℕ := if a ∈ W then a.val + 1 else 0

/-- Its color stabilizer is exactly pointwise fixing the left side. -/
theorem itcs_fix_color (W : Finset (Fin q)) (g : Perm (Fin q)) :
    (∀ a, itcsFixColor W (g a) = itcsFixColor W a) ↔ ∀ a ∈ W, g a = a := by
  constructor
  · intro h a ha
    have hh := h a
    have hga : g a ∈ W := by
      by_contra hn
      simp only [itcsFixColor, if_pos ha, if_neg hn] at hh
      omega
    simp only [itcsFixColor, if_pos ha, if_pos hga] at hh
    exact Fin.ext (by omega)
  · intro h a
    by_cases ha : a ∈ W
    · rw [h a ha]
    · have hga : g a ∉ W := by
        intro hga
        have he := h (g a) hga
        have he' : g a = a := g.injective he
        exact ha (he' ▸ hga)
      simp only [itcsFixColor, if_neg ha, if_neg hga]

/-- The even color stabilizer fixes the left side pointwise. -/
theorem itcs_fix_even (W : Finset (Fin q)) (g : alternatingGroup (Fin q)) :
    g ∈ evenStab (q := q) (classPart (itcsFixColor W)) ↔ ∀ a ∈ W, (g : Perm (Fin q)) a = a := by
  rw [mem_evenStab, itci_classPart_iff]
  exact itcs_fix_color W _

/-- The model's full left group is exactly the matrix group extended by even
permutations fixing its left side. -/
theorem itcs_left_group (M : W → R → Bool) :
    leftGroup M = (itcsMatrixAut M).map (permitted W R).subtype ⊔
      evenStab (q := q) (classPart (itcsFixColor W)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨h, hh, hagree⟩ := hg
    have hhmem : (h : alternatingGroup (Fin q)) ∈ (itcsMatrixAut M).map (permitted W R).subtype :=
      ⟨h, hh, rfl⟩
    have hk : (h : alternatingGroup (Fin q))⁻¹ * g ∈
        evenStab (q := q) (classPart (itcsFixColor W)) := by
      rw [itcs_fix_even]
      intro a ha
      change (h : Perm (Fin q))⁻¹ ((g : Perm (Fin q)) a) = a
      rw [hagree a ha, Perm.inv_apply_self]
    have hp := Subgroup.mul_mem ((itcsMatrixAut M).map (permitted W R).subtype ⊔
      evenStab (q := q) (classPart (itcsFixColor W)))
      (Subgroup.mem_sup_left hhmem) (Subgroup.mem_sup_right hk)
    simpa only [mul_inv_cancel_left] using hp
  · apply sup_le
    · rintro g ⟨h, hh, rfl⟩
      exact mem_leftOvercoset hh
    · intro g hg
      exact ⟨1, matrixTransports_one M, fun a ha => (itcs_fix_even W g).1 hg a ha⟩

/-- Mapping a finite generating list maps its generated subgroup. -/
theorem itcs_closure_map {G : Type*} [Group G] (f : G →* Perm (Fin q)) (ls : List G) :
    gens (ls.map f) = (itcsClosure ls).map f := by
  unfold gens itcsClosure
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp

/-- Program generators of the pointwise-fixing even subgroup. -/
theorem itcs_fix_gens (W : Finset (Fin q)) :
    gens (itciMs (itcsFixColor W) (itciOt (itcsFixColor W))) =
      (evenStab (q := q) (classPart (itcsFixColor W))).map (alternatingGroup (Fin q)).subtype := by
  have hcl : gens (itciT (itcsFixColor W)) =
      MulAction.stabilizer (Perm (Fin q)) (classPart (itcsFixColor W)) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, itci_classPart_iff]
    exact ⟨fun h a => itci_keep_of_mem h a, itci_mem_closure⟩
  rw [itciMs_gens (itciOt_spec _), hcl, itp_evenStab_map]

private theorem itcs_append (as bs : List (Perm (Fin q))) :
    gens (as ++ bs) = gens as ⊔ gens bs := by
  unfold gens
  rw [← Subgroup.closure_union]
  congr 1
  ext g
  simp

/-- The program's full-label generators after projecting the complete matrix group. -/
noncomputable def itcsLeftGens (W R : Finset (Fin q)) (ls : List (permitted W R)) : List (Perm (Fin q)) :=
  ls.map (fun h => (h.val : Perm (Fin q))) ++ itciMs (itcsFixColor W) (itciOt (itcsFixColor W))

/-- The resulting list generates exactly the group of `sojItem`'s overcoset. -/
theorem itcs_left_gens (M : W → R → Bool) (ls : List (permitted W R))
    (hls : itcsClosure ls = itcsMatrixAut M) :
    gens (itcsLeftGens W R ls) = (leftGroup M).map (alternatingGroup (Fin q)).subtype := by
  let f : permitted W R →* Perm (Fin q) :=
    (alternatingGroup (Fin q)).subtype.comp (permitted W R).subtype
  have hm : gens (ls.map fun h => (h.val : Perm (Fin q))) = (itcsMatrixAut M).map f := by
    change gens (ls.map f) = _
    rw [itcs_closure_map f ls, hls]
  rw [itcsLeftGens, itcs_append, hm, itcs_fix_gens, itcs_left_group, Subgroup.map_sup,
    Subgroup.map_map]

end GI.Impl
