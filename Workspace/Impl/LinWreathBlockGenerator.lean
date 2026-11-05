module

public import Workspace.Impl.LinWreathBlockFormula

@[expose] public section

/-! The three dense blocks are the generator images of the actual wreath
representation, rather than unrelated matrices with the same dimensions. -/
namespace GI.Impl
open Equiv
variable {R H : Type*} [CommRing R] [Group H] {d : ℕ}

def linWreathGeneratorElement (mode : Fin 3) (h : H) : H ≀ᵣ linTwo :=
  if mode.val = 0 then linWreathSingle 1 h else
    if mode.val = 1 then linWreathSingle linTwoSwap h else linWreathSwap

theorem linWreathBlock_generator (hd : 0 < d)
    (φ : H →* Matrix.GeneralLinearGroup (Fin d) R) (h : H) (mode : Fin 3) :
    linWreathBlock hd (φ h).val mode =
      (linWreathMatrixRep φ (linWreathGeneratorElement mode h)).val := by
  ext i j
  obtain ⟨⟨i, q⟩, rfl⟩ := (linWreathNumber d).surjective i
  obtain ⟨⟨j, r⟩, rfl⟩ := (linWreathNumber d).surjective j
  rw [linWreathMatrixRep_entry]
  set_option backward.isDefEq.respectTransparency false in
    fin_cases mode <;> rcases linTwo_cases q with rfl | rfl <;>
      rcases linTwo_cases r with rfl | rfl <;>
      simp [linWreathGeneratorElement, linWreathSingle, linWreathSwap, linWreathBlock,
      i.isLt, j.isLt, Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt,
      Matrix.one_apply, Fin.ext_iff, Ne.symm linTwoSwap_ne_one]

end GI.Impl
