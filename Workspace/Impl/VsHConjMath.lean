module

public import Workspace.Impl.VsHFront
public import Workspace.Impl.VsQSot

@[expose] public section

/-!
# Conjugation of local matrices

The `Q₈` branch computes the centralizer of `Ȳ` in `C` with the small orbit transporter, for
the action of permutations on matrices `g · M = T(g⁻¹) M T(g)`, `T(g) = Λ(g)ᵀ` (the stored local
matrix of `g` is `T(g)`). This is an action of `⟨hs⟩` (`vsH_conj_act`), and `g` fixes `T(b)`
iff `ρ g` commutes with `ρ b` (`vsH_conj_fix`).
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I}

/-- `T(g) = Λ(g)ᵀ`, the matrix of the stored local matrix of `g`. -/
noncomputable def vsHT (s : VsQSt I) (g : Perm (Fin I.n)) :
    Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p) :=
  (vsQLam s g)ᵀ

/-- The conjugation action on matrices. -/
noncomputable def vsHAl (s : VsQSt I) (g : Perm (Fin I.n))
    (M : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) :
    Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p) :=
  vsHT s g⁻¹ * M * vsHT s g

theorem vsHT_mul (hs : VsQStOK s) {g h : Perm (Fin I.n)} (hg : g ∈ gens s.hs) (hh : h ∈ gens s.hs) :
    vsHT s (g * h) = vsHT s h * vsHT s g := by
  rw [vsHT, vsQLam_mul hs hg hh, Matrix.transpose_mul]; rfl

theorem vsHT_one (hs : VsQStOK s) : vsHT s 1 = 1 := by
  rw [vsHT, vsQLam_one hs, Matrix.transpose_one]

/-- **The conjugation is an action of `⟨hs⟩`.** -/
theorem vsH_conj_act (hs : VsQStOK s) : VsQPAct (gens s.hs) (vsHAl s) := by
  refine ⟨fun M => ?_, fun g hg h hh M => ?_⟩
  · rw [vsHAl, inv_one, vsHT_one hs, one_mul, mul_one]
  · simp only [vsHAl]
    rw [_root_.mul_inv_rev, vsHT_mul hs (inv_mem hh) (inv_mem hg), vsHT_mul hs hg hh]
    simp only [_root_.mul_assoc]

/-- **Fixed points.** `g` fixes `T(b)` iff `ρ g` commutes with `ρ b`. -/
theorem vsH_conj_fix (hs : VsQStOK s) {g b : Perm (Fin I.n)} (hg : g ∈ gens s.hs)
    (hb : b ∈ gens s.hs) :
    vsHAl s g (vsHT s b) = vsHT s b ↔ vsPRho hs g * vsPRho hs b = vsPRho hs b * vsPRho hs g := by
  have e : vsHAl s g (vsHT s b) = vsHT s (g * b * g⁻¹) := by
    rw [vsHAl, vsHT_mul hs (mul_mem hg hb) (inv_mem hg), vsHT_mul hs hg hb, _root_.mul_assoc]
  have hgbg : g * b * g⁻¹ ∈ gens s.hs := mul_mem (mul_mem hg hb) (inv_mem hg)
  rw [e]
  have h1 : vsHT s (g * b * g⁻¹) = vsHT s b ↔ vsQLam s (g * b * g⁻¹) = vsQLam s b := by
    simp only [vsHT]; exact Matrix.transpose_inj
  rw [h1, ← vsQRho_ext hs hgbg hb, ← vsPRho_of hs hgbg, ← vsPRho_of hs hb,
    vsPRho_conj hs hb hg]
  constructor
  · intro h
    calc vsPRho hs g * vsPRho hs b = vsPRho hs g * vsPRho hs b * (vsPRho hs g)⁻¹ * vsPRho hs g := by
          group
      _ = vsPRho hs b * vsPRho hs g := by rw [h]
  · intro h
    rw [h, mul_inv_cancel_right]

end GI.Impl
