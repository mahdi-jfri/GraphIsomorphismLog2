import Workspace.Impl.TermJLabHom
import Workspace.Impl.TermJAlg

/-!
# The zero-sum correction at a row terminal

Proof of Theorem A.23: "Finally lift the surviving quotient representative and correct it by the
constructed `J`-transporter … the same sum equations construct its `J`-correction."

* `tmJJ_iff_lab`: a pair with coordinates in `N` lies in `J` exactly when its label is `1` and
  its top is even (`InJ`, `tmJJ_mem_iff`).
* `tmJ_u_mem`: for a lift `g` and a local transporter `z` of the same class, `u = z⁻¹ g` lies in
  `N ≀ Sym(q)`.
* `tmJ_corr_lab`: if `a ∈ Aut_{N≀Sym}(X)` has the label and the top sign of `u`, then `z a` lies
  in the piece and has class `h`. This is the correction.
* `tmJ_corr_exists`: such an `a` exists (from `tmJ_corr`, since some element of the piece has
  class `h`). The program finds one by solving the sum equation.
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Paper Equiv Equiv.Perm

variable {Ω C : Type}

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

open RowTerminal

/-- **Membership in `J` by the label and the parity** (`InJ`). -/
theorem tmJJ_iff_lab [Nonempty I.B] {p : (Fin L.q → Perm I.B) × Perm (Fin L.q)}
    (hp : ∀ i, p.1 i ∈ I.Nb) :
    tmJP p ∈ tmJJ I ↔ tmJLab I.Nb I.φ p.1 = 1 ∧ p.2 ∈ alternatingGroup (Fin L.q) := by
  rw [tmJJ_mem_iff I]
  constructor
  · rintro ⟨p', ⟨-, h1, h2⟩, he⟩
    rw [← tmJP_injective he]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨p, ⟨hp, h1, h2⟩, rfl⟩

/-- `z⁻¹ g` has all coordinates in `N` when `z` and `g` have the same class. -/
theorem tmJ_u_mem {h : Perm I.B} (hh : h ∈ I.Hb) {z g : Perm (I.B × Fin L.q)}
    (hzc : z ∈ tmJCls I.Nb h) (hgc : g ∈ tmJCls I.Nb h) : z⁻¹ * g ∈ tmJW I.Nb := by
  have := tmJCls_mul I.normalizes (I.Hb.inv_mem hh) (tmJCls_inv I.normalizes hh hzc) hgc
  rw [mul_inv_cancel] at this
  exact tmJCls_one_iff.1 this

variable [Nonempty I.B]

/-- An element of `N ≀ Sym(q)` lies in `J` when its label is `1` and its top is even. -/
theorem tmJJ_of_hom {j : Perm (I.B × Fin L.q)} (hj : j ∈ tmJW I.Nb)
    (hl : tmJLabHom I.φ ⟨j, hj⟩ = 1) (hs : sign (tmJTopHom ⟨j, hj⟩) = 1) : j ∈ tmJJ I := by
  obtain ⟨hp, he⟩ := tmJPairOf_spec (⟨j, hj⟩ : tmJW (q := L.q) I.Nb)
  have : tmJP (tmJPairOf (⟨j, hj⟩ : tmJW (q := L.q) I.Nb)) ∈ tmJJ I :=
    (tmJJ_iff_lab I hp).2 ⟨hl, hs⟩
  rwa [he] at this

/-- An element of `J` has label `1` and even top. -/
theorem tmJJ_hom {j : Perm (I.B × Fin L.q)} (hj : j ∈ tmJW I.Nb) (hJ : j ∈ tmJJ I) :
    tmJLabHom I.φ ⟨j, hj⟩ = 1 ∧ sign (tmJTopHom ⟨j, hj⟩) = 1 := by
  obtain ⟨hp, he⟩ := tmJPairOf_spec (⟨j, hj⟩ : tmJW (q := L.q) I.Nb)
  have hJ' : tmJP (tmJPairOf (⟨j, hj⟩ : tmJW (q := L.q) I.Nb)) ∈ tmJJ I := by rw [he]; exact hJ
  exact (tmJJ_iff_lab I hp).1 hJ'

/-- **The correction.** If `a ∈ Aut_{N≀Sym}(X)` has the label and the top sign of `u = z⁻¹ g`,
then `z a` lies in the piece and has class `h`. -/
theorem tmJ_corr_lab {r h : Perm I.B} (hr : r ∈ I.Hb) (hL : h ∈ tmGlLab I r)
    {g w z : Perm (I.B × Fin L.q)} (hg : g ∈ tmJG I) (hw : w ∈ tmJW I.Nb)
    (hf : tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q))) = g * w)
    (hzY : tmJStr (rowTuple I.e S.y) ∘ z = tmJStr (rowTuple I.e S.x))
    (hzc : z ∈ tmJCls I.Nb h) (hu : z⁻¹ * g ∈ tmJW I.Nb)
    {a : Perm (I.B × Fin L.q)} (ha : a ∈ tmJW I.Nb ⊓ tmJStab (tmJStr (rowTuple I.e S.x)))
    (hlab : tmJLabHom I.φ ⟨a, ha.1⟩ = tmJLabHom I.φ ⟨z⁻¹ * g, hu⟩)
    (hsg : sign (tmJTopHom ⟨a, ha.1⟩) = sign (tmJTopHom ⟨z⁻¹ * g, hu⟩)) :
    z * a ∈ tmJP '' tmCosetT I r ∧ z * a ∈ tmJCls I.Nb h := by
  have hj : a⁻¹ * (z⁻¹ * g) ∈ tmJW I.Nb := (tmJW I.Nb).mul_mem ((tmJW I.Nb).inv_mem ha.1) hu
  have e : (⟨a⁻¹ * (z⁻¹ * g), hj⟩ : tmJW (q := L.q) I.Nb) =
      (⟨a, ha.1⟩ : tmJW (q := L.q) I.Nb)⁻¹ * ⟨z⁻¹ * g, hu⟩ := rfl
  have hJ : a⁻¹ * (z⁻¹ * g) ∈ tmJJ I := by
    apply tmJJ_of_hom I hj
    · rw [e, map_mul, map_inv, hlab, inv_mul_cancel]
    · rw [e, map_mul, map_inv, Perm.sign_mul, Perm.sign_inv, hsg]
      exact Int.units_mul_self _
  exact (tmJ_corr I hr hL hg hw hf hzY hzc).2 a ha _ hJ (by group)

/-- **A correcting element exists.** -/
theorem tmJ_corr_exists {r h : Perm I.B} (hr : r ∈ I.Hb) (hL : h ∈ tmGlLab I r)
    {g w z : Perm (I.B × Fin L.q)} (hg : g ∈ tmJG I) (hw : w ∈ tmJW I.Nb)
    (hf : tmJP ((fun _ => h : Fin L.q → Perm I.B), (1 : Perm (Fin L.q))) = g * w)
    (hzY : tmJStr (rowTuple I.e S.y) ∘ z = tmJStr (rowTuple I.e S.x))
    (hzc : z ∈ tmJCls I.Nb h) (hu : z⁻¹ * g ∈ tmJW I.Nb) :
    ∃ a, ∃ ha : a ∈ tmJW I.Nb ⊓ tmJStab (tmJStr (rowTuple I.e S.x)),
      tmJLabHom I.φ ⟨a, ha.1⟩ = tmJLabHom I.φ ⟨z⁻¹ * g, hu⟩ ∧
      sign (tmJTopHom ⟨a, ha.1⟩) = sign (tmJTopHom ⟨z⁻¹ * g, hu⟩) := by
  obtain ⟨a, ha, j, hj, he⟩ := (tmJ_corr I hr hL hg hw hf hzY hzc).1
  have hjW : j ∈ tmJW I.Nb := hj.2
  have e : (⟨z⁻¹ * g, hu⟩ : tmJW (q := L.q) I.Nb) = ⟨a, ha.1⟩ * ⟨j, hjW⟩ := Subtype.ext he
  obtain ⟨h1, h2⟩ := tmJJ_hom I hjW hj
  refine ⟨a, ha, ?_, ?_⟩
  · rw [e, map_mul, h1, mul_one]
  · rw [e, map_mul, Perm.sign_mul, h2, mul_one]

end RT

end GI.Impl
