module

public import Workspace.Impl.CamDefs

@[expose] public section

/-!
# Counting facts for the socle read through a Maróti identification

* `camX_camHom_injective`: the coordinatewise action `camHom e` is faithful for `1 ≤ k < m`.
* `camX_card_prod`: `camProd e S` has order `(m!/2)^|S|`.
* `camX_half_factorial_inj`: `m ↦ m!/2` is injective on `m ≥ 2`, so `|Alt(m)|` fixes `m`.
* `camX_choose_inj`: `k ↦ binom(m, k)` is injective on `2k ≤ m`.
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n m k r : ℕ} {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})}

/-- The coordinatewise action is faithful: a tuple acting trivially is trivial in each
coordinate, because every `k`-set occurs in every coordinate of some point. -/
theorem camX_camHom_injective (hk1 : 1 ≤ k) (hkm : k < m) : Function.Injective (camHom e) := by
  refine (injective_iff_map_eq_one _).mpr fun h hh => ?_
  funext i
  apply cam_kSetPerm_injective (k := k) hk1 hkm
  rw [Pi.one_apply, cam_kSetPerm_one]
  ext A : 1
  have := congrFun (camHom_apply e h (e.symm fun _ => A)) i
  rw [hh, Equiv.Perm.one_apply, Equiv.apply_symm_apply] at this
  exact this.symm

theorem camX_card_prod (hm : 2 ≤ m) (hk1 : 1 ≤ k) (hkm : k < m) (S : Finset (Fin r)) :
    Nat.card (camProd e S) = (m.factorial / 2) ^ S.card := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  unfold camProd
  rw [Subgroup.card_map_of_injective (camX_camHom_injective hk1 hkm)]
  rw [Nat.card_congr (show (Subgroup.pi Set.univ fun i =>
      if i ∈ S then alternatingGroup (Fin m) else ⊥) ≃ ∀ i : Fin r, {x : Perm (Fin m) //
      x ∈ (if i ∈ S then alternatingGroup (Fin m) else ⊥)} from
    { toFun := fun p i => ⟨p.1 i, p.2 i trivial⟩
      invFun := fun f => ⟨fun i => (f i).1, fun i _ => (f i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }), Nat.card_pi]
  have hc : ∀ i : Fin r, Nat.card {x : Perm (Fin m) //
      x ∈ (if i ∈ S then alternatingGroup (Fin m) else ⊥)} =
      if i ∈ S then m.factorial / 2 else 1 := by
    intro i
    split_ifs
    · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    · exact Subgroup.card_bot
  simp only [hc]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

private theorem camX_half_factorial_lt {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    a.factorial / 2 < b.factorial / 2 := by
  have h1 : a.factorial < b.factorial := (Nat.factorial_lt (by omega)).mpr hab
  have h2 : 2 ∣ a.factorial := Nat.dvd_factorial (by norm_num) ha
  have h3 : 2 ∣ b.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  obtain ⟨x, hx⟩ := h2
  obtain ⟨y, hy⟩ := h3
  rw [hx, hy, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]
  omega

theorem camX_half_factorial_inj {m m' : ℕ} (hm : 2 ≤ m) (hm' : 2 ≤ m')
    (h : m.factorial / 2 = m'.factorial / 2) : m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd h (camX_half_factorial_lt hm hlt).ne
  · exact heq
  · exact absurd h (camX_half_factorial_lt hm' hgt).ne'

/-- One step up below the middle: `binom(m, a) < binom(m, a + 1)` when `2(a + 1) ≤ m`. -/
private theorem camX_choose_step {m a : ℕ} (h : 2 * (a + 1) ≤ m) :
    m.choose a < m.choose (a + 1) := by
  have he := Nat.choose_succ_right_eq m a
  have hpos : 0 < m.choose a := Nat.choose_pos (by omega)
  have hlt : m.choose a * (a + 1) < m.choose a * (m - a) :=
    Nat.mul_lt_mul_of_pos_left (by omega) hpos
  rw [← he] at hlt
  exact Nat.lt_of_mul_lt_mul_right hlt

private theorem camX_choose_lt {m a b : ℕ} (hab : a < b) (hb : 2 * b ≤ m) :
    m.choose a < m.choose b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + 1 + d := ⟨b - (a + 1), by omega⟩
  induction d with
  | zero => exact camX_choose_step (by omega)
  | succ d ih =>
    exact (ih (by omega) (by omega)).trans (camX_choose_step (by omega))

theorem camX_choose_inj {m k k' : ℕ} (hk : 2 * k ≤ m) (hk' : 2 * k' ≤ m)
    (h : m.choose k = m.choose k') : k = k' := by
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd h (camX_choose_lt hlt hk').ne
  · exact heq
  · exact absurd h (camX_choose_lt hgt hk).ne'

end GI.Impl
