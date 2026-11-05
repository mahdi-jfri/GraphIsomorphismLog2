module

public import Workspace.Impl.RowPure

@[expose] public section

/-!
# Coordinates from clean 3-cycles

The proof of Theorem A.17 builds clean block 3-cycles and copies the numbering of one row
along them. This file does the bookkeeping on an abstract set `V` with row labels
`lab : V → Fin q`.

The input is

* a clean cycle `c` with top `(0 1 2)`;
* for every row `j ≥ 3`, a clean cycle `d j` with top `(0 j 1)` that undoes `c` on row `0`:
  `d j (c x) = x` when `lab x = 0`.

Both come from commutators of localized lifts (`cleanBlockCycle_of_localized`). The second
property holds for `d j = [c, h]` when the top of `h` meets `{0, 1, 2}` only in `0`
(`comm_undo`), as the paper says: "Its correspondence from `B_b` back to `B_a` is exactly the
inverse of the already pure map".

Number row `0` by a bijection `row0 : B ≃ {x // lab x = 0}`. Put row `1` and row `2` at
`c (row0 b)` and `c² (row0 b)`, and row `j ≥ 3` at `d j (row0 b)` (`coordsOf`). In these
coordinates `c` is the pure cycle `(0 1 2)` and `d j` is the pure cycle `(0 j 1)`
(`coordsOf_c`, `coordsOf_d`). These cycles generate `Alt(q)` (`alternating_le_of_gen`), so every
pure even permutation lies in any group that contains `c` and all `d j` (`coordsOf_mem`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Paper

variable {V : Type} {q : ℕ}

/-! ### Clean cycles as localized lifts -/

theorem cleanCycle_apply_eq_self {I : Type} [DecidableEq I] {a b c i : I} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : cleanCycle a b c i = i ↔ i ≠ a ∧ i ≠ b ∧ i ≠ c := by
  unfold cleanCycle
  simp only [Perm.mul_apply, swap_apply_def]
  by_cases h1 : i = a
  · subst h1; simp [hab]; split_ifs <;> simp_all [eq_comm]
  by_cases h2 : i = b
  · subst h2; simp [Ne.symm hab, hbc, Ne.symm hbc]
  by_cases h3 : i = c
  · subst h3; simp [Ne.symm hac, Ne.symm hbc]; exact fun h => hac h
  simp [h1, h2, h3]

/-- **A clean cycle is a localized lift of its top.** -/
theorem _root_.GI.CleanBlockCycle.localized {I : Type} [DecidableEq I] {lab : V → I} {a b c : I}
    {s : Perm V} (h : CleanBlockCycle lab a b c s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LocalizedBlockLift lab (cleanCycle a b c) s where
  action := h.action
  fixes x hx := by
    obtain ⟨h1, h2, h3⟩ := (cleanCycle_apply_eq_self hab hac hbc).1 hx
    exact h.fixes x h1 h2 h3

/-- **The commutator undoes the clean cycle on its first row.** Let `g` be a clean cycle with
top `(a b c)`, and `h` a localized lift of `p` whose support meets `{a, b, c}` only in `a`.
Then `[g, h] = h g h⁻¹ g⁻¹` sends `g x` back to `x` for every `x` in row `a`. -/
theorem comm_undo {I : Type} [DecidableEq I] {lab : V → I} {a b c : I} {g h : Perm V}
    {p : Perm I} (hg : CleanBlockCycle lab a b c g) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hh : LocalizedBlockLift lab p h)
    (hmeet : ∀ i, (cleanCycle a b c i ≠ i ∧ p i ≠ i) ↔ i = a) {x : V} (hx : lab x = a) :
    rightLocalCommutator g h (g x) = x := by
  unfold rightLocalCommutator
  simp only [Perm.mul_apply, Perm.inv_apply_self]
  -- the row of `h⁻¹ x` is `p⁻¹ a`, which `p` moves, so it is not `a`, `b` or `c`
  set i := p⁻¹ a with hi
  have hlab : lab (h⁻¹ x) = i := by
    rw [hi, ← hx]
    exact block_action_inverse lab p h hh.action x
  have hpa : p a ≠ a := ((hmeet a).2 rfl).2
  have hia : i ≠ a := fun he => hpa (by
    have : p i = a := by rw [hi]; simp
    rw [he] at this; exact this)
  have hpi : p i ≠ i := by
    have : p i = a := by rw [hi]; simp
    rw [this]; exact Ne.symm hia
  have hci : cleanCycle a b c i = i := by
    by_contra hne
    exact hia ((hmeet i).1 ⟨hne, hpi⟩)
  obtain ⟨h1, h2, h3⟩ := (cleanCycle_apply_eq_self hab hac hbc).1 hci
  have hfix : g (h⁻¹ x) = h⁻¹ x := hg.fixes _ (hlab ▸ h1) (hlab ▸ h2) (hlab ▸ h3)
  rw [hfix]
  simp

/-! ### The coordinates -/

/-- The data of the coordinates: the cycles `c` and `d j`. -/
structure CycleData (lab : V → Fin q) (hq : 3 ≤ q) where
  c : Perm V
  d : Fin q → Perm V
  hc : CleanBlockCycle lab ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ c
  hd : ∀ j : Fin q, 3 ≤ (j : ℕ) → CleanBlockCycle lab ⟨0, by omega⟩ j ⟨1, by omega⟩ (d j)
  undo : ∀ j : Fin q, 3 ≤ (j : ℕ) → ∀ x, lab x = ⟨0, by omega⟩ → d j (c x) = x

namespace CycleData

variable {lab : V → Fin q} {hq : 3 ≤ q} (D : CycleData lab hq)

/-- The permutation that carries row `0` to row `j`. -/
def rho (j : Fin q) : Perm V :=
  if (j : ℕ) = 0 then 1 else if (j : ℕ) = 1 then D.c else if (j : ℕ) = 2 then D.c * D.c else D.d j

end CycleData

/-- The top of `CycleData.rho j`. -/
def cycTop (hq : 3 ≤ q) (j : Fin q) : Perm (Fin q) :=
  if (j : ℕ) = 0 then 1 else if (j : ℕ) = 1 then cleanCycle ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
  else if (j : ℕ) = 2 then cleanCycle ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ *
    cleanCycle ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
  else cleanCycle ⟨0, by omega⟩ j ⟨1, by omega⟩

namespace CycleData

variable {lab : V → Fin q} {hq : 3 ≤ q} (D : CycleData lab hq)

theorem rho_action (j : Fin q) (v : V) : lab (D.rho j v) = cycTop hq j (lab v) := by
  unfold rho cycTop
  split_ifs with h0 h1 h2
  · rfl
  · exact D.hc.action v
  · simp only [Perm.mul_apply]; rw [D.hc.action, D.hc.action]
  · exact (D.hd j (by omega)).action v

omit D in
theorem top_zero (j : Fin q) : cycTop hq j ⟨0, by omega⟩ = j := by
  unfold cycTop
  split_ifs with h0 h1 h2
  · exact Fin.ext h0.symm
  · apply Fin.ext; simp [cleanCycle, swap_apply_def, h1]
  · apply Fin.ext; simp [cleanCycle, swap_apply_def, Perm.mul_apply, h2]
  · apply Fin.ext
    have hj1 : j ≠ ⟨1, by omega⟩ := fun h => h1 (by rw [h])
    have hj0 : j ≠ ⟨0, by omega⟩ := fun h => h0 (by rw [h])
    simp [cleanCycle, swap_apply_def, hj1, hj0]

theorem rho_row (j : Fin q) {x : V} (hx : lab x = ⟨0, by omega⟩) : lab (D.rho j x) = j := by
  rw [D.rho_action, hx, top_zero]

/-- The coordinates: `(b, j) ↦ rho j (row0 b)`. -/
def coordFun {B : Type} (row0 : B ≃ {x : V // lab x = ⟨0, by omega⟩}) (z : B × Fin q) : V :=
  D.rho z.2 (row0 z.1).val

theorem coordFun_bijective {B : Type} (row0 : B ≃ {x : V // lab x = ⟨0, by omega⟩}) :
    Function.Bijective (D.coordFun row0) := by
  constructor
  · rintro ⟨b, j⟩ ⟨b', j'⟩ h
    have hj : j = j' := by
      have := congrArg lab h
      simp only [coordFun] at this
      rwa [D.rho_row j (row0 b).2, D.rho_row j' (row0 b').2] at this
    subst hj
    have h2 : (row0 b).val = (row0 b').val := (D.rho j).injective (by simpa [coordFun] using h)
    have : b = b' := row0.injective (Subtype.ext h2)
    rw [this]
  · intro y
    set j := lab y
    have hx : lab ((D.rho j)⁻¹ y) = ⟨0, by omega⟩ := by
      apply (cycTop hq j).injective
      rw [← D.rho_action, Perm.apply_inv_self, top_zero]
    refine ⟨(row0.symm ⟨_, hx⟩, j), ?_⟩
    simp [coordFun]

/-- **The coordinates of the clean cycles.** -/
noncomputable def coordsOf {B : Type} (row0 : B ≃ {x : V // lab x = ⟨0, by omega⟩}) :
    B × Fin q ≃ V :=
  Equiv.ofBijective _ (D.coordFun_bijective row0)

variable {B : Type} (row0 : B ≃ {x : V // lab x = ⟨0, by omega⟩})

theorem coordsOf_apply (b : B) (j : Fin q) : D.coordsOf row0 (b, j) = D.rho j (row0 b).val := rfl

theorem label_coordsOf (b : B) (j : Fin q) : lab (D.coordsOf row0 (b, j)) = j :=
  D.rho_row j (row0 b).2

theorem coordsOf_zero (b : B) : D.coordsOf row0 (b, ⟨0, by omega⟩) = (row0 b).val := by
  simp [coordsOf_apply, rho]

/-- Two permutations agree if they agree on every coordinate. -/
theorem perm_ext_coords {σ τ : Perm V}
    (h : ∀ b j, σ (D.coordsOf row0 (b, j)) = τ (D.coordsOf row0 (b, j))) : σ = τ := by
  ext y
  obtain ⟨⟨b, j⟩, rfl⟩ := (D.coordsOf row0).surjective y
  rw [h]

/-- **`c` is the pure cycle `(0 1 2)`.** -/
theorem coordsOf_c :
    D.c = coordinatePureLift (D.coordsOf row0)
      (cleanCycle ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩) := by
  refine D.perm_ext_coords row0 fun b j => ?_
  rw [coordinatePureLift_apply]
  set x := (row0 b).val
  by_cases h0 : (j : ℕ) = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext h0
    rw [hj]
    have e1 : cleanCycle (⟨0, by omega⟩ : Fin q) ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨0, by omega⟩ =
        ⟨1, by omega⟩ := by simp [cleanCycle, swap_apply_def]
    rw [e1, coordsOf_apply, coordsOf_apply]
    simp [rho]
  by_cases h1 : (j : ℕ) = 1
  · have hj : j = ⟨1, by omega⟩ := Fin.ext h1
    rw [hj]
    have e1 : cleanCycle (⟨0, by omega⟩ : Fin q) ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨1, by omega⟩ =
        ⟨2, by omega⟩ := by simp [cleanCycle, swap_apply_def]
    rw [e1, coordsOf_apply, coordsOf_apply]
    simp [rho]
  by_cases h2 : (j : ℕ) = 2
  · have hj : j = ⟨2, by omega⟩ := Fin.ext h2
    rw [hj]
    have e1 : cleanCycle (⟨0, by omega⟩ : Fin q) ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨2, by omega⟩ =
        ⟨0, by omega⟩ := by simp [cleanCycle, swap_apply_def]
    rw [e1, coordsOf_apply, coordsOf_apply]
    simp only [rho, show ¬ (2 = 0) by omega, show ¬ (2 = 1) by omega, if_true, if_false,
      Perm.mul_apply, Perm.coe_one, id]
    exact D.hc.returns x
  · have hne : cleanCycle (⟨0, by omega⟩ : Fin q) ⟨1, by omega⟩ ⟨2, by omega⟩ j = j := by
      rw [cleanCycle_apply_eq_self (by simp) (by simp) (by simp)]
      exact ⟨fun h => h0 (by rw [h]), fun h => h1 (by rw [h]), fun h => h2 (by rw [h])⟩
    rw [hne]
    have hl := D.label_coordsOf row0 b j
    exact D.hc.fixes _ (by rw [hl]; exact fun h => h0 (by rw [h]))
      (by rw [hl]; exact fun h => h1 (by rw [h])) (by rw [hl]; exact fun h => h2 (by rw [h]))

/-- **`d j` is the pure cycle `(0 j 1)`**, for `j ≥ 3`. -/
theorem coordsOf_d (j : Fin q) (hj : 3 ≤ (j : ℕ)) :
    D.d j = coordinatePureLift (D.coordsOf row0) (cleanCycle ⟨0, by omega⟩ j ⟨1, by omega⟩) := by
  have hd := D.hd j hj
  have hj0 : j ≠ ⟨0, by omega⟩ := fun h => by rw [h] at hj; simp at hj
  have hj1 : j ≠ ⟨1, by omega⟩ := fun h => by rw [h] at hj; simp at hj
  have hrj : D.rho j = D.d j := by
    simp only [rho, show ¬ ((j : ℕ) = 0) by omega, show ¬ ((j : ℕ) = 1) by omega,
      show ¬ ((j : ℕ) = 2) by omega, if_false]
  refine D.perm_ext_coords row0 fun b i => ?_
  rw [coordinatePureLift_apply]
  set x := (row0 b).val
  have hx : lab x = ⟨0, by omega⟩ := (row0 b).2
  by_cases h0 : i = ⟨0, by omega⟩
  · subst h0
    have e1 : cleanCycle (⟨0, by omega⟩ : Fin q) j ⟨1, by omega⟩ ⟨0, by omega⟩ = j := by
      simp [cleanCycle, swap_apply_def, hj0, hj1]
    rw [e1, coordsOf_zero, coordsOf_apply, hrj]
  by_cases h1 : i = ⟨1, by omega⟩
  · subst h1
    have e1 : cleanCycle (⟨0, by omega⟩ : Fin q) j ⟨1, by omega⟩ ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
      simp [cleanCycle, swap_apply_def, hj1, Ne.symm hj1]
    rw [e1, coordsOf_zero, coordsOf_apply]
    simp only [rho, show ¬ ((1 : ℕ) = 0) by omega, if_false, if_true]
    exact D.undo j hj x hx
  by_cases hij : i = j
  · subst hij
    have e1 : cleanCycle (⟨0, by omega⟩ : Fin q) i ⟨1, by omega⟩ i = ⟨1, by omega⟩ := by
      simp [cleanCycle, swap_apply_def, hj0, hj1]
    rw [e1, coordsOf_apply, coordsOf_apply, hrj]
    simp only [rho, show ¬ ((1 : ℕ) = 0) by omega, if_false, if_true]
    -- `d (d x) = d⁻¹ x = c x`, since `d (c x) = x` and `d³ = 1`
    have h3 := hd.returns (D.c x)
    rw [D.undo i hj x hx] at h3
    exact h3
  · have hne : cleanCycle (⟨0, by omega⟩ : Fin q) j ⟨1, by omega⟩ i = i := by
      rw [cleanCycle_apply_eq_self (Ne.symm hj0) (by simp) hj1]
      exact ⟨h0, hij, h1⟩
    rw [hne]
    have hl := D.label_coordsOf row0 b i
    exact hd.fixes _ (by rw [hl]; exact h0) (by rw [hl]; exact hij) (by rw [hl]; exact h1)

/-- **Every pure even permutation lies in any group containing the cycles.** -/
theorem coordsOf_mem (G : Subgroup (Perm V)) (hc : D.c ∈ G)
    (hd : ∀ j : Fin q, 3 ≤ (j : ℕ) → D.d j ∈ G) (p : alternatingGroup (Fin q)) :
    coordinatePureLift (D.coordsOf row0) p.val ∈ G := by
  refine alternating_le_of_gen hq (G.comap (coordinatePureLift (D.coordsOf row0))) ?_ ?_ p.2
  · show _ ∈ G
    rw [← D.coordsOf_c row0]; exact hc
  · intro j hj
    show _ ∈ G
    rw [← D.coordsOf_d row0 j hj]; exact hd j hj

end CycleData

end GI.Impl
