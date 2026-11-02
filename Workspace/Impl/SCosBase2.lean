import Workspace.Impl.SCosBase1

/-!
# The base case, the first four steps

The body of `scosBaseF` (function 4) on `v = [gv, xv, ind]` starts with four deterministic
steps: the point `α` (`findEq`), `n = N / 2`, the point `n + α`, and `τ`. Each step is a `Det`
lemma whose cost is a multiple of a power of a bound `M` with `v.wt ≤ M` and `N + 1 ≤ M`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

section Steps

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-- The indicator of `{α}` at position `i`. -/
theorem scosBase_indF (a : Fin n) (i : Fin (n + n)) :
    indF (Equiv.refl (Fin (n + n))) (scosPhiF ({a} : Finset (Fin n))) i =
      if (i : ℕ) = a then 1 else 0 := by
  unfold indF scosPhiF
  congr 1
  apply propext
  simp only [Equiv.refl_symm, Equiv.refl_apply, Finset.coe_singleton, Set.image_singleton,
    Set.mem_singleton_iff]
  constructor
  · rintro rfl; rfl
  · intro h; exact Fin.ext h

/-- The list of the indicator of `{α}`. -/
noncomputable def scosBaseXs (a : Fin n) : List ℕ :=
  (List.finRange (n + n)).map (indF (Equiv.refl (Fin (n + n))) (scosPhiF ({a} : Finset (Fin n))))

theorem scosBase_ind_eq (a : Fin n) : scosInd ({a} : Finset (Fin n)) = natList (scosBaseXs a) :=
  encFun_eq_natList _

theorem scosBase_findIdx (a : Fin n) :
    (scosBaseXs a).findIdx (fun y => decide (y = 1)) = a := by
  have hl : (a : ℕ) < (scosBaseXs a).length := by simp [scosBaseXs]; omega
  rw [List.findIdx_eq hl]
  simp only [scosBaseXs, List.getElem_map, List.getElem_finRange, scosBase_indF]
  refine ⟨by simp, fun j hj => ?_⟩
  simp [Fin.cast, show j ≠ (a : ℕ) from Nat.ne_of_lt hj]

theorem scosBase_xs_le (a : Fin n) : ∀ y ∈ scosBaseXs a, y ≤ n + n := by
  intro y hy
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
  rw [scosBase_indF]
  split_ifs <;> omega

/-- The input value. -/
noncomputable abbrev scosBaseV (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n) : Val :=
  .list [encGroup gs, encPerm (nintSum x), scosInd ({a} : Finset (Fin n))]

/-- **Step 1**: `α`, by `findEq`. -/
theorem scosBase_d1 (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n) {M : ℕ}
    (hM : (scosBaseV gs x a).wt ≤ M) (hN : n + n + 1 ≤ M) :
    Det (𝒫) [scosBaseV gs x a] (.call 29 (mk2 (.nat 1) (arg 2))) (.nat a)
      (200000 * M ^ 3) := by
  have hj : 1 ≤ n + n := by have := a.isLt; omega
  have hl : (scosBaseXs a).length ≤ n + n := by simp [scosBaseXs]
  have hf := findEq_spec (scos_findEq (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (scosBase_xs_le a) hj hl
  rw [scosBase_findIdx] at hf
  have d2 : Det (𝒫) [scosBaseV gs x a] (arg 2) (natList (scosBaseXs a)) _ :=
    Det.arg' (vs := [encGroup gs, encPerm (nintSum x), scosInd ({a} : Finset (Fin n))])
      (rest := []) (j := 2) (by rw [scosBase_ind_eq]; rfl)
  have d := Det.call (Det.mk2 (Det.nat (P := 𝒫) (env := [scosBaseV gs x a]) 1) d2) hf
  refine d.mono ?_
  have w1 := wt_list2_le (.nat 1) (natList (scosBaseXs a))
  have w2 : (natList (scosBaseXs a)).wt < (scosBaseV gs x a).wt := by
    rw [← scosBase_ind_eq]; exact wt_le_wt_list (by simp)
  have w3 : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
  have w4 := wt_nat_le (a : ℕ)
  have w5 : (Val.list [encGroup gs, encPerm (nintSum x),
    scosInd ({a} : Finset (Fin n))]).wt ≤ M := hM
  have p1 : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) M
  have p2 : (n + n + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left hN 3
  have ha := a.isLt
  have hK : findEqK = 100000 := rfl
  rw [hK]
  omega

/-- The list of entries of `X = nintSum x`. -/
theorem scosBase_xv (x : ScosPair n) : encPerm (nintSum x) =
    .list ((List.finRange (n + n)).map fun i => Val.nat (nintSum x i)) := rfl

/-- **Step 2**: `n = N / 2`. -/
theorem scosBase_d2 (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n) {M : ℕ}
    (hM : (scosBaseV gs x a).wt ≤ M) (hN : n + n + 1 ≤ M) :
    Det (𝒫) [scosBaseV gs x a, .nat a] (.arith .div (.length (arg 1)) (.nat 2)) (.nat n)
      (30 * M) := by
  have d1 : Det (𝒫) [scosBaseV gs x a, .nat a] (arg 1)
      (.list ((List.finRange (n + n)).map fun i => Val.nat (nintSum x i))) _ :=
    Det.arg' (vs := [encGroup gs, encPerm (nintSum x), scosInd ({a} : Finset (Fin n))])
      (rest := [.nat a]) (j := 1) rfl
  have d := Det.arith' (z := n) (op := .div) (Det.length d1) (Det.nat 2) (by
    simp only [List.length_map, List.length_finRange, BinOp.eval]; omega)
  refine d.mono ?_
  have w5 : (Val.list [encGroup gs, encPerm (nintSum x),
    scosInd ({a} : Finset (Fin n))]).wt ≤ M := hM
  simp only [List.length_map, List.length_finRange]
  omega

/-- **Step 3**: the point `n + α`. -/
theorem scosBase_d3 (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n) {M : ℕ}
    (hN : n + n + 1 ≤ M) :
    Det (𝒫) [scosBaseV gs x a, .nat a, .nat n] (.arith .add (.var 2) (.var 1))
      (.nat (n + a)) (10 * M) := by
  have d := Det.arith' (z := n + a) (op := .add)
    (Det.var' (P := 𝒫) (env := [scosBaseV gs x a, .nat a, .nat n]) (i := 2) rfl)
    (Det.var' (i := 1) rfl) rfl
  refine d.mono ?_
  have w1 := wt_nat_le n
  have w2 := wt_nat_le (a : ℕ)
  have := a.isLt
  omega

/-- The point `τ = n + x₂⁻¹ (x₁ α)`. -/
def scosBaseTau (x : ScosPair n) (a : Fin n) : Fin (n + n) := Fin.natAdd n (x.2⁻¹ (x.1 a))

/-- **Step 4**: `τ`, as entry `n + xv[α]` of `inv xv`. -/
theorem scosBase_d4 (gs : List (Perm (Fin (n + n)))) (x : ScosPair n) (a : Fin n) {M : ℕ}
    (hM : (scosBaseV gs x a).wt ≤ M) (hN : n + n + 1 ≤ M) :
    Det (𝒫) [scosBaseV gs x a, .nat a, .nat n, .nat (n + a)]
      (.get (.call 75 (arg 1)) (.arith .add (.var 2) (.get (arg 1) (.var 1))))
      (.nat (scosBaseTau x a)) (300000 * M ^ 4) := by
  have d1 : Det (𝒫) [scosBaseV gs x a, .nat a, .nat n, .nat (n + a)] (arg 1)
      (encPerm (nintSum x)) _ :=
    Det.arg' (vs := [encGroup gs, encPerm (nintSum x), scosInd ({a} : Finset (Fin n))])
      (rest := [.nat a, .nat n, .nat (n + a)]) (j := 1) rfl
  have d1' : Det (𝒫) [scosBaseV gs x a, .nat a, .nat n, .nat (n + a)] (arg 1)
      (.list ((List.finRange (n + n)).map fun i => Val.nat (nintSum x i))) _ := d1
  have dinv := Det.call d1 (inv_spec (scos_inv (c := c) (hps := hps) (hpre := hpre) (hmb := hmb))
    (nintSum x))
  have dinv' : Det (𝒫) [scosBaseV gs x a, .nat a, .nat n, .nat (n + a)] (.call 75 (arg 1))
      (.list ((List.finRange (n + n)).map fun i => Val.nat ((nintSum x)⁻¹ i))) _ := dinv
  have dxa := Det.get' d1' (Det.var' (i := 1) rfl)
    (scosBase_get_perm (nintSum x) (Fin.castAdd n a))
  rw [scosBase_castAdd] at dxa
  have dadd := Det.arith' (z := n + x.1 a) (op := .add) (Det.var' (i := 2) rfl) dxa rfl
  have dget := Det.get' dinv' dadd (scosBase_get_perm (nintSum x)⁻¹ (Fin.natAdd n (x.1 a)))
  rw [scosBase_tau] at dget
  refine dget.mono ?_
  have w5 : (Val.list [encGroup gs, encPerm (nintSum x),
    scosInd ({a} : Finset (Fin n))]).wt ≤ M := hM
  have w1 := wt_encPerm_le (nintSum x)⁻¹
  have w2 := wt_nat_le n
  have w3 := wt_nat_le (x.1 a : ℕ)
  have w3' := wt_nat_le ((Fin.castAdd n (x.1 a) : Fin (n + n)) : ℕ)
  have w4 := wt_nat_le ((Fin.natAdd n (x.2⁻¹ (x.1 a)) : Fin (n + n)) : ℕ)
  have w6 := wt_nat_le (a : ℕ)
  have := (x.1 a).isLt
  have := (x.2⁻¹ (x.1 a)).isLt
  have := a.isLt
  have p1 : M ≤ M ^ 4 := Nat.le_self_pow (by norm_num) M
  have p2 : (n + n + 1) ^ 4 ≤ M ^ 4 := Nat.pow_le_pow_left hN 4
  have p3 : (n + n + 1) ^ 2 ≤ M ^ 4 :=
    (Nat.pow_le_pow_right (by omega) (by norm_num)).trans p2
  have hK : invK = 100000 := rfl
  rw [hK]
  simp only [Fin.val_natAdd, Fin.val_castAdd] at *
  omega

end Steps

end GI.Impl
