module

public import Workspace.Impl.TermJAutJ
public import Workspace.Impl.TermJCoset

@[expose] public section

/-!
# Generators of `Aut_J(x)`: the local products of the kernel of the sum map

`tmJLamD lg c`: for a list `lg` of pairs `(a_k, g_k)` and integers `c_k`, the coordinates
`a ↦ ∏_{a_k = a} g_k^{c_k}` (list order), and `tmJLam lg c` the pair with these coordinates and
top `1`. Its label is `∏_k φ(g_k)^{c_k}` (`tmJLabOf_lam`), the sum map of the paper.
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Multicoset

variable {B : Type} {q : ℕ} {N : Subgroup (Perm B)} {A : Type*} [CommGroup A] {φ : N →* A}

/-- The coordinates of a local product. -/
def tmJLamD (lg : List (Fin q × Perm B)) (c : Fin lg.length → ℤ) : Fin q → Perm B :=
  fun a => ((List.finRange lg.length).map fun k =>
    if (lg.get k).1 = a then (lg.get k).2 ^ c k else 1).prod

/-- A local product. -/
def tmJLam (lg : List (Fin q × Perm B)) (c : Fin lg.length → ℤ) : Perm (B × Fin q) :=
  tmJP (tmJLamD lg c, 1)

/-- The sum map: `∏_k φ(g_k)^{e_k}` (at the coordinate `a` only, if `a` is given). -/
noncomputable def tmJSum (N : Subgroup (Perm B)) (φ : N →* A) (lg : List (Fin q × Perm B))
    (e : Fin lg.length → ℤ) (a : Fin q) : A :=
  ∏ k, if (lg.get k).1 = a then phiT N φ (lg.get k).2 ^ e k else 1

/-- The total sum map. -/
noncomputable def tmJSumT (N : Subgroup (Perm B)) (φ : N →* A) (lg : List (Fin q × Perm B))
    (e : Fin lg.length → ℤ) : A :=
  ∏ k, phiT N φ (lg.get k).2 ^ e k

theorem phiT_zpow {g : Perm B} (hg : g ∈ N) (n : ℤ) : phiT N φ (g ^ n) = phiT N φ g ^ n := by
  have hgn : g ^ n ∈ N := N.zpow_mem hg n
  simp only [phiT, dif_pos hg, dif_pos hgn]
  rw [← map_zpow]
  rfl

theorem phiT_list_prod (l : List (Perm B)) (hl : ∀ g ∈ l, g ∈ N) :
    phiT N φ l.prod = (l.map (phiT N φ)).prod := by
  induction l with
  | nil => simp [phiT_one]
  | cons g l ih =>
    simp only [List.prod_cons, List.map_cons]
    rw [phiT_mul (hl g List.mem_cons_self)
      (Subgroup.list_prod_mem _ fun h hh => hl h (List.mem_cons_of_mem _ hh)),
      ih fun h hh => hl h (List.mem_cons_of_mem _ hh)]

theorem tmJSum_prod (lg : List (Fin q × Perm B)) (e : Fin lg.length → ℤ) :
    ∏ a, tmJSum N φ lg e a = tmJSumT N φ lg e := by
  unfold tmJSum tmJSumT
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_ite_eq]
  simp

theorem tmJSum_add (lg : List (Fin q × Perm B)) (e e' : Fin lg.length → ℤ) (a : Fin q) :
    tmJSum N φ lg (e + e') a = tmJSum N φ lg e a * tmJSum N φ lg e' a := by
  unfold tmJSum
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs <;> simp [zpow_add]

theorem tmJSum_neg (lg : List (Fin q × Perm B)) (e : Fin lg.length → ℤ) (a : Fin q) :
    tmJSum N φ lg (-e) a = (tmJSum N φ lg e a)⁻¹ := by
  unfold tmJSum
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs <;> simp [zpow_neg]

theorem tmJSum_zero (lg : List (Fin q × Perm B)) (a : Fin q) : tmJSum N φ lg 0 a = 1 := by
  unfold tmJSum; simp

theorem tmJSum_single (lg : List (Fin q × Perm B)) (k : Fin lg.length) (a : Fin q) :
    tmJSum N φ lg (Pi.single k 1) a = if (lg.get k).1 = a then phiT N φ (lg.get k).2 else 1 := by
  classical
  unfold tmJSum
  rw [Finset.prod_eq_single k]
  · split_ifs <;> simp
  · intro k' _ hk; split_ifs <;> simp [Pi.single_eq_of_ne hk]
  · simp

/-- The coordinates of a local product lie in the row stabilizers. -/
theorem tmJLamD_mem {C : Type} {x : Fin q → B → C} {lg : List (Fin q × Perm B)}
    (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ tmJRowAut N (x (lg.get k).1))
    (c : Fin lg.length → ℤ) (a : Fin q) : tmJLamD lg c a ∈ tmJRowAut N (x a) := by
  unfold tmJLamD
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
  split_ifs with h
  · rw [← h]; exact Subgroup.zpow_mem _ (hlg k) _
  · exact Subgroup.one_mem _

/-- The label of a coordinate of a local product. -/
theorem phiT_lamD {lg : List (Fin q × Perm B)} (hlg : ∀ k : Fin lg.length, (lg.get k).2 ∈ N)
    (c : Fin lg.length → ℤ) (a : Fin q) : phiT N φ (tmJLamD lg c a) = tmJSum N φ lg c a := by
  unfold tmJLamD tmJSum
  rw [phiT_list_prod]
  · rw [Fin.prod_univ_def, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply]
    split_ifs
    · exact phiT_zpow (hlg k) _
    · exact phiT_one
  · intro g hg
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
    split_ifs
    · exact N.zpow_mem (hlg k) _
    · exact N.one_mem

end GI.Impl
