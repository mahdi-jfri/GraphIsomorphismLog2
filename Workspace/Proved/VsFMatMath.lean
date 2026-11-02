import Workspace.Impl.VsFMatMul
import Workspace.Proved.VStabLinMath

/-!
# What the matrix product program computes, over `ZMod p`

Read as vectors over `ZMod p` (`vsF`, from `Proved/VStabLinMath.lean`), the row computed by the
product program is `z + ∑_k a_k B_k` (`vsFMat_rowMul`), when every row of `B` has the length of
`z`. With `z = 0` this is row `a` of the product.
-/

namespace GI.Proved

open GI.Impl

theorem vsFMat_rowMul_foldl (p : ℕ) (a : List ℕ) (L : List (List ℕ)) (k : ℕ) (v : List ℕ)
    (hL : ∀ r ∈ L, r.length ≤ v.length) :
    vsF p (L.foldl (vsFMulAcc p a) (k, v)).2 = vsF p v +
      ∑ j ∈ Finset.range L.length, ((a.getD (k + j) 0 : ℕ) : ZMod p) • vsF p (L.getD j []) := by
  induction L generalizing k v with
  | nil => simp
  | cons r L ih =>
    rw [List.foldl_cons]
    have hr : r.length ≤ v.length := hL r (List.mem_cons_self ..)
    have hL' : ∀ r' ∈ L, r'.length ≤ (vsLin p 1 (a.getD k 0) v r).length := fun r' h' => by
      rw [vsLin_length]; exact hL r' (List.mem_cons_of_mem _ h')
    have := ih (k + 1) (vsLin p 1 (a.getD k 0) v r) hL'
    simp only [vsFMulAcc] at this ⊢
    rw [this, vsF_vsLin p 1 (a.getD k 0) hr, List.length_cons, Finset.sum_range_succ']
    simp only [Nat.cast_one, one_smul, add_zero, List.getD_cons_zero, List.getD_cons_succ]
    rw [add_assoc, add_comm (((a.getD k 0 : ℕ) : ZMod p) • vsF p r)]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show k + 1 + j = k + (j + 1) by omega]

/-- **Row of a product.** If every row of `B` has the length of `z`, the program's row
`vsFRowMul p a B z` is `z + ∑_k a_k B_k` over `ZMod p`. -/
theorem vsFMat_rowMul (p : ℕ) (a : List ℕ) (Bm : List (List ℕ)) (z : List ℕ)
    (hB : ∀ r ∈ Bm, r.length ≤ z.length) :
    vsF p (vsFRowMul p a Bm z) = vsF p z +
      ∑ j ∈ Finset.range Bm.length, ((a.getD j 0 : ℕ) : ZMod p) • vsF p (Bm.getD j []) := by
  simpa using vsFMat_rowMul_foldl p a Bm 0 z hB

end GI.Proved
