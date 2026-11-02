import Workspace.Impl.VsWDefs
import Workspace.Impl.VsFMatPow

/-!
# The list functions of the algebra pieces

Matrices are stored `D × D` lists (the rows of `Mᵀ`, as in `Impl/VsWDefs.lean`). A list `Bm`
of stored matrices spans a space of matrices; when this space is a commutative algebra `B`, the
map `x ↦ x ^ p` is linear on it, and its kernel and its fixed points are found by solving
linear equations.

* `vsWMC p D Bm a`: the stored matrix `∑ a_i Bm_i`.
* `vsWPowFlat`, `vsWFixFlat`: the flattened `M ^ p` and `M ^ p - M`.
* `vsFNilL p D Bm`, `vsFFixL p D Bm`: spanning lists of `{x ∈ B | x ^ p = 0}` and
  `{x ∈ B | x ^ p = x}`.
* `vsFAnnL p D Ys`: a spanning list of the common kernel of the `Ys`.
* `vsFEigL p D Ss`: bases of the nonzero joint eigenspaces of the `Ss`.
-/

namespace GI.Impl

/-- The stored matrix `∑ a_i Bm_i`: row `r` is the combination of the rows `r` of the `Bm_i`. -/
def vsWMC (p D : ℕ) (Bm : List (List (List ℕ))) (a : List ℕ) : List (List ℕ) :=
  (List.range D).map fun r => vsFRowMul p a (Bm.map fun M => M.getD r []) (vsWZ D)

/-- The flattened `p`-th power of a stored matrix. -/
def vsWPowFlat (p D : ℕ) (M : List (List ℕ)) : List ℕ := (vsFMatPowL p M (vsWZ D) (p - 1)).flatten

/-- The flattened `M ^ p - M`. -/
def vsWFixFlat (p D : ℕ) (M : List (List ℕ)) : List ℕ := vsLin p 1 (p - 1) (vsWPowFlat p D M) M.flatten

/-- A spanning list of the elements `x` of the span of `Bm` with `x ^ p = 0`. -/
def vsFNilL (p D : ℕ) (Bm : List (List (List ℕ))) : List (List (List ℕ)) :=
  (vsWKer p (Bm.map (vsWPowFlat p D))).map (vsWMC p D Bm)

/-- A spanning list of the elements `x` of the span of `Bm` with `x ^ p = x`. -/
def vsFFixL (p D : ℕ) (Bm : List (List (List ℕ))) : List (List (List ℕ)) :=
  (vsWKer p (Bm.map (vsWFixFlat p D))).map (vsWMC p D Bm)

/-- A spanning list of the common kernel of the stored matrices `Ys`. -/
def vsFAnnL (p D : ℕ) (Ys : List (List (List ℕ))) : List (List ℕ) := Ys.foldl (vsWCut p D) (vsWId D)

/-- Split a piece `P` by the eigenvalues of `s`: the nonempty bases of `span P ∩ ker (s - c)`. -/
def vsFEigSplit (p D : ℕ) (s : List (List ℕ)) (P : List (List ℕ)) : List (List (List ℕ)) :=
  ((List.range p).map fun c => vsWBas p (vsWCut p D P (vsWSubC p c s))).filter fun Q => !Q.isEmpty

/-- The pieces at the start: the whole space, unless it is zero. -/
def vsFEig0 (D : ℕ) : List (List (List ℕ)) := [vsWId D].filter fun Q => !Q.isEmpty

/-- Bases of the nonzero joint eigenspaces of the stored matrices `Ss`. -/
def vsFEigL (p D : ℕ) (Ss : List (List (List ℕ))) : List (List (List ℕ)) :=
  Ss.foldl (fun pcs s => pcs.flatMap (vsFEigSplit p D s)) (vsFEig0 D)

end GI.Impl
