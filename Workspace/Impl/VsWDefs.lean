module

public import Workspace.Impl.VStabLinUnit
public import Workspace.Impl.VsFMatMul

@[expose] public section

/-!
# The list functions of the linear algebra layer

These are the functions that the linear-algebra programs compute. Vectors are lists of
numbers below `p`. A subspace is given by a list of vectors that spans it. A matrix `M` is
stored as the rows of `Mᵀ`, so the image of `u` is `vsFRowMul p u A 0`.

* `vsWBas`: an echelon basis (the main parts of the rows of the insertion).
* `vsWKer`: the relations among a list of vectors.
* `vsWSolve`: coefficients of a vector in a list, if it lies in the span.
* `vsWInter`: an intersection (Zassenhaus: insert `(u, u)` and `(w, 0)`; the relations are the
  common vectors).
* `vsWImg`, `vsWCut`: images under a stored matrix, and the part of a subspace in the kernel of
  a stored matrix.
* `vsWKey`: the canonical key (the unit vectors sifted through an echelon basis).
* `vsWSubC`: a stored matrix minus a scalar matrix.
* Frames: `vsWComp` (a complement), `vsWFrRows` (the coordinate rows), `vsWCo`, `vsWLoc`,
  `vsWLift`.
-/

namespace GI.Impl

/-- The zero vector of length `m`. -/
def vsWZ (m : ℕ) : List ℕ := List.replicate m 0

/-- The pairs `(u, [])`. -/
def vsWPairs (us : List (List ℕ)) : List (List ℕ × List ℕ) := us.map fun u => (u, [])

/-- The echelon rows of a list of vectors. -/
def vsWRows (p : ℕ) (us : List (List ℕ)) : List VsRow := (vsInsertAll p (vsWPairs us)).1

/-- An echelon basis of the span of a list of vectors. -/
def vsWBas (p : ℕ) (us : List (List ℕ)) : List (List ℕ) := (vsWRows p us).map VsRow.x

/-- The relations among a list of vectors: they span the kernel of `a ↦ ∑ a_i u_i`. -/
def vsWKer (p : ℕ) (us : List (List ℕ)) : List (List ℕ) :=
  (vsInsertAll p (vsUnitPairs us.length us)).2

/-- The negative of a vector modulo `p`. -/
def vsWNeg (p : ℕ) (t : List ℕ) : List ℕ := vsLin p (p - 1) 0 t t

/-- The sift of `(u, 0)` through the unit-tag rows of `us`. -/
def vsWSolveSift (p : ℕ) (us : List (List ℕ)) (u : List ℕ) : List ℕ × List ℕ :=
  vsSift p (vsInsertAll p (vsUnitPairs us.length us)).1 (u, vsWZ us.length)

/-- Coefficients of `u` in the list `us`, or `none` if `u` is not in the span. -/
def vsWSolve (p : ℕ) (us : List (List ℕ)) (u : List ℕ) : Option (List ℕ) :=
  if vsNzIdx (vsWSolveSift p us u).1 < (vsWSolveSift p us u).1.length then none
  else some (vsWNeg p (vsWSolveSift p us u).2)

/-- The pairs of the intersection: `(u, u)` and `(w, 0)`. -/
def vsWZas (d : ℕ) (us ws : List (List ℕ)) : List (List ℕ × List ℕ) :=
  us.map (fun u => (u, u)) ++ ws.map fun w => (w, vsWZ d)

/-- A spanning list of the intersection of two spans. -/
def vsWInter (p d : ℕ) (us ws : List (List ℕ)) : List (List ℕ) :=
  (vsInsertAll p (vsWZas d us ws)).2

/-- The images of a list of vectors under a stored matrix. -/
def vsWImg (p d : ℕ) (A : List (List ℕ)) (us : List (List ℕ)) : List (List ℕ) :=
  us.map fun u => vsFRowMul p u A (vsWZ d)

/-- A spanning list of the part of `span us` in the kernel of a stored matrix. -/
def vsWCut (p d : ℕ) (us A : List (List ℕ)) : List (List ℕ) :=
  (vsWKer p (vsWImg p d A us)).map fun a => vsFRowMul p a us (vsWZ d)

/-- The canonical key of a span: the unit vectors sifted through an echelon basis. -/
def vsWKey (p d : ℕ) (us : List (List ℕ)) : List (List ℕ) :=
  (List.range d).map fun i => (vsSift p (vsWRows p us) (vsUnit d i, [])).1

/-- The identity matrix as a list. -/
def vsWId (d : ℕ) : List (List ℕ) := (List.range d).map (vsUnit d)

/-- A stored matrix minus `c` times the identity (`c < p`). -/
def vsWSubC (p c : ℕ) (A : List (List ℕ)) : List (List ℕ) :=
  (List.range A.length).map fun j => vsLin p 1 (p - c) (A.getD j []) (vsUnit A.length j)

/-! ### Frames -/

/-- A complement of `span ws'` in `span (ws' ++ ws)`: the main parts of the echelon rows that
the vectors of `ws` add after those of `ws'`. -/
def vsWComp (p : ℕ) (ws' ws : List (List ℕ)) : List (List ℕ) :=
  ((vsWRows p (ws' ++ ws)).drop (vsWRows p ws').length).map VsRow.x

/-- The coordinate pairs of a frame: `(w', 0)` and `(c_j, e_j)`. -/
def vsWFrPairs (ws' cs : List (List ℕ)) : List (List ℕ × List ℕ) :=
  ws'.map (fun w => (w, vsWZ cs.length)) ++ vsUnitPairs cs.length cs

/-- The coordinate rows of a frame. -/
def vsWFrRows (p : ℕ) (ws' cs : List (List ℕ)) : List VsRow := (vsInsertAll p (vsWFrPairs ws' cs)).1

/-- The local coordinates of `x` (modulo `span ws'`, in the complement `cs`). -/
def vsWCo (p : ℕ) (ws' cs : List (List ℕ)) (x : List ℕ) : List ℕ :=
  vsWNeg p (vsSift p (vsWFrRows p ws' cs) (x, vsWZ cs.length)).2

/-- The local matrix of a stored matrix, stored: row `j` holds the coordinates of `M c_j`. -/
def vsWLoc (p d : ℕ) (ws' cs A : List (List ℕ)) : List (List ℕ) :=
  (vsWImg p d A cs).map (vsWCo p ws' cs)

/-- The lift of a local span: `ws'` together with the combinations `∑ a_j c_j`. -/
def vsWLift (p d : ℕ) (ws' cs us : List (List ℕ)) : List (List ℕ) :=
  ws' ++ us.map fun a => vsFRowMul p a cs (vsWZ d)

end GI.Impl

namespace GI.Impl

open GI.Cited GI.Lang

/-- The value of a list of vectors. -/
def vsWVs (us : List (List ℕ)) : Val := .list (us.map natList)

end GI.Impl
