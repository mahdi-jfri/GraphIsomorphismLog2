-- VectorStabilizer is proved in `Workspace/Proved/VectorStabilizer.lean`; SmithNormalForm is not assumed
import Workspace.Cited.AlgoPermGroups
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bits

/-!
# Stage 2 tasks: integer normal forms and vector stabilizers

**`VectorStabilizer` is proved in `Workspace/Proved/VectorStabilizer.lean`.** `SmithNormalForm` is not assumed
by the main theorem.

* `SmithNormalFormTask`: [KannanBachem79] = R. Kannan, A. Bachem, *Polynomial algorithms for
  computing the Smith and Hermite normal forms of an integer matrix*, SIAM J. Comput. 8 (1979)
  499–507. The paper (proof of Theorem A.20): "Integer Hermite and Smith normal forms, including
  their transformation matrices, have polynomial bit complexity [KannanBachem79]." We could not
  access the source here; the statement below is the claim of its title and of the paper.
* `VectorStabilizerTask`: [LM, Theorem 1.4], verbatim: "Let `V` be an `n`-dimensional vector
  space over a finite field `k` of order `q^e` for some prime `q`. Theorem 1.4 Given a
  permutation group `G ≤ Sym(Ω)` such that `G ∈ Γ_d` and a representation `φ : G → GL(V)`, one
  can solve the following problems in time polynomial in `|Ω|, n, q` and `e`. (i) Given a vector
  `v ∈ V`, find the vector stabilizer `C_G(v)`." The paper (proof of Theorem A.20): "Luks–
  Miyazaki's vector-stabilizer algorithm applies to representations of the explicit solvable
  permutation cover [LM, Theorem 1.4 and Section 5.2]."
-/

namespace GI.Cited

open Equiv

/-! ### Integers in binary -/

/-- An integer, as its sign and its binary digits (least significant first). Every number in
the encoding is `0` or `1`, so integers of polynomial bit length are polynomial-size inputs. -/
def encInt (z : ℤ) : Val :=
  .list [.nat (if z < 0 then 1 else 0),
    .list ((Nat.bits z.natAbs).map fun b => .nat (if b then 1 else 0))]

/-- A matrix, as the list of its rows. -/
def encIntMatrix {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℤ) : Val :=
  .list ((List.finRange r).map fun i => .list ((List.finRange c).map fun j => encInt (A i j)))

/-- An integer matrix with at least one row and one column (so `r, c` are at most the number of
cells of the encoding). -/
structure IntMatrixInst where
  r : ℕ
  c : ℕ
  r_pos : 0 < r
  c_pos : 0 < c
  A : Matrix (Fin r) (Fin c) ℤ

/-- `D` is in Smith normal form: zero off the diagonal, and the diagonal entries are
nonnegative, each dividing the next. -/
def IsSmithForm {r c : ℕ} (D : Matrix (Fin r) (Fin c) ℤ) : Prop :=
  (∀ (i : Fin r) (j : Fin c), (i : ℕ) ≠ j → D i j = 0) ∧
  (∀ (i : Fin r) (j : Fin c), (i : ℕ) = j → 0 ≤ D i j) ∧
  ∀ (i : Fin r) (j : Fin c) (i' : Fin r) (j' : Fin c), (i : ℕ) = j → (i' : ℕ) = j' →
    (i : ℕ) + 1 = i' → D i j ∣ D i' j'

/-- The input of the Smith task: `[r, c, A]`. -/
def smithInput (I : IntMatrixInst) : Val := .list [.nat I.r, .nat I.c, encIntMatrix I.A]

/-- Every entry of the matrix `M` has absolute value below `2 ^ (s ^ 3)`, that is, at most
`s ^ 3` bits. -/
def EntriesBelow {r c : ℕ} (s : ℕ) (M : Matrix (Fin r) (Fin c) ℤ) : Prop :=
  ∀ i j, (M i j).natAbs < 2 ^ s ^ 3

/-- **Smith normal form with transformation matrices** ([KannanBachem79]). Output `[U, D, V]`
with `U, V` invertible over `ℤ`, `U A V = D`, and `D` in Smith normal form, where every entry of
`U, D, V` has at most `s³` bits, `s` the number of cells of the input.

*Output size.* `s` is at least the number of entries of `A` and at least its total bit length,
since each bit of `A` takes a cell. For `D` the bound is far from tight: each diagonal entry
divides a nonzero minor of `A`, and Hadamard's inequality bounds a minor by
`∏ (1 + |a_ij|) ≤ 2^s`. For `U, V`, [KannanBachem79] proves that the multipliers it computes
have polynomial bit length (we could not read it, so we do not know its exponent). For square
nonsingular `A`, Storjohann's multipliers have entries of `O(n (log n + log ‖A‖))` bits
(A. Storjohann, *Algorithms for matrix canonical forms*, PhD thesis, ETH Zürich, 2000, Chapter 8;
restated in Birmpilis, Labahn, Storjohann, arXiv:2111.09949, Introduction), which is `O(s²)`.
The exponent 3 leaves room for the standard reduction of the rectangular and singular case to
the nonsingular one. This bound is the least certain point of the task.

*Source check (source not read).* The statement is the standard one: Smith form with unimodular
multipliers of polynomial bit length, computable in polynomial time. The paper's matrices are
rectangular relation matrices, possibly of deficient rank; if [KannanBachem79] treats only
square nonsingular matrices in its main theorem, the general case is the standard reduction
(or Iliopoulos, SIAM J. Comput. 18 (1989), Storjohann's algorithms). `D` is unique once
`0 ≤ D i i` is asked, and every algorithm gives it; `U, V` are not pinned down. The input
bound holds: `r, c ≥ 1`, so `r, c` are at most the number of cells, and all other numbers are
bits or signs. -/
def SmithNormalFormTask : Task IntMatrixInst :=
  Task.ofVal smithInput
    (fun I v => ∃ (U : Matrix (Fin I.r) (Fin I.r) ℤ) (V : Matrix (Fin I.c) (Fin I.c) ℤ)
      (D : Matrix (Fin I.r) (Fin I.c) ℤ),
      v = .list [encIntMatrix U, encIntMatrix D, encIntMatrix V] ∧
      IsUnit U.det ∧ IsUnit V.det ∧ U * I.A * V = D ∧ IsSmithForm D ∧
      EntriesBelow (smithInput I).cells.length U ∧ EntriesBelow (smithInput I).cells.length D ∧
      EntriesBelow (smithInput I).cells.length V)

/-- Not assumed by the main theorem. -/
def SmithNormalForm : Prop := ∃ p, PolyTimeAt SmithNormalFormTask p

/-! ### Vector stabilizers of solvable permutation groups -/

/-- A vector over `𝔽_p`, as the list of its coordinates in `0, …, p - 1`. -/
def encVec {p d : ℕ} (v : Fin d → ZMod p) : Val :=
  .list ((List.finRange d).map fun i => .nat (v i).val)

/-- A matrix over `𝔽_p`, as the list of its rows. -/
def encModMatrix {p d : ℕ} (M : Matrix (Fin d) (Fin d) (ZMod p)) : Val :=
  .list ((List.finRange d).map fun i => encVec (M i))

/-- An instance: a solvable `G = ⟨gs⟩ ≤ Sym(n)`, a prime `p ≤ n`, a representation
`φ : G → GL_d(𝔽_p)` (encoded by the images of the generators, which determine it), and a vector
`v`. In the paper `p` is at most the cover degree ("The invariant factors of the represented
finite abelian groups have no prime divisors above `b`"), so `p ≤ n` holds and keeps the input
numbers polynomial. -/
structure VecStabInst where
  n : ℕ
  gs : List (Perm (Fin n))
  solvable : IsSolvable (gens gs)
  p : ℕ
  prime : p.Prime
  p_le : p ≤ n
  d : ℕ
  φ : gens gs →* Matrix.GeneralLinearGroup (Fin d) (ZMod p)
  v : Fin d → ZMod p

/-- The stabilizer `C_G(v) = {g ∈ G | φ(g) v = v}`, as a subgroup of `G`. -/
def vecStab (I : VecStabInst) : Subgroup (gens I.gs) where
  carrier := {g | (I.φ g).val.mulVec I.v = I.v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, Units.val_mul] at ha hb ⊢
    rw [← Matrix.mulVec_mulVec, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.one_mulVec]

/-- **Vector stabilizer** ([LM, Theorem 1.4(i)], for `q = p` prime, `e = 1`, `G` solvable, so
`G ∈ Γ_d` for every `d`). Output a generating list of `{g ∈ G | φ(g) v = v}`, with at most `n²`
generators (`GensOf`). -/
def VectorStabilizerTask : Task VecStabInst :=
  Task.ofVal
    (fun I => .list [encGroup I.gs, .nat I.p,
      .list (I.gs.attach.map fun g =>
        encModMatrix (I.φ ⟨g.1, Subgroup.subset_closure g.2⟩).val), encVec I.v])
    (fun I v => GensOf ((vecStab I).map (gens I.gs).subtype) v)

/-- Proved as `GI.Proved.vectorStabilizer` in `Workspace/Proved/VectorStabilizer.lean`. -/
def VectorStabilizer : Prop := ∃ p, PolyTimeAt VectorStabilizerTask p

end GI.Cited
