-- Proved in `Workspace/Proved/` (see each task's docstring)
import Workspace.Cited.AlgoLinear

/-!
# Stage 2 tasks for the row terminal (Theorem A.20, "Constructing the abelian coordinates")

**All three tasks are proved in `Workspace/Proved/`. Each docstring names the theorem.** These
tasks replace, for the row terminal, the unused `SmithNormalFormTask` of `AlgoLinear.lean` (whose
source covers less than that task states), and add the constructive membership that the
paper uses without a citation.

## What the paper feeds to the normal forms

The proof of Theorem A.20 (paragraph "Constructing the abelian coordinates") works with relation
matrices whose *rows* are relations among integer coordinates. All of them present finite
abelian groups, so all of them have full column rank:

1. `A/N`: the `t × t` matrix of the relations `e_i [a_i] = Σ_{j<i} c_ij [a_j]`. It is square,
   lower triangular, with diagonal `e_i ≥ 2`, so nonsingular with determinant `|A/N|`.
2. `A/B_i`: the rows of (1) and the coordinate rows of the generators of `B_i`:
   `(t + k_i) × t`, rank `t`.
3. `W = ⊕_i A/B_i`: the block diagonal of the matrices (2): `Σ_i (t + k_i) × r t`, rank `r t`.
4. `W/D`: the rows of (3) and the `t` rows `δ(a_j)`: `(Σ_i (t + k_i) + t) × r t`, rank `r t`.

"Coordinates, relation tests, solutions to homomorphism equations, and lifts" are solutions of
integer linear systems `z M = w` with such an `M` (rows of (3) and the `δ`-rows for
`δ(a) = w`); a Hermite form with a unimodular premultiplier solves them by back substitution.
The invariant factors and the primary components of `W/D` come from the Smith form of the matrix
(4). If `U M = [H; 0]` with `H` square (Hermite form), then the Smith form of `M` is that of `H`
with zero rows appended, and its multipliers are `diag(U_S, 1) U` and `V_S` for
`U_S H V_S = D`. So the paper needs:

* the **Hermite form with a premultiplier** of an `r × c` integer matrix of rank `c`
  (`HermiteFullRankTask`);
* the **Smith form with multipliers** of a *square nonsingular* integer matrix
  (`SmithNonsingularTask`).

## Sources

* `HermiteFullRankTask`: A. Storjohann, G. Labahn, *Asymptotically fast computation of
  Hermite normal forms of integer matrices*, Proc. ISSAC '96, ACM, 1996, pp. 259–266,
  **Theorem 12** (p. 265). Checked in the published PDF at
  https://cs.uwaterloo.ca/~astorjoh/p259-storjohann.pdf. It gives a deterministic bit-polynomial
  algorithm for a full-column-rank matrix, including the unimodular premultiplier. The form on
  p. 259 uses upper triangular rows, zero rows below, positive pivots, and nonnegative entries
  above each pivot strictly below that pivot. These are exactly `IsHermiteForm`.
* `SmithNonsingularTask`: R. Kannan, A. Bachem, *Polynomial algorithms for computing the Smith
  and Hermite normal forms of an integer matrix*, SIAM J. Comput. 8 (1979), 499–507,
  **Section 3, Theorems 3–5** (pp. 504–505): Theorem 3 specifies the positive Smith diagonal,
  Theorem 4 proves algorithm SNF polynomial, and Theorem 5 bounds both unimodular multipliers.
  Read in a transcript of the published SIAM paper. The publisher PDF was not available, so
  the transcript has not been checked against it. The explicit SNF algorithm takes square
  nonsingular input. Section 2, p. 504, also gives a full-rank
  rectangular Hermite reduction, and the paragraph after Theorem 5 states that SNF extends to
  arbitrary rectangular matrices, leaving the details to the reader. This task needs neither
  extension and does not rely on Sergeraert's description of their scope.
* `ConstructiveMembershipTask`: E. M. Luks, T. Miyazaki, *Polynomial-time normalizers*, DMTCS
  13:4 (2011), 61–96, **Theorem 3.1(v)** (p. 67). The straight-line-program definition is in
  **Section 2.3** (p. 66), not Section 3.1. Checked in the published PDF at
  https://dmtcs.episciences.org/en/articles/531/download. Instructions take a generator, invert
  an earlier entry, or multiply two earlier entries. The printed range ends at the penultimate
  entry, a typo: the final entry must also be computed, as the subsequent evaluation under
  homomorphisms requires. `slpEntries` checks every instruction. The empty program supplies
  the identity when the generator list is empty. Function composition versus the source's
  right-action convention is harmless: interpret permutations by inversion, an isomorphism
  from the opposite group, retaining instruction order.

The normal-form tasks exclude zero columns. If `A/N` is trivial, or the direct sum has no
summands, the caller handles the zero-dimensional group directly. Redundant compressed
generators may be removed to ensure `e_i ≥ 2`; nonsingularity only requires `e_i ≥ 1`.
For a homomorphism into a finite presented group, stack the image rows with the target relation
rows. The latter already have full column rank. Solving a row equation then gives a preimage;
the rows of the premultiplier below the square Hermite block give the integer kernel. Project
these rows to the source coordinates for the kernel generators. Thus full-rank Hermite calls
also cover equations whose homomorphism itself has deficient rank.

## Output sizes

Every correct output must have polynomial size. The sources
give polynomial running time, so their outputs have polynomially many bits, but they state no
exponent for the multipliers or the program length. Each task therefore takes the exponent `d`
as a parameter: an output entry has at most `s ^ d` bits (a program at most `s ^ d`
instructions), `s` the number of cells of the input, and the task reads
`∃ d p, PolyTimeAt (Task d) p`. This asks no more than the sources: an algorithm with running
time at most `c s^k` on the bit model writes at most that many bits, which is at most `s ^ d` for
a sufficiently large natural `d`, since `s ≥ 2` (round `c` up to a positive integer,
then take `d = k + c`). This is one uniform exponent for all instances of the task, not a
separate exponent for each input. Smaller choices of `d` need not give total tasks. Totality
for the chosen `d` follows from the source algorithm. Each output matrix has at most `s²`
entries, and a valid instruction index is below the generator count or the program length.
Thus every accepted output has polynomially many cells for fixed `d`.
-/

namespace GI.Cited

open Equiv

/-! ### Hermite normal form of a matrix of full column rank -/

/-- An `r × c` integer matrix of rank `c`, `1 ≤ c ≤ r`. Full column rank is stated as
injectivity of `z ↦ A z` on integer column vectors (the columns are linearly independent). -/
structure FullRankInst where
  r : ℕ
  c : ℕ
  c_pos : 0 < c
  c_le : c ≤ r
  A : Matrix (Fin r) (Fin c) ℤ
  rank : Function.Injective A.mulVec

/-- `H` is in Hermite normal form ([SL96, p. 259]) for a matrix of `c` columns: the rows from
`c` on are zero, the first `c` rows are upper triangular with positive diagonal, and each entry
above the diagonal is reduced modulo the diagonal entry of its column. -/
def IsHermiteForm {r c : ℕ} (H : Matrix (Fin r) (Fin c) ℤ) : Prop :=
  (∀ (i : Fin r) (j : Fin c), (j : ℕ) < i → H i j = 0) ∧
  (∀ (i : Fin r) (j : Fin c), (i : ℕ) = j → 0 < H i j) ∧
  ∀ (i : Fin r) (j : Fin c) (i' : Fin r), (i : ℕ) < j → (i' : ℕ) = j → 0 ≤ H i j ∧ H i j < H i' j

/-- The input of the Hermite task: `[r, c, A]`. -/
def fullRankInput (I : FullRankInst) : Val := .list [.nat I.r, .nat I.c, encIntMatrix I.A]

/-- Every entry of `M` has at most `B` bits. -/
def EntriesBits {r c : ℕ} (B : ℕ) (M : Matrix (Fin r) (Fin c) ℤ) : Prop :=
  ∀ i j, (M i j).natAbs < 2 ^ B

/-- **Hermite normal form with a unimodular premultiplier** ([SL96, Theorem 12]), output
exponent `d`. Output `[U, H]` with `U` invertible over `ℤ`, `U A = H`, `H` in Hermite normal
form, every entry of `U` and `H` of at most `s ^ d` bits (`s` the number of input cells).

*Output size.* `H` is unique and its entries are at most `|det|` of a nonzero `c × c` minor of
`A`, so `2^s` by Hadamard's inequality (`s` is at least the bit length of `A`); `U` is written by
the algorithm, within its running time. *Strength.* The task asks only what [SL96, Theorem 12]
states: some unimodular `U` with `U A = H`; `U` is not unique when `r > c`. -/
def HermiteFullRankTask (d : ℕ) : Task FullRankInst :=
  Task.ofVal fullRankInput
    (fun I v => ∃ (U : Matrix (Fin I.r) (Fin I.r) ℤ) (H : Matrix (Fin I.r) (Fin I.c) ℤ),
      v = .list [encIntMatrix U, encIntMatrix H] ∧ IsUnit U.det ∧ U * I.A = H ∧
      IsHermiteForm H ∧ EntriesBits ((fullRankInput I).cells.length ^ d) U ∧
      EntriesBits ((fullRankInput I).cells.length ^ d) H)

/-- Proved as `GI.Proved.hermiteFullRank` in `Workspace/Proved/HNFFinal.lean`. -/
def HermiteFullRank : Prop := ∃ d p, PolyTimeAt (HermiteFullRankTask d) p

/-! ### Smith normal form of a square nonsingular matrix -/

/-- A square integer matrix with nonzero determinant, `n ≥ 1`. -/
structure NonsingularInst where
  n : ℕ
  n_pos : 0 < n
  A : Matrix (Fin n) (Fin n) ℤ
  det_ne : A.det ≠ 0

/-- The input of the Smith task: `[n, A]`. -/
def nonsingularInput (I : NonsingularInst) : Val := .list [.nat I.n, encIntMatrix I.A]

/-- **Smith normal form with multipliers of a square nonsingular matrix** ([KannanBachem79, Section 3,
Theorems 3–5]; see the module docstring for the access limitation), output exponent `d`. Output `[U, D, V]` with `U, V`
invertible over `ℤ`, `U A V = D`, `D` in Smith normal form (`IsSmithForm`), every entry of at
most `s ^ d` bits. `D` is unique; its entries divide minors of `A`, so they have at most `s`
bits. -/
def SmithNonsingularTask (d : ℕ) : Task NonsingularInst :=
  Task.ofVal nonsingularInput
    (fun I v => ∃ (U V D : Matrix (Fin I.n) (Fin I.n) ℤ),
      v = .list [encIntMatrix U, encIntMatrix D, encIntMatrix V] ∧
      IsUnit U.det ∧ IsUnit V.det ∧ U * I.A * V = D ∧ IsSmithForm D ∧
      EntriesBits ((nonsingularInput I).cells.length ^ d) U ∧
      EntriesBits ((nonsingularInput I).cells.length ^ d) D ∧
      EntriesBits ((nonsingularInput I).cells.length ^ d) V)

/-- Proved as `GI.Proved.smithNonsingular` in `Workspace/Proved/SNFFinal.lean`. -/
def SmithNonsingular : Prop := ∃ d p, PolyTimeAt (SmithNonsingularTask d) p

/-! ### Constructive membership with straight-line programs -/

/-- An instruction of a straight-line program ([LM, Section 2.3, p. 66]): a generator, the inverse of
an earlier entry, or the product of two earlier entries. -/
inductive SlpInstr where
  | gen (i : ℕ)
  | inv (j : ℕ)
  | mul (j k : ℕ)

/-- The encoding of an instruction: `[0, i]`, `[1, j]` or `[2, j, k]`. -/
def encSlpInstr : SlpInstr → Val
  | .gen i => .list [.nat 0, .nat i]
  | .inv j => .list [.nat 1, .nat j]
  | .mul j k => .list [.nat 2, .nat j, .nat k]

/-- The entries of a straight-line program over `gs`, in order, or `none` if an instruction
names a generator or an entry that does not exist (an entry may only use earlier ones). -/
def slpEntries {n : ℕ} (gs : List (Perm (Fin n))) :
    List SlpInstr → List (Perm (Fin n)) → Option (List (Perm (Fin n)))
  | [], acc => some acc
  | ins :: prog, acc =>
    let next : Option (Perm (Fin n)) := match ins with
      | .gen i => gs[i]?
      | .inv j => acc[j]?.map (·⁻¹)
      | .mul j k => do let a ← acc[j]?; let b ← acc[k]?; pure (a * b)
    match next with
    | none => none
    | some g => slpEntries gs prog (acc ++ [g])

/-- `prog` is a straight-line program to reach `x` from `gs`: all its instructions are valid and
its last entry is `x`. The empty program reaches the identity (this only allows more outputs
than [LM]'s definition, for the trivial group). -/
def SlpReaches {n : ℕ} (gs : List (Perm (Fin n))) (prog : List SlpInstr) (x : Perm (Fin n)) :
    Prop :=
  ∃ es, slpEntries gs prog [] = some es ∧ (es.getLast?.getD 1) = x

/-- The value `[gs, x]` of a membership instance, as for `MembershipTask`. On a known member it is
`knownMemberInput` below. -/
def memberInput (I : MemberInst) : Val := .list [encGroup I.gs, encPerm I.x]

/-- An instance of constructive membership: generators `gs` and a permutation `x` that is known to
lie in the group they generate. The field `mem` is a promise. It is not part of the input. -/
structure KnownMemberInst where
  n : ℕ
  gs : List (Perm (Fin n))
  x : Perm (Fin n)
  mem : x ∈ gens gs

/-- The input of constructive membership: `[gs, x]`, as for `MembershipTask`. -/
def knownMemberInput (I : KnownMemberInst) : Val := .list [encGroup I.gs, encPerm I.x]

/-- **Constructive membership** ([LM, Theorem 3.1(v)]), output exponent `d`, on known members.
The input is `gs` and `x` with `x ∈ ⟨gs⟩`. The output is `[1, prog]` with a straight-line program
`prog` of at most `s ^ d` instructions that reaches `x` from `gs` (`s` the number of input cells).
There is no "not a member" answer: deciding membership is `MembershipTask`. This is the second half
of [LM, Theorem 3.1(v)] ("test whether x ∈ G and, if so, exhibit a straight-line program to reach
x from S"), restricted to members. The tag `1` is kept from the form with both answers.

*Output size.* The indices in the instructions are below the program length or the number of
generators, so the output has polynomially many cells. Every `x ∈ ⟨gs⟩` has such a program of
polynomial length (the algorithm of [LM] writes one within its running time). -/
def ConstructiveMembershipTask (d : ℕ) : Task KnownMemberInst :=
  Task.ofVal knownMemberInput
    (fun I v => ∃ prog : List SlpInstr, v = .list [.nat 1, .list (prog.map encSlpInstr)] ∧
      prog.length ≤ (knownMemberInput I).cells.length ^ d ∧ SlpReaches I.gs prog I.x)

/-- Proved as `GI.Proved.constructiveMembership` in `Workspace/Proved/SSConstructiveMembership.lean`. -/
def ConstructiveMembership : Prop := ∃ d p, PolyTimeAt (ConstructiveMembershipTask d) p

end GI.Cited
