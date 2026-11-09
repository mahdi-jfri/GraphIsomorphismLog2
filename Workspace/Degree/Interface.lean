module

public import Workspace.Degree.JohnsonWreath
public import Workspace.Cited.AlgoCameron
public import Workspace.Impl.Canon
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Workspace.Lang.Prims.PermGroups
public import Workspace.Lang.Encode
public import Workspace.Statement.Degree

/-!
# The interface between the group theory and the algorithm

The contracts between the parts of the proof, one named `Prop` for each. Each is proved in
another file.

* `PrimitiveAlternatives` is Lemma 8.2 of the paper, without its algorithmic claims: the small-order
  case and the Johnson-product case. It is proved as `GI.Degree.primitiveAlternatives` in
  `Workspace/Degree/PrimitiveBound.lean`, which imports this file.
* `StringSolver` is the string theorem of the paper (Theorem 1.3, for `Γ̂_D`), in the form in which
  the graph program calls it.
* `JohnsonRecognition` is the recognition of Johnson products, for all `h` with `3 h ≤ q`. A Johnson
  product has `3 h ≤ q` and `q ≥ 17` by `binom(q,h)^4 < 2^q`. It has a promise: the caller shows
  that the group is a Johnson product before it calls, by its order and `PrimitiveAlternatives`.

The Johnson-product case uses `WreathStructure` of `Workspace/Degree/JohnsonWreath.lean`. On
`Fin b` it is `GI.Cited.MarotiStructure` (`JohnsonProduct.marotiStructure`), so that the recognition
programs of `Workspace/Cited/AlgoCameron.lean` and `Impl/Cam*` apply.
-/

@[expose] public section

namespace GI.Degree

open Equiv GI.Cited GI.Algorithm GI.Lang GI.Impl GI.Assembly

variable {α : Type*} {q h r : ℕ}

/-- **The Johnson-product case of Lemma 8.2 of the paper**, for a primitive group `P`, with `e`
identifying the points with the `r`-tuples of `h`-subsets of `Fin q`. So the degree is
`binom(q,h)^r`.

* `wreath` gives the coordinate structure, and says that `S = johnsonSocle e` lies in `P`. Here
  `S ≅ Alt(q)^r`, by `coordHom_injective`.
* `S` is normal in `P`, and `[P : S] ≤ 2^r |K| ≤ 2^r D^(r-1)`, where
  `K = coordinateSet P e`, a subgroup by `coordinateSet_eq`.
* `binom(q,h)^4 < 2^q` is the condition `q > 4 log₂ binom(q,h)` of GNS Theorem 3.13. It is there
  so that Johnson recognition can use the size of `q`.
* `2 * h < q`: the case `2 h = q` of Lemma 8.2 of the paper does not occur for primitive groups. -/
structure JohnsonProduct (D : ℕ) (P : Subgroup (Perm α)) (e : α ≃ JohnsonTuple q h r) : Prop where
  five_le : 5 ≤ q
  le_D : q ≤ D
  one_le_h : 1 ≤ h
  two_mul_lt : 2 * h < q
  one_le_r : 1 ≤ r
  large : q.choose h ^ 4 < 2 ^ q
  wreath : WreathStructure P e
  socle_normal : ∀ g ∈ P, ∀ s ∈ johnsonSocle e, g * s * g⁻¹ ∈ johnsonSocle e
  index_le : ((johnsonSocle e).subgroupOf P).index ≤ 2 ^ r * (coordinateSet P e).ncard
  coordinate_le : (coordinateSet P e).ncard ≤ D ^ (r - 1)

/-- On `Fin b`, the structure of a Johnson product is `GI.Cited.MarotiStructure`. -/
theorem JohnsonProduct.marotiStructure {b : ℕ} {D : ℕ} {P : Subgroup (Perm (Fin b))}
    {e : Fin b ≃ JohnsonTuple q h r} (hP : JohnsonProduct D P e) : MarotiStructure P e :=
  ⟨hP.wreath.mem_wreath, fun a ha => hP.wreath.alt_le ⟨a, fun i _ => ha i, rfl⟩⟩

/-- **Lemma 8.2 of the paper** (and GNS Theorem 3.13), without its algorithmic claims. A primitive
group `P ∈ Γ̂_D` of degree `b` has order at most `b^(c₁ log D + c₂)`, or it is a Johnson product.

The constant `q₀` is the cutoff of the paper: every Johnson product with `q ≤ q₀` goes to the
small-order case, at the cost of a larger `c₂`. The constant `c₁` does not depend on `q₀`. -/
def PrimitiveAlternatives : Prop :=
  ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ q₀ : ℕ, ∃ c₂ : ℝ, 0 ≤ c₂ ∧
    ∀ (D b : ℕ), 6 ≤ D → 2 ≤ b → ∀ P : Subgroup (Perm (Fin b)),
      MulAction.IsPreprimitive P (Fin b) → GammaHat D P →
        Real.log (Nat.card P) ≤ (c₁ * Real.log D + c₂) * Real.log b ∨
        ∃ (q h r : ℕ) (e : Fin b ≃ JohnsonTuple q h r), q₀ < q ∧ JohnsonProduct D P e

/-- The state of a string query on `Fin k`: the group `G`, all positions active, the strings `x, y`,
no hierarchy, no rows, `h = 2` and `N = k`. -/
def stringState {k : ℕ} (G : Subgroup (Perm (Fin k))) (x y : Fin k → ℕ) : State (Fin k) ℕ where
  G := G
  dom := Set.univ
  dom_inv := fun _ _ _ => Iff.rfl
  x := x
  y := y
  hier := []
  rows := none
  floor := false
  h := 2
  h_le := le_rfl
  N := k
  counter := CounterInv.reset _ _ _ _
  carrier := CarrierOK.none _ _ _

/-- The value of `stringState (gens gs) x y`, with the layout of `StateVal`. -/
def stringVal (k : ℕ) (gs : List (Perm (Fin k))) (x y : Fin k → ℕ) : Val :=
  .list [.nat k, encGroup gs, encFun fun _ : Fin k => 1, encFun x, encFun y, .list [], .list [],
    boolVal false, .nat 2, .nat k]

/-- **The string theorem of the paper, as the graph program calls it.** On
`[D, stringVal k gs x y]`, function `fd` returns a canonical answer of `Iso_G(x, y)` for
`G = ⟨gs⟩ ∈ Γ̂_D`, at a cost of `exp(a log(k + 2) log(D + 2))` times a polynomial in the weight of
the value. The constants depend on nothing. It is proved from `GI.Degree.spine` and the root
wrapper. -/
def StringSolver (Pg : Program) (fd : ℕ) : Prop :=
  ∃ (a : ℝ) (K m : ℕ), 0 ≤ a ∧ ∀ (D k : ℕ) (gs : List (Perm (Fin k))) (x y : Fin k → ℕ),
    6 ≤ D → gs.length ≤ k ^ 2 → GammaHat D (gens gs) → (∀ i, x i < 2 * k ∧ y i < 2 * k) →
      FunAll Pg fd (.list [.nat D, stringVal k gs x y]) fun u cost =>
        AnsC (Equiv.refl _) u (stringState (gens gs) x y).answer ∧
          (cost : ℝ) ≤ Real.exp (a * Real.log ((k : ℝ) + 2) * Real.log ((D : ℝ) + 2)) * K *
            (((stringVal k gs x y).wt : ℝ) + 1) ^ m

/-- The contract moves to every extension of the program. -/
theorem StringSolver.of_sub {Pg Pg' : Program} {fd : ℕ} (hs : Pg.Sub Pg') (h : StringSolver Pg fd) :
    StringSolver Pg' fd := by
  obtain ⟨a, K, m, ha, h⟩ := h
  exact ⟨a, K, m, ha, fun D k gs x y h1 h2 h3 h4 => (h D k gs x y h1 h2 h3 h4).of_sub hs⟩

/-- `stringVal` is a canonical value of `stringState`, under the identity codes. This is what the
root wrapper needs. -/
theorem canon_stringVal {k : ℕ} (gs : List (Perm (Fin k))) (x y : Fin k → ℕ)
    (hgs : gs.length ≤ k ^ 2) (hc : ∀ i, x i < 2 * k ∧ y i < 2 * k) :
    Canon (Equiv.refl _) id (stringVal k gs x y) (stringState (gens gs) x y) := by
  classical
  refine ⟨⟨encGroup gs, _, _, _, .list [], .list [], ⟨gs, rfl, ?_, hgs⟩, ?_, rfl, rfl,
    ⟨[], rfl, .nil⟩, rfl, rfl⟩, hc, le_rfl, ?_⟩
  · have h : ∀ z : Perm (Fin k), Equiv.refl (Fin k) * z * (Equiv.refl (Fin k))⁻¹ = z := fun z => by
      ext; rfl
    ext g
    simp [groupFin, stringState, Subgroup.mem_map, h]
  · simp [DomVal, stringState]
  · simp [SmallInv, IntervalsOK, stringState, rhoNat]

/-- The numbers of a structure that recognition can identify. -/
structure RecogRange (m k : ℕ) : Prop where
  eight_le : 8 ≤ m
  one_le : 1 ≤ k
  three_mul : 3 * k ≤ m

/-- A primitive group of degree at least `25` with a Maróti structure in `RecogRange`. -/
structure RecogInst where
  n : ℕ
  le_n : 25 ≤ n
  gs : List (Perm (Fin n))
  primitive : MulAction.IsPreprimitive (gens gs) (Fin n)
  promise : ∃ (m k r : ℕ) (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
    RecogRange m k ∧ 1 ≤ r ∧ MarotiStructure (gens gs) e

/-- **Recognition of Johnson products.** On `encGroup gs`, the output is
`[1, m, k, r, E]`, where `E` lists an identification `e` with a Maróti structure, in `RecogRange`.
There is no enumeration and no bound `(k + 1)² < m + 2`. -/
def JohnsonRecognitionTask : GI.Cited.Task RecogInst :=
  Task.ofVal (fun I : RecogInst => encGroup I.gs) fun (I : RecogInst) v =>
    ∃ (m k r : ℕ) (e : Fin I.n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
      RecogRange m k ∧ 1 ≤ r ∧ MarotiStructure (gens I.gs) e ∧
        v = .list [.nat 1, .nat m, .nat k, .nat r, encKSetTuples e]

/-- See `JohnsonRecognitionTask`. -/
def JohnsonRecognition : Prop := ∃ p, PolyTimeAt JohnsonRecognitionTask p

/-- **The graph theorem of the paper (Theorem 1.1), as the final program calls it.** `fs b fd j` is
the list of functions of the graph program, with its entry at `b`, the string solver at `fd`, and
the primitive `Membership` at `j`. If a program holds the list at `b`, `Membership` at `j`, and `fd`
meets `StringSolver`, then function `b` on `inputVal G H` returns a correct output (`AnswerOK`) at a
cost of at most `exp(C log(n + 2) log(d + 2))` for every `d` that bounds the degrees of `G` and `H`.
The constant `C` may depend on the program but not on `n`, `d`, `G` or `H`.
`Workspace/Degree/GraphFinal.lean` proves this for `graphFuns`. -/
def GraphSolver (fs : ℕ → ℕ → ℕ → List Expr) : Prop :=
  ∀ (h : GI.Cited.Membership) (Pg : Program) (b fd j : ℕ), Pg.HasAt b (fs b fd j) →
    Pg.prims[j]? = some (membershipPrim h) → StringSolver Pg fd →
      ∃ C : ℝ, ∀ (n d : ℕ) (G H : SimpleGraph (Fin n)), GI.Statement.DegreeAtMost G d →
        GI.Statement.DegreeAtMost H d →
          FunAll Pg b (inputVal G H) fun w cost => AnswerOK G H w ∧
            (cost : ℝ) ≤ Real.exp (C * Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2))

end GI.Degree
