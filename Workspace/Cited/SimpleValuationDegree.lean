import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace GI.Cited

/-- **Valuation of `Aut(T)` against the minimal degree, for nonalternating simple `T`.**
There is an absolute constant `A` such that, for every finite nonabelian simple group
`T` not isomorphic to any alternating group, and every faithful action of `T` on
`n` points, some prime `ℓ ∈ {3, 5}` satisfies `v_ℓ(|Aut T|) ≤ A log n`.

*Source.* Paper, proof of Lemma A.8 (`lem:budget-primitive-valuation`), second
paragraph. It combines two cited facts:
(1) the order formulas of the groups of Lie type (e.g. [GMPS] = Guest, Morris,
Praeger, Spiga, *On the maximum orders of elements of finite almost simple groups and
primitive permutation groups*, Trans. AMS 367 (2015), Table 4 lists the groups with
their orders and minimal degrees) and of `|Out T|`, which give
`v_ℓ(|Aut T|) = O(r log q)` for `ℓ ∈ {3,5}`, `ℓ ≠ p`, where `T` has rank `r` over
`𝔽_q`, `q = p^f`;
(2) the minimal degrees in [GMPS, Table 4], which give `log μ(T) ≥ c₀ r log q`.
Every faithful action of `T` on `n` points has `n ≥ μ(T)`. Sporadic groups
and finitely many exceptional parameters are absorbed into `A`, using `n ≥ 5`.
The classification of finite simple groups (CFSG) says that every `T` covered here is
of Lie type or sporadic.

*Why it is true.* For `PSL_d(q)`: `v_ℓ(|PGL_d(q)|) ≤ d log_ℓ q + d/(ℓ-1)` by the order
formula and lifting the exponent, `|Out| ≤ 2 d f`, and `μ ≥ (q^d-1)/(q-1) ≥ q^{d-1}`
apart from the bounded exceptions `PSL_2(7), PSL_2(11)` (and those isomorphic to
alternating groups, which are excluded). The other classical families embed (up to a
central cover) in `GL_D(q^e)` with `D ≤ 2r+2`, `e ≤ 2`, and have
`μ ≥ q^{r}/2`-type bounds; exceptional families have bounded rank and
`μ ≥ q^{r}`. In every family `ℓ` can be chosen different from the
characteristic (`ℓ = 5` when `p = 3`, `ℓ = 3` otherwise). Suzuki groups have
`v_3(|T|) = 0` and are covered too. Since `n ≥ μ(T) ≥ 5`, `log n > 0`, so the finitely
many sporadic groups only enlarge `A`. Alternating groups must be excluded: `A_m` on
`m` points has `v_3(|A_m|) ≈ m/2`, not `O(log m)`.

*Why it is the weakest form needed.* The paper applies these two facts only to an
almost simple primitive group `G` of degree `n` with nonalternating socle `T`: it
uses `T ≤ G ≤ Aut(T)` and that `T` acts faithfully on the `n` points. The statement
uses only `|Aut T|` and the existence of a faithful action, and asks for one prime
in `{3,5}` with one absolute constant, which is exactly the claim
`6 v_ℓ(|G|) ≤ A₀ log n` of Lemma A.8 for this case. It is stated for groups in `Type`. -/
def SimpleValuationDegree : Prop :=
  ∃ A : ℝ, ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T →
    (∃ x y : T, x * y ≠ y * x) →
    (∀ m : ℕ, IsEmpty (T ≃* alternatingGroup (Fin m))) →
    ∀ n : ℕ, ∀ f : T →* Equiv.Perm (Fin n), Function.Injective f →
      ∃ ℓ : ℕ, (ℓ = 3 ∨ ℓ = 5) ∧
        (padicValNat ℓ (Nat.card (MulAut T)) : ℝ) ≤ A * Real.log n

end GI.Cited
