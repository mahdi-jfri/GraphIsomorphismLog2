# The cited results

The paper cites some results that it does not prove. Most of them are proved in this repository
(see `Workspace/Proved/`). Ten are not, and the proof uses them as axioms. All ten rely on the
classification of finite simple groups (CFSG).

Each axiom is declared in [`Workspace/Axioms/`](Workspace/Axioms). Its type is a definition in
[`Workspace/Cited/`](Workspace/Cited). The docstring of that definition quotes the source, says
why the result is true, and explains why the statement asks no more than the paper needs.

Running `#print axioms main_theorem` (see the README) lists exactly these ten axioms, together
with `propext`, `Classical.choice` and `Quot.sound`.

## Structural results

| Axiom | Statement | Source | Used in the paper |
|---|---|---|---|
| `GI.Axioms.transitiveAffected` ([`TransitiveAffected`](Workspace/Cited/TransitiveAffected.lean)) | Let `G` be a transitive group on `n` points with a surjection onto `Alt(k)`, where `k > max(8, 2 + log₂ n)`. Then no point stabilizer maps onto `Alt(k)`. | Helfgott, Bajpai, Dona, arXiv:1710.04574v1, Lemma 4.3(a). Babai, arXiv:1512.03547v2, Section 8. | Lemma A.15, Corollary A.25 |
| `GI.Axioms.marotiPrimitive` ([`MarotiPrimitive`](Workspace/Cited/MarotiPrimitive.lean)) | A primitive group of degree `n ≥ 25` has order less than `n^(1 + ⌊log₂ n⌋)`, or it lies in `Sym(m) wr Sym(r)` in its product action on `k`-sets and contains `Alt(m)^r`. | Maróti, J. Algebra 258 (2002), Theorem 1.1, through Helfgott, Bajpai, Dona, Theorem 3.1. | the dispatcher, Corollary A.13 |
| `GI.Axioms.sixTransitiveContainsAlt` ([`SixTransitiveContainsAlt`](Workspace/Cited/SixTransitive.lean)) | A 6-transitive group of degree `n ≥ 6` contains `Alt(n)`. | Helfgott, Bajpai, Dona, Section 6.2, Case 2b. | Section A.3, aggregation |
| `GI.Axioms.gmpOutBound` ([`GMPOutBound`](Workspace/Cited/GMP.lean)) | For a finite nonabelian simple group `T`, `\|Out T\| ≤ 2 √\|T\|`. | Guralnick, Maróti, Pyber, Adv. Math. 310 (2017), Lemma 7.7. | Lemma A.21, and Lemma A.8 through `\|Aut T\| ≤ \|T\|²` |
| `GI.Axioms.gmpTransitiveNonabelian` ([`GMPTransitiveNonabelian`](Workspace/Cited/GMP.lean)) | Let `G` be a transitive normal subgroup of `A ≤ Sym(n)`. Then the product of the orders of the nonabelian composition factors of `A/G` is at most `n^(log₂ n)`. | Guralnick, Maróti, Pyber, Theorem 1.4. | Corollary A.22 |
| `GI.Axioms.simpleValuationDegree` ([`SimpleValuationDegree`](Workspace/Cited/SimpleValuationDegree.lean)) | There is a constant `A` with the following property. Let `T` be a finite nonabelian simple group that is not alternating, acting faithfully on `n` points. Then `v_ℓ(\|Aut T\|) ≤ A log n` for some `ℓ ∈ {3, 5}`. | The order formulas for the groups of Lie type and their outer automorphisms, and the minimal degrees in Guest, Morris, Praeger, Spiga, Trans. AMS 367 (2015), Table 4. | Lemma A.8 |

## Algorithms

Each of these axioms says that a cited algorithm runs in polynomial time on the machine of
`Workspace/Statement/Machine.lean`. Its type has the form `∃ p, PolyTimeAt T p`, where the task
`T` says what a correct output is ([`Workspace/Cited/Algorithm.lean`](Workspace/Cited/Algorithm.lean)).
The tasks are in [`Workspace/Cited/AlgoPermGroups.lean`](Workspace/Cited/AlgoPermGroups.lean).
The input is a permutation group given by generators.

| Axiom | Task | Source | Used in the paper |
|---|---|---|---|
| `GI.Axioms.chiefSeriesAlgo` | Find a chief series of `G`. | Luks, Miyazaki, *Polynomial-time normalizers*, DMTCS 13:4 (2011), Theorem 3.1(x). Seress, *Permutation Group Algorithms* (2003), Section 6.2.7. | after Lemma A.21 |
| `GI.Axioms.quotientCentralizer` | Given `K ⊴ G` and subgroups `H` and `N` of `G` that contain `K`, with `H` normalizing `N`, find the preimage of `C_{H/K}(N/K)` in `H`. | Luks, Miyazaki, Lemma 3.2 (Kantor and Luks). | after Lemma A.21 |
| `GI.Axioms.sylowAlgo` | Given a prime `p`, find a Sylow `p`-subgroup of `G`. | Luks, Miyazaki, Theorem 3.1(xi). Luks, DIMACS 11 (1993), Lemma 8.3(i) (Kantor). | proof of Lemma A.19 |
| `GI.Axioms.sylowConjugate` | Given two Sylow `p`-subgroups `P₁` and `P₂` of `G`, find `g ∈ G` with `P₁^g = P₂`. | Luks, Miyazaki, Theorem 3.1(xi). Luks, DIMACS 11 (1993), Lemma 8.3(ii). | proof of Lemma A.19 |
