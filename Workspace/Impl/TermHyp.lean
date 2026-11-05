module

public import Workspace.Impl.TermSplit

@[expose] public section

/-!
# The hypothesis of T2

One step of the terminal case is a polynomial-time group computation that the paper takes from
[LM]. It is proved later; the rest of the terminal case uses it only through this statement.

* `Iface.TermRadSpec Pg K D g` (T2, the paragraph after Lemma A.21): from generators of `H` and of
  `N ⊴ H`, generators of the radical preimage `R` of `H/N` (`radicalPreimage`).

It has cost at most `K (w + 1)^D`, with `w` the weight of the input: polynomial time, as in
the paper. The output is a generating list in the form of the cited tasks (`GensOf`: at most
`m²` generators).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens GensOf)

namespace Iface

variable (Pg : Program)

/-- **T2: the solvable-quotient subgroup** (paragraph after Lemma A.21). On `[gens H, gens N]` with
`N ≤ H` normalized by `H` and `N` transitive on `Fin m`, the function `g` returns generators of a
subgroup `R'` with `N ≤ R' ≤ H`, `R'/N` solvable, and `[H : R'] ≤ b(H/N)²`, at cost at most
`K (w + ⌈expLogSq 3 m⌉₊ + 1)^D`. -/
def TermRadSpec (K D g : ℕ) : Prop :=
  ∀ {m : ℕ} (σH σN : List (Perm (Fin m))), gens σN ≤ gens σH →
    GI.Multicoset.Normalizes (gens σH) (gens σN) →
    MulAction.IsPretransitive (gens σN) (Fin m) →
    FunAll Pg g (.list [encGroup σH, encGroup σN]) (fun u cost =>
      ∃ R' : Subgroup (Perm (Fin m)),
        GensOf R' u ∧ R' ≤ gens σH ∧ gens σN ≤ R' ∧
        (∃ ℓ, relDerived R' (gens σN) ℓ ≤ gens σN) ∧
        (∀ [((gens σN).subgroupOf (gens σH)).Normal],
          (R'.subgroupOf (gens σH)).index ≤
            GI.Composition.bFac ((gens σH) ⧸ (gens σN).subgroupOf (gens σH)) ^ 2) ∧
        cost ≤ K * ((Val.list [encGroup σH, encGroup σN]).wt + ⌈expLogSq 3 m⌉₊ + 1) ^ D)

end Iface

end GI.Impl
