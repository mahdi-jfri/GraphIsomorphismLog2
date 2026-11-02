import Workspace.Impl.TermSplit

/-!
# The hypotheses of T2 and T4

Two steps of the terminal case are polynomial-time group computations that the paper takes from
[LM]. They are proved later; the rest of the terminal case uses them only through these two
statements.

* `Iface.TermRadSpec Pg K D g` (T2, the paragraph after Lemma A.21): from generators of `H` and of
  `N ⊴ H`, generators of the radical preimage `R` of `H/N` (`radicalPreimage`).
* `Iface.TermSupSpec Pg K D g` (T4, Lemma A.19): from generators of `R` and of `N ⊴ R` with
  `R/N` solvable, generators of a solvable `S ≤ R` with `S N = R`.

Both have cost at most `K (w + 1)^D`, with `w` the weight of the input: polynomial time, as in
the paper. The output is a generating list in the form of the cited tasks (`GensOf`: at most
`m²` generators).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens GensOf)

namespace Iface

variable (Pg : Program)

/-- **T2: the radical preimage** (paragraph after Lemma A.21). On `[gens H, gens N]` with
`N ≤ H` normalized by `H`, the function `g` returns generators of `radicalPreimage H N`, the full
preimage in `H` of the solvable radical of `H/N`, at cost at most `K (w + 1)^D`. -/
def TermRadSpec (K D g : ℕ) : Prop :=
  ∀ {m : ℕ} (σH σN : List (Perm (Fin m))), gens σN ≤ gens σH →
    GI.Multicoset.Normalizes (gens σH) (gens σN) →
    FunAll Pg g (.list [encGroup σH, encGroup σN]) (fun u cost =>
      GensOf (radicalPreimage (gens σH) (gens σN)) u ∧
      cost ≤ K * ((Val.list [encGroup σH, encGroup σN]).wt + 1) ^ D)

/-- **T4: the solvable supplement** (Lemma A.19). On `[gens R, gens N]` with `N ⊴ R` and `R/N`
solvable, the function `g` returns generators of a solvable `S ≤ R` with `S ⊔ N = R`, at cost at
most `K (w + 1)^D`. -/
def TermSupSpec (K D g : ℕ) : Prop :=
  ∀ {m : ℕ} (σR σN : List (Perm (Fin m))), gens σN ≤ gens σR →
    ∀ [((gens σN).subgroupOf (gens σR)).Normal],
    IsSolvable ((gens σR) ⧸ (gens σN).subgroupOf (gens σR)) →
    FunAll Pg g (.list [encGroup σR, encGroup σN]) (fun u cost =>
      ∃ S : Subgroup (Perm (Fin m)), GensOf S u ∧ S ≤ gens σR ∧ IsSolvable S ∧
        S ⊔ gens σN = gens σR ∧
        cost ≤ K * ((Val.list [encGroup σR, encGroup σN]).wt + 1) ^ D)

end Iface

end GI.Impl
