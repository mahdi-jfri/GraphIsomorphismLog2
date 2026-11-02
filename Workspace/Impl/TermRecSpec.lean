import Workspace.Impl.TermRecMath
import Workspace.Impl.TermRecCost
import Workspace.Impl.Weights

/-!
# The recursion of Theorem A.20 as a program statement (T5)

`Iface.TermRecSpec Pg K D g` is the statement a program for the recursion of Theorem A.20 must
meet, in the encoded object model of `TermGlue.lean`. On `[ℓ, gens H, gens N, X, Y]`, with `H`
a solvable cover, `N ⊴ H`, fuel `ℓ` at least the derived length of `H/N`
(`relDerived H N ℓ ≤ N`) and at most `n² + 5` (so that computing the derived series costs a
polynomial), `N` fixing every listed object, colors that name one subgroup each,
at most `n²` generators in every list, at most `M` objects per side and colors below `2M`, the
function `g` returns a canonical answer for `Iso_H(X, Y)` at cost at most
`(5 (M + 1)³ + 1)^ℓ · K (n + M + 2)^D`.

This is the form of the paper's recursion bound
`T_ℓ ≤ C (M + 1)³ T_{ℓ-1} + P(b, M)` unrolled (`tmRec_le`): one level makes at most
`(2M)² · M` pairwise calls and one profile call, at most `5 (M + 1)³` in all, and spends a
polynomial `P` of its own. `tmRec_spec_cost` turns it into `expLogSq` form for fuel at most
`5 log₃ n + 1` (Dixon's bound, cited `DixonDerivedLength`, through `tmRec_pow_le`).

Colors below `2M` hold at every level: a profile's color is the position of its class
representative among the at most `2M` pieces of both sides.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens)

/-- The input of one call of the recursion: `[ℓ, gens H, gens N, X, Y]`. -/
def tmRecIn {n : ℕ} (ℓ : ℕ) (σH σN : List (Perm (Fin n)))
    (X Y : List (ℕ × List (Perm (Fin n)) × Perm (Fin n))) : Val :=
  .list [.nat ℓ, encGroup σH, encGroup σN, tmGlObjsVal X, tmGlObjsVal Y]

/-- The listed objects are well formed: at most `n²` generators each, colors below `2M`, and
objects of one color have one subgroup. -/
def TmRecObjOK {n : ℕ} (M : ℕ) (Z : List (ℕ × List (Perm (Fin n)) × Perm (Fin n))) : Prop :=
  ∀ o ∈ Z, o.2.1.length ≤ n ^ 2 ∧ o.1 < 2 * M ∧
    ∀ o' ∈ Z, o.1 = o'.1 → gens o.2.1 = gens o'.2.1

namespace Iface

variable (Pg : Program)

/-- **The recursion of Theorem A.20** (solvable implicit multicoset transport), as a function of
a program. -/
def TermRecSpec (K D g : ℕ) : Prop :=
  ∀ {n : ℕ} (M ℓ : ℕ) (σH σN : List (Perm (Fin n)))
    (X Y : List (ℕ × List (Perm (Fin n)) × Perm (Fin n))),
    IsSolvable (gens σH) → gens σN ≤ gens σH → GI.Multicoset.Normalizes (gens σH) (gens σN) →
    relDerived (gens σH) (gens σN) ℓ ≤ gens σN → ℓ ≤ n ^ 2 + 5 →
    Fixes (gens σN) (tmGlMs X) → Fixes (gens σN) (tmGlMs Y) →
    σH.length ≤ n ^ 2 → σN.length ≤ n ^ 2 → X.length ≤ M → Y.length ≤ M →
    TmRecObjOK M (X ++ Y) →
    FunAll Pg g (tmRecIn ℓ σH σN X Y) (fun u cost =>
      AnsC (Equiv.refl (Fin n)) u (Iso (gens σH) (tmGlMs X) (tmGlMs Y)) ∧
      (cost : ℝ) ≤ (5 * ((M : ℝ) + 1) ^ 3 + 1) ^ ℓ * (K * (((n + M : ℕ) : ℝ) + 2) ^ D))

end Iface

/-- **The cost of the recursion in `expLogSq` form.** For fuel `ℓ ≤ 5 log₃ n + 1` the bound of
`TermRecSpec` is at most `expLogSq (3 (log K + D) + tmRecA 5) (n + M)`. -/
theorem tmRec_spec_cost {K D n M ℓ : ℕ} (hK : 1 ≤ K)
    (hℓ : (ℓ : ℝ) ≤ 5 * Real.logb 3 n + 1) :
    (5 * ((M : ℝ) + 1) ^ 3 + 1) ^ ℓ * (K * (((n + M : ℕ) : ℝ) + 2) ^ D) ≤
      expLogSq (3 * (Real.log K + D) + tmRecA 5) (n + M) := by
  have h1 := tmRec_pow_le (C₀ := 5) (by norm_num) (b := n) (M := M) (N := n + M)
    (by omega) (by omega) hℓ
  have h2 := pow_le_expLogSq (A := (K : ℝ)) (by exact_mod_cast hK) D (n + M)
  calc (5 * ((M : ℝ) + 1) ^ 3 + 1) ^ ℓ * (K * (((n + M : ℕ) : ℝ) + 2) ^ D)
      ≤ expLogSq (tmRecA 5) (n + M) * expLogSq (3 * (Real.log K + D)) (n + M) :=
        mul_le_mul h1 h2 (by positivity) (expLogSq_nonneg _ _)
    _ = expLogSq (3 * (Real.log K + D) + tmRecA 5) (n + M) := by
        rw [tm_expLogSq_mul, add_comm]

end GI.Impl
