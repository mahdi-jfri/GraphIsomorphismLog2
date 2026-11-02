import Workspace.Impl.SCosProg
import Workspace.Proved.SCosMath
import Workspace.Proved.NIntMath
import Workspace.Impl.LargestOrbit
import Workspace.Proved.SCosPalfy

/-!
# Problem and answer values

`N = n + n`. A pair `x = (a, b)` is the permutation `nintSum x = a ⊕ b` of `Fin N`; a group of
pairs `𝒢` is `𝒢.map nintSum`. A set `Φ` of points of `Fin n` is the set `scosPhiF Φ` of the
points `Fin.castAdd n a` of the first copy, given by its indicator `scosInd Φ`.

* `ScosProb n v 𝒢 x Φ`: `v = [gv, encPerm (a ⊕ b), ind]` is a problem of the recursion: `gv` a
  group value of `𝒢` of weight at most `scosW n`, `Φ` invariant under the first coordinates of
  `𝒢`, and the first coordinates of `𝒢` form a solvable group.
* `ScosAns n w x 𝒢 Φ`: `w` is `[]` and the subcoset `scosC x 𝒢 Φ` is empty, or
  `w = [encPerm (z₁ ⊕ z₂), lv]` with `z` in the subcoset and `lv` a group value of `L(𝒢, Φ)` of
  weight at most `scosW n` (then the subcoset is `z L(𝒢, Φ)`, `scosC_eq`).
* `scosMo 𝒢 Φ`: the largest size of an orbit of the first coordinates of `𝒢` on `Φ`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

variable {n : ℕ}

/-- `Φ` as a set of points of the first copy in `Fin (n + n)`. -/
def scosPhiF (Φ : Finset (Fin n)) : Set (Fin (n + n)) := Fin.castAdd n '' (Φ : Set (Fin n))

/-- The indicator of `Φ` on `Fin (n + n)`, in the format of `domFuns`. -/
noncomputable def scosInd (Φ : Finset (Fin n)) : Val :=
  indVal (Equiv.refl (Fin (n + n))) (scosPhiF Φ)

/-- The weight bound of the group values of the recursion (that of `pstab_spec`, `ker_spec`). -/
def scosW (n : ℕ) : ℕ := 320 * (n + n + 1) ^ 6

/-- **A problem of the recursion.** -/
structure ScosProb (n : ℕ) (v : Val) (𝒢 : Subgroup (ScosPair n)) (x : ScosPair n)
    (Φ : Finset (Fin n)) : Prop where
  val : ∃ gv, v = .list [gv, encPerm (nintSum x), scosInd Φ] ∧
    GroupVal (n + n) gv (𝒢.map nintSum) ∧ gv.wt ≤ scosW n
  inv : ScosInv 𝒢 Φ
  solv : IsSolvable (𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n))))

/-- **An answer of the recursion.** -/
def ScosAns (n : ℕ) (w : Val) (x : ScosPair n) (𝒢 : Subgroup (ScosPair n))
    (Φ : Finset (Fin n)) : Prop :=
  (w = .list [] ∧ scosC x 𝒢 Φ = ∅) ∨
  ∃ z ∈ scosC x 𝒢 Φ, ∃ lv, w = .list [encPerm (nintSum z), lv] ∧
    GroupVal (n + n) lv ((scosL 𝒢 Φ).map nintSum) ∧ lv.wt ≤ scosW n

open Classical in
/-- The largest size of an orbit of the first coordinates of `𝒢` on `Φ` (0 for `Φ = ∅`). -/
noncomputable def scosMo (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) : ℕ :=
  Φ.sup fun a => (Φ.filter fun b => ∃ g ∈ 𝒢, g.1 a = b).card

/-- The conclusion of `scos_palfy_classes` for the exponent `c`. -/
def ScosPalfyC (c : ℕ) : Prop :=
  ∀ (k : ℕ) (H : Subgroup (Perm (Fin k))) (lab : Fin k → ℕ), IsSolvable H →
    (∀ i j : Fin k, ∃ h ∈ H, h i = j) → IsMinimalBlocks H lab →
    ∀ S : Finset (Perm (Fin k)), (∀ s ∈ S, s ∈ H) →
      (∀ s ∈ S, ∀ t ∈ S, (∀ i, lab (s i) = lab (t i)) → s = t) →
        S.card ≤ ((Finset.univ.image lab).card + 1) ^ c

theorem scos_palfyC (hP : ScosPalfyBound) : ∃ c, ScosPalfyC c := scos_palfy_classes hP

/-- `𝒢` is transitive on `Φ` (through the first coordinates). -/
def ScosTrans (𝒢 : Subgroup (ScosPair n)) (Φ : Finset (Fin n)) : Prop :=
  ∀ a ∈ Φ, ∀ b ∈ Φ, ∃ g ∈ 𝒢, g.1 a = b

end GI.Impl
