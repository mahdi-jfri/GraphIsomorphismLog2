import Workspace.Proved.PalfyBasic

/-!
# The statement of LM Theorem 5.1 for solvable groups

Luks–Miyazaki, DMTCS 13:4 (2011), Theorem 5.1, for a solvable linear group `G` on a
finite-dimensional space `V` over `ZMod p`. We do not assume that `V` is irreducible. Instead
there is a third outcome, a proper nonzero `G`-invariant subspace. The three outcomes are:

* (i) `VsTImprim`: a normal `H ≤ G` and `m ≥ 2` subspaces of equal dimension whose direct sum
  is `V`, permuted by `H`, with `|G : H| ≤ m ^ vsTE`;
* (ii) `VsTAbel`: an abelian normal `A ≤ G` with `|G : A| ≤ 24 n`, for `n = dim V`;
* (iii) `VsTSub`: a proper nonzero `G`-invariant subspace.

This file also proves the final loop of LM §5.6 (`vsT_loop`): it is enough to show that every
abelian normal `A` of index more than `24 n` gives (i), (iii), or a larger abelian normal
subgroup.
-/

namespace GI.Proved

open Module

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- The exponent in the index bound of outcome (i). -/
def vsTE : ℕ := 414

/-- Outcome (i) of Theorem 5.1: `H ≤ G` is normal in `G`, the `m ≥ 2` subspaces `W i` have
equal dimension and direct sum `V`, every element of `H` maps each `W i` onto some `W j`, and
`|G : H| ≤ m ^ vsTE`. -/
def VsTImprim (G H : Subgroup (End (ZMod p) V)ˣ) {m : ℕ} (W : Fin m → Submodule (ZMod p) V) :
    Prop :=
  H ≤ G ∧ (H.subgroupOf G).Normal ∧ 2 ≤ m ∧ iSupIndep W ∧ iSup W = ⊤ ∧
  (∀ i j, finrank (ZMod p) (W i) = finrank (ZMod p) (W j)) ∧
  (∀ h ∈ H, ∀ i, ∃ j, (W i).map ((h : (End (ZMod p) V)ˣ) : End (ZMod p) V) = W j) ∧
  H.relIndex G ≤ m ^ vsTE

/-- `A ≤ G` is normal in `G` and abelian. -/
def VsTAbNormal (G A : Subgroup (End (ZMod p) V)ˣ) : Prop :=
  A ≤ G ∧ (A.subgroupOf G).Normal ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a

/-- Outcome (ii) of Theorem 5.1: an abelian normal subgroup of index at most `24 n`. -/
def VsTAbel (G A : Subgroup (End (ZMod p) V)ˣ) : Prop :=
  VsTAbNormal G A ∧ A.relIndex G ≤ 24 * finrank (ZMod p) V

/-- Outcome (iii) of Theorem 5.1: a proper nonzero `G`-invariant subspace. -/
def VsTSub (G : Subgroup (End (ZMod p) V)ˣ) (W : Submodule (ZMod p) V) : Prop :=
  palfyInv G W ∧ W ≠ ⊥ ∧ W ≠ ⊤

/-- One of the three outcomes of Theorem 5.1 holds for `G`. -/
def VsTOut (G : Subgroup (End (ZMod p) V)ˣ) : Prop :=
  (∃ (H : Subgroup (End (ZMod p) V)ˣ) (m : ℕ) (W : Fin m → Submodule (ZMod p) V),
      VsTImprim G H W) ∨
    (∃ A, VsTAbel G A) ∨ ∃ W, VsTSub G W

/-- The trivial subgroup is abelian and normal. -/
theorem vsTAbNormal_bot (G : Subgroup (End (ZMod p) V)ˣ) : VsTAbNormal G ⊥ := by
  refine ⟨bot_le, ?_, ?_⟩
  · rw [Subgroup.bot_subgroupOf]
    exact Subgroup.normal_bot
  · intro a ha b hb
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

/-- **The final loop of LM §5.6.** Suppose that every abelian normal `A ≤ G` with
`|G : A| > 24 n` gives outcome (i), outcome (iii), or an abelian normal `B` with `A < B`.
Then one of the outcomes holds. Proof: take a maximal abelian normal `A` (the subgroups form
a finite set, and `⊥` is one of them). If `|G : A| ≤ 24 n`, this is (ii). Otherwise the
hypothesis gives (i) or (iii), since a larger `B` would contradict maximality. -/
theorem vsT_loop [Finite V] (G : Subgroup (End (ZMod p) V)ˣ)
    (hstep : ∀ A, VsTAbNormal G A → 24 * finrank (ZMod p) V < A.relIndex G →
      (∃ (H : Subgroup (End (ZMod p) V)ˣ) (m : ℕ) (W : Fin m → Submodule (ZMod p) V),
        VsTImprim G H W) ∨ (∃ W, VsTSub G W) ∨ ∃ B, VsTAbNormal G B ∧ A < B) :
    VsTOut G := by
  obtain ⟨A, hA, hmax⟩ := (wellFounded_gt (α := Subgroup (End (ZMod p) V)ˣ)).has_min
    {A | VsTAbNormal G A} ⟨⊥, vsTAbNormal_bot G⟩
  by_cases hle : A.relIndex G ≤ 24 * finrank (ZMod p) V
  · exact Or.inr (Or.inl ⟨A, hA, hle⟩)
  rcases hstep A hA (lt_of_not_ge hle) with h | h | ⟨B, hB, hAB⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact absurd hAB (hmax B hB)

end GI.Proved
