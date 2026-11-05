module

public import Workspace.Proved.GMPLuksStabilizers

@[expose] public section

/-! # The two action kernels computing a normal-subgroup centralizer -/

namespace GI.Proved

variable {H V : Type*} [Group H] [MulAction H V]

theorem gmp_conjugation_aut_ker (N : Subgroup H) [N.Normal] :
    (MulAut.conjNormal (H := N)).ker = Subgroup.centralizer (N : Set H) := by
  have hi : Function.Injective (MulAut.toPerm N) := by
    intro a b hab
    apply MulEquiv.ext
    intro n
    exact congrArg (fun p : Equiv.Perm N => p n) hab
  rw [← MonoidHom.ker_comp_of_injective (MulAut.conjNormal (H := N)) (MulAut.toPerm N) hi]
  exact gmp_conjugation_ker N

/-- Every centralizing element survives the first kernel computation. -/
theorem gmp_centralizer_le_first_kernel (N : Subgroup H) [N.Normal] :
    Subgroup.centralizer (N : Set H) ≤ (gmpLuksFirstAction (V := V) N).ker := by
  intro h hh
  rw [← gmp_conjugation_aut_ker N] at hh
  apply (gmpLuksFirstAction_mem_ker N h).mpr
  intro x
  rw [← gmp_stabilizer_conjugation N h x]
  change (MulAction.stabilizer N x).map (MulAut.conjNormal h).toMonoidHom = _
  change MulAut.conjNormal h = 1 at hh
  rw [hh]
  exact Subgroup.map_id _

/-- Luks's second action restricted to the first kernel. Its domain
consists of elements preserving every normal-subgroup point stabilizer. -/
def gmpNormalCentralizerAction (N : Subgroup H) [N.Normal] :
    (gmpLuksFirstAction (V := V) N).ker →*
      Equiv.Perm (Σ a : V, N ⧸ MulAction.stabilizer N a) :=
  gmpLuksSecondAction
    ((MulAut.conjNormal (H := N)).comp (gmpLuksFirstAction (V := V) N).ker.subtype)
    (fun k a => gmpLuksFirstAction_preserves N k a)

/-- Luks, Proposition 7.3: the second kernel, inside the first one, is
exactly the normal-subgroup centralizer. This proves correctness of the
two kernel constructions without any classification input. -/
theorem gmpNormalCentralizerAction_ker [FaithfulSMul H V]
    (N : Subgroup H) [N.Normal] :
    (gmpNormalCentralizerAction (V := V) N).ker =
      (Subgroup.centralizer (N : Set H)).subgroupOf (gmpLuksFirstAction (V := V) N).ker := by
  unfold gmpNormalCentralizerAction
  erw [gmpLuksSecondAction_ker, ← MonoidHom.comap_ker, gmp_conjugation_aut_ker]
  rfl

end GI.Proved
