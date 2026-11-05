module

public import Workspace.RowQuotients
public import Workspace.CleanRowKernel

@[expose] public section

/-!
# Definitions for the statement of Theorem A.18

Clean coordinates are an identification `e : B × I ≃ V`; block `i` is
`B × {i}`. A tuple `x : I → Sym(B)` acts on `V` by `x i` inside block `i`
(`cleanRowPerm`). This identifies the row-preserving permutations of `V`
with `Sym(B)^m`, and the block kernel `K` with a subgroup of `Sym(B)^m`.
-/

namespace GI.Paper

open Equiv

variable {B I V : Type*}

/-- In clean coordinates `e`, the permutation of `V` that applies `x i`
inside block `i`: `e (b, i) ↦ e (x i b, i)`. -/
def cleanRowPerm (e : B × I ≃ V) : (I → Perm B) →* Perm V :=
  (relabelPerm e).toMonoidHom.comp rowCoordinatePerm

theorem cleanRowPerm_apply (e : B × I ≃ V) (x : I → Perm B) (b : B) (i : I) :
    cleanRowPerm e x (e (b, i)) = e (x i b, i) := by
  change e (rowCoordinatePerm x (e.symm (e (b, i)))) = _
  rw [e.symm_apply_apply]
  rfl

/-- The paper's `H = K[B] ≤ Sym(B)`: the permutations induced on block `i0` by
the elements of `G` that preserve every block. -/
def cleanLocalGroup (G : Subgroup (Perm V)) (e : B × I ≃ V) (i0 : I) : Subgroup (Perm B) :=
  (G.comap (cleanRowPerm e)).map (rowEval i0)

/-- A tuple of elements of a subgroup `H ≤ Sym(B)`, acting blockwise. -/
def cleanLift (e : B × I ≃ V) (H : Subgroup (Perm B)) : (I → H) →* Perm V where
  toFun x := cleanRowPerm e (fun r => (x r).val)
  map_one' := (cleanRowPerm e).map_one
  map_mul' x y := (cleanRowPerm e).map_mul (fun r => (x r).val) (fun r => (y r).val)

variable [DecidableEq I] (G : Subgroup (Perm V)) (K : Subgroup G) (e : B × I ≃ V) (i0 : I)

/-- The paper's `M = K ∩ N^m`, as a subgroup of `G`. -/
def rowNormalM (N : Subgroup (cleanLocalGroup G e i0)) : Subgroup G :=
  K ⊓ ((rowPower N).map (cleanLift e (cleanLocalGroup G e i0))).subgroupOf G

/-- The paper's `M* = (N*)^m`, as a subgroup of `G` (its elements in `G`). -/
def rowNormalMstar (Nstar : Subgroup (cleanLocalGroup G e i0)) : Subgroup G :=
  ((rowPower Nstar).map (cleanLift e (cleanLocalGroup G e i0))).subgroupOf G

/-- The zero-sum subgroup of `(N/N*)^m`, with `N/N*` realized as the image of
`N` in `H/N*` and the group law written multiplicatively. The product is over
one enumeration of `I`; the order does not matter because `N/N*` is abelian. -/
def rowZeroSum {H : Subgroup (Perm B)} [Fintype I] (N Nstar : Subgroup H) [Nstar.Normal] :
    Set (I → H ⧸ Nstar) :=
  {q | (∀ r, q r ∈ N.map (QuotientGroup.mk' Nstar)) ∧ (Finset.univ.toList.map q).prod = 1}

/-- The conclusions of Theorem A.18 for given `N* ≤ N ≤ H`, the block kernel `K`,
clean coordinates `e`, the clean complement `R = s(Alt(m))`, and the block
`i0` used to define `H`.

* `N* ◁ N ◁ H` (both are normal in `H`; normality is the instance arguments);
* `N/N*` is abelian;
* `M* = (N*)^m` lies in `G`, `M = K ∩ N^m`, `M* ◁ M ◁ G`, `M ≤ K`;
* `M/M*` is the zero-sum subgroup of `(N/N*)^m`: the coordinatewise map
  `ψ : M → (H/N*)^m` has kernel `M*` and image `rowZeroSum N N*`;
* `K/M` is the diagonal `H/N`: the map `θ : G → H/N` sends `x ∈ K` to the class
  of any one of its coordinates; on `K` it is onto with kernel `M`;
* `MR ◁ G` and `G/(MR) ≅ H/N`: `θ` is onto with kernel `MR`. -/
structure IsRowNormalForm [Fintype I] (s : alternatingGroup I →* G)
    (N Nstar : Subgroup (cleanLocalGroup G e i0)) [N.Normal] [Nstar.Normal] : Prop where
  nstar_le : Nstar ≤ N
  abelian : ∀ a ∈ N, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ Nstar
  mstar_le_G : (rowPower Nstar).map (cleanLift e (cleanLocalGroup G e i0)) ≤ G
  m_le : rowNormalM G K e i0 N ≤ K
  m_normal : (rowNormalM G K e i0 N).Normal
  mstar_le_m : rowNormalMstar G e i0 Nstar ≤ rowNormalM G K e i0 N
  mstar_normal : ((rowNormalMstar G e i0 Nstar).subgroupOf (rowNormalM G K e i0 N)).Normal
  zero_sum : ∃ ψ : rowNormalM G K e i0 N →* (I → cleanLocalGroup G e i0 ⧸ Nstar),
    (∀ (g : rowNormalM G K e i0 N) (x : I → cleanLocalGroup G e i0),
      cleanLift e _ x = g.val.val → ψ g = fun r => (x r : cleanLocalGroup G e i0 ⧸ Nstar)) ∧
    ψ.ker = (rowNormalMstar G e i0 Nstar).subgroupOf (rowNormalM G K e i0 N) ∧
    Set.range ψ = rowZeroSum N Nstar
  diagonal : ∃ θ : G →* cleanLocalGroup G e i0 ⧸ N,
    (∀ (g : G) (x : I → cleanLocalGroup G e i0) (r : I),
      cleanLift e _ x = g.val → θ g = (x r : cleanLocalGroup G e i0 ⧸ N)) ∧
    Function.Surjective (θ.comp K.subtype) ∧
    (θ.comp K.subtype).ker = (rowNormalM G K e i0 N).subgroupOf K ∧
    θ.ker = rowNormalM G K e i0 N ⊔ s.range
  mr_normal : (rowNormalM G K e i0 N ⊔ s.range).Normal

end GI.Paper
