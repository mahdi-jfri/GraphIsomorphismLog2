import Workspace.Impl.LinObjectDataSpec
import Workspace.Lang.Prims.Ops

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectKernelPrefix {G : Type*} [Group G] (A : Subgroup G) (Bs : List (Subgroup G)) (i : ℕ) : Subgroup G :=
  (Bs.take i).foldl (fun K B => K ⊓ B) A

theorem linObjectKernelFold_le {G : Type*} [Group G] (A : Subgroup G) (Bs : List (Subgroup G)) :
    Bs.foldl (fun K B => K ⊓ B) A ≤ A := by
  induction Bs generalizing A with
  | nil => exact le_rfl
  | cons B Bs ih => exact (ih (A ⊓ B)).trans inf_le_left

theorem linObjectKernelPrefix_le {G : Type*} [Group G] (A : Subgroup G) (Bs : List (Subgroup G)) (i : ℕ) :
    linObjectKernelPrefix A Bs i ≤ A := linObjectKernelFold_le A (Bs.take i)

@[simp] theorem linObjectKernelPrefix_zero {G : Type*} [Group G] (A : Subgroup G) (Bs : List (Subgroup G)) :
    linObjectKernelPrefix A Bs 0 = A := rfl

theorem linObjectKernelPrefix_succ {G : Type*} [Group G] (A : Subgroup G) (Bs : List (Subgroup G)) (i : Fin Bs.length) :
    linObjectKernelPrefix A Bs (i.val + 1) = linObjectKernelPrefix A Bs i.val ⊓ Bs.get i := by
  have he : Bs.take (i.val + 1) = Bs.take i.val ++ [Bs.get i] := by
    rw [List.take_add_one,List.getElem?_eq_getElem i.isLt]
    simp
  unfold linObjectKernelPrefix
  rw [he,List.foldl_append]
  rfl

theorem linObjectKernelPrefix_mem {G : Type*} [Group G] (A : Subgroup G) (Bs : List (Subgroup G)) (g : G) :
    g ∈ linObjectKernelPrefix A Bs Bs.length ↔ g ∈ A ∧ ∀ B ∈ Bs, g ∈ B := by
  unfold linObjectKernelPrefix
  rw [List.take_length]
  induction Bs generalizing A with
  | nil => simp
  | cons B Bs ih =>
    simp only [List.foldl_cons,ih,Subgroup.mem_inf,List.forall_mem_cons,and_assoc]

theorem linObjectKernelPrefix_solvable {G : Type*} [Group G] (A : Subgroup G) (hsol : IsSolvable A)
    (Bs : List (Subgroup G)) (i : ℕ) : IsSolvable (linObjectKernelPrefix A Bs i) := by
  letI : IsSolvable A := hsol
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective (linObjectKernelPrefix_le A Bs i))

/-- Intersect the accumulator with the next collected local stabilizer.
The coset intersection is nonempty because its translating element is one. -/
def linObjectKernelStepF (jsci mkGroup : ℕ) : Expr :=
  let A := .get (arg 0) (.nat 0)
  .letE (.prim jsci (mk3 (arg 2) (.get (.get (arg 0) (.nat 1)) (arg 1))
    (.get (.get A (.nat 1)) (.nat 0))))
    (.call mkGroup (mk2 (.get A (.nat 0)) (.get (.var 1) (.nat 1))))

def linObjectKernelFuns (b jsci : ℕ) : List Expr :=
  loopFuns b (.length (arg 1)) (arg 0) (linObjectKernelStepF jsci (b + 3)) ++ mkGroupFuns (b + 3)

theorem linObjectKernelFuns_length (b jsci : ℕ) : (linObjectKernelFuns b jsci).length = 10 := rfl

structure linObjectKernelAt (P : Program) (b jsci : ℕ) (hs : SolvableCosetIntersection) : Prop where
  loop : P.HasAt b (loopFuns b (.length (arg 1)) (arg 0) (linObjectKernelStepF jsci (b + 3)))
  make : P.HasAt (b + 3) (mkGroupFuns (b + 3))
  prim : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs)

theorem linObjectKernelAt_of {P : Program} {b jsci : ℕ} {hs : SolvableCosetIntersection}
    (h : P.HasAt b (linObjectKernelFuns b jsci))
    (hj : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs)) : linObjectKernelAt P b jsci hs :=
  ⟨h.left,h.right,hj⟩

end GI.Impl
