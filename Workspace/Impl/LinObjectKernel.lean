module

public import Workspace.Impl.LinObjectDataSpec
public import Workspace.Lang.Prims.Ops

@[expose] public section

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

theorem linObjectKernelFold_ge {G : Type*} [Group G] (N A : Subgroup G) (Bs : List (Subgroup G))
    (hNA : N ≤ A) (hBs : ∀ B ∈ Bs, N ≤ B) :
    N ≤ Bs.foldl (fun K B => K ⊓ B) A := by
  induction Bs generalizing A with
  | nil => exact hNA
  | cons B Bs ih =>
    exact ih (A ⊓ B) (le_inf hNA (hBs B (List.mem_cons_self ..)))
      (fun B' hB' => hBs B' (List.mem_cons_of_mem _ hB'))

theorem linObjectKernelPrefix_normalizes {n : ℕ} (N A : Subgroup (Equiv.Perm (Fin n)))
    (Bs : List (Subgroup (Equiv.Perm (Fin n)))) (hNA : N ≤ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ N)
    (hBsN : ∀ B ∈ Bs, N ≤ B) (i : ℕ) {B : Subgroup (Equiv.Perm (Fin n))} (hBA : B ≤ A) :
    GI.Lang.Normalizes B (linObjectKernelPrefix A Bs i) := by
  intro b hb k hk
  have hkA : k ∈ A := linObjectKernelPrefix_le A Bs i hk
  have hbA : b ∈ A := hBA hb
  have hc : b * k * b⁻¹ * k⁻¹ ∈ N := hcomm b hbA k hkA
  have hcK : b * k * b⁻¹ * k⁻¹ ∈ linObjectKernelPrefix A Bs i :=
    linObjectKernelFold_ge N A (Bs.take i) hNA (fun B' hB' => hBsN B' (List.mem_of_mem_take hB')) hc
  have hmul := (linObjectKernelPrefix A Bs i).mul_mem hcK hk
  simpa [mul_assoc] using hmul

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
