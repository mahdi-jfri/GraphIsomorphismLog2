import Workspace.Impl.LinWreathGenerators
import Workspace.Lang.Prims.Graph

/-! Number the explicit two-copy cover with the first copy followed by the
second. This is the layout read and written by the transporter programs. -/
namespace GI.Impl
open Equiv

/-- The group element 1 names the first copy, and the nonidentity element
names the second. -/
def linTwoSumEquiv (Ω : Type*) : (Ω × linTwo) ≃ (Ω ⊕ Ω) where
  toFun x := if x.2 = 1 then Sum.inl x.1 else Sum.inr x.1
  invFun x := x.elim (fun x => (x, 1)) (fun x => (x, linTwoSwap))
  left_inv x := by
    rcases x with ⟨x, q⟩
    rcases linTwo_cases q with rfl | rfl <;> simp
  right_inv x := by
    cases x <;> simp

def linWreathNumber (n : ℕ) : (Fin n × linTwo) ≃ Fin (n + n) :=
  (linTwoSumEquiv (Fin n)).trans finSumFinEquiv

@[simp] theorem linWreathNumber_one {n : ℕ} (x : Fin n) :
    linWreathNumber n (x, 1) = x.castAdd n := by simp [linWreathNumber, linTwoSumEquiv]

@[simp] theorem linWreathNumber_swap {n : ℕ} (x : Fin n) :
    linWreathNumber n (x, linTwoSwap) = x.natAdd n := by simp [linWreathNumber, linTwoSumEquiv]

variable {H Ω : Type*} [Group H] [MulAction H Ω]

@[simp] theorem linWreathCover_apply (a : H ≀ᵣ linTwo) (x : Ω) (q : linTwo) :
    linWreathCover a (x, q) = (a.left (a.right * q) • x, a.right * q) := rfl

/-- Numbered permutation representation of the wreath. -/
def linWreathFinCover (H : Type*) [Group H] {n : ℕ} [MulAction H (Fin n)] :
    (H ≀ᵣ linTwo) →* Perm (Fin (n + n)) where
  toFun a := (linWreathNumber n).permCongr (linWreathCover a)
  map_one' := by ext x; simp [Equiv.permCongr_apply]
  map_mul' a b := by ext x; simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]

@[simp] theorem linWreathFinCover_apply {n : ℕ} [MulAction H (Fin n)]
    (a : H ≀ᵣ linTwo) (x : Fin n × linTwo) :
    linWreathFinCover H a (linWreathNumber n x) = linWreathNumber n (linWreathCover a x) := by
  change (linWreathNumber n).permCongr (linWreathCover a) (linWreathNumber n x) = _
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]

theorem linWreathFinCover_injective {n : ℕ} [Nonempty (Fin n)]
    [MulAction H (Fin n)] [FaithfulSMul H (Fin n)] :
    Function.Injective (linWreathFinCover (n := n) H) :=
  (linWreathNumber n).permCongr.injective.comp linWreathCover_injective

/-- In the first-copy generator, the second copy stays fixed. -/
theorem linWreathFinCover_single_one {n : ℕ} [MulAction H (Fin n)] (h : H) (x : Fin n) :
    linWreathFinCover H (linWreathSingle 1 h) (x.castAdd n) = (h • x).castAdd n ∧
    linWreathFinCover H (linWreathSingle 1 h) (x.natAdd n) = x.natAdd n := by
  constructor
  · rw [← linWreathNumber_one, linWreathFinCover_apply]
    simp [linWreathCover_apply, linWreathSingle]
  · rw [← linWreathNumber_swap, linWreathFinCover_apply]
    simp [linWreathCover_apply, linWreathSingle]

theorem linWreathFinCover_single_swap {n : ℕ} [MulAction H (Fin n)] (h : H) (x : Fin n) :
    linWreathFinCover H (linWreathSingle linTwoSwap h) (x.castAdd n) = x.castAdd n ∧
    linWreathFinCover H (linWreathSingle linTwoSwap h) (x.natAdd n) = (h • x).natAdd n := by
  constructor
  · rw [← linWreathNumber_one, linWreathFinCover_apply]
    simp [linWreathCover_apply, linWreathSingle, Ne.symm linTwoSwap_ne_one]
  · rw [← linWreathNumber_swap, linWreathFinCover_apply]
    simp [linWreathCover_apply, linWreathSingle]

theorem linWreathFinCover_swap {n : ℕ} [MulAction H (Fin n)] (x : Fin n) :
    linWreathFinCover H (linWreathSwap : H ≀ᵣ linTwo) (x.castAdd n) = x.natAdd n ∧
    linWreathFinCover H (linWreathSwap : H ≀ᵣ linTwo) (x.natAdd n) = x.castAdd n := by
  constructor
  · rw [← linWreathNumber_one, linWreathFinCover_apply]
    simp [linWreathCover_apply, linWreathSwap]
  · rw [← linWreathNumber_swap, linWreathFinCover_apply]
    simp [linWreathCover_apply, linWreathSwap]

/-- The swapping generator's restriction is exactly the original-cover
transporter. This is an equality of its numbered point images. -/
theorem linWreathFinCover_extract {n : ℕ} [MulAction H (Fin n)]
    (a : H ≀ᵣ linTwo) (ha : a.right = linTwoSwap) (x : Fin n) :
    linWreathFinCover H a (x.castAdd n) = (a.left linTwoSwap • x).natAdd n := by
  rw [← linWreathNumber_one, linWreathFinCover_apply, linWreathCover_swap_apply a ha,
    linWreathNumber_swap]

end GI.Impl
