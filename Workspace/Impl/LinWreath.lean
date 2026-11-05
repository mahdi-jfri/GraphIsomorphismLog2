module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-! The two-copy wreath reduction used by A.20. The representation acts on
functions on two copies, and the covering group is still solvable. -/
namespace GI.Impl

abbrev linTwo := Multiplicative (ZMod 2)

def linTwoSwap : linTwo := Multiplicative.ofAdd 1

theorem linTwo_cases (q : linTwo) : q = 1 ∨ q = linTwoSwap := by
  change Multiplicative.ofAdd q.toAdd = 1 ∨ Multiplicative.ofAdd q.toAdd = linTwoSwap
  have h (t : ZMod 2) : t = 0 ∨ t = 1 := by
    have hv := ZMod.val_lt t
    have hh : t.val = 0 ∨ t.val = 1 := by omega
    rcases hh with hh | hh
    · left; apply ZMod.val_injective 2; simpa using hh
    · right; apply ZMod.val_injective 2; simpa [ZMod.val_one_eq_one_mod] using hh
  rcases h q.toAdd with h | h <;> simp [h, linTwoSwap]

@[simp] theorem linTwoSwap_ne_one : linTwoSwap ≠ 1 := by decide
@[simp] theorem linTwoSwap_mul_self : linTwoSwap * linTwoSwap = 1 := by decide
@[simp] theorem linTwoSwap_inv : linTwoSwap⁻¹ = linTwoSwap := by decide

variable {H : Type*} [Group H]

/-- Include the direct-product base of the wreath. -/
def linWreathBase : (linTwo → H) →* (H ≀ᵣ linTwo) where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' f g := by ext q <;> simp

def linWreathEval : (linTwo → H) →* H × H where
  toFun f := (f 1, f linTwoSwap)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem linWreathEval_injective : Function.Injective (linWreathEval (H := H)) := by
  intro f g h
  funext q
  rcases linTwo_cases q with rfl | rfl
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- Solvability follows from the solvable base H × H and the order-two quotient. -/
theorem linWreath_solvable [Group.IsSolvable H] : Group.IsSolvable (H ≀ᵣ linTwo) := by
  letI : Group.IsSolvable (linTwo → H) :=
    Group.isSolvable_of_isSolvable_injective linWreathEval_injective
  apply Group.isSolvable_of_ker_le_range (linWreathBase (H := H)) RegularWreathProduct.rightHom
  intro x hx
  have hh : x.right = 1 := hx
  exact ⟨x.left, by cases x; simp_all [linWreathBase]⟩

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The direct-sum action associated with a wreath element. At copy q it first
reads copy right⁻¹*q, then applies the q-th linear transformation. -/
def linWreathLinear (ρ : H →* (V ≃ₗ[R] V)) (w : H ≀ᵣ linTwo) :
    (linTwo → V) →ₗ[R] (linTwo → V) where
  toFun x q := ρ (w.left q) (x (w.right⁻¹ * q))
  map_add' x y := by ext q; simp
  map_smul' a x := by ext q; simp

@[simp] theorem linWreathLinear_apply (ρ : H →* (V ≃ₗ[R] V))
    (w : H ≀ᵣ linTwo) (x : linTwo → V) (q : linTwo) :
    linWreathLinear ρ w x q = ρ (w.left q) (x (w.right⁻¹ * q)) := rfl

@[simp] theorem linWreathLinear_one (ρ : H →* (V ≃ₗ[R] V)) :
    linWreathLinear ρ 1 = LinearMap.id := by
  ext x q
  simp [linWreathLinear]

theorem linWreathLinear_mul (ρ : H →* (V ≃ₗ[R] V)) (a b : H ≀ᵣ linTwo) :
    linWreathLinear ρ (a * b) = (linWreathLinear ρ a).comp (linWreathLinear ρ b) := by
  ext x q
  simp [linWreathLinear, map_mul, mul_assoc]

/-- The action is invertible because the wreath inverse acts as its inverse. -/
def linWreathEquiv (ρ : H →* (V ≃ₗ[R] V)) (w : H ≀ᵣ linTwo) :
    (linTwo → V) ≃ₗ[R] (linTwo → V) :=
  LinearEquiv.ofLinear (linWreathLinear ρ w) (linWreathLinear ρ w⁻¹)
    (by rw [← linWreathLinear_mul, mul_inv_cancel, linWreathLinear_one])
    (by rw [← linWreathLinear_mul, inv_mul_cancel, linWreathLinear_one])

/-- The two-copy representation, with no faithfulness assumption on ρ. -/
def linWreathRep (ρ : H →* (V ≃ₗ[R] V)) :
    (H ≀ᵣ linTwo) →* ((linTwo → V) ≃ₗ[R] (linTwo → V)) where
  toFun := linWreathEquiv ρ
  map_one' := by ext x q; simp [linWreathEquiv, linWreathLinear]
  map_mul' a b := by
    ext x q
    exact congrFun (congrArg (fun f : (linTwo → V) →ₗ[R] (linTwo → V) => f x)
      (linWreathLinear_mul ρ a b)) q

@[simp] theorem linWreathRep_apply (ρ : H →* (V ≃ₗ[R] V))
    (w : H ≀ᵣ linTwo) (x : linTwo → V) (q : linTwo) :
    linWreathRep ρ w x q = ρ (w.left q) (x (w.right⁻¹ * q)) := rfl

/-- The input pair as a vector on the two copies. -/
def linWreathPair (v w : V) : linTwo → V := fun q => if q = 1 then v else w

@[simp] theorem linWreathPair_one (v w : V) : linWreathPair v w 1 = v := by simp [linWreathPair]
@[simp] theorem linWreathPair_swap (v w : V) : linWreathPair v w linTwoSwap = w := by
  simp [linWreathPair]

/-- A swapping stabilizer element gives a transporter in the original cover. -/
theorem linWreath_extract (ρ : H →* (V ≃ₗ[R] V)) (v w : V) (a : H ≀ᵣ linTwo)
    (hs : a.right = linTwoSwap) (ha : linWreathRep ρ a (linWreathPair v w) = linWreathPair v w) :
    ρ (a.left linTwoSwap) v = w := by
  have hh := congrFun ha linTwoSwap
  simpa [hs] using hh

/-- The swapping part is nonempty exactly when the original vectors are in one orbit. -/
theorem linWreath_transport_iff (ρ : H →* (V ≃ₗ[R] V)) (v w : V) :
    (∃ a : H ≀ᵣ linTwo, a.right = linTwoSwap ∧
      linWreathRep ρ a (linWreathPair v w) = linWreathPair v w) ↔ ∃ g : H, ρ g v = w := by
  constructor
  · rintro ⟨a, hs, ha⟩
    exact ⟨a.left linTwoSwap, linWreath_extract ρ v w a hs ha⟩
  · rintro ⟨g, hg⟩
    let a : H ≀ᵣ linTwo := ⟨fun q => if q = 1 then g⁻¹ else g, linTwoSwap⟩
    refine ⟨a, rfl, ?_⟩
    funext q
    rcases linTwo_cases q with rfl | rfl
    · have hi : ρ g⁻¹ w = v := by
        rw [← hg, map_inv]
        exact (ρ g).symm_apply_apply v
      simpa [a, linWreathPair] using hi
    · simpa [a, linWreathPair] using hg

/-- Testing the returned stabilizer generators suffices to find a swapping
member. No enumeration of the stabilizer is needed. -/
theorem linWreath_swap_generator_iff (xs : List (H ≀ᵣ linTwo)) :
    (∃ a ∈ Subgroup.closure {a | a ∈ xs}, a.right = linTwoSwap) ↔
      ∃ a ∈ xs, a.right = linTwoSwap := by
  classical
  constructor
  · intro h
    by_contra hn
    have hbase : Subgroup.closure {a | a ∈ xs} ≤
        (RegularWreathProduct.rightHom : (H ≀ᵣ linTwo) →* linTwo).ker := by
      apply (Subgroup.closure_le _).mpr
      intro a ha
      change a.right = 1
      rcases linTwo_cases a.right with he | he
      · exact he
      · exact (hn ⟨a, ha, he⟩).elim
    obtain ⟨a, ha, hs⟩ := h
    have hh : a.right = 1 := hbase ha
    exact linTwoSwap_ne_one (hs.symm.trans hh)
  · rintro ⟨a, ha, hs⟩
    exact ⟨a, Subgroup.subset_closure ha, hs⟩

/-- An explicit permutation cover on two copies of the original domain. -/
def linWreathCover {Ω : Type*} [MulAction H Ω] :
    (H ≀ᵣ linTwo) →* Equiv.Perm (Ω × linTwo) :=
  RegularWreathProduct.toPerm H linTwo Ω

/-- Restricting a swapping cover permutation from the first copy to the second
recovers precisely the original-cover transporter used by linWreath_extract. -/
theorem linWreathCover_swap_apply {Ω : Type*} [MulAction H Ω]
    (a : H ≀ᵣ linTwo) (ha : a.right = linTwoSwap) (x : Ω) :
    linWreathCover a (x, 1) = (a.left linTwoSwap • x, linTwoSwap) := by
  change (a.left (a.right * 1) • x, a.right * 1) = _
  simp [ha]

/-- A single domain point detects whether a cover generator swaps the copies. -/
theorem linWreathCover_swap_test {Ω : Type*} [MulAction H Ω] (a : H ≀ᵣ linTwo) (x : Ω) :
    (linWreathCover a (x, 1)).2 = linTwoSwap ↔ a.right = linTwoSwap := by
  change a.right * 1 = linTwoSwap ↔ _
  simp

/-- The cover is faithful whenever the original permutation action is faithful. -/
theorem linWreathCover_injective {Ω : Type*} [Nonempty Ω]
    [MulAction H Ω] [FaithfulSMul H Ω] : Function.Injective (linWreathCover (H := H) (Ω := Ω)) :=
  RegularWreathProduct.toPermInj H linTwo Ω

/-- Its actual permutation image is solvable, so the cited vector task applies
without needing a faithful action of the matrix-image group. -/
theorem linWreathCover_solvable {Ω : Type*} [MulAction H Ω] [Group.IsSolvable H] :
    Group.IsSolvable (linWreathCover (H := H) (Ω := Ω)).range := by
  letI := linWreath_solvable (H := H)
  exact Group.isSolvable_of_surjective (linWreathCover (H := H) (Ω := Ω)).rangeRestrict_surjective

theorem linWreathCover_card (n : ℕ) : Nat.card (Fin n × linTwo) = 2 * n := by
  rw [Nat.card_prod]
  have hc : Nat.card linTwo = 2 := by
    change Nat.card (ZMod 2) = 2
    simp
  simp [hc, Nat.mul_comm]

end GI.Impl
