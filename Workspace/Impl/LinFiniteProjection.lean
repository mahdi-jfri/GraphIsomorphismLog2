module

public import Workspace.Impl.LinFiniteHomogeneous
public import Workspace.Impl.LinDescendAction

@[expose] public section

/-! Explicit coordinate reduction to cyclic quotient moduli. -/
namespace GI.Impl

noncomputable def linFiniteProjection {d : ℕ} (m q : Fin d → ℕ) (hd : ∀ i, q i ∣ m i) :
    linFiniteVec m →+ linFiniteVec q where
  toFun x i := ZMod.castHom (hd i) (ZMod (q i)) (x i)
  map_zero' := by funext i; exact map_zero (ZMod.castHom (hd i) (ZMod (q i)))
  map_add' x y := by funext i; exact map_add (ZMod.castHom (hd i) (ZMod (q i))) (x i) (y i)

theorem linFiniteProjection_surjective {d : ℕ} (m q : Fin d → ℕ) (hd : ∀ i, q i ∣ m i) :
    Function.Surjective (linFiniteProjection m q hd) := by
  intro y
  classical
  refine ⟨fun i => (ZMod.castHom_surjective (hd i) (y i)).choose, ?_⟩
  funext i
  exact (ZMod.castHom_surjective (hd i) (y i)).choose_spec

theorem linFiniteProjection_basis {d : ℕ} (m q : Fin d → ℕ) (hd : ∀ i, q i ∣ m i) (j : Fin d) :
    linFiniteProjection m q hd (linFiniteBasis m j) = linFiniteBasis q j := by
  classical
  funext i
  by_cases he : i = j
  · subst i
    simp [linFiniteProjection, linFiniteBasis]
    exact ZMod.cast_one (hd j)
  · have hji : j ≠ i := Ne.symm he
    simp [linFiniteProjection, linFiniteBasis, he, hji]

theorem linFiniteProjection_val {d : ℕ} (m q : Fin d → ℕ) (hd : ∀ i, q i ∣ m i)
    (hm : ∀ i, 0 < m i) (x : linFiniteVec m) (i : Fin d) :
    linFiniteProjection m q hd x i = ((x i).val : ZMod (q i)) := by
  letI : NeZero (m i) := ⟨(hm i).ne'⟩
  exact ZMod.cast_eq_val (x i)

theorem linFiniteProjection_kernel {d : ℕ} (m q : Fin d → ℕ) (hd : ∀ i, q i ∣ m i)
    (hm : ∀ i, 0 < m i) (x : linFiniteVec m) :
    linFiniteProjection m q hd x = 0 ↔ ∀ i, q i ∣ (x i).val := by
  constructor
  · intro h i
    have hi := congrFun h i
    rw [linFiniteProjection_val m q hd hm x i] at hi
    exact (ZMod.natCast_eq_zero_iff _ _).mp hi
  · intro h
    funext i
    rw [linFiniteProjection_val m q hd hm x i]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (h i)

theorem linFiniteNsmul_zero_iff {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (t : ℕ) (x : linFiniteVec m) :
    t • x = 0 ↔ ∀ i, m i ∣ t * (x i).val := by
  have he (i : Fin d) : ((t * (x i).val : ℕ) : ZMod (m i)) = t • x i := by
    letI : NeZero (m i) := ⟨(hm i).ne'⟩
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]
  constructor
  · intro h i
    have hi := congrFun h i
    change t • x i = 0 at hi
    exact (ZMod.natCast_eq_zero_iff _ _).mp ((he i).trans hi)
  · intro h
    funext i
    change t • x i = 0
    rw [← he i]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (h i)

end GI.Impl
