module

public import Workspace.BudgetInductionBasic

@[expose] public section

namespace GI.BudgetInduction

variable {V : Type*} {H L : Subgroup (Equiv.Perm V)} {a : V}

/-- In a free action, a transitive kernel contains every element: equality
at the basepoint already identifies the two acting permutations. -/
theorem no_step_of_free_at_point
    (free : Function.Injective (fun h : H => (h : Equiv.Perm V) a))
    {k : ℕ} (hk : 5 ≤ k) (s : VisibleStep a H L k) : False := by
  letI : IsSimpleGroup (alternatingGroup (Fin k)) := AlternatingSimple.isSimple_fin hk
  have kills : ∀ h : H, s.quotient h = 1 := by
    intro h
    obtain ⟨l, hl⟩ := s.transitiveKernel h
    have he : Subgroup.inclusion s.lower l = h := free hl
    rw [← he]
    exact (s.kernel _).mpr l.property
  obtain ⟨z, hz⟩ := exists_ne (1 : alternatingGroup (Fin k))
  obtain ⟨h, rfl⟩ := s.onto z
  exact hz (kills h)

theorem free_at_point_subgroup (hle : L ≤ H)
    (free : Function.Injective (fun h : H => (h : Equiv.Perm V) a)) :
    Function.Injective (fun l : L => (l : Equiv.Perm V) a) := by
  intro x y hxy
  have he : Subgroup.inclusion hle x = Subgroup.inclusion hle y := free hxy
  exact Subtype.ext (congrArg (fun z : H => (z : Equiv.Perm V)) he)

/-- The entire hereditary chain has zero weight in a free action. -/
theorem chain_zero_of_free_at_point {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff)
    (chain : MarkedChain cutoff a H w) :
    Function.Injective (fun h : H => (h : Equiv.Perm V) a) → w = 0 := by
  induction chain with
  | stop H => intro _; rfl
  | restrict hle _ ih => intro hf; exact ih (free_at_point_subgroup hle hf)
  | mark hk s _ _ => intro hf; exact (no_step_of_free_at_point hf (hcutoff.trans hk) s).elim

theorem sigma_zero_of_free_at_point [Fintype V] {cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (free : Function.Injective (fun h : H => (h : Equiv.Perm V) a)) :
    sigma cutoff a H = 0 :=
  chain_zero_of_free_at_point hcutoff (sigma_achieved hcutoff a H) free

/-- The actual left regular permutation representation. -/
def regularActionHom (G : Type*) [Group G] : G →* Equiv.Perm G where
  toFun g := Equiv.mulLeft g
  map_one' := Equiv.ext fun _ => one_mul _
  map_mul' g h := Equiv.ext fun x => mul_assoc g h x

theorem regular_image_free (G : Type*) [Group G]
    (K : Subgroup (Equiv.Perm G)) (hK : K ≤ (regularActionHom G).range) (a : G) :
    Function.Injective (fun h : K => (h : Equiv.Perm G) a) := by
  intro x y hxy
  obtain ⟨g, hg⟩ := hK x.property
  obtain ⟨h, hh⟩ := hK y.property
  have he : g * a = h * a := by
    change regularActionHom G g a = regularActionHom G h a
    rw [hg, hh]
    exact hxy
  have hgh : g = h := mul_right_cancel he
  apply Subtype.ext
  rw [← hg, ← hh, hgh]

/-- All actual subgroups of every finite left regular action have zero
budget, including every primitive member of this family. -/
theorem sigma_regular_zero (G : Type*) [Group G] [Fintype G]
    {cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (K : Subgroup (Equiv.Perm G)) (hK : K ≤ (regularActionHom G).range) (a : G) :
    sigma cutoff a K = 0 :=
  sigma_zero_of_free_at_point hcutoff (regular_image_free G K hK a)

end GI.BudgetInduction
