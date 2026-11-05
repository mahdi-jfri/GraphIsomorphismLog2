module

public import Workspace.Cited.CoherentConfig

@[expose] public section

/-!
# The coherent refinement used by the aggregation round

The aggregation round refines tuple colorings to coherent configurations (Section A.3). The
cited result `GI.Cited.KaryCoherentRefinement` only says that a suitable refinement function
exists. The round does not pick one by `Classical.choose`: it takes the function as data
(`RefineFn`), and every property it uses is a clause of the cited statement. The default
(`RefineFn.ofCited`) chooses one. A program meets the model with its own refinement (for
example, `k`-dimensional Weisfeiler--Leman), provided that refinement has these properties.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Cited

/-- **A coherent refinement for every degree `n` and arity `k`**, with the three clauses of
`GI.Cited.KaryCoherentRefinement`: the refined coloring is a coherent configuration, equal refined
colors (across inputs) have equal original colors, and refinement commutes with relabeling. -/
def RefineFn : Type :=
  ∀ n k : ℕ, {F : ((Fin k → Fin n) → ℕ) → ((Fin k → Fin n) → ℕ) //
    (∀ c, IsConfiguration (F c) ∧ IsCoherent (F c)) ∧
    (∀ c c' x y, F c x = F c' y → c x = c' y) ∧
    (∀ c (σ : Perm (Fin n)), F (fun x => c (σ.symm ∘ x)) = fun x => F c (σ.symm ∘ x))}

/-- The default refinement: a classical choice from the cited statement. -/
noncomputable def RefineFn.ofCited (hK : KaryCoherentRefinement) : RefineFn :=
  fun n k => ⟨(hK n k).choose, (hK n k).choose_spec⟩

/-! ### Joint refinement of two colorings

The paper refines the structures of the two inputs together, with one palette (Section A.3:
"Use the same palette for both inputs"). The round therefore takes a function that refines a
*pair* of colorings (`JointFn`). Its clauses (`JointOK`) are those of the cited joint task
(`GI.Cited.JointRefinement` in `Workspace/Cited/AlgoRefinement.lean`). Any `RefineFn`
gives one (`JointFn.ofRefine`), by refining each coloring on its own. -/

/-- `σ` carries the coloring `a` to the coloring `b`: `b(σ ∘ x) = a(x)`. -/
def CarriesTo {n k : ℕ} (σ : Perm (Fin n)) (a b : (Fin k → Fin n) → ℕ) : Prop :=
  ∀ x, b (σ ∘ x) = a x

/-- **The clauses of a joint refinement** `(d, d')` of `(c, c')`: both are coherent
configurations, they refine `c` and `c'` with one palette, and every relabeling that carries
`c` to `c'` (or `c` to itself, or `c'` to itself) carries the refined colorings in the same
way. -/
def JointOK {n k : ℕ} (c c' d d' : (Fin k → Fin n) → ℕ) : Prop :=
  IsConfiguration d ∧ IsCoherent d ∧ IsConfiguration d' ∧ IsCoherent d' ∧
  (∀ x y, d x = d y → c x = c y) ∧ (∀ x y, d' x = d' y → c' x = c' y) ∧
  (∀ x y, d x = d' y → c x = c' y) ∧
  ∀ σ : Perm (Fin n),
    (CarriesTo σ c c' → CarriesTo σ d d') ∧ (CarriesTo σ c c → CarriesTo σ d d) ∧
    (CarriesTo σ c' c' → CarriesTo σ d' d')

/-- **A joint coherent refinement for every degree `n` and arity `k`**: a pair of refined
colorings for each pair of colorings. -/
def JointFn : Type :=
  ∀ n k : ℕ, ∀ c c' : (Fin k → Fin n) → ℕ,
    {p : ((Fin k → Fin n) → ℕ) × ((Fin k → Fin n) → ℕ) // JointOK c c' p.1 p.2}

theorem carriesTo_iff {n k : ℕ} (σ : Perm (Fin n)) (a b : (Fin k → Fin n) → ℕ) :
    CarriesTo σ a b ↔ b = fun x => a (σ.symm ∘ x) := by
  constructor
  · intro h
    funext x
    have := h (σ.symm ∘ x)
    rwa [← Function.comp_assoc, Equiv.self_comp_symm, Function.id_comp] at this
  · rintro rfl x
    simp [← Function.comp_assoc]

/-- A `RefineFn` refines each coloring on its own; the pair of results is a joint refinement,
because the refinement commutes with relabeling. -/
theorem RefineFn.jointOK (F : RefineFn) (n k : ℕ) (c c' : (Fin k → Fin n) → ℕ) :
    JointOK c c' ((F n k).1 c) ((F n k).1 c') := by
  obtain ⟨h1, h2, h3⟩ := (F n k).2
  have hcar : ∀ (σ : Perm (Fin n)) (a b : (Fin k → Fin n) → ℕ), CarriesTo σ a b →
      CarriesTo σ ((F n k).1 a) ((F n k).1 b) := by
    intro σ a b h
    rw [carriesTo_iff] at h ⊢
    rw [h, h3]
  exact ⟨(h1 c).1, (h1 c).2, (h1 c').1, (h1 c').2, fun x y h => h2 c c x y h,
    fun x y h => h2 c' c' x y h, fun x y h => h2 c c' x y h,
    fun σ => ⟨hcar σ c c', hcar σ c c, hcar σ c' c'⟩⟩

/-- The default joint refinement: refine each coloring with a `RefineFn`. -/
def JointFn.ofRefine (F : RefineFn) : JointFn :=
  fun n k c c' => ⟨((F n k).1 c, (F n k).1 c'), F.jointOK n k c c'⟩

/-- **One side of a joint refinement**, as a function of its own coloring: the facts the
round uses about the refined coloring of one input, whatever the other input is. -/
def SideOK {n k : ℕ} (R : ((Fin k → Fin n) → ℕ) → ((Fin k → Fin n) → ℕ)) : Prop :=
  ∀ c, IsConfiguration (R c) ∧ IsCoherent (R c) ∧ (∀ x y, R c x = R c y → c x = c y) ∧
    ∀ σ : Perm (Fin n), CarriesTo σ c c → CarriesTo σ (R c) (R c)

/-- The first side, with the second coloring fixed. -/
def JointFn.left (J : JointFn) (n k : ℕ) (c' : (Fin k → Fin n) → ℕ) :
    ((Fin k → Fin n) → ℕ) → ((Fin k → Fin n) → ℕ) := fun c => (J n k c c').1.1

/-- The second side, with the first coloring fixed. -/
def JointFn.right (J : JointFn) (n k : ℕ) (c : (Fin k → Fin n) → ℕ) :
    ((Fin k → Fin n) → ℕ) → ((Fin k → Fin n) → ℕ) := fun c' => (J n k c c').1.2

theorem JointFn.left_ok (J : JointFn) (n k : ℕ) (c' : (Fin k → Fin n) → ℕ) :
    SideOK (J.left n k c') := fun c => by
  obtain ⟨h1, h2, -, -, h5, -, -, h8⟩ := (J n k c c').2
  exact ⟨h1, h2, h5, fun σ => (h8 σ).2.1⟩

theorem JointFn.right_ok (J : JointFn) (n k : ℕ) (c : (Fin k → Fin n) → ℕ) :
    SideOK (J.right n k c) := fun c' => by
  obtain ⟨-, -, h3, h4, -, h6, -, h8⟩ := (J n k c c').2
  exact ⟨h3, h4, h6, fun σ => (h8 σ).2.2⟩

/-- The relabeling clause across the two sides. -/
theorem JointFn.carries (J : JointFn) (n k : ℕ) {c c' : (Fin k → Fin n) → ℕ} {σ : Perm (Fin n)}
    (h : CarriesTo σ c c') : CarriesTo σ (J.left n k c' c) (J.right n k c c') :=
  ((J n k c c').2.2.2.2.2.2.2.2 σ).1 h

end GI.Algorithm
