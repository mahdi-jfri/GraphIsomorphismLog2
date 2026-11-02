import Workspace.Algorithm.DomainRestriction
import Workspace.Algorithm.HierInv

/-!
# The state of a fresh phase

Algorithm 5, `Solve`: "Use the faithful action and jointly compressed colors on `Ω`. …
Set `N ← |Ω|`, `λ ← N^α`, and `h ← 2`. Initialize each original orbit's hierarchy and
interval bounds. Return `Continue(S)` for the resulting state `S`."

Section 3: "Every fresh call uses the faithful permutation image on its own active domain …
Its caller retains the homomorphism used to lift the returned generators and
representative."

Section 3.3: "We keep a hierarchy of such partitions down to singletons. If its successive
ratios are `d_1, …, d_t`, then `d_1 ⋯ d_t = s`. … The initial bound `c_i = d_i` is always
available."

This file defines

* `TowerFrom` and `InitialTower`: a hierarchy of invariant partitions of one orbit `O`, from
  the singletons up to the whole orbit, whose ratios are the numbers of finer classes in a
  coarser class, with initial bounds `c_i = d_i`. Section 6.1 initializes "the hierarchy and
  interval bounds on each original orbit" and processes "a largest original orbit first";
  the state stores one hierarchy, the one of a largest orbit (`InitialTower`). Its ratios
  multiply to the size of that orbit (`TowerFrom.prod_ratio`).
* `State.FreshOf S S'`: `S'` is the state of the fresh phase started on `S`. It lives on the
  type `S.dom` of the active domain, with the faithful image `G|_dom` (`State.domGroup`), the
  restricted colorings, `N = |dom|`, `h = 2`, no row record, and an initial tower.
* `State.liftAnswer`: the answer of `S'` lifted back to `Ω` through the restriction map, and
  `State.liftAnswer_answer`: the lift of the exact answer of `S'` is the exact answer of `S`
  (`answer_restrict_image`).
* `State.freshOn`: the fresh state with a given hierarchy, and `exists_initialTower`: an
  initial tower always exists (a single interval from the largest orbit to its points).
* `exists_orbitHier`: the hierarchy of every original orbit at once (one interval from the
  points to the orbits, `orbitHier`) is an initial tower and satisfies the hierarchy invariant
  `HierInv` (`Workspace/Algorithm/HierInv.lean`). This is the hierarchy that the recursion
  stores at a fresh phase (`State.FreshOf.orbits`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

variable {Ω C : Type}

/-! ### The initial tower -/

/-- The number of points of `O` in the class of `a` of the partition `p`. -/
noncomputable def blockCard (O : Set Ω) (a : Ω) (p : Setoid Ω) : ℕ :=
  Nat.card {w // w ∈ O ∧ p.r a w}

/-- `TowerFrom G O a fine l`: reading the list `l` from its finest interval, each interval
`I` goes from the partition `fine` (its fine end) to `I.part` (its coarse end). The coarse
end is `G`-invariant and coarser than the fine end, and the ratio of `I` is the number of
fine classes in one coarse class, counted at the base point `a` inside the orbit `O`. The
last coarse end contains all of `O` in one class. (The list is ordered from the finest
interval to the coarsest, as in `ColumnStep.hier_eq`.) -/
def TowerFrom (G : Subgroup (Perm Ω)) (O : Set Ω) (a : Ω) : Setoid Ω → List (Interval Ω) → Prop
  | fine, [] => ∀ w ∈ O, fine.r a w
  | fine, I :: l => (∀ g ∈ G, ∀ v w, I.part.r (g v) (g w) ↔ I.part.r v w) ∧ fine ≤ I.part ∧
      I.ratio * blockCard O a fine = blockCard O a I.part ∧ TowerFrom G O a I.part l

/-- **The initial tower of a fresh phase** (Section 3.3 and Algorithm 5: "Initialize each
original orbit's hierarchy and interval bounds"): a hierarchy of `G`-invariant partitions of a
largest orbit `O = a^G` of `G` in `D`, from the singletons (`⊥`) up to `O`, with the initial
bounds `c_i = d_i`. -/
def InitialTower (G : Subgroup (Perm Ω)) (D : Set Ω) (l : List (Interval Ω)) : Prop :=
  (∃ a ∈ D, (∀ b ∈ D, Nat.card (orb G b) ≤ Nat.card (orb G a)) ∧ TowerFrom G (orb G a) a ⊥ l) ∧
    ∀ I ∈ l, I.cap = I.ratio

theorem blockCard_of_forall {O : Set Ω} {a : Ω} {p : Setoid Ω} (h : ∀ w ∈ O, p.r a w) :
    blockCard O a p = Nat.card O :=
  Nat.card_congr ⟨fun w => ⟨w.1, w.2.1⟩, fun w => ⟨w.1, w.2, h w.1 w.2⟩, fun _ => rfl,
    fun _ => rfl⟩

theorem blockCard_bot {O : Set Ω} {a : Ω} (ha : a ∈ O) : blockCard O a ⊥ = 1 := by
  unfold blockCard
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun w₁ w₂ => ?_⟩, ⟨⟨a, ha, (⊥ : Setoid Ω).refl a⟩⟩⟩
  have h1 : a = w₁.1 := by simpa using w₁.2.2
  have h2 : a = w₂.1 := by simpa using w₂.2.2
  exact Subtype.ext (h1.symm.trans h2)

/-- **The ratios of a tower multiply to the size of the orbit** (Section 3.3:
"`d_1 ⋯ d_t = s`"), relative to the fine end. -/
theorem TowerFrom.prod_ratio {G : Subgroup (Perm Ω)} {O : Set Ω} {a : Ω} :
    ∀ {fine : Setoid Ω} {l : List (Interval Ω)}, TowerFrom G O a fine l →
      (l.map Interval.ratio).prod * blockCard O a fine = Nat.card O
  | _, [], h => by simpa using blockCard_of_forall h
  | _, I :: l, h => by
    obtain ⟨-, -, hI, hl⟩ := h
    have := TowerFrom.prod_ratio hl
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, mul_left_comm, hI]
    exact this

namespace InitialTower

variable {G : Subgroup (Perm Ω)} {D : Set Ω} {l : List (Interval Ω)}

/-- The ratios of the initial tower multiply to the size of its orbit. -/
theorem prod_ratio (h : InitialTower G D l) :
    ∃ a ∈ D, (l.map Interval.ratio).prod = Nat.card (orb G a) := by
  obtain ⟨⟨a, haD, -, ht⟩, -⟩ := h
  refine ⟨a, haD, ?_⟩
  have := ht.prod_ratio
  have ha : a ∈ orb G a := ⟨1, G.one_mem, rfl⟩
  rwa [blockCard_bot ha, mul_one] at this

/-- The ratios of the initial tower multiply to at most the size of the domain. -/
theorem prod_ratio_le [Finite Ω] (h : InitialTower G D l) (hD : Invariant G D) :
    (l.map Interval.ratio).prod ≤ Nat.card D := by
  obtain ⟨a, haD, he⟩ := h.prod_ratio
  rw [he, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨g, hg, rfl⟩
  exact (hD g hg a).2 haD

/-- Every ratio of the initial tower is at least one: the ratios multiply to the size of a
nonempty orbit. -/
theorem one_le_ratio [Finite Ω] (h : InitialTower G D l) : ∀ I ∈ l, 1 ≤ I.ratio := by
  obtain ⟨a, -, he⟩ := h.prod_ratio
  have hpos : 0 < Nat.card (orb G a) := by
    haveI : Finite (orb G a) := Subtype.finite
    exact Nat.card_pos_iff.2 ⟨⟨⟨a, 1, G.one_mem, rfl⟩⟩, inferInstance⟩
  intro I hI
  have hne : (l.map Interval.ratio).prod ≠ 0 := by omega
  rw [Ne, List.prod_eq_zero_iff] at hne
  have : I.ratio ≠ 0 := fun h0 => hne (h0 ▸ List.mem_map_of_mem hI)
  omega

end InitialTower

/-- The one-interval tower: the whole orbit `O` of `a`, split into its points. -/
def orbitPart (O : Set Ω) : Setoid Ω where
  r v w := (v ∈ O ∧ w ∈ O) ∨ (v ∉ O ∧ w ∉ O)
  iseqv := ⟨fun v => by by_cases hv : v ∈ O <;> simp [hv],
    fun h => by rcases h with ⟨a, b⟩ | ⟨a, b⟩; exacts [Or.inl ⟨b, a⟩, Or.inr ⟨b, a⟩],
    fun h1 h2 => by
      rcases h1 with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases h2 with ⟨a', b'⟩ | ⟨a', b'⟩
      · exact Or.inl ⟨a, b'⟩
      · exact absurd b a'
      · exact absurd a' b
      · exact Or.inr ⟨a, b'⟩⟩

/-- **An initial tower always exists** on a nonempty finite domain: one interval from a largest
orbit to its points, with ratio and bound the size of the orbit (Section 3.3: "The initial
bound `c_i = d_i` is always available"). -/
theorem exists_initialTower [Finite Ω] (G : Subgroup (Perm Ω)) {D : Set Ω}
    (hne : D.Nonempty) : ∃ l : List (Interval Ω), InitialTower G D l := by
  classical
  obtain ⟨a, haD, hmax⟩ := Set.exists_max_image D (fun v => Nat.card (orb G v)) (Set.toFinite _)
    hne
  set O := orb G a
  have haO : a ∈ O := ⟨1, G.one_mem, rfl⟩
  have hOinv : ∀ g ∈ G, ∀ v, g v ∈ O ↔ v ∈ O := by
    intro g hg v
    constructor
    · rintro ⟨k, hk, hkv⟩
      exact ⟨g⁻¹ * k, G.mul_mem (G.inv_mem hg) hk, by rw [Perm.mul_apply, hkv, Perm.inv_apply_self]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨g * k, G.mul_mem hg hk, rfl⟩
  refine ⟨[⟨orbitPart O, Nat.card O, Nat.card O, 0⟩], ⟨a, haD, fun b hb => hmax b hb, ?_⟩, ?_⟩
  · refine ⟨fun g hg v w => ?_, fun v w h => ?_, ?_, fun w hw => Or.inl ⟨haO, hw⟩⟩
    · change ((g v ∈ O ∧ g w ∈ O) ∨ (g v ∉ O ∧ g w ∉ O)) ↔ ((v ∈ O ∧ w ∈ O) ∨ (v ∉ O ∧ w ∉ O))
      rw [hOinv g hg v, hOinv g hg w]
    · have : v = w := by simpa using h
      subst this
      exact (orbitPart O).refl v
    · rw [blockCard_bot haO, mul_one,
        blockCard_of_forall (p := orbitPart O) fun w hw => Or.inl ⟨haO, hw⟩]
  · intro I hI
    rw [List.mem_singleton] at hI
    subst hI
    rfl

/-- **The hierarchy of all original orbits** is an initial tower and satisfies the hierarchy
invariant, on a nonempty finite domain: one interval from the points to the orbits of `G`, with
ratio and bound the size `M` of a largest orbit (Algorithm 5, `Solve`: "Initialize each
original orbit's hierarchy and interval bounds"). -/
theorem exists_orbitHier [Finite Ω] (G : Subgroup (Perm Ω)) {D : Set Ω} (hD : Invariant G D)
    (hne : D.Nonempty) :
    ∃ M, InitialTower G D (orbitHier G M) ∧ HierInv G D (orbitHier G M) := by
  classical
  obtain ⟨a, haD, hmax⟩ := Set.exists_max_image D (fun v => Nat.card (orb G v)) (Set.toFinite _)
    hne
  have haO : a ∈ orb G a := ⟨1, G.one_mem, rfl⟩
  refine ⟨Nat.card (orb G a), ⟨⟨a, haD, fun b hb => hmax b hb, ?_⟩, ?_⟩,
    orbitHier_hierInv G hD fun b hb => hmax b hb⟩
  · refine ⟨fun g hg v w => orbitSetoid_inv G g hg v w, fun v w h => ?_, ?_, fun w hw => hw⟩
    · have : v = w := h
      subst this
      exact (orbitSetoid G).refl v
    · change Nat.card (orb G a) * blockCard (orb G a) a ⊥ = blockCard (orb G a) a (orbitSetoid G)
      rw [blockCard_bot haO, mul_one, blockCard_of_forall (p := orbitSetoid G) fun w hw => hw]
  · intro I hI
    rw [orbitHier, List.mem_singleton] at hI
    subst hI
    rfl

/-! ### The fresh state -/

namespace State

/-- The whole type is invariant under every group. -/
theorem invariant_univ (G : Subgroup (Perm Ω)) : Invariant G Set.univ := fun _ _ _ => by simp

/-- **The state of a fresh phase** started on `S` (Algorithm 5, `Solve`; Section 3: "Every
fresh call uses the faithful permutation image on its own active domain"; Section 6.1: "At a
fresh intransitive instance, initialize the hierarchy and interval bounds on each original
orbit"). The new state `S'` lives on the active domain `S.dom` of `S`:

* its group is the faithful image `G|_dom` and its domain is all of `S.dom`;
* its colorings are those of `S`, restricted to the domain (the joint color compression is
  a change of representation, `answer_recolor`, left to stage 2);
* its phase size is `N = |dom|`, its counter `h = 2`, it has no row record and is not in
  floor mode;
* its hierarchy is an initial tower with `c_i = d_i` (`InitialTower`). -/
structure FreshOf (S : State Ω C) (S' : State S.dom C) : Prop where
  G_eq : S'.G = S.domGroup
  dom_eq : S'.dom = Set.univ
  x_eq : S'.x = S.x ∘ Subtype.val
  y_eq : S'.y = S.y ∘ Subtype.val
  N_eq : S'.N = S.size
  h_eq : S'.h = 2
  rows_eq : S'.rows = none
  floor_eq : S'.floor = false
  tower : InitialTower S'.G S'.dom S'.hier
  /-- Section 6.1: "At a fresh intransitive instance, initialize the hierarchy and interval
  bounds on each original orbit": the stored hierarchy is a tower of every original orbit, with
  stored ratios that bound its true ratios (`HierInv`). -/
  orbits : GI.Algorithm.HierInv S'.G S'.dom S'.hier

/-- **The fresh state satisfies the hierarchy invariant.** -/
theorem FreshOf.hierInv {S : State Ω C} {S' : State S.dom C} (h : S.FreshOf S') : S'.HierInv :=
  h.orbits

/-- The answer of the fresh state, lifted to `Ω` (Section 3: "Its caller retains the
homomorphism used to lift the returned generators and representative"): the elements of `G`
whose restriction to the domain lies in `A`. -/
def liftAnswer (S : State Ω C) (A : Set (Perm S.dom)) : Set (Perm Ω) :=
  {g | ∃ hg : g ∈ S.G, S.domHom ⟨g, hg⟩ ∈ A}

/-- **The lift of the exact answer of the fresh state is the exact answer of `S`**
(`answer_restrict_image`). -/
theorem FreshOf.liftAnswer_answer {S : State Ω C} {S' : State S.dom C} (h : S.FreshOf S') :
    S.liftAnswer S'.answer = S.answer := by
  unfold liftAnswer State.answer
  rw [h.G_eq, h.dom_eq, h.x_eq, h.y_eq, answer_restrict_image S.G S.dom S.dom_inv S.x S.y]
  rfl

/-- The fresh state has `s = |dom|` positions. -/
theorem FreshOf.size_eq {S : State Ω C} {S' : State S.dom C} (h : S.FreshOf S') :
    S'.size = S.size := by
  unfold State.size
  rw [h.dom_eq]
  exact Nat.card_congr (Equiv.Set.univ _)

/-- The fresh state with the hierarchy `hier`. -/
noncomputable def freshOn (S : State Ω C) (hier : List (Interval S.dom)) : State S.dom C :=
  ⟨S.domGroup, Set.univ, invariant_univ _, S.x ∘ Subtype.val, S.y ∘ Subtype.val, hier, none,
    false, 2, le_rfl, S.size, CounterInv.reset _ _ _ _,
    CarrierOK.none _ _ _⟩

theorem freshOn_freshOf (S : State Ω C) {hier : List (Interval S.dom)}
    (h : InitialTower S.domGroup Set.univ hier)
    (h' : GI.Algorithm.HierInv S.domGroup Set.univ hier) :
    S.FreshOf (S.freshOn hier) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h, h'⟩

end State

end GI.Algorithm
