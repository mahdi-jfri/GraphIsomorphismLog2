import Workspace.Algorithm.Exact
import Workspace.Paper.RunningTime
import Workspace.TowerRank
import Workspace.FiniteBudget
import Workspace.OrbitBudget
import Workspace.AlternatingSections

/-!
# The recursive state (Section 6.1)

"The state contains the active action, the two colorings, the retained partition
hierarchy with its interval bounds, and, when present, the independent row action
and its invariant column partition. Origin labels on intervals record which old
interval is refined by a new one. A counter `h ∈ {0,1,2}` records the remaining
row-construction events before a charged reset." (Section 6.1)

A state lives on a type `Ω` of positions. Its *active domain* `dom ⊆ Ω` is where
the colors are compared, and its group `G ≤ Sym(Ω)` leaves `dom` invariant. An
inherited call on an orbit `Δ` keeps the type `Ω` and sets `dom = Δ`; its answer is
kept in lifted form (see `Workspace/Algorithm/Exact.lean`).

The hierarchy is a list of intervals (Section 3.3), each with its partition at the
coarse end, its ratio `d_i`, its alternating-width bound `c_i`, and an origin
label. The phase size `N` of Section 6 is part of the state, since "the values of
`N` and `λ` remain fixed throughout the phase".

The resources of the potential (Section 7.1) are read off the state:
`s = |dom|`, `ρ = Σ (2⌊log₂ d_i⌋ - 1)` (eq. `main-rho`),
`Q = Σ (log d_i) log max{c_i, 2}` (eq. `main-Q`), `σ` the hereditary budget of
Definition A.2 at a point of the domain, and the counter `h`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

/-- One interval of the partition hierarchy (Section 3.3). -/
structure Interval (Ω : Type) where
  /-- The invariant partition at the coarse end of the interval. -/
  part : Setoid Ω
  /-- The interval ratio `d_i`. -/
  ratio : ℕ
  /-- The interval bound `c_i` on the alternating width of the constituent. -/
  cap : ℕ
  /-- The origin label: which old interval this one refines. -/
  origin : ℕ

/-- The retained row record (Sections 5.3 and 6.3): the degree `m` of the
independent row action, the row partition (the kernel orbits of the natural
action), and the invariant column partition once it has been retained. -/
structure RowRecord (Ω : Type) where
  m : ℕ
  rows : Setoid Ω
  cols : Option (Setoid Ω)

/-- The retained rows `R` are a carrier of `G` on `D`: the row partition is invariant, and it
has exactly `R.m` classes on `D` (Section 6, "Why a row action is enlarged at most once": the
old row factor of degree `m` is an actual interval of the current action). -/
structure RowCarrier {Ω : Type} (G : Subgroup (Perm Ω)) (D : Set Ω) (R : RowRecord Ω) : Prop where
  inv : ∀ g ∈ G, ∀ v w, R.rows.r (g v) (g w) ↔ R.rows.r v w
  count : ∃ f : D → Fin R.m, Function.Surjective f ∧ ∀ v w : D, R.rows.r v w ↔ f v = f w

/-- **The counter invariant** (Section 6.1, "A counter `h ∈ {0,1,2}` records the remaining
row-construction events before a charged reset"; Section 6, "Why a row action is enlarged at
most once"; Section 7.1, "The one-promotion argument ensures that it never becomes negative").

* `h = 1`: one row event has happened since the last reset. Its rows are retained as a
  carrier of degree `m` with `m ≥ 4` and `N < m³` (from `m > λ = N^α` with `α > 1/3`,
  eq. `scale-constraints`).
* `h = 0`: the row action was enlarged once. Its rows have degree `m ≥ 4` and the faithful
  image of the group on the domain has alternating width at most `m` (Lemma A.29,
  `GI.Paper.lem_one_carrier_promotion`: "after constructing independent rows of degree `q`,
  every later large quotient in a subgroup or quotient of this action has degree at most
  `q`").

With `h = 2` nothing is required, so a reset (`rows = none`, `h = 2`) always satisfies it. -/
def CounterInv {Ω : Type} (G : Subgroup (Perm Ω)) (D : Set Ω) (hD : Invariant G D)
    (rows : Option (RowRecord Ω)) (h N : ℕ) : Prop :=
  (h = 1 → ∃ R, rows = some R ∧ RowCarrier G D R ∧ N < R.m ^ 3 ∧ 4 ≤ R.m) ∧
  (h = 0 → ∃ R, rows = some R ∧ 4 ≤ R.m ∧
    GI.SectionCaps.Cap (restrictHom G D hD).range R.m)

theorem CounterInv.reset {Ω : Type} (G : Subgroup (Perm Ω)) (D : Set Ω) (hD : Invariant G D) (N : ℕ) :
    CounterInv G D hD none 2 N := ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

/-- The counter invariant passes to a subgroup on the same domain: the rows stay invariant
with the same classes, and alternating width does not increase in a subgroup (Lemma A.29,
"Hereditary alternating-section width cannot increase in subgroups"). -/
theorem CounterInv.mono {Ω : Type} {G G' : Subgroup (Perm Ω)} {D : Set Ω} {hD : Invariant G D}
    {rows : Option (RowRecord Ω)} {h N : ℕ} (hinv : CounterInv G D hD rows h N) (hG : G' ≤ G) :
    CounterInv G' D (hD.mono hG) rows h N := by
  refine ⟨fun h1 => ?_, fun h0 => ?_⟩
  · obtain ⟨R, hR, hc, hN, hm⟩ := hinv.1 h1
    exact ⟨R, hR, ⟨fun g hg => hc.inv g (hG hg), hc.count⟩, hN, hm⟩
  · obtain ⟨R, hR, hm, hcap⟩ := hinv.2 h0
    refine ⟨R, hR, hm, ?_⟩
    have hle : (restrictHom G' D (hD.mono hG)).range ≤ (restrictHom G D hD).range := by
      rintro _ ⟨g, rfl⟩
      exact ⟨⟨g.1, hG g.2⟩, rfl⟩
    exact GI.SectionCaps.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
      hcap

/-! ### The carrier of the retained rows -/

section Carrier

variable {Ω : Type}

/-- `g` keeps every class of `c` that meets `D`. -/
def FixesCols (c : Setoid Ω) (D : Set Ω) (g : Perm Ω) : Prop := ∀ v ∈ D, c.r (g v) v

/-- **The retained row action is a carrier** (Section 5.3; Section 6, "Why a row action is
enlarged at most once": "write the carrier quotient as `G/M = Alt(m) × Q`"; Section A.4,
"Inheritance of the retained row action": "In a clean row normal form, put `J = M Alt(m)`. Then
`G/J ≅ Q`, and the `J`-orbits are the columns `[m] × C`").

On the domain `D`, the row map `row : D → [m]` reads the rows, `G` acts on them through
`ρ : G → Alt(m)`, and the column partition `cols` is invariant with at least two classes. The
subgroup `J` of the elements that fix every column carries every even row permutation
(`indep`), and the elements of `J` with trivial row image (the group `M`) are transitive on
every cell (row ∩ column). -/
structure CarrierSpec (G : Subgroup (Perm Ω)) (D : Set Ω) (m : ℕ) (rows cols : Setoid Ω)
    (row : Ω → Fin m) (ρ : G →* alternatingGroup (Fin m)) : Prop where
  three_le : 3 ≤ m
  row_iff : ∀ v ∈ D, ∀ w ∈ D, rows.r v w ↔ row v = row w
  row_onto : ∀ i, ∃ v ∈ D, row v = i
  row_equivariant : ∀ (g : G), ∀ v ∈ D, row ((g : Perm Ω) v) = (ρ g : Perm (Fin m)) (row v)
  cols_inv : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, cols.r (g v) (g w) ↔ cols.r v w
  two_cols : ∃ v ∈ D, ∃ w ∈ D, ¬ cols.r v w
  /-- "The clean carrier supplies every element of `Alt(m)`" inside `J`. -/
  indep : ∀ a, ∃ g : G, ρ g = a ∧ FixesCols cols D g
  /-- "`M` is transitive on the `u` points of each cell." -/
  cells : ∀ v ∈ D, ∀ w ∈ D, row v = row w → cols.r v w →
    ∃ g : G, ρ g = 1 ∧ FixesCols cols D g ∧ (g : Perm Ω) v = w

/-- The coarse end of the last interval of `pre`, starting from the points. -/
def hierLevel (pre : List (Interval Ω)) : Setoid Ω := pre.foldl (fun _ I => I.part) ⊥

/-- The column partition is a level of the hierarchy on `D` (Section 6, "The old row factor and
the new column factor are distinct actual intervals of the same hierarchy"; Algorithm 5:
"Expose the next primitive quotient above any retained column partition"). -/
def ColsLevel (D : Set Ω) (hier : List (Interval Ω)) (c : Setoid Ω) : Prop :=
  ∃ pre post, hier = pre ++ post ∧ ∀ v ∈ D, ∀ w ∈ D, ((hierLevel pre).r v w ↔ c.r v w)

/-- **The carrier invariant** of the retained row record: a retained record has a column
partition, its rows are a carrier (`CarrierSpec`), and its columns are a level of the hierarchy.
A state without a row record satisfies it. -/
def CarrierOK (G : Subgroup (Perm Ω)) (D : Set Ω) (rows : Option (RowRecord Ω))
    (hier : List (Interval Ω)) : Prop :=
  ∀ R, rows = some R → ∃ c, R.cols = some c ∧
    (∃ row ρ, CarrierSpec G D R.m R.rows c row ρ) ∧ ColsLevel D hier c

theorem CarrierOK.none (G : Subgroup (Perm Ω)) (D : Set Ω) (hier : List (Interval Ω)) :
    CarrierOK G D none hier := fun _ h => absurd h (by simp)

end Carrier

/-- **The recursive state** of Section 6.1. -/
structure State (Ω C : Type) where
  /-- The allowed relabelings. -/
  G : Subgroup (Perm Ω)
  /-- The active domain. -/
  dom : Set Ω
  dom_inv : Invariant G dom
  /-- The two colorings. -/
  x : Ω → C
  y : Ω → C
  /-- The retained partition hierarchy with interval bounds and origin labels. -/
  hier : List (Interval Ω)
  /-- The independent row action and its column partition, when present. -/
  rows : Option (RowRecord Ω)
  /-- The fixed-floor dispatcher mode. -/
  floor : Bool
  /-- The row counter `h ∈ {0, 1, 2}`. -/
  h : ℕ
  /-- "A counter `h ∈ {0,1,2}`" (Section 6.1). -/
  h_le : h ≤ 2
  /-- The phase size `N`. -/
  N : ℕ
  /-- The counter invariant (`CounterInv`). -/
  counter : CounterInv G dom dom_inv rows h N
  /-- The carrier invariant of the retained rows (`CarrierOK`). -/
  carrier : CarrierOK G dom rows hier

namespace State

variable {Ω C : Type}

/-- The exact answer of the state. -/
def answer (S : State Ω C) : Set (Perm Ω) := GI.Algorithm.answer S.G S.dom S.x S.y

/-- The size `s = |dom|` of the active domain. -/
noncomputable def size (S : State Ω C) : ℕ := Nat.card S.dom

/-- The state is transitive: `G` is transitive on the active domain. -/
def Transitive (S : State Ω C) : Prop :=
  ∀ v ∈ S.dom, ∀ w ∈ S.dom, ∃ g ∈ S.G, g v = w

/-- The core of a state, the data that determine its answer, is `(G, dom, x, y)`. -/
def Inst {C' : Type} (S : State Ω C') (G : Subgroup (Perm Ω)) (D : Set Ω) (x y : Ω → C') :
    Prop :=
  S.G = G ∧ S.dom = D ∧ S.x = x ∧ S.y = y

theorem answer_of_inst {S : State Ω C} {G : Subgroup (Perm Ω)} {D : Set Ω} {x y : Ω → C}
    (h : S.Inst G D x y) : S.answer = GI.Algorithm.answer G D x y := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [answer, h1, h2, h3, h4]

/-- Two states with the same core. -/
def SameCore (S T : State Ω C) : Prop := T.Inst S.G S.dom S.x S.y

theorem answer_of_sameCore {S T : State Ω C} (h : SameCore S T) : T.answer = S.answer :=
  answer_of_inst h

/-- `D₁` is a largest orbit of `G` in the active domain (Section 3.2: "We process a
largest orbit of the group at the start of a chain first"). -/
structure LargestOrbit (S : State Ω C) (D₁ : Set Ω) : Prop where
  subset : D₁ ⊆ S.dom
  /-- `D₁` is the orbit of one of its points. -/
  orbit : ∃ a ∈ S.dom, D₁ = {w | ∃ g ∈ S.G, g a = w}
  /-- No orbit in the domain is larger. -/
  largest : ∀ b ∈ S.dom, Nat.card {w | ∃ g ∈ S.G, g b = w} ≤ Nat.card D₁

theorem LargestOrbit.invariant {S : State Ω C} {D₁ : Set Ω} (h : S.LargestOrbit D₁) :
    Invariant S.G D₁ := by
  obtain ⟨a, -, rfl⟩ := h.orbit
  intro g hg v
  constructor
  · rintro ⟨k, hk, hkv⟩
    exact ⟨g⁻¹ * k, S.G.mul_mem (S.G.inv_mem hg) hk, by
      rw [Perm.mul_apply, hkv, Perm.inv_apply_self]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨g * k, S.G.mul_mem hg hk, rfl⟩

/-- The fixed-floor mode is active and the active domain has entered one proper
column of the retained column partition (Algorithm 5: "if the active column floor
has been entered"). -/
def FloorEntered (S : State Ω C) : Prop :=
  S.floor = true ∧ ∃ R : RowRecord Ω, S.rows = some R ∧ ∃ cols : Setoid Ω, R.cols = some cols ∧
    ∃ v ∈ S.dom, ∀ w ∈ S.dom, cols.r v w

/-- Fresh initialization of the interval bounds (Section 3.3: "The initial bound
`c_i = d_i` is always available"; Algorithm 5, `Solve`: "Initialize each original
orbit's hierarchy and interval bounds"). -/
def InitialBounds (S : State Ω C) : Prop := ∀ I ∈ S.hier, I.cap = I.ratio

/-- The stored bounds are clamped by their ratios (Section 3.3: "every stored bound
is at most its current interval ratio"). -/
def Clamped (S : State Ω C) : Prop := ∀ I ∈ S.hier, I.cap ≤ I.ratio

/-! ### The resources of the potential (Section 7.1) -/

/-- `ρ = Σ_i (2⌊log₂ d_i⌋ - 1)` of a hierarchy, over its ratios (eq. `main-rho`; a
trivial ratio contributes `0`). -/
noncomputable def hierRho (l : List (Interval Ω)) : ℝ :=
  (l.map fun I => ((GI.towerRank I.ratio : ℤ) : ℝ)).sum

/-- `Q = Σ_i (log d_i) log max{c_i, 2}` of a hierarchy (eq. `main-Q`). -/
noncomputable def hierQ (l : List (Interval Ω)) : ℝ :=
  (l.map fun I => Real.log I.ratio * Real.log (max I.cap 2 : ℕ)).sum

/-- `ρ = Σ (2⌊log₂ d_i⌋ - 1)` over the nontrivial ratios (eq. `main-rho`). -/
noncomputable def rho (S : State Ω C) : ℝ := hierRho S.hier

/-- `Q = Σ_i (log d_i) log max{c_i, 2}` (eq. `main-Q`). -/
noncomputable def capMoment (S : State Ω C) : ℝ := hierQ S.hier

/-- The largest value of `σ(G, v)` (Definition A.2, cutoff `κ`) over the points `v`
of a set `D`. -/
noncomputable def supSigma (κ : ℕ) (G : Subgroup (Perm Ω)) (D : Set Ω) : ℕ :=
  sSup ((fun v => GI.sigma κ v G) '' D)

/-- The symmetry measure `σ` of Definition A.2, with cutoff `κ`: the largest value of
`σ(G, v)` over the points `v` of the active domain. For a transitive state every point
gives the same value (`State.sigma_eq_point`). Section 7.1: "we do not evaluate `σ` on
an intransitive action"; there the original transitive orbit's value is a credit, and
the largest point value is at most that credit (Lemma A.3), so it serves as the
credit. It does not increase under a subgroup together with a smaller domain
(`State.sigma_le_of`). -/
noncomputable def sigma (κ : ℕ) (S : State Ω C) : ℕ := supSigma κ S.G S.dom

/-- The resources `s, ρ, σ, Q, h` that the potential of Section 7.1 reads from a
state. -/
noncomputable def res (κ : ℕ) (S : State Ω C) : GI.Paper.PotentialState where
  s := S.size
  ρ := S.rho
  σ := S.sigma κ
  Q := S.capMoment
  h := S.h

theorem hierRho_nonneg (l : List (Interval Ω)) : 0 ≤ hierRho l := by
  unfold hierRho
  apply List.sum_nonneg
  intro r hr
  obtain ⟨I, -, rfl⟩ := List.mem_map.1 hr
  exact_mod_cast GI.tower_rank_nonneg I.ratio

theorem hierQ_nonneg (l : List (Interval Ω)) : 0 ≤ hierQ l := by
  unfold hierQ
  apply List.sum_nonneg
  intro r hr
  obtain ⟨I, -, rfl⟩ := List.mem_map.1 hr
  apply mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

theorem rho_nonneg (S : State Ω C) : 0 ≤ S.rho := hierRho_nonneg _

theorem capMoment_nonneg (S : State Ω C) : 0 ≤ S.capMoment := hierQ_nonneg _

/-- `ρ, σ, Q ≥ 0`: the field `nonneg` of `GI.Paper.PhaseTree.Hyp` holds for the
resources of every state. -/
theorem res_nonneg (κ : ℕ) (S : State Ω C) :
    0 ≤ (S.res κ).ρ ∧ 0 ≤ (S.res κ).σ ∧ 0 ≤ (S.res κ).Q :=
  ⟨S.rho_nonneg, Nat.cast_nonneg _, S.capMoment_nonneg⟩

/-! ### The symmetry measure of a state -/

theorem supSigma_point_le [Finite Ω] (κ : ℕ) (G : Subgroup (Perm Ω)) {D : Set Ω} {v : Ω}
    (hv : v ∈ D) : GI.sigma κ v G ≤ supSigma κ G D :=
  le_csSup (Set.toFinite _).bddAbove ⟨v, hv, rfl⟩

theorem supSigma_le {κ : ℕ} {G : Subgroup (Perm Ω)} {D : Set Ω} {b : ℕ}
    (h : ∀ v ∈ D, GI.sigma κ v G ≤ b) : supSigma κ G D ≤ b := by
  unfold supSigma
  rcases (((fun v => GI.sigma κ v G) '' D)).eq_empty_or_nonempty with he | hne
  · rw [he, csSup_empty]; exact Nat.zero_le _
  · exact csSup_le hne (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)

theorem sigma_point_le [Finite Ω] (κ : ℕ) (S : State Ω C) {v : Ω} (hv : v ∈ S.dom) :
    GI.sigma κ v S.G ≤ S.sigma κ :=
  supSigma_point_le κ S.G hv

theorem sigma_le_of_forall {κ : ℕ} {S : State Ω C} {b : ℕ}
    (h : ∀ v ∈ S.dom, GI.sigma κ v S.G ≤ b) : S.sigma κ ≤ b :=
  supSigma_le h

/-- `σ` does not increase when the group shrinks and the domain shrinks (Lemma A.3,
inheritance: `σ(L, β) ≤ σ(H, β)` for `L ≤ H`). -/
theorem sigma_le_of {C' : Type} [Finite Ω] {κ : ℕ} (hκ : 5 ≤ κ) {S : State Ω C}
    {T : State Ω C'} (hG : T.G ≤ S.G) (hD : T.dom ⊆ S.dom) : T.sigma κ ≤ S.sigma κ := by
  haveI : Fintype Ω := Fintype.ofFinite Ω
  exact sigma_le_of_forall fun v hv =>
    (GI.sigma_subgroup_mono hκ v hG).trans (S.sigma_point_le κ (hD hv))

/-- For a transitive state, `σ` is its value at any point of the active domain. -/
theorem sigma_eq_point [Finite Ω] (κ : ℕ) {S : State Ω C} (htr : S.Transitive) {v : Ω}
    (hv : v ∈ S.dom) : S.sigma κ = GI.sigma κ v S.G := by
  classical
  haveI : Fintype Ω := Fintype.ofFinite Ω
  refine le_antisymm (sigma_le_of_forall fun w hw => ?_) (S.sigma_point_le κ hv)
  obtain ⟨g, hg, hgw⟩ := htr w hw v hv
  exact (GI.sigma_basepoint κ S.G ⟨⟨g, hg⟩, hgw⟩).le

/-! ### Building child states -/

open Classical in
/-- An inherited child: the same hierarchy, floor mode and phase, with a new core
`(G', D', x', y')`. Every later call "inherits the state of the original orbit containing
it" (Section 6.1). The row record and the counter are kept when the counter invariant still
holds for the new core; otherwise the child clears the row record and the floor mode and sets
`h = 2` (Section 6, the carrier policy: "An independent certificate or rectangle child that may
lose the carrier clears its row record and floor mode, and sets `h=2`"). -/
noncomputable def inherit {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C') : State Ω C' :=
  if hc : CounterInv G' D' hD' S.rows S.h S.N ∧ CarrierOK G' D' S.rows S.hier then
    ⟨G', D', hD', x', y', S.hier, S.rows, S.floor, S.h, S.h_le, S.N, hc.1, hc.2⟩
  else ⟨G', D', hD', x', y', S.hier, none, false, 2, le_rfl, S.N, CounterInv.reset _ _ _ _,
    CarrierOK.none _ _ _⟩

@[simp] theorem inherit_G {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C') : (S.inherit G' D' hD' x' y').G = G' := by
  unfold inherit; split <;> rfl

@[simp] theorem inherit_dom {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C') : (S.inherit G' D' hD' x' y').dom = D' := by
  unfold inherit; split <;> rfl

@[simp] theorem inherit_x {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C') : (S.inherit G' D' hD' x' y').x = x' := by
  unfold inherit; split <;> rfl

@[simp] theorem inherit_y {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C') : (S.inherit G' D' hD' x' y').y = y' := by
  unfold inherit; split <;> rfl

@[simp] theorem inherit_hier {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C') : (S.inherit G' D' hD' x' y').hier = S.hier := by
  unfold inherit; split <;> rfl

@[simp] theorem inherit_N {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C') : (S.inherit G' D' hD' x' y').N = S.N := by
  unfold inherit; split <;> rfl

theorem inherit_answer {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C') :
    (S.inherit G' D' hD' x' y').answer = GI.Algorithm.answer G' D' x' y' := by
  unfold inherit; split <;> rfl

open Classical in
/-- A child on the same domain under a subgroup: everything but the group, the colorings and
the hierarchy is kept, including the row record and the counter, when the new group still
carries the retained rows (`CarrierOK`; Section 6: "A cap contraction or a coordinate change
alone does not reset `h`"; Section A.4: "While processing the quotient `Q`, use full preimages
of all quotient restrictions. This keeps the entire kernel `J`"; the normalization and the
continuations of an aggregation round). Otherwise the child clears the row record and the
floor mode and sets `h = 2` ("A genuine hierarchy refinement may likewise fund a reset if it
discards the record and floor mode"). -/
noncomputable def restrict {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (hG' : G' ≤ S.G)
    (x' y' : Ω → C') (hier' : List (Interval Ω)) : State Ω C' where
  G := G'
  dom := S.dom
  dom_inv := S.dom_inv.mono hG'
  x := x'
  y := y'
  hier := hier'
  rows := if CarrierOK G' S.dom S.rows hier' then S.rows else none
  floor := if CarrierOK G' S.dom S.rows hier' then S.floor else false
  h := if CarrierOK G' S.dom S.rows hier' then S.h else 2
  h_le := by split_ifs; exacts [S.h_le, le_rfl]
  N := S.N
  counter := by split_ifs; exacts [S.counter.mono hG', CounterInv.reset _ _ _ _]
  carrier := by split_ifs with hc; exacts [hc, CarrierOK.none _ _ _]

section Restrict

variable {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (hG' : G' ≤ S.G)
  (x' y' : Ω → C') (hier' : List (Interval Ω))

theorem restrict_rows_of (hc : CarrierOK G' S.dom S.rows hier') :
    (S.restrict G' hG' x' y' hier').rows = S.rows := by
  simp only [restrict, hc, if_true]

theorem restrict_floor_of (hc : CarrierOK G' S.dom S.rows hier') :
    (S.restrict G' hG' x' y' hier').floor = S.floor := by
  simp only [restrict, hc, if_true]

theorem restrict_h_of (hc : CarrierOK G' S.dom S.rows hier') :
    (S.restrict G' hG' x' y' hier').h = S.h := by
  simp only [restrict, hc, if_true]

/-- A row record of the child is the parent's. -/
theorem restrict_rows_eq {R : RowRecord Ω} (h : (S.restrict G' hG' x' y' hier').rows = some R) :
    S.rows = some R := by
  by_cases hc : CarrierOK G' S.dom S.rows hier'
  · rwa [restrict_rows_of S G' hG' x' y' hier' hc] at h
  · simp only [restrict, hc, if_false] at h
    exact absurd h (by simp)

end Restrict

/-! ### The bookkeeping of the orbit-chain children -/

/-- The bookkeeping of a state: the row record, the floor mode and the counter `h`. -/
def book (S : State Ω C) : Option (RowRecord Ω) × Bool × ℕ := (S.rows, S.floor, S.h)

/-- The bookkeeping after a reset: no row record, floor mode off, `h = 2`. -/
def resetBook : Option (RowRecord Ω) × Bool × ℕ := (none, false, 2)

/-- **The row test of the first orbit-chain child**: the retained columns split the orbit `D`,
that is, `D` meets at least two column classes (vacuous without a row record). When the rows
are a carrier of `G` on the domain, this is exactly when they stay a carrier on a `G`-invariant
part `D` of the domain (`GI.Algorithm.State.inherit_book`, `Workspace/Algorithm/OrbitKeep.lean`):
a `G`-orbit is a union of columns, so it meets every row, and only the two-column condition can
fail ("Entry into one proper retained column clears both and resets", Section 6.1). A program
reads it off the stored column labels and the indicator of `D`. -/
def ColsSplit (S : State Ω C) (D : Set Ω) : Prop :=
  ∀ R, S.rows = some R → ∃ c, R.cols = some c ∧ ∃ v ∈ D, ∃ w ∈ D, ¬ c.r v w

open Classical in
/-- **The bookkeeping of the first orbit-chain child** on the largest orbit `D` (Section 6.1:
"The first largest orbit under a full quotient preimage retains both the carrier and `h`"): the
parent's row record, floor mode and counter when the columns split `D` (`ColsSplit`), and a
reset otherwise. -/
noncomputable def orbitBook (S : State Ω C) (D : Set Ω) : Option (RowRecord Ω) × Bool × ℕ :=
  if S.ColsSplit D then S.book else resetBook

/-- **A reset child** of the orbit chain: a new core, the hierarchy and phase size of `S`, and
the bookkeeping reset (Section 6.1: "later conditional queries lie in other original orbits of
size at most half the parent domain and may clear and reset there"). -/
def resetChild (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C) : State Ω C :=
  ⟨G', D', hD', x', y', S.hier, none, false, 2, le_rfl, S.N, CounterInv.reset _ _ _ _,
    CarrierOK.none _ _ _⟩

theorem resetChild_inst (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C) : (S.resetChild G' D' hD' x' y').Inst G' D' x' y' :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem inherit_inst {C' : Type} (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C') :
    (S.inherit G' D' hD' x' y').Inst G' D' x' y' := by
  unfold inherit; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

end State

end GI.Algorithm
