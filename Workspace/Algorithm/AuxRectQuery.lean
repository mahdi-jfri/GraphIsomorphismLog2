module

public import Workspace.Algorithm.AuxRectangle

@[expose] public section

/-!
# The rectangle query states (Algorithm `alg:auxiliary`)

Algorithm `alg:auxiliary`, the branch `q > λ`: "Represent the rectangle on an actual inherited
orbit `Δ`. Pull matrix-entry colors back to `Δ` in both instances. Use `Continue` to obtain its
complete permitted rectangle answer." After the algorithm: "If the diagonal action supplies only
one parity class of rectangle maps, query both classes by twisting the target matrix, as in
Lemma A.30. This uses at most two inherited calls and does not require an odd physical lift."

This file builds these query states from one structure, `RectRep`: a representation of the
rectangle `W × R` on an inherited orbit. It consists of
* a subgroup `H ≤ G` whose label images keep `W` and `R` (the group of the query);
* a map `cell` from the positions to `W × R` (or `none` off the orbit) that is equivariant under
  `H` and onto (the positions above each matrix entry);
* an optional twist `t`: every permitted label permutation `p` has a lift in `H`, or `t⁻¹ p` has
  one (the parity classes of Lemma A.30); for pair labels no twist is needed (Lemma A.27:
  "Every permitted pair permutation has a lift in `H`");
* the size bound `|Δ| ≤ θ s` of the orbit `Δ` of positions with a cell (eq. `IR2` with
  Lemma A.28 for pair labels; the ratio `η(1-η)q/m` of Lemma A.30 for the carrier).

The query of a twist `t` is the inherited state on `Δ` under `H` with the source string
`M ∘ cell` and the target string `N_t ∘ cell`, where `N_t(w, r) = N(t w, t r)` is the twisted
target matrix ("Pull matrix-entry colors back to `Δ` in both instances"; "precomposing the target
rectangle colors with a fixed odd-total-parity rectangle permutation"). From an element `h` of
its answer it reads `a₀ t π(h)` ("Project to the left side … and retain the source--target
alignment").

`RectRep.valid` proves the four facts that `RectOracle` asks: at most two queries, each a charged
call (`ChargedCall`: same phase and hierarchy, a subgroup on part of the domain, orbits of at
most `θ s` points), soundness (`a₀⁻¹ σ ∈ leftOvercoset M N`: an element of the answer transports
the pulled-back strings, so its label image transports the matrices), and completeness (a
permitted matrix transporter lifts to an element of one of the answers). `RectOracle.ofReps`
turns a family of representations into a rectangle oracle.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Rectangle

variable {P : Params} {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- **A representation of the rectangle `W × R` on an inherited orbit** (Algorithm
`alg:auxiliary`: "Represent the rectangle on an actual inherited orbit `Δ`"). -/
structure RectRep (P : Params) {Ω C : Type} (S : State Ω C) (L : GiantLabels S)
    (W R : Finset (Fin L.q)) : Type where
  /-- The group of the query, a subgroup of the parent action. -/
  H : Subgroup (Perm Ω)
  le : H ≤ S.G
  /-- Its label images keep the two sides. -/
  image : ∀ h (hh : h ∈ H), L.π ⟨h, le hh⟩ ∈ permitted W R
  /-- The matrix entry above a position, `none` off the orbit `Δ`. -/
  cell : Ω → Option (W × R)
  equivariant : ∀ h (hh : h ∈ H), ∀ v ∈ S.dom,
    cell (h v) = (cell v).map (movePoint ⟨_, image h hh⟩)
  /-- Every matrix entry has a position above it. -/
  onto : ∀ c, ∃ v ∈ S.dom, cell v = some c
  /-- The parity twist, if one is needed. -/
  twist : Option (permitted W R)
  /-- Every permitted label permutation, or its twist, lifts to `H`. -/
  lifts : ∀ p : permitted W R, (∃ h, ∃ hh : h ∈ H, L.π ⟨h, le hh⟩ = p) ∨
    ∃ t ∈ twist, ∃ h, ∃ hh : h ∈ H, L.π ⟨h, le hh⟩ = ((t⁻¹ * p : permitted W R) : _)
  /-- The orbit has at most `θ s` positions. -/
  small : (Nat.card {v // v ∈ S.dom ∧ cell v ≠ none} : ℝ) ≤ P.θ * S.size

namespace RectRep

variable {W R : Finset (Fin L.q)} (rep : RectRep P S L W R)

/-- The orbit `Δ`: the positions of the domain above a matrix entry. -/
def Δ : Set Ω := {v | v ∈ S.dom ∧ rep.cell v ≠ none}

theorem cell_smul_ne {h : Perm Ω} (hh : h ∈ rep.H) {v : Ω} (hv : v ∈ S.dom) :
    rep.cell (h v) ≠ none ↔ rep.cell v ≠ none := by
  rw [rep.equivariant h hh v hv]
  cases rep.cell v <;> simp

/-- `Δ` is invariant under `H`. -/
theorem Δ_inv : Invariant rep.H rep.Δ := by
  intro h hh v
  have hd := S.dom_inv h (rep.le hh) v
  constructor
  · rintro ⟨h1, h2⟩
    have hv := hd.1 h1
    exact ⟨hv, (rep.cell_smul_ne hh hv).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hd.2 h1, (rep.cell_smul_ne hh h1).2 h2⟩

/-- The pulled-back string of a matrix ("Pull matrix-entry colors back to `Δ`"). -/
def colors (M : W → R → Bool) : Ω → Option Bool := fun v => (rep.cell v).map fun c => M c.1 c.2

/-- The target matrix twisted by `t`: `N_t(w, r) = N(t w, t r)`. -/
def twistMat (t : permitted W R) (N : W → R → Bool) : W → R → Bool :=
  fun w r => N ((sideAction t).1 w) ((sideAction t).2 r)

theorem movePoint_eq (g : permitted W R) (c : W × R) :
    movePoint g c = ((sideAction g).1 c.1, (sideAction g).2 c.2) := rfl

/-- The inherited query state of the twist `t`. It clears the bookkeeping (`State.queryChild`;
Section 6: "An independent certificate or rectangle child that may lose the carrier clears its
row record"). -/
noncomputable def state (M N : W → R → Bool) (t : permitted W R) : State Ω (Option Bool) :=
  S.queryChild rep.H rep.Δ rep.Δ_inv (rep.colors M) (rep.colors (twistMat t N))

open Classical in
/-- **The rectangle query of the twist `t`**: `Continue` on the inherited state; from an element
`h` of the answer it reads `a₀ t π(h)`. -/
noncomputable def query (M N : W → R → Bool) (a₀ : alternatingGroup (Fin L.q))
    (t : permitted W R) : AuxQuery P S L where
  mode := .cont
  Ω' := Ω
  C' := Option Bool
  T := rep.state M N t
  read A := if h : ∃ g, g ∈ A ∧ g ∈ S.G then
      some (a₀ * ((t : alternatingGroup (Fin L.q)) * L.π ⟨h.choose, h.choose_spec.2⟩))
    else none
  solve_fin h := by cases h

/-- The queries: the untwisted one, and the twisted one if a twist is needed ("at most two
inherited calls"). -/
noncomputable def queries (M N : W → R → Bool) (a₀ : alternatingGroup (Fin L.q)) :
    List (AuxQuery P S L) :=
  rep.query M N a₀ 1 :: (rep.twist.map (rep.query M N a₀)).toList

theorem state_answer (M N : W → R → Bool) (t : permitted W R) :
    (rep.state M N t).answer =
      GI.Algorithm.answer rep.H rep.Δ (rep.colors M) (rep.colors (twistMat t N)) :=
  S.queryChild_answer ..

/-- An element of the answer transports the matrices ("An element of `H` preserves or transports
these pulled-back strings exactly when its induced pair permutation preserves or transports the
matrices"), first direction. -/
theorem transports_of_mem {M N : W → R → Bool} {t : permitted W R} {g : Perm Ω}
    (hg : g ∈ (rep.state M N t).answer) :
    ∃ hh : g ∈ rep.H, MatrixTransports M (twistMat t N) ⟨_, rep.image g hh⟩ := by
  rw [state_answer] at hg
  obtain ⟨hh, hx⟩ := hg
  refine ⟨hh, fun a b => ?_⟩
  obtain ⟨v, hv, hc⟩ := rep.onto (a, b)
  have e := hx v ⟨hv, by rw [hc]; simp⟩
  simp only [colors, rep.equivariant g hh v hv, hc, Option.map_some] at e
  exact Option.some.inj e

/-- Second direction: an element of `H` whose label image transports the matrices is in the
answer. -/
theorem mem_of_transports {M N : W → R → Bool} {t : permitted W R} {g : Perm Ω}
    (hh : g ∈ rep.H) (htr : MatrixTransports M (twistMat t N) ⟨_, rep.image g hh⟩) :
    g ∈ (rep.state M N t).answer := by
  rw [state_answer]
  refine ⟨hh, fun v hv => ?_⟩
  obtain ⟨hvd, hvc⟩ := hv
  simp only [colors, rep.equivariant g hh v hvd]
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hvc
  rw [hc]
  simp only [Option.map_some]
  exact congrArg some (htr c.1 c.2)

/-- `N_t` and `t` together: a transporter to `N_t` composed with `t` is a transporter to `N`. -/
theorem transports_twist {M N : W → R → Bool} {t h : permitted W R}
    (htr : MatrixTransports M (twistMat t N) h) : MatrixTransports M N (t * h) := by
  intro a b
  rw [map_mul]
  exact htr a b

theorem transports_untwist {M N : W → R → Bool} {t p : permitted W R}
    (htr : MatrixTransports M N p) : MatrixTransports M (twistMat t N) (t⁻¹ * p) := by
  intro a b
  have e := htr a b
  change N ((sideAction t).1 ((sideAction (t⁻¹ * p)).1 a))
    ((sideAction t).2 ((sideAction (t⁻¹ * p)).2 b)) = M a b
  rw [← Perm.mul_apply, ← Perm.mul_apply, ← Prod.fst_mul, ← Prod.snd_mul, ← map_mul,
    mul_inv_cancel_left]
  exact e

/-- **The query is a charged call** (Lemma A.27: "The queried action is literally the action of a
subgroup of `G` on one of its orbits"; Section 5.2: "The query is an actual subgroup-orbit
restriction, so it inherits the hierarchy and the symmetry measure"): same phase and hierarchy,
the group `H ≤ G`, the domain `Δ ⊆ dom`, and every orbit lies in `Δ`, which has at most `θ s`
points. -/
theorem query_call [Finite Ω] (M N : W → R → Bool) (a₀ : alternatingGroup (Fin L.q))
    (t : permitted W R) : AggCall P S (rep.query M N a₀ t).mode (rep.query M N a₀ t).T := by
  refine Or.inr ⟨rfl, rfl, show ChargedCall P S (rep.state M N t) from ?_⟩
  refine ⟨S.queryChild_N .., by simpa [state] using rep.le, by
    simp only [state, State.queryChild_dom]; exact fun v hv => hv.1, S.queryChild_hier .., fun v hv => ?_⟩
  left
  simp only [state, State.queryChild_G, State.queryChild_dom] at hv ⊢
  have hsub : orb rep.H v ⊆ rep.Δ := by
    rintro _ ⟨g, hg, rfl⟩
    exact (rep.Δ_inv g hg v).2 hv
  have hfin : (rep.Δ).Finite := Set.toFinite _
  have h1 : Nat.card (orb rep.H v) ≤ Nat.card rep.Δ := Nat.card_mono hfin hsub
  have h2 : Nat.card rep.Δ = Nat.card {v // v ∈ S.dom ∧ rep.cell v ≠ none} := rfl
  calc (Nat.card (orb rep.H v) : ℝ) ≤ Nat.card rep.Δ := by exact_mod_cast h1
    _ ≤ P.θ * S.size := by rw [h2]; exact rep.small

/-- **Soundness of a query**: a representative read off the answer lies in `a₀ · leftOvercoset M N`
("Project to the left side; extend over `Γ \ W` and impose parity"). -/
theorem query_sound (M N : W → R → Bool) (a₀ : alternatingGroup (Fin L.q)) (t : permitted W R)
    {σ : alternatingGroup (Fin L.q)}
    (hσ : (rep.query M N a₀ t).read (rep.query M N a₀ t).T.answer = some σ) :
    a₀⁻¹ * σ ∈ leftOvercoset M N := by
  classical
  simp only [query] at hσ
  split_ifs at hσ with hex
  rw [Option.some.injEq] at hσ
  subst hσ
  obtain ⟨hmem, -⟩ := hex.choose_spec
  obtain ⟨hh, htr⟩ := rep.transports_of_mem hmem
  have h2 := mem_leftOvercoset (transports_twist htr)
  rw [inv_mul_cancel_left]
  exact h2

/-- **Completeness of a query**: a lift `h ∈ H` of `t⁻¹ p`, for a permitted transporter `p` from
`M` to `N`, is in the answer, so the query reads a representative. -/
theorem query_complete (M N : W → R → Bool) (a₀ : alternatingGroup (Fin L.q)) (t : permitted W R)
    {p : permitted W R} (hp : MatrixTransports M N p) {h : Perm Ω} (hh : h ∈ rep.H)
    (hπ : L.π ⟨h, rep.le hh⟩ = ((t⁻¹ * p : permitted W R) : alternatingGroup (Fin L.q))) :
    ∃ σ, (rep.query M N a₀ t).read (rep.query M N a₀ t).T.answer = some σ := by
  classical
  have hmem : h ∈ (rep.state M N t).answer := by
    refine rep.mem_of_transports hh ?_
    have e : (⟨_, rep.image h hh⟩ : permitted W R) = t⁻¹ * p := Subtype.ext hπ
    rw [e]
    exact transports_untwist hp
  have hex : ∃ g, g ∈ (rep.state M N t).answer ∧ g ∈ S.G := ⟨h, hmem, rep.le hh⟩
  simp only [query]
  exact ⟨_, dif_pos hex⟩

/-- **The facts of a rectangle oracle** for one representation (`RectOracle.valid`). -/
theorem valid [Finite Ω] (M N : W → R → Bool) (a₀ : alternatingGroup (Fin L.q)) :
    (rep.queries M N a₀).length ≤ 2 ∧
    (∀ Q ∈ rep.queries M N a₀, AggCall P S Q.mode Q.T) ∧
    (∀ Q ∈ rep.queries M N a₀, ∀ σ, Q.read Q.T.answer = some σ →
      a₀⁻¹ * σ ∈ leftOvercoset M N) ∧
    ((∃ h : permitted W R, MatrixTransports M N h) →
      ∃ Q ∈ rep.queries M N a₀, ∃ σ, Q.read Q.T.answer = some σ) := by
  have hmem : ∀ Q ∈ rep.queries M N a₀, ∃ t, Q = rep.query M N a₀ t := by
    intro Q hQ
    simp only [queries, List.mem_cons] at hQ
    rcases hQ with rfl | hQ
    · exact ⟨1, rfl⟩
    · cases ht : rep.twist with
      | none => simp [ht] at hQ
      | some t => simp only [ht, Option.map_some, Option.toList_some,
          List.mem_singleton] at hQ; exact ⟨t, hQ⟩
  refine ⟨?_, fun Q hQ => ?_, fun Q hQ σ hσ => ?_, fun ⟨p, hp⟩ => ?_⟩
  · simp only [queries, List.length_cons]
    cases rep.twist <;> simp
  · obtain ⟨t, rfl⟩ := hmem Q hQ
    exact rep.query_call M N a₀ t
  · obtain ⟨t, rfl⟩ := hmem Q hQ
    exact rep.query_sound M N a₀ t hσ
  · rcases rep.lifts p with ⟨h, hh, hπ⟩ | ⟨t, ht, h, hh, hπ⟩
    · refine ⟨_, List.mem_cons_self .., rep.query_complete M N a₀ 1 hp hh ?_⟩
      rw [hπ, inv_one, one_mul]
    · refine ⟨rep.query M N a₀ t, ?_, rep.query_complete M N a₀ t hp hh hπ⟩
      simp only [queries, List.mem_cons]
      right
      rw [Option.mem_def] at ht
      simp [ht]

end RectRep

/-- The conditions on a rectangle under which `RectOracle` asks for queries. -/
def RectConds (P : Params) {Ω C : Type} (S : State Ω C) (L : GiantLabels S)
    (W R : Finset (Fin L.q)) : Prop :=
  (S.N : ℝ) ^ P.α < L.q ∧ Disjoint W R ∧ 3 ≤ W.card ∧ R.Nonempty ∧
    (W.card : ℝ) * R.card ≤ etaB * (1 - etaB) * (L.q : ℝ) ^ 2

open Classical in
/-- **A rectangle oracle from rectangle representations**: the queries of the representation
of every rectangle that `RectOracle` asks about, no query otherwise. -/
noncomputable def RectOracle.ofReps [Finite Ω]
    (rep : ∀ W R : Finset (Fin L.q), RectConds P S L W R → RectRep P S L W R) :
    RectOracle P S L where
  queries W R M N a₀ := if h : RectConds P S L W R then (rep W R h).queries M N a₀ else []
  valid W R M N a₀ hlam hd hW hR harea := by
    have h : RectConds P S L W R := ⟨hlam, hd, hW, hR, harea⟩
    simp only [dif_pos h]
    exact (rep W R h).valid M N a₀

end GI.Algorithm
