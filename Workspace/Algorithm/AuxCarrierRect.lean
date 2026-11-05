module

public import Workspace.Algorithm.AuxPairRect
public import Workspace.Paper.RectangleCarrier

@[expose] public section

/-!
# The rectangle on the row--column diagonal orbit (Lemma A.30)

Section 5.3: "Suppose a later column action has `q` natural blocks and `q ≤ m`. Couple its even
permutations diagonally to the same permutations of `q` selected rows. Above a pair of distinct
labels this gives a grid of equal cells. … Lemma A.30 proves that these are actual subgroup-orbit
calls and that their answers project to the full required rectangle coset."

The data of Lemma A.30 are `GI.Carrier.Data` (`Workspace/Paper/RectangleCarrier.lean`): the carrier
quotient `G ↠ Alt(m) × Q` of the domain action, the cells `[m] × 𝒞` of its kernel orbits, the
column giant `ψ : Q' ↠ Alt(q)` on the parts of `𝒞'`, and `q` chosen rows. `CarrierData` adds what
links them to the state:

* the column giant is the supplied label map on the diagonal preimage `D̃`:
  `ψ(column g) = π(g)` for `g ∈ D̃` (`link`);
* the current physical orbit lies above `[m] × 𝒞'` ("If the current physical orbit is
  `[m] × 𝒞'` with its `M`-fibers", `over`).

`RectRep.ofCarrier` builds the representation of a rectangle from them: the group is `D̃` cut
down to the side stabilizer ("Restrict further to the inverse image of the setwise stabilizer of
`W` and `R` in `Alt(q)`, then select the physical orbit above `W × R`"), the cells are the
diagonal cells of `Data.cellQuotient`, every permitted label permutation lifts (`ideal` maps `D̃`
onto `Alt(q)`, `Data.ideal_onto`), and the orbit has `u r |W||R|` points
(`GI.Paper.lem_diagonal_carrier_card`) out of `m q r u`
(`GI.Paper.lem_diagonal_carrier_current_orbit_card`), so at most `3q/(16m) ≤ 3/16 ≤ θ` of the
domain ("the sharper factor is `η(1-η)|C|²/(mq) ≤ η(1-η)q/m`").

The permitted transporters are those of `Alt(Γ)`, so the parity twist of Lemma A.30 (needed only
for the full `Sym(W) × Sym(R)` transporter) is not used here.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Rectangle GI.Carrier

variable {P : Params} {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- **The data of Lemma A.30 for a state**: the carrier data of the domain action, the link of
its column giant to the supplied labels, and the current orbit above `[m] × 𝒞'`. -/
structure CarrierData {Ω C : Type} (S : State Ω C) (L : GiantLabels S) : Type 1 where
  Q : Type
  𝒞 : Type
  [grp : Group Q]
  [act : MulAction Q 𝒞]
  [fin : Fintype 𝒞]
  m : ℕ
  d : GI.Carrier.Data S.domGroup S.dom Q 𝒞 m L.q
  /-- The column giant is the supplied label map on the diagonal preimage. -/
  link : ∀ (g : S.G) (hg : (⟨S.domHom g, g, rfl⟩ : S.domGroup) ∈ d.lift),
    d.ideal ⟨_, hg⟩ = L.π g
  /-- The current physical orbit lies above `[m] × 𝒞'`. -/
  above : ∀ x : S.dom, (d.label x).2 ∈ d.C'

attribute [instance] CarrierData.grp CarrierData.act CarrierData.fin

namespace CarrierData

variable (D : CarrierData S L)

/-- The elements of `G` whose domain image lies in the diagonal preimage `D̃`. -/
noncomputable def liftD : Subgroup (Perm Ω) := S.liftGroup (D.d.lift.map S.domGroup.subtype)

theorem mem_liftD {h : Perm Ω} :
    h ∈ D.liftD ↔ ∃ hg : h ∈ S.G, (⟨S.domHom ⟨h, hg⟩, ⟨h, hg⟩, rfl⟩ : S.domGroup) ∈ D.d.lift := by
  rw [liftD, State.mem_liftGroup]
  constructor
  · rintro ⟨hg, y, hy, hye⟩
    refine ⟨hg, ?_⟩
    have : y = ⟨S.domHom ⟨h, hg⟩, ⟨h, hg⟩, rfl⟩ := Subtype.ext hye
    rw [← this]; exact hy
  · rintro ⟨hg, hk⟩
    exact ⟨hg, _, hk, rfl⟩

/-- The group of the query: `D̃` cut down to the side stabilizer. -/
noncomputable def H (W R : Finset (Fin L.q)) : Subgroup (Perm Ω) := D.liftD ⊓ L.lift (permitted W R)

variable {W R : Finset (Fin L.q)}

/-- The diagonal element of an element of the query group. -/
noncomputable def elt {h : Perm Ω} (hh : h ∈ D.H W R) : D.d.lift :=
  ⟨⟨S.domHom ⟨h, L.lift_le _ hh.2⟩, ⟨h, L.lift_le _ hh.2⟩, rfl⟩,
    ((D.mem_liftD).1 hh.1).2⟩

theorem ideal_elt {h : Perm Ω} (hh : h ∈ D.H W R) :
    D.d.ideal (D.elt hh) = L.π ⟨h, L.lift_le _ hh.2⟩ :=
  D.link _ _

theorem elt_smul {h : Perm Ω} (hh : h ∈ D.H W R) (x : D.d.Points) :
    ((D.elt hh • x : D.d.Points) : S.dom).val = h x.val.val := rfl

theorem image {h : Perm Ω} (hh : h ∈ D.H W R) : L.π ⟨h, L.lift_le _ hh.2⟩ ∈ permitted W R :=
  (L.mem_lift.1 hh.2).2

theorem le : D.H W R ≤ S.G := fun _ hh => L.lift_le _ hh.2

theorem movePoint_eq_rect (g : permitted W R) (c : W × R) :
    movePoint g c = rectangleAction g c := rfl

section

variable [Finite Ω]

open Classical in
/-- The matrix entry above a position: the diagonal cell of a point above the chosen rows and
`𝒞'`, when it lies in `W × R`. -/
noncomputable def cell (W R : Finset (Fin L.q)) (v : Ω) : Option (W × R) :=
  if hv : v ∈ S.dom then
    if hp : (D.d.label ⟨v, hv⟩).1 ∈ Set.range D.d.rows ∧ (D.d.label ⟨v, hv⟩).2 ∈ D.d.C' then
      if h : D.d.cell ⟨⟨v, hv⟩, hp⟩ ∈ Set.range (crossEmbedding (W := W) (R := R)) then
        some (GI.EmbeddedQuotient.map D.d.cellQuotient crossEmbedding ⟨⟨⟨v, hv⟩, hp⟩, h⟩)
      else none
    else none
  else none

theorem cell_eq_some {v : Ω} (hv : v ∈ S.dom)
    (hp : (D.d.label ⟨v, hv⟩).1 ∈ Set.range D.d.rows ∧ (D.d.label ⟨v, hv⟩).2 ∈ D.d.C')
    (c : W × R) : D.cell W R v = some c ↔ D.d.cell ⟨⟨v, hv⟩, hp⟩ = crossEmbedding c := by
  classical
  unfold cell
  rw [dif_pos hv, dif_pos hp]
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact (GI.EmbeddedQuotient.embed_map D.d.cellQuotient crossEmbedding
        ⟨⟨⟨v, hv⟩, hp⟩, h⟩).symm
    · intro hc
      apply crossEmbedding.injective
      rw [GI.EmbeddedQuotient.embed_map]
      exact hc
  · simp only [false_iff]
    intro hc
    exact h ⟨c, hc.symm⟩

theorem cell_eq_none {v : Ω} (hv : v ∈ S.dom)
    (hp : (D.d.label ⟨v, hv⟩).1 ∈ Set.range D.d.rows ∧ (D.d.label ⟨v, hv⟩).2 ∈ D.d.C') :
    D.cell W R v = none ↔ D.d.cell ⟨⟨v, hv⟩, hp⟩ ∉ Set.range (crossEmbedding (W := W) (R := R)) := by
  classical
  unfold cell
  rw [dif_pos hv, dif_pos hp]
  split_ifs with h <;> simp [h]

theorem cell_of_not {v : Ω} (hv : v ∈ S.dom)
    (hp : ¬ ((D.d.label ⟨v, hv⟩).1 ∈ Set.range D.d.rows ∧ (D.d.label ⟨v, hv⟩).2 ∈ D.d.C')) :
    D.cell W R v = none := by
  classical
  unfold cell
  rw [dif_pos hv, dif_neg hp]

theorem cell_equivariant {h : Perm Ω} (hh : h ∈ D.H W R) {v : Ω} (hv : v ∈ S.dom) :
    D.cell W R (h v) = (D.cell W R v).map (movePoint ⟨_, D.image hh⟩) := by
  have hv' : h v ∈ S.dom := (S.dom_inv h (D.le hh) v).2 hv
  set k := D.elt hh
  by_cases hp : (D.d.label ⟨v, hv⟩).1 ∈ Set.range D.d.rows ∧ (D.d.label ⟨v, hv⟩).2 ∈ D.d.C'
  · set x : D.d.Points := ⟨⟨v, hv⟩, hp⟩
    have hp' := (k • x).property
    have hkx : (k • x : D.d.Points) = ⟨⟨h v, hv'⟩, hp'⟩ := rfl
    have hcell : D.d.cell ⟨⟨h v, hv'⟩, hp'⟩ =
        (L.π ⟨h, L.lift_le _ hh.2⟩ : alternatingGroup (Fin L.q)) • D.d.cell x := by
      rw [← hkx, D.d.cell_equivariant, D.ideal_elt]
    cases hc : D.cell W R v with
    | some c =>
      rw [Option.map_some, D.cell_eq_some hv' hp', movePoint_eq_rect, crossEmbedding_move]
      rw [D.cell_eq_some hv hp] at hc
      rw [hcell, hc]
    | none =>
      rw [Option.map_none, D.cell_eq_none hv' hp']
      rw [D.cell_eq_none hv hp] at hc
      rintro ⟨c', hc'⟩
      apply hc
      refine ⟨rectangleAction (⟨_, D.image hh⟩ : permitted W R)⁻¹ c', ?_⟩
      rw [crossEmbedding_move, hc', hcell, ← mul_smul]
      change ((L.π ⟨h, L.lift_le _ hh.2⟩)⁻¹ * L.π ⟨h, L.lift_le _ hh.2⟩) • _ = _
      rw [inv_mul_cancel, one_smul]
  · rw [D.cell_of_not hv hp]
    refine D.cell_of_not hv' fun hp' => hp ?_
    have h1 := (k⁻¹ • (⟨⟨h v, hv'⟩, hp'⟩ : D.d.Points)).property
    have e : ((k⁻¹ • (⟨⟨h v, hv'⟩, hp'⟩ : D.d.Points) : D.d.Points) : S.dom) = ⟨v, hv⟩ := by
      have e1 : (⟨h v, hv'⟩ : S.dom) = (k : S.domGroup) • (⟨v, hv⟩ : S.dom) := rfl
      change ((k⁻¹ : D.d.lift) : S.domGroup) • (⟨h v, hv'⟩ : S.dom) = _
      rw [e1, Subgroup.coe_inv, inv_smul_smul]
    rw [e] at h1
    exact h1

/-- The positions above the rectangle are the points of the query orbit of Lemma A.30. -/
noncomputable def cellEquiv (W R : Finset (Fin L.q)) :
    {v // v ∈ S.dom ∧ D.cell W R v ≠ none} ≃ GI.Paper.carrierOrbit D.d W R where
  toFun v :=
    have hp : (D.d.label ⟨v.1, v.2.1⟩).1 ∈ Set.range D.d.rows ∧
        (D.d.label ⟨v.1, v.2.1⟩).2 ∈ D.d.C' := by
      by_contra hp
      exact v.2.2 (D.cell_of_not v.2.1 hp)
    ⟨⟨⟨v.1, v.2.1⟩, hp⟩, by
      by_contra h
      exact v.2.2 ((D.cell_eq_none v.2.1 hp).2 h)⟩
  invFun x := ⟨x.1.1.1, x.1.1.2, fun h => (D.cell_eq_none x.1.1.2 x.1.2).1 h x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end

end CarrierData

/-- **The representation of a rectangle on the row--column diagonal orbit** (Lemma A.30), for
`q ≤ m` chosen rows, `θ ≥ 3/16`. -/
noncomputable def RectRep.ofCarrier [Finite Ω] (D : CarrierData S L) {W R : Finset (Fin L.q)}
    (hθ : 3 / 16 ≤ P.θ)
    (harea : (W.card : ℝ) * R.card ≤ etaB * (1 - etaB) * (L.q : ℝ) ^ 2) :
    RectRep P S L W R where
  H := D.H W R
  le := D.le
  image _ hh := D.image hh
  cell := D.cell W R
  equivariant _ hh _ hv := D.cell_equivariant hh hv
  onto c := by
    obtain ⟨x, hx⟩ := D.d.cellQuotient.onto (crossEmbedding c)
    exact ⟨x.1.1, x.1.2, (D.cell_eq_some x.1.2 x.2 c).2 hx⟩
  twist := none
  -- "`ideal` maps `D̃` onto `Alt(q)`": every permitted label permutation lifts
  lifts p := by
    left
    obtain ⟨k, hk⟩ := D.d.ideal_onto (p : alternatingGroup (Fin L.q))
    obtain ⟨g, hg⟩ := k.1.2
    have hk' : k.1 = ⟨S.domHom g, g, rfl⟩ := Subtype.ext hg.symm
    have hmem : (⟨S.domHom g, g, rfl⟩ : S.domGroup) ∈ D.d.lift := hk' ▸ k.2
    have hπ : L.π g = p := by
      rw [← D.link g hmem, ← hk]
      congr 1
      exact Subtype.ext hk'.symm
    refine ⟨g.1, ⟨(D.mem_liftD).2 ⟨g.2, hmem⟩, L.mem_lift.2 ⟨g.2, by rw [hπ]; exact p.2⟩⟩, hπ⟩
  small := by
    classical
    rw [Nat.card_congr (D.cellEquiv W R), GI.Paper.lem_diagonal_carrier_card]
    have hs : S.size = D.m * (L.q * D.d.r) * D.d.u := by
      rw [← GI.Paper.lem_diagonal_carrier_current_orbit_card D.d, State.size]
      exact Nat.card_congr
        { toFun := fun x => ⟨x, D.above x⟩, invFun := fun x => x.1,
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    have hqm : (L.q : ℝ) ≤ D.m := by exact_mod_cast GI.Paper.lem_diagonal_carrier_q_le_m D.d
    rw [hs]
    push_cast
    have e : etaB * (1 - etaB) = 3 / 16 := by norm_num [etaB]
    rw [e] at harea
    have hu : (0 : ℝ) ≤ D.d.u := Nat.cast_nonneg _
    have hr : (0 : ℝ) ≤ D.d.r := Nat.cast_nonneg _
    have hq : (0 : ℝ) ≤ L.q := Nat.cast_nonneg _
    have hur : (0 : ℝ) ≤ D.d.u * D.d.r := mul_nonneg hu hr
    -- `u r |W||R| ≤ u r (3/16) q² ≤ (3/16) m q r u ≤ θ m q r u`
    calc (D.d.u : ℝ) * D.d.r * (W.card * R.card) ≤ D.d.u * D.d.r * (3 / 16 * (L.q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left harea hur
      _ ≤ D.d.u * D.d.r * (3 / 16 * (L.q * D.m)) := by
          apply mul_le_mul_of_nonneg_left _ hur
          nlinarith
      _ = 3 / 16 * (D.m * (L.q * D.d.r) * D.d.u) := by ring
      _ ≤ P.θ * (D.m * (L.q * D.d.r) * D.d.u) :=
          mul_le_mul_of_nonneg_right hθ (by positivity)

end GI.Algorithm
