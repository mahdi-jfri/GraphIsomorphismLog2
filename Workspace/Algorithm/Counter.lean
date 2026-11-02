import Workspace.Algorithm.RowSteps
import Workspace.Paper.RectangleCarrier
import Workspace.CertificateCalls

/-!
# The row-action counter never becomes negative (Section 7.1)

Section 7.1: "Let `h ∈ {0, 1, 2}` count how many more times the current row action may be
enlarged … The one-promotion argument ensures that it never becomes negative." Section 6,
"Why a row action is enlarged at most once", and Lemma A.29 (`lem:one-carrier-promotion`) give
the argument. This file proves it for the column step of the recursion
(`column_step_counter`).

The state records the invariant `CounterInv` (`Workspace/Algorithm/State.lean`):

* at `h = 1`: the retained rows are a carrier of the action (an invariant partition of the
  domain into `m` rows) and `N < m³`, since they were made at a natural giant of degree
  `m > λ = N^α` with `α > 1/3` (eq. `scale-constraints`);
* at `h = 0`: every alternating section of the faithful action on the domain has degree at
  most the retained row degree (Lemma A.29: "`aw(G) ≤ q`").

At a column step with retained rows of degree `m` and new natural labels of degree `q > m`:

* `h = 0` is impossible: the labels give `Alt(q)` as a quotient of the action, but every
  alternating section has degree at most `m < q` (Section 6: "every later large quotient in a
  subgroup or quotient of this action has degree at most `q`");
* at `h = 1` the action has the old rows (`m` blocks) and the new label columns (`q` blocks).
  A row stabilizer has index at most `m < q`, so it maps onto `Alt(q)`
  (`GI.Endpoint.alternating_min_index`); the action is thus transitive on cells, all cells
  have the same size `u`, and `m q u = s ≤ N < m³ < m q²` gives `u < q`. Lemma A.29
  (`GI.Paper.lem_one_carrier_promotion_tower`) gives the cap `q`, which is the invariant at
  `h = 0` for the new rows;
* at `h = 2` the new rows are a carrier, and `N < q³` since `N^α < q` and `α > 1/3`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

/-! ### The action on the blocks of an invariant partition -/

section Blocks

variable {D : Type} (G : Subgroup (Perm D)) (r : Setoid D)
  (hr : ∀ g ∈ G, ∀ v w, r (g v) (g w) ↔ r v w)

/-- The action of `G` on the blocks of an invariant partition. -/
def blockHom : G →* Perm (Quotient r) where
  toFun g :=
    { toFun := Quotient.map' g.val fun a b h => (hr g g.2 a b).2 h
      invFun := Quotient.map' ⇑((g⁻¹ : G) : Perm D) fun a b h => (hr _ (g⁻¹).2 a b).2 h
      left_inv := fun a => Quotient.inductionOn' a fun v => by
        simp [Quotient.map'_mk'']
      right_inv := fun a => Quotient.inductionOn' a fun v => by
        simp [Quotient.map'_mk''] }
  map_one' := by
    ext a
    induction a using Quotient.inductionOn'
    rfl
  map_mul' g h := by
    ext a
    induction a using Quotient.inductionOn'
    rfl

theorem blockHom_mk (g : G) (v : D) :
    blockHom G r hr g (Quotient.mk r v) = Quotient.mk r (g.val v) := rfl

end Blocks

/-! ### Lemma A.29 for an action with an old row partition and new natural labels -/

section Promotion

variable {D : Type} [Fintype D]

/-- **The promotion step** (Lemma A.29, with the cell count of Section 6). `G` is transitive on
`D` and preserves a partition `r` into `m ≥ 4` blocks; `π : G → Alt(q)` is onto, with an
equivariant map `label : D → [q]`; `m < q` and `|D| < m³`. Then every alternating section
of `G` has degree at most `q`. -/
theorem promotion_cap (G : Subgroup (Perm D)) (htr : ∀ v w, ∃ g ∈ G, g v = w)
    (r : Setoid D) (hr : ∀ g ∈ G, ∀ v w, r (g v) (g w) ↔ r v w) {m q : ℕ}
    (hm : Nat.card (Quotient r) = m) (label : D → Fin q)
    (π : G →* alternatingGroup (Fin q)) (hπ : Function.Surjective π)
    (heq : ∀ (g : G) v, label (g.val v) = (π g).val (label v))
    (h4 : 4 ≤ m) (hmq : m < q) (hD : Fintype.card D < m ^ 3) :
    GI.SectionCaps.Cap G q := by
  classical
  have hq5 : 5 ≤ q := by omega
  let α := blockHom G r hr
  let γ : G →* Perm (Fin q) := (alternatingGroup (Fin q)).subtype.comp π
  let row : D → Quotient r := Quotient.mk r
  have hrow : ∀ (g : G) x, row (g.val x) = α g (row x) := fun _ _ => rfl
  have hcol : ∀ (g : G) x, label (g.val x) = γ g (label x) := heq
  -- A row stabilizer maps onto `Alt(q)`: its index is at most `m < q`.
  letI : MulAction G (Quotient r) := MulAction.compHom _ α
  have hstab : ∀ a : Quotient r, (MulAction.stabilizer G a).map π = ⊤ := by
    intro a
    by_contra hne
    have h1 := GI.Endpoint.alternating_min_index (by simpa using hq5) _ hne
    have hfin : (MulAction.stabilizer G a).index ≠ 0 := by
      rw [MulAction.index_stabilizer]
      exact ((Set.ncard_pos (Set.toFinite _)).2 ⟨a, MulAction.mem_orbit_self a⟩).ne'
    have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hfin) (Subgroup.index_map_dvd _ hπ)
    have h3 : (MulAction.stabilizer G a).index ≤ m := by
      rw [MulAction.index_stabilizer, ← hm]
      exact Set.ncard_le_card _
    simp only [Fintype.card_fin] at h1
    omega
  -- Every cell is the image of a fixed cell under an element of `G`.
  have hD0 : Nonempty D := by
    by_contra h0
    rw [not_nonempty_iff] at h0
    have : Nat.card (Quotient r) = 0 := by
      rw [Nat.card_eq_zero]; left; exact ⟨fun a => Quotient.inductionOn a fun v => h0.elim v⟩
    omega
  obtain ⟨v0⟩ := hD0
  let cell : Quotient r × Fin q → Type := fun p => {x // (row x, label x) = p}
  have hmove : ∀ p, ∃ g : G, (row (g.val v0), label (g.val v0)) = p := by
    rintro ⟨a, c⟩
    obtain ⟨w, rfl⟩ := Quotient.exists_rep a
    obtain ⟨g₁, hg₁, hw⟩ := htr v0 w
    haveI := alternatingGroup.isPretransitive_of_three_le_card (Fin q) (by simp; omega)
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin q)) (label w) c
    have hσ' : σ ∈ (MulAction.stabilizer G (Quotient.mk r w)).map π := by
      rw [hstab]; trivial
    obtain ⟨h, hh, rfl⟩ := hσ'
    refine ⟨h * ⟨g₁, hg₁⟩, ?_⟩
    have hhw : α h (Quotient.mk r w) = Quotient.mk r w := hh
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · change α h (row (g₁ v0)) = _
      rw [hw]; exact hhw
    · change label (h.val (g₁ v0)) = c
      rw [hw, heq]; exact hσ
  let u := Fintype.card (cell (row v0, label v0))
  have hcell : ∀ p, Fintype.card (cell p) = u := by
    intro p
    obtain ⟨g, hg⟩ := hmove p
    symm
    refine Fintype.card_congr (Equiv.subtypeEquiv (g.val) fun x => ?_)
    change _ ↔ (row (g.val x), label (g.val x)) = p
    rw [← hg, hrow, hcol, hrow, hcol]
    constructor
    · intro h
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨by rw [h.1], by rw [h.2]⟩
    · intro h
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨(α g).injective h.1, (γ g).injective h.2⟩
  -- Counting: `|D| = m q u`.
  have hcount : Fintype.card D = m * q * u := by
    have h1 : Fintype.card D = ∑ p : Quotient r × Fin q, Fintype.card (cell p) := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv fun x : D => (row x, label x)).symm
    rw [h1, Finset.sum_congr rfl (fun p _ => hcell p), Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, smul_eq_mul, ← Nat.card_eq_fintype_card (α := Quotient r),
      hm]
  have hu : u < q := by
    by_contra hu
    push Not at hu
    have : m * q * q ≤ m * q * u := Nat.mul_le_mul_left _ hu
    have hm3 : m ^ 3 ≤ m * q * q := by
      have : m * m * m ≤ m * q * q :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hmq.le) hmq.le
      simpa [pow_succ, pow_zero, one_mul, mul_assoc] using this
    omega
  have hcap := GI.Paper.lem_one_carrier_promotion_tower G row label α γ hrow hcol u
    (fun a c => (hcell (a, c)).le)
  have hRw : Fintype.card (Quotient r) = m := by rw [← Nat.card_eq_fintype_card, hm]
  rw [hRw, Fintype.card_fin] at hcap
  have : max q (max m u) = q := by omega
  rwa [this] at hcap

end Promotion

/-! ### The column step -/

section ColumnStep

variable {Ω C : Type}

/-- The giant labels factor through the faithful image on the domain: an element acting
trivially on the domain fixes every label, so its image in `Alt(q)` is trivial. -/
theorem labels_kill {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}
    (hnat : NaturalRows S L label) : S.domHom.ker ≤ L.π.ker := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  ext i
  obtain ⟨v, hv, rfl⟩ := hnat.onto i
  have h1 := hnat.equivariant g v hv
  have h2 : g.val v = v := congrArg Subtype.val (Equiv.ext_iff.1 hg ⟨v, hv⟩)
  rw [h2] at h1
  simp only [OneMemClass.coe_one, Perm.one_apply]
  exact congrArg Fin.val h1.symm

/-- `N < q³` from `N^α < q` and `α > 1/3` (eq. `scale-constraints`). -/
theorem lt_cube_of_rpow {N q : ℕ} {α : ℝ} (hα : 1 / 3 < α) (hq : (N : ℝ) ^ α < q) :
    N < q ^ 3 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : (0 : ℝ) < q := by
      have h0 : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg _) _
      linarith
    have : 0 < q := by exact_mod_cast this
    positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (N : ℝ) ^ α :=
    Real.rpow_le_rpow_of_exponent_le hN1 hα.le
  have h2 : (N : ℝ) ^ ((1 : ℝ) / 3) < q := h1.trans_lt hq
  have h3 : ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 < (q : ℝ) ^ 3 :=
    pow_lt_pow_left₀ h2 (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)] at h3
  norm_num at h3
  exact_mod_cast h3

/-- **The counter at a column step** (Section 7.1: "The one-promotion argument ensures that it
never becomes negative"; Lemma A.29). At a transitive `GiantStep` state of size `s ≤ N` in the
row case, with a column step, `h ≥ 1`, and the new state (new rows of degree `q`, counter
`h - 1`) satisfies the counter invariant. -/
theorem column_step_counter [Finite Ω] {α : ℝ} (hα : 1 / 3 < α) (S : State Ω C) (htr : S.Transitive)
    (hsN : S.size ≤ S.N) (L : GiantLabels S) (hrow : RowCase α S L) (I : ColumnStep S L) :
    1 ≤ S.h ∧ CounterInv S.G S.dom S.dom_inv (some ⟨L.q, I.rowPart, some I.cols⟩) (S.h - 1) S.N := by
  classical
  haveI : Fintype S.dom := Fintype.ofFinite _
  have hq4 := I.four_le
  -- The labels on the faithful image.
  have hkill := labels_kill I.natural
  have hsurj : Function.Surjective S.domHom.rangeRestrict := S.domHom.rangeRestrict_surjective
  have hkill' : S.domHom.rangeRestrict.ker ≤ L.π.ker := by
    rw [MonoidHom.ker_rangeRestrict]; exact hkill
  let π' : S.domGroup →* alternatingGroup (Fin L.q) :=
    GI.HomDescent.factor S.domHom.rangeRestrict hsurj L.π hkill'
  have hπ' : Function.Surjective π' :=
    GI.HomDescent.factor_surjective _ hsurj _ hkill' L.π_surj
  let lab : S.dom → Fin L.q := fun v => I.label v
  have heq : ∀ (g : S.domGroup) v, lab (g.val v) = (π' g).val (lab v) := by
    rintro ⟨_, g, rfl⟩ v
    have h1 : π' (S.domHom.rangeRestrict g) = L.π g :=
      GI.HomDescent.factor_apply _ hsurj _ hkill' g
    change I.label (S.domHom g v : Ω) = (π' (S.domHom.rangeRestrict g)).val (I.label v)
    rw [h1, State.domHom_apply]
    exact I.natural.equivariant g v v.2
  -- The new rows are a carrier, with `N < q³` and `q ≥ 4`.
  have hcarrier : RowCarrier S.G S.dom (⟨L.q, I.rowPart, some I.cols⟩ : RowRecord Ω) :=
    ⟨I.rowPart_inv, ⟨lab, fun i => by
      obtain ⟨v, hv, hvi⟩ := I.natural.onto i
      exact ⟨⟨v, hv⟩, hvi⟩, fun v w => by
        change (S.domKer fun v => I.label v).r v w ↔ _
        rw [State.domKer_r_of_mem _ v.2 w.2]⟩⟩
  have hcube : S.N < L.q ^ 3 := lt_cube_of_rpow hα hrow.1
  have hc := S.counter
  have hle := S.h_le
  -- The transitivity of the faithful image.
  have htr' : ∀ v w : S.dom, ∃ g ∈ S.domGroup, g v = w := by
    intro v w
    obtain ⟨g, hg, hgv⟩ := htr v v.2 w w.2
    exact ⟨S.domHom ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩, Subtype.ext hgv⟩
  rcases Nat.lt_trichotomy S.h 1 with h0 | h1 | h2
  · -- `h = 0` is impossible: `Alt(q)` would be a quotient of an action of cap `m < q`.
    exfalso
    have h0 : S.h = 0 := by omega
    obtain ⟨R, hR, hR4, hcap⟩ := hc.2 h0
    have hmq := hrow.2.2 R hR
    have := GI.SectionCaps.degree_le hcap (by omega) π' hπ'
    omega
  · -- `h = 1`: the promotion (Lemma A.29).
    refine ⟨h1.ge, fun h' => by omega, fun _ => ⟨_, rfl, hq4, ?_⟩⟩
    obtain ⟨R, hR, hcar, hN3, hR4⟩ := hc.1 h1
    have hmq := hrow.2.2 R hR
    obtain ⟨f, hf, hff⟩ := hcar.count
    let r : Setoid S.dom := Setoid.comap Subtype.val R.rows
    have hr : ∀ g ∈ S.domGroup, ∀ v w, r (g v) (g w) ↔ r v w := by
      rintro _ ⟨g, rfl⟩ v w
      exact hcar.inv g g.2 v w
    have hm : Nat.card (Quotient r) = R.m := by
      have e : Quotient r ≃ Fin R.m :=
        { toFun := Quotient.lift f fun a b h => (hff a b).1 h
          invFun := fun i => Quotient.mk r (Classical.choose (hf i))
          left_inv := fun a => Quotient.inductionOn a fun v => Quotient.sound <|
            (hff _ _).2 (Classical.choose_spec (hf (f v)))
          right_inv := fun i => Classical.choose_spec (hf i) }
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hD : Fintype.card S.dom < R.m ^ 3 := by
      have : Fintype.card S.dom = S.size := by
        rw [State.size, Nat.card_eq_fintype_card]
      omega
    exact promotion_cap S.domGroup htr' r hr hm lab π' hπ' heq hR4 hmq hD
  · -- `h = 2`: the new rows are a carrier.
    have h2' : S.h = 2 := by omega
    refine ⟨by omega, fun _ => ⟨_, rfl, hcarrier, hcube, hq4⟩, fun h' => by omega⟩

end ColumnStep

end GI.Algorithm
