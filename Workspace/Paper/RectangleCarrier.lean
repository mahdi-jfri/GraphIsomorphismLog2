import Workspace.DiagonalCarrier
import Workspace.SideParity
import Workspace.RectangleSides
import Workspace.EqualFibers
import Workspace.Parameters
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Paper statements: Lemma A.29 and Lemma A.30

Lemma A.29 (`lem:one-carrier-promotion`): `aw(G) ≤ q`
(`GI.Paper.lem_one_carrier_promotion`, via the tower bound
`lem_one_carrier_promotion_tower` and the numbers
`lem_one_carrier_promotion_numbers`); hereditary monotonicity
(`_hereditary`); the index split of the normal transpose (`_index_split`); the
cap-moment split (`_moment_split`).

Lemma A.30 (`lem:diagonal-carrier`): the data are `GI.Carrier.Data`; the diagonal
preimage `D̃` is `Data.lift`, with its diagonal natural action `Data.ideal`
onto `Alt(q)` and the exact cell quotient `Data.cellQuotient` on the points above
the chosen rows and `𝒞'`. The query group is `carrierGroup`, the query orbit
`carrierOrbit`. Proved: inherited action (`lem_diagonal_carrier_inherited`), one
orbit (`_orbit`), `u r |W| |R|` points (`_card`), exact pulled-back transporter
(`_exact`), constant strings (`_constant`), at most two calls by the parity twist
(`_parity_twist`), the exact ideal image: even total parity when the omitted
ideal labels number at most one, the full product otherwise (`_image_even`,
`_image_full`), the size ratios (`_ratio`, `_sharper_ratio`,
`_current_orbit_card`, `_q_le_m`).

Stage 2 (machine level, not stated here): "This is constructive without an arbitrary
subgroup-intersection oracle: generate the common kernel, lift generators of
`ker ψ` ... and lift the paired generators" (generation of `D̃`); "The quotient maps
and constructive membership give each lift"; computing the two string-isomorphism
calls and inducing the returned generators and representatives back
(`GI.TransportOutput.projectAnswer` is the mathematical content of the latter).
-/

namespace GI.Paper

open Equiv Equiv.Perm

/-! ### Lemma A.29 -/

section Promotion

variable {Ω : Type*} [Fintype Ω]

/-- **Lemma A.29, width bound** (`lem:one-carrier-promotion`). Let `G ≤ Sym(Ω)`
preserve a row partition (labels `row : Ω → Rw`) and a column partition
(labels `col : Ω → Cl`), acting on the labels through `α` and `γ`. If every
intersection of a row and a column has at most `u` points, then
`aw(G) ≤ max {|Cl|, |Rw|, u}`.

Paper: "The tower formed first by the `q` column blocks, then by their `m` row
intersections, and then by a complete local tower ... the iterated
wreath-product bound for alternating-section width". The upper bound needs only
that both partitions are invariant; the images `Alt(q)` and `Alt(m)` are not
used. -/
theorem lem_one_carrier_promotion_tower {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw]
    [Fintype Cl] [DecidableEq Cl] (G : Subgroup (Perm Ω))
    (row : Ω → Rw) (col : Ω → Cl) (α : G →* Perm Rw) (γ : G →* Perm Cl)
    (hrow : ∀ (g : G) x, row ((g : Perm Ω) x) = α g (row x))
    (hcol : ∀ (g : G) x, col ((g : Perm Ω) x) = γ g (col x)) (u : ℕ)
    (cells : ∀ r c, Fintype.card {x // (row x, col x) = (r, c)} ≤ u) :
    GI.SectionCaps.Cap G (max (Fintype.card Cl) (max (Fintype.card Rw) u)) := by
  classical
  -- Top of the tower: the action on the `q` column blocks.
  have top : GI.SectionCaps.Cap γ.range (Fintype.card Cl) :=
    GI.SectionCaps.subgroup GI.SectionCaps.permutations _
  -- Middle: the column kernel acts on rows; its kernel fixes every cell.
  let K := γ.ker
  let αK : K →* Perm Rw := α.comp K.subtype
  have middle : GI.SectionCaps.Cap αK.range (Fintype.card Rw) :=
    GI.SectionCaps.subgroup GI.SectionCaps.permutations _
  let ρ : αK.ker →* Perm Ω := G.subtype.comp (K.subtype.comp αK.ker.subtype)
  have faithful : Function.Injective ρ := by
    intro a b h
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  have bottom : GI.SectionCaps.Cap αK.ker u := by
    refine GI.Carrier.cap_of_fixed_labels ρ faithful (fun x => (row x, col x)) ?_ ?_
    · intro g x
      have hg : α g.val.val = 1 := g.property
      have hk : γ g.val.val = 1 := g.val.property
      change (row ((g.val.val : Perm Ω) x), col ((g.val.val : Perm Ω) x)) = (row x, col x)
      rw [hrow, hcol, hg, hk]
      rfl
    · intro b
      rw [Nat.card_eq_fintype_card]
      exact cells b.1 b.2
  have hK : GI.SectionCaps.Cap K (max u (Fintype.card Rw)) :=
    GI.SectionCaps.extension αK.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact bottom) middle
  have hG := GI.SectionCaps.extension γ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict]; exact hK) top
  intro U k hk q onto
  have := hG U k hk q onto
  omega

/-- **Lemma A.29, the numerical chain.** With `λ = N^α`, `1/3 < α < 1/2`,
`λ < m < q` and `m q u ≤ N`, the cell size satisfies
`u ≤ N/(mq) < N/λ² = N^{1-2α} < λ < q`. The strict steps need `N > 1`
(for `N ≤ 1` there is no `m > N^α ≥ ...` with room; we simply assume `1 < N`). -/
theorem lem_one_carrier_promotion_numbers {N α m q u : ℝ} (hN : 1 < N)
    (hα : 1 / 3 < α) (hα' : α < 1 / 2) (hm : N ^ α < m) (hmq : m < q)
    (hn : m * q * u ≤ N) :
    u ≤ N / (m * q) ∧ N / (m * q) < N / (N ^ α) ^ 2 ∧ N / (N ^ α) ^ 2 = N ^ (1 - 2 * α) ∧
      N ^ (1 - 2 * α) < N ^ α ∧ N ^ α < q := by
  have hN0 : 0 < N := by linarith
  have hlam : 0 < N ^ α := Real.rpow_pos_of_pos hN0 α
  have hm0 : 0 < m := lt_trans hlam hm
  have hq0 : 0 < q := lt_trans hm0 hmq
  have hmq0 : 0 < m * q := mul_pos hm0 hq0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hmq0]
    linarith
  · apply div_lt_div_of_pos_left hN0 (pow_pos hlam 2)
    rw [sq]
    exact mul_lt_mul'' hm (lt_trans hm hmq) hlam.le hlam.le
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Real.rpow_sub hN0, Real.rpow_one]
    norm_num
    rw [mul_comm]
  · exact Real.rpow_lt_rpow_of_exponent_lt hN (by linarith)
  · exact lt_trans hm hmq

/-- Consequence used in Lemma A.29: under the numerical hypotheses, `u < q`
and `m < q`, so `max {q, m, u} = q`. -/
theorem lem_one_carrier_promotion_cell_lt {N α m q u : ℝ} (hN : 1 < N)
    (hα : 1 / 3 < α) (hα' : α < 1 / 2) (hm : N ^ α < m) (hmq : m < q)
    (hn : m * q * u ≤ N) : u < q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := lem_one_carrier_promotion_numbers hN hα hα' hm hmq hn
  linarith

/-- **Lemma A.29** (`lem:one-carrier-promotion`), first claim: `aw(G) ≤ q`.
Here `G ≤ Sym(Ω)` preserves the old row partition (`m` blocks) and the natural
column partition (`q` blocks), every cell has `u` points, `λ = N^α < m < q`,
`1/3 < α < 1/2`, and `n = mqu ≤ N`. -/
theorem lem_one_carrier_promotion {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw]
    [Fintype Cl] [DecidableEq Cl] (G : Subgroup (Perm Ω))
    (row : Ω → Rw) (col : Ω → Cl) (α : G →* Perm Rw) (γ : G →* Perm Cl)
    (hrow : ∀ (g : G) x, row ((g : Perm Ω) x) = α g (row x))
    (hcol : ∀ (g : G) x, col ((g : Perm Ω) x) = γ g (col x)) (u : ℕ)
    (cells : ∀ r c, Fintype.card {x // (row x, col x) = (r, c)} = u)
    {N a : ℝ} (hN : 1 < N) (ha : 1 / 3 < a) (ha' : a < 1 / 2)
    (hm : N ^ a < Fintype.card Rw) (hmq : Fintype.card Rw < Fintype.card Cl)
    (hn : (Fintype.card Rw * Fintype.card Cl * u : ℕ) ≤ N) :
    GI.SectionCaps.Cap G (Fintype.card Cl) := by
  have hcap := lem_one_carrier_promotion_tower G row col α γ hrow hcol u
    (fun r c => (cells r c).le)
  have hmq' : Fintype.card Rw < Fintype.card Cl := by exact_mod_cast hmq
  have hu : (u : ℝ) < Fintype.card Cl :=
    lem_one_carrier_promotion_cell_lt hN ha ha' hm (by exact_mod_cast hmq)
      (by push_cast at hn; exact hn)
  have hu' : u < Fintype.card Cl := by exact_mod_cast hu
  intro U k hk q onto
  have := hcap U k hk q onto
  omega

/-- **Lemma A.29**, second claim: "Hereditary alternating-section width cannot
increase in subgroups, quotients, or their permutation images." -/
theorem lem_one_carrier_promotion_hereditary {G H : Type*} [Group G] [Group H] {b : ℕ}
    (hG : GI.SectionCaps.Cap G b) :
    (∀ U : Subgroup G, GI.SectionCaps.Cap U b) ∧
      ∀ f : G →* H, Function.Surjective f → GI.SectionCaps.Cap H b :=
  ⟨fun U => GI.SectionCaps.subgroup hG U, fun f hf => GI.SectionCaps.of_surjective f hf hG⟩

/-- **Lemma A.29, the index split** in the normal transpose:
`[L_i : L_{i-1}] = [L_i ∩ N : L_{i-1} ∩ N] [N L_i : N L_{i-1}]` for a normal
subgroup `N` of a finite group. Here `L' = L_{i-1} ≤ L = L_i`, and `N ⊔ L = N L`
since `N` is normal. -/
theorem lem_one_carrier_promotion_index_split {H : Type*} [Group H] [Finite H]
    (N L L' : Subgroup H) [N.Normal] (hL : L' ≤ L) :
    L'.relIndex L = (L' ⊓ N).relIndex (L ⊓ N) * (N ⊔ L').relIndex (N ⊔ L) := by
  have h1 : (L' ⊓ N).relIndex L = (L' ⊓ N).relIndex L' * L'.relIndex L :=
    (Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left hL).symm
  have h2 : (L' ⊓ N).relIndex L = (L' ⊓ N).relIndex (L ⊓ N) * (L ⊓ N).relIndex L :=
    (Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_inf_right N hL) inf_le_left).symm
  have h3 : (L' ⊓ N).relIndex L' = N.relIndex L' := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right N L'
  have h4 : (L ⊓ N).relIndex L = N.relIndex L := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right N L
  have h5 : N.relIndex (N ⊔ L) = N.relIndex L := Subgroup.relIndex_sup_left L N
  have h6 : N.relIndex (N ⊔ L') = N.relIndex L' := Subgroup.relIndex_sup_left L' N
  have h7 : N.relIndex (N ⊔ L') * (N ⊔ L').relIndex (N ⊔ L) = N.relIndex (N ⊔ L) :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le_sup_left hL N)
  have hne : N.relIndex L' ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  rw [h3] at h1
  rw [h4, ← h5, ← h7, h6] at h2
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
  calc N.relIndex L' * L'.relIndex L = (L' ⊓ N).relIndex (L ⊓ N) *
        (N.relIndex L' * (N ⊔ L').relIndex (N ⊔ L)) := h1.symm.trans h2
    _ = _ := by ring

/-- **Lemma A.29, the cap moment under splitting**: splitting a ratio `d = ab`
with cap `c` replaces `log d · log c` by `log a · log c + log b · log c`. -/
theorem lem_one_carrier_promotion_moment_split {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a * b) * Real.log c = Real.log a * Real.log c + Real.log b * Real.log c := by
  rw [Real.log_mul ha.ne' hb.ne', add_mul]

end Promotion

end GI.Paper

/-! ### Lemma A.30 -/

namespace GI.Carrier

open Equiv Equiv.Perm

/-- The data of Lemma A.30 (`lem:diagonal-carrier`).

* `G` acts on `Ω`; `π : G ↠ Alt(m) × Q` is the explicit quotient by `M = ker π`.
* The `M`-orbits are indexed by `[m] × 𝒞` through `label`, with the product action,
  and all have `u` points.
* `Q' ≤ Q` preserves `𝒞' ⊆ 𝒞`; `ψ : Q' ↠ Alt(q)`; the `ker ψ`-orbits on `𝒞'` are
  the `q` parts (`part`), each of size `r`, with the natural quotient action.
* `rows : [q] ↪ [m]` chooses `q` row labels ("Choose `q` row labels and identify
  them with `[q]`").

Transitivity of `G` and `9 ≤ q` are hypotheses of the paper's lemma that the
mathematical claims proved below do not use. -/
structure Data (G Ω Q 𝒞 : Type*) [Group G] [MulAction G Ω] [Group Q] [MulAction Q 𝒞]
    (m q : ℕ) where
  π : G →* alternatingGroup (Fin m) × Q
  π_onto : Function.Surjective π
  label : Ω → Fin m × 𝒞
  label_onto : Function.Surjective label
  label_equivariant : ∀ (g : G) (ω : Ω),
    label (g • ω) = ((π g).1 • (label ω).1, (π g).2 • (label ω).2)
  label_fibers : ∀ x y : Ω, label x = label y ↔ ∃ k : G, π k = 1 ∧ k • x = y
  u : ℕ
  label_card : ∀ l, Nat.card {ω // label ω = l} = u
  Q' : Subgroup Q
  C' : Set 𝒞
  preserved : ∀ z ∈ Q', ∀ c ∈ C', z • c ∈ C'
  ψ : Q' →* alternatingGroup (Fin q)
  ψ_onto : Function.Surjective ψ
  part : C' → Fin q
  part_onto : Function.Surjective part
  part_equivariant : ∀ (z : Q') (c : C'),
    part ⟨(z : Q) • c.val, preserved z z.property c c.property⟩ = ψ z • part c
  part_fibers : ∀ c c' : C', part c = part c' → ∃ z : Q', ψ z = 1 ∧ (z : Q) • c.val = c'.val
  r : ℕ
  part_card : ∀ j, Nat.card {c : C' // part c = j} = r
  rows : Fin q ↪ Fin m

variable {G Ω Q 𝒞 : Type*} [Group G] [MulAction G Ω] [Group Q] [MulAction Q 𝒞] {m q : ℕ}
variable (d : Data G Ω Q 𝒞 m q)

namespace Data

/-- `Alt(q)` placed on the chosen rows, fixing the other rows. -/
noncomputable def embedAlt : alternatingGroup (Fin q) →* alternatingGroup (Fin m) :=
  ((extendDomainHom d.rows.toEquivRange).comp (alternatingGroup (Fin q)).subtype).codRestrict
    (alternatingGroup (Fin m)) (fun a => by
      classical
      change sign (extendDomain (a : Perm (Fin q)) d.rows.toEquivRange) = 1
      rw [sign_extendDomain]
      exact a.property)

theorem embedAlt_apply (a : alternatingGroup (Fin q)) (i : Fin q) :
    (d.embedAlt a : Perm (Fin m)) (d.rows i) = d.rows ((a : Perm (Fin q)) i) :=
  viaFintypeEmbedding_apply_image (a : Perm (Fin q)) d.rows i

/-- The displayed subgroup `D = {(ψ(z), z) : z ∈ Q'}` of `Alt(q) × Q'`, placed in
`Alt(m) × Q`. -/
noncomputable def diag : Subgroup (alternatingGroup (Fin m) × Q) :=
  ((d.embedAlt.comp d.ψ).prod d.Q'.subtype).range

/-- The full preimage `D̃` of `D` in `G`. -/
noncomputable def lift : Subgroup G := d.diag.comap d.π

theorem mem_lift_iff (g : G) :
    g ∈ d.lift ↔ ∃ z : d.Q', d.π g = (d.embedAlt (d.ψ z), (z : Q)) := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩

theorem second_mem (g : d.lift) : (d.π g.val).2 ∈ d.Q' := by
  obtain ⟨z, hz⟩ := (d.mem_lift_iff g.val).mp g.property
  rw [hz]
  exact z.property

/-- The column element `z ∈ Q'` of an element of `D̃`. -/
def column (g : d.lift) : d.Q' := ⟨(d.π g.val).2, d.second_mem g⟩

theorem first_eq (g : d.lift) : (d.π g.val).1 = d.embedAlt (d.ψ (d.column g)) := by
  obtain ⟨z, hz⟩ := (d.mem_lift_iff g.val).mp g.property
  have hc : d.column g = z := Subtype.ext (by simp [column, hz])
  rw [hc, hz]

/-- The diagonal natural alternating action of `D̃` on `[q]`. -/
noncomputable def ideal : d.lift →* alternatingGroup (Fin q) where
  toFun g := d.ψ (d.column g)
  map_one' := by
    have : d.column 1 = 1 := Subtype.ext (by simp [column])
    rw [this, map_one]
  map_mul' g h := by
    have : d.column (g * h) = d.column g * d.column h := Subtype.ext (by simp [column])
    rw [this, map_mul]

theorem ideal_onto : Function.Surjective d.ideal := by
  intro a
  obtain ⟨z, rfl⟩ := d.ψ_onto a
  obtain ⟨g, hg⟩ := d.π_onto (d.embedAlt (d.ψ z), (z : Q))
  refine ⟨⟨g, (d.mem_lift_iff g).mpr ⟨z, hg⟩⟩, ?_⟩
  change d.ψ (d.column _) = d.ψ z
  congr 1
  exact Subtype.ext (by simp [column, hg])

/-- The physical points above the chosen rows and the column set `𝒞'`. -/
abbrev Points := {ω : Ω // (d.label ω).1 ∈ Set.range d.rows ∧ (d.label ω).2 ∈ d.C'}

theorem smul_mem (g : d.lift) (x : d.Points) :
    (d.label (g.val • x.val)).1 ∈ Set.range d.rows ∧ (d.label (g.val • x.val)).2 ∈ d.C' := by
  obtain ⟨⟨i, hi⟩, hc⟩ := x.property
  rw [d.label_equivariant]
  refine ⟨⟨(d.ψ (d.column g) : Perm (Fin q)) i, ?_⟩, ?_⟩
  · change d.rows _ = (d.π g.val).1 • (d.label x.val).1
    rw [d.first_eq, ← hi]
    exact (d.embedAlt_apply _ i).symm
  · exact d.preserved _ (d.second_mem g) _ hc

instance : MulAction d.lift d.Points where
  smul g x := ⟨g.val • x.val, d.smul_mem g x⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g.val h.val x.val)

theorem smul_val (g : d.lift) (x : d.Points) : (g • x).val = g.val • x.val := rfl

/-- The row index in `[q]` of a point. -/
noncomputable def rowIndex (x : d.Points) : Fin q := Classical.choose x.property.1

theorem rows_rowIndex (x : d.Points) : d.rows (d.rowIndex x) = (d.label x.val).1 :=
  Classical.choose_spec x.property.1

/-- The column part in `[q]` of a point. -/
def colPart (x : d.Points) : Fin q := d.part ⟨(d.label x.val).2, x.property.2⟩

theorem part_congr {c c' : d.C'} (h : c.val = c'.val) : d.part c = d.part c' :=
  congrArg d.part (Subtype.ext h)

/-- The diagonal row--column-part cell of a point. -/
noncomputable def cell (x : d.Points) : Fin q × Fin q := (d.rowIndex x, d.colPart x)

theorem cell_equivariant (g : d.lift) (x : d.Points) :
    d.cell (g • x) = d.ideal g • d.cell x := by
  apply Prod.ext
  · apply d.rows.injective
    change d.rows (d.rowIndex (g • x)) = d.rows ((d.ψ (d.column g) : Perm (Fin q)) (d.rowIndex x))
    rw [d.rows_rowIndex, smul_val, d.label_equivariant, d.first_eq, ← d.embedAlt_apply,
      d.rows_rowIndex]
    rfl
  · show d.colPart (g • x) = d.ψ (d.column g) • d.colPart x
    rw [colPart, colPart, ← d.part_equivariant]
    apply d.part_congr
    change (d.label (g.val • x.val)).2 = _
    rw [d.label_equivariant]
    rfl

theorem cell_kernel_fibers (x y : d.Points) :
    d.cell x = d.cell y ↔ ∃ k : d.lift, d.ideal k = 1 ∧ k • x = y := by
  constructor
  · intro h
    have hrow : (d.label x.val).1 = (d.label y.val).1 := by
      rw [← d.rows_rowIndex, ← d.rows_rowIndex, show d.rowIndex x = d.rowIndex y from
        congrArg Prod.fst h]
    -- "the latter subgroup is transitive on its `r` column labels"
    obtain ⟨z, hz1, hzc⟩ := d.part_fibers ⟨_, x.property.2⟩ ⟨_, y.property.2⟩
      (congrArg Prod.snd h)
    obtain ⟨g, hg⟩ := d.π_onto (1, (z : Q))
    have hgD : g ∈ d.lift := (d.mem_lift_iff g).mpr ⟨z, by rw [hg, hz1, map_one]⟩
    -- "and `M` is transitive on the `u` points of each cell"
    have hlab : d.label (g • x.val) = d.label y.val := by
      rw [d.label_equivariant, hg]
      exact Prod.ext (by simpa using hrow) hzc
    obtain ⟨k, hk1, hky⟩ := (d.label_fibers _ _).mp hlab
    have hkD : k ∈ d.lift := (d.mem_lift_iff k).mpr ⟨1, by rw [hk1, map_one, map_one]; rfl⟩
    refine ⟨⟨k, hkD⟩ * ⟨g, hgD⟩, ?_, Subtype.ext ?_⟩
    · rw [map_mul]
      have h1 : d.ideal ⟨k, hkD⟩ = 1 := by
        change d.ψ (d.column _) = 1
        have : d.column ⟨k, hkD⟩ = 1 := Subtype.ext (by simp [column, hk1])
        rw [this, map_one]
      have h2 : d.ideal ⟨g, hgD⟩ = 1 := by
        change d.ψ (d.column _) = 1
        have : d.column ⟨g, hgD⟩ = z := Subtype.ext (by simp [column, hg])
        rw [this, hz1]
      rw [h1, h2, mul_one]
    · change (k * g) • x.val = y.val
      rw [mul_smul, hky]
  · rintro ⟨k, hk, rfl⟩
    rw [d.cell_equivariant, hk, one_smul]

variable [Finite Ω] [Fintype 𝒞]

/-- Each diagonal cell has exactly `u r` points: `r` column labels, each with an
`M`-orbit of `u` points. -/
theorem cell_card (i j : Fin q) : Nat.card {x : d.Points // d.cell x = (i, j)} = d.u * d.r := by
  classical
  -- the cell is the union of the `M`-orbits over `(rows i, c)` with `part c = j`
  let S : Set (Fin m × 𝒞) := {l | l.1 = d.rows i ∧ ∃ h : l.2 ∈ d.C', d.part ⟨l.2, h⟩ = j}
  have e1 : {x : d.Points // d.cell x = (i, j)} ≃ {ω : Ω // d.label ω ∈ S} :=
    { toFun := fun x => ⟨x.val.val, by
        have h := x.property
        refine ⟨?_, x.val.property.2, congrArg Prod.snd h⟩
        rw [← d.rows_rowIndex, show d.rowIndex x.val = i from congrArg Prod.fst h]⟩
      invFun := fun ω => ⟨⟨ω.val, ⟨i, ω.property.1.symm⟩, ω.property.2.1⟩, by
        apply Prod.ext
        · apply d.rows.injective
          change d.rows (d.rowIndex _) = _
          rw [d.rows_rowIndex]
          exact ω.property.1
        · exact ω.property.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun ω => rfl }
  have e2 : S ≃ {c : d.C' // d.part c = j} :=
    { toFun := fun l => ⟨⟨l.val.2, l.property.2.1⟩, l.property.2.2⟩
      invFun := fun c => ⟨(d.rows i, c.val.val), rfl, c.val.property, c.property⟩
      left_inv := fun l => Subtype.ext (Prod.ext l.property.1.symm rfl)
      right_inv := fun c => rfl }
  have hS : Nat.card {ω : Ω // d.label ω ∈ S} = Nat.card S * d.u := by
    have := Fintype.ofFinite Ω
    have h := Fintype.card_congr (GI.fiberSubsetEquiv d.label S)
    rw [Fintype.card_sigma] at h
    have hc : ∀ z : S, Fintype.card {v // d.label v = z.1} = d.u := by
      intro z
      rw [← Nat.card_eq_fintype_card]
      exact d.label_card z.1
    simp_rw [hc] at h
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h]
  rw [Nat.card_congr e1, hS, Nat.card_congr e2, d.part_card, mul_comm]

/-- The diagonal cell map as an exact kernel quotient of the action of `D̃`. -/
noncomputable def cellQuotient :
    GI.StabilizerQuotient.KernelQuotient d.ideal d.Points (Fin q × Fin q) where
  map := d.cell
  onto := by
    rintro ⟨i, j⟩
    obtain ⟨c, hc⟩ := d.part_onto j
    obtain ⟨ω, hω⟩ := d.label_onto (d.rows i, c.val)
    have hp : (d.label ω).1 ∈ Set.range d.rows ∧ (d.label ω).2 ∈ d.C' := by
      rw [hω]; exact ⟨⟨i, rfl⟩, c.property⟩
    refine ⟨⟨ω, hp⟩, Prod.ext ?_ ?_⟩
    · apply d.rows.injective
      change d.rows (d.rowIndex _) = _
      rw [d.rows_rowIndex, hω]
    · change d.part _ = j
      rw [← hc]
      apply d.part_congr
      simp [hω]
  equivariant := d.cell_equivariant
  kernel_fibers := d.cell_kernel_fibers
  equal_fibers := by
    rintro ⟨i, j⟩ ⟨i', j'⟩
    rw [d.cell_card, d.cell_card]

end Data

end GI.Carrier

namespace GI.Carrier

open Equiv Equiv.Perm GI.Rectangle

variable {q : ℕ} {W R : Finset (Fin q)}

/-- The rectangle `W × R` inside the diagonal cells `[q] × [q]`. -/
def crossEmbedding : (W × R) ↪ Fin q × Fin q where
  toFun p := (p.1.val, p.2.val)
  inj' _ _ h := Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

theorem crossEmbedding_move (g : permitted W R) (p : W × R) :
    crossEmbedding (rectangleAction g p) = (g : alternatingGroup (Fin q)) • crossEmbedding p :=
  rfl

theorem card_range_crossEmbedding :
    Nat.card (Set.range (crossEmbedding (W := W) (R := R))) = W.card * R.card := by
  rw [← Nat.card_congr (Equiv.ofInjective _ crossEmbedding.injective)]
  simp [Nat.card_eq_fintype_card]

/-- "after prescribing the images of one left and one right point, an odd
transposition of two remaining left points corrects parity whenever needed,
since `|W| ≥ 3`": the permitted group is transitive on `W × R`. -/
theorem cross_transitive (hd : Disjoint W R) (hW : 3 ≤ W.card)
    (a : Fin q × Fin q) (ha : a ∈ Set.range (crossEmbedding (W := W) (R := R)))
    (b : Fin q × Fin q) (hb : b ∈ Set.range (crossEmbedding (W := W) (R := R))) :
    ∃ g : permitted W R, (g : alternatingGroup (Fin q)) • a = b := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨p', rfl⟩ := hb
  obtain ⟨g, h1, h2⟩ := exists_permitted_pair_map hd hW p.1.property p'.1.property
    p.2.property p'.2.property
  exact ⟨g, Prod.ext h1 h2⟩

theorem cross_preserved (g : permitted W R) (a : Fin q × Fin q)
    (ha : a ∈ Set.range (crossEmbedding (W := W) (R := R))) :
    (g : alternatingGroup (Fin q)) • a ∈ Set.range (crossEmbedding (W := W) (R := R)) := by
  obtain ⟨p, rfl⟩ := ha
  exact ⟨rectangleAction g p, crossEmbedding_move g p⟩

/-- Every pair of side permutations with even total parity is induced by a
permitted even permutation of `[q]` (it acts as `σ` on `W`, `τ` on `R`, and
trivially elsewhere). -/
theorem even_total_parity_permitted (hd : Disjoint W R) (σ : Perm W) (τ : Perm R)
    (h : sign σ * sign τ = 1) :
    ∃ g : permitted W R, rectangleAction g = GI.ProductAction.hom (σ, τ) := by
  classical
  let gp : Perm (Fin q) := ofSubtype σ * ofSubtype τ
  have hW : ∀ b, gp b ∈ W ↔ b ∈ W := by
    intro b
    change ofSubtype σ (ofSubtype τ b) ∈ W ↔ b ∈ W
    rw [show ofSubtype σ (ofSubtype τ b) ∈ W ↔ ofSubtype τ b ∈ W from
      ofSubtype_apply_mem_iff_mem σ _]
    by_cases hb : b ∈ R
    · rw [ofSubtype_apply_of_mem τ hb]
      have h1 : ((τ ⟨b, hb⟩ : R) : Fin q) ∉ W :=
        fun hw => Finset.disjoint_left.mp hd hw (τ ⟨b, hb⟩).property
      have h2 : b ∉ W := fun hw => Finset.disjoint_left.mp hd hw hb
      simp [h1, h2]
    · rw [ofSubtype_apply_of_not_mem τ hb]
  have hR : ∀ b, gp b ∈ R ↔ b ∈ R := by
    intro b
    change ofSubtype σ (ofSubtype τ b) ∈ R ↔ b ∈ R
    by_cases hb : b ∈ W
    · have h2 : b ∉ R := fun hr => Finset.disjoint_left.mp hd hb hr
      rw [ofSubtype_apply_of_not_mem τ h2, ofSubtype_apply_of_mem σ hb]
      have h1 : ((σ ⟨b, hb⟩ : W) : Fin q) ∉ R :=
        fun hr => Finset.disjoint_left.mp hd (σ ⟨b, hb⟩).property hr
      simp [h1, h2]
    · have h3 : ofSubtype τ b ∉ W := by
        intro hw
        by_cases hbR : b ∈ R
        · rw [ofSubtype_apply_of_mem τ hbR] at hw
          exact Finset.disjoint_left.mp hd hw (τ ⟨b, hbR⟩).property
        · rw [ofSubtype_apply_of_not_mem τ hbR] at hw
          exact hb hw
      rw [ofSubtype_apply_of_not_mem σ h3]
      exact ofSubtype_apply_mem_iff_mem τ b
  have hsign : gp ∈ alternatingGroup (Fin q) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_ofSubtype, sign_ofSubtype, h]
  have hside : gp ∈ sides W R :=
    ⟨MulAction.mem_stabilizer_set.mpr (fun b => by simpa using hW b),
     MulAction.mem_stabilizer_set.mpr (fun b => by simpa using hR b)⟩
  refine ⟨⟨⟨gp, hsign⟩, hside⟩, ?_⟩
  refine Equiv.ext fun p => Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · change ofSubtype σ (ofSubtype τ p.1.val) = (σ p.1).val
    have h2 : p.1.val ∉ R := fun hr => Finset.disjoint_left.mp hd p.1.property hr
    rw [ofSubtype_apply_of_not_mem τ h2, ofSubtype_apply_of_mem σ p.1.property]
  · change ofSubtype σ (ofSubtype τ p.2.val) = (τ p.2).val
    rw [ofSubtype_apply_of_mem τ p.2.property]
    have h1 : ((τ ⟨p.2.val, p.2.property⟩ : R) : Fin q) ∉ W :=
      fun hw => Finset.disjoint_left.mp hd hw (τ _).property
    rw [ofSubtype_apply_of_not_mem σ h1]

end GI.Carrier

namespace GI.Paper

open Equiv Equiv.Perm GI.Carrier GI.Rectangle

section DiagonalCarrier

variable {G Ω Q 𝒞 : Type*} [Group G] [MulAction G Ω] [Group Q] [MulAction Q 𝒞] {m q : ℕ}
variable (d : Data G Ω Q 𝒞 m q) [Finite Ω] [Fintype 𝒞] {W R : Finset (Fin q)}

/-- The group of Lemma A.30's query: "Restrict further to the inverse image of
the setwise stabilizer of `W` and `R` in `Alt(q)`", inside the diagonal
preimage `D̃ = d.lift ≤ G`. -/
noncomputable abbrev carrierGroup (d : Data G Ω Q 𝒞 m q) (W R : Finset (Fin q)) : Subgroup d.lift :=
  (permitted W R).comap d.ideal

/-- The physical points above `W × R` ("select the physical orbit above `W × R`"). -/
abbrev carrierOrbit (d : Data G Ω Q 𝒞 m q) [Finite Ω] [Fintype 𝒞] (W R : Finset (Fin q)) :=
  GI.EmbeddedQuotient.Physical d.cellQuotient (crossEmbedding (W := W) (R := R))

/-- The ideal cell of a point of the query orbit, in `W × R`. -/
noncomputable abbrev carrierMap (d : Data G Ω Q 𝒞 m q) [Finite Ω] [Fintype 𝒞]
    (W R : Finset (Fin q)) : carrierOrbit d W R → W × R :=
  GI.EmbeddedQuotient.map d.cellQuotient crossEmbedding

/-- The action of the query group on the query orbit. -/
noncomputable abbrev carrierAction (d : Data G Ω Q 𝒞 m q) [Finite Ω] [Fintype 𝒞] (W R : Finset (Fin q)) :
    carrierGroup d W R →* Perm (carrierOrbit d W R) :=
  GI.EmbeddedQuotient.action d.cellQuotient crossEmbedding (permitted W R) rectangleAction
    crossEmbedding_move

/-- **Lemma A.30, the query is an inherited subgroup-orbit action.** The query
group is a subgroup of `G` (through `D̃ ≤ G`) and acts on its points by the
original action of `G`: "The preimage ... is a genuine subgroup orbit of the
original physical permutation representation." -/
theorem lem_diagonal_carrier_inherited (g : carrierGroup d W R) (x : carrierOrbit d W R) :
    (carrierAction d W R g x).val.val = (g.val.val : G) • x.val.val := rfl

/-- **Lemma A.30, one orbit.** The points above `W × R` form one orbit of the
query group. "That kernel is transitive on every row--column-part fiber" and
"This image is transitive on `W × R`". -/
theorem lem_diagonal_carrier_orbit (hd : Disjoint W R) (hW : 3 ≤ W.card)
    (x : d.Points) (hx : d.cell x ∈ Set.range (crossEmbedding (W := W) (R := R))) :
    {y : d.Points | d.cell y ∈ Set.range (crossEmbedding (W := W) (R := R))} =
      MulAction.orbit (carrierGroup d W R) x :=
  d.cellQuotient.preimage_eq_orbit d.ideal_onto (permitted W R) _
    (fun p w hw => cross_preserved p w hw) (fun a ha b hb => cross_transitive hd hW a ha b hb) x hx

/-- **Lemma A.30, the size.** "The preimage has exactly `u r |W| |R|` points." -/
theorem lem_diagonal_carrier_card :
    Nat.card (carrierOrbit d W R) = d.u * d.r * (W.card * R.card) := by
  classical
  haveI : Fintype d.Points := Fintype.ofFinite _
  rcases isEmpty_or_nonempty (Fin q) with hq | hne
  · have hW : W = ∅ := Finset.eq_empty_of_isEmpty W
    haveI : IsEmpty (carrierOrbit d W R) := ⟨fun x => hq.elim (d.cell x.val).1⟩
    rw [Nat.card_of_isEmpty, hW, Finset.card_empty]
    ring
  · obtain ⟨a⟩ := hne
    have h := d.cellQuotient.subset_count (Set.range (crossEmbedding (W := W) (R := R))) (a, a)
    rw [card_range_crossEmbedding] at h
    have hc : Nat.card {x : d.Points // d.cellQuotient.map x = (a, a)} = d.u * d.r :=
      d.cell_card a a
    rw [hc] at h
    rw [h]
    ring

/-- **Lemma A.30, exact pulled-back query.** "Pull the rectangle color string
back constantly on the known fibers. String isomorphisms in this physical action
induce precisely the rectangle isomorphisms in its ideal image." Projecting the
entire physical transporter (through the faithful image of the query group)
gives the entire permitted rectangle transporter, including the empty case. -/
theorem lem_diagonal_carrier_exact {C : Type*} (x y : W × R → C) :
    GI.EmbeddedQuotient.permittedProjection d.cellQuotient crossEmbedding (permitted W R)
        rectangleAction crossEmbedding_move ''
      {p : (carrierAction d W R).range |
        Transports (x ∘ carrierMap d W R) (y ∘ carrierMap d W R) p.val} =
      {p : (rectangleAction (W := W) (R := R)).range | Transports x y p.val} :=
  GI.EmbeddedQuotient.exact_permitted_transporter d.cellQuotient crossEmbedding (permitted W R)
    rectangleAction crossEmbedding_move d.ideal_onto x y

/-- **Lemma A.30**: the pulled-back strings are constant on the fibers over the
ideal cells ("The input strings are constant on the known fibers"). -/
theorem lem_diagonal_carrier_constant {C : Type*} (x : W × R → C) (a b : carrierOrbit d W R)
    (h : d.cell a.val = d.cell b.val) :
    (x ∘ carrierMap d W R) a = (x ∘ carrierMap d W R) b := by
  apply congrArg x
  apply crossEmbedding.injective
  rw [GI.EmbeddedQuotient.embed_map, GI.EmbeddedQuotient.embed_map]
  exact h

/-- **Lemma A.30, the current physical orbit.** The points above `[m] × 𝒞'`
number `|Ω'| = m (q r) u`: "There are `mqr` cells in the current physical orbit",
each an `M`-orbit of `u` points. -/
theorem lem_diagonal_carrier_current_orbit_card :
    Nat.card {ω : Ω // (d.label ω).2 ∈ d.C'} = m * (q * d.r) * d.u := by
  classical
  haveI := Fintype.ofFinite Ω
  let S : Set (Fin m × 𝒞) := {l | l.2 ∈ d.C'}
  have hS : Nat.card {ω : Ω // d.label ω ∈ S} = Nat.card S * d.u := by
    have h := Fintype.card_congr (GI.fiberSubsetEquiv d.label S)
    rw [Fintype.card_sigma] at h
    have hc : ∀ z : S, Fintype.card {v // d.label v = z.1} = d.u := by
      intro z
      rw [← Nat.card_eq_fintype_card]
      exact d.label_card z.1
    simp_rw [hc] at h
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h]
  have eS : S ≃ Fin m × d.C' :=
    { toFun := fun l => (l.val.1, ⟨l.val.2, l.property⟩)
      invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
      left_inv := fun l => rfl
      right_inv := fun p => rfl }
  have hC : Nat.card d.C' = q * d.r := by
    have h := Fintype.card_congr (Equiv.sigmaFiberEquiv d.part)
    rw [Fintype.card_sigma] at h
    have hc : ∀ j, Fintype.card {c // d.part c = j} = d.r := by
      intro j
      rw [← Nat.card_eq_fintype_card]
      exact d.part_card j
    simp_rw [hc] at h
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin] at h
    rw [Nat.card_eq_fintype_card, ← h]
  rw [show Nat.card {ω : Ω // (d.label ω).2 ∈ d.C'} = Nat.card {ω : Ω // d.label ω ∈ S} from rfl,
    hS, Nat.card_congr eS, Nat.card_prod, hC, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The ideal image of the query group in `Sym W × Sym R`: an element of the query
group acts on the ideal labels by `ideal`, which lies in the permitted group
`(Sym W × Sym R × Sym Y) ∩ Alt(q)`, and then on the two sides. -/
noncomputable abbrev carrierSides (d : Data G Ω Q 𝒞 m q) (W R : Finset (Fin q)) :
    carrierGroup d W R →* Perm W × Perm R :=
  sideAction.comp ((d.ideal.comp (carrierGroup d W R).subtype).codRestrict (permitted W R)
    (fun g => g.property))

omit [Finite Ω] [Fintype 𝒞] in
/-- The ideal image of the query group is the side image of the whole permitted group:
`ideal` maps `D̃` onto `Alt(q)`, so the query group maps onto the permitted group. -/
theorem carrierSides_range :
    (carrierSides d W R).range = (sideAction (W := W) (R := R)).range := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨h, rfl⟩
    obtain ⟨g, hg⟩ := d.ideal_onto (h : alternatingGroup (Fin q))
    have hmem : g ∈ carrierGroup d W R := by
      change d.ideal g ∈ permitted W R
      rw [hg]
      exact h.property
    refine ⟨⟨g, hmem⟩, ?_⟩
    change sideAction ⟨d.ideal g, _⟩ = sideAction h
    congr 1
    exact Subtype.ext hg

omit [Finite Ω] [Fintype 𝒞] in
/-- **Lemma A.30, the exact ideal image, `|Y| ≤ 1`.** With `Y = [q] \ (W ∪ R)` the
omitted ideal labels, if `|Y| ≤ 1` the ideal image of the query group is "the
even-total-parity subgroup of `Sym(W) × Sym(R)`". -/
theorem lem_diagonal_carrier_image_even (hd : Disjoint W R) (hY : (W ∪ R)ᶜ.card ≤ 1)
    (p : Perm W × Perm R) :
    p ∈ (carrierSides d W R).range ↔ sign p.1 * sign p.2 = 1 := by
  rw [carrierSides_range]
  exact sideAction_mem_range_iff hd hY p

omit [Finite Ω] [Fintype 𝒞] in
/-- **Lemma A.30, the exact ideal image, `|Y| ≥ 2`.** If the omitted ideal labels
number at least two, they "can absorb parity", and the ideal image is the full
product `Sym(W) × Sym(R)`. -/
theorem lem_diagonal_carrier_image_full (hd : Disjoint W R) (hY : 2 ≤ (W ∪ R)ᶜ.card) :
    (carrierSides d W R).range = ⊤ := by
  rw [carrierSides_range]
  exact sideAction_range_eq_top hd hY

omit [Finite Ω] [Fintype 𝒞] in
/-- The chosen rows give `q ≤ m`, as Lemma A.30 assumes. -/
theorem lem_diagonal_carrier_q_le_m (d : Data G Ω Q 𝒞 m q) : q ≤ m := by
  simpa using Fintype.card_le_of_embedding d.rows

end DiagonalCarrier

/-- **Lemma A.30, the parity twist ("at most two string-isomorphism calls").**
Let `t` act by a transposition `(a b)` of two left labels, an odd-total-parity
rectangle permutation. The full transporter under `Sym(W) × Sym(R)` is the union
of the permitted transporter and `t` times the permitted transporter to the
twisted target `y ∘ t`: "If the ideal image has index two, solve its second coset
by precomposing the target rectangle colors with a fixed odd-total-parity
rectangle permutation." The permitted image contains every even-total-parity pair
(`GI.Carrier.even_total_parity_permitted`), which is what the proof uses. -/
theorem lem_diagonal_carrier_parity_twist {q : ℕ} {W R : Finset (Fin q)} (hd : Disjoint W R)
    {a b : Fin q} (ha : a ∈ W) (hb : b ∈ W) (hab : a ≠ b) {C : Type*} (x y : W × R → C) :
    let t : Perm (W × R) := GI.ProductAction.hom (swap ⟨a, ha⟩ ⟨b, hb⟩, 1)
    {p | p ∈ (GI.ProductAction.hom (L := W) (R := R)).range ∧ Transports x y p} =
      {p | p ∈ (rectangleAction (W := W) (R := R)).range ∧ Transports x y p} ∪
        (fun p => t * p) ''
          {p | p ∈ (rectangleAction (W := W) (R := R)).range ∧ Transports x (y ∘ t) p} := by
  intro t
  have hab' : (⟨a, ha⟩ : W) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
  have htt : t * t = 1 := by
    change GI.ProductAction.hom _ * GI.ProductAction.hom _ = 1
    rw [← map_mul, Prod.mk_mul_mk, swap_mul_self, mul_one]
    exact map_one _
  have permitted_le : ∀ p ∈ (rectangleAction (W := W) (R := R)).range,
      p ∈ (GI.ProductAction.hom (L := W) (R := R)).range := by
    rintro p ⟨g, rfl⟩
    exact ⟨sideAction g, product_side g⟩
  ext p
  constructor
  · rintro ⟨⟨⟨σ, τ⟩, rfl⟩, hp⟩
    by_cases heven : sign σ * sign τ = 1
    · obtain ⟨g, hg⟩ := GI.Carrier.even_total_parity_permitted hd σ τ heven
      exact Or.inl ⟨⟨g, hg⟩, hp⟩
    · have hodd : sign (swap (⟨a, ha⟩ : W) ⟨b, hb⟩ * σ) * sign τ = 1 := by
        rw [Perm.sign_mul, sign_swap hab']
        rcases Int.units_eq_one_or (sign σ * sign τ) with h | h
        · exact absurd h heven
        · rw [mul_assoc, h]; rfl
      obtain ⟨g, hg⟩ := GI.Carrier.even_total_parity_permitted hd _ τ hodd
      refine Or.inr ⟨t * GI.ProductAction.hom (σ, τ), ⟨⟨g, ?_⟩, ?_⟩, ?_⟩
      · rw [hg]
        change _ = GI.ProductAction.hom _ * GI.ProductAction.hom _
        rw [← map_mul]
        rfl
      · intro v
        change y (t (t (GI.ProductAction.hom (σ, τ) v))) = x v
        rw [← Perm.mul_apply t t, htt, Perm.one_apply]
        exact hp v
      · change t * (t * _) = _
        rw [← mul_assoc, htt, one_mul]
  · rintro (⟨hP, hp⟩ | ⟨p', ⟨hP, hp⟩, rfl⟩)
    · exact ⟨permitted_le p hP, hp⟩
    · refine ⟨(GI.ProductAction.hom (L := W) (R := R)).range.mul_mem ⟨_, rfl⟩ (permitted_le p' hP),
        ?_⟩
      intro v
      exact hp v

/-- **Lemma A.30, the size ratio.** With `|Ω'| = m q r u` points in the current
physical orbit `[m] × 𝒞'`, and `W, R ⊆ [q]` disjoint, `|W| |R| ≤ q²/4` gives
`u r |W| |R| ≤ (q/(4m)) |Ω'| ≤ |Ω'|/4` (the last step uses `q ≤ m`). Integer
forms: `4m · u r |W| |R| ≤ q |Ω'|` and `4 u r |W| |R| ≤ |Ω'|`. -/
theorem lem_diagonal_carrier_ratio {m q u r : ℕ} {W R : Finset (Fin q)} (hd : Disjoint W R)
    (hqm : q ≤ m) :
    4 * m * (u * r * (W.card * R.card)) ≤ q * (m * q * r * u) ∧
      4 * (u * r * (W.card * R.card)) ≤ m * q * r * u := by
  have hsum : W.card + R.card ≤ q := by
    rw [← Finset.card_union_of_disjoint hd]
    exact (Finset.card_le_univ _).trans (by simp)
  have hsq : 4 * (W.card * R.card) ≤ q * q := by
    have h1 := Nat.mul_le_mul hsum hsum
    zify at h1 ⊢
    nlinarith [sq_nonneg ((W.card : ℤ) - R.card)]
  constructor
  · nlinarith [Nat.zero_le (m * u * r)]
  · have : 4 * (W.card * R.card) ≤ m * q := hsq.trans (Nat.mul_le_mul_right q hqm)
    nlinarith [Nat.zero_le (u * r)]

/-- **Lemma A.30, the sharper ratio.** If `W, R ⊆ C ⊆ [q]`, `|W| ≥ η|C|`,
`|R| ≤ |C| - |W|` and `1/2 ≤ η ≤ 1`, then
`u r |W| |R| ≤ (η(1-η)|C|²/(mq)) · |Ω'|` with `|Ω'| = m q r u`, and
`η(1-η)|C|²/(mq) ≤ η(1-η) q/m`. -/
theorem lem_diagonal_carrier_sharper_ratio {m q u r w s c η : ℝ} (hm : 0 < m) (hq : 0 < q)
    (hu : 0 ≤ u) (hr : 0 ≤ r) (hc : 0 ≤ c) (hcq : c ≤ q) (hη : 1 / 2 ≤ η) (hη1 : η ≤ 1)
    (hw : η * c ≤ w) (hs : s ≤ c - w) :
    u * r * (w * s) ≤ η * (1 - η) * c ^ 2 / (m * q) * (m * q * r * u) ∧
      η * (1 - η) * c ^ 2 / (m * q) ≤ η * (1 - η) * q / m := by
  have harea := GI.rectangle_area_bound hc hη hw hs
  have hmq : 0 < m * q := mul_pos hm hq
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ hmq]
    have hur : 0 ≤ u * r := mul_nonneg hu hr
    have := mul_le_mul_of_nonneg_left harea hur
    nlinarith
  · rw [div_le_div_iff₀ hmq hm]
    have hk : 0 ≤ η * (1 - η) := mul_nonneg (by linarith) (by linarith)
    have hc2 : c ^ 2 ≤ q * q := by nlinarith
    have := mul_le_mul_of_nonneg_left hc2 hk
    nlinarith


end GI.Paper
