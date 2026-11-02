import Workspace.Algorithm.State
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# The row record of the first orbit-chain child

Section 6.1: "The first largest orbit under a full quotient preimage retains both the carrier and
`h`; later conditional queries lie in other original orbits of size at most half the parent
domain and may clear and reset there." In the recursion (`Run.orbitStop`, `Run.orbitChain`) the
first child runs under the parent group `G` on its largest orbit `D`. It keeps the row record,
the floor mode and `h` exactly when the state invariants still hold on `D` (`State.inherit`).

This file shows that this condition is the simple test `State.ColsSplit`: `D` meets two column
classes (`inherit_book`). The reason: the rows are a carrier of `G` on the domain, so the
column-fixing subgroup `J` moves a point to every row (`ρ(J) = Alt(m)` is transitive on the rows),
hence every `G`-invariant part of the domain meets every row; the other facts of the carrier
restrict to `D`. The counter invariant restricts too: for `h = 0`, the image of `G` on `D` is a
quotient of its image on the domain, and the alternating width does not grow under quotients
(`GI.SectionCaps.quotient_degree_le`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

variable {Ω C : Type}

/-- `Alt(m)` is transitive on `Fin m` for `m ≥ 3`. -/
theorem exists_alt_move {m : ℕ} (hm : 3 ≤ m) (i j : Fin m) :
    ∃ a : alternatingGroup (Fin m), (a : Perm (Fin m)) i = j := by
  haveI := _root_.alternatingGroup.isPretransitive_of_three_le_card (α := Fin m) (by simpa using hm)
  exact MulAction.exists_smul_eq (alternatingGroup (Fin m)) i j

/-- **A carrier restricts to an invariant part that meets two columns.** If the rows are a carrier
of `G` on `D`, then they are a carrier of `G` on every nonempty `G`-invariant `D' ⊆ D` that meets
two column classes. Every row meets `D'`: the column-fixing elements realize every even row
permutation. -/
theorem CarrierSpec.restrict {G : Subgroup (Perm Ω)} {D D' : Set Ω} {m : ℕ} {rows cols : Setoid Ω}
    {row : Ω → Fin m} {ρ : G →* alternatingGroup (Fin m)} (h : CarrierSpec G D m rows cols row ρ)
    (hD' : Invariant G D') (hsub : D' ⊆ D) (hne : D'.Nonempty)
    (htwo : ∃ v ∈ D', ∃ w ∈ D', ¬ cols.r v w) : CarrierSpec G D' m rows cols row ρ where
  three_le := h.three_le
  row_iff v hv w hw := h.row_iff v (hsub hv) w (hsub hw)
  row_onto i := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨σ, hσ⟩ := exists_alt_move h.three_le (row a) i
    obtain ⟨g, hg, -⟩ := h.indep σ
    refine ⟨(g : Perm Ω) a, (hD' g g.2 a).2 ha, ?_⟩
    rw [h.row_equivariant g a (hsub ha), hg, hσ]
  row_equivariant g v hv := h.row_equivariant g v (hsub hv)
  cols_inv g hg v hv w hw := h.cols_inv g hg v (hsub hv) w (hsub hw)
  two_cols := htwo
  indep a := by
    obtain ⟨g, hg, hf⟩ := h.indep a
    exact ⟨g, hg, fun v hv => hf v (hsub hv)⟩
  cells v hv w hw h1 h2 := by
    obtain ⟨g, hg, hf, hgv⟩ := h.cells v (hsub hv) w (hsub hw) h1 h2
    exact ⟨g, hg, fun u hu => hf u (hsub hu), hgv⟩

/-- A column level of the hierarchy on `D` is one on every `D' ⊆ D`. -/
theorem ColsLevel.restrict {D D' : Set Ω} {hier : List (Interval Ω)} {c : Setoid Ω}
    (h : ColsLevel D hier c) (hsub : D' ⊆ D) : ColsLevel D' hier c := by
  obtain ⟨pre, post, he, hc⟩ := h
  exact ⟨pre, post, he, fun v hv w hw => hc v (hsub hv) w (hsub hw)⟩

/-- **Alternating width does not grow on a smaller invariant part**: the image of `G` on `D'` is
a quotient of its image on `D ⊇ D'`. -/
theorem cap_restrict {G : Subgroup (Perm Ω)} {D D' : Set Ω} (hD : Invariant G D)
    (hD' : Invariant G D') (hsub : D' ⊆ D) {b : ℕ}
    (hcap : GI.SectionCaps.Cap (restrictHom G D hD).range b) :
    GI.SectionCaps.Cap (restrictHom G D' hD').range b := by
  intro U k hk q hq
  -- The elements of `G` whose image on `D'` lies in `U`.
  let A : Subgroup G := U.comap (restrictHom G D' hD').rangeRestrict
  let p : A →* (restrictHom G D hD).range := (restrictHom G D hD).rangeRestrict.comp A.subtype
  let pU : A →* U :=
    { toFun := fun a => ⟨(restrictHom G D' hD').rangeRestrict a, a.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul (restrictHom G D' hD').rangeRestrict (a : G) b) }
  refine GI.SectionCaps.quotient_degree_le hcap hk p (q.comp pU) ?_ ?_
  · intro s
    obtain ⟨u, rfl⟩ := hq s
    obtain ⟨g, hg⟩ := (restrictHom G D' hD').rangeRestrict_surjective (u : (restrictHom G D' hD').range)
    have hgA : g ∈ A := by change (restrictHom G D' hD').rangeRestrict g ∈ U; rw [hg]; exact u.2
    refine ⟨⟨g, hgA⟩, ?_⟩
    change q ⟨(restrictHom G D' hD').rangeRestrict g, hgA⟩ = q u
    congr 1
    exact Subtype.ext hg
  · intro a ha
    have hfix : ∀ v : D, ((a : G) : Perm Ω) v = v := fun v => by
      have := congrArg (fun f : (restrictHom G D hD).range => ((f : Perm D) v : Ω)) ha
      simpa [p, restrictHom_apply] using this
    change q (pU a) = 1
    have h1 : pU a = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      ext v
      change ((a : G) : Perm Ω) v = v
      exact hfix ⟨v, hsub v.2⟩
    rw [h1, map_one]

namespace State

/-- A largest orbit is nonempty. -/
theorem LargestOrbit.nonempty {S : State Ω C} {D₁ : Set Ω} (hD₁ : S.LargestOrbit D₁) :
    D₁.Nonempty := by
  obtain ⟨a, -, hD⟩ := hD₁.orbit
  rw [hD]
  exact ⟨a, 1, S.G.one_mem, rfl⟩

/-- **The keep condition of `inherit` on an invariant part of the domain** under the parent group
is the column test `ColsSplit`. -/
theorem inherit_cond_iff (S : State Ω C) {D : Set Ω} (hD : Invariant S.G D) (hsub : D ⊆ S.dom)
    (hne : D.Nonempty) :
    (CounterInv S.G D hD S.rows S.h S.N ∧ CarrierOK S.G D S.rows S.hier) ↔ S.ColsSplit D := by
  constructor
  · rintro ⟨-, hc⟩ R hR
    obtain ⟨c, hc', ⟨row, ρ, hs⟩, -⟩ := hc R hR
    exact ⟨c, hc', hs.two_cols⟩
  · intro hsp
    -- The carrier on `D`.
    have hcar : CarrierOK S.G D S.rows S.hier := by
      intro R hR
      obtain ⟨c, hc, ⟨row, ρ, hs⟩, hl⟩ := S.carrier R hR
      obtain ⟨c', hc', htwo⟩ := hsp R hR
      rw [hc] at hc'
      cases hc'
      exact ⟨c, hc, ⟨row, ρ, hs.restrict hD hsub hne htwo⟩, hl.restrict hsub⟩
    refine ⟨⟨fun h1 => ?_, fun h0 => ?_⟩, hcar⟩
    · obtain ⟨R, hR, hrc, hN, hm⟩ := S.counter.1 h1
      obtain ⟨c, -, ⟨row, ρ, hs⟩, -⟩ := hcar R hR
      refine ⟨R, hR, ⟨fun g hg => hrc.inv g hg, ?_⟩, hN, hm⟩
      refine ⟨fun v => row v.1, fun i => ?_, fun v w => hs.row_iff v.1 v.2 w.1 w.2⟩
      obtain ⟨v, hv, hvi⟩ := hs.row_onto i
      exact ⟨⟨v, hv⟩, hvi⟩
    · obtain ⟨R, hR, hm, hcap⟩ := S.counter.2 h0
      exact ⟨R, hR, hm, cap_restrict S.dom_inv hD hsub hcap⟩

/-- **The first orbit-chain child keeps the bookkeeping exactly when the columns split its
orbit**: the bookkeeping of the inherited state on an invariant part `D` of the domain under the
parent group is `orbitBook D`. -/
theorem inherit_book (S : State Ω C) {D : Set Ω} (hD : Invariant S.G D) (hsub : D ⊆ S.dom)
    (hne : D.Nonempty) (x y : Ω → C) : (S.inherit S.G D hD x y).book = S.orbitBook D := by
  classical
  have hiff := S.inherit_cond_iff hD hsub hne
  unfold inherit orbitBook
  by_cases h : S.ColsSplit D
  · rw [dif_pos (hiff.2 h), if_pos h]; rfl
  · rw [dif_neg (fun h' => h (hiff.1 h')), if_neg h]; rfl

end State

end GI.Algorithm
