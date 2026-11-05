module

public import Workspace.Impl.GenChild
public import Workspace.Algorithm.NormLabels

@[expose] public section

/-!
# States and modes of normalization children

All normalization children have the same group and domain. An orbit test therefore decides
one mode for all of them. Their bookkeeping is kept because the normalized group keeps the
carrier. The exposed hierarchy keeps `SmallInv`, including its ban on ratio-one intervals.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {P : Params} {S : State Ω C}

/-- Normalization keeps the bookkeeping on every coset. -/
theorem normChild_book (N : NormAbove P S) (j : Fin N.I.k) :
    (N.child j).book = S.book := by
  simp only [NormAbove.child, State.book,
    State.restrict_rows_of _ _ _ _ _ _ N.keeps,
    State.restrict_floor_of _ _ _ _ _ _ N.keeps,
    State.restrict_h_of _ _ _ _ _ _ N.keeps]

/-- Transitivity does not depend on the coset or on the target coloring. -/
theorem normChild_transitive (N : NormAbove P S) (j : Fin N.I.k) :
    (N.child j).Transitive ↔
      ∀ v ∈ S.dom, ∀ w ∈ S.dom, ∃ g ∈ N.I.G', g v = w := Iff.rfl

/-- A boolean orbit test selects a single mode for the whole normalization. -/
def normMode (transitive : Bool) : Mode := if transitive then .giant else .cont

/-- Only correctness of the orbit test is needed to justify `Run.normalize`'s mode guard. -/
theorem normMode_spec (N : NormAbove P S) (b : Bool)
    (hb : b = true ↔ ∀ v ∈ S.dom, ∀ w ∈ S.dom, ∃ g ∈ N.I.G', g v = w) :
    ∀ j, (normMode b = .cont ∧ ¬ (N.child j).Transitive) ∨
      (normMode b = .giant ∧ (N.child j).Transitive) := by
  intro j
  cases b with
  | false => exact Or.inl ⟨rfl, fun h => Bool.false_ne_true (hb.mpr h)⟩
  | true => exact Or.inr ⟨rfl, hb.mp rfl⟩

/-- Normalization does not increase the natural hierarchy rank. -/
theorem normRho_le (N : NormAbove P S) : rhoNat N.I.hier' ≤ rhoNat S.hier := by
  have h : (rhoNat N.I.hier' : ℝ) ≤ rhoNat S.hier := by
    rw [rhoNat_cast, rhoNat_cast]
    exact N.I.rho_le
  exact_mod_cast h

/-- The exposed hierarchy of the chosen normalization keeps `SmallInv`. -/
theorem normChild_smallInv [Finite Ω] (Q : PrimitiveQuotient S) (c : Q.NormChoice)
    (htr : S.Transitive) (hq : P.q₀ < (Q.normalizationOf c).q)
    (hkc : Q.KillsCols) (hkl : Q.KeepsLevels) (h : SmallInv S)
    (j : Fin (Q.normAboveOf c htr hq hkc hkl).I.k) :
    SmallInv ((Q.normAboveOf c htr hq hkc hkl).child j) := by
  let N := Q.normAboveOf c htr hq hkc hkl
  have hbk := normChild_book N j
  have hr : (N.child j).rows = S.rows := congrArg Prod.fst hbk
  refine h.of_rho_le rfl (Q.intervalsOK h.1) (normRho_le N) ?_
  rw [hr]
  exact h.2.2

/-- Normalization children are good `Continue` calls. -/
theorem normChild_good_cont (N : NormAbove P S) (hgood : Good P .cont S)
    (j : Fin N.I.k) : Good P .cont (N.child j) :=
  ⟨hgood.1, hgood.2.1, N.tower⟩

/-- A transitive normalization child is a good call with exactly its supplied labels. -/
theorem normChild_good_giant (N : NormAbove P S) (hgood : Good P .cont S)
    (hs : (S.N : ℝ) ^ P.γ < S.size) (j : Fin N.I.k)
    (ht : (N.child j).Transitive) :
    GoodL P .giant (N.child j) (some (N.childLabels j)) :=
  ⟨hgood.1, hgood.2.1, ht, hs, N.tower, N.childLabels j, rfl, N.q_large⟩

/-- An intransitive normalization child has smaller measure. -/
theorem normChild_mlt_cont [Finite Ω] (N : NormAbove P S) (htr : S.Transitive)
    (j : Fin N.I.k) (ht : ¬ (N.child j).Transitive) :
    MLt (measure P .cont (N.child j)) (measure P .cont S) := by
  have htrj := trInd_of_not _ ht
  have htrS := trInd_of S htr
  have hsz : (N.child j).size = S.size := rfl
  have hNj : (N.child j).N = S.N := rfl
  rw [mlt_iff]
  simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
  omega

/-- A transitive normalization child has smaller measure when called in giant mode. -/
theorem normChild_mlt_giant [Finite Ω] (hκ : 5 ≤ P.κ) (N : NormAbove P S)
    (htr : S.Transitive) (j : Fin N.I.k) (ht : (N.child j).Transitive) :
    MLt (measure P .giant (N.child j)) (measure P .cont S) := by
  have hσ : (N.child j).sigma P.κ ≤ S.sigma P.κ :=
    State.sigma_le_of hκ N.I.le le_rfl
  have hρ := normRho_le N
  have hd : rhoNat N.I.hier' < rhoNat S.hier ∨
      capSum N.I.hier' ≤ capSum S.hier := by
    rcases N.I.drop with h | h
    · left
      have h' : (rhoNat N.I.hier' : ℝ) < rhoNat S.hier := by
        rw [rhoNat_cast, rhoNat_cast]
        exact h
      exact_mod_cast h'
    · exact Or.inr h
  have htrj := trInd_of _ ht
  have htrS := trInd_of S htr
  have hsz : (N.child j).size = S.size := rfl
  have hNj : (N.child j).N = S.N := rfl
  have hhier : (N.child j).hier = N.I.hier' := rfl
  have hρj : rhoNat (N.child j).hier = rhoNat N.I.hier' := rfl
  have hcj : capSum (N.child j).hier = capSum N.I.hier' := rfl
  have hbk := normChild_book N j
  have hfl : (N.child j).floor = S.floor := congrArg (fun b => b.2.1) hbk
  have hh : (N.child j).h = S.h := congrArg (fun b => b.2.2) hbk
  have hf : flInd (N.child j) = flInd S := by simp only [flInd, hfl]
  rw [mlt_iff]
  simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
  omega

/-- Replace the group, target, and hierarchy in the canonical parent value. The other entries
are kept, including the row record, floor flag, counter and phase size. -/
theorem normCanon_child [Finite Ω] {n : ℕ} {e : Ω ≃ Fin n} {cc : C → ℕ}
    {gv dv xv yv hv rv fv hh : Val} {sz : ℕ}
    (hcan : Canon e cc (.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz]) S)
    (Q : PrimitiveQuotient S) (c : Q.NormChoice) (htr : S.Transitive)
    (hq : P.q₀ < (Q.normalizationOf c).q) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (j : Fin (Q.normAboveOf c htr hq hkc hkl).I.k) {gv' yv' hv' : Val}
    (hg : GroupValC n gv' (groupFin e (Q.normGroup c.e c.hS)))
    (hy : ColorVal e cc yv' (S.y ∘ c.τ j))
    (hH : HierValC e hv' (Q.pre ++ Q.top :: Q.post)) :
    Canon e cc (dispChildVal n gv' dv xv yv' hv' rv fv hh sz)
      ((Q.normAboveOf c htr hq hkc hkl).child j) := by
  let N := Q.normAboveOf c htr hq hkc hkl
  obtain ⟨gv0, dv0, xv0, yv0, hv0, rv0, -, hd, hx, -, -, hr, heq⟩ := hcan.val
  simp only [Val.list.injEq, List.cons.injEq] at heq
  obtain ⟨-, -, rfl, rfl, -, -, rfl, rfl, rfl, hNe, -⟩ := heq
  have hbk := normChild_book N j
  have hrows : (N.child j).rows = S.rows := congrArg Prod.fst hbk
  have hfl : (N.child j).floor = S.floor := congrArg (fun b => b.2.1) hbk
  have hhT : (N.child j).h = S.h := congrArg (fun b => b.2.2) hbk
  refine ⟨⟨gv', dv, xv, yv', hv', rv, hg, hd, hx, hy, hH,
    hrows ▸ hr, ?_⟩, fun a => ⟨(hcan.colors a).1, (hcan.colors (c.τ j a)).2⟩,
    hcan.fits, normChild_smallInv Q c htr hq hkc hkl hcan.small j⟩
  change dispChildVal n gv' dv xv yv' hv' rv (boolVal S.floor) (.nat S.h) sz =
    .list [.nat n, gv', dv, xv, yv', hv', rv, boolVal (N.child j).floor,
      .nat (N.child j).h, .nat (N.child j).N]
  simp only [dispChildVal, hfl, hhT, hNe]
  rfl

end GI.Impl
