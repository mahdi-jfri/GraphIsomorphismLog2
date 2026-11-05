module

public import Workspace.Impl.RowMain
public import Workspace.Algorithm.RowSupply

@[expose] public section

/-!
# The coordinate program in the row case

`coords_spec_of_thr` asks for the logarithmic threshold `2 max(8, 2 + log₂ s) + 3 ≤ q`, where
`s` bounds the size `f > 0` of row `0`. In the row case of the giant step these come from the
state: `s` is the domain size `S.size`, `f` is the number of points of label `0` (positive
because the labels are onto), and the threshold follows from the row case `N^α < q`, the
parameter condition `Params.RowThreshold` and `S.size ≤ S.N` (the same argument as in
`GI.Algorithm.rowBranch`). The result is `coords_spec_row`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {Ω C : Type}

/-- **The threshold of the row case.** Above the base size, `N^α < q` and `s ≤ N` give the
logarithmic threshold for `s`. -/
theorem rowCase_thr {P : Params} (hT : P.RowThreshold) {S : State Ω C} {q : ℕ}
    (hN₀ : P.N₀ < S.N) (hsN : S.size ≤ S.N) (hspos : 0 < S.size)
    (hq : (S.N : ℝ) ^ P.α < q) : 2 * max 63 (12 * Real.logb 2 S.size) + 3 ≤ (q : ℝ) := by
  have hlog : Real.logb 2 S.size ≤ Real.logb 2 S.N :=
    Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hspos) (by exact_mod_cast hsN)
  have h1 := hT S.N hN₀
  have : max 63 (12 * Real.logb 2 S.size) ≤ max 63 (12 * Real.logb 2 S.N) :=
    max_le_max le_rfl (by linarith)
  linarith

/-- The threshold forces at least `19` rows. -/
theorem nineteen_le_of_thr {q s : ℕ} (hthr : 2 * max 63 (12 * Real.logb 2 s) + 3 ≤ (q : ℝ)) :
    19 ≤ q := by
  have h63 : (63 : ℝ) ≤ max 63 (12 * Real.logb 2 s) := le_max_left _ _
  have : (19 : ℝ) ≤ q := by linarith
  exact_mod_cast this

section Row

variable {n : ℕ} {e : Ω ≃ Fin n} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}

/-- Row `0` is nonempty, since the labels are onto, and it has at most `S.size` points. -/
theorem row0_card (hnat : NaturalRows S L label) (h0 : 0 < L.q) [Finite S.dom] :
    0 < Nat.card {x : S.dom // label x = ⟨0, h0⟩} ∧
      Nat.card {x : S.dom // label x = ⟨0, h0⟩} ≤ S.size := by
  obtain ⟨v, hv, hlv⟩ := hnat.onto ⟨0, h0⟩
  refine ⟨Nat.card_pos_iff.2 ⟨⟨⟨⟨v, hv⟩, hlv⟩⟩, inferInstance⟩, ?_⟩
  exact Finite.card_subtype_le _

/-- **The coordinate program in the row case** (Theorem A.17 inside Algorithm 4). Above the base
size, with the row case bound `N^α < q`, the natural one-label map `label` read as `rl`, and
generators `ps` of `G` paired with their label images, the program `coordFuns` returns pure
coordinates `E` for the rows. `RowForm.ofPure` turns them into a row form whose map is `E`.
The cited tasks are `PointwiseStab` and `NormalizedFactor` (as the primitives the program calls). -/
theorem coords_spec_row [Finite Ω]
    (hst : GI.Cited.PointwiseStab) (hfac : GI.Cited.NormalizedFactor) {Pa : Params}
    (hT : Pa.RowThreshold) (hN₀ : Pa.N₀ < S.N) (hsN : S.size ≤ S.N)
    (hq : (S.N : ℝ) ^ Pa.α < L.q)
    {P : Program} {b jp jf : ℕ} (hb : P.HasAt b (coordFuns b jp jf))
    (hjp : P.prims[jp]? = some (pointwiseStabPrim hst))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {ps : List (Perm (Fin n) × Perm (Fin L.q))} (hps : PairGens e L S.G ps) {rl : List ℕ}
    (hrl : RowLabs e S label rl) (hnat : NaturalRows S L label) :
    FunAll P b (.list [winCtx n L.q rl ps]) (fun w c =>
      ∃ E : Fin (zeroPts rl n).length × Fin L.q ≃ S.dom, PureCoords S L label E ∧
        w = coordsVal e S E ∧ c ≤ coordCost hst hfac (n + L.q + ps.length + 2)) := by
  classical
  have hq0 : 0 < L.q := by
    have : (0 : ℝ) < L.q := lt_of_le_of_lt (Real.rpow_nonneg (Nat.cast_nonneg _) _) hq
    exact_mod_cast this
  have hspos : 0 < S.size := by
    obtain ⟨v, hv, -⟩ := hnat.onto ⟨0, hq0⟩
    exact Nat.card_pos_iff.2 ⟨⟨⟨v, hv⟩⟩, inferInstance⟩
  have hthr := rowCase_thr hT hN₀ hsN hspos hq
  have h19 := nineteen_le_of_thr hthr
  obtain ⟨hfpos, hfs⟩ := row0_card hnat (by omega : 0 < L.q)
  exact coords_spec_of_thr hst hfac hb hjp hjf hps hrl hnat hfs hfpos hthr
    (fun {_} => (Nat.card_eq_fintype_card).symm)

/-- **At a `GiantStep` node in the row case.** `Good P₀ .giant S` gives `N₀ < N` and
`S.size ≤ N`, `P₀_rowThreshold` gives the parameter condition, and the row case gives `N^α < q`
(`hrow.1`). The label map `label` is the natural one-label map of the row case. -/
theorem coords_spec_good [Finite Ω]
    (hst : GI.Cited.PointwiseStab) (hfac : GI.Cited.NormalizedFactor)
    (hgood : Good P₀ .giant S) (hrow : RowCase P₀.α S L)
    {P : Program} {b jp jf : ℕ} (hb : P.HasAt b (coordFuns b jp jf))
    (hjp : P.prims[jp]? = some (pointwiseStabPrim hst))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {ps : List (Perm (Fin n) × Perm (Fin L.q))} (hps : PairGens e L S.G ps) {rl : List ℕ}
    (hrl : RowLabs e S label rl) (hnat : NaturalRows S L label) :
    FunAll P b (.list [winCtx n L.q rl ps]) (fun w c =>
      ∃ E : Fin (zeroPts rl n).length × Fin L.q ≃ S.dom, PureCoords S L label E ∧
        w = coordsVal e S E ∧ c ≤ coordCost hst hfac (n + L.q + ps.length + 2)) :=
  coords_spec_row hst hfac P₀_rowThreshold hgood.1 hgood.2.1 hrow.1 hb hjp hjf hps hrl hnat

end Row

end GI.Impl
