module

public import Workspace.Algorithm.Existence
public import Workspace.Algorithm.SingleFactor
public import Workspace.Algorithm.NormLabels

@[expose] public section

/-!
# Building the subroutine data from the giant-step data

`Supply P` (`Workspace/Algorithm/Existence.lean`) has two fields: the case data of `Continue`
and of `GiantStep`, on the states that the recursion reaches (inside a phase, with the
hierarchy invariant `HierInv`). This file constructs the first field, so that only the second
remains a hypothesis (`GiantSupply`).

## `Continue`

On a transitive state above the threshold, with the hierarchy invariant:

* the primitive quotient is the exposed quotient `State.expose`
  (`Workspace/Algorithm/Expose.lean`), which needs at least two positions. A state inside a
  phase has `N > N₀ ≥ 1`, so `N^γ ≥ 1` for `γ ≥ 0`, and a state above the threshold has at
  least two positions;
* the normalization of a single factor that fails the integer small test is
  `PrimitiveQuotient.normalization` (`Workspace/Algorithm/SingleFactor.lean`), with `q = m`.
  Its degree is above `q₀` when the bounded alternating degrees are enumerated
  (`Params.EnumeratesBounded`: `q₀! ≤ 2^⌊a log 2⌋`; Section A.3: "When `m ≤ q₀`, enumerate
  the alternating quotient at its actual Cameron block level"; Section 7.5 (iv): "Fix `a ≥ 1`
  large enough for all multiplicities"). Indeed a single factor of degree `m ≤ q₀` has order at
  most `m! ≤ q₀!`, so it passes the integer small test and the dispatcher enumerates it
  (`PrimitiveQuotient.q₀_lt_of_single`). Its labels carry the data of the Cameron constituent:
  they are read on the domain, and they come with the Johnson block map of the constituent
  (`PrimitiveQuotient.normAbove`, `Workspace/Algorithm/NormLabels.lean`).

No cited result is used.

## What remains

`GiantSupply P`: on a transitive state above the threshold inside a phase, with the hierarchy
invariant and supplied labels `L` on `q > q₀` points (with their constituent data,
`SuppliedLabels`), the row terminal, the column step, or an
aggregation round (`GiantCase P S L`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

/-- **The parameter condition that the dispatcher enumerates the bounded alternating
degrees**: `q₀! ≤ 2^b` with `b = ⌊a log 2⌋` (Section 6: "An enumerative reduction includes the
bounded alternating-degree cases"; Section A.3: "When `m ≤ q₀`, enumerate the alternating
quotient"; Section 7.5 (iv): "Fix `a ≥ 1` large enough for all multiplicities"). The paper fixes
`q₀` in Section 7.5 (i) and then `a` in (iv), so its choices satisfy it. It is stated with the
integer exponent `b` of the integer small test `PrimitiveQuotient.SmallZ`, which the
normalization guard uses; for `a ≥ 0` it implies `q₀! ≤ exp(a (log 2)²)`
(`Params.EnumeratesBounded.real`). -/
def Params.EnumeratesBounded (P : Params) : Prop :=
  P.q₀.factorial ≤ 2 ^ P.smallExp

/-- The real form of `Params.EnumeratesBounded`: `q₀! ≤ 2^b ≤ 2^(a log 2) = exp(a (log 2)²)`. -/
theorem Params.EnumeratesBounded.real {P : Params} (hE : P.EnumeratesBounded) (ha : 0 ≤ P.a) :
    (P.q₀.factorial : ℝ) ≤ Real.exp (P.a * Real.log 2 ^ 2) := by
  have h1 : (P.q₀.factorial : ℝ) ≤ (2 : ℝ) ^ (P.smallExp : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast hE
  refine h1.trans ?_
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.2
  have := P.smallExp_le ha
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- **The giant-step data**: the field `giant` of `Supply`. -/
structure GiantSupply (P : Params) : Type 1 where
  /-- The case of a transitive `GiantStep` state above the threshold inside a phase, with the
  hierarchy invariant and supplied labels `L` on `q > q₀` points, which carry the data of their
  Cameron constituent (`SuppliedLabels`). -/
  giant : ∀ {Ω C : Type} [Finite Ω] (S : State Ω C), S.HierInv → P.N₀ < S.N → S.size ≤ S.N →
    S.Transitive → (S.N : ℝ) ^ P.γ < S.size → (L : SuppliedLabels S) → P.q₀ < L.q →
      GiantCase P S L

namespace PrimitiveQuotient

variable {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S)

/-- **A single factor that fails the integer small test has degree above `q₀`** when the
bounded degrees are enumerated: a single factor of degree `m ≤ q₀` has order at most
`m! ≤ q₀! ≤ 2^b`, and `2^b ≤ d^(b ⌊log₂ d⌋)` since `d ≥ 2`, so it passes the test. -/
theorem q₀_lt_of_single {P : Params} (hE : P.EnumeratesBounded) (hs : ¬ Q.SmallZ P.smallExp)
    {m k : ℕ} (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e) :
    P.q₀ < m := by
  by_contra hm
  push Not at hm
  apply hs
  unfold SmallZ
  have hcard := Product.card_le e Q.ρ.range hS.1
  simp only [pow_one, Nat.factorial_one, mul_one] at hcard
  have hd2 := Q.two_le
  have hL : 1 ≤ Nat.log 2 Q.d := Nat.le_log_of_pow_le (by norm_num) (by simpa using hd2)
  calc Nat.card Q.ρ.range ≤ P.q₀.factorial := hcard.trans (Nat.factorial_le hm)
    _ ≤ 2 ^ P.smallExp := hE
    _ ≤ Q.d ^ P.smallExp := Nat.pow_le_pow_left hd2 _
    _ ≤ Q.d ^ (P.smallExp * Nat.log 2 Q.d) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right _ hL)

/-- The normalization of a single factor that fails the integer small test, with its degree
above `q₀`. -/
noncomputable def normalizationAbove [Finite Ω] {P : Params} (hE : P.EnumeratesBounded)
    (hs : ¬ Q.SmallZ P.smallExp) (h : Q.SingleFactor) : {I : Normalization S // P.q₀ < I.q} :=
  ⟨Q.normalization h, Q.q₀_lt_of_single hE hs _ h.choose_spec.choose_spec.choose_spec⟩

end PrimitiveQuotient

section Build

variable {P : Params}

/-- A state inside a phase and above the threshold has two distinct positions, for `γ ≥ 0`. -/
theorem not_univOn_bot_of_large (hP : P.Terminating) (hγ : 0 ≤ P.γ) {Ω C : Type}
    {S : State Ω C} (hN : P.N₀ < S.N) (hs : (S.N : ℝ) ^ P.γ < S.size) :
    ¬ UnivOn S.dom ⊥ := by
  intro hall
  have h1 : (1 : ℝ) ≤ (S.N : ℝ) ^ P.γ :=
    Real.one_le_rpow (by have := hP.N₀_pos; exact_mod_cast (show 1 ≤ S.N by omega)) hγ
  have h2 : 1 < S.size := by exact_mod_cast h1.trans_lt hs
  have hsub : Nat.card S.dom ≤ 1 := by
    haveI : Subsingleton S.dom := ⟨fun v w => Subtype.ext (hall v.1 v.2 w.1 w.2)⟩
    haveI : Finite S.dom := Finite.of_subsingleton
    exact Finite.card_le_one_iff_subsingleton.2 inferInstance
  change Nat.card S.dom > 1 at h2
  omega

/-- **The case data of `Continue`**, built: the exposed primitive quotient and the
single-factor normalization. -/
noncomputable def contCase (hP : P.Terminating) (hγ : 0 ≤ P.γ) (hE : P.EnumeratesBounded)
    {Ω C : Type} [Finite Ω] (S : State Ω C) (hinv : S.HierInv) (hN : P.N₀ < S.N)
    (htr : S.Transitive) (hs : (S.N : ℝ) ^ P.γ < S.size) : ContCase P S :=
  let Q := S.expose htr hinv (not_univOn_bot_of_large hP hγ hN hs)
  .quotient Q (S.expose_killsCols htr hinv _) (S.expose_keepsLevels htr hinv _)
    fun hsm h => (Q.normalizationAbove hE hsm h).2

/-- **The subroutine data from the giant-step data.** -/
noncomputable def Supply.ofGiant (hP : P.Terminating) (hγ : 0 ≤ P.γ)
    (hE : P.EnumeratesBounded) (Gs : GiantSupply P) : Supply P where
  cont S hinv hN _ htr hs _ := contCase hP hγ hE S hinv hN htr hs
  giant := Gs.giant

/-- Every `Supply` restricts to its giant-step data. -/
def Supply.toGiant (Su : Supply P) : GiantSupply P := ⟨Su.giant⟩

/-- **`Supply P` is nonempty exactly when `GiantSupply P` is**, for parameters with `γ ≥ 0`
that enumerate the bounded alternating degrees. -/
theorem supply_nonempty_iff (hP : P.Terminating) (hγ : 0 ≤ P.γ) (hE : P.EnumeratesBounded) :
    Nonempty (Supply P) ↔ Nonempty (GiantSupply P) :=
  ⟨fun ⟨Su⟩ => ⟨Su.toGiant⟩, fun ⟨Gs⟩ => ⟨Supply.ofGiant hP hγ hE Gs⟩⟩

/-- **Every state has a run of `Solve`, given only the giant-step data.** -/
theorem exists_run_solve_giant (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (ha : 128 ≤ P.a) (hγ : 0 ≤ P.γ) (hE : P.EnumeratesBounded) (Gs : GiantSupply P)
    {Ω C : Type} [Finite Ω] (S : State Ω C) : Nonempty (Run P .solve S none S.answer) :=
  exists_run_solve hP hM ha (Supply.ofGiant hP hγ hE Gs) S

end Build

end GI.Algorithm
