module

public import Workspace.Impl.TermGlueLabNM5
public import Workspace.Impl.LinAbelianCoordinates
public import Workspace.Impl.TermGlueLabQ
public import Workspace.Impl.TermGlueLabPInv
public import Workspace.Impl.TermGlueLabPPoly

@[expose] public section

/-!
# The label driver: the setup module of step 5

The setup of step 5 (`tmGLPSetF abel _ _ quo minv`) calls three programs: the
abelian coordinates of `A/N` at `abel`, the quotient coordinates at `quo` and the inverse of a
unimodular matrix at `minv`. `tmGLNSetFuns u jo jm jh js` holds the three (107 functions):
`linAbelianCoordinatesFuns` at `u` (96, GroupOrder at `jo`, ConstructiveMembership at `jm`),
`tmGLQFuns` at `u + 96` (9, Hermite at `jh`, Smith at `js`), the inverse `tmGLPInvF` at
`u + 105` with its Hermite call at `u + 106`.

`tmGLN_set_ok` gives the three contracts `hab`, `hquo`, `hminv` of `tmGLN_m5_ok`. Their costs
`tmGLNFA`, `tmGLNFQ`, `tmGLNFI` are of the form `C (W + 1)^D` or `C (W + 2)^D`: for the abelian
coordinates this is the bound of `linAbelianCoordinates_spec_poly`; for the other two it is a
polynomial upper bound of `tmGLQBudget` and `tmGLPInvC` (from `tmGLQBudget_poly`,
`tmGLPInvC_poly`). So the three costs are monotone without a monotonicity lemma for the
budgets themselves.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val GroupOrder ConstructiveMembership HermiteFullRank SmithNonsingular encGroup
  encIntMatrix gens FullRankInst fullRankInput)

/-- **The setup module** at `u`. -/
def tmGLNSetFuns (u jo jm jh js : ℕ) : List Expr :=
  linAbelianCoordinatesFuns u jo jm ++ (tmGLQFuns (u + 96) jh js ++
    [tmGLPInvF (u + 106), linHermiteF jh])

theorem length_tmGLNSetFuns (u jo jm jh js : ℕ) : (tmGLNSetFuns u jo jm jh js).length = 107 := by
  rw [tmGLNSetFuns, List.length_append, List.length_append, linAbelianCoordinatesFuns_length,
    length_tmGLQFuns]; rfl

/-! ### The cost constants -/

/-- The constants of the abelian coordinates. -/
noncomputable def tmGLNAbK (ho : GroupOrder) (hm : ConstructiveMembership) : ℕ :=
  (linAbelianCoordinates_spec_poly ho hm).choose
noncomputable def tmGLNAbD (ho : GroupOrder) (hm : ConstructiveMembership) : ℕ :=
  (linAbelianCoordinates_spec_poly ho hm).choose_spec.choose

/-- The constants of the quotient coordinates. -/
noncomputable def tmGLNQC (hH : HermiteFullRank) (hS : SmithNonsingular) : ℕ :=
  (tmGLN_pbu_W (tmGLQBudget_poly hH hS)).choose
noncomputable def tmGLNQD (hH : HermiteFullRank) (hS : SmithNonsingular) : ℕ :=
  (tmGLN_pbu_W (tmGLQBudget_poly hH hS)).choose_spec.choose

/-- The constants of the inverse. -/
noncomputable def tmGLNIC (hH : HermiteFullRank) : ℕ :=
  (tmGLN_pbu_W (tmGLPInvC_poly hH)).choose
noncomputable def tmGLNID (hH : HermiteFullRank) : ℕ :=
  (tmGLN_pbu_W (tmGLPInvC_poly hH)).choose_spec.choose

/-- The cost of the abelian coordinates. -/
noncomputable def tmGLNFA (ho : GroupOrder) (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  tmGLNAbK ho hm * (W + 1) ^ tmGLNAbD ho hm

/-- The cost of the quotient coordinates. -/
noncomputable def tmGLNFQ (hH : HermiteFullRank) (hS : SmithNonsingular) (W : ℕ) : ℕ :=
  tmGLNQC hH hS * (W + 2) ^ tmGLNQD hH hS

/-- The cost of the inverse. -/
noncomputable def tmGLNFI (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  tmGLNIC hH * (W + 2) ^ tmGLNID hH

theorem tmGLNFA_mono (ho : GroupOrder) (hm : ConstructiveMembership) :
    Monotone (tmGLNFA ho hm) := fun _ _ h =>
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) _)

theorem tmGLNFQ_mono (hH : HermiteFullRank) (hS : SmithNonsingular) :
    Monotone (tmGLNFQ hH hS) := fun _ _ h =>
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 2) _)

theorem tmGLNFI_mono (hH : HermiteFullRank) : Monotone (tmGLNFI hH) := fun _ _ h =>
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 2) _)

theorem tmGLNFA_poly (ho : GroupOrder) (hm : ConstructiveMembership) :
    PBU fun _ W _ => tmGLNFA ho hm W :=
  PBU.smul _ (PBU.pow (PBU.addc PBU.W 1) _)

theorem tmGLNFQ_poly (hH : HermiteFullRank) (hS : SmithNonsingular) :
    PBU fun _ W _ => tmGLNFQ hH hS W :=
  PBU.smul _ (PBU.pow (PBU.addc PBU.W 2) _)

theorem tmGLNFI_poly (hH : HermiteFullRank) : PBU fun _ W _ => tmGLNFI hH W :=
  PBU.smul _ (PBU.pow (PBU.addc PBU.W 2) _)

/-! ### The contracts -/

/-- **The setup module meets the three contracts of the setup of step 5.** -/
theorem tmGLN_set_ok (ho : GroupOrder) (hm : ConstructiveMembership) (hH : HermiteFullRank)
    (hS : SmithNonsingular) {P : Program} {u jo jm jh js : ℕ}
    (h : P.HasAt u (tmGLNSetFuns u jo jm jh js))
    (hjo : P.prims[jo]? = some (groupOrderPrim ho))
    (hjm : P.prims[jm]? = some (linMembershipPrim hm))
    (hjh : P.prims[jh]? = some (linHermitePrim hH))
    (hjs : P.prims[js]? = some (linSmithPrim hS)) :
    (∀ {n : ℕ} (ns as : List (Equiv.Perm (Fin n))), gens ns ≤ gens as →
      (∀ x ∈ gens as, ∀ y ∈ gens as, x * y * x⁻¹ * y⁻¹ ∈ gens ns) →
      FunAll P u (.list [encGroup ns, encGroup as]) (fun out c =>
        (∃ M : Matrix (Fin as.length) (Fin as.length) ℤ, out = encIntMatrix M ∧
          linPermPresentation ns as M) ∧
        c ≤ tmGLNFA ho hm (Val.list [encGroup ns, encGroup as]).wt)) ∧
    (∀ I : FullRankInst, FunAll P (u + 96) (fullRankInput I) (fun out c =>
      TmGLQOut I.A out ∧ c ≤ tmGLNFQ hH hS (fullRankInput I).wt)) ∧
    (∀ {t : ℕ} (ht : 0 < t) (V : Matrix (Fin t) (Fin t) ℤ) (hV : IsUnit V.det),
      FunAll P (u + 105) (fullRankInput (tmGLPInst ht V hV)) (fun w c =>
        ∃ U : Matrix (Fin t) (Fin t) ℤ, w = encIntMatrix U ∧ U * V = 1 ∧ V * U = 1 ∧
          c ≤ tmGLNFI hH (fullRankInput (tmGLPInst ht V hV)).wt)) := by
  have hA : P.HasAt u (linAbelianCoordinatesFuns u jo jm) := h.left
  have h1 : P.HasAt (u + 96) (tmGLQFuns (u + 96) jh js ++ [tmGLPInvF (u + 106), linHermiteF jh]) := by
    have := h.right; rwa [linAbelianCoordinatesFuns_length] at this
  have hQ : P.HasAt (u + 96) (tmGLQFuns (u + 96) jh js) := h1.left
  have h2 : P.HasAt (u + 105) [tmGLPInvF (u + 106), linHermiteF jh] := by
    have := h1.right; rwa [length_tmGLQFuns] at this
  have hinv : P.funs[u + 105]? = some (tmGLPInvF (u + 106)) :=
    (h2.block (gs := [tmGLPInvF (u + 106)]) 0 rfl).single
  have hher : P.funs[u + 106]? = some (linHermiteF jh) :=
    (h2.block (gs := [linHermiteF jh]) 1 rfl).single
  refine ⟨fun ns as hle hc => ?_, fun I => ?_, fun ht V hV => ?_⟩
  · exact (linAbelianCoordinates_spec_poly ho hm).choose_spec.choose_spec hA hjo hjm ns as hle hc
  · refine (tmGLQ_spec hH hS hQ hjh hjs I).mono fun out c hc => ⟨hc.1, hc.2.trans ?_⟩
    exact (tmGLN_pbu_W (tmGLQBudget_poly hH hS)).choose_spec.choose_spec _
  · refine (tmGLPInv_spec hH hinv hher hjh ht V hV).mono fun w c ⟨U, hU, h1, h2, hc⟩ =>
      ⟨U, hU, h1, h2, hc.trans ?_⟩
    exact (tmGLN_pbu_W (tmGLPInvC_poly hH)).choose_spec.choose_spec _

end GI.Impl
