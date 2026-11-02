import Workspace.Impl.TermRecStep
import Workspace.Impl.PolyBd

/-!
# T5, the own cost of one level is polynomial in `n + M`

"The entire affine calculation is polynomial in `b + M`", and so is the rest of one level: the
derived series, the pieces, the point stabilizers and transporters, the profiles. Each of the
cost bounds of `TermRecProg*.lean` is a sum of products of powers of `n`, `M` and of the bounds
of the cited algorithms, so it is at most `C (n + M + 2)^D` for constants `C, D` that depend only
on the cited algorithms and on the glue (`PBU`, with `k = n`, `W = M`).

`tmRiOwn_poly`: the own cost `tmRiOwnC` of one level (the step `tmRiStepO`, the case `ℓ = 0`
`tmRiBaseC`, and the dispatch) has such a bound.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val SolvableCosetIntersection DerivedSubgroup Membership)

/-! ### The building blocks -/

theorem tmRiP_bs (p : Prim) {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) :
    PBU fun k W B => p.boundSize (f k W B) :=
  PBU.smul p.c (PBU.pow (PBU.addc hf 2) p.k)

theorem tmRiP_F (d : ℕ) : PBU fun k _ _ => (k + 1) ^ d := PBU.pow PBU.k1 d

theorem tmRiP_mem (h : Membership) : PBU fun k _ _ => memCost h k :=
  PBU.smul (membershipPrim h).c (PBU.pow (PBU.smul 400 (tmRiP_F 6)) (membershipPrim h).k)

theorem tmRiP_red (h : Membership) {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) :
    PBU fun k W B => reduceCost h k (f k W B) :=
  PBU.add (PBU.mul (PBU.addc hf 1) (tmRiP_mem h))
    (PBU.smul reduceK (PBU.pow (PBU.mul (PBU.addc hf 2) PBU.k1) 6))

theorem tmRiP_cnf (h : Membership) {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) :
    PBU fun k W B => cosetNFCost h k (f k W B) :=
  PBU.add (PBU.add (tmRiP_red h hf) (PBU.smul 20 hf)) (PBU.smul 2000 (tmRiP_F 6))

theorem tmRiP_combM {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) : PBU fun k W B => combM k (f k W B) :=
  PBU.smul 100 (PBU.pow (PBU.mul (PBU.addc hf 2) PBU.k1) 2)

theorem tmRiP_comb {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) : PBU fun k W B => combCost k (f k W B) :=
  PBU.mul (PBU.addc hf 1) (PBU.add
    (PBU.smul combK (PBU.pow (PBU.add (PBU.addc (PBU.add (PBU.smul 4 hf)
      (PBU.smul 2 (tmRiP_combM hf))) 7) (tmRiP_F 4)) 2))
    (PBU.smul loopModK (PBU.addc (PBU.add (PBU.smul 2 hf) (tmRiP_combM hf)) 1)))

/-! ### The sizes -/

theorem tmRiP_B : PBU fun k W _ => tmRiB k W :=
  PBU.mul (PBU.addc PBU.W 1) (PBU.addc (PBU.add (tmRiP_F 6) PBU.W) 1)

theorem tmRiP_V : PBU fun k W _ => tmRiVs k W :=
  PBU.smul (10 ^ 8) (PBU.mul (PBU.addc PBU.W 1) tmRiP_B)

theorem tmRiP_SQ : PBU fun k W _ => tmRiSQ k W :=
  PBU.smul (10 ^ 5) (PBU.pow (PBU.addc tmRiP_V 1) 2)

/-! ### The parts of one level -/

theorem tmRiP_test (psci : Prim) {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) :
    PBU fun k W B => tmRiTestC psci k (f k W B) :=
  PBU.add (PBU.add (tmRiP_bs psci (PBU.smul (10 ^ 4) (tmRiP_F 6)))
    (PBU.smul (10 ^ 10) (tmRiP_F 8))) (PBU.smul 1000 hf)

theorem tmRiP_objP (psci : Prim) : PBU fun k W _ => tmRiObjPC psci k (2 * W) :=
  PBU.add (PBU.add (tmRiP_test psci (PBU.smul 2 PBU.W)) (PBU.smul (10 ^ 6) (tmRiP_F 6)))
    (PBU.smul 1000 (PBU.smul 2 PBU.W))

theorem tmRiP_pcsStep {fo fe : ℕ → ℕ → ℕ → ℕ} (ho : PBU fo) (he : PBU fe) :
    PBU fun k W B => tmRiPcsStepC (fo k W B) (fe k W B) :=
  PBU.add (PBU.mul (PBU.smul 2 he) ho) (PBU.smul (10 ^ 6) (PBU.pow (PBU.addc he 1) 2))

theorem tmRiP_pcs (psci : Prim) :
    PBU fun k W _ => tmRiPcsC (tmRiObjPC psci k (2 * W)) (tmRiVs k W) :=
  PBU.add (PBU.mul tmRiP_V (tmRiP_pcsStep (tmRiP_objP psci) tmRiP_V))
    (PBU.smul (10 ^ 5) (PBU.pow (PBU.addc tmRiP_V 1) 3))

theorem tmRiP_der (pder : Prim) (hmem : Membership) :
    PBU fun k _ _ => tmRiDerC pder hmem k :=
  PBU.add (PBU.mul (PBU.addc (PBU.pow PBU.k 2) 5)
    (PBU.add (PBU.add (tmRiP_bs pder (PBU.smul 400 (tmRiP_F 6)))
      (tmRiP_red hmem (PBU.smul 2 (PBU.pow PBU.k 2)))) (PBU.smul (10 ^ 9) (tmRiP_F 8))))
    (PBU.smul (10 ^ 8) (tmRiP_F 8))

theorem tmRiP_mapSh : PBU fun k W _ => tmRiMapShC k (2 * W) W :=
  PBU.add (PBU.mul (PBU.addc PBU.W 1) (PBU.add (PBU.add (PBU.smul permK (tmRiP_F 3))
      (PBU.smul (10 ^ 5) (tmRiP_F 6))) (PBU.smul 100 (PBU.smul 2 PBU.W))))
    (PBU.mul (PBU.smul mapK (PBU.addc PBU.W 1)) (PBU.mul (PBU.smul (10 ^ 4) (PBU.addc PBU.W 1))
      (PBU.addc (PBU.add (tmRiP_F 6) (PBU.smul 2 PBU.W)) 1)))

theorem tmRiP_Y (psci : Prim) :
    PBU fun k W _ => tmRiYC psci k W (4 * (10 * tmRiVs k W + 20) + 10) :=
  PBU.add (PBU.add (PBU.add (tmRiP_test psci (PBU.smul 2 PBU.W))
      (tmRiP_bs psci (PBU.smul (10 ^ 4) (tmRiP_F 6)))) tmRiP_mapSh)
    (PBU.smul (10 ^ 12) (PBU.pow (PBU.addc (PBU.add (PBU.add
      (PBU.addc (PBU.smul 4 (PBU.addc (PBU.smul 10 tmRiP_V) 20)) 10) PBU.W) (tmRiP_F 9)) 1) 3))

theorem tmRiP_B2 : PBU fun k W _ => tmRiB2 k W :=
  PBU.addc (PBU.mul (PBU.smul (10 ^ 4) (PBU.addc PBU.W 1)) (tmRiP_F 6)) 100

theorem tmRiP_pair (hmem : Membership) {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) :
    PBU fun k W B => tmRiPairC hmem k W (f k W B) := by
  have p100 : PBU fun k W _ => 100 * ((tmRiB2 k W + 2) * (k + 1)) ^ 2 :=
    PBU.smul 100 (PBU.pow (PBU.mul (PBU.addc tmRiP_B2 2) PBU.k1) 2)
  exact PBU.add (PBU.add (PBU.add (PBU.add
    (PBU.mul (PBU.smul mapK (PBU.addc PBU.W 1)) (PBU.addc (PBU.add (PBU.smul 5 hf) tmRiP_B2) 10))
    (tmRiP_comb (PBU.addc (PBU.smul 3 tmRiP_B2) 30))) (tmRiP_cnf hmem p100))
    (PBU.smul 100 (PBU.add (PBU.add hf tmRiP_B2) p100))) (PBU.smul (10 ^ 4) (tmRiP_F 6))

theorem tmRiP_tab (hmem : Membership) :
    PBU fun k W _ => tmRiTabC hmem k W (2 * W) (tmRiVs k W) := by
  have pm : PBU fun _ W _ => 2 * W := PBU.smul 2 PBU.W
  have pW : PBU fun k W _ => 10 * tmRiVs k W + 20 := PBU.addc (PBU.smul 10 tmRiP_V) 20
  have pc : PBU fun k _ _ => 1400 * (k + 1) ^ 6 + 1 := PBU.addc (PBU.smul 1400 (tmRiP_F 6)) 1
  exact PBU.add (PBU.mul pm (PBU.add (PBU.add (PBU.add (PBU.add
      (PBU.mul pm (tmRiP_pair hmem pW))
      (PBU.mul (PBU.smul mapK (PBU.addc pm 1)) (PBU.addc (PBU.add pW (PBU.mul pm pc)) 5)))
      (PBU.smul 50 tmRiP_V)) (PBU.const 100)) (PBU.mul pm pc)))
    (PBU.mul (PBU.smul mapK (PBU.addc pm 1)) (PBU.addc (PBU.add tmRiP_V
      (PBU.mul pm (PBU.addc (PBU.smul 2 (PBU.addc (PBU.mul pm pc) 4)) 1))) 5))

theorem tmRiP_prof (hmem : Membership) {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) :
    PBU fun k W B => tmRiProfC hmem k (f k W B) :=
  PBU.add (PBU.add (tmRiP_red hmem (PBU.addc (PBU.smul 2 (PBU.pow PBU.k 2)) 1))
    (PBU.smul (10 ^ 6) (PBU.pow (PBU.addc hf 1) 2))) (PBU.smul (10 ^ 7) (tmRiP_F 8))

theorem tmRiP_prC (hmem : Membership) : PBU fun k W _ => tmRiPrC hmem k W :=
  PBU.add (PBU.add (PBU.mul (PBU.smul 2 PBU.W) (tmRiP_prof hmem (PBU.smul 3 tmRiP_V)))
    (PBU.mul (PBU.smul mapK (PBU.addc (PBU.smul 2 PBU.W) 1))
      (PBU.addc (PBU.add tmRiP_V (PBU.smul 2000 tmRiP_B)) 5)))
    (PBU.smul 8000 (PBU.pow (PBU.addc (PBU.smul 2 PBU.W) 1) 3))

theorem tmRiP_stepO (hsci : SolvableCosetIntersection) (hder : DerivedSubgroup)
    (hmem : Membership) (Kg Dg : ℕ) :
    PBU fun k W _ => tmRiStepO hsci hder hmem Kg Dg k W :=
  PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add
    (tmRiP_der (derivedSubgroupPrim hder) hmem)
    (PBU.smul 2 (tmRiP_pcs (solvableCosetIntersectionPrim hsci))))
    (PBU.mul (PBU.smul 4 (PBU.pow PBU.W 3)) (tmRiP_Y (solvableCosetIntersectionPrim hsci))))
    (tmRiP_tab hmem)) (PBU.smul 2 (tmRiP_prC hmem)))
    (PBU.smul Kg (PBU.pow (PBU.addc tmRiP_V 1) Dg))) (PBU.smul 10 tmRiP_SQ))
    (PBU.smul 10 (PBU.addc (PBU.smul 700 (tmRiP_F 6)) 1))

theorem tmRiP_base (psci : Prim) :
    PBU fun k W _ => tmRiBaseC (tmRiObjPC psci k (2 * W)) k (tmRiVs k W) :=
  PBU.add (PBU.mul tmRiP_V (tmRiP_pcsStep (tmRiP_objP psci)
      (PBU.add (PBU.smul 10 tmRiP_V) (PBU.smul 2000 (tmRiP_F 6)))))
    (PBU.smul (10 ^ 7) (PBU.pow (PBU.addc (PBU.add tmRiP_V (tmRiP_F 6)) 1) 2))

/-- **The own cost of one level**: the step, the case `ℓ = 0`, and the dispatch. -/
noncomputable def tmRiOwnC (hsci : SolvableCosetIntersection) (hder : DerivedSubgroup)
    (hmem : Membership) (Kg Dg n M : ℕ) : ℕ :=
  tmRiStepO hsci hder hmem Kg Dg n M +
    tmRiBaseC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n (2 * M)) n (tmRiVs n M) +
    10 * tmRiVs n M

/-- **The own cost of one level is polynomial in `n + M`.** -/
theorem tmRiOwn_poly (hsci : SolvableCosetIntersection) (hder : DerivedSubgroup)
    (hmem : Membership) (Kg Dg : ℕ) :
    ∃ C D : ℕ, ∀ n M, tmRiOwnC hsci hder hmem Kg Dg n M ≤ C * (n + M + 2) ^ D := by
  obtain ⟨C, D, h⟩ : PBU fun k W _ => tmRiOwnC hsci hder hmem Kg Dg k W :=
    PBU.add (PBU.add (tmRiP_stepO hsci hder hmem Kg Dg)
      (tmRiP_base (solvableCosetIntersectionPrim hsci))) (PBU.smul 10 tmRiP_V)
  refine ⟨C, D, fun n M => ?_⟩
  have := h n M 0
  unfold PB at this
  rwa [show M + 0 + n + 2 = n + M + 2 by omega] at this

end GI.Impl
