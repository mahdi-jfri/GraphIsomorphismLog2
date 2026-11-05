module

public import Workspace.Impl.LinFinitePair
public import Workspace.Impl.LinFiniteActionWeight
public import Workspace.Impl.LinGroupSlp

@[expose] public section

/-! Executable full affine group operations and shared-entry SLP evaluation. -/
namespace GI.Impl
open GI.Cited GI.Lang

variable {G : Type*} [Group G] {d : ℕ} (m : Fin d → ℕ)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m)

theorem linFiniteAffineMul_spec {P : Program} {b : ℕ} (hp : linFinitePairAt P b)
    (hm : ∀ i, 0 < m i) (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (g h : G) :
    FunDet P b (.list [linFiniteAffineVal m ρ c g, linFiniteAffineVal m ρ c h])
      (linFiniteAffineVal m ρ c (g * h))
      (linFinitePairMulCost (Val.list [linFiniteAffineVal m ρ c g, linFiniteAffineVal m ρ c h]).wt (d + 1)) := by
  have hs := linFinitePairMul_spec hp (linFiniteModuli m)
    (linFiniteActionMatrix m ρ c g) (linFiniteActionMatrix m ρ c g⁻¹)
    (linFiniteActionMatrix m ρ c h) (linFiniteActionMatrix m ρ c h⁻¹)
  rw [linFiniteActionMatrix_mul m hm ρ c hc g h,
    linFiniteActionMatrix_mul m hm ρ c hc h⁻¹ g⁻¹] at hs
  simpa only [linFiniteAffineVal, linFinitePairVal, mul_inv_rev] using hs

theorem linFiniteAffineInv_spec {P : Program} {b : ℕ} (hp : linFinitePairAt P b) (g : G) :
    FunDet P (b + 1) (linFiniteAffineVal m ρ c g) (linFiniteAffineVal m ρ c g⁻¹)
      (linFinitePairInvCost (linFiniteAffineVal m ρ c g).wt) := by
  simpa only [linFiniteAffineVal, linFinitePairVal, inv_inv] using
    linFinitePairInv_spec hp (linFiniteModuli m) (linFiniteActionMatrix m ρ c g) (linFiniteActionMatrix m ρ c g⁻¹)

def linFiniteActionOpCost (W d : ℕ) : ℕ :=
  let B := linFiniteActionWeight W d
  100000 * (1 + linFinitePairMulCost (100 * (B + 1)) (d + 1) + 1000 * (B + 1))

theorem linFiniteActionMul_uniform {P : Program} {b : ℕ} (hp : linFinitePairAt P b)
    (hm : ∀ i, 0 < m i) (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (g h : G) :
    FunDet P b (.list [linFiniteAffineVal m ρ c g, linFiniteAffineVal m ρ c h])
      (linFiniteAffineVal m ρ c (g * h))
      (linFiniteActionOpCost (linVecVal (fun i => (m i : ℤ))).wt d) := by
  have wg := linFiniteAffineVal_wt m hm ρ c g
  have wh := linFiniteAffineVal_wt m hm ρ c h
  have wi := wt_list2_le (linFiniteAffineVal m ρ c g) (linFiniteAffineVal m ρ c h)
  have ww : (Val.list [linFiniteAffineVal m ρ c g, linFiniteAffineVal m ρ c h]).wt ≤
      100 * (linFiniteActionWeight (linVecVal (fun i => (m i : ℤ))).wt d + 1) := by omega
  have hh := linFinitePairMulCost_mono (n := d + 1) ww
  apply (linFiniteAffineMul_spec m ρ c hp hm hc g h).mono
  dsimp only [linFiniteActionOpCost]
  omega

theorem linFiniteActionInv_uniform {P : Program} {b : ℕ} (hp : linFinitePairAt P b)
    (hm : ∀ i, 0 < m i) (g : G) :
    FunDet P (b + 1) (linFiniteAffineVal m ρ c g) (linFiniteAffineVal m ρ c g⁻¹)
      (linFiniteActionOpCost (linVecVal (fun i => (m i : ℤ))).wt d) := by
  have ww := linFiniteAffineVal_wt m hm ρ c g
  apply (linFiniteAffineInv_spec m ρ c hp g).mono
  dsimp only [linFiniteActionOpCost, linFinitePairInvCost]
  omega

theorem linFiniteActionOpCost_poly : PBU (fun d W _ => linFiniteActionOpCost W d) := by
  have hb := linFiniteActionWeight_poly
  have hp := linPoly_subst linFinitePairMulCost_poly (PBU.addc PBU.k 1)
    (PBU.smul 100 (PBU.addc hb 1)) (PBU.const 0)
  exact PBU.smul 100000 (PBU.add (PBU.add (PBU.const 1) hp) (PBU.smul 1000 (PBU.addc hb 1)))

def linFiniteActionSlpFuns (b : ℕ) : List Expr :=
  linGroupSlpFuns b (b + 5) (b + 6) ++ linFinitePairFuns (b + 5)

theorem linFiniteActionSlpFuns_length (b : ℕ) : (linFiniteActionSlpFuns b).length = 65 := rfl

structure linFiniteActionSlpAt (P : Program) (b : ℕ) : Prop where
  slp : linGroupSlpAt P b (b + 5) (b + 6)
  ops : linFinitePairAt P (b + 5)

theorem linFiniteActionSlpAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linFiniteActionSlpFuns b)) : linFiniteActionSlpAt P b where
  slp := linGroupSlpAt_of (h.block 0 rfl)
  ops := linFinitePairAt_of (h.block 5 rfl)

theorem linFiniteActionSlp_spec {P : Program} {b : ℕ} (hp : linFiniteActionSlpAt P b)
    (hm : ∀ i, 0 < m i) (hc : ∀ g h, c (g * h) = ρ g (c h) + c g)
    (gs : List G) (prog : List SlpInstr) (es : List G) (he : linSlpEntries gs prog [] = some es) :
    FunDet P b (.list [linGroupSlpTable (linFiniteAffineVal m ρ c) gs,
        .list (prog.map encSlpInstr), linFiniteAffineVal m ρ c 1])
      (linFiniteAffineVal m ρ c (es.getLast?.getD 1))
      (linGroupSlpCost (Val.list [linGroupSlpTable (linFiniteAffineVal m ρ c) gs,
        .list (prog.map encSlpInstr), linFiniteAffineVal m ρ c 1]).wt prog.length
        (linFiniteActionWeight (linVecVal (fun i => (m i : ℤ))).wt d)
        (linFiniteActionOpCost (linVecVal (fun i => (m i : ℤ))).wt d)) := by
  exact linGroupSlp_spec hp.slp (linFiniteAffineVal m ρ c) (linFiniteAffineVal_wt m hm ρ c)
    (linFiniteActionMul_uniform m ρ c hp.ops hm hc) (linFiniteActionInv_uniform m ρ c hp.ops hm) gs prog es he

end GI.Impl
