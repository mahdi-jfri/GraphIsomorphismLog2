module

public import Workspace.Impl.AggItemCfCol
public import Workspace.Impl.AggItemCfDMain
public import Workspace.Impl.AggItemCfRBounds
public import Workspace.Impl.PolyBd

@[expose] public section

/-!
# The object stage of Cases 2b/3 (`ItCfObjSpec`)

The three programs of the object stage and their contracts:
* `col` (`it_cfCol_spec`, `AggItemCfCol.lean`), with cost `itCfColC hps` of the input weight,
  which is at most `itCfColCo hps * (W + 1) ^ itCfColDo hps` (`itCf_colC_pb`);
* `orb` (`itCf_orb_spec`, `AggItemCfRBounds.lean`);
* `des` (`itCf_des_spec`, `AggItemCfDMain.lean`).

`itCf_objSpec` puts them together, with one constant and one exponent for all three
(`itCfObjCo`, `itCfObjDo`).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens pointwiseStab PointwiseStab encKColoring)

/-- One step of the search for a uniform polynomial bound (`PBU`) of an expression built from
sums, products, powers, constants and the weight `W`. -/
macro "itcf_pbu_step" : tactic =>
  `(tactic| first
    | with_reducible exact PBU.W
    | with_reducible apply PBU.add
    | with_reducible apply PBU.mul
    | with_reducible apply PBU.pow
    | with_reducible exact PBU.const _)

/-- **Composition.** A function with a uniform polynomial bound, applied to one. -/
theorem itCf_pbu_comp {f : ℕ → ℕ} (hf : PBU fun _ X _ => f X) {g : ℕ → ℕ → ℕ → ℕ}
    (hg : PBU g) : PBU fun k W B => f (g k W B) := by
  obtain ⟨C, D, h⟩ := hf
  obtain ⟨C', D', h'⟩ := hg
  refine ⟨C * (C' + 2) ^ D, D' * D, fun k W B => ?_⟩
  have hY : 1 ≤ W + B + k + 2 := by omega
  have e1 : f (g k W B) ≤ C * (g k W B + 0 + 0 + 2) ^ D := h 0 (g k W B) 0
  have e2 : g k W B + 0 + 0 + 2 ≤ (C' + 2) * (W + B + k + 2) ^ D' := by
    have := h' k W B
    unfold PB at this
    have : 1 ≤ (W + B + k + 2) ^ D' := Nat.one_le_pow _ _ (by omega)
    nlinarith
  unfold PB
  calc f (g k W B) ≤ C * ((C' + 2) * (W + B + k + 2) ^ D') ^ D :=
        e1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e2 D))
    _ = C * (C' + 2) ^ D * (W + B + k + 2) ^ (D' * D) := by rw [mul_pow, ← pow_mul]; ring

theorem itCf_pbu_domC : PBU fun _ X _ => itDomC X := by
  unfold itDomC; repeat itcf_pbu_step

theorem itCf_pbu_degB (hps : PointwiseStab) : PBU fun _ X _ => itCfDegB hps X := by
  unfold itCfDegB; repeat itcf_pbu_step

theorem itCf_pbu_memC : PBU fun _ X _ => itCfMemC X := by
  unfold itCfMemC; repeat itcf_pbu_step

theorem itCf_pbu_cellC : PBU fun _ X _ => itCfCellC X := by
  unfold itCfCellC
  refine PBU.add (PBU.add (PBU.mul (PBU.const _) (itCf_pbu_comp itCf_pbu_memC ?_)) ?_) (PBU.const _)
  · repeat itcf_pbu_step
  · repeat itcf_pbu_step

theorem itCf_pbu_TB : PBU fun _ X _ => itCfTB X := by
  unfold itCfTB; repeat itcf_pbu_step

theorem itCf_pbu_frC (hps : PointwiseStab) : PBU fun _ X _ => itCfFrC hps X := by
  unfold itCfFrC
  refine PBU.add (PBU.add (PBU.add (PBU.mul (PBU.const _) (itCf_pbu_comp itCf_pbu_domC PBU.W))
    (PBU.mul (PBU.const _) (itCf_pbu_comp (itCf_pbu_degB hps) ?_)))
    (PBU.mul (PBU.const _) (PBU.add PBU.W (itCf_pbu_comp itCf_pbu_domC PBU.W)))) (PBU.const _)
  exact PBU.addc (PBU.mul (PBU.const _) (PBU.add PBU.W (itCf_pbu_comp itCf_pbu_domC PBU.W))) _

theorem itCf_pbu_colMC (hps : PointwiseStab) {g : ℕ → ℕ → ℕ → ℕ} (hg : PBU g) :
    PBU fun k W B => itCfColMC hps W (g k W B) := by
  have hT := itCf_pbu_comp itCf_pbu_TB PBU.W
  have hCB : PBU fun k W B => itCfCB W (g k W B) := by
    unfold itCfCB
    exact PBU.addc (PBU.mul (PBU.const _) (PBU.add (PBU.add (PBU.add PBU.W hg) PBU.W) hT)) _
  unfold itCfColMC
  refine PBU.addc ?_ _
  refine PBU.add ?_ (PBU.mul (PBU.const _) ?_)
  · refine PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add ?_ ?_) ?_)
      (PBU.mul (PBU.const _) hT)) ?_) ?_) ?_
    · unfold linTakeCost; repeat itcf_pbu_step
    · unfold Prim.boundSize; repeat itcf_pbu_step
    · repeat itcf_pbu_step
    · unfold itCfColIB; repeat itcf_pbu_step
    · refine PBU.mul (PBU.mul PBU.W PBU.W) (itCf_pbu_comp itCf_pbu_cellC ?_)
      exact PBU.addc (PBU.add (PBU.add (PBU.mul (PBU.const _) hCB)
        (PBU.mul (PBU.const _) (PBU.mul PBU.W PBU.W))) PBU.W) _
    · unfold itCfColIB itCfColKB
      refine PBU.mul (PBU.mul (PBU.const _) (PBU.addc (PBU.mul PBU.W PBU.W) _)) ?_
      refine PBU.addc (PBU.add (PBU.addc (PBU.mul (PBU.const _) (PBU.add hCB ?_)) _) ?_) _
      · repeat itcf_pbu_step
      · repeat itcf_pbu_step
  · unfold itCfColIB itCfColKB
    refine PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add PBU.W hg) hT) ?_) hCB) ?_) ?_
    · repeat itcf_pbu_step
    · repeat itcf_pbu_step
    · repeat itcf_pbu_step

/-- **The cost of `col` is polynomial in the input weight.** -/
theorem itCf_colC_pb (hps : PointwiseStab) :
    ∃ C D : ℕ, ∀ W, itCfColC hps W ≤ C * (W + 1) ^ D := by
  have hF := itCf_pbu_comp (itCf_pbu_frC hps) PBU.W
  have hU : PBU fun _ W _ => itCfColC hps W := by
    unfold itCfColC
    refine PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add (PBU.mul (PBU.const _) hF)
      (PBU.mul (PBU.const _) (itCf_pbu_colMC hps hF))) ?_) ?_) ?_) _
    · repeat itcf_pbu_step
    · repeat itcf_pbu_step
    · repeat itcf_pbu_step
  obtain ⟨C, D, h⟩ := hU
  refine ⟨C * 2 ^ D, D, fun W => ?_⟩
  have h1 : itCfColC hps W ≤ C * (W + 0 + 0 + 2) ^ D := h 0 W 0
  have h2 : (W + 0 + 0 + 2) ^ D ≤ 2 ^ D * (W + 1) ^ D := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) D
  calc itCfColC hps W ≤ C * (2 ^ D * (W + 1) ^ D) := h1.trans (Nat.mul_le_mul_left _ h2)
    _ = C * 2 ^ D * (W + 1) ^ D := by ring

/-- The constant of the cost bound of `col`. -/
noncomputable def itCfColCo (hps : PointwiseStab) : ℕ := (itCf_colC_pb hps).choose

/-- The exponent of the cost bound of `col`. -/
noncomputable def itCfColDo (hps : PointwiseStab) : ℕ := (itCf_colC_pb hps).choose_spec.choose

theorem itCfColC_le (hps : PointwiseStab) (W : ℕ) :
    itCfColC hps W ≤ itCfB (itCfColCo hps) (itCfColDo hps) W :=
  (itCf_colC_pb hps).choose_spec.choose_spec W

theorem itCfB_monoCD {C D C' D' M : ℕ} (hC : C ≤ C') (hD : D ≤ D') :
    itCfB C D M ≤ itCfB C' D' M :=
  Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) hD)

/-- The constant of the object stage. -/
noncomputable def itCfObjCo (hps : PointwiseStab) : ℕ := itCfColCo hps + itCfRCo hps + itCfDCo

/-- The exponent of the object stage. -/
noncomputable def itCfObjDo (hps : PointwiseStab) : ℕ := itCfColDo hps + itCfRDo hps + itCfDDo

/-- **The object stage of Cases 2b/3.** The programs `col`, `orb`, `des` at the indices `fcol`,
`forb`, `fdes` meet `ItCfObjSpec`, with the pointwise stabilizer at primitive index `jps`. -/
theorem itCf_objSpec (hps : PointwiseStab) {P : Program}
    {fcol fr dom orb rng0 fd pd cnt deg jps rep tk ps tor rng mp fc an1 an2 fnd pe pp : ℕ}
    (hf : P.funs[fcol]? = some (itCfColF fr rep tk ps tor rng mp))
    (hfr : P.funs[fr]? = some (itCfFrF dom deg))
    (hdom : P.funs[dom]? = some (itDomF orb rng0 fd)) (horb : P.HasAt orb (orbitFuns orb))
    (hrng0 : P.HasAt rng0 (rangeFuns rng0)) (hfd : P.HasAt fd (filterFuns fd pd))
    (hpd : P.funs[pd]? = some (acpDomF cnt)) (hcnt : P.HasAt cnt (countFuns cnt))
    (hdeg : P.HasAt deg (itCfDegFuns deg jps)) (hj : P.prims[jps]? = some (pointwiseStabPrim hps))
    (hrep : P.HasAt rep (replicateFuns rep))
    (htk : P.HasAt tk (linTakeFuns tk)) (hpsF : P.HasAt ps (pstabFuns ps jps))
    (hto : P.HasAt tor (tupOrbFuns tor))
    (hrng : P.HasAt rng (rangeFuns rng)) (hmp : P.HasAt mp (mapFuns mp fc))
    (hfc : P.funs[fc]? = some (itCfCellF an1 an2 fnd)) (han1 : P.HasAt an1 (anyFuns an1 pe))
    (hpe : P.funs[pe]? = some itCfEqP) (han2 : P.HasAt an2 (anyFuns an2 pp))
    (hpp : P.funs[pp]? = some itCfPairP) (hfnd : P.HasAt fnd (findFuns fnd pe))
    {forb dm dg dd rd tb mb rw rm ce : ℕ}
    (hfo : P.funs[forb]? = some (itCfROrbF dm dg rd))
    (hdm : P.funs[dm]? = some (itDomF orb rng0 fd))
    (hdg : P.funs[dg]? = some (itCfRDegreeF dd))
    (hdd : P.HasAt dd (itCfDegFuns dd jps))
    (hrd : P.funs[rd]? = some (itCfRReadF tb ce))
    (htb : P.funs[tb]? = some (itCfRTableF mb rng0))
    (hmb : P.HasAt mb (mapFuns mb rw)) (hrw : P.funs[rw]? = some (itCfRRowF rm rng0))
    (hrm : P.HasAt rm (mapFuns rm ce)) (hce : P.funs[ce]? = some itCfRCellF)
    {fdes : ℕ} {I : ItCfDIdx} (hD : ItCfDOk P I) (hfde : P.funs[fdes]? = some (itCfDesF I.core)) :
    ItCfObjSpec P fcol forb fdes (itCfObjCo hps) (itCfObjDo hps) where
  col hs t := (it_cfCol_spec hps hf hfr hdom horb hrng0 hfd hpd hcnt hdeg hj hrep htk hpsF hto
      hrng hmp hfc han1 hpe han2 hpp hfnd hs t).mono fun w c ⟨hw, hc⟩ =>
    ⟨hw, hc.trans ((itCfColC_le hps _).trans (itCfB_monoCD (by unfold itCfObjCo; omega)
      (by unfold itCfObjDo; omega)))⟩
  orb hs t R := (itCf_orb_spec hps hfo hdm horb hrng0 hfd hpd hcnt hdg hdd hj hrd htb hmb hrw
      hrm hce hs t R).mono fun w c ⟨hw, hc⟩ =>
    ⟨hw, hc.trans (itCfB_monoCD (by unfold itCfObjCo; omega) (by unfold itCfObjDo; omega))⟩
  des col t := (itCf_des_spec hD hfde col t).mono fun w c ⟨hw, hc⟩ =>
    ⟨hw, hc.trans (itCfB_monoCD (by unfold itCfObjCo; omega) (by unfold itCfObjDo; omega))⟩

end GI.Impl
