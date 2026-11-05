module

public import Workspace.Impl.AggSpecBody
public import Workspace.Impl.AggBodyKr
public import Workspace.Impl.LayoutAsm

@[expose] public section

/-!
# The aggregation round in the concrete program

`asAgg rd cr cm it rest` is the function list of the aggregation round, placed at `asmAggBase`
in `asmProg` (`asb i = asmAggBase + i`):

* `0` the step (`aggBodyE`); `1`–`4` the entries of the reading, the certificate phase, the
  comparison phase and the items (the parameters `rd, cr, cm, it`); their helpers are the list
  `rest`, from `asb 1000` on;
* `5` `CombineExact` (`ceF`), `6` one continuation (`lcChildF`), `7` the label lift
  (`liftLabF`, with the shift module of the core at `289`), `8` the cap update (`lcHierF`),
  `9` the coset rule (`combStep`);
* blocks: `20` map of the continuations, `30` append, `33` fold, `36` coset normal form,
  `42` compose, `50` graph preimage, `100` kernel cut, `120` gather, `124` split of pairs,
  `133` set, `136` inverse.

The round uses the primitives `PointwiseStab` (`0`), `Membership` (`1`), `Preimage` (`2`) and
`NormalizedFactor` (`3`) of `asmProg`, and no extra primitive (the phases may use others).

`as_asm_agg`: `Iface.AggSpec` for `asmRest … Wg Wr (asWa …)` and `asmProg … (asAgg …)`, given
the contracts of the four phases at `asb 1`, …, `asb 4`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership)

set_option maxRecDepth 100000

/-- The index of entry `i` of the aggregation round. -/
def asb (i : ℕ) : ℕ := asmAggBase + i

/-- **The functions of the aggregation round** (see the module docstring). -/
def asAgg (rd cr cm it : Expr) (rest : List Expr) : List Expr :=
  [aggBodyE (asb 1) (asb 2) (asb 3) (asb 4) (asb 20) (asb 5), rd, cr, cm, it,
    ceF (asb 30) (asb 33) (asb 36),
    lcChildF asmF (asb 50) (asb 100) (asb 7) (asb 120) (asb 8),
    liftLabF 289 (asb 124) 3,
    lcHierF (asb 133),
    combStep (asb 42) (asb 136) (asb 30)] ++ List.replicate 10 .nil ++
  mapFuns (asb 20) (asb 6) ++ List.replicate 7 .nil ++ appendFuns (asb 30) ++
  foldlFuns (asb 33) (asb 9) ++ cosetNFFuns (asb 36) 1 ++ composeFuns (asb 42) ++
  List.replicate 4 .nil ++ graphPreFuns (asb 50) 2 ++ krFuns (asb 100) 0 ++ gatherFuns (asb 120) ++
  pSplitFuns (asb 124) ++ setFuns (asb 133) ++ invFuns (asb 136) ++ List.replicate 852 .nil ++
  rest

theorem length_asAgg (rd cr cm it : Expr) (rest : List Expr) :
    (asAgg rd cr cm it rest).length = 1000 + rest.length := by
  simp only [asAgg, List.length_append, List.length_replicate]
  rfl

/-- **The work of the aggregation round at a node**: `asOwn` for `k = |Ω|` and the input weight
bound `2 (stateW k S + labWStd k N) + 6`. -/
noncomputable def asWa (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (X : ℕ → ℕ) (nd : Node P₀) : ℝ :=
  (asOwn hpre hfac hm (abKrC hst) X (Nat.card nd.Ω)
    (2 * (stateW (Nat.card nd.Ω) nd.S + labWStd (Nat.card nd.Ω) nd.S.N) + 6) : ℕ)

section Asm

variable {Pg : Program} {rd cr cm it : Expr} {rest : List Expr}

theorem as_blk (hG : Pg.HasAt asmAggBase (asAgg rd cr cm it rest)) {gs : List Expr} (i : ℕ)
    (hg : ((asAgg rd cr cm it rest).drop i).take gs.length = gs) : Pg.HasAt (asb i) gs :=
  hG.block i hg

theorem as_one (hG : Pg.HasAt asmAggBase (asAgg rd cr cm it rest)) {e : Expr} (i : ℕ)
    (hg : ((asAgg rd cr cm it rest).drop i).take 1 = [e]) : Pg.funs[asb i]? = some e :=
  (as_blk (gs := [e]) hG i hg).single

end Asm

private theorem spd_asAgg_peel {P : Program} {N n N' : ℕ} {A B : List Expr}
    (h : P.HasAt (asb N) (A ++ B)) (hl : A.length = n) (hN : N + n = N') :
    P.HasAt (asb N) A ∧ P.HasAt (asb N') B := by
  refine ⟨h.left, ?_⟩
  have h2 := h.right
  rw [asb, hl, Nat.add_assoc, hN] at h2
  exact h2

private theorem spd_asAgg_cons {P : Program} {N N' : ℕ} {e : Expr} {B : List Expr}
    (h : P.HasAt (asb N) (e :: B)) (hN : N + 1 = N') :
    P.funs[asb N]? = some e ∧ P.HasAt (asb N') B := by
  have h' : P.HasAt (asb N) ([e] ++ B) := h
  obtain ⟨h1, h2⟩ := spd_asAgg_peel h' rfl hN
  exact ⟨h1.single, h2⟩

/-- **The aggregation round of the concrete program meets its step specification**, for the
work `asWa`, given the contracts of the reading, the two phases and the items at
`asb 1`, …, `asb 4`, with hand-over relations `H` and phase bound `X`. -/
theorem as_asm_agg (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (extra : List Prim) (gen row : List Expr) (Wg Wr : Node P₀ → ℝ)
    (H : AsHand) (X : ℕ → ℕ) (rd cr cm it : Expr) (rest : List Expr)
    (hgen : gen.length ≤ asmSlot) (hrow : row.length ≤ asmSlot)
    (hr : AsReadOK (asmRest hst hm hpre hfac Wg Wr (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac extra gen row (asAgg rd cr cm it rest)) asmF H X (asb 1))
    (hc : AsCertOK (asmRest hst hm hpre hfac Wg Wr (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac extra gen row (asAgg rd cr cm it rest)) asmF H X (asb 2))
    (hcm : AsCompOK (asmRest hst hm hpre hfac Wg Wr (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac extra gen row (asAgg rd cr cm it rest)) asmF H X (asb 3))
    (hi : AsItemsOK (asmRest hst hm hpre hfac Wg Wr (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac extra gen row (asAgg rd cr cm it rest)) asmF H X (asb 4)) :
    (asmRest hst hm hpre hfac Wg Wr (asWa hst hm hpre hfac X)).iface.AggSpec
      (asmProg hst hm hpre hfac extra gen row (asAgg rd cr cm it rest)) asmF asmAggBase := by
  set R := asmRest hst hm hpre hfac Wg Wr (asWa hst hm hpre hfac X) with hR
  set Pg := asmProg hst hm hpre hfac extra gen row (asAgg rd cr cm it rest) with hPg
  have hG : Pg.HasAt (asb 0) (asAgg rd cr cm it rest) := asmProg_hasAt_agg hgen hrow
  have p0 : Pg.prims[0]? = some (pointwiseStabPrim hst) := rfl
  have p1 : Pg.prims[1]? = some (membershipPrim hm) := rfl
  have p2 : Pg.prims[2]? = some (preimagePrim hpre) := rfl
  have p3 : Pg.prims[3]? = some (normalizedFactorPrim hfac) := rfl
  have hlift : LiftAt Pg 289 112 2 3 := asm_liftAt
  have hsb : ShiftAt Pg 289 := ⟨hlift.shiftApp, hlift.append, hlift.addMap, hlift.addK⟩
  unfold asAgg at hG
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hG
  obtain ⟨h0, hG⟩ := spd_asAgg_cons (N' := 1) hG rfl
  obtain ⟨_, hG⟩ := spd_asAgg_cons (N' := 2) hG rfl
  obtain ⟨_, hG⟩ := spd_asAgg_cons (N' := 3) hG rfl
  obtain ⟨_, hG⟩ := spd_asAgg_cons (N' := 4) hG rfl
  obtain ⟨_, hG⟩ := spd_asAgg_cons (N' := 5) hG rfl
  obtain ⟨h5, hG⟩ := spd_asAgg_cons (N' := 6) hG rfl
  obtain ⟨h6, hG⟩ := spd_asAgg_cons (N' := 7) hG rfl
  obtain ⟨h7, hG⟩ := spd_asAgg_cons (N' := 8) hG rfl
  obtain ⟨h8, hG⟩ := spd_asAgg_cons (N' := 9) hG rfl
  obtain ⟨h9, hG⟩ := spd_asAgg_cons (N' := 10) hG rfl
  obtain ⟨_, hG⟩ := spd_asAgg_peel (N' := 20) hG rfl rfl
  obtain ⟨h20, hG⟩ := spd_asAgg_peel (N' := 23) hG rfl rfl
  obtain ⟨_, hG⟩ := spd_asAgg_peel (N' := 30) hG rfl rfl
  obtain ⟨h30, hG⟩ := spd_asAgg_peel (N' := 33) hG rfl rfl
  obtain ⟨h33, hG⟩ := spd_asAgg_peel (N' := 36) hG rfl rfl
  obtain ⟨h36, hG⟩ := spd_asAgg_peel (N' := 42) hG rfl rfl
  obtain ⟨h42, hG⟩ := spd_asAgg_peel (N' := 46) hG rfl rfl
  obtain ⟨_, hG⟩ := spd_asAgg_peel (N' := 50) hG rfl rfl
  obtain ⟨h50, hG⟩ := spd_asAgg_peel (N' := 100) hG rfl rfl
  obtain ⟨h100, hG⟩ := spd_asAgg_peel (N' := 120) hG rfl rfl
  obtain ⟨h120, hG⟩ := spd_asAgg_peel (N' := 124) hG rfl rfl
  obtain ⟨h124, hG⟩ := spd_asAgg_peel (N' := 133) hG rfl rfl
  obtain ⟨h133, hG⟩ := spd_asAgg_peel (N' := 136) hG rfl rfl
  have h136 := hG.left
  have hlc : AsLcAt R.iface Pg asmF hpre hfac (asb 20) (abKrC hst) :=
    asLcAt_of R.iface Pg asmF hpre hfac h20 h6 h50 p2
      (ab_krOK hst h100 p0) (abKrC_mono hst) h7 hsb
      h124 p3 h120 h8 h133
  have hce : AsCeAt Pg hm (asb 5) :=
    asCeAt_of Pg hm h5 h30 h33 h9
      h42 h136 h30 h36 p1
  rw [show asb 0 = asmAggBase from Nat.add_zero _] at h0
  have hW : ∀ nd : Node P₀, nd.run.kind = .aggregate →
      (asOwn hpre hfac hm (abKrC hst) X (Nat.card nd.Ω) (R.iface.inW .giant nd.S) : ℝ) ≤
        R.iface.W nd := by
    intro nd hk
    simp only [Rest.iface, Rest.W, hk, hR, asmRest, asWa, Iface.inW, le_refl]
  intro Ω C S k e c hc' v hv hg hP hIH
  exact as_agg_spec R.iface hpre hfac hm H (fun h h' => LabValStd.unique h h') h0 hr hc hcm hi
    hlc hce hW S k e c hc' v hv hg hP hIH

end GI.Impl
