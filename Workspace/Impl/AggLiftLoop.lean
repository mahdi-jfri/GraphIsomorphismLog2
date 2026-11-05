module

public import Workspace.Impl.AggLiftChild
public import Workspace.Impl.MapGhost
public import Workspace.Impl.AggCombExact

@[expose] public section

/-!
# `LiftAndContinue` on all overcosets of a round, as a program

The program maps `lcChildF` over the list of overcosets (`mapQ_spec`). For each overcoset
`(ρ(σ_i), π⁻¹(E_i))` the output has a piece `[encPerm a_i, u_i]`: `e⁻¹ a_i` lies in the
overcoset and `u_i` is a canonical answer of the child on `e⁻¹ a_i` (`lcChild_spec`). The cost is
at most `n · lcB(2W + 6)` plus the costs of the child runs plus the overhead of the map.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Preimage NormalizedFactor)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

theorem lcX_mono {M M' : ℕ} (h : M ≤ M') : lcX M ≤ lcX M' := by
  unfold lcX; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

theorem lcB_mono (pre fac : Prim) {krC : ℕ → ℕ} (hkrm : Monotone krC) {M M' : ℕ} (h : M ≤ M') :
    lcB pre fac krC M ≤ lcB pre fac krC M' := by
  have hx := lcX_mono h
  unfold lcB Prim.boundSize
  have h1 : pre.c * (1000 * lcX M ^ 4 + 2) ^ pre.k ≤ pre.c * (1000 * lcX M' ^ 4 + 2) ^ pre.k :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
      have := Nat.pow_le_pow_left hx 4; omega) _)
  have h2 := Nat.mul_le_mul_left graphPreK (Nat.pow_le_pow_left hx 8)
  have h3 := hkrm hx
  have h4 := lc_liftLabCost_mono fac hx
  have h5 : gatherK * (40 * lcX M ^ 2) ^ 3 ≤ gatherK * (40 * lcX M' ^ 2) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
      have := Nat.pow_le_pow_left hx 2; omega) 3)
  have h6 : lcHierK * (7 * M + 20) ^ 2 ≤ lcHierK * (7 * M' + 20) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have h7 := Nat.mul_le_mul_left lcK (Nat.pow_le_pow_left hx 8)
  omega

/-- An overcoset as data: `σ`, the subgroup `E₀` and generators of `E₀`. -/
abbrev LcOver (q : ℕ) :=
  alternatingGroup (Fin q) × Subgroup (alternatingGroup (Fin q)) × List (Perm (Fin q))

/-- **`LiftAndContinue` on all overcosets meets its specification.** -/
theorem lcMap_spec (I : Iface) (hpre : Preimage) (hfac : NormalizedFactor) {Pg : Program}
    {F : Funs} {b f bpre jpre bkr blift sb sp jfac bg bh bset : ℕ} {krC : ℕ → ℕ}
    (hb : Pg.HasAt b (mapFuns b f))
    (hf : Pg.funs[f]? = some (lcChildF F bpre bkr blift bg bh))
    (hbpre : Pg.HasAt bpre (graphPreFuns bpre jpre))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hkr : LcKrOK Pg bkr krC) (hkrm : Monotone krC)
    (hlift : Pg.funs[blift]? = some (liftLabF sb sp jfac)) (hsb : ShiftAt Pg sb)
    (hsp : Pg.HasAt sp (pSplitFuns sp))
    (hjfac : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (hga : Pg.HasAt bg (gatherFuns bg))
    (hbh : Pg.funs[bh]? = some (lcHierF bset)) (hset : Pg.HasAt bset (setFuns bset))
    {e : Ω ≃ Fin k} {c : C → ℕ} {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C}
    (hcan : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    {L : GiantLabels S} (con : L.Constituent)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {sel : ℕ} (hsel : sel < S.hier.length) (cap : ℕ) (os : List (LcOver L.q))
    (hos : ∀ o ∈ os, gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype)
    (hcall : ∀ o ∈ os, ∀ (τ : Perm Ω) val,
      Canon e c val (lcChild S o.2.1 τ sel cap) →
      FunAll Pg F.cont val (I.Post .cont (lcChild S o.2.1 τ sel cap) e val)) :
    FunAll Pg b (.list [lcCtx (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) k L.q ps
        sel cap, .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)])
      (fun w cost => ∃ ws : List Val, w = .list ws ∧ ws.length = os.length ∧
        (∀ i (hi : i < os.length) (hw : i < ws.length), ∃ a u, ws[i] = .list [encPerm a, u] ∧
          (toFin e).symm a ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)) ∧
          AnsC e u (lcChild S os[i].2.1 ((toFin e).symm a) sel cap).answer) ∧
        ∃ cs : ℕ → ℕ, (∀ i (hi : i < os.length), ∃ τ ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)),
          ∃ (A : Set (Perm Ω)) (r : Run P₀ .cont (lcChild S os[i].2.1 τ sel cap) none A),
            (cs i : ℝ) ≤ r.total I.work) ∧
        cost ≤ os.length * lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC
            (2 * (Val.list [lcCtx (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) k L.q ps
              sel cap, .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)]).wt + 6) +
          ∑ i ∈ Finset.range os.length, cs i +
          mapQK * (os.length + 1) *
            ((Val.list [lcCtx (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) k L.q ps
              sel cap, .list (os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)]).wt + w.wt + 1)) := by
  set ctx := lcCtx (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) k L.q ps sel cap
    with hctx
  set xs := os.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2 with hxs
  set W := (Val.list [ctx, .list xs]).wt with hW
  set B := lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC (2 * W + 6) with hB
  have hsum := sum_wt_lt_wt_list [ctx, .list xs]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  have hxl : xs.length = os.length := List.length_map _
  refine (mapQ_spec (R := fun i w => ∀ hi : i < os.length, ∃ a u, w = .list [encPerm a, u] ∧
      (toFin e).symm a ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)) ∧
      AnsC e u (lcChild S os[i].2.1 ((toFin e).symm a) sel cap).answer)
    (Q := fun i cb => ∀ hi : i < os.length,
      ∃ τ ∈ L.rep os[i].1 • (L.lift os[i].2.1 : Set (Perm Ω)),
      ∃ (A : Set (Perm Ω)) (r : Run P₀ .cont (lcChild S os[i].2.1 τ sel cap) none A),
        (cb : ℝ) ≤ r.total I.work) (B := fun _ => B) hb ?_).mono ?_
  · intro i hi
    have hi' : i < os.length := hxl ▸ hi
    have hxi : xs[i] = lcOv (os[i].1 : Perm (Fin L.q)) os[i].2.2 := List.getElem_map _
    have hwi : xs[i].wt < (Val.list xs).wt := wt_getElem_lt xs i hi
    rw [hxi] at hwi ⊢
    have h := lcChild_spec I hpre hfac hf hbpre hjpre hkr hkrm hlift hsb hsp hjfac hga hbh hset
      hcan con hps hsel cap os[i].1 os[i].2.1 os[i].2.2 (hos _ (List.getElem_mem hi'))
      (fun τ val hv => hcall _ (List.getElem_mem hi') τ val hv)
    refine h.mono fun w cost ⟨hR, cb, hQ, hc⟩ => ⟨fun _ => hR, cb, fun _ => hQ, hc.trans ?_⟩
    refine Nat.add_le_add_right (lcB_mono _ _ hkrm ?_) _
    have := wt_list2_le ctx (lcOv (os[i].1 : Perm (Fin L.q)) os[i].2.2)
    have ectx : lcCtx (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) k L.q ps sel cap =
      ctx := rfl
    rw [ectx]
    omega
  · rintro w cost ⟨ws, rfl, hl, hR, cs, hQ, hc⟩
    refine ⟨ws, rfl, hl.trans hxl, fun i hi hw => hR i hw hi, cs,
      fun i hi => hQ i (hxl ▸ hi) hi, ?_⟩
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, hxl] at hc
    exact hc

/-- **The pieces of the children, in combine form.** If each entry of `ws` is `[encPerm a, u]`
with `u` a canonical answer `A_i(e⁻¹ a)`, then `ws` lists the pieces `cps`, and the set of
piece `i` is the image of `e⁻¹ a_i • A_i(e⁻¹ a_i)`. -/
theorem lc_cps (e : Ω ≃ Fin k) (Pr : ℕ → Perm Ω → Prop) (Ans : ℕ → Perm Ω → Set (Perm Ω))
    (ws : List Val)
    (h : ∀ i (hw : i < ws.length), ∃ a u, ws[i] = .list [encPerm a, u] ∧ Pr i ((toFin e).symm a) ∧
      AnsC e u (Ans i ((toFin e).symm a))) :
    ∃ cps : List (Perm (Fin k) × Acc k), ws = cps.map encPiece ∧
      ∀ i (hc : i < cps.length), Pr i ((toFin e).symm cps[i].1) ∧
        ceSet cps[i] = toFin e '' ((toFin e).symm cps[i].1 • Ans i ((toFin e).symm cps[i].1)) := by
  induction ws generalizing Pr Ans with
  | nil => exact ⟨[], rfl, fun i hc => absurd hc (by simp)⟩
  | cons w ws ih =>
    obtain ⟨cps, hws, hcps⟩ := ih (fun i => Pr (i + 1)) (fun i => Ans (i + 1))
      (fun i hw => h (i + 1) (by simp; omega))
    obtain ⟨a, u, hw0, hP, hA⟩ := h 0 (by simp)
    have hta : toFin e ((toFin e).symm a) = a := MulEquiv.apply_symm_apply _ _
    obtain ⟨acc, henc, hset⟩ := ce_contPiece e ((toFin e).symm a) hA
    rw [hta] at henc hset
    refine ⟨(a, acc) :: cps, ?_, ?_⟩
    · simp only [List.map_cons, List.cons.injEq]
      exact ⟨by simpa using hw0.trans henc, hws⟩
    · intro i hc
      cases i with
      | zero => exact ⟨hP, hset⟩
      | succ i => exact hcps i (by simpa using hc)

end GI.Impl
