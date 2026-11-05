module

public import Workspace.Impl.AggItemCfDeg
public import Workspace.Impl.AggItemS2b

@[expose] public section

/-!
# The degree of transitivity on the dominant orbit

`itCfFrF dom deg` runs on `⟨H⟩`, a group by generators. It lists the dominant orbit
`Φ = domSet H` in increasing order (`itDomF`, `it_dom_spec`) and runs the chain loop on it
(`itCfDegFuns`, `itCf_deg_spec`). The result is `[⟨Φ⟩, d]` with `d = transDeg H Φ`, the degree
that fixes the object of Case 2b (`orbitalOut`). The programs `col` and `orb` both start with it.

The cost is at most `itCfFrC hps W` for a group value of weight `W` (`it_cfFr_spec`). The
bound `itCfDegB` is the cost bound of the chain loop with all its parameters replaced by one
number `X` that dominates them (`itCf_degC_le`).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens pointwiseStab PointwiseStab)

variable {q : ℕ}

/-- The cost bound of the chain loop with every parameter at most `X`. -/
noncomputable def itCfDegB (hps : PointwiseStab) (X : ℕ) : ℕ :=
  X * ((pointwiseStabPrim hps).c *
        (2 * (X + 700 * (X + 1) ^ 6 + X + 2) + 8 + 3 + 2) ^ (pointwiseStabPrim hps).k +
      stabOrbitK * (2 * (X + 700 * (X + 1) ^ 6 + X + 2) + 8) ^ 9 +
      1000 * (X + (2 * (X + 700 * (X + 1) ^ 6 + 2 * X + 10) + 7) + X + 10)) +
    X * (100 * (X + X + (2 * (X + 700 * (X + 1) ^ 6 + 2 * X + 10) + 7) + 1)) +
    loopK * (X + 1) * (X + X + (2 * (X + 700 * (X + 1) ^ 6 + 2 * X + 10) + 7) + 1) +
    100 * (X + X + (2 * (X + 700 * (X + 1) ^ 6 + 2 * X + 10) + 7)) + 300

theorem itCf_degC_le (hps : PointwiseStab) (a gv : Val) (q N X : ℕ) (ha : a.wt ≤ X)
    (hg : gv.wt ≤ X) (hq : q ≤ X) (hN : N ≤ X) :
    itCfDegC hps a gv q N ≤ itCfDegB hps X := by
  unfold itCfDegC itCfDegD itCfDegM itCfDegY itCfDegG Prim.boundSize itCfDegB
  gcongr

theorem itCfDegB_mono (hps : PointwiseStab) {X Y : ℕ} (h : X ≤ Y) :
    itCfDegB hps X ≤ itCfDegB hps Y := by
  unfold itCfDegB
  gcongr

/-- On `⟨H⟩`: the sorted dominant orbit `Φ` and the degree of transitivity of `H` on it. -/
def itCfFrF (dom deg : ℕ) : Expr :=
  .letE (.call dom (.var 0))
    (.letE (.call deg (mk2 (.var 0) (.var 1))) (mk2 (.var 1) (.get (.var 2) (.nat 1))))

/-- The cost bound of `itCfFrF` on a group value of weight `W`. -/
noncomputable def itCfFrC (hps : PointwiseStab) (W : ℕ) : ℕ :=
  4 * itDomC W + 4 * itCfDegB hps (2 * (W + itDomC W) + 6) + 40 * (W + itDomC W) + 200

/-- **The degree of transitivity on the dominant orbit, as a program.** -/
theorem it_cfFr_spec (hps : PointwiseStab) {P : Program} {fr dom orb rng fd pd cnt deg jps : ℕ}
    (hfr : P.funs[fr]? = some (itCfFrF dom deg))
    (hdom : P.funs[dom]? = some (itDomF orb rng fd)) (horb : P.HasAt orb (orbitFuns orb))
    (hrng : P.HasAt rng (rangeFuns rng)) (hfd : P.HasAt fd (filterFuns fd pd))
    (hpd : P.funs[pd]? = some (acpDomF cnt)) (hcnt : P.HasAt cnt (countFuns cnt))
    (hdeg : P.HasAt deg (itCfDegFuns deg jps)) (hj : P.prims[jps]? = some (pointwiseStabPrim hps))
    (hs : List (Perm (Fin q))) :
    FunDet P fr (encGroup hs)
      (.list [encPts (domSet (gens hs)).sort, .nat (transDeg (gens hs) (domSet (gens hs)))])
      (itCfFrC hps (encGroup hs).wt) := by
  set W := (encGroup hs).wt with hW
  set xs := (domSet (gens hs)).sort with hxs
  set d := transDeg (gens hs) (domSet (gens hs)) with hd
  have hD := it_dom_spec hdom horb hrng hfd hpd hcnt hs
  rw [← hxs] at hD
  have hxW : (encPts xs).wt < itDomC W := hD.wt_lt
  have dD := Det.call (Det.var' (P := P) (env := [encGroup hs]) (i := 0) rfl) hD
  have hnd : xs.Nodup := Finset.sort_nodup _ _
  have hmem : ∀ b, b ∈ xs ↔ b ∈ domSet (gens hs) := fun b => Finset.mem_sort _
  have hpres : ∀ h ∈ gens hs, ∀ a ∈ domSet (gens hs), h a ∈ domSet (gens hs) :=
    fun h hh a ha => apply_mem_domSet hh ha
  have hG := (itCf_deg_spec hps hdeg hj hs (domSet (gens hs)) xs hpres hnd hmem).wt_lt
  set a : Val := .list [encGroup hs, encPts xs] with ha
  have ea : (Val.list [encGroup hs, encPts xs]).wt = a.wt := rfl
  set X := 2 * (W + itDomC W) + 6 with hX
  have hq1 : q + 1 ≤ W := by
    have := S_le_wt_encGroup hs
    nlinarith
  have hN : xs.length < (encPts xs).wt := by
    have := length_lt_wt_list (xs.map fun j : Fin q => Val.nat j.val)
    rw [List.length_map] at this
    rw [itCf_encPts_eq]; exact this
  have haX : a.wt ≤ X := by have := wt_list2_le (encGroup hs) (encPts xs); omega
  have hB := itCf_degC_le hps a (encGroup hs) q xs.length X haX (by omega) (by omega) (by omega)
  have hdq : d ≤ q := by
    have h1 := (transDeg_spec (gens hs) (domSet (gens hs))).2
    have h2 := Finset.card_le_univ (domSet (gens hs))
    rw [Fintype.card_fin] at h2
    omega
  refine FunDet.intro hfr (EvalAll.letE dD fun w1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  have dm := Det.mk2 (Det.var' (P := P) (env := [encGroup hs, encPts xs]) (i := 0) rfl)
    (Det.var' (P := P) (env := [encGroup hs, encPts xs]) (i := 1) rfl)
  have hcall : EvalAll P [encGroup hs, encPts xs] (.call deg (mk2 (.var 0) (.var 1)))
      (fun w c => ∃ (gs : List (Perm (Fin q))) (f : ℕ), w = .list [encGroup gs, .nat d, .nat f] ∧
        w.wt < itCfDegB hps X ∧ c ≤ (W + 1 + ((encPts xs).wt + 1) + 2 * a.wt + 7) +
          itCfDegB hps X + itCfDegB hps X + 1) :=
    EvalAll.call_funAll dm fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      exact hG.mono fun w c ⟨⟨gs, f, hw, hc⟩, hwc⟩ => ⟨gs, f, hw, by omega, by omega⟩
  refine EvalAll.letE hcall fun w2 c2 h2 => ?_
  obtain ⟨gs, f, rfl, hw2, hc2⟩ := h2
  refine (Det.mk2 (Det.var' (P := P) (env := [encGroup hs, encPts xs,
      .list [encGroup gs, .nat d, .nat f]]) (i := 1) rfl)
    (Det.get' (Det.var' (P := P) (env := [encGroup hs, encPts xs,
      .list [encGroup gs, .nat d, .nat f]]) (i := 2) rfl) (Det.nat 1) rfl)).post
    fun c hc => ⟨rfl, ?_⟩
  have := wt_list2_le (encPts xs) (.nat d)
  have := wt_nat_le d
  have := wt_nat_le 1
  have eW : itDomC (encGroup hs).wt = itDomC W := rfl
  unfold itCfFrC
  rw [← hX]
  omega

end GI.Impl
