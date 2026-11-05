module

public import Workspace.Impl.AggItemCfRRead
public import Workspace.Impl.AggItemCfRDegree
public import Workspace.Impl.AggItemS2b

@[expose] public section

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited Equiv Equiv.Perm

/-- Recompute the dominant set and degree, then read the supplied refined table. -/
def itCfROrbF (dm dg rd : ℕ) : Expr :=
  .letE (.call dm (arg 1))
    (.letE (.call dg (mk2 (arg 1) (.var 1)))
      (.call rd (mk4 (arg 0) (arg 3) (arg 2) (.var 2))))

/-- Compose the dominant-set, degree and table-reader programs. The costs
of those three calls remain separate so that their bounds can be supplied
without expanding the stabilizer-chain proof in this lemma. -/
theorem itCfR_orb_of_calls {P : Program} {f dm dg rd : ℕ}
    (hf : P.funs[f]? = some (itCfROrbF dm dg rd))
    {q ℓ : ℕ} (hs : List (Perm (Fin q))) (t : Fin ℓ → Fin q) (R : Refiner2 q)
    (domv : Val) {Bd Bg Br : ℕ}
    (hdom : FunDet P dm (encGroup hs) domv Bd)
    (hdeg : FunDet P dg (.list [encGroup hs, domv])
      (.nat (transDeg (gens hs) (domSet (gens hs)))) Bg)
    (hread : FunDet P rd
      (.list [.nat q, encKColoring (R (orbColOut (gens hs) t)), stTv t,
        .nat (transDeg (gens hs) (domSet (gens hs)))])
      (itCfOutV (orbitalOut R (gens hs) t)) Br) :
    FunDet P f (itCfOrbIn hs t (R (orbColOut (gens hs) t)))
      (itCfOutV (orbitalOut R (gens hs) t))
      (100000 * ((itCfOrbIn hs t (R (orbColOut (gens hs) t))).wt + Bd + Bg + Br + q + 10)) := by
  set inp := itCfOrbIn hs t (R (orbColOut (gens hs) t))
  set cv := encKColoring (R (orbColOut (gens hs) t))
  set d := transDeg (gens hs) (domSet (gens hs))
  set out := itCfOutV (orbitalOut R (gens hs) t)
  set W := 100 * (inp.wt + Bd + Bg + Br + q + 10)
  have hW5 : 5 ≤ W := by dsimp [W]; omega
  have wg : (encGroup hs).wt < inp.wt := wt_le_wt_list (by simp [inp, itCfOrbIn])
  have wc : cv.wt < inp.wt := wt_le_wt_list (by simp [inp, cv, itCfOrbIn])
  have wt : (stTv t).wt < inp.wt := wt_le_wt_list (by simp [inp, itCfOrbIn])
  have wq : (Val.nat q).wt < inp.wt := wt_le_wt_list (by simp [inp, itCfOrbIn])
  have wd := wt_nat_le d
  have hdq : d ≤ q := (transDeg_spec _ _).2.trans
    ((Finset.card_le_univ _).trans_eq (Fintype.card_fin q))
  have wdom := hdom.wt_lt
  have wout := hread.wt_lt
  change out.wt < Br at wout
  have wdg := wt_list2_le (encGroup hs) domv
  have wrd := wt_list4_le (.nat q) cv (stTv t) (.nat d)
  have gq (rest : List Val) : StDC P (inp :: rest) (arg 0) (.nat q) 3 0 W :=
    StDC.arg rfl (by show inp.wt ≤ W; dsimp [W]; omega) (by omega) (by dsimp [W]; omega)
  have gg (rest : List Val) : StDC P (inp :: rest) (arg 1) (encGroup hs) 3 0 W :=
    StDC.arg rfl (by show inp.wt ≤ W; dsimp [W]; omega) (by omega) (by dsimp [W]; omega)
  have gt (rest : List Val) : StDC P (inp :: rest) (arg 2) (stTv t) 3 0 W :=
    StDC.arg rfl (by show inp.wt ≤ W; dsimp [W]; omega) (by omega) (by dsimp [W]; omega)
  have gc (rest : List Val) : StDC P (inp :: rest) (arg 3) cv 3 0 W :=
    StDC.arg rfl (by show inp.wt ≤ W; dsimp [W]; omega) (by omega) (by dsimp [W]; omega)
  have cdom := StDC.call (gg []) hdom (by dsimp [W]; omega)
  have vdom : StDC P [inp, domv] (.var 1) domv 1 0 W :=
    StDC.var' rfl (by dsimp [W]; omega)
  have cdeg := StDC.call (StDC.mk2 (gg [domv]) vdom (by dsimp [W]; omega) (by omega))
    hdeg (by dsimp [W]; omega)
  have vdeg : StDC P [inp, domv, .nat d] (.var 2) (.nat d) 1 0 W :=
    StDC.var' rfl (by dsimp [W]; omega)
  have crd := StDC.call (StDC.mk4 (gq [domv, .nat d]) (gc [domv, .nat d])
    (gt [domv, .nat d]) vdeg (by dsimp [W]; omega) (by omega)) hread
    (by dsimp [W]; omega)
  have res := StDC.letE cdom (StDC.letE cdeg crd (by dsimp [W]; omega))
    (by dsimp [W]; omega)
  exact StDC.funDet hf res (by dsimp [W]; omega)

/-- The cost of recomputing the dominant set and degree and reading the object.
The remaining cost task is to collect the stabilizer-chain bound into
one monomial in the input weight. -/
noncomputable def itCfRCompC (hps : PointwiseStab) {q ℓ : ℕ}
    (hs : List (Perm (Fin q))) (t : Fin ℓ → Fin q) (r : (Fin 2 → Fin q) → ℕ) : ℕ :=
  let xs := (domSet (gens hs)).sort
  let a := Val.list [encGroup hs, encPts xs]
  100000 * ((itCfOrbIn hs t r).wt + itDomC (encGroup hs).wt +
    10 * (a.wt + itCfDegC hps a (encGroup hs) q xs.length + q + 10) +
    10 ^ 16 * ((itCfOrbIn hs t r).wt + 1) ^ 4 + q + 10)

/-- The complete orbital computation, from function-table and module facts.
This is correctness with a compositional cost bound, before collecting
that bound into the object-stage monomial. -/
theorem itCfR_orb_from_programs (hps : PointwiseStab) {P : Program}
    {f dm dg dd jps orb rng fd pd cnt rd tb mb rw rm ce : ℕ}
    (hf : P.funs[f]? = some (itCfROrbF dm dg rd))
    (hdm : P.funs[dm]? = some (itDomF orb rng fd))
    (horb : P.HasAt orb (orbitFuns orb)) (hrng : P.HasAt rng (rangeFuns rng))
    (hfd : P.HasAt fd (filterFuns fd pd)) (hpd : P.funs[pd]? = some (acpDomF cnt))
    (hcnt : P.HasAt cnt (countFuns cnt))
    (hdg : P.funs[dg]? = some (itCfRDegreeF dd))
    (hdd : P.HasAt dd (itCfDegFuns dd jps))
    (hj : P.prims[jps]? = some (pointwiseStabPrim hps))
    (hrd : P.funs[rd]? = some (itCfRReadF tb ce))
    (htb : P.funs[tb]? = some (itCfRTableF mb rng))
    (hmb : P.HasAt mb (mapFuns mb rw)) (hrw : P.funs[rw]? = some (itCfRRowF rm rng))
    (hrm : P.HasAt rm (mapFuns rm ce)) (hce : P.funs[ce]? = some itCfRCellF)
    {q ℓ : ℕ} (hs : List (Perm (Fin q))) (t : Fin ℓ → Fin q) (R : Refiner2 q) :
    FunDet P f (itCfOrbIn hs t (R (orbColOut (gens hs) t)))
      (itCfOutV (orbitalOut R (gens hs) t))
      (itCfRCompC hps hs t (R (orbColOut (gens hs) t))) := by
  have hdom := it_dom_spec hdm horb hrng hfd hpd hcnt hs
  have hdeg := itCfR_degree_spec hps hdg hdd hj hs (domSet (gens hs))
    (domSet (gens hs)).sort (fun _ hh _ ha => apply_mem_domSet hh ha)
    (Finset.sort_nodup _ _) (fun _ => Finset.mem_sort _)
  set r := R (orbColOut (gens hs) t)
  set M := (itCfOrbIn hs t r).wt
  have hg : (encGroup hs).wt < M := wt_le_wt_list (by simp [M, itCfOrbIn])
  have hr : (encKColoring r).wt < M := wt_le_wt_list (by simp [M, itCfOrbIn])
  have ht : (stTv t).wt < M := wt_le_wt_list (by simp [M, itCfOrbIn])
  have hq : q ≤ M := by
    have h := S_le_wt_encGroup hs
    have hqg : q + 1 ≤ (encGroup hs).wt :=
      (Nat.le_mul_of_pos_left _ (by omega)).trans h
    omega
  have hdq : transDeg (gens hs) (domSet (gens hs)) ≤ q :=
    (transDeg_spec _ _).2.trans ((Finset.card_le_univ _).trans_eq (Fintype.card_fin q))
  have hlen : (stDL r).length = q * q := by rw [stDL_length, pow_two]
  have htl : ∀ u ∈ stL (fun i => (t i : ℕ)), u < q := by
    intro u hu
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hu
    exact (t i).isLt
  have hreader := itCfR_read_spec hrd htb hmb hrng hrw hrm hce
    (stDL r) (stL fun i => (t i : ℕ)) q (transDeg (gens hs) (domSet (gens hs)))
    hlen htl (N := M) (by rw [natList_stDL]; exact hr.le) ht.le hq (hdq.trans hq)
  rw [itCfROut_eq] at hreader
  rw [natList_stDL] at hreader
  exact itCfR_orb_of_calls hf hs t R _ hdom hdeg hreader

end GI.Impl
