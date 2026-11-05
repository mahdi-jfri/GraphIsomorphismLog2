module

public import Workspace.Impl.AggItemS2b
public import Workspace.Impl.AggItemSrc
public import Workspace.Impl.AggItemCol

@[expose] public section

/-!
# The source tuple of the round, as a program

The items choose the source tuple by the case of `H = π(F_x)` (`itSrc`): in Case 2b the six
smallest points of the dominant orbit (`stSrc2b`), in Case 3 the first tuple that passes the test
of the Design Lemma on the refined colors `d` of `x` (`stSrc3`), and the zero tuple otherwise.
`itSrcOf H d` is this choice as a function of `H` and `d` (`itSrc_eq_of`).

The program `itSrcF` runs on `[st, w, code]`, where `st` is the items' start state, `w = [d, d']`
is the output of the refinement call and `code` is the case code of `H`. It branches on the
code:
* `2`: the group of the second parts of `fx` (`it_grp_spec`), its sorted dominant orbit
  (`it_dom_spec`), and its first six points (`it_s2b_spec`);
* `3`: the search of the Design Lemma on `[d, q, κ]` (`stDSrc3_spec`);
* otherwise: `κ + 1` zeros.
`it_srcp_spec`: it returns the entries of `itSrcOf (gens (fx.map snd)) d`. No primitive is
called.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encPts encKColoring)
open GI.Machine (BinOp)

variable {Ω C : Type} {k : ℕ}

/-- **The source tuple as a function of the group and the refined colors.** -/
noncomputable def itSrcOf {q κ : ℕ} (H : Subgroup (Perm (Fin q))) (d : (Fin κ → Fin q) → ℕ)
    (hq : 0 < q) : Fin (κ + 1) → Fin q :=
  match aggCase H with
  | .twoB => if h : 8 ≤ (domSet H).card then stSrc2b _ h else fun _ => ⟨0, hq⟩
  | .three => stSrc3 d (Nat.lt_succ_self _) hq
  | .one => fun _ => ⟨0, hq⟩
  | .twoA => fun _ => ⟨0, hq⟩

/-- `itSrc` is `itSrcOf` of the group and the refined colors of `x`. -/
theorem itSrc_eq_of {S : State Ω C} {L : GiantLabels S} (Ag : Aggregation P₀ S L) (J : JointFn) :
    itSrc Ag J = itSrcOf (itX0 Ag J).grp (itX0 Ag J).col (it_q_pos Ag) := rfl

theorem it_code_two {a : AggCase} (h : AggCase.code a = 2) : a = .twoB := by
  cases a <;> simp_all [AggCase.code]

theorem it_code_three {a : AggCase} (h : AggCase.code a = 3) : a = .three := by
  cases a <;> simp_all [AggCase.code]

theorem it_code_le (a : AggCase) : AggCase.code a ≤ 3 := by
  cases a <;> simp [AggCase.code]

/-- Outside Cases 2b and 3 the source tuple is the zero tuple. -/
theorem itSrcOf_zero {q κ : ℕ} (H : Subgroup (Perm (Fin q))) (d : (Fin κ → Fin q) → ℕ)
    (hq : 0 < q) (h2 : AggCase.code (aggCase H) ≠ 2) (h3 : AggCase.code (aggCase H) ≠ 3) :
    itSrcOf H d hq = fun _ => ⟨0, hq⟩ := by
  unfold itSrcOf
  cases hc : aggCase H <;> simp_all [AggCase.code]

/-- On `[st, w, code]`: the entries of the source tuple. -/
def itSrcF (grp dom s2b s3 rep κ : ℕ) : Expr :=
  .ite (.arith .eq (arg 2) (.nat 2))
    (.call s2b (.call dom (.call grp
      (mk2 (.get (.get (arg 0) (.nat 1)) (.nat 1)) (.get (arg 0) (.nat 3))))))
    (.ite (.arith .eq (arg 2) (.nat 3))
      (.call s3 (mk3 (.get (arg 1) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (.nat 1)) (.nat κ)))
      (.call rep (mk2 (.nat (κ + 1)) (.nat 0))))

/-- The cost bound of `itSrcF` for the size parameter `W`. -/
def itSrcPC (W : ℕ) : ℕ :=
  itGrpC W + itDomC (100 * (W + 1) ^ 3) + itS2bC (6 * (W + 1) ^ 2) +
    stDSrcK * (30 * (W + 1) ^ 2 + 2 * W + 21) ^ 36 + 10 ^ 7 * (W + 1) ^ 3

/-- The weight bound of the source tuple. -/
theorem it_wt_src {q κ : ℕ} (t : Fin (κ + 1) → Fin q) {W : ℕ} (hq : q ≤ W) (hκ : κ + 1 ≤ W) :
    (natList (stL fun i => (t i : ℕ))).wt ≤ 5 * (W + 1) ^ 2 :=
  wt_natList_le_sq (fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    have := (t i).2; omega) (by simp [stL]; omega)

set_option maxHeartbeats 2000000 in
/-- **The source tuple as a program.** On `[st, [d, d'], code]`, with `st` the items' start state,
`d` the refined colors of `x` and `code` the case code of `H = ⟨fx.map snd⟩`, `itSrcF` returns
the entries of `itSrcOf H d`. -/
theorem it_srcp_spec {P : Program} {f grp dom s2b s3 rep rb mp sf app orb rng fd pd cnt
      pw fs sp des dc rb' : ℕ}
    (hf : P.funs[f]? = some (itSrcF grp dom s2b s3 rep P₀.κ))
    (hgrp : P.funs[grp]? = some (itGrpF rb mp app))
    (hrb : P.HasAt rb (rangeFuns rb)) (hmp : P.HasAt mp (mapFuns mp sf))
    (hsf : P.funs[sf]? = some itSndF) (happ : P.HasAt app (appendFuns app))
    (hdom : P.funs[dom]? = some (itDomF orb rng fd)) (horb : P.HasAt orb (orbitFuns orb))
    (hrng : P.HasAt rng (rangeFuns rng)) (hfd : P.HasAt fd (filterFuns fd pd))
    (hpd : P.funs[pd]? = some (acpDomF cnt)) (hcnt : P.HasAt cnt (countFuns cnt))
    (hs2b : P.funs[s2b]? = some (itS2bF app rep P₀.κ)) (hrep : P.HasAt rep (replicateFuns rep))
    (hs3 : P.funs[s3]? = some (stDSrcF pw fs rb' dc)) (hpw : P.HasAt pw (stDPowFuns pw))
    (hfs : P.HasAt fs (findFuns fs sp)) (hsp : P.funs[sp]? = some (stDSrcPF des dc))
    (hdes : StDesOK P des) (hdc : P.HasAt dc (stDDecFuns dc)) (hrb' : P.HasAt rb' (rangeFuns rb'))
    (sv : Val) {q : ℕ} (ps fx fy : List (Perm (Fin k) × Perm (Fin q)))
    (tt : List (TestTuple q P₀.κ)) (cr : TestTuple q P₀.κ → TestTuple q P₀.κ → Bool)
    (d d' : (Fin P₀.κ → Fin q) → ℕ) (hd : ∀ x, d x < 2 * q ^ P₀.κ)
    (hd' : ∀ x, d' x < 2 * q ^ P₀.κ) (hq : 24 ≤ q) {W : ℕ}
    (hW : (itSt sv k q ps fx fy tt cr).wt + q ^ P₀.κ + q + P₀.κ ≤ W) :
    FunDet P f (.list [itSt sv k q ps fx fy tt cr, .list [encKColoring d, encKColoring d'],
        .nat (AggCase.code (aggCase (gens (fx.map Prod.snd))))])
      (natList (stL fun i => (itSrcOf (gens (fx.map Prod.snd)) d (by omega) i : ℕ)))
      (itSrcPC W) := by
  have hκ5 : 5 ≤ P₀.κ := by norm_num [P₀]
  have hκ7 : 7 ≤ P₀.κ := by norm_num [P₀]
  set st := itSt sv k q ps fx fy tt cr with hst
  set H := gens (fx.map Prod.snd) with hH
  set wv := Val.list [encKColoring d, encKColoring d'] with hwv
  set cv := Val.nat (AggCase.code (aggCase H)) with hcv
  set v := Val.list [st, wv, cv] with hv
  have hstl : st = .list [sv, .list [.nat k, .nat q], .list (ps.map pairV), .list (fx.map pairV),
      .list (fy.map pairV), stCv tt cr] := rfl
  have hkq : (Val.list [.nat k, .nat q]).wt < st.wt := by
    rw [hstl]; exact wt_le_wt_list (by simp)
  have hfxw : (Val.list (fx.map pairV)).wt < st.wt := by
    rw [hstl]; exact wt_le_wt_list (by simp)
  have hqw : (Val.nat q).wt < (Val.list [.nat k, .nat q]).wt := wt_le_wt_list (by simp)
  have hW1 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW23 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hqκ : (q ^ P₀.κ + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  -- weights of the input
  have wd := wt_encKColoring_le hd
  have wd' := wt_encKColoring_le hd'
  have hww : wv.wt ≤ _ := wt_list2_le (encKColoring d) (encKColoring d')
  have hcode : AggCase.code (aggCase H) ≤ 3 := it_code_le _
  have hcw : cv.wt ≤ 5 := (wt_nat_le _).trans (by omega)
  have hvw : v.wt ≤ _ := wt_list3_le st wv cv
  have hW3p : 1 ≤ (W + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  set W' := 200 * (W + 1) ^ 3 with hW'
  have hvW : v.wt ≤ W' := by omega
  have ewv : (Val.list [encKColoring d, encKColoring d']).wt = wv.wt := rfl
  have hwW : wv.wt ≤ W' := by omega
  -- the code test
  have dcode : ∀ m : ℕ, m ≤ 3 → StDC P [v] (.arith .eq (arg 2) (.nat m))
      (.nat (if AggCase.code (aggCase H) = m then 1 else 0)) 7 0 W' := fun m hm =>
    (StDC.arith' (StDC.arg (vs := [st, wv, cv]) (rest := []) (j := 2) rfl hvW (by omega)
      (by rw [← hcv]; omega)) (StDC.nat m (by omega)) (z := if AggCase.code (aggCase H) = m then 1 else 0) rfl (by
        have : (if AggCase.code (aggCase H) = m then 1 else 0) ≤ 1 := by split_ifs <;> omega
        omega)).mono (by omega) le_rfl
  -- `q` and `fx`
  set stvs : List Val := [sv, .list [.nat k, .nat q], .list (ps.map pairV), .list (fx.map pairV),
      .list (fy.map pairV), stCv tt cr] with hstvs
  have hst0 : [st, wv, cv][0]? = some (.list stvs) := by rw [hstl]; rfl
  have a0 : StDC P [v] (arg 0) (.list stvs) 3 0 W' :=
    StDC.arg (vs := [st, wv, cv]) (rest := []) (j := 0) hst0 hvW (by omega) (by rw [← hstl]; omega)
  have hkqw : (Val.list [.nat k, .nat q]).wt ≤ W' := by omega
  have h1 : stvs[1]? = some (.list [.nat k, .nat q]) := rfl
  have h2 : [Val.nat k, .nat q][1]? = some (.nat q) := rfl
  have n1 : StDC P [v] (.nat 1) (.nat 1) 1 0 W' := StDC.nat 1 (by omega)
  have dkq := StDC.get a0 n1 h1 hkqw
  have dq := StDC.get dkq n1 h2 (by omega)
  -- the three branches
  have hsrcw := it_wt_src (itSrcOf H d (by omega)) (W := W) (by omega) (by omega)
  have bzero : AggCase.code (aggCase H) ≠ 2 → AggCase.code (aggCase H) ≠ 3 →
      StDC P [v] (.call rep (mk2 (.nat (P₀.κ + 1)) (.nat 0)))
        (natList (stL fun i => (itSrcOf H d (by omega) i : ℕ))) 6 (10 ^ 6 * (W + 1) ^ 3) W' := by
    intro h2 h3
    have e : itSrcOf H d (by omega) = fun _ => ⟨0, by omega⟩ := itSrcOf_zero H d _ h2 h3
    have hR := (replicate_spec hrep (P₀.κ + 1) (.nat 0)).mono (Q' := fun w c =>
      w = .list (List.replicate (P₀.κ + 1) (.nat 0)) ∧ c ≤ 10 ^ 6 * (W + 1) ^ 3) (by
        rintro w c ⟨rfl, hc⟩
        refine ⟨rfl, hc.trans ?_⟩
        have h1 := wt_list2_le (.nat (P₀.κ + 1)) (.nat 0)
        have h2 := wt_nat_le (P₀.κ + 1)
        have h3 := wt_nat_le 0
        have h4 : (Val.list (List.replicate (P₀.κ + 1) (Val.nat 0))).wt ≤ 5 * (W + 1) ^ 2 := by
          have := wt_natList_le_sq (xs := List.replicate (P₀.κ + 1) 0) (B := W)
            (fun x hx => by rw [List.eq_of_mem_replicate hx]; omega) (by simp; omega)
          simpa [natList] using this
        have := Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (show P₀.κ + 1 + 1 ≤ W + 1 by omega))
          (show (Val.list [.nat (P₀.κ + 1), .nat 0]).wt + (P₀.κ + 1) +
            (Val.list (List.replicate (P₀.κ + 1) (Val.nat 0))).wt + 1 ≤ 20 * (W + 1) ^ 2 by omega)
        have e2 : loopModK * (W + 1) * (20 * (W + 1) ^ 2) = 20000 * (W + 1) ^ 3 := by
          simp only [loopModK]; ring
        omega)
    have eo : Val.list (List.replicate (P₀.κ + 1) (.nat 0)) =
        natList (stL fun i => (itSrcOf H d (by omega) i : ℕ)) := by
      rw [e]; simp [natList, stL, List.map_const']
    rw [← eo]
    have hw2 := wt_list2_le (.nat (P₀.κ + 1)) (.nat 0)
    have := wt_nat_le (P₀.κ + 1)
    exact (StDC.call (StDC.mk2 (StDC.nat (P₀.κ + 1) (by omega)) (StDC.nat 0 (by omega))
      (by have := wt_nat_le 0; omega) (by omega)) hR (by rw [eo]; omega)).mono le_rfl
      (by omega)
  have b3 : aggCase H = .three →
      StDC P [v] (.call s3 (mk3 (.get (arg 1) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (.nat 1))
        (.nat P₀.κ))) (natList (stL fun i => (itSrcOf H d (by omega) i : ℕ))) 21
        (stDSrcK * (30 * (W + 1) ^ 2 + 2 * W + 21) ^ 36) W' := by
    intro h3
    have e : itSrcOf H d (by omega) = stSrc3 d (Nat.lt_succ_self _) (by omega) := by
      unfold itSrcOf; rw [h3]
    rw [e]
    have hin := wt_list3_le (encKColoring d) (.nat q) (.nat P₀.κ)
    have w4 := wt_nat_le q
    have w5 := wt_nat_le P₀.κ
    have hS := stDSrc3_spec hs3 hpw hfs hsp hdes hdc hrb' d (by omega) (by omega) hd
      (N := 30 * (W + 1) ^ 2 + 2 * W + 20) (by omega)
    have hw1 : [st, wv, cv][1]? = some wv := rfl
    have hw0 : [encKColoring d, encKColoring d'][0]? = some (encKColoring d) := rfl
    have dd := StDC.get (StDC.arg (P := P) (rest := []) (W := W') hw1 hvW (by omega) (by omega))
      (StDC.nat (P := P) (env := [v]) (W := W') 0 (by omega)) hw0 (by omega)
    have := StDC.call (StDC.mk3 dd dq (StDC.nat P₀.κ (by omega)) (by omega) (by omega)) hS
      (by
        have := it_wt_src (stSrc3 (ℓ := P₀.κ + 1) d (Nat.lt_succ_self _) (by omega)) (W := W)
          (by omega) (by omega)
        omega)
    exact this.mono (by omega) (by
      have : 30 * (W + 1) ^ 2 + 2 * W + 20 + 1 = 30 * (W + 1) ^ 2 + 2 * W + 21 := by omega
      rw [this]; omega)
  have b2 : aggCase H = .twoB →
      StDC P [v] (.call s2b (.call dom (.call grp
        (mk2 (.get (.get (arg 0) (.nat 1)) (.nat 1)) (.get (arg 0) (.nat 3))))))
        (natList (stL fun i => (itSrcOf H d (by omega) i : ℕ))) 20
        (itGrpC W + itDomC (100 * (W + 1) ^ 3) + itS2bC (6 * (W + 1) ^ 2)) W' := by
    intro h2
    have h8 : 8 ≤ (domSet H).card := st_domSet_eight hq h2
    have e : itSrcOf H d (by omega) = stSrc2b _ h8 := by
      unfold itSrcOf; rw [h2, dif_pos h8]
    rw [e]
    have hgr := it_grp_spec hgrp hrb hmp hsf happ fx (W := W) (by omega) (by omega)
    have hgw := it_grp_wt fx (W := W) (by omega) (by omega)
    have hD := (it_dom_spec hdom horb hrng hfd hpd hcnt (fx.map Prod.snd)).mono
      (itDomC_mono hgw)
    have hΦn : (domSet H).card ≤ q := by simpa using Finset.card_le_univ (domSet H)
    have hDw : (encPts (domSet H).sort).wt ≤ 5 * (W + 1) ^ 2 := by
      rw [acp_encPts_eq]
      have := wt_natList_le_sq (xs := (domSet H).sort.map Fin.val) (B := W)
        (fun x hx => by
          obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
          have := y.2; omega) (by simp; omega)
      simpa [natList, List.map_map, Function.comp_def] using this
    have hS := it_s2b_spec hs2b happ hrep (domSet H) h8 hκ7 (W := 6 * (W + 1) ^ 2) (by omega)
      (by omega)
    have h3 : stvs[3]? = some (.list (fx.map pairV)) := rfl
    have dfx := StDC.get a0 (StDC.nat (P := P) (env := [v]) (W := W') 3 (by omega)) h3 (by omega)
    have hqf := wt_list2_le (.nat q) (.list (fx.map pairV))
    have d1 := StDC.call (StDC.mk2 dq dfx (by omega) (by omega)) hgr (by omega)
    have ez : (encPts (domSet (gens (fx.map Prod.snd))).sort).wt = (encPts (domSet H).sort).wt :=
      rfl
    have d2 := StDC.call d1 hD (by omega)
    have d3 := StDC.call d2 hS (by
      have := it_wt_src (stSrc2b (ℓ := P₀.κ + 1) (domSet H) h8) (W := W) (by omega) (by omega)
      omega)
    exact d3.mono (by omega) (by omega)
  -- the branch
  have dif := StDC.ite (dcode 2 (by omega))
    (fun hx => (b2 (it_code_two (by
      by_contra hc
      exact hx (if_neg hc)))).mono le_rfl le_rfl)
    (fun hx => by
      have hn2 : AggCase.code (aggCase H) ≠ 2 := fun h => by
        rw [if_pos h] at hx; exact absurd hx (by norm_num)
      exact StDC.ite (dcode 3 (by omega))
        (fun hy => (b3 (it_code_three (by
          by_contra hc
          exact hy (if_neg hc)))).mono le_rfl le_rfl)
        (fun hy => by
          have hn3 : AggCase.code (aggCase H) ≠ 3 := fun h => by
            rw [if_pos h] at hy; exact absurd hy (by norm_num)
          exact bzero hn2 hn3)
        (by omega))
    (by omega)
  refine FunDet.intro hf (dif.det.mono ?_)
  unfold itSrcPC
  rw [hW']
  omega

end GI.Impl
