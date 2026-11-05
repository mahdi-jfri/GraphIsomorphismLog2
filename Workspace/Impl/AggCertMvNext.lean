module

public import Workspace.Impl.AggCertMvClose

@[expose] public section

/-!
# The move program: the next window call of a round

When representatives remain, `cpNextF` (at `b + 9`) computes the window colors of the next
representative (`wp_spec`), drops it from the list (`tail`), and returns the next window call
with the new program state. `cp_answer_next` says what this output stands for.

Helpers used also by the first window call of a round:

* `cp_inLen_unpack`: the length facts of `CpInLen`, read back on a known `inner`;
* `cp_ansGens_length`: one answer gives at most `k² + 1` generators;
* `cp_wt_codes`: the window color codes are small;
* `cp_zv_det`: reading the colors of the current string;
* `cp_bud_wp`: the window colors within the budget.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

section Help

variable {k q : ℕ}

theorem cp_inLen_unpack {D : ℕ} {as gs hs : List (Perm (Fin k))} {dv : Val}
    {incP : List (Fin (k + q))} {a : Perm (Fin k)}
    (h : CpInLen k q D (cpInnerV as gs hs dv incP a)) :
    gs.length + (as.length + 1) * (k ^ 2 + 1) ≤ D * (k ^ 2 + 1) ∧ hs.length ≤ k ^ 2 ∧
      (∃ f : Fin k → ℕ, dv = encFun f ∧ ∀ i, f i ≤ 1) ∧ incP.length ≤ k := by
  obtain ⟨as', gs', hs', f, incP', a', heq, h1, h2, h3, h4⟩ := h
  simp only [cpInnerV, encPts_eq, Val.list.injEq, List.cons.injEq, encGroup,
    GI.Cited.encPerms, and_true, true_and] at heq
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := heq
  have l1 := congrArg List.length e1
  have l2 := congrArg List.length e2
  have l3 := congrArg List.length e3
  have l5 := congrArg List.length e5
  simp only [List.length_map, List.length_cons] at l1 l2 l3 l5
  refine ⟨by rw [l1, l2]; exact h1, by omega, ⟨f, e4, h3⟩, by omega⟩

theorem cp_ansGens_length {a : Perm (Fin k)} {u : Val}
    {o : Option (Perm (Fin k) × List (Perm (Fin k)))} (h : AnsOV u o) :
    (ansGens a o).length ≤ k ^ 2 + 1 := by
  match o, h with
  | none, _ => simp [ansGens]
  | some (x, gs), ⟨_, hl⟩ => simp only [ansGens, cosGens, List.length_cons, List.length_map]; omega

theorem cp_stageGens_snoc (dn : List (Perm (Fin k) × Option (Perm (Fin k) × List (Perm (Fin k)))))
    (a : Perm (Fin k)) (o : Option (Perm (Fin k) × List (Perm (Fin k)))) :
    stageGens (dn ++ [(a, o)]) = stageGens dn ++ ansGens a o := by
  simp [stageGens, List.flatMap_append]

end Help

section Codes

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
  [Fintype S.dom]

theorem cp_wt_codesX (z : Ω → C) (a : Perm (Fin k)) :
    (natList (winCodesX e c S z a)).wt ≤ k * (4 * k + 5) + 4 := by
  have h := wt_natList_le (B := 2 * k) (xs := winCodesX e c S z a) fun x hx => by
    simp only [winCodesX, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact (posOf_le _ _).trans (length_winList e c S z a).le
  simp only [winCodesX, List.length_map, List.length_finRange] at h
  unfold winCodesX
  have : 2 * (2 * k) + 5 = 4 * k + 5 := by ring
  rw [this] at h
  omega

theorem cp_wt_codesY (z : Ω → C) (a : Perm (Fin k)) :
    (natList (winCodesY e c S z a)).wt ≤ k * (4 * k + 5) + 4 := by
  have h := wt_natList_le (B := 2 * k) (xs := winCodesY e c S z a) fun x hx => by
    simp only [winCodesY, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact (posOf_le _ _).trans (length_winList e c S z a).le
  simp only [winCodesY, List.length_map, List.length_finRange] at h
  unfold winCodesY
  have : 2 * (2 * k) + 5 = 4 * k + 5 := by ring
  rw [this] at h
  omega

end Codes

section Wp

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
  [Fintype S.dom] (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

/-- **The window colors, within the budget.** -/
theorem cp_bud_wp {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    {dv xv : Val} (hdv : DomVal e dv S.dom) (z : Ω → C) (hxv : ColorVal e c xv z)
    (hcode : ∀ v, c (z v) < 2 * k) (a : Perm (Fin k)) {W : ℕ}
    (hW : 10 ^ 10 * (k + 1) ^ 12 ≤ W) :
    CpFB Pg (cpWp b) (.list [dv, xv, encPerm a]) W (cpG hst hpre hm W)
      (fun w => w = .list [natList (winCodesX e c S z a), natList (winCodesY e c S z a)]) := by
  have h := wp_spec hat.wp hat.dom hdv z hxv hcode a
  have hx := cp_wt_codesX (e := e) (c := c) (S := S) z a
  have hy := cp_wt_codesY (e := e) (c := c) (S := S) z a
  have := wt_list2_le (natList (winCodesX e c S z a)) (natList (winCodesY e c S z a))
  have h2 : k * (4 * k + 5) ≤ 5 * (k + 1) ^ 2 := by nlinarith
  have h12 : (k + 1) ^ 2 ≤ (k + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by omega) _
  refine CpFB.det h ?_ (by omega) rfl
  have a1 : wpK * (3 * k + 2) ^ 6 ≤ wpK * (W + 1) ^ 6 := by
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 6)
    have : k + 1 ≤ (k + 1) ^ 12 := Nat.le_self_pow (by omega) _
    omega
  have a2 := cp_poly_le (W := W) (K := wpK) (d := 6) (by simp [wpK]) (by norm_num)
    (by have : 1 ≤ (k + 1) ^ 12 := Nat.one_le_pow _ _ (by omega)
        omega)
  have := cpG_poly hst hpre hm (W := W)
  omega

end Wp

end GI.Impl

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

section Next

variable {k : ℕ} {Ω C : Type} [Finite Ω] [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ}
  {S : State Ω C} [Fintype S.dom] {L : GiantLabels S}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

/-- Reading the colors of the current string, `y` if `s` is set and `x` otherwise. -/
theorem cp_zv_det {P : Program} {env : List Val} {W : ℕ} {ks : List Val} {x : Val}
    (h0 : env[0]? = some (.list [.list ks, x])) (hw : (Val.list [.list ks, x]).wt ≤ W)
    {ps ss : List Val} (hp : ks[0]? = some (.list ps)) (hs : ps[0]? = some (.list ss))
    {s : Bool} (h2 : ks[2]? = some (boolVal s)) {xv yv : Val} (hx : ss[3]? = some xv)
    (hy : ss[4]? = some yv) :
    Det P env cpZv (if s then yv else xv) (12 * (W + 20)) := by
  have hxw : (if s then yv else xv).wt ≤ W := by
    have h1 : (Val.list ks).wt < W :=
      lt_of_lt_of_le (cp_wt_get (vs := [.list ks, x]) (j := 0) rfl) hw
    have h3 := (cp_wt_get hs).trans ((cp_wt_get hp).trans h1)
    split_ifs
    · exact ((cp_wt_get hy).trans h3).le
    · exact ((cp_wt_get hx).trans h3).le
  have hc := cp_rdK (P := P) h0 hw h2 (by omega)
  refine (Det.ite hc (ct := 5 * (W + 20)) (ce := 5 * (W + 20)) (fun hne => ?_) (fun he => ?_)).mono ?_
  · have : s = true := by cases s <;> simp_all
    subst this
    exact cp_rdS h0 hw hp hs hy (by omega)
  · have : s = false := by cases s <;> simp_all
    subst this
    exact cp_rdS h0 hw hp hs hx (by omega)
  · rw [Nat.max_self]; omega


set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **The next window call of a round.** -/
theorem cp_next_spec {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e c S L πd sv gp osA D) {NT M₀ Bw W : ℕ}
    (hBw : cpBw k L.q (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)).wt NT M₀ D
      ≤ Bw) (hW : 10 ^ 4 * (Bw + 2) ^ 2 ≤ W)
    {m f : ℕ} {acc : List (StagePair S)} {T : Finset (Fin L.q)} {σ : CpSt k L.q}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    {acc' : List (Set (Perm S.dom))}
    {dn : List (Perm (Fin k) × Option (Perm (Fin k) × List (Perm (Fin k))))} {a a' : Perm (Fin k)}
    {as hs : List (Perm (Fin k))} {dv : Val} {incl : List S.dom}
    (hm' : m = cpMeas (Fintype.card S.dom) D
      (.win acc T σ.Ts σ.s σ.t ((a' :: as).map (domOfPos e S)) acc')) (hmf : m ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hNT : σ.res.length + σ.Ts.length + 1 ≤ NT)
    (hR : CpRoundInv e πd σ acc T rec) (ht : σ.t < Fintype.card S.dom)
    (hne : inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t ≠ ∅)
    (hl : ((grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t,
      kernelIn (cpPhi S πd T) (grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t)),
      (dn.map Prod.fst ++ a :: a' :: as).map (domOfPos e S)) ∈ rec)
    (hG : ∀ b ∈ dn.map Prod.fst ++ a :: a' :: as, (toFin e).symm b ∈ S.G)
    (ho : ∀ p ∈ dn, AnsSet e p.2 (cpCall πd T σ.s σ.t (domOfPos e S p.1)).answer)
    (hacc : acc' = cpAcc S (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t
      ((dn.map Prod.fst ++ [a]).map (domOfPos e S)))
    (hgv : GroupValC k (encGroup hs)
      (groupFin e (S.liftGroup (kernelIn (cpPhi S πd T)
        (grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t)))))
    (hdv : DomVal e dv (Subtype.val '' (inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t : Set S.dom)))
    (hnd : incl.Nodup) (hinc : ∀ v, v ∈ incl ↔ v ∈ inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t)
    {o : Option (Perm (Fin k) × List (Perm (Fin k)))}
    (hao : AnsSet e o (cpCall πd T σ.s σ.t (domOfPos e S a)).answer)
    (hT : T = σ.T) (hlen : CpLen D σ)
    (hin : CpInLen k L.q D (cpInnerV as (stageGens (dn ++ [(a, o)])) hs dv
      (incl.map (domPos e L.q)) a'))
    (harg : (Val.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
        (cpInnerV (a' :: as) (stageGens dn) hs dv (incl.map (domPos e L.q)) a),
      .list ((stageGens (dn ++ [(a, o)])).map encPerm)]).wt ≤ 4 * Bw) :
    CpFB Pg (b + 9) (.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
        (cpInnerV (a' :: as) (stageGens dn) hs dv (incl.map (domPos e L.q)) a),
      .list ((stageGens (dn ++ [(a, o)])).map encPerm)]) W
      (2 * cpG hst hpre hm W + 5000 * (W + 20))
      (CpMvPost e S L πd (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) D Bw M₀
        NT m ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R
          (.win acc T σ.Ts σ.s σ.t ((a' :: as).map (domOfPos e S)) acc')) '' Cands rec) f) := by
  have hcan := ctx.canon
  obtain ⟨gv0, dv0, xv, yv, hv, rv, hgv0, hdv0, hxv, hyv, hhv, hrv, hsv⟩ := ctx.canon.val
  subst hsv
  set par := cpParV k L.q (Fintype.card S.dom) D (.list [.nat k, gv0, dv0, xv, yv, hv, rv,
    boolVal S.floor, .nat S.h, .nat S.N]) (gpV gp) (encPts osA) with hpar
  set inner := cpInnerV (a' :: as) (stageGens dn) hs dv (incl.map (domPos e L.q)) a with hinner
  set gs' := stageGens (dn ++ [(a, o)]) with hgs'
  set inner' := cpInnerV as gs' hs dv (incl.map (domPos e L.q)) a' with hinner'
  obtain ⟨hW1, hW2, hW3, hW4, hW5⟩ := cp_W_facts hBw hW
  have hWB : 10 ^ 4 * (Bw + 2) ≤ W := by
    have : Bw + 2 ≤ (Bw + 2) ^ 2 := Nat.le_self_pow (by omega) _
    omega
  have hk12 : k + L.q + 1 ≤ (k + L.q + 1) ^ 12 := Nat.le_self_pow (by omega) _
  set ks := σ.vals par inner with hks
  have hsv : σ.val par inner = .list ks := rfl
  set gV : Val := .list (gs'.map encPerm) with hgV
  have hwB : (Val.list [.list ks, gV]).wt ≤ 4 * Bw := by rw [← hsv]; exact harg
  have hwW : (Val.list [.list ks, gV]).wt ≤ W := by omega
  have hp0 : ks[0]? = some (.list [.list [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor,
    .nat S.h, .nat S.N], .list [.nat k, .nat L.q], gpV gp, .nat (Fintype.card S.dom), .nat D,
    encPts osA, pSplitCtx k L.q, .nat (k + L.q)]) := rfl
  have hs0 : [Val.list [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h, .nat S.N],
    .list [.nat k, .nat L.q], gpV gp, .nat (Fintype.card S.dom), .nat D,
    encPts osA, pSplitCtx k L.q, .nat (k + L.q)][0]? = some (.list [.nat k, gv0, dv0, xv, yv, hv,
      rv, boolVal S.floor, .nat S.h, .nat S.N]) := rfl
  have hi0 : ks[10]? = some (.list [.list ((a' :: as).map encPerm),
    .list ((stageGens dn).map encPerm), encGroup hs, dv, encPts (incl.map (domPos e L.q)),
    encPerm a]) := rfl
  have h0 : ∀ rest : List Val, (Val.list [.list ks, gV] :: rest)[0]? =
      some (.list [.list ks, gV]) := fun _ => rfl
  refine CpFB.intro hat.next ?_
  rw [hsv]
  unfold cpNextF
  -- the window colors of `a'`
  have hz : ColorVal e c (if σ.s then yv else xv) (cpZ S σ.s) := by
    cases σ.s <;> simpa [cpStr]
  have hcode : ∀ v, c (cpZ S σ.s v) < 2 * k := by
    intro v; cases σ.s
    · exact (hcan.colors v).1
    · exact (hcan.colors v).2
  have hasW : (Val.list ((a' :: as).map encPerm)).wt < (Val.list [.list ks, gV]).wt := by
    have := cp_wt_get (vs := ks) (j := 10) hi0
    have := cp_wt_get (vs := [.list ((a' :: as).map encPerm),
      .list ((stageGens dn).map encPerm), encGroup hs, dv, encPts (incl.map (domPos e L.q)),
      encPerm a]) (j := 0) rfl
    have := cp_wt_get (vs := [.list ks, gV]) (j := 0) rfl
    omega
  have ha'W : (encPerm a').wt < W :=
    (cp_wt_get (vs := (a' :: as).map encPerm) (j := 0) rfl).trans (hasW.trans_le hwW)
  have dA := Det.mk3 (cp_rdS (P := Pg) (h0 []) hwW hp0 hs0 (j := 2) (v := dv0) rfl (by omega))
    (cp_zv_det (P := Pg) (h0 []) hwW hp0 hs0 (s := σ.s) rfl rfl rfl)
    (Det.rd (a := 4) (j := 0) (cp_rdI (P := Pg) (h0 []) hwW hi0 (j := 0) rfl (by omega)) le_rfl rfl
      ha'W.le (by omega))
  have hdv0W : dv0.wt < (Val.list [.list ks, gV]).wt := by
    have := cp_wt_get (vs := ks) (j := 0) hp0
    have := cp_wt_get hs0
    have := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 2) rfl
    have := cp_wt_get (vs := [.list ks, gV]) (j := 0) rfl
    omega
  have hzW : (if σ.s then yv else xv).wt < (Val.list [.list ks, gV]).wt := by
    have := cp_wt_get (vs := ks) (j := 0) hp0
    have := cp_wt_get hs0
    have := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 3) rfl
    have := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 4) rfl
    have := cp_wt_get (vs := [.list ks, gV]) (j := 0) rfl
    split_ifs <;> omega
  have hAW : (Val.list [dv0, if σ.s then yv else xv, encPerm a']).wt ≤ W := by
    have := wt_list3_le dv0 (if σ.s then yv else xv) (encPerm a')
    have := cp_wt_get (vs := (a' :: as).map encPerm) (j := 0) (v := encPerm a') rfl
    omega
  have hW2' : 10 ^ 10 * (k + 1) ^ 12 ≤ W := by
    have : (k + 1) ^ 12 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_left (by omega) 12
    omega
  have hbw := cp_bud_wp hst hpre hm hat hdv0 (cpZ S σ.s) hz hcode a' hW2'
  -- the weights of the new values
  have hres : σ.res.length ≤ NT := by omega
  have hTsl : σ.Ts.length ≤ NT := by omega
  have hc : σ.cache.length ≤ M₀ := by omega
  have hIV := cp_wt_inner hin
  have hIVB : inner'.wt ≤ Bw := by
    have e1 : 10 ^ 4 * (D + 1) * (k + L.q + 1) ^ 6 ≤ 10 ^ 6 * (D + 1) * (k + L.q + 1) ^ 6 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
    omega
  have hKS := cp_wt_state (par := par) hlen hR.loglen hTsl hres hc hIV (u := .list [])
    (by simp only [wt_list_nil]; have : 1 ≤ (k + 1) ^ 6 := Nat.one_le_pow _ _ (by omega); omega)
  have hKV : (σ.val par inner').wt < Bw :=
    lt_of_lt_of_le (cp_wt_get (vs := [σ.val par inner', .list []]) (j := 0) rfl) (hKS.trans hBw)
  have hparB : 4 * par.wt ≤ Bw := hW4
  have hsvP : (Val.list [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]).wt < par.wt := cp_wt_get (vs := [Val.list [.nat k, gv0, dv0, xv, yv, hv, rv,
        boolVal S.floor, .nat S.h, .nat S.N], .list [.nat k, .nat L.q], gpV gp,
        .nat (Fintype.card S.dom), .nat D, encPts osA, pSplitCtx k L.q, .nat (k + L.q)]) (j := 0)
        rfl
  have hhvP := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 5) (v := hv) rfl
  have hNP := cp_wt_get (vs := [.nat k, gv0, dv0, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
      .nat S.N]) (j := 9) (v := .nat S.N) rfl
  have hhsI : (encGroup hs).wt < inner'.wt := cp_wt_get (vs := [.list (as.map encPerm),
      .list (gs'.map encPerm), encGroup hs, dv, encPts (incl.map (domPos e L.q)), encPerm a'])
      (j := 2) rfl
  have hdvI : dv.wt < inner'.wt := cp_wt_get (vs := [.list (as.map encPerm),
      .list (gs'.map encPerm), encGroup hs, dv, encPts (incl.map (domPos e L.q)), encPerm a'])
      (j := 3) rfl
  have hB6 : 10 ^ 6 ≤ Bw := by
    have : 1 ≤ (D + 1) * (k + L.q + 1) ^ 6 :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
    have e1 : 10 ^ 6 * (D + 1) * (k + L.q + 1) ^ 6 = 10 ^ 6 * ((D + 1) * (k + L.q + 1) ^ 6) := by
      ring
    omega
  have hcx := cp_wt_codesX (e := e) (c := c) (S := S) (cpZ S σ.s) a'
  have hcy := cp_wt_codesY (e := e) (c := c) (S := S) (cpZ S σ.s) a'
  have hkk : k * (4 * k + 5) + 4 ≤ Bw := by
    have : k * (4 * k + 5) ≤ 5 * (k + L.q + 1) ^ 2 := by nlinarith
    have : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have : (k + L.q + 1) ^ 6 ≤ (D + 1) * (k + L.q + 1) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
    have e1 : 10 ^ 6 * (D + 1) * (k + L.q + 1) ^ 6 = 10 ^ 6 * ((D + 1) * (k + L.q + 1) ^ 6) := by
      ring
    omega
  set WV := winVal' k (encGroup hs) dv (natList (winCodesX e c S (cpZ S σ.s) a'))
    (natList (winCodesY e c S (cpZ S σ.s) a')) hv S.N with hWVd
  have hWV : WV.wt ≤ 21 * Bw + 14 := by
    rw [hWVd, winVal']
    refine (wt_list_le_of _ (c := Bw) ?_).trans (by simp only [List.length_cons, List.length_nil]; clear * -; omega)
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    have := wt_nat_le k; have := wt_nat_le 0; have := wt_nat_le 2
    have : (boolVal false).wt ≤ 2 := wt_nat_le 0
    have : k ≤ k * (4 * k + 5) := Nat.le_mul_of_pos_right _ (by omega)
    rcases hx with h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first | omega | (simp; omega)
  have hTop : (Val.list [.nat 1, .nat (modeCode .cont), WV, σ.val par inner']).wt ≤ W := by
    refine (wt_list_le_of _ (c := 21 * Bw + 14) ?_).trans (by simp only [List.length_cons, List.length_nil]; omega)
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    have := wt_nat_le 1; have := wt_nat_le (modeCode .cont)
    have : modeCode .cont = 1 := rfl
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  refine (CpEB.letE (CpEB.call (CpEB.det dA le_rfl hAW
      (Q := fun v => v = .list [dv0, if σ.s then yv else xv, encPerm a']) rfl)
    fun v hv _ => hv ▸ hbw) (Cb := cpG hst hpre hm W + 4000 * (W + 20))
    fun wv hwv hwvW => ?_).mono (by clear * - hAW; omega) fun _ h => h
  subst hwv
  have h1 : ∀ rest : List Val, (Val.list [.list ks, gV] :: rest)[0]? =
      some (.list [.list ks, gV]) := fun _ => rfl
  refine (CpEB.letE (CpEB.call (CpEB.det (cp_rdI (P := Pg) (h1 _) hwW hi0 (j := 0)
      (v := .list ((a' :: as).map encPerm)) rfl (by omega)) le_rfl (hasW.trans_le hwW).le
      (Q := fun v => v = .list (encPerm a' :: as.map encPerm)) rfl)
    fun v hv hvw => hv ▸ cp_bud_tail hst hpre hm hat.tail _ _ (hv ▸ hvw))
    (Cb := 3900 * (W + 20)) fun tv htv htW => ?_).mono (by clear * - hasW hwW; omega)
    fun _ h => h
  subst htv
  set env := [Val.list [.list ks, gV], .list [natList (winCodesX e c S (cpZ S σ.s) a'),
    natList (winCodesY e c S (cpZ S σ.s) a')], .list (as.map encPerm)] with henv
  have hgVW : gV.wt ≤ W := (cp_wt_get (vs := [.list ks, gV]) (j := 1) rfl).le.trans hwW
  have dI := cp_mkList' (P := Pg) (env := env) (W := W) (c := 6 * (W + 20)) (v := inner')
    [(.var 2, .list (as.map encPerm)), (GI.Lang.arg 1, gV), (cpIf 2, encGroup hs), (cpIf 3, dv),
      (cpIf 4, encPts (incl.map (domPos e L.q))), (.get (cpIf 0) (.nat 0), encPerm a')] rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (Det.rv (P := Pg) (env := env) (i := 2) rfl htW).mono (by omega)
      · exact (Det.rd (a := 1) (j := 1) (Det.rv (P := Pg) (env := env) (i := 0) rfl hwW) le_rfl
          rfl hgVW (by omega)).mono (by omega)
      · exact (cp_rdI (P := Pg) (h1 _) hwW hi0 (j := 2) rfl (by omega)).mono (by omega)
      · exact (cp_rdI (P := Pg) (h1 _) hwW hi0 (j := 3) rfl (by omega)).mono (by omega)
      · exact (cp_rdI (P := Pg) (h1 _) hwW hi0 (j := 4) rfl (by omega)).mono (by omega)
      · exact (Det.rd (a := 4) (j := 0) (cp_rdI (P := Pg) (h1 _) hwW hi0 (j := 0) rfl (by omega))
          le_rfl rfl ha'W.le (by omega)).mono (by omega)) (by omega)
  have dK := cp_mkList' (P := Pg) (env := env) (W := W) (c := 50 * (W + 20))
    (v := σ.val par inner')
    [(cpKf 0, par), (cpKf 1, .list (σ.Ts.map (tsV k))), (cpKf 2, boolVal σ.s),
      (cpKf 3, .list (σ.res.map resV)), (cpKf 4, .list (σ.cache.map ckEntV)),
      (cpKf 5, gpV σ.p0), (cpKf 6, gpV σ.px), (cpKf 7, .nat σ.t), (cpKf 8, gpV σ.ps),
      (cpKf 9, encPts σ.osP),
      (Expr.mkList [.var 2, GI.Lang.arg 1, cpIf 2, cpIf 3, cpIf 4, .get (cpIf 0) (.nat 0)], inner'),
      (cpKf 11, tsV k σ.T), (cpKf 12, .list (σ.lz.map cpSgV)), (cpKf 13, .list (σ.lx.map cpSgV)),
      (cpKf 14, .list (σ.logs.map cpLogV))] rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 0) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 1) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 2) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 3) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 4) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 5) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 6) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 7) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 8) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 9) rfl (by omega)).mono (by omega)
      · exact dI.mono (by simp only [List.length_cons, List.length_nil]; omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 11) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 12) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 13) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 14) rfl (by omega)).mono (by omega))
      (by omega)
  have hwpW : (Val.list [natList (winCodesX e c S (cpZ S σ.s) a'),
      natList (winCodesY e c S (cpZ S σ.s) a')]).wt ≤ W := hwvW
  have dWv := cp_mkList' (P := Pg) (env := env) (W := W) (c := 6 * (W + 20)) (v := WV)
    [(cpSf 0, .nat k), (cpIf 2, encGroup hs), (cpIf 3, dv),
      (.get (.var 1) (.nat 0), natList (winCodesX e c S (cpZ S σ.s) a')),
      (.get (.var 1) (.nat 1), natList (winCodesY e c S (cpZ S σ.s) a')), (cpSf 5, hv),
      (.nil, .list []), (.nat 0, .nat 0), (.nat 2, .nat 2), (cpSf 9, .nat S.N)] rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (cp_rdS (P := Pg) (h1 _) hwW hp0 hs0 (j := 0) rfl (by omega)).mono (by omega)
      · exact (cp_rdI (P := Pg) (h1 _) hwW hi0 (j := 2) rfl (by omega)).mono (by omega)
      · exact (cp_rdI (P := Pg) (h1 _) hwW hi0 (j := 3) rfl (by omega)).mono (by omega)
      · exact (Det.rd (a := 1) (j := 0) (Det.rv (P := Pg) (env := env) (i := 1) rfl hwpW) le_rfl
          rfl (by omega) (by omega)).mono (by omega)
      · exact (Det.rd (a := 1) (j := 1) (Det.rv (P := Pg) (env := env) (i := 1) rfl hwpW) le_rfl
          rfl (by omega) (by omega)).mono (by omega)
      · exact (cp_rdS (P := Pg) (h1 _) hwW hp0 hs0 (j := 5) rfl (by omega)).mono (by omega)
      · exact Det.nil.mono (by omega)
      · exact (Det.nat 0).mono (by omega)
      · exact (Det.nat 2).mono (by omega)
      · exact (cp_rdS (P := Pg) (h1 _) hwW hp0 hs0 (j := 9) rfl (by omega)).mono (by omega))
      (by omega)
  have hmc : modeCode .cont = 1 := rfl
  have dTop := cp_mkList' (P := Pg) (env := env) (W := W) (c := 900 * (W + 20))
    (v := .list [.nat 1, .nat (modeCode .cont), WV, σ.val par inner'])
    [(.nat 1, .nat 1), (.nat (modeCode .cont), .nat (modeCode .cont)),
      (cpWinE (cpIf 2) (cpIf 3) (.var 1), WV),
      (Expr.mkList [cpKf 0, cpKf 1, cpKf 2, cpKf 3, cpKf 4, cpKf 5, cpKf 6, cpKf 7, cpKf 8, cpKf 9,
        Expr.mkList [.var 2, GI.Lang.arg 1, cpIf 2, cpIf 3, cpIf 4, .get (cpIf 0) (.nat 0)],
        cpKf 11, cpKf 12, cpKf 13, cpKf 14], σ.val par inner')] rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact (Det.nat 1).mono (by omega)
      · exact (Det.nat _).mono (by rw [hmc]; omega)
      · exact dWv.mono (by simp only [List.length_cons, List.length_nil]; omega)
      · exact dK.mono (by simp only [List.length_cons, List.length_nil]; omega)) hTop
  have hwt : ∀ u', AnsC e u' (cpCall πd T σ.s σ.t (domOfPos e S a')).answer →
      (Val.list [CpSt.val par σ inner', u']).wt ≤ Bw := fun u' hu' =>
    (cp_wt_state hlen hR.loglen hTsl hres hc hIV (cp_wt_ans hu')).trans hBw
  refine CpEB.det dTop ?_ hTop
    (Or.inl (cp_answer_next (u := .list []) ctx.inj hcan hhv ctx.good ctx.tr hm' hmf hM hNT hR ht hne hl hG ho
      hacc hgv hdv hnd hinc hao hT hlen hin hwt))
  simp only [List.length_cons, List.length_nil]
  omega


end Next

end GI.Impl
