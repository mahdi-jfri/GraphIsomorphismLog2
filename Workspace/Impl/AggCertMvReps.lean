import Workspace.Impl.AggCertMvWin
import Workspace.Impl.AggCertStart
import Workspace.Impl.AggCosets

/-!
# The move program: the representatives of a round

`cpRepsF` (at `b + 4`) runs on `[kst, key, i]`, where `key` is the cache key of the pair
`(A, N)` of the round and `i` the index that the cache lookup found. On a hit it returns the
cached representatives. On a miss it computes the orbit of the label tuple of `T` under the
graph form of `A` (`graphTup_spec`), keeps the group elements, splits them into pairs, keeps
their first parts, and adds the new entry in front of the cache. `cp_reps_spec` is the result
used later: the new cache is good for a longer record, and the record holds the returned
representatives for `(A, N)`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)
open GI.Machine (BinOp)

section Help

/-- A list whose entries all lie in the range of `f` is the image of a list. -/
theorem cp_lift_list {α β : Type*} (f : α → β) :
    ∀ l : List β, (∀ y ∈ l, ∃ x, f x = y) → ∃ l' : List α, l'.map f = l
  | [], _ => ⟨[], rfl⟩
  | y :: l, h => by
    obtain ⟨x, hx⟩ := h y (List.mem_cons_self ..)
    obtain ⟨l', hl'⟩ := cp_lift_list f l fun z hz => h z (List.mem_cons_of_mem _ hz)
    exact ⟨x :: l', by rw [List.map_cons, hx, hl']⟩

/-- A list without repeats that lists a set has the size of the set. -/
theorem cp_length_eq_ncard {α : Type*} [DecidableEq α] {l : List α} {s : Set α} (hnd : l.Nodup)
    (hmem : ∀ y, y ∈ l ↔ y ∈ s) : l.length = s.ncard := by
  have : s = (l.toFinset : Set α) := by
    ext y; simp [hmem]
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

/-- A list of at most `D` small values has weight `O(D (k + q)⁶)`. -/
theorem cp_wt_listD {k q D : ℕ} {vs : List Val} (hl : vs.length ≤ D)
    (h : ∀ v ∈ vs, v.wt ≤ 100 * (k + q + 1) ^ 2) :
    (Val.list vs).wt ≤ 201 * ((D + 1) * (k + q + 1) ^ 6) + 4 := by
  have h1 := cp_wt_list hl h
  have h2 : (k + q + 1) ^ 2 ≤ (k + q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 1 ≤ (k + q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h4 : D * (2 * (100 * (k + q + 1) ^ 2) + 1) ≤ (D + 1) * (201 * (k + q + 1) ^ 6) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h5 : (D + 1) * (201 * (k + q + 1) ^ 6) = 201 * ((D + 1) * (k + q + 1) ^ 6) := by ring
  omega

/-- The weight of one pair of the orbit module. -/
theorem cp_wt_tupElt {k q : ℕ} (y : List (Fin (k + q))) (hy : y.length ≤ q)
    (g : Perm (Fin (k + q))) :
    (GI.Lang.encPair ptsKey (y, g)).wt ≤ 100 * (k + q + 1) ^ 2 := by
  have h1 := wt_ptsKey_le y
  have h2 := wt_encPerm_le g
  have h3 := wt_list2_le (natList (ptsKey y)) (encPerm g)
  have h4 : y.length * (2 * (k + q) + 5) ≤ (k + q + 1) * (5 * (k + q + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h5 : (k + q + 1) * (5 * (k + q + 1)) = 5 * (k + q + 1) ^ 2 := by ring
  have h6 : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold GI.Lang.encPair
  simp only at h1 h2 h3 ⊢
  omega

end Help

section Read

variable {P : Program} {W : ℕ} {env : List Val} {ks vs : List Val}

theorem cp_rdKsV (h0 : env[0]? = some (.list vs)) (hw : (Val.list vs).wt ≤ W)
    (hk : vs[0]? = some (.list ks)) : Det P env cpKs (.list ks) (2 * (W + 20)) :=
  Det.rd (Det.rv h0 hw) le_rfl hk ((cp_wt_get hk).trans_le hw).le (by omega)

theorem cp_rdKV (h0 : env[0]? = some (.list vs)) (hw : (Val.list vs).wt ≤ W)
    (hk : vs[0]? = some (.list ks)) {j : ℕ} {v : Val} (hv : ks[j]? = some v) (hj : j ≤ 15) :
    Det P env (cpKf j) v (3 * (W + 20)) := by
  have h1 : (Val.list ks).wt < W := (cp_wt_get hk).trans_le hw
  exact Det.rd (cp_rdKsV h0 hw hk) le_rfl hv ((cp_wt_get hv).trans h1).le hj

theorem cp_rdPV (h0 : env[0]? = some (.list vs)) (hw : (Val.list vs).wt ≤ W)
    (hk : vs[0]? = some (.list ks)) {ps : List Val} (hp : ks[0]? = some (.list ps)) {j : ℕ}
    {v : Val} (hv : ps[j]? = some v) (hj : j ≤ 15) : Det P env (cpPf j) v (4 * (W + 20)) := by
  have h1 : (Val.list ks).wt < W := (cp_wt_get hk).trans_le hw
  have h2 := (cp_wt_get hp).trans h1
  exact Det.rd (cp_rdKV h0 hw hk hp (by omega)) le_rfl hv ((cp_wt_get hv).trans h2).le hj

end Read

section Steps

variable {k q : ℕ}

/-- The step of the map of second parts. -/
theorem cp_sec_step {P : Program} {f : ℕ} (hf : P.funs[f]? = some cpSecF)
    (p : List (Fin (k + q)) × Perm (Fin (k + q))) (hp : p.1.length ≤ q) :
    FunDet P f (.list [.nat 0, GI.Lang.encPair ptsKey p]) (encPerm p.2)
      (500 * (k + q + 1) ^ 2) := by
  have g1 := Det.arg' (P := P) (vs := [.nat 0, GI.Lang.encPair ptsKey p]) (rest := []) (j := 1) rfl
  refine FunDet.intro hf ((Det.get' g1 (Det.nat 1) (v := encPerm p.2) rfl).mono ?_)
  have w1 := cp_wt_tupElt p.1 hp p.2
  simp only [Prod.mk.eta] at w1
  have w2 := wt_list2_le (.nat 0) (GI.Lang.encPair ptsKey p)
  have w3 := wt_nat_le 0
  have w5 := wt_encPerm_le p.2
  have a3 : 1 ≤ (k + q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

end Steps


section Reps

variable {k : ℕ} {Ω C : Type} [Finite Ω] [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ}
  {S : State Ω C} [Fintype S.dom] {L : GiantLabels S}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
/-- **The representatives of a round.** On `[kst, key, i]`, with `i` the index found by the
cache lookup, the program returns representatives `as` of the cosets of `N` in `A` and a new
cache `c'`; `c'` is good for a longer record `rec'`, which holds `as` for `(A, N)`. -/
theorem cp_reps_spec {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e c S L πd sv gp osA D) {NT M₀ Bw W : ℕ}
    (hBw : cpBw k L.q (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)).wt NT M₀ D
      ≤ Bw) (hW : 10 ^ 4 * (Bw + 2) ^ 2 ≤ W)
    {σ : CpSt k L.q} {acc : List (StagePair S)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (hR : CpRoundInv e πd σ acc σ.T rec) (hlen : CpLen D σ) {inner : Val}
    {ns : List (Perm (Fin k) × Perm (Fin L.q))}
    (hns : PairGens e L (S.liftGroup (kernelIn (cpPhi S πd σ.T)
      (grp (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t))) ns)
    (hnsl : ns.length ≤ (k + L.q) ^ 2)
    (hwA : (Val.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) inner,
      ckKeyV σ.ps ns, .nat (σ.cache.findIdx (ckTest σ.ps ns))]).wt ≤ 4 * Bw) :
    CpFB Pg (b + 4) (.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
        inner, ckKeyV σ.ps ns, .nat (σ.cache.findIdx (ckTest σ.ps ns))]) W
      (5 * cpG hst hpre hm W + 200 * (W + 20))
      (fun w => ∃ (as : List (Perm (Fin k))) (c' : List (CacheEntry k L.q))
        (rec' : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))),
        w = .list [.list (as.map encPerm), .list (c'.map ckEntV)] ∧ CacheOK' e c' rec' ∧
        Cands rec' ⊆ Cands rec ∧ c'.length ≤ σ.cache.length + 1 ∧
        ((grp (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t,
          kernelIn (cpPhi S πd σ.T) (grp (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t)),
          as.map (domOfPos e S)) ∈ rec' ∧
        (∀ a ∈ as, (toFin e).symm a ∈ S.G) ∧ as.length ≤ D ∧
        ∀ ent ∈ c', ent.1.length ≤ (k + L.q) ^ 2 ∧ ent.2.1.length ≤ (k + L.q) ^ 2 ∧
          ent.2.2.length ≤ D) := by
  set par := cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA) with hpar
  obtain ⟨hW1, hW2, hW3, hW4, hW5⟩ := cp_W_facts hBw hW
  have hA : grp (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t ≤ S.domGroup :=
    (grp_le _ _ _).trans Pgrp_le
  have hAP : grp (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t ≤ Pgrp S.domGroup πd σ.T :=
    grp_le _ _ _
  have hN : kernelIn (cpPhi S πd σ.T) (grp (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t) ≤
      S.domGroup := inf_le_left.trans hA
  have hps := hR.ps
  set ks := σ.vals par inner with hks
  have hsv : σ.val par inner = .list ks := rfl
  set i := σ.cache.findIdx (ckTest σ.ps ns) with hi
  set vs : List Val := [.list ks, ckKeyV σ.ps ns, .nat i] with hvs
  have hvsB : (Val.list vs).wt ≤ 4 * Bw := by rw [hvs, ← hsv]; exact hwA
  have hwW : (Val.list vs).wt ≤ W := by omega
  have h0 : ∀ rest : List Val, (Val.list vs :: rest)[0]? = some (.list vs) := fun _ => rfl
  have hk0 : vs[0]? = some (.list ks) := rfl
  have hksv : (Val.list ks).wt < (Val.list vs).wt := cp_wt_get hk0
  have hcW : (Val.list (σ.cache.map ckEntV)).wt < (Val.list ks).wt :=
    cp_wt_get (vs := ks) (j := 4) rfl
  -- size facts
  set X := (D + 1) * (k + L.q + 1) ^ 6 with hX
  have hXB : 10 ^ 6 * X ≤ Bw := by
    have : 10 ^ 6 * (D + 1) * (k + L.q + 1) ^ 6 = 10 ^ 6 * X := by rw [hX]; ring
    omega
  have hP2 : 1 ≤ (k + L.q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hP26 : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hP6X : (k + L.q + 1) ^ 6 ≤ X := Nat.le_mul_of_pos_left _ (by omega)
  have hDX : D + 1 ≤ X := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
  have hk1 : (k + 1) ^ 2 ≤ (k + L.q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hkq2 : (k + L.q) ^ 2 ≤ (k + L.q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  refine CpFB.intro hat.reps ?_
  rw [hsv]
  unfold cpRepsF
  have dc := Det.arith (op := BinOp.lt) (Det.arg' (P := Pg) (vs := vs) (rest := []) (j := 2)
    (v := .nat i) rfl) (Det.length (cp_rdKV (P := Pg) (h0 []) hwW hk0 (j := 4) rfl (by omega)))
  have hcl : (σ.cache.map ckEntV).length = σ.cache.length := List.length_map _
  have hilen : i ≤ σ.cache.length := List.findIdx_le_length
  have hz : BinOp.lt.eval i (σ.cache.map ckEntV).length ≤ 1 := by
    simp only [BinOp.eval]; split_ifs <;> omega
  have hzw := wt_nat_le (BinOp.lt.eval i (σ.cache.map ckEntV).length)
  have hyl := length_lt_wt_list (σ.cache.map ckEntV)
  refine (CpEB.ite dc (Ct := 20 * (W + 20)) (Ce := 5 * cpG hst hpre hm W + 150 * (W + 20)) ?_ ?_).mono
    (by omega) fun _ h => h
  · -- a hit
    intro hx
    have hilt : i < σ.cache.length := by
      by_contra hc
      apply hx
      simp only [BinOp.eval, hcl]
      split_ifs <;> omega
    set ent := σ.cache[i] with hent
    have hentm : ent ∈ σ.cache := List.getElem_mem hilt
    have hgetc : (σ.cache.map ckEntV)[i]? = some (ckEntV ent) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hilt]; rfl
    have hentW : (ckEntV ent).wt < (Val.list (σ.cache.map ckEntV)).wt := cp_wt_get hgetc
    have d1 := Det.get' (cp_rdKV (P := Pg) (h0 []) hwW hk0 (j := 4) rfl (by omega))
      (Det.arg' (P := Pg) (vs := vs) (rest := []) (j := 2) (v := .nat i) rfl) hgetc
    have hrW : (Val.list (ent.2.2.map encPerm)).wt < (ckEntV ent).wt :=
      cp_wt_get (vs := [encGroup (ent.1.map encPair), encGroup (ent.2.1.map encPair),
        .list (ent.2.2.map encPerm)]) (j := 2) rfl
    have d2 := Det.get' d1 (Det.nat 2) (v := .list (ent.2.2.map encPerm)) rfl
    have d3 := Det.mk2 d2 (cp_rdKV (P := Pg) (h0 []) hwW hk0 (j := 4) rfl (by omega))
    have hoW := wt_list2_le (.list (ent.2.2.map encPerm)) (.list (σ.cache.map ckEntV))
    have hiW := wt_nat_le i
    have hiv : (Val.nat i).wt < (Val.list vs).wt := cp_wt_get (vs := vs) (j := 2) rfl
    have hmem := CacheOK.hit hR.cache.1 hA hN hps hns hentm (ckFind_hit hilt)
    refine CpEB.det d3 (by omega) (by omega) ⟨ent.2.2, σ.cache, rec, rfl, hR.cache,
      subset_rfl, by omega, hmem, fun a ha => hR.cache.2 ent hentm a ha,
      (hlen.2.2.2.2.2.2 ent hentm).2.2, hlen.2.2.2.2.2.2⟩
  · -- a miss
    intro hx
    have hnlt : ¬ i < σ.cache.length := by
      intro hc
      have : BinOp.lt.eval i (σ.cache.map ckEntV).length = 1 := by
        simp only [BinOp.eval, hcl]; split_ifs <;> omega
      omega
    have hno := ckFind_miss hnlt
    have hkqW : k + L.q + 1 ≤ W := by
      have : k + L.q + 1 ≤ (k + L.q + 1) ^ 12 := Nat.le_self_pow (by omega) _
      omega
    have hpsl : σ.ps.length ≤ (k + L.q) ^ 2 := hlen.2.2.2.2.1
    have hkqX : k + L.q + 1 ≤ X := (Nat.le_self_pow (n := 2) (by norm_num) (k + L.q + 1)).trans (hP26.trans hP6X)
    -- the orbit of the label tuple of `T`
    set x₀ := labPts k (tlist σ.T) with hx₀
    have hx0l : x₀.length ≤ L.q := by
      rw [hx₀, labPts, List.length_map, length_tlist]
      exact (Finset.card_le_univ _).trans (by simp)
    have hB : (actOrbit (fun g (xs : List (Fin (k + L.q))) => xs.map g) (σ.ps.map encPair)
        x₀).ncard ≤ D := by
      rw [ncard_tupOrbit πd ctx.hπ hAP hps]
      exact (Subgroup.card_le_card_group _).trans (ctx.hD σ.T hR.card).le
    set pl : List Val := [sv, .list [.nat k, .nat L.q], gpV gp, .nat (Fintype.card S.dom), .nat D,
      encPts osA, pSplitCtx k L.q, .nat (k + L.q)] with hpl
    have hp0 : ks[0]? = some (.list pl) := rfl
    have hplW : (Val.list pl).wt < (Val.list ks).wt := cp_wt_get hp0
    have hp1 : (Val.list [.nat k, .nat L.q]).wt < (Val.list pl).wt :=
      cp_wt_get (vs := pl) (j := 1) rfl
    have hp4 : (Val.nat D).wt < (Val.list pl).wt := cp_wt_get (vs := pl) (j := 4) rfl
    have hp6 : (pSplitCtx k L.q).wt < (Val.list pl).wt := cp_wt_get (vs := pl) (j := 6) rfl
    have hk8 : (gpV σ.ps).wt < (Val.list ks).wt := cp_wt_get (vs := ks) (j := 8) rfl
    set tl : List Val := [indT σ.T, natList (ptsKey x₀)] with htl
    have hk11 : (Val.list tl).wt < (Val.list ks).wt := cp_wt_get (vs := ks) (j := 11) rfl
    have ht1 : (natList (ptsKey x₀)).wt < (Val.list tl).wt := cp_wt_get (vs := tl) (j := 1) rfl
    have dT := Det.mk4 (cp_rdPV (P := Pg) (h0 []) hwW hk0 hp0 (j := 1) rfl (by omega))
      (cp_rdKV (P := Pg) (h0 []) hwW hk0 (j := 8) rfl (by omega))
      (Det.rd (a := 3) (cp_rdKV (P := Pg) (h0 []) hwW hk0 (j := 11) (v := .list tl) rfl
        (by omega)) le_rfl (show tl[1]? = some (natList (ptsKey x₀)) from rfl) (by omega)
        (by omega))
      (cp_rdPV (P := Pg) (h0 []) hwW hk0 hp0 (j := 4) rfl (by omega))
    have hTa := wt_list4_le (.list [.nat k, .nat L.q]) (gpV σ.ps) (natList (ptsKey x₀)) (.nat D)
    have hTup : CpFB Pg (cpTup b)
        (.list [.list [.nat k, .nat L.q], gpV σ.ps, natList (ptsKey x₀), .nat D]) W
        (cpG hst hpre hm W)
        (fun v => ∃ L' : List (List (Fin (k + L.q)) × Perm (Fin (k + L.q))),
          v = encPairs ptsKey L' ∧ (L'.map Prod.fst).Nodup ∧
          (∀ y, y ∈ L'.map Prod.fst ↔
            y ∈ actOrbit (fun g (xs : List (Fin (k + L.q))) => xs.map g) (σ.ps.map encPair) x₀) ∧
          (∀ p ∈ L', p.2 ∈ gens (σ.ps.map encPair) ∧ x₀.map p.2 = p.1) ∧ L'.length ≤ D ∧
          (encPairs ptsKey L').wt ≤ 201 * X + 4) := by
      refine FunAll.mono (graphTup_spec hat.tup σ.ps x₀ hB) ?_
      rintro w cst ⟨L', rfl, hnd, hmem, htr, hc⟩
      have hLl : L'.length ≤ D := by
        have := cp_length_eq_ncard hnd hmem
        rw [List.length_map] at this; omega
      have hwL : (encPairs ptsKey L').wt ≤ 201 * X + 4 := by
        have := cp_wt_listD (k := k) (q := L.q) (D := D)
          (vs := L'.map (GI.Lang.encPair ptsKey)) (by rw [List.length_map]; exact hLl) (by
            intro v hv
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
            have := cp_wt_tupElt p.1 (by rw [← (htr p hp).2, List.length_map]; exact hx0l) p.2
            simpa using this)
        exact this
      refine ⟨⟨L', rfl, hnd, hmem, htr, hLl, hwL⟩, by omega, ?_⟩
      have hM : tupM k L.q σ.ps D x₀.length ≤ W + 1 := by
        unfold tupM
        omega
      have h12 : graphTupK * tupM k L.q σ.ps D x₀.length ^ 12 ≤ graphTupK * (W + 1) ^ 12 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 12)
      have hp := cp_poly_le (W := W) (K := graphTupK) (d := 12) (by simp [graphTupK])
        (by norm_num) hW5
      have := cpG_poly hst hpre hm (W := W)
      omega
    refine (CpEB.letE (CpEB.call (CpEB.det dT le_rfl (by omega)
        (Q := fun v => v = .list [.list [.nat k, .nat L.q], gpV σ.ps, natList (ptsKey x₀), .nat D])
        rfl) fun v hv _ => hv ▸ hTup) (Cb := 4 * cpG hst hpre hm W + 110 * (W + 20))
      fun tv htv htW => ?_).mono (by omega) fun _ h => h
    obtain ⟨L', rfl, hnd, hmem, htr, hLl, hwL⟩ := htv
    -- the group elements, as pairs
    set tv := encPairs ptsKey L' with htv
    obtain ⟨qs, hqs'⟩ := cp_lift_list encPair (L'.map Prod.snd) (by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
      obtain ⟨p', -, he⟩ := mem_gens_encPair.1 (htr p hp).1
      exact ⟨p', he⟩)
    have hqs := hqs'.symm
    have hqsl : qs.length = L'.length := by
      have := congrArg List.length hqs; simp only [List.length_map] at this; omega
    have hsecE : L'.map (fun p => encPerm p.2) = qs.map (fun p => encPerm (encPair p)) := by
      have := congrArg (List.map encPerm) hqs
      simpa [List.map_map, Function.comp_def] using this
    have hS := mapList_spec hat.mapSec L' (GI.Lang.encPair ptsKey) (fun p => encPerm p.2)
      (c := .nat 0) (B := 500 * (k + L.q + 1) ^ 2)
      (fun a _ a' _ he => by
        simp only [GI.Lang.encPair, Val.list.injEq, List.cons.injEq] at he
        exact he.2.1)
      (fun p hp => cp_sec_step hat.sec p (by rw [← (htr p hp).2, List.length_map]; exact hx0l))
    rw [hsecE] at hS
    have hsW : (Val.list (qs.map fun p => encPerm (encPair p))).wt ≤ 201 * X + 4 :=
      cp_wt_listD (k := k) (q := L.q) (D := D) (by rw [List.length_map]; omega) (by
        intro v hv; obtain ⟨p, -, rfl⟩ := List.mem_map.1 hv
        have := wt_encPerm_le (encPair p); omega)
    have h1 : ∀ rest : List Val, (Val.list vs :: rest)[0]? = some (.list vs) := fun _ => rfl
    have dS := Det.mk2 (Det.nat (P := Pg) (env := [Val.list vs, tv]) 0)
      (Det.rv (P := Pg) (env := [Val.list vs, tv]) (i := 1) rfl htW)
    have hz0 := wt_nat_le 0
    have hSa := wt_list2_le (.nat 0) tv
    have hmk : mapK = 1000 := rfl
    have hbS : CpFB Pg (cpMapSec b) (.list [.nat 0, tv]) W (cpG hst hpre hm W)
        (fun v => v = .list (qs.map fun p => encPerm (encPair p))) := by
      have eTv : (Val.list [.nat 0, .list (L'.map (GI.Lang.encPair ptsKey))]).wt =
          (Val.list [.nat 0, tv]).wt := rfl
      refine CpFB.det hS ?_ (by omega) rfl
      have c1 : L'.length * (500 * (k + L.q + 1) ^ 2) ≤ (W + 1) * (500 * (W + 1)) :=
        Nat.mul_le_mul (by omega) (by omega)
      have c2 : mapK * (L'.length + 1) * ((Val.list [.nat 0, .list (L'.map
          (GI.Lang.encPair ptsKey))]).wt +
          (Val.list (qs.map fun p => encPerm (encPair p))).wt + 1) ≤ 1000 * (W + 1) * (W + 1) := by
        rw [hmk]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      have c3 : (W + 1) * (500 * (W + 1)) + 1000 * (W + 1) * (W + 1) = 1500 * (W + 1) ^ 2 := by
        ring
      have hp := cp_poly_le (W := W) (K := 1500) (d := 2) (by norm_num) (by norm_num) hW5
      have := cpG_poly hst hpre hm (W := W)
      omega
    refine (CpEB.letE (CpEB.call (CpEB.det dS le_rfl (by omega)
        (Q := fun v => v = .list [.nat 0, tv]) rfl) fun v hv _ => hv ▸ hbS)
      (Cb := 3 * cpG hst hpre hm W + 90 * (W + 20)) fun secv' hsecv hsW' => ?_).mono
      (by omega) fun _ h => h
    subst hsecv
    set secv := Val.list (qs.map fun p => encPerm (encPair p)) with hsecv
    -- the split into pairs
    have dP := Det.mk2 (cp_rdPV (P := Pg) (h1 [tv, secv]) hwW hk0 hp0 (j := 6) rfl (by omega))
      (Det.rv (P := Pg) (env := [Val.list vs, tv, secv]) (i := 2) rfl hsW')
    have hPa := wt_list2_le (pSplitCtx k L.q) secv
    have hpW : (Val.list (qs.map pairV)).wt ≤ 201 * X + 4 :=
      cp_wt_listD (k := k) (q := L.q) (D := D) (by rw [List.length_map]; omega) (by
        intro v hv; obtain ⟨p, -, rfl⟩ := List.mem_map.1 hv
        have := wt_pairV_le p; omega)
    have hbP : CpFB Pg (cpSplit b) (.list [pSplitCtx k L.q, secv]) W (cpG hst hpre hm W)
        (fun v => v = .list (qs.map pairV)) := by
      have eSv : (Val.list [pSplitCtx k L.q, .list (qs.map fun p => encPerm (encPair p))]).wt =
          (Val.list [pSplitCtx k L.q, secv]).wt := rfl
      refine CpFB.det (pSplitMap_spec hat.split qs) ?_ (by omega) rfl
      have hpc : pSplitCost k L.q ≤ 10 ^ 11 * (W + 1) ^ 6 := by
        unfold pSplitCost
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)
      have c1 : qs.length * pSplitCost k L.q ≤ (W + 1) * (10 ^ 11 * (W + 1) ^ 6) :=
        Nat.mul_le_mul (by omega) hpc
      have c2 : mapK * (qs.length + 1) * ((Val.list [pSplitCtx k L.q,
          .list (qs.map fun p => encPerm (encPair p))]).wt + (Val.list (qs.map pairV)).wt + 1) ≤
          1000 * (W + 1) * (W + 1) := by
        rw [hmk]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      have c3 : (W + 1) * (10 ^ 11 * (W + 1) ^ 6) = 10 ^ 11 * (W + 1) ^ 7 := by ring
      have c4 : 1000 * (W + 1) * (W + 1) = 1000 * (W + 1) ^ 2 := by ring
      have c5 : (W + 1) ^ 2 ≤ (W + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
      have hp := cp_poly_le (W := W) (K := 10 ^ 12) (d := 7) (by norm_num) (by norm_num) hW5
      have := cpG_poly hst hpre hm (W := W)
      omega
    refine (CpEB.letE (CpEB.call (CpEB.det dP le_rfl (by omega)
        (Q := fun v => v = .list [pSplitCtx k L.q, secv]) rfl) fun v hv _ => hv ▸ hbP)
      (Cb := 2 * cpG hst hpre hm W + 70 * (W + 20)) fun pv hpv hpW' => ?_).mono
      (by omega) fun _ h => h
    subst hpv
    -- the first parts
    set as := qs.map Prod.fst with has
    set splv := Val.list (qs.map pairV) with hsplv
    have hasl : as.length = qs.length := by rw [has, List.length_map]
    have dF := Det.mk2 (Det.nat (P := Pg) (env := [Val.list vs, tv, secv, splv]) 0)
      (Det.rv (P := Pg) (env := [Val.list vs, tv, secv, splv]) (i := 3) rfl hpW')
    have hFa := wt_list2_le (.nat 0) splv
    have hFo : (qs.map fun p => encPerm p.1) = as.map encPerm := by rw [has, List.map_map]; rfl
    have hfW : (Val.list (as.map encPerm)).wt ≤ 201 * X + 4 :=
      cp_wt_listD (k := k) (q := L.q) (D := D) (by rw [List.length_map]; omega) (by
        intro v hv; obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv
        have := wt_encPerm_le a; omega)
    have hF := mapList_spec hat.mapFst qs pairV (fun p => encPerm p.1) (c := .nat 0)
      (B := 300 * (k + L.q + 1) ^ 2) (fun a _ a' _ he => by rw [pairV_injective he])
      (fun p _ => krFst_step hat.fstF p)
    rw [hFo] at hF
    have hbF : CpFB Pg (cpMapFst b) (.list [.nat 0, splv]) W (cpG hst hpre hm W)
        (fun v => v = .list (as.map encPerm)) := by
      have ePv : (Val.list [.nat 0, .list (qs.map pairV)]).wt = (Val.list [.nat 0, splv]).wt :=
        rfl
      refine CpFB.det hF ?_ (by omega) rfl
      have c1 : qs.length * (300 * (k + L.q + 1) ^ 2) ≤ (W + 1) * (300 * (W + 1)) :=
        Nat.mul_le_mul (by omega) (by omega)
      have c2 : mapK * (qs.length + 1) * ((Val.list [.nat 0, .list (qs.map pairV)]).wt +
          (Val.list (as.map encPerm)).wt + 1) ≤ 1000 * (W + 1) * (W + 1) := by
        rw [hmk]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      have c3 : (W + 1) * (300 * (W + 1)) + 1000 * (W + 1) * (W + 1) = 1300 * (W + 1) ^ 2 := by
        ring
      have hp := cp_poly_le (W := W) (K := 1300) (d := 2) (by norm_num) (by norm_num) hW5
      have := cpG_poly hst hpre hm (W := W)
      omega
    refine (CpEB.letE (CpEB.call (CpEB.det dF le_rfl (by omega)
        (Q := fun v => v = .list [.nat 0, splv]) rfl) fun v hv _ => hv ▸ hbF)
      (Cb := cpG hst hpre hm W + 50 * (W + 20)) fun fv hfv hfW' => ?_).mono
      (by omega) fun _ h => h
    subst hfv
    -- the new cache entry, in front of the cache
    set fstv := Val.list (as.map encPerm) with hfstv
    have dK := Det.arg' (P := Pg) (vs := vs) (rest := [tv, secv, splv, fstv]) (j := 1)
      (v := .list [encGroup (σ.ps.map encPair), encGroup (ns.map encPair)]) rfl
    have dE := Det.mk1 (Det.snoc dK
      (Det.rv (P := Pg) (env := [Val.list vs, tv, secv, splv, fstv]) (i := 4) rfl hfW'))
    have eV : Val.list ([encGroup (σ.ps.map encPair), encGroup (ns.map encPair)] ++ [fstv]) =
        ckEntV (σ.ps, ns, as) := rfl
    rw [eV] at dE
    have dA := Det.mk2 dE (cp_rdKV (P := Pg) (h1 [tv, secv, splv, fstv]) hwW hk0 (j := 4) rfl
      (by omega))
    have hentB := cp_wt_ent (k := k) (q := L.q) (D := D) (ent := (σ.ps, ns, as)) hpsl hnsl
      (by show as.length ≤ D; omega)
    have hXe : 2000 * (D + 1) * (k + L.q + 1) ^ 6 = 2000 * X := by rw [hX]; ring
    have hE1 := cp_wt_list (vs := [ckEntV (σ.ps, ns, as)]) (n := 1)
      (c := (ckEntV (σ.ps, ns, as)).wt) (by simp) (by simp)
    have hE2 := wt_list2_le (.list [ckEntV (σ.ps, ns, as)]) (.list (σ.cache.map ckEntV))
    have hkeyW : (ckKeyV σ.ps ns).wt < (Val.list vs).wt := cp_wt_get (vs := vs) (j := 1) rfl
    have hbA := cp_bud_app hst hpre hm hat.app [ckEntV (σ.ps, ns, as)] (σ.cache.map ckEntV) hW5
      (by omega)
    refine (CpEB.letE (CpEB.call (CpEB.det dA le_rfl (by omega)
        (Q := fun v => v = .list [.list [ckEntV (σ.ps, ns, as)], .list (σ.cache.map ckEntV)])
        rfl) fun v hv _ => hv ▸ hbA) (Cb := 5 * (W + 20)) fun cv hcv hcW => ?_).mono
      (by omega) fun _ h => h
    subst hcv
    have dR := Det.mk2 (Det.rv (P := Pg) (env := [Val.list vs, tv, secv, splv, fstv,
        .list ([ckEntV (σ.ps, ns, as)] ++ σ.cache.map ckEntV)]) (i := 4) rfl hfW')
      (Det.rv (P := Pg) (env := [Val.list vs, tv, secv, splv, fstv,
        .list ([ckEntV (σ.ps, ns, as)] ++ σ.cache.map ckEntV)]) (i := 5) rfl hcW)
    have hRw := wt_list2_le fstv (.list ([ckEntV (σ.ps, ns, as)] ++ σ.cache.map ckEntV))
    have hcat := wt_list_append_le [ckEntV (σ.ps, ns, as)] (σ.cache.map ckEntV)
    -- what the new cache stands for
    have hq0 := orbit_pairs_lift hps (fun p hp => (htr p hp).1) hqs
    have hq : ∀ a ∈ as, (toFin e).symm a ∈ S.G := by
      intro a ha
      rw [has] at ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      exact hq0 p hp
    have hRe := repsOK_of_orbit πd ctx.hπ hAP hps hnd hmem htr hqs
    have e2 : as.map (domOfPos e S) = qs.map fun p => domOfPos e S p.1 := by
      rw [has, List.map_map]; rfl
    refine CpEB.det dR (by omega) (by omega) ⟨as, (σ.ps, ns, as) :: σ.cache,
      ((grp (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t,
        kernelIn (cpPhi S πd σ.T) (grp (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t)), as.map (domOfPos e S)) :: rec, rfl,
      CacheOK'.miss hR.cache hA hN hps hns hno as (by rw [e2]; exact hRe) hq, cands_cons _,
      by simp, List.mem_cons_self .., hq, by omega, ?_⟩
    intro ent hent
    rcases List.mem_cons.1 hent with h | hent'
    · rw [h]; exact ⟨hpsl, hnsl, by show as.length ≤ D; omega⟩
    · exact hlen.2.2.2.2.2.2 ent hent'

end Reps

end GI.Impl
