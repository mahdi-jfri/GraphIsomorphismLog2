import Workspace.Impl.AggCmpMvB

/-!
# The move program: the start of a pair, the end of the phase, and the dispatch

`cm_pair_spec`: from a program state at the start of a pair (`fl = 0`), the function `cmPairF`
returns the output `cmOutV` when all `N²` pairs are done (`cm_pair_nil_post`), and otherwise what
the function at `b + 5` returns.

`cm_mv_spec` is the move of the loop: from every program state that `CmRep` relates, the move
function `cmMvF` returns what a move must return (the hypothesis `hmv` of `cm_phase_spec`), at
cost at most `cmMvCost`. It takes as hypotheses the two moves that need new group computations:
the start of a pair (`CmStartOK`, at `b + 5`) and the call (`CmCallOK`, at `b + 4`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens Membership)
open scoped Pointwise

section Specs

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] (e : Ω ≃ Fin k) {S : State Ω C} [Fintype S.dom]
  {L : SuppliedLabels S} (Cs : Set (Aggregation P₀ S L.toGiantLabels))
  (Ag₀ : Aggregation P₀ S L.toGiantLabels) (O : TestTupleOrder L.q P₀.κ)
  (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- **What the start of a pair must do** (the function at `b + 5`): from a program state at the
start of a pair with index below `N²`, return what a move must return. -/
def CmStartOK (Pg : Program) (b W Cst : ℕ) (par : Val) (Out : List Bool → Val → Prop)
    (Bw M₀ : ℕ) : Prop :=
  ∀ {m f : ℕ} {acc : List Bool} {ps' : List (CmPair L.q P₀.κ)} {σ : CmSt k}
    {ents : List (CmEnt S.dom)} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))} {u : Val},
    m = cmMs (Fintype.card S.dom) (.pos (.pair acc ps') : CmPt S L.q P₀.κ) →
    cmMc (Fintype.card S.dom) (.pos (.pair acc ps') : CmPt S L.q P₀.κ) ≤ f →
    σ.cache.length + m ≤ M₀ → CmCacheOK ents rec → List.Forall₂ (CmEntOK e S) σ.cache ents →
    (∀ p ∈ σ.cache, p.1.length ≤ (k + L.q) ^ 2) → σ.fl = 0 → σ.acc = acc →
    ps' = (cmPairs O).drop acc.length → acc.length < O.tuples.length * O.tuples.length →
    (Val.list [σ.val par, u]).wt ≤ Bw →
    CpFB Pg (b + 5) (.list [σ.val par, u]) W Cst
      (CmMvPost e Cs Ag₀ O πd par Out Bw M₀ m
        ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick (.pos (.pair acc ps')))
          '' CmCands Cs Ag₀ O rec) f)

/-- **What the call must do** (the function at `b + 4`): from a program state at stage
`j < n` with a representative, return what a move must return. -/
def CmCallOK (Pg : Program) (b W Ccall : ℕ) (par : Val) (Out : List Bool → Val → Prop)
    (Bw M₀ : ℕ) : Prop :=
  ∀ {m f : ℕ} {acc : List Bool} {ab : CmPair L.q P₀.κ} {ps' : List (CmPair L.q P₀.κ)} {j : ℕ}
    {o : Option (Perm S.dom)} {σ : CmSt k} {ents : List (CmEnt S.dom)}
    {rec : List (Set (Perm S.dom) × Option (Perm S.dom))} {u : Val},
    m = cmMs (Fintype.card S.dom) (.pos (.stage acc ab ps' j o) : CmPt S L.q P₀.κ) →
    cmMc (Fintype.card S.dom) (.pos (.stage acc ab ps' j o) : CmPt S L.q P₀.κ) ≤ f →
    σ.cache.length + m ≤ M₀ → CmCacheOK ents rec → List.Forall₂ (CmEntOK e S) σ.cache ents →
    (∀ p ∈ σ.cache, p.1.length ≤ (k + L.q) ^ 2) → σ.fl = 1 → σ.acc = acc →
    (cmPairs O).drop acc.length = ab :: ps' → σ.j = j → j < Fintype.card S.dom →
    CmOK e σ.o o → σ.o ≠ none → (Val.list [σ.val par, u]).wt ≤ Bw →
    CpFB Pg (b + 4) (.list [σ.val par, u]) W Ccall
      (CmMvPost e Cs Ag₀ O πd par Out Bw M₀ m
        ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick (.pos (.stage acc ab ps' j o)))
          '' CmCands Cs Ag₀ O rec) f)

end Specs

/-- The cost of a move. -/
noncomputable def cmMvCost (hm : Membership) (W Cst Ccall : ℕ) : ℕ :=
  Cst + Ccall + cmAnsCost hm W + 1000 * (W + 20)

section Mv

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : SuppliedLabels S} {Cs : Set (Aggregation P₀ S L.toGiantLabels)}
  {Ag₀ : Aggregation P₀ S L.toGiantLabels} {O : TestTupleOrder L.q P₀.κ}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}

set_option maxHeartbeats 4000000 in
/-- **The start of a pair, or the end of the phase.** -/
theorem cm_pair_spec (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs)
    {Pg : Program} {b jm : ℕ} (hat : CmMvAt0 Pg b jm)
    {sv : Val} {ps fx fy : GPairs k L.q} {logs : List (CmLog k L.q)} {M₀ Bw W Cst : ℕ}
    (hW : 100 * Bw + 1000 ≤ W)
    (hst : CmStartOK e Cs Ag₀ O πd Pg b W Cst (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom))
      (fun a out => out = cmOutV sv k ps fx fy O.tuples a) Bw M₀)
    {m f : ℕ} {acc : List Bool} {ps' : List (CmPair L.q P₀.κ)} {σ : CmSt k}
    {ents : List (CmEnt S.dom)} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (hm : m = cmMs (Fintype.card S.dom) (.pos (.pair acc ps') : CmPt S L.q P₀.κ))
    (hmf : cmMc (Fintype.card S.dom) (.pos (.pair acc ps') : CmPt S L.q P₀.κ) ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hc : CmCacheOK ents rec)
    (hF : List.Forall₂ (CmEntOK e S) σ.cache ents)
    (hlen : ∀ p ∈ σ.cache, p.1.length ≤ (k + L.q) ^ 2) (hfl : σ.fl = 0) (hacc : σ.acc = acc)
    (hps : ps' = (cmPairs O).drop acc.length) {u : Val}
    (hwt : (Val.list [σ.val (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)), u]).wt ≤ Bw) :
    CpFB Pg (b + 1) (.list [σ.val (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)), u])
      W (Cst + 200 * (W + 20))
      (CmMvPost e Cs Ag₀ O πd (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom))
        (fun a out => out = cmOutV sv k ps fx fy O.tuples a) Bw M₀ m
        ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick (.pos (.pair acc ps')))
          '' CmCands Cs Ag₀ O rec) f) := by
  set par := cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom) with hpar
  set ks := σ.vals par with hks
  have hsv : σ.val par = .list ks := rfl
  have hwW : (Val.list [.list ks, u]).wt ≤ W := by rw [← hsv]; omega
  have h0 : (Val.list [.list ks, u] :: [])[0]? = some (.list [.list ks, u]) := rfl
  set pv : List Val := [sv, .list [.nat k, .nat L.q], .list (ps.map pairV),
    .list (fx.map pairV), .list (fy.map pairV), .list (logs.map cmLogV), .list (O.tuples.map stTT),
    .nat (Fintype.card S.dom), .nat O.tuples.length] with hpv
  have hp0 : ks[0]? = some (.list pv) := rfl
  have hparB : par.wt < Bw := by
    have h1 := cm_wt_lt_of_mem (vs := ks) (v := par) (by simp [hks, CmSt.vals])
    have h2 := cm_wt_lt_of_mem (vs := [.list ks, u]) (v := .list ks) (by simp)
    rw [← hsv] at h1 h2
    omega
  have hpvW : ∀ v ∈ pv, v.wt < Bw := fun v hv =>
    lt_trans (cm_wt_lt_of_mem hv) hparB
  have dN := cp_rdP (P := Pg) h0 hwW hp0 (j := 8) (v := .nat O.tuples.length) rfl (by omega)
  have dA := cp_rdK (P := Pg) h0 hwW (j := 4) (v := .list (σ.acc.map boolVal)) rfl (by omega)
  have dL := Det.length dA
  have dNN := Det.arith (op := .mul) dN dN
  have hlenNN : (Val.nat (O.tuples.length * O.tuples.length)).wt ≤ 2 * Bw := by
    have h1 : (Val.nat O.tuples.length).wt < Bw := hpvW _ (by simp [hpv])
    have h2 := wt_nat O.tuples.length
    have h3 := wt_nat (O.tuples.length * O.tuples.length)
    have h4 := GI.Machine.len_mul_le O.tuples.length O.tuples.length
    omega
  have hAl : σ.acc.length < W := by
    have h1 := length_lt_wt_list (σ.acc.map boolVal)
    have h2 := cm_wt_lt_of_mem (vs := ks) (v := .list (σ.acc.map boolVal)) (by simp [hks, CmSt.vals])
    have h3 := cm_wt_lt_of_mem (vs := [.list ks, u]) (v := .list ks) (by simp)
    simp only [List.length_map] at h1
    omega
  have dLt := Det.arith (op := .lt) dL dNN
  simp only [GI.Machine.BinOp.eval_mul, GI.Machine.BinOp.eval_lt, List.length_map] at dLt
  have hlt01 := wt_nat_le (if σ.acc.length < O.tuples.length * O.tuples.length then 1 else 0)
  refine CpFB.intro hat.pair ?_
  unfold cmPairF
  rw [hsv]
  by_cases hlt : σ.acc.length < O.tuples.length * O.tuples.length
  · -- the start of a pair
    rw [if_pos hlt] at dLt hlt01
    refine (CpEB.ite dLt (Ct := Cst + 2 * (W + 20)) (Ce := 0) (fun _ => ?_)
      fun h => absurd h one_ne_zero).mono (by omega) fun _ h => h
    refine (CpEB.call (Cb := Cst) (CpEB.det (Det.rv (P := Pg)
      (env := [.list [.list ks, u]]) (i := 0) rfl hwW) le_rfl hwW
      (Q := fun v => v = .list [.list ks, u]) rfl) fun v hv _ => ?_).mono (by omega)
      fun _ h => h
    subst hv
    rw [← hsv]
    exact hst hm hmf hM hc hF hlen hfl hacc hps (by rw [← hacc]; exact hlt) hwt
  · -- the end of the phase
    rw [if_neg hlt] at dLt hlt01
    have hnil : ps' = [] := by
      rw [hps]; exact cm_pairs_drop_end O (by rw [← hacc]; omega)
    subst hnil
    set out := cmOutV sv k ps fx fy O.tuples σ.acc with hout
    have hTA : (Val.list [.list (O.tuples.map stTT), .list (σ.acc.map boolVal)]).wt ≤ 8 * Bw := by
      have h1 := wt_list2_le (.list (O.tuples.map stTT)) (.list (σ.acc.map boolVal))
      have h2 : (Val.list (O.tuples.map stTT)).wt < Bw := hpvW _ (by simp [hpv])
      have h3 := cm_wt_lt_of_mem (vs := ks) (v := .list (σ.acc.map boolVal)) (by simp [hks, CmSt.vals])
      have h4 : (Val.list ks).wt < Bw := by
        rw [← hsv]
        exact lt_of_lt_of_le (cm_wt_lt_of_mem (vs := [σ.val par, u]) (by simp)) hwt
      omega
    have houtW : out.wt ≤ 40 * Bw := by
      have h := wt_list_le [sv, .list [.nat k, .nat L.q], .list (ps.map pairV),
        .list (fx.map pairV), .list (fy.map pairV),
        .list [.list (O.tuples.map stTT), .list (σ.acc.map boolVal)]]
      have hsum := sum_wt_lt_wt_list pv
      simp only [hpv, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at h hsum
      have : (Val.list pv).wt < Bw := hparB
      rw [hpv] at this
      have e : out.wt = (Val.list [sv, .list [.nat k, .nat L.q], .list (ps.map pairV),
        .list (fx.map pairV), .list (fy.map pairV),
        .list [.list (O.tuples.map stTT), .list (σ.acc.map boolVal)]]).wt := rfl
      omega
    have dl := cp_mkList' (P := Pg) (env := [.list [.list ks, u]]) (W := W) (c := 20 * (W + 20))
      [(cpPf 0, sv), (cpPf 1, .list [.nat k, .nat L.q]), (cpPf 2, .list (ps.map pairV)),
        (cpPf 3, .list (fx.map pairV)), (cpPf 4, .list (fy.map pairV)),
        (mk2 (cpPf 6) (cpKf 4), .list [.list (O.tuples.map stTT), .list (σ.acc.map boolVal)])]
      (v := out) rfl (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
        · exact (cp_rdP (P := Pg) h0 hwW hp0 (j := 0) rfl (by omega)).mono (by omega)
        · exact (cp_rdP (P := Pg) h0 hwW hp0 (j := 1) rfl (by omega)).mono (by omega)
        · exact (cp_rdP (P := Pg) h0 hwW hp0 (j := 2) rfl (by omega)).mono (by omega)
        · exact (cp_rdP (P := Pg) h0 hwW hp0 (j := 3) rfl (by omega)).mono (by omega)
        · exact (cp_rdP (P := Pg) h0 hwW hp0 (j := 4) rfl (by omega)).mono (by omega)
        · exact (Det.mk2 (cp_rdP (P := Pg) h0 hwW hp0 (j := 6) rfl (by omega)) dA).mono
            (by omega)) (by omega)
    have dr := Det.mk2 (Det.nat (P := Pg) (env := [.list [.list ks, u]]) 0) dl
    have hrw : (Val.list [.nat 0, out]).wt ≤ W := by
      have := wt_list2_le (.nat 0) out
      have := wt_nat_le 0
      omega
    refine (CpEB.ite dLt (Ct := 0) (Ce := 6 * (20 * (W + 20) + W + 1) + 5 + 2 * W + 100)
      (fun h => absurd rfl h) fun _ => ?_).mono (by omega) fun _ h => h
    refine CpEB.det dr (by simp only [List.length_cons, List.length_nil]; have := wt_nat_le 0; omega)
      hrw ?_
    refine Or.inl ?_
    rw [← hacc]
    exact cm_pair_nil_post hAg₀ hsub hcl hc σ.acc rfl

/-- **The dispatch on `fl`.** -/
theorem cm_dispatch {Pg : Program} {b jm : ℕ} (hat : CmMvAt0 Pg b jm) {par u : Val}
    {σ : CmSt k} {Bw W C : ℕ} {Q : Val → Prop} (hW : 100 * Bw + 1000 ≤ W)
    (hwt : (Val.list [σ.val par, u]).wt ≤ Bw) (hfl : σ.fl ≤ 2)
    (h0 : σ.fl = 0 → CpFB Pg (b + 1) (.list [σ.val par, u]) W C Q)
    (h1 : σ.fl = 1 → CpFB Pg (b + 2) (.list [σ.val par, u]) W C Q)
    (h2 : σ.fl = 2 → CpFB Pg (b + 3) (.list [σ.val par, u]) W C Q) :
    CpFB Pg b (.list [σ.val par, u]) W (C + 30 * (W + 20)) Q := by
  set ks := σ.vals par with hks
  have hsv : σ.val par = .list ks := rfl
  have hwW : (Val.list [.list ks, u]).wt ≤ W := by rw [← hsv]; omega
  have h00 : ([.list [.list ks, u]] : List Val)[0]? = some (.list [.list ks, u]) := rfl
  have dF := cp_rdK (P := Pg) h00 hwW (j := 5) (v := .nat σ.fl) rfl (by omega)
  have dV : CpEB Pg [.list [.list ks, u]] (.var 0) W (1 * (W + 20))
      (fun v => v = .list [.list ks, u]) :=
    CpEB.det (Det.rv (i := 0) rfl hwW) le_rfl hwW rfl
  refine CpFB.intro hat.mv ?_
  unfold cmMvF
  rw [hsv] at h0 h1 h2 ⊢
  have dE0 := Det.arith (op := .eq) dF (Det.nat 0)
  have dE1 := Det.arith (op := .eq) dF (Det.nat 1)
  simp only [GI.Machine.BinOp.eval_eq] at dE0 dE1
  have w0 := wt_nat_le (if σ.fl = 0 then 1 else 0)
  have w1 := wt_nat_le (if σ.fl = 1 then 1 else 0)
  have hcall : ∀ i, (σ.fl = i → CpFB Pg (b + (i + 1)) (.list [.list ks, u]) W C Q) → σ.fl = i →
      CpEB Pg [.list [.list ks, u]] (.call (b + (i + 1)) (.var 0)) W (C + 2 * (W + 20)) Q :=
    fun i hi hfi => (CpEB.call dV fun v hv _ => hv ▸ hi hfi).mono (by omega) fun _ h => h
  by_cases e0 : σ.fl = 0
  · rw [if_pos e0] at dE0 w0
    exact (CpEB.ite dE0 (Ct := C + 2 * (W + 20)) (Ce := 0) (fun _ => hcall 0 h0 e0)
      fun h => absurd h one_ne_zero).mono (by omega) fun _ h => h
  · rw [if_neg e0] at dE0 w0
    refine (CpEB.ite dE0 (Ct := 0) (Ce := C + 10 * (W + 20)) (fun h => absurd rfl h)
      fun _ => ?_).mono (by omega) fun _ h => h
    by_cases e1 : σ.fl = 1
    · rw [if_pos e1] at dE1 w1
      exact (CpEB.ite dE1 (Ct := C + 2 * (W + 20)) (Ce := 0) (fun _ => hcall 1 h1 e1)
        fun h => absurd h one_ne_zero).mono (by omega) fun _ h => h
    · rw [if_neg e1] at dE1 w1
      exact (CpEB.ite dE1 (Ct := 0) (Ce := C + 2 * (W + 20)) (fun h => absurd rfl h)
        fun _ => hcall 2 h2 (by omega)).mono (by omega) fun _ h => h

theorem cm_mvCost_facts (hm : Membership) (W Cst Ccall : ℕ) :
    Cst + 200 * (W + 20) ≤ Cst + Ccall + cmAnsCost hm W + 200 * (W + 20) ∧
    Ccall + 200 * (W + 20) ≤ Cst + Ccall + cmAnsCost hm W + 200 * (W + 20) ∧
    cmAnsCost hm W ≤ Cst + Ccall + cmAnsCost hm W + 200 * (W + 20) ∧
    Cst + Ccall + cmAnsCost hm W + 200 * (W + 20) + 30 * (W + 20) ≤ cmMvCost hm W Cst Ccall := by
  unfold cmMvCost
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **The move**: the hypothesis `hmv` of `cm_phase_spec`, given the start of a pair and the
call. -/
theorem cm_mv_spec (hm : Membership) (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs)
    {Pg : Program} {b jm : ℕ} (hat : CmMvAt0 Pg b jm)
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {sv : Val} {ps fx fy : GPairs k L.q} {logs : List (CmLog k L.q)} {M₀ Bw W Cst Ccall : ℕ}
    (hBw : cmBw (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)).wt k L.q M₀
      (O.tuples.length * O.tuples.length) ≤ Bw) (hW : 100 * Bw + 1000 ≤ W)
    (hst : CmStartOK e Cs Ag₀ O πd Pg b W Cst (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom))
      (fun a out => out = cmOutV sv k ps fx fy O.tuples a) Bw M₀)
    (hca : CmCallOK e Cs Ag₀ O πd Pg b W Ccall
      (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom))
      (fun a out => out = cmOutV sv k ps fx fy O.tuples a) Bw M₀) :
    ∀ m st Ss f, CmRep e (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)) Cs Ag₀ O πd Bw M₀
      m st Ss f → FunAll Pg b st (fun w c => c ≤ cmMvCost hm W Cst Ccall ∧
      (Iface.StepPostC (measure P₀ .giant S) (fun a out => out = cmOutV sv k ps fx fy O.tuples a)
          (fun st Ss f => ∃ m, CmRep e (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)) Cs
            Ag₀ O πd Bw M₀ m st Ss f) Ss f w ∨
        ∃ m' st' Ss', m' < m ∧ Ss' ⊆ Ss ∧
          CmRep e (cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom)) Cs Ag₀ O πd Bw M₀
            m' st' Ss' f ∧ w = .list [.nat 2, st'])) := by
  intro m st Ss f h
  obtain ⟨pt, σ, ents, rec, hmeq, hmf, hwt, hM, hc, hF, hlen, rfl, hok⟩ := h
  set par := cmParV sv ps fx fy logs O.tuples (Fintype.card S.dom) with hpar
  obtain ⟨f1, f2, f3, f4⟩ := cm_mvCost_facts hm W Cst Ccall
  suffices hb : CpFB Pg b st W (Cst + Ccall + cmAnsCost hm W + 200 * (W + 20) + 30 * (W + 20))
      (CmMvPost e Cs Ag₀ O πd par (fun a out => out = cmOutV sv k ps fx fy O.tuples a) Bw M₀ m
        ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick pt) '' CmCands Cs Ag₀ O rec) f) by
    refine FunAll.mono hb fun w c hw => ⟨hw.2.2.trans f4, ?_⟩
    rcases hw.1 with h | ⟨st', ⟨m', Ss', hlt, hss, hrep⟩, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨m', st', Ss', hlt, hss, hrep, rfl⟩
  rcases pt with (_ | ⟨acc, ps'⟩ | ⟨acc, ab, ps', j, o⟩) | ⟨acc, ab, ps', j, A⟩
  · exact hok.elim
  · obtain ⟨hfl, hacc, hps, u, rfl⟩ := hok
    refine cm_dispatch hat hW hwt (by omega) (fun h0 => ?_) (fun h => by omega) (fun h => by omega)
    exact (cm_pair_spec hAg₀ hsub hcl hat hW hst hmeq hmf hM hc hF hlen hfl hacc hps hwt).mono
      f1 fun _ h => h
  · obtain ⟨hfl, hacc, hdrop, hj, hjn, ho, u, rfl⟩ := hok
    refine cm_dispatch hat hW hwt (by omega) (fun h => by omega) (fun _ => ?_) (fun h => by omega)
    exact (cm_stage_spec hat hBw hW hmeq hmf hM hc hF hlen hfl hacc hdrop hj hjn ho hwt
      (fun hjl hne => hca hmeq hmf hM hc hF hlen hfl hacc hdrop hj hjl ho hne hwt)).mono
      f2 fun _ h => h
  · obtain ⟨hfl, hacc, hdrop, hj, hjn, a₀, u, ho, ha₀, hA, hu, rfl⟩ := hok
    refine cm_dispatch hat hW hwt (by omega) (fun h => by omega) (fun h => by omega) (fun _ => ?_)
    exact (cm_ans_spec hm hat hjm hBw hW hmeq hmf hM hc hF hlen hacc hdrop hj hjn ho ha₀ hA hu
      hwt).mono f3 fun _ h => h

end Mv

end GI.Impl
