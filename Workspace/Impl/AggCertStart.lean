module

public import Workspace.Impl.AggCertTrans

@[expose] public section

/-!
# The start of a round with a nonempty increment, on program data

At the start of a round whose increment is nonempty, the program looks up the coset
representatives `a :: as` of `(A_t, ker)` in its cache (or computes and records them), and asks
the window call of the first one. `cp_round_start` says that this step meets `StepPostC` for the
relation `CpRep`, when the program has computed

* a new cache `c'` for a record `rec'` whose candidates are among those of `rec` and which holds
  the representatives `a :: as` of the round (a cache hit: `c' = c`; a miss: one new entry,
  `CacheOK.miss`), all of them position permutations of elements of `G`;
* the group value `gv = encGroup hs` of the lifted kernel (`kr_spec`, `groupValC_of_kr`);
* the window indicator `dv` and the list `incl` of the increment (`inc_spec`);
* the codes of the window colors of `a` (`wp_spec`).

The new program state is inside the round, after the call of `a` (`CpWinInv` with no earlier
representatives).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)
open scoped Pointwise

section Start

variable {k : ℕ} {Ω C : Type} [Finite Ω] [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ}
  {S : State Ω C} [Fintype S.dom] {L : GiantLabels S}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}

/-- Changing only the cache keeps the data of a round, for a good cache. -/
theorem CpRoundInv.with_cache {σ : CpSt k L.q} {acc : List (StagePair S)}
    {T : Finset (Fin L.q)}
    {rec rec' : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) {c' : List (CacheEntry k L.q)} (hc' : CacheOK' e c' rec') :
    CpRoundInv e πd { σ with cache := c' } acc T rec' :=
  { h with
    cache := hc'
    loglen := ⟨h.loglen.1, h.loglen.2, h.loglen.3, h.loglen.4⟩
    resLog := h.resLog }

/-- The parameter facts of a test set of size `κ`. -/
theorem cp_card_facts {T : Finset (Fin L.q)} (hT : T.card = P₀.κ) :
    5 ≤ T.card ∧ P₀.κ = T.card ∧ 1 ≤ P₀.θ * T.card := by
  refine ⟨hT ▸ P₀_terminating.κ_five, hT.symm, ?_⟩
  rw [hT]
  norm_num [P₀]

/-- The remaining script inside a round, in the form of `AggCertPos.lean`. -/
theorem cpAt_win_eq (R : CosetRepFn S.dom) (acc : List (StagePair S)) (T : Finset (Fin L.q))
    (Ts : List (Finset (Fin L.q))) (s : Bool) (t : ℕ) (τs : List (Perm S.dom))
    (acc' : List (Set (Perm S.dom))) :
    cpAt S πd (dstr S S.x) (dstr S S.y) R (.win acc T Ts s t τs acc') =
      cpWin S (phiT S.domGroup πd T) (dstr S (cpZ S s)) (Fintype.card S.dom)
        (cpK S πd (dstr S S.x) (dstr S S.y) acc T Ts s) R t τs acc' := by
  simp only [cpAt]
  rw [cpStr_dstr]

/-- **The start of a round with a nonempty increment**: the first window call. -/
theorem cp_round_start (hc : Function.Injective c) {sv : Val} (hS : Canon e c sv S) {hv : Val}
    (hh : HierValC e hv S.hier) (hgood : Good P₀ .giant S) (htr : S.Transitive)
    {par : Val} {D Bw M₀ NT : ℕ} {σ : CpSt k L.q} {acc : List (StagePair S)}
    {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) (ht : σ.t < Fintype.card S.dom)
    (hne : inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t ≠ ∅)
    {m f : ℕ} (hm : m = cpMeas (Fintype.card S.dom) D (.round acc T σ.Ts σ.s σ.t))
    (hmf : m ≤ f) (hM : σ.cache.length + m ≤ M₀) (hNT : σ.res.length + σ.Ts.length + 1 ≤ NT)
    {c' : List (CacheEntry k L.q)}
    {rec' : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (hc' : CacheOK' e c' rec') (hsub : Cands rec' ⊆ Cands rec)
    (hlen : c'.length ≤ σ.cache.length + 1) {a : Perm (Fin k)} {as : List (Perm (Fin k))}
    (hl : ((grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t,
      kernelIn (cpPhi S πd T) (grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t)),
      (a :: as).map (domOfPos e S)) ∈ rec')
    (hG : ∀ b ∈ a :: as, (toFin e).symm b ∈ S.G) (hD : as.length ≤ D)
    {hs : List (Perm (Fin k))}
    (hgv : GroupValC k (encGroup hs) (groupFin e (S.liftGroup (kernelIn (cpPhi S πd T)
      (grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t)))))
    {dv : Val}
    (hdv : DomVal e dv (Subtype.val '' (inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t : Set S.dom)))
    {incl : List S.dom} (hnd : incl.Nodup)
    (hinc : ∀ v, v ∈ incl ↔ v ∈ inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t)
    (hT : T = σ.T) (hlen : CpLen D { σ with cache := c' })
    (hin : CpInLen k L.q D (cpInnerV as [] hs dv (incl.map (domPos e L.q)) a))
    (hwt : ∀ u, AnsC e u (cpCall πd T σ.s σ.t (domOfPos e S a)).answer →
      (Val.list [CpSt.val par { σ with cache := c' }
        (cpInnerV as [] hs dv (incl.map (domPos e L.q)) a), u]).wt ≤ Bw) :
    Iface.StepPostC (measure P₀ .giant S) (CpOut e S L πd)
      (fun st Ss f => ∃ m, CpRep e πd par D Bw M₀ NT m st Ss f)
      ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R (.round acc T σ.Ts σ.s σ.t)) '' Cands rec) f
      (.list [.nat 1, .nat (modeCode .cont), winVal' k (encGroup hs) dv
        (natList (winCodesX e c S (cpZ S σ.s) a)) (natList (winCodesY e c S (cpZ S σ.s) a)) hv S.N,
        CpSt.val par { σ with cache := c' } (cpInnerV as [] hs dv (incl.map (domPos e L.q)) a)]) := by
  -- narrow to the candidates of `rec'`
  refine stepPostC_mono_set (cpAt_narrow S πd _ _ hsub acc T σ.Ts σ.s ht
    (by rw [cpStr_dstr]; exact hne) (by rw [cpStr_dstr]; exact hl)) ?_
  obtain ⟨hk5, hκ, hθ⟩ := cp_card_facts h.card
  obtain ⟨g, rfl⟩ : ∃ g, toFin e g = a :=
    ⟨(toFin e).symm a, (toFin e).apply_symm_apply a⟩
  have hg : g ∈ S.G := by
    have := hG _ (List.mem_cons_self ..)
    rwa [(toFin e).symm_apply_apply] at this
  have hτ : S.domHom ⟨g, hg⟩ = domOfPos e S (toFin e g) := (domOfPos_toFin e S hg).symm
  have hset : ∀ (τs : List (Perm S.dom)) (acc' : List (Set (Perm S.dom))),
      (fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R (.win acc T σ.Ts σ.s σ.t τs acc')) =
      fun R => cpWin S (phiT S.domGroup πd T) (dstr S (cpZ S σ.s)) (Fintype.card S.dom)
        (cpK S πd (dstr S S.x) (dstr S S.y) acc T σ.Ts σ.s) R σ.t τs acc' := fun τs acc' =>
    funext fun R => cpAt_win_eq R acc T σ.Ts σ.s σ.t τs acc'
  have hm0 : 0 < m := by rw [hm]; simp only [cpMeas]; positivity
  have hlist : (toFin e g :: as).map (domOfPos e S) = S.domHom ⟨g, hg⟩ :: as.map (domOfPos e S) := by
    rw [List.map_cons, hτ]
  rw [hset, hlist]
  refine cp_window_step hc hS hh hgood htr πd T hk5 hκ hθ (cpZ S σ.s) (Fintype.card S.dom)
    (cpK S πd (dstr S S.x) (dstr S S.y) acc T σ.Ts σ.s) (hc'.1.cands_nonempty
      (CosetRepFn.default S.dom)) σ.t hg (as.map (domOfPos e S)) [] hgv hdv (f := f) (by omega)
    fun u hu => ?_
  rw [← hset]
  have hu' : AnsC e u (cpCall πd T σ.s σ.t (domOfPos e S (toFin e g))).answer := by
    rw [← hτ]; exact hu
  set pos : CpPos S L.q := .win acc T σ.Ts σ.s σ.t (as.map (domOfPos e S))
    ([] ++ [winVal S (S.domHom ⟨g, hg⟩) (windowCall S (kernelIn (phiT S.domGroup πd T)
      (grp (phiT S.domGroup πd T) (dstr S (cpZ S σ.s)) σ.t)) (inc (phiT S.domGroup πd T)
      (dstr S (cpZ S σ.s)) σ.t) (cpInv S (phiT S.domGroup πd T) (dstr S (cpZ S σ.s)) σ.t)
      (dstr S (cpZ S σ.s)) (S.domHom ⟨g, hg⟩)).answer]) with hpos
  have hlt : cpMeas (Fintype.card S.dom) D pos < m := by
    rw [hm, hpos]
    exact cpMeas_win_lt (by rw [List.length_map]; exact hD)
  refine ⟨cpMeas (Fintype.card S.dom) D pos, pos, { σ with cache := c' }, rec', rfl, by omega,
    hwt u hu', by simp only; omega, hNT, hlen, rfl, hT, rfl, rfl, rfl, _, u, rfl,
    ⟨h.with_cache hc', ht, hne, [], toFin e g, as, hs, dv, incl, rfl, by simpa using hl,
    by simpa using hG, rfl, by simp, ?_, hu', hgv, hdv, hnd, hinc⟩, hin⟩
  simp only [List.nil_append, List.map_nil, List.map_cons, cpAcc, hτ]

/-- **A cache miss keeps a good cache**: the new entry's representatives are the first parts of
pairs of the graph of `G`. -/
theorem CacheOK'.miss {c : List (CacheEntry k L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (hc : CacheOK' e c rec) {A N : Subgroup (Perm S.dom)} (hA : A ≤ S.domGroup)
    (hN : N ≤ S.domGroup) {ps ns : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L (S.liftGroup A) ps) (hns : PairGens e L (S.liftGroup N) ns)
    (hno : ∀ ent ∈ c, ¬ KeyMatch ent ps ns) (as : List (Perm (Fin k)))
    (hR : RepsOK (A, N) (as.map (domOfPos e S))) (hq : ∀ a ∈ as, (toFin e).symm a ∈ S.G) :
    CacheOK' e ((ps, ns, as) :: c) (((A, N), as.map (domOfPos e S)) :: rec) := by
  refine ⟨hc.1.miss hA hN hps hns hno as hR, fun ent hent => ?_⟩
  rcases List.mem_cons.1 hent with rfl | h
  · exact hq
  · exact hc.2 ent h

/-- **The pairs of the transversal lie in the graph of `G`**: their first parts are position
permutations of elements of `G`. -/
theorem orbit_pairs_lift {A : Subgroup (Perm S.dom)} {ps : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L (S.liftGroup A) ps)
    {L' : List (List (Fin (k + L.q)) × Perm (Fin (k + L.q)))}
    (htr : ∀ p ∈ L', p.2 ∈ gens (ps.map encPair))
    {qs : List (Perm (Fin k) × Perm (Fin L.q))} (hqs : L'.map Prod.snd = qs.map encPair) :
    ∀ p ∈ qs, (toFin e).symm p.1 ∈ S.G := by
  intro p hp
  have hp' : encPair p ∈ L'.map Prod.snd := by rw [hqs]; exact List.mem_map_of_mem hp
  obtain ⟨⟨y, t⟩, hyt, ht⟩ := List.mem_map.1 hp'
  have hg := htr _ hyt
  simp only at ht hg
  subst ht
  obtain ⟨p', hp'', he⟩ := mem_gens_encPair.1 hg
  have := encPair_injective he
  subst this
  rw [hps] at hp''
  obtain ⟨g, hg, -, h1, -⟩ := (mem_graphOf e L).1 hp''
  rw [← h1, (toFin e).symm_apply_apply]
  exact hg

end Start

end GI.Impl
