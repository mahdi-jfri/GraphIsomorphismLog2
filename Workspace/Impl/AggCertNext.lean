import Workspace.Impl.AggCertClose

/-!
# The next window call of a round, on program data

After the answer `u` of the window call of `a`, if representatives remain, the program adds the
generators of the answer to the collected ones (`ansGens_spec`) and asks the window call of the
next representative `a'`. `cp_answer_next` says that this meets `StepPostC` for `CpRep`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)
open scoped Pointwise

section Next

variable {k : ℕ} {Ω C : Type} [Finite Ω] [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ}
  {S : State Ω C} [Fintype S.dom] {L : GiantLabels S}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}

/-- **The next window call of a round.** -/
theorem cp_answer_next (hc : Function.Injective c) {sv : Val} (hS : Canon e c sv S) {hv : Val}
    (hh : HierValC e hv S.hier) (hgood : Good P₀ .giant S) (htr : S.Transitive)
    {par : Val} {D Bw M₀ NT m f : ℕ}
    {acc : List (StagePair S)} {T : Finset (Fin L.q)} {σ : CpSt k L.q}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    {acc' : List (Set (Perm S.dom))} {u : Val}
    {dn : List (Perm (Fin k) × Option (Perm (Fin k) × List (Perm (Fin k))))} {a a' : Perm (Fin k)}
    {as hs : List (Perm (Fin k))} {dv : Val} {incl : List S.dom}
    (hm : m = cpMeas (Fintype.card S.dom) D
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
    (hwt : ∀ u', AnsC e u' (cpCall πd T σ.s σ.t (domOfPos e S a')).answer →
      (Val.list [CpSt.val par σ (cpInnerV as (stageGens (dn ++ [(a, o)])) hs dv
        (incl.map (domPos e L.q)) a'), u']).wt ≤ Bw) :
    Iface.StepPostC (measure P₀ .giant S) (CpOut e S L πd)
      (fun st Ss f => ∃ m, CpRep e πd par D Bw M₀ NT m st Ss f)
      ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R
        (.win acc T σ.Ts σ.s σ.t ((a' :: as).map (domOfPos e S)) acc')) '' Cands rec) f
      (.list [.nat 1, .nat (modeCode .cont), winVal' k (encGroup hs) dv
        (natList (winCodesX e c S (cpZ S σ.s) a')) (natList (winCodesY e c S (cpZ S σ.s) a'))
        hv S.N,
        CpSt.val par σ (cpInnerV as (stageGens (dn ++ [(a, o)])) hs dv
          (incl.map (domPos e L.q)) a')]) := by
  obtain ⟨hk5, hκ, hθ⟩ := cp_card_facts hR.card
  obtain ⟨g, rfl⟩ : ∃ g, toFin e g = a' :=
    ⟨(toFin e).symm a', (toFin e).apply_symm_apply a'⟩
  have hg : g ∈ S.G := by
    have := hG (toFin e g) (by simp)
    rwa [(toFin e).symm_apply_apply] at this
  have hτ : S.domHom ⟨g, hg⟩ = domOfPos e S (toFin e g) := (domOfPos_toFin e S hg).symm
  have hset : ∀ (τs : List (Perm S.dom)) (acc'' : List (Set (Perm S.dom))),
      (fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R (.win acc T σ.Ts σ.s σ.t τs acc'')) =
      fun R => cpWin S (phiT S.domGroup πd T) (dstr S (cpZ S σ.s)) (Fintype.card S.dom)
        (cpK S πd (dstr S S.x) (dstr S S.y) acc T σ.Ts σ.s) R σ.t τs acc'' := fun τs acc'' =>
    funext fun R => cpAt_win_eq R acc T σ.Ts σ.s σ.t τs acc''
  have hm0 : 0 < m := by rw [hm]; simp only [cpMeas]; omega
  have hlist : (toFin e g :: as).map (domOfPos e S) = S.domHom ⟨g, hg⟩ :: as.map (domOfPos e S) := by
    rw [List.map_cons, hτ]
  rw [hset, hlist]
  refine cp_window_step hc hS hh hgood htr πd T hk5 hκ hθ (cpZ S σ.s) (Fintype.card S.dom)
    (cpK S πd (dstr S S.x) (dstr S S.y) acc T σ.Ts σ.s) (hR.cache.1.cands_nonempty
      (CosetRepFn.default S.dom)) σ.t hg (as.map (domOfPos e S)) acc' hgv hdv (f := f) (by omega)
    fun u hu => ?_
  rw [← hset]
  have hu' : AnsC e u (cpCall πd T σ.s σ.t (domOfPos e S (toFin e g))).answer := by
    rw [← hτ]; exact hu
  set pos : CpPos S L.q := .win acc T σ.Ts σ.s σ.t (as.map (domOfPos e S))
    (acc' ++ [winVal S (S.domHom ⟨g, hg⟩) (windowCall S (kernelIn (phiT S.domGroup πd T)
      (grp (phiT S.domGroup πd T) (dstr S (cpZ S σ.s)) σ.t)) (inc (phiT S.domGroup πd T)
      (dstr S (cpZ S σ.s)) σ.t) (cpInv S (phiT S.domGroup πd T) (dstr S (cpZ S σ.s)) σ.t)
      (dstr S (cpZ S σ.s)) (S.domHom ⟨g, hg⟩)).answer]) with hpos
  have hlt : cpMeas (Fintype.card S.dom) D pos < m := by
    rw [hm, hpos]
    exact cpMeas_win_cons
  refine ⟨cpMeas (Fintype.card S.dom) D pos, pos, σ, rec, rfl, by omega,
    hwt u hu', by omega, hNT, hlen, rfl, hT, rfl, rfl, rfl, _, u, rfl,
    ⟨hR, ht, hne, dn ++ [(a, o)], toFin e g, as, hs, dv, incl, rfl, by simpa using hl,
    by simpa using hG, rfl, fun p hp => ?_, ?_, hu', hgv, hdv, hnd, hinc⟩, hin⟩
  · rcases List.mem_append.1 hp with hp | hp
    · exact ho p hp
    · rw [List.mem_singleton.1 hp]; exact hao
  · rw [hacc]
    simp only [List.map_append, List.map_cons, List.map_nil, cpAcc, List.append_assoc,
      List.singleton_append, hτ]

end Next

end GI.Impl
