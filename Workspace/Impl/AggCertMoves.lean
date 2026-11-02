import Workspace.Impl.AggCertNext

/-!
# The moves without calls, for the relation `CpRep`

`AggCertTrans.lean` gives the data after each move without a call; this file adds the measure,
the candidate set and the bounds, in the form that `stepOKC_of_move` asks: either the move
continues to a program state of smaller measure that stands for a subset of the candidates
(`cp_round_empty_rep`, `cp_x_end_rep`, `cp_y_end_cons_rep`), or it finishes
(`cp_y_end_nil_post`). `cp_reps_length_le` bounds the number of representatives of one round by
`|Alt(T)|`, which is the `D` of the measure.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)
open scoped Pointwise

section Moves

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : GiantLabels S} {πd : S.domGroup →* alternatingGroup (Fin L.q)}

/-- **At most `|Alt(T)|` representatives in a round**: the recorded representatives are one per
coset of the kernel, and the quotient embeds in `Alt(T)`. -/
theorem cp_reps_length_le {T : Finset (Fin L.q)} {A : Subgroup (Perm S.dom)}
    (hA : A ≤ Pgrp S.domGroup πd T) {l : List (Perm S.dom)}
    (h : RepsOK (A, kernelIn (cpPhi S πd T) A) l) :
    l.length ≤ Nat.card (alternatingGroup T) := by
  refine h.2.2.trans ?_
  show Nat.card (A ⧸ (kernelIn (cpPhi S πd T) A).subgroupOf A) ≤ _
  rw [card_quot_kernelIn _ hA]
  exact Subgroup.card_le_card_group _

/-- The common form of a move that continues. -/
def CpCont (par : Val) (D Bw M₀ NT : ℕ) (m : ℕ) (Ss : Set (Script (List (StagePair S))))
    (f : ℕ) (st' : Val) : Prop :=
  ∃ m' Ss', m' < m ∧ Ss' ⊆ Ss ∧ CpRep e πd par D Bw M₀ NT m' st' Ss' f

/-- **A round with an empty increment.** -/
theorem cp_round_empty_rep {par : Val} {D Bw M₀ NT m f : ℕ} {σ : CpSt k L.q}
    {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec)
    (hm : m = cpMeas (Fintype.card S.dom) D (.round acc T σ.Ts σ.s σ.t)) (hmf : m ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hNT : σ.res.length + σ.Ts.length + 1 ≤ NT)
    (ht : σ.t < Fintype.card S.dom) (he : inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t = ∅)
    (hT : T = σ.T) (hlen : CpLen D σ.succ)
    {u : Val} (hwt : (Val.list [σ.succ.val par (.list []), u]).wt ≤ Bw) :
    CpCont (e := e) (πd := πd) par D Bw M₀ NT m
      ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R (.round acc T σ.Ts σ.s σ.t)) '' Cands rec)
      f (.list [σ.succ.val par (.list []), u]) := by
  have hlt : cpMeas (Fintype.card S.dom) D (.round acc T σ.Ts σ.s (σ.t + 1) : CpPos S L.q) < m :=
    hm ▸ cpMeas_round_succ ht
  refine ⟨_, _, hlt, ?_, ⟨.round acc T σ.Ts σ.s (σ.t + 1), σ.succ, rec, rfl, by omega, hwt,
    by simp only [CpSt.succ]; omega, by simp only [CpSt.succ]; omega, hlen, rfl, hT, rfl, rfl, rfl,
    h.succ_empty ht he hlen.2.2.2.2.1, u, rfl⟩⟩
  rintro _ ⟨R, hR, rfl⟩
  exact ⟨R, hR, cpAt_round_empty S πd _ _ R acc T σ.Ts σ.s ht (by rw [cpStr_dstr]; exact he)⟩

/-- **The end of the loop of `x`.** -/
theorem cp_x_end_rep {par : Val} {D Bw M₀ NT m f : ℕ} {σ : CpSt k L.q}
    {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec)
    (hm : m = cpMeas (Fintype.card S.dom) D (.round acc T σ.Ts σ.s σ.t)) (hmf : m ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hNT : σ.res.length + σ.Ts.length + 1 ≤ NT)
    (hs : σ.s = false) (ht : σ.t = Fintype.card S.dom)
    {osA : List (Fin (k + L.q))} (hA : CpAll e S L.q osA)
    (hT : T = σ.T) (hlen : CpLen D (σ.yStart osA))
    {u : Val} (hwt : (Val.list [(σ.yStart osA).val par (.list []), u]).wt ≤ Bw) :
    CpCont (e := e) (πd := πd) par D Bw M₀ NT m
      ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R (.round acc T σ.Ts σ.s σ.t)) '' Cands rec)
      f (.list [(σ.yStart osA).val par (.list []), u]) := by
  have hlt : cpMeas (Fintype.card S.dom) D (.round acc T σ.Ts true 0 : CpPos S L.q) < m := by
    rw [hm, hs, ht]; exact cpMeas_x_end
  refine ⟨_, _, hlt, ?_, ⟨.round acc T σ.Ts true 0, σ.yStart osA, rec, rfl, by omega, hwt,
    by simp only [CpSt.yStart]; omega, by simp only [CpSt.yStart]; omega, hlen, rfl, hT, rfl, rfl,
    rfl, h.x_end hs ht hA, u, rfl⟩⟩
  rintro _ ⟨R, hR, rfl⟩
  refine ⟨R, hR, ?_⟩
  simp only
  rw [hs, ht, cpAt_x_end]

/-- **The end of the loop of `y`, with more test sets**; `p0` is the graph form of the next
`P_T` (`ptGraph_spec`). -/
theorem cp_y_end_cons_rep {par : Val} {D Bw M₀ NT m f : ℕ} {σ : CpSt k L.q}
    {acc : List (StagePair S)} {T T' : Finset (Fin L.q)} {Ts : List (Finset (Fin L.q))}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec)
    (hm : m = cpMeas (Fintype.card S.dom) D (.round acc T σ.Ts σ.s σ.t)) (hmf : m ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hNT : σ.res.length + σ.Ts.length + 1 ≤ NT)
    (hs : σ.s = true) (ht : σ.t = Fintype.card S.dom) (hTs : σ.Ts = T' :: Ts) (hT : T = σ.T)
    {p0 : GPairs k L.q} (hp0 : PairGens e L (S.liftGroup (Pgrp S.domGroup πd T')) p0)
    {osA : List (Fin (k + L.q))} (hA : CpAll e S L.q osA) (hlen : CpLen D (σ.next T' Ts p0 osA))
    {u : Val} (hwt : (Val.list [(σ.next T' Ts p0 osA).val par (.list []), u]).wt ≤ Bw) :
    CpCont (e := e) (πd := πd) par D Bw M₀ NT m
      ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R (.round acc T σ.Ts σ.s σ.t)) '' Cands rec)
      f (.list [(σ.next T' Ts p0 osA).val par (.list []), u]) := by
  have hlt : cpMeas (Fintype.card S.dom) D
      (.round (acc ++ [cpPair S πd (dstr S S.x) (dstr S S.y) T]) T' Ts false 0 : CpPos S L.q) <
      m := by
    rw [hm, hs, ht, hTs]; exact cpMeas_y_end_cons
  have hNT' : (σ.next T' Ts p0 osA).res.length + (σ.next T' Ts p0 osA).Ts.length + 1 ≤ NT := by
    simp only [CpSt.next, List.length_append, List.length_singleton]
    rw [hTs, List.length_cons] at hNT
    omega
  refine ⟨_, _, hlt, ?_, ⟨.round (acc ++ [cpPair S πd (dstr S S.x) (dstr S S.y) T]) T' Ts false 0,
    σ.next T' Ts p0 osA, rec, rfl, by omega, hwt, by simp only [CpSt.next]; omega,
    hNT', hlen, rfl, rfl, rfl, rfl, rfl, h.y_end_cons hT hs ht hTs hp0 hA, u, rfl⟩⟩
  rintro _ ⟨R, hR, rfl⟩
  refine ⟨R, hR, ?_⟩
  simp only
  rw [hs, ht, hTs, cpAt_y_end_cons]

/-- **The end of the phase**: after the loop of `y` of the last test set, the move returns the
output. -/
theorem cp_y_end_nil_post {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ}
    {Rep : Val → Set (Script (List (StagePair S))) → ℕ → Prop} {f : ℕ} {σ : CpSt k L.q}
    {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) (hs : σ.s = true) (ht : σ.t = Fintype.card S.dom)
    (hTs : σ.Ts = [])
    (hlen : ∀ r ∈ σ.res ++ [(σ.px, σ.ps)], r.1.length ≤ (k + L.q) ^ 2 ∧
      r.2.length ≤ (k + L.q) ^ 2) :
    Iface.StepPostC μ (CpOut e S L πd) Rep
      ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R (.round acc T σ.Ts σ.s σ.t)) '' Cands rec)
      f (.list [.nat 0, .list [.list ((σ.res ++ [(σ.px, σ.ps)]).map resV),
        .list ((σ.logs ++ [(T, σ.lx, σ.lz)]).map cpLogV)]]) := by
  obtain ⟨R, hR⟩ := h.cache.1.cands_nonempty (CosetRepFn.default S.dom)
  refine stepPostC_done _ hR (a := acc ++ [cpPair S πd (dstr S S.x) (dstr S S.y) T]) ?_
    (cpOut_y_end_nil h hs ht hTs hlen)
  rw [hs, ht, hTs, cpAt_y_end_nil]
  rfl

end Moves

end GI.Impl
