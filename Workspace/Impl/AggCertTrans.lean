module

public import Workspace.Impl.AggCertRep

@[expose] public section

/-!
# The moves of the certificate phase on program data

For each move of the walk (`AggCertWalk.lean`), what the program must compute and why the new
data stands for the new position (`CpRoundInv`, `CpWinInv`, `AggCertRep.lean`). These lemmas
say nothing about programs; the move function only has to compute the named values.

Moves without a call:

* `CpRoundInv.succ_empty`: a round with an empty increment keeps the stage; only `t` grows.
* `CpRoundInv.x_end`: after the last round of `x`, the loop of `y` starts at `P_T` with the
  whole domain outside the window; the final group of `x` is kept.
* `CpRoundInv.y_end_cons`: after the last round of `y`, the pair of final groups is added to the
  results and the next test set starts (its `P_T` computed by `ptGraph_spec`).
* `cpOut_y_end_nil`: after the last round of `y` of the last test set, the results are the output
  (`CpOut`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)
open scoped Pointwise

/-- The data of the next round after a round with an empty increment: the stage `(ps, [])` is
logged. -/
def CpSt.succ {k q : ℕ} (σ : CpSt k q) : CpSt k q :=
  { σ with t := σ.t + 1, lz := σ.lz ++ [(σ.ps, [])] }

/-- The data at the start of the loop of `y`, with the points `osA` of the whole domain; the log
of `x` is kept. -/
def CpSt.yStart {k q : ℕ} (σ : CpSt k q) (osA : List (Fin (k + q))) : CpSt k q :=
  { σ with s := true, t := 0, px := σ.ps, ps := σ.p0, osP := osA, lz := [], lx := σ.lz }

/-- The data at the start of the next test set, with the graph form `p0` of its `P_T`; the log
of the finished test set is stored. -/
def CpSt.next {k q : ℕ} (σ : CpSt k q) (T : Finset (Fin q)) (Ts : List (Finset (Fin q)))
    (p0 : GPairs k q) (osA : List (Fin (k + q))) : CpSt k q :=
  { Ts := Ts, s := false, res := σ.res ++ [(σ.px, σ.ps)], cache := σ.cache, p0 := p0, px := σ.px,
    t := 0, ps := p0, osP := osA, T := T, lz := [], lx := [],
    logs := σ.logs ++ [(σ.T, σ.lx, σ.lz)] }

/-- A property of all indexed entries survives appending one entry. -/
theorem cp_idx_snoc {α : Type} {P : ℕ → α → Prop} {l : List α} {a : α}
    (h : ∀ j (hj : j < l.length), P j l[j]) (ha : P l.length a) :
    ∀ j (hj : j < (l ++ [a]).length), P j (l ++ [a])[j] := by
  intro j hj
  rcases Nat.lt_or_ge j l.length with h1 | h1
  · rw [List.getElem_append_left h1]; exact h j h1
  · have hj' : j = l.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst hj'
    rw [List.getElem_append_right (le_refl _)]
    simpa using ha

/-- Length bounds of a log survive appending a stage. -/
theorem cpLgLen_snoc {k q : ℕ} {l : List (CpStgD k q)} {d : CpStgD k q} (h : CpLgLen l)
    (hl : l.length < k) (hd : CpSgLen d) : CpLgLen (l ++ [d]) := by
  refine ⟨by simp only [List.length_append, List.length_singleton]; omega, fun d' hd' => ?_⟩
  rcases List.mem_append.1 hd' with h' | h'
  · exact h.2 d' h'
  · rw [List.mem_singleton.1 h']; exact hd

theorem cpLgLen_nil {k q : ℕ} : CpLgLen ([] : List (CpStgD k q)) :=
  ⟨Nat.zero_le _, fun _ h => absurd h List.not_mem_nil⟩

theorem cp_card_dom_le {k : ℕ} {Ω C : Type} {S : State Ω C} [Fintype S.dom] (e : Ω ≃ Fin k) :
    Fintype.card S.dom ≤ k := by
  have := Fintype.card_le_of_injective (fun v : S.dom => e v.1) fun a b h =>
    Subtype.ext (e.injective h)
  simpa using this

theorem cp_os_length_le {k : ℕ} {Ω C : Type} {S : State Ω C} [Fintype S.dom] (e : Ω ≃ Fin k)
    {os : List S.dom} (h : os.Nodup) : os.length ≤ k :=
  (List.Nodup.length_le_card h).trans (cp_card_dom_le e)

section Moves

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : GiantLabels S} {πd : S.domGroup →* alternatingGroup (Fin L.q)}

/-- A round with an empty increment keeps the stage. -/
theorem stage_succ_of_inc_empty {V Q C₀ : Type} [DecidableEq V] [Fintype V] [Group Q]
    {P : Subgroup (Perm V)} (phi : P →* Q) (z : V → C₀) {t : ℕ} (h : inc phi z t = ∅) :
    stage phi z (t + 1) = stage phi z t := by
  apply Prod.ext
  · change grp phi z (t + 1) = grp phi z t
    rw [grp_succ, h, automorphisms_mask_empty]
  · change win phi z (t + 1) = win phi z t
    rw [win_succ, h, Finset.union_empty]

/-- **A round with an empty increment**: the same data with `t + 1`; the stage of round `t`
is logged with an empty increment. -/
theorem CpRoundInv.succ_empty {σ : CpSt k L.q} {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) (ht : σ.t < Fintype.card S.dom)
    (he : inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t = ∅)
    (hpsl : σ.ps.length ≤ (k + L.q) ^ 2) :
    CpRoundInv e πd σ.succ acc T rec := by
  have hs := stage_succ_of_inc_empty (cpPhi S πd T) (dstr S (cpZ S σ.s)) he
  have hg : grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) (σ.t + 1) =
      grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t := congrArg Prod.fst hs
  have hw : win (cpPhi S πd T) (dstr S (cpZ S σ.s)) (σ.t + 1) =
      win (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t := congrArg Prod.snd hs
  have hnk := cp_card_dom_le (S := S) e
  have hd : CpStg e πd T (cpZ S σ.s) σ.lz.length (σ.ps, []) := by
    refine ⟨?_, hpsl, [], List.nodup_nil, fun v => ?_, rfl⟩
    · rw [h.lz_len]; exact h.ps
    · rw [h.lz_len, he]; simp
  refine { h with t_le := ht, ps := ?_, os := ?_, lz_len := ?_, lz := ?_, loglen := ?_ }
  · simp only [CpSt.succ]
    rw [hg]; exact h.ps
  · simp only [CpSt.succ]
    rw [hw]; exact h.os
  · simp only [CpSt.succ, List.length_append, List.length_singleton, h.lz_len]
  · exact cp_idx_snoc h.lz hd
  · exact { h.loglen with
      lz := cpLgLen_snoc h.loglen.lz (by rw [h.lz_len]; omega) ⟨hpsl, Nat.zero_le _⟩ }

/-- The whole domain, as the points outside the empty window. -/
def CpAll (e : Ω ≃ Fin k) (S : State Ω C) (q : ℕ) (osP : List (Fin (k + q))) : Prop :=
  ∃ os : List S.dom, os.Nodup ∧ (∀ v, v ∈ os) ∧ osP = os.map (domPos e q)

/-- **The end of the loop of `x`**: the loop of `y` starts at `P_T` with an empty window; the
log of `x` is complete. -/
theorem CpRoundInv.x_end {σ : CpSt k L.q} {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) (hs : σ.s = false) (ht : σ.t = Fintype.card S.dom)
    {osA : List (Fin (k + L.q))} (hA : CpAll e S L.q osA) :
    CpRoundInv e πd (σ.yStart osA) acc T rec := by
  refine { h with
    t_le := Nat.zero_le _
    px := fun _ => ?_
    ps := h.p0
    os := ?_
    lz_len := rfl
    lz := fun j hj => absurd hj (Nat.not_lt_zero _)
    lx := fun _ => ?_
    loglen := { h.loglen with lz := cpLgLen_nil, lx := h.loglen.lz } }
  · have := h.ps
    rw [hs, ht] at this
    exact this
  · obtain ⟨os, hnd, hall, rfl⟩ := hA
    refine ⟨os, hnd, fun v => ?_, rfl⟩
    simp only [CpSt.yStart, win_zero, Finset.notMem_empty, not_false_eq_true, iff_true]
    exact hall v
  · have hz := h.lz
    rw [hs] at hz
    exact ⟨h.lz_len.trans ht, hz⟩

/-- **The output of the phase**: `[⟨results⟩, ⟨logs⟩]`, the graph forms of the final groups
for every test set in order, and the logs of all test sets in the order of a `TestSetOrder`. -/
def CpOut (e : Ω ≃ Fin k) (S : State Ω C) [Fintype S.dom] (L : GiantLabels S)
    (πd : S.domGroup →* alternatingGroup (Fin L.q)) (a : List (StagePair S)) (out : Val) : Prop :=
  ∃ (res : List (GPairs k L.q × GPairs k L.q))
    (logs : List (Finset (Fin L.q) × List (CpStgD k L.q) × List (CpStgD k L.q))),
    out = .list [.list (res.map resV), .list (logs.map cpLogV)] ∧
    List.Forall₂ (fun (r : StagePair S) (p : GPairs k L.q × GPairs k L.q) =>
      PairGens e L (S.liftGroup r.1.1) p.1 ∧ PairGens e L (S.liftGroup r.2.1) p.2) a res ∧
    (∃ O : TestSetOrder L.q P₀.κ, logs.map Prod.fst = O.sets) ∧
    (∀ l ∈ logs, CpStgs e πd l.1 S.x l.2.1 ∧ CpStgs e πd l.1 S.y l.2.2) ∧
    (∀ l ∈ logs, CpLgLen l.2.1 ∧ CpLgLen l.2.2) ∧
    List.Forall₂ (fun (l : Finset (Fin L.q) × List (CpStgD k L.q) × List (CpStgD k L.q))
      (p : GPairs k L.q × GPairs k L.q) =>
        PairGens e L (S.liftGroup (grp (cpPhi S πd l.1) (dstr S S.x) (Fintype.card S.dom))) p.1 ∧
        PairGens e L (S.liftGroup (grp (cpPhi S πd l.1) (dstr S S.y) (Fintype.card S.dom))) p.2)
      logs res ∧
    ∀ r ∈ res, r.1.length ≤ (k + L.q) ^ 2 ∧ r.2.length ≤ (k + L.q) ^ 2

/-- The results and the logs after the loop of `y` still match. -/
theorem CpRoundInv.resLog_y_end {σ : CpSt k L.q} {acc : List (StagePair S)}
    {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) (hs : σ.s = true) (ht : σ.t = Fintype.card S.dom) :
    List.Forall₂ (fun (l : Finset (Fin L.q) × List (CpStgD k L.q) × List (CpStgD k L.q))
      (p : GPairs k L.q × GPairs k L.q) =>
        PairGens e L (S.liftGroup (grp (cpPhi S πd l.1) (dstr S S.x) (Fintype.card S.dom))) p.1 ∧
        PairGens e L (S.liftGroup (grp (cpPhi S πd l.1) (dstr S S.y) (Fintype.card S.dom))) p.2)
      (σ.logs ++ [(T, σ.lx, σ.lz)]) (σ.res ++ [(σ.px, σ.ps)]) := by
  refine List.rel_append h.resLog (List.Forall₂.cons ⟨h.px hs, ?_⟩ List.Forall₂.nil)
  have := h.ps
  rw [hs, ht] at this
  exact this

/-- The results after the loop of `y`: the pair of final stages is added. -/
theorem CpRoundInv.res_y_end {σ : CpSt k L.q} {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) (hs : σ.s = true) (ht : σ.t = Fintype.card S.dom) :
    List.Forall₂ (fun (r : StagePair S) (p : GPairs k L.q × GPairs k L.q) =>
      PairGens e L (S.liftGroup r.1.1) p.1 ∧ PairGens e L (S.liftGroup r.2.1) p.2)
      (acc ++ [cpPair S πd (dstr S S.x) (dstr S S.y) T]) (σ.res ++ [(σ.px, σ.ps)]) := by
  refine List.rel_append h.res (List.Forall₂.cons ⟨h.px hs, ?_⟩ List.Forall₂.nil)
  have := h.ps
  rw [hs, ht] at this
  exact this

/-- The logs after the loop of `y`: the log of `T` is added. -/
theorem CpRoundInv.logs_y_end {σ : CpSt k L.q} {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) (hs : σ.s = true) (ht : σ.t = Fintype.card S.dom) :
    ∀ l ∈ σ.logs ++ [(T, σ.lx, σ.lz)], CpStgs e πd l.1 S.x l.2.1 ∧ CpStgs e πd l.1 S.y l.2.2 := by
  intro l hl
  rcases List.mem_append.1 hl with hl | hl
  · exact h.logs l hl
  · rw [List.mem_singleton.1 hl]
    have hz := h.lz
    rw [hs] at hz
    exact ⟨h.lx hs, h.lz_len.trans ht, hz⟩

theorem CpRoundInv.loglen_y_end {σ : CpSt k L.q} {acc : List (StagePair S)}
    {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) :
    ∀ l ∈ σ.logs ++ [(T, σ.lx, σ.lz)], CpLgLen l.2.1 ∧ CpLgLen l.2.2 := by
  intro l hl
  rcases List.mem_append.1 hl with hl | hl
  · exact h.loglen.logs l hl
  · rw [List.mem_singleton.1 hl]; exact ⟨h.loglen.lx, h.loglen.lz⟩

/-- **The end of the loop of `y`, for the last test set**: the results and the logs are the
output. -/
theorem cpOut_y_end_nil {σ : CpSt k L.q} {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) (hs : σ.s = true) (ht : σ.t = Fintype.card S.dom)
    (hTs : σ.Ts = [])
    (hlen : ∀ r ∈ σ.res ++ [(σ.px, σ.ps)], r.1.length ≤ (k + L.q) ^ 2 ∧
      r.2.length ≤ (k + L.q) ^ 2) :
    CpOut e S L πd (acc ++ [cpPair S πd (dstr S S.x) (dstr S S.y) T])
      (.list [.list ((σ.res ++ [(σ.px, σ.ps)]).map resV),
        .list ((σ.logs ++ [(T, σ.lx, σ.lz)]).map cpLogV)]) := by
  refine ⟨_, _, rfl, h.res_y_end hs ht, ?_, h.logs_y_end hs ht, h.loglen_y_end,
    h.resLog_y_end hs ht, hlen⟩
  obtain ⟨O, hO⟩ := h.ord
  exact ⟨O, by rw [← hO, hTs]; simp⟩

/-- **The end of the loop of `y`, with more test sets**: the next test set starts with its
`P_T` (graph form `p0`) and an empty window. -/
theorem CpRoundInv.y_end_cons {σ : CpSt k L.q} {acc : List (StagePair S)} {T T' : Finset (Fin L.q)}
    {Ts : List (Finset (Fin L.q))}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (h : CpRoundInv e πd σ acc T rec) (hT : T = σ.T) (hs : σ.s = true)
    (ht : σ.t = Fintype.card S.dom)
    (hTs : σ.Ts = T' :: Ts) {p0 : GPairs k L.q}
    (hp0 : PairGens e L (S.liftGroup (Pgrp S.domGroup πd T')) p0)
    {osA : List (Fin (k + L.q))} (hA : CpAll e S L.q osA) :
    CpRoundInv e πd (σ.next T' Ts p0 osA) (acc ++ [cpPair S πd (dstr S S.x) (dstr S S.y) T]) T'
      rec := by
  have hc := h.cardTs
  rw [hTs] at hc
  have hlog := h.logs_y_end hs ht
  have hll := h.loglen_y_end
  have hrl := h.resLog_y_end hs ht
  rw [hT] at hlog hll hrl
  refine ⟨hc T' (List.mem_cons_self ..), fun T'' hT'' => hc T'' (List.mem_cons_of_mem _ hT''),
    Nat.zero_le _, h.res_y_end hs ht, h.cache, hp0, fun h' => absurd h' (by simp [CpSt.next]), hp0,
    ?_, ?_, rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun h' => absurd h' (by simp [CpSt.next]),
    hlog, ⟨?_, cpLgLen_nil, cpLgLen_nil, hll⟩, hrl⟩
  · obtain ⟨os, hnd, hall, rfl⟩ := hA
    refine ⟨os, hnd, fun v => ?_, rfl⟩
    simp only [CpSt.next, win_zero, Finset.notMem_empty, not_false_eq_true, iff_true]
    exact hall v
  · obtain ⟨O, hO⟩ := h.ord
    refine ⟨O, ?_⟩
    rw [← hO, hTs, hT]
    simp [CpSt.next]
  · simp only [CpSt.next, List.length_append, List.length_singleton, h.loglen.logs_len]

end Moves

end GI.Impl
