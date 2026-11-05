module

public import Workspace.Impl.AggCertMoves

@[expose] public section

/-!
# The certificate phase, from a move function

`cert_phase_spec`: if a move function `mv` meets the condition of `stepOKC_of_move` for the
relation `CpRep` (which the moves of `AggCertStart.lean`, `AggCertClose.lean`,
`AggCertNext.lean` and `AggCertMoves.lean` give, once a program computes their data), then the
script runner with the loop of moves as step function runs the certificate phase: on the
initial program state it returns the output (`CpOut`: the graph forms of the final groups of all
test sets) of a run of `certPhase … R …` for coset representatives `R` that agree with the
choices the program made, with at most `f₀ = cpMeas_start` calls, at cost at most
`(n + 1) runK (B + 1)` plus the cost of the calls, where `n` is the number of calls and
`B = (M + 1) (20 Bm + 2 Bw + 60) + Bw` (`stepOKC_of_move`).

`cpRep_init`: the initial program state stands for the phase.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)
open scoped Pointwise

section Phase

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : GiantLabels S} {πd : S.domGroup →* alternatingGroup (Fin L.q)}

/-- The data at the start of the phase, for the test sets `T :: Ts`. -/
def CpSt.init {k q : ℕ} (T : Finset (Fin q)) (Ts : List (Finset (Fin q))) (p0 : GPairs k q)
    (osA : List (Fin (k + q))) : CpSt k q :=
  { Ts := Ts, s := false, res := [], cache := [], p0 := p0, px := [], t := 0, ps := p0,
    osP := osA, T := T, lz := [], lx := [], logs := [] }

/-- **The initial program state stands for the phase**: for the candidates of the empty record
(all coset representatives), the phase is the start of the first round of `x`. -/
theorem cpRep_init (O : TestSetOrder L.q P₀.κ) {par : Val} {D Bw : ℕ}
    {T : Finset (Fin L.q)} {Ts : List (Finset (Fin L.q))} (hO : O.sets = T :: Ts)
    (hcard : ∀ T' ∈ O.sets, T'.card = P₀.κ) {p0 : GPairs k L.q}
    (hp0 : PairGens e L (S.liftGroup (Pgrp S.domGroup πd T)) p0)
    {osA : List (Fin (k + L.q))} (hA : CpAll e S L.q osA) (hlen : CpLen D (CpSt.init T Ts p0 osA))
    {u : Val}
    (hwt : (Val.list [(CpSt.init T Ts p0 osA).val par (.list []), u]).wt ≤ Bw) :
    CpRep e πd par D Bw ((2 * Ts.length + 2) * (Fintype.card S.dom + 1) * (D + 2))
      (Ts.length + 1) ((2 * Ts.length + 2) * (Fintype.card S.dom + 1) * (D + 2))
      (.list [(CpSt.init T Ts p0 osA).val par (.list []), u])
      ((fun R => certPhase S πd P₀.κ O R (dstr S S.x) (dstr S S.y)) '' Cands [])
      ((2 * Ts.length + 2) * (Fintype.card S.dom + 1) * (D + 2)) := by
  have hm := cpMeas_start (S := S) (n := Fintype.card S.dom) (D := D) (T := T) (Ts := Ts)
  rw [hO] at hcard
  refine ⟨.round [] T Ts false 0, CpSt.init T Ts p0 osA, [], hm.symm, le_rfl, hwt,
    by simp [CpSt.init], by simp [CpSt.init], hlen, ?_, rfl, rfl, rfl, rfl, ?_, u, rfl⟩
  · ext s
    simp only [Set.mem_image]
    constructor <;> rintro ⟨R, hR, rfl⟩ <;> exact ⟨R, hR, by rw [cpAt_start S πd _ _ P₀.κ O R hO]⟩
  · refine ⟨hcard T (List.mem_cons_self ..), fun T' hT' => hcard T' (List.mem_cons_of_mem _ hT'),
      Nat.zero_le _, List.Forall₂.nil, ⟨CacheOK.nil, fun ent h => by simp [CpSt.init] at h⟩, hp0,
      fun h => by simp [CpSt.init] at h, hp0, ?_, ⟨O, by simpa [CpSt.init] using hO.symm⟩, rfl,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun h => by simp [CpSt.init] at h,
      fun l h => by simp [CpSt.init] at h,
      ⟨rfl, cpLgLen_nil, cpLgLen_nil, fun l h => by simp [CpSt.init] at h⟩, List.Forall₂.nil⟩
    obtain ⟨os, hnd, hall, rfl⟩ := hA
    refine ⟨os, hnd, fun v => ?_, rfl⟩
    simp only [CpSt.init, win_zero, Finset.notMem_empty, not_false_eq_true, iff_true]
    exact hall v

variable (I : Iface) (Pg : Program) (F : Funs)

/-- **The certificate phase, from a move function.** -/
theorem cert_phase_spec {d stp mv : ℕ} (hd : Pg.funs[d]? = some (runBody F d stp))
    (hstp : Pg.funs[stp]? = some (cpLoopBody stp mv)) {par : Val} {D Bm Bw M₀ NT : ℕ}
    (hmv : ∀ m st Ss f, CpRep e πd par D Bw M₀ NT m st Ss f → FunAll Pg mv st (fun w c =>
      c ≤ Bm ∧ (Iface.StepPostC (measure P₀ .giant S) (CpOut e S L πd)
          (fun st Ss f => ∃ m, CpRep e πd par D Bw M₀ NT m st Ss f) Ss f w ∨
        ∃ m' st' Ss', m' < m ∧ Ss' ⊆ Ss ∧ CpRep e πd par D Bw M₀ NT m' st' Ss' f ∧
          w = .list [.nat 2, st'])))
    (ih : I.IHBelow Pg F (measure P₀ .giant S))
    (κ : ℕ) (O : TestSetOrder L.q κ) {st₀ : Val} {m₀ f₀ : ℕ}
    (h₀ : CpRep e πd par D Bw M₀ NT m₀ st₀
      ((fun R => certPhase S πd κ O R (dstr S S.x) (dstr S S.y)) '' Cands []) f₀) :
    FunAll Pg d st₀ (fun out cost => ∃ R : CosetRepFn S.dom, ∃ (a : List (StagePair S))
      (ex : Exec P₀ (certPhase S πd κ O R (dstr S S.x) (dstr S S.y)) a), CpOut e S L πd a out ∧
      ex.calls.length ≤ f₀ ∧
      (cost : ℝ) ≤ ((ex.calls.length : ℝ) + 1) *
        (runK * (((M₀ + 1) * cpLoopC Bm Bw + Bw : ℕ) + 1)) + I.execCost ex) := by
  have hs := stepOKC_of_move (M := M₀) hstp hmv (fun m st Ss f h => by
      obtain ⟨_, _, _, _, _, hw, _⟩ := h; exact hw)
    (fun m st Ss f h => by obtain ⟨_, _, _, hm, _, _, hM, _⟩ := h; omega)
  refine (I.run_specC Pg F hd hs ih f₀ st₀ _ ⟨m₀, h₀⟩).mono ?_
  rintro out cost ⟨s, ⟨R, -, rfl⟩, a, ex, hout, -, hlen, hc⟩
  exact ⟨R, a, ex, hout, hlen, by exact_mod_cast hc⟩

end Phase

end GI.Impl
