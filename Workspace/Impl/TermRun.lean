module

public import Workspace.Impl.TermLoop
public import Workspace.Impl.TermPrep

@[expose] public section

/-!
# The script phase of the row terminal (T1)

This file shows that the step function `tmStepF` (`TermLoop.lean`) with the call values of
`tmAskF` (`TermStep.lean`) meets `Iface.StepOK` for the terminal script `tmScr I 0` (`tm_stepOK`).
So the script runner (`Iface.run_spec`) runs the terminal's `5q²` calls and returns the
canonical answers of the calls, in the program's order (`tmOut`).

The program state `[[ctx, j, aN, aH], u]` stands for `tmScr I j` (`tmRep`): the lists, with `u`
added (`tmAbsN`, `tmAbsH`), are canonical answers of the first `j` calls. Every recursive run
returns the exact answer (`Run.exact`), so the rest of the script is fixed.

The calls are linked to the strings by `hTN`, `hTH`: the `N`-test on rows `a`, `c` is
`rowState ⟨hsN⟩ a c`, the coset call on rows `i`, `j` is `rowState ⟨hsH⟩ (x_i) (y_j)`, where
`hsN`, `hsH` are the generator lists of the context.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

variable {Ω C : Type}

/-- The weight of a list of values of weight at most `A`. -/
theorem wt_list_le_of {l : List Val} {A : ℕ} (h : ∀ v ∈ l, v.wt ≤ A) :
    (Val.list l).wt ≤ l.length * (2 * A + 1) + 4 := by
  have h1 := wt_list_le l
  have h2 : (l.map Val.wt).sum ≤ l.length * A := by
    have := List.sum_le_card_nsmul (l.map Val.wt) A (by
      simp only [List.mem_map, forall_exists_index, and_imp]
      rintro _ v hv rfl
      exact h v hv)
    simpa using this
  have : l.length * (2 * A + 1) = 2 * (l.length * A) + l.length := by ring
  omega

theorem mem_of_mem_tmAbsN {T4 j : ℕ} {aN : List Val} {u v : Val} (h : v ∈ aN) :
    v ∈ tmAbsN T4 j aN u := by
  unfold tmAbsN; split_ifs <;> simp [h]

theorem mem_of_mem_tmAbsH {T4 j : ℕ} {aH : List Val} {u v : Val} (h : v ∈ aH) :
    v ∈ tmAbsH T4 j aH u := by
  unfold tmAbsH; split_ifs <;> simp [h]

theorem length_le_tmAbsN (T4 j : ℕ) (aN : List Val) (u : Val) :
    aN.length ≤ (tmAbsN T4 j aN u).length := by
  unfold tmAbsN; split_ifs <;> simp

theorem length_le_tmAbsH (T4 j : ℕ) (aH : List Val) (u : Val) :
    aH.length ≤ (tmAbsH T4 j aH u).length := by
  unfold tmAbsH; split_ifs <;> simp

/-- The weight bound of a program state of the terminal. -/
def tmStW (Wc q A : ℕ) : ℕ := 4 * Wc + 100 * (q + 1) ^ 2 * (A + 1)

/-- **The weight of a program state.** -/
theorem wt_tmSt_le {ctx : Val} {j q A : ℕ} {aN aH : List Val} {u : Val}
    (hj : j ≤ 5 * q ^ 2) (hN : ∀ v ∈ tmAbsN (4 * q ^ 2) j aN u, v.wt ≤ A)
    (hH : ∀ v ∈ tmAbsH (4 * q ^ 2) j aH u, v.wt ≤ A)
    (lN : (tmAbsN (4 * q ^ 2) j aN u).length ≤ 4 * q ^ 2)
    (lH : (tmAbsH (4 * q ^ 2) j aH u).length ≤ q ^ 2) (hu : u.wt ≤ A) :
    (Val.list [tmKst ctx j aN aH, u]).wt ≤ tmStW ctx.wt q A := by
  have wN := wt_list_le_of (l := aN) (A := A) fun v hv => hN v (mem_of_mem_tmAbsN hv)
  have wH := wt_list_le_of (l := aH) (A := A) fun v hv => hH v (mem_of_mem_tmAbsH hv)
  have l1 := (length_le_tmAbsN (4 * q ^ 2) j aN u).trans lN
  have l2 := (length_le_tmAbsH (4 * q ^ 2) j aH u).trans lH
  have m1 : aN.length * (2 * A + 1) ≤ 4 * q ^ 2 * (2 * A + 1) := Nat.mul_le_mul_right _ l1
  have m2 : aH.length * (2 * A + 1) ≤ q ^ 2 * (2 * A + 1) := Nat.mul_le_mul_right _ l2
  have wk := wt_list4_le ctx (.nat j) (.list aN) (.list aH)
  have wj := wt_nat_le j
  have w2 := wt_list2_le (tmKst ctx j aN aH) u
  have e1 : (tmKst ctx j aN aH).wt = (Val.list [ctx, .nat j, .list aN, .list aH]).wt := rfl
  have e2 : 100 * (q + 1) ^ 2 * (A + 1) = 100 * (q ^ 2 * A) + 100 * q ^ 2 + 200 * (q * A) +
      200 * q + 100 * A + 100 := by ring
  have e3 : 4 * q ^ 2 * (2 * A + 1) = 8 * (q ^ 2 * A) + 4 * q ^ 2 := by ring
  have e4 : q ^ 2 * (2 * A + 1) = 2 * (q ^ 2 * A) + q ^ 2 := by ring
  unfold tmStW
  omega

/-! ### The representation of the script -/

section Rep

variable {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) {S : State Ω C} {L : GiantLabels S}
  (I : RowTerminal P₀ S L) {m : ℕ} (eB : I.B ≃ Fin m) (E : Fin m × Fin L.q ≃ S.dom)
  (hsN hsH : List (Perm (Fin m)))

/-- The context of the calls. -/
def tmCtxOf : Val :=
  tmCtx (colVal e c S.x) (colVal e c S.y) (coordsVal e S E) (encGroup hsN) (encGroup hsH) m L.q

/-- The value of the call on rows `a`, `b` under the group at entry `sel` of the context. -/
noncomputable def tmAskVal (sel a b : ℕ) : Val :=
  if h : a < 2 * L.q ∧ b < 2 * L.q then
    tmRowVal (if sel = 3 then hsN else hsH) c (tmRowStr S E (tmRowAt L.q a h.1))
      (tmRowStr S E (tmRowAt L.q b h.2))
  else .nat 0

/-- **The program state `st` stands for the script `s`.** -/
def tmRep (st : Val) (s : Script (Set (Perm Ω))) : Prop :=
  ∃ (j : ℕ) (aN aH : List Val) (u : Val),
    st = .list [tmKst (tmCtxOf e c E hsN hsH) j aN aH, u] ∧ j ≤ 5 * L.q ^ 2 ∧
    List.Forall₂ (fun v ac => AnsC eB v (I.typeCall ac).answer)
      (tmAbsN (4 * L.q ^ 2) j aN u) ((tmTests L.q).take j) ∧
    List.Forall₂ (fun v ij => AnsC eB v (I.cosetCall ij).answer)
      (tmAbsH (4 * L.q ^ 2) j aH u) ((tmCosets L.q).take (j - 4 * L.q ^ 2)) ∧
    u.wt ≤ ansW m ∧ s = tmScr I j

/-- **What the script phase returns**: the answer of the state, and the canonical answers of
the calls in the program's order. -/
def tmOut (a : Set (Perm Ω)) (out : Val) : Prop :=
  a = S.answer ∧ ∃ us vs : List Val, out = .list [.list us, .list vs] ∧
    List.Forall₂ (fun v ac => AnsC eB v (I.typeCall ac).answer) us
      (tmTests L.q) ∧
    List.Forall₂ (fun v ij => AnsC eB v (I.cosetCall ij).answer) vs
      (tmCosets L.q)

/-- The start: no answers yet. -/
theorem tmRep_start (hq : 0 < L.q) :
    tmRep e c I eB E hsN hsH (.list [tmKst (tmCtxOf e c E hsN hsH) 0 [] [], .list []])
      (tmWithOrder I).script := by
  refine ⟨0, [], [], .list [], rfl, Nat.zero_le _, ?_, ?_, by simp [ansW], tmScr_zero I hq⟩
  · simp [tmAbsN]
  · simp [tmAbsH]

/-! ### The step function meets `StepOK` -/

theorem tmRowAt_lt (q a : ℕ) (h : a < 2 * q) (ha : a < q) : tmRowAt q a h = .inl ⟨a, ha⟩ := by
  simp [tmRowAt, ha]

theorem tmRowAt_add (q b : ℕ) (h : q + b < 2 * q) :
    tmRowAt q (q + b) h = .inr ⟨b, by omega⟩ := by
  simp [tmRowAt]

theorem tm_getElem_of_getElem? {α : Type} {l : List α} {j : ℕ} {x : α} (hj : j < l.length)
    (h : l[j]? = some x) : l[j] = x := by
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem tm_forall₂_wt {α : Type} {R : Val → α → Prop} {A : ℕ} {l₁ : List Val} {l₂ : List α}
    (h : List.Forall₂ R l₁ l₂) (hR : ∀ v a, R v a → v.wt ≤ A) : ∀ v ∈ l₁, v.wt ≤ A := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hR _ _ hab
    · exact ih v hv

/-- Where the functions of the script phase are. -/
structure TmAt (Pg : Program) (stp ak rw vf ga d ap : ℕ) : Prop where
  step : Pg.funs[stp]? = some (tmStepBody ak)
  ask : Pg.funs[ak]? = some (tmAskBody rw vf)
  row : Pg.funs[rw]? = some (tmRowBody ga)
  gather : Pg.HasAt ga (gatherFuns ga)
  val : Pg.funs[vf]? = some (tmValBody ap (d + 9))
  dom : DomAt Pg d
  append : Pg.HasAt ap (appendFuns ap)

/-- The cost bound of one step. -/
def tmStepB (Wc q A : ℕ) : ℕ := 40 * (tmAskK * (Wc + 1) ^ 6) + 10 ^ 5 * (tmStW Wc q A + 1) ^ 2

theorem tm_q_le_ctx : L.q ≤ (tmCtxOf e c E hsN hsH).wt := by
  have h1 : (coordsVal e S E).wt < (tmCtxOf e c E hsN hsH).wt := wt_le_wt_list (by simp)
  have h2 := length_lt_wt_list ((List.finRange L.q).map fun j =>
    natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))
  simp only [List.length_map, List.length_finRange] at h2
  have e1 : (coordsVal e S E).wt = (Val.list ((List.finRange L.q).map fun j =>
    natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))).wt := rfl
  omega

theorem tm_ask_eq (sel a b : ℕ) (ha : a < 2 * L.q)
    (hb : b < 2 * L.q) :
    tmAskVal c E hsN hsH sel a b = tmRowVal (if sel = 3 then hsN else hsH) c
      (tmRowStr S E (tmRowAt L.q a ha)) (tmRowStr S E (tmRowAt L.q b hb)) := by
  unfold tmAskVal
  rw [dif_pos ⟨ha, hb⟩]

/-- **The step function of the terminal meets `StepOK`.** The hypotheses `hTN`, `hTH` say that
the value of each call is canonical for the call of the terminal data, and that the call is
below `μ`. -/
theorem tm_stepOK {Pg : Program} {stp ak rw vf ga d ap : ℕ} (hP : TmAt Pg stp ak rw vf ga d ap)
    (hcol : ∀ x, c (S.x x) < 2 * k ∧ c (S.y x) < 2 * k) (hq : 0 < L.q)
    {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ}
    (hTN : ∀ (a b : ℕ) (ha : a < 2 * L.q) (hb : b < 2 * L.q), ∃ c' : C → ℕ,
      Function.Injective c' ∧ Canon eB c' (tmRowVal hsN c (tmRowStr S E (tmRowAt L.q a ha))
        (tmRowStr S E (tmRowAt L.q b hb))) (I.typeCall (tmRowAt L.q a ha, tmRowAt L.q b hb)) ∧
      MLt (measure P₀ .solve (I.typeCall (tmRowAt L.q a ha, tmRowAt L.q b hb))) μ)
    (hTH : ∀ (i j : Fin L.q), ∃ c' : C → ℕ,
      Function.Injective c' ∧ Canon eB c' (tmRowVal hsH c (tmRowStr S E (.inl i))
        (tmRowStr S E (.inr j))) (I.cosetCall (i, j)) ∧
      MLt (measure P₀ .solve (I.cosetCall (i, j))) μ) :
    Iface.StepOK Pg stp μ (tmOut I eB) (tmRep e c I eB E hsN hsH)
      (tmStepB (tmCtxOf e c E hsN hsH).wt L.q (ansW m)) := by
  set ctx := tmCtxOf e c E hsN hsH with hctx
  set Wc := ctx.wt
  have hqW : L.q ≤ Wc := tm_q_le_ctx e c E hsN hsH
  -- the weight of a program state
  have hwt : ∀ st s, tmRep e c I eB E hsN hsH st s → st.wt ≤ tmStW Wc L.q (ansW m) := by
    rintro st s ⟨j, aN, aH, u, rfl, hj, hN, hH, hu, -⟩
    refine wt_tmSt_le hj (tm_forall₂_wt hN fun v _ h => h.wt_le)
      (tm_forall₂_wt hH fun v _ h => h.wt_le) ?_ ?_ hu
    · rw [hN.length_eq, List.length_take, length_tmTests]; omega
    · rw [hH.length_eq, List.length_take, length_tmCosets]; omega
  set X := tmStW Wc L.q (ansW m)
  set Ca := tmAskK * (Wc + 1) ^ 6
  set cl : List Val := [colVal e c S.x, colVal e c S.y, coordsVal e S E, encGroup hsN,
    encGroup hsH, tmOnes m, .nat m, .nat L.q]
  have hcl : ctx = .list cl := rfl
  have hmW : m < Wc := by
    have h1 : (tmOnes m).wt < Wc := wt_le_wt_list (by simp)
    have := length_lt_wt_list (List.replicate m (Val.nat 1))
    simp only [List.length_replicate] at this
    have : (Val.list (List.replicate m (Val.nat 1))).wt = (tmOnes m).wt := rfl
    omega
  have hask : ∀ sel a b, (sel = 3 ∨ sel = 4) → a < 2 * L.q → b < 2 * L.q →
      FunDet Pg ak (.list [.list cl, .nat sel, .nat a, .nat b]) (tmAskVal c E hsN hsH sel a b) Ca := by
    intro sel a b hs ha hb
    rw [tm_ask_eq c E hsN hsH sel a b ha hb]
    refine tmAsk_spec hP.ask hP.row hP.gather hP.val hP.dom hP.append e c S E (encGroup hsN)
      (encGroup hsH) hcol sel _ ?_ (by omega) a b ha hb
    rcases hs with rfl | rfl <;> rfl
  have haskw : ∀ sel a b, (sel = 3 ∨ sel = 4) → a < 2 * L.q → b < 2 * L.q →
      (tmAskVal c E hsN hsH sel a b).wt ≤ Ca := by
    intro sel a b hs ha hb
    rw [tm_ask_eq c E hsN hsH sel a b ha hb]
    refine (wt_tmRowVal_le _ c _ _).trans ?_
    have hg : (encGroup (if sel = 3 then hsN else hsH)).wt < Wc := by
      split_ifs
      · exact wt_le_wt_list (by simp)
      · exact wt_le_wt_list (by simp)
    have h1 : (m + 1) ^ 2 ≤ (Wc + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
    have h2 : Wc + 1 ≤ (Wc + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    have h3 : (Wc + 1) ^ 2 ≤ (Wc + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [Ca, tmAskK]
    omega
  refine ⟨fun st s hst => ?_, fun st s hst => ?_⟩
  swap
  · have h1 : st.wt ≤ X := hwt st s hst
    have h2 : X ≤ (X + 1) ^ 2 := by nlinarith
    have h3 : tmStepB Wc L.q (ansW m) = 40 * Ca + 10 ^ 5 * (X + 1) ^ 2 := rfl
    omega
  have hX := hwt st s hst
  obtain ⟨j, aN, aH, u, rfl, hj, hN, hH, hu, rfl⟩ := hst
  have hdet := tmStep_det hP.step (tmAskVal c E hsN hsH) cl (q := L.q) rfl hq hask haskw j hj aN aH u
    hX (by unfold X tmStW; omega)
  refine FunAll.mono hdet fun w cw ⟨hw, hcw⟩ => ⟨hcw, ?_⟩
  subst hw
  set T4 := 4 * L.q ^ 2 with hT4
  by_cases h1 : j < T4
  · -- an `N`-test
    obtain ⟨ha, hb⟩ := tm_idx_test hq h1
    obtain ⟨h1', h2', hget⟩ := tmTests_getElem? L.q j h1
    have hlj : j < (tmTests L.q).length := by rw [length_tmTests]; exact h1
    have hac := tm_getElem_of_getElem? hlj hget
    obtain ⟨kk, hs, hk⟩ := tmScr_test I j h1
    rw [hs]
    rw [hac] at hk ⊢
    obtain ⟨c', hc', hcan, hlt⟩ := hTN _ _ h1' h2'
    have hv : tmStepOut (tmAskVal c E hsN hsH) (.list cl) L.q j aN aH u =
        .list [.nat 1, .nat (modeCode .solve), tmAskVal c E hsN hsH 3 (j / (2 * L.q)) (j % (2 * L.q)),
          tmKst (.list cl) (j + 1) (tmAbsN T4 j aN u) (tmAbsH T4 j aH u)] := by
      simp only [tmStepOut, ← hT4, if_pos h1]; rfl
    rw [hv]
    refine ⟨m, eB, c', _, _, hc', Or.inl rfl, rfl, ?_, trivial, hlt, fun u' hu' => ?_⟩
    · rw [tm_ask_eq c E hsN hsH 3 _ _ h1' h2', if_pos rfl]
      exact hcan
    · rw [hk]
      refine ⟨j + 1, _, _, u', rfl, by omega, ?_, ?_, hu'.wt_le, rfl⟩
      · have e1 : tmAbsN T4 (j + 1) (tmAbsN T4 j aN u) u' = tmAbsN T4 j aN u ++ [u'] := by
          simp [tmAbsN]; omega
        rw [e1, tm_take_succ _ j hlj, hac]
        exact List.rel_append hN (List.Forall₂.cons hu' List.Forall₂.nil)
      · have e1 : tmAbsH T4 (j + 1) (tmAbsH T4 j aH u) u' = tmAbsH T4 j aH u := by
          simp [tmAbsH]; omega
        rw [e1, show j + 1 - 4 * L.q ^ 2 = j - 4 * L.q ^ 2 by omega]
        exact hH
  by_cases h2 : j < 5 * L.q ^ 2
  · -- a coset call
    have h2' : j - T4 < L.q ^ 2 := by omega
    obtain ⟨ha, hb⟩ := tm_idx_coset hq h2
    obtain ⟨i1, i2, hget⟩ := tmCosets_getElem? L.q (j - T4) h2'
    have hlj : j - T4 < (tmCosets L.q).length := by rw [length_tmCosets]; exact h2'
    have hij := tm_getElem_of_getElem? hlj hget
    obtain ⟨kk, hs, hk⟩ := tmScr_coset I j (by omega) h2
    rw [hs]
    rw [hij] at hk ⊢
    obtain ⟨c', hc', hcan, hlt⟩ := hTH ⟨(j - T4) / L.q, i1⟩ ⟨(j - T4) % L.q, i2⟩
    have hv : tmStepOut (tmAskVal c E hsN hsH) (.list cl) L.q j aN aH u =
        .list [.nat 1, .nat (modeCode .solve),
          tmAskVal c E hsN hsH 4 ((j - T4) / L.q) (L.q + (j - T4) % L.q),
          tmKst (.list cl) (j + 1) (tmAbsN T4 j aN u) (tmAbsH T4 j aH u)] := by
      simp only [tmStepOut, ← hT4, if_neg h1, if_pos h2]; rfl
    rw [hv]
    refine ⟨m, eB, c', _, _, hc', Or.inl rfl, rfl, ?_, trivial, hlt, fun u' hu' => ?_⟩
    · rw [tm_ask_eq c E hsN hsH 4 _ _ ha hb, if_neg (by omega), tmRowAt_lt _ _ ha i1,
        tmRowAt_add _ _ hb]
      exact hcan
    · rw [hk]
      refine ⟨j + 1, _, _, u', rfl, by omega, ?_, ?_, hu'.wt_le, rfl⟩
      · have e1 : tmAbsN T4 (j + 1) (tmAbsN T4 j aN u) u' = tmAbsN T4 j aN u := by
          simp [tmAbsN]; omega
        have e2 : (tmTests L.q).take (j + 1) = (tmTests L.q).take j := by
          rw [List.take_of_length_le (by rw [length_tmTests]; omega),
            List.take_of_length_le (by rw [length_tmTests]; omega)]
        rw [e1, e2]
        exact hN
      · have e1 : tmAbsH T4 (j + 1) (tmAbsH T4 j aH u) u' = tmAbsH T4 j aH u ++ [u'] := by
          simp [tmAbsH]; omega
        rw [e1, show j + 1 - 4 * L.q ^ 2 = j - T4 + 1 by omega, tm_take_succ _ _ hlj, hij]
        exact List.rel_append hH (List.Forall₂.cons hu' List.Forall₂.nil)
  · -- the end
    have hj5 : j = 5 * L.q ^ 2 := by omega
    subst hj5
    rw [tmScr_done]
    have hv : tmStepOut (tmAskVal c E hsN hsH) (.list cl) L.q (5 * L.q ^ 2) aN aH u =
        .list [.nat 0, .list [.list (tmAbsN T4 (5 * L.q ^ 2) aN u),
          .list (tmAbsH T4 (5 * L.q ^ 2) aH u)]] := by
      simp only [tmStepOut, ← hT4, if_neg h1, if_neg h2]
    rw [hv]
    refine ⟨_, rfl, rfl, _, _, rfl, ?_, ?_⟩
    · rw [List.take_of_length_le (by rw [length_tmTests]; omega)] at hN
      exact hN
    · rw [List.take_of_length_le (by rw [length_tmCosets]; omega)] at hH
      exact hH

end Rep

end GI.Impl
