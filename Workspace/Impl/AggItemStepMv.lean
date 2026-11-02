import Workspace.Impl.AggItemStepProg

/-!
# The moves of the step function of the items keep the relation

At a context `K` with a case contract `ItSCaseAt` (relations `R`, bound `B`), every move of the
step function (`itSMvF`) on a state of `itSRep` either returns what one step of the script must
return (`StepPostC`), or a new state of `itSRep` of smaller measure for fewer candidates.

* `itS_rep_wt`, `itS_rep_m`: the states have weight at most `itSBw V T n B` and measure at most
  `3 N + 3`, with at most `N` branches, `V` a bound of `K.v` and `T` a bound of the branch tuples.
* `itS_move`: the move lemma, in the form that `stepOKC_of_move` asks.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)

variable {Ω C : Type} {k : ℕ}

/-- The weight bound of the accumulated lists after at most `n` branches. -/
def itSAccB (n B : ℕ) : ℕ := 4 * (n * B * (2 * B + 1) + 4) + 6

/-- The weight bound of the states of the step function. -/
def itSBw (V T n B : ℕ) : ℕ := 4 * (V + T + n + itSAccB n B + B) + 2 * B + 60

/-- The cost bound of the dispatched branch step. -/
def itSCd (B : ℕ) : ℕ := 4 * B + itSDispC (2 * B + 20)

/-- The cost bound of one move on states of weight at most `W`. -/
def itSBm (W B : ℕ) : ℕ := 7 * (itSM1C W (itSCd B) + itSM3C W) + itSMvC W

/-- **The programs of the step function**, at their indices. -/
structure ItSProgAt (Pg : Program) (mv m0 m1 m3 disp fac app : ℕ) : Prop where
  mv : Pg.funs[mv]? = some (itSMvF m0 m1 m3)
  m0 : Pg.funs[m0]? = some itSM0F
  m1 : Pg.funs[m1]? = some (itSM1F disp fac)
  m3 : Pg.funs[m3]? = some itSM3F
  fac : Pg.funs[fac]? = some (itSFacF app)
  app : Pg.HasAt app (appendFuns app)

/-- The accumulated lists weigh at most `itSAccB n B`. -/
theorem itS_acc_wt {q B j n : ℕ} {pcs : List (Perm (Fin k) × Acc k)} {os : List (LcOver q)}
    (h : ItSAcc B j pcs os) (hj : j ≤ n) : (itSOutV pcs os).wt ≤ itSAccB n B := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have w1 := wt_list_le_of _ h1
  have w2 := wt_list_le_of _ h2
  rw [List.length_map] at w1 w2
  have l1 : pcs.length * (2 * B + 1) ≤ n * B * (2 * B + 1) :=
    Nat.mul_le_mul_right _ (h3.trans (Nat.mul_le_mul_right _ hj))
  have l2 : os.length * (2 * B + 1) ≤ n * B * (2 * B + 1) :=
    Nat.mul_le_mul_right _ (h4.trans (Nat.mul_le_mul_right _ hj))
  have := wt_list2_le (.list (pcs.map encPiece))
    (.list (os.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2))
  have e : (itSOutV pcs os).wt = (Val.list [.list (pcs.map encPiece),
    .list (os.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2)]).wt := rfl
  unfold itSAccB
  omega

/-- The weight of a state `[H, u]`. -/
theorem itS_state_wt {q : ℕ} {tag j n V T B : ℕ} {G x u : Val}
    {pcs : List (Perm (Fin k) × Acc k)} {os : List (LcOver q)} (htag : tag ≤ 3) (hj : j ≤ n)
    (hG : G.wt ≤ V) (hT : (itSTv q).wt ≤ T) (ha : (itSOutV pcs os).wt ≤ itSAccB n B)
    (hx : x.wt ≤ B) (hu : u.wt ≤ B + 2) :
    (Val.list [itSH tag G j pcs os x, u]).wt ≤ itSBw V T n B := by
  have h6 := wt_list6_le (.nat tag) G (itSTv q) (.nat j) (itSOutV pcs os) x
  have e : (itSH tag G j pcs os x).wt =
    (Val.list [.nat tag, G, itSTv q, .nat j, itSOutV pcs os, x]).wt := rfl
  have h2 := wt_list2_le (itSH tag G j pcs os x) u
  have := wt_nat_le tag
  have := wt_nat_le j
  unfold itSBw
  omega

section Rep

variable {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S} {Pg : Program}
  {R : ItSCaseRel} {fi0 fb0 : ℕ} {K : ItSCtx k S L} {B : ℕ}

/-- **The states of the step function are small.** -/
theorem itS_rep_wt (hA : ItSCaseAt Pg R fi0 fb0 e c S L K B) {V T N : ℕ} (hV : K.v.wt ≤ V)
    (hT : (itSTv L.q).wt ≤ T) (hN : (itSTups L.q).length ≤ N) {m : ℕ} {st : Val} {Ss : Set (Script (Branches Ω))} {f : ℕ}
    (h : itSRep R e c S L K B m st Ss f) :
    st.wt ≤ itSBw V T N B := by
  rcases h with ⟨j, rs, pcs, os, w, D, rfl, hj, hK, -, -, -, hacc, -, -⟩ |
    ⟨j, b, rs, pcs, os, bst, D, sb, fb, rfl, hb, hR, -, -, -, hacc, -, -⟩ |
    ⟨j, b, rs, pcs, os, kst, u, D, sb, fb, rfl, hb, hR, -, -, -, hacc, -, -⟩
  · have := wt_nat_le 0
    exact itS_state_wt (by omega) (hj.trans hN) hV hT (itS_acc_wt hacc (hj.trans hN))
      (hA.wtK w D hK) (by omega)
  · have hj : j < (itSTups L.q).length := (List.getElem?_eq_some_iff.1 hb).1
    have := wt_nat_le 0
    exact itS_state_wt (by omega) (by omega) hV hT (itS_acc_wt hacc (by omega))
      (hA.wtR b bst D sb fb hR) (by omega)
  · have hj : j < (itSTups L.q).length := (List.getElem?_eq_some_iff.1 hb).1
    have hw := hA.wtR b _ D sb fb hR
    have hk : kst.wt < (Val.list [kst, u]).wt := wt_le_wt_list (by simp)
    have hu : u.wt < (Val.list [kst, u]).wt := wt_le_wt_list (by simp)
    exact itS_state_wt (by omega) (by omega) hV hT (itS_acc_wt hacc (by omega)) (by omega)
      (by omega)

/-- **The measure of a state** is at most `3 n + 3`. -/
theorem itS_rep_m {N m : ℕ} {st : Val} {Ss : Set (Script (Branches Ω))} {f : ℕ}
    (hN : (itSTups L.q).length ≤ N) (h : itSRep R e c S L K B m st Ss f) : m ≤ 3 * N + 3 := by
  rcases h with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ <;> omega

/-- **What a move must return** from a state of measure `m` for the candidates `Ss`: as in
`stepOKC_of_move`, with the cost bound `Bm`. -/
def ItSMvPost (R : ItSCaseRel) (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (L : SuppliedLabels S)
    (K : ItSCtx k S L) (B Bm m : ℕ) (Ss : Set (Script (Branches Ω))) (f : ℕ) (w : Val)
    (cost : ℕ) : Prop :=
  cost ≤ Bm ∧ (Iface.StepPostC (measure P₀ .giant S) (ItSFin e L.toGiantLabels)
      (fun st Ss f => ∃ m, itSRep R e c S L K B m st Ss f) Ss f w ∨
    ∃ m' st' Ss', m' < m ∧ Ss' ⊆ Ss ∧ itSRep R e c S L K B m' st' Ss' f ∧
      w = .list [.nat 2, st'])

theorem itS_m3C_mono {W W' : ℕ} (h : W ≤ W') : itSM3C W ≤ itSM3C W' := by
  unfold itSM3C; omega

theorem itS_mvC_mono {W W' : ℕ} (h : W ≤ W') : itSMvC W ≤ itSMvC W' := by
  unfold itSMvC; omega

theorem itS_m1C_mono {W W' Cd : ℕ} (h : W ≤ W') : itSM1C W Cd ≤ itSM1C W' Cd := by
  unfold itSM1C itSFacC
  have : (2 * (W + Cd) + 6 + 1) ^ 2 ≤ (2 * (W' + Cd) + 6 + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have := Nat.mul_le_mul_left (10 ^ 6) this
  omega

variable {mv m0 m1 m3 disp fac app : ℕ}
variable (hP : ItSProgAt Pg mv m0 m1 m3 disp fac app) (hA : ItSCaseAt Pg R fi0 fb0 e c S L K B)
  {V T N : ℕ} (hV : K.v.wt ≤ V) (hT : (itSTv L.q).wt ≤ T) (hN : (itSTups L.q).length ≤ N)
include hP hA hV hT hN

/-- **The move between branches.** -/
theorem itS_move0 {j : ℕ} {rs : List (Branches Ω)} {pcs : List (Perm (Fin k) × Acc k)}
    {os : List (LcOver L.q)} {w : Val} {D : Set (Aggregation P₀ S L.toGiantLabels)}
    {Ss : Set (Script (Branches Ω))} {f : ℕ} (hj : j ≤ (itSTups L.q).length)
    (hK : R.Kc e c S L K w D) (hD : D ⊆ itSBase K)
    (hSs : Ss = (fun Ag => itSW Ag rs ((itSTups L.q).drop j)) '' D)
    (hout : ItSOut e L.toGiantLabels (Branches.concat rs) pcs os) (hacc : ItSAcc B j pcs os)
    (hf : ((itSTups L.q).length - j) * B ≤ f) :
    FunAll Pg mv (.list [itSH 0 K.v j pcs os w, .nat 0])
      (fun w' cost => ItSMvPost R e c S L K B (itSBm (itSBw V T N B) B)
        (3 * ((itSTups L.q).length - j) + 1) Ss f w' cost) := by
  have hst := itS_state_wt (tag := 0) (B := B) (u := .nat 0) (by omega) (hj.trans hN) hV hT
    (itS_acc_wt hacc (hj.trans hN))
    (hA.wtK w D hK) (by have := wt_nat_le 0; omega)
  set Bw := itSBw V T N B with hBw
  have hH : (itSH 0 K.v j pcs os w).wt < (Val.list [itSH 0 K.v j pcs os w, .nat 0]).wt :=
    wt_le_wt_list (by simp)
  have eH : itSH 0 K.v j pcs os w = .list (.nat 0 :: [K.v, itSTv L.q, .nat j, itSOutV pcs os, w]) :=
    rfl
  have hcost : ∀ (c c' : ℕ) (w' : Val), c' ≤ itSM3C (itSH 0 K.v j pcs os w).wt → w'.wt < c' →
      c ≤ c' + itSMvC (Val.list [itSH 0 K.v j pcs os w, .nat 0]).wt + 6 * w'.wt →
      c ≤ itSBm Bw B := by
    intro c c' w' h1 h2 h3
    have := itS_m3C_mono (show (itSH 0 K.v j pcs os w).wt ≤ Bw by omega)
    have := itS_mvC_mono hst
    unfold itSBm
    omega
  rcases Nat.lt_or_ge j (itSTups L.q).length with hjn | hjn
  · -- a tuple is left: start its branch
    obtain ⟨b, hb, hbj⟩ : ∃ b, (itSTups L.q)[j]? = some b ∧ (itSTups L.q)[j] = b :=
      ⟨_, List.getElem?_eq_getElem hjn, rfl⟩
    have h0 := FunAll.wt_lt (itS_m0_next hP.m0 K.v j pcs os w hb)
    rw [eH] at h0 hcost ⊢
    refine FunAll.mono (itS_mv_spec0 hP.mv _ (.nat 0) h0) fun w' cost h => ?_
    obtain ⟨c', ⟨⟨rfl, hc'⟩, hwc⟩, hc⟩ := h
    refine ⟨hcost _ _ _ hc' hwc hc, Or.inr ⟨_, _, _, ?_, ?_, Or.inr (Or.inl ⟨j, b, rs, pcs, os, _, D,
        fun Ag => (Ag.items b).script, B, rfl, hb, hA.start b w D hK, hD, rfl, hout, hacc, ?_,
        rfl⟩), rfl⟩⟩
    · omega
    · rw [hSs]
      rintro _ ⟨Ag, hAg, rfl⟩
      refine ⟨Ag, hAg, ?_⟩
      show itSW Ag rs ((itSTups L.q).drop j) = _
      rw [List.drop_eq_getElem_cons hjn, itSW_cons, hbj]
    · have : (itSTups L.q).length - j = ((itSTups L.q).length - (j + 1)) + 1 := by omega
      rw [this, Nat.add_mul, one_mul] at hf
      omega
  · -- no tuple is left: return the output
    have h0 := FunAll.wt_lt (itS_m0_end hP.m0 K.v j pcs os w hjn)
    rw [eH] at h0 hcost ⊢
    obtain ⟨Ag, hAg⟩ := hA.ne w D hK
    refine FunAll.mono (itS_mv_spec0 hP.mv _ (.nat 0) h0) fun w' cost h => ?_
    obtain ⟨c', ⟨⟨rfl, hc'⟩, hwc⟩, hc⟩ := h
    refine ⟨hcost _ _ _ hc' hwc hc, Or.inl (Or.inl ⟨Branches.concat rs, _, rfl, ⟨pcs, os, rfl, hout⟩,
        ?_⟩)⟩
    rw [hSs]
    refine ⟨Ag, hAg, ?_⟩
    show itSW Ag rs ((itSTups L.q).drop j) = _
    rw [List.drop_eq_nil_of_le hjn, itSW_nil]

/-- **The move after a call.** -/
theorem itS_move3 {j : ℕ} {b : Fin (P₀.κ + 1) → Fin L.q} {rs : List (Branches Ω)}
    {pcs : List (Perm (Fin k) × Acc k)} {os : List (LcOver L.q)} {kst u : Val}
    {D : Set (Aggregation P₀ S L.toGiantLabels)}
    {sb : Aggregation P₀ S L.toGiantLabels → Script (Branches Ω)} {fb : ℕ}
    {Ss : Set (Script (Branches Ω))} {f : ℕ} (hb : (itSTups L.q)[j]? = some b)
    (hR : R.Rb e c S L K b (.list [kst, u]) D sb fb) (hD : D ⊆ itSBase K)
    (hSs : Ss = (fun Ag => (sb Ag).bind fun r => itSW Ag (rs ++ [r]) ((itSTups L.q).drop (j + 1))) '' D)
    (hout : ItSOut e L.toGiantLabels (Branches.concat rs) pcs os) (hacc : ItSAcc B j pcs os)
    (hf : fb + ((itSTups L.q).length - (j + 1)) * B ≤ f) :
    FunAll Pg mv (.list [itSH 3 K.v (j + 1) pcs os kst, u])
      (fun w' cost => ItSMvPost R e c S L K B (itSBm (itSBw V T N B) B)
        (3 * ((itSTups L.q).length - (j + 1)) + 3) Ss f w' cost) := by
  have hjn : j < (itSTups L.q).length := (List.getElem?_eq_some_iff.1 hb).1
  have hst := itS_rep_wt hA hV hT hN (Or.inr (Or.inr ⟨j, b, rs, pcs, os, kst, u, D, sb, fb, rfl, hb, hR,
    hD, hSs, hout, hacc, hf, rfl⟩))
  set Bw := itSBw V T N B with hBw
  have h0 := FunAll.wt_lt (itS_m3_spec hP.m3 K.v (j + 1) pcs os kst u)
  have eH : itSH 3 K.v (j + 1) pcs os kst =
      .list (.nat 3 :: [K.v, itSTv L.q, .nat (j + 1), itSOutV pcs os, kst]) := rfl
  rw [eH] at h0 hst ⊢
  refine FunAll.mono (itS_mv_spec3 hP.mv _ u h0) fun w' cost h => ?_
  obtain ⟨c', ⟨⟨rfl, hc'⟩, hwc⟩, hc⟩ := h
  refine ⟨?_, Or.inr ⟨_, _, _, ?_, subset_rfl, Or.inr (Or.inl ⟨j, b, rs, pcs, os, _, D, sb, fb, rfl, hb,
    hR, hD, hSs, hout, hacc, hf, rfl⟩), rfl⟩⟩
  · have := itS_m3C_mono hst
    have := itS_mvC_mono hst
    unfold itSBm
    omega
  · omega

/-- The dispatched branch step, in the form of `itS_m1_spec`. -/
theorem itS_disp_br {b : Fin (P₀.κ + 1) → Fin L.q} {bst : Val}
    {D : Set (Aggregation P₀ S L.toGiantLabels)}
    {sb : Aggregation P₀ S L.toGiantLabels → Script (Branches Ω)} {fb : ℕ}
    (hdisp : ∀ bst Q, FunAll Pg fb0 bst Q → FunAll Pg disp (.list [.nat (AggCase.code K.case), bst])
      (fun w cst => ∃ c', Q w c' ∧
        cst ≤ c' + itSDispC (Val.list [.nat (AggCase.code K.case), bst]).wt + 3 * w.wt))
    (hR : R.Rb e c S L K b bst D sb fb) :
    FunAll Pg disp (.list [.nat (AggCase.code K.case), bst]) (fun w cst => cst ≤ itSCd B ∧
      ((∃ (pcs' : List (Perm (Fin k) × Acc k)) (os' : List (LcOver L.q)) (w' : Val),
          w = .list [.nat 0, .list [.list (pcs'.map encPiece),
            .list (os'.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2), w']] ∧
          ∃ (r : Branches Ω) (D' : Set (Aggregation P₀ S L.toGiantLabels)), D' ⊆ D ∧
            (∀ Ag ∈ D', sb Ag = .done r) ∧ R.Kc e c S L K w' D' ∧
            ItSOut e L.toGiantLabels r pcs' os' ∧ (itSOutV pcs' os').wt ≤ B) ∨
        (∃ cm arg kst, w = .list [.nat 1, cm, arg, kst] ∧ 0 < fb ∧
          ∃ (m : Mode) (Ω' C' : Type) (T : State Ω' C') (k' : ℕ) (e' : Ω' ≃ Fin k')
            (c' : C' → ℕ) (D' : Set (Aggregation P₀ S L.toGiantLabels))
            (kk : Aggregation P₀ S L.toGiantLabels → Set (Perm Ω') → Script (Branches Ω)),
            cm = .nat (modeCode m) ∧ D' ⊆ D ∧ D'.Nonempty ∧ Function.Injective c' ∧
            (m = .solve ∨ m = .cont) ∧ Canon e' c' arg T ∧ Good P₀ m T ∧
            MLt (measure P₀ m T) (measure P₀ .giant S) ∧ (∀ Ag ∈ D', sb Ag = .ask m T (kk Ag)) ∧
            ∀ u, AnsC e' u T.answer →
              R.Rb e c S L K b (.list [kst, u]) D' (fun Ag => kk Ag T.answer) (fb - 1)))) := by
  have hbw := hA.wtR b bst D sb fb hR
  have h2 := wt_list2_le (.nat (AggCase.code K.case)) bst
  have hcode : (Val.nat (AggCase.code K.case)).wt ≤ 5 :=
    (wt_nat_le _).trans (by have := it_code_le K.case; omega)
  refine FunAll.mono (hdisp bst _ (FunAll.wt_lt (hA.step b bst D sb fb hR))) fun w cost h => ?_
  obtain ⟨c', ⟨⟨hc', hp⟩, hwc⟩, hc⟩ := h
  refine ⟨?_, ?_⟩
  · unfold itSCd itSDispC at *
    omega
  rcases hp with ⟨r, pcs', os', w', D', rfl, h1, h2, h3, h4, h5⟩ |
    ⟨hf0, m, Ω', C', T, k', e', c'', arg, kst, D', kk, h1, h2, h3, h4, rfl, h6, h7, h8, h9, h10⟩
  · exact Or.inl ⟨pcs', os', w', rfl, r, D', h1, h2, h3, h4, h5⟩
  · exact Or.inr ⟨_, arg, kst, rfl, hf0, m, Ω', C', T, k', e', c'', D', kk, rfl, h1, h2, h3, h4, h6,
      h7, h8, h9, h10⟩

/-- **The move inside a branch.** -/
theorem itS_move1
    (hdisp : ∀ bst Q, FunAll Pg fb0 bst Q → FunAll Pg disp (.list [.nat (AggCase.code K.case), bst])
      (fun w cst => ∃ c', Q w c' ∧
        cst ≤ c' + itSDispC (Val.list [.nat (AggCase.code K.case), bst]).wt + 3 * w.wt))
    {j : ℕ} {b : Fin (P₀.κ + 1) → Fin L.q} {rs : List (Branches Ω)}
    {pcs : List (Perm (Fin k) × Acc k)} {os : List (LcOver L.q)} {bst : Val}
    {D : Set (Aggregation P₀ S L.toGiantLabels)}
    {sb : Aggregation P₀ S L.toGiantLabels → Script (Branches Ω)} {fb : ℕ}
    {Ss : Set (Script (Branches Ω))} {f : ℕ} (hb : (itSTups L.q)[j]? = some b)
    (hR : R.Rb e c S L K b bst D sb fb) (hD : D ⊆ itSBase K)
    (hSs : Ss = (fun Ag => (sb Ag).bind fun r => itSW Ag (rs ++ [r]) ((itSTups L.q).drop (j + 1))) '' D)
    (hout : ItSOut e L.toGiantLabels (Branches.concat rs) pcs os) (hacc : ItSAcc B j pcs os)
    (hf : fb + ((itSTups L.q).length - (j + 1)) * B ≤ f) :
    FunAll Pg mv (.list [itSH 1 K.v (j + 1) pcs os bst, .nat 0])
      (fun w' cost => ItSMvPost R e c S L K B (itSBm (itSBw V T N B) B)
        (3 * ((itSTups L.q).length - (j + 1)) + 2) Ss f w' cost) := by
  have hjn : j < (itSTups L.q).length := (List.getElem?_eq_some_iff.1 hb).1
  have hst := itS_rep_wt hA hV hT hN (Or.inr (Or.inl ⟨j, b, rs, pcs, os, bst, D, sb, fb, rfl, hb, hR,
    hD, hSs, hout, hacc, hf, rfl⟩))
  set Bw := itSBw V T N B with hBw
  have hH : (itSH 1 K.v (j + 1) pcs os bst).wt < (Val.list [itSH 1 K.v (j + 1) pcs os bst, .nat 0]).wt :=
    wt_le_wt_list (by simp)
  have h1 := FunAll.wt_lt (itS_m1_spec hP.m1 hP.fac hP.app K.st
    (.list [encKColoring K.d, encKColoring K.d']) (natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ)))
    (AggCase.code K.case) (j + 1) pcs os bst (itS_disp_br hP hA hV hT hN hdisp hR))
  have eH : itSH 1 K.v (j + 1) pcs os bst =
      .list (.nat 1 :: [K.v, itSTv L.q, .nat (j + 1), itSOutV pcs os, bst]) := rfl
  have eK : Val.list [K.st, .list [encKColoring K.d, encKColoring K.d'], .nat (AggCase.code K.case),
      natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))] = K.v := rfl
  rw [eK] at h1
  rw [eH] at h1 hst hH ⊢
  refine FunAll.mono (itS_mv_spec1 hP.mv _ (.nat 0) h1) fun w' cost h => ?_
  obtain ⟨c', ⟨⟨hc', hp⟩, hwc⟩, hc⟩ := h
  refine ⟨?_, ?_⟩
  · have := itS_m1C_mono (Cd := itSCd B) (show (Val.list (.nat 1 :: [K.v, itSTv L.q, .nat (j + 1),
      itSOutV pcs os, bst])).wt ≤ Bw by omega)
    have := itS_mvC_mono hst
    unfold itSBm
    omega
  rcases hp with ⟨pcs', os', w', ⟨r, D', hD', hsb, hK', hr, hrB⟩, rfl⟩ |
    ⟨cm, arg, kst, ⟨hf0, m, Ω', C', T', k', e', c'', D', kk, rfl, hD', hne, hinj, hm, hcan, hg,
      hlt, hsb, hrb⟩, rfl⟩
  · -- the branch is finished
    have hacc' : ItSAcc B (j + 1) (pcs ++ pcs') (os ++ os') := by
      obtain ⟨a1, a2, a3, a4⟩ := hacc
      have eo : itSOutV pcs' os' = .list [.list (pcs'.map encPiece),
          .list (os'.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)] := rfl
      have wA : (Val.list (pcs'.map encPiece)).wt < (itSOutV pcs' os').wt := by
        rw [eo]; exact wt_le_wt_list (by simp)
      have wB : (Val.list (os'.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)).wt <
          (itSOutV pcs' os').wt := by
        rw [eo]; exact wt_le_wt_list (by simp)
      have lA := length_lt_wt_list (pcs'.map encPiece)
      have lB := length_lt_wt_list (os'.map fun o => lcOv (o.1 : Perm (Fin L.q)) o.2.2)
      rw [List.length_map] at lA lB
      refine ⟨fun v hv => ?_, fun v hv => ?_, ?_, ?_⟩
      · rw [List.map_append] at hv
        rcases List.mem_append.1 hv with hv | hv
        · exact a1 v hv
        · have := wt_le_wt_list hv; omega
      · rw [List.map_append] at hv
        rcases List.mem_append.1 hv with hv | hv
        · exact a2 v hv
        · have := wt_le_wt_list hv; omega
      · rw [List.length_append, Nat.add_mul, one_mul]; omega
      · rw [List.length_append, Nat.add_mul, one_mul]; omega
    refine Or.inr ⟨_, _, _, ?_, ?_, Or.inl ⟨j + 1, rs ++ [r], pcs ++ pcs', os ++ os', w', D', rfl,
      hjn, hK', hD'.trans hD, rfl, itSOut_append hout hr, hacc', by omega, rfl⟩, rfl⟩
    · omega
    · rw [hSs]
      rintro _ ⟨Ag, hAg, rfl⟩
      refine ⟨Ag, hD' hAg, ?_⟩
      show (sb Ag).bind _ = _
      rw [hsb Ag hAg]
      rfl
  · -- the case asks a call
    refine Or.inl (Or.inr ⟨by omega, m, Ω', C', T', k', e', c'', arg, _,
      (fun Ag A => (kk Ag A).bind fun r => itSW Ag (rs ++ [r]) ((itSTups L.q).drop (j + 1))) '' D',
      hinj, hm, rfl, hcan, hg, hlt, hne.image _, ?_, fun u hu => ⟨_, Or.inr (Or.inr ⟨j, b, rs, pcs, os,
      kst, u, D', fun Ag => kk Ag T'.answer, fb - 1, rfl, hb, hrb u hu, hD'.trans hD, ?_, hout, hacc,
      by omega, rfl⟩)⟩⟩)
    · rintro _ ⟨Ag, hAg, rfl⟩
      rw [hSs]
      refine ⟨Ag, hD' hAg, ?_⟩
      show (sb Ag).bind _ = _
      rw [hsb Ag hAg]
      rfl
    · rw [Set.image_image]

/-- The bound of the step function of the items: `n` branches, `V` bounds `K.v`, `T` bounds the
branch tuples, `B` is the bound of the case. -/
def itSStepB (V T n B : ℕ) : ℕ :=
  (3 * n + 3 + 1) * cpLoopC (itSBm (itSBw V T n B) B) (itSBw V T n B) + itSBw V T n B

/-- **The step function of the items meets `StepOKC`.** -/
theorem itS_stepOKC {d : ℕ} (hd : Pg.funs[d]? = some (cpLoopBody d mv))
    (hdisp : ∀ bst Q, FunAll Pg fb0 bst Q → FunAll Pg disp (.list [.nat (AggCase.code K.case), bst])
      (fun w cst => ∃ c', Q w c' ∧
        cst ≤ c' + itSDispC (Val.list [.nat (AggCase.code K.case), bst]).wt + 3 * w.wt)) :
    Iface.StepOKC Pg d (measure P₀ .giant S) (ItSFin e L.toGiantLabels)
      (fun st Ss f => ∃ m, itSRep R e c S L K B m st Ss f)
      (itSStepB V T N B) := by
  refine stepOKC_of_move hd (fun m st Ss f h => ?_) (fun m st Ss f h => itS_rep_wt hA hV hT hN h)
    (fun m st Ss f h => itS_rep_m hN h)
  rcases h with ⟨j, rs, pcs, os, w, D, rfl, hj, hK, hD, hSs, hout, hacc, hf, rfl⟩ |
    ⟨j, b, rs, pcs, os, bst, D, sb, fb, rfl, hb, hR, hD, hSs, hout, hacc, hf, rfl⟩ |
    ⟨j, b, rs, pcs, os, kst, u, D, sb, fb, rfl, hb, hR, hD, hSs, hout, hacc, hf, rfl⟩
  · exact itS_move0 hP hA hV hT hN hj hK hD hSs hout hacc hf
  · exact itS_move1 hP hA hV hT hN hdisp hb hR hD hSs hout hacc hf
  · exact itS_move3 hP hA hV hT hN hb hR hD hSs hout hacc hf

end Rep

end GI.Impl
