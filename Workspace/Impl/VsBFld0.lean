import Workspace.Impl.VsBFldM
import Workspace.Proved.VsBFld0M

/-!
# The field line when `T = 0`

* `vsBTestE`, `vsB_test_spec`: is `f(g) ≠ 0`?
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The test, on `[ctxB, g]`: `1` if `f(g) ≠ 0`, else `0`. -/
def vsBTestE (act tail eqN : ℕ) : Expr :=
  .arith .sub (.nat 1) (.call eqN (mk2 (.call tail (.call act (mk3 (.get (arg 0) (.nat 0)) (arg 1)
    (.get (arg 0) (.nat 2))))) (.call tail (.get (arg 0) (.nat 2)))))

theorem vsQVec_injective' {p d : ℕ} [NeZero p] :
    Function.Injective (vsQVec : (Fin d → ZMod p) → List ℕ) := fun a b h => by
  rw [← vsWV_vsQVec a, ← vsWV_vsQVec b, h]

set_option maxHeartbeats 4000000 in
theorem vsB_test_spec {P : Program} {f bB eqN phi Cφ S Tm : ℕ}
    (hf : P.funs[f]? = some (vsBTestE (bB + 3) (bB + 4) eqN)) (hB : P.HasAt bB (vsBBFuns bB phi))
    (heq : P.HasAt eqN (eqNatsFuns eqN))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    FunDet P f (.list [vsBCtxB s, encPerm g]) (boolVal (decide (vsBAlpha s g 0 ≠ 0)))
      (Cφ + 10 ^ 17 * S ^ 6) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hact : P.HasAt (bB + 3) (vsBActFuns (bB + 3) phi) := hB.block 3 rfl
  have htl : P.HasAt (bB + 4) (linTailFuns (bB + 4)) := hact.block 1 rfl
  have hS1 := hS.one_le
  set ac := Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x]
  set z0 := natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))
  set F := vsBAlpha s g 0
  have g0 := Det.arg' (P := P) (rest := []) (vs := [vsBCtxB s, encPerm g]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [vsBCtxB s, encPerm g]) (j := 1) rfl
  have dac := Det.get' g0 (Det.nat 0) (show [ac, .nat I.p, z0][0]? = some ac from rfl)
  have dz := Det.get' g0 (Det.nat 2) (show [ac, .nat I.p, z0][2]? = some z0 from rfl)
  have dact := Det.call (Det.mk3 dac g1 dz) (vsB_f_spec hB hphi hS hs hg)
  have dt1 := Det.call dact (linTail_spec htl (.nat 0 :: (vsQVec F).map Val.nat))
  have dt2 := Det.call dz (linTail_spec htl (.nat 0 :: (vsQVec (0 : Fin (vsQD s) → ZMod I.p)).map Val.nat))
  have e1 : Val.list (List.drop 1 (Val.nat 0 :: (vsQVec F).map Val.nat)) = natList (vsQVec F) := rfl
  have e2 : Val.list (List.drop 1 (Val.nat 0 :: (vsQVec (0 : Fin (vsQD s) → ZMod I.p)).map Val.nat)) =
    natList (vsQVec (0 : Fin (vsQD s) → ZMod I.p)) := rfl
  rw [e1] at dt1
  rw [e2] at dt2
  have deq := Det.call (Det.mk2 dt1 dt2) (eqNats_spec heq (vsQVec F) (vsQVec (0 : Fin (vsQD s) → ZMod I.p)))
  have dsub := Det.arith' (op := .sub) (Det.nat 1) deq
    (z := (decide (F ≠ 0)).toNat) (by
      simp only [GI.Machine.BinOp.eval, boolVal]
      by_cases hF : F = 0
      · simp [hF]
      · have : vsQVec F ≠ vsQVec (0 : Fin (vsQD s) → ZMod I.p) := fun h => hF (vsQVec_injective' h)
        simp [hF, this])
  refine FunDet.intro hf (dsub.mono ?_)
  have wc := vsB_wt_ctxB hS hs
  have wac : ac.wt < (vsBCtxB s).wt := wt_le_wt_list (by simp [vsBCtxB, ac])
  have wz : z0.wt < (vsBCtxB s).wt := wt_le_wt_list (by simp [vsBCtxB, z0])
  have wF := vsB_wt_vecA hS hs F
  have w0 := vsB_wt_vecA hS hs (0 : Fin (vsQD s) → ZMod I.p)
  have wg := hS.wt_perm g
  have wa := wt_list2_le (vsBCtxB s) (encPerm g)
  have w3 := wt_list3_le ac (encPerm g) z0
  have w2 := wt_list2_le (natList (vsQVec F)) (natList (vsQVec (0 : Fin (vsQD s) → ZMod I.p)))
  have hlt : ∀ v : Fin (vsQD s) → ZMod I.p,
      linTailCost (Val.list (Val.nat 0 :: (vsQVec v).map Val.nat)).wt ≤ 10 ^ 8 * S ^ 6 := by
    intro v
    unfold linTailCost
    have e : (Val.list (Val.nat 0 :: (vsQVec v).map Val.nat)).wt = (natList (0 :: vsQVec v)).wt := rfl
    rw [e]
    have := (vsB_wt_vecA hS hs v).2
    have h1 : (natList (0 :: vsQVec v)).wt + 1 ≤ 21 * S ^ 2 := by
      have := Nat.one_le_pow 2 S hS1; omega
    have := Nat.pow_le_pow_left h1 3
    have e2 : (21 * S ^ 2) ^ 3 = 9261 * S ^ 6 := by ring
    omega
  have hl1 := hlt F
  have hl2 := hlt 0
  have hDd := vsQD_le hs; have := hS.d
  have hq : loopModK * ((vsQVec F).length + 1) * ((Val.list [natList (vsQVec F),
      natList (vsQVec (0 : Fin (vsQD s) → ZMod I.p))]).wt + (vsQVec F).length + 4) ≤ 10 ^ 6 * S ^ 3 := by
    rw [vsQVec_length]
    have h2 : (vsQD s + 1) * ((Val.list [natList (vsQVec F), natList (vsQVec (0 : Fin (vsQD s) → ZMod I.p))]).wt +
        vsQD s + 4) ≤ S * (200 * S ^ 2) := Nat.mul_le_mul (by omega) (by
          have := Nat.le_self_pow (n := 2) (by norm_num) S; have := Nat.one_le_pow 2 S hS1; omega)
    have e : S * (200 * S ^ 2) = 200 * S ^ 3 := by ring
    simp only [loopModK]
    calc 1000 * (vsQD s + 1) * _ = 1000 * ((vsQD s + 1) * ((Val.list [natList (vsQVec F),
          natList (vsQVec (0 : Fin (vsQD s) → ZMod I.p))]).wt + vsQD s + 4)) := by ring
      _ ≤ _ := by omega
  have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2
  have hb : (decide (F ≠ 0)).toNat ≤ 1 := by cases decide (F ≠ 0) <;> simp
  have := wt_nat_le (decide (F ≠ 0)).toNat
  have hb2 := wt_boolVal_le (decide (vsQVec F = vsQVec (0 : Fin (vsQD s) → ZMod I.p)))
  have e1' : (natList (vsQVec F)).wt = (Val.list (List.drop 1 (Val.nat 0 :: (vsQVec F).map Val.nat))).wt := rfl
  have e2' : (natList (vsQVec (0 : Fin (vsQD s) → ZMod I.p))).wt =
    (Val.list (List.drop 1 (Val.nat 0 :: (vsQVec (0 : Fin (vsQD s) → ZMod I.p)).map Val.nat))).wt := rfl
  have ez : z0.wt = (Val.list (Val.nat 0 :: (vsQVec (0 : Fin (vsQD s) → ZMod I.p)).map Val.nat)).wt := rfl
  have ef : (Val.list (Val.nat 0 :: (vsQVec F).map Val.nat)).wt = (natList (0 :: vsQVec F)).wt := rfl
  have hs6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
  have eF0 : (natList (0 :: vsQVec (vsBAlpha s g 0))).wt = (natList (0 :: vsQVec F)).wt := rfl
  omega

/-! ### The answers of the case `T = 0` -/

section Ans

variable {s : VsQSt I} (hs : VsQStOK s)
include hs

theorem vsB_sol_iff {h : Perm (Fin I.n)} :
    h ∈ vsQSol I (gens s.hs) (vsQSp I s.ws') (vsWV I.p I.d s.x) (vsWV I.p I.d s.y) ↔
      h ∈ gens s.hs ∧ vsBAlpha s h 0 = vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x) := by
  constructor
  · rintro ⟨hh, h2⟩
    exact ⟨hh, (vsBAlpha_zero_eq hs hh _ hs.prob.cy).mpr h2⟩
  · rintro ⟨hh, h2⟩
    exact vsB_mem_sol hs hh h2

/-- If `f` vanishes on the generators and `t = 0`, the answer is `(1, hs)`. -/
theorem vsB0_ans_all (h0 : ∀ g ∈ s.hs, vsBAlpha s g 0 = 0)
    (ht : vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x) = 0) :
    VsQAnsOK hs.prob (some (1, s.hs)) := by
  refine ⟨(vsB_sol_iff hs).mpr ⟨one_mem _, by rw [ht, (vsBAlpha_act hs).one 0]⟩, ?_, hs.hsl⟩
  rw [← vsBStab0_eq hs]
  ext h
  exact ⟨fun hh => ⟨hh, vsB_f_zero hs h0 h hh⟩, fun hh => hh.1⟩

/-- If `f` vanishes on the generators and `t ≠ 0`, there is no solution. -/
theorem vsB0_ans_none (h0 : ∀ g ∈ s.hs, vsBAlpha s g 0 = 0)
    (ht : vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x) ≠ 0) :
    VsQAnsOK hs.prob none := by
  show vsQSol I _ _ _ _ = ∅
  ext h
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hh
  obtain ⟨hh, hf⟩ := (vsB_sol_iff hs).mp hh
  exact ht (hf ▸ vsB_f_zero hs h0 h hh)

variable (hab : s.Ab) (hdom : VsBDom s) (hT : ∀ k ∈ vsBH1 hs, vsBAlpha s k 0 = 0)
  {g₀ : Perm (Fin I.n)} (hg₀ : g₀ ∈ gens s.hs) {m : Fin (vsQD s) → ZMod I.p}
  (hm : (vsQLam s g₀ - 1) *ᵥ m = vsBAlpha s g₀ 0) (hne : vsBAlpha s g₀ 0 ≠ 0)
include hab hdom hT hg₀ hm hne

omit hab hdom hT hg₀ in
theorem vsB0_m_ne : m ≠ 0 := by
  rintro rfl
  rw [mulVec_zero] at hm
  exact hne hm.symm

/-- The solutions: `Λ(h) m = t + m`. -/
theorem vsB0_sol_iff {h : Perm (Fin I.n)} :
    h ∈ vsQSol I (gens s.hs) (vsQSp I s.ws') (vsWV I.p I.d s.x) (vsWV I.p I.d s.y) ↔
      h ∈ gens s.hs ∧ vsQLam s h *ᵥ m = vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x) + m := by
  rw [vsB_sol_iff hs]
  refine and_congr_right fun hh => ?_
  rw [vsB_T0_form hs hab hdom hT hg₀ hm hne hh, sub_mulVec, one_mulVec, sub_eq_iff_eq_add]

/-- The stabilizer is `H₁`. -/
theorem vsB0_stab : vsBStab0 hs = vsBH1 hs := by
  have hm0 := vsB0_m_ne hs hm hne
  ext h
  constructor
  · rintro ⟨hh, h0⟩
    rw [vsB_T0_form hs hab hdom hT hg₀ hm hne hh] at h0
    refine ⟨hh, ?_⟩
    rcases hdom _ (sub_mem (vsB_lam_mem hs hh) (one_mem _)) with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd (h1 m h0) hm0
  · rintro ⟨hh, h1⟩
    exact ⟨hh, by rw [vsB_T0_form hs hab hdom hT hg₀ hm hne hh, h1, sub_self, zero_mulVec]⟩

/-- If `t + m = 0` there is no solution. -/
theorem vsB0_ans_u0 (hu : vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x) + m = 0) :
    VsQAnsOK hs.prob none := by
  have hm0 := vsB0_m_ne hs hm hne
  show vsQSol I _ _ _ _ = ∅
  ext h
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hh
  obtain ⟨hh, he⟩ := (vsB0_sol_iff hs hab hdom hT hg₀ hm hne).mp hh
  rw [hu] at he
  apply hm0
  have := congrArg (vsQLam s h⁻¹ *ᵥ ·) he
  simpa [mulVec_mulVec, vsB_lam_inv' hs hh] using this

/-- With `τ ∈ L` and `τ m = t + m`, the solutions are the `h` with `Λ(h) = τ`. -/
theorem vsB0_sol_tau {τ : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)} (hτ : τ ∈ vsBLamA s)
    (hτm : τ *ᵥ m = vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x) + m) {h : Perm (Fin I.n)} :
    h ∈ vsQSol I (gens s.hs) (vsQSp I s.ws') (vsWV I.p I.d s.x) (vsWV I.p I.d s.y) ↔
      h ∈ gens s.hs ∧ vsQLam s h = τ := by
  have hm0 := vsB0_m_ne hs hm hne
  rw [vsB0_sol_iff hs hab hdom hT hg₀ hm hne, ← hτm]
  refine and_congr_right fun hh => ⟨fun he => ?_, fun he => by rw [he]⟩
  rcases hdom _ (sub_mem (vsB_lam_mem hs hh) hτ) with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd (h1 m (by rw [sub_mulVec, he, sub_self])) hm0

end Ans

end GI.Impl
