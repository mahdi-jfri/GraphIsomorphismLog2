import Workspace.Impl.VsBFld0T

/-!
# The λ-descent and the point `m` in the case `T = 0`

* `vsB_descA`: the descent along the λ-chain finds `h` with `Λ(h) = τ`, or reports that there is
  none.
* `vsB0mE`, `vsB0m_spec`: on `[ctxA, ctxB, g]` the coefficients of a solution `m` of
  `(Λ(g) - 1) m = f(g)`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The cost bound of the λ-descent. -/
def vsBDaCost (S Cφ : ℕ) : ℕ :=
  S * (2 * Cφ + 10 ^ 19 * S ^ 7 + 10 ^ 6 * vsBS2 S ^ 4 + permK * S ^ 3 +
    10 ^ 4 * (vsBWd S + 10 ^ 5 * S ^ 3)) +
  loopModK * (S + 1) * (vsBWd S + S + 10 ^ 6 * S ^ 3 + 1)

/-- The carried unit. -/
noncomputable def vsBEncU (s : VsQSt I) (u : vsBU s) : Val :=
  vsQE I.p (vsQD s) 0 ((u : (vsBMt s)ˣ) : vsBMt s)

set_option maxHeartbeats 4000000 in
/-- **The λ-descent.** -/
theorem vsB_descA {P : Program} {dA bA sotA cmp phi jp jm Cφ S Tm : ℕ}
    (hds : P.HasAt dA (vsBDescFuns dA (bA + 2) (sotA + 8) (bA + 3) cmp))
    (hsot : P.HasAt sotA (vsQSotFuns sotA (bA + 1) jp jm)) (hcmp : P.HasAt cmp (composeFuns cmp))
    (hA : P.HasAt bA (vsBAFuns bA phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) (hab : s.Ab) (hD : 1 ≤ vsQD s)
    (hdom : VsBDom s)
    {LsA : List (List ((Fin (vsQD s) → ZMod I.p) × Perm (Fin I.n)))} (hl : LsA.length = (vsBPs I.n).length)
    (hO : ∀ i (hi : i < LsA.length), VsBOrbL (vsBAp s ((vsBPs I.n).getD i 0))
      (vsBKs (vsBAp s) (vsBe0 s hD) (gens s.hs : Set (Perm (Fin I.n))) ((vsBPs I.n).take i))
      (vsBe0 s hD) LsA[i])
    (hW : ∀ L ∈ LsA, VsBPW (vsBS2 S) vsQVec L) (τ : vsBU s) :
    FunAll P dA (vsBDescIn (vsBCtxA s hD) (vsBPs I.n) vsQVec LsA (vsBEncU s) τ)
      (fun w c => VsBDescOut (gens s.hs) (vsBPsi hs) (vsBEncU s) τ w ∧ c ≤ vsBDaCost S Cφ) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  have hnS := hS.n
  have hQ1 : 1 ≤ vsBS2 S := by unfold vsBS2; have := Nat.one_le_pow 3 S hS1; omega
  have hSQ : S ≤ vsBS2 S := by unfold vsBS2; have := Nat.le_self_pow (n := 3) (by norm_num) S; omega
  have hps : (vsBPs I.n).length ≤ I.n + 1 := by simp [vsBPs]; omega
  have H := vsB_descHyp hs hab hD hdom
  have hT : ∀ q ∈ vsBPs I.n, ∀ τ', (natList (0 :: vsQVec (vsBTq s hD q τ'))).wt ≤ vsBS2 S := by
    intro q _ τ'
    have := (vsB_wt_vecA hS hs (vsBTq s hD q τ')).2
    have : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
    unfold vsBS2; omega
  have hWe : ∀ τ' : vsBU s, (vsBEncU s τ').wt ≤ 2 * 10 ^ 4 * S ^ 3 := fun τ' =>
    vsB_wt_carA hS hs _
  have hds' := vsBDesc_spec hds hsot hcmp H vsQVec_injective (ctx := vsBCtxA s hD)
    (enc := vsBEncU s) hl hO hQ1 hW hWe hT
    (Ctk := 10 ^ 18 * S ^ 7)
    (fun q hq τ' => (vsB_tkA_spec hA hS hs hD (pp := q) (by
      have := List.mem_range.mp hq; simp [vsBPs] at this; omega) τ').mono (by
      have w := wt_list3_le (vsBCtxA s hD) (.nat q) (vsBEncU s τ')
      have := vsB_wt_ctxA hS hs hD; have := hWe τ'; have := wt_nat_le q
      have : q < I.n + 1 := by have := List.mem_range.mp hq; simp [vsBPs] at this; omega
      have h13 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
      have h37 : S ^ 3 ≤ S ^ 7 := Nat.pow_le_pow_right hS1 (by norm_num)
      omega))
    (Cup := Cφ + 10 ^ 16 * S ^ 5)
    (fun τ' t ht => vsB_upA_spec hA hphi hS hs hD τ' ht) τ
  refine hds'.mono fun w c hw => ⟨hw.1, ?_⟩
  obtain ⟨-, hc⟩ := hw
  have hlA : LsA.length ≤ S := by omega
  have wa : (vsBDescIn (vsBCtxA s hD) (vsBPs I.n) vsQVec LsA (vsBEncU s) τ).wt ≤ vsBWd S := by
    have w := wt_list_le [vsBCtxA s hD, .list ((vsBPs I.n).map Val.nat),
      .list (LsA.map (vsQPairs vsQVec)), vsBEncU s τ, encPerm (1 : Perm (Fin I.n))]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at w
    have w1 := vsB_wt_ctxA hS hs hD
    have w2 : (Val.list ((vsBPs I.n).map Val.nat)).wt ≤ 5 * (S + 1) ^ 2 :=
      wt_natList_le_sq (xs := vsBPs I.n) (fun y hy => by simp [vsBPs] at hy; omega) (by omega)
    have w3 := vsB_wt_Ls hS1 hlA hW
    have w4 := hWe τ
    have w5 := hS.wt_perm (1 : Perm (Fin I.n))
    have q : (S + 1) ^ 2 ≤ 4 * S ^ 6 := by
      have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h2 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
      have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
      omega
    have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have e3 : 100 * S * vsBS2 S ^ 3 = 100 * (S * vsBS2 S ^ 3) := by ring
    unfold vsBWd
    have e4 : 10 ^ 3 * S * vsBS2 S ^ 3 = 1000 * (S * vsBS2 S ^ 3) := by ring
    have ew : (vsBDescIn (vsBCtxA s hD) (vsBPs I.n) vsQVec LsA (vsBEncU s) τ).wt =
        (Val.list [vsBCtxA s hD, .list ((vsBPs I.n).map Val.nat),
      .list (LsA.map (vsQPairs vsQVec)), vsBEncU s τ, encPerm (1 : Perm (Fin I.n))]).wt := rfl
    have := Nat.one_le_pow 6 S hS1
    omega
  have hlen : (vsBPs I.n).length ≤ S := by omega
  have hn3 : (I.n + 1) ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left hnS 3
  have hn2 : (I.n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hnS 2
  have q23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q37 : S ^ 3 ≤ S ^ 7 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q57 : S ^ 5 ≤ S ^ 7 := Nat.pow_le_pow_right hS1 (by norm_num)
  have h4 : S ^ 4 ≤ vsBS2 S ^ 4 := Nat.pow_le_pow_left hSQ 4
  unfold vsBDaCost
  set Wa := (vsBDescIn (vsBCtxA s hD) (vsBPs I.n) vsQVec LsA (vsBEncU s) τ).wt
  have k1 : (vsBPs I.n).length * (10 ^ 18 * S ^ 7 + (Cφ + 10 ^ 16 * S ^ 5) +
      10 ^ 6 * vsBS2 S ^ 4 + permK * (I.n + 1) ^ 3 +
      10 ^ 4 * (Wa + 2 * 10 ^ 4 * S ^ 3 + 4 * (I.n + 1) ^ 2 + 20)) ≤
      S * (2 * Cφ + 10 ^ 19 * S ^ 7 + 10 ^ 6 * vsBS2 S ^ 4 + permK * S ^ 3 +
        10 ^ 4 * (vsBWd S + 10 ^ 5 * S ^ 3)) := by
    apply Nat.mul_le_mul hlen
    have : permK * (I.n + 1) ^ 3 ≤ permK * S ^ 3 := Nat.mul_le_mul_left _ hn3
    have := Nat.one_le_pow 3 S hS1
    omega
  have k2 : loopModK * ((vsBPs I.n).length + 1) * (Wa + (vsBPs I.n).length +
      (2 * (2 * 10 ^ 4 * S ^ 3 + 4 * (I.n + 1) ^ 2 + 3) + 7) + 1) ≤
      loopModK * (S + 1) * (vsBWd S + S + 10 ^ 6 * S ^ 3 + 1) := by
    apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
    have := Nat.one_le_pow 3 S hS1
    omega
  omega

/-! ### The point `m` -/

/-- On `[ctxA, ctxB, g]`: the solution coefficients of `(Λ(g) - 1) m = f(g)`. -/
def vsB0mE (lcar subC act tail sv : ℕ) : Expr :=
  .call sv (mk3 (.get (arg 0) (.nat 2))
    (.call subC (mk3 (.get (arg 0) (.nat 2)) (.nat 1) (.get (.call lcar (mk2 (arg 0) (arg 2))) (.nat 3))))
    (.call tail (.call act (mk3 (.get (arg 1) (.nat 0)) (arg 2) (.get (arg 1) (.nat 2))))))

/-- The coefficients of `m`. -/
noncomputable def vsB0a (s : VsQSt I) (g : Perm (Fin I.n)) : List ℕ :=
  vsBSolveL I.p (vsBR s g) (vsQVec (vsBAlpha s g 0))

set_option maxHeartbeats 8000000 in
theorem vsB0m_spec {P : Program} {f bA bB sc sv phi Cφ S Tm : ℕ}
    (hf : P.funs[f]? = some (vsB0mE (bA + 4) sc (bB + 3) (bB + 4) sv))
    (hA : P.HasAt bA (vsBAFuns bA phi)) (hB : P.HasAt bB (vsBBFuns bB phi))
    (hsc : P.HasAt sc (vsWSubCFuns sc)) (hsv : P.HasAt sv (vsBSolveFuns sv))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) (hD : 1 ≤ vsQD s) (hdom : VsBDom s)
    (hT : ∀ k ∈ vsBH1 hs, vsBAlpha s k 0 = 0) {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs)
    (hne : vsBAlpha s g 0 ≠ 0) :
    FunDet P f (.list [vsBCtxA s hD, vsBCtxB s, encPerm g]) (natList (vsB0a s g))
      (2 * Cφ + 10 ^ 17 * S ^ 6) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  have hpS := hS.p
  have hact : P.HasAt (bB + 3) (vsBActFuns (bB + 3) phi) := hB.block 3 rfl
  have htl : P.HasAt (bB + 4) (linTailFuns (bB + 4)) := hact.block 1 rfl
  set cA := vsBCtxA s hD
  set cB := vsBCtxB s
  set ac := Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x]
  set z0 := natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))
  set F := vsBAlpha s g 0
  set Lam := vsQL (vsQLam s g)ᵀ
  have g0 := Det.arg' (P := P) (rest := []) (vs := [cA, cB, encPerm g]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [cA, cB, encPerm g]) (j := 1) rfl
  have g2 := Det.arg' (P := P) (rest := []) (vs := [cA, cB, encPerm g]) (j := 2) rfl
  have dp := Det.get' g0 (Det.nat 2) (show [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
    natList (List.replicate (vsQD s) 0), .nat I.n, natList (vsQVec (vsBe0 s hD))][2]? = some (.nat I.p) from rfl)
  -- the stored `Λ(g)`
  have dl := Det.call (Det.mk2 g0 g2) (vsB_lcar_spec hA hphi hS hs hD hg)
  have dL := Det.get' dl (Det.nat 3) (show [Val.nat I.p, natList (List.replicate (vsQD s) 0), .nat 0,
    .list (Lam.map natList)][3]? = some (.list (Lam.map natList)) from rfl)
  have hLsq : VsWSq I.p (vsQD s) Lam := by
    have := vsQL_sq (p := I.p) (vsQLam s g)ᵀ
    exact ⟨this.2, this.1⟩
  have dR := Det.call (Det.mk3 dp (Det.nat 1) dL)
    (vsWSubC_spec hsc I.prime.pos (N := S) hpS (by omega) I.prime.one_lt.le hLsq)
  have eR : vsWSubC I.p 1 Lam = vsBR s g := rfl
  rw [eR] at dR
  -- `f(g)`
  have dac := Det.get' g1 (Det.nat 0) (show [ac, .nat I.p, z0][0]? = some ac from rfl)
  have dz := Det.get' g1 (Det.nat 2) (show [ac, .nat I.p, z0][2]? = some z0 from rfl)
  have dact := Det.call (Det.mk3 dac g2 dz) (vsB_f_spec hB hphi hS hs hg)
  have dt1 := Det.call dact (linTail_spec htl (.nat 0 :: (vsQVec F).map Val.nat))
  have e1 : Val.list (List.drop 1 (Val.nat 0 :: (vsQVec F).map Val.nat)) = natList (vsQVec F) := rfl
  rw [e1] at dt1
  -- solving
  have hRfit := vsBR_sq (s := s) g
  have hFfit : VsWFit I.p (vsQD s) [vsQVec F] := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨vsQVec_lt F, vsQVec_length F⟩
  have hsp' : vsWV I.p (vsQD s) (vsQVec F) ∈ vsWSp I.p (vsQD s) (vsBR s g) := by
    exact vsB0_m_sp hs hdom hT hg hne
  have dsv := Det.call (Det.mk3 dp dR dt1)
    (vsBSolve_spec hsv I.prime (N := S) hpS (by omega) hRfit.1 (by rw [hRfit.2]; omega) hFfit hsp')
  refine FunDet.intro hf (dsv.mono ?_)
  -- the cost
  have wcA := vsB_wt_ctxA hS hs hD
  have wcB := vsB_wt_ctxB hS hs
  have wg := hS.wt_perm g
  have w3 := wt_list3_le cA cB (encPerm g)
  have wE := vsB_wt_carA hS hs (vsQLam s g)
  have wL : (Val.list (Lam.map natList)).wt < (vsQE I.p (vsQD s) 0 (vsQLam s g)).wt :=
    wt_le_wt_list (by simp [vsQE, Lam])
  have wpc : (Val.nat I.p).wt < cA.wt := wt_le_wt_list (by simp [cA, vsBCtxA])
  have wac : ac.wt < cB.wt := wt_le_wt_list (by simp [cB, vsBCtxB, ac])
  have wz : z0.wt < cB.wt := wt_le_wt_list (by simp [cB, vsBCtxB, z0])
  have w2 := wt_list2_le cA (encPerm g)
  have wR := wt_vsWVs_le (VsWFit.bnd hRfit.1 hpS (by omega : vsQD s ≤ S)) (by rw [hRfit.2]; omega)
  have wR' : (Val.list (Lam.map natList)).wt ≤ 2 * 10 ^ 4 * S ^ 3 := by omega
  have w3R := wt_list3_le (.nat I.p) (.nat 1) (Val.list (Lam.map natList))
  have wF := (vsB_wt_vecA hS hs F)
  have w3a := wt_list3_le ac (encPerm g) z0
  have hlt : linTailCost (Val.list (Val.nat 0 :: (vsQVec F).map Val.nat)).wt ≤ 10 ^ 8 * S ^ 6 := by
    unfold linTailCost
    have e : (Val.list (Val.nat 0 :: (vsQVec F).map Val.nat)).wt = (natList (0 :: vsQVec F)).wt := rfl
    rw [e]
    have h1 : (natList (0 :: vsQVec F)).wt + 1 ≤ 21 * S ^ 2 := by
      have := Nat.one_le_pow 2 S hS1; omega
    have := Nat.pow_le_pow_left h1 3
    have e2 : (21 * S ^ 2) ^ 3 = 9261 * S ^ 6 := by ring
    omega
  have w3s := wt_list3_le (.nat I.p) (vsWVs (vsBR s g)) (natList (vsQVec F))
  have hsol := vsBSolve_comb I.prime hRfit.1 hFfit hsp'
  have wo := wt_natList_le_sq (B := S) (xs := vsB0a s g) (fun y hy => (hsol.1 y hy).le.trans hpS)
    (by rw [vsB0a, hsol.2.1, hRfit.2]; omega)
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
  have := wt_nat_le I.p
  have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q46 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q56 : S ^ 5 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hs6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
  have hN4 : (S + 1) ^ 4 ≤ 16 * S ^ 4 := by
    have h1 : (S + 1) ^ 4 ≤ (2 * S) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have e : (2 * S) ^ 4 = 16 * S ^ 4 := by ring
    omega
  have hN6 : (S + 1) ^ 6 ≤ 64 * S ^ 6 := by
    have h1 : (S + 1) ^ 6 ≤ (2 * S) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have e : (2 * S) ^ 6 = 64 * S ^ 6 := by ring
    omega
  have hN3 : (S + 1) ^ 3 ≤ 8 * S ^ 3 := by
    have h1 : (S + 1) ^ 3 ≤ (2 * S) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have e : (2 * S) ^ 3 = 8 * S ^ 3 := by ring
    omega
  have eF0 : (natList (0 :: vsQVec (vsBAlpha s g 0))).wt = (natList (0 :: vsQVec F)).wt := rfl
  have ef : (Val.list (Val.nat 0 :: (vsQVec F).map Val.nat)).wt = (natList (0 :: vsQVec F)).wt := rfl
  have e1' : (natList (vsQVec F)).wt = (Val.list (List.drop 1 (Val.nat 0 :: (vsQVec F).map Val.nat))).wt := rfl
  have ea : (natList (vsBSolveL I.p (vsBR s g) (vsQVec F))).wt = (natList (vsB0a s g)).wt := rfl
  have eq3 : (vsWVs (vsWSubC I.p 1 Lam)).wt = (vsWVs (vsBR s g)).wt := rfl
  have ecA : cA.wt = (vsBCtxA s hD).wt := rfl
  have ecB : cB.wt = (vsBCtxB s).wt := rfl
  have hN2 : (S + 1) ^ 2 ≤ 4 * S ^ 2 := by
    have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
    omega
  have t1 : (Val.list [cA, cB, encPerm g]).wt ≤ 10 ^ 7 * S ^ 6 := by omega
  have t2 : (vsWVs (vsBR s g)).wt ≤ 10 ^ 7 * S ^ 6 := by omega
  have t3 : (natList (vsBSolveL I.p (vsBR s g) (vsQVec F))).wt ≤ 10 ^ 7 * S ^ 6 := by omega
  have t4 : (Val.list [Val.nat I.p, vsWVs (vsBR s g), natList (vsQVec F)]).wt ≤ 10 ^ 7 * S ^ 6 := by omega
  have t5 : (Val.list [ac, encPerm g, z0]).wt ≤ 10 ^ 7 * S ^ 6 := by omega
  have t6 : (vsQE I.p (vsQD s) 0 (vsQLam s g)).wt ≤ 10 ^ 7 * S ^ 6 := by omega
  omega

end GI.Impl
