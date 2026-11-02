import Workspace.Impl.VsBFldHyp
import Workspace.Impl.VsBDesc
import Workspace.Impl.VsBSolve
import Workspace.Impl.VsQAnaBase

/-!
# The preparation of the field line

On the local context `lc = vsQLCV s` the program `prep` builds the two contexts, runs the
λ-chain (from `1 :: hs`, ending at generators of `H₁ = ker Λ`) and the translation chain (from
those, ending at generators of `ker f|H₁`), and computes the target `t`, the coordinates of
`y - x`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

theorem vsQVec_e0 {s : VsQSt I} (hD : 1 ≤ vsQD s) : vsQVec (vsBe0 s hD) = vsUnit (vsQD s) 0 := by
  haveI : Fact (1 < I.p) := ⟨I.prime.one_lt⟩
  apply List.ext_getElem (by simp [vsQVec_length, vsUnit_length])
  intro j h1 h2
  have hjD : j < vsQD s := by simpa [vsQVec_length] using h1
  have e : (List.finRange (vsQD s))[j]'(by simpa using hjD) = ⟨j, hjD⟩ := Fin.ext (by simp)
  simp only [vsQVec, vsUnit, List.getElem_map, List.getElem_range, vsBe0]
  rw [e]
  by_cases hj : j = 0
  · subst hj; simp [ZMod.val_one]
  · rw [if_neg hj, Pi.single_apply, if_neg (by intro h; apply hj; simpa using congrArg Fin.val h)]
    simp

theorem vsQVec_zero {p D : ℕ} : vsQVec (0 : Fin D → ZMod p) = List.replicate D 0 := by
  apply List.ext_getElem (by simp [vsQVec_length])
  intro j h1 h2
  simp [vsQVec]

/-- The end of the λ-chain is `H₁`. -/
theorem vsB_KsA {s : VsQSt I} (hs : VsQStOK s) (hD : 1 ≤ vsQD s) (hdom : VsBDom s) :
    vsBKs (vsBAp s) (vsBe0 s hD) (gens s.hs : Set (Perm (Fin I.n))) (vsBPs I.n) =
      (vsBH1 hs : Set (Perm (Fin I.n))) := by
  ext h
  simp only [vsBKs, Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨hh, hq⟩
    refine ⟨hh, (vsB_lam_eq_one h).mpr fun q hq2 hqN => ?_⟩
    have hp : q - 2 ∈ vsBPs I.n := List.mem_range.mpr (by omega)
    have := hq (q - 2) hp
    rw [vsBAp, vsB_stab_iff hs hD hdom _ hh] at this
    rwa [show q - 2 + 2 = q by omega] at this
  · rintro ⟨hh, h1⟩
    refine ⟨hh, fun q _ => ?_⟩
    rw [vsBAp, vsB_stab_iff hs hD hdom _ hh, h1, one_pow]

/-- The end of the translation chain is the kernel of `f` on `H₁`. -/
theorem vsB_KsB {s : VsQSt I} (hs : VsQStOK s) :
    vsBKs (vsBAj s) 0 (vsBH1 hs : Set (Perm (Fin I.n))) (List.range (vsQD s)) =
      {k | k ∈ vsBH1 hs ∧ vsBAlpha s k 0 = 0} := by
  ext h
  simp only [vsBKs, Set.mem_setOf_eq, SetLike.mem_coe, vsBAj, zero_add, List.mem_range]
  constructor
  · rintro ⟨hh, hq⟩
    refine ⟨hh, funext fun j => ?_⟩
    have := hq j j.2
    rwa [dif_pos j.2] at this
  · rintro ⟨hh, h0⟩
    refine ⟨hh, fun j hj => ?_⟩
    rw [dif_pos hj, h0]; rfl

/-- `Γ`, from the local context. -/
def vsBGamE : Expr := .get (arg 0) (.nat 0)

/-- The context of the λ-chain, from the local context. -/
def vsBCtxAE (unit : ℕ) : Expr :=
  mk6 vsBGamE (arg 1) (.get (.get (arg 1) (.nat 0)) (.nat 0)) (.get (.get (arg 1) (.nat 0)) (.nat 3))
    (.get (.get vsBGamE (.nat 0)) (.nat 0)) (.call unit (mk2 (arg 2) (.nat 0)))

/-- The context of the translation chain, from the local context. -/
def vsBCtxBE (appd : ℕ) : Expr :=
  mk3 (mk3 vsBGamE (arg 1) (.get (arg 0) (.nat 4))) (.get (.get (arg 1) (.nat 0)) (.nat 0))
    (.call appd (mk2 (mk1 (.nat 0)) (.get (.get (arg 1) (.nat 0)) (.nat 3))))

/-- The preparation: contexts, the λ-chain, the translation chain and the target. -/
def vsBPrepE (unit appd rng chA chB co lin : ℕ) : Expr :=
  .letE (vsBCtxAE unit)
  (.letE (vsBCtxBE appd)
  (.letE (.call chA (mk6 (.var 1) (.get (.get (arg 0) (.nat 1)) (.nat 1))
      (.call rng (.ite (.arith .lt (.get (.var 1) (.nat 4)) (.nat 2)) (.nat 1)
        (.arith .sub (.get (.var 1) (.nat 4)) (.nat 1))))
      (.call appd (mk2 (mk1 (.nat 0)) (.get (.var 1) (.nat 5))))
      (.arith .add (.get (.var 1) (.nat 4)) (.nat 1)) (.get (.var 1) (.nat 4))))
  (.letE (.call chB (mk6 (.var 2) (.get (.var 3) (.nat 0)) (.call rng (arg 2)) (mk2 (.nat 0) (.nat 0))
      (.get (.var 2) (.nat 1)) (.get (.var 1) (.nat 4))))
  (.letE (.call co (mk2 (arg 1) (.call lin (.snoc (mk4 (.get (.var 2) (.nat 1)) (.nat 1)
      (.arith .sub (.get (.var 2) (.nat 1)) (.nat 1)) (.get (arg 0) (.nat 5))) (.get (arg 0) (.nat 4))))))
    (vsBmk5 (.var 1) (.var 2) (.var 3) (.var 4) (.var 5))))))

/-- The cost bound of one chain of the field line. -/
noncomputable def vsBChCost (hps : PointwiseStab) (hm : Membership) (n S Cφ : ℕ) : ℕ :=
  (S + 1) * (vsQSotCost hps hm n (vsBS2 S) (Cφ + 10 ^ 18 * S ^ 7) +
    10 ^ 4 * (10 ^ 8 * S ^ 6 + 1000 * vsBS2 S ^ 4)) +
  loopModK * (S + 2) * (10 ^ 8 * S ^ 6 + S + 1000 * vsBS2 S ^ 4 + 1)

theorem vsQSotCost_mono (hps : PointwiseStab) (hm : Membership) (n S : ℕ) {A A' : ℕ} (h : A ≤ A') :
    vsQSotCost hps hm n S A ≤ vsQSotCost hps hm n S A' := by
  unfold vsQSotCost
  have := Nat.mul_le_mul_left (S ^ 2) h
  omega

theorem vsB_chain_cost_le (hps : PointwiseStab) (hm : Membership) {n S Cφ A k W : ℕ}
    (hA : A ≤ Cφ + 10 ^ 18 * S ^ 7) (hk : k ≤ S) (hW : W ≤ 10 ^ 8 * S ^ 6) :
    k * (vsQSotCost hps hm n (vsBS2 S) A + 10 ^ 4 * (W + 1000 * vsBS2 S ^ 4)) +
      loopModK * (k + 1) * (W + k + 1000 * vsBS2 S ^ 4 + 1) ≤ vsBChCost hps hm n S Cφ := by
  unfold vsBChCost
  have h1 := vsQSotCost_mono hps hm n (vsBS2 S) hA
  have h2 : k * (vsQSotCost hps hm n (vsBS2 S) A + 10 ^ 4 * (W + 1000 * vsBS2 S ^ 4)) ≤
      (S + 1) * (vsQSotCost hps hm n (vsBS2 S) (Cφ + 10 ^ 18 * S ^ 7) +
        10 ^ 4 * (10 ^ 8 * S ^ 6 + 1000 * vsBS2 S ^ 4)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : loopModK * (k + 1) * (W + k + 1000 * vsBS2 S ^ 4 + 1) ≤
      loopModK * (S + 2) * (10 ^ 8 * S ^ 6 + S + 1000 * vsBS2 S ^ 4 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  omega

theorem vsB_wt_gens' {S Tm : ℕ} (hS : VsQDSz I S Tm) {gs : List (Perm (Fin I.n))}
    (hl : gs.length ≤ I.n ^ 2 + 4) : (Val.list (gs.map encPerm)).wt ≤ 500 * S ^ 6 := by
  have h1 := wt_list_encPerms_le gs
  have hS1 := hS.one_le
  have hn := hS.n
  have h2 : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hS2 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS1
  have h3 : (gs.length + 1) * (I.n + 1) ≤ (6 * S ^ 2) * S :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 := Nat.pow_le_pow_left h3 2
  have e : ((6 * S ^ 2) * S) ^ 2 = 36 * S ^ 6 := by ring
  omega

theorem vsB_wt_gens {S Tm : ℕ} (hS : VsQDSz I S Tm) {gs : List (Perm (Fin I.n))}
    (hl : gs.length ≤ I.n ^ 2 + 2) : (Val.list (gs.map encPerm)).wt ≤ 208 * S ^ 6 := by
  have h1 := wt_list_encPerms_le gs
  have hS1 := hS.one_le
  have hn := hS.n
  have h2 : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hS2 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS1
  have h3 : (gs.length + 1) * (I.n + 1) ≤ (4 * S ^ 2) * S :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 := Nat.pow_le_pow_left h3 2
  have e : ((4 * S ^ 2) * S) ^ 2 = 16 * S ^ 6 := by ring
  omega

theorem vsB_chain_out_wt (hps : PointwiseStab) (hm : Membership) {n S Cφ : ℕ} (hS1 : 1 ≤ S)
    {Y : Type} {keyY : Y → List ℕ} {gs : List (Perm (Fin n))} {Ls : List (List (Y × Perm (Fin n)))}
    (hg : (Val.list (gs.map encPerm)).wt ≤ 208 * S ^ 6) (hl : Ls.length ≤ S)
    (hW : ∀ L ∈ Ls, VsBPW (vsBS2 S) keyY L) :
    (Val.list [.list (gs.map encPerm), .list (Ls.map (vsQPairs keyY))]).wt ≤ vsBChCost hps hm n S Cφ := by
  have h1 := GI.Lang.wt_list_le_of (Ls.map (vsQPairs keyY)) (c := 40 * vsBS2 S ^ 3) (by
    intro v hv; obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hv; exact (hW L hL).2.1)
  rw [List.length_map] at h1
  have h2 := wt_list2_le (.list (gs.map encPerm)) (.list (Ls.map (vsQPairs keyY)))
  have hS2 : S ≤ vsBS2 S := by
    unfold vsBS2; have := Nat.le_self_pow (n := 3) (by norm_num) S; omega
  have h3 : Ls.length * (2 * (40 * vsBS2 S ^ 3) + 1) ≤ vsBS2 S * (81 * vsBS2 S ^ 3) :=
    Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 3 (vsBS2 S) (by omega); omega)
  have e : vsBS2 S * (81 * vsBS2 S ^ 3) = 81 * vsBS2 S ^ 4 := by ring
  have h4 : S ^ 6 ≤ vsBS2 S ^ 4 := by
    unfold vsBS2
    calc S ^ 6 ≤ (S ^ 3) ^ 4 := by rw [← pow_mul]; exact Nat.pow_le_pow_right hS1 (by norm_num)
      _ ≤ (10 ^ 7 * S ^ 3) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h5 : 1 ≤ vsBS2 S ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold vsBChCost
  have h6 : 1000 * vsBS2 S ^ 4 ≤ loopModK * (S + 2) * (10 ^ 8 * S ^ 6 + S + 1000 * vsBS2 S ^ 4 + 1) := by
    simp only [loopModK]; nlinarith
  omega

/-- What the preparation returns. -/
def VsBPrepOut {s : VsQSt I} (hs : VsQStOK s) (hD : 1 ≤ vsQD s) (S : ℕ) (w : Val) : Prop :=
  ∃ (gsA : List (Perm (Fin I.n))) (LsA : List (List ((Fin (vsQD s) → ZMod I.p) × Perm (Fin I.n))))
    (gsB : List (Perm (Fin I.n))) (LsB : List (List (ZMod I.p × Perm (Fin I.n)))),
    w = .list [vsBCtxA s hD, vsBCtxB s,
      .list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))],
      .list [.list (gsB.map encPerm), .list (LsB.map (vsQPairs vsBKeyB))],
      natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))] ∧
    (genGroup gsA : Set (Perm (Fin I.n))) = vsBH1 hs ∧ gsA.length ≤ I.n ^ 2 + 2 ∧
    LsA.length = (vsBPs I.n).length ∧
    (∀ i (hi : i < LsA.length), VsBOrbL (vsBAp s ((vsBPs I.n).getD i 0))
      (vsBKs (vsBAp s) (vsBe0 s hD) (gens s.hs : Set (Perm (Fin I.n))) ((vsBPs I.n).take i))
      (vsBe0 s hD) LsA[i]) ∧ (∀ L ∈ LsA, VsBPW (vsBS2 S) vsQVec L) ∧
    (genGroup gsB : Set (Perm (Fin I.n))) = {k | k ∈ vsBH1 hs ∧ vsBAlpha s k 0 = 0} ∧
    gsB.length ≤ I.n ^ 2 + 2 ∧ LsB.length = vsQD s ∧
    (∀ i (hi : i < LsB.length), VsBOrbL (vsBAj s ((List.range (vsQD s)).getD i 0))
      (vsBKs (vsBAj s) 0 (vsBH1 hs : Set (Perm (Fin I.n))) ((List.range (vsQD s)).take i)) 0 LsB[i]) ∧
    (∀ L ∈ LsB, VsBPW (vsBS2 S) vsBKeyB L)

section

variable {P : Program} {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
  (hD : 1 ≤ vsQD s)
include hS hs

/-- Access to the local context in any environment that starts with it. -/
theorem vsB_lc_arg (rest : List Val) (j : ℕ) (v : Val)
    (hv : [vsQStV I s, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat (vsQD s), vsFMatsVal (vsQMs s)][j]? = some v) :
    Det P (vsQLCV s :: rest) (arg j) v (2 * (vsQLCV s).wt + j + 5) :=
  Det.arg' (vs := [vsQStV I s, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat (vsQD s), vsFMatsVal (vsQMs s)])
    (rest := rest) hv

set_option maxHeartbeats 2000000 in
include hD in
theorem vsB_ctxA_det {unit : ℕ} (hu : P.HasAt unit (vsUnitFuns unit)) (rest : List Val) :
    Det P (vsQLCV s :: rest) (vsBCtxAE unit) (vsBCtxA s hD) (10 ^ 9 * S ^ 6) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  set lc := vsQLCV s
  set stV := vsQStV I s
  set frV := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set fr0 := Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQD s))]
  have dst := vsB_lc_arg hS hs (P := P) rest 0 stV rfl
  have dfr := vsB_lc_arg hS hs (P := P) rest 1 frV rfl
  have dD := vsB_lc_arg hS hs (P := P) rest 2 (.nat (vsQD s)) rfl
  have dΓ := Det.get' dst (Det.nat 0) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
    natList s.y][0]? = some (vsQGam I) from rfl)
  have dfr0 := Det.get' dfr (Det.nat 0) (show [fr0, vsWVs s.ws', vsWVs (vsQCs s),
    .list ((vsWFrRows I.p s.ws' (vsQCs s)).map VsRow.val)][0]? = some fr0 from rfl)
  have dp := Det.get' dfr0 (Det.nat 0) (show [Val.nat I.p, .nat I.d, natList (vsWZ I.d),
    natList (vsWZ (vsQD s))][0]? = some (.nat I.p) from rfl)
  have dz := Det.get' dfr0 (Det.nat 3) (show [Val.nat I.p, .nat I.d, natList (vsWZ I.d),
    natList (vsWZ (vsQD s))][3]? = some (natList (vsWZ (vsQD s))) from rfl)
  have dG := Det.get' dΓ (Det.nat 0) (show [encGroup I.gs, vsQTable I, vsQE I.p I.d (vsQExp I) 1][0]? =
    some (encGroup I.gs) from rfl)
  have dn := Det.get' dG (Det.nat 0) (show [Val.nat I.n, .list ((1 :: I.gs).map encPerm)][0]? =
    some (.nat I.n) from rfl)
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  have wU := (vsB_wt_vecA hS hs (vsBe0 s hD)).1
  rw [vsQVec_e0 hD] at wU
  have kU : ∀ w, w = natList (vsUnit (vsQD s) 0) → loopModK * (vsQD s + 1) *
      ((Val.list [.nat (vsQD s), .nat 0]).wt + vsQD s + w.wt + 1) ≤ 10 ^ 5 * S ^ 3 := by
    rintro w rfl
    have := wt_list2_le (.nat (vsQD s)) (.nat 0)
    have := wt_nat_le (vsQD s); have := wt_nat_le 0
    have h2 : (vsQD s + 1) * ((Val.list [.nat (vsQD s), .nat 0]).wt + vsQD s +
        (natList (vsUnit (vsQD s) 0)).wt + 1) ≤ S * (100 * S ^ 2) :=
      Nat.mul_le_mul (by omega) (by have := Nat.le_self_pow (n := 2) (by norm_num) S; omega)
    have e : S * (100 * S ^ 2) = 100 * S ^ 3 := by ring
    simp only [loopModK]
    calc 1000 * (vsQD s + 1) * _ = 1000 * ((vsQD s + 1) * ((Val.list [.nat (vsQD s), .nat 0]).wt +
          vsQD s + (natList (vsUnit (vsQD s) 0)).wt + 1)) := by ring
      _ ≤ _ := by omega
  have de := Det.call (Det.mk2 dD (Det.nat 0)) ((vsUnit_spec hu (vsQD s) 0).mono fun w c hw =>
    ⟨hw.1, hw.2.trans (kU w hw.1)⟩)
  rw [← vsQVec_e0 hD] at de
  have dall := Det.mk6' dΓ dfr dp dz dn de
  refine dall.mono ?_
  have wLC := vsQ_wt_LC hS hs
  have elc : lc.wt = (vsQLCV s).wt := rfl
  have wst : stV.wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV, stV])
  have wfr : frV.wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV, frV])
  have wDv : (Val.nat (vsQD s)).wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV])
  have wΓ : (vsQGam I).wt < stV.wt := wt_le_wt_list (by simp [stV, vsQStV])
  have wfr0 : fr0.wt < frV.wt := wt_le_wt_list (by simp [frV, vsWFrVal, fr0])
  have wG : (encGroup I.gs).wt < (vsQGam I).wt := wt_le_wt_list (by simp [vsQGam])
  have wpv : (Val.nat I.p).wt < fr0.wt := wt_le_wt_list (by simp [fr0])
  have wzv : (natList (vsWZ (vsQD s))).wt < fr0.wt := wt_le_wt_list (by simp [fr0])
  have wnv : (Val.nat I.n).wt < (encGroup I.gs).wt := wt_le_wt_list (by simp [encGroup, encPerms])
  have wc := vsB_wt_ctxA hS hs hD
  have ec : (Val.list [vsQGam I, frV, .nat I.p, natList (vsWZ (vsQD s)), .nat I.n,
    natList (vsQVec (vsBe0 s hD))]).wt = (vsBCtxA s hD).wt := rfl
  have w2 := wt_list2_le (.nat (vsQD s)) (.nat 0)
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
  have q36 : S ^ 3 ≤ S ^ 6 := hS.pow_le (by omega)
  have q26 : S ^ 2 ≤ S ^ 6 := hS.pow_le (by omega)
  have eU : (natList (vsQVec (vsBe0 s hD))).wt = (natList (vsUnit (vsQD s) 0)).wt := by rw [vsQVec_e0 hD]
  omega

set_option maxHeartbeats 2000000 in
theorem vsB_ctxB_det {appd : ℕ} (hap : P.HasAt appd (appendFuns appd)) (rest : List Val) :
    Det P (vsQLCV s :: rest) (vsBCtxBE appd) (vsBCtxB s) (10 ^ 9 * S ^ 6) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  set lc := vsQLCV s
  set stV := vsQStV I s
  set frV := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set fr0 := Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQD s))]
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  have dst := vsB_lc_arg hS hs (P := P) rest 0 stV rfl
  have dfr := vsB_lc_arg hS hs (P := P) rest 1 frV rfl
  have dΓ := Det.get' dst (Det.nat 0) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
    natList s.y][0]? = some (vsQGam I) from rfl)
  have dx := Det.get' dst (Det.nat 4) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
    natList s.y][4]? = some (natList s.x) from rfl)
  have dfr0 := Det.get' dfr (Det.nat 0) (show [fr0, vsWVs s.ws', vsWVs (vsQCs s),
    .list ((vsWFrRows I.p s.ws' (vsQCs s)).map VsRow.val)][0]? = some fr0 from rfl)
  have dp := Det.get' dfr0 (Det.nat 0) (show [Val.nat I.p, .nat I.d, natList (vsWZ I.d),
    natList (vsWZ (vsQD s))][0]? = some (.nat I.p) from rfl)
  have dz := Det.get' dfr0 (Det.nat 3) (show [Val.nat I.p, .nat I.d, natList (vsWZ I.d),
    natList (vsWZ (vsQD s))][3]? = some (natList (vsWZ (vsQD s))) from rfl)
  have wZ := (vsB_wt_vecA hS hs (0 : Fin (vsQD s) → ZMod I.p)).2
  rw [vsQVec_zero] at wZ
  have kap : loopModK * ((vsWZ (vsQD s)).map Val.nat).length.succ *
      ((Val.list [.list [.nat 0], .list ((vsWZ (vsQD s)).map Val.nat)]).wt +
        ((vsWZ (vsQD s)).map Val.nat).length +
        (Val.list ([Val.nat 0] ++ (vsWZ (vsQD s)).map Val.nat)).wt + 1) ≤ 10 ^ 6 * S ^ 3 := by
    have w2 := wt_list2_le (.list [.nat 0]) (.list ((vsWZ (vsQD s)).map Val.nat))
    have w1 : (Val.list [.nat 0]).wt ≤ 10 := by decide
    have wz2 := (vsB_wt_vecA hS hs (0 : Fin (vsQD s) → ZMod I.p)).1
    rw [vsQVec_zero] at wz2
    have e1 : (Val.list ((vsWZ (vsQD s)).map Val.nat)).wt = (natList (List.replicate (vsQD s) 0)).wt := rfl
    have e2 : (Val.list ([Val.nat 0] ++ (vsWZ (vsQD s)).map Val.nat)).wt =
      (natList (0 :: List.replicate (vsQD s) 0)).wt := rfl
    have hl : ((vsWZ (vsQD s)).map Val.nat).length.succ ≤ S := by simp [vsWZ]; omega
    have : ((vsWZ (vsQD s)).map Val.nat).length.succ * (60 * S ^ 2 + S + 40) ≤ S * (200 * S ^ 2) :=
      Nat.mul_le_mul hl (by have := Nat.le_self_pow (n := 2) (by norm_num) S
                            have := Nat.one_le_pow 2 S hS1; omega)
    have e3 : S * (200 * S ^ 2) = 200 * S ^ 3 := by ring
    have hlen : ((vsWZ (vsQD s)).map Val.nat).length ≤ S := by simp [vsWZ]; omega
    simp only [loopModK]
    calc 1000 * _ * _ ≤ 1000 * (((vsWZ (vsQD s)).map Val.nat).length.succ * (60 * S ^ 2 + S + 40)) := by
          rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; omega
      _ ≤ _ := by omega
  have dap := Det.call (Det.mk2 (Det.mk1 (Det.nat (P := P) (env := lc :: rest) 0)) dz)
    ((append_spec hap [.nat 0] ((vsWZ (vsQD s)).map Val.nat)).mono fun w c hw =>
      ⟨hw.1, hw.2.trans (hw.1 ▸ kap)⟩)
  have e0 : Val.list ([Val.nat 0] ++ (vsWZ (vsQD s)).map Val.nat) =
      natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p)) := by
    rw [vsQVec_zero]; rfl
  rw [e0] at dap
  have dall := Det.mk3 (Det.mk3 dΓ dfr dx) dp dap
  refine dall.mono ?_
  have wLC := vsQ_wt_LC hS hs
  have elc : lc.wt = (vsQLCV s).wt := rfl
  have wst : stV.wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV, stV])
  have wfr : frV.wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV, frV])
  have wΓ : (vsQGam I).wt < stV.wt := wt_le_wt_list (by simp [stV, vsQStV])
  have wxs : (natList s.x).wt < stV.wt := wt_le_wt_list (by simp [stV, vsQStV])
  have wfr0 : fr0.wt < frV.wt := wt_le_wt_list (by simp [frV, vsWFrVal, fr0])
  have wpv : (Val.nat I.p).wt < fr0.wt := wt_le_wt_list (by simp [fr0])
  have wzv : (natList (vsWZ (vsQD s))).wt < fr0.wt := wt_le_wt_list (by simp [fr0])
  have wc := vsB_wt_ctxB hS hs
  have ec : (Val.list [.list [vsQGam I, frV, natList s.x], .nat I.p,
    natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))]).wt = (vsBCtxB s).wt := rfl
  have w3 := wt_list3_le (vsQGam I) frV (natList s.x)
  have w2 := wt_list2_le (.list [.nat 0]) (natList (vsWZ (vsQD s)))
  have w1 : (Val.list [.nat 0]).wt ≤ 10 := by decide
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3; have := wt_nat_le 4
  have q36 : S ^ 3 ≤ S ^ 6 := hS.pow_le (by omega)
  have q26 : S ^ 2 ≤ S ^ 6 := hS.pow_le (by omega)
  have eZ : (natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))).wt =
    (natList (0 :: List.replicate (vsQD s) 0)).wt := by rw [vsQVec_zero]
  omega

end

/-- The program layout that the preparation needs. -/
structure VsBPrepAt (P : Program) (hps : PointwiseStab) (hm : Membership) (f unit appd rng chA chB co lin
    sotA sotB bA bB phi jp jm : ℕ) : Prop where
  f0 : P.funs[f]? = some (vsBPrepE unit appd rng chA chB co lin)
  unit : P.HasAt unit (vsUnitFuns unit)
  appd : P.HasAt appd (appendFuns appd)
  rng : P.HasAt rng (rangeFuns rng)
  chA : P.HasAt chA (vsBChainFuns chA (sotA + 22))
  chB : P.HasAt chB (vsBChainFuns chB (sotB + 22))
  sotA : P.HasAt sotA (vsQSotFuns sotA (bA + 1) jp jm)
  sotB : P.HasAt sotB (vsQSotFuns sotB bB jp jm)
  bA : P.HasAt bA (vsBAFuns bA phi)
  bB : P.HasAt bB (vsBBFuns bB phi)
  co : P.HasAt co (vsWCoFuns co)
  lin : P.HasAt lin (vsLinFuns lin)
  jp : P.prims[jp]? = some (pointwiseStabPrim hps)
  jm : P.prims[jm]? = some (membershipPrim hm)

set_option maxHeartbeats 8000000 in
/-- **The preparation of the field line.** -/
theorem vsBPrep_spec (hps : PointwiseStab) (hm : Membership) {P : Program}
    {f unit appd rng chA chB co lin sotA sotB bA bB phi jp jm Cφ S Tm : ℕ}
    (H : VsBPrepAt P hps hm f unit appd rng chA chB co lin sotA sotB bA bB phi jp jm)
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) (hab : s.Ab) (hD : 1 ≤ vsQD s)
    (hdom : VsBDom s) :
    FunAll P f (vsQLCV s) (fun w c => VsBPrepOut hs hD S w ∧
      c ≤ 100 * vsBChCost hps hm I.n S Cφ + 10 ^ 12 * S ^ 6) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hnS := hS.n
  have hpS := hS.p
  have hdS := hS.d
  have hDd := vsQD_le hs
  set lc := vsQLCV s
  set cA := vsBCtxA s hD
  set cB := vsBCtxB s
  have dcA := vsB_ctxA_det hS hs hD (P := P) H.unit []
  refine FunAll.intro H.f0 (EvalAll.letE dcA fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  have dcB := vsB_ctxB_det hS hs (P := P) H.appd [cA]
  refine EvalAll.letE dcB fun v2 c2 hv2 => ?_
  obtain ⟨rfl, hc2⟩ := hv2
  -- the input of the λ-chain, in the environment `[lc, cA, cB]`
  set E2 := [lc] ++ [cA] ++ [cB]
  have dvA : Det P E2 (.var 1) cA (cA.wt + 1) := Det.var' rfl
  have dst := vsB_lc_arg hS hs (P := P) [cA, cB] 0 (vsQStV I s) rfl
  have dG := Det.get' dst (Det.nat 1) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
    natList s.y][1]? = some (encGroup s.hs) from rfl)
  have dgs := Det.get' dG (Det.nat 1) (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][1]? =
    some (.list ((1 :: s.hs).map encPerm)) from rfl)
  have dn := Det.get' dvA (Det.nat 4) (show [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
    natList (List.replicate (vsQD s) 0), .nat I.n, natList (vsQVec (vsBe0 s hD))][4]? = some (.nat I.n) from rfl)
  have de0 := Det.get' dvA (Det.nat 5) (show [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
    natList (List.replicate (vsQD s) 0), .nat I.n, natList (vsQVec (vsBe0 s hD))][5]? =
      some (natList (vsQVec (vsBe0 s hD))) from rfl)
  obtain ⟨cNA, dNA, hcNA⟩ : ∃ c, Det P E2 (.ite (.arith .lt (.get (.var 1) (.nat 4)) (.nat 2)) (.nat 1)
      (.arith .sub (.get (.var 1) (.nat 4)) (.nat 1))) (.nat (max I.n 2 - 1)) c ∧
      c ≤ 3 * cA.wt + 3 * I.n + 100 := by
    have wnv : (Val.nat I.n).wt < cA.wt := wt_le_wt_list (by simp [cA, vsBCtxA])
    have := wt_nat_le I.n; have := wt_nat_le 1; have := wt_nat_le (I.n - 1)
    have := wt_nat_le (max I.n 2 - 1)
    by_cases hn2 : I.n < 2
    · have dlt := Det.arith' (op := .lt) dn (Det.nat 2) (z := 1) (by simp [GI.Machine.BinOp.eval, hn2])
      have e : max I.n 2 - 1 = 1 := by omega
      rw [e]
      exact ⟨_, Det.ite_pos dlt one_ne_zero (Det.nat 1), by omega⟩
    · have dlt := Det.arith' (op := .lt) dn (Det.nat 2) (z := 0) (by simp [GI.Machine.BinOp.eval, hn2])
      have dsub := Det.arith' (op := .sub) dn (Det.nat 1) (z := I.n - 1) rfl
      have e : max I.n 2 - 1 = I.n - 1 := by omega
      rw [e]
      exact ⟨_, Det.ite_zero dlt dsub, by omega⟩
  -- small helpers: range and the key `0 :: v`
  have hrange : ∀ k ≤ S, FunDet P rng (.nat k) (natList (List.range k)) (10 ^ 5 * S ^ 3) := by
    intro k hk
    refine (range_spec H.rng k).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
    obtain ⟨rfl, -⟩ := hw
    have wr : (natList (List.range k)).wt ≤ 5 * (S + 1) ^ 2 :=
      wt_natList_le_sq (fun y hy => (List.mem_range.mp hy).le.trans hk) (by simp [hk])
    have wk := wt_nat_le k
    have q : (S + 1) ^ 2 ≤ 4 * S ^ 2 := by
      have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
      omega
    have hSS := Nat.le_self_pow (n := 2) (by norm_num) S
    have h2 : (k + 1) * ((Val.nat k).wt + k + (natList (List.range k)).wt + 1) ≤ (2 * S) * (30 * S ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (2 * S) * (30 * S ^ 2) = 60 * S ^ 3 := by ring
    simp only [loopModK]
    calc 1000 * (k + 1) * _ = 1000 * ((k + 1) * ((Val.nat k).wt + k + (natList (List.range k)).wt + 1)) := by
          ring
      _ ≤ _ := by omega
  have hcons : ∀ v : Fin (vsQD s) → ZMod I.p, FunDet P appd (.list [.list [.nat 0], natList (vsQVec v)])
      (natList (0 :: vsQVec v)) (10 ^ 6 * S ^ 3) := by
    intro v
    refine (append_spec H.appd [.nat 0] ((vsQVec v).map Val.nat)).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
    obtain ⟨rfl, -⟩ := hw
    have w2 := wt_list2_le (.list [.nat 0]) (.list ((vsQVec v).map Val.nat))
    have w1 : (Val.list [.nat 0]).wt ≤ 10 := by decide
    have wv := vsB_wt_vecA hS hs v
    have e1 : (Val.list ((vsQVec v).map Val.nat)).wt = (natList (vsQVec v)).wt := rfl
    have e2 : (Val.list ([Val.nat 0] ++ (vsQVec v).map Val.nat)).wt = (natList (0 :: vsQVec v)).wt := rfl
    rw [List.length_map, vsQVec_length]
    have hl : (vsQD s).succ ≤ S := by omega
    have : (vsQD s).succ * (60 * S ^ 2 + S + 40) ≤ S * (200 * S ^ 2) :=
      Nat.mul_le_mul hl (by have := Nat.le_self_pow (n := 2) (by norm_num) S
                            have := Nat.one_le_pow 2 S hS1; omega)
    have e3 : S * (200 * S ^ 2) = 200 * S ^ 3 := by ring
    simp only [loopModK]
    calc 1000 * (vsQD s).succ * _ ≤ 1000 * ((vsQD s).succ * (60 * S ^ 2 + S + 40)) := by
          rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; omega
      _ ≤ _ := by omega
  have drng := Det.call dNA (hrange _ (by omega))
  have dkey := Det.call (Det.mk2 (Det.mk1 (Det.nat (P := P) (env := E2) 0)) de0) (hcons (vsBe0 s hD))
  have dB := Det.arith' (op := .add) dn (Det.nat 1) (z := I.n + 1) rfl
  have dinA := Det.mk6' dvA dgs drng dkey dB dn
  have einA : Val.list [cA, .list ((1 :: s.hs).map encPerm), natList (List.range (max I.n 2 - 1)),
      natList (0 :: vsQVec (vsBe0 s hD)), .nat (I.n + 1), .nat I.n] =
      vsBChainIn cA (1 :: s.hs) (vsBPs I.n) vsQVec (vsBe0 s hD) (I.n + 1) := rfl
  rw [einA] at dinA
  -- the λ-chain
  have hpsA : (vsBPs I.n).length ≤ S := by simp [vsBPs]; omega
  have hglA : (1 :: s.hs).length ≤ I.n ^ 2 + 2 := by simp; have := hs.hsl; omega
  have hS2A := vsB_S2 hS (Gl := I.n ^ 2 + 2) le_rfl
  have hK0 : genGroup (1 :: s.hs) ≤ gens s.hs := le_of_eq (vsB_genGroup_cons s.hs)
  have chA := vsBChain_spec hps hm H.chA H.sotA H.jp H.jm (K₀ := gens s.hs) (α := vsBAp s)
    (keyY := vsQVec) (y₀ := vsBe0 s hD) (ctx := cA) (ps := vsBPs I.n) (gs₀ := 1 :: s.hs)
    (S := vsBS2 S) (A := Cφ + 10 ^ 18 * S ^ 7) (B := I.n + 1) (Gl := I.n ^ 2 + 2)
    (fun q _ => vsBAq_act hs hab (q + 2)) hK0 hglA (by omega) (by omega) hS2A.1
    (by unfold vsBS2; have := Nat.le_self_pow (n := 3) (by norm_num) S; omega)
    (fun q hq gs hgs hgl => vsB_sotHypA hphi hS hs H.bA hab hD hdom hq hgs hgl)
  have wcA := vsB_wt_ctxA hS hs hD
  have wcB := vsB_wt_ctxB hS hs
  have winA : (vsBChainIn cA (1 :: s.hs) (vsBPs I.n) vsQVec (vsBe0 s hD) (I.n + 1)).wt ≤ 10 ^ 8 * S ^ 6 := by
    have w := wt_list_le [cA, .list ((1 :: s.hs).map encPerm), .list ((vsBPs I.n).map Val.nat),
      natList (0 :: vsQVec (vsBe0 s hD)), .nat (I.n + 1), .nat I.n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at w
    have wg := vsB_wt_gens hS hglA
    have wr : (Val.list ((vsBPs I.n).map Val.nat)).wt ≤ 5 * (S + 1) ^ 2 :=
      wt_natList_le_sq (xs := vsBPs I.n) (fun y hy => by simp [vsBPs] at hy; omega) (by simp [vsBPs]; omega)
    have wk := (vsB_wt_vecA hS hs (vsBe0 s hD)).2
    have := wt_nat_le (I.n + 1); have := wt_nat_le I.n
    have q : (S + 1) ^ 2 ≤ 4 * S ^ 6 := by
      have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h2 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
      have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
      omega
    have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have q16 : S ≤ S ^ 6 := Nat.le_self_pow (by norm_num) _
    have e1 : (Val.list (encPerm 1 :: s.hs.map encPerm)).wt = (Val.list ((1 :: s.hs).map encPerm)).wt := rfl
    have e2 : cA.wt = (vsBCtxA s hD).wt := rfl
    have e3 : (Val.list [cA, .list (encPerm 1 :: s.hs.map encPerm), .list ((vsBPs I.n).map Val.nat),
      natList (0 :: vsQVec (vsBe0 s hD)), .nat (I.n + 1), .nat I.n]).wt =
      (Val.list [cA, .list ((1 :: s.hs).map encPerm), .list ((vsBPs I.n).map Val.nat),
      natList (0 :: vsQVec (vsBe0 s hD)), .nat (I.n + 1), .nat I.n]).wt := rfl
    show (Val.list [cA, .list ((1 :: s.hs).map encPerm), .list ((vsBPs I.n).map Val.nat),
      natList (0 :: vsQVec (vsBe0 s hD)), .nat (I.n + 1), .nat I.n]).wt ≤ _
    omega
  refine EvalAll.letE (Ra := fun w c => ∃ (gsA : List (Perm (Fin I.n)))
      (LsA : List (List ((Fin (vsQD s) → ZMod I.p) × Perm (Fin I.n)))),
      w = .list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))] ∧
      LsA.length = (vsBPs I.n).length ∧
      (genGroup gsA : Set (Perm (Fin I.n))) =
        vsBKs (vsBAp s) (vsBe0 s hD) (genGroup (1 :: s.hs) : Set (Perm (Fin I.n))) (vsBPs I.n) ∧
      gsA.length ≤ I.n ^ 2 + 2 ∧
      (∀ i (hi : i < LsA.length), VsBOrbL (vsBAp s ((vsBPs I.n).getD i 0))
        (vsBKs (vsBAp s) (vsBe0 s hD) (genGroup (1 :: s.hs) : Set (Perm (Fin I.n))) ((vsBPs I.n).take i))
        (vsBe0 s hD) LsA[i]) ∧ (∀ L ∈ LsA, VsBPW (vsBS2 S) vsQVec L) ∧
      c ≤ 2 * vsBChCost hps hm I.n S Cφ + 10 ^ 11 * S ^ 6)
    (EvalAll.call_funAll dinA fun v ca hv => ?_) fun v3 c3 hv3 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine chA.mono fun w c hw => ?_
    obtain ⟨gsA, LsA, rfl, hl, hG, hgl, hO, hW, hc⟩ := hw
    refine ⟨gsA, LsA, rfl, hl, hG, hgl, hO, hW, ?_⟩
    have := vsB_chain_cost_le hps hm (n := I.n) (Cφ := Cφ) (A := Cφ + 10 ^ 18 * S ^ 7) le_rfl hpsA winA
    have wo := vsB_chain_out_wt hps hm (Cφ := Cφ) hS1 (vsB_wt_gens hS hgl) (by omega) hW
    have wLC := vsQ_wt_LC hS hs
    have elc : lc.wt = (vsQLCV s).wt := rfl
    have wst : (vsQStV I s).wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV])
    have wGs : (encGroup s.hs).wt < (vsQStV I s).wt := wt_le_wt_list (by simp [vsQStV])
    have wgl : (Val.list ((1 :: s.hs).map encPerm)).wt < (encGroup s.hs).wt :=
      wt_le_wt_list (by simp [encGroup, encPerms])
    have wE2 := wt_list3_le lc cA cB
    have eE2 : (Val.list E2).wt = (Val.list [lc, cA, cB]).wt := rfl
    have ecA : cA.wt = (vsBCtxA s hD).wt := rfl
    have ecB : cB.wt = (vsBCtxB s).wt := rfl
    have wn := wt_nat_le I.n; have wn1 := wt_nat_le (I.n + 1); have := wt_nat_le (I.n - 1)
    have := wt_nat_le (max I.n 2 - 1)
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 4; have := wt_nat_le 5
    have wnv : (Val.nat I.n).wt < cA.wt := wt_le_wt_list (by simp [cA, vsBCtxA])
    have wev : (natList (vsQVec (vsBe0 s hD))).wt < cA.wt := wt_le_wt_list (by simp [cA, vsBCtxA])
    have wk := (vsB_wt_vecA hS hs (vsBe0 s hD)).2
    have wr : (natList (List.range (max I.n 2 - 1))).wt ≤ 5 * (S + 1) ^ 2 :=
      wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp; omega)
    have q : (S + 1) ^ 2 ≤ 4 * S ^ 6 := by
      have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h2 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
      have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
      omega
    have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have w2k := wt_list2_le (.list [.nat 0]) (natList (vsQVec (vsBe0 s hD)))
    have w1 : (Val.list [.nat 0]).wt ≤ 10 := by decide
    have einw : (Val.list [cA, .list ((1 :: s.hs).map encPerm), natList (List.range (max I.n 2 - 1)),
      natList (0 :: vsQVec (vsBe0 s hD)), .nat (I.n + 1), .nat I.n]).wt =
      (vsBChainIn cA (1 :: s.hs) (vsBPs I.n) vsQVec (vsBe0 s hD) (I.n + 1)).wt := rfl
    have t2 : c ≤ vsBChCost hps hm I.n S Cφ := by omega
    have t3 : ca ≤ 10 ^ 10 * S ^ 6 := by
      have wnv' : (Val.nat I.n).wt ≤ I.n + 2 := wt_nat_le _
      have wv1 : (Val.list [Val.nat 0]).wt ≤ 10 := by decide
      have wLC' : lc.wt ≤ 10 ^ 6 * S ^ 6 := wLC
      have hwin : (vsBChainIn cA (1 :: s.hs) (vsBPs I.n) vsQVec (vsBe0 s hD) (I.n + 1)).wt ≤
        10 ^ 8 * S ^ 6 := winA
      have wm := (vsB_wt_vecA hS hs (vsBe0 s hD)).1
      have wcA' : cA.wt ≤ 10 ^ 6 * S ^ 3 := wcA
      have wLC2 : (vsQLCV s).wt ≤ 10 ^ 6 * S ^ 6 := wLC
      have q16 : S ≤ S ^ 6 := Nat.le_self_pow (by norm_num) _
      have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
      clear * - q16 q26 hca wcA' wLC' wLC2 wGs wst wgl hcNA wr q wk w2k wv1 hwin q36 hnS hS1 wnv' wm
      omega
    omega
  obtain ⟨gsA, LsA, rfl, hlA, hGA, hglA', hOA, hWA, hc3⟩ := hv3
  have hGA' : (genGroup gsA : Set (Perm (Fin I.n))) = vsBH1 hs := by
    rw [hGA, vsB_genGroup_cons, ← vsB_KsA hs hD hdom]
  set chAv := Val.list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))]
  set E3 := E2 ++ [chAv]
  -- the input of the translation chain
  have dvB : Det P E3 (.var 2) cB (cB.wt + 1) := Det.var' rfl
  have dvA3 : Det P E3 (.var 1) cA (cA.wt + 1) := Det.var' rfl
  have dgsA := Det.get' (Det.var' (P := P) (env := E3) (i := 3) rfl) (Det.nat 0)
    (show [Val.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))][0]? =
      some (.list (gsA.map encPerm)) from rfl)
  have dD3 := vsB_lc_arg hS hs (P := P) [cA, cB, chAv] 2 (.nat (vsQD s)) rfl
  have drD := Det.call dD3 (hrange (vsQD s) (by omega))
  have dk0 := Det.mk2 (Det.nat (P := P) (env := E3) 0) (Det.nat (P := P) (env := E3) 0)
  have dp3 := Det.get' dvB (Det.nat 1) (show [Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x],
    .nat I.p, natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))][1]? = some (.nat I.p) from rfl)
  have dn3 := Det.get' dvA3 (Det.nat 4) (show [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
    natList (List.replicate (vsQD s) 0), .nat I.n, natList (vsQVec (vsBe0 s hD))][4]? = some (.nat I.n) from rfl)
  have dinB := Det.mk6' dvB dgsA drD dk0 dp3 dn3
  have einB : Val.list [cB, .list (gsA.map encPerm), natList (List.range (vsQD s)), .list [.nat 0, .nat 0],
      .nat I.p, .nat I.n] = vsBChainIn cB gsA (List.range (vsQD s)) vsBKeyB (0 : ZMod I.p) I.p := by
    simp [vsBChainIn, vsBKeyB, natList]
  rw [einB] at dinB
  have hKB : genGroup gsA ≤ vsBH1 hs := fun g hg => by
    have : g ∈ (genGroup gsA : Set (Perm (Fin I.n))) := hg
    rw [hGA'] at this; exact this
  have chBs := vsBChain_spec hps hm H.chB H.sotB H.jp H.jm (K₀ := vsBH1 hs) (α := vsBAj s)
    (keyY := vsBKeyB) (y₀ := (0 : ZMod I.p)) (ctx := cB) (ps := List.range (vsQD s)) (gs₀ := gsA)
    (S := vsBS2 S) (A := Cφ + 10 ^ 16 * S ^ 6) (B := I.p) (Gl := I.n ^ 2 + 2)
    (fun j _ => vsBAj_act hs j) hKB hglA' (by omega) (by omega) hS2A.1
    (by unfold vsBS2; have := Nat.le_self_pow (n := 3) (by norm_num) S; simp; omega)
    (fun j hj gs hgs hgl => vsB_sotHypB hphi hS hs H.bB hj hgs hgl)
  have winB : (vsBChainIn cB gsA (List.range (vsQD s)) vsBKeyB (0 : ZMod I.p) I.p).wt ≤ 10 ^ 8 * S ^ 6 := by
    have w := wt_list_le [cB, .list (gsA.map encPerm), .list ((List.range (vsQD s)).map Val.nat),
      natList (0 :: vsBKeyB (0 : ZMod I.p)), .nat I.p, .nat I.n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at w
    have wg := vsB_wt_gens hS hglA'
    have wr : (Val.list ((List.range (vsQD s)).map Val.nat)).wt ≤ 5 * (S + 1) ^ 2 :=
      wt_natList_le_sq (xs := List.range (vsQD s)) (fun y hy => by simp at hy; omega) (by simp; omega)
    have wk : (natList (0 :: vsBKeyB (0 : ZMod I.p))).wt ≤ 20 := by
      simp [vsBKeyB, natList]; decide
    have := wt_nat_le I.p; have := wt_nat_le I.n
    have q : (S + 1) ^ 2 ≤ 4 * S ^ 6 := by
      have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h2 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
      have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
      omega
    have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have q16 : S ≤ S ^ 6 := Nat.le_self_pow (by norm_num) _
    have e2 : cB.wt = (vsBCtxB s).wt := rfl
    have hs1 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
    show (Val.list [cB, .list (gsA.map encPerm), .list ((List.range (vsQD s)).map Val.nat),
      natList (0 :: vsBKeyB (0 : ZMod I.p)), .nat I.p, .nat I.n]).wt ≤ _
    omega
  have hpsB : (List.range (vsQD s)).length ≤ S := by simp; omega
  refine EvalAll.letE (Ra := fun w c => ∃ (gsB : List (Perm (Fin I.n)))
      (LsB : List (List (ZMod I.p × Perm (Fin I.n)))),
      w = .list [.list (gsB.map encPerm), .list (LsB.map (vsQPairs vsBKeyB))] ∧
      LsB.length = (List.range (vsQD s)).length ∧
      (genGroup gsB : Set (Perm (Fin I.n))) =
        vsBKs (vsBAj s) 0 (genGroup gsA : Set (Perm (Fin I.n))) (List.range (vsQD s)) ∧
      gsB.length ≤ I.n ^ 2 + 2 ∧
      (∀ i (hi : i < LsB.length), VsBOrbL (vsBAj s ((List.range (vsQD s)).getD i 0))
        (vsBKs (vsBAj s) 0 (genGroup gsA : Set (Perm (Fin I.n))) ((List.range (vsQD s)).take i)) 0 LsB[i]) ∧
      (∀ L ∈ LsB, VsBPW (vsBS2 S) vsBKeyB L) ∧
      c ≤ 14 * vsBChCost hps hm I.n S Cφ + 10 ^ 11 * S ^ 6)
    (EvalAll.call_funAll dinB fun v ca hv => ?_) fun v4 c4 hv4 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine chBs.mono fun w c hw => ?_
    obtain ⟨gsB, LsB, rfl, hl, hG, hgl, hO, hW, hc⟩ := hw
    refine ⟨gsB, LsB, rfl, hl, hG, hgl, hO, hW, ?_⟩
    have := vsB_chain_cost_le hps hm (n := I.n) (Cφ := Cφ) (A := Cφ + 10 ^ 16 * S ^ 6)
      (by have : S ^ 6 ≤ S ^ 7 := Nat.pow_le_pow_right hS1 (by norm_num); omega) hpsB winB
    have wo := vsB_chain_out_wt hps hm (Cφ := Cφ) hS1 (vsB_wt_gens hS hgl) (by omega) hW
    have t2 : c ≤ vsBChCost hps hm I.n S Cφ := by omega
    have woA := vsB_chain_out_wt hps hm (Cφ := Cφ) hS1 (vsB_wt_gens hS hglA') (by omega) hWA
    have t3 : ca ≤ 10 ^ 10 * S ^ 6 + 10 * vsBChCost hps hm I.n S Cφ := by
      have wv1 : (Val.list [Val.nat 0]).wt ≤ 10 := by decide
      have wLC2 : (vsQLCV s).wt ≤ 10 ^ 6 * S ^ 6 := vsQ_wt_LC hS hs
      have q16 : S ≤ S ^ 6 := Nat.le_self_pow (by norm_num) _
      have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
      have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
      have wcA' : cA.wt ≤ 10 ^ 6 * S ^ 3 := wcA
      have wcB' : cB.wt ≤ 10 ^ 6 * S ^ 3 := wcB
      have hwin : (vsBChainIn cB gsA (List.range (vsQD s)) vsBKeyB (0 : ZMod I.p) I.p).wt ≤
        10 ^ 8 * S ^ 6 := winB
      have wgA : (Val.list (gsA.map encPerm)).wt < chAv.wt := wt_le_wt_list (by simp [chAv])
      have wnv : (Val.nat I.n).wt ≤ I.n + 2 := wt_nat_le _
      have wpv : (Val.nat I.p).wt ≤ I.p + 2 := wt_nat_le _
      have wDv : (Val.nat (vsQD s)).wt ≤ vsQD s + 2 := wt_nat_le _
      have wrD : (natList (List.range (vsQD s))).wt ≤ 5 * (S + 1) ^ 2 :=
        wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp; omega)
      have q : (S + 1) ^ 2 ≤ 4 * S ^ 6 := by
        have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
        omega
      have w00 : (Val.list [Val.nat 0, Val.nat 0]).wt ≤ 20 := by decide
      have echA : chAv.wt = (Val.list [Val.list (List.map encPerm gsA),
        Val.list (List.map (vsQPairs vsQVec) LsA)]).wt := rfl
      have wE3 := wt_list_le E3
      simp only [E3, E2, List.append_assoc, List.singleton_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at wE3
      have einw : (Val.list [cB, .list (gsA.map encPerm), natList (List.range (vsQD s)),
        .list [.nat 0, .nat 0], .nat I.p, .nat I.n]).wt =
        (vsBChainIn cB gsA (List.range (vsQD s)) vsBKeyB (0 : ZMod I.p) I.p).wt := by rw [einB]
      clear * - hca wv1 wLC2 q16 q26 q36 wcA' wcB' hwin wgA wnv wpv wDv wrD q w00 echA woA einw hnS hpS hS1
      omega
    have hs1 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
    omega
  obtain ⟨gsB, LsB, rfl, hlB, hGB, hglB, hOB, hWB, hc4⟩ := hv4
  set chBv := Val.list [.list (gsB.map encPerm), .list (LsB.map (vsQPairs vsBKeyB))]
  set E4 := E3 ++ [chBv]
  -- the target
  have hxf := hs.fx s.x (List.mem_singleton_self _)
  have hyf := hs.fy s.y (List.mem_singleton_self _)
  have dvB4 : Det P E4 (.var 2) cB (cB.wt + 1) := Det.var' rfl
  have dp4 := Det.get' dvB4 (Det.nat 1) (show [Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x],
    .nat I.p, natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))][1]? = some (.nat I.p) from rfl)
  have dst4 := vsB_lc_arg hS hs (P := P) [cA, cB, chAv, chBv] 0 (vsQStV I s) rfl
  have dfr4 := vsB_lc_arg hS hs (P := P) [cA, cB, chAv, chBv] 1 (vsWFrVal I.p I.d s.ws' (vsQCs s)) rfl
  have dy := Det.get' dst4 (Det.nat 5) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
    natList s.y][5]? = some (natList s.y) from rfl)
  have dx := Det.get' dst4 (Det.nat 4) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
    natList s.y][4]? = some (natList s.x) from rfl)
  have dsub4 := Det.arith' (op := .sub) dp4 (Det.nat 1) (z := I.p - 1) rfl
  have dlin := Det.call (Det.snoc (Det.mk4 dp4 (Det.nat 1) dsub4 dy) dx)
    (vsLin_spec H.lin (N := S) (a := 1) (b := I.p - 1) (v := s.y) (u := s.x) I.prime.pos
      (fun y hy => (hyf.1 y hy).le.trans hpS) (fun y hy => (hxf.1 y hy).le.trans hpS)
      (by rw [hyf.2]; omega) (by rw [hxf.2]; omega) (by rw [hyf.2, hxf.2]) hpS (by omega) (by omega))
  have hLf := vsLin_fit (a := 1) (b' := I.p - 1) (u := s.x) I.prime.pos hs.fy
  have dco := Det.call (Det.mk2 dfr4 dlin) (vsWCo_spec H.co (vsQ_frOK hS hs) hLf)
  rw [vsB_target hs] at dco
  refine EvalAll.letE dco fun v5 c5 hv5 => ?_
  obtain ⟨rfl, hc5⟩ := hv5
  set tV := natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))
  set E5 := E4 ++ [tV]
  have dout := Det.vsBmk5 (Det.var' (P := P) (env := E5) (i := 1) rfl) (Det.var' (P := P) (env := E5) (i := 2) rfl)
    (Det.var' (P := P) (env := E5) (i := 3) rfl) (Det.var' (P := P) (env := E5) (i := 4) rfl)
    (Det.var' (P := P) (env := E5) (i := 5) rfl)
  refine dout.post fun c hc => ⟨⟨gsA, LsA, gsB, LsB, rfl, hGA', hglA', hlA, ?_, hWA, ?_, hglB, by simpa using hlB,
    ?_, hWB⟩, ?_⟩
  · intro i hi
    have := hOA i hi
    rwa [vsB_genGroup_cons] at this
  · rw [hGB, hGA', vsB_KsB hs]
  · intro i hi
    have := hOB i hi
    rwa [hGA'] at this
  · have woA := vsB_chain_out_wt hps hm (Cφ := Cφ) hS1 (vsB_wt_gens hS hglA') (by omega) hWA
    have woB := vsB_chain_out_wt hps hm (Cφ := Cφ) hS1 (vsB_wt_gens hS hglB) (by simp at hlB; omega) hWB
    have wLC2 : (vsQLCV s).wt ≤ 10 ^ 6 * S ^ 6 := vsQ_wt_LC hS hs
    have q16 : S ≤ S ^ 6 := Nat.le_self_pow (by norm_num) _
    have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have q46 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have hs1 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
    have wcA' : cA.wt ≤ 10 ^ 6 * S ^ 3 := wcA
    have wcB' : cB.wt ≤ 10 ^ 6 * S ^ 3 := wcB
    have wt5 : tV.wt ≤ 20 * S ^ 2 := (vsB_wt_vecA hS hs _).1
    have wout := wt_list_le [cA, cB, chAv, chBv, tV]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at wout
    have echA : chAv.wt = (Val.list [Val.list (List.map encPerm gsA),
      Val.list (List.map (vsQPairs vsQVec) LsA)]).wt := rfl
    have echB : chBv.wt = (Val.list [Val.list (List.map encPerm gsB),
      Val.list (List.map (vsQPairs vsBKeyB) LsB)]).wt := rfl
    -- the target computation
    have wst : (vsQStV I s).wt < (vsQLCV s).wt := wt_le_wt_list (by simp [vsQLCV])
    have wfr : (vsWFrVal I.p I.d s.ws' (vsQCs s)).wt < (vsQLCV s).wt := wt_le_wt_list (by simp [vsQLCV])
    have wxs : (natList s.x).wt < (vsQStV I s).wt := wt_le_wt_list (by simp [vsQStV])
    have wys : (natList s.y).wt < (vsQStV I s).wt := wt_le_wt_list (by simp [vsQStV])
    have wLin := wt_natList_le_sq (B := S) (xs := vsLin I.p 1 (I.p - 1) s.y s.x)
      (fun y hy => (vsLin_lt I.prime.pos _ _ y hy).le.trans hpS) (by rw [vsLin_length, hyf.2]; omega)
    have hS3 : (S + 1) ^ 3 ≤ 8 * S ^ 3 := by
      have h1 : (S + 1) ^ 3 ≤ (2 * S) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      have e : (2 * S) ^ 3 = 8 * S ^ 3 := by ring
      omega
    have hS4 : (4 * S + 1) ^ 4 ≤ 625 * S ^ 4 := by
      have h1 : (4 * S + 1) ^ 4 ≤ (5 * S) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      have e : (5 * S) ^ 4 = 625 * S ^ 4 := by ring
      omega
    have q2 : (S + 1) ^ 2 ≤ 4 * S ^ 2 := by
      have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
      omega
    have wl5 := wt_list_snoc_le [Val.nat I.p, .nat 1, .nat (I.p - 1), natList s.y] (natList s.x)
    have wl4 := wt_list4_le (.nat I.p) (.nat 1) (.nat (I.p - 1)) (natList s.y)
    have w2c := wt_list2_le (vsWFrVal I.p I.d s.ws' (vsQCs s)) (natList (vsLin I.p 1 (I.p - 1) s.y s.x))
    have := wt_nat_le I.p; have := wt_nat_le (I.p - 1); have := wt_nat_le 1; have := wt_nat_le 0
    have := wt_nat_le 2; have := wt_nat_le 3; have := wt_nat_le 4; have := wt_nat_le 5
    have wE5 := wt_list_le E5
    simp only [E5, E4, E3, E2, List.append_assoc, List.singleton_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at wE5
    have eLin : (vsLinArg I.p 1 (I.p - 1) s.y s.x).wt = (Val.list ([Val.nat I.p, .nat 1, .nat (I.p - 1),
      natList s.y] ++ [natList s.x])).wt := rfl
    have elc : lc.wt = (vsQLCV s).wt := rfl
    have hxy : (vsLinArg I.p 1 (I.p - 1) s.y s.x).wt ≤ 8 * ((vsQStV I s).wt + 10 * S) + 100 := by
      rw [eLin]; omega
    have ecA : cA.wt = (vsBCtxA s hD).wt := rfl
    have ecB : cB.wt = (vsBCtxB s).wt := rfl
    have wpE : (Val.nat I.p).wt ≤ I.p + 2 := wt_nat_le _
    omega
