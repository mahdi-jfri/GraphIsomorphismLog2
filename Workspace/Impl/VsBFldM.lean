import Workspace.Impl.VsBFldPrep
import Workspace.Impl.VsQAnaAb

/-!
# The field line when `T = M'`

* `vsB_descB`: the translation descent finds `k ∈ H₁` with `f(k) = v` for every `v` in `f(H₁)`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The weight bound of the argument of a descent of the field line. -/
def vsBWd (S : ℕ) : ℕ := 10 ^ 3 * S * vsBS2 S ^ 3 + 10 ^ 8 * S ^ 6

/-- The cost bound of a descent of the field line. -/
def vsBDsCost (S Cφ : ℕ) : ℕ :=
  S * (2 * Cφ + 10 ^ 17 * S ^ 7 + 10 ^ 6 * vsBS2 S ^ 4 + permK * S ^ 3 +
    10 ^ 4 * (vsBWd S + 10 ^ 3 * S ^ 6)) +
  loopModK * (S + 1) * (vsBWd S + S + 10 ^ 3 * S ^ 6 + 1)

theorem vsB_wt_Ls {S : ℕ} (hS1 : 1 ≤ S) {Y : Type} {keyY : Y → List ℕ} {n : ℕ} {Ls : List (List (Y × Perm (Fin n)))}
    (hl : Ls.length ≤ S) (hW : ∀ L ∈ Ls, VsBPW (vsBS2 S) keyY L) :
    (Val.list (Ls.map (vsQPairs keyY))).wt ≤ 100 * S * vsBS2 S ^ 3 + 4 := by
  have h1 := GI.Lang.wt_list_le_of (Ls.map (vsQPairs keyY)) (c := 40 * vsBS2 S ^ 3) (by
    intro v hv; obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hv; exact (hW L hL).2.1)
  rw [List.length_map] at h1
  have h2 : Ls.length * (2 * (40 * vsBS2 S ^ 3) + 1) ≤ S * (81 * vsBS2 S ^ 3 + 1) :=
    Nat.mul_le_mul hl (by omega)
  have e : S * (81 * vsBS2 S ^ 3 + 1) = 81 * (S * vsBS2 S ^ 3) + S := by ring
  have e2 : 100 * S * vsBS2 S ^ 3 = 100 * (S * vsBS2 S ^ 3) := by ring
  have hQ : 1 ≤ vsBS2 S ^ 3 := Nat.one_le_pow _ _ (by unfold vsBS2; have := Nat.one_le_pow 3 S hS1; omega)
  have h3 : S ≤ S * vsBS2 S ^ 3 := Nat.le_mul_of_pos_right _ hQ
  omega

set_option maxHeartbeats 4000000 in
/-- **The translation descent.** -/
theorem vsB_descB {P : Program} {dB bB sotB cmp phi jp jm Cφ S Tm : ℕ}
    (hds : P.HasAt dB (vsBDescFuns dB (bB + 1) (sotB + 8) (bB + 2) cmp))
    (hsot : P.HasAt sotB (vsQSotFuns sotB bB jp jm)) (hcmp : P.HasAt cmp (composeFuns cmp))
    (hB : P.HasAt bB (vsBBFuns bB phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {LsB : List (List (ZMod I.p × Perm (Fin I.n)))} (hl : LsB.length = vsQD s)
    (hO : ∀ i (hi : i < LsB.length), VsBOrbL (vsBAj s ((List.range (vsQD s)).getD i 0))
      (vsBKs (vsBAj s) 0 (vsBH1 hs : Set (Perm (Fin I.n))) ((List.range (vsQD s)).take i)) 0 LsB[i])
    (hW : ∀ L ∈ LsB, VsBPW (vsBS2 S) vsBKeyB L) {v : Fin (vsQD s) → ZMod I.p}
    (hex : ∃ k ∈ vsBH1 hs, vsBAlpha s k 0 = v) :
    FunAll P dB (vsBDescIn (vsBCtxB s) (List.range (vsQD s)) vsBKeyB LsB
      (fun u => natList (vsQVec (Multiplicative.toAdd u))) (Multiplicative.ofAdd v))
      (fun w c => ∃ (τm : Multiplicative (Fin (vsQD s) → ZMod I.p)) (prod : Perm (Fin I.n)),
        w = .list [.nat 1, natList (vsQVec (Multiplicative.toAdd τm)), encPerm prod] ∧
        prod ∈ vsBH1 hs ∧ vsBAlpha s prod 0 = v ∧ c ≤ vsBDsCost S Cφ) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  have hnS := hS.n
  have hQ1 : 1 ≤ vsBS2 S := by unfold vsBS2; have := Nat.one_le_pow 3 S hS1; omega
  have hSQ : S ≤ vsBS2 S := by unfold vsBS2; have := Nat.le_self_pow (n := 3) (by norm_num) S; omega
  have H := vsB_descHypB hs
  have hT : ∀ q ∈ List.range (vsQD s), ∀ τ', (natList (0 :: vsBKeyB (vsBTj s q τ'))).wt ≤ vsBS2 S := by
    intro q _ τ'
    have := wt_natList_le_sq (B := S) (xs := 0 :: vsBKeyB (vsBTj s q τ')) (fun z hz => by
      simp only [vsBKeyB, List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl
      · omega
      · exact (ZMod.val_lt _).le.trans hS.p) (by simp [vsBKeyB]; have := I.prime.two_le; have := hS.p; omega)
    have : (S + 1) ^ 2 ≤ 4 * S ^ 3 := by
      have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
      have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
      omega
    unfold vsBS2; omega
  have hWe : ∀ τ' : Multiplicative (Fin (vsQD s) → ZMod I.p),
      (natList (vsQVec (Multiplicative.toAdd τ'))).wt ≤ 20 * S ^ 2 := fun τ' =>
    (vsB_wt_vecA hS hs _).1
  have hds' := vsBDesc_spec hds hsot hcmp H vsBKeyB_injective (ctx := vsBCtxB s)
    (enc := fun u => natList (vsQVec (Multiplicative.toAdd u))) (by rw [hl]; simp) hO hQ1 hW hWe hT
    (Ctk := 10 ^ 8 * S ^ 3)
    (fun q hq τ' => (vsB_tkB_spec hB (List.mem_range.mp hq) τ').mono (by
      have w := wt_list3_le (vsBCtxB s) (.nat q) (natList (vsQVec (Multiplicative.toAdd τ')))
      have := vsB_wt_ctxB hS hs; have := hWe τ'; have := wt_nat_le q
      have : q < vsQD s := List.mem_range.mp hq
      have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
      have h13 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
      omega))
    (Cup := Cφ + 10 ^ 16 * S ^ 6)
    (fun τ' t ht => vsB_upB_spec hB hphi hS hs τ' ((vsBH1_le hs) ht)) (Multiplicative.ofAdd v)
  refine hds'.mono fun w c hw => ?_
  obtain ⟨⟨ok, τm, prod, rfl, hok⟩, hc⟩ := hw
  rcases hok with ⟨rfl, hp, hpe⟩ | ⟨rfl, hno⟩
  · refine ⟨τm, prod, rfl, hp, ?_, ?_⟩
    · have := congrArg Multiplicative.toAdd hpe
      simpa [vsBPsiB] using this
    · have wa : (vsBDescIn (vsBCtxB s) (List.range (vsQD s)) vsBKeyB LsB
          (fun u => natList (vsQVec (Multiplicative.toAdd u))) (Multiplicative.ofAdd v)).wt ≤ vsBWd S := by
        have w := wt_list_le [vsBCtxB s, .list ((List.range (vsQD s)).map Val.nat),
          .list (LsB.map (vsQPairs vsBKeyB)), natList (vsQVec (Multiplicative.toAdd (Multiplicative.ofAdd v))),
          encPerm (1 : Perm (Fin I.n))]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
          List.length_nil] at w
        have w1 := vsB_wt_ctxB hS hs
        have w2 : (Val.list ((List.range (vsQD s)).map Val.nat)).wt ≤ 5 * (S + 1) ^ 2 :=
          wt_natList_le_sq (xs := List.range (vsQD s)) (fun y hy => by simp at hy; omega) (by simp; omega)
        have w3 := vsB_wt_Ls hS1 (by omega : LsB.length ≤ S) hW
        have w4 := hWe (Multiplicative.ofAdd v)
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
        have ew : (vsBDescIn (vsBCtxB s) (List.range (vsQD s)) vsBKeyB LsB
            (fun u => natList (vsQVec (Multiplicative.toAdd u))) (Multiplicative.ofAdd v)).wt =
            (Val.list [vsBCtxB s, .list ((List.range (vsQD s)).map Val.nat),
          .list (LsB.map (vsQPairs vsBKeyB)), natList (vsQVec (Multiplicative.toAdd (Multiplicative.ofAdd v))),
          encPerm (1 : Perm (Fin I.n))]).wt := rfl
        have := Nat.one_le_pow 6 S hS1
        omega
      have hlen : (List.range (vsQD s)).length ≤ S := by simp; omega
      have hn3 : (I.n + 1) ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left hnS 3
      have hn2 : (I.n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hnS 2
      have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
      have q36 : S ^ 3 ≤ S ^ 7 := Nat.pow_le_pow_right hS1 (by norm_num)
      have q67 : S ^ 6 ≤ S ^ 7 := Nat.pow_le_pow_right hS1 (by norm_num)
      have h4 : S ^ 4 ≤ vsBS2 S ^ 4 := Nat.pow_le_pow_left hSQ 4
      unfold vsBDsCost
      set Wa := (vsBDescIn (vsBCtxB s) (List.range (vsQD s)) vsBKeyB LsB
          (fun u => natList (vsQVec (Multiplicative.toAdd u))) (Multiplicative.ofAdd v)).wt
      have k1 : (List.range (vsQD s)).length * (10 ^ 8 * S ^ 3 + (Cφ + 10 ^ 16 * S ^ 6) +
          10 ^ 6 * vsBS2 S ^ 4 + permK * (I.n + 1) ^ 3 +
          10 ^ 4 * (Wa + 20 * S ^ 2 + 4 * (I.n + 1) ^ 2 + 20)) ≤
          S * (2 * Cφ + 10 ^ 17 * S ^ 7 + 10 ^ 6 * vsBS2 S ^ 4 + permK * S ^ 3 +
            10 ^ 4 * (vsBWd S + 10 ^ 3 * S ^ 6)) := by
        apply Nat.mul_le_mul hlen
        have : permK * (I.n + 1) ^ 3 ≤ permK * S ^ 3 := Nat.mul_le_mul_left _ hn3
        have := Nat.one_le_pow 6 S hS1
        omega
      have k2 : loopModK * ((List.range (vsQD s)).length + 1) * (Wa + (List.range (vsQD s)).length +
          (2 * (20 * S ^ 2 + 4 * (I.n + 1) ^ 2 + 3) + 7) + 1) ≤
          loopModK * (S + 1) * (vsBWd S + S + 10 ^ 3 * S ^ 6 + 1) := by
        apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
        have := Nat.one_le_pow 6 S hS1
        omega
      omega
  · exfalso
    obtain ⟨k, hk, hkv⟩ := hex
    exact hno ⟨k, hk, by simp [vsBPsiB, hkv]⟩

/-- The context of the corrections: `[ctxB, orbit lists of chain B, 1, [Γ, frame, x], 0 :: 0, range D]`. -/
noncomputable def vsBCtxM (s : VsQSt I) (LsB : List (List (ZMod I.p × Perm (Fin I.n)))) : Val :=
  .list [vsBCtxB s, .list (LsB.map (vsQPairs vsBKeyB)), encPerm (1 : Perm (Fin I.n)),
    .list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x],
    natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p)), natList (List.range (vsQD s))]

/-- The correction of a generator `g`, on `[ctxM, g]`: `g k` with `k ∈ H₁`, `f(k) = f(g⁻¹)`. -/
def vsBCorrE (act tail inv descB cmp : ℕ) : Expr :=
  .letE (.call tail (.call act (mk3 (.get (arg 0) (.nat 3)) (.call inv (arg 1)) (.get (arg 0) (.nat 4)))))
  (.letE (.call descB (vsBmk5 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 5)) (.get (arg 0) (.nat 1))
      (.var 1) (.get (arg 0) (.nat 2))))
    (.call cmp (mk2 (arg 1) (.get (.var 2) (.nat 2)))))

theorem vsB_wt_ctxM {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {LsB : List (List (ZMod I.p × Perm (Fin I.n)))} (hl : LsB.length ≤ S)
    (hW : ∀ L ∈ LsB, VsBPW (vsBS2 S) vsBKeyB L) : (vsBCtxM s LsB).wt ≤ vsBWd S := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have w := wt_list_le [vsBCtxB s, .list (LsB.map (vsQPairs vsBKeyB)), encPerm (1 : Perm (Fin I.n)),
    .list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x],
    natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p)), natList (List.range (vsQD s))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w
  have w1 := vsB_wt_ctxB hS hs
  have wac : (Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x]).wt < (vsBCtxB s).wt :=
    wt_le_wt_list (by simp [vsBCtxB])
  have wz : (natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))).wt < (vsBCtxB s).wt :=
    wt_le_wt_list (by simp [vsBCtxB])
  have w3 := vsB_wt_Ls hS1 hl hW
  have w5 := hS.wt_perm (1 : Perm (Fin I.n))
  have hDd := vsQD_le hs; have := hS.d
  have wr : (natList (List.range (vsQD s))).wt ≤ 5 * (S + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp; omega)
  have q : (S + 1) ^ 2 ≤ 4 * S ^ 6 := by
    have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
    omega
  have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have e3 : 100 * S * vsBS2 S ^ 3 = 100 * (S * vsBS2 S ^ 3) := by ring
  have e4 : 10 ^ 3 * S * vsBS2 S ^ 3 = 1000 * (S * vsBS2 S ^ 3) := by ring
  have := Nat.one_le_pow 6 S hS1
  unfold vsBWd vsBCtxM
  omega

set_option maxHeartbeats 4000000 in
/-- **The correction of a generator.** -/
theorem vsB_corr_spec {P : Program} {cr dB bB sotB cmp phi jp jm Cφ S Tm : ℕ}
    (hcr : P.funs[cr]? = some (vsBCorrE (bB + 3) (bB + 4) (bB + 32) dB cmp))
    (hds : P.HasAt dB (vsBDescFuns dB (bB + 1) (sotB + 8) (bB + 2) cmp))
    (hsot : P.HasAt sotB (vsQSotFuns sotB bB jp jm)) (hcmp : P.HasAt cmp (composeFuns cmp))
    (hB : P.HasAt bB (vsBBFuns bB phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
    {LsB : List (List (ZMod I.p × Perm (Fin I.n)))} (hl : LsB.length = vsQD s)
    (hO : ∀ i (hi : i < LsB.length), VsBOrbL (vsBAj s ((List.range (vsQD s)).getD i 0))
      (vsBKs (vsBAj s) 0 (vsBH1 hs : Set (Perm (Fin I.n))) ((List.range (vsQD s)).take i)) 0 LsB[i])
    (hW : ∀ L ∈ LsB, VsBPW (vsBS2 S) vsBKeyB L)
    (htm : ∀ v, ∃ k ∈ vsBH1 hs, vsBAlpha s k 0 = v) {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    FunAll P cr (.list [vsBCtxM s LsB, encPerm g]) (fun w c => ∃ k ∈ vsBH1 hs,
      vsBAlpha s k 0 = vsBAlpha s g⁻¹ 0 ∧ w = encPerm (g * k) ∧
      c ≤ vsBDsCost S Cφ + Cφ + 200 * vsBWd S + 10 ^ 18 * S ^ 6) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hact : P.HasAt (bB + 3) (vsBActFuns (bB + 3) phi) := hB.block 3 rfl
  have htl : P.HasAt (bB + 4) (linTailFuns (bB + 4)) := hact.block 1 rfl
  have hinv : P.HasAt (bB + 32) (invFuns (bB + 32)) := hact.block 29 rfl
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  set cM := vsBCtxM s LsB
  set ac := Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x]
  set z0 := natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))
  set a := Val.list [cM, encPerm g]
  have lm : ∀ rest k v, [vsBCtxB s, .list (LsB.map (vsQPairs vsBKeyB)), encPerm (1 : Perm (Fin I.n)), ac, z0,
      natList (List.range (vsQD s))][k]? = some v → Det P (a :: rest) (.get (arg 0) (.nat k)) v _ :=
    fun rest k v hv => Det.get' (Det.arg' (P := P) (rest := rest) (vs := [cM, encPerm g]) (j := 0) rfl)
      (Det.nat k) hv
  have g1 := Det.arg' (P := P) (rest := []) (vs := [cM, encPerm g]) (j := 1) rfl
  have dinv := Det.call g1 (inv_spec hinv g)
  have dact := Det.call (Det.mk3 (lm [] 3 ac rfl) dinv (lm [] 4 z0 rfl)) (vsB_f_spec hB hphi hS hs (inv_mem hg))
  have dtl := Det.call dact (linTail_spec htl (.nat 0 :: (vsQVec (vsBAlpha s g⁻¹ 0)).map Val.nat))
  have edrop : Val.list (List.drop 1 (Val.nat 0 :: (vsQVec (vsBAlpha s g⁻¹ 0)).map Val.nat)) =
      natList (vsQVec (vsBAlpha s g⁻¹ 0)) := rfl
  rw [edrop] at dtl
  set fv := natList (vsQVec (vsBAlpha s g⁻¹ 0))
  refine FunAll.intro hcr (EvalAll.letE dtl fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  have din := Det.vsBmk5 (lm [fv] 0 _ rfl) (lm [fv] 5 _ rfl) (lm [fv] 1 _ rfl)
    (Det.var' (P := P) (env := [a, fv]) (i := 1) rfl) (lm [fv] 2 _ rfl)
  have edin : Val.list [vsBCtxB s, natList (List.range (vsQD s)), .list (LsB.map (vsQPairs vsBKeyB)), fv,
      encPerm (1 : Perm (Fin I.n))] = vsBDescIn (vsBCtxB s) (List.range (vsQD s)) vsBKeyB LsB
      (fun u => natList (vsQVec (Multiplicative.toAdd u))) (Multiplicative.ofAdd (vsBAlpha s g⁻¹ 0)) := rfl
  rw [edin] at din
  have hdB := vsB_descB hds hsot hcmp hB hphi hS hs hl hO hW (htm (vsBAlpha s g⁻¹ 0))
  refine EvalAll.letE (Ra := fun w c => ∃ (τm : Multiplicative (Fin (vsQD s) → ZMod I.p))
      (prod : Perm (Fin I.n)),
      w = .list [.nat 1, natList (vsQVec (Multiplicative.toAdd τm)), encPerm prod] ∧
      prod ∈ vsBH1 hs ∧ vsBAlpha s prod 0 = vsBAlpha s g⁻¹ 0 ∧ c ≤ vsBDsCost S Cφ + 100 * vsBWd S + 10 ^ 7 * S ^ 6)
    (EvalAll.call_funAll din fun v ca hv => ?_) fun v2 c2 hv2 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hdB.mono fun w c hw => ?_
    obtain ⟨τm, prod, rfl, hp, hpe, hc⟩ := hw
    refine ⟨τm, prod, rfl, hp, hpe, ?_⟩
    have wcM := vsB_wt_ctxM hS hs (by omega : LsB.length ≤ S) hW
    have ecM : cM.wt = (vsBCtxM s LsB).wt := rfl
    have wcM' : cM.wt ≤ vsBWd S := wcM
    have wg := hS.wt_perm g
    have w2 := wt_list2_le cM (encPerm g)
    have ea : (Val.list [cM, encPerm g]).wt = a.wt := rfl
    have wfv := (vsB_wt_vecA hS hs (vsBAlpha s g⁻¹ 0)).1
    have efv : fv.wt = (natList (vsQVec (vsBAlpha s g⁻¹ 0))).wt := rfl
    have wenv := wt_list2_le a fv
    have wτ := (vsB_wt_vecA hS hs (Multiplicative.toAdd τm)).1
    have wp := hS.wt_perm prod
    have w3 := wt_list3_le (.nat 1) (natList (vsQVec (Multiplicative.toAdd τm))) (encPerm prod)
    have wcB : (vsBCtxB s).wt < cM.wt := wt_le_wt_list (by simp [cM, vsBCtxM])
    have wLs : (Val.list (LsB.map (vsQPairs vsBKeyB))).wt < cM.wt := wt_le_wt_list (by simp [cM, vsBCtxM])
    have w1 : (encPerm (1 : Perm (Fin I.n))).wt < cM.wt := wt_le_wt_list (by simp [cM, vsBCtxM])
    have wrD : (natList (List.range (vsQD s))).wt < cM.wt := wt_le_wt_list (by simp [cM, vsBCtxM])
    have win := wt_list_le [vsBCtxB s, natList (List.range (vsQD s)), .list (LsB.map (vsQPairs vsBKeyB)), fv,
      encPerm (1 : Perm (Fin I.n))]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at win
    have edin2 : (vsBDescIn (vsBCtxB s) (List.range (vsQD s)) vsBKeyB LsB
      (fun u => natList (vsQVec (Multiplicative.toAdd u))) (Multiplicative.ofAdd (vsBAlpha s g⁻¹ 0))).wt =
      (Val.list [vsBCtxB s, natList (List.range (vsQD s)), .list (LsB.map (vsQPairs vsBKeyB)), fv,
      encPerm (1 : Perm (Fin I.n))]).wt := rfl
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 5
    have hn2 : (I.n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hS.n 2
    have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have hs6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
    omega
  · obtain ⟨τm, prod, rfl, hp, hpe, hc2⟩ := hv2
    set r := Val.list [.nat 1, natList (vsQVec (Multiplicative.toAdd τm)), encPerm prod]
    have dpr := Det.get' (Det.var' (P := P) (env := [a, fv, r]) (i := 2) rfl) (Det.nat 2)
      (show [Val.nat 1, natList (vsQVec (Multiplicative.toAdd τm)), encPerm prod][2]? = some (encPerm prod) from rfl)
    have g1' := Det.arg' (P := P) (rest := [fv, r]) (vs := [cM, encPerm g]) (j := 1) rfl
    have dc := Det.call (Det.mk2 g1' dpr) (compose_spec hcmp g prod)
    refine dc.post fun c hc => ⟨prod, hp, hpe, rfl, ?_⟩
    have wcM := vsB_wt_ctxM hS hs (by omega : LsB.length ≤ S) hW
    have wcM' : cM.wt ≤ vsBWd S := wcM
    have wg := hS.wt_perm g
    have wgi := hS.wt_perm g⁻¹
    have wp := hS.wt_perm prod
    have wgp := hS.wt_perm (g * prod)
    have w2 := wt_list2_le cM (encPerm g)
    have ea : (Val.list [cM, encPerm g]).wt = a.wt := rfl
    have wfv := (vsB_wt_vecA hS hs (vsBAlpha s g⁻¹ 0))
    have efv : fv.wt = (natList (vsQVec (vsBAlpha s g⁻¹ 0))).wt := rfl
    have wτ := (vsB_wt_vecA hS hs (Multiplicative.toAdd τm)).1
    have w3 := wt_list3_le (.nat 1) (natList (vsQVec (Multiplicative.toAdd τm))) (encPerm prod)
    have er : r.wt = (Val.list [.nat 1, natList (vsQVec (Multiplicative.toAdd τm)), encPerm prod]).wt := rfl
    have wenv := wt_list3_le a fv r
    have wm2 := wt_list2_le (encPerm g) (encPerm prod)
    have wac : ac.wt < cM.wt := wt_le_wt_list (by simp [cM, vsBCtxM, ac])
    have wz0 : z0.wt < cM.wt := wt_le_wt_list (by simp [cM, vsBCtxM, z0])
    have w3a := wt_list3_le ac (encPerm g⁻¹) z0
    have hlt : linTailCost (Val.list (Val.nat 0 :: (vsQVec (vsBAlpha s g⁻¹ 0)).map Val.nat)).wt ≤ 10 ^ 8 * S ^ 6 := by
      unfold linTailCost
      have e : (Val.list (Val.nat 0 :: (vsQVec (vsBAlpha s g⁻¹ 0)).map Val.nat)).wt =
        (natList (0 :: vsQVec (vsBAlpha s g⁻¹ 0))).wt := rfl
      rw [e]
      have h1 : (natList (0 :: vsQVec (vsBAlpha s g⁻¹ 0))).wt + 1 ≤ 21 * S ^ 2 := by
        have := Nat.one_le_pow 2 S hS1; omega
      have := Nat.pow_le_pow_left h1 3
      have e2 : (21 * S ^ 2) ^ 3 = 9261 * S ^ 6 := by ring
      omega
    have hn4 : invK * (I.n + 1) ^ 4 ≤ 10 ^ 5 * S ^ 4 :=
      Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_left hS.n 4)
    have hn3 : permK * (I.n + 1) ^ 3 ≤ 30000 * S ^ 3 :=
      Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_left hS.n 3)
    have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have q46 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have hs6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
    have := wt_nat_le 4
    have edr : (natList (vsQVec (vsBAlpha s g⁻¹ 0))).wt =
      (Val.list (List.drop 1 (Val.nat 0 :: (vsQVec (vsBAlpha s g⁻¹ 0)).map Val.nat))).wt := rfl
    omega

theorem vsBStab0_eq {s : VsQSt I} (hs : VsQStOK s) :
    vsBStab0 hs = vsQStab (gens s.hs) (vsQSp I s.ws') (vsWV I.p I.d s.x) hs.prob.le hs.prob.invW' := by
  ext g
  rw [mem_vsQStab]
  constructor
  · rintro ⟨hg, h0⟩; exact ⟨hg, (vsBAlpha_zero_eq_zero hs hg).mp h0⟩
  · rintro ⟨hg, h0⟩; exact ⟨hg, (vsBAlpha_zero_eq_zero hs hg).mpr h0⟩

theorem vsB_mem_sol {s : VsQSt I} (hs : VsQStOK s) {h : Perm (Fin I.n)} (hh : h ∈ gens s.hs)
    (hf : vsBAlpha s h 0 = vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)) :
    h ∈ vsQSol I (gens s.hs) (vsQSp I s.ws') (vsWV I.p I.d s.x) (vsWV I.p I.d s.y) :=
  ⟨hh, (vsBAlpha_zero_eq hs hh _ (by
    have := hs.prob.cy; exact this)).mp hf⟩

/-- Pulling a list of permutations out of a relation on encodings. -/
theorem vsB_forall₂_perms {Q : Perm (Fin I.n) → Perm (Fin I.n) → Prop} :
    ∀ {gs : List (Perm (Fin I.n))} {ws : List Val},
      List.Forall₂ (fun x w => ∀ g, x = encPerm g → ∃ c, Q g c ∧ w = encPerm c) (gs.map encPerm) ws →
      ∃ cs : List (Perm (Fin I.n)), ws = cs.map encPerm ∧ List.Forall₂ Q gs cs
  | [], [], _ => ⟨[], rfl, List.Forall₂.nil⟩
  | g :: gs, w :: ws, h => by
    obtain ⟨hgw, hrest⟩ := List.forall₂_cons.mp h
    obtain ⟨c, hc, rfl⟩ := hgw g rfl
    obtain ⟨cs, rfl, hcs⟩ := vsB_forall₂_perms hrest
    exact ⟨c :: cs, rfl, List.Forall₂.cons hc hcs⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem vsB_forall₂_left {α β : Type} {Q : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ Q l m → ∀ a ∈ l, ∃ b ∈ m, Q a b
  | [], [], _ => by simp
  | a :: l, b :: m, h => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.mp h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, h1⟩
    · obtain ⟨y, hy, hq⟩ := vsB_forall₂_left h2 x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hq⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem vsB_forall₂_right {α β : Type} {Q : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ Q l m → ∀ b ∈ m, ∃ a ∈ l, Q a b
  | [], [], _ => by simp
  | a :: l, b :: m, h => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.mp h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, h1⟩
    · obtain ⟨x, hx, hq⟩ := vsB_forall₂_right h2 y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hq⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- `1`, from the local context (the first generator of `encGroup hs`). -/
def vsBOneE : Expr := .get (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 1)) (.nat 0)

/-- The case `T = M'`, on `[lc, prep]`. -/
def vsBCaseME (rng descB mapC appd red : ℕ) : Expr :=
  .letE (mk6 (.get (arg 1) (.nat 1)) (.get (.get (arg 1) (.nat 3)) (.nat 1)) vsBOneE
      (.get (.get (arg 1) (.nat 1)) (.nat 0)) (.get (.get (arg 1) (.nat 1)) (.nat 2))
      (.call rng (.get (arg 0) (.nat 2))))
  (.letE (.call descB (vsBmk5 (.get (.var 1) (.nat 0)) (.get (.var 1) (.nat 5)) (.get (.var 1) (.nat 1))
      (.get (arg 1) (.nat 4)) (.get (.var 1) (.nat 2))))
  (.letE (.call mapC (mk2 (.var 1) (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 1))))
  (.letE (.call appd (mk2 (.call appd (mk2 (mk1 (.get (.var 1) (.nat 2))) (.get (.get (arg 1) (.nat 3)) (.nat 0))))
      (.var 3)))
    (mk2 (.nat 0) (mk3 (.nat 1) (.get (.var 2) (.nat 2))
      (.call red (mk2 (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 0)) (.var 4))))))))

/-- The cost bound of the case `T = M'`. -/
noncomputable def vsBMCost (hm : Membership) (n S Cφ : ℕ) : ℕ :=
  10 * S ^ 2 * (vsBDsCost S Cφ + Cφ + 10 ^ 4 * vsBWd S + 10 ^ 18 * S ^ 6) + reduceCost hm n (4 * S ^ 2)

/-- The program layout that the case `T = M'` needs. -/
structure VsBMAt (P : Program) (hm : Membership) (f rng dB mc cr appd red bB sotB cmp phi jp jm : ℕ) :
    Prop where
  hf : P.funs[f]? = some (vsBCaseME rng dB mc appd red)
  hrng : P.HasAt rng (rangeFuns rng)
  hdB : P.HasAt dB (vsBDescFuns dB (bB + 1) (sotB + 8) (bB + 2) cmp)
  hmc : P.HasAt mc (mapFuns mc cr)
  hcr : P.funs[cr]? = some (vsBCorrE (bB + 3) (bB + 4) (bB + 32) dB cmp)
  happd : P.HasAt appd (appendFuns appd)
  hred : P.HasAt red (reduceFuns red jm)
  hbB : P.HasAt bB (vsBBFuns bB phi)
  hsotB : P.HasAt sotB (vsQSotFuns sotB bB jp jm)
  hcmp : P.HasAt cmp (composeFuns cmp)
  hjm : P.prims[jm]? = some (membershipPrim hm)

set_option maxHeartbeats 8000000 in
/-- **The case `T = M'`.** -/
theorem vsBCaseM_spec (hm : Membership) {P : Program}
    {f rng dB mc cr appd red bB sotB cmp phi jp jm Cφ S Tm : ℕ}
    (H : VsBMAt P hm f rng dB mc cr appd red bB sotB cmp phi jp jm)
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) (hD : 1 ≤ vsQD s) {chA : Val}
    {gsB : List (Perm (Fin I.n))} {LsB : List (List (ZMod I.p × Perm (Fin I.n)))}
    (hGB : (genGroup gsB : Set (Perm (Fin I.n))) = {k | k ∈ vsBH1 hs ∧ vsBAlpha s k 0 = 0})
    (hglB : gsB.length ≤ I.n ^ 2 + 2) (hl : LsB.length = vsQD s)
    (hO : ∀ i (hi : i < LsB.length), VsBOrbL (vsBAj s ((List.range (vsQD s)).getD i 0))
      (vsBKs (vsBAj s) 0 (vsBH1 hs : Set (Perm (Fin I.n))) ((List.range (vsQD s)).take i)) 0 LsB[i])
    (hW : ∀ L ∈ LsB, VsBPW (vsBS2 S) vsBKeyB L)
    (htm : ∀ v, ∃ k ∈ vsBH1 hs, vsBAlpha s k 0 = v) {Wp : ℕ}
    (hWp : (Val.list [vsQLCV s, .list [vsBCtxA s hD, vsBCtxB s, chA,
      .list [.list (gsB.map encPerm), .list (LsB.map (vsQPairs vsBKeyB))],
      natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))]]).wt ≤ Wp) :
    FunAll P f (.list [vsQLCV s, .list [vsBCtxA s hD, vsBCtxB s, chA,
      .list [.list (gsB.map encPerm), .list (LsB.map (vsQPairs vsBKeyB))],
      natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))]])
      (fun w c => ∃ a, w = vsQLeafV a ∧ VsQAnsOK hs.prob a ∧ c ≤ vsBMCost hm I.n S Cφ + 1000 * Wp) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  have hnS := hS.n
  set lc := vsQLCV s
  set t := vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)
  set tV := natList (vsQVec t)
  set chBv := Val.list [.list (gsB.map encPerm), .list (LsB.map (vsQPairs vsBKeyB))]
  set pv := Val.list [vsBCtxA s hD, vsBCtxB s, chA, chBv, tV]
  set a := Val.list [lc, pv]
  have g0 := fun rest => Det.arg' (P := P) (rest := rest) (vs := [lc, pv]) (j := 0) rfl
  have g1 := fun rest => Det.arg' (P := P) (rest := rest) (vs := [lc, pv]) (j := 1) rfl
  have lp : ∀ rest k v, [vsBCtxA s hD, vsBCtxB s, chA, chBv, tV][k]? = some v →
      Det P (a :: rest) (.get (arg 1) (.nat k)) v _ := fun rest k v hv => Det.get' (g1 rest) (Det.nat k) hv
  have dcB := lp [] 1 _ rfl
  have dLs := Det.get' (lp [] 3 _ rfl) (Det.nat 1)
    (show [Val.list (gsB.map encPerm), .list (LsB.map (vsQPairs vsBKeyB))][1]? =
      some (.list (LsB.map (vsQPairs vsBKeyB))) from rfl)
  have dst := Det.get' (g0 []) (Det.nat 0) (show [vsQStV I s, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat (vsQD s),
    vsFMatsVal (vsQMs s)][0]? = some (vsQStV I s) from rfl)
  have dG := Det.get' dst (Det.nat 1) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
    natList s.y][1]? = some (encGroup s.hs) from rfl)
  have dGl := Det.get' dG (Det.nat 1) (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][1]? =
    some (.list ((1 :: s.hs).map encPerm)) from rfl)
  have d1 := Det.get' dGl (Det.nat 0) (show ((1 :: s.hs).map encPerm)[0]? = some (encPerm 1) from rfl)
  have dac := Det.get' dcB (Det.nat 0) (show [Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x],
    .nat I.p, natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))][0]? =
      some (.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x]) from rfl)
  have dz0 := Det.get' dcB (Det.nat 2) (show [Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x],
    .nat I.p, natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))][2]? =
      some (natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))) from rfl)
  have dD := Det.get' (g0 []) (Det.nat 2) (show [vsQStV I s, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat (vsQD s),
    vsFMatsVal (vsQMs s)][2]? = some (.nat (vsQD s)) from rfl)
  have hrange : FunDet P rng (.nat (vsQD s)) (natList (List.range (vsQD s))) (10 ^ 5 * S ^ 3) := by
    refine (range_spec H.hrng (vsQD s)).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
    obtain ⟨rfl, -⟩ := hw
    have wr : (natList (List.range (vsQD s))).wt ≤ 5 * (S + 1) ^ 2 :=
      wt_natList_le_sq (fun y hy => (List.mem_range.mp hy).le.trans (by omega)) (by simp; omega)
    have wk := wt_nat_le (vsQD s)
    have q : (S + 1) ^ 2 ≤ 4 * S ^ 2 := by
      have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
      omega
    have hSS := Nat.le_self_pow (n := 2) (by norm_num) S
    have h2 : (vsQD s + 1) * ((Val.nat (vsQD s)).wt + vsQD s + (natList (List.range (vsQD s))).wt + 1) ≤
        (2 * S) * (30 * S ^ 2) := Nat.mul_le_mul (by omega) (by omega)
    have e : (2 * S) * (30 * S ^ 2) = 60 * S ^ 3 := by ring
    simp only [loopModK]
    calc 1000 * (vsQD s + 1) * _ = 1000 * ((vsQD s + 1) * ((Val.nat (vsQD s)).wt + vsQD s +
          (natList (List.range (vsQD s))).wt + 1)) := by ring
      _ ≤ _ := by omega
  have drng := Det.call dD hrange
  have dM := Det.mk6' dcB dLs d1 dac dz0 drng
  have eM : Val.list [vsBCtxB s, .list (LsB.map (vsQPairs vsBKeyB)), encPerm (1 : Perm (Fin I.n)),
      .list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x],
      natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p)), natList (List.range (vsQD s))] = vsBCtxM s LsB := rfl
  rw [eM] at dM
  set cM := vsBCtxM s LsB
  refine FunAll.intro H.hf (EvalAll.letE dM fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  -- the solution `h₀`
  set E1 := [a, cM]
  have lM : ∀ k v, [vsBCtxB s, .list (LsB.map (vsQPairs vsBKeyB)), encPerm (1 : Perm (Fin I.n)),
      .list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x],
      natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p)), natList (List.range (vsQD s))][k]? = some v →
      Det P E1 (.get (.var 1) (.nat k)) v _ := fun k v hv =>
    Det.get' (Det.var' (P := P) (env := E1) (i := 1) rfl) (Det.nat k) hv
  have din := Det.vsBmk5 (lM 0 _ rfl) (lM 5 _ rfl) (lM 1 _ rfl) (lp [cM] 4 tV rfl) (lM 2 _ rfl)
  have edin : Val.list [vsBCtxB s, natList (List.range (vsQD s)), .list (LsB.map (vsQPairs vsBKeyB)), tV,
      encPerm (1 : Perm (Fin I.n))] = vsBDescIn (vsBCtxB s) (List.range (vsQD s)) vsBKeyB LsB
      (fun u => natList (vsQVec (Multiplicative.toAdd u))) (Multiplicative.ofAdd t) := rfl
  rw [edin] at din
  have hdB := vsB_descB H.hdB H.hsotB H.hcmp H.hbB hphi hS hs hl hO hW (htm t)
  refine EvalAll.letE (Ra := fun w c => ∃ (τm : Multiplicative (Fin (vsQD s) → ZMod I.p))
      (prod : Perm (Fin I.n)),
      w = .list [.nat 1, natList (vsQVec (Multiplicative.toAdd τm)), encPerm prod] ∧
      prod ∈ vsBH1 hs ∧ vsBAlpha s prod 0 = t ∧ c ≤ vsBDsCost S Cφ + 100 * vsBWd S + 100 * Wp + 10 ^ 8 * S ^ 6)
    (EvalAll.call_funAll din fun v ca hv => ?_) fun v2 c2 hv2 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hdB.mono fun w c hw => ?_
    obtain ⟨τm, prod, rfl, hp, hpe, hc⟩ := hw
    refine ⟨τm, prod, rfl, hp, hpe, ?_⟩
    have wcM := vsB_wt_ctxM hS hs (by omega : LsB.length ≤ S) hW
    have wcM' : cM.wt ≤ vsBWd S := wcM
    have ea : (Val.list [lc, pv]).wt = a.wt := rfl
    have wa : a.wt ≤ Wp := hWp
    have wE1 := wt_list2_le a cM
    have wτ := (vsB_wt_vecA hS hs (Multiplicative.toAdd τm)).1
    have wp := hS.wt_perm prod
    have w3 := wt_list3_le (.nat 1) (natList (vsQVec (Multiplicative.toAdd τm))) (encPerm prod)
    have wpv : pv.wt < a.wt := wt_le_wt_list (by simp [a])
    have wtV : tV.wt < pv.wt := wt_le_wt_list (by simp [pv])
    have wcB : (vsBCtxB s).wt < cM.wt := wt_le_wt_list (by simp [cM, vsBCtxM])
    have wLs : (Val.list (LsB.map (vsQPairs vsBKeyB))).wt < cM.wt := wt_le_wt_list (by simp [cM, vsBCtxM])
    have w1 : (encPerm (1 : Perm (Fin I.n))).wt < cM.wt := wt_le_wt_list (by simp [cM, vsBCtxM])
    have wrD : (natList (List.range (vsQD s))).wt < cM.wt := wt_le_wt_list (by simp [cM, vsBCtxM])
    have win := wt_list_le [vsBCtxB s, natList (List.range (vsQD s)), .list (LsB.map (vsQPairs vsBKeyB)), tV,
      encPerm (1 : Perm (Fin I.n))]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at win
    have edin2 : (vsBDescIn (vsBCtxB s) (List.range (vsQD s)) vsBKeyB LsB
      (fun u => natList (vsQVec (Multiplicative.toAdd u))) (Multiplicative.ofAdd t)).wt =
      (Val.list [vsBCtxB s, natList (List.range (vsQD s)), .list (LsB.map (vsQPairs vsBKeyB)), tV,
      encPerm (1 : Perm (Fin I.n))]).wt := rfl
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 4; have := wt_nat_le 5
    have hn2 : (I.n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hS.n 2
    have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have hs6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
    have ecM2 : (Val.list [vsBCtxB s, .list (LsB.map (vsQPairs vsBKeyB)), encPerm (1 : Perm (Fin I.n)),
      .list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x],
      natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p)), natList (List.range (vsQD s))]).wt = cM.wt := rfl
    omega
  obtain ⟨τm, prod, rfl, hp, hpe, hc2⟩ := hv2
  set r0 := Val.list [.nat 1, natList (vsQVec (Multiplicative.toAdd τm)), encPerm prod]
  -- the corrections
  set E2 := [a, cM, r0]
  have hcorr : ∀ x ∈ (1 :: s.hs).map encPerm, FunAll P cr (.list [cM, x]) (fun w c =>
      (∀ g, x = encPerm g → ∃ c', (∃ k ∈ vsBH1 hs, vsBAlpha s k 0 = vsBAlpha s g⁻¹ 0 ∧ c' = g * k) ∧
        w = encPerm c') ∧ c ≤ vsBDsCost S Cφ + Cφ + 200 * vsBWd S + 10 ^ 18 * S ^ 6) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    have hgg : g ∈ gens s.hs := by
      rcases List.mem_cons.mp hg with rfl | hg
      · exact one_mem _
      · exact Subgroup.subset_closure hg
    refine (vsB_corr_spec H.hcr H.hdB H.hsotB H.hcmp H.hbB hphi hS hs hl hO hW htm hgg).mono ?_
    rintro w c ⟨k, hk, hkf, rfl, hc⟩
    refine ⟨fun g' hg' => ?_, hc⟩
    have := encPerm_injective hg'
    subst this
    exact ⟨g * k, ⟨k, hk, hkf, rfl⟩, rfl⟩
  have dGl2 : ∀ rest, Det P (a :: rest) (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 1))
      (.list ((1 :: s.hs).map encPerm)) _ := fun rest =>
    Det.get' (Det.get' (Det.get' (g0 rest) (Det.nat 0) (show [vsQStV I s, vsWFrVal I.p I.d s.ws' (vsQCs s),
      .nat (vsQD s), vsFMatsVal (vsQMs s)][0]? = some (vsQStV I s) from rfl)) (Det.nat 1)
      (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
      natList s.y][1]? = some (encGroup s.hs) from rfl)) (Det.nat 1)
      (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][1]? = some (.list ((1 :: s.hs).map encPerm)) from rfl)
  set Ccr := vsBDsCost S Cφ + Cφ + 200 * vsBWd S + 10 ^ 18 * S ^ 6
  set Q : Perm (Fin I.n) → Perm (Fin I.n) → Prop := fun g c' =>
    ∃ k ∈ vsBH1 hs, vsBAlpha s k 0 = vsBAlpha s g⁻¹ 0 ∧ c' = g * k
  have hmap := map_spec H.hmc (c := cM) (B := fun _ => Ccr) hcorr
  refine EvalAll.letE (Ra := fun w c => ∃ cs : List (Perm (Fin I.n)), w = .list (cs.map encPerm) ∧
      List.Forall₂ Q (1 :: s.hs) cs ∧ c ≤ 2 * S ^ 2 * Ccr + 10 ^ 4 * S ^ 2 * vsBWd S + 100 * Wp)
    (EvalAll.call_funAll (Det.mk2 (Det.var' (P := P) (env := E2) (i := 1) rfl) (dGl2 [cM, r0]))
      fun v ca hv => ?_) fun v3 c3 hv3 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hmap.mono fun w c hw => ?_
    obtain ⟨ws, rfl, hR, hc⟩ := hw
    obtain ⟨cs, rfl, hcs⟩ := vsB_forall₂_perms hR
    refine ⟨cs, rfl, hcs, ?_⟩
    have hcsl : cs.length = s.hs.length + 1 := by have := hcs.length_eq; simp at this; omega
    have hnS2 : I.n ^ 2 + 1 ≤ S ^ 2 := by
      have := Nat.pow_le_pow_left hS.n 2
      have e : (I.n + 1) ^ 2 = I.n ^ 2 + 2 * I.n + 1 := by ring
      omega
    have hhs := hs.hsl
    have wcs := vsB_wt_gens hS (gs := cs) (by omega)
    have wxs := vsB_wt_gens hS (gs := 1 :: s.hs) (by simp; omega)
    have wcM := vsB_wt_ctxM hS hs (by omega : LsB.length ≤ S) hW
    have wcM' : cM.wt ≤ vsBWd S := wcM
    rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
    have w2 := wt_list2_le cM (.list ((1 :: s.hs).map encPerm))
    have hWd : 10 ^ 8 * S ^ 6 ≤ vsBWd S := by unfold vsBWd; omega
    have k1 : (1 :: s.hs).length * Ccr ≤ S ^ 2 * Ccr := Nat.mul_le_mul_right _ (by simp; omega)
    have k2 : mapK * ((1 :: s.hs).length + 1) * ((Val.list [cM, .list ((1 :: s.hs).map encPerm)]).wt +
        (Val.list (cs.map encPerm)).wt + 1) ≤ 1000 * (2 * S ^ 2) * (3 * vsBWd S) := by
      simp only [mapK]
      apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by simp; have := Nat.one_le_pow 2 S hS1; omega))
      have := Nat.one_le_pow 6 S hS1
      clear * - w2 wcs wxs wcM' hWd this
      omega
    have e3 : 1000 * (2 * S ^ 2) * (3 * vsBWd S) = 6000 * (S ^ 2 * vsBWd S) := by ring
    have e4 : 10 ^ 4 * S ^ 2 * vsBWd S = 10 ^ 4 * (S ^ 2 * vsBWd S) := by ring
    have e5 : 2 * S ^ 2 * Ccr = 2 * (S ^ 2 * Ccr) := by ring
    have hCc : vsBWd S ≤ Ccr := by simp only [Ccr]; omega
    have hS2W : vsBWd S ≤ S ^ 2 * vsBWd S := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hS1)
    have hS2C : Ccr ≤ S ^ 2 * Ccr := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hS1)
    have ea : (Val.list [lc, pv]).wt = a.wt := rfl
    have wa : a.wt ≤ Wp := hWp
    have wE2 := wt_list3_le a cM r0
    have wr0 : r0.wt ≤ 1000 * S ^ 2 := by
      have w3 := wt_list3_le (.nat 1) (natList (vsQVec (Multiplicative.toAdd τm))) (encPerm prod)
      have := (vsB_wt_vecA hS hs (Multiplicative.toAdd τm)).1; have := hS.wt_perm prod
      have := wt_nat_le 1
      show (Val.list [.nat 1, natList (vsQVec (Multiplicative.toAdd τm)), encPerm prod]).wt ≤ _
      omega
    have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have wst : (vsQStV I s).wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV])
    have wlc : lc.wt < a.wt := wt_le_wt_list (by simp [a])
    have wGs : (encGroup s.hs).wt < (vsQStV I s).wt := wt_le_wt_list (by simp [vsQStV])
    have wgl : (Val.list ((1 :: s.hs).map encPerm)).wt < (encGroup s.hs).wt :=
      wt_le_wt_list (by simp [encGroup, encPerms])
    have := wt_nat_le 0; have := wt_nat_le 1
    have ef1 : (Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]).wt =
      (vsQStV I s).wt := rfl
    have eg1 : (Val.list [Val.nat I.n, .list ((1 :: s.hs).map encPerm)]).wt = (encGroup s.hs).wt := rfl
    omega
  obtain ⟨cs, rfl, hcs, hc3⟩ := hv3
  set csV := Val.list (cs.map encPerm)
  set E3 := [a, cM, r0, csV]
  have hcsl : cs.length = s.hs.length + 1 := by have := hcs.length_eq; simp at this; omega
  -- the generators
  have d1' := Det.get' (Det.var' (P := P) (env := E3) (i := 1) rfl) (Det.nat 2)
    (show [vsBCtxB s, .list (LsB.map (vsQPairs vsBKeyB)), encPerm (1 : Perm (Fin I.n)),
      .list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x],
      natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p)), natList (List.range (vsQD s))][2]? =
      some (encPerm 1) from rfl)
  have dgsB := Det.get' (lp [cM, r0, csV] 3 _ rfl) (Det.nat 0)
    (show [Val.list (gsB.map encPerm), .list (LsB.map (vsQPairs vsBKeyB))][0]? =
      some (.list (gsB.map encPerm)) from rfl)
  have kapp : ∀ xs ys : List Val, ys.length ≤ 2 * S ^ 2 → (Val.list xs).wt ≤ 1000 * S ^ 6 →
      (Val.list ys).wt ≤ 1000 * S ^ 6 → FunDet P appd (.list [.list xs, .list ys]) (.list (xs ++ ys))
        (10 ^ 9 * S ^ 8) := by
    intro xs ys hyl hxw hyw
    refine (append_spec H.happd xs ys).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
    obtain ⟨rfl, -⟩ := hw
    have w2 := wt_list2_le (.list xs) (.list ys)
    have := wt_list_mono (show xs <+: xs ++ ys from List.prefix_append _ _)
    have h3 : (Val.list (xs ++ ys)).wt ≤ 2 * ((Val.list xs).wt + (Val.list ys).wt) + (xs ++ ys).length + 4 := by
      have := wt_list_le (xs ++ ys)
      have h1 := sum_wt_lt_wt_list xs
      have h2 := sum_wt_lt_wt_list ys
      simp only [List.map_append, List.sum_append] at this
      omega
    have hxl : xs.length < (Val.list xs).wt := length_lt_wt_list xs
    have hl2 : (xs ++ ys).length = xs.length + ys.length := List.length_append
    have hyl' : ys.length + 1 ≤ 3 * S ^ 2 := by have := Nat.one_le_pow 2 S hS1; omega
    have h4 : (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length + (Val.list (xs ++ ys)).wt + 1) ≤
        (3 * S ^ 2) * (10 ^ 4 * S ^ 6) := Nat.mul_le_mul hyl' (by
          have := Nat.pow_le_pow_right hS1 (show 2 ≤ 6 by norm_num); omega)
    have e : (3 * S ^ 2) * (10 ^ 4 * S ^ 6) = 3 * 10 ^ 4 * S ^ 8 := by ring
    simp only [loopModK]
    calc 1000 * (ys.length + 1) * _ = 1000 * ((ys.length + 1) * ((Val.list [.list xs, .list ys]).wt +
          ys.length + (Val.list (xs ++ ys)).wt + 1)) := by ring
      _ ≤ _ := by omega
  have hgB := vsB_wt_gens hS hglB
  have hcsw := vsB_wt_gens hS (gs := cs) (by have := hs.hsl; omega)
  have w1v : (Val.list [encPerm (1 : Perm (Fin I.n))]).wt ≤ 1000 * S ^ 6 := by
    have := wt_list1_le (encPerm (1 : Perm (Fin I.n))); have := hS.wt_perm (1 : Perm (Fin I.n))
    have := Nat.pow_le_pow_right hS1 (show 2 ≤ 6 by norm_num)
    have := Nat.one_le_pow 6 S hS1; omega
  have dL1 := Det.call (Det.mk2 (Det.mk1 d1') dgsB) (kapp [encPerm 1] (gsB.map encPerm)
    (by simp; have := Nat.le_self_pow (n := 2) (by norm_num) S; nlinarith [hS.n]) w1v (by omega))
  have wL1 : (Val.list ([encPerm (1 : Perm (Fin I.n))] ++ gsB.map encPerm)).wt ≤ 1000 * S ^ 6 := by
    have := vsB_wt_gens' hS (gs := 1 :: gsB) (by simp; omega)
    have e : Val.list ([encPerm (1 : Perm (Fin I.n))] ++ gsB.map encPerm) = Val.list ((1 :: gsB).map encPerm) := rfl
    rw [e]; omega
  have dL := Det.call (Det.mk2 dL1 (Det.var' (P := P) (env := E3) (i := 3) rfl))
    (kapp _ (cs.map encPerm) (by
      simp; have := hs.hsl; have : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have := Nat.one_le_pow 2 S hS1; omega) wL1 (by omega))
  have eL : Val.list [.nat I.n, .list ([encPerm (1 : Perm (Fin I.n))] ++ gsB.map encPerm ++ cs.map encPerm)] =
      encGroup (gsB ++ cs) := by simp [encGroup, encPerms]
  set LV := Val.list ([encPerm (1 : Perm (Fin I.n))] ++ gsB.map encPerm ++ cs.map encPerm)
  refine EvalAll.letE dL fun v4 c4 hv4 => ?_
  obtain ⟨rfl, hc4⟩ := hv4
  set E4 := [a, cM, r0, csV, LV]
  have dn := Det.get' (Det.get' (Det.get' (Det.arg' (P := P) (rest := [cM, r0, csV, LV]) (vs := [lc, pv])
    (j := 0) rfl) (Det.nat 0) (show [vsQStV I s, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat (vsQD s),
    vsFMatsVal (vsQMs s)][0]? = some (vsQStV I s) from rfl)) (Det.nat 1)
    (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
      natList s.y][1]? = some (encGroup s.hs) from rfl)) (Det.nat 0)
    (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][0]? = some (.nat I.n) from rfl)
  have dred0 := Det.mk2 dn (Det.var' (P := P) (env := E4) (i := 4) rfl)
  rw [eL] at dred0
  have dred := Det.call dred0 (reduce_spec hm H.hred H.hjm (gsB ++ cs))
  have dh := Det.get' (Det.var' (P := P) (env := E4) (i := 2) rfl) (Det.nat 2)
    (show [Val.nat 1, natList (vsQVec (Multiplicative.toAdd τm)), encPerm prod][2]? = some (encPerm prod) from rfl)
  have dout := Det.mk2 (Det.nat (P := P) (env := E4) 0) (Det.mk3 (Det.nat (P := P) (env := E4) 1) dh dred)
  refine dout.post fun c hc => ⟨some (prod, keepList (gsB ++ cs)), rfl, ?_, ?_⟩
  · refine ⟨vsB_mem_sol hs ((vsBH1_le hs) hp) hpe, ?_, length_keepList_le _⟩
    rw [gens_keepList, ← vsBStab0_eq hs]
    refine vsB_stab_gens hs hGB (fun c hc => ?_) (fun g hg => ?_)
    · obtain ⟨g, hg, k, hk, hkf, rfl⟩ := vsB_forall₂_right hcs c hc
      have hgg : g ∈ gens s.hs := by
        rcases List.mem_cons.mp hg with rfl | hg
        · exact one_mem _
        · exact Subgroup.subset_closure hg
      refine ⟨mul_mem hgg ((vsBH1_le hs) hk), ?_⟩
      rw [vsB_f_mul' hs hgg ((vsBH1_le hs) hk), hkf, ← vsB_f_mul' hs hgg (inv_mem hgg), mul_inv_cancel,
        (vsBAlpha_act hs).one]
    · obtain ⟨c, hc, k, hk, -, rfl⟩ := vsB_forall₂_left hcs g (List.mem_cons_of_mem _ hg)
      exact ⟨g * k, hc, by rwa [inv_mul_cancel_left]⟩
  · have hnS2 : I.n ^ 2 + 1 ≤ S ^ 2 := by
      have := Nat.pow_le_pow_left hS.n 2
      have e : (I.n + 1) ^ 2 = I.n ^ 2 + 2 * I.n + 1 := by ring
      omega
    have hhs := hs.hsl
    have hred := reduceCost_mono hm I.n (show (gsB ++ cs).length ≤ 4 * S ^ 2 by simp; omega)
    have wleaf := vsQLeaf_wt hS (a := some (prod, keepList (gsB ++ cs)))
      (by intro r hr; simp at hr; rw [← hr]; exact length_keepList_le _)
    have eleaf : (vsQLeafV (some (prod, keepList (gsB ++ cs)))).wt =
      (Val.list [.nat 0, .list [.nat 1, encPerm prod, encGroup (keepList (gsB ++ cs))]]).wt := rfl
    have wcM := vsB_wt_ctxM hS hs (by omega : LsB.length ≤ S) hW
    have wcM' : cM.wt ≤ vsBWd S := wcM
    have ea : (Val.list [lc, pv]).wt = a.wt := rfl
    have wa : a.wt ≤ Wp := hWp
    have wr0 : r0.wt ≤ 1000 * S ^ 2 := by
      have w3 := wt_list3_le (.nat 1) (natList (vsQVec (Multiplicative.toAdd τm))) (encPerm prod)
      have := (vsB_wt_vecA hS hs (Multiplicative.toAdd τm)).1; have := hS.wt_perm prod
      have := wt_nat_le 1
      show (Val.list [.nat 1, natList (vsQVec (Multiplicative.toAdd τm)), encPerm prod]).wt ≤ _
      omega
    have wcs := vsB_wt_gens hS (gs := cs) (by omega)
    have wLV : LV.wt ≤ 2000 * S ^ 6 := by
      have e : LV = Val.list ((1 :: (gsB ++ cs)).map encPerm) := by simp [LV]
      rw [e]
      have h1 := wt_list_encPerms_le (1 :: (gsB ++ cs))
      have h3 : ((1 :: (gsB ++ cs)).length + 1) * (I.n + 1) ≤ (6 * S ^ 2) * S :=
        Nat.mul_le_mul (by simp; have := Nat.one_le_pow 2 S hS1; omega) hS.n
      have h4 := Nat.pow_le_pow_left h3 2
      have e2 : ((6 * S ^ 2) * S) ^ 2 = 36 * S ^ 6 := by ring
      omega
    have wE4 := wt_list_le E4
    simp only [E4, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at wE4
    have hWd : 10 ^ 8 * S ^ 6 ≤ vsBWd S := by unfold vsBWd; omega
    have hS2W : vsBWd S ≤ S ^ 2 * vsBWd S := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hS1)
    unfold vsBMCost
    have eM : 10 * S ^ 2 * (vsBDsCost S Cφ + Cφ + 10 ^ 4 * vsBWd S + 10 ^ 18 * S ^ 6) =
        10 * (S ^ 2 * vsBDsCost S Cφ) + 10 * (S ^ 2 * Cφ) + 10 ^ 5 * (S ^ 2 * vsBWd S) + 10 ^ 19 * S ^ 8 := by ring
    have eC : 2 * S ^ 2 * Ccr = 2 * (S ^ 2 * vsBDsCost S Cφ) + 2 * (S ^ 2 * Cφ) + 400 * (S ^ 2 * vsBWd S) +
        2 * 10 ^ 18 * S ^ 8 := by simp only [Ccr]; ring
    have e4 : 10 ^ 4 * S ^ 2 * vsBWd S = 10 ^ 4 * (S ^ 2 * vsBWd S) := by ring
    have hD1 : vsBDsCost S Cφ ≤ S ^ 2 * vsBDsCost S Cφ := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hS1)
    have q68 : S ^ 6 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by norm_num)
    have q28 : S ^ 2 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by norm_num)
    have q38 : S ^ 3 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by norm_num)
    have hs8 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS1
    have wst : (vsQStV I s).wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV])
    have wlc : lc.wt < a.wt := wt_le_wt_list (by simp [a])
    have wpv : pv.wt < a.wt := wt_le_wt_list (by simp [a])
    have wGs : (encGroup s.hs).wt < (vsQStV I s).wt := wt_le_wt_list (by simp [vsQStV])
    have wgl : (Val.list ((1 :: s.hs).map encPerm)).wt < (encGroup s.hs).wt :=
      wt_le_wt_list (by simp [encGroup, encPerms])
    have ef1 : (Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]).wt =
      (vsQStV I s).wt := rfl
    have eg1 : (Val.list [Val.nat I.n, .list ((1 :: s.hs).map encPerm)]).wt = (encGroup s.hs).wt := rfl
    have ecM2 : (Val.list [vsBCtxB s, .list (LsB.map (vsQPairs vsBKeyB)), encPerm (1 : Perm (Fin I.n)),
      .list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x],
      natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p)), natList (List.range (vsQD s))]).wt = cM.wt := rfl
    have wkG := wt_encGroup_le_sq (length_keepList_le (gsB ++ cs))
    have hn6 : (I.n + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left hS.n 6
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3; have := wt_nat_le 4
    have := wt_nat_le 5; have := wt_nat_le I.n
    have w1v' : (Val.list [encPerm (1 : Perm (Fin I.n))]).wt ≤ 1000 * S ^ 6 := w1v
    have wM2 := wt_list2_le (.list [encPerm (1 : Perm (Fin I.n))]) (.list (gsB.map encPerm))
    have wM3 := wt_list2_le (.list ([encPerm (1 : Perm (Fin I.n))] ++ gsB.map encPerm)) csV
    have ecs : csV.wt = (Val.list (cs.map encPerm)).wt := rfl
    have wn2 := wt_list2_le (.nat I.n) LV
    have eG : (encGroup (gsB ++ cs)).wt = (Val.list [.nat I.n, LV]).wt := by rw [← eL]
    have wh := hS.wt_perm prod
    have w3o := wt_list3_le (.nat 1) (encPerm prod) (encGroup (keepList (gsB ++ cs)))
    have w2o := wt_list2_le (.nat 0) (.list [.nat 1, encPerm prod, encGroup (keepList (gsB ++ cs))])
    have wcBp : (vsBCtxB s).wt < pv.wt := wt_le_wt_list (by simp [pv])
    have wchB : chBv.wt < pv.wt := wt_le_wt_list (by simp [pv])
    have wLsB : (Val.list (LsB.map (vsQPairs vsBKeyB))).wt < chBv.wt := wt_le_wt_list (by simp [chBv])
    have wacB : (Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x]).wt < (vsBCtxB s).wt :=
      wt_le_wt_list (by simp [vsBCtxB])
    have wz0B : (natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))).wt < (vsBCtxB s).wt :=
      wt_le_wt_list (by simp [vsBCtxB])
    have wDl : (Val.nat (vsQD s)).wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV])
    have wrD : (natList (List.range (vsQD s))).wt ≤ 5 * (S + 1) ^ 2 :=
      wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp; omega)
    have q2 : (S + 1) ^ 2 ≤ 4 * S ^ 2 := by
      have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
      omega
    have w1p := hS.wt_perm (1 : Perm (Fin I.n))
    have echB : chBv.wt = (Val.list [Val.list (List.map encPerm gsB), Val.list (List.map (vsQPairs vsBKeyB) LsB)]).wt := rfl
    have tk : (Val.list [lc, pv]).wt ≤ Wp := hWp
    have tcM : cM.wt ≤ vsBWd S := wcM
    have tl : (vsBCtxB s).wt ≤ Wp := by omega
    have tst : (vsQStV I s).wt ≤ Wp := by omega
    have tch : (Val.list [Val.list (List.map encPerm gsB), Val.list (List.map (vsQPairs vsBKeyB) LsB)]).wt ≤ Wp := by omega
    have q26' : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have q36' : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have hs6' : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS1
    have tr : (natList (List.range (vsQD s))).wt ≤ 20 * S ^ 6 := by omega
    have t1 : c1 ≤ 30 * Wp + 10 * vsBWd S + 10 ^ 7 * S ^ 6 := by omega
    have t2 : c2 ≤ vsBDsCost S Cφ + 100 * vsBWd S + 100 * Wp + 10 ^ 8 * S ^ 6 := by omega
    have t4 : c4 ≤ 10 ^ 10 * S ^ 8 + 10 * Wp + 10 * vsBWd S := by omega
    have er0 : (Val.list [Val.nat 1, natList (vsQVec (Multiplicative.toAdd τm)), encPerm prod]).wt = r0.wt := rfl
    have t5 : c ≤ reduceCost hm I.n (4 * S ^ 2) + 30 * Wp + 30 * vsBWd S + 10 ^ 9 * S ^ 8 := by
      have tlc : lc.wt ≤ Wp := by omega
      have tst2 : (Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]).wt ≤ Wp := by
        omega
      have tg : (encGroup (keepList (gsB ++ cs))).wt ≤ 320 * S ^ 6 := by omega
      have tle : (vsQLeafV (some (prod, keepList (gsB ++ cs)))).wt ≤ 10 ^ 4 * S ^ 6 := wleaf
      have gn := wt_nat_le I.n; have hnS' := hS.n
      have g0 := wt_nat_le 0; have g1' := wt_nat_le 1
      have q18 : S ≤ S ^ 8 := Nat.le_self_pow (by norm_num) _
      clear * - hc tk tlc tst2 tg tle wLV wr0 er0 hred wh w3o w2o eleaf eG wn2 q68 hs8 hWd eg1 wGs wst wlc gn hnS' g0 g1' q18 q28
      omega
    omega
