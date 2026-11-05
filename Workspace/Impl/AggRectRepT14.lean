module

public import Workspace.Impl.AggRectRepT13

@[expose] public section

/-!
# The concrete representation program

`rcRepF b` is the list of the functions of the representation program, placed at base `b`
(`287` functions; the main function is at `b`). `rcRIdxAt b` is its index layout.

* `rcR_ok_of_hasAt`: the entries of `rcRepF b`, placed at `b`, give `RcROk`.
* `rcR_repSpec_at`: so the main function at `b` meets `RcRepSpec` with the bound
  `rcRB hst hpre`, when PointwiseStab is primitive `0` and Preimage is primitive `2`.
* `length_rcRepF`: the list has `287 ≤ 100000` functions.
-/

namespace GI.Impl

set_option maxRecDepth 100000

open GI.Lang
open GI.Cited (PointwiseStab Preimage)

private theorem rcR_peel {P : Program} {b N n N' : ℕ} {A B : List Expr}
    (h : P.HasAt (b + N) (A ++ B)) (hl : A.length = n) (hN : N + n = N') :
    P.HasAt (b + N) A ∧ P.HasAt (b + N') B := by
  refine ⟨h.left, ?_⟩
  have h2 := h.right
  rw [hl, Nat.add_assoc, hN] at h2
  exact h2

/-- **The index layout** of the representation program at base `b`. -/
def rcRIdxAt (b : ℕ) : RcRIdx where
  gD := b + 1
  rng := b + 30
  fEq := b + 33
  cnt := b + 37
  stab := b + 42
  orb := b + 75
  tup := b + 107
  pre := b + 144
  kr := b + 194
  tl := b + 214
  pe := b + 217
  g0 := b + 2
  g1 := b + 3
  mSnd := b + 230
  mFst := b + 233
  smP := b + 4
  fSm := b + 236
  w1P := b + 5
  fW1 := b + 239
  genF := b + 6
  mGen := b + 242
  grF := b + 7
  mGR := b + 245
  keyP := b + 8
  fKey := b + 248
  keyN := b + 9
  keysP := b + 10
  fKeys := b + 251
  rowF := b + 11
  mRow := b + 254
  rhoF := b + 12
  mRho := b + 257
  psF := b + 13
  mPs := b + 260
  embRF := b + 14
  mEmbR := b + 263
  embF := b + 15
  mEmb := b + 266
  carF := b + 16
  pairF := b + 17
  lk0P := b + 18
  fLk0 := b + 269
  lk1P := b + 19
  fLk1 := b + 272
  lk2P := b + 20
  fLk2 := b + 275
  look := b + 21
  look1 := b + 22
  look2 := b + 23
  piF := b + 24
  mPi := b + 278
  outF := b + 25
  mOut := b + 281
  cellF := b + 26
  mCell := b + 284
  st1 := b + 27
  st2 := b + 28
  st4 := b + 29
  main := b
  jp := 0
  jpre := 2

/-- **The representation program** with base `b`: `287` functions, the main function at
`b`. -/
def rcRepF (b : ℕ) : List Expr :=
  [(rcRIdxAt b).mainF] ++
  ([rcRGetDF] ++
  ([rcRGet0F] ++
  ([rcRGet1F] ++
  ([(rcRIdxAt b).smPF] ++
  ([(rcRIdxAt b).w1PF] ++
  ([(rcRIdxAt b).genFF] ++
  ([rcRGrF] ++
  ([(rcRIdxAt b).keyPF] ++
  ([(rcRIdxAt b).keyNF] ++
  ([(rcRIdxAt b).keysPF] ++
  ([(rcRIdxAt b).rowFF] ++
  ([(rcRIdxAt b).rhoFF] ++
  ([(rcRIdxAt b).psFF] ++
  ([(rcRIdxAt b).embRFF] ++
  ([(rcRIdxAt b).embFF] ++
  ([(rcRIdxAt b).carFF] ++
  ([(rcRIdxAt b).pairFF] ++
  ([(rcRIdxAt b).lk0PF] ++
  ([(rcRIdxAt b).lk1PF] ++
  ([(rcRIdxAt b).lk2PF] ++
  ([(rcRIdxAt b).lookF] ++
  ([(rcRIdxAt b).look1F] ++
  ([(rcRIdxAt b).look2F] ++
  ([(rcRIdxAt b).piFF] ++
  ([(rcRIdxAt b).outFF] ++
  ([(rcRIdxAt b).cellFF] ++
  ([(rcRIdxAt b).st1F] ++
  ([(rcRIdxAt b).st2F] ++
  ([(rcRIdxAt b).st4F] ++
  ((rangeFuns (rcRIdxAt b).rng) ++
  ((findEqFuns (rcRIdxAt b).fEq) ++
  ((countFuns (rcRIdxAt b).cnt) ++
  ((graphStabFuns (rcRIdxAt b).stab (rcRIdxAt b).jp) ++
  ((orbitFuns (rcRIdxAt b).orb) ++
  ((graphTupFuns (rcRIdxAt b).tup) ++
  ((graphPreFuns (rcRIdxAt b).pre (rcRIdxAt b).jpre) ++
  ((krFuns (rcRIdxAt b).kr (rcRIdxAt b).jp) ++
  ((tailFuns (rcRIdxAt b).tl) ++
  ((pEncMapFuns (rcRIdxAt b).pe) ++
  ((mapFuns (rcRIdxAt b).mSnd (rcRIdxAt b).g1) ++
  ((mapFuns (rcRIdxAt b).mFst (rcRIdxAt b).g0) ++
  ((filterFuns (rcRIdxAt b).fSm (rcRIdxAt b).smP) ++
  ((findFuns (rcRIdxAt b).fW1 (rcRIdxAt b).w1P) ++
  ((mapFuns (rcRIdxAt b).mGen (rcRIdxAt b).genF) ++
  ((mapFuns (rcRIdxAt b).mGR (rcRIdxAt b).grF) ++
  ((findFuns (rcRIdxAt b).fKey (rcRIdxAt b).keyP) ++
  ((filterFuns (rcRIdxAt b).fKeys (rcRIdxAt b).keysP) ++
  ((mapFuns (rcRIdxAt b).mRow (rcRIdxAt b).rowF) ++
  ((mapFuns (rcRIdxAt b).mRho (rcRIdxAt b).rhoF) ++
  ((mapFuns (rcRIdxAt b).mPs (rcRIdxAt b).psF) ++
  ((mapFuns (rcRIdxAt b).mEmbR (rcRIdxAt b).embRF) ++
  ((mapFuns (rcRIdxAt b).mEmb (rcRIdxAt b).embF) ++
  ((findFuns (rcRIdxAt b).fLk0 (rcRIdxAt b).lk0P) ++
  ((findFuns (rcRIdxAt b).fLk1 (rcRIdxAt b).lk1P) ++
  ((findFuns (rcRIdxAt b).fLk2 (rcRIdxAt b).lk2P) ++
  ((mapFuns (rcRIdxAt b).mPi (rcRIdxAt b).piF) ++
  ((mapFuns (rcRIdxAt b).mOut (rcRIdxAt b).outF) ++
  ((mapFuns (rcRIdxAt b).mCell (rcRIdxAt b).cellF)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxHeartbeats 4000000 in
/-- **The entries of `rcRepF b`** from its place. -/
theorem rcR_ok_of_hasAt {P : Program} {b : ℕ} (h : P.HasAt b (rcRepF b)) :
    RcROk P (rcRIdxAt b) := by
  have h : P.HasAt (b + 0) (rcRepF b) := h
  unfold rcRepF at h
  obtain ⟨x_main, h⟩ := rcR_peel (N' := 1) h rfl rfl
  obtain ⟨x_gD, h⟩ := rcR_peel (N' := 2) h rfl rfl
  obtain ⟨x_g0, h⟩ := rcR_peel (N' := 3) h rfl rfl
  obtain ⟨x_g1, h⟩ := rcR_peel (N' := 4) h rfl rfl
  obtain ⟨x_smP, h⟩ := rcR_peel (N' := 5) h rfl rfl
  obtain ⟨x_w1P, h⟩ := rcR_peel (N' := 6) h rfl rfl
  obtain ⟨x_genF, h⟩ := rcR_peel (N' := 7) h rfl rfl
  obtain ⟨x_grF, h⟩ := rcR_peel (N' := 8) h rfl rfl
  obtain ⟨x_keyP, h⟩ := rcR_peel (N' := 9) h rfl rfl
  obtain ⟨x_keyN, h⟩ := rcR_peel (N' := 10) h rfl rfl
  obtain ⟨x_keysP, h⟩ := rcR_peel (N' := 11) h rfl rfl
  obtain ⟨x_rowF, h⟩ := rcR_peel (N' := 12) h rfl rfl
  obtain ⟨x_rhoF, h⟩ := rcR_peel (N' := 13) h rfl rfl
  obtain ⟨x_psF, h⟩ := rcR_peel (N' := 14) h rfl rfl
  obtain ⟨x_embRF, h⟩ := rcR_peel (N' := 15) h rfl rfl
  obtain ⟨x_embF, h⟩ := rcR_peel (N' := 16) h rfl rfl
  obtain ⟨x_carF, h⟩ := rcR_peel (N' := 17) h rfl rfl
  obtain ⟨x_pairF, h⟩ := rcR_peel (N' := 18) h rfl rfl
  obtain ⟨x_lk0P, h⟩ := rcR_peel (N' := 19) h rfl rfl
  obtain ⟨x_lk1P, h⟩ := rcR_peel (N' := 20) h rfl rfl
  obtain ⟨x_lk2P, h⟩ := rcR_peel (N' := 21) h rfl rfl
  obtain ⟨x_look, h⟩ := rcR_peel (N' := 22) h rfl rfl
  obtain ⟨x_look1, h⟩ := rcR_peel (N' := 23) h rfl rfl
  obtain ⟨x_look2, h⟩ := rcR_peel (N' := 24) h rfl rfl
  obtain ⟨x_piF, h⟩ := rcR_peel (N' := 25) h rfl rfl
  obtain ⟨x_outF, h⟩ := rcR_peel (N' := 26) h rfl rfl
  obtain ⟨x_cellF, h⟩ := rcR_peel (N' := 27) h rfl rfl
  obtain ⟨x_st1, h⟩ := rcR_peel (N' := 28) h rfl rfl
  obtain ⟨x_st2, h⟩ := rcR_peel (N' := 29) h rfl rfl
  obtain ⟨x_st4, h⟩ := rcR_peel (N' := 30) h rfl rfl
  obtain ⟨x_rng, h⟩ := rcR_peel (N' := 33) h rfl rfl
  obtain ⟨x_fEq, h⟩ := rcR_peel (N' := 37) h rfl rfl
  obtain ⟨x_cnt, h⟩ := rcR_peel (N' := 42) h rfl rfl
  obtain ⟨x_stab, h⟩ := rcR_peel (N' := 75) h rfl rfl
  obtain ⟨x_orb, h⟩ := rcR_peel (N' := 107) h rfl rfl
  obtain ⟨x_tup, h⟩ := rcR_peel (N' := 144) h rfl rfl
  obtain ⟨x_pre, h⟩ := rcR_peel (N' := 194) h rfl rfl
  obtain ⟨x_kr, h⟩ := rcR_peel (N' := 214) h rfl rfl
  obtain ⟨x_tl, h⟩ := rcR_peel (N' := 217) h rfl rfl
  obtain ⟨x_pe, h⟩ := rcR_peel (N' := 230) h rfl rfl
  obtain ⟨x_mSnd, h⟩ := rcR_peel (N' := 233) h rfl rfl
  obtain ⟨x_mFst, h⟩ := rcR_peel (N' := 236) h rfl rfl
  obtain ⟨x_fSm, h⟩ := rcR_peel (N' := 239) h rfl rfl
  obtain ⟨x_fW1, h⟩ := rcR_peel (N' := 242) h rfl rfl
  obtain ⟨x_mGen, h⟩ := rcR_peel (N' := 245) h rfl rfl
  obtain ⟨x_mGR, h⟩ := rcR_peel (N' := 248) h rfl rfl
  obtain ⟨x_fKey, h⟩ := rcR_peel (N' := 251) h rfl rfl
  obtain ⟨x_fKeys, h⟩ := rcR_peel (N' := 254) h rfl rfl
  obtain ⟨x_mRow, h⟩ := rcR_peel (N' := 257) h rfl rfl
  obtain ⟨x_mRho, h⟩ := rcR_peel (N' := 260) h rfl rfl
  obtain ⟨x_mPs, h⟩ := rcR_peel (N' := 263) h rfl rfl
  obtain ⟨x_mEmbR, h⟩ := rcR_peel (N' := 266) h rfl rfl
  obtain ⟨x_mEmb, h⟩ := rcR_peel (N' := 269) h rfl rfl
  obtain ⟨x_fLk0, h⟩ := rcR_peel (N' := 272) h rfl rfl
  obtain ⟨x_fLk1, h⟩ := rcR_peel (N' := 275) h rfl rfl
  obtain ⟨x_fLk2, h⟩ := rcR_peel (N' := 278) h rfl rfl
  obtain ⟨x_mPi, h⟩ := rcR_peel (N' := 281) h rfl rfl
  obtain ⟨x_mOut, h⟩ := rcR_peel (N' := 284) h rfl rfl
  have x_mCell := h
  exact ⟨x_gD.single,
    x_rng,
    x_fEq,
    x_cnt,
    x_stab,
    x_orb,
    x_tup,
    x_pre,
    x_kr,
    x_tl,
    x_pe,
    x_g0.single,
    x_g1.single,
    x_mSnd,
    x_mFst,
    x_smP.single,
    x_fSm,
    x_w1P.single,
    x_fW1,
    x_genF.single,
    x_mGen,
    x_grF.single,
    x_mGR,
    x_keyP.single,
    x_fKey,
    x_keyN.single,
    x_keysP.single,
    x_fKeys,
    x_rowF.single,
    x_mRow,
    x_rhoF.single,
    x_mRho,
    x_psF.single,
    x_mPs,
    x_embRF.single,
    x_mEmbR,
    x_embF.single,
    x_mEmb,
    x_carF.single,
    x_pairF.single,
    x_lk0P.single,
    x_fLk0,
    x_lk1P.single,
    x_fLk1,
    x_lk2P.single,
    x_fLk2,
    x_look.single,
    x_look1.single,
    x_look2.single,
    x_piF.single,
    x_mPi,
    x_outF.single,
    x_mOut,
    x_cellF.single,
    x_mCell,
    x_st1.single,
    x_st2.single,
    x_st4.single,
    x_main.single⟩

theorem length_rcRepF (b : ℕ) : (rcRepF b).length = 287 := rfl

/-- **The representation program at `b` meets its contract.** -/
theorem rcR_repSpec_at {P : Program} {b : ℕ} (h : P.HasAt b (rcRepF b)) (hst : PointwiseStab)
    (hj : P.prims[0]? = some (pointwiseStabPrim hst)) (hpre : Preimage)
    (hjp : P.prims[2]? = some (preimagePrim hpre)) :
    RcRepSpec P b (rcRB hst hpre) :=
  rcR_repSpec (J := rcRIdxAt b) (rcR_ok_of_hasAt h) hst hj hpre hjp

end GI.Impl
