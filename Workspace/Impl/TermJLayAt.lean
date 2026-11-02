import Workspace.Impl.TermJLay

/-!
# The layout facts of the `J`-answer

`tmJLay_at`: if the code `tmJFuns B` sits at `B`, then the top function sits at `tmJA B 0`, the
nonempty case at `tmJA B 1` (`TmJNEAt`) and the per-label program at `tmJPos B` (`TmJHAt`).
-/

namespace GI.Impl

open GI.Lang

private theorem tmJ_get {P : Program} {b : ℕ} {l : List Expr} (h : P.HasAt b l) {j : ℕ}
    {e : Expr} (hj : l[j]? = some e) : P.funs[b + j]? = some e := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hj
  exact h j hlt

private theorem tmJ_blk {P : Program} {B : ℕ} (h : P.HasAt B (tmJFuns B)) (i : ℕ)
    {l : List Expr} (hl : (tmJLay B)[i]? = some l) : P.HasAt (tmJA B i) l :=
  tmJBlk_hasAt h (tmJLay_fit B) hl

/-- **The layout facts of the `J`-answer.** -/
theorem tmJLay_at {P : Program} {B : ℕ} (h : P.HasAt B (tmJFuns B)) :
    P.funs[tmJA B 0]? = some (tmJTopF (tmJA B 1)) ∧
    TmJNEAt P (tmJA B 1) (tmJA B 2) (tmJA B 3) (tmJA B 4) (tmJA B 5) (tmJPos B).b 5 17 10 15 0 ∧
    TmJHAt P (tmJPos B) := by
  have b0 := tmJ_blk h 0 (l := [tmJTopF (tmJA B 1)]) rfl
  have b1 := tmJ_blk h 1 (l := [tmJNEF (tmJA B 2) (tmJA B 3) (tmJA B 4) (tmJA B 5)]) rfl
  have b2 := tmJ_blk h 2 (l := [tmJPrepF (tmJA B 6) (tmJA B 7) (tmJA B 8) (tmJA B 9) (tmJA B 10)
    (tmJA B 11)]) rfl
  have b3 := tmJ_blk h 3 (l := [tmJLabsF (tmJA B 12) (tmJA B 13)]) rfl
  have b4 := tmJ_blk h 4 (l := [tmJAutF (tmJA B 14) (tmJA B 54 + 1) (tmJA B 15) (tmJA B 16)
    (tmJA B 51) (tmJA B 17)]) rfl
  have b5 := tmJ_blk h 5 (l := [tmJOutF (tmJA B 18) (tmJA B 12) (tmJA B 17) (tmJA B 7)
    (tmJA B 19)]) rfl
  have b6 := tmJ_blk h 6 (l := [tmJPrepAF (tmJA B 20) (tmJA B 21) (tmJA B 22) (tmJA B 7)
    (tmJA B 23)]) rfl
  have b7 := tmJ_blk h 7 (l := mkGroupFuns (tmJA B 7)) rfl
  have b8 := tmJ_blk h 8 (l := [tmJLgF (tmJA B 22) (tmJA B 24) (tmJA B 26),
    tmJLgRowF (tmJA B 25), tmJLgEF]) rfl
  have b9 := tmJ_blk h 9 (l := [tmJTlF (tmJA B 22) (tmJA B 27) (tmJA B 26), tmJTlEF]) rfl
  have b10 := tmJ_blk h 10 (l := [tmJBetaF (tmJA B 28) (tmJA B 29), tmJLgPEF]) rfl
  have b11 := tmJ_blk h 11 (l := linAbelianCoordinatesFuns (tmJA B 11) 5 17) rfl
  have b12 := tmJ_blk h 12 (l := mapFuns (tmJA B 12) (tmJA B 30)) rfl
  have b13 := tmJ_blk h 13 (l := mapFuns (tmJA B 13) (tmJA B 39)) rfl
  have b14 := tmJ_blk h 14 (l := [tmJNsF (tmJA B 22) (tmJA B 31) (tmJA B 26),
    tmJNsRowF 10 (tmJA B 32)]) rfl
  have b15 := tmJ_blk h 15 (l := [tmJS2F (tmJA B 33), tmJS2EF (tmJA B 39 + 9)]) rfl
  have b16 := tmJ_blk h 16 (l := [tmJTsF (tmJA B 34), tmJTsEF (tmJA B 51) (tmJA B 30)]) rfl
  have b17 := tmJ_blk h 17 (l := appendFuns (tmJA B 17)) rfl
  have b18 := tmJ_blk h 18 (l := invFuns (tmJA B 18)) rfl
  have b19 := tmJ_blk h 19 (l := redFuns (tmJA B 19) 0) rfl
  have b20 := tmJ_blk h 20 (l := [tmCsTabF (tmJA B 35) (tmJA B 22) (tmJA B 36) (tmJA B 18),
    tmCsTabEF]) rfl
  have b21 := tmJ_blk h 21 (l := [tmJGF (tmJA B 35) (tmJA B 37), tmCsConjF (tmJA B 30)]) rfl
  have b22 := tmJ_blk h 22 (l := rangeFuns (tmJA B 22)) rfl
  have b23 := tmJ_blk h 23 (l := [tmJNqF (tmJA B 22) (tmJA B 38) (tmJA B 26),
    tmJNqRowF (tmJA B 32)]) rfl
  have b24 := tmJ_blk h 24 (l := mapFuns (tmJA B 24) (tmJA B 8 + 1)) rfl
  have b25 := tmJ_blk h 25 (l := mapFuns (tmJA B 25) (tmJA B 8 + 2)) rfl
  have b26 := tmJ_blk h 26 (l := [tmJFlatF (tmJA B 26 + 1)] ++
    foldlFuns (tmJA B 26 + 1) (tmJA B 26 + 4) ++ [tmJFlatStepF (tmJA B 17)]) rfl
  have b27 := tmJ_blk h 27 (l := mapFuns (tmJA B 27) (tmJA B 9 + 1)) rfl
  have b28 := tmJ_blk h 28 (l := mapFuns (tmJA B 28) (tmJA B 10 + 1)) rfl
  have b29 := tmJ_blk h 29 (l := tmJVVecsFuns (tmJA B 29) 17) rfl
  have b30 := tmJ_blk h 30 (l := composeFuns (tmJA B 30)) rfl
  have b31 := tmJ_blk h 31 (l := mapFuns (tmJA B 31) (tmJA B 14 + 1)) rfl
  have b32 := tmJ_blk h 32 (l := mapFuns (tmJA B 32) (tmJA B 49)) rfl
  have b33 := tmJ_blk h 33 (l := mapFuns (tmJA B 33) (tmJA B 15 + 1)) rfl
  have b34 := tmJ_blk h 34 (l := mapFuns (tmJA B 34) (tmJA B 16 + 1)) rfl
  have b35 := tmJ_blk h 35 (l := domFuns (tmJA B 35)) rfl
  have b36 := tmJ_blk h 36 (l := mapFuns (tmJA B 36) (tmJA B 20 + 1)) rfl
  have b37 := tmJ_blk h 37 (l := mapFuns (tmJA B 37) (tmJA B 21 + 1)) rfl
  have b38 := tmJ_blk h 38 (l := mapFuns (tmJA B 38) (tmJA B 23 + 1)) rfl
  have b39 := tmJ_blk h 39 (l := tmJHFuns (tmJPos B)) rfl
  have b40 := tmJ_blk h 40 (l := replicateFuns (tmJA B 40)) rfl
  have b41 := tmJ_blk h 41 (l := [tmJPairF (tmJA B 22) (tmJA B 42), tmJPairEF]) rfl
  have b42 := tmJ_blk h 42 (l := mapFuns (tmJA B 42) (tmJA B 41 + 1)) rfl
  have b43 := tmJ_blk h 43 (l := mapFuns (tmJA B 43) (tmJA B 39 + 4)) rfl
  have b44 := tmJ_blk h 44 (l := mapFuns (tmJA B 44) (tmJA B 39 + 5)) rfl
  have b45 := tmJ_blk h 45 (l := mapFuns (tmJA B 45) (tmJA B 39 + 6)) rfl
  have b46 := tmJ_blk h 46 (l := [linBitsDecodeF (tmJA B 46)]) rfl
  have b47 := tmJ_blk h 47 (l := [linPermPowF (tmJA B 47) (tmJA B 30)]) rfl
  have b48 := tmJ_blk h 48 (l := foldlFuns (tmJA B 48) (tmJA B 39 + 8)) rfl
  have b49 := tmJ_blk h 49 (l := [tmJLocAF (tmJA B 49 + 1) (tmJA B 41),
    tmJDsAF (tmJA B 22) (tmJA B 50), tmJDsAEF]) rfl
  have b50 := tmJ_blk h 50 (l := mapFuns (tmJA B 50) (tmJA B 49 + 2)) rfl
  have b51 := tmJ_blk h 51 (l := [tmJSwSF (tmJA B 18) (tmJA B 52) (tmJA B 53) (tmJA B 41),
    tmJSwDEF, tmJSwPEF]) rfl
  have b52 := tmJ_blk h 52 (l := mapFuns (tmJA B 52) (tmJA B 51 + 1)) rfl
  have b53 := tmJ_blk h 53 (l := mapFuns (tmJA B 53) (tmJA B 51 + 2)) rfl
  have b54 := tmJ_blk h 54 (l := tmJSolFuns (tmJA B 54) 15) rfl
  have b55 := tmJ_blk h 55 (l := tmJVSumFuns (tmJA B 55) 17) rfl
  have b56 := tmJ_blk h 56 (l := mapFuns (tmJA B 56) (tmJA B 39 + 12)) rfl
  have b57 := tmJ_blk h 57 (l := [itParF (tmJA B 22) (tmJA B 58) (tmJA B 59), itInvB (tmJA B 60),
    itInvT, itParS]) rfl
  have b58 := tmJ_blk h 58 (l := mapFuns (tmJA B 58) (tmJA B 57 + 1)) rfl
  have b59 := tmJ_blk h 59 (l := foldlFuns (tmJA B 59) (tmJA B 57 + 3)) rfl
  have b60 := tmJ_blk h 60 (l := filterFuns (tmJA B 60) (tmJA B 57 + 2)) rfl
  have b61 := tmJ_blk h 61 (l := [tmJLMainF (tmJA B 22) (tmJA B 17) (tmJA B 63) (tmJA B 65)
      (tmJA B 68) (tmJA B 41), tmJLRowF (tmJA B 22) (tmJA B 64),
    tmJLBitF 1 (tmJA B 17) (tmJA B 30) (tmJA B 18), tmJLPiF (tmJA B 66) (tmJA B 67),
    tmJLRkF (tmJA B 62), tmJLColF, tmJLDF 3 (tmJA B 30) (tmJA B 18)]) rfl
  have b62 := tmJ_blk h 62 (l := eqNatsFuns (tmJA B 62)) rfl
  have b63 := tmJ_blk h 63 (l := mapFuns (tmJA B 63) (tmJA B 61 + 1)) rfl
  have b64 := tmJ_blk h 64 (l := mapFuns (tmJA B 64) (tmJA B 61 + 2)) rfl
  have b65 := tmJ_blk h 65 (l := mapFuns (tmJA B 65) (tmJA B 61 + 3)) rfl
  have b66 := tmJ_blk h 66 (l := filterFuns (tmJA B 66) (tmJA B 61 + 4)) rfl
  have b67 := tmJ_blk h 67 (l := filterFuns (tmJA B 67) (tmJA B 61 + 5)) rfl
  have b68 := tmJ_blk h 68 (l := mapFuns (tmJA B 68) (tmJA B 61 + 6)) rfl
  have pairAt : TmJPairAt P (tmJA B 41) (tmJA B 22) (tmJA B 42) (tmJA B 41 + 1) :=
    ⟨tmJ_get b41 (j := 0) rfl, b22, b42, tmJ_get b41 (j := 1) rfl⟩
  have hfl : P.funs[tmJA B 26]? = some (tmJFlatF (tmJA B 26 + 1)) := tmJ_get b26 (j := 0) rfl
  have hflF : P.HasAt (tmJA B 26 + 1) (foldlFuns (tmJA B 26 + 1) (tmJA B 26 + 4)) :=
    b26.block 1 rfl
  have hst : P.funs[tmJA B 26 + 4]? = some (tmJFlatStepF (tmJA B 17)) := tmJ_get b26 (j := 4) rfl
  have hHA : TmJHAt P (tmJPos B) :=
    { hfuns := b39, hiv := b18, hrep := b40, hpr := pairAt, hrg := b22, hcomp := b30,
      htbR := b43, htbE := b44, htbP := b45, hdc := tmJ_get b46 (j := 0) rfl,
      hpp := tmJ_get b47 (j := 0) rfl, hfld := b48, hlocA := tmJ_get b49 (j := 0) rfl,
      hds := tmJ_get b49 (j := 1) rfl, htbA := b50, htbe := tmJ_get b49 (j := 2) rfl,
      hswS := tmJ_get b51 (j := 0) rfl, htbD := b52, hswDE := tmJ_get b51 (j := 1) rfl,
      htbP2 := b53, hswPE := tmJ_get b51 (j := 2) rfl, hsol := b54, hvsum := b55, hzm := b56,
      hpar := tmJ_get b57 (j := 0) rfl, hrng := b22, hmp := b58, hib := tmJ_get b57 (j := 1) rfl,
      hflt := b60, hit := tmJ_get b57 (j := 2) rfl, hfld2 := b59, hst := tmJ_get b57 (j := 3) rfl,
      hL :=
        { hmain := tmJ_get b61 (j := 0) rfl, hrow := tmJ_get b61 (j := 1) rfl,
          hbit := tmJ_get b61 (j := 2) rfl, hpi := tmJ_get b61 (j := 3) rfl,
          hrk := tmJ_get b61 (j := 4) rfl, hcol := tmJ_get b61 (j := 5) rfl,
          hd := tmJ_get b61 (j := 6) rfl, hrg := b22, hap := b17, hcp := b30, hiv := b18,
          hen := b62, hmR := b63, hmB := b64, hmP := b65, hfR := b66, hfC := b67, hmD := b68,
          hpair := pairAt } }
  refine ⟨tmJ_get b0 (j := 0) rfl, ?_, hHA⟩
  refine ⟨tmJ_get b1 (j := 0) rfl, ?_, ?_, ?_, ?_⟩
  · -- the context
    refine ⟨tmJA B 6, tmJA B 7, tmJA B 8, tmJA B 9, tmJA B 10, tmJA B 11,
      { hf := tmJ_get b2 (j := 0) rfl, hpa := ?_, hmk := b7, hlg := ?_, htl := ?_, hbt := ?_,
        hlac := b11 }⟩
    · refine ⟨tmJA B 20, tmJA B 21, tmJA B 22, tmJA B 23,
        { hf := tmJ_get b6 (j := 0) rfl, htab := ?_, hgg := ?_, hrg := b22, hmk := b7,
          hnq := ?_ }⟩
      · exact ⟨tmJA B 35, tmJA B 22, tmJA B 36, tmJA B 20 + 1, tmJA B 18,
          { hf := tmJ_get b20 (j := 0) rfl, hdom := domAt_of_hasAt b35, hrg := b22, htb := b36,
            htbe := tmJ_get b20 (j := 1) rfl, hinv := b18 }⟩
      · exact ⟨tmJA B 35, tmJA B 37, tmJA B 21 + 1, tmJA B 30,
          { hf := tmJ_get b21 (j := 0) rfl, hdom := domAt_of_hasAt b35, hmpc := b37,
            hcj := tmJ_get b21 (j := 1) rfl, hcp := b30 }⟩
      · exact ⟨tmJA B 22, tmJA B 38, tmJA B 23 + 1, tmJA B 32, tmJA B 49, tmJA B 49 + 1,
          tmJA B 50, tmJA B 49 + 2, tmJA B 41, tmJA B 22, tmJA B 42, tmJA B 41 + 1, tmJA B 26,
          tmJA B 17,
          { hf := tmJ_get b23 (j := 0) rfl, hrg := b22, htbR := b38,
            hrow := tmJ_get b23 (j := 1) rfl, hmp := b32, hlocA := tmJ_get b49 (j := 0) rfl,
            hds := tmJ_get b49 (j := 1) rfl, htb := b50, htbe := tmJ_get b49 (j := 2) rfl,
            hpr := pairAt, hfl := hfl, hflF := hflF, hst := hst, happ := b17 }⟩
    · exact ⟨tmJA B 22, tmJA B 24, tmJA B 8 + 1, tmJA B 25, tmJA B 8 + 2, tmJA B 26, tmJA B 17,
        { hf := tmJ_get b8 (j := 0) rfl, hrg := b22, htbR := b24,
          hrow := tmJ_get b8 (j := 1) rfl, hmp := b25, he := tmJ_get b8 (j := 2) rfl,
          hfl := hfl, hflF := hflF, hst := hst, happ := b17 }⟩
    · exact ⟨tmJA B 22, tmJA B 27, tmJA B 9 + 1, tmJA B 26, tmJA B 17,
        { hf := tmJ_get b9 (j := 0) rfl, hrg := b22, htbE := b27, he := tmJ_get b9 (j := 1) rfl,
          hfl := hfl, hflF := hflF, hst := hst, happ := b17 }⟩
    · exact ⟨tmJA B 28, tmJA B 10 + 1, tmJA B 29, tmJ_get b10 (j := 0) rfl, b28,
        tmJ_get b10 (j := 1) rfl, b29⟩
  · exact ⟨tmJA B 12, tmJA B 30, tmJA B 13, tmJ_get b3 (j := 0) rfl, b12, b30, b13⟩
  · -- `Aut_J`
    refine ⟨tmJA B 14, tmJA B 54 + 1, tmJA B 15, tmJA B 16, tmJA B 51, tmJA B 17,
      { hf := tmJ_get b4 (j := 0) rfl, hns := ?_, hker := ⟨tmJA B 54, rfl, b54⟩, hs2 := ?_,
        hts := ?_, happ := b17 }⟩
    · exact ⟨tmJA B 22, tmJA B 31, tmJA B 14 + 1, tmJA B 32, tmJA B 49, tmJA B 49 + 1,
        tmJA B 50, tmJA B 49 + 2, tmJA B 41, tmJA B 22, tmJA B 42, tmJA B 41 + 1, tmJA B 26,
        tmJA B 17,
        { hf := tmJ_get b14 (j := 0) rfl, hrg := b22, hmpR := b31,
          hrow := tmJ_get b14 (j := 1) rfl, hmp := b32, hlocA := tmJ_get b49 (j := 0) rfl,
          hds := tmJ_get b49 (j := 1) rfl, htb := b50, htbe := tmJ_get b49 (j := 2) rfl,
          hpr := pairAt, hfl := hfl, hflF := hflF, hst := hst, happ := b17 }⟩
    · exact ⟨tmJA B 33, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        { hf := tmJ_get b15 (j := 0) rfl, he := tmJ_get b15 (j := 1) rfl, hmp := b33,
          hlam := hHA.lamAt }⟩
    · exact ⟨tmJA B 34, tmJA B 16 + 1, tmJA B 30, tmJA B 18, tmJA B 52, tmJA B 51 + 1,
        tmJA B 53, tmJA B 51 + 2, tmJA B 41, tmJA B 22, tmJA B 42, tmJA B 41 + 1,
        tmJ_get b16 (j := 0) rfl, b34, tmJ_get b16 (j := 1) rfl, tmJ_get b51 (j := 0) rfl, b18,
        b52, tmJ_get b51 (j := 1) rfl, b53, tmJ_get b51 (j := 2) rfl, pairAt, b30⟩
  · exact ⟨tmJA B 18, tmJA B 12, tmJA B 30, tmJA B 17, tmJA B 7, tmJA B 19,
      { hf := tmJ_get b5 (j := 0) rfl, hiv := b18, hmpC := b12, hcp := b30, happ := b17,
        hmk := b7, hrd := b19 }⟩

end GI.Impl
