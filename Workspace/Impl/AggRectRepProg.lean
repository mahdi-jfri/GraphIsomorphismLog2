import Workspace.Impl.AggRectRepFinH
import Workspace.Impl.AggCertBud
import Workspace.Impl.AggInc
import Workspace.Lang.Prims.BlockHom
import Workspace.Lang.Lib.Tabulate

/-!
# The rectangle representation program

The program `rcRMain I` on `[sv, q, ⟨ps⟩, W, R]` follows the steps of the rectangle
representation. The indices of its functions are the fields of `I : RcRIdx`;
`RcROk P I` says that each index holds its function (or its library module).

1. `st1`: the base point `x` (first domain position, `findEq 1`), the graph pairs of `G_x`
   (**PointwiseStab**, `graphStab`), the orbit labels of their second parts (`orbit`), and the
   labels whose orbit has at most two points (`filter` by `count`).
2. `st2`: the base labels `d₁, d₂` (first and last small label), the orbit table of the tuple
   `(x, d₁, d₂)` (`graphTup`, keys only), the two first points `w₀, w₁` of `W`, the generators
   `rcRGens W R w₀ w₁` (`t < q²`, `a = t / q`, `b = t % q`), the flags `car` (one small label) and
   `uno` (`d₁, d₂` in one orbit), and `range k`.
3. `pairF` (two small labels): **Preimage** on `ps` with the generators. `carF` (one small
   label): the row keys and row numbers (`rcRKeyN`, `rcRKeysN`, `rcRRowN'`), the pairs
   `(g, ρ(g) ⊕ π(g))` and the generators `embed(σ) ⊕ σ`, then **Preimage** in degree `m + q`.
4. `st4`: **PointwiseStab** with no points (`kr`) on the first parts, the generators without the
   identity of `encGroup` (`tail`), the label part of each (`rcRPiN`), and the cells
   (`rcRCellN`). The output is `[hs, cells, []]`.

Every lookup is a safe `getD` (`rcRGetDF`), so the program never fails on an index.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- The indices of the functions of the program. -/
structure RcRIdx where
  gD : ℕ
  rng : ℕ
  fEq : ℕ
  cnt : ℕ
  stab : ℕ
  orb : ℕ
  tup : ℕ
  pre : ℕ
  kr : ℕ
  tl : ℕ
  pe : ℕ
  g0 : ℕ
  g1 : ℕ
  mSnd : ℕ
  mFst : ℕ
  smP : ℕ
  fSm : ℕ
  w1P : ℕ
  fW1 : ℕ
  genF : ℕ
  mGen : ℕ
  grF : ℕ
  mGR : ℕ
  keyP : ℕ
  fKey : ℕ
  keyN : ℕ
  keysP : ℕ
  fKeys : ℕ
  rowF : ℕ
  mRow : ℕ
  rhoF : ℕ
  mRho : ℕ
  psF : ℕ
  mPs : ℕ
  embRF : ℕ
  mEmbR : ℕ
  embF : ℕ
  mEmb : ℕ
  carF : ℕ
  pairF : ℕ
  lk0P : ℕ
  fLk0 : ℕ
  lk1P : ℕ
  fLk1 : ℕ
  lk2P : ℕ
  fLk2 : ℕ
  look : ℕ
  look1 : ℕ
  look2 : ℕ
  piF : ℕ
  mPi : ℕ
  outF : ℕ
  mOut : ℕ
  cellF : ℕ
  mCell : ℕ
  st1 : ℕ
  st2 : ℕ
  st4 : ℕ
  main : ℕ
  jp : ℕ
  jpre : ℕ

namespace RcRIdx

variable (I : RcRIdx)

/-! ### Small expressions -/

/-- `l.getD i d`, by a call of `rcRGetDF`. -/
def gd (l i d : Expr) : Expr := .call I.gD (mk3 l i d)

end RcRIdx

/-- Equality of two numbers (`1` or `0`). -/
def rcREq (a b : Expr) : Expr := .arith .eq a b

/-- Conjunction of two bits. -/
def rcRAnd (a b : Expr) : Expr := .arith .mul a b

/-- Negation of a bit. -/
def rcRNot (a : Expr) : Expr := .arith .eq a (.nat 0)

/-- The transposition `(x y)` applied to `z`. -/
def rcRSw (x y z : Expr) : Expr := .ite (rcREq z x) y (.ite (rcREq z y) x z)

/-- **Safe lookup**: on `[l, i, d]`, entry `i` of `l` if it exists, and `d` otherwise. -/
def rcRGetDF : Expr := .ite (.arith .lt (arg 1) (.length (arg 0))) (.get (arg 0) (arg 1)) (arg 2)

/-- On `[c, [a, b, …]]`: `a`. -/
def rcRGet0F : Expr := .get (arg 1) (.nat 0)

/-- On `[c, [a, b, …]]`: `b`. -/
def rcRGet1F : Expr := .get (arg 1) (.nat 1)

namespace RcRIdx

variable (I : RcRIdx)

/-! ### Stage 1: the base point and the small labels -/

/-- On `[lab, c]`: whether at most two labels equal the label of `c`. -/
def smPF : Expr := .arith .lt (.call I.cnt (mk2 (I.gd (arg 0) (arg 1) (.nat 0)) (arg 0))) (.nat 3)

/-- **Stage 1** on `A = [sv, q, ⟨ps⟩, W, R]`: `[x, lab, range q, small]`. -/
def st1F : Expr :=
  .letE (.get (arg 0) (.nat 0))
  (.letE (.get (arg 0) (.nat 2))
  (.letE (.call I.fEq (mk2 (.nat 1) (.var 2)))
  (.letE (.call I.stab (mk3 (mk2 (.var 1) (arg 1)) (arg 2) (mk1 (.var 3))))
  (.letE (.call I.orb (mk2 (arg 1) (.call I.mSnd (mk2 (.nat 0) (.var 4)))))
  (.letE (.call I.rng (arg 1))
  (.letE (.call I.fSm (mk2 (.var 5) (.var 6)))
  (mk4 (.var 3) (.var 5) (.var 6) (.var 7))))))))

/-! ### Stage 2: the orbit table and the generators -/

/-- On `[[wl, w₀], j]`: whether `j ∈ W` and `j ≠ w₀`. -/
def w1PF : Expr :=
  rcRAnd (rcREq (I.gd (.get (arg 0) (.nat 0)) (arg 1) (.nat 0)) (.nat 1))
    (rcRNot (rcREq (arg 1) (.get (arg 0) (.nat 1))))

/-- On `[[a, b, w₀, w₁, cond], j]`: the image of `j` under `rcRGen`. -/
def _root_.GI.Impl.rcRGrF : Expr :=
  .letE (rcRSw (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))
    (.ite (.get (arg 0) (.nat 4)) (rcRSw (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 3)) (.var 1))
      (arg 1))

/-- On `[[wl, rl, w₀, w₁, q, range q], t]`: the generator `rcRGen W R w₀ w₁ (t / q) (t % q)`. -/
def genFF : Expr :=
  let C := arg 0
  .letE (.arith .div (arg 1) (.get C (.nat 4)))
  (.letE (.arith .mod (arg 1) (.get C (.nat 4)))
  (.letE (rcRAnd (rcRNot (rcREq (.var 1) (.var 2)))
      (rcRAnd (rcREq (I.gd (.get C (.nat 0)) (.var 1) (.nat 0)) (I.gd (.get C (.nat 0)) (.var 2) (.nat 0)))
        (rcREq (I.gd (.get C (.nat 1)) (.var 1) (.nat 0)) (I.gd (.get C (.nat 1)) (.var 2) (.nat 0)))))
  (.call I.mGR (mk2 (mk5 (.var 1) (.var 2) (.get C (.nat 2)) (.get C (.nat 3)) (.var 3))
    (.get C (.nat 5))))))

/-- **Stage 2** on `[A, R₁]` with `R₁ = [x, lab, range q, small]`:
`[d₁, d₂, Lk, gens, car, uno, range k]`. -/
def st2F : Expr :=
  let A := arg 0
  let R1 := arg 1
  let kE := Expr.get (.get A (.nat 0)) (.nat 0)
  let qE := Expr.get A (.nat 1)
  let sm := Expr.get R1 (.nat 3)
  .letE (I.gd sm (.nat 0) (.nat 0))
  (.letE (I.gd sm (.arith .sub (.length sm) (.nat 1)) (.nat 0))
  (.letE (.call I.mFst (mk2 (.nat 0) (.call I.tup (mk4 (mk2 kE qE) (.get A (.nat 2))
      (mk3 (.get R1 (.nat 0)) (.arith .add kE (.var 1)) (.arith .add kE (.var 2)))
      (.arith .mul (.arith .mul kE qE) qE)))))
  (.letE (.call I.fEq (mk2 (.nat 1) (.get A (.nat 3))))
  (.letE (.call I.fW1 (mk2 (mk2 (.get A (.nat 3)) (.var 4)) (.get R1 (.nat 2))))
  (.letE (.call I.mGen (mk2 (Expr.mkList [.get A (.nat 3), .get A (.nat 4), .var 4, .var 5, qE,
      .get R1 (.nat 2)]) (.call I.rng (.arith .mul qE qE))))
  (Expr.mkList [.var 1, .var 2, .var 3, .var 6, rcREq (.length sm) (.nat 1),
    rcREq (I.gd (.get R1 (.nat 1)) (.var 1) (.nat 0)) (I.gd (.get R1 (.nat 1)) (.var 2) (.nat 0)),
    .call I.rng kE]))))))

/-! ### Stage 3: the group, by one Preimage call -/

/-- **Pairs** on `[A, R₂]`: `[qs, []]` for the Preimage output `qs` on `ps` and the generators. -/
def pairFF : Expr :=
  mk2 (.call I.pre (mk3 (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (arg 0) (.nat 1)))
    (.get (arg 0) (.nat 2)) (.get (arg 1) (.nat 3)))) .nil

/-- On `[[dl, rlab, rli], j]`: whether `j` is in the domain with row label `rli`. -/
def keyPF : Expr :=
  rcRAnd (rcREq (I.gd (.get (arg 0) (.nat 0)) (arg 1) (.nat 0)) (.nat 1))
    (rcREq (I.gd (.get (arg 0) (.nat 1)) (arg 1) (.nat 0)) (.get (arg 0) (.nat 2)))

/-- On `[[dl, rlab, range k, …], i]`: the key `rcRKeyN dl rlab k i`. -/
def keyNF : Expr :=
  .call I.fKey (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
    (I.gd (.get (arg 0) (.nat 1)) (arg 1) (.nat 0))) (.get (arg 0) (.nat 2)))

/-- On `[[dl, rlab, range k], j]`: whether `j` is in the domain and is its own key. -/
def keysPF : Expr :=
  rcRAnd (rcREq (I.gd (.get (arg 0) (.nat 0)) (arg 1) (.nat 0)) (.nat 1))
    (rcREq (.call I.keyN (.var 0)) (arg 1))

/-- On `[[dl, rlab, range k, keys], i]`: the row number `rcRRowN' dl rlab k i`. -/
def rowFF : Expr := .call I.fEq (mk2 (.call I.keyN (.var 0)) (.get (arg 0) (.nat 3)))

/-- On `[[rowT, keys, h], r]`: the row of `h` applied to the key of row `r`. -/
def rhoFF : Expr :=
  I.gd (.get (arg 0) (.nat 0)) (I.gd (.get (arg 0) (.nat 2))
    (I.gd (.get (arg 0) (.nat 1)) (arg 1) (.nat 0)) (.nat 0)) (.nat 0)

/-- On `[[rowT, keys, m, range m], [g, π]]`: `[g, ρ(g) ⊕ π]`. -/
def psFF : Expr :=
  .letE (.call I.mRho (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
      (.get (arg 1) (.nat 0))) (.get (arg 0) (.nat 3))))
    (mk2 (.get (arg 1) (.nat 0)) (.call (I.pe + 12) (mk2 (.get (arg 0) (.nat 2))
      (mk2 (.var 1) (.get (arg 1) (.nat 1))))))

/-- On `[[σ, q], j]`: `σ j` for `j < q`, and `j` otherwise (the embedding on the rows). -/
def embRFF : Expr :=
  .ite (.arith .lt (arg 1) (.get (arg 0) (.nat 1))) (I.gd (.get (arg 0) (.nat 0)) (arg 1) (.nat 0))
    (arg 1)

/-- On `[[q, m, range m], σ]`: `embed(σ) ⊕ σ`. -/
def embFF : Expr :=
  .call (I.pe + 12) (mk2 (.get (arg 0) (.nat 1))
    (mk2 (.call I.mEmbR (mk2 (mk2 (arg 1) (.get (arg 0) (.nat 0))) (.get (arg 0) (.nat 2))))
      (arg 1)))

/-- **Single labels** on `[A, R₂]`: `[qs, rowT]` for the Preimage output `qs` on the pairs
`(g, ρ(g) ⊕ π(g))` and the generators `embed(σ) ⊕ σ`, and the row numbers `rowT`. -/
def carFF : Expr :=
  let A := arg 0
  let R2 := arg 1
  let kE := Expr.get (.get A (.nat 0)) (.nat 0)
  let qE := Expr.get A (.nat 1)
  let dl := Expr.get (.get A (.nat 0)) (.nat 2)
  let rK := Expr.get R2 (.nat 6)
  .letE (.get (.get (.get (.get A (.nat 0)) (.nat 6)) (.nat 0)) (.nat 1))
  (.letE (.call I.fKeys (mk2 (mk3 dl (.var 1) rK) rK))
  (.letE (.call I.mRow (mk2 (mk4 dl (.var 1) rK (.var 2)) rK))
  (.letE (.length (.var 2))
  (.letE (.call I.rng (.var 4))
  (.letE (.call I.mPs (mk2 (mk4 (.var 3) (.var 2) (.var 4) (.var 5)) (.get A (.nat 2))))
  (.letE (.call I.mEmb (mk2 (mk3 qE (.var 4) (.var 5)) (.get R2 (.nat 3))))
  (mk2 (.call I.pre (mk3 (mk2 kE (.arith .add (.var 4) qE)) (.var 6) (.var 7))) (.var 3))))))))

/-! ### Stage 4: the generators with their label parts, and the cells -/

/-- On `[i, y]`: whether `y` has head `i`. -/
def lk0PF : Expr := rcREq (I.gd (arg 1) (.nat 0) (.nat 0)) (arg 0)

/-- On `[t, y]`: whether the first label of `y` is `t`. -/
def lk1PF : Expr := rcREq (I.gd (arg 1) (.nat 1) (.nat 0)) (arg 0)

/-- On `[[t, a], y]`: whether the first label of `y` is `t` and the second is not `a`. -/
def lk2PF : Expr :=
  rcRAnd (rcREq (I.gd (arg 1) (.nat 1) (.nat 0)) (.get (arg 0) (.nat 0)))
    (rcRNot (rcREq (I.gd (arg 1) (.nat 2) (.nat 0)) (.get (arg 0) (.nat 1))))

/-- On `[Lk, i]`: `rcRLook Lk i`. -/
def lookF : Expr := I.gd (arg 0) (.call I.fLk0 (mk2 (arg 1) (arg 0))) .nil

/-- On `[Lk, t]`: `rcRLook1 Lk t`. -/
def look1F : Expr := I.gd (arg 0) (.call I.fLk1 (mk2 (arg 1) (arg 0))) .nil

/-- On `[Lk, t, a]`: `rcRLook2 Lk t a`. -/
def look2F : Expr := I.gd (arg 0) (.call I.fLk2 (mk2 (mk2 (arg 1) (arg 2)) (arg 0))) .nil

/-- On `[[Lk, k, h], j]`: `rcRPiN Lk k h j`. -/
def piFF : Expr :=
  let Lk := Expr.get (arg 0) (.nat 0)
  let kE := Expr.get (arg 0) (.nat 1)
  let hE := Expr.get (arg 0) (.nat 2)
  .letE (.call I.look1 (mk2 Lk (.arith .add kE (arg 1))))
  (.letE (.call I.look (mk2 Lk (I.gd hE (I.gd (.var 1) (.nat 0) (.nat 0)) (.nat 0))))
  (.letE (I.gd (.var 2) (.nat 1) (.nat 0))
  (.letE (I.gd (.var 2) (.nat 2) (.nat 0))
  (.arith .sub (.ite (rcREq (.var 3) (.var 4)) (.var 3)
    (.letE (.call I.look (mk2 Lk (I.gd hE (I.gd (.call I.look2 (mk3 Lk (.arith .add kE (arg 1))
        (I.gd (.var 1) (.nat 2) (.nat 0)))) (.nat 0) (.nat 0)) (.nat 0))))
      (.ite (.arith .lt (.nat 0) (.arith .add (rcREq (.var 3) (I.gd (.var 5) (.nat 1) (.nat 0)))
          (rcREq (.var 3) (I.gd (.var 5) (.nat 2) (.nat 0)))))
        (.var 3) (.var 4)))) kE))))

/-- On `[[Lk, k, range q], h]`: `[h, π(h)]`. -/
def outFF : Expr :=
  mk2 (arg 1) (.call I.mPi (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))
    (.get (arg 0) (.nat 2))))

/-- On `[[dl, Lk, k, q, wl, rl, car, uno, rowT], i]`: `rcRCellN`. -/
def cellFF : Expr :=
  let C := arg 0
  let wl := Expr.get C (.nat 4)
  let rl := Expr.get C (.nat 5)
  let qE := Expr.get C (.nat 3)
  .ite (rcREq (I.gd (.get C (.nat 0)) (arg 1) (.nat 0)) (.nat 0)) (.nat 0)
    (.letE (.call I.look (mk2 (.get C (.nat 1)) (arg 1)))
    (.letE (.arith .sub (I.gd (.var 1) (.nat 1) (.nat 0)) (.get C (.nat 2)))
    (.ite (.get C (.nat 6))
      (.letE (I.gd (.get C (.nat 8)) (arg 1) (.nat 0))
        (.ite (rcRAnd (.arith .lt (.var 3) qE) (rcRAnd (rcREq (I.gd wl (.var 3) (.nat 0)) (.nat 1))
            (rcREq (I.gd rl (.var 2) (.nat 0)) (.nat 1))))
          (.arith .add (.arith .add (.nat 1) (.arith .mul (.var 3) qE)) (.var 2)) (.nat 0)))
      (.letE (.arith .sub (I.gd (.var 1) (.nat 2) (.nat 0)) (.get C (.nat 2)))
        (.ite (rcRAnd (rcREq (I.gd wl (.var 2) (.nat 0)) (.nat 1))
            (rcREq (I.gd rl (.var 3) (.nat 0)) (.nat 1)))
          (.arith .add (.arith .add (.nat 1) (.arith .mul (.var 2) qE)) (.var 3))
          (.ite (rcRAnd (.get C (.nat 7)) (rcRAnd (rcREq (I.gd wl (.var 3) (.nat 0)) (.nat 1))
              (rcREq (I.gd rl (.var 2) (.nat 0)) (.nat 1))))
            (.arith .add (.arith .add (.nat 1) (.arith .mul (.var 3) qE)) (.var 2)) (.nat 0)))))))

/-- **Stage 4** on `[A, R₁, R₂, R₃]`: `[⟨[h, π(h)]⟩, cells, []]`. -/
def st4F : Expr :=
  let A := arg 0
  let R1 := arg 1
  let R2 := arg 2
  let kE := Expr.get (.get A (.nat 0)) (.nat 0)
  .letE (.call I.tl (.get (.call I.kr (mk2 kE (.get (arg 3) (.nat 0)))) (.nat 1)))
  (.letE (.call I.mOut (mk2 (mk3 (.get R2 (.nat 2)) kE (.get R1 (.nat 2))) (.var 1)))
  (mk3 (.var 2) (.call I.mCell (mk2 (Expr.mkList [.get (.get A (.nat 0)) (.nat 2), .get R2 (.nat 2),
      kE, .get A (.nat 1), .get A (.nat 3), .get A (.nat 4), .get R2 (.nat 4), .get R2 (.nat 5),
      .get (arg 3) (.nat 1)]) (.get R2 (.nat 6)))) .nil))

/-- **The program** on `A = [sv, q, ⟨ps⟩, W, R]`. -/
def mainF : Expr :=
  .letE (.call I.st1 (.var 0))
  (.letE (.call I.st2 (mk2 (.var 0) (.var 1)))
  (.letE (.ite (.get (.var 2) (.nat 4)) (.call I.carF (mk2 (.var 0) (.var 2)))
      (.call I.pairF (mk2 (.var 0) (.var 2))))
  (.call I.st4 (mk4 (.var 0) (.var 1) (.var 2) (.var 3)))))

end RcRIdx

open RcRIdx in
/-- **Each index holds its function.** -/
structure RcROk (P : Program) (I : RcRIdx) : Prop where
  gD : P.funs[I.gD]? = some rcRGetDF
  rng : P.HasAt I.rng (rangeFuns I.rng)
  fEq : P.HasAt I.fEq (findEqFuns I.fEq)
  cnt : P.HasAt I.cnt (countFuns I.cnt)
  stab : P.HasAt I.stab (graphStabFuns I.stab I.jp)
  orb : P.HasAt I.orb (orbitFuns I.orb)
  tup : P.HasAt I.tup (graphTupFuns I.tup)
  pre : P.HasAt I.pre (graphPreFuns I.pre I.jpre)
  kr : P.HasAt I.kr (krFuns I.kr I.jp)
  tl : P.HasAt I.tl (tailFuns I.tl)
  pe : P.HasAt I.pe (pEncMapFuns I.pe)
  g0 : P.funs[I.g0]? = some rcRGet0F
  g1 : P.funs[I.g1]? = some rcRGet1F
  mSnd : P.HasAt I.mSnd (mapFuns I.mSnd I.g1)
  mFst : P.HasAt I.mFst (mapFuns I.mFst I.g0)
  smP : P.funs[I.smP]? = some I.smPF
  fSm : P.HasAt I.fSm (filterFuns I.fSm I.smP)
  w1P : P.funs[I.w1P]? = some I.w1PF
  fW1 : P.HasAt I.fW1 (findFuns I.fW1 I.w1P)
  genF : P.funs[I.genF]? = some I.genFF
  mGen : P.HasAt I.mGen (mapFuns I.mGen I.genF)
  grF : P.funs[I.grF]? = some rcRGrF
  mGR : P.HasAt I.mGR (mapFuns I.mGR I.grF)
  keyP : P.funs[I.keyP]? = some I.keyPF
  fKey : P.HasAt I.fKey (findFuns I.fKey I.keyP)
  keyN : P.funs[I.keyN]? = some I.keyNF
  keysP : P.funs[I.keysP]? = some I.keysPF
  fKeys : P.HasAt I.fKeys (filterFuns I.fKeys I.keysP)
  rowF : P.funs[I.rowF]? = some I.rowFF
  mRow : P.HasAt I.mRow (mapFuns I.mRow I.rowF)
  rhoF : P.funs[I.rhoF]? = some I.rhoFF
  mRho : P.HasAt I.mRho (mapFuns I.mRho I.rhoF)
  psF : P.funs[I.psF]? = some I.psFF
  mPs : P.HasAt I.mPs (mapFuns I.mPs I.psF)
  embRF : P.funs[I.embRF]? = some I.embRFF
  mEmbR : P.HasAt I.mEmbR (mapFuns I.mEmbR I.embRF)
  embF : P.funs[I.embF]? = some I.embFF
  mEmb : P.HasAt I.mEmb (mapFuns I.mEmb I.embF)
  carF : P.funs[I.carF]? = some I.carFF
  pairF : P.funs[I.pairF]? = some I.pairFF
  lk0P : P.funs[I.lk0P]? = some I.lk0PF
  fLk0 : P.HasAt I.fLk0 (findFuns I.fLk0 I.lk0P)
  lk1P : P.funs[I.lk1P]? = some I.lk1PF
  fLk1 : P.HasAt I.fLk1 (findFuns I.fLk1 I.lk1P)
  lk2P : P.funs[I.lk2P]? = some I.lk2PF
  fLk2 : P.HasAt I.fLk2 (findFuns I.fLk2 I.lk2P)
  look : P.funs[I.look]? = some I.lookF
  look1 : P.funs[I.look1]? = some I.look1F
  look2 : P.funs[I.look2]? = some I.look2F
  piF : P.funs[I.piF]? = some I.piFF
  mPi : P.HasAt I.mPi (mapFuns I.mPi I.piF)
  outF : P.funs[I.outF]? = some I.outFF
  mOut : P.HasAt I.mOut (mapFuns I.mOut I.outF)
  cellF : P.funs[I.cellF]? = some I.cellFF
  mCell : P.HasAt I.mCell (mapFuns I.mCell I.cellF)
  st1 : P.funs[I.st1]? = some I.st1F
  st2 : P.funs[I.st2]? = some I.st2F
  st4 : P.funs[I.st4]? = some I.st4F
  main : P.funs[I.main]? = some I.mainF

end GI.Impl
