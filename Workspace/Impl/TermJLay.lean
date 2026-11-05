module

public import Workspace.Impl.TermJGlue
public import Workspace.Impl.LayoutAsm
public import Workspace.Impl.DomRestrict

@[expose] public section

/-!
# The layout of the `J`-answer

All functions of the `J`-answer sit in blocks of 1000 starting at a base `B`: block `i` starts at
`tmJA B i = B + 1000 i` (`tmJLay B`, flattened by `tmJBlk`). Library blocks (range, compose,
append, the pair program, the flatten loop, …) are placed once and shared. `tmJPos B` is the
position record of the per-label program. `tmJLay_at` derives the layout facts `TmJNEAt`,
`TmJHAt` that `tmJ_termJSpec` asks for from one `HasAt` of the whole list.

Primitive indices of the final table: PointwiseStab `0`, Membership `1`, NormalizedFactor `3`,
GroupOrder `5`, NormalizedIntersection `10`, HermiteFullRank `15` (`linHermitePrim`),
ConstructiveMembership `17` (`linMembershipPrim`).
-/

namespace GI.Impl

open GI.Lang

/-- Blocks of 1000 functions. -/
def tmJBlk (bs : List (List Expr)) : List Expr := (bs.map (asmPad 1000)).flatten

theorem length_tmJBlk : ∀ {bs : List (List Expr)}, (∀ l ∈ bs, l.length ≤ 1000) →
    (tmJBlk bs).length = 1000 * bs.length
  | [], _ => rfl
  | l :: bs, h => by
    have e := length_tmJBlk (bs := bs) fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    simp only [tmJBlk, List.map_cons, List.flatten_cons, List.length_append] at e ⊢
    rw [e, length_asmPad (h l List.mem_cons_self), List.length_cons]
    ring

theorem tmJBlk_hasAt {P : Program} : ∀ {b : ℕ} {bs : List (List Expr)}, P.HasAt b (tmJBlk bs) →
    (∀ l ∈ bs, l.length ≤ 1000) → ∀ {i : ℕ} {l : List Expr}, bs[i]? = some l →
      P.HasAt (b + 1000 * i) l
  | b, l' :: bs, h, hf, 0, l, hl => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl
    have h' : P.HasAt b (asmPad 1000 l' ++ tmJBlk bs) := by
      simpa [tmJBlk] using h
    simpa [asmPad] using h'.left.left
  | b, l' :: bs, h, hf, i + 1, l, hl => by
    simp only [List.getElem?_cons_succ] at hl
    have h' : P.HasAt b (asmPad 1000 l' ++ tmJBlk bs) := by
      simpa [tmJBlk] using h
    have h2 := h'.right
    rw [length_asmPad (hf l' List.mem_cons_self)] at h2
    have := tmJBlk_hasAt h2 (fun l'' hl'' => hf l'' (List.mem_cons_of_mem _ hl'')) hl
    rw [show b + 1000 * (i + 1) = b + 1000 + 1000 * i by ring]
    exact this

/-- The start of block `i`. -/
abbrev tmJA (B i : ℕ) : ℕ := B + 1000 * i

/-- The positions of the per-label program. -/
abbrev tmJPos (B : ℕ) : TmJHPos where
  b := tmJA B 39
  iv := tmJA B 18
  rep := tmJA B 40
  pr := tmJA B 41
  prg := tmJA B 22
  prt := tmJA B 42
  prte := tmJA B 41 + 1
  rg := tmJA B 22
  comp := tmJA B 30
  tbR := tmJA B 43
  tbE := tmJA B 44
  tbP := tmJA B 45
  dc := tmJA B 46
  pp := tmJA B 47
  fld := tmJA B 48
  locA := tmJA B 49
  dsA := tmJA B 49 + 1
  tbA := tmJA B 50
  tbe := tmJA B 49 + 2
  swS := tmJA B 51
  tbD := tmJA B 52
  swDE := tmJA B 51 + 1
  tbP2 := tmJA B 53
  swPE := tmJA B 51 + 2
  sol := tmJA B 54
  jh := 15
  vsum := tmJA B 55
  jm := 17
  zm := tmJA B 56
  par := tmJA B 57
  rng := tmJA B 22
  mp := tmJA B 58
  ib := tmJA B 57 + 1
  flt := tmJA B 60
  it := tmJA B 57 + 2
  fld2 := tmJA B 59
  st := tmJA B 57 + 3
  L := tmJA B 61
  ap := tmJA B 17
  en := tmJA B 62
  mR := tmJA B 63
  mB := tmJA B 64
  mP := tmJA B 65
  fR := tmJA B 66
  fC := tmJA B 67
  mD := tmJA B 68
  jmem := 1
  jf := 3

/-- **The blocks of the `J`-answer**, block `i` at `tmJA B i`. -/
def tmJLay (B : ℕ) : List (List Expr) :=
  let a := tmJA B
  let p := tmJPos B
  [ -- 0-5: top, nonempty case, prep, labels, `Aut_J`, output
    [tmJTopF (a 1)],
    [tmJNEF (a 2) (a 3) (a 4) (a 5)],
    [tmJPrepF (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)],
    [tmJLabsF (a 12) (a 13)],
    [tmJAutF (a 14) (p.sol + 1) (a 15) (a 16) p.swS (a 17)],
    [tmJOutF (a 18) (a 12) (a 17) (a 7) (a 19)],
    -- 6-11: prep parts
    [tmJPrepAF (a 20) (a 21) (a 22) (a 7) (a 23)],
    mkGroupFuns (a 7),
    [tmJLgF (a 22) (a 24) (a 26), tmJLgRowF (a 25), tmJLgEF],
    [tmJTlF (a 22) (a 27) (a 26), tmJTlEF],
    [tmJBetaF (a 28) (a 29), tmJLgPEF],
    linAbelianCoordinatesFuns (a 11) 5 17,
    -- 12-19
    mapFuns (a 12) (a 30),
    mapFuns (a 13) p.b,
    [tmJNsF (a 22) (a 31) (a 26), tmJNsRowF 10 (a 32)],
    [tmJS2F (a 33), tmJS2EF (p.b + 9)],
    [tmJTsF (a 34), tmJTsEF p.swS (a 30)],
    appendFuns (a 17),
    invFuns (a 18),
    redFuns (a 19) 0,
    -- 20-29
    [tmCsTabF (a 35) (a 22) (a 36) (a 18), tmCsTabEF],
    [tmJGF (a 35) (a 37), tmCsConjF (a 30)],
    rangeFuns (a 22),
    [tmJNqF (a 22) (a 38) (a 26), tmJNqRowF (a 32)],
    mapFuns (a 24) (a 8 + 1),
    mapFuns (a 25) (a 8 + 2),
    [tmJFlatF (a 26 + 1)] ++ foldlFuns (a 26 + 1) (a 26 + 4) ++ [tmJFlatStepF (a 17)],
    mapFuns (a 27) (a 9 + 1),
    mapFuns (a 28) (a 10 + 1),
    tmJVVecsFuns (a 29) 17,
    -- 30-38
    composeFuns (a 30),
    mapFuns (a 31) (a 14 + 1),
    mapFuns (a 32) p.locA,
    mapFuns (a 33) (a 15 + 1),
    mapFuns (a 34) (a 16 + 1),
    domFuns (a 35),
    mapFuns (a 36) (a 20 + 1),
    mapFuns (a 37) (a 21 + 1),
    mapFuns (a 38) (a 23 + 1),
    -- 39-60: the per-label program
    tmJHFuns p,
    replicateFuns (a 40),
    [tmJPairF (a 22) (a 42), tmJPairEF],
    mapFuns (a 42) (a 41 + 1),
    mapFuns (a 43) (p.b + 4),
    mapFuns (a 44) (p.b + 5),
    mapFuns (a 45) (p.b + 6),
    [linBitsDecodeF (a 46)],
    [linPermPowF (a 47) (a 30)],
    foldlFuns (a 48) (p.b + 8),
    [tmJLocAF (a 49 + 1) (a 41), tmJDsAF (a 22) (a 50), tmJDsAEF],
    mapFuns (a 50) (a 49 + 2),
    [tmJSwSF (a 18) (a 52) (a 53) (a 41), tmJSwDEF, tmJSwPEF],
    mapFuns (a 52) (a 51 + 1),
    mapFuns (a 53) (a 51 + 2),
    tmJSolFuns (a 54) 15,
    tmJVSumFuns (a 55) 17,
    mapFuns (a 56) (p.b + 12),
    [itParF (a 22) (a 58) (a 59), itInvB (a 60), itInvT, itParS],
    mapFuns (a 58) (a 57 + 1),
    foldlFuns (a 59) (a 57 + 3),
    filterFuns (a 60) (a 57 + 2),
    -- 61-68: the local transporter
    [tmJLMainF (a 22) (a 17) (a 63) (a 65) (a 68) (a 41), tmJLRowF (a 22) (a 64),
      tmJLBitF 1 (a 17) (a 30) (a 18), tmJLPiF (a 66) (a 67), tmJLRkF (a 62), tmJLColF,
      tmJLDF 3 (a 30) (a 18)],
    eqNatsFuns (a 62),
    mapFuns (a 63) (a 61 + 1),
    mapFuns (a 64) (a 61 + 2),
    mapFuns (a 65) (a 61 + 3),
    filterFuns (a 66) (a 61 + 4),
    filterFuns (a 67) (a 61 + 5),
    mapFuns (a 68) (a 61 + 6)]

theorem tmJLay_length (B : ℕ) : (tmJLay B).length = 69 := rfl

private theorem l_map (b f : ℕ) : (mapFuns b f).length = 3 := rfl
private theorem l_comp (b : ℕ) : (composeFuns b).length = 4 := rfl
private theorem l_inv (b : ℕ) : (invFuns b).length = 12 := rfl
private theorem l_app (b : ℕ) : (appendFuns b).length = 3 := rfl
private theorem l_fold (b f : ℕ) : (foldlFuns b f).length = 3 := rfl
private theorem l_rep (b : ℕ) : (replicateFuns b).length = 3 := rfl
private theorem l_eq (b : ℕ) : (eqNatsFuns b).length = 3 := rfl
private theorem l_mk (b : ℕ) : (mkGroupFuns b).length = 7 := rfl
private theorem l_rg (b : ℕ) : (rangeFuns b).length = 3 := rfl
private theorem l_flt (b f : ℕ) : (filterFuns b f).length = 3 := rfl
private theorem l_red (b j : ℕ) : (redFuns b j).length = 8 := rfl

theorem tmJLay_fit (B : ℕ) : ∀ l ∈ tmJLay B, l.length ≤ 1000 := by
  simp only [tmJLay, List.forall_mem_cons, List.length_cons, List.length_nil, List.length_append,
    l_map, l_comp, l_inv, l_app, l_fold, l_rep, l_eq, l_mk, l_rg, l_flt, l_red, length_domFuns,
    tmJSolFuns_length, tmJVSumFuns_length, tmJVVecsFuns_length, linAbelianCoordinatesFuns_length,
    tmJHFuns_length]
  and_intros
  all_goals first | omega | simp

/-- The code of the `J`-answer at base `B`. -/
def tmJFuns (B : ℕ) : List Expr := tmJBlk (tmJLay B)

theorem length_tmJFuns (B : ℕ) : (tmJFuns B).length = 69000 := by
  rw [tmJFuns, length_tmJBlk (tmJLay_fit B), tmJLay_length]

end GI.Impl
