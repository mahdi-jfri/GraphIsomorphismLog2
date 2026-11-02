import Workspace.Impl.AggWin
import Workspace.Impl.FreshColor

/-!
# The colors of a window call, in `GI.Lang`

A window call asks `Continue` on the lifted window state, whose colorings are `liftColor z` and
`liftColor (z ∘ τ)` on the extended color type `Option C` (`Workspace/Impl/AggWin.lean`). Its
canonical value holds the compressed codes `winCodesX`, `winCodesY` (`canon_window`). This file
computes them.

`wpFuns b d` (fifteen functions at base `b`, with the domain module of `DomRestrict.lean` at `d`),
on `[dv, xv, av]` (the parent's domain indicator, the parent's codes of `z`, and the positions `a`
of a lift of `τ`):

1. the identity list `[0, …, k-1]` (`range`);
2. the codes of `z ∘ a`: gather `xv` through `av`;
3. the raw codes `winRawX`, `winRawY`: entry `i` is `dv[i] · (code + 1)` (one map each);
4. their concatenation `winList`;
5. the compressed codes: `posOf winList` on each raw code (`mapPos_spec`).

`wp_spec`: the output is `[winCodesX, winCodesY]`, at cost at most `wpK (k + 1)⁸` when the parent's
codes are below `2k` (as on a canonical value).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {k : ℕ}

/-! ### The raw codes -/

/-- On `[[D, X], i]`: `D[i] · (X[i] + 1)`. -/
def wrF : Expr :=
  .arith .mul (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.arith .add (.get (.get (arg 0) (.nat 1)) (arg 1)) (.nat 1))

theorem wr_step {P : Program} {f : ℕ} (hf : P.funs[f]? = some wrF) (dI g : Fin k → ℕ)
    {B : ℕ} (hd : ∀ i, dI i ≤ 1) (hg : ∀ i, g i ≤ B) (i : Fin k) :
    FunDet P f (.list [.list [encFun dI, encFun g], .nat i]) (.nat (dI i * (g i + 1)))
      (1000 * (k + B + 2) ^ 2) := by
  set c := Val.list [encFun dI, encFun g]
  set vs : List Val := [c, .nat i]
  have g0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) (v := c) rfl
  have g1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) (v := .nat i) rfl
  have dD := Det.get' g0 (Det.nat 0) (v := encFun dI) rfl
  have dX := Det.get' g0 (Det.nat 1) (v := encFun g) rfl
  have dDi := Det.get' dD g1 (encFun_getElem? dI i)
  have dXi := Det.get' dX g1 (encFun_getElem? g i)
  have da := Det.arith' (op := .add) dXi (Det.nat 1) (z := g i + 1) rfl
  have dm := Det.arith' (op := .mul) dDi da (z := dI i * (g i + 1)) rfl
  refine FunDet.intro hf (dm.mono ?_)
  have w1 := wt_encFun_le dI (B := 1) hd
  have w2 := wt_encFun_le g hg
  have w3 := wt_list2_le (encFun dI) (encFun g)
  have w4 := wt_list2_le c (.nat i)
  have w5 := wt_nat_le (i : ℕ)
  have w6 := wt_nat_le (dI i)
  have w7 := wt_nat_le (g i)
  have hi := i.isLt
  have h1 := hd i
  have h2 := hg i
  have hm : dI i * (g i + 1) ≤ g i + 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h | h <;> rw [h] <;> omega
  have hc : c.wt = (Val.list [encFun dI, encFun g]).wt := rfl
  have hvs : (Val.list vs).wt = (Val.list [c, .nat i]).wt := rfl
  have q1 : k * (2 * 1 + 5) ≤ 7 * (k + B + 2) ^ 2 := by nlinarith
  have q2 : k * (2 * B + 5) ≤ 5 * (k + B + 2) ^ 2 := by nlinarith
  have q3 : k + B + 2 ≤ (k + B + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

/-- The list of the raw codes `dI i · (g i + 1)`. -/
def wrList (dI g : Fin k → ℕ) : List ℕ := (List.finRange k).map fun i => dI i * (g i + 1)

theorem wpEncPerm_one : encPerm (1 : Perm (Fin k)) =
    .list ((List.finRange k).map fun i : Fin k => Val.nat (i : ℕ)) := rfl

/-- `map wrF` at base `b` (four functions). -/
def wrMapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [wrF]

/-- **The raw codes.** -/
theorem wrMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (wrMapFuns b)) (dI g : Fin k → ℕ)
    {B : ℕ} (hd : ∀ i, dI i ≤ 1) (hg : ∀ i, g i ≤ B) :
    FunDet P b (.list [.list [encFun dI, encFun g], encPerm (1 : Perm (Fin k))])
      (natList (wrList dI g)) (10 ^ 6 * (k + B + 2) ^ 3) := by
  have hf : P.funs[b + 3]? = some wrF := by
    simpa [wrMapFuns, mapFuns, loopFuns] using h.right.single
  have hm := mapList_spec h.left (List.finRange k) (fun i : Fin k => Val.nat (i : ℕ))
    (fun i => Val.nat (dI i * (g i + 1))) (c := .list [encFun dI, encFun g])
    (B := 1000 * (k + B + 2) ^ 2)
    (fun a _ a' _ he => by simp only [Val.nat.injEq] at he; rw [Fin.ext he])
    (fun i _ => wr_step hf dI g hd hg i)
  rw [← wpEncPerm_one] at hm
  have e2 : Val.list ((List.finRange k).map fun i => Val.nat (dI i * (g i + 1))) =
      natList (wrList dI g) := by simp [natList, wrList, List.map_map, Function.comp_def]
  rw [e2] at hm
  refine hm.mono ?_
  simp only [List.length_finRange]
  set N := k + B + 2 with hN
  have w1 := wt_encFun_le dI (B := 1) hd
  have w2 := wt_encFun_le g hg
  have w3 := wt_list2_le (encFun dI) (encFun g)
  have w4 := wt_list2_le (.list [encFun dI, encFun g]) (encPerm (1 : Perm (Fin k)))
  have w5 := wt_encPerm_le (1 : Perm (Fin k))
  have w6 := wt_natList_le (xs := wrList dI g) (B := B + 1) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    have h1 := hd i
    have h2 := hg i
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h | h <;> rw [h] <;> omega)
  have hl : (wrList dI g).length = k := by simp [wrList]
  rw [hl] at w6
  have q1 : k * (2 * 1 + 5) ≤ 7 * N ^ 2 := by nlinarith
  have q2 : k * (2 * B + 5) ≤ 5 * N ^ 2 := by nlinarith
  have q3 : k * (2 * (B + 1) + 5) ≤ 7 * N ^ 2 := by nlinarith
  have q4 : (k + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q5 : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW : (Val.list [Val.list [encFun dI, encFun g], encPerm (1 : Perm (Fin k))]).wt +
      (natList (wrList dI g)).wt + 1 ≤ 100 * N ^ 2 := by omega
  have a1 : k * (1000 * N ^ 2) ≤ 1000 * N ^ 3 := by
    calc k * (1000 * N ^ 2) ≤ N * (1000 * N ^ 2) := Nat.mul_le_mul_right _ (by omega)
      _ = 1000 * N ^ 3 := by ring
  have a2 : mapK * (k + 1) * ((Val.list [Val.list [encFun dI, encFun g],
      encPerm (1 : Perm (Fin k))]).wt + (natList (wrList dI g)).wt + 1) ≤ mapK * N * (100 * N ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hW
  have a3 : mapK * N * (100 * N ^ 2) = 100000 * N ^ 3 := by simp only [mapK]; ring
  omega

/-! ### The module -/

/-- The body of the module on `[dv, xv, av]`, with the domain module at `d`. -/
def wpEntry (b d : ℕ) : Expr :=
  .letE (.call (b + 1) (.length (arg 0)))
    (.letE (.call (b + 4) (mk2 (arg 1) (arg 2)))
      (.letE (.call (b + 8) (mk2 (mk2 (arg 0) (arg 1)) (.var 1)))
        (.letE (.call (b + 8) (mk2 (mk2 (arg 0) (.var 2)) (.var 1)))
          (.letE (.call (b + 12) (mk2 (.var 3) (.var 4)))
            (mk2 (.call (d + 9) (mk2 (.var 5) (.var 3)))
              (.call (d + 9) (mk2 (.var 5) (.var 4))))))))

/-- The module at base `b` (fifteen functions). -/
def wpFuns (b d : ℕ) : List Expr :=
  [wpEntry b d] ++ rangeFuns (b + 1) ++ gatherFuns (b + 4) ++ wrMapFuns (b + 8) ++ appendFuns (b + 12)

/-- The cost constant of the module. -/
def wpK : ℕ := 10 ^ 13

/-- Append, with the result known. -/
theorem wpAppend_det {P : Program} {b : ℕ} (h : P.HasAt b (appendFuns b)) (xs ys : List ℕ) {W : ℕ}
    (hx : (natList xs).wt ≤ W) (hy : (natList ys).wt ≤ W) (hl : ys.length ≤ W) :
    FunDet P b (.list [natList xs, natList ys]) (natList (xs ++ ys))
      (loopModK * (W + 1) * (20 * W + 20)) := by
  refine (append_spec h (xs.map Val.nat) (ys.map Val.nat)).mono fun w c hw => ⟨?_, ?_⟩
  · rw [hw.1]; simp [natList]
  · have hc := hw.2
    rw [hw.1] at hc
    have e1 : Val.list (xs.map Val.nat ++ ys.map Val.nat) = natList (xs ++ ys) := by simp [natList]
    rw [e1] at hc
    have w1 := wt_list2_le (natList xs) (natList ys)
    have w2 : (natList (xs ++ ys)).wt ≤ 3 * ((natList xs).wt + (natList ys).wt) + 4 := by
      have h0 := wt_list_le ((xs ++ ys).map Val.nat)
      have h1 := sum_wt_lt_wt_list (xs.map Val.nat)
      have h2 := sum_wt_lt_wt_list (ys.map Val.nat)
      have h3 := length_lt_wt_list (xs.map Val.nat)
      have h4 := length_lt_wt_list (ys.map Val.nat)
      simp only [List.map_append, List.sum_append, List.length_append] at h0
      have : (natList xs).wt = (Val.list (xs.map Val.nat)).wt := rfl
      have : (natList ys).wt = (Val.list (ys.map Val.nat)).wt := rfl
      have : (natList (xs ++ ys)).wt = (Val.list (xs.map Val.nat ++ ys.map Val.nat)).wt := by
        simp [natList]
      omega
    have e2 : (List.map Val.nat ys).length = ys.length := by simp
    rw [e2] at hc
    have e3 : (Val.list [.list (xs.map Val.nat), .list (ys.map Val.nat)]).wt =
      (Val.list [natList xs, natList ys]).wt := rfl
    rw [e3] at hc
    have : loopModK * (ys.length + 1) * ((Val.list [natList xs, natList ys]).wt + ys.length +
        (natList (xs ++ ys)).wt + 1) ≤ loopModK * (W + 1) * (20 * W + 20) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    exact hc.trans this

/-- The list of both raw codes. -/
def wpList (dI g : Fin k → ℕ) (a : Perm (Fin k)) : List ℕ := wrList dI g ++ wrList dI (g ∘ a)

theorem wt_wrList_le (dI g : Fin k → ℕ) {B : ℕ} (hd : ∀ i, dI i ≤ 1) (hg : ∀ i, g i ≤ B) :
    (natList (wrList dI g)).wt ≤ 8 * (k + B + 2) ^ 2 := by
  have w6 := wt_natList_le (xs := wrList dI g) (B := B + 1) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    have h1 := hd i
    have h2 := hg i
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h | h <;> rw [h] <;> omega)
  have hl : (wrList dI g).length = k := by simp [wrList]
  rw [hl] at w6
  have : k * (2 * (B + 1) + 5) ≤ 7 * (k + B + 2) ^ 2 := by nlinarith
  have : 4 ≤ (k + B + 2) ^ 2 := by nlinarith
  omega

/-- **The window colors, for any indicator and codes.** -/
theorem wp_spec_gen {P : Program} {b d : ℕ} (hb : P.HasAt b (wpFuns b d)) (hd : DomAt P d)
    (dI g : Fin k → ℕ) (a : Perm (Fin k)) {B : ℕ} (hdI : ∀ i, dI i ≤ 1) (hg : ∀ i, g i ≤ B) :
    FunDet P b (.list [encFun dI, encFun g, encPerm a])
      (.list [natList ((wrList dI g).map (posOf (wpList dI g a))),
        natList ((wrList dI (g ∘ a)).map (posOf (wpList dI g a)))])
      (wpK * (k + B + 2) ^ 6) := by
  have hentry : P.funs[b]? = some (wpEntry b d) := by
    simpa using (hb.block 0 (gs := [wpEntry b d]) (by rfl)).single
  have hrange : P.HasAt (b + 1) (rangeFuns (b + 1)) := hb.block 1 (by rfl)
  have hgat : P.HasAt (b + 4) (gatherFuns (b + 4)) := hb.block 4 (by rfl)
  have hwr : P.HasAt (b + 8) (wrMapFuns (b + 8)) := hb.block 8 (by rfl)
  have happ : P.HasAt (b + 12) (appendFuns (b + 12)) := hb.block 12 (by rfl)
  have hga : ∀ i, (g ∘ a) i ≤ B := fun i => hg (a i)
  set N := k + B + 2 with hN
  set V := Val.list [encFun dI, encFun g, encPerm a] with hV
  set I := encPerm (1 : Perm (Fin k))
  set G := encFun (g ∘ a)
  set RX := natList (wrList dI g)
  set RY := natList (wrList dI (g ∘ a))
  set LL := natList (wpList dI g a)
  -- the identity list
  have dl : Det P [V] (.length (arg 0)) (.nat k) (2 * V.wt + 5 + (encFun dI).wt + 1 + k + 3) := by
    have := Det.length (Det.arg' (P := P) (vs := [encFun dI, encFun g, encPerm a]) (rest := [])
      (j := 0) (v := .list ((List.finRange k).map fun i => Val.nat (dI i))) rfl)
    simp only [List.length_map, List.length_finRange] at this
    have hVV : V.wt = (Val.list [encFun dI, encFun g, encPerm a]).wt := rfl
    exact this.mono (by have : (encFun dI).wt = (Val.list ((List.finRange k).map fun i =>
      Val.nat (dI i))).wt := rfl; omega)
  have d1 := Det.call dl (range_det hrange k)
  -- the codes of `g ∘ a`
  have hav : encPerm a = natList ((List.finRange k).map fun i => ((a i : Fin k) : ℕ)) := by
    rw [encPerm_eq_encFun, encFun_eq_natList]
  have hgath := gather_spec hgat (L := (List.finRange k).map fun i => Val.nat (g i))
    (is := (List.finRange k).map fun i => ((a i : Fin k) : ℕ)) (fun i hi => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi; simp)
  have eG : Val.list (((List.finRange k).map fun i => ((a i : Fin k) : ℕ)).map fun i =>
      ((List.finRange k).map fun i => Val.nat (g i)).getD i (.nat 0)) = G := by
    simp only [List.map_map, G, encFun]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    rw [getD_finRange_map _ _ (a i).isLt]
  rw [eG, ← hav] at hgath
  have d2 := Det.call (Det.mk2 (Det.arg' (P := P) (vs := [encFun dI, encFun g, encPerm a])
    (rest := [I]) (j := 1) (v := encFun g) rfl) (Det.arg' (P := P)
      (vs := [encFun dI, encFun g, encPerm a]) (rest := [I]) (j := 2) (v := encPerm a) rfl)) hgath
  -- the raw codes
  have d3 := Det.call (Det.mk2 (Det.mk2 (Det.arg' (P := P) (vs := [encFun dI, encFun g, encPerm a])
    (rest := [I, G]) (j := 0) (v := encFun dI) rfl) (Det.arg' (P := P)
      (vs := [encFun dI, encFun g, encPerm a]) (rest := [I, G]) (j := 1) (v := encFun g) rfl))
    (Det.var' (P := P) (env := [V, I, G]) (i := 1) (v := I) rfl)) (wrMap_spec hwr dI g hdI hg)
  have d4 := Det.call (Det.mk2 (Det.mk2 (Det.arg' (P := P) (vs := [encFun dI, encFun g, encPerm a])
    (rest := [I, G, RX]) (j := 0) (v := encFun dI) rfl)
      (Det.var' (P := P) (env := [V, I, G, RX]) (i := 2) (v := G) rfl))
    (Det.var' (P := P) (env := [V, I, G, RX]) (i := 1) (v := I) rfl))
    (wrMap_spec hwr dI (g ∘ a) hdI hga)
  -- weights
  have wX := wt_wrList_le dI g hdI hg
  have wY := wt_wrList_le dI (g ∘ a) hdI hga
  have hlY : (wrList dI (g ∘ a)).length ≤ 8 * N ^ 2 := by
    have : (wrList dI (g ∘ a)).length = k := by simp [wrList]
    have : k ≤ N ^ 2 := le_trans (by omega) (Nat.le_self_pow (by norm_num) N)
    omega
  have d5 := Det.call (Det.mk2 (Det.var' (P := P) (env := [V, I, G, RX, RY]) (i := 3) (v := RX) rfl)
    (Det.var' (P := P) (env := [V, I, G, RX, RY]) (i := 4) (v := RY) rfl))
    (wpAppend_det happ (wrList dI g) (wrList dI (g ∘ a)) wX wY hlY)
  have wL : LL.wt ≤ 3 * (RX.wt + RY.wt) + 4 := by
    have h0 := wt_list_le ((wpList dI g a).map Val.nat)
    have h1 := sum_wt_lt_wt_list ((wrList dI g).map Val.nat)
    have h2 := sum_wt_lt_wt_list ((wrList dI (g ∘ a)).map Val.nat)
    have h3 := length_lt_wt_list ((wrList dI g).map Val.nat)
    have h4 := length_lt_wt_list ((wrList dI (g ∘ a)).map Val.nat)
    simp only [wpList, List.map_append, List.sum_append, List.length_append] at h0
    have : RX.wt = (Val.list ((wrList dI g).map Val.nat)).wt := rfl
    have : RY.wt = (Val.list ((wrList dI (g ∘ a)).map Val.nat)).wt := rfl
    have : LL.wt = (Val.list ((wrList dI g).map Val.nat ++ (wrList dI (g ∘ a)).map Val.nat)).wt := by
      simp [LL, natList, wpList]
    omega
  have eRX : RX.wt = (natList (wrList dI g)).wt := rfl
  have eRY : RY.wt = (natList (wrList dI (g ∘ a))).wt := rfl
  have eN : N ^ 2 = (k + B + 2) ^ 2 := rfl
  have hN4 : 4 ≤ N ^ 2 := by nlinarith
  have hA : LL.wt + RX.wt ≤ 70 * N ^ 2 := by omega
  have hA' : LL.wt + RY.wt ≤ 70 * N ^ 2 := by omega
  have p1 := mapPos_spec hd (wpList dI g a) (wrList dI g) hA
  have p2 := mapPos_spec hd (wpList dI g a) (wrList dI (g ∘ a)) hA'
  have d6 := Det.mk2
    (Det.call (Det.mk2 (Det.var' (P := P) (env := [V, I, G, RX, RY, LL]) (i := 5) (v := LL) rfl)
      (Det.var' (P := P) (env := [V, I, G, RX, RY, LL]) (i := 3) (v := RX) rfl)) p1)
    (Det.call (Det.mk2 (Det.var' (P := P) (env := [V, I, G, RX, RY, LL]) (i := 5) (v := LL) rfl)
      (Det.var' (P := P) (env := [V, I, G, RX, RY, LL]) (i := 4) (v := RY) rfl)) p2)
  refine FunDet.intro hentry ((Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4
    (Det.letE d5 d6))))).mono ?_)
  -- the weights
  have n2 : 4 ≤ N ^ 2 := hN4
  have kN : k + 1 ≤ N := by omega
  have k2 : (k + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left kN 2
  have q1 : k * (2 * 1 + 5) ≤ 7 * N ^ 2 := by nlinarith
  have q2 : k * (2 * B + 5) ≤ 7 * N ^ 2 := by nlinarith
  have q3 : k * (2 * (2 * k) + 5) ≤ 7 * N ^ 2 := by nlinarith
  have wd := wt_encFun_le dI (B := 1) hdI
  have wg := wt_encFun_le g hg
  have wG : G.wt ≤ k * (2 * B + 5) + 4 := wt_encFun_le (g ∘ a) hga
  have wa := wt_encPerm_le a
  have wI : I.wt ≤ 4 * (k + 1) ^ 2 := wt_encPerm_le _
  have wV := wt_list3_le (encFun dI) (encFun g) (encPerm a)
  have eV : V.wt = (Val.list [encFun dI, encFun g, encPerm a]).wt := rfl
  have w1 := wt_list2_le (encFun g) (encPerm a)
  have e1 : (Val.list [Val.list (List.map (fun i => Val.nat (g i)) (List.finRange k)), encPerm a]).wt =
    (Val.list [encFun g, encPerm a]).wt := rfl
  have w2 := wt_list2_le (encFun dI) (encFun g)
  have w3 := wt_list2_le (Val.list [encFun dI, encFun g]) I
  have w4 := wt_list2_le (encFun dI) G
  have w5 := wt_list2_le (Val.list [encFun dI, G]) I
  have w6 := wt_list2_le RX RY
  have w7 := wt_list2_le LL RX
  have w8 := wt_list2_le LL RY
  have eL : (natList (wrList dI g ++ wrList dI (g ∘ a))).wt = LL.wt := rfl
  have hpos : ∀ l : List ℕ, l.length = k → (natList (l.map (posOf (wpList dI g a)))).wt ≤
      7 * N ^ 2 + 4 := by
    intro l hl
    have h1 := wt_natList_le (xs := l.map (posOf (wpList dI g a))) (B := 2 * k) (by
      intro x hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      have := posOf_le (wpList dI g a) y
      have : (wpList dI g a).length = 2 * k := by simp [wpList, wrList]; ring
      omega)
    rw [List.length_map, hl] at h1
    omega
  have o1 := hpos (wrList dI g) (by simp [wrList])
  have o2 := hpos (wrList dI (g ∘ a)) (by simp [wrList])
  have w9 := wt_list2_le (natList ((wrList dI g).map (posOf (wpList dI g a))))
    (natList ((wrList dI (g ∘ a)).map (posOf (wpList dI g a))))
  -- the large terms
  have n1 : 1 ≤ N ^ 2 := by omega
  have p26 : N ^ 2 ≤ N ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p36 : N ^ 3 ≤ N ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have e6 : N ^ 6 = (N ^ 2) ^ 3 := by ring
  have e4 : (N ^ 2) ^ 2 = N ^ 4 := by ring
  have p46 : N ^ 4 ≤ N ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have g1 : gatherK * ((Val.list [encFun g, encPerm a]).wt + 1) ^ 3 ≤ gatherK * 29791 * N ^ 6 := by
    have : (Val.list [encFun g, encPerm a]).wt + 1 ≤ 31 * N ^ 2 := by omega
    have := Nat.pow_le_pow_left this 3
    rw [e6]
    calc _ ≤ gatherK * (31 * N ^ 2) ^ 3 := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have g3 : loopModK * (8 * (k + B + 2) ^ 2 + 1) * (20 * (8 * (k + B + 2) ^ 2) + 20) ≤
      loopModK * 1620 * N ^ 6 := by
    have h1 : 8 * (k + B + 2) ^ 2 + 1 ≤ 9 * N ^ 2 := by omega
    have h2 : 20 * (8 * (k + B + 2) ^ 2) + 20 ≤ 180 * N ^ 2 := by omega
    calc _ ≤ loopModK * (9 * N ^ 2) * (180 * N ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ = loopModK * 1620 * (N ^ 2) ^ 2 := by ring
      _ ≤ _ := by rw [e4]; exact Nat.mul_le_mul_left _ p46
  have g4 : 10 ^ 7 * (70 * N ^ 2 + 1) ^ 3 ≤ 10 ^ 7 * 357911 * N ^ 6 := by
    have := Nat.pow_le_pow_left (show 70 * N ^ 2 + 1 ≤ 71 * N ^ 2 by omega) 3
    rw [e6]
    calc _ ≤ 10 ^ 7 * (71 * N ^ 2) ^ 3 := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have g5 : (k + 1) ^ 3 ≤ N ^ 6 := (Nat.pow_le_pow_left kN 3).trans p36
  have eN3 : (k + B + 2) ^ 3 = N ^ 3 := rfl
  have g2 : (k + B + 2) ^ 3 ≤ N ^ 6 := by rw [eN3]; exact p36
  rw [e1]
  have eI : (encPerm (1 : Perm (Fin k))).wt = I.wt := rfl
  clear_value N V I G RX RY LL
  have wd' : (encFun dI).wt ≤ 7 * N ^ 2 + 4 := by omega
  simp only [gatherK, loopModK, wpK] at g1 g3 ⊢
  omega

/-! ### The window codes -/

section Win

variable {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
  [Fintype S.dom]

open Classical in
theorem wrList_winRawX (z : Ω → C) :
    wrList (fun i => if e.symm i ∈ S.dom then 1 else 0) (fun i => c (z (e.symm i))) =
      (List.finRange k).map (winRawX e c S z) := by
  unfold wrList winRawX
  refine List.map_congr_left fun i _ => ?_
  split_ifs <;> simp_all

open Classical in
theorem wrList_winRawY (z : Ω → C) (a : Perm (Fin k)) :
    wrList (fun i => if e.symm i ∈ S.dom then 1 else 0) ((fun i => c (z (e.symm i))) ∘ a) =
      (List.finRange k).map (winRawY e c S z a) := by
  unfold wrList winRawY
  refine List.map_congr_left fun i _ => ?_
  split_ifs <;> simp_all

/-- **The window colors.** On the parent's domain indicator `dv`, the parent's codes `xv` of `z`
(below `2k`) and the positions `a` of a lift of `τ`, the module returns the compressed codes of
both colorings of the window state. -/
theorem wp_spec {P : Program} {b d : ℕ} (hb : P.HasAt b (wpFuns b d)) (hd : DomAt P d)
    {dv xv : Val} (hdv : DomVal e dv S.dom) (z : Ω → C) (hxv : ColorVal e c xv z)
    (hcode : ∀ v, c (z v) < 2 * k) (a : Perm (Fin k)) :
    FunDet P b (.list [dv, xv, encPerm a])
      (.list [natList (winCodesX e c S z a), natList (winCodesY e c S z a)])
      (wpK * (3 * k + 2) ^ 6) := by
  classical
  have h := wp_spec_gen hb hd (fun i => if e.symm i ∈ S.dom then 1 else 0)
    (fun i => c (z (e.symm i))) a (B := 2 * k) (fun i => by beta_reduce; split_ifs <;> omega)
    (fun i => (hcode _).le)
  have e1 : (k + 2 * k + 2) = 3 * k + 2 := by ring
  rw [e1] at h
  have hL : wpList (fun i => if e.symm i ∈ S.dom then 1 else 0) (fun i => c (z (e.symm i))) a =
      winList e c S z a := by
    unfold wpList winList
    rw [wrList_winRawX, wrList_winRawY]
  rw [hL, wrList_winRawX, wrList_winRawY] at h
  unfold DomVal at hdv
  unfold ColorVal at hxv
  subst hdv hxv
  convert h using 3 <;> simp [winCodesX, winCodesY, List.map_map, Function.comp_def]

end Win

end GI.Impl
