module

public import Workspace.Impl.VStabLinVec
public import Workspace.Lang.Lib.Fold

@[expose] public section

/-!
# Sifting a vector through echelon rows

A row is a pivot `j` with two vectors: the main part `x` (where pivots live) and a tag `t`
(which records how the row was made). A vector pair `(x, t)` is sifted through the rows in
order: for a row `(j, rx, rt)` with `c = x[j]`, replace `x` by `x - c rx` and `t` by `t - c rt`,
modulo `p`.

* `vsSiftStepFuns`: one step, on `[p, (x, t), row]`; `vsSiftStep_spec`.
* `vsSiftFuns`: the `foldl` of the steps over a list of rows; `vsSift_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- `x - c r` modulo `p` (for `c < p`). -/
def vsAxpy (p c : ℕ) (x r : List ℕ) : List ℕ := vsLin p 1 (p - c) x r

/-- An echelon row: pivot, main part, tag. -/
structure VsRow where
  j : ℕ
  x : List ℕ
  t : List ℕ

/-- The value of a row: `[j, natList x, natList t]`. -/
def VsRow.val (r : VsRow) : Val := .list [.nat r.j, natList r.x, natList r.t]

/-- The value of a vector pair: `[natList x, natList t]`. -/
def vsPairVal (xt : List ℕ × List ℕ) : Val := .list [natList xt.1, natList xt.2]

/-- One sifting step. -/
def vsSiftStep (p : ℕ) (xt : List ℕ × List ℕ) (r : VsRow) : List ℕ × List ℕ :=
  (vsAxpy p (xt.1.getD r.j 0) xt.1 r.x, vsAxpy p (xt.1.getD r.j 0) xt.2 r.t)

/-- Sifting through a list of rows. -/
def vsSift (p : ℕ) (rows : List VsRow) (xt : List ℕ × List ℕ) : List ℕ × List ℕ :=
  rows.foldl (vsSiftStep p) xt

/-- The step, on `[p, (x, t), row]`, calling the combination at `lin`. -/
def vsSiftStepF (lin : ℕ) : Expr :=
  .letE (.get (.get (arg 1) (.nat 0)) (.get (arg 2) (.nat 0)))
    (.letE (.arith .sub (arg 0) (.var 1))
      (mk2
        (.call lin (.snoc (mk4 (arg 0) (.nat 1) (.var 2) (.get (arg 1) (.nat 0)))
          (.get (arg 2) (.nat 1))))
        (.call lin (.snoc (mk4 (arg 0) (.nat 1) (.var 2) (.get (arg 1) (.nat 1)))
          (.get (arg 2) (.nat 2))))))

/-- Numbers and lengths of a vector pair and a row are at most `N`, entries of the pair below
`p`, and the row's parts are at least as long as the pair's. -/
structure VsFits (p N : ℕ) (xt : List ℕ × List ℕ) (r : VsRow) : Prop where
  hx : ∀ y ∈ xt.1, y < p
  ht : ∀ y ∈ xt.2, y < p
  hrx : ∀ y ∈ r.x, y ≤ N
  hrt : ∀ y ∈ r.t, y ≤ N
  lx : xt.1.length ≤ N
  lt : xt.2.length ≤ N
  lrx : r.x.length ≤ N
  lrt : r.t.length ≤ N
  jx : r.j < xt.1.length
  xx : xt.1.length ≤ r.x.length
  tt : xt.2.length ≤ r.t.length
  j : r.j ≤ N

theorem wt_vsPairVal_le {p N : ℕ} {xt : List ℕ × List ℕ} (hpN : p ≤ N)
    (hx : ∀ y ∈ xt.1, y < p) (ht : ∀ y ∈ xt.2, y < p) (lx : xt.1.length ≤ N)
    (lt : xt.2.length ≤ N) : (vsPairVal xt).wt ≤ 20 * (N + 1) ^ 2 + 6 := by
  have h1 := wt_natList_le_sq (fun y hy => (hx y hy).le.trans hpN) lx
  have h2 := wt_natList_le_sq (fun y hy => (ht y hy).le.trans hpN) lt
  have := wt_list2_le (natList xt.1) (natList xt.2)
  simp only [vsPairVal]
  omega

theorem wt_vsRowVal_le {N : ℕ} {r : VsRow} (hrx : ∀ y ∈ r.x, y ≤ N) (hrt : ∀ y ∈ r.t, y ≤ N)
    (lrx : r.x.length ≤ N) (lrt : r.t.length ≤ N) (hj : r.j ≤ N) :
    r.val.wt ≤ 40 * (N + 1) ^ 2 := by
  have h1 := wt_natList_le_sq hrx lrx
  have h2 := wt_natList_le_sq hrt lrt
  have := wt_list3_le (.nat r.j) (natList r.x) (natList r.t)
  have := wt_nat_le r.j
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  simp only [VsRow.val]
  omega

theorem vsSiftStep_spec {P : Program} {f lin : ℕ} (hf : P.funs[f]? = some (vsSiftStepF lin))
    (hl : P.HasAt lin (vsLinFuns lin)) {p N : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    {xt : List ℕ × List ℕ} {r : VsRow} (H : VsFits p N xt r) :
    FunDet P f (.list [.nat p, vsPairVal xt, r.val]) (vsPairVal (vsSiftStep p xt r))
      (3 * 10 ^ 6 * (N + 1) ^ 3) := by
  set A := Val.list [.nat p, vsPairVal xt, r.val] with hA
  set c := xt.1.getD r.j 0 with hc
  have hcp : c < p := H.hx c (by simp [hc, List.getD_eq_getElem?_getD, H.jx])
  have dA := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, vsPairVal xt, r.val]) (j := 1) rfl
  have dR := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, vsPairVal xt, r.val]) (j := 2) rfl
  have dx := Det.get' dA (Det.nat 0) (show [natList xt.1, natList xt.2][0]? = some _ from rfl)
  have dj := Det.get' dR (Det.nat 0)
    (show [Val.nat r.j, natList r.x, natList r.t][0]? = some _ from rfl)
  have dc := Det.get' dx dj (natList_getElem? H.jx)
  -- environment after the first `let`
  set E1 := [A, Val.nat c]
  have dp1 := Det.arg' (P := P) (rest := [Val.nat c]) (vs := [Val.nat p, vsPairVal xt, r.val])
    (j := 0) rfl
  have ds := Det.arith' (op := .sub) dp1 (Det.var' (P := P) (env := E1) (i := 1) rfl) rfl
  -- environment after the second `let`
  set E2 := [A, Val.nat c, Val.nat (p - c)]
  have hlin : ∀ (v u : List ℕ), (∀ y ∈ v, y ≤ N) → (∀ y ∈ u, y ≤ N) → v.length ≤ N →
      u.length ≤ N → v.length ≤ u.length →
      FunDet P lin (vsLinArg p 1 (p - c) v u) (natList (vsAxpy p c v u))
        (10 ^ 6 * (N + 1) ^ 3) := fun v u hv hu hlv hlu hvu =>
    vsLin_spec hl hp hv hu hlv hlu hvu hpN (by omega) (by omega)
  have g0 := Det.arg' (P := P) (rest := [Val.nat c, Val.nat (p - c)])
    (vs := [Val.nat p, vsPairVal xt, r.val]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := [Val.nat c, Val.nat (p - c)])
    (vs := [Val.nat p, vsPairVal xt, r.val]) (j := 1) rfl
  have g2 := Det.arg' (P := P) (rest := [Val.nat c, Val.nat (p - c)])
    (vs := [Val.nat p, vsPairVal xt, r.val]) (j := 2) rfl
  have dv2 := Det.var' (P := P) (env := E2) (i := 2) rfl
  have a1 := Det.snoc (Det.mk4 g0 (Det.nat 1) dv2
    (Det.get' g1 (Det.nat 0) (show [natList xt.1, natList xt.2][0]? = some _ from rfl)))
    (Det.get' g2 (Det.nat 1) (show [Val.nat r.j, natList r.x, natList r.t][1]? = some _ from rfl))
  have a2 := Det.snoc (Det.mk4 g0 (Det.nat 1) dv2
    (Det.get' g1 (Det.nat 1) (show [natList xt.1, natList xt.2][1]? = some _ from rfl)))
    (Det.get' g2 (Det.nat 2) (show [Val.nat r.j, natList r.x, natList r.t][2]? = some _ from rfl))
  have hxN : ∀ y ∈ xt.1, y ≤ N := fun y hy => (H.hx y hy).le.trans hpN
  have htN : ∀ y ∈ xt.2, y ≤ N := fun y hy => (H.ht y hy).le.trans hpN
  have c1 := Det.call a1 (hlin xt.1 r.x hxN H.hrx H.lx H.lrx H.xx)
  have c2 := Det.call a2 (hlin xt.2 r.t htN H.hrt H.lt H.lrt H.tt)
  have dm := Det.mk2 c1 c2
  refine FunDet.intro hf ((Det.letE dc (Det.letE ds dm)).mono ?_)
  -- the cost
  have wP := wt_vsPairVal_le hpN H.hx H.ht H.lx H.lt
  have wR := wt_vsRowVal_le H.hrx H.hrt H.lrx H.lrt H.j
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN3 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hlt1 : ∀ y ∈ vsAxpy p c xt.1 r.x, y < p := vsLin_lt hp _ _
  have hlt2 : ∀ y ∈ vsAxpy p c xt.2 r.t, y < p := vsLin_lt hp _ _
  have wO := wt_vsPairVal_le (xt := (vsAxpy p c xt.1 r.x, vsAxpy p c xt.2 r.t)) hpN hlt1 hlt2
    (by simp only [vsAxpy, vsLin_length]; exact H.lx)
    (by simp only [vsAxpy, vsLin_length]; exact H.lt)
  have w3 := wt_list3_le (.nat p) (vsPairVal xt) r.val
  have wl1 := wt_natList_le_sq hxN H.lx
  have wl2 := wt_natList_le_sq htN H.lt
  have wl3 := wt_natList_le_sq H.hrx H.lrx
  have wl4 := wt_natList_le_sq H.hrt H.lrt
  have wa1 := wt_vsLinArg_le (p := p) (a := 1) (b := p - c) hxN H.hrx H.lx H.lrx hpN (by omega)
    (by omega)
  have wa2 := wt_vsLinArg_le (p := p) (a := 1) (b := p - c) htN H.hrt H.lt H.lrt hpN (by omega)
    (by omega)
  have wo1 := wt_natList_le_sq (fun y hy => (hlt1 y hy).le.trans hpN)
    (by simp only [vsAxpy, vsLin_length]; exact H.lx)
  have wo2 := wt_natList_le_sq (fun y hy => (hlt2 y hy).le.trans hpN)
    (by simp only [vsAxpy, vsLin_length]; exact H.lt)
  have wp := wt_nat_le p
  have wc := wt_nat_le c
  have wpc := wt_nat_le (p - c)
  have wj := wt_nat_le r.j
  have e1 : (Val.list [Val.nat p, .nat 1, .nat (p - c), natList xt.1, natList r.x]).wt =
    (vsLinArg p 1 (p - c) xt.1 r.x).wt := rfl
  have e2 : (Val.list [Val.nat p, .nat 1, .nat (p - c), natList xt.2, natList r.t]).wt =
    (vsLinArg p 1 (p - c) xt.2 r.t).wt := rfl
  have eO : (Val.list [natList (vsAxpy p c xt.1 r.x), natList (vsAxpy p c xt.2 r.t)]).wt =
    (vsPairVal (vsSiftStep p xt r)).wt := rfl
  have e4 : (Val.list [natList (vsAxpy p c xt.1 r.x), natList (vsAxpy p c xt.2 r.t)]) =
    vsPairVal (vsSiftStep p xt r) := rfl
  have l1 : (Val.list [Val.nat p, Val.nat 1, Val.nat (p - c)]).wt ≤ 5 * (N + 1) ^ 2 + 20 := by
    have := wt_list3_le (.nat p) (.nat 1) (.nat (p - c)); have := wt_nat_le 1; omega
  have l2 := wt_list4_le (.nat p) (.nat 1) (.nat (p - c)) (natList xt.1)
  have l3 := wt_list4_le (.nat p) (.nat 1) (.nat (p - c)) (natList xt.2)
  have l4 := wt_list_snoc_le [Val.nat p, .nat 1, .nat (p - c), natList xt.1] (natList r.x)
  have l5 := wt_list_snoc_le [Val.nat p, .nat 1, .nat (p - c), natList xt.2] (natList r.t)
  have w1 := wt_nat_le 1
  have wO' : (vsPairVal (vsSiftStep p xt r)).wt ≤ 20 * (N + 1) ^ 2 + 6 := wO
  have wg := wt_nat_le (xt.1.getD r.j 0)
  have esub : BinOp.sub.eval p c = p - c := rfl
  have hj := H.j
  have hgN : xt.1.getD r.j 0 ≤ N := by omega
  simp only [List.cons_append, List.nil_append] at *
  rw [e4]
  omega

/-! ### The full sift -/

/-- A vector pair whose entries are below `p` and whose lengths are at most `N`. -/
structure VsPairFits (p N : ℕ) (xt : List ℕ × List ℕ) : Prop where
  hx : ∀ y ∈ xt.1, y < p
  ht : ∀ y ∈ xt.2, y < p
  lx : xt.1.length ≤ N
  lt : xt.2.length ≤ N

/-- A row fits pairs of lengths `lx` and `lt`: its numbers are at most `N`, its pivot is below
`lx`, and its parts are at least as long as the pair's. -/
structure VsRowFits (N lx lt : ℕ) (r : VsRow) : Prop where
  hrx : ∀ y ∈ r.x, y ≤ N
  hrt : ∀ y ∈ r.t, y ≤ N
  lrx : r.x.length ≤ N
  lrt : r.t.length ≤ N
  jx : r.j < lx
  xx : lx ≤ r.x.length
  tt : lt ≤ r.t.length
  j : r.j ≤ N

theorem VsFits.of {p N : ℕ} {xt : List ℕ × List ℕ} {r : VsRow} (hP : VsPairFits p N xt)
    (hR : VsRowFits N xt.1.length xt.2.length r) : VsFits p N xt r :=
  ⟨hP.hx, hP.ht, hR.hrx, hR.hrt, hP.lx, hP.lt, hR.lrx, hR.lrt, hR.jx, hR.xx, hR.tt, hR.j⟩

theorem vsSiftStep_length (p : ℕ) (xt : List ℕ × List ℕ) (r : VsRow) :
    (vsSiftStep p xt r).1.length = xt.1.length ∧ (vsSiftStep p xt r).2.length = xt.2.length := by
  simp [vsSiftStep, vsAxpy, vsLin_length]

theorem vsSiftStep_fits {p N : ℕ} (hp : 0 < p) {xt : List ℕ × List ℕ} (h : VsPairFits p N xt)
    (r : VsRow) : VsPairFits p N (vsSiftStep p xt r) := by
  obtain ⟨e1, e2⟩ := vsSiftStep_length p xt r
  exact ⟨vsLin_lt hp _ _, vsLin_lt hp _ _, e1 ▸ h.lx, e2 ▸ h.lt⟩

theorem vsSift_length (p : ℕ) (rows : List VsRow) (xt : List ℕ × List ℕ) :
    (vsSift p rows xt).1.length = xt.1.length ∧ (vsSift p rows xt).2.length = xt.2.length := by
  induction rows generalizing xt with
  | nil => exact ⟨rfl, rfl⟩
  | cons r rs ih =>
    obtain ⟨a1, a2⟩ := ih (vsSiftStep p xt r)
    obtain ⟨b1, b2⟩ := vsSiftStep_length p xt r
    exact ⟨a1.trans b1, a2.trans b2⟩

theorem vsSift_fits {p N : ℕ} (hp : 0 < p) (rows : List VsRow) {xt : List ℕ × List ℕ}
    (h : VsPairFits p N xt) : VsPairFits p N (vsSift p rows xt) := by
  induction rows generalizing xt with
  | nil => exact h
  | cons r rs ih => exact ih (vsSiftStep_fits hp h r)

theorem vsSift_take_succ (p : ℕ) (rows : List VsRow) (xt : List ℕ × List ℕ) (i : ℕ)
    (hi : i < rows.length) :
    vsSift p (rows.take (i + 1)) xt = vsSiftStep p (vsSift p (rows.take i) xt) rows[i] := by
  rw [vsSift, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    List.foldl_append]
  rfl

/-- The weight of a list whose entries weigh at most `c`. -/
theorem vs_wt_list_le_of (vs : List Val) {c : ℕ} (h : ∀ v ∈ vs, v.wt ≤ c) :
    (Val.list vs).wt ≤ vs.length * (2 * c + 1) + 4 := by
  have h1 := wt_list_le vs
  have h2 := List.sum_le_card_nsmul (vs.map Val.wt) c (by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ v hv rfl; exact h v hv)
  simp only [List.length_map, smul_eq_mul] at h2
  have : vs.length * (2 * c + 1) = 2 * (vs.length * c) + vs.length := by ring
  omega

/-- The weight of a list of at most `N + 1` rows that fit. -/
theorem wt_vsRows_le {N lx lt : ℕ} {rows : List VsRow} (hr : ∀ r ∈ rows, VsRowFits N lx lt r)
    (hl : rows.length ≤ N + 1) : (Val.list (rows.map VsRow.val)).wt ≤ 81 * (N + 1) ^ 3 + 4 := by
  have h := vs_wt_list_le_of (rows.map VsRow.val) (c := 40 * (N + 1) ^ 2) (by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ r hr' rfl
    have H := hr r hr'
    exact wt_vsRowVal_le H.hrx H.hrt H.lrx H.lrt H.j)
  rw [List.length_map] at h
  have e : (N + 1) * (2 * (40 * (N + 1) ^ 2) + 1) ≤ 81 * (N + 1) ^ 3 := by
    have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e3 : (N + 1) ^ 3 = (N + 1) * (N + 1) ^ 2 := by ring
    rw [e3]; nlinarith
  have := Nat.mul_le_mul_right (2 * (40 * (N + 1) ^ 2) + 1) hl
  omega

/-- The arguments of the sift: `[p, rows, (x, t)]`. -/
abbrev vsSiftArg (p : ℕ) (rows : List VsRow) (xt : List ℕ × List ℕ) : Val :=
  .list [.nat p, .list (rows.map VsRow.val), vsPairVal xt]

/-- The sift, at base `b`: the `foldl` of the step at `st`. -/
abbrev vsSiftFuns (b st : ℕ) : List Expr := foldlFuns b st

/-- **The sift.** On `[p, rows, (x, t)]`, with at most `N` rows that fit the pair, the result
is the pair sifted through the rows. -/
theorem vsSift_spec {P : Program} {b st lin : ℕ} (h : P.HasAt b (vsSiftFuns b st))
    (hf : P.funs[st]? = some (vsSiftStepF lin)) (hl : P.HasAt lin (vsLinFuns lin))
    {p N : ℕ} (hp : 0 < p) (hpN : p ≤ N) {xt : List ℕ × List ℕ} (hP : VsPairFits p N xt)
    {rows : List VsRow} (hr : ∀ r ∈ rows, VsRowFits N xt.1.length xt.2.length r)
    (hrl : rows.length ≤ N) :
    FunDet P b (vsSiftArg p rows xt) (vsPairVal (vsSift p rows xt)) (4 * 10 ^ 6 * (N + 1) ^ 4) := by
  have hR := wt_vsRows_le hr (by omega)
  have hM : ∀ i acc, i ≤ (rows.map VsRow.val).length →
      acc = vsPairVal (vsSift p (rows.take i) xt) → acc.wt ≤ 20 * (N + 1) ^ 2 + 6 := by
    rintro i acc - rfl
    have H := vsSift_fits hp (rows.take i) hP
    exact wt_vsPairVal_le hpN H.hx H.ht H.lx H.lt
  have hg : ∀ i acc (hi : i < (rows.map VsRow.val).length),
      acc = vsPairVal (vsSift p (rows.take i) xt) →
      FunAll P st (.list [.nat p, acc, (rows.map VsRow.val)[i]]) (fun w cost =>
        w = vsPairVal (vsSift p (rows.take (i + 1)) xt) ∧ cost ≤ 3 * 10 ^ 6 * (N + 1) ^ 3) := by
    rintro i acc hi rfl
    rw [List.length_map] at hi
    have H := vsSift_fits hp (rows.take i) hP
    obtain ⟨e1, e2⟩ := vsSift_length p (rows.take i) xt
    have hri := hr rows[i] (List.getElem_mem hi)
    rw [← e1, ← e2] at hri
    rw [List.getElem_map, vsSift_take_succ p rows xt i hi]
    exact vsSiftStep_spec hf hl hp hpN (VsFits.of H hri)
  refine ((foldl_spec h (c := .nat p) (acc0 := vsPairVal xt) (M := 20 * (N + 1) ^ 2 + 6)
    (B := fun _ => 3 * 10 ^ 6 * (N + 1) ^ 3)
    (Inv := fun i acc => acc = vsPairVal (vsSift p (rows.take i) xt)) (by simp [vsSift])
    hM hg).mono fun w cost hw => ⟨?_, ?_⟩)
  · rw [hw.1, List.length_map, List.take_length]
  · have hc := hw.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map] at hc
    have wP := wt_vsPairVal_le hpN hP.hx hP.ht hP.lx hP.lt
    have w3 := wt_list3_le (.nat p) (.list (rows.map VsRow.val)) (vsPairVal xt)
    have wp := wt_nat_le p
    have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have hN3 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hN4 : (N + 1) * (N + 1) ^ 3 = (N + 1) ^ 4 := by ring
    have k1 : rows.length * (3 * 10 ^ 6 * (N + 1) ^ 3) ≤ (N + 1) * (3 * 10 ^ 6 * (N + 1) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have k2 : loopModK * (rows.length + 1) *
        ((Val.list [.nat p, .list (rows.map VsRow.val), vsPairVal xt]).wt + rows.length +
          (20 * (N + 1) ^ 2 + 6) + 1) ≤ 1000 * (N + 1) * (400 * (N + 1) ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
    have e1 : (N + 1) * (3 * 10 ^ 6 * (N + 1) ^ 3) = 3 * 10 ^ 6 * (N + 1) ^ 4 := by
      rw [← hN4]; ring
    have e2 : 1000 * (N + 1) * (400 * (N + 1) ^ 3) = 400000 * (N + 1) ^ 4 := by
      rw [← hN4]; ring
    have ea : (vsSiftArg p rows xt).wt =
      (Val.list [.nat p, .list (rows.map VsRow.val), vsPairVal xt]).wt := rfl
    omega

end GI.Impl
