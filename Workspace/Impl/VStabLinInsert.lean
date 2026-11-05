module

public import Workspace.Impl.VStabLinSift

@[expose] public section

/-!
# Inserting a vector pair into echelon rows

To insert a pair `(x, t)`, sift it through the rows. If the main part becomes zero, the tag is
a relation and is returned. Otherwise the first nonzero entry `k` of the main part becomes a new
pivot: both parts are scaled by the inverse of that entry modulo `p`, and the new row is added
at the end.

* `vsNzTestF`, `vsInvTestF`, `vsInvF`: the tests and the inverse modulo `p` by search
  (`vsInv_spec`).
* `vsInsertFuns`: the insertion, on `[p, rows, (x, t)]`; `vsInsert_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-! ### The inverse modulo `p`, by search -/

/-- The least `s < p` with `s c ≡ 1 (mod p)`, or `p` if there is none. -/
def vsInv (p c : ℕ) : ℕ := (List.range p).findIdx fun s => s * c % p == 1

theorem vsInv_le (p c : ℕ) : vsInv p c ≤ p := by
  have := List.findIdx_le_length (xs := List.range p) (p := fun s => s * c % p == 1)
  simpa [vsInv] using this

/-- The test of the inverse, on `[[p, c], s]`: is `s c mod p = 1`? -/
def vsInvTestF : Expr :=
  .arith .eq (.arith .mod (.arith .mul (arg 1) (.get (arg 0) (.nat 1))) (.get (arg 0) (.nat 0)))
    (.nat 1)

/-- The test as a function on values. -/
def vsInvQ (p c : ℕ) : Val → Bool
  | .nat s => s * c % p == 1
  | .list _ => false

theorem vsInvTest_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some vsInvTestF)
    {p c s N : ℕ} (hcN : c ≤ N) (hsN : s ≤ N) :
    FunDet P f (.list [.list [.nat p, .nat c], .nat s]) (boolVal (vsInvQ p c (.nat s)))
      (20 * (Val.list [.list [.nat p, .nat c], .nat s]).wt + 3 * (N + 1) ^ 2 + 100) := by
  have d0 := Det.arg' (P := P) (rest := []) (vs := [.list [.nat p, .nat c], .nat s]) (j := 0) rfl
  have ds := Det.arg' (P := P) (rest := []) (vs := [.list [.nat p, .nat c], .nat s]) (j := 1) rfl
  have dc := Det.get' d0 (Det.nat 1) (show [Val.nat p, .nat c][1]? = some (.nat c) from rfl)
  have dp := Det.get' d0 (Det.nat 0) (show [Val.nat p, .nat c][0]? = some (.nat p) from rfl)
  have m := Det.arith' (op := .mul) ds dc rfl
  have r := Det.arith' (op := .mod) m dp rfl
  have e := Det.arith' (op := .eq) r (Det.nat 1) rfl
  have hv : Val.nat (BinOp.eval .eq (BinOp.eval .mod (BinOp.eval .mul s c) p) 1) =
      boolVal (vsInvQ p c (.nat s)) := by
    simp only [BinOp.eval, vsInvQ, boolVal]
    cases h : (s * c % p == 1) <;> simp_all
  rw [hv] at e
  refine FunDet.intro hf (e.mono ?_)
  have hsc : s * c ≤ (N + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h1 : s * c % p ≤ s * c := Nat.mod_le _ _
  have h2 : BinOp.eval .eq (s * c % p) 1 ≤ 1 := by simp only [BinOp.eval]; split_ifs <;> omega
  have wc := wt_nat_le c
  have wp := wt_nat_le p
  have hcX : (Val.nat c).wt < (Val.list [.list [.nat p, .nat c], .nat s]).wt :=
    lt_trans (wt_le_wt_list (by simp)) (wt_le_wt_list (v := Val.list [.nat p, .nat c]) (by simp))
  have hpX : (Val.nat p).wt < (Val.list [.list [.nat p, .nat c], .nat s]).wt :=
    lt_trans (wt_le_wt_list (by simp)) (wt_le_wt_list (v := Val.list [.nat p, .nat c]) (by simp))
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  simp only [BinOp.eval] at h1 h2 ⊢
  by_cases heq : s * c % p = 1 <;> simp_all only [heq, ite_true, ite_false] <;> omega

/-- The inverse, on `[p, c]`: search `range p`. -/
def vsInvF (rng fnd : ℕ) : Expr :=
  .letE (.call rng (arg 0)) (.call fnd (mk2 (.var 0) (.var 1)))

theorem vsInv_spec {P : Program} {f rng fnd tst : ℕ} (hf : P.funs[f]? = some (vsInvF rng fnd))
    (hr : P.HasAt rng (rangeFuns rng)) (hfd : P.HasAt fnd (findFuns fnd tst))
    (ht : P.funs[tst]? = some vsInvTestF) {p c N : ℕ} (hpN : p ≤ N) (hcN : c ≤ N) :
    FunDet P f (.list [.nat p, .nat c]) (.nat (vsInv p c)) (2 * 10 ^ 5 * (N + 1) ^ 3) := by
  have dp := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat c]) (j := 0) rfl
  have hrng := Det.call dp ((range_spec hr p).mono fun w c hw => ⟨hw.1, hw.1 ▸ hw.2⟩)
  have hLw : (Val.list ((List.range p).map Val.nat)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by simp at hx; omega) (by simp; omega)
  have hA2 := wt_list2_le (Val.list [.nat p, .nat c]) (.list ((List.range p).map Val.nat))
  have wA := wt_list2_le (.nat p) (.nat c)
  have wp := wt_nat_le p
  have wc := wt_nat_le c
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN3 : (N + 1) * (N + 1) ^ 2 = (N + 1) ^ 3 := by ring
  have htest : ∀ x ∈ ((List.range p).map Val.nat), FunDet P tst (.list [(Val.list [.nat p, .nat c]), x]) (boolVal (vsInvQ p c x))
      (20 * (60 * (N + 1) ^ 2) + 3 * (N + 1) ^ 2 + 100) := by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    refine (vsInvTest_spec ht hcN (by omega : s ≤ N)).mono ?_
    have := wt_list2_le (Val.list [.nat p, .nat c]) (.nat s)
    have := wt_nat_le s
    omega
  have hfind := find_spec hfd htest
  have hidx : ((List.range p).map Val.nat).findIdx (vsInvQ p c) = vsInv p c := by
    simp only [vsInv, List.findIdx_map]
    rfl
  have dfd : FunDet P fnd (.list [(Val.list [.nat p, .nat c]), .list ((List.range p).map Val.nat)]) (.nat (vsInv p c))
      ((((List.range p).map Val.nat).map fun _ => 20 * (60 * (N + 1) ^ 2) + 3 * (N + 1) ^ 2 + 100).sum +
        loopModK * (((List.range p).map Val.nat).length + 1) * ((Val.list [(Val.list [.nat p, .nat c]), .list ((List.range p).map Val.nat)]).wt + 2 * ((List.range p).map Val.nat).length + 3)) :=
    hfind.mono fun w c hw => ⟨hw.1.trans (by rw [hidx]), hw.2⟩
  have d0 := Det.var' (P := P) (env := [(Val.list [.nat p, .nat c]), .list ((List.range p).map Val.nat)]) (i := 0) rfl
  have d1 := Det.var' (P := P) (env := [(Val.list [.nat p, .nat c]), .list ((List.range p).map Val.nat)]) (i := 1) rfl
  have dc := Det.call (Det.mk2 d0 d1) dfd
  refine FunDet.intro hf ((Det.letE hrng dc).mono ?_)
  have hLl : ((List.range p).map Val.nat).length = p := by simp
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at *
  rw [hLl]
  have wv := wt_nat_le (vsInv p c)
  have hv := vsInv_le p c
  have k1 : p * (20 * (60 * (N + 1) ^ 2) + 3 * (N + 1) ^ 2 + 100) ≤
      (N + 1) * (1400 * (N + 1) ^ 2) := Nat.mul_le_mul (by omega) (by omega)
  have k2 : loopModK * (p + 1) * ((Val.list [(Val.list [.nat p, .nat c]), .list ((List.range p).map Val.nat)]).wt + 2 * p + 3) ≤
      1000 * (N + 1) * (60 * (N + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have k3 : loopModK * (p + 1) * ((Val.nat p).wt + p + (natList (List.range p)).wt + 1) ≤
      1000 * (N + 1) * (60 * (N + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by
      have : (natList (List.range p)).wt = (Val.list ((List.range p).map Val.nat)).wt := rfl
      omega)
  have e1 : (N + 1) * (1400 * (N + 1) ^ 2) = 1400 * (N + 1) ^ 3 := by rw [← hN3]; ring
  have e2 : 1000 * (N + 1) * (60 * (N + 1) ^ 2) = 60000 * (N + 1) ^ 3 := by rw [← hN3]; ring
  have e3 : (natList (List.range p)).wt = (Val.list ((List.range p).map Val.nat)).wt := rfl
  have hN3' : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-! ### The first nonzero entry -/

/-- The index of the first nonzero entry, or the length if there is none. -/
def vsNzIdx (x : List ℕ) : ℕ := x.findIdx fun a => decide (0 < a)

theorem vsNzIdx_le (x : List ℕ) : vsNzIdx x ≤ x.length := List.findIdx_le_length

/-- The test, on `[c, a]`: is `a` nonzero? -/
def vsNzTestF : Expr := .arith .lt (.nat 0) (arg 1)

/-- The test as a function on values. -/
def vsNzQ : Val → Bool
  | .nat a => decide (0 < a)
  | .list _ => false

theorem vsNzTest_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some vsNzTestF) {a N : ℕ}
    (haN : a ≤ N) :
    FunDet P f (.list [.nat 0, .nat a]) (boolVal (vsNzQ (.nat a))) (100 * (N + 1)) := by
  have da := Det.arg' (P := P) (rest := []) (vs := [Val.nat 0, .nat a]) (j := 1) rfl
  have e := Det.arith' (op := .lt) (Det.nat 0) da rfl
  have hv : Val.nat (BinOp.eval .lt 0 a) = boolVal (vsNzQ (.nat a)) := by
    simp only [BinOp.eval, vsNzQ, boolVal]
    by_cases h : 0 < a <;> simp [h]
  rw [hv] at e
  refine FunDet.intro hf (e.mono ?_)
  have w := wt_list2_le (.nat 0) (.nat a)
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le a
  have h2 : BinOp.eval .lt 0 a ≤ 1 := by simp only [BinOp.eval]; split_ifs <;> omega
  rw [← hv] at *
  omega

/-! ### The insertion -/

/-- The new row made from a sifted pair `y` whose main part is nonzero first at `k`. -/
def vsNewRow (p : ℕ) (y : List ℕ × List ℕ) (k : ℕ) : VsRow :=
  ⟨k, vsLin p (vsInv p (y.1.getD k 0)) 0 y.1 y.1, vsLin p (vsInv p (y.1.getD k 0)) 0 y.2 y.2⟩

/-- The result of the insertion: `[1, rows ++ [new row]]` if the sifted main part is nonzero,
and `[0, tag]` if it is zero. -/
def vsInsertVal (p : ℕ) (rows : List VsRow) (xt : List ℕ × List ℕ) : Val :=
  if vsNzIdx (vsSift p rows xt).1 < (vsSift p rows xt).1.length then
    .list [.nat 1, .list ((rows ++ [vsNewRow p (vsSift p rows xt)
      (vsNzIdx (vsSift p rows xt).1)]).map VsRow.val)]
  else .list [.nat 0, natList (vsSift p rows xt).2]

/-- The body of the insertion, on `[p, rows, (x, t)]`. -/
def vsInsertF (sft fnz inv lin : ℕ) : Expr :=
  .letE (.call sft (.var 0))
    (.letE (.call fnz (mk2 (.nat 0) (.get (.var 1) (.nat 0))))
      (.ite (.arith .lt (.var 2) (.length (.get (.var 1) (.nat 0))))
        (.letE (.call inv (mk2 (arg 0) (.get (.get (.var 1) (.nat 0)) (.var 2))))
          (mk2 (.nat 1) (.snoc (arg 1)
            (mk3 (.var 2)
              (.call lin (.snoc (mk4 (arg 0) (.var 3) (.nat 0) (.get (.var 1) (.nat 0)))
                (.get (.var 1) (.nat 0))))
              (.call lin (.snoc (mk4 (arg 0) (.var 3) (.nat 0) (.get (.var 1) (.nat 1)))
                (.get (.var 1) (.nat 1))))))))
        (mk2 (.nat 0) (.get (.var 1) (.nat 1)))))

/-- The twenty-five functions of the insertion, at base `b`. -/
def vsInsertFuns (b : ℕ) : List Expr :=
  [vsInsertF (b + 13) (b + 10) (b + 3) (b + 17), vsNzTestF, vsInvTestF, vsInvF (b + 4) (b + 7)] ++
    rangeFuns (b + 4) ++ findFuns (b + 7) (b + 2) ++ findFuns (b + 10) (b + 1) ++
    vsSiftFuns (b + 13) (b + 16) ++ [vsSiftStepF (b + 17)] ++ vsLinFuns (b + 17)

theorem vsInsertFuns_length (b : ℕ) : (vsInsertFuns b).length = 25 := rfl

theorem vsNewRow_fits {p N : ℕ} (hp : 0 < p) (hpN : p ≤ N) {y : List ℕ × List ℕ}
    (hy : VsPairFits p N y) {k : ℕ} (hk : k < y.1.length) :
    VsRowFits N y.1.length y.2.length (vsNewRow p y k) where
  hrx := fun z hz => (vsLin_lt hp _ _ z hz).le.trans hpN
  hrt := fun z hz => (vsLin_lt hp _ _ z hz).le.trans hpN
  lrx := by simp only [vsNewRow, vsLin_length]; exact hy.lx
  lrt := by simp only [vsNewRow, vsLin_length]; exact hy.lt
  jx := hk
  xx := by simp [vsNewRow, vsLin_length]
  tt := by simp [vsNewRow, vsLin_length]
  j := by have := hy.lx; simp only [vsNewRow]; omega

/-- The branch of the insertion that makes a new row. -/
def vsInsertThenE (inv lin : ℕ) : Expr :=
  .letE (.call inv (mk2 (arg 0) (.get (.get (.var 1) (.nat 0)) (.var 2))))
    (mk2 (.nat 1) (.snoc (arg 1)
      (mk3 (.var 2)
        (.call lin (.snoc (mk4 (arg 0) (.var 3) (.nat 0) (.get (.var 1) (.nat 0)))
          (.get (.var 1) (.nat 0))))
        (.call lin (.snoc (mk4 (arg 0) (.var 3) (.nat 0) (.get (.var 1) (.nat 1)))
          (.get (.var 1) (.nat 1)))))))

theorem vsInsertThen_spec {P : Program} {inv lin rg fi it : ℕ}
    (hinv : P.funs[inv]? = some (vsInvF rg fi)) (hrg : P.HasAt rg (rangeFuns rg))
    (hfi : P.HasAt fi (findFuns fi it)) (hit : P.funs[it]? = some vsInvTestF)
    (hln : P.HasAt lin (vsLinFuns lin)) {p N : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    {rows : List VsRow} {y : List ℕ × List ℕ} (hy : VsPairFits p N y)
    (hr : ∀ r ∈ rows, VsRowFits N y.1.length y.2.length r) (hrl : rows.length ≤ N)
    {A X : Val} (hA : A = .list [.nat p, .list (rows.map VsRow.val), X])
    (hAw : A.wt ≤ 250 * (N + 1) ^ 3) {k : ℕ} (hk : k < y.1.length) :
    Det P [A, vsPairVal y, .nat k] (vsInsertThenE inv lin)
      (.list [.nat 1, .list ((rows ++ [vsNewRow p y k]).map VsRow.val)])
      (3 * 10 ^ 6 * (N + 1) ^ 3) := by
  subst hA
  have hy1N : ∀ z ∈ y.1, z ≤ N := fun z hz => (hy.hx z hz).le.trans hpN
  have hy2N : ∀ z ∈ y.2, z ≤ N := fun z hz => (hy.ht z hz).le.trans hpN
  have hcN : y.1.getD k 0 ≤ N := hy1N _ (by simp [List.getD_eq_getElem?_getD, hk])
  have hsN : vsInv p (y.1.getD k 0) ≤ N := (vsInv_le _ _).trans hpN
  -- the inverse
  have dY2 := Det.var' (P := P) (env := [.list [.nat p, .list (rows.map VsRow.val), X], vsPairVal y,
    .nat k]) (i := 1) rfl
  have dx2 := Det.get' dY2 (Det.nat 0) (show [natList y.1, natList y.2][0]? = some _ from rfl)
  have dk2 := Det.var' (P := P) (env := [.list [.nat p, .list (rows.map VsRow.val), X], vsPairVal y,
    .nat k]) (i := 2) rfl
  have dc := Det.get' dx2 dk2 (natList_getElem? hk)
  have dp2 := Det.arg' (P := P) (rest := [vsPairVal y, .nat k])
    (vs := [.nat p, .list (rows.map VsRow.val), X]) (j := 0) rfl
  have dinv := Det.call (Det.mk2 dp2 dc) (vsInv_spec hinv hrg hfi hit hpN hcN)
  -- the new row
  have dp3 := Det.arg' (P := P) (rest := [vsPairVal y, .nat k, .nat (vsInv p (y.1.getD k 0))])
    (vs := [.nat p, .list (rows.map VsRow.val), X]) (j := 0) rfl
  have dR3 := Det.arg' (P := P) (rest := [vsPairVal y, .nat k, .nat (vsInv p (y.1.getD k 0))])
    (vs := [.nat p, .list (rows.map VsRow.val), X]) (j := 1) rfl
  have dY3 := Det.var' (P := P) (env := [.list [.nat p, .list (rows.map VsRow.val), X], vsPairVal y,
    .nat k, .nat (vsInv p (y.1.getD k 0))]) (i := 1) rfl
  have dk3 := Det.var' (P := P) (env := [.list [.nat p, .list (rows.map VsRow.val), X], vsPairVal y,
    .nat k, .nat (vsInv p (y.1.getD k 0))]) (i := 2) rfl
  have ds3 := Det.var' (P := P) (env := [.list [.nat p, .list (rows.map VsRow.val), X], vsPairVal y,
    .nat k, .nat (vsInv p (y.1.getD k 0))]) (i := 3) rfl
  have dx3 := Det.get' dY3 (Det.nat 0) (show [natList y.1, natList y.2][0]? = some _ from rfl)
  have dt3 := Det.get' dY3 (Det.nat 1) (show [natList y.1, natList y.2][1]? = some _ from rfl)
  have l1 := Det.call (Det.snoc (Det.mk4 dp3 ds3 (Det.nat 0) dx3) dx3)
    (vsLin_spec hln hp hy1N hy1N hy.lx hy.lx le_rfl hpN hsN (Nat.zero_le _))
  have l2 := Det.call (Det.snoc (Det.mk4 dp3 ds3 (Det.nat 0) dt3) dt3)
    (vsLin_spec hln hp hy2N hy2N hy.lt hy.lt le_rfl hpN hsN (Nat.zero_le _))
  have drow := Det.mk3 dk3 l1 l2
  have dout := Det.mk2 (Det.nat 1) (Det.snoc dR3 drow)
  have hrow : Val.list [.nat k, natList (vsLin p (vsInv p (y.1.getD k 0)) 0 y.1 y.1), natList (vsLin p (vsInv p (y.1.getD k 0)) 0 y.2 y.2)] =
    (vsNewRow p y k).val := rfl
  have hR' : (rows.map VsRow.val) ++ [(vsNewRow p y k).val] = (rows ++ [vsNewRow p y k]).map VsRow.val := by
    simp
  rw [hrow, hR'] at dout
  refine (Det.letE dinv dout).mono ?_
  -- the cost
  have hnf := vsNewRow_fits hp hpN hy hk
  have hR'w := wt_vsRows_le (rows := rows ++ [vsNewRow p y k]) (fun r hr' => by
    simp only [List.mem_append, List.mem_singleton] at hr'
    rcases hr' with hr' | rfl
    · exact hr r hr'
    · exact hnf) (by simp; omega)
  have wrow := wt_vsRowVal_le hnf.hrx hnf.hrt hnf.lrx hnf.lrt hnf.j
  have wY := wt_vsPairVal_le hpN hy.hx hy.ht hy.lx hy.lt
  have wx := wt_natList_le_sq hy1N hy.lx
  have wt := wt_natList_le_sq hy2N hy.lt
  have wa1 : (Val.list [.nat p, .nat (vsInv p (y.1.getD k 0)), .nat 0, natList y.1, natList y.1]).wt ≤
      50 * (N + 1) ^ 2 := wt_vsLinArg_le (p := p) (a := (vsInv p (y.1.getD k 0))) (b := 0) hy1N hy1N hy.lx hy.lx hpN hsN
    (Nat.zero_le _)
  have wa2 : (Val.list [.nat p, .nat (vsInv p (y.1.getD k 0)), .nat 0, natList y.2, natList y.2]).wt ≤
      50 * (N + 1) ^ 2 := wt_vsLinArg_le (p := p) (a := (vsInv p (y.1.getD k 0))) (b := 0) hy2N hy2N hy.lt hy.lt hpN hsN
    (Nat.zero_le _)
  have wl1 := wt_natList_le_sq (fun z hz => (vsLin_lt hp _ _ z hz).le.trans hpN)
    (by rw [vsLin_length]; exact hy.lx : (vsLin p (vsInv p (y.1.getD k 0)) 0 y.1 y.1).length ≤ N)
  have wl2 := wt_natList_le_sq (fun z hz => (vsLin_lt hp _ _ z hz).le.trans hpN)
    (by rw [vsLin_length]; exact hy.lt : (vsLin p (vsInv p (y.1.getD k 0)) 0 y.2 y.2).length ≤ N)
  have w4a := wt_list4_le (.nat p) (.nat (vsInv p (y.1.getD k 0))) (.nat 0) (natList y.1)
  have w4b := wt_list4_le (.nat p) (.nat (vsInv p (y.1.getD k 0))) (.nat 0) (natList y.2)
  have wpc := wt_list2_le (.nat p) (.nat (y.1.getD k 0))
  have wo := wt_list2_le (.nat 1) (.list ((rows ++ [vsNewRow p y k]).map VsRow.val))
  have wp := wt_nat_le p
  have ws := wt_nat_le (vsInv p (y.1.getD k 0))
  have wc := wt_nat_le (y.1.getD k 0)
  have wk := wt_nat_le k
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN3 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hkN : k ≤ N := by have := hy.lx; omega
  have e1 : (vsLinArg p (vsInv p (y.1.getD k 0)) 0 y.1 y.1).wt =
    (Val.list ([Val.nat p, .nat (vsInv p (y.1.getD k 0)), .nat 0, natList y.1] ++ [natList y.1])).wt := rfl
  have e2 : (vsLinArg p (vsInv p (y.1.getD k 0)) 0 y.2 y.2).wt =
    (Val.list ([Val.nat p, .nat (vsInv p (y.1.getD k 0)), .nat 0, natList y.2] ++ [natList y.2])).wt := rfl
  have e3 : (vsPairVal y).wt = (Val.list [natList y.1, natList y.2]).wt := rfl
  simp only [List.cons_append, List.nil_append] at *
  omega

/-- **The insertion.** On `[p, rows, (x, t)]`, with at most `N` rows that fit the pair, the
result is `vsInsertVal p rows xt`. -/
theorem vsInsert_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsInsertFuns b)) {p N : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) {xt : List ℕ × List ℕ} (hP : VsPairFits p N xt)
    {rows : List VsRow} (hr : ∀ r ∈ rows, VsRowFits N xt.1.length xt.2.length r)
    (hrl : rows.length ≤ N) :
    FunDet P b (vsSiftArg p rows xt) (vsInsertVal p rows xt) (10 ^ 7 * (N + 1) ^ 4) := by
  have hf0 : P.funs[b]? = some (vsInsertF (b + 13) (b + 10) (b + 3) (b + 17)) :=
    h.get (j := 0) (by simp [vsInsertFuns])
  have hnz : P.funs[b + 1]? = some vsNzTestF := h.get (j := 1) (by simp [vsInsertFuns])
  have hit : P.funs[b + 2]? = some vsInvTestF := h.get (j := 2) (by simp [vsInsertFuns])
  have hinv : P.funs[b + 3]? = some (vsInvF (b + 4) (b + 7)) :=
    h.get (j := 3) (by simp [vsInsertFuns])
  have hrg : P.HasAt (b + 4) (rangeFuns (b + 4)) := h.block 4 rfl
  have hfi : P.HasAt (b + 7) (findFuns (b + 7) (b + 2)) := h.block 7 rfl
  have hfn : P.HasAt (b + 10) (findFuns (b + 10) (b + 1)) := h.block 10 rfl
  have hsf : P.HasAt (b + 13) (vsSiftFuns (b + 13) (b + 16)) := h.block 13 rfl
  have hst : P.funs[b + 16]? = some (vsSiftStepF (b + 17)) := h.get (j := 16) (by rw [vsInsertFuns_length]; omega)
  have hln : P.HasAt (b + 17) (vsLinFuns (b + 17)) := h.block 17 rfl
  -- facts on the sifted pair
  have hyP := vsSift_fits hp rows hP
  obtain ⟨hl1, hl2⟩ := vsSift_length p rows xt
  have hR := wt_vsRows_le hr (by omega)
  have hpw := wt_nat_le p
  have hYw := wt_vsPairVal_le hpN hyP.hx hyP.ht hyP.lx hyP.lt
  have hXw := wt_vsPairVal_le hpN hP.hx hP.ht hP.lx hP.lt
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN3 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN4 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hAw : (vsSiftArg p rows xt).wt ≤ 250 * (N + 1) ^ 3 := by
    have := wt_list3_le (.nat p) (.list (rows.map VsRow.val)) (vsPairVal xt)
    have e : (vsSiftArg p rows xt).wt =
      (Val.list [.nat p, .list (rows.map VsRow.val), vsPairVal xt]).wt := rfl
    omega
  have hout : (vsInsertVal p rows xt).wt ≤ 200 * (N + 1) ^ 3 := by
    unfold vsInsertVal
    split_ifs with hk
    · have hnf := vsNewRow_fits hp hpN hyP hk
      rw [hl1, hl2] at hnf
      have := wt_vsRows_le (rows := rows ++ [vsNewRow p (vsSift p rows xt)
          (vsNzIdx (vsSift p rows xt).1)]) (fun r hr' => by
        simp only [List.mem_append, List.mem_singleton] at hr'
        rcases hr' with hr' | rfl
        · exact hr r hr'
        · exact hnf) (by simp; omega)
      have := wt_list2_le (.nat 1) (.list ((rows ++ [vsNewRow p (vsSift p rows xt)
          (vsNzIdx (vsSift p rows xt).1)]).map VsRow.val))
      have := wt_nat_le 1
      omega
    · have := wt_list2_le (.nat 0) (natList (vsSift p rows xt).2)
      have := wt_natList_le_sq (fun z hz => (hyP.ht z hz).le.trans hpN) hyP.lt
      have := wt_nat_le 0
      omega
  -- the sift
  have dsift := Det.call (Det.var' (P := P) (env := [vsSiftArg p rows xt]) (i := 0) rfl)
    (vsSift_spec hsf hst hln hp hpN hP hr hrl)
  -- the first nonzero entry
  obtain ⟨y, hy⟩ : ∃ y, vsSift p rows xt = y := ⟨_, rfl⟩
  rw [hy] at dsift hyP hl1 hl2 hYw
  have hy1N : ∀ z ∈ y.1, z ≤ N := fun z hz => (hyP.hx z hz).le.trans hpN
  have hlx := hyP.lx
  have hlt := hyP.lt
  have dY1 := Det.var' (P := P) (env := [vsSiftArg p rows xt, vsPairVal y]) (i := 1) rfl
  have dx1 := Det.get' dY1 (Det.nat 0) (show [natList y.1, natList y.2][0]? = some _ from rfl)
  have htest : ∀ x ∈ y.1.map Val.nat, FunDet P (b + 1) (.list [.nat 0, x]) (boolVal (vsNzQ x))
      (100 * (N + 1)) := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact vsNzTest_spec hnz (hy1N a ha)
  have hidx : (y.1.map Val.nat).findIdx vsNzQ = vsNzIdx y.1 := by
    simp only [vsNzIdx, List.findIdx_map]
    rfl
  have wx := wt_natList_le_sq hy1N hyP.lx
  have dfd : FunDet P (b + 10) (.list [.nat 0, natList y.1]) (.nat (vsNzIdx y.1))
      (31000 * (N + 1) ^ 3) := by
    refine (find_spec hfn htest).mono fun w c hw => ⟨hw.1.trans (by rw [hidx]), ?_⟩
    have hc := hw.2
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at hc
    have k1 : y.1.length * (100 * (N + 1)) ≤ (N + 1) * (100 * (N + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    have w2 := wt_list2_le (.nat 0) (.list (y.1.map Val.nat))
    have wx' : (Val.list (y.1.map Val.nat)).wt ≤ 5 * (N + 1) ^ 2 := wx
    have w0 := wt_nat_le 0
    have k2 : loopModK * (y.1.length + 1) *
        ((Val.list [.nat 0, .list (y.1.map Val.nat)]).wt + 2 * y.1.length + 3) ≤
        1000 * (N + 1) * (30 * (N + 1) ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by
        have : (natList y.1).wt = (Val.list (y.1.map Val.nat)).wt := rfl
        omega)
    have e1 : (N + 1) * (100 * (N + 1)) = 100 * (N + 1) ^ 2 := by ring
    have e2 : 1000 * (N + 1) * (30 * (N + 1) ^ 2) = 30000 * (N + 1) ^ 3 := by ring
    omega
  have dfind := Det.call (Det.mk2 (Det.nat 0) dx1) dfd
  -- the two branches
  set k := vsNzIdx y.1 with hkdef
  have hbody : Det P [vsSiftArg p rows xt, vsPairVal y, .nat k]
      (.ite (.arith .lt (.var 2) (.length (.get (.var 1) (.nat 0))))
        (vsInsertThenE (b + 3) (b + 17)) (mk2 (.nat 0) (.get (.var 1) (.nat 1))))
      (vsInsertVal p rows xt) (4 * 10 ^ 6 * (N + 1) ^ 3) := by
    have dY2 := Det.var' (P := P) (env := [vsSiftArg p rows xt, vsPairVal y, .nat k]) (i := 1) rfl
    have dx2 := Det.get' dY2 (Det.nat 0) (show [natList y.1, natList y.2][0]? = some _ from rfl)
    have dk2 := Det.var' (P := P) (env := [vsSiftArg p rows xt, vsPairVal y, .nat k]) (i := 2) rfl
    have dcnd := Det.arith' (op := .lt) dk2 (Det.length dx2) rfl
    have wk := wt_nat_le k
    have hkl : k ≤ y.1.length := vsNzIdx_le _
    have wY2 : (vsPairVal y).wt = (Val.list [natList y.1, natList y.2]).wt := rfl
    by_cases hk : k < y.1.length
    · have hthen := vsInsertThen_spec hinv hrg hfi hit hln hp hpN hyP (by rw [hl1, hl2]; exact hr)
        hrl rfl hAw hk
      have hv : vsInsertVal p rows xt =
          .list [.nat 1, .list ((rows ++ [vsNewRow p y k]).map VsRow.val)] := by
        simp only [vsInsertVal, hy, ← hkdef, if_pos hk]
      have hev : BinOp.eval .lt k (List.map Val.nat y.1).length ≠ 0 := by
        simp [BinOp.eval, hk]
      rw [hv] at hout ⊢
      refine (Det.ite_pos dcnd hev hthen).mono ?_
      have := Nat.mod_le 0 1
      have hle : BinOp.eval .lt k (List.map Val.nat y.1).length ≤ 1 := by
        simp only [BinOp.eval]; split_ifs <;> omega
      simp only [List.length_map] at *
      omega
    · have hv : vsInsertVal p rows xt = .list [.nat 0, natList y.2] := by
        simp only [vsInsertVal, hy, ← hkdef, if_neg hk]
      have hev : BinOp.eval .lt k (List.map Val.nat y.1).length = 0 := by
        simp [BinOp.eval, hk]
      rw [hev] at dcnd
      have dt2 := Det.get' dY2 (Det.nat 1) (show [natList y.1, natList y.2][1]? = some _ from rfl)
      have dout := Det.mk2 (Det.nat 0) dt2
      rw [hv] at hout ⊢
      refine (Det.ite_zero dcnd dout).mono ?_
      have := wt_list2_le (.nat 0) (natList y.2)
      have := wt_natList_le_sq (fun z hz => (hyP.ht z hz).le.trans hpN) hyP.lt
      have := wt_nat_le 0
      simp only [List.length_map] at *
      omega
  refine FunDet.intro hf0 ((Det.letE dsift (Det.letE dfind hbody)).mono ?_)
  have w2 := wt_list2_le (.nat 0) (natList y.1)
  have w0 := wt_nat_le 0
  have wk := wt_nat_le k
  have hkl : k ≤ y.1.length := vsNzIdx_le _
  have wA0 : (Val.list [vsSiftArg p rows xt]).wt ≤ 2 * (vsSiftArg p rows xt).wt + 10 := by
    have := wt_list_le [vsSiftArg p rows xt]; simp at this; omega
  omega

end GI.Impl
