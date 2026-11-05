module

public import Workspace.Impl.GenExposeMath
public import Workspace.Impl.ColsSplit

@[expose] public section

/-!
# Numbering the classes of a labeling, in `GI.Lang`

The exposure program numbers the classes of a labeling `lab` of `Fin k` on the domain (given by
its indicator `dm`), as `Workspace/Impl/GenExposeMath.lean` (`Cls`) describes:

* `keyF`: the key of a point, `lab i` on the domain and `k` off it (`Cls.keyOf`);
* `repF`: the first point with the same key (`Cls.repOf`, with `findEq`);
* `isRepF`: the test of a representative on the domain (`Cls.repTest`), for `filter`;
* `numF`: the number of a point (`Cls.numOf`, with `findEq` in the list of representatives).

`clsFuns b` (at base `b`) on `[lab, dm]` returns `[num, reps, rep]` (`cls_spec`), at cost at
most `clsK (X + 1)^4` when all labels are at most `X` and `k ≤ X`.

`actFuns b` on `[[num, reps], gens]` maps every generator `g` to the list of the numbers of
`g r_t` (`act_spec`), the action of `g` on the numbers.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm)

variable {k : ℕ}

/-! ### Two library facts -/

theorem natList_range_eq (k : ℕ) : natList (List.range k) = encFun fun i : Fin k => (i : ℕ) := by
  rw [range_eq_encPerm_one, encPerm_eq_encFun]; rfl

theorem wt_range_le (k : ℕ) : (natList (List.range k)).wt ≤ 4 * (k + 1) ^ 2 := by
  rw [range_eq_encPerm_one]; exact wt_encPerm_le _

theorem mul_le_pow_succ (C n : ℕ) {k X : ℕ} (hk : k ≤ X) :
    k * (C * (X + 1) ^ n) ≤ C * (X + 1) ^ (n + 1) := by
  rw [pow_succ]
  calc k * (C * (X + 1) ^ n) ≤ (X + 1) * (C * (X + 1) ^ n) := Nat.mul_le_mul_right _ (by omega)
    _ = C * ((X + 1) ^ n * (X + 1)) := by ring

/-- `range` with a cubic cost bound. -/
theorem range_det {P : Program} {b : ℕ} (h : P.HasAt b (rangeFuns b)) (k : ℕ) :
    FunDet P b (.nat k) (natList (List.range k)) (7000 * (k + 1) ^ 3) := by
  refine (range_spec h k).mono fun w cost hw => ⟨hw.1, ?_⟩
  have hc := hw.2
  rw [hw.1, range_eq_encPerm_one] at hc
  have h1 := wt_encPerm_le (1 : Equiv.Perm (Fin k))
  have h2 := wt_nat_le k
  have h3 : loopModK * (k + 1) * ((Val.nat k).wt + k + (encPerm (1 : Equiv.Perm (Fin k))).wt + 1)
      ≤ loopModK * (k + 1) * (7 * (k + 1) ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
  have h4 : loopModK * (k + 1) * (7 * (k + 1) ^ 2) = 7000 * (k + 1) ^ 3 := by
    simp only [loopModK]; ring
  omega

/-- **Tabulating a function of the points** with `map` over `[0, …, k - 1]`, for a context of
weight at most `100 (X + 1)²`. -/
theorem tab_det {P : Program} {b f : ℕ} (hmap : P.HasAt b (mapFuns b f)) {c : Val}
    {F : Fin k → ℕ} {B X : ℕ} (hF : ∀ i : Fin k, FunDet P f (.list [c, .nat i]) (.nat (F i)) B)
    (hFX : ∀ i, F i ≤ X) (hcX : c.wt ≤ 100 * (X + 1) ^ 2) (hkX : k ≤ X) :
    FunDet P b (.list [c, natList (List.range k)]) (encFun F) (k * B + 10 ^ 6 * (X + 1) ^ 3) := by
  have hT := tabulate_spec hmap (F := fun i => .nat (F i)) hF
  rw [natList_range_eq]
  refine FunAll.mono hT fun w cost hw => ⟨hw.1, ?_⟩
  have hc := hw.2
  have e1 : (Val.list ((List.finRange k).map fun i => Val.nat (F i))) = encFun F := rfl
  rw [e1] at hc
  have w1 := wt_encFun_le' F hFX hkX
  have w2 := wt_list2_le c (encFun fun i : Fin k => (i : ℕ))
  have w3 : (encFun fun i : Fin k => (i : ℕ)).wt ≤ 4 * (k + 1) ^ 2 := wt_ids_le k
  have w4 : (k + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : mapK * (k + 1) * ((Val.list [c, encFun fun i : Fin k => (i : ℕ)]).wt +
      (encFun F).wt + 1) ≤ mapK * (X + 1) * (1000 * (X + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by nlinarith)
  have h3 : mapK * (X + 1) * (1000 * (X + 1) ^ 2) = 1000000 * (X + 1) ^ 3 := by
    simp only [mapK]; ring
  omega

/-! ### The key of a point -/

/-- On `[[lab, dm, k], i]`: `lab i` if `dm i ≠ 0`, else `k`. -/
def keyF : Expr :=
  .ite (.get (.get (arg 0) (.nat 1)) (arg 1)) (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.get (arg 0) (.nat 2))

theorem key_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some keyF) (lab dm : Fin k → ℕ)
    {X : ℕ} (hlab : ∀ i, lab i ≤ X) (hdm : ∀ i, dm i ≤ 1) (hkX : k ≤ X) (i : Fin k) :
    FunDet P f (.list [.list [encFun lab, encFun dm, .nat k], .nat i])
      (.nat (Cls.keyOf lab dm i)) (1000 * (X + 1) ^ 2) := by
  set ctx : Val := .list [encFun lab, encFun dm, .nat k] with hctx
  have h0 := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 0) rfl
  have h1 := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 1) rfl
  have hd := Det.get' (Det.get' h0 (Det.nat 1) (v := encFun dm) rfl) h1 (encFun_getElem? dm i)
  have hl := Det.get' (Det.get' h0 (Det.nat 0) (v := encFun lab) rfl) h1 (encFun_getElem? lab i)
  have hk := Det.get' h0 (Det.nat 2) (v := .nat k) rfl
  have hout := Det.ite' hd hl hk
  refine FunDet.intro hf (hout.post fun c hc => ⟨?_, ?_⟩)
  · unfold Cls.keyOf; split_ifs <;> rfl
  · have k1 : 1 ≤ X + 1 := by omega
    have wL := wt_encFun_le' lab hlab hkX
    have hX1 : 1 ≤ X := by have := i.isLt; omega
    have wD := wt_encFun_le' dm (fun j => (hdm j).trans hX1) hkX
    have wC := wt_list3_le (encFun lab) (encFun dm) (.nat k)
    have wA := wt_list2_le ctx (.nat i)
    have := wt_nat_le k
    have := wt_nat_le (i : ℕ)
    have := wt_nat_le (lab i)
    have := wt_nat_le (dm i)
    have := hlab i
    have := hdm i
    have := i.isLt
    have hm : max (Val.nat (lab i)).wt (Val.nat k).wt ≤ X + 2 := max_le (by omega) (by omega)
    have hco : ctx.wt = (Val.list [encFun lab, encFun dm, .nat k]).wt := rfl
    have hX : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    clear hout hd hl hk h0 h1
    omega

/-! ### The representative of a point -/

/-- On `[key, i]`: the first point with the key of `i`. -/
def repF (fe : ℕ) : Expr := .call fe (mk2 (.get (arg 0) (arg 1)) (arg 0))

theorem rep_det {P : Program} {f fe : ℕ} (hf : P.funs[f]? = some (repF fe))
    (hfe : P.HasAt fe (findEqFuns fe)) (key : Fin k → ℕ) {X : ℕ} (hkey : ∀ i, key i ≤ X)
    (hkX : k ≤ X) (i : Fin k) :
    FunDet P f (.list [encFun key, .nat i]) (.nat (Cls.repOf key i)) (10 ^ 6 * (X + 1) ^ 3) := by
  have hxs : ∀ x ∈ (List.finRange k).map key, x ≤ X := by
    intro x hx; obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact hkey j
  have hF := findEq_spec hfe (xs := (List.finRange k).map key) (j := key i) (B := X) hxs (hkey i)
    (by simp; omega)
  have h0 := Det.arg' (P := P) (vs := [encFun key, .nat i]) (rest := []) (j := 0) rfl
  have h1 := Det.arg' (P := P) (vs := [encFun key, .nat i]) (rest := []) (j := 1) rfl
  have hg := Det.get' h0 h1 (encFun_getElem? key i)
  have h0' : Det P [.list [encFun key, .nat i]] (arg 0) (natList ((List.finRange k).map key))
      (2 * (Val.list [encFun key, .nat i]).wt + 0 + 5) := by
    rw [← encFun_eq_natList]; exact h0
  have hc := Det.call (Det.mk2 hg h0') hF
  refine FunDet.intro hf (hc.mono ?_)
  have wK := wt_encFun_le' key hkey hkX
  have wA := wt_list2_le (encFun key) (.nat i)
  have wB := wt_list2_le (.nat (key i)) (natList ((List.finRange k).map key))
  have wN : (natList ((List.finRange k).map key)).wt = (encFun key).wt := by
    rw [encFun_eq_natList]
  have := wt_nat_le (i : ℕ)
  have := wt_nat_le (key i)
  have := hkey i
  have := i.isLt
  have hr : Cls.repOf key i < k := Cls.repOf_lt key i
  have := wt_nat_le (Cls.repOf key i)
  have e1 : ((List.finRange k).map key).findIdx (fun x => decide (x = key i)) = Cls.repOf key i :=
    rfl
  rw [e1]
  have hX : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hX2 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  simp only [findEqK]
  clear hc hF hg h0 h1 h0'
  omega

/-! ### The test of a representative -/

/-- On `[[dm, rep], j]`: `dm j ≠ 0` and `rep j = j`. -/
def isRepF : Expr :=
  .ite (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.arith .eq (.get (.get (arg 0) (.nat 1)) (arg 1)) (arg 1)) (.nat 0)

/-- The test of the filter, on values. -/
def repQ (dm key : Fin k → ℕ) : Val → Bool
  | .nat j => Cls.repTest dm key j
  | _ => false

theorem isRep_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some isRepF) (dm key : Fin k → ℕ)
    (hdm : ∀ i, dm i ≤ 1) {X : ℕ} (hkX : k ≤ X) (j : Fin k) :
    FunDet P f (.list [.list [encFun dm, encFun (Cls.repOf key)], .nat j])
      (boolVal (repQ dm key (.nat j))) (1000 * (X + 1) ^ 2) := by
  set ctx : Val := .list [encFun dm, encFun (Cls.repOf key)] with hctx
  have h0 := Det.arg' (P := P) (vs := [ctx, .nat j]) (rest := []) (j := 0) rfl
  have h1 := Det.arg' (P := P) (vs := [ctx, .nat j]) (rest := []) (j := 1) rfl
  have hd := Det.get' (Det.get' h0 (Det.nat 0) (v := encFun dm) rfl) h1 (encFun_getElem? dm j)
  have hr := Det.get' (Det.get' h0 (Det.nat 1) (v := encFun (Cls.repOf key)) rfl) h1
    (encFun_getElem? (Cls.repOf key) j)
  have he := Det.arith' (op := .eq) hr h1 (z := if Cls.repOf key j = j then 1 else 0)
    (by simp [BinOp.eval])
  have hout := Det.ite' hd he (Det.nat 0)
  refine FunDet.intro hf (hout.post fun c hc => ⟨?_, ?_⟩)
  · simp only [repQ, Cls.repTest, dif_pos j.isLt]
    by_cases hz : dm j = 0
    · simp [hz]
    · have hb : (dm j != 0) = true := bne_iff_ne.2 hz
      by_cases hz2 : Cls.repOf key j = j
      · simp [hz, hz2, hb]
      · have hb2 : (Cls.repOf key j == (j : ℕ)) = false := by simpa using hz2
        simp [hz, hz2, hb, hb2]
  · have hX1 : 1 ≤ X := by have := j.isLt; omega
    have wD := wt_encFun_le' dm (fun i => (hdm i).trans hX1) hkX
    have wR := wt_encFun_le' (Cls.repOf key) (fun i => (Cls.repOf_lt key i).le.trans hkX) hkX
    have wC := wt_list2_le (encFun dm) (encFun (Cls.repOf key))
    have wA := wt_list2_le ctx (.nat j)
    have := wt_nat_le (j : ℕ)
    have := wt_nat_le (dm j)
    have := wt_nat_le (Cls.repOf key j)
    have := hdm j
    have := j.isLt
    have := Cls.repOf_lt key j
    have hb : (if Cls.repOf key j = j then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega
    have w01 : ∀ x : ℕ, x ≤ 1 → (Val.nat x).wt ≤ 3 := fun x hx => by
      have := wt_nat_le x; omega
    have := w01 _ hb
    have := w01 0 (by omega)
    have hm : max (Val.nat (if Cls.repOf key j = j then 1 else 0)).wt (Val.nat 0).wt ≤ 3 :=
      max_le (by omega) (by omega)
    have hm2 : max (k + 2 + 3 + 3 + 1) (0 + 3) ≤ k + 9 := max_le (by omega) (by omega)
    have hco : ctx.wt = (Val.list [encFun dm, encFun (Cls.repOf key)]).wt := rfl
    have hX : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    clear hout hd hr he h0 h1
    omega

/-! ### The number of a point -/

/-- On `[[dm, rep, reps], i]`: the position of `rep i` in `reps` if `dm i ≠ 0`, else the length
of `reps`. -/
def numF (fe : ℕ) : Expr :=
  .ite (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.call fe (mk2 (.get (.get (arg 0) (.nat 1)) (arg 1)) (.get (arg 0) (.nat 2))))
    (.length (.get (arg 0) (.nat 2)))

theorem num_det {P : Program} {f fe : ℕ} (hf : P.funs[f]? = some (numF fe))
    (hfe : P.HasAt fe (findEqFuns fe)) (dm key : Fin k → ℕ) (hdm : ∀ i, dm i ≤ 1) {X : ℕ}
    (hkX : k ≤ X) (i : Fin k) :
    FunDet P f (.list [.list [encFun dm, encFun (Cls.repOf key), natList (Cls.repsOf dm key)],
      .nat i]) (.nat (Cls.numOf dm key i)) (10 ^ 6 * (X + 1) ^ 3) := by
  set R := Cls.repsOf dm key with hR
  have hRle : ∀ x ∈ R, x ≤ X := fun x hx => by
    obtain ⟨h, -⟩ := (Cls.mem_repsOf dm key).1 hx; omega
  have hRl : R.length ≤ X := (Cls.repsOf_length_le dm key).trans hkX
  set ctx : Val := .list [encFun dm, encFun (Cls.repOf key), natList R] with hctx
  have hF := findEq_spec hfe (xs := R) (j := Cls.repOf key i) (B := X) hRle
    ((Cls.repOf_lt key i).le.trans hkX) hRl
  have h0 := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 0) rfl
  have h1 := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 1) rfl
  have hd := Det.get' (Det.get' h0 (Det.nat 0) (v := encFun dm) rfl) h1 (encFun_getElem? dm i)
  have hr := Det.get' (Det.get' h0 (Det.nat 1) (v := encFun (Cls.repOf key)) rfl) h1
    (encFun_getElem? (Cls.repOf key) i)
  have hR2 := Det.get' h0 (Det.nat 2) (v := natList R) rfl
  have hc := Det.call (Det.mk2 hr hR2) hF
  have hl := Det.length hR2
  have hout := Det.ite' hd hc hl
  have hval : (if dm i = 0 then Val.nat ((R.map Val.nat).length) else
      Val.nat (R.findIdx fun x => decide (x = Cls.repOf key i))) =
      .nat (Cls.numOf dm key i) := by
    unfold Cls.numOf; rw [← hR]; split_ifs <;> simp
  rw [hval] at hout
  refine FunDet.intro hf (hout.mono ?_)
  have hX1 : 1 ≤ X := by have := i.isLt; omega
  have wD := wt_encFun_le' dm (fun j => (hdm j).trans hX1) hkX
  have wRp := wt_encFun_le' (Cls.repOf key) (fun j => (Cls.repOf_lt key j).le.trans hkX) hkX
  have wRs : (natList R).wt ≤ 5 * (X + 1) ^ 2 := wt_natList_le_sq hRle hRl
  have wC := wt_list3_le (encFun dm) (encFun (Cls.repOf key)) (natList R)
  have wA := wt_list2_le ctx (.nat i)
  have wB := wt_list2_le (.nat (Cls.repOf key i)) (natList R)
  have := wt_nat_le (i : ℕ)
  have := wt_nat_le (dm i)
  have := wt_nat_le (Cls.repOf key i)
  have := hdm i
  have := i.isLt
  have := Cls.repOf_lt key i
  have hfi : R.findIdx (fun x => decide (x = Cls.repOf key i)) ≤ R.length := List.findIdx_le_length
  have := wt_nat_le (R.findIdx fun x => decide (x = Cls.repOf key i))
  have := wt_nat_le (Cls.numOf dm key i)
  have hnum : Cls.numOf dm key i ≤ R.length := by
    unfold Cls.numOf; rw [← hR]; split_ifs <;> omega
  have hlen : (R.map Val.nat).length = R.length := List.length_map _
  have := wt_nat_le R.length
  have := wt_nat_le (R.map Val.nat).length
  have hco : ctx.wt = (Val.list [encFun dm, encFun (Cls.repOf key), natList R]).wt := rfl
  have hnl : (natList R).wt = (Val.list (R.map Val.nat)).wt := rfl
  have hX : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hX2 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  simp only [findEqK]
  clear hout hd hr hc hl hR2 hF h0 h1 hval
  rw [_root_.max_def, _root_.max_def]
  split_ifs <;> omega

/-! ### The list of representatives -/

theorem filter_range_repQ (dm key : Fin k → ℕ) :
    ((List.range k).map Val.nat).filter (repQ dm key) = (Cls.repsOf dm key).map Val.nat := by
  rw [List.filter_map]; rfl

theorem reps_det {P : Program} {b p : ℕ} (hfilt : P.HasAt b (filterFuns b p))
    (hp : P.funs[p]? = some isRepF) (dm key : Fin k → ℕ) (hdm : ∀ i, dm i ≤ 1) {X : ℕ}
    (hkX : k ≤ X) :
    FunDet P b (.list [.list [encFun dm, encFun (Cls.repOf key)], natList (List.range k)])
      (natList (Cls.repsOf dm key)) (10 ^ 7 * (X + 1) ^ 3) := by
  set c : Val := .list [encFun dm, encFun (Cls.repOf key)] with hc
  have hP : ∀ x ∈ (List.range k).map Val.nat, FunDet P p (.list [c, x]) (boolVal (repQ dm key x))
      (1000 * (X + 1) ^ 2) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact isRep_det hp dm key hdm hkX ⟨j, List.mem_range.1 hj⟩
  have hF := filter_spec hfilt hP
  refine FunAll.mono hF fun w cost hw => ⟨by rw [hw.1, filter_range_repQ]; rfl, ?_⟩
  have hcst := hw.2
  rw [hw.1, filter_range_repQ] at hcst
  simp only [List.map_map, List.length_map, List.length_range] at hcst
  have hs : ((List.range k).map ((fun _ => 1000 * (X + 1) ^ 2) ∘ Val.nat)).sum =
      k * (1000 * (X + 1) ^ 2) := by
    rw [show ((fun _ => 1000 * (X + 1) ^ 2) ∘ Val.nat) = fun _ => 1000 * (X + 1) ^ 2 from rfl,
      List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
  rw [hs] at hcst
  have hX1 : k ≤ X := hkX
  have wD := wt_encFun_le' dm (B := X + 1) (fun i => (hdm i).trans (by omega)) (by omega)
  have wR := wt_encFun_le' (Cls.repOf key) (B := X + 1)
    (fun i => (Cls.repOf_lt key i).le.trans (by omega)) (by omega)
  have wC := wt_list2_le (encFun dm) (encFun (Cls.repOf key))
  have wI := wt_range_le k
  have hRle : ∀ x ∈ Cls.repsOf dm key, x ≤ X := fun x hx => by
    obtain ⟨h, -⟩ := (Cls.mem_repsOf dm key).1 hx; omega
  have hRl : (Cls.repsOf dm key).length ≤ X := (Cls.repsOf_length_le dm key).trans hkX
  have wO : (natList (Cls.repsOf dm key)).wt ≤ 5 * (X + 1) ^ 2 := wt_natList_le_sq hRle hRl
  have e1 : (Val.list ((Cls.repsOf dm key).map Val.nat)).wt = (natList (Cls.repsOf dm key)).wt :=
    rfl
  have e2 : (Val.list [c, .list ((List.range k).map Val.nat)]).wt =
      (Val.list [c, natList (List.range k)]).wt := rfl
  have wA := wt_list2_le c (natList (List.range k))
  have hco : c.wt = (Val.list [encFun dm, encFun (Cls.repOf key)]).wt := rfl
  have w4 : (k + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e3 : (X + 1 + 1) ^ 2 ≤ 4 * (X + 1) ^ 2 := by nlinarith
  have h2 : loopModK * (k + 1) * ((Val.list [c, natList (List.range k)]).wt + k +
      (natList (Cls.repsOf dm key)).wt + 1) ≤ loopModK * (X + 1) * (1000 * (X + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by nlinarith)
  have h3 : loopModK * (X + 1) * (1000 * (X + 1) ^ 2) = 1000000 * (X + 1) ^ 3 := by
    simp only [loopModK]; ring
  have h4 : k * (1000 * (X + 1) ^ 2) ≤ 1000 * (X + 1) ^ 3 := by nlinarith
  rw [e1, e2] at hcst
  omega

/-! ### The module -/

/-- The body of the class numbering on `[lab, dm]`: the environment grows as
`[a, ids, key, rep, reps, num]`, and the result is `[num, reps, rep]`. -/
def clsE (brange bkey brep bfilt bnum : ℕ) : Expr :=
  .letE (.call brange (.length (arg 0)))
  (.letE (.call bkey (mk2 (mk3 (arg 0) (arg 1) (.length (arg 0))) (.var 1)))
  (.letE (.call brep (mk2 (.var 2) (.var 1)))
  (.letE (.call bfilt (mk2 (mk2 (arg 1) (.var 3)) (.var 1)))
  (.letE (.call bnum (mk2 (mk3 (arg 1) (.var 3) (.var 4)) (.var 1)))
  (mk3 (.var 5) (.var 4) (.var 3))))))

/-- The class-numbering module at base `b` (24 functions). -/
def clsFuns (b : ℕ) : List Expr :=
  [clsE (b + 5) (b + 8) (b + 11) (b + 14) (b + 17), keyF, repF (b + 20), isRepF,
    numF (b + 20)] ++
  rangeFuns (b + 5) ++ mapFuns (b + 8) (b + 1) ++ mapFuns (b + 11) (b + 2) ++
  filterFuns (b + 14) (b + 3) ++ mapFuns (b + 17) (b + 4) ++ findEqFuns (b + 20)

theorem length_clsFuns (b : ℕ) : (clsFuns b).length = 24 := by
  simp [clsFuns, rangeFuns, mapFuns, filterFuns, findEqFuns, findFuns, loopFuns]

/-- The cost constant of the class numbering. -/
def clsK : ℕ := 10 ^ 9

/-- The result of the class numbering of `lab` on the domain `dm`. -/
def clsVal (lab dm : Fin k → ℕ) : Val :=
  .list [encFun (Cls.numOf dm (Cls.keyOf lab dm)), natList (Cls.repsOf dm (Cls.keyOf lab dm)),
    encFun (Cls.repOf (Cls.keyOf lab dm))]

set_option maxHeartbeats 1000000 in
/-- **The class numbering meets its specification.** -/
theorem cls_spec {P : Program} {b : ℕ} (h : P.HasAt b (clsFuns b)) (lab dm : Fin k → ℕ) {X : ℕ}
    (hlab : ∀ i, lab i ≤ X) (hdm : ∀ i, dm i ≤ 1) (hkX : k ≤ X) :
    FunDet P b (.list [encFun lab, encFun dm]) (clsVal lab dm) (clsK * (X + 1) ^ 4) := by
  have hentry : P.funs[b]? = some (clsE (b + 5) (b + 8) (b + 11) (b + 14) (b + 17)) :=
    (h.block 0 rfl : P.HasAt (b + 0) _).single
  have hkey : P.funs[b + 1]? = some keyF := (h.block 1 rfl : P.HasAt (b + 1) _).single
  have hrep : P.funs[b + 2]? = some (repF (b + 20)) := (h.block 2 rfl : P.HasAt (b + 2) _).single
  have hisr : P.funs[b + 3]? = some isRepF := (h.block 3 rfl : P.HasAt (b + 3) _).single
  have hnum : P.funs[b + 4]? = some (numF (b + 20)) := (h.block 4 rfl : P.HasAt (b + 4) _).single
  have hrange : P.HasAt (b + 5) (rangeFuns (b + 5)) := h.block 5 rfl
  have hmk : P.HasAt (b + 8) (mapFuns (b + 8) (b + 1)) := h.block 8 rfl
  have hmr : P.HasAt (b + 11) (mapFuns (b + 11) (b + 2)) := h.block 11 rfl
  have hfl : P.HasAt (b + 14) (filterFuns (b + 14) (b + 3)) := h.block 14 rfl
  have hmn : P.HasAt (b + 17) (mapFuns (b + 17) (b + 4)) := h.block 17 rfl
  have hfe : P.HasAt (b + 20) (findEqFuns (b + 20)) := h.block 20 rfl
  set key := Cls.keyOf lab dm with hkeydef
  have hkeyX : ∀ i, key i ≤ X := fun i => by
    simp only [hkeydef, Cls.keyOf]; split_ifs; exacts [hkX, hlab i]
  have hX1 : 1 ≤ X + 1 := by omega
  -- weights
  have wL := wt_encFun_le' lab hlab hkX
  have wD := wt_encFun_le' dm (B := X + 1) (fun i => (hdm i).trans (by omega)) (by omega)
  have wK := wt_encFun_le' key hkeyX hkX
  have wR := wt_encFun_le' (Cls.repOf key) (B := X)
    (fun i => (Cls.repOf_lt key i).le.trans hkX) hkX
  have hRle : ∀ x ∈ Cls.repsOf dm key, x ≤ X := fun x hx => by
    obtain ⟨h, -⟩ := (Cls.mem_repsOf dm key).1 hx; omega
  have hRl : (Cls.repsOf dm key).length ≤ X := (Cls.repsOf_length_le dm key).trans hkX
  have wRs : (natList (Cls.repsOf dm key)).wt ≤ 5 * (X + 1) ^ 2 := wt_natList_le_sq hRle hRl
  have hnumX : ∀ i, Cls.numOf dm key i ≤ X := fun i => by
    unfold Cls.numOf; split_ifs
    · omega
    · exact List.findIdx_le_length.trans hRl
  have wN := wt_encFun_le' (Cls.numOf dm key) hnumX hkX
  have wI := wt_range_le k
  have e4 : (X + 1 + 1) ^ 2 ≤ 4 * (X + 1) ^ 2 := by nlinarith
  have hk2 : (k + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  set a : Val := .list [encFun lab, encFun dm] with ha
  have wA := wt_list2_le (encFun lab) (encFun dm)
  have hlen : ((List.finRange k).map fun i => Val.nat (lab i)).length = k := by simp
  -- the steps
  have d0 := Det.arg' (P := P) (vs := [encFun lab, encFun dm]) (rest := []) (j := 0) rfl
  have dlen := Det.length (vs := (List.finRange k).map fun i => Val.nat (lab i)) d0
  simp only [List.length_map, List.length_finRange] at dlen
  have d1 := Det.call dlen (range_det hrange k)
  have dkey : FunDet P (b + 8) (.list [.list [encFun lab, encFun dm, .nat k],
      natList (List.range k)]) (encFun key) (k * (1000 * (X + 1) ^ 2) + 10 ^ 6 * (X + 1) ^ 3) :=
    tab_det hmk (fun i => key_det hkey lab dm hlab hdm hkX i) hkeyX (by
      have := wt_list3_le (encFun lab) (encFun dm) (.nat k)
      have := wt_nat_le k
      nlinarith) hkX
  have drep : FunDet P (b + 11) (.list [encFun key, natList (List.range k)])
      (encFun (Cls.repOf key)) (k * (10 ^ 6 * (X + 1) ^ 3) + 10 ^ 6 * (X + 1) ^ 3) :=
    tab_det hmr (fun i => rep_det hrep hfe key hkeyX hkX i)
      (fun i => (Cls.repOf_lt key i).le.trans hkX) (by nlinarith) hkX
  have dreps := reps_det hfl hisr dm key hdm hkX
  have dnum : FunDet P (b + 17) (.list [.list [encFun dm, encFun (Cls.repOf key),
      natList (Cls.repsOf dm key)], natList (List.range k)]) (encFun (Cls.numOf dm key))
      (k * (10 ^ 6 * (X + 1) ^ 3) + 10 ^ 6 * (X + 1) ^ 3) :=
    tab_det hmn (fun i => num_det hnum hfe dm key hdm hkX i) hnumX (by
      have := wt_list3_le (encFun dm) (encFun (Cls.repOf key)) (natList (Cls.repsOf dm key))
      nlinarith) hkX
  set ids := natList (List.range k) with hids
  set R := natList (Cls.repsOf dm key) with hR
  have s2 := Det.call (Det.mk2 (Det.mk3 (Det.arg' (P := P) (vs := [encFun lab, encFun dm])
    (rest := [ids]) (j := 0) rfl) (Det.arg' (P := P) (vs := [encFun lab, encFun dm])
    (rest := [ids]) (j := 1) rfl) (by
      have := Det.length (vs := (List.finRange k).map fun i => Val.nat (lab i))
        (Det.arg' (P := P) (vs := [encFun lab, encFun dm]) (rest := [ids]) (j := 0) rfl)
      simp only [List.length_map, List.length_finRange] at this; exact this)) (Det.var' (P := P) (env := [a, ids]) (i := 1) rfl)) dkey
  have s3 := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, ids, encFun key]) (i := 2) rfl)
    (Det.var' (P := P) (env := [a, ids, encFun key]) (i := 1) rfl)) drep
  have s4 := Det.call (Det.mk2 (Det.mk2 (Det.arg' (P := P) (vs := [encFun lab, encFun dm])
      (rest := [ids, encFun key, encFun (Cls.repOf key)]) (j := 1) rfl)
    (Det.var' (P := P) (env := [a, ids, encFun key, encFun (Cls.repOf key)]) (i := 3) rfl))
    (Det.var' (P := P) (env := [a, ids, encFun key, encFun (Cls.repOf key)]) (i := 1) rfl)) dreps
  have s5 := Det.call (Det.mk2 (Det.mk3 (Det.arg' (P := P) (vs := [encFun lab, encFun dm])
      (rest := [ids, encFun key, encFun (Cls.repOf key), R]) (j := 1) rfl)
    (Det.var' (P := P) (env := [a, ids, encFun key, encFun (Cls.repOf key), R]) (i := 3) rfl)
    (Det.var' (P := P) (env := [a, ids, encFun key, encFun (Cls.repOf key), R]) (i := 4) rfl))
    (Det.var' (P := P) (env := [a, ids, encFun key, encFun (Cls.repOf key), R]) (i := 1) rfl)) dnum
  have s6 := Det.mk3
    (Det.var' (P := P) (env := [a, ids, encFun key, encFun (Cls.repOf key), R,
      encFun (Cls.numOf dm key)]) (i := 5) rfl)
    (Det.var' (P := P) (env := [a, ids, encFun key, encFun (Cls.repOf key), R,
      encFun (Cls.numOf dm key)]) (i := 4) rfl)
    (Det.var' (P := P) (env := [a, ids, encFun key, encFun (Cls.repOf key), R,
      encFun (Cls.numOf dm key)]) (i := 3) rfl)
  refine FunDet.intro hentry ((Det.letE d1 (Det.letE s2 (Det.letE s3 (Det.letE s4
    (Det.letE s5 s6))))).mono ?_)
  have w3 := wt_list3_le (encFun lab) (encFun dm) (.nat k)
  have w3' := wt_list2_le (.list [encFun lab, encFun dm, .nat k]) ids
  have w4 := wt_list2_le (encFun key) ids
  have w5 := wt_list2_le (encFun dm) (encFun (Cls.repOf key))
  have w5' := wt_list2_le (.list [encFun dm, encFun (Cls.repOf key)]) ids
  have w6 := wt_list3_le (encFun dm) (encFun (Cls.repOf key)) R
  have w6' := wt_list2_le (.list [encFun dm, encFun (Cls.repOf key), R]) ids
  have w7 := wt_list3_le (encFun (Cls.numOf dm key)) R (encFun (Cls.repOf key))
  have wk := wt_nat_le k
  have hX3 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hX4 : (X + 1) ^ 3 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hk3 : (k + 1) ^ 3 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have m1 : k * (1000 * (X + 1) ^ 2) ≤ 1000 * (X + 1) ^ 3 := mul_le_pow_succ 1000 2 hkX
  have m2 : k * (10 ^ 6 * (X + 1) ^ 3) ≤ 10 ^ 6 * (X + 1) ^ 4 := mul_le_pow_succ _ 3 hkX
  have hwa : a.wt = (Val.list [encFun lab, encFun dm]).wt := rfl
  have hwi : ids.wt ≤ 4 * (k + 1) ^ 2 := wI
  have hwR : R.wt ≤ 5 * (X + 1) ^ 2 := wRs
  have ho : ((List.finRange k).map fun i => Val.nat (lab i)).length = k := by simp
  have hXd : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  simp only [clsK]
  clear d0 dlen d1 dkey drep dreps dnum s2 s3 s4 s5 s6
  clear_value ids R a key
  omega

/-! ### The action of the generators on the numbers -/

/-- A permutation of `Fin k` as a function on numbers (`0` above `k`). -/
def permAt (g : Perm (Fin k)) (r : ℕ) : ℕ := if h : r < k then g ⟨r, h⟩ else 0

/-- A function on `Fin k` as a function on numbers (`0` above `k`). -/
def funAt (f : Fin k → ℕ) (r : ℕ) : ℕ := if h : r < k then f ⟨r, h⟩ else 0

/-- The numbers of the images of the representatives under `g`. -/
def actList (num : Fin k → ℕ) (reps : List ℕ) (g : Perm (Fin k)) : List ℕ :=
  reps.map fun r => funAt num (permAt g r)

/-- On `[[num, reps], g]`: `gather (num, gather (g, reps))`. -/
def actF (bg : ℕ) : Expr :=
  .call bg (mk2 (.get (arg 0) (.nat 0)) (.call bg (mk2 (arg 1) (.get (arg 0) (.nat 1)))))

theorem gather_fun (f : Fin k → ℕ) (is : List ℕ) (hi : ∀ i ∈ is, i < k) :
    is.map (fun i => ((List.finRange k).map fun j => Val.nat (f j)).getD i (.nat 0)) =
      (is.map (funAt f)).map Val.nat := by
  rw [List.map_map]
  refine List.map_congr_left fun i hi' => ?_
  have h := hi i hi'
  simp [funAt, h, List.getD_eq_getElem?_getD]

theorem actF_det {P : Program} {f bg : ℕ} (hf : P.funs[f]? = some (actF bg))
    (hg : P.HasAt bg (gatherFuns bg)) (num : Fin k → ℕ) (reps : List ℕ) {X : ℕ}
    (hnum : ∀ i, num i ≤ X) (hreps : ∀ r ∈ reps, r < k) (hlen : reps.length ≤ X) (hkX : k ≤ X)
    (g : Perm (Fin k)) :
    FunDet P f (.list [.list [encFun num, natList reps], encPerm g])
      (natList (actList num reps g)) (10 ^ 12 * (X + 1) ^ 6) := by
  have hX1 : ∀ r ∈ reps, r ≤ X := fun r hr => by have := hreps r hr; omega
  have wN := wt_encFun_le' num hnum hkX
  have wR : (natList reps).wt ≤ 5 * (X + 1) ^ 2 := wt_natList_le_sq hX1 hlen
  have wG : (encPerm g).wt ≤ 4 * (X + 1) ^ 2 :=
    (wt_encPerm_le g).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  set c : Val := .list [encFun num, natList reps] with hc
  have h0 := Det.arg' (P := P) (vs := [c, encPerm g]) (rest := []) (j := 0) rfl
  have h1 := Det.arg' (P := P) (vs := [c, encPerm g]) (rest := []) (j := 1) rfl
  have hn := Det.get' h0 (Det.nat 0) (v := encFun num) rfl
  have hr := Det.get' h0 (Det.nat 1) (v := natList reps) rfl
  -- inner gather
  have gi := gather_spec hg (L := (List.finRange k).map fun j => Val.nat (g j)) (is := reps)
    (by simpa using hreps)
  have e1 : reps.map (fun i => ((List.finRange k).map fun j => Val.nat (g j)).getD i (.nat 0)) =
      (reps.map (permAt g)).map Val.nat := gather_fun (fun j => (g j : ℕ)) reps hreps
  rw [e1] at gi
  have hin := Det.call (Det.mk2 h1 hr) gi
  -- outer gather
  have hpl : ∀ i ∈ reps.map (permAt g), i < k := by
    intro i hi
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hi
    have := hreps r hr'
    simp [permAt, this]
  have go := gather_spec hg (L := (List.finRange k).map fun j => Val.nat (num j))
    (is := reps.map (permAt g)) (by simpa using hpl)
  rw [gather_fun num _ hpl] at go
  have hout := Det.call (Det.mk2 hn hin) go
  refine FunDet.intro hf (hout.post fun cost hc' => ⟨?_, ?_⟩)
  · simp [actList, natList, List.map_map]
  · have hP : ∀ x ∈ reps.map (permAt g), x ≤ X := fun x hx => (hpl x hx).le.trans hkX
    have wP : (natList (reps.map (permAt g))).wt ≤ 5 * (X + 1) ^ 2 :=
      wt_natList_le_sq hP (by simpa using hlen)
    have hQ : ∀ x ∈ (reps.map (permAt g)).map (funAt num), x ≤ X := by
      intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      unfold funAt; split_ifs; exacts [hnum _, Nat.zero_le _]
    have wQ : (natList ((reps.map (permAt g)).map (funAt num))).wt ≤ 5 * (X + 1) ^ 2 :=
      wt_natList_le_sq hQ (by simpa using hlen)
    have e2 : (Val.list (((reps.map (permAt g)).map (funAt num)).map Val.nat)).wt =
        (natList ((reps.map (permAt g)).map (funAt num))).wt := rfl
    have e3 : (Val.list ((reps.map (permAt g)).map Val.nat)).wt =
        (natList (reps.map (permAt g))).wt := rfl
    have e4 : (Val.list ((List.finRange k).map fun j => Val.nat (g j))).wt = (encPerm g).wt := rfl
    have e5 : (Val.list ((List.finRange k).map fun j => Val.nat (num j))).wt = (encFun num).wt :=
      rfl
    have wA := wt_list2_le c (encPerm g)
    have wC := wt_list2_le (encFun num) (natList reps)
    have wI := wt_list2_le (.list ((List.finRange k).map fun j => Val.nat (g j))) (natList reps)
    have wO := wt_list2_le (.list ((List.finRange k).map fun j => Val.nat (num j)))
      (natList (reps.map (permAt g)))
    have wI2 := wt_list2_le (encPerm g) (natList reps)
    have wO2 := wt_list2_le (encFun num) (natList (reps.map (permAt g)))
    have e6 : (Val.list [encFun num, Val.list ((reps.map (permAt g)).map Val.nat)]).wt =
        (Val.list [encFun num, natList (reps.map (permAt g))]).wt := rfl
    -- the two gather bounds
    obtain ⟨Y, hY⟩ : ∃ Y, X + 1 = Y := ⟨_, rfl⟩
    have hY1 : 1 ≤ Y := by omega
    have g1 : gatherK * ((Val.list [.list ((List.finRange k).map fun j => Val.nat (g j)),
        natList reps]).wt + 1) ^ 3 ≤ gatherK * (100 * Y ^ 2) ^ 3 := by
      refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 3)
      rw [e4] at wI; rw [hY] at wG wR; nlinarith
    have g2 : gatherK * ((Val.list [.list ((List.finRange k).map fun j => Val.nat (num j)),
        natList (reps.map (permAt g))]).wt + 1) ^ 3 ≤ gatherK * (100 * Y ^ 2) ^ 3 := by
      refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 3)
      rw [e5] at wO; rw [hY] at wN wP; nlinarith
    have g3 : gatherK * (100 * Y ^ 2) ^ 3 = 10 ^ 11 * Y ^ 6 := by simp only [gatherK]; ring
    have hco : c.wt = (Val.list [encFun num, natList reps]).wt := rfl
    have hY6 : Y ^ 2 ≤ Y ^ 6 := Nat.pow_le_pow_right hY1 (by norm_num)
    rw [e2, e3, e6] at hc'
    rw [hY] at wN wR wG wP wQ ⊢
    clear hout hin go gi hn hr h0 h1 hc
    have hY0 : 1 ≤ Y ^ 6 := Nat.one_le_pow _ _ hY1
    clear_value c
    omega

theorem forall₂_eq_map {α β : Type*} {f : α → β} :
    ∀ {l : List α} {ws : List β}, List.Forall₂ (fun a w => w = f a) l ws → ws = l.map f
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h t => by rw [h, forall₂_eq_map t]; rfl

theorem wt_list_map_le' {α : Type*} (l : List α) (f : α → Val) {W : ℕ}
    (hf : ∀ a ∈ l, (f a).wt ≤ W) : (Val.list (l.map f)).wt ≤ l.length * (2 * W + 1) + 4 := by
  have h1 := wt_list_le (l.map f)
  have h2 : ((l.map f).map Val.wt).sum ≤ l.length * W := by
    have := List.sum_le_card_nsmul ((l.map f).map Val.wt) W (by
      simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      exact hf)
    simpa using this
  simp only [List.length_map] at h1
  nlinarith

open GI.Cited (encGroup)

/-- On `[[num, reps], [k, perms]]`: the number of classes and the action of each permutation on
the class numbers. -/
def actE (bm : ℕ) : Expr :=
  mk2 (.length (.get (arg 0) (.nat 1))) (.call bm (mk2 (arg 0) (.get (arg 1) (.nat 1))))

/-- The action module at base `b` (9 functions). -/
def actFuns (b : ℕ) : List Expr :=
  [actE (b + 2), actF (b + 5)] ++ mapFuns (b + 2) (b + 1) ++ gatherFuns (b + 5)

theorem length_actFuns (b : ℕ) : (actFuns b).length = 9 := by
  simp [actFuns, mapFuns, gatherFuns, loopFuns]

/-- The value computed by the action module. -/
def actVal (num : Fin k → ℕ) (reps : List ℕ) (gs : List (Perm (Fin k))) : Val :=
  .list [.nat reps.length, .list ((1 :: gs).map fun g => natList (actList num reps g))]

theorem wt_actList_le (num : Fin k → ℕ) (reps : List ℕ) {X : ℕ} (hnum : ∀ i, num i ≤ X)
    (hlen : reps.length ≤ X) (g : Perm (Fin k)) :
    (natList (actList num reps g)).wt ≤ 5 * (X + 1) ^ 2 := by
  refine wt_natList_le_sq (fun x hx => ?_) (by simpa [actList] using hlen)
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  unfold funAt; split_ifs; exacts [hnum _, Nat.zero_le _]

/-- **The action module meets its specification.** -/
theorem act_spec {P : Program} {b : ℕ} (h : P.HasAt b (actFuns b)) (num : Fin k → ℕ)
    (reps : List ℕ) (gs : List (Perm (Fin k))) {X : ℕ} (hnum : ∀ i, num i ≤ X)
    (hreps : ∀ r ∈ reps, r < k) (hlen : reps.length ≤ X) (hkX : k ≤ X) (hgs : gs.length ≤ X ^ 2) :
    FunDet P b (.list [.list [encFun num, natList reps], encGroup gs]) (actVal num reps gs)
      (10 ^ 15 * (X + 1) ^ 8) := by
  have hentry : P.funs[b]? = some (actE (b + 2)) := (h.block 0 rfl : P.HasAt (b + 0) _).single
  have hf : P.funs[b + 1]? = some (actF (b + 5)) := (h.block 1 rfl : P.HasAt (b + 1) _).single
  have hm : P.HasAt (b + 2) (mapFuns (b + 2) (b + 1)) := h.block 2 rfl
  have hg : P.HasAt (b + 5) (gatherFuns (b + 5)) := h.block 5 rfl
  set c : Val := .list [encFun num, natList reps] with hc
  obtain ⟨Y, hY⟩ : ∃ Y, X + 1 = Y := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by omega
  have hM := map_spec hm (c := c) (xs := (1 :: gs).map encPerm)
    (R := fun x w => ∀ g : Perm (Fin k), x = encPerm g → w = natList (actList num reps g))
    (B := fun _ => 10 ^ 12 * (X + 1) ^ 6) (by
      intro x hx
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
      refine FunAll.mono (actF_det hf hg num reps hnum hreps hlen hkX g) fun w cost hw =>
        ⟨fun g' hg' => ?_, hw.2⟩
      have : g' = g := encPerm_injective hg'.symm
      rw [hw.1, this])
  have hM' : FunDet P (b + 2) (.list [c, .list ((1 :: gs).map encPerm)])
      (.list ((1 :: gs).map fun g => natList (actList num reps g)))
      ((1 + gs.length) * (10 ^ 12 * Y ^ 6) + 1000 * (gs.length + 2) *
        ((Val.list [c, .list ((1 :: gs).map encPerm)]).wt +
          (Val.list ((1 :: gs).map fun g => natList (actList num reps g))).wt + 1)) := by
    refine FunAll.mono hM fun w cost hw => ?_
    obtain ⟨ws, rfl, hws, hcost⟩ := hw
    have hws' : ws = (1 :: gs).map fun g => natList (actList num reps g) := by
      rw [List.forall₂_map_left_iff] at hws
      exact forall₂_eq_map (hws.imp fun a w hw => hw a rfl)
    subst hws'
    refine ⟨rfl, ?_⟩
    simp only [List.map_map, List.length_map, List.length_cons, mapK] at hcost
    rw [show ((fun _ => 10 ^ 12 * (X + 1) ^ 6) ∘ encPerm) =
      fun _ : Perm (Fin k) => 10 ^ 12 * (X + 1) ^ 6 from rfl, List.map_const', List.sum_replicate,
      smul_eq_mul, List.length_cons, hY] at hcost
    exact hcost.trans (le_of_eq (by ring))
  have d0 := Det.arg' (P := P) (vs := [c, encGroup gs]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [c, encGroup gs]) (rest := []) (j := 1) rfl
  have dr := Det.get' d0 (Det.nat 1) (v := natList reps) rfl
  have dl := Det.length (vs := reps.map Val.nat) dr
  rw [List.length_map] at dl
  have dp := Det.get' d1 (Det.nat 1) (v := .list ((1 :: gs).map encPerm)) rfl
  have dc := Det.call (Det.mk2 d0 dp) hM'
  have hout := Det.mk2 dl dc
  refine FunDet.intro hentry (hout.mono ?_)
  -- weights
  have wN := wt_encFun_le' num hnum hkX
  have hX1 : ∀ r ∈ reps, r ≤ X := fun r hr => by have := hreps r hr; omega
  have wR : (natList reps).wt ≤ 5 * (X + 1) ^ 2 := wt_natList_le_sq hX1 hlen
  have wC := wt_list2_le (encFun num) (natList reps)
  have hco : c.wt = (Val.list [encFun num, natList reps]).wt := rfl
  have wP := wt_list_map_le' (1 :: gs) encPerm (W := 4 * (X + 1) ^ 2) (fun g _ =>
    (wt_encPerm_le g).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)))
  have wQ := wt_list_map_le' (1 :: gs) (fun g => natList (actList num reps g))
    (W := 5 * (X + 1) ^ 2) (fun g _ => wt_actList_le num reps hnum hlen g)
  have wG : (encGroup gs).wt ≤ 2 * ((Val.nat k).wt + (Val.list ((1 :: gs).map encPerm)).wt) + 6 :=
    wt_list2_le _ _
  have wk := wt_nat_le k
  have wl := wt_nat_le reps.length
  have wA := wt_list2_le c (encGroup gs)
  have wI := wt_list2_le c (.list ((1 :: gs).map encPerm))
  have wO := wt_list2_le (.nat reps.length)
    (.list ((1 :: gs).map fun g => natList (actList num reps g)))
  simp only [List.length_cons] at wP wQ
  rw [hY] at wN wR wP wQ ⊢
  have hk : k + 1 ≤ Y := by omega
  have hg2 : gs.length + 1 ≤ Y ^ 2 := by
    have : X ^ 2 + 1 ≤ (X + 1) ^ 2 := by nlinarith
    rw [hY] at this; omega
  set W1 := (Val.list ((1 :: gs).map encPerm)).wt
  set W2 := (Val.list ((1 :: gs).map fun g => natList (actList num reps g))).wt
  have hW1 : W1 ≤ 9 * Y ^ 4 + 4 := by nlinarith
  have hW2 : W2 ≤ 11 * Y ^ 4 + 4 := by nlinarith
  have hY24 : Y ^ 2 ≤ Y ^ 4 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY46 : Y ^ 4 ≤ Y ^ 6 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY68 : Y ^ 6 ≤ Y ^ 8 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hYY : 1 ≤ Y ^ 2 := Nat.one_le_pow _ _ hY1
  have m1 : (1 + gs.length) * (10 ^ 12 * Y ^ 6) ≤ 10 ^ 12 * Y ^ 8 := by
    have : (1 + gs.length) * (10 ^ 12 * Y ^ 6) ≤ Y ^ 2 * (10 ^ 12 * Y ^ 6) :=
      Nat.mul_le_mul_right _ (by omega)
    calc _ ≤ Y ^ 2 * (10 ^ 12 * Y ^ 6) := this
      _ = 10 ^ 12 * Y ^ 8 := by ring
  have m2 : 1000 * (gs.length + 2) * ((Val.list [c, .list ((1 :: gs).map encPerm)]).wt + W2 + 1)
      ≤ 1000 * (2 * Y ^ 2) * (200 * Y ^ 4) := by
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_
    omega
  have m3 : 1000 * (2 * Y ^ 2) * (200 * Y ^ 4) = 400000 * Y ^ 6 := by ring
  clear hout dc dl dp dr d0 d1 hM hM'
  have hYq : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  clear_value c W1 W2
  omega

/-! ### The computed action is the class action -/

/-- **The computed action is the class action.** If the `t`-th representative is a point of
the domain with number `t`, and `ρ` acts on the numbers as `num`, then the list computed for a
generator `g` of `G` is the permutation `homFin e ρ g`. -/
theorem actList_eq {Ω : Type} {G : Subgroup (Perm Ω)} {D : Set Ω} {e : Ω ≃ Fin k}
    {num : Fin k → ℕ} {reps : List ℕ} {d : ℕ} (hdl : reps.length = d) {ρ : G →* Perm (Fin d)}
    (hrep : ∀ t (ht : t < reps.length), ∃ hr : reps[t] < k, e.symm ⟨_, hr⟩ ∈ D ∧
      num ⟨_, hr⟩ = t)
    (hρ : ∀ g : Perm (Fin k), (toFin e).symm g ∈ G → ∀ (r : Fin k), e.symm r ∈ D →
      ∀ hlt : num r < d, ((homFin e ρ g) ⟨num r, hlt⟩ : ℕ) = num (g r))
    {g : Perm (Fin k)} (hg : (toFin e).symm g ∈ G) :
    natList (actList num reps g) = encPerm (homFin e ρ g) := by
  subst hdl
  unfold natList encPerm
  congr 1
  refine List.ext_getElem (by simp [actList]) fun t h1 h2 => ?_
  have ht : t < reps.length := by simpa [actList] using h1
  obtain ⟨hr, hD, hnum⟩ := hrep t ht
  simp only [actList, List.map_map, List.getElem_map, Function.comp_apply, List.getElem_finRange]
  congr 1
  have hgr : ((g ⟨_, hr⟩ : Fin k) : ℕ) < k := (g ⟨_, hr⟩).isLt
  have e1 : funAt num (permAt g reps[t]) = num (g ⟨_, hr⟩) := by
    simp [permAt, funAt, hr, hgr]
  rw [e1, ← hρ g hg ⟨_, hr⟩ hD (by rw [hnum]; exact ht)]
  congr 2
  exact Fin.ext (by simp [hnum])

/-! ### Weights of the outputs -/

theorem numOf_le (dm key : Fin k → ℕ) (i : Fin k) : Cls.numOf dm key i ≤ k := by
  have := Cls.repsOf_length_le dm key
  unfold Cls.numOf; split_ifs
  · omega
  · exact List.findIdx_le_length.trans this

theorem wt_clsVal_le (lab dm : Fin k → ℕ) : (clsVal lab dm).wt ≤ 40 * (k + 1) ^ 2 := by
  have w1 := wt_encFun_le' (Cls.numOf dm (Cls.keyOf lab dm)) (B := k) (numOf_le _ _) le_rfl
  have w2 : (natList (Cls.repsOf dm (Cls.keyOf lab dm))).wt ≤ 5 * (k + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by
      obtain ⟨h, -⟩ := (Cls.mem_repsOf dm _).1 hx; omega) (Cls.repsOf_length_le _ _)
  have w3 := wt_encFun_le' (Cls.repOf (Cls.keyOf lab dm)) (B := k)
    (fun i => (Cls.repOf_lt _ i).le) le_rfl
  have := wt_list3_le (encFun (Cls.numOf dm (Cls.keyOf lab dm)))
    (natList (Cls.repsOf dm (Cls.keyOf lab dm))) (encFun (Cls.repOf (Cls.keyOf lab dm)))
  have h1 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold clsVal
  omega

theorem wt_actVal_le (num : Fin k → ℕ) (reps : List ℕ) (gs : List (Perm (Fin k))) {X : ℕ}
    (hnum : ∀ i, num i ≤ X) (hlen : reps.length ≤ X) (hkX : k ≤ X) (hgs : gs.length ≤ X ^ 2) :
    (actVal num reps gs).wt ≤ 100 * (X + 1) ^ 4 := by
  have wQ := wt_list_map_le' (1 :: gs) (fun g => natList (actList num reps g))
    (W := 5 * (X + 1) ^ 2) (fun g _ => wt_actList_le num reps hnum hlen g)
  have wO := wt_list2_le (.nat reps.length)
    (.list ((1 :: gs).map fun g => natList (actList num reps g)))
  have wl := wt_nat_le reps.length
  simp only [List.length_cons] at wQ
  have hg : gs.length + 1 ≤ (X + 1) ^ 2 := by nlinarith
  have h1 : (gs.length + 1) * (2 * (5 * (X + 1) ^ 2) + 1) ≤ (X + 1) ^ 2 * (11 * (X + 1) ^ 2) := by
    apply Nat.mul_le_mul hg; nlinarith
  have h2 : (X + 1) ^ 2 * (11 * (X + 1) ^ 2) = 11 * (X + 1) ^ 4 := by ring
  have h3 : X + 1 ≤ (X + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  unfold actVal
  omega

end GI.Impl
