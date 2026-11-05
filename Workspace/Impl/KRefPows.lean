module

public import Workspace.Impl.KRefLib

@[expose] public section

/-!
# Powers and digits

* `krefPowFuns b` (four functions): on `[m, e, []]`, the list `[m^0, …, m^(e-1)]`.
* `krefDigFuns b` (five functions): on `[[pw, base], x]`, the list of `x / p % base` for `p` in
  `pw`. With `pw` the powers of `base`, these are the digits of `x` in base `base`, lowest first,
  which are the entries of the tuple `finFunctionFinEquiv.symm x`.
-/

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

/-! ### Powers -/

/-- The step of `pows`: add `m^i` at the end. -/
def krefPowG : Expr :=
  .snoc (arg 2) (.ite (arg 1)
    (.arith .mul (.get (arg 2) (.arith .sub (arg 1) (.nat 1))) (arg 0)) (.nat 1))

/-- `pows`, at base `b` (four functions). -/
def krefPowFuns (b : ℕ) : List Expr := iterFuns b (b + 3) ++ [krefPowG]

/-- `[m^0, …, m^(i-1)]`. -/
def krefPowList (m i : ℕ) : List ℕ := (List.range i).map (m ^ ·)

theorem krefPowList_succ (m i : ℕ) : krefPowList m (i + 1) = krefPowList m i ++ [m ^ i] := by
  simp [krefPowList, List.range_succ]

theorem wt_krefPowList_mono (m : ℕ) {i j : ℕ} (h : i ≤ j) :
    (natList (krefPowList m i)).wt ≤ (natList (krefPowList m j)).wt := by
  apply wt_list_mono
  refine ⟨((List.range' i (j - i)).map (m ^ ·)).map Val.nat, ?_⟩
  simp only [natList, krefPowList, ← List.map_append]
  congr 2
  rw [show j = i + (j - i) by omega, List.range_add]
  simp [List.range'_eq_map_range, Nat.add_sub_cancel_left]

theorem kref_powG {P : Program} {g : ℕ} (hg : P.funs[g]? = some krefPowG) {m i Z : ℕ}
    (hm : m ≤ Z) (hi : i ≤ Z) (hw : (natList (krefPowList m (i + 1))).wt ≤ Z) :
    FunDet P g (.list [.nat m, .nat i, natList (krefPowList m i)])
      (natList (krefPowList m (i + 1))) (300 * (Z + 1) ^ 1) := by
  have hwacc : (natList (krefPowList m i)).wt ≤ Z :=
    (wt_krefPowList_mono m (Nat.le_succ i)).trans hw
  have hWA : (Val.list [.nat m, .nat i, natList (krefPowList m i)]).wt ≤ 6 * Z + 15 := by
    have := wt_list3_le (.nat m) (.nat i) (natList (krefPowList m i))
    have := wt_nat_le m
    have := wt_nat_le i
    omega
  set acc := natList (krefPowList m i) with hacc
  set A : List Val := [.nat m, .nat i, acc]
  have hv : (Val.nat (m ^ i)).wt ≤ Z := by
    have : Val.nat (m ^ i) ∈ (krefPowList m (i + 1)).map Val.nat := by
      simp [krefPowList_succ]
    exact (wt_le_wt_list this).le.trans hw
  have hA2 : Det P [.list A] (arg 2) acc (2 * (Val.list A).wt + 2 + 5) := Det.arg' rfl
  have hA1 : Det P [.list A] (arg 1) (.nat i) (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
  have hA0 : Det P [.list A] (arg 0) (.nat m) (2 * (Val.list A).wt + 0 + 5) := Det.arg' rfl
  have hite : Det P [.list A]
      (.ite (arg 1) (.arith .mul (.get (arg 2) (.arith .sub (arg 1) (.nat 1))) (arg 0)) (.nat 1))
      (.nat (m ^ i)) (2 * (Val.list A).wt + 6 + max (8 * (Val.list A).wt + 4 * Z + 60) 4 +
        (Val.nat (m ^ i)).wt + 1) := by
    refine Det.ite hA1 (fun hi0 => ?_) (fun hi0 => ?_)
    · have hsub := Det.arith' (op := .sub) hA1 (Det.nat (P := P) (env := [.list A]) 1)
        (z := i - 1) rfl
      have hx : ((krefPowList m i).map Val.nat)[i - 1]? = some (.nat (m ^ (i - 1))) := by
        simp [krefPowList, List.getElem?_range (show i - 1 < i by omega)]
      have hgt := Det.get' hA2 hsub hx
      have hmul := Det.arith (op := .mul) hgt hA0
      have he : BinOp.eval .mul (m ^ (i - 1)) m = m ^ i := by
        simp only [BinOp.eval]
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [he] at hmul
      refine hmul.mono ?_
      have h1 : (Val.nat (m ^ (i - 1))).wt < acc.wt :=
        wt_le_wt_list (List.mem_of_getElem? hx)
      omega
    · subst hi0
      exact (Det.nat 1).mono (by omega)
  have hs := Det.snoc hA2 hite
  rw [show natList (krefPowList m (i + 1)) = .list ((krefPowList m i).map Val.nat ++
    [.nat (m ^ i)]) by simp [natList, krefPowList_succ]]
  refine FunDet.intro hg (hs.mono ?_)
  have e : (Val.list ((krefPowList m i).map Val.nat ++ [.nat (m ^ i)])) =
      natList (krefPowList m (i + 1)) := by simp [natList, krefPowList_succ]
  rw [e]
  simp only [pow_one]
  omega

/-- **Powers.** -/
theorem kref_pows {P : Program} {b : ℕ} (h : P.HasAt b (krefPowFuns b)) {m e Z : ℕ}
    (hm : m ≤ Z) (he : e ≤ Z) (hw : (natList (krefPowList m e)).wt ≤ Z) :
    FunDet P b (.list [.nat m, .nat e, .list []]) (natList (krefPowList m e))
      (loopModK * 320 * 27 * (Z + 1) ^ 3) := by
  have hit : P.HasAt b (iterFuns b (b + 3)) := h.left
  have hg : P.funs[b + 3]? = some krefPowG := by
    simpa [iterFuns, loopFuns] using h.right.single
  have := kref_iterA hit (c := .nat m) (n := e) (accs := fun i => natList (krefPowList m i))
    (Y := Z) (K := 300) (d := 1) (A := 2) (by norm_num)
    (fun i hi => kref_powG hg hm (by omega)
      ((wt_krefPowList_mono m (by omega)).trans hw))
    (fun i hi => by
      show (natList (krefPowList m i)).wt ≤ 2 * (Z + 1)
      have := (wt_krefPowList_mono m hi).trans hw; omega)
    (by have := wt_nat_le m; omega) (by omega)
  simpa [krefPowList, natList] using this


/-! ### A map over a list of numbers with a context of two numbers -/

/-- On `[[L, a], x]`: call the map at `md` on `[[a, x], L]`. -/
def krefOuterF (md : ℕ) : Expr :=
  .call md (mk2 (mk2 (.get (arg 0) (.nat 1)) (arg 1)) (.get (arg 0) (.nat 0)))

/-- The outer function, the map and its body `E` (five functions). -/
def krefOuterFuns (b : ℕ) (E : Expr) : List Expr :=
  [krefOuterF (b + 1)] ++ mapFuns (b + 1) (b + 4) ++ [E]

def krefOuterK (K : ℕ) : ℕ := 2 * (mapK * (3 * K + 11) * 15 ^ 3) + 400

theorem natList_wt_eq (L : List ℕ) : (Val.list (L.map Val.nat)).wt = (natList L).wt := rfl

/-- **The outer map.** -/
theorem kref_outer {P : Program} {b : ℕ} {E : Expr} (h : P.HasAt b (krefOuterFuns b E))
    {L : List ℕ} {a x Z K : ℕ} {g : ℕ → ℕ}
    (hE : ∀ p ∈ L, FunDet P (b + 4) (.list [.list [.nat a, .nat x], .nat p]) (.nat (g p))
      (K * (Z + 1) ^ 1))
    (ha : a ≤ Z) (hx : x ≤ Z) (hwL : (natList L).wt ≤ Z) :
    FunDet P b (.list [.list [natList L, .nat a], .nat x]) (natList (L.map g))
      (krefOuterK K * (Z + 1) ^ 3) := by
  have hf : P.funs[b]? = some (krefOuterF (b + 1)) := h.left.left.single
  have hmap : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.left.right
  have hc : (Val.list [.nat a, .nat x]).wt ≤ 14 * (Z + 1) := by
    have := wt_list2_le (.nat a) (.nat x); have := wt_nat_le a; have := wt_nat_le x; omega
  have hm := kref_mapL hmap (l := L) (enc := Val.nat) (F := fun p => .nat (g p)) (A := 14)
    (by norm_num) (fun p _ p' _ hpp => by cases hpp; rfl) hE hc (by rw [natList_wt_eq]; omega)
  have e1 : Val.list (L.map Val.nat) = natList L := rfl
  have e2 : Val.list (L.map fun p => Val.nat (g p)) = natList (L.map g) := by
    simp [natList, List.map_map, Function.comp_def]
  rw [e1, e2] at hm
  have hm' : FunDet P (b + 1) (.list [.list [.nat a, .nat x], natList L]) (natList (L.map g))
      (mapK * (3 * K + 11) * 15 ^ 3 * (Z + 1) ^ 3) := hm
  have hWA : (Val.list [.list [natList L, .nat a], .nat x]).wt ≤ 10 * Z + 30 := by
    have := wt_list2_le (.list [natList L, .nat a]) (.nat x)
    have := wt_list2_le (natList L) (.nat a)
    have := wt_nat_le a; have := wt_nat_le x; omega
  set A : List Val := [.list [natList L, .nat a], .nat x] with hA
  have d1 : Det P [.list A] (.get (arg 0) (.nat 1)) (.nat a) (3 * (Val.list A).wt + 0 + 1 + 9) :=
    Det.arg2 rfl rfl
  have d2 : Det P [.list A] (arg 1) (.nat x) (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
  have d3 : Det P [.list A] (.get (arg 0) (.nat 0)) (natList L)
      (3 * (Val.list A).wt + 0 + 0 + 9) := Det.arg2 rfl rfl
  have hl := Det.mk2 (Det.mk2 d1 d2) d3
  refine FunDet.intro hf ((Det.call hl hm').mono ?_)
  have hw := FunDet.wt_lt hm'
  have h3 : (Val.list [.list [.nat a, .nat x], natList L]).wt ≤ 2 * (14 * (Z + 1) + Z) + 6 := by
    have := wt_list2_le (.list [.nat a, .nat x]) (natList L); omega
  have hT : Z + 1 ≤ (Z + 1) ^ 3 := kref_le_pow (by norm_num)
  unfold krefOuterK
  rw [Nat.add_mul, Nat.mul_assoc 2]
  omega

/-! ### Digits -/

/-- On `[[base, x], p]`: `x / p % base`. -/
def krefDigE : Expr :=
  .arith .mod (.arith .div (.get (arg 0) (.nat 1)) (arg 1)) (.get (arg 0) (.nat 0))

theorem kref_digE {P : Program} {g : ℕ} (hg : P.funs[g]? = some krefDigE) {base x p Z : ℕ}
    (hb : base ≤ Z) (hx : x ≤ Z) (hp : p ≤ Z) :
    FunDet P g (.list [.list [.nat base, .nat x], .nat p]) (.nat (x / p % base))
      (400 * (Z + 1) ^ 1) := by
  have hWA : (Val.list [.list [.nat base, .nat x], .nat p]).wt ≤ 10 * Z + 40 := by
    have := wt_list2_le (.list [.nat base, .nat x]) (.nat p)
    have := wt_list2_le (.nat base) (.nat x)
    have := wt_nat_le base; have := wt_nat_le x; have := wt_nat_le p; omega
  set A : List Val := [.list [.nat base, .nat x], .nat p] with hA
  have d1 : Det P [.list A] (.get (arg 0) (.nat 1)) (.nat x) (3 * (Val.list A).wt + 0 + 1 + 9) :=
    Det.arg2 rfl rfl
  have d2 : Det P [.list A] (arg 1) (.nat p) (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
  have d3 : Det P [.list A] (.get (arg 0) (.nat 0)) (.nat base)
      (3 * (Val.list A).wt + 0 + 0 + 9) := Det.arg2 rfl rfl
  have hdiv := Det.arith' (op := .div) d1 d2 (z := x / p) rfl
  have hmod := Det.arith' (op := .mod) hdiv d3 (z := x / p % base) rfl
  refine FunDet.intro hg (hmod.mono ?_)
  have := Nat.div_le_self x p
  have := Nat.mod_le (x / p) base
  simp only [pow_one]
  omega

/-- The digit module: `krefOuterFuns` with body `krefDigE`. -/
def krefDigFuns (b : ℕ) : List Expr := krefOuterFuns b krefDigE

def krefDigK : ℕ := krefOuterK 400

/-- **Digits.** On `[[pw, base], x]`, the list of `x / p % base` for `p` in `pw`. -/
theorem kref_dig {P : Program} {b : ℕ} (h : P.HasAt b (krefDigFuns b)) {pw : List ℕ}
    {base x Z : ℕ} (hpw : ∀ p ∈ pw, p ≤ Z) (hb : base ≤ Z) (hx : x ≤ Z)
    (hwpw : (natList pw).wt ≤ Z) :
    FunDet P b (.list [.list [natList pw, .nat base], .nat x])
      (natList (pw.map fun p => x / p % base)) (krefDigK * (Z + 1) ^ 3) := by
  have hE : P.funs[b + 4]? = some krefDigE := by
    simpa [krefDigFuns, krefOuterFuns, mapFuns, loopFuns, Nat.add_assoc] using h.right.single
  exact kref_outer h (fun p hp => kref_digE hE hb hx (hpw p hp)) hb hx hwpw

/-! ### The maps that merge one entry into a new last point -/

/-- On `[[kk, i], r]`: `kk` if `r = i`, else `r`. -/
def krefRhoE : Expr :=
  .ite (.arith .eq (arg 1) (.get (arg 0) (.nat 1))) (.get (arg 0) (.nat 0)) (arg 1)

theorem kref_rhoE {P : Program} {g : ℕ} (hg : P.funs[g]? = some krefRhoE) {kk i r Z : ℕ}
    (hk : kk ≤ Z) (hi : i ≤ Z) (hr : r ≤ Z) :
    FunDet P g (.list [.list [.nat kk, .nat i], .nat r]) (.nat (if r = i then kk else r))
      (400 * (Z + 1) ^ 1) := by
  have hWA : (Val.list [.list [.nat kk, .nat i], .nat r]).wt ≤ 10 * Z + 40 := by
    have := wt_list2_le (.list [.nat kk, .nat i]) (.nat r)
    have := wt_list2_le (.nat kk) (.nat i)
    have := wt_nat_le kk; have := wt_nat_le i; have := wt_nat_le r; omega
  set A : List Val := [.list [.nat kk, .nat i], .nat r] with hA
  have d1 : Det P [.list A] (.get (arg 0) (.nat 1)) (.nat i) (3 * (Val.list A).wt + 0 + 1 + 9) :=
    Det.arg2 rfl rfl
  have d2 : Det P [.list A] (arg 1) (.nat r) (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
  have d3 : Det P [.list A] (.get (arg 0) (.nat 0)) (.nat kk)
      (3 * (Val.list A).wt + 0 + 0 + 9) := Det.arg2 rfl rfl
  have heq := Det.arith' (op := .eq) d2 d1 (z := if r = i then 1 else 0) rfl
  have hv : (Val.nat (if r = i then kk else r)).wt ≤ Z + 2 := by
    have h1 : (if r = i then kk else r) ≤ Z := by split_ifs <;> omega
    have := wt_nat_le (if r = i then kk else r); omega
  refine FunDet.intro hg ((Det.ite heq (v := .nat (if r = i then kk else r))
    (ct := 3 * (Val.list A).wt + 0 + 0 + 9) (ce := 2 * (Val.list A).wt + 1 + 5)
    (fun h1 => ?_) (fun h1 => ?_)).mono ?_)
  · have : r = i := by by_contra hne; simp [hne] at h1
    rw [if_pos this]; exact d3
  · have : r ≠ i := by intro hre; simp [hre] at h1
    rw [if_neg this]; exact d2
  · have : (if r = i then 1 else 0) ≤ 1 := by split_ifs <;> omega
    simp only [pow_one]
    omega

def krefRhoFuns (b : ℕ) : List Expr := krefOuterFuns b krefRhoE

def krefRhoK : ℕ := krefOuterK 400

/-- **The merge maps.** On `[[L, kk], i]`, the list of `kk` if `r = i`, else `r`, over `r ∈ L`. -/
theorem kref_rho {P : Program} {b : ℕ} (h : P.HasAt b (krefRhoFuns b)) {L : List ℕ}
    {kk i Z : ℕ} (hL : ∀ r ∈ L, r ≤ Z) (hk : kk ≤ Z) (hi : i ≤ Z) (hwL : (natList L).wt ≤ Z) :
    FunDet P b (.list [.list [natList L, .nat kk], .nat i])
      (natList (L.map fun r => if r = i then kk else r)) (krefRhoK * (Z + 1) ^ 3) := by
  have hE : P.funs[b + 4]? = some krefRhoE := by
    simpa [krefRhoFuns, krefOuterFuns, mapFuns, loopFuns, Nat.add_assoc] using h.right.single
  exact kref_outer h (fun r hr => kref_rhoE hE hk hi (hL r hr)) hk hi hwL

end GI.Lang
