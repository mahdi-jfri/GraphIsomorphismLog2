module

public import Workspace.Impl.KRefPows

@[expose] public section

/-!
# Indices of modified tuples, and equality patterns

* `krefCodesFuns b` (eight functions): on `[[pw, E], Ρ]`, for each list `ρ` of `Ρ` the number
  `∑ r < |pw|, E[ρ[r]] * pw[r]`. With `pw` the powers of `n` and `E` the entries of a tuple
  followed by one more point, this is the index of the tuple `r ↦ E[ρ[r]]`.
* `krefPatFuns b` (eight functions): on `[D, D]`, for each entry of `D` the first position of
  that entry.
-/

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

theorem natList_inj {a b : List ℕ} (h : natList a = natList b) : a = b := by
  unfold natList at h
  injection h with h
  exact List.map_injective_iff.mpr (fun x y hxy => by injection hxy) h

theorem kref_natList_get {l : List ℕ} {r : ℕ} (h : r < l.length) :
    (l.map Val.nat)[r]? = some (.nat (l.getD r 0)) := by
  simp [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem length_natList_lt' (xs : List ℕ) : xs.length < (natList xs).wt := by
  have := length_lt_wt_list (xs.map Val.nat)
  simpa [natList] using this

theorem kref_getD_le {l : List ℕ} {Z : ℕ} (h : ∀ a ∈ l, a ≤ Z) (r : ℕ) : l.getD r 0 ≤ Z := by
  rw [List.getD_eq_getElem?_getD]
  cases hr : l[r]? with
  | none => simp
  | some a => simpa using h a (List.mem_of_getElem? hr)

/-! ### Dot products through an index list -/

/-- `∑ r < i, E[ρ[r]] * pw[r]`. -/
def krefDot (pw E ρ : List ℕ) (i : ℕ) : ℕ :=
  ∑ r ∈ Finset.range i, E.getD (ρ.getD r 0) 0 * pw.getD r 0

theorem krefDot_mono (pw E ρ : List ℕ) {i j : ℕ} (h : i ≤ j) :
    krefDot pw E ρ i ≤ krefDot pw E ρ j :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- The step: `acc + E[ρ[r]] * pw[r]`. -/
def krefDotG : Expr :=
  .arith .add (arg 2) (.arith .mul (.get (.get (arg 0) (.nat 1)) (.get (.get (arg 0) (.nat 2))
    (arg 1))) (.get (.get (arg 0) (.nat 0)) (arg 1)))

/-- Bounds for one list `ρ`. -/
structure KrefDotOK (Z : ℕ) (pw E ρ : List ℕ) : Prop where
  len : pw.length ≤ ρ.length
  lt : ∀ a ∈ ρ, a < E.length
  sum : krefDot pw E ρ pw.length ≤ Z
  wt : (natList ρ).wt ≤ Z

theorem kref_dotG {P : Program} {g : ℕ} (hg : P.funs[g]? = some krefDotG) {pw E ρ : List ℕ}
    {Z r : ℕ} (hpw : ∀ a ∈ pw, a ≤ Z) (hE : ∀ a ∈ E, a ≤ Z) (hρ : KrefDotOK Z pw E ρ)
    (hwpw : (natList pw).wt ≤ Z) (hwE : (natList E).wt ≤ Z) (hr : r < pw.length)
    (hpl : pw.length ≤ Z) :
    FunDet P g (.list [.list [natList pw, natList E, natList ρ], .nat r,
        .nat (krefDot pw E ρ r)]) (.nat (krefDot pw E ρ (r + 1))) (1000 * (Z + 1) ^ 1) := by
  have hrρ : r < ρ.length := lt_of_lt_of_le hr hρ.len
  have hρr : ρ.getD r 0 < E.length := hρ.lt _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrρ]; simp)
  have hsr : krefDot pw E ρ r ≤ Z := (krefDot_mono pw E ρ hr.le).trans hρ.sum
  have hs1 : krefDot pw E ρ (r + 1) ≤ Z := (krefDot_mono pw E ρ hr).trans hρ.sum
  have hsucc : krefDot pw E ρ (r + 1) =
      krefDot pw E ρ r + E.getD (ρ.getD r 0) 0 * pw.getD r 0 := Finset.sum_range_succ _ _
  have hc : (Val.list [natList pw, natList E, natList ρ]).wt ≤ 6 * Z + 7 := by
    have := wt_list3_le (natList pw) (natList E) (natList ρ); have := hρ.wt; omega
  have hWA : (Val.list [.list [natList pw, natList E, natList ρ], .nat r,
      .nat (krefDot pw E ρ r)]).wt ≤ 16 * Z + 30 := by
    have := wt_list3_le (.list [natList pw, natList E, natList ρ]) (.nat r)
      (.nat (krefDot pw E ρ r))
    have := wt_nat_le r; have := wt_nat_le (krefDot pw E ρ r); omega
  set A : List Val := [.list [natList pw, natList E, natList ρ], .nat r,
      .nat (krefDot pw E ρ r)] with hA
  have dρ : Det P [.list A] (.get (arg 0) (.nat 2)) (natList ρ) (3 * (Val.list A).wt + 0 + 2 + 9) :=
    Det.arg2 rfl rfl
  have dE : Det P [.list A] (.get (arg 0) (.nat 1)) (natList E) (3 * (Val.list A).wt + 0 + 1 + 9) :=
    Det.arg2 rfl rfl
  have dpw : Det P [.list A] (.get (arg 0) (.nat 0)) (natList pw)
      (3 * (Val.list A).wt + 0 + 0 + 9) := Det.arg2 rfl rfl
  have dr : Det P [.list A] (arg 1) (.nat r) (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
  have ds : Det P [.list A] (arg 2) (.nat (krefDot pw E ρ r)) (2 * (Val.list A).wt + 2 + 5) :=
    Det.arg' rfl
  have d1 := Det.get' dρ dr (kref_natList_get hrρ)
  have d2 := Det.get' dE d1 (kref_natList_get hρr)
  have d3 := Det.get' dpw dr (kref_natList_get hr)
  have d4 := Det.arith (op := .mul) d2 d3
  have d5 := Det.arith (op := .add) ds d4
  simp only [BinOp.eval] at d5
  rw [← hsucc] at d5
  refine FunDet.intro hg (d5.mono ?_)
  have hprod : E.getD (ρ.getD r 0) 0 * pw.getD r 0 ≤ Z := by omega
  have := wt_nat_le (E.getD (ρ.getD r 0) 0 * pw.getD r 0)
  have := wt_nat_le (krefDot pw E ρ (r + 1))
  have := wt_nat_le (ρ.getD r 0)
  have := wt_nat_le (E.getD (ρ.getD r 0) 0)
  have := wt_nat_le (pw.getD r 0)
  have := kref_getD_le hE (ρ.getD r 0)
  have := length_natList_lt' E
  have := kref_getD_le hpw r
  simp only [pow_one]
  omega

/-! ### The list of indices -/

/-- On `[[pw, E], ρ]`: run the dot loop at `id` on `[[pw, E, ρ], |pw|, 0]`. -/
def krefCodeF (id : ℕ) : Expr :=
  .call id (mk3 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))
    (.length (.get (arg 0) (.nat 0))) (.nat 0))

/-- `codes`, at base `b` (eight functions). -/
def krefCodesFuns (b : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ [krefCodeF (b + 4)] ++ iterFuns (b + 4) (b + 7) ++ [krefDotG]

def krefCodeK : ℕ := 3 * (loopModK * 1020 * 8 ^ 3) + 1000

def krefCodesK : ℕ := mapK * (3 * krefCodeK + 11) * 7 ^ 5

/-- Bounds for `codes`. -/
structure KrefCodesOK (Z : ℕ) (pw E : List ℕ) (Ρ : List (List ℕ)) : Prop where
  hpw : ∀ a ∈ pw, a ≤ Z
  hE : ∀ a ∈ E, a ≤ Z
  hρ : ∀ ρ ∈ Ρ, KrefDotOK Z pw E ρ
  wpw : (natList pw).wt ≤ Z
  wE : (natList E).wt ≤ Z
  wΡ : (Val.list (Ρ.map natList)).wt ≤ Z
  lpw : pw.length ≤ Z

theorem kref_codeF {P : Program} {b : ℕ} (h : P.HasAt b (krefCodesFuns b)) {pw E ρ : List ℕ}
    {Z : ℕ} {Ρ : List (List ℕ)} (hok : KrefCodesOK Z pw E Ρ) (hρ : ρ ∈ Ρ) :
    FunDet P (b + 3) (.list [.list [natList pw, natList E], natList ρ])
      (.nat (krefDot pw E ρ pw.length)) (krefCodeK * (Z + 1) ^ 3) := by
  have hf : P.funs[b + 3]? = some (krefCodeF (b + 4)) := by
    simpa [krefCodesFuns, mapFuns, loopFuns] using h.left.left.right.single
  have hit : P.HasAt (b + 4) (iterFuns (b + 4) (b + 7)) := by
    simpa [krefCodesFuns, mapFuns, loopFuns, Nat.add_assoc] using h.left.right
  have hg : P.funs[b + 7]? = some krefDotG := by
    simpa [krefCodesFuns, mapFuns, loopFuns, iterFuns, Nat.add_assoc] using h.right.single
  have hok' := hok.hρ ρ hρ
  have hc : (Val.list [natList pw, natList E, natList ρ]).wt ≤ 7 * (Z + 1) := by
    have := wt_list3_le (natList pw) (natList E) (natList ρ); have := hok'.wt
    have := hok.wpw; have := hok.wE; omega
  have hloop := kref_iterA hit (c := .list [natList pw, natList E, natList ρ]) (n := pw.length)
    (accs := fun i => .nat (krefDot pw E ρ i)) (Y := Z) (K := 1000) (d := 1) (A := 7)
    (by norm_num) (fun i hi => kref_dotG hg hok.hpw hok.hE hok' hok.wpw hok.wE hi hok.lpw)
    (fun i hi => by
      show (Val.nat (krefDot pw E ρ i)).wt ≤ 7 * (Z + 1)
      have := wt_nat_le (krefDot pw E ρ i)
      have := (krefDot_mono pw E ρ hi).trans hok'.sum; omega) hc (by have := hok.lpw; omega)
  have e0 : krefDot pw E ρ 0 = 0 := by simp [krefDot]
  simp only [e0] at hloop
  have hloop' : FunDet P (b + 4) (.list [.list [natList pw, natList E, natList ρ],
      .nat pw.length, .nat 0]) (.nat (krefDot pw E ρ pw.length))
      (loopModK * 1020 * 8 ^ 3 * (Z + 1) ^ 3) := hloop
  have hWA : (Val.list [.list [natList pw, natList E], natList ρ]).wt ≤ 10 * Z + 20 := by
    have := wt_list2_le (.list [natList pw, natList E]) (natList ρ)
    have := wt_list2_le (natList pw) (natList E)
    have := hok'.wt; have := hok.wpw; have := hok.wE; omega
  set A : List Val := [.list [natList pw, natList E], natList ρ] with hA
  have dpw : Det P [.list A] (.get (arg 0) (.nat 0)) (natList pw)
      (3 * (Val.list A).wt + 0 + 0 + 9) := Det.arg2 rfl rfl
  have dE : Det P [.list A] (.get (arg 0) (.nat 1)) (natList E)
      (3 * (Val.list A).wt + 0 + 1 + 9) := Det.arg2 rfl rfl
  have dρ : Det P [.list A] (arg 1) (natList ρ) (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
  have dl := Det.length dpw
  have hlen : (pw.map Val.nat).length = pw.length := List.length_map _
  have dl' : Det P [.list A] (.length (.get (arg 0) (.nat 0))) (.nat pw.length)
      (3 * (Val.list A).wt + 0 + 0 + 9 + pw.length + 3) := by
    rw [← hlen]; exact dl
  have dargs := Det.mk3 (Det.mk3 dpw dE dρ) dl' (Det.nat 0)
  refine FunDet.intro hf ((Det.call dargs hloop').mono ?_)
  have hw := FunDet.wt_lt hloop'
  have h3 : (Val.list [.list [natList pw, natList E, natList ρ], .nat pw.length, .nat 0]).wt ≤
      30 * (Z + 1) := by
    have := wt_list3_le (.list [natList pw, natList E, natList ρ]) (.nat pw.length) (.nat 0)
    have := wt_nat_le pw.length; have := wt_nat_le 0; have := hok.lpw; omega
  have h3' : (Val.list [natList pw, natList E, natList ρ]).wt ≤ 7 * (Z + 1) := hc
  have hT : Z + 1 ≤ (Z + 1) ^ 3 := kref_le_pow (by norm_num)
  have := hok.lpw
  unfold krefCodeK
  rw [Nat.add_mul, Nat.mul_assoc 3]
  omega

/-- **Codes.** -/
theorem kref_codes {P : Program} {b : ℕ} (h : P.HasAt b (krefCodesFuns b)) {pw E : List ℕ}
    {Z : ℕ} {Ρ : List (List ℕ)} (hok : KrefCodesOK Z pw E Ρ) :
    FunDet P b (.list [.list [natList pw, natList E], .list (Ρ.map natList)])
      (natList (Ρ.map fun ρ => krefDot pw E ρ pw.length)) (krefCodesK * (Z + 1) ^ 5) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left.left.left
  have hc : (Val.list [natList pw, natList E]).wt ≤ 6 * (Z + 1) := by
    have := wt_list2_le (natList pw) (natList E); have := hok.wpw; have := hok.wE; omega
  have := kref_mapL hmap (l := Ρ) (enc := natList)
    (F := fun ρ => .nat (krefDot pw E ρ pw.length)) (Y := Z) (A := 6) (by norm_num)
    (fun a _ a' _ haa => by rw [natList_inj haa]) (fun ρ hρ => kref_codeF h hok hρ) hc
    (by have := hok.wΡ; omega)
  have e : Val.list (Ρ.map fun ρ => Val.nat (krefDot pw E ρ pw.length)) =
      natList (Ρ.map fun ρ => krefDot pw E ρ pw.length) := by
    simp [natList, List.map_map, Function.comp_def]
  rw [e] at this
  exact this

/-! ### Equality patterns -/

/-- On `[D, d]`: the first position of `d` in `D`. -/
def krefPatF (fe : ℕ) : Expr := .call fe (mk2 (arg 1) (arg 0))

/-- `pat`, at base `b` (eight functions). -/
def krefPatFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [krefPatF (b + 4)] ++ findEqFuns (b + 4)

def krefPatK : ℕ := mapK * (3 * (2 * (findEqK * 4 ^ 3) + 100) + 11) * 4 ^ 5

/-- **Equality patterns.** -/
theorem kref_pat {P : Program} {b : ℕ} (h : P.HasAt b (krefPatFuns b)) {D : List ℕ} {Z : ℕ}
    (hD : ∀ a ∈ D, a ≤ Z) (hl : D.length ≤ Z) (hw : (natList D).wt ≤ Z) :
    FunDet P b (.list [natList D, natList D])
      (natList (D.map fun a => D.findIdx fun y => decide (y = a))) (krefPatK * (Z + 1) ^ 5) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left.left
  have hf : P.funs[b + 3]? = some (krefPatF (b + 4)) := by
    simpa [krefPatFuns, mapFuns, loopFuns] using h.left.right.single
  have hfe : P.HasAt (b + 4) (findEqFuns (b + 4)) := by
    simpa [krefPatFuns, mapFuns, loopFuns, Nat.add_assoc] using h.right
  have hbody : ∀ a ∈ D, FunDet P (b + 3) (.list [natList D, .nat a])
      (.nat (D.findIdx fun y => decide (y = a))) ((2 * (findEqK * 4 ^ 3) + 100) * (Z + 1) ^ 3) := by
    intro a ha
    have hfind := findEq_spec hfe hD (hD a ha) hl
    have hWA : (Val.list [natList D, .nat a]).wt ≤ 4 * Z + 10 := by
      have := wt_list2_le (natList D) (.nat a); have := wt_nat_le a; have := hD a ha; omega
    have d := Det.mk2 (Det.arg' (vs := [natList D, .nat a]) (rest := []) (j := 1) (P := P) rfl)
      (Det.arg' (vs := [natList D, .nat a]) (rest := []) (j := 0) rfl)
    refine FunDet.intro hf ((Det.call d hfind).mono ?_)
    have hw' := FunDet.wt_lt hfind
    have h2 : (Val.list [.nat a, natList D]).wt ≤ 4 * Z + 10 := by
      have := wt_list2_le (.nat a) (natList D); have := wt_nat_le a; have := hD a ha; omega
    have hT : Z + 1 ≤ (Z + 1) ^ 3 := kref_le_pow (by norm_num)
    have e1 : findEqK * (Z + 1) ^ 3 ≤ findEqK * 4 ^ 3 * (Z + 1) ^ 3 :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by norm_num))
    rw [Nat.add_mul, Nat.mul_assoc 2]
    omega
  have := kref_mapL hmap (l := D) (enc := Val.nat)
    (F := fun a => .nat (D.findIdx fun y => decide (y = a))) (Y := Z) (A := 3) (by norm_num)
    (fun a _ a' _ haa => by cases haa; rfl) hbody (by omega) (by rw [natList_wt_eq]; omega)
  have e : Val.list (D.map fun a => Val.nat (D.findIdx fun y => decide (y = a))) =
      natList (D.map fun a => D.findIdx fun y => decide (y = a)) := by
    simp [natList, List.map_map, Function.comp_def]
  rw [e] at this
  exact this

end GI.Lang
