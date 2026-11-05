module

public import Workspace.Impl.JohnD

@[expose] public section

/-!
# The sets `B(x, y)` and `C(x, y)` as programs

`johnCompCF` computes `natList (johnC n labL δ x y)` from `[D, Rn, x, y]` (`john_compC_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ} {labL : List ℕ} {δ : ℕ}

theorem john_DV_get {x : ℕ} (hx : x < n) :
    ((List.range n).map fun x => natList (johnDRow n labL δ x))[x]? =
      some (natList (johnDRow n labL δ x)) := by
  simp [hx]

theorem john_DRow_get {x z : ℕ} (hz : z < n) :
    ((johnDRow n labL δ x).map Val.nat)[z]? = some (.nat (johnD n labL δ x z).toNat) := by
  simp [johnDRow, hz]

/-- `if` on a known number, with the costs of both branches added. -/
theorem john_det_ite {P : Program} {env : List Val} {c t e : Expr} {x : ℕ} {v1 v0 : Val}
    {cc ct ce : ℕ} (hc : Det P env c (.nat x) cc) (ht : Det P env t v1 ct)
    (he : Det P env e v0 ce) :
    Det P env (.ite c t e) (if x = 0 then v0 else v1) (cc + ct + ce + v1.wt + v0.wt + 1) :=
  (Det.ite' hc ht he).mono (by
    have := max_le (le_add_right (le_refl ct) : ct ≤ ct + ce) (le_add_left (le_refl ce))
    have := max_le (le_add_right (le_refl v1.wt) : v1.wt ≤ v1.wt + v0.wt)
      (le_add_left (le_refl v0.wt))
    omega)

/-- Reading the entry `(x, z)` of `D`. -/
theorem john_det_DE {P : Program} {env : List Val} {eD eX eZ : Expr} {x z cD cX cZ : ℕ}
    (hD : Det P env eD (johnDV n labL δ) cD) (hX : Det P env eX (.nat x) cX)
    (hZ : Det P env eZ (.nat z) cZ) (hx : x < n) (hz : z < n) :
    Det P env (.get (.get eD eX) eZ) (.nat (johnD n labL δ x z).toNat)
      (cD + cX + cZ + (johnDV n labL δ).wt + 5) := by
  have h1 := Det.get' hD hX (john_DV_get hx)
  have h2 := Det.get' h1 hZ (john_DRow_get (labL := labL) (δ := δ) (x := x) hz)
  refine h2.mono ?_
  have : (natList (johnDRow n labL δ x)).wt < (johnDV n labL δ).wt :=
    wt_le_wt_list (List.mem_of_getElem? (john_DV_get hx))
  have : (Val.nat (johnD n labL δ x z).toNat).wt ≤ 3 := wt_boolVal_le _
  omega

/-- The test of `B(x, y)` on values. -/
def johnQB (n : ℕ) (labL : List ℕ) (δ x y : ℕ) : Val → Bool
  | .nat z => !johnD n labL δ x z && johnD n labL δ y z
  | .list _ => false

/-- The test of `johnCF` on values. -/
def johnQA (n : ℕ) (labL : List ℕ) (δ r : ℕ) : Val → Bool
  | .nat z => !johnD n labL δ z r
  | .list _ => false

theorem john_ctx_wt3 (a b c : Val) {A : ℕ} (ha : a.wt ≤ A) (hb : b.wt ≤ A) (hc : c.wt ≤ A) :
    (Val.list [a, b, c]).wt ≤ 6 * A + 7 := by
  have := wt_list3_le a b c; omega

/-- **The test of `B(x, y)`.** -/
theorem john_bF_spec {x y z : ℕ} (hx : x < n) (hy : y < n) (hz : z < n) :
    FunDet johnProgram 82 (.list [.list [johnDV n labL δ, .nat x, .nat y], .nat z])
      (boolVal (johnQB n labL δ x y (.nat z))) (2000 * (n + 1) ^ 2) := by
  set c := Val.list [johnDV n labL δ, .nat x, .nat y]
  set a := Val.list [c, .nat z]
  have hc : Det johnProgram [a] (arg 0) c (2 * a.wt + 5) := Det.arg' rfl
  have hD := Det.get' hc (Det.nat 0)
    (show [johnDV n labL δ, Val.nat x, .nat y][0]? = some (johnDV n labL δ) from rfl)
  have hX := Det.get' hc (Det.nat 1)
    (show [johnDV n labL δ, Val.nat x, .nat y][1]? = some (.nat x) from rfl)
  have hY := Det.get' hc (Det.nat 2)
    (show [johnDV n labL δ, Val.nat x, .nat y][2]? = some (.nat y) from rfl)
  have hZ : Det johnProgram [a] (arg 1) (.nat z) (2 * a.wt + 6) := Det.arg' rfl
  have h := john_det_ite (john_det_DE hD hX hZ hx hz) (Det.nat 0) (john_det_DE hD hY hZ hy hz)
  have hv : (if (johnD n labL δ x z).toNat = 0 then Val.nat (johnD n labL δ y z).toNat
      else Val.nat 0) = boolVal (johnQB n labL δ x y (.nat z)) := by
    simp only [johnQB]
    cases johnD n labL δ x z <;> cases johnD n labL δ y z <;> rfl
  rw [hv] at h
  refine FunDet.intro john_at_bF.single (h.mono ?_)
  have wD := john_wt_DV n labL δ
  have e1 := wt_list3_le (johnDV n labL δ) (.nat x) (.nat y)
  have e2 := wt_list2_le c (.nat z)
  have ec : c.wt = (Val.list [johnDV n labL δ, .nat x, .nat y]).wt := rfl
  have ea : a.wt = (Val.list [c, .nat z]).wt := rfl
  have w1 := wt_nat_le x; have w2 := wt_nat_le y; have w3 := wt_nat_le z
  have w4 := wt_nat_le 0; have w5 := wt_nat_le 1; have w6 := wt_nat_le 2
  have w7 : (Val.nat (johnD n labL δ x z).toNat).wt ≤ 3 := wt_boolVal_le _
  have w8 : (Val.nat (johnD n labL δ y z).toNat).wt ≤ 3 := wt_boolVal_le _
  have w9 : (Val.nat (johnQB n labL δ x y (.nat z)).toNat).wt ≤ 3 := wt_boolVal_le _
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  omega

/-- **The set `B(x, y)`.** -/
theorem john_B_spec {x y : ℕ} (hx : x < n) (hy : y < n) :
    FunDet johnProgram 79
      (.list [.list [johnDV n labL δ, .nat x, .nat y], natList (List.range n)])
      (natList (johnB n labL δ x y)) (1000000 * (n + 1) ^ 3) := by
  have hF := filter_spec john_at_filterB (c := .list [johnDV n labL δ, .nat x, .nat y])
    (xs := (List.range n).map Val.nat) (q := johnQB n labL δ x y)
    (B := fun _ => 2000 * (n + 1) ^ 2) (by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
      exact john_bF_spec hx hy (List.mem_range.mp hz))
  have e : Val.list (((List.range n).map Val.nat).filter (johnQB n labL δ x y)) =
      natList (johnB n labL δ x y) := by
    simp only [natList, johnB, List.filter_map]
    rfl
  refine hF.mono ?_
  rintro w cost ⟨rfl, hc⟩
  refine ⟨e, hc.trans ?_⟩
  rw [e]
  -- The bound.
  have hsum := john_sum_le (l := (List.range n).map Val.nat)
    (f := fun _ => 2000 * (n + 1) ^ 2) (B := 2000 * (n + 1) ^ 2) fun _ _ => le_rfl
  simp only [List.length_map, List.length_range] at hsum
  have wD := john_wt_DV n labL δ
  have wR := john_wt_Rn n
  have wB : (natList (johnB n labL δ x y)).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (fun v hv => by
        simp only [johnB, List.mem_filter, List.mem_range] at hv; omega)
      (by simp only [johnB]; exact (List.length_filter_le _ _).trans (by simp))
  have e1 := wt_list3_le (johnDV n labL δ) (.nat x) (.nat y)
  have e2 := wt_list2_le (.list [johnDV n labL δ, .nat x, .nat y]) (natList (List.range n))
  have hRn : natList (List.range n) = Val.list ((List.range n).map Val.nat) := rfl
  rw [hRn] at e2 wR
  have w1 := wt_nat_le x; have w2 := wt_nat_le y
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  set A := (Val.list [.list [johnDV n labL δ, .nat x, .nat y],
    .list ((List.range n).map Val.nat)]).wt
  have hA : A + n + (natList (johnB n labL δ x y)).wt + 1 ≤ 200 * (n + 1) ^ 2 := by omega
  have p1 : n * (2000 * (n + 1) ^ 2) ≤ 2000 * (n + 1) ^ 3 := by
    calc n * (2000 * (n + 1) ^ 2) ≤ (n + 1) * (2000 * (n + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2000 * (n + 1) ^ 3 := by ring
  have p2 : loopModK * (n + 1) * (A + n + (natList (johnB n labL δ x y)).wt + 1) ≤
      1000 * (200 * (n + 1) ^ 3) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (n + 1) * (A + n + (natList (johnB n labL δ x y)).wt + 1) ≤
        (n + 1) * (200 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ hA
      _ = 200 * (n + 1) ^ 3 := by ring
  simp only [List.length_map, List.length_range]
  omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ} {labL : List ℕ} {δ : ℕ}

theorem john_B_lt {x y z : ℕ} (hz : z ∈ johnB n labL δ x y) : z < n := by
  simp only [johnB, List.mem_filter, List.mem_range] at hz; exact hz.1

theorem john_wt_B (x y : ℕ) : (natList (johnB n labL δ x y)).wt ≤ 5 * (n + 1) ^ 2 :=
  wt_natList_le_sq (fun v hv => (john_B_lt hv).le)
    (by simp only [johnB]; exact (List.length_filter_le _ _).trans (by simp))

/-- **The test of `johnCF`.** -/
theorem john_aF_spec {r z : ℕ} (hr : r < n) (hz : z < n) :
    FunDet johnProgram 90 (.list [.list [johnDV n labL δ, .nat r], .nat z])
      (boolVal (johnQA n labL δ r (.nat z))) (2000 * (n + 1) ^ 2) := by
  set c := Val.list [johnDV n labL δ, .nat r]
  set a := Val.list [c, .nat z]
  have hc : Det johnProgram [a] (arg 0) c (2 * a.wt + 5) := Det.arg' rfl
  have hD := Det.get' hc (Det.nat 0)
    (show [johnDV n labL δ, Val.nat r][0]? = some (johnDV n labL δ) from rfl)
  have hR := Det.get' hc (Det.nat 1)
    (show [johnDV n labL δ, Val.nat r][1]? = some (.nat r) from rfl)
  have hZ : Det johnProgram [a] (arg 1) (.nat z) (2 * a.wt + 6) := Det.arg' rfl
  have h := Det.arith (op := .sub) (Det.nat 1) (john_det_DE hD hZ hR hz hr)
  have hv : BinOp.eval .sub 1 (johnD n labL δ z r).toNat = (johnQA n labL δ r (.nat z)).toNat := by
    simp only [johnQA, BinOp.eval]
    cases johnD n labL δ z r <;> rfl
  rw [hv] at h
  refine FunDet.intro john_at_aF.single (h.mono ?_)
  have wD := john_wt_DV n labL δ
  have e1 := wt_list2_le (johnDV n labL δ) (.nat r)
  have e2 := wt_list2_le c (.nat z)
  have ec : c.wt = (Val.list [johnDV n labL δ, .nat r]).wt := rfl
  have ea : a.wt = (Val.list [c, .nat z]).wt := rfl
  have w1 := wt_nat_le r; have w3 := wt_nat_le z
  have w4 := wt_nat_le 0; have w5 := wt_nat_le 1
  have w9 : (Val.nat (johnQA n labL δ r (.nat z)).toNat).wt ≤ 3 := wt_boolVal_le _
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  omega

/-- **An entry of `C(x, y)`, by `all`.** -/
theorem john_allA_spec {x y r : ℕ} (hr : r < n) :
    FunDet johnProgram 87
      (.list [.list [johnDV n labL δ, .nat r], natList (johnB n labL δ x y)])
      (.nat ((johnB n labL δ x y).all fun z => !johnD n labL δ z r).toNat)
      (300000 * (n + 1) ^ 3) := by
  have hA := all_spec john_at_allA (c := .list [johnDV n labL δ, .nat r])
    (xs := (johnB n labL δ x y).map Val.nat) (q := johnQA n labL δ r)
    (B := fun _ => 2000 * (n + 1) ^ 2) (by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
      exact john_aF_spec hr (john_B_lt hz))
  have e : ((johnB n labL δ x y).map Val.nat).all (johnQA n labL δ r) =
      (johnB n labL δ x y).all fun z => !johnD n labL δ z r := by
    rw [List.all_map]; rfl
  refine hA.mono ?_
  rintro w cost ⟨rfl, hc⟩
  refine ⟨by rw [e], hc.trans ?_⟩
  have hl : (johnB n labL δ x y).length ≤ n :=
    (List.length_filter_le _ _).trans (by simp)
  have hsum := john_sum_le (l := (johnB n labL δ x y).map Val.nat)
    (f := fun _ => 2000 * (n + 1) ^ 2) (B := 2000 * (n + 1) ^ 2) fun _ _ => le_rfl
  simp only [List.length_map] at hsum ⊢
  have wD := john_wt_DV n labL δ
  have wB := john_wt_B (n := n) (labL := labL) (δ := δ) x y
  have hBv : natList (johnB n labL δ x y) = Val.list ((johnB n labL δ x y).map Val.nat) := rfl
  rw [hBv] at wB
  have e1 := wt_list2_le (johnDV n labL δ) (.nat r)
  have e2 := wt_list2_le (.list [johnDV n labL δ, .nat r])
    (.list ((johnB n labL δ x y).map Val.nat))
  have w1 := wt_nat_le r
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  set A := (Val.list [.list [johnDV n labL δ, .nat r],
    .list ((johnB n labL δ x y).map Val.nat)]).wt
  have hA' : A + (johnB n labL δ x y).length + 4 ≤ 200 * (n + 1) ^ 2 := by omega
  have p1 : (johnB n labL δ x y).length * (2000 * (n + 1) ^ 2) ≤ 2000 * (n + 1) ^ 3 := by
    calc (johnB n labL δ x y).length * (2000 * (n + 1) ^ 2) ≤ (n + 1) * (2000 * (n + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2000 * (n + 1) ^ 3 := by ring
  have p2 : loopModK * ((johnB n labL δ x y).length + 1) *
      (A + (johnB n labL δ x y).length + 4) ≤ 1000 * (200 * (n + 1) ^ 3) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc ((johnB n labL δ x y).length + 1) * (A + (johnB n labL δ x y).length + 4) ≤
        (n + 1) * (200 * (n + 1) ^ 2) := Nat.mul_le_mul (by omega) hA'
      _ = 200 * (n + 1) ^ 3 := by ring
  omega

/-- **An entry of `C(x, y)`, as the function `johnCF`.** -/
theorem john_cF_spec {x y r : ℕ} (hr : r < n) :
    FunDet johnProgram 86
      (.list [.list [johnDV n labL δ, natList (johnB n labL δ x y)], .nat r])
      (.nat ((johnB n labL δ x y).all fun z => !johnD n labL δ z r).toNat)
      (400000 * (n + 1) ^ 3) := by
  set c := Val.list [johnDV n labL δ, natList (johnB n labL δ x y)]
  set a := Val.list [c, .nat r]
  have hc : Det johnProgram [a] (arg 0) c (2 * a.wt + 5) := Det.arg' rfl
  have hD := Det.get' hc (Det.nat 0)
    (show [johnDV n labL δ, natList (johnB n labL δ x y)][0]? = some (johnDV n labL δ) from rfl)
  have hB := Det.get' hc (Det.nat 1)
    (show [johnDV n labL δ, natList (johnB n labL δ x y)][1]? =
      some (natList (johnB n labL δ x y)) from rfl)
  have hR : Det johnProgram [a] (arg 1) (.nat r) (2 * a.wt + 6) := Det.arg' rfl
  have hcall := Det.call (Det.mk2 (Det.mk2 hD hR) hB) (john_allA_spec (x := x) (y := y) hr)
  refine FunDet.intro john_at_cF.single (hcall.mono ?_)
  have wD := john_wt_DV n labL δ
  have wB := john_wt_B (n := n) (labL := labL) (δ := δ) x y
  have e1 := wt_list2_le (johnDV n labL δ) (natList (johnB n labL δ x y))
  have e2 := wt_list2_le c (.nat r)
  have e3 := wt_list2_le (johnDV n labL δ) (.nat r)
  have e4 := wt_list2_le (.list [johnDV n labL δ, .nat r]) (natList (johnB n labL δ x y))
  have ec : c.wt = (Val.list [johnDV n labL δ, natList (johnB n labL δ x y)]).wt := rfl
  have ea : a.wt = (Val.list [c, .nat r]).wt := rfl
  have w1 := wt_nat_le r; have w4 := wt_nat_le 0; have w5 := wt_nat_le 1
  have w9 : (Val.nat ((johnB n labL δ x y).all fun z => !johnD n labL δ z r).toNat).wt ≤ 3 :=
    wt_boolVal_le _
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have y23 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := john_pow_le (by omega) (by omega)
  omega

theorem john_wt_C (x y : ℕ) : (natList (johnC n labL δ x y)).wt ≤ 7 * n + 4 := by
  have := john_wt_bits (xs := johnC n labL δ x y) (by
    intro v hv; simp only [johnC, List.mem_map] at hv
    obtain ⟨r, -, rfl⟩ := hv; exact Bool.toNat_le _)
  simp only [johnC, List.length_map, List.length_range] at this
  unfold johnC
  omega

/-- **The set `C(x, y)` from `B(x, y)`.** -/
theorem john_mapC_spec (x y : ℕ) :
    FunDet johnProgram 83
      (.list [.list [johnDV n labL δ, natList (johnB n labL δ x y)], natList (List.range n)])
      (natList (johnC n labL δ x y)) (1000000 * (n + 1) ^ 4) := by
  have hT := john_tab john_at_mapC (c := .list [johnDV n labL δ, natList (johnB n labL δ x y)])
    (n := n) (B := 400000 * (n + 1) ^ 3)
    (G := fun r => .nat ((johnB n labL δ x y).all fun z => !johnD n labL δ z r).toNat)
    fun r hr => john_cF_spec hr
  have e : Val.list ((List.range n).map fun r =>
      Val.nat ((johnB n labL δ x y).all fun z => !johnD n labL δ z r).toNat) =
      natList (johnC n labL δ x y) := by
    simp [natList, johnC, List.map_map, Function.comp_def]
  rw [e] at hT
  refine hT.mono ?_
  have wD := john_wt_DV n labL δ
  have wB := john_wt_B (n := n) (labL := labL) (δ := δ) x y
  have wR := john_wt_Rn n
  have wC := john_wt_C (n := n) (labL := labL) (δ := δ) x y
  have e1 := wt_list2_le (johnDV n labL δ) (natList (johnB n labL δ x y))
  have e2 := wt_list2_le (.list [johnDV n labL δ, natList (johnB n labL δ x y)])
    (natList (List.range n))
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  set A := (Val.list [.list [johnDV n labL δ, natList (johnB n labL δ x y)],
    natList (List.range n)]).wt
  have hA : A + (natList (johnC n labL δ x y)).wt + 1 ≤ 200 * (n + 1) ^ 2 := by omega
  have p1 : n * (400000 * (n + 1) ^ 3) ≤ 400000 * (n + 1) ^ 4 := by
    calc n * (400000 * (n + 1) ^ 3) ≤ (n + 1) * (400000 * (n + 1) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 400000 * (n + 1) ^ 4 := by ring
  have p2 : mapK * (n + 1) * (A + (natList (johnC n labL δ x y)).wt + 1) ≤
      1000 * (200 * (n + 1) ^ 3) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (n + 1) * (A + (natList (johnC n labL δ x y)).wt + 1) ≤ (n + 1) * (200 * (n + 1) ^ 2) :=
          Nat.mul_le_mul_left _ hA
      _ = 200 * (n + 1) ^ 3 := by ring
  have y34 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := john_pow_le (by omega) (by omega)
  omega

/-- **The set `C(x, y)`.** -/
theorem john_compC_spec {x y : ℕ} (hx : x < n) (hy : y < n) :
    FunDet johnProgram 78
      (.list [johnDV n labL δ, natList (List.range n), .nat x, .nat y])
      (natList (johnC n labL δ x y)) (3000000 * (n + 1) ^ 4) := by
  set a := Val.list [johnDV n labL δ, natList (List.range n), .nat x, .nat y]
  have hD : Det johnProgram [a] (arg 0) (johnDV n labL δ) (2 * a.wt + 5) := Det.arg' rfl
  have hR : Det johnProgram [a] (arg 1) (natList (List.range n)) (2 * a.wt + 6) := Det.arg' rfl
  have hX : Det johnProgram [a] (arg 2) (.nat x) (2 * a.wt + 7) := Det.arg' rfl
  have hY : Det johnProgram [a] (arg 3) (.nat y) (2 * a.wt + 8) := Det.arg' rfl
  have hB := Det.call (Det.mk2 (Det.mk3 hD hX hY) hR) (john_B_spec (labL := labL) (δ := δ) hx hy)
  set Bv := natList (johnB n labL δ x y)
  have hD' : Det johnProgram [a, Bv] (arg 0) (johnDV n labL δ) (2 * a.wt + 5) := Det.arg' rfl
  have hR' : Det johnProgram [a, Bv] (arg 1) (natList (List.range n)) (2 * a.wt + 6) :=
    Det.arg' rfl
  have hBv : Det johnProgram [a, Bv] (.var 1) Bv (Bv.wt + 1) := Det.var' rfl
  have hC := Det.call (Det.mk2 (Det.mk2 hD' hBv) hR') (john_mapC_spec (labL := labL) (δ := δ) x y)
  refine FunDet.intro john_at_compCF.single ((Det.letE hB hC).mono ?_)
  have wD := john_wt_DV n labL δ
  have wB : Bv.wt ≤ 5 * (n + 1) ^ 2 := john_wt_B x y
  have wR := john_wt_Rn n
  have wC := john_wt_C (n := n) (labL := labL) (δ := δ) x y
  have e1 := wt_list4_le (johnDV n labL δ) (natList (List.range n)) (.nat x) (.nat y)
  have ea : a.wt = (Val.list [johnDV n labL δ, natList (List.range n), .nat x, .nat y]).wt := rfl
  have e2 := wt_list3_le (johnDV n labL δ) (.nat x) (.nat y)
  have e3 := wt_list2_le (.list [johnDV n labL δ, .nat x, .nat y]) (natList (List.range n))
  have e4 := wt_list2_le (johnDV n labL δ) Bv
  have e5 := wt_list2_le (.list [johnDV n labL δ, Bv]) (natList (List.range n))
  have w1 := wt_nat_le x; have w2 := wt_nat_le y
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have y23 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := john_pow_le (by omega) (by omega)
  have y34 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := john_pow_le (by omega) (by omega)
  omega

end GI.Impl
