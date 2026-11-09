module

public import Workspace.Degree.JohnRProg

@[expose] public section

/-!
# The specs of the ball search

`johnR_iter_spec` is the result used later: the function `106` computes the ball of radius `d`.
-/

namespace GI.Degree

open GI.Lang GI.Cited GI.Proved GI.Impl Equiv
open GI.Machine (BinOp)

variable {n : ℕ} {labL : List ℕ} {υ : ℕ}

/-- The entries of the balls are `0` or `1`. -/
theorem johnBall_bits (d : ℕ) : ∀ v ∈ johnBall n labL υ d, v ≤ 1 := by
  cases d with
  | zero =>
    intro v hv
    simp only [johnBall, johnDRow, List.mem_map] at hv
    obtain ⟨y, -, rfl⟩ := hv
    exact Bool.toNat_le _
  | succ d =>
    intro v hv
    simp only [johnBall, johnBallStep, List.mem_map] at hv
    obtain ⟨y, -, rfl⟩ := hv
    split
    · exact Bool.toNat_le _
    · exact le_rfl

theorem johnBall_length (d : ℕ) : (johnBall n labL υ d).length = n := by
  cases d <;> simp [johnBall, johnBallStep, johnDRow]

theorem johnBall_wt (d : ℕ) : (natList (johnBall n labL υ d)).wt ≤ 7 * n + 4 :=
  john_wt_bitsN ⟨johnBall_length d, johnBall_bits d⟩

/-- A ball as a list of `0`s and `1`s. -/
structure BallOK (n : ℕ) (Rl : List ℕ) : Prop where
  len : Rl.length = n
  bits : ∀ v ∈ Rl, v ≤ 1

theorem BallOK.wt {Rl : List ℕ} (h : BallOK n Rl) : (natList Rl).wt ≤ 7 * n + 4 :=
  john_wt_bitsN ⟨h.len, h.bits⟩

theorem BallOK.get {Rl : List ℕ} (h : BallOK n Rl) {y : ℕ} (hy : y < n) :
    (Rl.map Val.nat)[y]? = some (.nat (Rl.getD y 0)) :=
  john_get_row (h.len ▸ hy)

theorem BallOK.getD_le {Rl : List ℕ} (h : BallOK n Rl) (y : ℕ) : Rl.getD y 0 ≤ 1 := by
  rw [List.getD_eq_getElem?_getD]
  cases hy : Rl[y]? with
  | none => simp
  | some a => exact h.bits a (List.mem_of_getElem? hy)

theorem johnBall_ok (d : ℕ) : BallOK n (johnBall n labL υ d) :=
  ⟨johnBall_length d, johnBall_bits d⟩

variable {Rl : List ℕ}

/-- **The test.** -/
theorem johnR_test_spec (hR : BallOK n Rl) {z y : ℕ} (hy : y < n) :
    FunDet johnRProgram 117 (.list [.list [natList (johnDRow n labL υ z), natList Rl], .nat y])
      (boolVal (johnD n labL υ z y && Rl.getD y 0 == 1)) (2000 * (n + 1) ^ 2) := by
  set c := Val.list [natList (johnDRow n labL υ z), natList Rl]
  set a := Val.list [c, .nat y]
  have hc : Det johnRProgram [a] (arg 0) c (2 * a.wt + 5) := Det.arg' rfl
  have hU := Det.get' hc (Det.nat 0)
    (show [natList (johnDRow n labL υ z), natList Rl][0]? =
      some (natList (johnDRow n labL υ z)) from rfl)
  have hRv := Det.get' hc (Det.nat 1)
    (show [natList (johnDRow n labL υ z), natList Rl][1]? = some (natList Rl) from rfl)
  have hY : Det johnRProgram [a] (arg 1) (.nat y) (2 * a.wt + 6) := Det.arg' rfl
  have h1 := Det.get' (vs := (johnDRow n labL υ z).map Val.nat) hU hY
    (john_DRow_get (labL := labL) (δ := υ) (x := z) hy)
  have h2 := Det.get' (vs := Rl.map Val.nat) hRv hY (hR.get hy)
  have hv : BinOp.eval .mul (johnD n labL υ z y).toNat (Rl.getD y 0) =
      (johnD n labL υ z y && Rl.getD y 0 == 1).toNat := by
    have := hR.getD_le y
    simp only [BinOp.eval]
    rcases Nat.lt_or_ge (Rl.getD y 0) 1 with h0 | h0
    · obtain h0' : Rl.getD y 0 = 0 := by omega
      rw [h0']; cases johnD n labL υ z y <;> rfl
    · obtain h0' : Rl.getD y 0 = 1 := by omega
      rw [h0']; cases johnD n labL υ z y <;> rfl
  have h := Det.arith' h1 h2 hv
  refine FunDet.intro johnR_at_test.single (h.mono ?_)
  have wU := john_wt_DRow n labL υ z
  have wR := hR.wt
  have e1 := wt_list2_le (natList (johnDRow n labL υ z)) (natList Rl)
  have e2 := wt_list2_le c (.nat y)
  have ec : c.wt = (Val.list [natList (johnDRow n labL υ z), natList Rl]).wt := rfl
  have ea : a.wt = (Val.list [c, .nat y]).wt := rfl
  have w3 := wt_nat_le y; have w4 := wt_nat_le 0; have w5 := wt_nat_le 1
  have w6 : (Val.nat (johnD n labL υ z y).toNat).wt ≤ 3 := wt_boolVal_le _
  have w7 : (Val.nat (Rl.getD y 0)).wt ≤ 3 := (wt_nat_le _).trans (by have := hR.getD_le y; omega)
  have w8 := Bool.toNat_le (johnD n labL υ z y && Rl.getD y 0 == 1)
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  omega

/-- The test of the search, on values. -/
def johnQBall (n : ℕ) (labL : List ℕ) (υ : ℕ) (Rl : List ℕ) (z : ℕ) : Val → Bool
  | .nat y => johnD n labL υ z y && Rl.getD y 0 == 1
  | .list _ => false

/-- **The search over the points.** -/
theorem johnR_any_spec (hR : BallOK n Rl) (z : ℕ) :
    FunDet johnRProgram 114
      (.list [.list [natList (johnDRow n labL υ z), natList Rl], natList (List.range n)])
      (boolVal ((List.range n).any fun y => johnD n labL υ z y && Rl.getD y 0 == 1))
      (300000 * (n + 1) ^ 3) := by
  have hA := any_spec johnR_at_any (c := .list [natList (johnDRow n labL υ z), natList Rl])
    (xs := (List.range n).map Val.nat) (q := johnQBall n labL υ Rl z)
    (B := fun _ => 2000 * (n + 1) ^ 2) (by
      intro v hv
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
      exact johnR_test_spec hR (List.mem_range.mp hy))
  have e : ((List.range n).map Val.nat).any (johnQBall n labL υ Rl z) =
      (List.range n).any fun y => johnD n labL υ z y && Rl.getD y 0 == 1 := by
    rw [List.any_map]; rfl
  refine hA.mono ?_
  rintro w cost ⟨rfl, hc⟩
  refine ⟨by rw [e], hc.trans ?_⟩
  have hsum := john_sum_le (l := (List.range n).map Val.nat)
    (f := fun _ => 2000 * (n + 1) ^ 2) (B := 2000 * (n + 1) ^ 2) fun _ _ => le_rfl
  simp only [List.length_map, List.length_range] at hsum ⊢
  have wU := john_wt_DRow n labL υ z
  have wR := hR.wt
  have wRn := john_wt_Rn n
  have hRn : natList (List.range n) = Val.list ((List.range n).map Val.nat) := rfl
  rw [hRn] at wRn
  have e1 := wt_list2_le (natList (johnDRow n labL υ z)) (natList Rl)
  have e2 := wt_list2_le (.list [natList (johnDRow n labL υ z), natList Rl])
    (.list ((List.range n).map Val.nat))
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  set A := (Val.list [.list [natList (johnDRow n labL υ z), natList Rl],
    .list ((List.range n).map Val.nat)]).wt
  have hA' : A + n + 4 ≤ 200 * (n + 1) ^ 2 := by omega
  have p1 : n * (2000 * (n + 1) ^ 2) ≤ 2000 * (n + 1) ^ 3 := by
    calc n * (2000 * (n + 1) ^ 2) ≤ (n + 1) * (2000 * (n + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2000 * (n + 1) ^ 3 := by ring
  have p2 : loopModK * (n + 1) * (A + n + 4) ≤ 1000 * (200 * (n + 1) ^ 3) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (n + 1) * (A + n + 4) ≤ (n + 1) * (200 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ hA'
      _ = 200 * (n + 1) ^ 3 := by ring
  omega

/-- The new entry of the ball. -/
def johnBallEnt (n : ℕ) (labL : List ℕ) (υ : ℕ) (Rl : List ℕ) (z : ℕ) : ℕ :=
  if Rl.getD z 0 = 0 then
    ((List.range n).any fun y => johnD n labL υ z y && Rl.getD y 0 == 1).toNat else 1

theorem johnBallStep_eq (Rl : List ℕ) :
    johnBallStep n labL υ Rl = (List.range n).map (johnBallEnt n labL υ Rl) := rfl

/-- **The new entry of the ball.** -/
theorem johnR_ent_spec (hR : BallOK n Rl) {z : ℕ} (hz : z < n) :
    FunDet johnRProgram 113
      (.list [.list [johnDV n labL υ, natList Rl, natList (List.range n)], .nat z])
      (.nat (johnBallEnt n labL υ Rl z)) (500000 * (n + 1) ^ 3) := by
  set c := Val.list [johnDV n labL υ, natList Rl, natList (List.range n)]
  set a := Val.list [c, .nat z]
  have hc : Det johnRProgram [a] (arg 0) c (2 * a.wt + 5) := Det.arg' rfl
  have hU := Det.get' hc (Det.nat 0)
    (show [johnDV n labL υ, natList Rl, natList (List.range n)][0]? = some (johnDV n labL υ)
      from rfl)
  have hRv := Det.get' hc (Det.nat 1)
    (show [johnDV n labL υ, natList Rl, natList (List.range n)][1]? = some (natList Rl) from rfl)
  have hRn := Det.get' hc (Det.nat 2)
    (show [johnDV n labL υ, natList Rl, natList (List.range n)][2]? =
      some (natList (List.range n)) from rfl)
  have hZ : Det johnRProgram [a] (arg 1) (.nat z) (2 * a.wt + 6) := Det.arg' rfl
  have hRz := Det.get' (vs := Rl.map Val.nat) hRv hZ (hR.get hz)
  have hUz := Det.get' (vs := (List.range n).map fun x => natList (johnDRow n labL υ x)) hU hZ
    (john_DV_get hz)
  have hcall := Det.call (Det.mk2 (Det.mk2 hUz hRv) hRn) (johnR_any_spec (υ := υ) hR z)
  have h := john_det_ite hRz (Det.nat 1) hcall
  have hv : (if Rl.getD z 0 = 0 then
      boolVal ((List.range n).any fun y => johnD n labL υ z y && Rl.getD y 0 == 1)
      else Val.nat 1) = .nat (johnBallEnt n labL υ Rl z) := by
    unfold johnBallEnt; split <;> rfl
  rw [hv] at h
  refine FunDet.intro johnR_at_ent.single (h.mono ?_)
  have wD := john_wt_DV n labL υ
  have wU := john_wt_DRow n labL υ z
  have wR := hR.wt
  have wRn := john_wt_Rn n
  have hlt : (natList (johnDRow n labL υ z)).wt < (johnDV n labL υ).wt :=
    wt_le_wt_list (List.mem_of_getElem? (john_DV_get (labL := labL) (δ := υ) hz))
  have e1 := wt_list3_le (johnDV n labL υ) (natList Rl) (natList (List.range n))
  have e2 := wt_list2_le c (.nat z)
  have e3 := wt_list2_le (natList (johnDRow n labL υ z)) (natList Rl)
  have e4 := wt_list2_le (.list [natList (johnDRow n labL υ z), natList Rl])
    (natList (List.range n))
  have ec : c.wt = (Val.list [johnDV n labL υ, natList Rl, natList (List.range n)]).wt := rfl
  have ea : a.wt = (Val.list [c, .nat z]).wt := rfl
  have w3 := wt_nat_le z; have w4 := wt_nat_le 0; have w5 := wt_nat_le 1; have w6 := wt_nat_le 2
  have w7 : (Val.nat (Rl.getD z 0)).wt ≤ 3 := (wt_nat_le _).trans (by have := hR.getD_le z; omega)
  have w8 : (boolVal ((List.range n).any fun y => johnD n labL υ z y && Rl.getD y 0 == 1)).wt ≤ 3 :=
    wt_boolVal_le _
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have y23 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := john_pow_le (by omega) (by omega)
  omega

/-- **One step of the ball, by `map`.** -/
theorem johnR_map_spec (hR : BallOK n Rl) :
    FunDet johnRProgram 110
      (.list [.list [johnDV n labL υ, natList Rl, natList (List.range n)], natList (List.range n)])
      (natList (johnBallStep n labL υ Rl)) (2000000 * (n + 1) ^ 4) := by
  have hT := john_tab johnR_at_map (c := .list [johnDV n labL υ, natList Rl, natList (List.range n)])
    (n := n) (B := 500000 * (n + 1) ^ 3) (G := fun z => .nat (johnBallEnt n labL υ Rl z))
    fun z hz => johnR_ent_spec hR hz
  have e : Val.list ((List.range n).map fun z => Val.nat (johnBallEnt n labL υ Rl z)) =
      natList (johnBallStep n labL υ Rl) := by
    simp [natList, johnBallStep_eq, List.map_map, Function.comp_def]
  rw [e] at hT
  refine hT.mono ?_
  have wD := john_wt_DV n labL υ
  have wR := hR.wt
  have wRn := john_wt_Rn n
  have hS : BallOK n (johnBallStep n labL υ Rl) := by
    have := johnBall_ok (n := n) (labL := labL) (υ := υ) 1
    refine ⟨by simp [johnBallStep], ?_⟩
    intro v hv
    simp only [johnBallStep, List.mem_map] at hv
    obtain ⟨y, -, rfl⟩ := hv
    split
    · exact Bool.toNat_le _
    · exact le_rfl
  have wS := hS.wt
  have e1 := wt_list3_le (johnDV n labL υ) (natList Rl) (natList (List.range n))
  have e2 := wt_list2_le (.list [johnDV n labL υ, natList Rl, natList (List.range n)])
    (natList (List.range n))
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  set A := (Val.list [.list [johnDV n labL υ, natList Rl, natList (List.range n)],
    natList (List.range n)]).wt
  have hA : A + (natList (johnBallStep n labL υ Rl)).wt + 1 ≤ 200 * (n + 1) ^ 2 := by omega
  have p1 : n * (500000 * (n + 1) ^ 3) ≤ 500000 * (n + 1) ^ 4 := by
    calc n * (500000 * (n + 1) ^ 3) ≤ (n + 1) * (500000 * (n + 1) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 500000 * (n + 1) ^ 4 := by ring
  have p2 : mapK * (n + 1) * (A + (natList (johnBallStep n labL υ Rl)).wt + 1) ≤
      1000 * (200 * (n + 1) ^ 3) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (n + 1) * (A + (natList (johnBallStep n labL υ Rl)).wt + 1) ≤
        (n + 1) * (200 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ hA
      _ = 200 * (n + 1) ^ 3 := by ring
  have y34 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := john_pow_le (by omega) (by omega)
  omega

/-- **One step of the ball, as the function `johnBallStepF`.** -/
theorem johnR_step_spec (hR : BallOK n Rl) (i : ℕ) :
    FunDet johnRProgram 109
      (.list [.list [johnDV n labL υ, natList (List.range n)], .nat i, natList Rl])
      (natList (johnBallStep n labL υ Rl)) (3000000 * (n + 1) ^ 4 + 100 * i) := by
  set c := Val.list [johnDV n labL υ, natList (List.range n)]
  set a := Val.list [c, .nat i, natList Rl]
  have hc : Det johnRProgram [a] (arg 0) c (2 * a.wt + 5) := Det.arg' rfl
  have hU := Det.get' hc (Det.nat 0)
    (show [johnDV n labL υ, natList (List.range n)][0]? = some (johnDV n labL υ) from rfl)
  have hRn := Det.get' hc (Det.nat 1)
    (show [johnDV n labL υ, natList (List.range n)][1]? = some (natList (List.range n)) from rfl)
  have hRv : Det johnRProgram [a] (arg 2) (natList Rl) (2 * a.wt + 7) := Det.arg' rfl
  have hcall := Det.call (Det.mk2 (Det.mk3 hU hRv hRn) hRn) (johnR_map_spec (υ := υ) hR)
  refine FunDet.intro johnR_at_step.single (hcall.mono ?_)
  have wD := john_wt_DV n labL υ
  have wR := hR.wt
  have wRn := john_wt_Rn n
  have hS : (natList (johnBallStep n labL υ Rl)).wt ≤ 7 * n + 4 := by
    refine john_wt_bitsN ⟨by simp [johnBallStep], ?_⟩
    intro v hv
    simp only [johnBallStep, List.mem_map] at hv
    obtain ⟨y, -, rfl⟩ := hv
    split
    · exact Bool.toNat_le _
    · exact le_rfl
  have e1 := wt_list3_le (johnDV n labL υ) (natList Rl) (natList (List.range n))
  have e2 := wt_list2_le (.list [johnDV n labL υ, natList Rl, natList (List.range n)])
    (natList (List.range n))
  have e3 := wt_list2_le (johnDV n labL υ) (natList (List.range n))
  have e4 := wt_list3_le c (.nat i) (natList Rl)
  have ec : c.wt = (Val.list [johnDV n labL υ, natList (List.range n)]).wt := rfl
  have ea : a.wt = (Val.list [c, .nat i, natList Rl]).wt := rfl
  have w := wt_nat_le i
  have w0 := wt_nat_le 0; have w1 := wt_nat_le 1; have w2 := wt_nat_le 2
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have y24 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := john_pow_le (by omega) (by omega)
  omega

/-- **The ball of radius `d`**, by iterating `johnBallStepF`. -/
theorem johnR_iter_spec (d : ℕ) :
    FunDet johnRProgram 106
      (.list [.list [johnDV n labL υ, natList (List.range n)], .nat d,
        natList (johnBall n labL υ 0)])
      (natList (johnBall n labL υ d)) (10000000 * (d + 1) * ((n + 1) ^ 4 + d)) := by
  have hI := iter_spec johnR_at_iter (c := .list [johnDV n labL υ, natList (List.range n)])
    (k := d) (acc0 := natList (johnBall n labL υ 0))
    (Inv := fun i acc => acc = natList (johnBall n labL υ i)) (M := 7 * n + 4)
    (B := fun i => 3000000 * (n + 1) ^ 4 + 100 * i) rfl
    (fun i acc _ h => h ▸ johnBall_wt i)
    (fun i acc _ h => by
      subst h
      exact FunAll.mono (johnR_step_spec (johnBall_ok i) i) fun w c h => ⟨h.1, h.2⟩)
  refine hI.mono ?_
  rintro w cost ⟨rfl, hc⟩
  refine ⟨rfl, hc.trans ?_⟩
  have hsum : ∑ i ∈ Finset.range d, (3000000 * (n + 1) ^ 4 + 100 * i) ≤
      d * (3000000 * (n + 1) ^ 4 + 100 * d) := by
    calc ∑ i ∈ Finset.range d, (3000000 * (n + 1) ^ 4 + 100 * i)
        ≤ ∑ _i ∈ Finset.range d, (3000000 * (n + 1) ^ 4 + 100 * d) :=
          Finset.sum_le_sum fun i hi => by have := Finset.mem_range.mp hi; omega
      _ = d * (3000000 * (n + 1) ^ 4 + 100 * d) := by simp
  have wD := john_wt_DV n labL υ
  have wRn := john_wt_Rn n
  have w0 := johnBall_wt (n := n) (labL := labL) (υ := υ) 0
  have e1 := wt_list2_le (johnDV n labL υ) (natList (List.range n))
  have e2 := wt_list3_le (.list [johnDV n labL υ, natList (List.range n)]) (.nat d)
    (natList (johnBall n labL υ 0))
  have wd := wt_nat_le d
  have y0 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have y24 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := john_pow_le (by omega) (by omega)
  set A := (Val.list [.list [johnDV n labL υ, natList (List.range n)], .nat d,
    natList (johnBall n labL υ 0)]).wt
  have hA : A + d + (7 * n + 4) + 1 ≤ 200 * ((n + 1) ^ 4 + d) := by omega
  have p1 : loopModK * (d + 1) * (A + d + (7 * n + 4) + 1) ≤
      200000 * ((d + 1) * ((n + 1) ^ 4 + d)) := by
    calc loopModK * (d + 1) * (A + d + (7 * n + 4) + 1)
        ≤ 1000 * ((d + 1) * (200 * ((n + 1) ^ 4 + d))) := by
          rw [Nat.mul_assoc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hA)
      _ = 200000 * ((d + 1) * ((n + 1) ^ 4 + d)) := by ring
  have p2 : d * (3000000 * (n + 1) ^ 4 + 100 * d) ≤ 3000000 * ((d + 1) * ((n + 1) ^ 4 + d)) := by
    nlinarith
  have p3 : 10000000 * (d + 1) * ((n + 1) ^ 4 + d) =
      10000000 * ((d + 1) * ((n + 1) ^ 4 + d)) := by ring
  omega

end GI.Degree
