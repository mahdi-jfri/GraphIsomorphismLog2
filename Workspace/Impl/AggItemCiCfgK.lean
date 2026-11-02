import Workspace.Impl.AggItemCiCfgL

/-!
# The configuration branch: the color codes

The colors of the pair structure in `itcqArg` are codes: a pair color `v` gets its first place
in the list `itcqCL` of all pair colors (`itcqCode`). This file computes the code of the pair
color at a position (`itcq_cd_spec`): the pair color by `itcqPcF`, then `find` in the list, with
the equality test `eqTestF`. The test is costed by weights (`itcq_eqT_spec`), since the
library bound `eqTest_det` grows with the values, and colors can be about `q^κ`.
`itcq_mapPos_spec` maps a program over the positions `0, …, m - 1`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val)
open GI.Machine (BinOp)

variable {q : ℕ}

/-- Equality with the number `v`. -/
def itcqEqQ (v : ℕ) : Val → Bool
  | .nat y => decide (y = v)
  | _ => false

theorem itcq_findIdx (l : List ℕ) (v : ℕ) : (l.map Val.nat).findIdx (itcqEqQ v) = l.idxOf v := by
  rw [List.findIdx_map, List.idxOf]
  congr 1

/-- On `[[[col table, fiber points, n], ⟨colors⟩], t]`: the place of the pair color of position
`t` in the list of colors, with the pair color program at `fpc` and `find` at `fb`. -/
def itcqCdF (fpc fb : ℕ) : Expr :=
  .call fb (mk2 (.call fpc (mk2 (.get (arg 0) (.nat 0)) (arg 1))) (.get (arg 0) (.nat 1)))

/-- The cost bound of `itcqCdF`. -/
def itcqCdC (W : ℕ) : ℕ := 10 ^ 5 * (W + 2) ^ 2

theorem itcq_cd_arith {W len F c : ℕ} (hl : len ≤ W)
    (hF : F ≤ len * (10 * (4 * W + 10 + 1)) +
      loopModK * (len + 1) * (4 * W + 10 + 2 * len + 3))
    (hc : c ≤ 21 * (4 * W + 10 + 1) + (50 * (4 * W + 10 + 1) + F)) : c ≤ itcqCdC W := by
  unfold loopModK at hF
  unfold itcqCdC
  have h1 : len * (10 * (4 * W + 10 + 1)) ≤ W * (40 * W + 110) := Nat.mul_le_mul hl (by omega)
  have h2 : (len + 1) * (4 * W + 10 + 2 * len + 3) ≤ (W + 1) * (6 * W + 13) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : 1000 * (len + 1) * (4 * W + 10 + 2 * len + 3) ≤ 1000 * ((W + 1) * (6 * W + 13)) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h2
  nlinarith

section Prog

variable {P : Program}

/-- **The equality test**, costed by the weight `W` of its input. -/
theorem itcq_eqT_spec {f : ℕ} (hf : P.funs[f]? = some eqTestF) (v y : ℕ) {W : ℕ}
    (hW : (Val.list [.nat v, .nat y]).wt ≤ W) :
    FunDet P f (.list [.nat v, .nat y]) (boolVal (itcqEqQ v (.nat y))) (10 * (W + 1)) := by
  have hv : (Val.nat v).wt ≤ W := (st_wt_mem (by simp)).trans hW
  have hy : (Val.nat y).wt ≤ W := (st_wt_mem (by simp)).trans hW
  have a1 := StDC.arg (P := P) (rest := []) (vs := [.nat v, .nat y]) (j := 1) rfl hW
    (by have := wt_nat_le 1; have := wt_list_eq [Val.nat v, .nat y]; omega) hy
  have a0 := StDC.arg (P := P) (rest := []) (vs := [.nat v, .nat y]) (j := 0) rfl hW
    (by have := wt_list_eq [Val.nat v, .nat y]; omega) hv
  have e := StDC.arith a1 a0 (op := .eq) (z := (itcqEqQ v (.nat y)).toNat)
    (by simp only [BinOp.eval_eq, itcqEqQ]; by_cases h : y = v <;> simp [h])
    ((wt_boolVal_le _).trans (by have := wt_list_eq [Val.nat v, .nat y]; omega))
  exact StDC.funDet hf e (by omega)

/-- **The code of the pair color at position `t`.** -/
theorem itcq_cd_spec {fpc fb fe fcd : ℕ} (hfp : P.funs[fpc]? = some itcqPcF)
    (hfb : P.HasAt fb (findFuns fb fe)) (hfe : P.funs[fe]? = some eqTestF)
    (hcd : P.funs[fcd]? = some (itcqCdF fpc fb)) (Z : PairCfg q) (CL : List ℕ)
    (t : Fin (Z.fiber.card * Z.fiber.card))
    (hmem : itcqPC Z rfl ((itciPE _).symm t) ∈ CL) {W : ℕ}
    (hW : (Val.list [.list [.list [rcColVal Z, itcqFV Z, .nat Z.fiber.card], natList CL],
      .nat t]).wt ≤ W) :
    FunDet P fcd (.list [.list [.list [rcColVal Z, itcqFV Z, .nat Z.fiber.card], natList CL],
      .nat t]) (.nat (itcqCode CL (itcqPC Z rfl ((itciPE _).symm t)))) (itcqCdC W) := by
  set cz : Val := .list [rcColVal Z, itcqFV Z, .nat Z.fiber.card] with hcz
  set v := itcqPC Z rfl ((itciPE _).symm t) with hv
  set env : List Val := [.list [.list [cz, natList CL], .nat t]]
  have hcl : (Val.list [cz, natList CL]).wt < W :=
    lt_of_lt_of_le (wt_le_wt_list (by simp)) hW
  have hczw : cz.wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp)) hcl.le
  have hCLw : (natList CL).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp)) hcl.le
  have htw : (Val.nat t).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp)) hW
  have hcolw : (rcColVal Z).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp)) hczw.le
  have hvw : (Val.nat v).wt ≤ (rcColVal Z).wt := itcq_pcw Z _ _
  have hlen : CL.length < W := by
    have := length_lt_wt_list (CL.map Val.nat)
    simp only [List.length_map] at this
    unfold natList at hCLw; omega
  have h2 := wt_nat_le 2
  have A0 := StDC.arg (P := P) (rest := []) (vs := [.list [cz, natList CL], .nat t]) (j := 0)
    (W := 4 * W + 10) rfl (by omega) (by omega) (by omega)
  have A1 := StDC.arg (P := P) (rest := []) (vs := [.list [cz, natList CL], .nat t]) (j := 1)
    (W := 4 * W + 10) rfl (by omega) (by omega) (by omega)
  have g0 := StDC.get A0 (StDC.nat 0 (by omega)) (v := cz) rfl (by omega)
  have g1 := StDC.get A0 (StDC.nat 1 (by omega)) (v := natList CL) rfl (by omega)
  have hpin : (Val.list [cz, .nat t]).wt ≤ 4 * W + 10 := by
    have := wt_list2_le cz (.nat t); omega
  have pc := StDC.call (StDC.mk2 g0 A1 hpin (by omega))
    (itcq_pcF_spec hfp Z t hpin) (le_trans (itcq_pcw Z _ _) (by omega))
  have hfin : (Val.list [.nat v, natList CL]).wt ≤ 4 * W + 10 := by
    have := wt_list2_le (.nat v) (natList CL); omega
  have hfd : FunDet P fb (.list [.nat v, natList CL]) (.nat (itcqCode CL v))
      (CL.length * (10 * (4 * W + 10 + 1)) +
        loopModK * (CL.length + 1) * (4 * W + 10 + 2 * CL.length + 3)) := by
    have hfs := find_spec (P := P) hfb (c := .nat v) (xs := CL.map Val.nat) (q := itcqEqQ v)
      (B := fun _ => 10 * (4 * W + 10 + 1)) (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        refine itcq_eqT_spec hfe v y ?_
        have := wt_list2_le (.nat v) (.nat y)
        have : (Val.nat y).wt ≤ (natList CL).wt :=
          st_wt_mem (List.mem_map_of_mem (f := Val.nat) hy)
        omega)
    refine FunAll.mono hfs fun w c ⟨hw, hc⟩ => ⟨?_, ?_⟩
    · rw [hw, itcq_findIdx, itcqCode, if_pos hmem]
    · simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
      have := Nat.mul_le_mul_left (loopModK * (CL.length + 1))
        (show (Val.list [.nat v, .list (CL.map Val.nat)]).wt + 2 * CL.length + 3 ≤
          4 * W + 10 + 2 * CL.length + 3 by unfold natList at hfin; omega)
      exact hc.trans (Nat.add_le_add_left this _)
  have hcw : (Val.nat (itcqCode CL v)).wt ≤ 4 * W + 10 := by
    have := wt_nat_le (itcqCode CL v)
    have := itcqCode_lt hmem
    omega
  have e := StDC.call (StDC.mk2 pc g1 hfin (by omega)) hfd hcw
  exact StDC.funDet hcd e (itcq_cd_arith hlen.le le_rfl (by omega))

/-- **Map over positions**: if `fp` on `[c, t]` gives `g t` for every position `t < m`, then
`map fp` on `[c, [0, …, m - 1]]` gives the list of the `g t`. -/
theorem itcq_mapPos_spec {mb fp : ℕ} (hm : P.HasAt mb (mapFuns mb fp)) {c : Val} {m : ℕ}
    {g : Fin m → ℕ} {Bd : ℕ} (hf : ∀ t : Fin m, FunDet P fp (.list [c, .nat t]) (.nat (g t)) Bd) :
    FunAll P mb (.list [c, natList (List.range m)]) (fun w cost =>
      w = .list ((List.finRange m).map fun t => .nat (g t)) ∧
        cost ≤ m * Bd + mapK * (m + 1) * ((Val.list [c, natList (List.range m)]).wt + w.wt + 1)) := by
  let F : Val → Val := fun x => match x with
    | .nat t => if ht : t < m then .nat (g ⟨t, ht⟩) else .nat 0
    | _ => .nat 0
  have key := map_spec (P := P) hm (c := c) (xs := (List.range m).map Val.nat)
    (R := fun x w => w = F x) (B := fun _ => Bd) (by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      have ht' := List.mem_range.1 ht
      refine FunAll.mono (hf ⟨t, ht'⟩) fun w cost ⟨hw, hc⟩ => ⟨?_, hc⟩
      subst hw
      simp only [F, dif_pos ht'])
  refine key.mono fun w cost ⟨ws, hw, h2, hc⟩ => ?_
  have hval : w = .list ((List.finRange m).map fun t => .nat (g t)) := by
    rw [hw, itcq_f2_map h2, ← List.map_coe_finRange_eq_range]
    simp only [List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, F, dif_pos t.isLt, Fin.eta]
  refine ⟨hval, ?_⟩
  simp only [List.map_const', List.sum_replicate, List.length_map, List.length_range,
    smul_eq_mul] at hc
  exact hc

end Prog

end GI.Impl

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val)

variable {q : ℕ}

/-- The cost bound of the list of color codes. -/
def itcqCdsC (W : ℕ) : ℕ := 10 ^ 7 * (W + 3) ^ 4

theorem itcq_cds_arith {m W o c : ℕ} (hm : m ≤ W) (ho : o ≤ 2 * (m * (W + 2)) + m + 4)
    (hc : c ≤ m * itcqCdC (4 * W + 10) + 1000 * (m + 1) * (W + o + 1)) : c ≤ itcqCdsC W := by
  unfold itcqCdC at hc
  unfold itcqCdsC
  have h1 : m * (10 ^ 5 * (4 * W + 10 + 2) ^ 2) ≤ W * (10 ^ 5 * (4 * W + 12) ^ 2) :=
    Nat.mul_le_mul_right _ hm
  have h2 : (m + 1) * (W + o + 1) ≤ (W + 1) * (2 * (W * (W + 2)) + 2 * W + 5) := by
    have : m * (W + 2) ≤ W * (W + 2) := Nat.mul_le_mul_right _ hm
    exact Nat.mul_le_mul (by omega) (by omega)
  have h3 : 1000 * (m + 1) * (W + o + 1) ≤ 1000 * ((W + 1) * (2 * (W * (W + 2)) + 2 * W + 5)) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h2
  have h4 : (4 * W + 12) ^ 2 = 16 * (W + 3) ^ 2 := by ring
  rw [h4] at h1
  nlinarith

section Prog

variable {P : Program}

/-- **The color codes of `Z`**: the codes in `CL` of the pair colors at all positions, as the
value `encFun` of `itcqXV`/`itcqYV` (for `Z = X`, `h = rfl` and `Z = Y`, `h = hc.symm`). -/
theorem itcq_cds_spec {fpc fb fe fcd mb : ℕ} (hfp : P.funs[fpc]? = some itcqPcF)
    (hfb : P.HasAt fb (findFuns fb fe)) (hfe : P.funs[fe]? = some eqTestF)
    (hcd : P.funs[fcd]? = some (itcqCdF fpc fb)) (hm : P.HasAt mb (mapFuns mb fcd))
    (Z : PairCfg q) {n : ℕ} (h : Z.fiber.card = n) (CL : List ℕ)
    (hmem : ∀ t, itcqPC Z rfl ((itciPE Z.fiber.card).symm t) ∈ CL) {W : ℕ}
    (hW : (Val.list [.list [.list [rcColVal Z, itcqFV Z, .nat Z.fiber.card], natList CL],
      natList (List.range (Z.fiber.card * Z.fiber.card))]).wt ≤ W) :
    FunAll P mb (.list [.list [.list [rcColVal Z, itcqFV Z, .nat Z.fiber.card], natList CL],
      natList (List.range (Z.fiber.card * Z.fiber.card))]) (fun w cost =>
        w = encFun (fun t : Fin (n * n) => itcqCode CL (itcqPC Z h ((itciPE n).symm t))) ∧
          cost ≤ itcqCdsC W) := by
  subst h
  set c : Val := .list [.list [rcColVal Z, itcqFV Z, .nat Z.fiber.card], natList CL]
  set m := Z.fiber.card * Z.fiber.card
  have hcw : c.wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp)) hW
  have hRw : (natList (List.range m)).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp)) hW
  have hCLw : (natList CL).wt < c.wt := wt_le_wt_list (by simp)
  have hmw : m ≤ W := by
    have := length_lt_wt_list ((List.range m).map Val.nat)
    simp only [List.length_map, List.length_range] at this
    unfold natList at hRw; omega
  have hlen : CL.length < W := by
    have := length_lt_wt_list (CL.map Val.nat)
    simp only [List.length_map] at this
    unfold natList at hCLw; omega
  have key := itcq_mapPos_spec (P := P) hm (c := c) (m := m)
    (g := fun t => itcqCode CL (itcqPC Z rfl ((itciPE Z.fiber.card).symm t)))
    (Bd := itcqCdC (4 * W + 10)) fun t => itcq_cd_spec hfp hfb hfe hcd Z CL t (hmem t) (by
      have := wt_list2_le c (.nat t)
      have := wt_nat_le (t : ℕ)
      have : (t : ℕ) < m := t.isLt
      have hx : (Val.list [c, .nat t]).wt ≤ 4 * W + 10 := by omega
      exact hx)
  refine key.mono fun w cost ⟨hw, hc⟩ => ⟨hw, ?_⟩
  have hout := itcq_natList_wt (l := (List.finRange m).map fun t =>
      itcqCode CL (itcqPC Z rfl ((itciPE Z.fiber.card).symm t))) (B := W + 2) (by
    intro x hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    have := wt_nat_le (itcqCode CL (itcqPC Z rfl ((itciPE Z.fiber.card).symm t)))
    have := itcqCode_lt (hmem t)
    omega)
  simp only [List.length_map, List.length_finRange] at hout
  have hw' : w.wt ≤ 2 * (m * (W + 2)) + m + 4 := by
    rw [hw]; unfold natList at hout; simpa [List.map_map] using hout
  have := Nat.mul_le_mul_left (mapK * (m + 1))
    (show (Val.list [c, natList (List.range m)]).wt + w.wt + 1 ≤ W + w.wt + 1 by omega)
  refine itcq_cds_arith hmw hw' ((hc.trans (Nat.add_le_add_left this _)).trans ?_)
  unfold mapK; exact le_rfl

end Prog

end GI.Impl
