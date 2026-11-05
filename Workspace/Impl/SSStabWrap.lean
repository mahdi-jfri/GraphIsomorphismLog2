module

public import Workspace.Impl.SSStabList

@[expose] public section

/-!
# The pointwise stabilizer

`ssStabF` builds the table for the base `S ++ [0, …, n-1]` and lists the entries of the levels
`≥ |S|`, that is, of the slots `|S| n + q`, `q < n²` (`ssStabF_spec`). By `ss_stab_gens` they
generate the pointwise stabilizer of `S`. The program is `ssWrapProgram ssStabFuns`, with
`ssStabF` at `56`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- On `[encGroup gs, encPts S]`: the entries of the levels `≥ |S|` of the table for the base
`S ++ [0, …, n-1]`. -/
def ssStabF (app range start loop : ℕ) : Expr :=
  .letE (.get (.get (.var 0) (.nat 0)) (.nat 0))
    (.letE (.call app (mk2 (.get (.var 0) (.nat 1)) (.call range (.var 1))))
      (.letE (.call start (mk2 (.get (.var 0) (.nat 0)) (.var 2)))
        (.call loop (mk3 (mk2 (.get (.var 3) (.nat 0))
            (.arith .mul (.length (.get (.var 0) (.nat 1))) (.var 1)))
          (.arith .mul (.var 1) (.var 1)) .nil))))

/-- The functions of the pointwise stabilizer wrapper, from `52` on. -/
def ssStabFuns : List Expr := iterFuns 52 55 ++ ([ssStabStepF] ++ [ssStabF 19 47 50 52])

/-- The parts of the pointwise stabilizer wrapper. -/
structure SsStabAt (P : Program) : Prop where
  wrap : SsWrapAt P
  it : P.HasAt 52 (iterFuns 52 55)
  st : P.funs[55]? = some ssStabStepF
  fn : P.funs[56]? = some (ssStabF 19 47 50 52)

theorem ssStabAt_of : SsStabAt (ssWrapProgram ssStabFuns) := by
  have h := ssWrap_extra ssStabFuns
  unfold ssStabFuns at h
  have h1 := h.right
  rw [show 52 + (iterFuns 52 55).length = 55 from rfl] at h1
  have h2 := h1.right
  rw [show 55 + [ssStabStepF].length = 56 from rfl] at h2
  exact ⟨ssWrapAt_of _, h.left, h1.left.single, h2.single⟩

theorem ssEncPts_eq (S : List (Fin n)) : encPts S = .list ((S.map Fin.val).map Val.nat) := by
  unfold encPts; congr 1
  induction S with
  | nil => rfl
  | cons a S ih => exact congrArg (Val.nat a.val :: ·) ih

theorem ssEncB_append (S : List (Fin n)) :
    ssEncB (S ++ List.finRange n) =
      .list ((S.map Fin.val).map Val.nat ++ (List.range n).map Val.nat) := by
  unfold ssEncB natList
  rw [List.map_append, List.map_append, List.map_coe_finRange_eq_range]

/-- The cells of a list of points are at most the size of a list that also holds the group. -/
theorem ss_encPts_cells_le {gs : List (Perm (Fin n))} (S : List (Fin n)) {vs : List Val}
    (hG : encGroup gs ∈ vs) (hS : encPts S ∈ vs) :
    ∀ a ∈ (encPts S).cells, a ≤ (Val.list vs).size + 1 := by
  intro a ha
  rw [ssEncPts_eq] at hS ha
  have hSs := ss_size_le_list hS
  have hGs := ss_size_le_list hG
  have hP : (encPerm (1 : Perm (Fin n))).size ≤ (Val.list ((1 :: gs).map encPerm)).size :=
    ss_size_le_list (by simp)
  have hG2 : (Val.list ((1 :: gs).map encPerm)).size ≤ (encGroup gs).size :=
    ss_size_le_list (vs := [.nat n, .list ((1 :: gs).map encPerm)]) (by simp)
  rw [size_encPerm] at hP
  have hsz : (Val.list ((S.map Fin.val).map Val.nat)).size = 3 + 2 * S.length := by
    rw [size_eq_length]
    simp only [cells_list, List.length_append, List.length_cons, List.length_nil]
    rw [length_cellsList_map_nat]
    simp
  simp only [cells_list, List.length_map, List.cons_append, List.nil_append,
    List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | ha
  · omega
  · omega
  · rw [length_cellsList_map_nat]
    simp only [List.length_map]
    omega
  · obtain ⟨v, hv, ha⟩ := cam_mem_cellsList ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi
    simp only [cells_nat, List.mem_cons, List.not_mem_nil, or_false] at ha
    have := j.isLt
    omega

theorem ss_stab_cost {X r1 r2 s : ℕ} (hr1 : r1 ≤ 1000 * (X + 1) * (3 * X + 1))
    (hr2 : r2 ≤ 1000 * (X + 1) * (6 * X + 8)) (hs : s ≤ 10 ^ 5 * (X + 1) ^ 2) :
    r1 + r2 + 2 * (10 ^ 8 * (X + 1) ^ 4) + s + 300 * (30 * X + 50 + 1) ≤
      4 * (10 ^ 8 * (X + 1) ^ 4) := by
  have h1 : (X + 1) * (3 * X + 1) ≤ 8 * (X + 1) ^ 2 := by nlinarith
  have h1' : (X + 1) * (6 * X + 8) ≤ 8 * (X + 1) ^ 2 := by nlinarith
  have h2 : (X + 1) ^ 2 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  rw [Nat.mul_assoc] at hr1 hr2
  generalize (X + 1) * (3 * X + 1) = A at *
  generalize (X + 1) * (6 * X + 8) = A' at *
  generalize (X + 1) ^ 2 = Q2 at *
  generalize (X + 1) ^ 4 = Q4 at *
  linarith

/-- **The pointwise stabilizer.** -/
theorem ssStabF_spec {P : Program} (hP : SsStabAt P) (gs : List (Perm (Fin n)))
    (S : List (Fin n)) :
    FunAll P 56 (.list [encGroup gs, encPts S]) (fun v c =>
      GensOf (pointwiseStab (gens gs) S) v ∧
        c ≤ 10 * ssPolyK * ((Val.list [encGroup gs, encPts S]).wt + 1) ^ 32) := by
  rw [ssEncPts_eq]
  have hw := hP.wrap
  set w := (Val.list [encGroup gs, Val.list ((S.map Fin.val).map Val.nat)]).wt with hwdef
  -- the bound `Y`
  have hY : n + (S ++ List.finRange n).length + gs.length + 2 ≤ 3 * (w + 1) := by
    rw [List.length_append, List.length_finRange]
    have h1 := ss_encGroup_wt gs
    have h2 := sum_wt_lt_wt_list [encGroup gs, Val.list ((S.map Fin.val).map Val.nat)]
    have h3 := length_lt_wt_list ((S.map Fin.val).map Val.nat)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_map] at h2 h3
    have h4 : (Val.list ((S.map Fin.val).map Val.nat)).wt = (Val.list ((S.map Fin.val).map Val.nat)).wt := rfl
    omega
  have hY' : n + (List.finRange n).length + gs.length + 2 ≤ 3 * (w + 1) := by
    rw [List.length_append] at hY; omega
  set Y := 3 * (w + 1) with hYdef
  obtain ⟨hBw, -, hnW, hMW, -⟩ := ss_start_wts hY
  obtain ⟨hRw, -, -, -, -⟩ := ss_start_wts hY'
  rw [ssEncB_finRange] at hRw
  rw [ssEncB_append] at hBw
  have hst := ssStartF_spec hw.start hw.core hY
  rw [ssEncB_append] at hst
  obtain ⟨hinv, hcl, hgen⟩ := ssBuild_spec (B := S ++ List.finRange n) (gs := gs)
  have hsm := ssInv_small hinv hY
  have hsw := ss_st_wt hinv hY
  have hgens := ss_stab_gens (C := List.finRange n) rfl
    (fun i => List.mem_append_right _ (List.mem_finRange i)) hinv.wf hcl hinv.entry_mem hgen
  rw [List.length_append, List.length_finRange, Nat.add_sub_cancel_left] at hgens
  have hYW := (ss_le_core (Y := Y) (by omega)).1
  obtain ⟨-, hTY, -, hY3, hZ⟩ := ss_Y_facts hY
  have hZW := ssZ_le_ssW Y
  rw [List.length_append, List.length_finRange] at hMW hTY
  have hdist : (S.length + n) * n = S.length * n + n * n := Nat.add_mul _ _ _
  generalize ssBuild (S ++ List.finRange n) gs = st at hst hinv hsm hsw hgens
  obtain ⟨T, prog⟩ := st
  have hlen : T.length = S.length * n + n * n := by
    rw [hinv.len, List.length_append, List.length_finRange, Nat.add_mul]
  have hTw : (ssEncTab T).wt ≤ ssW Y := hsm.tab.wt_le_ssW
  have hnn : n * n * (2 * n + 3) ≤ 10 * Y ^ 3 := by
    refine le_trans (Nat.mul_le_mul (Nat.mul_le_mul_right n (Nat.le_add_left n S.length))
      (by omega : 2 * n + 3 ≤ 2 * n + 8)) hTY
  have hL : ∀ q ≤ n * n, (Val.list ((ssStabList T S.length q).map encPerm)).wt ≤ ssW Y :=
    fun q hq => (ssSmall_stabList T S.length q (Z := ssZ Y)
      (by have := Nat.mul_le_mul_right (2 * n + 3) hq; omega) (by omega)).wt_le_ssW
  have hloop := ssStabLoop_spec (k0 := S.length) (m := n * n) hP.it hP.st (by omega) hTw (by omega) hL
  have happ := append_spec hw.core.gen.insAt.appAt ((S.map Fin.val).map Val.nat)
    ((List.range n).map Val.nat)
  set X := ssW Y with hX
  have haX : w ≤ X := by omega
  set W := 30 * X + 50 with hW
  clear_value W
  have hGa : (encGroup gs).wt < w := wt_le_wt_list (by simp)
  have hSa : (Val.list ((S.map Fin.val).map Val.nat)).wt < w := wt_le_wt_list (by simp)
  set a := Val.list [.list [.nat n, .list ((1 :: gs).map encPerm)],
    .list ((S.map Fin.val).map Val.nat)] with ha
  have haw : a.wt = w := rfl
  have haW : a.wt ≤ W := by omega
  have hnw : (Val.nat n).wt ≤ X := (wt_nat_le _).trans (by omega)
  have dG : ∀ rest, StDC P (a :: rest) (.get (.var 0) (.nat 0))
      (.list [.nat n, .list ((1 :: gs).map encPerm)]) 3 0 W := fun rest =>
    StDC.get (x := 0) (StDC.var' rfl haW) (StDC.nat 0 (by omega)) rfl (by
      show (encGroup gs).wt ≤ W; omega)
  have dSp : ∀ rest, StDC P (a :: rest) (.get (.var 0) (.nat 1))
      (.list ((S.map Fin.val).map Val.nat)) 3 0 W := fun rest =>
    StDC.get (x := 1) (StDC.var' rfl haW) (StDC.nat 1 (by omega)) rfl (by
      show (Val.list ((S.map Fin.val).map Val.nat)).wt ≤ W; omega)
  have dn := StDC.get (x := 0) (v := .nat n) (dG []) (StDC.nat 0 (by omega)) rfl
    (hnw.trans (by omega))
  -- the base
  have hrange : FunDet P 47 (.nat n) (natList (List.range n))
      (1000 * (X + 1) * (3 * X + 1)) :=
    (range_spec hw.range n).mono fun w c ⟨hw', hc⟩ => ⟨hw', hc.trans (by
      rw [hw']; unfold loopModK
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
        (by have := wt_nat_le n; omega))⟩
  have hBv : (Val.list ((S.map Fin.val).map Val.nat ++ (List.range n).map Val.nat)).wt ≤ X :=
    hBw
  have happD : FunDet P 19 (.list [.list ((S.map Fin.val).map Val.nat),
      .list ((List.range n).map Val.nat)])
      (.list ((S.map Fin.val).map Val.nat ++ (List.range n).map Val.nat))
      (1000 * (X + 1) * (6 * X + 8)) :=
    happ.mono fun w c ⟨hw', hc⟩ => ⟨hw', hc.trans (by
      rw [hw']; unfold loopModK
      have h1 : (Val.list [.list ((S.map Fin.val).map Val.nat),
          .list ((List.range n).map Val.nat)]).wt ≤ 4 * X + 6 := st_wt_list2 (show (Val.list ((S.map Fin.val).map Val.nat)).wt ≤ X by
        show (Val.list ((S.map Fin.val).map Val.nat)).wt ≤ X; omega) (show (natList (List.range n)).wt ≤ X from hRw)
      have h2 := length_lt_wt_list ((List.range n).map Val.nat)
      have h3 : (natList (List.range n)).wt = (Val.list ((List.range n).map Val.nat)).wt := rfl
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by simp only [List.length_map, List.length_range]; omega))
        (by simp only [List.length_map, List.length_range]; omega))⟩
  have dRg := StDC.call (StDC.var' (P := P) (env := [a, .nat n]) (i := 1) rfl
    (hnw.trans (by omega))) hrange (show (natList (List.range n)).wt ≤ W by omega)
  have dB := StDC.call (StDC.mk2 (dSp _) dRg
    ((st_wt_list2 (show (Val.list ((S.map Fin.val).map Val.nat)).wt ≤ X by omega) hRw).trans (by omega)) (by omega)) happD
    (hBv.trans (by omega))
  -- the table
  have dS := StDC.call (StDC.mk2 (dG _) (StDC.var' (P := P)
    (env := [a, .nat n, .list ((S.map Fin.val).map Val.nat ++ (List.range n).map Val.nat)])
    (i := 2) rfl (hBv.trans (by omega)))
    ((st_wt_list2 (show (encGroup gs).wt ≤ X by omega) hBv).trans (by omega)) (by omega)) hst
    (show (ssEncSt (T, prog)).wt ≤ W by omega)
  -- the listing
  set env3 := [a, .nat n, .list ((S.map Fin.val).map Val.nat ++ (List.range n).map Val.nat),
    ssEncSt (T, prog)] with henv3
  have dT : StDC P env3 (.get (.var 3) (.nat 0)) (ssEncTab T) 3 0 W :=
    StDC.get (x := 0) (v := ssEncTab T)
      (StDC.var' (v := .list [ssEncTab T, ssEncProg prog]) rfl (by
        show (ssEncSt (T, prog)).wt ≤ W; omega)) (StDC.nat 0 (by omega)) rfl (by omega)
  have dV1 : StDC P env3 (.var 1) (.nat n) 1 0 W := StDC.var' rfl (hnw.trans (by omega))
  have dSl := StDC.length (dSp (env3.drop 1)) (by
    have := length_lt_wt_list ((S.map Fin.val).map Val.nat)
    have h4 : (Val.list ((S.map Fin.val).map Val.nat)).wt = (Val.list ((S.map Fin.val).map Val.nat)).wt := rfl
    omega)
  rw [List.length_map, List.length_map] at dSl
  have hoff : (Val.nat (S.length * n)).wt ≤ X := (wt_nat_le _).trans (by omega)
  have hnn' : (Val.nat (n * n)).wt ≤ X := (wt_nat_le _).trans (by omega)
  have dOff := StDC.arith (op := .mul) (z := S.length * n) dSl dV1 rfl (hoff.trans (by omega))
  have hc2 := st_wt_list2 hTw hoff
  have dC := StDC.mk2 dT dOff (hc2.trans (by omega)) (by omega)
  have dM := StDC.arith (op := .mul) (z := n * n) dV1 dV1 rfl (hnn'.trans (by omega))
  have h0 := hL 0 (Nat.zero_le _)
  have hres := hL (n * n) le_rfl
  have dLp := StDC.call (StDC.mk3 dC dM (StDC.nil (by omega))
    ((st_wt_list3 hc2 (hnn'.trans (by omega)) (h0.trans (by omega))).trans (by omega))
    (by omega)) hloop (hres.trans (by omega))
  refine FunAll.mono (StDC.funDet (c := 4 * ssCoreCost Y) hP.fn (StDC.letE dn (StDC.letE dB
    (StDC.letE dS dLp (hres.trans (by omega))) (hres.trans (by omega)))
    (hres.trans (by omega))) (ss_cost_fin2 (by norm_num) ?_)) fun v c ⟨hv, hc⟩ =>
    ⟨⟨ssStabList T S.length (n * n), hv, (length_ssStabList _ _ _).trans (by rw [sq]), hgens⟩,
      ss_wrap_cost ?_⟩
  · have := ss_stab_cost (X := X) (r1 := 1000 * (X + 1) * (3 * X + 1))
      (r2 := 1000 * (X + 1) * (6 * X + 8)) (s := 10 ^ 5 * (X + 1) ^ 2) le_rfl le_rfl le_rfl
    unfold ssCoreCost
    rw [hW]
    simp only [Nat.zero_add, Nat.add_zero]
    rw [← hX]
    exact le_of_eq_of_le (by ring) this
  · show c ≤ 100 * ssCoreCost Y
    have h4 : 4 * ssCoreCost Y ≤ 100 * ssCoreCost Y := Nat.mul_le_mul_right _ (by norm_num)
    exact hc.trans h4

end GI.Impl
