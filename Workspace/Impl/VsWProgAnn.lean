module

public import Workspace.Impl.VsWProgId
public import Workspace.Impl.VsFAlgSpanStep

@[expose] public section

/-!
# The common kernel as a program

* `vsFAnnFuns b` (72 functions), `vsFAnn_spec`: on `[p, D, vsFMatsVal Ys]` the spanning list
  `vsWVs (vsFAnnL p D Ys)` of the common kernel of the stored matrices `Ys`.
  Meaning: `GI.Proved.vsFAnnL_span`, and `GI.Proved.vsFAnnL_nil` for `Ys = vsFNilL p D Bm`.
-/

namespace GI.Impl

open GI.Lang GI.Cited

theorem vsWCut_length_le {p N d : ℕ} (hp1 : 1 < p) (hpN : p ≤ N) (hdN : d ≤ N)
    {us A : List (List ℕ)} (hA : GI.Proved.VsWSq p d A) (hl : us.length ≤ N) :
    (vsWCut p d us A).length ≤ us.length := by
  have hI := vsWImg_fit' (p := p) (d := d) (by omega) A us
  have hIl : (vsWImg p d A us).length = us.length := by simp [vsWImg]
  have := vsWKer_length_le hp1 hpN hdN hI (by omega)
  simp only [vsWCut, List.length_map]
  omega

theorem vsWCut_fold_ok {p N d : ℕ} (hp1 : 1 < p) (hpN : p ≤ N) (hdN : d ≤ N) :
    ∀ (L : List (List (List ℕ))) (us : List (List ℕ)), (∀ y ∈ L, GI.Proved.VsWSq p d y) →
      GI.Proved.VsWFit p d us → us.length ≤ N →
      GI.Proved.VsWFit p d (L.foldl (vsWCut p d) us) ∧ (L.foldl (vsWCut p d) us).length ≤ us.length
  | [], us, _, hu, _ => ⟨hu, le_rfl⟩
  | y :: L, us, hL, hu, hl => by
    have h1 := vsWCut_length_le hp1 hpN hdN (us := us) (hL y (List.mem_cons_self ..)) hl
    obtain ⟨a, b⟩ := vsWCut_fold_ok hp1 hpN hdN L (vsWCut p d us y)
      (fun y' hy' => hL y' (List.mem_cons_of_mem _ hy')) (GI.Proved.vsWCut_fit (by omega)) (by omega)
    exact ⟨a, by rw [List.foldl_cons]; omega⟩

/-- One step, on `[[p, D], us, y]`: the cut of `us` by `y`. -/
def vsFAnnStepF (cut : ℕ) : Expr :=
  .call cut (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1) (arg 2))

theorem vsFAnnStep_spec {P : Program} {g cut : ℕ} (hg : P.funs[g]? = some (vsFAnnStepF cut))
    (hc : P.HasAt cut (vsWCutFuns cut)) {p N d : ℕ} (hp1 : 1 < p) (hpN : p ≤ N) (hdN : d ≤ N)
    {us y : List (List ℕ)} (hus : GI.Proved.VsWFit p d us) (hl : us.length ≤ N)
    (hy : GI.Proved.VsWSq p d y) :
    FunDet P g (.list [.list [.nat p, .nat d], vsWVs us, vsWVs y]) (vsWVs (vsWCut p d us y))
      (2 * 10 ^ 8 * (N + 1) ^ 5) := by
  set X := Val.list [.list [.nat p, .nat d], vsWVs us, vsWVs y]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [Val.list [.nat p, .nat d], vsWVs us, vsWVs y])
    (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [Val.list [.nat p, .nat d], vsWVs us, vsWVs y])
    (j := 1) rfl
  have a2 := Det.arg' (P := P) (rest := []) (vs := [Val.list [.nat p, .nat d], vsWVs us, vsWVs y])
    (j := 2) rfl
  have g0 := Det.get' a0 (Det.nat 0) (show [Val.nat p, .nat d][0]? = some (.nat p) from rfl)
  have g1 := Det.get' a0 (Det.nat 1) (show [Val.nat p, .nat d][1]? = some (.nat d) from rfl)
  refine FunDet.intro hg ((Det.call (Det.mk4 g0 g1 a1 a2)
    (vsWCut_spec hc hp1 hpN hdN hus hl hy)).mono ?_)
  have wus := wt_vsWVs_le (VsWFit.bnd hus hpN hdN) (show us.length ≤ N + 1 by omega)
  have wy := wt_vsWVs_le (VsWFit.bnd hy.1 hpN hdN) (show y.length ≤ N + 1 by have := hy.2; omega)
  have hCf := GI.Proved.vsWCut_fit (p := p) (d := d) (us := us) (A := y) (by omega)
  have hCl := vsWCut_length_le hp1 hpN hdN (us := us) hy hl
  have wC := wt_vsWVs_le (VsWFit.bnd hCf hpN hdN) (show (vsWCut p d us y).length ≤ N + 1 by omega)
  have wp := wt_nat_le p
  have wd := wt_nat_le d
  have w2 := wt_list2_le (.nat p) (.nat d)
  have wX := wt_list3_le (.list [.nat p, .nat d]) (vsWVs us) (vsWVs y)
  have eX : X.wt = (Val.list [.list [.nat p, .nat d], vsWVs us, vsWVs y]).wt := rfl
  have w4 := wt_list4_le (.nat p) (.nat d) (vsWVs us) (vsWVs y)
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- The common kernel, on `[p, D, Ys]`: fold the cut over `Ys` from the identity. -/
def vsFAnnF (fo id : ℕ) : Expr := .call fo (mk3 (mk2 (arg 0) (arg 1)) (arg 2) (.call id (arg 1)))

/-- The common kernel program at base `b` (72 functions). -/
def vsFAnnFuns (b : ℕ) : List Expr :=
  [vsFAnnF (b + 1) (b + 62)] ++ foldlFuns (b + 1) (b + 4) ++ [vsFAnnStepF (b + 5)] ++
    vsWCutFuns (b + 5) ++ vsWIdFuns (b + 62)

theorem vsFAnnFuns_length (b : ℕ) : (vsFAnnFuns b).length = 72 := rfl

/-- **The common kernel program.** -/
theorem vsFAnn_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsFAnnFuns b)) {p N D : ℕ}
    (hp1 : 1 < p) (hpN : p ≤ N) (hDN : D ≤ N) {Ys : List (List (List ℕ))}
    (hY : ∀ y ∈ Ys, GI.Proved.VsWSq p D y) (hYl : Ys.length ≤ N) :
    FunDet P b (.list [.nat p, .nat D, vsFMatsVal Ys]) (vsWVs (vsFAnnL p D Ys))
      (10 ^ 9 * (N + 1) ^ 6) := by
  have h0 : P.funs[b]? = some (vsFAnnF (b + 1) (b + 62)) := h.get (j := 0) (by simp [vsFAnnFuns])
  have hfo : P.HasAt (b + 1) (foldlFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hst : P.funs[b + 4]? = some (vsFAnnStepF (b + 5)) :=
    h.get (j := 4) (by rw [vsFAnnFuns_length]; omega)
  have hcut : P.HasAt (b + 5) (vsWCutFuns (b + 5)) := h.block 5 rfl
  have hid : P.HasAt (b + 62) (vsWIdFuns (b + 62)) := h.block 62 rfl
  set X := Val.list [.nat p, .nat D, vsFMatsVal Ys]
  have a k {v : Val} (hv : [Val.nat p, .nat D, vsFMatsVal Ys][k]? = some v) :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat D, vsFMatsVal Ys]) (j := k) hv
  have dI := Det.call (a 1 rfl) (vsWId_spec hid hDN)
  have hIf := GI.Proved.vsWId_fit hp1 D
  have hIl : (vsWId D).length = D := by simp [vsWId]
  set xs := Ys.map fun M => Val.list (M.map natList)
  have hxs : vsFMatsVal Ys = .list xs := rfl
  have hfold := foldl_spec hfo (c := .list [.nat p, .nat D]) (xs := xs) (acc0 := vsWVs (vsWId D))
    (Inv := fun i acc => acc = vsWVs ((Ys.take i).foldl (vsWCut p D) (vsWId D)))
    (M := 11 * (N + 1) ^ 3 + 4) (B := fun _ => 2 * 10 ^ 8 * (N + 1) ^ 5) (by simp)
    (fun i acc hi hacc => by
      subst hacc
      obtain ⟨hf, hl⟩ := vsWCut_fold_ok hp1 hpN hDN (Ys.take i) (vsWId D)
        (fun y hy => hY y (List.mem_of_mem_take hy)) hIf (by omega)
      exact wt_vsWVs_le (VsWFit.bnd hf hpN hDN) (by omega))
    (fun i acc hi hacc => by
      subst hacc
      have hi' : i < Ys.length := by simpa [xs] using hi
      obtain ⟨hf, hl⟩ := vsWCut_fold_ok hp1 hpN hDN (Ys.take i) (vsWId D)
        (fun y hy => hY y (List.mem_of_mem_take hy)) hIf (by omega)
      have hx : xs[i] = vsWVs Ys[i] := by simp [xs, vsWVs]
      rw [hx]
      refine FunAll.mono (vsFAnnStep_spec hst hcut hp1 hpN hDN hf (by omega)
        (hY _ (List.getElem_mem hi'))) fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
        List.foldl_append]
      rfl)
  have hlen : xs.length = Ys.length := by simp [xs]
  have dF := Det.call (Det.mk3 (Det.mk2 (a 0 rfl) (a 1 rfl)) (a 2 rfl) dI) (hfold.mono
    fun w c hw => ⟨by rw [hw.1, hlen, List.take_length], hw.2⟩)
  refine FunDet.intro h0 (dF.mono ?_)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at *
  obtain ⟨hAf, hAl⟩ := vsWCut_fold_ok hp1 hpN hDN Ys (vsWId D) hY hIf (by omega)
  have wA := wt_vsWVs_le (VsWFit.bnd hAf hpN hDN) (show (vsFAnnL p D Ys).length ≤ N + 1 by
    rw [vsFAnnL]; omega)
  have wI := wt_vsWVs_le (VsWFit.bnd hIf hpN hDN) (show (vsWId D).length ≤ N + 1 by omega)
  have wY : (vsFMatsVal Ys).wt ≤ 40 * (N + 1) ^ 4 :=
    wt_vsFMatsVal_le hpN hDN (fun M hM => GI.Proved.vsWSq_vsFSq (hY M hM)) (by omega)
  rw [hxs] at wY
  have wp := wt_nat_le p
  have wd := wt_nat_le D
  have w2 := wt_list2_le (.nat p) (.nat D)
  have w3 := wt_list3_le (.list [.nat p, .nat D]) (.list xs) (vsWVs (vsWId D))
  have wX := wt_list3_le (.nat p) (.nat D) (vsFMatsVal Ys)
  have eX : X.wt = (Val.list [.nat p, .nat D, vsFMatsVal Ys]).wt := rfl
  rw [hxs] at wX eX
  have hK : loopModK = 1000 := rfl
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q5 : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have k1 : xs.length * (2 * 10 ^ 8 * (N + 1) ^ 5) ≤ (N + 1) * (2 * 10 ^ 8 * (N + 1) ^ 5) :=
    Nat.mul_le_mul_right _ (by omega)
  have k2 : loopModK * (xs.length + 1) * ((Val.list [.list [.nat p, .nat D], .list xs,
      vsWVs (vsWId D)]).wt + xs.length + (11 * (N + 1) ^ 3 + 4) + 1) ≤
      1000 * (N + 1) * (200 * (N + 1) ^ 4) := by
    rw [hK]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e1 : (N + 1) * (2 * 10 ^ 8 * (N + 1) ^ 5) = 2 * 10 ^ 8 * (N + 1) ^ 6 := by ring
  have e2 : 1000 * (N + 1) * (200 * (N + 1) ^ 4) = 200000 * (N + 1) ^ 5 := by ring
  have q6 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have ex : (Val.list [Val.nat p, Val.nat D, vsFMatsVal Ys]).wt =
    (Val.list [Val.nat p, Val.nat D, .list xs]).wt := rfl
  have ey : (Val.list [Val.list [Val.nat p, Val.nat D], vsFMatsVal Ys, vsWVs (vsWId D)]).wt =
    (Val.list [Val.list [Val.nat p, Val.nat D], .list xs, vsWVs (vsWId D)]).wt := rfl
  omega

end GI.Impl
