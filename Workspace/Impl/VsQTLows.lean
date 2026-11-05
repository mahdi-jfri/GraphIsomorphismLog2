module

public import Workspace.Impl.VsQTSot
public import Workspace.Lang.Lib.LinIntTake

@[expose] public section

/-!
# The lows of a split by a chain of partial sums

Given local bases `P_1, …, P_b` (of subspaces `U_i`), the lows of the split are the lifts of
`U_1 + … + U_j` for `j = b - 1, …, 1`, and then `W'`. One low, on `[[fr, p, Ps, b], k]`, takes
the first `b - 1 - k` bases, joins them, lifts and takes an echelon basis.

* `vsQTLowE`, `vsQTLow_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved

/-- One low, on `[[fr, p, Ps, b], k]`. -/
def vsQTLowE (tk cat lift bas : ℕ) : Expr :=
  .call bas (mk2 (.get (arg 0) (.nat 1))
    (.call lift (mk2 (.get (arg 0) (.nat 0))
      (.call cat (.call tk (mk2 (.arith .sub (.arith .sub (.get (arg 0) (.nat 3)) (.nat 1)) (arg 1))
        (.get (arg 0) (.nat 2))))))))

/-- The layout of one low. -/
structure VsQTLowAt (P : Program) (f tk cat lift bas : ℕ) : Prop where
  hf : P.funs[f]? = some (vsQTLowE tk cat lift bas)
  htk : P.HasAt tk (linTakeFuns tk)
  hcat : P.HasAt cat (vsWFlatFuns cat)
  hlift : P.HasAt lift (vsWLiftFuns lift)
  hbas : P.HasAt bas (vsWBasFuns bas)

/-- The value of the bases. -/
def vsQTPsV (Ps : List (List (List ℕ))) : Val := .list (Ps.map vsWVs)

/-- The context of the lows. -/
def vsQTLowCtx (p d : ℕ) (ws' cs : List (List ℕ)) (Ps : List (List (List ℕ))) : Val :=
  .list [vsWFrVal p d ws' cs, .nat p, vsQTPsV Ps, .nat Ps.length]

/-- What one low is. -/
noncomputable def vsQTLowL (p d : ℕ) (ws' cs : List (List ℕ)) (Ps : List (List (List ℕ))) (k : ℕ) :
    List (List ℕ) :=
  vsWBas p (vsWLift p d ws' cs (Ps.take (Ps.length - 1 - k)).flatten)

set_option maxHeartbeats 8000000 in
theorem vsQTLow_spec {P : Program} {f tk cat lift bas : ℕ} (H : VsQTLowAt P f tk cat lift bas)
    {p N d : ℕ} (hpp : p.Prime) {ws' cs : List (List ℕ)} (hF : VsWFrOK p N d ws' cs) {Ps : List (List (List ℕ))}
    (hPs : ∀ P' ∈ Ps, VsWFit p cs.length P') (hsum : ws'.length + (Ps.map List.length).sum ≤ N)
    (hbN : Ps.length ≤ N) {k : ℕ} (hk : k ≤ N) :
    FunDet P f (.list [vsQTLowCtx p d ws' cs Ps, .nat k]) (vsWVs (vsQTLowL p d ws' cs Ps k))
      (10 ^ 12 * (N + 1) ^ 12) := by
  obtain ⟨hp1, hpN, hdN, h', hc, hl⟩ := hF
  have hcd : cs.length ≤ N := by omega
  set c := vsQTLowCtx p d ws' cs Ps
  set X := Val.list [c, .nat k]
  have rc : ∀ k' v, [vsWFrVal p d ws' cs, .nat p, vsQTPsV Ps, .nat Ps.length][k']? = some v →
      Det P [X] (.get (arg 0) (.nat k')) v _ := fun k' v hv =>
    Det.get' (Det.arg' (P := P) (rest := []) (vs := [c, .nat k]) (j := 0) rfl) (Det.nat k') hv
  have g1 := Det.arg' (P := P) (rest := []) (vs := [c, .nat k]) (j := 1) rfl
  set j := Ps.length - 1 - k
  have dj := Det.arith (op := .sub) (Det.arith (op := .sub) (rc 3 _ rfl) (Det.nat 1)) g1
  simp only [GI.Machine.BinOp.eval] at dj
  have dtk := Det.call (Det.mk2 dj (rc 2 _ rfl))
    (linTake_spec H.htk (Ps.map vsWVs) j (by simp [j]; omega))
  rw [← List.map_take] at dtk
  set T := Ps.take j
  have hT : ∀ P' ∈ T, VsWFit p cs.length P' := fun P' h => hPs P' (List.mem_of_mem_take h)
  have hTs : (T.map List.length).sum ≤ (Ps.map List.length).sum := by
    exact ((List.take_sublist j Ps).map List.length).sum_le_sum (fun _ _ => Nat.zero_le _)
  have hfl : VsWFit p cs.length T.flatten := fun u hu => by
    obtain ⟨P', hP', hu⟩ := List.mem_flatten.mp hu
    exact hT P' hP' u hu
  have hfll : T.flatten.length = (T.map List.length).sum := List.length_flatten
  -- weights
  have hP1 : ∀ P' ∈ Ps, (vsWVs P').wt ≤ 11 * (N + 1) ^ 3 + 4 := fun P' hP' =>
    wt_vsWVs_le (VsWFit.bnd (hPs P' hP') hpN hcd) (by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hP'); omega)
  have q13 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hq3 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have wPs : (vsQTPsV Ps).wt ≤ 40 * (N + 1) ^ 4 := by
    have := wt_list_le_of (Ps.map vsWVs) (c := 11 * (N + 1) ^ 3 + 4) (by
      intro v hv; obtain ⟨P', hP', rfl⟩ := List.mem_map.mp hv; exact hP1 P' hP')
    rw [List.length_map] at this
    have h2 : Ps.length * (2 * (11 * (N + 1) ^ 3 + 4) + 1) ≤ (N + 1) * (31 * (N + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (N + 1) * (31 * (N + 1) ^ 3) = 31 * (N + 1) ^ 4 := by ring
    have : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    show (Val.list _).wt ≤ _
    omega
  -- joining
  set xss := T.map fun P' => P'.map natList
  have e1 : Val.list (T.map vsWVs) = Val.list (xss.map Val.list) := by
    simp [xss, vsWVs, List.map_map, Function.comp_def]
  rw [e1] at dtk
  have e2 : Val.list xss.flatten = vsWVs T.flatten := by
    simp [xss, vsWVs, List.map_flatten, List.map_map, Function.comp_def]
  have wTf := wt_vsWVs_le (VsWFit.bnd hfl hpN hcd) (by omega)
  have wTi : (Val.list (xss.map Val.list)).wt ≤ 40 * (N + 1) ^ 4 := by
    have hsub : (xss.map Val.list) <+: (Ps.map vsWVs) := by
      have : xss.map Val.list = (Ps.map vsWVs).take j := by
        simp [xss, T, List.map_take, vsWVs, List.map_map, Function.comp_def]; rfl
      rw [this]; exact List.take_prefix _ _
    exact (wt_list_mono hsub).trans wPs
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have dcat := Det.call dtk (vsWConcat_spec H.hcat (N := N) xss
    (by simp only [xss, List.length_map]; exact (List.length_take_le' _ _).trans hbN)
    (fun xs hxs => by
      obtain ⟨P', hP', rfl⟩ := List.mem_map.mp hxs
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hP')
      simp; omega)
    (by rw [e2]; omega) (by omega))
  rw [e2] at dcat
  have hLfit := vsWLift_fit (d := d) (by omega) h' cs T.flatten
  have hLl : (vsWLift p d ws' cs T.flatten).length ≤ N := by
    rw [vsWLift, List.length_append, List.length_map]; omega
  have dlift := Det.call (Det.mk2 (rc 0 _ rfl) dcat)
    (vsWLift_spec H.hlift ⟨hp1, hpN, hdN, h', hc, hl⟩ hfl (by omega))
  have dbas := Det.call (Det.mk2 (rc 1 _ rfl) dlift) (vsWBas_spec H.hbas (by omega) hpN hdN hLfit hLl)
  refine FunDet.intro H.hf (dbas.mono ?_)
  -- the cost
  have wF := wt_vsWFrVal_le ⟨hp1, hpN, hdN, h', hc, hl⟩
  have wL := wt_vsWVs_le (VsWFit.bnd hLfit hpN hdN) (by omega)
  have hBf := vsWBas_fit (by omega) hLfit
  have wB := wt_vsWVs_le (VsWFit.bnd hBf hpN hdN) (by
    haveI : Fact p.Prime := ⟨hpp⟩
    rw [vsWBas_length hpp hLfit]
    have := Submodule.finrank_le (R := ZMod p) (vsWSp p d (vsWLift p d ws' cs T.flatten))
    simp only [Module.finrank_fin_fun] at this
    omega)
  have wc : c.wt ≤ 2000 * (N + 1) ^ 4 := by
    have := wt_list4_le (vsWFrVal p d ws' cs) (.nat p) (vsQTPsV Ps) (.nat Ps.length)
    have := wt_nat_le p; have := wt_nat_le Ps.length
    have : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := q34
    have : N + 1 ≤ (N + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
    show (Val.list _).wt ≤ _
    omega
  have wX := wt_list2_le c (.nat k)
  have := wt_nat_le k; have := wt_nat_le j; have := wt_nat_le 0; have := wt_nat_le 1
  have := wt_nat_le 2; have := wt_nat_le 3; have := wt_nat_le (Ps.length - 1)
  have w2j := wt_list2_le (.nat j) (vsQTPsV Ps)
  have hj : j ≤ N := by omega
  have wtk : linTakeCost (Val.list [.nat j, .list (Ps.map vsWVs)]).wt ≤ 10 ^ 4 * (200 * (N + 1) ^ 4) ^ 3 := by
    unfold linTakeCost
    have e : (Val.list [.nat j, .list (Ps.map vsWVs)]).wt = (Val.list [.nat j, vsQTPsV Ps]).wt := rfl
    rw [e]
    have : N + 1 ≤ (N + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have e12 : (200 * (N + 1) ^ 4) ^ 3 = 8 * 10 ^ 6 * (N + 1) ^ 12 := by ring
  have wF2 := wt_list2_le (vsWFrVal p d ws' cs) (vsWVs T.flatten)
  have wL2 := wt_list2_le (.nat p) (vsWVs (vsWLift p d ws' cs T.flatten))
  have q412 : (N + 1) ^ 4 ≤ (N + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have q512 : (N + 1) ^ 5 ≤ (N + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have q612 : (N + 1) ^ 6 ≤ (N + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have ewx : (Val.list (xss.map Val.list)).wt ≤ 40 * (N + 1) ^ 4 := wTi
  have eTv : (Val.list (List.take j (List.map vsWVs Ps))).wt ≤ 40 * (N + 1) ^ 4 :=
    (wt_list_mono (List.take_prefix _ _)).trans wPs
  have ecx : X.wt = (Val.list [c, .nat k]).wt := rfl
  have et1 : (Val.list [Val.nat (Ps.length - 1 - k), vsQTPsV Ps]).wt = (Val.list [Val.nat j, vsQTPsV Ps]).wt := rfl
  have et2 : (Val.nat (Ps.length - 1 - k)).wt = (Val.nat j).wt := rfl
  clear_value c X xss T j
  have := wt_nat_le p; have := wt_nat_le Ps.length
  omega

end GI.Impl
