module

public import Workspace.Impl.GMPCosetIndex

@[expose] public section

/-! # Computing one entry of a conjugation-action table -/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

/-- On `[gv, reps, h, r]`, find the coset of `h * r * h⁻¹`. -/
def gmpConjIndexF (fd comp inv : ℕ) : Expr :=
  .letE (.call inv (arg 2))
    (.letE (.call comp (mk2 (arg 2) (arg 3)))
      (.letE (.call comp (mk2 (.var 2) (.var 1)))
        (.call fd (mk2 (mk2 (arg 0) (.var 3)) (arg 1)))))

noncomputable def gmpConjIndexCost (hm : Membership) (Y L : ℕ) : ℕ :=
  gmpIndexCost hm Y L + 10 ^ 7 * Y

theorem gmpConjIndex_spec (hm : Membership) {P : Program}
    {f fd pt jm comp inv n : ℕ} (hf : P.funs[f]? = some (gmpConjIndexF fd comp inv))
    (hfd : P.HasAt fd (findFuns fd pt))
    (hpt : P.funs[pt]? = some (tmRpPredF jm comp inv))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hcomp : P.HasAt comp (composeFuns comp)) (hinv : P.HasAt inv (invFuns inv))
    {gv : Val} {V : Subgroup (Perm (Fin n))} (hV : GroupVal n gv V)
    (rs : List (Perm (Fin n))) (h r : Perm (Fin n)) {Y : ℕ}
    (hY : (n + 1) ^ 4 ≤ Y)
    (harg : (Val.list [gv, .list (rs.map encPerm), encPerm h, encPerm r]).wt ≤ Y) :
    FunDet P f (.list [gv, .list (rs.map encPerm), encPerm h, encPerm r])
      (.nat (gmpCosetIndex V rs (h * r * h⁻¹))) (gmpConjIndexCost hm Y rs.length) := by
  let a := Val.list [gv, .list (rs.map encPerm), encPerm h, encPerm r]
  have hY1 : 1 ≤ Y := (Nat.one_le_pow 4 (n + 1) (by omega)).trans hY
  have hn3 : (n + 1) ^ 3 ≤ Y :=
    (Nat.pow_le_pow_right (by omega) (by omega : 3 ≤ 4)).trans hY
  have hvY : gv.wt ≤ Y := (wt_le_wt_list (by simp) : gv.wt < a.wt).le.trans harg
  have hrsY : (Val.list (rs.map encPerm)).wt ≤ Y :=
    (wt_le_wt_list (by simp) : (Val.list (rs.map encPerm)).wt < a.wt).le.trans harg
  have hhY : (encPerm h).wt ≤ Y :=
    (wt_le_wt_list (by simp) : (encPerm h).wt < a.wt).le.trans harg
  have hrY : (encPerm r).wt ≤ Y :=
    (wt_le_wt_list (by simp) : (encPerm r).wt < a.wt).le.trans harg
  have hn2 : (n + 1) ^ 2 ≤ Y :=
    (Nat.pow_le_pow_right (by omega) (by omega : 2 ≤ 4)).trans hY
  have hwi : (encPerm h⁻¹).wt ≤ 4 * Y := (wt_encPerm_le h⁻¹).trans (Nat.mul_le_mul_left _ hn2)
  have hwp : (encPerm (h * r)).wt ≤ 4 * Y :=
    (wt_encPerm_le (h * r)).trans (Nat.mul_le_mul_left _ hn2)
  have hwc : (encPerm (h * r * h⁻¹)).wt ≤ 4 * Y :=
    (wt_encPerm_le (h * r * h⁻¹)).trans (Nat.mul_le_mul_left _ hn2)
  have dH (rest : List Val) := Det.arg' (P := P)
    (vs := [gv, .list (rs.map encPerm), encPerm h, encPerm r]) (rest := rest) (j := 2) rfl
  have dR (rest : List Val) := Det.arg' (P := P)
    (vs := [gv, .list (rs.map encPerm), encPerm h, encPerm r]) (rest := rest) (j := 3) rfl
  have dI := Det.call (dH []) (inv_spec hinv h)
  have dP := Det.call (Det.mk2 (dH [encPerm h⁻¹]) (dR [encPerm h⁻¹])) (compose_spec hcomp h r)
  have dC := Det.call (Det.mk2
    (Det.var' (P := P) (env := [a, encPerm h⁻¹, encPerm (h * r)]) (i := 2) rfl)
    (Det.var' (P := P) (env := [a, encPerm h⁻¹, encPerm (h * r)]) (i := 1) rfl))
    (compose_spec hcomp (h * r) h⁻¹)
  have dG := Det.arg' (P := P) (vs := [gv, .list (rs.map encPerm), encPerm h, encPerm r])
    (rest := [encPerm h⁻¹, encPerm (h * r), encPerm (h * r * h⁻¹)]) (j := 0) rfl
  have dRs := Det.arg' (P := P) (vs := [gv, .list (rs.map encPerm), encPerm h, encPerm r])
    (rest := [encPerm h⁻¹, encPerm (h * r), encPerm (h * r * h⁻¹)]) (j := 1) rfl
  have dY := Det.var' (P := P)
    (env := [a, encPerm h⁻¹, encPerm (h * r), encPerm (h * r * h⁻¹)]) (i := 3) rfl
  have dF := Det.call (Det.mk2 (Det.mk2 dG dY) dRs)
    (gmpCosetIndex_spec hm hfd hpt hjm hcomp hinv hV hY hvY rs (h * r * h⁻¹))
  have d := Det.letE dI (Det.letE dP (Det.letE dC dF))
  refine FunDet.intro hf (d.mono ?_)
  have w1 := wt_list2_le (encPerm h) (encPerm r)
  have w2 := wt_list2_le (encPerm (h * r)) (encPerm h⁻¹)
  have w3 := wt_list2_le gv (encPerm (h * r * h⁻¹))
  have w4 := wt_list2_le (.list [gv, encPerm (h * r * h⁻¹)]) (.list (rs.map encPerm))
  have hlen : rs.length ≤ Y := by
    have hw := length_lt_wt_list (rs.map encPerm)
    simp only [List.length_map] at hw
    omega
  have hindex : gmpCosetIndex V rs (h * r * h⁻¹) ≤ rs.length := by
    exact le_trans List.findIdx_le_length (by rw [List.length_map])
  have wIndex : (Val.nat (gmpCosetIndex V rs (h * r * h⁻¹))).wt ≤ Y + 2 :=
    (wt_nat_le _).trans (by omega)
  have hInv := Nat.mul_le_mul_left invK hY
  have hComp := Nat.mul_le_mul_left permK hn3
  have hwarg : a.wt = (Val.list [gv, .list (rs.map encPerm), encPerm h, encPerm r]).wt := rfl
  unfold gmpConjIndexCost
  simp only [invK, permK] at *
  omega

theorem gmpConjIndexCost_poly (hm : Membership) :
    PBU (fun L Y _ => gmpConjIndexCost hm Y L) :=
  (gmpIndexCost_poly hm).add (PBU.W.smul (10 ^ 7))

end GI.Impl
