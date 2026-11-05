module

public import Workspace.Impl.AggItemCfROrb

@[expose] public section

/-! The orbital program's component bounds, collected in the input weight. -/

set_option maxRecDepth 2000

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited Equiv Equiv.Perm

noncomputable def itCfRCoef (hps : PointwiseStab) : ℕ :=
  (pointwiseStabPrim hps).c * 2000 ^ (pointwiseStabPrim hps).k +
    stabOrbitK * 2000 ^ 9 + 10 ^ 9

noncomputable def itCfRExp (hps : PointwiseStab) : ℕ :=
  6 * (pointwiseStabPrim hps).k + 60

private theorem itCfR_raise {M i j C : ℕ} (h : i ≤ j) :
    C * (M + 1) ^ i ≤ C * (M + 1) ^ j :=
  Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) h)

/-- All stabilizer-chain costs are polynomial in the original input weight.
The exponent includes the exponent of the cited stabilizer primitive. -/
theorem itCfR_deg_bound (hps : PointwiseStab) (a gv : Val) (q N M : ℕ)
    (hg : gv.wt ≤ M) (hq : q ≤ M) (hN : N ≤ M)
    (ha : a.wt ≤ 20 * (M + 1) ^ 2) :
    itCfDegC hps a gv q N ≤ itCfRCoef hps * (M + 1) ^ itCfRExp hps := by
  let k := (pointwiseStabPrim hps).k
  let c := (pointwiseStabPrim hps).c
  have hp1 : 1 ≤ (M + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hp16 : M + 1 ≤ (M + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have hp26 : (M + 1) ^ 2 ≤ (M + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hq6 := Nat.pow_le_pow_left (show q + 1 ≤ M + 1 by omega) 6
  have hG : itCfDegG gv q ≤ 701 * (M + 1) ^ 6 := by
    unfold itCfDegG
    omega
  have hM : itCfDegM gv q N ≤ 2000 * (M + 1) ^ 6 := by
    unfold itCfDegM
    omega
  have hY : itCfDegY gv q N + 5 ≤ 2000 * (M + 1) ^ 6 := by
    unfold itCfDegY
    omega
  have hsum : a.wt + N + itCfDegM gv q N + 10 ≤ 3000 * (M + 1) ^ 6 := by omega
  have hprim : (pointwiseStabPrim hps).boundSize (itCfDegY gv q N + 3) ≤
      (c * 2000 ^ k) * (M + 1) ^ (6 * k) := by
    unfold Prim.boundSize
    have h := Nat.mul_le_mul_left c (Nat.pow_le_pow_left hY k)
    simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using h
  have hstab : stabOrbitK * itCfDegY gv q N ^ 9 ≤
      (stabOrbitK * 2000 ^ 9) * (M + 1) ^ 54 := by
    have h := Nat.mul_le_mul_left stabOrbitK
      (Nat.pow_le_pow_left (show itCfDegY gv q N ≤ 2000 * (M + 1) ^ 6 by omega) 9)
    simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using h
  obtain ⟨S, hS⟩ : ∃ S : ℕ, stabOrbitK * 2000 ^ 9 = S := ⟨_, rfl⟩
  rw [hS] at hstab
  have hsmall : 1000 * (a.wt + itCfDegM gv q N + N + 10) ≤ 3000000 * (M + 1) ^ 6 := by
    calc _ = 1000 * (a.wt + N + itCfDegM gv q N + 10) := by congr 1; omega
         _ ≤ 1000 * (3000 * (M + 1) ^ 6) := Nat.mul_le_mul_left _ hsum
         _ = _ := by rw [← Nat.mul_assoc]
  have hs : itCfDegD hps a gv q N ≤
      (c * 2000 ^ k + S + 3000000) * (M + 1) ^ (6 * k + 54) := by
    have h1 := hprim.trans (itCfR_raise (M := M) (C := c * 2000 ^ k)
      (show 6 * k ≤ 6 * k + 54 by omega))
    have h2 := hstab.trans (itCfR_raise (M := M) (C := S)
      (show 54 ≤ 6 * k + 54 by omega))
    have h3 := hsmall.trans (itCfR_raise (M := M) (C := 3000000)
      (show 6 ≤ 6 * k + 54 by omega))
    unfold itCfDegD
    calc _ ≤ _ + _ + _ := Nat.add_le_add (Nat.add_le_add h1 h2) h3
         _ = _ := by simp only [Nat.add_mul]
  have hmain : N * itCfDegD hps a gv q N ≤
      (c * 2000 ^ k + S + 3000000) *
        (M + 1) ^ (6 * k + 55) := by
    calc _ ≤ (M + 1) * ((c * 2000 ^ k + S + 3000000) *
        (M + 1) ^ (6 * k + 54)) := Nat.mul_le_mul (by omega) hs
         _ = _ := by rw [show 6 * k + 55 = (6 * k + 54) + 1 by omega, pow_succ (M + 1) (6 * k + 54)]; ac_rfl
  have hlinear : 100 * (a.wt + N + itCfDegM gv q N + 1) ≤ 300000 * (M + 1) ^ 6 := by
    have h := Nat.mul_le_mul_left 100 hsum
    omega
  have hloop1 : N * (100 * (a.wt + N + itCfDegM gv q N + 1)) ≤ 300000 * (M + 1) ^ 7 := by
    have h := Nat.mul_le_mul (show N ≤ M + 1 by omega) hlinear
    convert h using 1 <;> rw [pow_succ (M + 1)] <;> ring
  have hloop2 : loopK * (N + 1) * (a.wt + N + itCfDegM gv q N + 1) ≤
      900000 * (M + 1) ^ 7 := by
    have h := Nat.mul_le_mul
      (Nat.mul_le_mul_left loopK (show N + 1 ≤ M + 1 by omega))
      (show a.wt + N + itCfDegM gv q N + 1 ≤ 3000 * (M + 1) ^ 6 by omega)
    convert h using 1 <;> unfold loopK <;> rw [pow_succ (M + 1)] <;> ring
  have htail : 100 * (a.wt + N + itCfDegM gv q N) + 300 ≤ 400000 * (M + 1) ^ 6 := by
    omega
  have hmain' := hmain.trans (itCfR_raise (M := M)
    (show 6 * k + 55 ≤ 6 * k + 60 by omega))
  have hloop1' := hloop1.trans (itCfR_raise (M := M) (show 7 ≤ 6 * k + 60 by omega))
  have hloop2' := hloop2.trans (itCfR_raise (M := M) (show 7 ≤ 6 * k + 60 by omega))
  have htail' := htail.trans (itCfR_raise (M := M) (show 6 ≤ 6 * k + 60 by omega))
  have hall := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hmain' hloop1') hloop2') htail'
  have hc : ((c * 2000 ^ k + S + 3000000) +
      300000 + 900000 + 400000) ≤ c * 2000 ^ k + S + 10 ^ 9 := by
    have hnum : 3000000 + 300000 + 900000 + 400000 ≤ (10 ^ 9 : ℕ) := by norm_num
    simpa only [Nat.add_assoc] using Nat.add_le_add_left hnum (c * 2000 ^ k + S)
  have hlast := Nat.mul_le_mul_right ((M + 1) ^ (6 * k + 60)) hc
  have hfirst : itCfDegC hps a gv q N ≤
      ((c * 2000 ^ k + S + 3000000) +
        300000 + 900000 + 400000) * (M + 1) ^ (6 * k + 60) := by
    simpa only [itCfDegC, Nat.add_mul, Nat.add_assoc] using hall
  have hfinal := hfirst.trans hlast
  simpa only [itCfRCoef, itCfRExp, ← hS, k, c] using hfinal

/-- Explicit constants for the orbital object stage. -/
noncomputable def itCfRCo (hps : PointwiseStab) : ℕ := 10 ^ 25 * (itCfRCoef hps + 1)
noncomputable def itCfRDo (hps : PointwiseStab) : ℕ := itCfRExp hps

theorem itCfR_pts_wt {q : ℕ} (xs : List (Fin q)) (hlen : xs.length ≤ q) :
    (encPts xs).wt ≤ 5 * (q + 1) ^ 2 := by
  have h := wt_natList_le_sq (xs := xs.map Fin.val) (B := q)
    (by intro x hx; obtain ⟨v, _, rfl⟩ := List.mem_map.1 hx; exact v.isLt.le)
    (by simpa only [List.length_map] using hlen)
  simpa only [itCf_encPts_eq, natList, List.map_map, Function.comp_def] using h

/-- The complete orbital cost has the bound required by `ItCfObjSpec`. -/
theorem itCfR_comp_bound (hps : PointwiseStab) {q ℓ : ℕ}
    (hs : List (Perm (Fin q))) (t : Fin ℓ → Fin q) (r : (Fin 2 → Fin q) → ℕ) :
    itCfRCompC hps hs t r ≤
      itCfB (itCfRCo hps) (itCfRDo hps) (itCfOrbIn hs t r).wt := by
  set M := (itCfOrbIn hs t r).wt
  set xs := (domSet (gens hs)).sort
  set a := Val.list [encGroup hs, encPts xs]
  have hg : (encGroup hs).wt ≤ M :=
    (wt_le_wt_list (by simp [M, itCfOrbIn])).le
  have hq : q ≤ M := by
    have h := S_le_wt_encGroup hs
    have hqg : q + 1 ≤ (encGroup hs).wt :=
      (Nat.le_mul_of_pos_left _ (by omega)).trans h
    omega
  have hlen : xs.length ≤ q := by
    simp only [xs, Finset.length_sort]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin q)
  have hwpts := itCfR_pts_wt xs hlen
  have hp2 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hp12 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq2 := Nat.pow_le_pow_left (show q + 1 ≤ M + 1 by omega) 2
  have haw : a.wt ≤ 20 * (M + 1) ^ 2 := by
    have hw := wt_list2_le (encGroup hs) (encPts xs)
    change a.wt ≤ _ at hw
    omega
  have hdeg := itCfR_deg_bound hps a (encGroup hs) q xs.length M hg hq
    (hlen.trans hq) haw
  obtain ⟨T, hT⟩ : ∃ T : ℕ, itCfRCoef hps = T := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, itCfRExp hps = D := ⟨_, rfl⟩
  rw [hT, hD] at hdeg
  have hD60 : 60 ≤ D := by rw [← hD]; unfold itCfRExp; omega
  have hp1D : M + 1 ≤ (M + 1) ^ D := Nat.le_self_pow (by omega) _
  have hp0D : 1 ≤ (M + 1) ^ D := Nat.one_le_pow _ _ (by omega)
  have hp2D : (M + 1) ^ 2 ≤ (M + 1) ^ D := Nat.pow_le_pow_right (by omega) (by omega)
  have hA : a.wt ≤ 20 * (M + 1) ^ D := haw.trans (Nat.mul_le_mul_left _ hp2D)
  have hdom : itDomC (encGroup hs).wt ≤ 10 ^ 9 * (M + 1) ^ D := by
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)).trans
      (itCfR_raise (M := M) (by omega))
  have hread : 10 ^ 16 * (M + 1) ^ 4 ≤ 10 ^ 16 * (M + 1) ^ D :=
    itCfR_raise (by omega)
  have hdeg' : 10 * (a.wt + itCfDegC hps a (encGroup hs) q xs.length + q + 10) ≤
      (10 * (20 + T + 1 + 10)) * (M + 1) ^ D := by
    have hqD : q ≤ (M + 1) ^ D := (show q ≤ M + 1 by omega).trans hp1D
    have hten : 10 ≤ 10 * (M + 1) ^ D := by omega
    have hh := Nat.mul_le_mul_left 10
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hA hdeg) hqD) hten)
    simpa only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] using hh
  have htotal : itCfRCompC hps hs t r ≤
      (100000 * (1 + 10 ^ 9 + 10 * (20 + T + 1 + 10) + 10 ^ 16 + 1 + 10)) *
        (M + 1) ^ D := by
    have hmD : M ≤ (M + 1) ^ D := (Nat.le_succ _).trans hp1D
    have hqD : q ≤ (M + 1) ^ D := hq.trans hmD
    have hten : 10 ≤ 10 * (M + 1) ^ D := by omega
    have hh := Nat.mul_le_mul_left 100000
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add hmD hdom) hdeg') hread) hqD) hten)
    simpa only [itCfRCompC, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, a, xs, M] using hh
  have hcoef : 100000 * (1 + 10 ^ 9 + 10 * (20 + T + 1 + 10) + 10 ^ 16 + 1 + 10) ≤
      10 ^ 25 * (T + 1) := by omega
  have hh := htotal.trans (Nat.mul_le_mul_right _ hcoef)
  simpa only [itCfB, itCfRCo, itCfRDo, hT, hD, M] using hh

/-- The orbital field of `ItCfObjSpec`, with explicit polynomial constants. -/
theorem itCf_orb_spec (hps : PointwiseStab) {P : Program}
    {f dm dg dd jps orb rng fd pd cnt rd tb mb rw rm ce : ℕ}
    (hf : P.funs[f]? = some (itCfROrbF dm dg rd))
    (hdm : P.funs[dm]? = some (itDomF orb rng fd))
    (horb : P.HasAt orb (orbitFuns orb)) (hrng : P.HasAt rng (rangeFuns rng))
    (hfd : P.HasAt fd (filterFuns fd pd)) (hpd : P.funs[pd]? = some (acpDomF cnt))
    (hcnt : P.HasAt cnt (countFuns cnt))
    (hdg : P.funs[dg]? = some (itCfRDegreeF dd))
    (hdd : P.HasAt dd (itCfDegFuns dd jps))
    (hj : P.prims[jps]? = some (pointwiseStabPrim hps))
    (hrd : P.funs[rd]? = some (itCfRReadF tb ce))
    (htb : P.funs[tb]? = some (itCfRTableF mb rng))
    (hmb : P.HasAt mb (mapFuns mb rw)) (hrw : P.funs[rw]? = some (itCfRRowF rm rng))
    (hrm : P.HasAt rm (mapFuns rm ce)) (hce : P.funs[ce]? = some itCfRCellF)
    {q ℓ : ℕ} (hs : List (Perm (Fin q))) (t : Fin ℓ → Fin q) (R : Refiner2 q) :
    FunAll P f (itCfOrbIn hs t (R (orbColOut (gens hs) t))) (fun w cost =>
      w = itCfOutV (orbitalOut R (gens hs) t) ∧
        cost ≤ itCfB (itCfRCo hps) (itCfRDo hps)
          (itCfOrbIn hs t (R (orbColOut (gens hs) t))).wt) := by
  exact FunAll.mono (itCfR_orb_from_programs hps hf hdm horb hrng hfd hpd hcnt hdg hdd hj
    hrd htb hmb hrw hrm hce hs t R) fun w cost ⟨hw, hc⟩ =>
      ⟨hw, hc.trans (itCfR_comp_bound hps hs t _)⟩

end GI.Impl
