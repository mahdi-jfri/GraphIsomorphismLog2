import Workspace.Impl.AggItemCfDCore

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited
open GI.Machine (BinOp)

theorem itCfD_des_calls {P : Program} {f core B : ℕ}
    (hf : P.funs[f]? = some (itCfDesF core)) (dl tl : List ℕ) (q κ : ℕ)
    (hcore : 0 < κ → κ < tl.length →
      FunDet P core (stDA dl tl q κ) (itCfDOut dl tl q κ) B) :
    FunDet P f (.list [.nat q, .nat κ, natList dl, natList tl]) (itCfDOut dl tl q κ)
      (10 ^ 5 * ((Val.list [.nat q, .nat κ, natList dl, natList tl]).wt + B + 10)) := by
  set inp : Val := .list [.nat q, .nat κ, natList dl, natList tl]
  set W := 100 * (inp.wt + B + 10)
  have wq : (Val.nat q).wt < inp.wt := wt_le_wt_list (by simp [inp])
  have wk : (Val.nat κ).wt < inp.wt := wt_le_wt_list (by simp [inp])
  have wd : (natList dl).wt < inp.wt := wt_le_wt_list (by simp [inp])
  have wt : (natList tl).wt < inp.wt := wt_le_wt_list (by simp [inp])
  have hln : tl.length < (natList tl).wt := by
    have := length_lt_wt_list (tl.map Val.nat); simpa [natList] using this
  have wA := wt_list4_le (natList dl) (natList tl) (.nat q) (.nat κ)
  have hW5 : 5 ≤ W := by dsimp [W]; omega
  have gq : StDC P [inp] (arg 0) (.nat q) 3 0 W :=
    StDC.arg rfl (by show inp.wt ≤ W; dsimp [W]; omega) (by omega) (by dsimp [W]; omega)
  have gk : StDC P [inp] (arg 1) (.nat κ) 3 0 W :=
    StDC.arg rfl (by show inp.wt ≤ W; dsimp [W]; omega) (by omega) (by dsimp [W]; omega)
  have gd : StDC P [inp] (arg 2) (natList dl) 3 0 W :=
    StDC.arg rfl (by show inp.wt ≤ W; dsimp [W]; omega) (by omega) (by dsimp [W]; omega)
  have gt : StDC P [inp] (arg 3) (natList tl) 3 0 W :=
    StDC.arg rfl (by show inp.wt ≤ W; dsimp [W]; omega) (by omega) (by dsimp [W]; omega)
  have gl := StDC.length gt (by simp only [List.length_map]; dsimp [W]; omega)
  simp only [List.length_map] at gl
  have wbool := wt_nat_le (BinOp.eval .lt κ tl.length)
  have hb : BinOp.eval .lt κ tl.length ≤ 1 := by simp only [BinOp.eval]; split_ifs <;> omega
  simp only [BinOp.eval] at wbool hb
  have gc := StDC.arith (W := W) gk gl (op := .lt) (z := BinOp.eval .lt κ tl.length) rfl (by
    change (Val.nat (BinOp.eval .lt κ tl.length)).wt ≤ W
    dsimp [W]
    omega)
  have wzero : (Val.list [Val.nat 0]).wt ≤ W := by
    have hh : (Val.list [Val.nat 0]).wt = 9 := by decide
    dsimp [W]; omega
  have gz : StDC P [inp] (.snoc .nil (.nat 0)) (.list [.nat 0]) 3 0 W :=
    StDC.snoc (StDC.nil (by omega)) (StDC.nat 0 (by omega)) wzero
  by_cases hk : κ = 0
  · subst κ
    have ho : itCfDOut dl tl q 0 = .list [.nat 0] := by simp [itCfDOut]
    rw [ho]
    have gres := StDC.ite (t := .ite (.arith .lt (arg 1) (.length (arg 3)))
      (.call core (mk4 (arg 2) (arg 3) (arg 0) (arg 1))) (.snoc .nil (.nat 0)))
      (nt := 0) (Et := 0) gk (fun h => absurd rfl h) (fun _ => gz) wzero
    exact StDC.funDet hf gres (by dsimp [W, inp]; omega)
  · have hkpos : 0 < κ := Nat.pos_of_ne_zero hk
    by_cases hkl : κ < tl.length
    · have hc := hcore hkpos hkl
      have wo := hc.wt_lt
      have ga := StDC.call (StDC.mk4 gd gt gq gk (by
        change (stDA dl tl q κ).wt ≤ W
        unfold stDA; dsimp [W]; omega) (by omega)) hc (by dsimp [W]; omega)
      have hx : BinOp.eval .lt κ tl.length ≠ 0 := by simp [BinOp.eval, hkl]
      have gin := StDC.ite (e := .snoc .nil (.nat 0)) (ne := 0) (Ee := 0) gc
        (fun _ => ga) (fun h => absurd h hx) (by dsimp [W]; omega)
      have gout := StDC.ite (e := .snoc .nil (.nat 0)) (ne := 0) (Ee := 0) gk
        (fun _ => gin) (fun h => absurd h hk) (by dsimp [W]; omega)
      exact StDC.funDet hf gout (by dsimp [W, inp]; omega)
    · have ho : itCfDOut dl tl q κ = .list [.nat 0] := by simp [itCfDOut, hkl]
      rw [ho]
      have hx : BinOp.eval .lt κ tl.length = 0 := by simp [BinOp.eval, hkl]
      have gin := StDC.ite (t := .call core (mk4 (arg 2) (arg 3) (arg 0) (arg 1)))
        (nt := 0) (Et := 0) gc (fun h => absurd hx h) (fun _ => gz) wzero
      have gout := StDC.ite (e := .snoc .nil (.nat 0)) (ne := 0) (Ee := 0) gk
        (fun _ => gin) (fun h => absurd h hk) wzero
      exact StDC.funDet hf gout (by dsimp [W, inp]; omega)

/-- Explicit constants for the design object stage. -/
def itCfDCo : ℕ := 10 ^ 110
def itCfDDo : ℕ := 17

/-- The design field of `ItCfObjSpec`, for arbitrary numeric colors. -/
theorem itCf_des_spec {P : Program} {I : ItCfDIdx} {f : ℕ} (h : ItCfDOk P I)
    (hf : P.funs[f]? = some (itCfDesF I.core))
    {q κ ℓ : ℕ} (col : (Fin κ → Fin q) → ℕ) (t : Fin ℓ → Fin q) :
    FunAll P f (itCfDesIn col t) (fun w cost =>
      w = itCfOutV (designOut col t) ∧ cost ≤ itCfB itCfDCo itCfDDo (itCfDesIn col t).wt) := by
  set M := (itCfDesIn col t).wt
  have wd : (encKColoring col).wt < M := wt_le_wt_list (by simp [M, itCfDesIn])
  have wt : (stTv t).wt < M := wt_le_wt_list (by simp [M, itCfDesIn])
  have wq : (Val.nat q).wt < M := wt_le_wt_list (by simp [M, itCfDesIn])
  have wk : (Val.nat κ).wt < M := wt_le_wt_list (by simp [M, itCfDesIn])
  have hA : (stDA (stDL col) (stL fun i => (t i : ℕ)) q κ).wt ≤ 8 * M + 8 := by
    have hw := wt_list4_le (encKColoring col) (stTv t) (.nat q) (.nat κ)
    simpa only [stDA, natList_stDL] using (show
      (Val.list [encKColoring col, stTv t, .nat q, .nat κ]).wt ≤ 8 * M + 8 by omega)
  have hprog := itCfD_des_calls hf (stDL col) (stL fun i => (t i : ℕ)) q κ
    (B := 10 ^ 80 * (8 * M + 8 + 1) ^ 17) (by
      intro hk hkl
      have htlen : (stL fun i => (t i : ℕ)).length = ℓ := by simp [stL]
      have hlpos : 0 < ℓ := by omega
      have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (t ⟨0, hlpos⟩).isLt
      have hc : ItCfDCtx (stDL col) (stL fun i => (t i : ℕ)) q κ :=
        ⟨stDL_length col, by
          intro x hx
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
          exact (t i).isLt, hkl, hqpos, hk⟩
      exact itCfD_core_spec h hc hA)
  rw [natList_stDL, itCfDOut_eq] at hprog
  change FunDet P f (itCfDesIn col t) (itCfOutV (designOut col t)) _ at hprog
  have hpow := Nat.mul_le_mul_left (10 ^ 80) (Nat.pow_le_pow_left
    (show 8 * M + 8 + 1 ≤ 9 * (M + 1) by omega) 17)
  have he : 10 ^ 80 * (9 * (M + 1)) ^ 17 = (10 ^ 80 * 9 ^ 17) * (M + 1) ^ 17 := by ring
  have hcore := hpow.trans_eq he
  have hp : M + 1 ≤ (M + 1) ^ 17 := Nat.le_self_pow (by norm_num) _
  have hp0 : 1 ≤ (M + 1) ^ 17 := Nat.one_le_pow _ _ (by omega)
  refine FunAll.mono hprog fun w cost ⟨hw, hc⟩ => ⟨hw, hc.trans ?_⟩
  change 10 ^ 5 * (M + 10 ^ 80 * (8 * M + 8 + 1) ^ 17 + 10) ≤
    itCfB itCfDCo itCfDDo M
  unfold itCfB itCfDCo itCfDDo
  omega

end GI.Impl
