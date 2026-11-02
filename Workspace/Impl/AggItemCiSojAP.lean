import Workspace.Impl.AggItemCiSojAlign

/-!
# The fixed rectangle alignment as a program

The colored-partition program already computes the sorted-color alignment and
its parity correction. For the three side colors its overcoset list has one
entry. Reading that entry's representative gives precisely `itcsAlign`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm)

variable {q : ℕ}

/-- The coloring program's nonempty overcoset list uses the fixed even alignment. -/
theorem itcs_align_os {W R W' R' : Finset (Fin q)}
    (hc : ItciCnt (itcsSide W R) (itcsSide W' R')) (h3 : 3 ≤ W.card)
    (E : Subgroup (alternatingGroup (Fin q))) :
    itciOs (itcsSide W R) (itcsSide W' R') (itciOt (itcsSide W R)) E =
      [(⟨itcsAlign W R W' R', itcs_align_sign h3⟩, E,
        itciMs (itcsSide W R) (itciOt (itcsSide W R)))] := by
  classical
  obtain ⟨a, ha⟩ := itcs_side_odd (R := R) h3
  have hal : ∀ a, itcsSide W' R' (itciAl (itcsSide W R) (itcsSide W' R') a) =
      itcsSide W R a := itci_al_apply hc
  simp only [itciOs, if_pos hal, ha]
  by_cases hs : sign (itciAl (itcsSide W R) (itcsSide W' R')) = 1
  · simp only [dif_pos hs, itcsAlign, if_pos hs, ha]
  · have hs' : sign (itciAl (itcsSide W R) (itcsSide W' R') * itciTr (itcsSide W R) a) = 1 := by
      simpa only [itcsAlign, if_neg hs, ha] using itcs_align_sign (R := R) (W' := W') (R' := R') h3
    simp only [dif_neg hs, dif_pos hs', itcsAlign, if_neg hs, ha]

/-- On the two side-color tables, return the fixed alignment as a permutation table. -/
def itcsAlignF (part : ℕ) : Expr :=
  .get (.get (.call part (.var 0)) (.nat 0)) (.nat 0)

/-- Cost of extracting the alignment from the coloring item. -/
def itcsAlignC (M : ℕ) : ℕ := itciFC M + 20 * (1000 * (M + 2) ^ 3 + 1)

/-- The program returns the exact alignment function used by `itcsChoices`. -/
theorem itcs_align_prog {Pg : Program} {Ii : ItciIdx} {fa : ℕ}
    (hi : ItciOk Pg Ii) (hf : Pg.funs[fa]? = some (itcsAlignF Ii.f))
    {W R W' R' : Finset (Fin q)} (hc : ItciCnt (itcsSide W R) (itcsSide W' R'))
    (h3 : 3 ≤ W.card) {M : ℕ}
    (hX : (encFun (itcsSide W R)).wt ≤ M) (hY : (encFun (itcsSide W' R')).wt ≤ M) :
    FunDet Pg fa (.list [encFun (itcsSide W R), encFun (itcsSide W' R')])
      (encPerm (itcsAlign W R W' R')) (itcsAlignC M) := by
  have hq := (itci_q_le_wt (itcsSide W R)).trans hX
  have hp := itci_prog hi (itcsSide W R) (itcsSide W' R') hX hY ⊥
  have ho := itciOV_wt (itciOs_props (itcsSide W R) (itcsSide W' R') ⊥).1
    (itciOs_props (itcsSide W R) (itcsSide W' R') ⊥).2
  rw [itcs_align_os hc h3] at hp ho
  let ms := itciMs (itcsSide W R) (itciOt (itcsSide W R))
  have hshape : itciOV [(⟨itcsAlign W R W' R', itcs_align_sign h3⟩, ⊥, ms)] =
      .list [lcOv (itcsAlign W R W' R') ms] := rfl
  rw [hshape] at hp ho
  have hpair : (lcOv (itcsAlign W R W' R') ms).wt ≤ 200 * (q + 1) ^ 3 :=
    (st_wt_mem (List.mem_cons_self ..)).trans ho
  have hal : (encPerm (itcsAlign W R W' R')).wt ≤ 200 * (q + 1) ^ 3 :=
    (st_wt_mem (List.mem_cons_self ..)).trans hpair
  have hpow : (q + 1) ^ 3 ≤ (M + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h1 : M + 2 ≤ (M + 2) ^ 3 := Nat.le_self_pow (by omega) _
  let Bw := 1000 * (M + 2) ^ 3
  have hin : (Val.list [encFun (itcsSide W R), encFun (itcsSide W' R')]).wt ≤ Bw := by
    have := wt_list2_le (encFun (itcsSide W R)) (encFun (itcsSide W' R'))
    dsimp only [Bw]; omega
  have g0 := StDC.var' (i := 0) (P := Pg) (env := [.list [encFun (itcsSide W R),
    encFun (itcsSide W' R')]]) (W := Bw) rfl hin
  have gcall := StDC.call (cb := itciFC M) g0 hp (by dsimp only [Bw]; omega)
  have gpair := StDC.get gcall (StDC.nat 0 (by dsimp only [Bw]; omega))
    (v := lcOv (itcsAlign W R W' R') ms) rfl (by dsimp only [Bw]; omega)
  have gres := StDC.get gpair (StDC.nat 0 (by dsimp only [Bw]; omega))
    (v := encPerm (itcsAlign W R W' R')) rfl (by dsimp only [Bw]; omega)
  exact StDC.funDet hf gres (by unfold itcsAlignC; dsimp only [Bw]; omega)

end GI.Impl
