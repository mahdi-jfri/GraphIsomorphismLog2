import Workspace.Impl.GenNormStep

/-! # The recursive induction hypothesis applies to the computed children -/
namespace GI.Impl
open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

/-- The measured induction hypothesis supplies exactly the two recursive calls used by
normalization. The giant input has the standard label weight and the exact child labels. -/
theorem normChild_fromIH (R : Rest) {Pg : Program} {F : Funs}
    {Ω C : Type} [Finite Ω] {n : ℕ} {en : Ω ≃ Fin n} {cc : C → ℕ} {S : State Ω C}
    (hcc : Function.Injective cc) (hgood : Good P₀ .cont S)
    (ih : R.iface.IH Pg F .cont S) (hs : (S.N : ℝ) ^ P₀.γ < S.size) (htr : S.Transitive)
    (Q : PrimitiveQuotient S) (nc : Q.NormChoice)
    (hq : P₀.q₀ < (Q.normalizationOf nc).q) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (b : Bool) (hmode : ∀ j,
      (normMode b = .cont ∧ ¬ ((Q.normAboveOf nc htr hq hkc hkl).child j).Transitive) ∨
      (normMode b = .giant ∧ ((Q.normAboveOf nc htr hq hkc hkl).child j).Transitive))
    {lv : Val} (hL : ∀ j, LabValStd en ((Q.normAboveOf nc htr hq hkc hkl).child j) lv
      ((Q.normAboveOf nc htr hq hkc hkl).childLabels j))
    (j : Fin (Q.normAboveOf nc htr hq hkc hkl).I.k) {val : Val}
    (hcan : Canon en cc val ((Q.normAboveOf nc htr hq hkc hkl).child j)) :
    FunAll Pg (F.get (normMode b)) (if b then .list [val, lv] else val)
      (R.iface.Post (normMode b) ((Q.normAboveOf nc htr hq hkc hkl).child j) en
        (if b then .list [val, lv] else val)) := by
  let NN := Q.normAboveOf nc htr hq hkc hkl
  cases b with
  | false =>
    have ht : ¬ (NN.child j).Transitive := by
      rcases hmode j with h | h
      · exact h.2
      · simp [normMode] at h
    exact ih .cont (NN.child j) (normChild_good_cont NN hgood j)
      (normChild_mlt_cont NN htr j ht) n en cc hcc val hcan
  | true =>
    have ht : (NN.child j).Transitive := by
      rcases hmode j with h | h
      · simp [normMode] at h
      · exact h.2
    have hg : Good P₀ .giant (NN.child j) := by
      obtain ⟨hN, hsz, htr, hlarge, hhi, L, hLeq, hqL⟩ := normChild_good_giant NN hgood hs j ht
      exact ⟨hN, hsz, htr, hlarge, hhi, L, hqL⟩
    apply ih .giant (NN.child j) hg
      (normChild_mlt_giant P₀_terminating.κ_five NN htr j ht) n en cc hcc
        (.list [val, lv])
    exact ⟨val, lv, NN.childLabels j, rfl, hcan, hL j, NN.q_large,
      (hL j).wt_le hcan.small'.1⟩

end GI.Impl
