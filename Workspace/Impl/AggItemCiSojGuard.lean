import Workspace.Impl.AggItemCiSojSD

/-!
# The finite side-size guard of the first rectangle

Certificate facts give disjoint source sides with at least three left points.
Their raw colors differ, so the target sides read with those colors are disjoint
as well. Thus the program only needs to compare the two side sizes.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle GI.Paper GI.CoherentEntrance GI.PairRefinement Equiv Equiv.Perm

variable {q : ℕ}

private theorem itcs_three_num {q n w : ℕ} (hq : 16 ≤ q)
    (hlarge : (1 / 4 : ℝ) * q ≤ n) (hdom : (3 / 4 : ℝ) * n < w) : 3 ≤ w := by
  have hq' : (16 : ℝ) ≤ q := by exact_mod_cast hq
  have h4 : (4 : ℝ) ≤ n := by linarith only [hlarge, hq']
  have hw : (3 : ℝ) < w := by linarith only [h4, hdom]
  exact_mod_cast hw.le

/-- The good source configuration and the giant-label lower bound supply the
left-side precondition at every certificate. -/
theorem itcs_cert_three (X : PairCfg q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB)
    (hX : X.Good deltaB) (hq : 16 ≤ q) : 3 ≤ (rectW X i₀ cert).card := by
  apply itcs_three_num hq
  · simpa only [deltaB] using hX.large
  · simpa only [rectW, card_idealSide, etaB, colorClass_card] using cert.dominant

/-- The raw colors in a certificate satisfy the supplied object palette bound. -/
theorem itcs_cert_palette (X : PairCfg q) (x₀ : Fin q) {B : ℕ}
    (hcol : itCfColsLe (.pair X x₀) B) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) :
    (certVals X i₀ cert).1 ≤ B ∧ (certVals X i₀ cert).2.1 ≤ B ∧
      (certVals X i₀ cert).2.2 ≤ B :=
  ⟨hcol.1 _ _, hcol.1 _ _, hcol.1 _ _⟩

/-- Disjoint nonempty certificate sides have distinct raw row colors. -/
theorem itcs_cert_colors (X : PairCfg q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) :
    (certVals X i₀ cert).1 ≠ (certVals X i₀ cert).2.1 := by
  intro h
  have hcode : cert.leftColor = cert.rightColor := by
    have hl := cert.leftPoint.property
    have hr := cert.rightPoint.property
    rw [← hl, ← hr]
    exact (X.coloring_eq_iff false false _ _ _ _).2 h
  have hl : cert.leftPoint.val ∈ colorClass X.coloring false i₀ cert.leftColor :=
    (mem_colorClass _ _ _ _ _).2 cert.leftPoint.property
  have hr : cert.leftPoint.val ∈ colorClass X.coloring false i₀ cert.rightColor := by
    rwa [← hcode]
  exact Finset.disjoint_left.1 cert.disjoint hl hr

/-- Reading two distinct raw colors yields disjoint target sides even when the
branch has no target isomorphism. -/
theorem itcs_target_disjoint (Y : PairCfg q) (y₀ : Fin q) {vL vR : ℕ} (hv : vL ≠ vR) :
    Disjoint (Y.fiber.filter fun a => Y.col y₀ a = vL)
      (Y.fiber.filter fun a => Y.col y₀ a = vR) := by
  classical
  apply Finset.disjoint_left.2
  intro a ha hb
  exact hv ((Finset.mem_filter.1 ha).2.symm.trans (Finset.mem_filter.1 hb).2)

/-- Under the cited source hypotheses, the model's rectangle guard has precisely
its two side-size comparisons left to test. -/
theorem itcs_guard_iff (X Y : PairCfg q) (y₀ : Fin q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB)
    (hX : X.Good deltaB) (hq : 16 ≤ q) :
    ((rectW X i₀ cert).card = (Y.fiber.filter fun a => Y.col y₀ a = (certVals X i₀ cert).1).card ∧
      (rectR X i₀ cert).card = (Y.fiber.filter fun a => Y.col y₀ a = (certVals X i₀ cert).2.1).card ∧
      3 ≤ (rectW X i₀ cert).card ∧ Disjoint (rectW X i₀ cert) (rectR X i₀ cert) ∧
      Disjoint (Y.fiber.filter fun a => Y.col y₀ a = (certVals X i₀ cert).1)
        (Y.fiber.filter fun a => Y.col y₀ a = (certVals X i₀ cert).2.1)) ↔
    ((rectW X i₀ cert).card = (Y.fiber.filter fun a => Y.col y₀ a = (certVals X i₀ cert).1).card ∧
      (rectR X i₀ cert).card = (Y.fiber.filter fun a => Y.col y₀ a = (certVals X i₀ cert).2.1).card) := by
  have hd : Disjoint (rectW X i₀ cert) (rectR X i₀ cert) := Finset.disjoint_map _ |>.2 cert.disjoint
  have ht := itcs_target_disjoint Y y₀ (itcs_cert_colors X i₀ cert)
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, itcs_cert_three X i₀ cert hX hq, hd, ht⟩⟩

end GI.Impl
