module

public import Workspace.Impl.AggRectRepT6

@[expose] public section

/-!
# The main function of the representation program

`rcR_main_run`: the main function runs the four stages in turn; stage 3 is the single-label
branch or the pair branch, chosen by the bit of stage 2. The cost is the sum of the stage costs
and a linear term.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

section Main

variable {P : Program} {I : RcRIdx}

/-- **The main function**, from the four stages. -/
theorem rcR_main_run (ok : RcROk P I) {In : Val} {W C1 C2 C3 C4 : ℕ} {Q1 : Val → Prop}
    {Q2 : Val → Val → Prop} {Q3 : Val → Val → Val → Prop} {Q : Val → Prop}
    (h1 : CpFB P I.st1 In W C1 Q1)
    (h2 : ∀ R1, Q1 R1 → R1.wt ≤ W → CpFB P I.st2 (.list [In, R1]) W C2 (Q2 R1))
    (h3 : ∀ R1 R2, Q1 R1 → Q2 R1 R2 → R1.wt ≤ W → R2.wt ≤ W → ∃ (vs : List Val) (b : ℕ),
      R2 = .list vs ∧ vs[4]? = some (.nat b) ∧
      (b ≠ 0 → CpFB P I.carF (.list [In, R2]) W C3 (Q3 R1 R2)) ∧
      (b = 0 → CpFB P I.pairF (.list [In, R2]) W C3 (Q3 R1 R2)))
    (h4 : ∀ R1 R2 R3, Q1 R1 → Q2 R1 R2 → Q3 R1 R2 R3 → R1.wt ≤ W → R2.wt ≤ W → R3.wt ≤ W →
      CpFB P I.st4 (.list [In, R1, R2, R3]) W C4 Q)
    (hIn : In.wt ≤ W) (hw2 : ∀ R1, Q1 R1 → (Val.list [In, R1]).wt ≤ W)
    (hw3 : ∀ R1 R2, Q1 R1 → Q2 R1 R2 → (Val.list [In, R2]).wt ≤ W)
    (hw4 : ∀ R1 R2 R3, Q1 R1 → Q2 R1 R2 → Q3 R1 R2 R3 → (Val.list [In, R1, R2, R3]).wt ≤ W) :
    CpFB P I.main In W (C1 + C2 + 2 * C3 + C4 + 100 * W + 100) Q := by
  refine CpFB.intro ok.main (rcR_letC (Cb := C2 + 2 * C3 + C4 + 70 * W + 90)
    (rcR_callC (Cb := C1) (rcR_detC (rcRDW.var (P := P) (env := [In]) (i := 0) rfl hIn)
      (C := W + 1) le_rfl (Q := (· = In)) rfl) (fun v hv _ => by subst hv; exact h1) le_rfl)
    ?_ (by omega))
  intro R1 hR1 hR1w
  refine rcR_letC (Cb := 2 * C3 + C4 + 50 * W + 60)
    (rcR_callC (Cb := C2) (rcR_detC (rcRDW.mk2 (rcRDW.var (P := P) (env := [In, R1]) (i := 0) rfl
      hIn) (rcRDW.var (i := 1) rfl hR1w) (hw2 R1 hR1)) (C := 5 * W + 10) (by omega)
      (Q := (· = .list [In, R1])) rfl) (fun v hv _ => by subst hv; exact h2 R1 hR1 hR1w) le_rfl)
    ?_ (by omega)
  intro R2 hR2 hR2w
  obtain ⟨vs, b, rfl, hb, hcar, hpair⟩ := h3 R1 R2 hR1 hR2 hR1w hR2w
  have dmk := rcRDW.mk2 (rcRDW.var (P := P) (env := [In, R1, .list vs]) (i := 0) rfl hIn)
    (rcRDW.var (i := 2) rfl hR2w) (hw3 R1 _ hR1 hR2)
  have dc := rcRDW.get (rcRDW.var (P := P) (env := [In, R1, .list vs]) (i := 2) rfl hR2w) hb
  have hW1 : 1 ≤ W := by
    have := wt_le_wt_list (List.mem_of_getElem? hb); omega
  refine rcR_letC (Cb := C4 + 20 * W + 30) ((CpEB.ite dc.1
    (fun hb0 => rcR_callC (Cb := C3) (rcR_detC dmk (C := 5 * W + 10) (by omega)
      (Q := (· = .list [In, .list vs])) rfl) (fun v hv _ => by subst hv; exact hcar hb0) le_rfl)
    (fun hb0 => rcR_callC (Cb := C3) (rcR_detC dmk (C := 5 * W + 10) (by omega)
      (Q := (· = .list [In, .list vs])) rfl) (fun v hv _ => by subst hv; exact hpair hb0) le_rfl)
    ).mono (C' := 2 * C3 + 15 * W + 40) (by omega) fun _ h => h) ?_ (by omega)
  intro R3 hR3 hR3w
  have d4 := rcRDW.mk4 (rcRDW.var (P := P) (env := [In, R1, .list vs, R3]) (i := 0) rfl hIn)
    (rcRDW.var (i := 1) rfl hR1w) (rcRDW.var (i := 2) rfl hR2w) (rcRDW.var (i := 3) rfl hR3w)
    (hw4 R1 _ R3 hR1 hR2 hR3)
  exact rcR_callC (Cb := C4) (rcR_detC d4 (C := 9 * W + 20) (by omega)
    (Q := (· = .list [In, R1, .list vs, R3])) rfl)
    (fun v hv _ => by subst hv; exact h4 R1 _ R3 hR1 hR2 hR3 hR1w hR2w hR3w) (by omega)

end Main

end GI.Impl
