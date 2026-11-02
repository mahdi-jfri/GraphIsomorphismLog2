import Workspace.Impl.AggItemCiSojFinalSpec
import Workspace.Impl.AggItemCiSojGB
import Workspace.Impl.AggItemCiSojEnvelope
import Workspace.Impl.AggItemCiSojRectStart
import Workspace.Impl.AggItemCiSojStart
import Workspace.Impl.AggItemCiSojAnswersB

/-! # A common polynomial budget for the first-rectangle pipelines -/

namespace GI.Impl

open GI.Lang

/-- Structural table/list operations and parent data fit this fixed envelope. -/
def itcsWrapperC (W : ℕ) : ℕ :=
  10^9*(itSVB W+W+100)^8+2*(2*W+3)^64

/-- The structural envelope is polynomial in the parent input weight. -/
theorem itcs_wrapper_pbu : PBU fun _ W _ => itcsWrapperC W := by
  simp only [itcsWrapperC,itSVB,cmOutB,cmPb,cmNb]
  norm_poly

/-- Alignment is one of the fixed polynomial table operations. -/
theorem itcs_align_cost_pbu : PBU fun _ W _ => itcsAlignC (100*(2*W+4)^2) := by
  simp only [itcsAlignC,itciFC]
  norm_poly

/-- The bounded object interface has polynomial input weight. -/
theorem itcs_object_cost_pbu : PBU fun _ W _ => itCfObjB (2*W+3) (2*(2*W+3)^64) := by
  simp only [itCfObjB]
  norm_poly

/-- Canonical recursive answers have polynomial weight in the physical degree. -/
theorem itcs_answer_weight_pbu : PBU fun _ W _ => ansW W := by
  simp only [ansW,groupW]
  norm_poly

/-- The proved own-cost bounds used by the first-rectangle stages. -/
def itcsCostFns (pf : Prim) (Bc Br : ℕ → ℕ) : List (ℕ → ℕ) :=
  [(Bc),
   (Br),
   (fun W => itcsFrontC (2*W+3) (2*(2*W+3)^64)),
   (fun W => itcsBTC (2*W+3) (2*(2*W+3)^64)),
   (fun W => itcsBalPartC (2*W+3) (2*(2*W+3)^64)),
   (fun W => itcsImpPartC (2*W+3) (2*(2*W+3)^64)),
   (fun W => itcsSideC (2*W+3) (2*(2*W+3)^64)),
   (fun W => itcsGuardC (2*W+3)),
   (fun W => itcsFixProgC (2*W+3)),
   (fun W => itcsMarkC (2*W+3)),
   (fun W => itcsPhysC (W+(2*W+3)+W^2+2)),
   (fun W => itcsSwapLcC (W+(2*W+3)+W^2+2)),
   (fun W => itcsDomC W (2*W+3)),
   (fun W => itcsPullC W (2*W+3) (2*(2*W+3)^64)),
   (fun W => itcsRowsBound pf W),
   (fun W => itcsProcessC pf W),
   (fun W => itcsGroupBuildC (3*(2*W+3)+W^2+10)),
   (fun W => itcsAlignC (100*(2*W+4)^2)),
   (itcsWrapperC),
   (fun W => itCfObjB (2*W+3) (2*(2*W+3)^64)),
   ansW,
   (fun W => itcsFinalC pf W)]

/-- Every listed stage bound is polynomial. The two cited program bounds enter
as hypotheses, without assuming that their bound functions are monotone. -/
theorem itcs_cost_fns_pbu (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) :
    ∀ f ∈ itcsCostFns pf Bc Br, PBU fun _ W _ => f W := by
  intro f hf
  simp only [itcsCostFns,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hBc
  · exact hBr
  · exact itcs_front_pbu
  · exact itcs_bal_test_pbu
  · exact itcs_bal_part_pbu
  · exact itcs_imp_part_pbu
  · exact itcs_side_pbu
  · exact itcs_guard_pbu
  · exact itcs_fix_prog_pbu
  · exact itcs_mark_pbu
  · exact itcs_phys_pbu
  · exact itcs_swap_lc_pbu
  · exact itcs_dom_pbu
  · exact itcs_pull_pbu
  · exact itcs_answers_pbu pf
  · exact itcs_process_pbu pf
  · exact itcs_group_build_pbu
  · exact itcs_align_cost_pbu
  · exact itcs_wrapper_pbu
  · exact itcs_object_cost_pbu
  · exact itcs_answer_weight_pbu
  · exact itcs_final_pbu pf

/-- Finite sums preserve the uniform polynomial bound. -/
theorem itcs_sum_cost_pbu (fs : List (ℕ → ℕ))
    (h : ∀ f ∈ fs, PBU fun _ W _ => f W) :
    PBU fun _ W _ => (fs.map fun f => f W).sum := by
  induction fs with
  | nil => exact PBU.const 0
  | cons f fs ih =>
    exact PBU.add (h f (List.mem_cons_self ..))
      (ih (fun g hg => h g (List.mem_cons_of_mem _ hg)))

/-- One stage's cost is bounded by the sum at that same argument. -/
theorem itcs_sum_cost_member (fs : List (ℕ → ℕ)) {f : ℕ → ℕ} (hf : f ∈ fs) (W : ℕ) :
    f W ≤ (fs.map fun g => g W).sum := by
  induction fs with
  | nil => exact False.elim (List.not_mem_nil hf)
  | cons g gs ih =>
    rcases List.mem_cons.1 hf with rfl | hf
    · exact Nat.le_add_right _ _
    · exact (ih hf).trans (Nat.le_add_left _ _)

/-- A common stage budget before taking a monotone envelope. -/
def itcsStageB (pf : Prim) (Bc Br : ℕ → ℕ) (W : ℕ) : ℕ :=
  ((itcsCostFns pf Bc Br).map fun f => f W).sum

/-- The whole stage budget is polynomial. -/
theorem itcs_stage_pbu (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) :
    PBU fun _ W _ => itcsStageB pf Bc Br W :=
  itcs_sum_cost_pbu _ (itcs_cost_fns_pbu pf Bc Br hBc hBr)

/-- The monotone growth budget used for successive encoding stages. -/
noncomputable def itcsGrow (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) : ℕ → ℕ :=
  itcsEnvelope (itcsStageB pf Bc Br) (itcs_stage_pbu pf Bc Br hBc hBr)

/-- Every listed call at an input below the current budget fits the next budget. -/
theorem itcs_stage_cost_le (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    {f : ℕ → ℕ} (hf : f ∈ itcsCostFns pf Bc Br) {a W : ℕ} (ha : a ≤ W) :
    f a ≤ itcsGrow pf Bc Br hBc hBr W :=
  (itcs_sum_cost_member _ hf a).trans
    (itcs_envelope_of_le (itcsStageB pf Bc Br) (itcs_stage_pbu pf Bc Br hBc hBr) ha)

/-- A fixed budget for the finite sequence of item encoding and answer-processing
stages. The growth is in the cost analysis only. -/
noncomputable def itcsXs (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) (W : ℕ) : ℕ :=
  1000*(itcsGrow pf Bc Br hBc hBr)^[128] (W+100)

/-- The complete fixed-stage budget is uniformly polynomial. -/
theorem itcs_xs_pbu (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) :
    PBU fun _ W _ => itcsXs pf Bc Br hBc hBr W :=
  PBU.smul 1000 (itcs_iter_pbu _ (itcs_stage_pbu pf Bc Br hBc hBr) 128 (PBU.addc PBU.W 100))

end GI.Impl
