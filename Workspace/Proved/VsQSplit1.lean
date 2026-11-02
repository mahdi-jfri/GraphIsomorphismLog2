import Workspace.Impl.VsQDrvDefs
import Workspace.Proved.VsQLoc
import Workspace.Proved.VsWEigCount

/-!
# Chain splits from a local invariant subspace

Let `s` be a valid state with local dimension `D`. If a local subspace `U = span us` of `𝔽_p^D`
is neither `0` nor everything and is mapped into itself by the local matrices of the generators,
then its lift `W' + comb U` lies strictly between `W'` and `W` and is `H`-invariant. So the
chain `W > W' + comb U > W'` with the single coset representative `1` is a correct split
(`vsQ_split1`).

* `vsWLift_fit`: lifts are stored vectors of length `d`.
* `vsQLam_inv_gens`: invariance under the generators gives invariance under `H`.
* `vsQ_split1`: the split.
-/

open Matrix

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv

variable {I : VecStabInst}

theorem vsWLift_fit {p : ℕ} (hp : 0 < p) {d : ℕ} {ws' : List (List ℕ)} (h' : VsWFit p d ws')
    (cs us : List (List ℕ)) : VsWFit p d (vsWLift p d ws' cs us) := by
  refine vsWFit_append h' fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨u, -, rfl⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [vsFRowMul]
    exact vsFMulAcc_foldl_lt hp _ _ (fun y hy => by simp [vsWZ] at hy; omega)
  · rw [vsFRowMul, vsFMulAcc_foldl_length]
    simp [vsWZ]

section

variable {s : VsQSt I} (hs : VsQStOK s)
include hs

/-- **Invariance under the generators gives invariance under the group.** The inverse case uses
that an injective linear map of the finite space `U` into itself is onto. -/
theorem vsQLam_inv_gens {U : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)}
    (hU : ∀ g ∈ s.hs, ∀ a ∈ U, (vsQLam s g).mulVec a ∈ U) :
    ∀ h ∈ gens s.hs, ∀ a ∈ U, (vsQLam s h).mulVec a ∈ U := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem g hg => exact hU g hg
  | one => intro a ha; rw [vsQLam_one hs, one_mulVec]; exact ha
  | mul g k hg hk ihg ihk =>
    intro a ha
    rw [vsQLam_mul hs hg hk, ← mulVec_mulVec]
    exact ihg _ (ihk a ha)
  | inv g hg ih =>
    intro a ha
    have hgi : vsQLam s g⁻¹ * vsQLam s g = 1 := by
      rw [← vsQLam_mul hs (inv_mem hg) hg, inv_mul_cancel, vsQLam_one hs]
    let f : U →ₗ[ZMod I.p] U := (Matrix.toLin' (vsQLam s g)).restrict fun b hb => by
      rw [Matrix.toLin'_apply]; exact ih b hb
    have hinj : Function.Injective f := by
      intro b c hbc
      have e : (vsQLam s g).mulVec b = (vsQLam s g).mulVec c := by
        have := congrArg Subtype.val hbc
        simpa [f, Matrix.toLin'_apply] using this
      have e2 := congrArg (vsQLam s g⁻¹).mulVec e
      rw [mulVec_mulVec, mulVec_mulVec, hgi, one_mulVec, one_mulVec] at e2
      exact Subtype.ext e2
    obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨a, ha⟩
    have e : (vsQLam s g).mulVec b = a := by
      have := congrArg Subtype.val hb
      simpa [f, Matrix.toLin'_apply] using this
    rw [← e, mulVec_mulVec, hgi, one_mulVec]
    exact b.2

theorem vsQ_bas_lift_sp (us : List (List ℕ)) :
    vsQSp I (vsWBas I.p (vsWLift I.p I.d s.ws' (vsQCs s) us)) =
      vsQLift s (vsWSp I.p (vsQD s) us) := by
  have hc : VsWFit I.p I.d (vsQCs s) := vsWComp_fit I.prime.pos hs.fit' hs.fit
  change vsWSp I.p I.d _ = _
  rw [vsWBas_span I.prime (vsWLift_fit I.prime.pos hs.fit' _ _), vsWLift_span hc]
  rfl

/-- **A chain split from a local invariant subspace.** -/
theorem vsQ_split1 {E Tm : ℕ} (hTm : 1 ≤ Tm) {us : List (List ℕ)}
    (hbot : vsWSp I.p (vsQD s) us ≠ ⊥) (htop : vsWSp I.p (vsQD s) us ≠ ⊤)
    (hU : ∀ g ∈ s.hs, ∀ a ∈ vsWSp I.p (vsQD s) us,
      (vsQLam s g).mulVec a ∈ vsWSp I.p (vsQD s) us) :
    VsQSplitOK s E Tm [1] s.hs [vsWBas I.p (vsWLift I.p I.d s.ws' (vsQCs s) us), s.ws'] := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  have hsp := vsQ_bas_lift_sp hs us
  have hfit := vsWBas_fit I.prime.pos (vsWLift_fit I.prime.pos hs.fit' (vsQCs s) us)
  refine ⟨hs.hsl, le_rfl, ?_, ?_, by simpa using hTm, ?_, List.cons_ne_nil _ _, rfl, ?_, ?_,
    Or.inl ⟨rfl, by simp⟩⟩
  · intro t ht
    rw [List.mem_singleton] at ht
    rw [ht]; exact one_mem _
  · intro h hh
    exact ⟨1, List.mem_singleton_self _, by simpa using hh⟩
  · have h1 := vsQLift_lt hs (bot_lt_iff_ne_bot.mpr hbot)
    have h2 := vsQLift_lt hs (lt_top_iff_ne_top.mpr htop)
    rw [vsQLift_bot hs] at h1
    rw [vsQLift_top hs] at h2
    simp only [VsQChain, List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨hsp ▸ h2, hsp ▸ h1⟩
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · refine ⟨hfit, ?_⟩
      rw [vsWBas_length I.prime (vsWLift_fit I.prime.pos hs.fit' (vsQCs s) us)]
      exact (Submodule.finrank_le _).trans (by simp)
    · exact ⟨hs.fit', hs.wl'⟩
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · rw [hsp]; exact vsQLift_inv hs le_rfl (vsQLam_inv_gens hs hU)
    · exact hs.prob.invW'

end

end GI.Proved
