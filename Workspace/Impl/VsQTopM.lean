import Workspace.Impl.VsQAna
import Workspace.Impl.VsQDrv

/-!
# The initial state

The vector stabilizer of `v` is the answer of the problem with `H = G`, `W = 𝔽_p^d` (the basis
`vsWId d`), `W' = 0` and `x = y = v`.

* `vsQ0`: the initial state, with the generators of `G` cut to at most `n²` (`keepList`).
* `vsQ0_ok`: it is valid.
* `vsQ0_stab`: its stabilizer is `C_G(v)`.
* `vsQ0_sol`: `1` is a solution, so the answer is never empty.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable (I : VecStabInst)

/-- The initial state. -/
noncomputable def vsQ0 : VsQSt I :=
  ⟨keepList I.gs, [], vsWId I.d, vsQVec I.v, vsQVec I.v⟩

variable {I}

theorem vsQ0_fitv : VsWFit I.p I.d [vsQVec I.v] := by
  intro u hu
  rw [List.mem_singleton] at hu
  subst hu
  refine ⟨fun y hy => ?_, by simp [vsQVec]⟩
  simp only [vsQVec, List.mem_map, List.mem_finRange, true_and] at hy
  obtain ⟨i, rfl⟩ := hy
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  exact ZMod.val_lt _

theorem vsQ0_ok : VsQStOK (vsQ0 I) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hG : gens (vsQ0 I).hs = gens I.gs := gens_keepList _
  have htop : vsQSp I (vsQ0 I).ws = ⊤ := vsWId_span I.d
  have hbot : vsQSp I (vsQ0 I).ws' = ⊥ := by simp [vsQ0, vsQSp, vsWSp]
  refine ⟨⟨by rw [hG], ?_, ?_, ?_, ?_, ?_⟩, length_keepList_le _, vsWId_fit I.prime.one_lt _, ?_,
    by simp [vsQ0, vsWId], by simp [vsQ0], vsQ0_fitv, vsQ0_fitv⟩
  · rw [hbot]; exact bot_le
  · intro h _ w _; rw [htop]; trivial
  · intro h _ w hw; rw [hbot] at hw ⊢; rw [(Submodule.mem_bot _).1 hw, mulVec_zero]; exact Submodule.zero_mem _
  · intro h _; rw [htop]; trivial
  · rw [htop]; trivial
  · intro u hu; simp [vsQ0] at hu

theorem vsQ0_stab :
    vsQStab (gens (vsQ0 I).hs) (vsQSp I (vsQ0 I).ws') (vsWV I.p I.d (vsQ0 I).x) vsQ0_ok.prob.le
      vsQ0_ok.prob.invW' = (vecStab I).map (gens I.gs).subtype := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hG : gens (vsQ0 I).hs = gens I.gs := gens_keepList _
  have hbot : vsQSp I (vsQ0 I).ws' = ⊥ := by simp [vsQ0, vsQSp, vsWSp]
  have hx : vsWV I.p I.d (vsQ0 I).x = I.v := vsWV_vsQVec I.v
  ext h
  rw [mem_vsQStab, hbot, hx, Submodule.mem_bot, sub_eq_zero, Subgroup.mem_map]
  constructor
  · rintro ⟨hh, he⟩
    rw [hG] at hh
    refine ⟨⟨h, hh⟩, ?_, rfl⟩
    show (I.φ ⟨h, hh⟩).val.mulVec I.v = I.v
    have : vsQPhi I h = (I.φ ⟨h, hh⟩ : Matrix (Fin I.d) (Fin I.d) (ZMod I.p)) := by
      rw [vsQPhi, dif_pos hh]
    rw [← this]; exact he
  · rintro ⟨⟨g, hg⟩, hgs, rfl⟩
    refine ⟨by rw [hG]; exact hg, ?_⟩
    have : vsQPhi I g = (I.φ ⟨g, hg⟩ : Matrix (Fin I.d) (Fin I.d) (ZMod I.p)) := by
      rw [vsQPhi, dif_pos hg]
    show vsQPhi I g *ᵥ I.v = I.v
    rw [this]; exact hgs

theorem vsQ0_sol : (1 : Perm (Fin I.n)) ∈ vsQSol I (gens (vsQ0 I).hs) (vsQSp I (vsQ0 I).ws')
    (vsWV I.p I.d (vsQ0 I).x) (vsWV I.p I.d (vsQ0 I).y) :=
  ⟨one_mem _, by simp [vsQPhi_one, vsQ0]⟩

end GI.Impl
