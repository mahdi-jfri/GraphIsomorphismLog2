module

public import Workspace.Impl.VsHPsP

@[expose] public section

/-!
# The pieces computed by the program, in the hard case

`VsHHyp.pieces`: for `Ps = vsHPs s ((1 :: as) ++ K)` (what `vsHPs_spec` returns), with `k ≥ 1`,
the facts used by the split of `vsQ_splitC`: the pieces fit, there are `r^k ≥ 2` of them, they
are independent with equal positive dimension and span everything, and the orbit of the tuple
of their spans has at most `(r^k + 1)^278` points.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime] {hs : VsQStOK s}
  {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ys : List (Perm (Fin I.n))} {r : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem VsHHyp.pieces (h : VsHHyp hs as Lb ys r) (hk : 1 ≤ (vsHK s Lb r ys).length) :
    let K := vsHK s Lb r ys
    let Ps := vsHPs s ((1 :: as) ++ K)
    (∀ P ∈ Ps, VsWFit I.p (vsQD s) P) ∧ Ps.length = r ^ K.length ∧ 2 ≤ Ps.length ∧
      (iSupIndep fun i : Fin Ps.length => vsWSp I.p (vsQD s) Ps[i]) ∧
      (∃ e, 0 < e ∧ ∀ i : Fin Ps.length, finrank (ZMod I.p) (vsWSp I.p (vsQD s) Ps[i]) = e) ∧
      (⨆ i : Fin Ps.length, vsWSp I.p (vsQD s) Ps[i]) = ⊤ ∧
      (vsQOrb (vsQTAct s) s.hs (Ps.map (vsWSp I.p (vsQD s)))).ncard ≤ (Ps.length + 1) ^ 278 := by
  intro K Ps
  obtain ⟨hKs, hc, hidx, hP⟩ := h.split
  have hr := h.hard.2.2.2.1
  have hg1 : gens (1 :: as) = gens as := vsH_genGroup_one as
  have has1 : gens (1 :: as) ≤ gens s.hs := hg1 ▸ h.has
  have hc1 : ∀ x ∈ (1 :: as) ++ K, ∀ y ∈ (1 :: as) ++ K,
      vsPRho hs x * vsPRho hs y = vsPRho hs y * vsPRho hs x := by
    intro x hx y hy
    have hx' : x = 1 ∨ x ∈ as ++ K := by simpa using hx
    have hy' : y = 1 ∨ y ∈ as ++ K := by simpa using hy
    rcases hx' with rfl | hx' <;> rcases hy' with rfl | hy'
    · rfl
    · rw [vsPRho_one, one_mul, mul_one]
    · rw [vsPRho_one, one_mul, mul_one]
    · exact hc x hx' y hy'
  have hP1 : VsMPiecesOut (vsPBar hs (gens s.hs)) (vsMAlgE (vsPBar hs (gens (1 :: as))) (vsHEf hs K))
      (r ^ K.length) (vsHBound hs as ys r K.length) := by rw [hg1]; exact hP
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := vsH_split_data hs has1 hKs hc1 hP1
  have hlen : Ps.length = r ^ K.length := h2
  have h2le : 2 ≤ Ps.length := by
    rw [hlen]
    calc 2 ≤ r := hr.two_le
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ K.length := Nat.pow_le_pow_right hr.pos hk
  refine ⟨h1, hlen, h2le, h3, h4, h5, h6.trans ?_⟩
  rw [hlen]
  exact vsH_bound_le hr.two_le hk hidx

end GI.Impl
