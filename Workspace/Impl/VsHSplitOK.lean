import Workspace.Impl.VsHQ8Two
import Workspace.Impl.VsQTSplitM

/-!
# The split of the hard case is correct

From an orbit list `L` and stabilizer `⟨ks⟩` of the tuple of pieces (what the spine's wrapper
returns), the split by the chain of partial sums is correct, case 2 with `E = 278`:
`vsH_splitOK_of` in general, `VsHHyp.splitOK` for `k ≥ 1` and `vsH_q8two_splitOK` for the
second `Q₈`.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I} [Fact I.p.Prime]

/-- **The split from the pieces facts.** -/
theorem vsH_splitOK_of (hs : VsQStOK s) {Ps : List (List (List ℕ))} {Tm : ℕ}
    (hPs : ∀ P ∈ Ps, VsWFit I.p (vsQD s) P) (hb : 2 ≤ Ps.length)
    (hind : iSupIndep fun i : Fin Ps.length => vsWSp I.p (vsQD s) Ps[i])
    (hdim : ∃ e, 0 < e ∧ ∀ i : Fin Ps.length, finrank (ZMod I.p) (vsWSp I.p (vsQD s) Ps[i]) = e)
    (htop : (⨆ i : Fin Ps.length, vsWSp I.p (vsQD s) Ps[i]) = ⊤)
    (horb : (vsQOrb (vsQTAct s) s.hs (Ps.map (vsWSp I.p (vsQD s)))).ncard ≤ (Ps.length + 1) ^ 278)
    {L : List (VsQTup s × Perm (Fin I.n))} {ks : List (Perm (Fin I.n))}
    (hL : VsQOrbL (vsQTAct s) s.hs (Ps.map (vsWSp I.p (vsQD s))) L)
    (hks : gens ks = vsQStabG (vsQTAct_act hs) le_rfl (Ps.map (vsWSp I.p (vsQD s))))
    (hksl : ks.length ≤ I.n ^ 2) (hTm : L.length ≤ Tm) (hnab : ¬ s.Ab) :
    VsQSplitOK s 278 Tm (L.map Prod.snd) ks (vsQTLows s (vsQTQs Ps)) := by
  obtain ⟨e, he, hde⟩ := hdim
  obtain ⟨hch, hst⟩ := vsH_chain (p := I.p) (D := vsQD s) hind hde he htop (by omega)
  exact vsQT_splitOK hs hPs hb hch hst hL hks hksl hTm (hL.length_eq ▸ horb) hnab

variable {hs : VsQStOK s} {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
  {ys : List (Perm (Fin I.n))} {r : ℕ}

/-- **The hard case with `k ≥ 1`.** -/
theorem VsHHyp.splitOK (h : VsHHyp hs as Lb ys r) (hk : 1 ≤ (vsHK s Lb r ys).length) {Tm : ℕ}
    {L : List (VsQTup s × Perm (Fin I.n))} {ks : List (Perm (Fin I.n))}
    (hL : VsQOrbL (vsQTAct s) s.hs ((vsHPs s ((1 :: as) ++ vsHK s Lb r ys)).map
      (vsWSp I.p (vsQD s))) L)
    (hks : gens ks = vsQStabG (vsQTAct_act hs) le_rfl
      ((vsHPs s ((1 :: as) ++ vsHK s Lb r ys)).map (vsWSp I.p (vsQD s))))
    (hksl : ks.length ≤ I.n ^ 2) (hTm : L.length ≤ Tm) (hnab : ¬ s.Ab) :
    VsQSplitOK s 278 Tm (L.map Prod.snd) ks (vsQTLows s (vsQTQs (vsHPs s ((1 :: as) ++ vsHK s Lb r ys)))) := by
  obtain ⟨h1, -, h2, h3, h4, h5, h6⟩ := h.pieces hk
  exact vsH_splitOK_of hs h1 h2 h3 h4 h5 h6 hL hks hksl hTm hnab

/-- **The second `Q₈`.** -/
theorem vsH_q8two_splitOK (hs : VsQStOK s) {as : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs)
    {Y Y' : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ}
    (hY : VsMHard (vsPBar hs (gens s.hs)) (vsPBar hs (gens as)) Y 2)
    (hYi : VsMIso (vsPBar hs (gens as)) Y 2 (Fin.elim0 : Fin 0 → _))
    (hY' : VsMHard (vsPBar hs (gens s.hs)) (vsPBar hs (gens as)) Y' 2)
    (hYi' : VsMIso (vsPBar hs (gens as)) Y' 2 (Fin.elim0 : Fin 0 → _))
    (hYY : Y' ≤ Subgroup.centralizer (Y : Set _))
    {y y' : Perm (Fin I.n)} (hy : y ∈ gens s.hs) (hy' : y' ∈ gens s.hs)
    (hyY : vsPRho hs y ∈ Y) (hyS : vsPRho hs y ∉ vsMScal (vsPBar hs (gens as)))
    (hyY' : vsPRho hs y' ∈ Y') (hyS' : vsPRho hs y' ∉ vsMScal (vsPBar hs (gens as))) {Tm : ℕ}
    {L : List (VsQTup s × Perm (Fin I.n))} {ks : List (Perm (Fin I.n))}
    (hL : VsQOrbL (vsQTAct s) s.hs ((vsHPs s ((1 :: as) ++ [y * y'])).map (vsWSp I.p (vsQD s))) L)
    (hks : gens ks = vsQStabG (vsQTAct_act hs) le_rfl
      ((vsHPs s ((1 :: as) ++ [y * y'])).map (vsWSp I.p (vsQD s))))
    (hksl : ks.length ≤ I.n ^ 2) (hTm : L.length ≤ Tm) (hnab : ¬ s.Ab) :
    VsQSplitOK s 278 Tm (L.map Prod.snd) ks (vsQTLows s (vsQTQs (vsHPs s ((1 :: as) ++ [y * y'])))) ∧
      L.length ≤ 72 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := vsH_q8two_pieces hs has hY hYi hY' hYi' hYY hy hy' hyY hyS
    hyY' hyS'
  refine ⟨vsH_splitOK_of hs h1 (by omega) h3 h4 h5 (h6.trans ?_) hL hks hksl hTm hnab,
    hL.length_eq ▸ h6⟩
  rw [h2]
  calc 72 ≤ 3 ^ 4 := by norm_num
    _ ≤ (2 + 1) ^ 278 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

end GI.Impl
