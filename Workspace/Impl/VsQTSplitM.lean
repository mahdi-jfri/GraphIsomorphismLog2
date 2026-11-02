import Workspace.Impl.VsQTKeyP
import Workspace.Proved.VsQSplitC

/-!
# The split from the tuple transporter

From the orbit list `L` and the stabilizer generators `ks` that the transporter returns for the
tuple of spans of `P_1, …, P_b`, the transporters `ts = L.map snd`, the group `ks` and the lows
of the partial sums `P_1 + … + P_j` (`j = b - 1, …, 1`) form a correct split of case 2
(`vsQT_splitOK`), given that the partial sums form a strict chain with equal steps.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The bases of the partial sums, from the largest. -/
def vsQTQs (Ps : List (List (List ℕ))) : List (List (List ℕ)) :=
  (List.range (Ps.length - 1)).map fun k => (Ps.take (Ps.length - 1 - k)).flatten

theorem vsQTQs_length (Ps : List (List (List ℕ))) : (vsQTQs Ps).length = Ps.length - 1 := by
  simp [vsQTQs]

/-- A span of a joined list is invariant when the span of each part is. -/
theorem vsQT_flatten_inv {s : VsQSt I} {Xm : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)}
    {Ls : List (List (List ℕ))}
    (h : ∀ P ∈ Ls, (vsWSp I.p (vsQD s) P).map (Matrix.toLin' Xm) = vsWSp I.p (vsQD s) P) :
    ∀ a ∈ vsWSp I.p (vsQD s) Ls.flatten, Xm *ᵥ a ∈ vsWSp I.p (vsQD s) Ls.flatten := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨u, hu, rfl⟩ := hv
    obtain ⟨P, hP, huP⟩ := List.mem_flatten.mp hu
    have h1 : Xm *ᵥ vsWV I.p (vsQD s) u ∈ (vsWSp I.p (vsQD s) P).map (Matrix.toLin' Xm) :=
      ⟨_, vsWV_mem_vsWSp _ huP, by rw [Matrix.toLin'_apply]⟩
    rw [h P hP] at h1
    refine Submodule.span_mono ?_ h1
    rintro w ⟨u', hu', he⟩
    exact ⟨u', List.mem_flatten.mpr ⟨P, hP, hu'⟩, he⟩
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ c hx

/-- **The split from the tuple transporter.** -/
theorem vsQT_splitOK {s : VsQSt I} (hs : VsQStOK s) {E Tm : ℕ} {Ps : List (List (List ℕ))}
    (hPs : ∀ P ∈ Ps, VsWFit I.p (vsQD s) P) (hb : 2 ≤ Ps.length) {e : ℕ}
    (hch : (vsQTLoc s (vsQTQs Ps)).IsChain fun a b => b < a)
    (hdim : ∀ x ∈ List.zipWith (fun (a b : Submodule (ZMod I.p) (Fin (vsQD s) → ZMod I.p)) =>
      Module.finrank (ZMod I.p) a - Module.finrank (ZMod I.p) b)
      (vsQTLoc s (vsQTQs Ps)) (vsQTLoc s (vsQTQs Ps)).tail, x = e)
    {L : List (VsQTup s × Perm (Fin I.n))} {ks : List (Perm (Fin I.n))}
    (hL : VsQOrbL (vsQTAct s) s.hs (Ps.map (vsWSp I.p (vsQD s))) L)
    (hks : gens ks = vsQStabG (vsQTAct_act hs) le_rfl (Ps.map (vsWSp I.p (vsQD s))))
    (hksl : ks.length ≤ I.n ^ 2) (hTm : L.length ≤ Tm) (hE : L.length ≤ (Ps.length + 1) ^ E)
    (hnab : ¬ s.Ab) :
    VsQSplitOK s E Tm (L.map Prod.snd) ks (vsQTLows s (vsQTQs Ps)) := by
  set ys₀ := Ps.map (vsWSp I.p (vsQD s))
  have hα := vsQTAct_act hs
  have hstab : ∀ c ∈ gens ks, c ∈ gens s.hs ∧ vsQTAct s c ys₀ = ys₀ := fun c hc => by
    rw [hks] at hc; exact hc
  refine vsQ_splitC hs (e := e) ?_ hch hdim (by rw [vsQTQs_length]; omega) hksl
    (fun c hc => (hstab c hc).1) ?_ ?_ (by simpa using hTm) ?_ hnab ?_
  · intro Q hQ
    simp only [vsQTQs, List.mem_map] at hQ
    obtain ⟨k, -, rfl⟩ := hQ
    intro u hu
    obtain ⟨P, hP, huP⟩ := List.mem_flatten.mp hu
    exact hPs P (List.mem_of_mem_take hP) u huP
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    exact (hL.pr q hq).1
  · intro h hh
    have hy : vsQTAct s h ys₀ ∈ vsQOrb (vsQTAct s) s.hs ys₀ := ⟨h, hh, rfl⟩
    obtain ⟨q, hq, hq1⟩ := List.mem_map.mp ((hL.mem _).2 hy)
    obtain ⟨hqg, hqa⟩ := hL.pr q hq
    refine ⟨q.2, List.mem_map_of_mem hq, ?_⟩
    rw [hks]
    refine ⟨mul_mem (inv_mem hqg) hh, ?_⟩
    rw [hα.mul _ (inv_mem hqg) _ hh, ← hq1, ← hqa, ← hα.mul _ (inv_mem hqg) _ hqg, inv_mul_cancel, hα.one]
  · intro c hc Q hQ
    have hfix := (vsQTStab_iff c ys₀).1 (hstab c hc).2
    simp only [vsQTQs, List.mem_map] at hQ
    obtain ⟨k, -, rfl⟩ := hQ
    refine vsQT_flatten_inv fun P hP => hfix _ ?_
    exact List.mem_map_of_mem (List.mem_of_mem_take hP)
  · rw [List.length_map, vsQTQs_length]
    have : Ps.length - 1 + 2 = Ps.length + 1 := by omega
    rw [this]; exact hE

end GI.Impl
