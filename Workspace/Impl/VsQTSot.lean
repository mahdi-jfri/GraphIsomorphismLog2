import Workspace.Impl.VsQTActP

/-!
# The small orbit transporter on tuples of local subspaces

* `vsQTS`: the size bound for the transporter.
* `vsQT_sotHyp`: the hypotheses of `vsQSot_spec` for the action `vsQTAct` of `H` on a tuple of
  at most `S` local subspaces whose orbit has at most `B` points.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The size bound of the tuple transporter. -/
def vsQTS (S B : ℕ) : ℕ := 10 ^ 7 * (S ^ 3 + 1) ^ 2 + B

theorem vsQTAct_length {s : VsQSt I} (h : Perm (Fin I.n)) (ys : VsQTup s) :
    (vsQTAct s h ys).length = ys.length := List.length_map _

theorem vsQTOrb_length {s : VsQSt I} {gs : List (Perm (Fin I.n))} {ys₀ ys : VsQTup s}
    (hy : ys ∈ vsQOrb (vsQTAct s) gs ys₀) : ys.length = ys₀.length := by
  obtain ⟨g, -, rfl⟩ := hy
  exact vsQTAct_length g ys₀

theorem vsQTKey_wt {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) {ys : VsQTup s}
    (hb : ys.length ≤ S) : (natList (0 :: vsQTKey ys)).wt ≤ 20 * (S ^ 3 + 1) ^ 2 := by
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  have hpS := hS.p
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
  have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hkl := vsQTKey_length ys
  have hkN : (vsQTKey ys).length ≤ S ^ 3 := by
    rw [hkl]
    have : ys.length * (vsQD s * vsQD s + 1) ≤ S * (S * S) := Nat.mul_le_mul hb (by
      have h1 : vsQD s + 1 ≤ S := by omega
      have h2 := Nat.mul_le_mul h1 h1
      have e : (vsQD s + 1) * (vsQD s + 1) = vsQD s * vsQD s + 2 * vsQD s + 1 := by ring
      omega)
    have e : S * (S * S) = S ^ 3 := by ring
    omega
  have := wt_natList_le_sq (B := S ^ 3 + 1) (xs := 0 :: vsQTKey ys) (fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · omega
    · simp only [vsQTKey, List.mem_flatMap, vsQTKeyM, List.mem_cons] at hy
      obtain ⟨U, -, hy⟩ := hy
      rcases hy with rfl | hy
      · omega
      · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
        have := vsWKey_fit I.prime.one_lt (d := vsQD s) (vsQTBas U)
        exact ((this r hr).1 y hy).le.trans (by omega)) (by simp; omega)
  have h1 : (S ^ 3 + 1 + 1) ^ 2 ≤ (2 * (S ^ 3 + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e : (2 * (S ^ 3 + 1)) ^ 2 = 4 * (S ^ 3 + 1) ^ 2 := by ring
  omega

/-- **The transporter hypotheses for tuples.** -/
theorem vsQT_sotHyp {P : Program} {fa itm loc phi tl chk mp fI tl' chk' ker img key cat appd Cφ S Tm B : ℕ}
    (H : VsQTActAt P fa itm loc phi tl chk mp fI tl' chk' ker img key cat appd)
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) {ys₀ : VsQTup s} (hb : ys₀.length ≤ S)
    (hB : (vsQOrb (vsQTAct s) s.hs ys₀).ncard ≤ B) :
    VsQSotHyp P fa (gens s.hs) (vsQTAct s) s.hs vsQTKey ys₀ (vsQTCtx s) (vsQTS S B)
      (Cφ + 10 ^ 15 * (S ^ 3 + 1) ^ 7) B := by
  have hS1 := hS.one_le
  have hnS := hS.n
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
  have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hq : S ^ 3 + 1 ≤ (S ^ 3 + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  exact
    { hk := vsQTKey_injective
      hK := le_rfl
      hn := by unfold vsQTS; omega
      hm := by
        have := hs.hsl
        have : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
        unfold vsQTS; omega
      hac := by
        have w1 := wt_list2_le (vsQGam I) (vsWFrVal I.p I.d s.ws' (vsQCs s))
        have w2 := wt_list3_le (.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)]) (.nat I.p) (.nat (vsQD s))
        have := wt_nat_le I.p; have := wt_nat_le (vsQD s)
        have := vsQ_wt_fr hS hs; have := hS.g; have := hS.p; have := vsQD_le hs; have := hS.d
        show (Val.list _).wt ≤ _
        unfold vsQTS; omega
      hkey := fun y hy => by
        have := vsQTKey_wt hS hs (ys := y) (by rw [vsQTOrb_length hy]; exact hb)
        unfold vsQTS; omega
      hfa := fun g hg y hy => vsQTAct_spec H hphi hS hs (Subgroup.subset_closure hg)
        (by rw [vsQTOrb_length hy]; exact hb)
      hBS := by unfold vsQTS; omega
      hB := hB }

end GI.Impl
