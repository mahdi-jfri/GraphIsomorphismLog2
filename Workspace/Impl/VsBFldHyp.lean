module

public import Workspace.Impl.VsBFldBP
public import Workspace.Impl.VsBChain
public import Workspace.Proved.VsBFldC

@[expose] public section

/-!
# The transporter hypotheses of the two chains

The size bound of the transporters of both chains is `vsBS2 S = 10^7 S^3`; generator lists
have at most `n² + 2` elements.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The size bound of the transporters of the field line. -/
def vsBS2 (S : ℕ) : ℕ := 10 ^ 7 * S ^ 3

section

variable {P : Program} {phi Cφ S Tm : ℕ}
  (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
    (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
  (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
include hS hs

omit hs in
theorem vsB_S2 {Gl : ℕ} (hGl : Gl ≤ I.n ^ 2 + 2) : Gl + 1 ≤ vsBS2 S ∧ I.n + 2 ≤ vsBS2 S := by
  have hS1 := hS.one_le
  have hn := hS.n
  have h2 : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  have h3 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS1
  have : I.n ≤ S ^ 3 := by have := Nat.le_self_pow (n := 3) (by norm_num) S; omega
  unfold vsBS2
  constructor <;> omega

include hphi in
/-- The transporter hypotheses of stage `p` of the λ-chain. -/
theorem vsB_sotHypA {bA : ℕ} (hA : P.HasAt bA (vsBAFuns bA phi)) (hab : s.Ab) (hD : 1 ≤ vsQD s)
    (hdom : VsBDom s) {pp : ℕ} (hpp : pp ∈ vsBPs I.n) {gs : List (Perm (Fin I.n))}
    (hgs : genGroup gs ≤ gens s.hs) (hgl : gs.length ≤ I.n ^ 2 + 2) :
    VsQSotHyp P (bA + 1) (gens s.hs) (vsBAp s pp) gs vsQVec (vsBe0 s hD)
      (.list [vsBCtxA s hD, .nat pp]) (vsBS2 S) (Cφ + 10 ^ 18 * S ^ 7) (I.n + 1) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hn := hS.n
  have hpp' : pp + 2 ≤ 4 * S := by
    have := List.mem_range.mp hpp
    have : max I.n 2 ≤ S + 1 := by omega
    omega
  have hS2 := vsB_S2 hS hgl
  have h13 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  exact
    { hk := vsQVec_injective
      hK := hgs
      hn := by omega
      hm := hS2.1
      hac := by
        have w := wt_list2_le (vsBCtxA s hD) (.nat pp)
        have := vsB_wt_ctxA hS hs hD
        have := wt_nat_le pp
        unfold vsBS2; omega
      hkey := fun y _ => by
        have := (vsB_wt_vecA hS hs y).2
        unfold vsBS2; omega
      hfa := fun g hg y _ =>
        vsB_actA_spec hA hphi hS hs hD hpp' (hgs (Subgroup.subset_closure hg)) y
      hBS := by omega
      hB := vsB_orb_le hs hab hD hdom (by omega) hgs }

include hphi in
/-- The transporter hypotheses of stage `j` of the translation chain. -/
theorem vsB_sotHypB {bB : ℕ} (hB : P.HasAt bB (vsBBFuns bB phi)) {j : ℕ} (hj : j ∈ List.range (vsQD s))
    {gs : List (Perm (Fin I.n))} (hgs : genGroup gs ≤ vsBH1 hs) (hgl : gs.length ≤ I.n ^ 2 + 2) :
    VsQSotHyp P bB (vsBH1 hs) (vsBAj s j) gs vsBKeyB 0
      (.list [vsBCtxB s, .nat j]) (vsBS2 S) (Cφ + 10 ^ 16 * S ^ 6) I.p := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hS2 := vsB_S2 hS hgl
  have h13 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hpS := hS.p
  exact
    { hk := vsBKeyB_injective
      hK := hgs
      hn := by have := hS.n; omega
      hm := hS2.1
      hac := by
        have w := wt_list2_le (vsBCtxB s) (.nat j)
        have := vsB_wt_ctxB hS hs
        have := wt_nat_le j
        have : j < vsQD s := List.mem_range.mp hj
        have := vsQD_le hs; have := hS.d
        unfold vsBS2; omega
      hkey := fun y _ => by
        have := wt_natList_le_sq (B := S) (xs := 0 :: vsBKeyB y) (fun z hz => by
          simp only [vsBKeyB, List.mem_cons, List.mem_nil_iff, or_false] at hz
          rcases hz with rfl | rfl
          · omega
          · exact (ZMod.val_lt _).le.trans hpS) (by simp [vsBKeyB]; have := I.prime.two_le; omega)
        have : (S + 1) ^ 2 ≤ 4 * S ^ 3 := by
          have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
          omega
        unfold vsBS2; omega
      hfa := fun g hg y _ =>
        vsB_actB_spec hB hphi hS hs (List.mem_range.mp hj) ((vsBH1_le hs) (hgs (Subgroup.subset_closure hg))) y
      hBS := by unfold vsBS2; omega
      hB := by
        calc (vsQOrb (vsBAj s j) gs 0).ncard ≤ (Set.univ : Set (ZMod I.p)).ncard :=
              Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
          _ = I.p := by rw [Set.ncard_univ, Nat.card_zmod] }

end

end GI.Impl
