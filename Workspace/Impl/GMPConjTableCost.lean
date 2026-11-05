module

public import Workspace.Impl.GMPConjTable

@[expose] public section

/-! # Joint polynomial bounds for the conjugation table -/

namespace GI.Impl

/-- Substituting polynomial sizes into a joint polynomial cost bound. -/
theorem gmpPBU_comp {f a b c : ℕ → ℕ → ℕ → ℕ} (hf : PBU f)
    (ha : PBU a) (hb : PBU b) (hc : PBU c) :
    PBU (fun k W B => f (a k W B) (b k W B) (c k W B)) := by
  obtain ⟨C, D, hf⟩ := hf
  obtain ⟨C', D', h⟩ := ((((hb.add hc).add ha).addc 2).pow D).smul C
  exact ⟨C', D', fun k W B => (hf _ _ _).trans (h k W B)⟩

theorem gmpConjTableStepCost_poly (hm : GI.Cited.Membership) :
    PBU (fun L Y _ => gmpConjTableStepCost hm Y L) := by
  exact (gmpPBU_comp (gmpConjRowCost_poly hm) PBU.k (PBU.W.smul 100) (PBU.const 0)).add
    ((PBU.W.add ((PBU.k.addc 1).pow 2)).smul (10 ^ 6))

theorem gmpConjTableCost_poly (hm : GI.Cited.Membership) :
    PBU (fun L Y S => gmpConjTableCost hm Y L S) := by
  exact (PBU.B.mul (gmpConjTableStepCost_poly hm)).add
    (((PBU.B.addc 1).smul GI.Lang.mapK).mul
      ((PBU.W.add (((PBU.B.addc 1).mul ((PBU.k.addc 1).pow 2)).smul 20)).addc 10))

end GI.Impl
