module

public import Workspace.Impl.LinFiniteActionProg

@[expose] public section

/-! The full affine interpreter has a uniform polynomial bit cost in its
actual input, including the invariant factors stored in the identity record. -/
namespace GI.Impl
open GI.Cited GI.Lang
universe u

theorem linPoly_source_bound {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) :
    ∃ K D : ℕ, ∀ n s W, n ≤ W → s ≤ W → f n s 0 ≤ K * (W + 1) ^ D := by
  obtain ⟨C, D, h⟩ := hf
  refine ⟨C * 2 ^ D, D, ?_⟩
  intro n s W hn hs
  have hh := h n s 0
  change f n s 0 ≤ C * (s + 0 + n + 2) ^ D at hh
  calc
    f n s 0 ≤ C * (2 * (W + 1)) ^ D :=
      hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    _ = (C * 2 ^ D) * (W + 1) ^ D := by rw [mul_pow]; ring

theorem linFiniteModuli_wt_lower {d : ℕ} (m : Fin d → ℕ) :
    (linVecVal (fun i => (m i : ℤ))).wt ≤ (linVecVal (linFiniteModuli m)).wt := by
  have he := linExtend_value encInt (fun i => (m i : ℤ)) 0
  have hh := wt_list_mono (List.prefix_append ((List.finRange d).map fun i => encInt (m i : ℤ)) [encInt 0])
  change (linVecVal (fun i => (m i : ℤ))).wt ≤
    (Val.list ((List.finRange (d + 1)).map fun i => encInt (linFiniteModuli m i))).wt
  unfold linFiniteModuli
  rw [he]
  exact hh

theorem linGroupSlpCost_mono {W V L K B B' C C' : ℕ}
    (hW : W ≤ V) (hL : L ≤ K) (hB : B ≤ B') (hC : C ≤ C') :
    linGroupSlpCost W L B C ≤ linGroupSlpCost V K B' C' := by
  dsimp only [linGroupSlpCost, linGroupSlpLoopCost, linGroupSlpLoopStepCost,
    linGroupSlpStepCost, linGroupSlpArg, linVectorAccWt]
  gcongr

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linFiniteActionSlp_spec_poly :
    ∃ K D : ℕ, ∀ {G : Type u} [Group G] {d : ℕ} (m : Fin d → ℕ),
      (∀ i, 0 < m i) →
      ∀ (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m),
      (∀ g h, c (g * h) = ρ g (c h) + c g) →
      ∀ {P : Program} {b : ℕ}, linFiniteActionSlpAt P b →
      ∀ (gs : List G) (prog : List SlpInstr) (es : List G), linSlpEntries gs prog [] = some es →
      FunDet P b (.list [linGroupSlpTable (linFiniteAffineVal m ρ c) gs,
        .list (prog.map encSlpInstr), linFiniteAffineVal m ρ c 1])
        (linFiniteAffineVal m ρ c (es.getLast?.getD 1))
        (K * ((Val.list [linGroupSlpTable (linFiniteAffineVal m ρ c) gs,
          .list (prog.map encSlpInstr), linFiniteAffineVal m ρ c 1]).wt + 1) ^ D) := by
  obtain ⟨a, e, hU⟩ := linPoly_source_bound (PBU.add linFiniteActionWeight_poly linFiniteActionOpCost_poly)
  have ht : PBU (fun _ W _ => linGroupSlpCost W W (a * (W + 1) ^ e) (a * (W + 1) ^ e)) :=
    linPoly_subst linGroupSlpCost_poly PBU.W PBU.W (PBU.smul a (PBU.pow (PBU.addc PBU.W 1) e))
  obtain ⟨K, D, hb⟩ := ht
  refine ⟨K * 2 ^ D, D, ?_⟩
  intro G hG d m hm ρ c hc P b hp gs prog es he
  let arg := Val.list [linGroupSlpTable (linFiniteAffineVal m ρ c) gs,
    .list (prog.map encSlpInstr), linFiniteAffineVal m ρ c 1]
  let W := arg.wt
  let S := (linVecVal (fun i => (m i : ℤ))).wt
  have w1 : (linFiniteAffineVal m ρ c 1).wt < W := wt_le_wt_list (by simp [W, arg])
  have wmod : (linVecVal (linFiniteModuli m)).wt < (linFiniteAffineVal m ρ c 1).wt :=
    wt_le_wt_list (by simp [linFiniteAffineVal])
  have hS : S ≤ W := (linFiniteModuli_wt_lower m).trans (wmod.le.trans w1.le)
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => encInt (m i : ℤ))
    simp only [List.length_map, List.length_finRange] at hh
    exact hh.le.trans hS
  have hL : prog.length ≤ W := by
    have hh := length_lt_wt_list (prog.map encSlpInstr)
    have ww : (Val.list (prog.map encSlpInstr)).wt < W := wt_le_wt_list (by simp [W, arg])
    simp only [List.length_map] at hh
    exact hh.le.trans ww.le
  have hu := hU d S W hd hS
  have hs := linFiniteActionSlp_spec m ρ c hp hm hc gs prog es he
  have hmono := linGroupSlpCost_mono (W := W) le_rfl hL
    (show linFiniteActionWeight S d ≤ a * (W + 1) ^ e by omega)
    (show linFiniteActionOpCost S d ≤ a * (W + 1) ^ e by omega)
  have hbound := hb 0 W 0
  change linGroupSlpCost W W (a * (W + 1) ^ e) (a * (W + 1) ^ e) ≤ K * (W + 2) ^ D at hbound
  apply hs.mono
  calc
    _ ≤ linGroupSlpCost W W (a * (W + 1) ^ e) (a * (W + 1) ^ e) := hmono
    _ ≤ K * (2 * (W + 1)) ^ D :=
      hbound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    _ = (K * 2 ^ D) * (W + 1) ^ D := by rw [mul_pow]; ring

end GI.Impl
