module

public import Workspace.Impl.LinPrimePassCost
public import Workspace.Impl.LinPrimePassArg

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 24000

private theorem linPrimePassWholeCost {W P L T ca cl cb wo : ℕ}
    (hp : ca ≤ 100001 * (W + P + 1)) (hl : cl ≤ P + 2 * L + 2)
    (hb : cb ≤ L + 2 * T + 100) (hw : wo ≤ T + 4) :
    ca + (cl + cb + wo + 1) + wo + 1 ≤ 10000000 * (W + P + L + T + 1) := by omega

set_option maxHeartbeats 200000 in
theorem linPrimePass_spec (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jm jv n d p : ℕ} (hat : linPrimePassAt P b jm jv hm hv)
    (gs : List (Equiv.Perm (Fin n))) (hlen : gs.length ≤ n ^ 2)
    (m : Fin d → ℕ) (hp : p.Prime) (hpn : p ≤ n) [NeZero n] (hmpos : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m))
    (hs : IsSolvable ρ.range)
    (c : gens gs → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (x : linFiniteVec m) (acc : Equiv.Perm (Fin n)) :
    let D := linTrialPrimaryData m p hp hmpos
    let a := linPrimePrepareInputVal gs m ρ c x acc p
    FunAll P b a (fun out cost => linPrimePassOut gs m D ρ c x acc out ∧
      cost ≤ linPrimePassCost hm hv a.wt) := by
  let D := linTrialPrimaryData m p hp hmpos
  let q := linPrimaryOrders p D.exponent
  let ρp := linPrimeAction D hmpos ρ
  let cp := fun g => linPrimeProjection D (c g)
  let xp := linPrimeProjection D x
  let a := linPrimePrepareInputVal gs m ρ c x acc p
  let W := a.wt
  let prep := linPrimaryLoopInputVal gs D.exponent ρp cp xp 1
  let B := linPrimePassPrepareBudget W
  let L := linPrimePassLoopBudget hm hv W
  let T := linPrimePassLiftBudget hm hv W
  have da := linPrimePassPrepareArg_spec (P := P) gs m ρ c x acc p
  have warg := linDet_wt_le da
  have hprepare := (linPrimePrepare_spec hat.prepare gs m hp hmpos ρ c x 1).mono
    (linPrimePass_prepare_bound warg)
  have wprep : prep.wt ≤ B := hprepare.wt_lt.le
  have dprep := Det.call da hprepare
  have hcp : ∀ g k, cp (g * k) = ρp g (cp k) + cp g := linPrimeAction_cocycle D hmpos ρ c hc
  have hsp : IsSolvable ρp.range := by
    refine solvable_range_of_ker_le ρ ρp ?_ hs
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    refine AddEquiv.ext fun y => ?_
    obtain ⟨z, rfl⟩ := linPrimeProjection_surjective D y
    change ρp g (linPrimeProjection D z) = linPrimeProjection D z
    rw [linPrimeAction_image, hg]
    rfl
  have hloop : FunAll P (b + 88) prep (fun out cost =>
      linPrimaryLoopInv gs D.exponent ρp cp xp 1 (linPrimaryHeight D.exponent) out ∧ cost ≤ L) := FunAll.mono (linPrimaryLoop_spec hm hv hat.loop gs hlen hp hpn D.exponent ρp hsp cp hcp xp 1)
    (fun out cost ho => ⟨ho.1, ho.2.trans (linPrimePass_loop_bound hm hv wprep)⟩)
  have dv := Det.var' (P := P) (env := [a, prep]) (i := 1) rfl
  have call := normBound_call dv hloop
  apply FunAll.intro hat.entry
  apply EvalAll.letE dprep
  intro z cz hz
  obtain ⟨rfl, hcz⟩ := hz
  have hcz' : cz ≤ 100001 * (W + B + 1) := by
    change cz ≤ 100000 * (a.wt + 1) + B + prep.wt + 1 at hcz
    dsimp only [W]
    omega
  apply EvalAll.letE call
  intro phase cl ho
  have wphase : phase.wt ≤ L := ho.2.1
  have hcl : cl ≤ B + 2 * L + 2 := by
    have hh := ho.2.2
    change cl ≤ prep.wt + 1 + 2 * L + 1 at hh
    omega
  have hterminal := linPrimaryLoopInv_terminal gs hp D.exponent ρp cp hcp xp 1 phase ho.1
  rcases hterminal with ⟨rfl, hno⟩ | ⟨ks, hle, g, hphase, hkslen, hg, hofs, hstab, htrans⟩
  · have dlen := Det.length (Det.var' (P := P) (env := [a, prep, .list []]) (i := 2) rfl)
    have de := Det.ite_zero (t := linPrimePassTailF (b + 525) (b + 528) (b + 595) (b + 642) (b + 720))
      dlen (Det.nil (P := P) (env := [a, prep, .list []]))
    refine de.post fun cb hcb => ⟨Or.inl ⟨rfl, ?_⟩, ?_⟩
    · rintro ⟨g, hg⟩
      apply hno
      refine ⟨g, ?_⟩
      rw [← linPrimeProjection_eval D hmpos ρ c]
      exact hg
    · have hb : (Val.list []).wt + 1 + 0 + 3 + 5 + (Val.list []).wt + 1 ≤ L + 2 * T + 100 := by
        norm_num only [wt_list_nil]
        omega
      have hw : (Val.list []).wt ≤ T + 4 := by norm_num only [wt_list_nil]; omega
      norm_num only [List.length_cons, List.length_nil, Nat.add_assoc] at hcb
      have hbody : cb ≤ L + 2 * T + 100 := by
        norm_num only [wt_list_nil] at hcb
        omega
      exact linPrimePassWholeCost (W := W) (P := B) (L := L) (T := T) hcz' hcl hbody hw
  · simp only [mul_one] at hphase
    subst phase
    let table := linGroupSlpTable (linFiniteAffineVal q (ρp.comp (Subgroup.inclusion hle))
      (cp ∘ Subgroup.inclusion hle)) (linActionGens ks)
    let ident := linFiniteAffineVal q (ρp.comp (Subgroup.inclusion hle)) (cp ∘ Subgroup.inclusion hle) 1
    let pp := linFinitePointVal q 0
    let phase := Val.list [.list [encGroup ks, table, ident], pp, encPerm g.val]
    let result := Val.list [linActionContext ks m (ρ.comp (Subgroup.inclusion hle)) (c ∘ Subgroup.inclusion hle),
      linFinitePointVal m (linFiniteEval ρ c g x), encPerm (g.val * acc)]
    have wphase' : phase.wt ≤ L := wphase
    have wtarg : a.wt + prep.wt + phase.wt ≤ linPrimePassLiftArg hm hv W := by
      change a.wt + prep.wt + phase.wt ≤ W + B + L
      dsimp only [W]
      omega
    have dt := (linPrimePass_success_spec hm hv hat gs ks hle m hmpos ρ c hc g x acc p prep table ident pp).mono
      (linPrimePassSuccessCost_mono hm wtarg)
    change Det P [a, prep, phase]
      (linPrimePassTailF (b + 525) (b + 528) (b + 595) (b + 642) (b + 720)) result T at dt
    have wr := linDet_wt_le dt
    have dlen := Det.length (Det.var' (P := P) (env := [a, prep, phase]) (i := 2) rfl)
    have di := Det.ite_pos (e := .nil) dlen (by change (3 : ℕ) ≠ 0; decide) dt
    refine di.post fun cb hcb => ⟨Or.inr ⟨ks, hle, g, rfl, hkslen, ?_, ?_, ?_⟩, ?_⟩
    · rw [linPrimeProjection_eval D hmpos ρ c]
      exact hg
    · exact hstab
    · intro h
      rw [linPrimeProjection_eval D hmpos ρ c]
      exact htrans h
    · have hb : phase.wt + 1 + 3 + 3 + T + result.wt + 1 ≤ L + 2 * T + 100 := by omega
      have hw : result.wt ≤ T + 4 := by omega
      norm_num only [List.length_cons, List.length_nil, Nat.add_assoc] at hcb
      have hbody : cb ≤ L + 2 * T + 100 := by
        change cb ≤ phase.wt + (7 + (T + (result.wt + 1))) at hcb
        omega
      exact linPrimePassWholeCost (W := W) (P := B) (L := L) (T := T) hcz' hcl hbody hw

end GI.Impl
