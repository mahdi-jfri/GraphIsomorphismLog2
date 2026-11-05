module

public import Workspace.Impl.LinObjectKernelStep
public import Workspace.Impl.LinObjectKernelMath

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 300000 in
set_option maxRecDepth 2000 in
theorem linObjectKernel_spec {P : Program} {b jsci n : ℕ} {hs : SolvableCosetIntersection}
    (h : linObjectKernelAt P b jsci hs) (as : List (Equiv.Perm (Fin n)))
    (Bs : List (Subgroup (Equiv.Perm (Fin n)))) (groups : List Val)
    (hgroups : List.Forall₂ (fun B v => GroupValC n v B) Bs groups)
    (N : Subgroup (Equiv.Perm (Fin n))) (hNA : N ≤ gens as)
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ N)
    (hBsN : ∀ B ∈ Bs, N ≤ B) (hBsA : ∀ B ∈ Bs, B ≤ gens as) (hal : as.length ≤ n ^ 2) :
    let input := Val.list [encGroup as,.list groups]
    FunAll P b input (fun out cost =>
      GroupValC n out (linObjectKernelPrefix (gens as) Bs Bs.length) ∧ cost ≤ linObjectKernelCost hs n input.wt) := by
  let input := Val.list [encGroup as,.list groups]
  let W := input.wt
  let k := groups.length
  let M := linObjectKernelAccWt n
  let D := linObjectKernelStepCost hs n W
  have hk := Det.length (Det.arg' (P := P) (vs := [encGroup as,.list groups]) (rest := []) (j := 1) rfl)
  have hacc := Det.arg' (P := P) (vs := [encGroup as,.list groups]) (rest := []) (j := 0) rfl
  have hgw : (Val.list groups).wt < W := wt_le_wt_list (by simp [W,input])
  have hkw : k ≤ W := (length_lt_wt_list groups).le.trans hgw.le
  have hwpos : 0 < W := by omega
  have hmain := loopBdd_spec h.loop hk hacc (by dsimp only [W,input,k] at *; omega)
    (Inv := fun i acc => GroupValC n acc (linObjectKernelPrefix (gens as) Bs i))
    (M := M) (D := fun _ => D)
    (show GroupValC n (encGroup as) (linObjectKernelPrefix (gens as) Bs 0) from ⟨as,rfl,rfl,hal⟩)
    (fun i acc hi hinv => linObjectKernel_acc_wt hinv) (by
      intro i acc hi hinv
      have hiB : i < Bs.length := by have hl := hgroups.length_eq; omega
      let j : Fin Bs.length := ⟨i,hiB⟩
      let bv := groups.get (j.cast hgroups.length_eq)
      have hbv : GroupValC n bv (Bs.get j) := hgroups.get hiB hi
      have hget : groups[i]? = some bv := by simp [bv,j]
      have hs0 := linObjectKernel_step_spec h as groups acc bv
        (linObjectKernelPrefix (gens as) Bs i) (Bs.get j) hget hinv hbv
        (linObjectKernelPrefix_normalizes N (gens as) Bs hNA hcomm hBsN i
          (hBsA (Bs.get j) (List.get_mem _ _)))
      exact hs0.mono fun out cost hout => ⟨by
        change GroupValC n out (linObjectKernelPrefix (gens as) Bs (j.val + 1))
        rw [linObjectKernelPrefix_succ (gens as) Bs j]
        exact hout.1,by exact hout.2.trans (Nat.le_add_right _ _)⟩)
  refine hmain.mono fun out cost hout => ⟨?_,?_⟩
  · have hl := hgroups.length_eq
    simpa only [k,← hl] using hout.1
  · have hc := hout.2
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hc
    exact hc.trans (linObjectKernel_loop_collect W M D k hkw)

theorem linObjectKernel_aut_spec {P : Program} {b jsci n : ℕ} {hs : SolvableCosetIntersection}
    (h : linObjectKernelAt P b jsci hs) (as : List (Equiv.Perm (Fin n)))
    (Y : List (TmRiO n)) (groups : List Val)
    (hgroups : List.Forall₂ (fun S v => GroupValC n v (GI.Multicoset.Aut (gens as) (tmGlMs S)))
      (tmRiPcsO (gens as) Y) groups)
    (ns : List (Equiv.Perm (Fin n))) (hNA : gens ns ≤ gens as)
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hfix : GI.Multicoset.Fixes (gens ns) (tmGlMs Y)) (hal : as.length ≤ n ^ 2) :
    let input := Val.list [encGroup as,.list groups]
    FunAll P b input (fun out cost => GroupValC n out (GI.Multicoset.Aut (gens as) (tmGlMs Y)) ∧
      cost ≤ linObjectKernelCost hs n input.wt) := by
  have hBs : List.Forall₂ (fun B v => GroupValC n v B)
      ((tmRiPcsO (gens as) Y).map fun S => GI.Multicoset.Aut (gens as) (tmGlMs S)) groups := by
    simpa only [List.forall₂_map_left_iff] using hgroups
  have hBsN : ∀ B ∈ (tmRiPcsO (gens as) Y).map (fun S => GI.Multicoset.Aut (gens as) (tmGlMs S)),
      gens ns ≤ B := by
    intro B hB
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hB
    have hfixS : GI.Multicoset.Fixes (gens ns) (tmGlMs S) := (tmRiPcsO_pc le_rfl hfix hS).1.2.2.2
    exact fun g hg => ⟨hNA hg, hfixS.act_eq hg⟩
  have hBsA : ∀ B ∈ (tmRiPcsO (gens as) Y).map (fun S => GI.Multicoset.Aut (gens as) (tmGlMs S)),
      B ≤ gens as := by
    intro B hB
    obtain ⟨S, _, rfl⟩ := List.mem_map.mp hB
    exact GI.Multicoset.aut_le (gens as) (tmGlMs S)
  have hr := linObjectKernel_spec h as _ groups hBs (gens ns) hNA hcomm hBsN hBsA hal
  simpa only [List.length_map,linObjectKernel_aut_eq] using hr

theorem linObjectKernel_uniform (hs : SolvableCosetIntersection) :
    ∃ K D : ℕ, ∀ n W, n ≤ W → linObjectKernelCost hs n W ≤ K * (W + 1) ^ D := by
  obtain ⟨K,D,hKD⟩ := linPoly_source_bound (linObjectKernelCost_poly hs)
  exact ⟨K,D,fun n W hn => hKD n W W hn le_rfl⟩

end GI.Impl
