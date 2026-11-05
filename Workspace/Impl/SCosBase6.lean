module

public import Workspace.Impl.SCosBase5

@[expose] public section

/-!
# The base case, the last step

Step 7 of `scosBaseF`, with its correctness. If `τ` is found at index `i`, the pair `(τ, t)` of
the transversal has `t ∈ 𝒢.map nintSum`, so `t = nintSum g` with `g ∈ 𝒢` and `g₂ α = x₂⁻¹ (x₁ α)`;
the answer `[x t, 𝒢_{n+α}]` is correct by `scosBase_mem_scosC` and `scosBase_pstab`. If `τ` is not
found, it is not in the orbit of `n + α`, so the subcoset is empty (`scosBase_of_mem`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

section Steps

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-- The expression of step 7. -/
def scosBaseIte : Expr :=
  .ite (.arith .lt (.var 6) (.length (.var 5)))
    (mk2 (.call 87 (mk2 (arg 1) (.get (.get (.var 5) (.var 6)) (.nat 1))))
      (.call 117 (mk2 (arg 0) (mk1 (.var 3)))))
    .nil

/-- The cost bound of step 7. -/
noncomputable def scosBaseT7 (hps : PointwiseStab) (M S : ℕ) : ℕ :=
  200000 * S + scosBaseP hps M

theorem scosBase_genGroup {𝒢 : Subgroup (ScosPair n)} {gs : List (Perm (Fin (n + n)))}
    (hgs : gens gs = 𝒢.map nintSum) {σ : Perm (Fin (n + n))} :
    σ ∈ genGroup (1 :: gs) ↔ σ ∈ 𝒢.map nintSum := by
  rw [← hgs, ← gens_cons_one]; rfl

/-- **Step 7.** -/
theorem scosBase_e7 {𝒢 : Subgroup (ScosPair n)} (gs : List (Perm (Fin (n + n))))
    (x : ScosPair n) (a : Fin n) (hinv : ScosInv 𝒢 {a}) (hgs : gens gs = 𝒢.map nintSum)
    (L : List (Fin (n + n) × Perm (Fin (n + n))))
    (hL2 : ∀ β, β ∈ L.map Prod.fst ↔ ∃ g ∈ genGroup (1 :: gs), g (Fin.natAdd n a) = β)
    (hL3 : ∀ p ∈ L, p.2 ∈ genGroup (1 :: gs) ∧ p.2 (Fin.natAdd n a) = p.1)
    {M S : ℕ} (hM : (scosBaseV gs x a).wt ≤ M) (hN : n + n + 1 ≤ M)
    (hW6 : 320 * (n + n + 1) ^ 6 ≤ M) (hLw : (encPairs ptKey L).wt ≤ S) (hMS : M ^ 3 ≤ S) :
    EvalAll (𝒫) (scosBaseE6 gs x a L (L.findIdx fun p => decide ((p.1 : ℕ) = scosBaseTau x a)))
      scosBaseIte (fun w cost => ScosAns n w x 𝒢 {a} ∧ cost ≤ scosBaseT7 hps M S) := by
  set i := L.findIdx fun p => decide ((p.1 : ℕ) = scosBaseTau x a) with hi
  have hil : i ≤ L.length := List.findIdx_le_length
  have hM1 : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) M
  have hc := scosBase_cond (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs x a L hil hLw
  refine EvalAll.ite hc (fun _ _ h => ⟨_, h.1⟩) fun y cc h => ?_
  obtain ⟨hy, hcc⟩ := h
  cases hy
  by_cases hf : i < L.length
  · -- found
    rw [if_pos hf, if_neg one_ne_zero]
    have dcomp := scosBase_comp (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs x a L hf
      hM hN hLw hMS
    have estab := scosBase_stab (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) gs x a L
      (i := i) hM hN hW6
    refine (EvalAll.mk2_last dcomp estab).mono fun w cb hw => ?_
    obtain ⟨lv, cl, ⟨hG, hlw, hcl⟩, rfl, hcb⟩ := hw
    -- the transversal element
    have hq : decide (((L[i]'hf).1 : ℕ) = scosBaseTau x a) = true :=
      List.findIdx_getElem (xs := L) (p := fun p => decide ((p.1 : ℕ) = scosBaseTau x a)) (w := hf)
    have hq' : (L[i]'hf).1 = scosBaseTau x a := Fin.ext (of_decide_eq_true hq)
    obtain ⟨ht1, ht2⟩ := hL3 _ (List.getElem_mem hf)
    obtain ⟨g, hg, hgt⟩ := (scosBase_genGroup hgs).mp ht1
    rw [← hgt] at ht2 hcb ⊢
    rw [hq'] at ht2
    refine ⟨Or.inr ⟨x * g, scosBase_mem_scosC hinv hg ht2, lv, by rw [map_mul], ?_, hlw⟩, ?_⟩
    · rw [hgs, scosBase_pstab hinv] at hG; exact hG
    · -- the cost
      have w1 := wt_list2_le (encPerm (nintSum x * nintSum g)) lv
      have w2 := wt_encPerm_le (nintSum x * nintSum g)
      have p1 : (n + n + 1) ^ 2 ≤ (n + n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have hS1 : M ≤ S := hM1.trans hMS
      unfold scosBaseT7
      omega
  · -- not found
    rw [if_neg hf, if_pos rfl]
    refine (Det.nil (P := 𝒫) (env := scosBaseE6 gs x a L i)).post fun cb hcb => ⟨Or.inl ⟨rfl, ?_⟩, ?_⟩
    · refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => hf ?_
      obtain ⟨σ, hσ, hστ⟩ := scosBase_of_mem hinv hy
      obtain ⟨q, hq, hq1⟩ := List.mem_map.mp ((hL2 _).mpr ⟨σ, (scosBase_genGroup hgs).mpr hσ, hστ⟩)
      exact List.findIdx_lt_length_of_exists ⟨q, hq, by simp [hq1, scosBaseTau]⟩
    · have w0 : (Val.list []).wt ≤ 5 := by
        exact (wt_list_le []).trans (by simp)
      have hS1 : M ≤ S := hM1.trans hMS
      unfold scosBaseT7
      omega

end Steps

end GI.Impl
