module

public import Workspace.Impl.SCosNode2

@[expose] public section

/-!
# The dispatcher, functions 0–3

`solveF` (function 0) answers `[xv, gv]` when `Φ = ∅` (`scosC_empty`) and otherwise calls
`nodeF` (function 1). `nodeF` computes the orbit labels of `𝒢` on `Fin N`, the first point
`Fin.castAdd n a₀` of `Φ`, and the indicator of the orbit `O` of `a₀` (`scosNode_orbitInd`).
If `O` has fewer points than `Φ`, it calls `splitF` (`scosNode_split_spec`); else `O = Φ`, so
`𝒢` is transitive on `Φ` (`scosTrans_of_eq`), and it calls `transF` (`scosNode_trans_spec`).

The own costs `scosOwnE n` (the case `Φ = ∅`) and `scosOwnN n` (all other cases, apart from the
recursive calls) are polynomials in `n` (`scosOwnE_le`, `scosOwnN_le`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The own cost of function 0 in the case `Φ = ∅`. -/
def scosOwnE (n : ℕ) : ℕ := 1000000 * scosNodeS3 n

/-- The own cost of functions 0, 1, 2, 3, 10, 69, 72 when `Φ ≠ ∅`, apart from the calls
`call 0`, `call 4`, `call 5` on the subproblems. -/
def scosOwnN (n : ℕ) : ℕ := 100000000 * scosNodeS5 n

theorem scosOwnE_le (n : ℕ) : scosOwnE n ≤ 10 ^ 21 * (n + 1) ^ 21 :=
  le_of_eq (by unfold scosOwnE scosNodeS3 scosNodeS; ring)

theorem scosOwnN_le (n : ℕ) : scosOwnN n ≤ 10 ^ 33 * (n + 1) ^ 35 :=
  le_of_eq (by unfold scosOwnN scosNodeS5 scosNodeS; ring)

section Steps

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-- **Function 1, `nodeF`.** -/
theorem scosNode_node_spec {v : Val} {𝒢 : Subgroup (ScosPair n)} {x : ScosPair n}
    {Φ : Finset (Fin n)} (hv : ScosProb n v 𝒢 x Φ) (hne : Φ.Nonempty)
    (T : Subgroup (ScosPair n) → Finset (Fin n) → ℕ)
    (hrec : ∀ v' 𝒢' x' Φ', ScosProb n v' 𝒢' x' Φ' → Φ' ⊂ Φ → 𝒢' ≤ 𝒢 →
      FunAll 𝒫 0 v' (fun w c => ScosAns n w x' 𝒢' Φ' ∧ c ≤ T 𝒢' Φ'))
    (Rb Rg : ℕ → Prop)
    (hbase : ScosTrans 𝒢 Φ → Φ.card = 1 → FunAll 𝒫 4 v (fun w c => ScosAns n w x 𝒢 Φ ∧ Rb c))
    (hbig : ScosTrans 𝒢 Φ → 2 ≤ Φ.card → FunAll 𝒫 5 v (fun w c => ScosAns n w x 𝒢 Φ ∧ Rg c)) :
    FunAll 𝒫 1 v (fun w cost => ScosAns n w x 𝒢 Φ ∧
      ((∃ O : Finset (Fin n), O.Nonempty ∧ O ⊂ Φ ∧
          (∃ a ∈ O, ∀ b, b ∈ O ↔ b ∈ Φ ∧ ∃ g ∈ 𝒢, g.1 a = b) ∧
          cost ≤ 10000000 * scosNodeS5 n + T 𝒢 O + T (scosL 𝒢 O) (Φ \ O)) ∨
        (ScosTrans 𝒢 Φ ∧ Φ.card = 1 ∧ ∃ cb, Rb cb ∧ cost ≤ 10000000 * scosNodeS5 n + cb) ∨
        (ScosTrans 𝒢 Φ ∧ 2 ≤ Φ.card ∧ ∃ cg, Rg cg ∧ cost ≤ 10000000 * scosNodeS5 n + cg))) := by
  obtain ⟨gs, rfl, hgs, hw⟩ := scosNode_prob hv
  have hwg := hw.trans (scosNode_W n)
  have hwx := scosNode_wtPerm (nintSum x)
  have hwi := scosNode_wtInd Φ
  have hwv := scosNode_wtProb _ _ _ hwg hwx hwi
  have hS := scosNodeS_le3 n
  have hS3 := scosNodeS3_le5 n
  have hS' := scosNodeS_big n
  have hN := scosNode_N n
  refine FunAll.intro (scos_node (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)) ?_
  unfold scosNodeF
  have a0 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ]] (arg 0)
      (encGroup gs) _ := Det.arg' (rest := []) (j := 0) rfl
  obtain ⟨lab, hlab, hlt, d1⟩ := scosNode_orbDet hw a0
  have hwl := scosNode_wtLab lab (fun x => (hlt x).le)
  have hwl' : (Val.list ((List.finRange (n + n)).map fun i => Val.nat (lab i))).wt =
      (encFun lab).wt := rfl
  refine scosNode_let d1 fun c1 hc1 => ?_
  show EvalAll 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ], encFun lab] _ _
  have a2 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ], encFun lab] (arg 2)
      (scosInd Φ) _ := Det.arg' (j := 2) rfl
  obtain ⟨a₀, ha₀, d2⟩ := scosNode_findDet hne a2
  refine scosNode_let d2 fun c2 hc2 => ?_
  show EvalAll 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ], encFun lab,
    .nat (Fin.castAdd n a₀ : ℕ)] _ _
  have gl : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ], encFun lab,
      .nat (Fin.castAdd n a₀ : ℕ)] (.get (.var 1) (.var 2)) (.nat (lab (Fin.castAdd n a₀))) _ :=
    Det.get' (Det.var' (i := 1) rfl) (Det.var' (i := 2) rfl)
      (encFun_getElem? lab (Fin.castAdd n a₀))
  have vl : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ], encFun lab,
      .nat (Fin.castAdd n a₀ : ℕ)] (.var 1) (encFun lab) _ := Det.var' (i := 1) rfl
  have d3 := scosNode_eqIndDet hv.inv ha₀ hgs hlab hlt gl vl
  have hwa := wt_nat_le (Fin.castAdd n a₀ : ℕ)
  have hwa' := (Fin.castAdd n a₀).isLt
  have hwlab := wt_nat_le (lab (Fin.castAdd n a₀))
  have hwlab' := hlt (Fin.castAdd n a₀)
  refine scosNode_let d3 fun c3 hc3 => ?_
  show EvalAll 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ], encFun lab,
    .nat (Fin.castAdd n a₀ : ℕ), scosInd (scosNodeO 𝒢 Φ a₀)] _ _
  have hwo := scosNode_wtInd (scosNodeO 𝒢 Φ a₀)
  have v3 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ], encFun lab,
      .nat (Fin.castAdd n a₀ : ℕ), scosInd (scosNodeO 𝒢 Φ a₀)] (.var 3)
      (scosInd (scosNodeO 𝒢 Φ a₀)) _ := Det.var' (i := 3) rfl
  have a2' : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ], encFun lab,
      .nat (Fin.castAdd n a₀ : ℕ), scosInd (scosNodeO 𝒢 Φ a₀)] (arg 2) (scosInd Φ) _ :=
    Det.arg' (j := 2) rfl
  have hcond := Det.arith (op := .eq) (scosNode_countDet v3) (scosNode_countDet a2')
  have hle := scosNode_eval_eq_le (scosNodeO 𝒢 Φ a₀).card Φ.card
  have hwe := wt_nat_le (BinOp.eval .eq (scosNodeO 𝒢 Φ a₀).card Φ.card)
  refine scosNode_ite hcond fun cc hcc => ?_
  by_cases hEq : (scosNodeO 𝒢 Φ a₀).card = Φ.card
  · -- The orbit is `Φ`: the transitive case.
    have htr := scosTrans_of_eq (scosNodeO_eq_iff.mpr hEq)
    have e1 : BinOp.eval .eq (scosNodeO 𝒢 Φ a₀).card Φ.card = 1 := by simp [BinOp.eval, hEq]
    rw [e1, if_neg one_ne_zero]
    refine scosNode_call (Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x),
      scosInd Φ], encFun lab, .nat (Fin.castAdd n a₀ : ℕ), scosInd (scosNodeO 𝒢 Φ a₀)])
      (i := 0) rfl) fun ca hca => ?_
    refine (scosNode_trans_spec hv hne Rb Rg (hbase htr) (hbig htr)).mono
      fun w cost ⟨hans, hd⟩ => ⟨hans, Or.inr ?_⟩
    have := scosNode_wtAns hans
    rcases hd with ⟨h1, cb, hRb, hcb⟩ | ⟨h2, cg, hRg, hcg⟩
    · exact Or.inl ⟨htr, h1, cb, hRb, by omega⟩
    · exact Or.inr ⟨htr, h2, cg, hRg, by omega⟩
  · -- The orbit is smaller than `Φ`: the intransitive case.
    have e1 : BinOp.eval .eq (scosNodeO 𝒢 Φ a₀).card Φ.card = 0 := by simp [BinOp.eval, hEq]
    rw [e1, if_pos rfl]
    have hsub := scosNodeO_subset 𝒢 Φ a₀
    have hss : scosNodeO 𝒢 Φ a₀ ⊂ Φ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hEq (by rw [h])⟩
    have hOne : (scosNodeO 𝒢 Φ a₀).Nonempty := ⟨a₀, self_mem_scosNodeO ha₀⟩
    have b0 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ], encFun lab,
        .nat (Fin.castAdd n a₀ : ℕ), scosInd (scosNodeO 𝒢 Φ a₀)] (arg 0) (encGroup gs) _ :=
      Det.arg' (j := 0) rfl
    have b1 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ], encFun lab,
        .nat (Fin.castAdd n a₀ : ℕ), scosInd (scosNodeO 𝒢 Φ a₀)] (arg 1)
        (encPerm (nintSum x)) _ := Det.arg' (j := 1) rfl
    have hm4 := Det.mk4 b0 b1 a2' v3
    have hw4 := scosNode_wt4 _ _ _ _ hwg hwx hwi hwo
    refine scosNode_call hm4 fun ca hca => ?_
    refine (scosNode_split_spec hgs hw hv.inv hv.solv (scosInv_scosNodeO hv.inv ha₀) hOne hss T
      hrec).mono fun w cost ⟨hans, hcost⟩ => ⟨hans, Or.inl ⟨scosNodeO 𝒢 Φ a₀, hOne, hss,
        ⟨a₀, self_mem_scosNodeO ha₀, fun b => mem_scosNodeO⟩, ?_⟩⟩
    have := scosNode_wtAns hans
    omega

/-- **The dispatcher, functions 0–3.** On a problem `v` of `𝒢`, `x`, `Φ`, function 0 answers
correctly, given correct answers of the recursive calls. Its cost is its own cost plus: nothing
for `Φ = ∅`; the costs of the two subproblems on the orbit `O` of a point of `Φ` and on `Φ \ O`
when `𝒢` is not transitive on `Φ`; the cost of function 4 or 5 when it is. -/
theorem scos_solve_step {v : Val} {𝒢 : Subgroup (ScosPair n)} {x : ScosPair n}
    {Φ : Finset (Fin n)} (hv : ScosProb n v 𝒢 x Φ)
    (T : Subgroup (ScosPair n) → Finset (Fin n) → ℕ)
    (hrec : ∀ v' 𝒢' x' Φ', ScosProb n v' 𝒢' x' Φ' → Φ' ⊂ Φ → 𝒢' ≤ 𝒢 →
      FunAll 𝒫 0 v' (fun w c => ScosAns n w x' 𝒢' Φ' ∧ c ≤ T 𝒢' Φ'))
    (Rb Rg : ℕ → Prop)
    (hbase : ScosTrans 𝒢 Φ → Φ.card = 1 → FunAll 𝒫 4 v (fun w c => ScosAns n w x 𝒢 Φ ∧ Rb c))
    (hbig : ScosTrans 𝒢 Φ → 2 ≤ Φ.card → FunAll 𝒫 5 v (fun w c => ScosAns n w x 𝒢 Φ ∧ Rg c)) :
    FunAll 𝒫 0 v (fun w cost => ScosAns n w x 𝒢 Φ ∧ ((Φ = ∅ ∧ cost ≤ scosOwnE n) ∨
      (∃ O : Finset (Fin n), O.Nonempty ∧ O ⊂ Φ ∧
          (∃ a ∈ O, ∀ b, b ∈ O ↔ b ∈ Φ ∧ ∃ g ∈ 𝒢, g.1 a = b) ∧
        cost ≤ scosOwnN n + T 𝒢 O + T (scosL 𝒢 O) (Φ \ O)) ∨
      (ScosTrans 𝒢 Φ ∧ Φ.card = 1 ∧ ∃ cb, Rb cb ∧ cost ≤ scosOwnN n + cb) ∨
      (ScosTrans 𝒢 Φ ∧ 2 ≤ Φ.card ∧ ∃ cg, Rg cg ∧ cost ≤ scosOwnN n + cg))) := by
  have hnode := scosNode_node_spec (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) hv
  obtain ⟨gs, rfl, hgs, hw⟩ := scosNode_prob hv
  have hwg := hw.trans (scosNode_W n)
  have hwx := scosNode_wtPerm (nintSum x)
  have hwi := scosNode_wtInd Φ
  have hwv := scosNode_wtProb _ _ _ hwg hwx hwi
  have hS := scosNodeS_le3 n
  have hS3 := scosNodeS3_le5 n
  have hS' := scosNodeS_big n
  refine FunAll.intro (scos_solve (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)) ?_
  unfold scosSolveF
  have a2 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ]] (arg 2) (scosInd Φ) _ :=
    Det.arg' (rest := []) (j := 2) rfl
  refine scosNode_ite (scosNode_countDet a2) fun cc hcc => ?_
  by_cases h0 : Φ.card = 0
  · -- `Φ = ∅`: the answer `[xv, gv]`.
    rw [if_pos h0]
    have hΦ : Φ = ∅ := Finset.card_eq_zero.mp h0
    have a0 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ]] (arg 0)
        (encGroup gs) _ := Det.arg' (rest := []) (j := 0) rfl
    have a1 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ]] (arg 1)
        (encPerm (nintSum x)) _ := Det.arg' (rest := []) (j := 1) rfl
    have h2 := wt_list2_le (encPerm (nintSum x)) (encGroup gs)
    refine (Det.mk2 a1 a0).post fun c' hc' => ⟨?_, Or.inl ⟨hΦ, ?_⟩⟩
    · subst hΦ
      refine Or.inr ⟨x, (scosC_empty x 𝒢).1, encGroup gs, rfl, ?_, hw⟩
      rw [(scosC_empty x 𝒢).2]
      exact ⟨gs, rfl, hgs⟩
    · unfold scosOwnE
      omega
  · -- `Φ ≠ ∅`: call `nodeF`.
    rw [if_neg h0]
    have hne : Φ.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
    refine scosNode_call (Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x),
      scosInd Φ]]) (i := 0) rfl) fun ca hca => ?_
    refine (hnode hne T hrec Rb Rg hbase hbig).mono fun w cost ⟨hans, hd⟩ => ⟨hans, Or.inr ?_⟩
    have := scosNode_wtAns hans
    unfold scosOwnN
    rcases hd with ⟨O, h1, h2, h3, hc⟩ | ⟨h1, h2, cb, hRb, hcb⟩ | ⟨h1, h2, cg, hRg, hcg⟩
    · exact Or.inl ⟨O, h1, h2, h3, by omega⟩
    · exact Or.inr (Or.inl ⟨h1, h2, cb, hRb, by omega⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, cg, hRg, by omega⟩)

end Steps

end GI.Impl
