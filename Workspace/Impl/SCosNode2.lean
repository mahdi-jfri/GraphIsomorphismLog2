module

public import Workspace.Impl.SCosNode1

@[expose] public section

/-!
# Functions 2 (`splitF`) and 3 (`transF`)

`transF` counts `|Φ|` and calls `baseF` (function 4) for `|Φ| = 1`, else `bigF` (function 5)
(`scosNode_trans_spec`). `splitF` solves on the orbit `O`, and, when that subcoset is a coset
`z L(𝒢, O)`, solves `[lv, z, Φ \ O]` (`scosNode_split_spec`). The second problem is a problem
of the recursion: `L(𝒢, O) ≤ 𝒢` keeps solvability (`scosNode_solv`), and `Φ \ O` is invariant
(`scosInv_sdiff`). Its answer is an answer on `Φ`, because the subcoset on `Φ` is the subcoset
of `z L(𝒢, O)` on `Φ \ O` (`scosC_split_coset`) and `L(𝒢, Φ) = L(L(𝒢, O), Φ \ O)`
(`scosL_split`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

section Steps

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

theorem scosNode_eval_eq_le (a b : ℕ) : BinOp.eval .eq a b ≤ 1 := by
  simp only [BinOp.eval]; split_ifs <;> omega

/-- **Function 3, `transF`.** -/
theorem scosNode_trans_spec {v : Val} {𝒢 : Subgroup (ScosPair n)} {x : ScosPair n}
    {Φ : Finset (Fin n)} (hv : ScosProb n v 𝒢 x Φ) (hne : Φ.Nonempty) (Rb Rg : ℕ → Prop)
    (hbase : Φ.card = 1 → FunAll 𝒫 4 v (fun w c => ScosAns n w x 𝒢 Φ ∧ Rb c))
    (hbig : 2 ≤ Φ.card → FunAll 𝒫 5 v (fun w c => ScosAns n w x 𝒢 Φ ∧ Rg c)) :
    FunAll 𝒫 3 v (fun w cost => ScosAns n w x 𝒢 Φ ∧
      ((Φ.card = 1 ∧ ∃ cb, Rb cb ∧ cost ≤ 1000000 * scosNodeS3 n + cb) ∨
        (2 ≤ Φ.card ∧ ∃ cg, Rg cg ∧ cost ≤ 1000000 * scosNodeS3 n + cg))) := by
  obtain ⟨gs, rfl, hgs, hw⟩ := scosNode_prob hv
  have hwv := scosNode_wtProb _ _ _ (hw.trans (scosNode_W n)) (scosNode_wtPerm (nintSum x))
    (scosNode_wtInd Φ)
  refine FunAll.intro (scos_trans (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)) ?_
  have a2 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ]] (arg 2) (scosInd Φ) _ :=
    Det.arg' (rest := []) (j := 2) rfl
  have hcond := Det.arith (op := .eq) (scosNode_countDet a2) (Det.nat 1)
  have hle := scosNode_eval_eq_le Φ.card 1
  have hwe := wt_nat_le (BinOp.eval .eq Φ.card 1)
  have hS := scosNodeS_le3 n
  have hS' := scosNodeS_big n
  unfold scosTransF
  refine scosNode_ite hcond fun cc hcc => ?_
  by_cases h1 : Φ.card = 1
  · have e1 : BinOp.eval .eq Φ.card 1 = 1 := by simp [BinOp.eval, h1]
    rw [e1, if_neg one_ne_zero]
    refine scosNode_call (Det.var' (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ]])
      (i := 0) rfl) fun ca hca => ?_
    refine (hbase h1).mono fun w cb ⟨hans, hR⟩ => ⟨hans, Or.inl ⟨h1, cb, hR, ?_⟩⟩
    have := scosNode_wtAns hans
    omega
  · have e1 : BinOp.eval .eq Φ.card 1 = 0 := by simp [BinOp.eval, h1]
    have h2 : 2 ≤ Φ.card := by have := Finset.card_pos.mpr hne; omega
    rw [e1, if_pos rfl]
    refine scosNode_call (Det.var' (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ]])
      (i := 0) rfl) fun ca hca => ?_
    refine (hbig h2).mono fun w cg ⟨hans, hR⟩ => ⟨hans, Or.inr ⟨h2, cg, hR, ?_⟩⟩
    have := scosNode_wtAns hans
    omega

/-- An answer of the second problem of `splitF` is an answer on `Φ`. -/
theorem scosNode_ans_split {w : Val} {𝒢 : Subgroup (ScosPair n)} {x z : ScosPair n}
    {Φ O : Finset (Fin n)} (hinv : ScosInv 𝒢 Φ) (hO : ScosInv 𝒢 O) (hsub : O ⊆ Φ)
    (hz : z ∈ scosC x 𝒢 O) (h : ScosAns n w z (scosL 𝒢 O) (Φ \ O)) : ScosAns n w x 𝒢 Φ := by
  have hC : scosC x 𝒢 Φ = scosC z (scosL 𝒢 O) (Φ \ O) :=
    scosC_split_coset hsub (scosC_eq hO hz)
  have hL : scosL 𝒢 Φ = scosL (scosL 𝒢 O) (Φ \ O) := scosL_split 𝒢 hinv hO hsub
  unfold ScosAns
  rw [hC, hL]
  exact h

/-- **Function 2, `splitF`.** -/
theorem scosNode_split_spec {gs : List (Perm (Fin (n + n)))} {𝒢 : Subgroup (ScosPair n)}
    {x : ScosPair n} {Φ O : Finset (Fin n)} (hgs : gens gs = 𝒢.map nintSum)
    (hw : (encGroup gs).wt ≤ scosW n) (hinv : ScosInv 𝒢 Φ)
    (hsolv : IsSolvable (𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n)))))
    (hO : ScosInv 𝒢 O) (hOne : O.Nonempty) (hsub : O ⊂ Φ)
    (T : Subgroup (ScosPair n) → Finset (Fin n) → ℕ)
    (hrec : ∀ v' 𝒢' x' Φ', ScosProb n v' 𝒢' x' Φ' → Φ' ⊂ Φ → 𝒢' ≤ 𝒢 →
      FunAll 𝒫 0 v' (fun w c => ScosAns n w x' 𝒢' Φ' ∧ c ≤ T 𝒢' Φ')) :
    FunAll 𝒫 2 (.list [encGroup gs, encPerm (nintSum x), scosInd Φ, scosInd O])
      (fun w cost => ScosAns n w x 𝒢 Φ ∧
        cost ≤ 1000000 * scosNodeS3 n + T 𝒢 O + T (scosL 𝒢 O) (Φ \ O)) := by
  have hwg := hw.trans (scosNode_W n)
  have hwx := scosNode_wtPerm (nintSum x)
  have hwi := scosNode_wtInd Φ
  have hwo := scosNode_wtInd O
  have hU := scosNode_wt4 _ _ _ _ hwg hwx hwi hwo
  have hS := scosNodeS_le3 n
  have hS' := scosNodeS_big n
  refine FunAll.intro (scos_split (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)) ?_
  unfold scosSplitF
  have a0 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ, scosInd O]] (arg 0)
      (encGroup gs) _ := Det.arg' (rest := []) (j := 0) rfl
  have a1 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ, scosInd O]] (arg 1)
      (encPerm (nintSum x)) _ := Det.arg' (rest := []) (j := 1) rfl
  have a3 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ, scosInd O]] (arg 3)
      (scosInd O) _ := Det.arg' (rest := []) (j := 3) rfl
  have hm := Det.mk3 a0 a1 a3
  have hm3 := wt_list3_le (encGroup gs) (encPerm (nintSum x)) (scosInd O)
  have hprob : ScosProb n (.list [encGroup gs, encPerm (nintSum x), scosInd O]) 𝒢 x O :=
    ⟨⟨_, rfl, ⟨gs, rfl, hgs⟩, hw⟩, hO, hsolv⟩
  refine EvalAll.letE (Ra := fun r c1 => ScosAns n r x 𝒢 O ∧ c1 ≤ 200 * scosNodeS n + T 𝒢 O)
    (scosNode_call hm fun ca hca => (hrec _ _ _ _ hprob hsub le_rfl).mono
      fun w cb ⟨hans, hcb⟩ => ⟨hans, by have := scosNode_wtAns hans; omega⟩) ?_
  rintro r c1 ⟨hans, hc1⟩
  rcases hans with ⟨rfl, hemp⟩ | ⟨z, hz, lv, rfl, hlv, hlvw⟩
  · -- The subcoset on `O` is empty, so the subcoset on `Φ` is empty.
    have hl := Det.length (Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ,
      scosInd O], .list []]) (i := 1) rfl)
    refine scosNode_ite hl fun cc hcc => ?_
    simp only [List.length_nil, if_pos]
    refine (Det.var' (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ, scosInd O],
      .list []]) (i := 1) rfl).post fun c' hc' => ⟨Or.inl ⟨rfl, scosC_split_empty hsub.subset hemp⟩,
        ?_⟩
    simp only [wt_list_nil, List.length_nil] at hcc hc' ⊢
    omega
  · -- The subcoset on `O` is `z L(𝒢, O)`: solve `[lv, z, Φ \ O]`.
    have hR : (Val.list [encPerm (nintSum z), lv]).wt ≤ 5 * scosNodeS n := by
      have := wt_list2_le (encPerm (nintSum z)) lv
      have := scosNode_wtPerm (nintSum z)
      have := scosNode_W n
      omega
    have hl := Det.length (Det.var' (P := 𝒫) (env := [.list [encGroup gs, encPerm (nintSum x), scosInd Φ,
      scosInd O], .list [encPerm (nintSum z), lv]]) (i := 1) rfl)
    refine scosNode_ite hl fun cc hcc => ?_
    rw [if_neg (by simp)]
    have g1 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ, scosInd O],
        .list [encPerm (nintSum z), lv]] (.get (.var 1) (.nat 1)) lv _ :=
      Det.get' (Det.var' (i := 1) rfl) (Det.nat 1) rfl
    have g0 : Det 𝒫 [.list [encGroup gs, encPerm (nintSum x), scosInd Φ, scosInd O],
        .list [encPerm (nintSum z), lv]] (.get (.var 1) (.nat 0)) (encPerm (nintSum z)) _ :=
      Det.get' (Det.var' (i := 1) rfl) (Det.nat 0) rfl
    have sd := scosNode_subDet (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)
      (rest := [.list [encPerm (nintSum z), lv]]) hsub.subset hU
    have hm2 := Det.mk3 g1 g0 sd
    have hw3 := wt_list3_le lv (encPerm (nintSum z)) (scosInd (Φ \ O))
    have hwz := scosNode_wtPerm (nintSum z)
    have hwd := scosNode_wtInd (Φ \ O)
    have hWS := scosNode_W n
    have hprob2 : ScosProb n (.list [lv, encPerm (nintSum z), scosInd (Φ \ O)]) (scosL 𝒢 O) z
        (Φ \ O) :=
      ⟨⟨lv, rfl, hlv, hlvw⟩, scosInv_mono (scosInv_sdiff hinv hO) (scosL_le _ _),
        scosNode_solv (scosL_le _ _) hsolv⟩
    refine scosNode_call hm2 fun ca2 hca2 => ?_
    refine (hrec _ _ _ _ hprob2 (Finset.sdiff_ssubset hsub.subset hOne) (scosL_le _ _)).mono
      fun w cb ⟨hans, hcb⟩ => ⟨scosNode_ans_split hinv hO hsub.subset hz hans, ?_⟩
    have := scosNode_wtAns hans
    simp only [List.length_cons, List.length_nil] at hcc
    omega

end Steps

end GI.Impl
