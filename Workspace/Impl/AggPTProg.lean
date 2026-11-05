module

public import Workspace.Impl.AggPT
public import Workspace.Impl.AggMTProg

@[expose] public section

/-!
# `P_T` in graph form, in `GI.Lang`

`ptFuns` on `[[k, q], pairs of G, indT T]` builds the generators of `M_T` (`cycGens_spec`) and
calls **Preimage** on the graph group of `G` (`graphPre_spec`). By `liftGroup_Pgrp` the output
pairs are the graph form of the lift of `P_T` (`ptGraph_spec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm GI.LocalGroups
open GI.Cited (Val encPerm gens Preimage)

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- The generators of `M_T`, as a list. -/
def mtGens (q : ℕ) (T : Finset (Fin q)) : List (Perm (Fin q)) :=
  (List.range (q ^ 3)).map (genOf T)

theorem gens_mtGens {q : ℕ} (T : Finset (Fin q)) : gens (mtGens q T) = MT T := by
  rw [← closure_genOf]
  unfold gens mtGens
  congr 1
  ext σ
  simp

/-- Every generator of `M_T` is the label part of a pair of the graph of `G`: it is even, and
`π` maps `G` onto the even permutations. -/
theorem mtGens_snd {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    (T : Finset (Fin L.q)) :
    ∀ m ∈ mtGens L.q T, ∃ p ∈ Subgroup.closure {p | p ∈ ps}, MonoidHom.snd _ _ p = m := by
  intro m hm
  have hMT : m ∈ MT T := by
    rw [← gens_mtGens]; exact Subgroup.subset_closure hm
  rw [MT_eq_KT] at hMT
  obtain ⟨-, -, hs⟩ := hMT
  obtain ⟨g, hg⟩ := L.π_surj ⟨m, mem_alternatingGroup.2 hs⟩
  refine ⟨(toFin e g, m), ?_, rfl⟩
  rw [hps, mem_graphOf]
  exact ⟨g, g.2, g.2, rfl, by rw [hg]⟩

/-- On `[[k, q], pairs, s]`. -/
def ptEntry (b : ℕ) : Expr :=
  .letE (.call (b + 1) (mk2 (.get (arg 0) (.nat 1)) (arg 2)))
    (.call (b + 13) (mk3 (arg 0) (arg 1) (.var 1)))

/-- The module at base `b`, with the cited primitive at `jpre`. -/
def ptFuns (b jpre : ℕ) : List Expr :=
  [ptEntry b] ++ cycGensFuns (b + 1) ++ graphPreFuns (b + 13) jpre

/-- The size parameter of the module. -/
def ptM (k q : ℕ) (ps : List (Perm (Fin k) × Perm (Fin q))) : ℕ := k + q + ps.length + 2

/-- The cost constant of the module. -/
def ptK : ℕ := 10 ^ 17

/-- **`P_T` in graph form.** From pairs `ps` of the graph of `G`, the module returns pairs of the
graph of the lift of `P_T` to `G`. The cost is one **Preimage** call plus `ptK * ptM ^ 24`. -/
theorem ptGraph_spec (h : Preimage) {P : Program} {b jpre : ℕ}
    (hb : P.HasAt b (ptFuns b jpre)) (hj : P.prims[jpre]? = some (preimagePrim h))
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    (πd : S.domGroup →* alternatingGroup (Fin L.q))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) (T : Finset (Fin L.q)) :
    FunAll P b (.list [.list [.nat k, .nat L.q], .list (ps.map pairV), indT T])
      (fun w c => ∃ qs : List (Perm (Fin k) × Perm (Fin L.q)), w = .list (qs.map pairV) ∧
        qs.length ≤ (k + L.q) ^ 2 ∧
        PairGens e L (S.liftGroup (Pgrp S.domGroup πd T)) qs ∧
        c ≤ (preimagePrim h).bound (preimageEnc (pairInst (MonoidHom.snd _ _) ps
          (mtGens L.q T) (mtGens_snd hps T))) + ptK * ptM k L.q ps ^ 24) := by
  have hentry : P.funs[b]? = some (ptEntry b) := by
    simpa using (hb.block 0 (gs := [ptEntry b]) (by rfl)).single
  have hcy : P.HasAt (b + 1) (cycGensFuns (b + 1)) := hb.block 1 (by rfl)
  have hgp : P.HasAt (b + 13) (graphPreFuns (b + 13) jpre) := hb.block 13 (by rfl)
  set A : Val := .list [.list [.nat k, .nat L.q], .list (ps.map pairV), indT T] with hA
  set MS : Val := .list ((mtGens L.q T).map encPerm) with hMS
  have gq := Det.get' (Det.arg' (P := P) (vs := [.list [.nat k, .nat L.q], .list (ps.map pairV),
    indT T]) (rest := []) (j := 0) rfl) (Det.nat 1) (v := .nat L.q) rfl
  have gs := Det.arg' (P := P) (vs := [.list [.nat k, .nat L.q], .list (ps.map pairV),
    indT T]) (rest := []) (j := 2) rfl
  have hC := cycGens_spec hcy T
  have eM : Val.list ((List.range (L.q ^ 3)).map fun t => encPerm (genOf T t)) = MS := by
    simp [hMS, mtGens]
  rw [eM] at hC
  have d1 := Det.call (Det.mk2 gq gs) hC
  have hG := graphPre_spec h hgp hj ps (mtGens L.q T) (mtGens_snd hps T)
  have dI := Det.mk3 (Det.arg' (P := P) (vs := [.list [.nat k, .nat L.q], .list (ps.map pairV),
    indT T]) (rest := [MS]) (j := 0) rfl) (Det.arg' (P := P) (vs := [.list [.nat k, .nat L.q],
    .list (ps.map pairV), indT T]) (rest := [MS]) (j := 1) rfl)
    (Det.var' (P := P) (env := [A, MS]) (i := 1) rfl)
  refine FunAll.intro hentry (EvalAll.letE d1 fun _ _ h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.call_funAll dI fun _ _ h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  refine hG.mono fun w c hw => ?_
  obtain ⟨qs, rfl, hl, hcl, hc⟩ := hw
  refine ⟨qs, rfl, hl, ?_, ?_⟩
  · have := pairGens_of_pre hps hcl
    rwa [gens_mtGens, inf_eq_right.2 (fun g hg => hg.1), ← liftGroup_Pgrp πd hπ] at this
  · set M := ptM k L.q ps with hM
    have hMd : k + L.q + ps.length + 2 = M := rfl
    have n1 : 1 ≤ M := by omega
    have pw : ∀ a b : ℕ, a ≤ b → M ^ a ≤ M ^ b := fun a b hab => Nat.pow_le_pow_right n1 hab
    have pl : ∀ x n, x ≤ M → x ^ n ≤ M ^ n := fun x n hx => Nat.pow_le_pow_left hx n
    -- the weights
    have wps : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := by
      have := wt_pairList_le ps
      have := pl (pM k L.q ps) 3 (by unfold pM; omega)
      omega
    have wI := wt_indT_le T
    have wkq := wt_list2_le (.nat k) (.nat L.q)
    have wk := wt_nat_le k
    have wq := wt_nat_le L.q
    have wA := wt_list3_le (.list [.nat k, .nat L.q]) (.list (ps.map pairV)) (indT T)
    have wqI := wt_list2_le (.nat L.q) (indT T)
    have q3 : L.q ^ 3 ≤ M ^ 3 := pl _ 3 (by omega)
    have wMS : MS.wt ≤ 9 * M ^ 5 + 4 := by
      have h1 := wt_list_map_le (mtGens L.q T) encPerm (W := 4 * (L.q + 1) ^ 2)
        fun m _ => wt_encPerm_le m
      have hlen : (mtGens L.q T).length = L.q ^ 3 := by simp [mtGens]
      rw [hlen] at h1
      have h2 : L.q ^ 3 * (2 * (4 * (L.q + 1) ^ 2) + 1) ≤ M ^ 3 * (9 * M ^ 2) :=
        Nat.mul_le_mul q3 (by
          have := pl (L.q + 1) 2 (by omega)
          have : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ n1
          omega)
      have h3 : M ^ 3 * (9 * M ^ 2) = 9 * M ^ 5 := by ring
      rw [hMS]; omega
    have wB := wt_list3_le (.list [.nat k, .nat L.q]) (.list (ps.map pairV)) MS
    have wQ : (Val.list (qs.map pairV)).wt ≤ 400 * M ^ 6 := by
      have h1 := wt_pairList_le qs
      have h2 : pM k L.q qs ≤ 2 * M ^ 2 := by
        have : (k + L.q) ^ 2 ≤ M ^ 2 := pl _ 2 (by omega)
        have : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
        unfold pM; omega
      have h3 := Nat.pow_le_pow_left h2 3
      have e : (2 * M ^ 2) ^ 3 = 8 * M ^ 6 := by ring
      omega
    -- the costs
    have cC : cycGensCost L.q ≤ 10 ^ 13 * M ^ 24 := by
      unfold cycGensCost
      exact Nat.mul_le_mul_left _ ((pl _ 9 (by omega)).trans (pw 9 24 (by omega)))
    have cP : graphPreK * preM k L.q ps (mtGens L.q T) ^ 8 ≤ graphPreK * (256 * M ^ 24) := by
      refine Nat.mul_le_mul_left _ ?_
      have hlen : (mtGens L.q T).length = L.q ^ 3 := by simp [mtGens]
      have h1 : preM k L.q ps (mtGens L.q T) ≤ 2 * M ^ 3 := by
        unfold preM
        rw [hlen]
        have : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) M
        omega
      calc preM k L.q ps (mtGens L.q T) ^ 8 ≤ (2 * M ^ 3) ^ 8 := Nat.pow_le_pow_left h1 8
        _ = 256 * M ^ 24 := by ring
    have m1 : M ^ 3 ≤ M ^ 24 := pw 3 24 (by omega)
    have m2 : M ^ 5 ≤ M ^ 24 := pw 5 24 (by omega)
    have m3 : M ^ 6 ≤ M ^ 24 := pw 6 24 (by omega)
    have m4 : M ≤ M ^ 24 := (Nat.le_self_pow (by norm_num) M).trans (pw 1 24 (by omega))
    simp only [ptK, graphPreK] at *
    omega

end GI.Impl
