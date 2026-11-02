import Workspace.Impl.TermSupSearchStep

/-!
# T4, the search as a function

The proof of Lemma A.19: "If `K` is not nilpotent, choose a nonnormal Sylow subgroup `P` of
`K`." The function `supFindBody`, on `gens K`, runs the search step (`supSearchBody`) for
`d = 0, 1, …, n`, starting from the state `[|K|, 0, 0, 0]` (the cited **GroupOrder**).

`supFind_spec`: the result satisfies `SupSearchInv K (n + 1)`. So either it is `[0, 1, p, P]`
with `P` a Sylow `p`-subgroup of `K` that `K` does not normalize, or it is `[r, 0, 0, 0]` and
`K` is nilpotent (`sup_sieve_end`).
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- **The search** on `gens K`. -/
def supFindBody (it jord : ℕ) : Expr :=
  .call it (mk3 (.var 0) (.arith .add (.get (.var 0) (.nat 0)) (.nat 1))
    (mk4 (.prim jord (.var 0)) (.nat 0) (.nat 0) (.nat 0)))

/-- Where the search function and its modules sit. -/
structure SupFindAt (P : Program) (f it g mg le jsy jnc jord jm : ℕ) (hsy : SylowAlgo)
    (hnc : NormalClosure) (hord : GroupOrder) (hmem : Membership) : Prop where
  entry : P.funs[f]? = some (supFindBody it jord)
  iter : P.HasAt it (iterFuns it g)
  step : SupSearchAt P g mg le jsy jnc jord jm hsy hnc hord hmem

/-- The cost bound of the search. -/
def supFindCost (psy pnc pord pm : Prim) (n : ℕ) : ℕ :=
  (n + 2) * supSearchCost psy pnc pord pm n + 10 ^ 9 * (n + 1) ^ 7

/-- **The search.** -/
theorem supFind_spec {hsy : SylowAlgo} {hnc : NormalClosure} {hord : GroupOrder}
    {hmem : Membership} {P : Program} {f it g mg le jsy jnc jord jm : ℕ}
    (hP : SupFindAt P f it g mg le jsy jnc jord jm hsy hnc hord hmem)
    {ks : List (Perm (Fin n))} (hkl : ks.length ≤ n ^ 2) :
    FunAll P f (encGroup ks) (fun w c => SupSearchInv (gens ks) (n + 1) w ∧
      c ≤ supFindCost (sylowPrim hsy) (normalClosurePrim hnc) (groupOrderPrim hord)
        (membershipPrim hmem) n) := by
  have hKw := wt_encGroup_le_sq hkl
  have hn1 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have hn7 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  set Y := 10 ^ 4 * (n + 1) ^ 6 with hY
  set B := supSearchCost (sylowPrim hsy) (normalClosurePrim hnc) (groupOrderPrim hord)
    (membershipPrim hmem) n with hB
  have hYB : (groupOrderPrim hord).boundSize Y + Y ≤ B := by
    simp only [hB, supSearchCost]
    have : Y ≤ Y ^ 3 := Nat.le_self_pow (by norm_num) _
    rw [← hY]
    omega
  -- the argument of the loop
  have d0 := Det.var' (P := P) (env := [encGroup ks]) (i := 0) rfl
  have dn := Det.arith' (op := .add) (Det.encPerms_size d0) (Det.nat 1) (z := n + 1) rfl
  have dord := groupOrder_call hord hP.step.ord d0 (⟨ks, rfl, rfl⟩ : GroupVal n _ (gens ks))
  have hbo := (groupOrderPrim hord).bound_le (show (encGroup ks).size ≤ Y from
    (Val.size_le_wt _).trans (by omega))
  have d4 := Det.mk4 dord (Det.nat (P := P) (env := [encGroup ks]) 0) (Det.nat 0) (Det.nat 0)
  have darg := Det.mk3 d0 dn d4
  set acc0 : Val := .list [.nat (Nat.card (gens ks)), .nat 0, .nat 0, .nat 0] with hacc0
  have h0 : SupSearchInv (gens ks) 0 acc0 := Or.inl ⟨_, rfl, sup_sieve_zero _⟩
  have haw := sup_search_wt h0
  have hit := iter_spec hP.iter (c := encGroup ks) (k := n + 1) (M := 700 * (n + 1) ^ 6) h0
    (fun i acc _ h => sup_search_wt h)
    (fun i acc hi h => supSearch_step hP.step hkl (by omega) h)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hit
  have hw3 := wt_list3_le (encGroup ks) (.nat (n + 1)) acc0
  have hnw := wt_nat_le (n + 1)
  have hnK : (Val.nat n).wt < (encGroup ks).wt := wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have hn2 : n ^ 2 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  refine FunAll.intro hP.entry (EvalAll.call_funAll darg fun v ca hv => ?_)
  obtain ⟨rfl, hca⟩ := hv
  refine hit.mono fun w c h => ⟨h.1, ?_⟩
  have hww := sup_search_wt h.1
  have hc := h.2
  have hL : loopModK * (n + 1 + 1) * ((Val.list [encGroup ks, .nat (n + 1), acc0]).wt + (n + 1) +
      700 * (n + 1) ^ 6 + 1) ≤ 10 ^ 8 * (n + 1) ^ 7 := by
    have h1 : (Val.list [encGroup ks, .nat (n + 1), acc0]).wt + (n + 1) + 700 * (n + 1) ^ 6 + 1 ≤
        5000 * (n + 1) ^ 6 := by omega
    calc loopModK * (n + 1 + 1) * ((Val.list [encGroup ks, .nat (n + 1), acc0]).wt + (n + 1) +
          700 * (n + 1) ^ 6 + 1) ≤ loopModK * (2 * (n + 1)) * (5000 * (n + 1) ^ 6) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) h1
      _ = 10 ^ 7 * (n + 1) ^ 7 := by simp only [loopModK]; ring
      _ ≤ 10 ^ 8 * (n + 1) ^ 7 := Nat.mul_le_mul_right _ (by norm_num)
  have hNB : (n + 1) * B + B = (n + 2) * B := by ring
  unfold supFindCost
  rw [← hB]
  rw [← hB] at hc
  clear_value Y B acc0
  omega

end GI.Impl
