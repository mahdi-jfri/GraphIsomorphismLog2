import Workspace.Impl.TermGlueLabPXLab

/-!
# The stabilizer generators `b_j` from the `N`-test table

Step 5 of the label program. The coordinates of `A/B(x)` need generators of the
groups `Aut_N(x_i)` (their images generate `B(x)`, `tmGLP_label_closure`). The `N`-test table
already holds them: entry `i + 2 q i` answers `Iso_N(x_i, x_i) = Aut_N(x_i)` by a stored coset
`[x, encGroup gs]`, so `⟨gs⟩ = Aut_N(x_i)`. The program `tmGLPBsFuns` reads these entries for
`i = 0, …, q - 1` and appends the generator lists (with the leading `1` of `encGroup`).
`tmGLPBs_spec`: the result is `[b_j]` with `TmGLPBsOut`: every `b_j` lies in some `Aut_N(x_i)`,
and every `Aut_N(x_i)` lies in `⟨b_j⟩`. No string call.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]

/-- The index `i + 2 q i` of the entry `(x_i, x_i)`, on the step argument `[[us, q], i, acc]`. -/
def tmGLPBsIdx : Expr :=
  .arith .add (arg 1) (.arith .mul (.arith .mul (.nat 2) (.get (arg 0) (.nat 1))) (arg 1))

/-- One step: append the generator list of the entry `(x_i, x_i)`. -/
def tmGLPBsStep (app : ℕ) : Expr :=
  .call app (mk2 (arg 2)
    (.get (.get (.get (.get (arg 0) (.nat 0)) tmGLPBsIdx) (.nat 1)) (.nat 1)))

/-- **The stabilizer generators** (3 + 3 functions), on `[us, q]`. -/
def tmGLPBsFuns (b : ℕ) : List Expr :=
  loopFuns b (.get (.var 0) (.nat 1)) .nil (tmGLPBsStep (b + 3)) ++ appendFuns (b + 3)

theorem length_tmGLPBsFuns (b : ℕ) : (tmGLPBsFuns b).length = 6 := rfl

/-- **The facts of the result**: the `b_j` lie in the groups `Aut_N(x_i)` and generate them. -/
def TmGLPBsOut (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω)
    (bs : List (Perm (Fin n))) : Prop :=
  (∀ b ∈ bs, ∃ j : Fin q, b ∈ Aut N (X j)) ∧
    ∀ j : Fin q, (Aut N (X j) : Set (Perm (Fin n))) ⊆ Subgroup.closure {b | b ∈ bs}

/-- The state after the rows `j < i`. -/
def TmGLPBsInv (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (B i : ℕ) (acc : Val) :
    Prop :=
  ∃ bs : List (Perm (Fin n)), acc = .list (bs.map encPerm) ∧
    (Val.list (bs.map encPerm)).wt ≤ 4 + i * B ∧ (∀ b ∈ bs, ∃ j : Fin q, b ∈ Aut N (X j)) ∧
    ∀ j : Fin q, j.1 < i → (Aut N (X j) : Set (Perm (Fin n))) ⊆ Subgroup.closure {b | b ∈ bs}

/-- The cost bound. -/
def tmGLPBsC (W : ℕ) : ℕ := 10 ^ 6 * (W + 1) ^ 4

/-- The diagonal entry of the table is a stored coset whose group is `Aut_N(x_i)`. -/
theorem tmGLP_diag_entry {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} {us : List Val}
    (hT : TmGLPTestOK N X us) (i : Fin q) :
    ∃ (x : Perm (Fin n)) (gs : List (Perm (Fin n))),
      us[i.1 + 2 * q * i.1]? = some (.list [encPerm x, encGroup gs]) ∧
      ∀ g, g ∈ gens gs ↔ g ∈ Aut N (X i) := by
  obtain ⟨u, hu, hA⟩ := hT i i
  rcases hA with ⟨-, hA⟩ | ⟨x, gs, rfl, -, -⟩
  · have h1 : (1 : Perm (Fin n)) ∈ Iso N (X i) (X i) := by
      rw [iso_self]; exact (Aut N (X i)).one_mem
    rw [hA] at h1
    exact absurd h1 (Set.notMem_empty _)
  · obtain ⟨u', hu', hA'⟩ := hT i i
    rw [hu] at hu'
    cases hu'
    exact ⟨x, gs, hu, tmCs_gens_aut (tmCs_ansC_cons hA' rfl)⟩

private theorem tmGLP_bs_ar1 {i q W : ℕ} (hi : i < q) (hq : q < W) : i * W + W ≤ W * W := by
  have : (i + 1) * W ≤ W * W := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, one_mul] at this
  exact this

private theorem tmGLP_bs_ar2 {L X W : ℕ} (hL : L ≤ W) (hX : X ≤ 10 * (W + 1) ^ 2) :
    loopModK * (L + 1) * X ≤ 10 ^ 4 * (W + 1) ^ 3 := by
  unfold loopModK
  rw [Nat.mul_assoc]
  calc 1000 * ((L + 1) * X) ≤ 1000 * ((W + 1) * (10 * (W + 1) ^ 2)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) hX)
    _ = 10 ^ 4 * (W + 1) ^ 3 := by ring

private theorem tmGLP_bs_ar3 {q W c L : ℕ} (hq : q < W)
    (hc : c ≤ q * (10 ^ 5 * (W + 1) ^ 3) + L)
    (hL : L ≤ loopModK * (q + 1) * (W + q + (4 + W * W) + 1)) :
    c ≤ 10 ^ 6 * (W + 1) ^ 4 := by
  have h1 : q * (10 ^ 5 * (W + 1) ^ 3) ≤ (W + 1) * (10 ^ 5 * (W + 1) ^ 3) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : loopModK * (q + 1) * (W + q + (4 + W * W) + 1) ≤
      1000 * ((W + 1) * (6 * (W + 1) ^ 2)) := by
    rw [Nat.mul_assoc]; unfold loopModK
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by nlinarith))
  have h3 : (W + 1) ^ 3 ≤ (W + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have e1 : (W + 1) * (10 ^ 5 * (W + 1) ^ 3) = 10 ^ 5 * (W + 1) ^ 4 := by ring
  have e2 : (W + 1) * (6 * (W + 1) ^ 2) = 6 * (W + 1) ^ 3 := by ring
  rw [e1] at h1
  rw [e2] at h2
  generalize (W + 1) ^ 3 = C3 at *
  generalize (W + 1) ^ 4 = C4 at *
  omega

/-- **The stabilizer generators.** On `[us, q]` with `us` a `TmGLPTestOK` table, the module at
`b` returns `[b_j]` with `TmGLPBsOut`. -/
theorem tmGLPBs_spec {P : Program} {b : ℕ} (h : P.HasAt b (tmGLPBsFuns b))
    {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} {us : List Val}
    (hT : TmGLPTestOK N X us) :
    FunAll P b (.list [.list us, .nat q]) (fun w c => ∃ bs : List (Perm (Fin n)),
      w = .list (bs.map encPerm) ∧ TmGLPBsOut N X bs ∧
        c ≤ tmGLPBsC (Val.list [.list us, .nat q]).wt) := by
  set a : Val := .list [.list us, .nat q] with ha
  have hloop : P.HasAt b (loopFuns b (.get (.var 0) (.nat 1)) .nil (tmGLPBsStep (b + 3))) := h.left
  have happ : P.HasAt (b + 3) (appendFuns (b + 3)) := h.right
  have hk := Det.get' (Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl) (Det.nat 1)
    (vs := [.list us, .nat q]) (v := .nat q) rfl
  set W := a.wt with hW
  have wus : (Val.list us).wt < W := wt_le_wt_list (by simp)
  have hqus := tmGLP_test_len hT
  have lus := length_lt_wt_list us
  have hqW : q < W := by omega
  have hM : ∀ i acc, i ≤ q → TmGLPBsInv N X W i acc → acc.wt ≤ 4 + W * W := by
    rintro i acc hi ⟨bs, rfl, hw, -⟩
    have : i * W ≤ W * W := Nat.mul_le_mul_right _ (by omega)
    omega
  refine (loopBdd_spec hloop hk Det.nil (by have := wt_nat_le q; omega) (M := 4 + W * W)
    (Inv := TmGLPBsInv N X W)
    ⟨[], rfl, by simp, fun _ hb => absurd hb List.not_mem_nil,
      fun _ hj => absurd hj (Nat.not_lt_zero _)⟩ hM
    (D := fun _ => 10 ^ 5 * (W + 1) ^ 3) ?_).mono ?_
  · rintro i acc hi ⟨bs, rfl, hbw, hbA, hbG⟩
    obtain ⟨x, gs, hu, hgs⟩ := tmGLP_diag_entry hT ⟨i, hi⟩
    set ys : List Val := (1 :: gs).map encPerm with hys
    have eG : encGroup gs = .list [.nat n, .list ys] := rfl
    set A : Val := .list [a, .nat i, .list (bs.map encPerm)] with hA
    have g0 := Det.arg' (P := P) (vs := [a, .nat i, .list (bs.map encPerm)]) (rest := []) (j := 0) rfl
    have g1 := Det.arg' (P := P) (vs := [a, .nat i, .list (bs.map encPerm)]) (rest := []) (j := 1) rfl
    have g2 := Det.arg' (P := P) (vs := [a, .nat i, .list (bs.map encPerm)]) (rest := []) (j := 2) rfl
    have dus := Det.get' g0 (Det.nat 0) (vs := [.list us, .nat q]) (v := .list us) rfl
    have dq := Det.get' g0 (Det.nat 1) (vs := [.list us, .nat q]) (v := .nat q) rfl
    have d2q := Det.arith' (op := .mul) (Det.nat 2) dq (z := 2 * q) rfl
    have dm := Det.arith' (op := .mul) d2q g1 (z := 2 * q * i) rfl
    have didx := Det.arith' (op := .add) g1 dm (z := i + 2 * q * i) rfl
    have du := Det.get' dus didx hu
    have dg := Det.get' du (Det.nat 1) (vs := [encPerm x, encGroup gs]) (v := encGroup gs) rfl
    have dg' : Det P [A] _ (.list [.nat n, .list ys]) _ := dg
    have dl := Det.get' dg' (Det.nat 1) (vs := [.nat n, .list ys]) (v := .list ys) rfl
    have dargs := Det.mk2 g2 dl
    -- weights
    have wu : (Val.list [encPerm x, encGroup gs]).wt < (Val.list us).wt :=
      wt_le_wt_list (List.mem_of_getElem? hu)
    have wg : (encGroup gs).wt < (Val.list [encPerm x, encGroup gs]).wt := wt_le_wt_list (by simp)
    have wl : (Val.list ys).wt < (encGroup gs).wt := by rw [eG]; exact wt_le_wt_list (by simp)
    have lys := length_lt_wt_list ys
    have har := tmGLP_bs_ar1 hi hqW
    have wnew : (Val.list (bs.map encPerm ++ ys)).wt ≤ 4 + (i * W + W) := by
      have := wt_list_append_le (bs.map encPerm) ys
      omega
    have wnew' : (Val.list (bs.map encPerm ++ ys)).wt ≤ 4 + W * W := by omega
    have w2 := wt_list2_le (.list (bs.map encPerm)) (.list ys)
    have hap := append_spec happ (bs.map encPerm) ys
    have hapB : FunAll P (b + 3) (.list [.list (bs.map encPerm), .list ys]) (fun w c =>
        w = .list (bs.map encPerm ++ ys) ∧ c ≤ 10 ^ 4 * (W + 1) ^ 3) := by
      refine FunAll.mono hap fun w c ⟨hw, hc⟩ => ⟨hw, hc.trans (tmGLP_bs_ar2 (by omega) ?_)⟩
      subst hw
      have hS : W * W ≤ (W + 1) ^ 2 :=
        (Nat.mul_le_mul (Nat.le_succ W) (Nat.le_succ W)).trans_eq (sq _).symm
      have hS1 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      have h2 := (Val.list us).two_le_size
      have h3 := (Val.list us).size_le_wt
      have hS2 : 16 ≤ (W + 1) ^ 2 :=
        (Nat.mul_le_mul (show 4 ≤ W + 1 by omega) (show 4 ≤ W + 1 by omega)).trans_eq (sq _).symm
      omega
    have dcall := Det.call dargs hapB
    refine dcall.post fun c hc => ⟨⟨bs ++ 1 :: gs, by rw [List.map_append], ?_, ?_, ?_⟩, ?_⟩
    · rw [List.map_append, Nat.add_mul, one_mul]; omega
    · intro b' hb'
      rcases List.mem_append.1 hb' with hb' | hb'
      · exact hbA b' hb'
      · refine ⟨⟨i, hi⟩, ?_⟩
        rcases List.mem_cons.1 hb' with rfl | hb'
        · exact (Aut N (X ⟨i, hi⟩)).one_mem
        · exact (hgs b').1 (Subgroup.subset_closure hb')
    · intro j hj g hg
      have hsub : {b | b ∈ bs} ⊆ {b | b ∈ bs ++ 1 :: gs} := fun b' hb' =>
        List.mem_append_left _ hb'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact Subgroup.closure_mono hsub (hbG j hj hg)
      · have hj' : j = ⟨i, hi⟩ := Fin.ext hj
        subst hj'
        have hg' : g ∈ gens gs := (hgs g).2 hg
        have hle : gens gs ≤ Subgroup.closure {b | b ∈ bs ++ 1 :: gs} := by
          refine Subgroup.closure_le _ |>.2 fun b' hb' => Subgroup.subset_closure ?_
          exact List.mem_append_right _ (List.mem_cons_of_mem _ hb')
        exact hle hg'
    · -- the cost of the step
      have wA := wt_stepArg_le a i (.list (bs.map encPerm))
      have wi := wt_nat_le i
      have wq := wt_nat_le q
      have w2q := wt_nat_le (2 * q)
      have w2qi := wt_nat_le (2 * q * i)
      have wiq := wt_nat_le (i + 2 * q * i)
      have hqi : 2 * q * i ≤ 2 * (W * W) := by
        have : q * i ≤ W * W := Nat.mul_le_mul (by omega) (by omega)
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ this
      have hS : W * W ≤ (W + 1) ^ 2 :=
        (Nat.mul_le_mul (Nat.le_succ W) (Nat.le_succ W)).trans_eq (sq _).symm
      have hS1 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      have hS3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have ewA : A.wt = (Val.list [a, .nat i, .list (bs.map encPerm)]).wt := rfl
      beta_reduce
      generalize 2 * q * i = QI at *
      generalize W * W = WW at *
      generalize (W + 1) ^ 2 = S2 at *
      generalize (W + 1) ^ 3 = S3 at *
      omega
  · rintro u c ⟨⟨bs, rfl, -, hbA, hbG⟩, hc⟩
    refine ⟨bs, rfl, ⟨hbA, fun j => hbG j j.2⟩, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    exact tmGLP_bs_ar3 hqW hc le_rfl

end GI.Impl
