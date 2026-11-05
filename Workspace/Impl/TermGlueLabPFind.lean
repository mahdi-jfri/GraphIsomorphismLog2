module

public import Workspace.Impl.TermGlueLabPRel

@[expose] public section

/-!
# The type of a row from the stored coset table

Steps 2 and 3 of the label program. For a row `Z` with a known `w ∈ H` and
`Z^w = y_l`, the module `tmGLPFindFuns b rel` runs the reading of `TermGlueLabPRel` (at `rel`)
on the stored cosets `Iso_H(x_j, y_l)` for `j = 0, 1, …, q - 1` and stops at the first success.
The result is `[j, n]` with `j` the first row of `x` whose `N`-orbit holds `Z` and `n ∈ N`,
`x_j^n = Z` (`tmGLPFind_spec`). Since `j` is the first such row, `x_j` is the representative of
the type of `Z` ("the first row of type `a`").

The input is `[[gens N, vs, q, l], w]`, with `vs` the coset table (`TmCsTabOK`).
-/

namespace GI.Impl

open GI.Lang Equiv
open scoped GI.Multicoset
open GI.Cited (Val encPerm encGroup gens Membership NormalizedFactor)

/-! ### The program -/

/-- The context `[gens N, vs, q, l]`. -/
def tmGLPCtx {n : ℕ} (σN : List (Perm (Fin n))) (vs : List Val) (q l : ℕ) : Val :=
  .list [encGroup σN, .list vs, .nat q, .nat l]

/-- One try, on `[a, j]` with `a = [ctx, w]`: the reading at `rel` on the coset of `(j, l)`,
then `[j, n]` or `[]`. -/
def tmGLPTryF (rel : ℕ) : Expr :=
  .letE (.call rel (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (.get (.get (.get (arg 0) (.nat 0)) (.nat 1))
        (.arith .add (.arith .mul (arg 1) (.get (.get (arg 0) (.nat 0)) (.nat 2)))
          (.get (.get (arg 0) (.nat 0)) (.nat 3))))
      (.get (arg 0) (.nat 1))))
    (.ite (.length (.var 1)) (mk2 (arg 1) (.get (.var 1) (.nat 0))) .nil)

/-- The step of the search, on `[a, j, acc]`: keep a found answer, else try `j`. -/
def tmGLPFindStep (tr : ℕ) : Expr :=
  .ite (.length (arg 2)) (arg 2) (.call tr (mk2 (arg 0) (arg 1)))

/-- **The search** (4 functions), with the reading at `rel`. -/
def tmGLPFindFuns (b rel : ℕ) : List Expr :=
  loopFuns b (.get (.get (.var 0) (.nat 0)) (.nat 2)) .nil (tmGLPFindStep (b + 3)) ++
    [tmGLPTryF rel]

theorem length_tmGLPFindFuns (b rel : ℕ) : (tmGLPFindFuns b rel).length = 4 := rfl

/-! ### One try -/

variable {n : ℕ} {Ω : Type*} [GI.Multicoset.RAct (Perm (Fin n)) Ω]

/-- The result of one try at row `j`. -/
def TmGLPTryOut (N : Subgroup (Perm (Fin n))) (X Z : Ω) (j : ℕ) (u : Val) : Prop :=
  (u = .list [] ∧ ∀ x ∈ N, X ↼ x ≠ Z) ∨ (∃ x ∈ N, u = .list [.nat j, encPerm x] ∧ X ↼ x = Z)

/-- The cost bound of one try, for an input of weight `W`. -/
def tmGLPTryC (pm pf : Prim) (W : ℕ) : ℕ :=
  6 * tmGLPRelC pm pf (6 * W + 7) + 10 ^ 5 * (W + 1) ^ 2

set_option maxHeartbeats 2000000 in
/-- **One try**: the reading on the stored coset of `(j, l)`. -/
theorem tmGLPTry_spec (hm : Membership) (hfac : NormalizedFactor) {P : Program} {f rel jm jf : ℕ}
    (hf : P.funs[f]? = some (tmGLPTryF rel)) (hr : TmGLPRelAt P rel jm jf)
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {H : Subgroup (Perm (Fin n))} {σN : List (Perm (Fin n))} (hNH : gens σN ≤ H)
    (hn : GI.Multicoset.Normalizes H (gens σN)) {q : ℕ} {X Y : Fin q → Ω} {vs : List Val}
    (hT : TmCsTabOK H X Y vs) (l : Fin q) {Z : Ω} {w : Perm (Fin n)} (hw : w ∈ H)
    (hZ : Z ↼ w = Y l) (j : Fin q) :
    FunAll P f (.list [.list [tmGLPCtx σN vs q l, encPerm w], .nat j])
      (fun u c => TmGLPTryOut (gens σN) (X j) Z j u ∧
        c ≤ tmGLPTryC (membershipPrim hm) (normalizedFactorPrim hfac)
          (Val.list [.list [tmGLPCtx σN vs q l, encPerm w], .nat j]).wt) := by
  obtain ⟨v, hv, hvA⟩ := hT.2 j l
  set ctx := tmGLPCtx σN vs q l with hctx
  set a : Val := .list [ctx, encPerm w] with ha
  set A : Val := .list [a, .nat j] with hA
  apply FunAll.intro hf
  have g0 := Det.arg' (P := P) (vs := [a, .nat j]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [a, .nat j]) (rest := []) (j := 1) rfl
  have dc := Det.get' g0 (Det.nat 0) (vs := [ctx, encPerm w]) (v := ctx) rfl
  have dN := Det.get' dc (Det.nat 0) (vs := [encGroup σN, .list vs, .nat q, .nat l])
    (v := encGroup σN) rfl
  have dvs := Det.get' dc (Det.nat 1) (vs := [encGroup σN, .list vs, .nat q, .nat l])
    (v := .list vs) rfl
  have dq := Det.get' dc (Det.nat 2) (vs := [encGroup σN, .list vs, .nat q, .nat l])
    (v := .nat q) rfl
  have dl := Det.get' dc (Det.nat 3) (vs := [encGroup σN, .list vs, .nat q, .nat l])
    (v := .nat l) rfl
  have dk := Det.arith' (op := .add) (Det.arith' (op := .mul) g1 dq (z := j * q) rfl) dl
    (z := j * q + l) rfl
  have dv := Det.get' dvs dk hv
  have dw := Det.get' g0 (Det.nat 1) (vs := [ctx, encPerm w]) (v := encPerm w) rfl
  have dargs := Det.mk3 dN dv dw
  -- weights
  have wa : a.wt < A.wt := wt_le_wt_list (by simp [hA])
  have wc : ctx.wt < a.wt := wt_le_wt_list (by simp [ha])
  have ww : (encPerm w).wt < a.wt := wt_le_wt_list (by simp [ha])
  have wN : (encGroup σN).wt < ctx.wt := wt_le_wt_list (by simp [hctx, tmGLPCtx])
  have wvs : (Val.list vs).wt < ctx.wt := wt_le_wt_list (by simp [hctx, tmGLPCtx])
  have wv : v.wt < (Val.list vs).wt := wt_le_wt_list (List.mem_of_getElem? hv)
  have lvs := length_lt_wt_list vs
  have hq : q ≤ vs.length := by
    rw [hT.1]; exact Nat.le_mul_of_pos_left q (Nat.pos_of_ne_zero (by rintro rfl; exact j.elim0))
  have hjq : j.1 * q ≤ q * q := Nat.mul_le_mul_right _ j.2.le
  have hl := l.2
  have hW3 := wt_list3_le (encGroup σN) v (encPerm w)
  have eA : A.wt = (Val.list [a, .nat j]).wt := rfl
  have hrel : EvalAll P [A] (.call rel (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (.get (.get (.get (arg 0) (.nat 0)) (.nat 1))
        (.arith .add (.arith .mul (arg 1) (.get (.get (arg 0) (.nat 0)) (.nat 2)))
          (.get (.get (arg 0) (.nat 0)) (.nat 3))))
      (.get (arg 0) (.nat 1))))
      (fun u c => TmGLPRelOut (gens σN) (X j) Z u ∧ u.wt < c ∧
        c ≤ 6 * tmGLPRelC (membershipPrim hm) (normalizedFactorPrim hfac) (6 * A.wt + 7) +
          10 ^ 4 * (A.wt + 1) ^ 2) := by
    refine EvalAll.call_funAll dargs fun v' ca hv' => ?_
    obtain ⟨rfl, hca⟩ := hv'
    refine FunAll.mono (FunAll.wt_lt (tmGLPRel_spec hm hfac hr hjm hjf hNH hn hvA hw hZ))
      fun u cu hu => ⟨hu.1.1, by omega, ?_⟩
    have hcu := hu.1.2
    have hwu := hu.2
    have hmono := tmGLPRelC_mono (membershipPrim hm) (normalizedFactorPrim hfac)
      (show (Val.list [encGroup σN, v, encPerm w]).wt ≤ 6 * A.wt + 7 by omega)
    have wq := wt_nat_le q
    have wl := wt_nat_le l
    have wj := wt_nat_le j
    have wjq := wt_nat_le (j * q)
    have a1 : A.wt + 1 ≤ (A.wt + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have a2 : q * q ≤ (A.wt + 1) ^ 2 := by
      have : q ≤ A.wt + 1 := by omega
      calc q * q ≤ (A.wt + 1) * (A.wt + 1) := Nat.mul_le_mul this this
        _ = (A.wt + 1) ^ 2 := by ring
    have Bca : ca ≤ 100 * (A.wt + 1) ^ 2 := by
      clear hcu hwu hmono
      omega
    omega
  refine EvalAll.letE hrel fun u cu hu => ?_
  obtain ⟨hout, hwu, hcu⟩ := hu
  have du := Det.var' (P := P) (env := [A, u]) (i := 1) (v := u) rfl
  have a1 : A.wt + 1 ≤ (A.wt + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  rcases hout with ⟨rfl, hno⟩ | ⟨x, hx, rfl, hxZ⟩
  · refine (Det.ite_zero (t := mk2 (arg 1) (.get (.var 1) (.nat 0))) (Det.length du)
      (Det.nil (P := P))).post fun c hc => ⟨Or.inl ⟨rfl, hno⟩, ?_⟩
    simp only [List.length_nil, wt_list_nil] at hc ⊢
    unfold tmGLPTryC
    omega
  · have e1 := Det.arg' (P := P) (vs := [a, .nat j]) (rest := [.list [encPerm x]]) (j := 1) rfl
    have ex := Det.get' du (Det.nat 0) (vs := [encPerm x]) (v := encPerm x) rfl
    refine (Det.ite_pos (e := .nil) (Det.length du) (by simp) (Det.mk2 e1 ex)).post
      fun c hc => ⟨Or.inr ⟨x, hx, rfl, hxZ⟩, ?_⟩
    have hA' : (Val.list [a, .nat j]).wt = A.wt := rfl
    have w2 := wt_list2_le (.nat j) (encPerm x)
    have wj := wt_nat_le j
    have wx1 := wt_list1_le (encPerm x)
    have wx := wt_encPerm_le x
    have hn1 := tmGLP_n_lt_wt w
    have n2 : (n + 1) ^ 2 ≤ (A.wt + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    simp only [List.length_cons, List.length_nil] at hc
    unfold tmGLPTryC
    omega

theorem tmGLPTryC_mono (pm pf : Prim) {W V : ℕ} (h : W ≤ V) :
    tmGLPTryC pm pf W ≤ tmGLPTryC pm pf V := by
  unfold tmGLPTryC tmGLPRelC tmGLPRel2C; gcongr

/-! ### The search -/

/-- The state of the search after the rows `j < i`. -/
def TmGLPFindInv (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (Z : Ω) (i : ℕ)
    (acc : Val) : Prop :=
  (acc = .list [] ∧ ∀ j : Fin q, j.1 < i → ∀ x ∈ N, X j ↼ x ≠ Z) ∨
    (∃ j : Fin q, j.1 < i ∧ ∃ x ∈ N, acc = .list [.nat j, encPerm x] ∧ X j ↼ x = Z ∧
      ∀ j' : Fin q, j'.1 < j.1 → ∀ x ∈ N, X j' ↼ x ≠ Z)

/-- **The result of the search**: `[]` when no row of `x` has `Z` in its `N`-orbit, else
`[j, n]` with `j` the first such row, `n ∈ N` and `x_j^n = Z`. -/
def TmGLPFindOut (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (Z : Ω) (u : Val) :
    Prop :=
  (u = .list [] ∧ ∀ j : Fin q, ∀ x ∈ N, X j ↼ x ≠ Z) ∨
    (∃ j : Fin q, ∃ x ∈ N, u = .list [.nat j, encPerm x] ∧ X j ↼ x = Z ∧
      ∀ j' : Fin q, j'.1 < j.1 → ∀ x ∈ N, X j' ↼ x ≠ Z)

/-- The cost bound of the search, for an input of weight `W`. -/
def tmGLPFindC (pm pf : Prim) (W : ℕ) : ℕ :=
  (W + 1) * (3 * tmGLPTryC pm pf (4 * W + 10) + 10 ^ 3 * (W + 1)) + 10 ^ 7 * (W + 1) ^ 3

set_option maxHeartbeats 2000000 in
/-- **The search.** On `[[gens N, vs, q, l], w]`, with `vs` the coset table, `w ∈ H` and
`Z^w = y_l`, the result is `TmGLPFindOut`. -/
theorem tmGLPFind_spec (hm : Membership) (hfac : NormalizedFactor) {P : Program} {b rel jm jf : ℕ}
    (h : P.HasAt b (tmGLPFindFuns b rel)) (hr : TmGLPRelAt P rel jm jf)
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {H : Subgroup (Perm (Fin n))} {σN : List (Perm (Fin n))} (hNH : gens σN ≤ H)
    (hn : GI.Multicoset.Normalizes H (gens σN)) {q : ℕ} {X Y : Fin q → Ω} {vs : List Val}
    (hT : TmCsTabOK H X Y vs) (l : Fin q) {Z : Ω} {w : Perm (Fin n)} (hw : w ∈ H)
    (hZ : Z ↼ w = Y l) :
    FunAll P b (.list [tmGLPCtx σN vs q l, encPerm w]) (fun u c => TmGLPFindOut (gens σN) X Z u ∧
      c ≤ tmGLPFindC (membershipPrim hm) (normalizedFactorPrim hfac)
        (Val.list [tmGLPCtx σN vs q l, encPerm w]).wt) := by
  set ctx := tmGLPCtx σN vs q l with hctx
  set a : Val := .list [ctx, encPerm w] with ha
  have hloop : P.HasAt b (loopFuns b (.get (.get (.var 0) (.nat 0)) (.nat 2)) .nil
      (tmGLPFindStep (b + 3))) := h.left
  have htry : P.funs[b + 3]? = some (tmGLPTryF rel) := (h.block (gs := [tmGLPTryF rel]) 3 rfl).single
  have hk := Det.get' (Det.get' (Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl) (Det.nat 0)
    (vs := [ctx, encPerm w]) (v := ctx) rfl) (Det.nat 2)
    (vs := [encGroup σN, .list vs, .nat q, .nat l]) (v := .nat q) rfl
  -- weights
  have wc : ctx.wt < a.wt := wt_le_wt_list (by simp [ha])
  have ww : (encPerm w).wt < a.wt := wt_le_wt_list (by simp [ha])
  have wvs : (Val.list vs).wt < ctx.wt := wt_le_wt_list (by simp [hctx, tmGLPCtx])
  have wq : (Val.nat q).wt < ctx.wt := wt_le_wt_list (by simp [hctx, tmGLPCtx])
  have lvs := length_lt_wt_list vs
  have hq : q ≤ vs.length := by
    rw [hT.1]
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · simp [h0]
    · exact Nat.le_mul_of_pos_left q h0
  have hn1 := tmGLP_n_lt_wt w
  have hqa : q < a.wt := by omega
  have a1 : a.wt + 1 ≤ (a.wt + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have n2 : (n + 1) ^ 2 ≤ (a.wt + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hM : ∀ i acc, i ≤ q → TmGLPFindInv (gens σN) X Z i acc → acc.wt ≤ 20 * (a.wt + 1) ^ 2 := by
    rintro i acc - (⟨rfl, -⟩ | ⟨j, -, x, -, rfl, -⟩)
    · simp only [wt_list_nil]; omega
    · have := wt_list2_le (.nat j) (encPerm x)
      have := wt_nat_le j
      have := wt_encPerm_le x
      have := j.2
      omega
  refine (loopBdd_spec hloop hk Det.nil (by have := wt_nat_le q; omega) (M := 20 * (a.wt + 1) ^ 2)
    (Inv := TmGLPFindInv (gens σN) X Z) (Or.inl ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩)
    hM (D := fun _ => 3 * tmGLPTryC (membershipPrim hm) (normalizedFactorPrim hfac) (4 * a.wt + 10) +
      10 ^ 3 * (a.wt + 1)) ?_).mono ?_
  · intro i acc hi hinv
    have hacc := hM i acc hi.le hinv
    have wi := wt_nat_le i
    rcases hinv with ⟨rfl, hno⟩ | ⟨j, hj, x, hx, rfl, hxZ, hmin⟩
    · -- nothing found yet: try row `i`
      have dl := Det.length (Det.arg' (P := P) (vs := [a, .nat i, .list []]) (rest := []) (j := 2) rfl)
      refine EvalAll.ite dl (fun _ _ h => ⟨0, h.1⟩) fun y cc hy => ?_
      obtain ⟨h1, h2⟩ := hy
      cases h1
      rw [show ([] : List Val).length = 0 from rfl, if_pos rfl]
      have dargs := Det.mk2 (Det.arg' (P := P) (vs := [a, .nat i, .list []]) (rest := []) (j := 0) rfl)
        (Det.arg' (P := P) (vs := [a, .nat i, .list []]) (rest := []) (j := 1) rfl)
      refine EvalAll.call_funAll dargs fun v ca hv => ?_
      obtain ⟨rfl, hca⟩ := hv
      have hspec := tmGLPTry_spec hm hfac htry hr hjm hjf hNH hn hT l hw hZ ⟨i, hi⟩
      refine FunAll.mono (FunAll.wt_lt hspec) fun u cu hu => ⟨?_, ?_⟩
      · rcases hu.1.1 with ⟨rfl, hno'⟩ | ⟨x, hx, rfl, hxZ⟩
        · refine Or.inl ⟨rfl, fun j hj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
          · exact hno j hj
          · have : j = ⟨i, hi⟩ := Fin.ext hj
            subst this; exact hno'
        · exact Or.inr ⟨⟨i, hi⟩, Nat.lt_succ_self i, x, hx, rfl, hxZ, fun j' hj' => hno j' hj'⟩
      · have hcu := hu.1.2
        have hwu := hu.2
        have hmono := tmGLPTryC_mono (membershipPrim hm) (normalizedFactorPrim hfac)
          (show (Val.list [a, .nat i]).wt ≤ 4 * a.wt + 10 by
            have := wt_list2_le a (.nat i); omega)
        have hl3 := wt_list3_le a (.nat i) (.list [])
        have hl2 := wt_list2_le a (.nat i)
        simp only [List.length_nil, wt_list_nil] at h2 hl3
        have e : (Val.list [Val.list [tmGLPCtx σN vs q l, encPerm w],
            Val.nat (⟨i, hi⟩ : Fin q)]).wt = (Val.list [a, .nat i]).wt := rfl
        rw [e] at hcu
        beta_reduce
        omega
    · -- already found: keep it
      have dacc := Det.arg' (P := P) (vs := [a, .nat i, .list [.nat j, encPerm x]]) (rest := [])
        (j := 2) rfl
      refine (Det.ite_pos (e := .call (b + 3) (mk2 (arg 0) (arg 1))) (Det.length dacc) (by simp)
        dacc).post fun c hc => ⟨Or.inr ⟨j, by omega, x, hx, rfl, hxZ, hmin⟩, ?_⟩
      have hl3 := wt_list3_le a (.nat i) (.list [.nat j, encPerm x])
      simp only [List.length_cons, List.length_nil] at hc
      beta_reduce
      have := Nat.zero_le (tmGLPTryC (membershipPrim hm) (normalizedFactorPrim hfac) (4 * a.wt + 10))
      have e2 : (a.wt + 1) ^ 2 = (a.wt + 1) * (a.wt + 1) := by ring
      omega
  · rintro u c ⟨hinv, hc⟩
    refine ⟨?_, ?_⟩
    · rcases hinv with ⟨rfl, hno⟩ | ⟨j, -, x, hx, rfl, hxZ, hmin⟩
      · exact Or.inl ⟨rfl, fun j => hno j j.2⟩
      · exact Or.inr ⟨j, x, hx, rfl, hxZ, hmin⟩
    · rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
      have h1 : (q + 1) * (a.wt + q + 20 * (a.wt + 1) ^ 2 + 1) ≤ (a.wt + 1) * (22 * (a.wt + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (a.wt + 1) * (22 * (a.wt + 1) ^ 2) = 22 * (a.wt + 1) ^ 3 := by ring
      have h3 : q * (3 * tmGLPTryC (membershipPrim hm) (normalizedFactorPrim hfac) (4 * a.wt + 10) +
          10 ^ 3 * (a.wt + 1)) ≤ (a.wt + 1) * (3 * tmGLPTryC (membershipPrim hm)
            (normalizedFactorPrim hfac) (4 * a.wt + 10) + 10 ^ 3 * (a.wt + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      unfold tmGLPFindC
      have h4 : loopModK * (q + 1) * (a.wt + q + 20 * (a.wt + 1) ^ 2 + 1) ≤
          1000 * (22 * (a.wt + 1) ^ 3) := by
        rw [Nat.mul_assoc]; unfold loopModK; omega
      generalize (3 * tmGLPTryC (membershipPrim hm) (normalizedFactorPrim hfac) (4 * a.wt + 10) +
        10 ^ 3 * (a.wt + 1)) = T at hc h3 ⊢
      generalize loopModK * (q + 1) * (a.wt + q + 20 * (a.wt + 1) ^ 2 + 1) = L at hc h4
      generalize (a.wt + 1) ^ 3 = C3 at h4 ⊢
      omega

end GI.Impl
