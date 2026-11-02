import Workspace.Impl.TermGlueLabPOffR

/-!
# The transporters `t_a(h)` for one element `h`: all rows

Step 3 of the label program. The module `tmGLPOffFuns b find rel` runs the row
program of `TermGlueLabPOffR` for every row `i < q` and collects the results
(`tmGLPOff_spec`). Entry `i` of the result is the search result for `x_J^h`, with `x_J` the
first row of the type of `x_i`: `[j, s_i]` with `x_j` the first row of the type of `x_J^h` and
`x_J^h = x_j^{s_i}`. These are the row-by-row transporters of `tmGLP_u_rows`, and, when every
type is distinct, the `j`'s give the permutation of the types whose sign is `ε(h)`.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens Membership NormalizedFactor)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]

/-- One step, on `[a, i, acc]`. -/
def tmGLPOStep (row : ℕ) : Expr := .snoc (arg 2) (.call row (mk2 (arg 0) (arg 1)))

/-- **The transporters for one `h`** (5 functions): the loop, the row program at `b + 3` and
the first-column search at `b + 4`. The search is at `find`, the reading at `rel`. -/
def tmGLPOffFuns (b find rel : ℕ) : List Expr :=
  loopFuns b (.get (.var 0) (.nat 2)) .nil (tmGLPOStep (b + 3)) ++
    [tmGLPORowF (b + 4) find rel, tmCsFirstF (b + 4)]

theorem length_tmGLPOffFuns (b find rel : ℕ) : (tmGLPOffFuns b find rel).length = 5 := rfl

/-- The state after the rows `k < i`. -/
def TmGLPOInv (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (h : Perm (Fin n))
    (B i : ℕ) (acc : Val) : Prop :=
  ∃ l : List Val, acc = .list l ∧ l.length = i ∧ (∀ v ∈ l, v.wt ≤ B) ∧
    ∀ k : Fin q, k.1 < i → ∃ v, l[k.1]? = some v ∧ TmGLPOItem N X h k v

/-- **The result for one `h`**: one search result per row (`TmGLPOItem`). -/
def TmGLPOOut (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (h : Perm (Fin n))
    (u : Val) : Prop :=
  ∃ l : List Val, u = .list l ∧ l.length = q ∧
    ∀ k : Fin q, ∃ v, l[k.1]? = some v ∧ TmGLPOItem N X h k v

/-- The cost bound, for an input of weight `W`. -/
def tmGLPOffC (pm pf : Prim) (W : ℕ) : ℕ :=
  (W + 1) * (2 * tmGLPORowC pm pf W + 10 ^ 4 * (W + 1) ^ 3) + 10 ^ 6 * (W + 1) ^ 4

set_option maxHeartbeats 4000000 in
/-- **The transporters for one `h ∈ H`.** On `[gens N, vs, q, xl, h⁻¹]`, with `vs` the coset
table of `x, y` (a nonempty entry in every row) and `xl` the labels of `x`, the result holds
the search result for `x_J^h` for every row (`TmGLPOOut`). -/
theorem tmGLPOff_spec (hm : Membership) (hfac : NormalizedFactor) {P : Program}
    {b find rel jm jf : ℕ} (h : P.HasAt b (tmGLPOffFuns b find rel))
    (hfd : P.HasAt find (tmGLPFindFuns find rel)) (hr : TmGLPRelAt P rel jm jf)
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {H : Subgroup (Perm (Fin n))} {σN : List (Perm (Fin n))} (hNH : gens σN ≤ H)
    (hn : GI.Multicoset.Normalizes H (gens σN)) {q : ℕ} {X Y : Fin q → Ω} {vs : List Val}
    (hT : TmCsTabOK H X Y vs) (hY : ∀ j : Fin q, ∃ l : Fin q, (Iso H (X j) (Y l)).Nonempty)
    {xl : List Val} (hxl : TmGLPXOut (gens σN) X (.list xl)) {g : Perm (Fin n)} (hg : g ∈ H) :
    FunAll P b (tmGLPOIn σN vs q xl g⁻¹) (fun u c => TmGLPOOut (gens σN) X g u ∧
      c ≤ tmGLPOffC (membershipPrim hm) (normalizedFactorPrim hfac)
        (tmGLPOIn σN vs q xl g⁻¹).wt) := by
  set a := tmGLPOIn σN vs q xl g⁻¹ with ha
  set W := a.wt with hW
  set va : List Val := [encGroup σN, .list vs, .nat q, .list xl, encPerm g⁻¹] with hva
  have hloop : P.HasAt b (loopFuns b (.get (.var 0) (.nat 2)) .nil (tmGLPOStep (b + 3))) :=
    h.left
  have hrow : P.funs[b + 3]? = some (tmGLPORowF (b + 4) find rel) :=
    (h.block (gs := [tmGLPORowF (b + 4) find rel]) 3 rfl).single
  have hfirst : P.funs[b + 4]? = some (tmCsFirstF (b + 4)) :=
    (h.block (gs := [tmCsFirstF (b + 4)]) 4 rfl).single
  have hk := Det.get' (Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl) (Det.nat 2)
    (vs := va) (v := .nat q) rfl
  have wq : (Val.nat q).wt < W := wt_le_wt_list (by simp)
  have wxl : (Val.list xl).wt < W := wt_le_wt_list (by simp)
  have wgi : (encPerm g⁻¹).wt < W := wt_le_wt_list (by simp)
  have hnW : n < W := (tmGLP_n_lt_wt g⁻¹).trans wgi
  have hqW : q < W := by
    obtain ⟨l, hl0, hll, -⟩ := hxl
    cases hl0
    have := length_lt_wt_list xl
    omega
  have hS : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hS3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hB : 2 * q + 8 * (n + 1) ^ 2 + 10 ≤ 20 * (W + 1) ^ 2 := by
    have := Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 2
    omega
  have hM : ∀ i acc, i ≤ q → TmGLPOInv (gens σN) X g (20 * (W + 1) ^ 2) i acc →
      acc.wt ≤ 50 * (W + 1) ^ 3 := by
    rintro i acc hi ⟨l, rfl, hl, h1, -⟩
    have h2 := wt_list_le_of h1
    have h3 : l.length * (2 * (20 * (W + 1) ^ 2) + 1) ≤ (W + 1) * (41 * (W + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : (W + 1) * (41 * (W + 1) ^ 2) = 41 * (W + 1) ^ 3 := by ring
    have : 4 ≤ (W + 1) ^ 3 := by
      have : 2 ≤ W + 1 := by omega
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ (W + 1) ^ 3 := Nat.pow_le_pow_left this 3
    omega
  refine (loopBdd_spec hloop hk Det.nil (by have := wt_nat_le q; omega) (M := 50 * (W + 1) ^ 3)
    (Inv := TmGLPOInv (gens σN) X g (20 * (W + 1) ^ 2))
    ⟨[], rfl, rfl, fun v hv => absurd hv List.not_mem_nil,
      fun k hk => absurd hk (Nat.not_lt_zero _)⟩ hM
    (D := fun _ => 2 * tmGLPORowC (membershipPrim hm) (normalizedFactorPrim hfac) W +
      10 ^ 4 * (W + 1) ^ 3) ?_).mono ?_
  · rintro i acc hi ⟨l, rfl, hl, hlw, hlv⟩
    have hlW := hM i (.list l) hi.le ⟨l, rfl, hl, hlw, hlv⟩
    have g0 := Det.arg' (P := P) (vs := [a, .nat i, .list l]) (rest := []) (j := 0) rfl
    have g1 := Det.arg' (P := P) (vs := [a, .nat i, .list l]) (rest := []) (j := 1) rfl
    have g2 := Det.arg' (P := P) (vs := [a, .nat i, .list l]) (rest := []) (j := 2) rfl
    have wA := wt_list3_le a (.nat i) (.list l)
    have wi := wt_nat_le i
    have w2 := wt_list2_le a (.nat i)
    have dargs := (Det.mk2 g0 g1).mono (c' := 5000 * (W + 1) ^ 3) (by omega)
    have hspec := tmGLPORow_spec hm hfac hrow hfirst hfd hr hjm hjf hNH hn hT hY hxl hg ⟨i, hi⟩
    have hcall : EvalAll P [.list [a, .nat i, .list l]] (.call (b + 3) (mk2 (arg 0) (arg 1)))
        (fun w c => TmGLPOItem (gens σN) X g ⟨i, hi⟩ w ∧ c ≤ 5000 * (W + 1) ^ 3 +
          2 * tmGLPORowC (membershipPrim hm) (normalizedFactorPrim hfac) W + 1) := by
      refine EvalAll.call_funAll dargs fun v ca hv => ?_
      obtain ⟨rfl, hca⟩ := hv
      refine FunAll.mono (FunAll.wt_lt hspec) fun w cb hw => ⟨hw.1.1, ?_⟩
      have : cb ≤ tmGLPORowC (membershipPrim hm) (normalizedFactorPrim hfac) W := hw.1.2
      have := hw.2
      omega
    refine (EvalAll.snoc_det g2 hcall).mono ?_
    rintro v c ⟨w, cb, ⟨hw, hcb⟩, rfl, hc⟩
    have hwB : w.wt ≤ 20 * (W + 1) ^ 2 := by
      obtain ⟨J, -, hw'⟩ := hw
      exact (tmGLP_wt_findOut hw').trans hB
    refine ⟨⟨l ++ [w], rfl, by simp [hl], ?_, ?_⟩, ?_⟩
    · intro v' hv'
      rcases List.mem_append.1 hv' with hv' | hv'
      · exact hlw v' hv'
      · rw [List.mem_singleton.1 hv']; exact hwB
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · obtain ⟨v', hv', hit⟩ := hlv k hk
        exact ⟨v', by rw [List.getElem?_append_left (by omega)]; exact hv', hit⟩
      · refine ⟨w, by rw [hk, ← hl, List.getElem?_concat_length], ?_⟩
        have : k = ⟨i, hi⟩ := Fin.ext hk
        subst this; exact hw
    · have wsn := wt_list_snoc_le l w
      have eA : (Val.list [a, .nat i, .list l]).wt = (Val.list [a, .nat i, .list l]).wt := rfl
      beta_reduce
      clear hspec hcall
      generalize tmGLPORowC (membershipPrim hm) (normalizedFactorPrim hfac) W = R at hcb hc ⊢
      generalize (W + 1) ^ 3 = S3 at *
      omega
  · rintro u c ⟨⟨l, rfl, hl, -, hlv⟩, hc⟩
    refine ⟨⟨l, rfl, hl, fun k => hlv k k.2⟩, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have h1 : q * (2 * tmGLPORowC (membershipPrim hm) (normalizedFactorPrim hfac) W +
        10 ^ 4 * (W + 1) ^ 3) ≤ (W + 1) * (2 * tmGLPORowC (membershipPrim hm)
          (normalizedFactorPrim hfac) W + 10 ^ 4 * (W + 1) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : loopModK * (q + 1) * (W + q + 50 * (W + 1) ^ 3 + 1) ≤
        1000 * ((W + 1) * (52 * (W + 1) ^ 3)) := by
      rw [Nat.mul_assoc]; unfold loopModK
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    have e2 : (W + 1) * (52 * (W + 1) ^ 3) = 52 * (W + 1) ^ 4 := by ring
    unfold tmGLPOffC
    generalize loopModK * (q + 1) * (W + q + 50 * (W + 1) ^ 3 + 1) = L at hc h4
    generalize (W + 1) * (2 * tmGLPORowC (membershipPrim hm) (normalizedFactorPrim hfac) W +
        10 ^ 4 * (W + 1) ^ 3) = T at hc h1 ⊢
    generalize (W + 1) ^ 4 = C4 at e2 ⊢
    omega

end GI.Impl
