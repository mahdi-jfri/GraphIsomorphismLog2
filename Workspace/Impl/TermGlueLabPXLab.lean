import Workspace.Impl.TermGlueLabPRep

/-!
# The labels of `x` from the `N`-test table

Step 2 of the label program. For every row `x_i`, the program reads the `N`-test
table `us` (entry `(x_j, x_i)` holds `Iso_N(x_j, x_i)`): the first `j` with a nonempty entry
(`tmCsFirstF`) is the first row of the type of `x_i`, and the stored coset `n ⟨…⟩` gives
`n ∈ N` with `x_j^n = x_i`. The result is the list of the pairs `[j, n]`
(`tmGLPXLab_spec`). No string call: the entries were computed in the `N`-test phase.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]

/-- **The `N`-test table of the rows of `x`**: entry `i + 2 q j` answers `Iso_N(x_j, x_i)`. -/
def TmGLPTestOK (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (us : List Val) : Prop :=
  ∀ i j : Fin q, ∃ u, us[i.1 + 2 * q * j.1]? = some u ∧
    AnsC (Equiv.refl (Fin n)) u (Iso N (X j) (X i))

/-- One pair `[j, n]` for the row `x_k`: `j` the first row of its type, `x_j^n = x_k`. -/
def TmGLPXItem (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (k : Fin q) (v : Val) :
    Prop :=
  ∃ J : Fin q, ∃ x ∈ N, v = .list [.nat J, encPerm x] ∧ TmGLPFirst N X (X k) J ∧ X J ↼ x = X k

/-! ### The program -/

/-- One step, on `[a, i, acc]` with `a = [us, q]`. -/
def tmGLPXStep (first : ℕ) : Expr :=
  .letE (.call first (mk2 (mk4 (.get (arg 0) (.nat 0)) (arg 1)
      (.arith .mul (.nat 2) (.get (arg 0) (.nat 1))) (.get (arg 0) (.nat 1))) (.nat 0)))
    (.snoc (arg 2) (mk2 (.var 1)
      (.get (.get (.get (arg 0) (.nat 0))
        (.arith .add (arg 1) (.arith .mul (.arith .mul (.nat 2) (.get (arg 0) (.nat 1)))
          (.var 1)))) (.nat 0))))

/-- **The labels of `x`** (4 functions). -/
def tmGLPXLabFuns (b : ℕ) : List Expr :=
  loopFuns b (.get (.var 0) (.nat 1)) .nil (tmGLPXStep (b + 3)) ++ [tmCsFirstF (b + 3)]

theorem length_tmGLPXLabFuns (b : ℕ) : (tmGLPXLabFuns b).length = 4 := rfl

/-! ### The specification -/

/-- The state after the rows `k < i`. -/
def TmGLPXInv (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (B i : ℕ) (acc : Val) :
    Prop :=
  ∃ l : List Val, acc = .list l ∧ l.length = i ∧ (∀ v ∈ l, v.wt ≤ B) ∧
    ∀ k : Fin q, k.1 < i → ∃ v, l[k.1]? = some v ∧ TmGLPXItem N X k v

/-- The result: one pair per row. -/
def TmGLPXOut (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (u : Val) : Prop :=
  ∃ l : List Val, u = .list l ∧ l.length = q ∧
    ∀ k : Fin q, ∃ v, l[k.1]? = some v ∧ TmGLPXItem N X k v

theorem tmGLP_test_len {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} {us : List Val}
    (hT : TmGLPTestOK N X us) : q ≤ us.length := by
  rcases Nat.eq_zero_or_pos q with h0 | h0
  · omega
  · obtain ⟨u, hu, -⟩ := hT ⟨q - 1, by omega⟩ ⟨q - 1, by omega⟩
    have h1 := (List.getElem?_eq_some_iff.mp hu).1
    simp only at h1
    have : q - 1 ≤ 2 * q * (q - 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- One row: the first row of its type and the transporter, from the table. -/
theorem tmGLP_xrow {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} {us : List Val}
    (hT : TmGLPTestOK N X us) (i : Fin q) {J : ℕ} (hJq : J ≤ q)
    (hJe : ∀ j', 0 ≤ j' → j' < J → us[i.1 + 2 * q * j']? = some (.list []))
    (hJn : J < q → ∃ a l, us[i.1 + 2 * q * J]? = some (.list (a :: l))) :
    ∃ hJ : J < q, ∃ v, us[i.1 + 2 * q * J]? = some v ∧ ∃ x ∈ N, ∃ gs : List (Perm (Fin n)),
      v = .list [encPerm x, encGroup gs] ∧ TmGLPFirst N X (X i) ⟨J, hJ⟩ ∧
        X ⟨J, hJ⟩ ↼ x = X i := by
  -- the entries before `J` are empty cosets
  have hno : ∀ j' : Fin q, j'.1 < J → X i ∉ orbitN N (X j') := by
    intro j' hj' ⟨y, hy, hyZ⟩
    obtain ⟨u, hu, hA⟩ := hT i j'
    rw [hJe j'.1 (Nat.zero_le _) hj'] at hu
    have := tmCs_ansC_nil hA (Option.some.inj hu).symm
    have hmem : y ∈ Iso N (X j') (X i) := ⟨hy, hyZ⟩
    rw [this] at hmem
    exact hmem
  -- `J < q`: the entry of `(x_i, x_i)` is not empty
  have hJ : J < q := by
    by_contra hc
    exact hno i (by omega) (tmGLP_self_mem N (X i))
  obtain ⟨u, hu, hA⟩ := hT i ⟨J, hJ⟩
  obtain ⟨a0, l0, hl0⟩ := hJn hJ
  rw [hl0] at hu
  cases hu
  rcases id hA with ⟨h1, -⟩ | ⟨x, gs, hv, -, -⟩
  · cases h1
  have hI := tmCs_ansC_cons hA hv
  have hx : x ∈ Iso N (X ⟨J, hJ⟩) (X i) := by rw [hI]; exact ⟨1, (gens gs).one_mem, mul_one x⟩
  exact ⟨hJ, _, hl0, x, hx.1, gs, hv, ⟨⟨x, hx.1, hx.2⟩, hno⟩, hx.2⟩

/-- The cost bound of the labels of `x`, for an input of weight `W`. -/
def tmGLPXLabC (W : ℕ) : ℕ := 10 ^ 7 * (W + 1) ^ 3

set_option maxHeartbeats 4000000 in
/-- **The labels of `x`.** On `[us, q]` with `us` the `N`-test table of the rows of `x`, the
result is one pair `[j, n]` per row (`TmGLPXOut`). -/
theorem tmGLPXLab_spec {P : Program} {b : ℕ} (h : P.HasAt b (tmGLPXLabFuns b))
    {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} {us : List Val}
    (hT : TmGLPTestOK N X us) :
    FunAll P b (.list [.list us, .nat q]) (fun u c => TmGLPXOut N X u ∧
      c ≤ tmGLPXLabC (Val.list [.list us, .nat q]).wt) := by
  set a : Val := .list [.list us, .nat q] with ha
  have hloop : P.HasAt b (loopFuns b (.get (.var 0) (.nat 1)) .nil (tmGLPXStep (b + 3))) := h.left
  have hfirst : P.funs[b + 3]? = some (tmCsFirstF (b + 3)) :=
    (h.block (gs := [tmCsFirstF (b + 3)]) 3 rfl).single
  have hk := Det.get' (Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl) (Det.nat 1)
    (vs := [.list us, .nat q]) (v := .nat q) rfl
  set W := a.wt with hW
  have wus : (Val.list us).wt < W := wt_le_wt_list (by simp [ha])
  have lus := length_lt_wt_list us
  have hqus := tmGLP_test_len hT
  have hqW : q < W := by omega
  have hM : ∀ i acc, i ≤ q → TmGLPXInv N X (6 * W + 10) i acc → acc.wt ≤ 20 * (W + 1) ^ 2 := by
    rintro i acc hi ⟨l, rfl, hl, h1, -⟩
    have h2 := wt_list_le_of h1
    have h3 : l.length * (2 * (6 * W + 10) + 1) ≤ (W + 1) * (12 * W + 21) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hW2 : 2 ≤ W := by omega
    have h4 : (W + 1) * (12 * W + 21) + 4 ≤ 20 * (W + 1) ^ 2 := by nlinarith
    omega
  refine (loopBdd_spec hloop hk Det.nil (by have := wt_nat_le q; omega) (M := 20 * (W + 1) ^ 2)
    (Inv := TmGLPXInv N X (6 * W + 10))
    ⟨[], rfl, rfl, fun v hv => absurd hv List.not_mem_nil, fun k hk => absurd hk (Nat.not_lt_zero _)⟩ hM
    (D := fun _ => 10 ^ 5 * (W + 1) ^ 2) ?_).mono ?_
  · rintro i acc hi ⟨l, rfl, hl, hlw, hlv⟩
    have hlW := hM i (.list l) hi.le ⟨l, rfl, hl, hlw, hlv⟩
    set A : Val := .list [a, .nat i, .list l] with hA
    have g0 := Det.arg' (P := P) (vs := [a, .nat i, .list l]) (rest := []) (j := 0) rfl
    have g1 := Det.arg' (P := P) (vs := [a, .nat i, .list l]) (rest := []) (j := 1) rfl
    have dus := Det.get' g0 (Det.nat 0) (vs := [.list us, .nat q]) (v := .list us) rfl
    have dq := Det.get' g0 (Det.nat 1) (vs := [.list us, .nat q]) (v := .nat q) rfl
    have d2q := Det.arith' (op := .mul) (Det.nat 2) dq (z := 2 * q) rfl
    have dargs := Det.mk2 (Det.mk4 dus g1 d2q dq) (Det.nat 0)
    have hl' : ∀ j < q, ∃ l', us[i + 2 * q * j]? = some (.list l') := by
      intro j hj
      obtain ⟨u, hu, hA'⟩ := hT ⟨i, hi⟩ ⟨j, hj⟩
      rcases hA' with ⟨rfl, -⟩ | ⟨x, gs, rfl, -, -⟩
      · exact ⟨[], hu⟩
      · exact ⟨_, hu⟩
    obtain ⟨J, hJ, -, hJq, hJe, hJn⟩ := tmCs_first_spec hfirst (vs := us) (base := i)
      (stride := 2 * q) (q := q) hl' q 0 (by omega) (by omega)
    obtain ⟨hJlt, v, hv, x, hxN, gs, rfl, hfst, hxX⟩ :=
      tmGLP_xrow hT ⟨i, hi⟩ hJq (fun j' _ hj' => hJe j' (Nat.zero_le _) hj') hJn
    have dJ := Det.call dargs hJ
    have e0 := Det.arg' (P := P) (vs := [a, .nat i, .list l]) (rest := [.nat J]) (j := 0) rfl
    have e1 := Det.arg' (P := P) (vs := [a, .nat i, .list l]) (rest := [.nat J]) (j := 1) rfl
    have e2 := Det.arg' (P := P) (vs := [a, .nat i, .list l]) (rest := [.nat J]) (j := 2) rfl
    have eJ := Det.var' (P := P) (env := [A, .nat J]) (i := 1) (v := .nat J) rfl
    have eus := Det.get' e0 (Det.nat 0) (vs := [.list us, .nat q]) (v := .list us) rfl
    have eq := Det.get' e0 (Det.nat 1) (vs := [.list us, .nat q]) (v := .nat q) rfl
    have e2q := Det.arith' (op := .mul) (Det.nat 2) eq (z := 2 * q) rfl
    have em := Det.arith' (op := .mul) e2q eJ (z := 2 * q * J) rfl
    have eidx := Det.arith' (op := .add) e1 em (z := i + 2 * q * J) rfl
    have ev := Det.get' eus eidx hv
    have ex := Det.get' ev (Det.nat 0) (vs := [encPerm x, encGroup gs]) (v := encPerm x) rfl
    have ebody := Det.snoc e2 (Det.mk2 eJ ex)
    refine (Det.letE dJ ebody).post fun c hc => ⟨⟨l ++ [.list [.nat J, encPerm x]], rfl,
      by simp [hl], ?_, ?_⟩, ?_⟩
    · -- weights
      have wv : (Val.list [encPerm x, encGroup gs]).wt < (Val.list us).wt :=
        wt_le_wt_list (List.mem_of_getElem? hv)
      have wx : (encPerm x).wt < (Val.list [encPerm x, encGroup gs]).wt := wt_le_wt_list (by simp)
      have w2 := wt_list2_le (.nat J) (encPerm x)
      have wJ := wt_nat_le J
      intro v' hv'
      rcases List.mem_append.1 hv' with hv' | hv'
      · exact hlw v' hv'
      · rw [List.mem_singleton.1 hv']; omega
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · obtain ⟨v', hv', hit⟩ := hlv k hk
        exact ⟨v', by rw [List.getElem?_append_left (by omega)]; exact hv', hit⟩
      · refine ⟨_, by rw [hk, ← hl, List.getElem?_concat_length], ⟨J, hJlt⟩, x, hxN, rfl, ?_, ?_⟩
        · have : k = ⟨i, hi⟩ := Fin.ext hk
          subst this; exact hfst
        · have : k = ⟨i, hi⟩ := Fin.ext hk
          subst this; exact hxX
    · have wv : (Val.list [encPerm x, encGroup gs]).wt < (Val.list us).wt :=
        wt_le_wt_list (List.mem_of_getElem? hv)
      have wx : (encPerm x).wt < (Val.list [encPerm x, encGroup gs]).wt := wt_le_wt_list (by simp)
      have w2 := wt_list2_le (.nat J) (encPerm x)
      have wJ := wt_nat_le J
      have wi := wt_nat_le i
      have wq := wt_nat_le q
      have w2q := wt_nat_le (2 * q)
      have w0 := wt_nat_le 0
      have wA := wt_list3_le a (.nat i) (.list l)
      have eA : A.wt = (Val.list [a, .nat i, .list l]).wt := rfl
      have wc := wt_list4_le (.list us) (.nat i) (.nat (2 * q)) (.nat q)
      have ec : (tmCsFirstCtx us i (2 * q) q).wt =
          (Val.list [.list us, .nat i, .nat (2 * q), .nat q]).wt := rfl
      have wc0 := wt_list2_le (.list [.list us, .nat i, .nat (2 * q), .nat q]) (.nat 0)
      have wsn := wt_list_snoc_le l (.list [.nat J, encPerm x])
      have hS : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      have hfc : (q + 1) * tmCsFirstK (tmCsFirstCtx us i (2 * q) q).wt ≤ 10 ^ 4 * (W + 1) ^ 2 := by
        unfold tmCsFirstK
        have : (tmCsFirstCtx us i (2 * q) q).wt ≤ 10 * W + 20 := by omega
        calc (q + 1) * (200 * (tmCsFirstCtx us i (2 * q) q).wt + 400)
            ≤ (W + 1) * (200 * (10 * W + 20) + 400) := Nat.mul_le_mul (by omega) (by omega)
          _ ≤ 10 ^ 4 * (W + 1) ^ 2 := by nlinarith
      have hqJ : 2 * q * J ≤ 2 * (W + 1) ^ 2 := by
        have : q * J ≤ (W + 1) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
        nlinarith
      beta_reduce
      generalize (q + 1) * tmCsFirstK (tmCsFirstCtx us i (2 * q) q).wt = F at hc hfc
      generalize 2 * q * J = QJ at hc hqJ
      generalize (W + 1) ^ 2 = S at *
      omega
  · rintro u c ⟨⟨l, rfl, hl, -, hlv⟩, hc⟩
    refine ⟨⟨l, rfl, hl, fun k => hlv k k.2⟩, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have h1 : q * (10 ^ 5 * (W + 1) ^ 2) ≤ (W + 1) * (10 ^ 5 * (W + 1) ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : loopModK * (q + 1) * (W + q + 20 * (W + 1) ^ 2 + 1) ≤
        1000 * ((W + 1) * (22 * (W + 1) ^ 2)) := by
      rw [Nat.mul_assoc]; unfold loopModK
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by nlinarith))
    have e1 : (W + 1) * (10 ^ 5 * (W + 1) ^ 2) = 10 ^ 5 * (W + 1) ^ 3 := by ring
    have e2 : (W + 1) * (22 * (W + 1) ^ 2) = 22 * (W + 1) ^ 3 := by ring
    unfold tmGLPXLabC
    generalize loopModK * (q + 1) * (W + q + 20 * (W + 1) ^ 2 + 1) = L at hc h4
    generalize (W + 1) ^ 3 = C3 at e1 e2 ⊢
    omega

end GI.Impl

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens)

attribute [local instance] stringRAct

/-- **The `N`-test table is a table of the rows of `x`.** -/
theorem tmGLP_testOK_of {Ω C : Type} (S : State Ω C) {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (σN : List (Perm (Fin m))) {us : List Val}
    (hus : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
      us (tmTests q)) :
    TmGLPTestOK (gens σN) (fun i => tmRowStr S E (.inl i)) us := by
  intro i j
  have hlen : us.length = 4 * q ^ 2 := by rw [hus.length_eq, length_tmTests]
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0)
  have hidx : i.1 + 2 * q * j.1 < 4 * q ^ 2 := by
    have : i.1 + 2 * q * j.1 < 2 * q * q := by nlinarith [i.2, j.2]
    nlinarith
  obtain ⟨h1, h2, hc⟩ := tmTests_getElem? q (i.1 + 2 * q * j.1) hidx
  have hq2 : 0 < 2 * q := by omega
  have e1 : (i.1 + 2 * q * j.1) / (2 * q) = j.1 := by
    rw [Nat.mul_comm, Nat.add_mul_div_right _ _ hq2, Nat.div_eq_of_lt (by omega)]
    simp
  have e2 : (i.1 + 2 * q * j.1) % (2 * q) = i.1 := by
    rw [Nat.mul_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have r1 : tmRowAt q ((i.1 + 2 * q * j.1) / (2 * q)) h1 = .inl j := by
    unfold tmRowAt; simp only [e1, dif_pos j.2]
  have r2 : tmRowAt q ((i.1 + 2 * q * j.1) % (2 * q)) h2 = .inl i := by
    unfold tmRowAt; simp only [e2, dif_pos i.2]
  rw [r1, r2] at hc
  have hlt : i.1 + 2 * q * j.1 < us.length := by rw [hlen]; exact hidx
  refine ⟨us[i.1 + 2 * q * j.1], List.getElem?_eq_getElem hlt, ?_⟩
  have hR := List.forall₂_iff_get.1 hus
  have := hR.2 (i.1 + 2 * q * j.1) hlt (by rw [← hR.1]; exact hlt)
  have hget : (tmTests q).get ⟨i.1 + 2 * q * j.1, by rw [← hR.1]; exact hlt⟩ = (.inl j, .inl i) := by
    have := List.getElem?_eq_getElem (l := tmTests q) (i := i.1 + 2 * q * j.1)
      (by rw [← hR.1]; exact hlt)
    rw [hc] at this
    exact (Option.some.inj this).symm
  rw [hget] at this
  simp only [List.get_eq_getElem] at this
  convert this using 1
  unfold tmTestState
  rw [rowState_answer]
  rfl

end GI.Impl
