import Workspace.Impl.AggItemCiCfgH

/-!
# The configuration query: lifting a diagonal permutation, as a program

* `itcqRhB` on `[[g, n], t]` with `g = itciD n a`: the value `a t` for `t < n` (read at the
  position `t (n + 1)` of `(t, t)`, `itcq_dec_val`), else `t`. Mapped over `[0, …, q - 1]` it gives
  `itcqRho X a` (`itcq_rho_spec`).
* `itcqLfB rm cmp` on `[[α, β, n, R], g]` with `R = [0, …, q - 1]`: `α * itcqRho X a * β`
  (`itcq_lfB_spec`). With `α = itciEnum X`, `β = (itciEnum X)⁻¹` this is the lift
  `itciLift X a` (`itcq_lift_rho`); with `α = itciEnum Y` it is the extension
  `itciExt X Y a` (`itcq_ext_rho`).
* `itcq_mapP_spec`: a map over a list of permutations, for the lifted generators.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encPerms)

variable {q : ℕ}

/-- On `[[g, n], t]`: entry `t (n + 1)` of `g` divided by `n + 1` if `t < n`, else `t`. -/
def itcqRhB : Expr :=
  .ite (.arith .lt (arg 1) (.get (arg 0) (.nat 1)))
    (.arith .div (.get (.get (arg 0) (.nat 0))
        (.arith .mul (arg 1) (.arith .add (.get (arg 0) (.nat 1)) (.nat 1))))
      (.arith .add (.get (arg 0) (.nat 1)) (.nat 1)))
    (arg 1)

/-- The value of `itcqRhB`. -/
def itcqRv {n : ℕ} (a : Perm (Fin n)) (t : ℕ) : ℕ := if h : t < n then (a ⟨t, h⟩ : ℕ) else t

/-- On `[[α, β, n, R], g]`: `α * ρ * β`, with `ρ` the map of `itcqRhB` (at `rm`) over `R`. -/
def itcqLfB (rm cmp : ℕ) : Expr :=
  .call cmp (mk2 (.call cmp (mk2 (.get (arg 0) (.nat 0))
      (.call rm (mk2 (mk2 (arg 1) (.get (arg 0) (.nat 2))) (.get (arg 0) (.nat 3))))))
    (.get (arg 0) (.nat 1)))

/-- The cost bound of the map of `itcqRhB`. -/
def itcqRhC (M : ℕ) : ℕ := 10 ^ 5 * (M + 1) ^ 3

/-- The cost bound of `itcqLfB`. -/
def itcqLfC (M : ℕ) : ℕ := 10 ^ 9 * (M + 1) ^ 3

theorem itcq_rhC_arith {M q C : ℕ} (hq : q + 1 ≤ M)
    (hC : C ≤ q * (100 * (5 * M + 12)) + 1000 * (q + 1) * (2 * M + 14 * M ^ 2 + 8)) :
    C ≤ itcqRhC M := by
  unfold itcqRhC
  have h1 : q * (100 * (5 * M + 12)) ≤ M * (100 * (5 * M + 12)) := Nat.mul_le_mul_right _ (by omega)
  have h2 : 1000 * (q + 1) * (2 * M + 14 * M ^ 2 + 8) ≤ 1000 * M * (2 * M + 14 * M ^ 2 + 8) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq)
  have e : (M + 1) ^ 3 = M ^ 3 + 3 * M ^ 2 + 3 * M + 1 := by ring
  have e2 : M * (100 * (5 * M + 12)) = 500 * M ^ 2 + 1200 * M := by ring
  have e3 : 1000 * M * (2 * M + 14 * M ^ 2 + 8) = 14000 * M ^ 3 + 2000 * M ^ 2 + 8000 * M := by
    ring
  omega

theorem itcq_lfC_arith {M C : ℕ}
    (hC : C ≤ 100 * (20 * M ^ 2 + 21) + itcqRhC (4 * M + 10) + 2 * (permK * M ^ 3)) :
    C ≤ itcqLfC M := by
  unfold itcqLfC
  unfold itcqRhC permK at hC
  have h1 : (4 * M + 10 + 1) ^ 3 ≤ (11 * (M + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have e1 : (11 * (M + 1)) ^ 3 = 1331 * (M + 1) ^ 3 := by ring
  have h2 : M ^ 3 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h3 : M ^ 2 ≤ (M + 1) ^ 3 := by
    calc M ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (M + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : 1 ≤ (M + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

section Prog

variable {P : Program}

theorem itcq_01_wt {W : ℕ} (hW : 3 ≤ W) (p : Prop) [Decidable p] :
    (Val.nat (if p then 1 else 0)).wt ≤ W := by
  split_ifs
  · have := wt_nat_le 1; omega
  · have := wt_nat_le 0; omega

set_option maxHeartbeats 1000000 in
/-- **One entry of the positions of a lift**, in cost `100 (W + 1)`. -/
theorem itcq_rhB_spec {f : ℕ} (hf : P.funs[f]? = some itcqRhB) {n : ℕ} (a : Perm (Fin n)) (t : ℕ)
    {W : ℕ} (hW : (Val.list [.list [encPerm (itciD n a), .nat n], .nat t]).wt + n * n + 3 ≤ W) :
    FunDet P f (.list [.list [encPerm (itciD n a), .nat n], .nat t]) (.nat (itcqRv a t))
      (100 * (W + 1)) := by
  have h0 : (Val.list [encPerm (itciD n a), .nat n]).wt <
      (Val.list [.list [encPerm (itciD n a), .nat n], .nat t]).wt := wt_le_wt_list (by simp)
  have h1 : (Val.nat t).wt < (Val.list [.list [encPerm (itciD n a), .nat n], .nat t]).wt :=
    wt_le_wt_list (by simp)
  have hg : (encPerm (itciD n a)).wt < (Val.list [encPerm (itciD n a), .nat n]).wt :=
    wt_le_wt_list (by simp)
  have hn : (Val.nat n).wt < (Val.list [encPerm (itciD n a), .nat n]).wt :=
    wt_le_wt_list (by simp)
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hn1 := wt_nat_le (n + 1)
  have A0 := StDC.arg (P := P) (rest := []) (vs := [.list [encPerm (itciD n a), .nat n], .nat t])
    (j := 0) rfl (W := W) (by omega) (by omega) (by omega)
  have A1 := StDC.arg (P := P) (rest := []) (vs := [.list [encPerm (itciD n a), .nat n], .nat t])
    (j := 1) rfl (W := W) (by omega) (by omega) (by omega)
  have gN := StDC.get A0 (StDC.nat 1 (by omega)) (v := .nat n) rfl (by omega)
  have gG := StDC.get A0 (StDC.nat 0 (by omega)) (v := encPerm (itciD n a)) rfl (by omega)
  have cL := StDC.arith A1 gN (op := .lt) rfl (itcq_01_wt (by omega) (t < n))
  have hv : (Val.nat (itcqRv a t)).wt ≤ W := by
    unfold itcqRv
    split_ifs with h
    · have := wt_nat_le (a ⟨t, h⟩ : ℕ); have := (a ⟨t, h⟩).isLt; omega
    · omega
  have body : StDC P [.list [.list [encPerm (itciD n a), .nat n], .nat t]] itcqRhB
      (.nat (itcqRv a t)) 38 0 W := by
    unfold itcqRhB
    refine StDC.ite (nt := 25) (Et := 0) (ne := 3) (Ee := 0) cL (fun hlt => ?_) (fun hz => ?_) hv
    · have hlt' : t < n := by
        simp only [GI.Machine.BinOp.eval] at hlt; split_ifs at hlt with h; exact h; simp at hlt
      have n1 := StDC.arith gN (StDC.nat 1 (by omega)) (op := .add) (z := n + 1) rfl (by omega)
      have hd := itcq_diag_lt hlt'
      have hmw : (Val.nat (t * (n + 1))).wt ≤ W := by have := wt_nat_le (t * (n + 1)); omega
      have mm := StDC.arith A1 n1 (op := .mul) (z := t * (n + 1)) rfl hmw
      have hent : (Val.nat (itciD n a ⟨t * (n + 1), hd⟩)).wt ≤ W := by
        have := wt_nat_le (itciD n a ⟨t * (n + 1), hd⟩ : ℕ)
        have := (itciD n a ⟨t * (n + 1), hd⟩).isLt
        omega
      have e := StDC.get gG mm (v := .nat (itciD n a ⟨t * (n + 1), hd⟩))
        (encFun_getElem?_nat (fun i => (itciD n a i : ℕ)) _ hd) hent
      have e2 : GI.Machine.BinOp.div.eval (itciD n a ⟨t * (n + 1), hd⟩ : ℕ) (n + 1) =
          itcqRv a t := by
        simp only [GI.Machine.BinOp.eval]
        rw [itcqRv, dif_pos hlt']
        exact itcq_dec_val a ⟨t, hlt'⟩
      exact (StDC.arith e n1 e2 hv).mono (by omega) (by omega)
    · have hge : ¬ t < n := by
        intro h; simp [GI.Machine.BinOp.eval, h] at hz
      have : itcqRv a t = t := by rw [itcqRv, dif_neg hge]
      rw [this]
      exact A1
  exact StDC.funDet hf body (by omega)

/-- **The positions of a lift**: the map of `itcqRhB` over `[0, …, q - 1]` gives `itcqRho X a`,
in cost `itcqRhC M` for `M` at least `q + 1` and the weight of `[itciD n a, n]`. -/
theorem itcq_rho_spec {mb fr : ℕ} (hm : P.HasAt mb (mapFuns mb fr))
    (hf : P.funs[fr]? = some itcqRhB) (X : PairCfg q) (a : Perm (Fin X.fiber.card)) {M : ℕ}
    (hq : q + 1 ≤ M)
    (hM : (Val.list [encPerm (itciD X.fiber.card a), .nat X.fiber.card]).wt ≤ M) :
    FunDet P mb (.list [.list [encPerm (itciD X.fiber.card a), .nat X.fiber.card],
      natList (List.range q)]) (encPerm (itcqRho X a)) (itcqRhC M) := by
  have hnq : X.fiber.card ≤ q := by have := X.fiber.card_le_univ; simpa using this
  have hg : (encPerm (itciD X.fiber.card a)).wt <
      (Val.list [encPerm (itciD X.fiber.card a), .nat X.fiber.card]).wt := wt_le_wt_list (by simp)
  have hlg : X.fiber.card * X.fiber.card < (encPerm (itciD X.fiber.card a)).wt := by
    have := length_lt_wt_list ((List.finRange (X.fiber.card * X.fiber.card)).map fun i =>
      Val.nat (itciD X.fiber.card a i))
    simpa using this
  have key := itcq_mapPos_spec (P := P) hm
    (c := .list [encPerm (itciD X.fiber.card a), .nat X.fiber.card]) (m := q)
    (g := fun t => (itcqRho X a t : ℕ)) (Bd := 100 * (5 * M + 12)) (fun t => by
      have e : (itcqRho X a t : ℕ) = itcqRv a t := by rw [itcqRho_apply]; rfl
      show FunDet P fr _ (.nat (itcqRho X a t : ℕ)) _
      rw [e]
      refine (itcq_rhB_spec hf a t ?_).mono le_rfl
      have := wt_list2_le (.list [encPerm (itciD X.fiber.card a), .nat X.fiber.card]) (.nat t)
      have := wt_nat_le (t : ℕ)
      have := t.isLt
      omega)
  refine key.mono fun w c hwc => ⟨hwc.1, ?_⟩
  obtain ⟨hw, hc⟩ := hwc
  have hR := itcq_range_wt q
  have hin := wt_list2_le (.list [encPerm (itciD X.fiber.card a), .nat X.fiber.card])
    (natList (List.range q))
  have hout : w.wt ≤ 4 * (q + 1) ^ 2 := by rw [hw]; exact wt_encPerm_le (itcqRho X a)
  have hq2 : (q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hq 2
  refine itcq_rhC_arith hq (hc.trans ?_)
  refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
  unfold mapK at *
  omega

/-- **`α * itcqRho X a * β`** from `[[α, β, n, R], itciD n a]`, in cost `itcqLfC M` for `M` at
least `q + 1` and the input weight. -/
theorem itcq_lfB_spec {f mb fr cmp : ℕ} (hf : P.funs[f]? = some (itcqLfB mb cmp))
    (hm : P.HasAt mb (mapFuns mb fr)) (hfr : P.funs[fr]? = some itcqRhB)
    (hcmp : P.HasAt cmp (composeFuns cmp)) (X : PairCfg q) (α β : Perm (Fin q))
    (a : Perm (Fin X.fiber.card)) {M : ℕ} (hq : q + 1 ≤ M)
    (hM : (Val.list [.list [encPerm α, encPerm β, .nat X.fiber.card, natList (List.range q)],
      encPerm (itciD X.fiber.card a)]).wt ≤ M) :
    FunDet P f (.list [.list [encPerm α, encPerm β, .nat X.fiber.card, natList (List.range q)],
      encPerm (itciD X.fiber.card a)]) (encPerm (α * itcqRho X a * β)) (itcqLfC M) := by
  set c := Val.list [encPerm α, encPerm β, .nat X.fiber.card, natList (List.range q)] with hc
  set g := encPerm (itciD X.fiber.card a) with hg
  have hcw : c.wt < (Val.list [c, g]).wt := wt_le_wt_list (by simp)
  have hgw : g.wt < (Val.list [c, g]).wt := wt_le_wt_list (by simp)
  have hαw : (encPerm α).wt < c.wt := wt_le_wt_list (by simp)
  have hβw : (encPerm β).wt < c.wt := wt_le_wt_list (by simp)
  have hnw : (Val.nat X.fiber.card).wt < c.wt := wt_le_wt_list (by simp)
  have hRw : (natList (List.range q)).wt < c.wt := wt_le_wt_list (by simp)
  have hq2 : (q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hq 2
  have hq3 : (q + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left hq 3
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have hρ := wt_encPerm_le (itcqRho X a)
  have hαρ := wt_encPerm_le (α * itcqRho X a)
  have hαρβ := wt_encPerm_le (α * itcqRho X a * β)
  have hgn := wt_list2_le g (.nat X.fiber.card)
  have hgnR := wt_list2_le (.list [g, .nat X.fiber.card]) (natList (List.range q))
  have h2a := wt_list2_le (encPerm α) (encPerm (itcqRho X a))
  have h2b := wt_list2_le (encPerm (α * itcqRho X a)) (encPerm β)
  obtain ⟨W, hW⟩ : ∃ W, W = 20 * M ^ 2 + 20 := ⟨_, rfl⟩
  have A0 := StDC.arg (P := P) (rest := []) (vs := [c, g]) (j := 0) rfl (W := W) (by omega)
    (by omega) (by omega)
  have A1 := StDC.arg (P := P) (rest := []) (vs := [c, g]) (j := 1) rfl (W := W) (by omega)
    (by omega) (by omega)
  have gα := StDC.get A0 (StDC.nat 0 (by omega)) (v := encPerm α) rfl (by omega)
  have gβ := StDC.get A0 (StDC.nat 1 (by omega)) (v := encPerm β) rfl (by omega)
  have gn := StDC.get A0 (StDC.nat 2 (by omega)) (v := .nat X.fiber.card) rfl (by omega)
  have gR := StDC.get A0 (StDC.nat 3 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have m1 := StDC.mk2 A1 gn (by omega) (by omega)
  have m2 := StDC.mk2 m1 gR (by omega) (by omega)
  have hgz : (Val.list [encPerm (itciD X.fiber.card a), .nat X.fiber.card]).wt =
      (Val.list [g, .nat X.fiber.card]).wt := rfl
  have cρ := StDC.call m2 (itcq_rho_spec hm hfr X a (M := 4 * M + 10) (by omega) (by omega))
    (by omega)
  have c1 := StDC.call (StDC.mk2 gα cρ (by omega) (by omega)) (compose_spec hcmp α (itcqRho X a))
    (by omega)
  have c2 := StDC.call (StDC.mk2 c1 gβ (by omega) (by omega))
    (compose_spec hcmp (α * itcqRho X a) β) (by omega)
  refine StDC.funDet hf c2 ?_
  refine itcq_lfC_arith ?_
  have : permK * (q + 1) ^ 3 ≤ permK * M ^ 3 := Nat.mul_le_mul_left _ hq3
  rw [hW] at *
  omega

/-- A list related entrywise to `l.map encPerm` by `x = encPerm g → w = F g` is `l.map F`. -/
theorem itcq_f2_perm {m : ℕ} {F : Perm (Fin m) → Val} :
    ∀ {l : List (Perm (Fin m))} {ws : List Val},
      List.Forall₂ (fun x w => ∀ g, x = encPerm g → w = F g) (l.map encPerm) ws → ws = l.map F
  | [], _, h => by simp only [List.map_nil, List.forall₂_nil_left_iff] at h; exact h
  | g :: l, ws, h => by
    rw [List.map_cons] at h
    cases h with
    | cons h1 h2 => rw [h1 g rfl, itcq_f2_perm h2]; rfl

/-- **A map over a list of permutations.** -/
theorem itcq_mapP_spec {mb fb : ℕ} (hm : P.HasAt mb (mapFuns mb fb)) {c : Val} {m : ℕ}
    {l : List (Perm (Fin m))} {F : Perm (Fin m) → Val} {Bd : ℕ}
    (hf : ∀ g ∈ l, FunDet P fb (.list [c, encPerm g]) (F g) Bd) :
    FunAll P mb (.list [c, .list (l.map encPerm)]) (fun w cost => w = .list (l.map F) ∧
      cost ≤ l.length * Bd + mapK * (l.length + 1) *
        ((Val.list [c, .list (l.map encPerm)]).wt + w.wt + 1)) := by
  have key := map_spec (P := P) hm (c := c) (xs := l.map encPerm)
    (R := fun x w => ∀ g, x = encPerm g → w = F g) (B := fun _ => Bd) (by
      intro x hx
      obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hx
      refine FunAll.mono (hf g₀ hg₀) fun w cost ⟨hw, hc⟩ => ⟨fun g hg => ?_, hc⟩
      rw [encPerm_injective hg] at hw
      exact hw)
  refine key.mono fun w cost ⟨ws, hw, h2, hc⟩ => ⟨by rw [hw, itcq_f2_perm h2], ?_⟩
  simp only [List.map_map, List.length_map, Function.comp_def, List.map_const',
    List.sum_replicate, smul_eq_mul] at hc
  exact hc

end Prog

end GI.Impl
