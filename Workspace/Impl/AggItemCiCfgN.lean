import Workspace.Impl.AggItemCiCfgQ

/-!
# The configuration query: the step program on a nonempty answer

`itcqSbF` on `[kst, [x, encGroup gs]]` with the kept state `kst = itcqKs X x₀ Y y₀ w` and
`x = itciD n p₁` (Lemma A.12, after the call):
1. `R = [0, …, q - 1]`, the outer points `D_X`, `D_Y` by color (`itcqDsF`), the enumerations
   `itciEnum X = C_X ++ D_X`, `itciEnum Y = C_Y ++ D_Y` and the inverse of the first;
2. `σ₀ = itciEnum Y * itcqRho X p₁ * (itciEnum X)⁻¹ = itciExt X Y p₁` (`itcqLfB`);
3. the lifts `itciLift X (itciDec g)` of the answer's generators `1 :: gs` (`itcqLfB`, mapped);
4. the transpositions of two outer points of the same color `itcqCs X`, and `S = itcqSg X gs`
   (lifts, then these);
5. the overcoset program `itcqOuF` on `[σ₀, S, w]`.
`itcq_sbF_spec` gives `itciRes (itciOV (itcqOs X (itciExt X Y p₁) (itcqSg X gs))) w`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

variable {q : ℕ}

/-- The generators the step program builds: the lifts of the answer's generators (with the
identity of `encGroup` first), then the transpositions outside the fiber. -/
noncomputable def itcqSg (X : PairCfg q) (gs : List (Perm (Fin (X.fiber.card * X.fiber.card)))) :
    List (Perm (Fin q)) :=
  ((1 :: gs).map itciDec).map (itciLift X) ++ itcqCs X

/-- Entry `j` of the kept state (entry `0` of the input). -/
def itcqK (j : ℕ) : Expr := .get (.get (.var 0) (.nat 0)) (.nat j)

/-- Entry `j` of the answer (entry `1` of the input). -/
def itcqU (j : ℕ) : Expr := .get (.get (.var 0) (.nat 1)) (.nat j)

/-- **The step program on a nonempty answer.** -/
def itcqSbF (rng fdl app inv lf lm cs ou : ℕ) : Expr :=
  .letE (.call rng (.length (.get (itcqK 1) (.nat 0))))
  (.letE (.call fdl (itcqK 1))
  (.letE (.call fdl (itcqK 2))
  (.letE (.call app (mk2 (itcqK 3) (.var 2)))
  (.letE (.call app (mk2 (itcqK 4) (.var 3)))
  (.letE (.call inv (.var 4))
  (.letE (.length (itcqK 3))
  (.letE (.call lf (mk2 (mk4 (.var 5) (.var 6) (.var 7) (.var 1)) (itcqU 0)))
  (.letE (.call lm (mk2 (mk4 (.var 4) (.var 6) (.var 7) (.var 1)) (.get (itcqU 1) (.nat 1))))
  (.letE (.call cs (mk3 (.var 2) (.var 1) (itcqK 1)))
  (.letE (.call app (mk2 (.var 9) (.var 10)))
  (.call ou (mk3 (.var 8) (.var 11) (itcqK 0)))))))))))))

/-- The cost bound of `itcqSbF`. -/
def itcqSbC (M : ℕ) : ℕ :=
  300 * (itcqOuC (100 * (M + 1) ^ 4) + 1) + 2 * itcqDsC M + itcqCsC (30 * (M + 1) ^ 2)

theorem itcq_dv_wt (Z : PairCfg q) : (itcqDV Z).wt ≤ 5 * (q + 1) ^ 2 := by
  refine wt_natList_le_sq (fun x hx => ?_) ?_
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact a.isLt.le
  · simp only [List.length_map, itciFo_length]
    exact Finset.card_le_univ _ |>.trans (by simp)

theorem itcqCs_length (X : PairCfg q) : (itcqCs X).length ≤ q * q := by
  have hd : (itciFo X).length ≤ q := by
    rw [itciFo_length]; exact Finset.card_le_univ _ |>.trans (by simp)
  simp only [itcqCs, List.length_map, List.length_range]
  exact Nat.mul_le_mul hd hd

/-- The lifted generators, as the program builds them. -/
theorem itcq_lifts_eq (X : PairCfg q) (gs : List (Perm (Fin (X.fiber.card * X.fiber.card)))) :
    (1 :: gs).map (fun g => encPerm (itciEnum X * itcqRho X (itciDec g) * (itciEnum X)⁻¹)) =
      (((1 :: gs).map itciDec).map (itciLift X)).map encPerm := by
  simp only [List.map_map]
  refine List.map_congr_left fun g _ => ?_
  simp only [Function.comp_apply, itcq_lift_rho]

/-- A bound on the costs of the pieces of `itcqSbF`. -/
theorem itcq_sbC_arith {M q n C c2 c3 c4 c5 c9 c11 W : ℕ} (hq : q + 1 ≤ M) (hn : n ≤ 290)
    (hW : W = itcqOuC (100 * (M + 1) ^ 4))
    (h2 : c2 ≤ itcqDsC M) (h3 : c3 ≤ itcqDsC M) (h4 : c4 ≤ 1000 * (M + 1) * (100 * (M + 1) ^ 2))
    (h5 : c5 ≤ 1000 * (M + 1) * (100 * (M + 1) ^ 2))
    (h9 : c9 ≤ M * itcqLfC (200 * (M + 1) ^ 2) + 1000 * (M + 1) * (100 * (M + 1) ^ 3))
    (h11 : c11 ≤ 1000 * (M + 1) ^ 2 * (100 * (M + 1) ^ 4))
    (hC : C ≤ n * (W + 1) + (10000 * (q + 1) ^ 3 + c2 + c3 + c4 + c5 + invK * (q + 1) ^ 4 +
      itcqLfC (200 * (M + 1) ^ 2) + c9 + itcqCsC (30 * (M + 1) ^ 2) + c11 + W)) :
    C ≤ itcqSbC M := by
  unfold itcqSbC
  rw [← hW]
  generalize itcqDsC M = Ds at *
  generalize itcqCsC (30 * (M + 1) ^ 2) = Cs at *
  unfold itcqOuC at hW
  unfold itcqLfC at h9 hC
  unfold invK at hC
  obtain ⟨T, hT⟩ : ∃ T, T = M + 1 := ⟨_, rfl⟩
  rw [← hT] at hW h4 h5 h9 h11 hC
  have hT1 : 1 ≤ T := by omega
  -- the powers of `T` up to `12` are below `T ^ 12`
  have p2 : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num) _
  have p3 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right hT1 (by omega)
  have p4 : T ^ 3 ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by omega)
  have p5 : T ^ 4 ≤ T ^ 5 := Nat.pow_le_pow_right hT1 (by omega)
  have p6 : T ^ 5 ≤ T ^ 6 := Nat.pow_le_pow_right hT1 (by omega)
  have p7 : T ^ 6 ≤ T ^ 7 := Nat.pow_le_pow_right hT1 (by omega)
  have p12 : T ^ 7 ≤ T ^ 12 := Nat.pow_le_pow_right hT1 (by omega)
  -- `W ≥ 10¹⁰ T¹²`
  have hW12 : 10 ^ 22 * T ^ 12 ≤ W := by
    rw [hW]
    have : 100 * T ^ 2 ≤ 100 * T ^ 4 + 1 := by omega
    have h6 := Nat.pow_le_pow_left this 6
    have e : (100 * T ^ 2) ^ 6 = 10 ^ 12 * T ^ 12 := by ring
    have e' : 10 ^ 22 * T ^ 12 = 10 ^ 10 * (10 ^ 12 * T ^ 12) := by ring
    rw [e']
    exact Nat.mul_le_mul_left _ (e ▸ h6)
  -- the pieces
  have e2 : (M + 2) ^ 3 ≤ (2 * T) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have e2' : (2 * T) ^ 3 = 8 * T ^ 3 := by ring
  have e4 : 1000 * T * (100 * T ^ 2) = 100000 * T ^ 3 := by ring
  have e9a : M * (10 ^ 9 * (200 * T ^ 2 + 1) ^ 3) ≤ T * (10 ^ 9 * (202 * T ^ 2) ^ 3) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
  have e9b : T * (10 ^ 9 * (202 * T ^ 2) ^ 3) = 10 ^ 9 * 8242408 * T ^ 7 := by ring
  have e9c : 1000 * T * (100 * T ^ 3) = 100000 * T ^ 4 := by ring
  have elf : 10 ^ 9 * (200 * T ^ 2 + 1) ^ 3 ≤ 10 ^ 9 * (202 * T ^ 2) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have elf' : 10 ^ 9 * (202 * T ^ 2) ^ 3 = 10 ^ 9 * 8242408 * T ^ 6 := by ring
  have e11 : 1000 * T ^ 2 * (100 * T ^ 4) = 100000 * T ^ 6 := by ring
  have eq3 : (q + 1) ^ 3 ≤ T ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have eq4 : (q + 1) ^ 4 ≤ T ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have eq6 : (q + 1) ^ 6 ≤ T ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hnW : n * (W + 1) ≤ 290 * (W + 1) := Nat.mul_le_mul_right _ hn
  clear hW
  generalize (100 * T ^ 4 + 1) ^ 6 = Z at *
  generalize (200 * T ^ 2 + 1) ^ 3 = A at *
  generalize (M + 2) ^ 3 = B at *
  generalize (q + 1) ^ 3 = Q3 at *
  generalize (q + 1) ^ 4 = Q4 at *
  generalize (q + 1) ^ 6 = Q6 at *
  generalize T ^ 2 = T2 at *
  generalize T ^ 3 = T3 at *
  generalize T ^ 4 = T4 at *
  generalize T ^ 5 = T5 at *
  generalize T ^ 6 = T6 at *
  generalize T ^ 7 = T7 at *
  generalize T ^ 12 = T12 at *
  omega

/-- `itcq_sbC_arith` in the shape of the cost of `itcqSbF`. -/
theorem itcq_sbC_shape {M q n c2 c3 c4 c5 c9 c11 W : ℕ} (hq : q + 1 ≤ M) (hn : n ≤ 290)
    (hW : W = itcqOuC (100 * (M + 1) ^ 4))
    (h2 : c2 ≤ itcqDsC M) (h3 : c3 ≤ itcqDsC M) (h4 : c4 ≤ 1000 * (M + 1) * (100 * (M + 1) ^ 2))
    (h5 : c5 ≤ 1000 * (M + 1) * (100 * (M + 1) ^ 2))
    (h9 : c9 ≤ M * itcqLfC (200 * (M + 1) ^ 2) + 1000 * (M + 1) * (100 * (M + 1) ^ 3))
    (h11 : c11 ≤ 1000 * (M + 1) ^ 2 * (100 * (M + 1) ^ 4)) :
    n * (W + 1) + (0 + 0 + 10000 * (q + 1) ^ 3 + (0 + c2 + (0 + c3 + (0 + 0 + c4 +
      (0 + 0 + c5 + (0 + invK * (q + 1) ^ 4 + (0 + (0 + 0 + 0 + 0 + 0 +
        itcqLfC (200 * (M + 1) ^ 2) + (0 + 0 + 0 + 0 + (0 + 0) + c9 +
          (0 + 0 + 0 + 0 + 0 + itcqCsC (30 * (M + 1) ^ 2) +
          (0 + 0 + c11 + (0 + 0 + 0 + W)))))))))))) ≤ itcqSbC M :=
  itcq_sbC_arith hq hn hW h2 h3 h4 h5 h9 h11 (by omega)

section Prog

variable {P : Program}

set_option maxHeartbeats 8000000 in
/-- **The step program on a nonempty answer.** -/
theorem itcq_sbF_spec {f rng fdl app inv lf lm cs ou : ℕ}
    (hf : P.funs[f]? = some (itcqSbF rng fdl app inv lf lm cs ou))
    (hrng : P.HasAt rng (rangeFuns rng))
    (hdl : ∀ (Z : PairCfg q) (z₀ : Fin q) {W : ℕ}, (rcCertIn Z z₀).wt ≤ W →
      FunDet P fdl (rcCertIn Z z₀) (itcqDV Z) (itcqDsC W))
    (happ : P.HasAt app (appendFuns app)) (hinv : P.HasAt inv (invFuns inv))
    (hlf : ∀ (X : PairCfg q) (α β : Perm (Fin q)) (a : Perm (Fin X.fiber.card)) {M : ℕ},
      q + 1 ≤ M → (Val.list [.list [encPerm α, encPerm β, .nat X.fiber.card,
        natList (List.range q)], encPerm (itciD X.fiber.card a)]).wt ≤ M →
      FunDet P lf (.list [.list [encPerm α, encPerm β, .nat X.fiber.card, natList (List.range q)],
        encPerm (itciD X.fiber.card a)]) (encPerm (α * itcqRho X a * β)) (itcqLfC M))
    (hlm : P.HasAt lm (mapFuns lm lf))
    (hcs : ∀ (X : PairCfg q) (x₀ : Fin q) {V : ℕ}, q + 1 ≤ V →
      (Val.list [itcqDV X, natList (List.range q), rcCertIn X x₀]).wt ≤ V →
      FunDet P cs (.list [itcqDV X, natList (List.range q), rcCertIn X x₀])
        (.list ((itcqCs X).map encPerm)) (itcqCsC V))
    (hou : ∀ (X : PairCfg q) (σ₀ : Perm (Fin q)) (S : List (Perm (Fin q))) (w : Val) {M : ℕ},
      q + 1 ≤ M → (Val.list [encPerm σ₀, .list (S.map encPerm), w]).wt ≤ M →
      FunDet P ou (.list [encPerm σ₀, .list (S.map encPerm), w])
        (itciRes (itciOV (itcqOs X σ₀ S)) w) (itcqOuC M))
    (X : PairCfg q) (x₀ : Fin q) (Y : PairCfg q) (y₀ : Fin q) (w : Val)
    (p₁ : Perm (Fin X.fiber.card)) (gs : List (Perm (Fin (X.fiber.card * X.fiber.card))))
    (hgD : ∀ g ∈ gs, itciD _ (itciDec g) = g) {M : ℕ} (hq : q + 1 ≤ M)
    (hM : (Val.list [itcqKs X x₀ Y y₀ w, .list [encPerm (itciD _ p₁), encGroup gs]]).wt ≤ M) :
    FunDet P f (.list [itcqKs X x₀ Y y₀ w, .list [encPerm (itciD _ p₁), encGroup gs]])
      (itciRes (itciOV (itcqOs X (itciExt X Y p₁) (itcqSg X gs))) w) (itcqSbC M) := by
  classical
  -- the input and its parts
  have hks : (itcqKs X x₀ Y y₀ w).wt < (Val.list [itcqKs X x₀ Y y₀ w,
      .list [encPerm (itciD _ p₁), encGroup gs]]).wt := wt_le_wt_list (List.mem_cons_self ..)
  have hus : (Val.list [encPerm (itciD _ p₁), encGroup gs]).wt < (Val.list [itcqKs X x₀ Y y₀ w,
      .list [encPerm (itciD _ p₁), encGroup gs]]).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hk0 : w.wt < (itcqKs X x₀ Y y₀ w).wt := wt_le_wt_list (List.mem_cons_self ..)
  have hk1 : (rcCertIn X x₀).wt < (itcqKs X x₀ Y y₀ w).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hk2 : (rcCertIn Y y₀).wt < (itcqKs X x₀ Y y₀ w).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hk3 : (itcqFV X).wt < (itcqKs X x₀ Y y₀ w).wt := wt_le_wt_list
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have hk4 : (itcqFV Y).wt < (itcqKs X x₀ Y y₀ w).wt := wt_le_wt_list
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have hu0 : (encPerm (itciD _ p₁)).wt < (Val.list [encPerm (itciD _ p₁), encGroup gs]).wt :=
    wt_le_wt_list (List.mem_cons_self ..)
  have hu1 : (encGroup gs).wt < (Val.list [encPerm (itciD _ p₁), encGroup gs]).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hG : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hcol : (rcColVal X).wt < (rcCertIn X x₀).wt := wt_le_wt_list (List.mem_cons_self ..)
  have hℓ : (1 :: gs).length < M := by
    have := length_lt_wt_list ((1 :: gs).map encPerm); rw [List.length_map] at this; omega
  have hnq : X.fiber.card ≤ q := by have := X.fiber.card_le_univ; simpa using this
  have hq2 : (q + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hM1 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hM23 : (M + 1) ^ 2 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM34 : (M + 1) ^ 3 ≤ (M + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  -- value weights
  have wR := itcq_range_wt q
  have wDX := itcq_dv_wt X
  have wDY := itcq_dv_wt Y
  have wPX := wt_encPerm_le (itciEnum X)
  have wPY := wt_encPerm_le (itciEnum Y)
  have wPXi := wt_encPerm_le (itciEnum X)⁻¹
  have wσ := wt_encPerm_le (itciEnum Y * itcqRho X p₁ * (itciEnum X)⁻¹)
  have wn := wt_nat_le X.fiber.card
  have wqn := wt_nat_le q
  have wL := it_perms_wt (q := q) (l := ((1 :: gs).map itciDec).map (itciLift X)) (m := M)
    (by simp only [List.length_map]; omega)
  have wLm : M * (9 * (q + 1) ^ 2) ≤ (M + 1) * (9 * (M + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have eL : (M + 1) * (9 * (M + 1) ^ 2) = 9 * (M + 1) ^ 3 := by ring
  have hCl := itcqCs_length X
  have hqq : q * q ≤ (M + 1) ^ 2 := by
    have := Nat.mul_le_mul (show q ≤ M + 1 by omega) (show q ≤ M + 1 by omega)
    have e : (M + 1) ^ 2 = (M + 1) * (M + 1) := by ring
    omega
  have wC := it_perms_wt (q := q) (l := itcqCs X) (m := (M + 1) ^ 2) (by omega)
  have wCm : (M + 1) ^ 2 * (9 * (q + 1) ^ 2) ≤ (M + 1) ^ 2 * (9 * (M + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have eC : (M + 1) ^ 2 * (9 * (M + 1) ^ 2) = 9 * (M + 1) ^ 4 := by ring
  have wS := it_perms_wt (q := q) (l := itcqSg X gs) (m := 2 * (M + 1) ^ 2) (by
    simp only [itcqSg, List.length_append, List.length_map]; omega)
  have wSm : 2 * (M + 1) ^ 2 * (9 * (q + 1) ^ 2) ≤ 2 * (M + 1) ^ 2 * (9 * (M + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have eS : 2 * (M + 1) ^ 2 * (9 * (M + 1) ^ 2) = 18 * (M + 1) ^ 4 := by ring
  -- the bound of the input of the overcoset program and of every value
  have hou_in : (Val.list [encPerm (itciEnum Y * itcqRho X p₁ * (itciEnum X)⁻¹),
      .list ((itcqSg X gs).map encPerm), w]).wt ≤ 100 * (M + 1) ^ 4 := by
    have := wt_list3_le (encPerm (itciEnum Y * itcqRho X p₁ * (itciEnum X)⁻¹))
      (.list ((itcqSg X gs).map encPerm)) w
    omega
  have hext := itcq_ext_rho X Y p₁
  have wE := wt_encPerm_le (itciExt X Y p₁)
  have hou_in : (Val.list [encPerm (itciExt X Y p₁), .list ((itcqSg X gs).map encPerm), w]).wt ≤
      100 * (M + 1) ^ 4 := by
    have := wt_list3_le (encPerm (itciExt X Y p₁)) (.list ((itcqSg X gs).map encPerm)) w
    omega
  have hO := hou X (itciExt X Y p₁) (itcqSg X gs) w (M := 100 * (M + 1) ^ 4) (by omega) hou_in
  have hout := hO.wt_lt
  obtain ⟨W, hW⟩ : ∃ W, W = itcqOuC (100 * (M + 1) ^ 4) := ⟨_, rfl⟩
  have hWb : 100 * (M + 1) ^ 4 ≤ W := by
    rw [hW]; unfold itcqOuC
    have : 100 * (M + 1) ^ 4 ≤ (100 * (M + 1) ^ 4 + 1) ^ 6 :=
      (Nat.le_succ _).trans (Nat.le_self_pow (by norm_num) _)
    omega
  rw [← hW] at hO hout
  set vin := Val.list [itcqKs X x₀ Y y₀ w, .list [encPerm (itciD _ p₁), encGroup gs]] with hvin
  -- reading the kept state and the answer
  have hK : ∀ (env : List Val), env[0]? = some vin → ∀ (j : ℕ) (a : Val),
      [w, rcCertIn X x₀, rcCertIn Y y₀, itcqFV X, itcqFV Y][j]? = some a → a.wt ≤ W →
      j + 2 ≤ W → StDC P env (itcqK j) a 5 0 W := by
    intro env he j a ha haw hj
    have v0 := StDC.var' (P := P) he (W := W) (by omega)
    have g0 := StDC.get v0 (StDC.nat 0 (by omega)) (v := itcqKs X x₀ Y y₀ w) rfl (by omega)
    exact (StDC.get g0 (StDC.nat j hj) ha haw).mono (by omega) (by omega)
  have hU : ∀ (env : List Val), env[0]? = some vin → ∀ (j : ℕ) (a : Val),
      [encPerm (itciD _ p₁), encGroup gs][j]? = some a → a.wt ≤ W →
      j + 2 ≤ W → StDC P env (itcqU j) a 5 0 W := by
    intro env he j a ha haw hj
    have v0 := StDC.var' (P := P) he (W := W) (by omega)
    have g0 := StDC.get v0 (StDC.nat 1 (by omega))
      (v := .list [encPerm (itciD _ p₁), encGroup gs]) rfl (by omega)
    exact (StDC.get g0 (StDC.nat j hj) ha haw).mono (by omega) (by omega)
  -- 1. `R`
  have g1 := hK [vin] rfl 1 (rcCertIn X x₀) rfl (by omega) (by omega)
  have g10 := StDC.get g1 (StDC.nat 0 (by omega)) (v := rcColVal X) rfl (by omega)
  have ln := StDC.length g10 (by rw [itcq_rc_length]; omega)
  rw [itcq_rc_length] at ln
  have d1 := StDC.call ln (st_range_det hrng q) (by omega)
  -- 2, 3. the points outside the fibers
  have d2 := StDC.call (hK [vin, natList (List.range q)] rfl 1 (rcCertIn X x₀) rfl (by omega)
    (by omega)) (hdl X x₀ (W := M) (by omega)) (by omega)
  have d3 := StDC.call (hK [vin, natList (List.range q), itcqDV X] rfl 2 (rcCertIn Y y₀) rfl
    (by omega) (by omega)) (hdl Y y₀ (W := M) (by omega)) (by omega)
  -- 4, 5. the enumerations
  have hx4 := wt_list2_le (itcqFV X) (itcqDV X)
  have a4 := StDC.mk2 (hK [vin, natList (List.range q), itcqDV X, itcqDV Y] rfl 3 (itcqFV X) rfl
    (by omega) (by omega)) (StDC.var' (P := P)
      (env := [vin, natList (List.range q), itcqDV X, itcqDV Y]) (i := 2) rfl (W := W) (by omega))
    (by omega) (by omega)
  have d4 := StDC.call a4 (itcq_app_det happ (((itciFl X.fiber).map Fin.val).map Val.nat)
    (((itciFo X).map Fin.val).map Val.nat)) (by rw [← itcq_enum_enc]; omega)
  rw [← itcq_enum_enc] at d4
  have hx5 := wt_list2_le (itcqFV Y) (itcqDV Y)
  have a5 := StDC.mk2 (hK [vin, natList (List.range q), itcqDV X, itcqDV Y,
    encPerm (itciEnum X)] rfl 4 (itcqFV Y) rfl (by omega) (by omega)) (StDC.var' (P := P)
      (env := [vin, natList (List.range q), itcqDV X, itcqDV Y, encPerm (itciEnum X)]) (i := 3)
      rfl (W := W) (by omega)) (by omega) (by omega)
  have d5 := StDC.call a5 (itcq_app_det happ (((itciFl Y.fiber).map Fin.val).map Val.nat)
    (((itciFo Y).map Fin.val).map Val.nat)) (by rw [← itcq_enum_enc]; omega)
  rw [← itcq_enum_enc] at d5
  -- 6. the inverse
  have d6 := StDC.call (StDC.var' (P := P) (env := [vin, natList (List.range q), itcqDV X,
    itcqDV Y, encPerm (itciEnum X), encPerm (itciEnum Y)]) (i := 4) rfl (W := W) (by omega))
    (inv_spec hinv (itciEnum X)) (by omega)
  -- 7. `n`
  have d7 := StDC.length (hK [vin, natList (List.range q), itcqDV X, itcqDV Y,
    encPerm (itciEnum X), encPerm (itciEnum Y), encPerm (itciEnum X)⁻¹] rfl 3 (itcqFV X) rfl
    (by omega) (by omega)) (by rw [itcq_fv_len]; omega)
  rw [itcq_fv_len] at d7
  -- 8. the extension
  set e7 : List Val := [vin, natList (List.range q), itcqDV X, itcqDV Y, encPerm (itciEnum X),
    encPerm (itciEnum Y), encPerm (itciEnum X)⁻¹, .nat X.fiber.card] with he7
  have hc8 := wt_list4_le (encPerm (itciEnum Y)) (encPerm (itciEnum X)⁻¹) (.nat X.fiber.card)
    (natList (List.range q))
  have m8 := StDC.mk4 (StDC.var' (P := P) (env := e7) (i := 5) rfl (W := W) (by omega))
    (StDC.var' (P := P) (env := e7) (i := 6) rfl (W := W) (by omega))
    (StDC.var' (P := P) (env := e7) (i := 7) rfl (W := W) (by omega))
    (StDC.var' (P := P) (env := e7) (i := 1) rfl (W := W) (by omega)) (by omega) (by omega)
  have hx8 := wt_list2_le (.list [encPerm (itciEnum Y), encPerm (itciEnum X)⁻¹,
    .nat X.fiber.card, natList (List.range q)]) (encPerm (itciD _ p₁))
  have d8 := StDC.call (StDC.mk2 m8 (hU e7 rfl 0 (encPerm (itciD _ p₁)) rfl (by omega) (by omega))
    (by omega) (by omega)) (hlf X (itciEnum Y) (itciEnum X)⁻¹ p₁ (M := 200 * (M + 1) ^ 2)
      (by omega) (by omega)) (by omega)
  rw [← hext] at d8
  -- 9. the lifted generators
  set e8 : List Val := e7 ++ [encPerm (itciExt X Y p₁)] with he8
  have hc9 := wt_list4_le (encPerm (itciEnum X)) (encPerm (itciEnum X)⁻¹) (.nat X.fiber.card)
    (natList (List.range q))
  have m9 := StDC.mk4 (StDC.var' (P := P) (env := e8) (i := 4) rfl (W := W) (by omega))
    (StDC.var' (P := P) (env := e8) (i := 6) rfl (W := W) (by omega))
    (StDC.var' (P := P) (env := e8) (i := 7) rfl (W := W) (by omega))
    (StDC.var' (P := P) (env := e8) (i := 1) rfl (W := W) (by omega)) (by omega) (by omega)
  have gG := StDC.get (hU e8 rfl 1 (encGroup gs) rfl (by omega) (by omega)) (StDC.nat 1 (by omega))
    (v := .list ((1 :: gs).map encPerm)) rfl (by omega)
  have hx9 := wt_list2_le (.list [encPerm (itciEnum X), encPerm (itciEnum X)⁻¹,
    .nat X.fiber.card, natList (List.range q)]) (.list ((1 :: gs).map encPerm))
  have hmp := itcq_mapP_spec (P := P) hlm (c := .list [encPerm (itciEnum X),
    encPerm (itciEnum X)⁻¹, .nat X.fiber.card, natList (List.range q)]) (l := 1 :: gs)
    (F := fun g => encPerm (itciEnum X * itcqRho X (itciDec g) * (itciEnum X)⁻¹))
    (Bd := itcqLfC (200 * (M + 1) ^ 2)) (fun g hg => by
      have e : itciD X.fiber.card (itciDec g) = g := by
        rcases List.mem_cons.1 hg with rfl | hg'
        · rw [itciDec_one, map_one]
        · exact hgD g hg'
      have hgw : (encPerm g).wt < (Val.list ((1 :: gs).map encPerm)).wt :=
        wt_le_wt_list (List.mem_map.2 ⟨g, hg, rfl⟩)
      have hx := wt_list2_le (.list [encPerm (itciEnum X), encPerm (itciEnum X)⁻¹,
        .nat X.fiber.card, natList (List.range q)]) (encPerm g)
      have := hlf X (itciEnum X) (itciEnum X)⁻¹ (itciDec g) (M := 200 * (M + 1) ^ 2) (by omega)
        (by rw [e]; omega)
      rw [e] at this
      exact this)
  rw [itcq_lifts_eq] at hmp
  have hmd : FunDet P lm (.list [.list [encPerm (itciEnum X), encPerm (itciEnum X)⁻¹,
      .nat X.fiber.card, natList (List.range q)], .list ((1 :: gs).map encPerm)])
      (.list ((((1 :: gs).map itciDec).map (itciLift X)).map encPerm))
      ((1 :: gs).length * itcqLfC (200 * (M + 1) ^ 2) + mapK * ((1 :: gs).length + 1) *
        ((Val.list [.list [encPerm (itciEnum X), encPerm (itciEnum X)⁻¹, .nat X.fiber.card,
          natList (List.range q)], .list ((1 :: gs).map encPerm)]).wt +
          (Val.list ((((1 :: gs).map itciDec).map (itciLift X)).map encPerm)).wt + 1)) :=
    hmp.mono fun v c ⟨hv, hc⟩ => ⟨hv, by subst hv; exact hc⟩
  have d9 := StDC.call (StDC.mk2 m9 gG (by omega) (by omega)) hmd (by omega)
  -- 10. the transpositions outside the fiber
  set e9 : List Val := e8 ++ [.list ((((1 :: gs).map itciDec).map (itciLift X)).map encPerm)]
    with he9
  have hx10 := wt_list3_le (itcqDV X) (natList (List.range q)) (rcCertIn X x₀)
  have d10 := StDC.call (StDC.mk3 (StDC.var' (P := P) (env := e9) (i := 2) rfl (W := W) (by omega))
    (StDC.var' (P := P) (env := e9) (i := 1) rfl (W := W) (by omega))
    (hK e9 rfl 1 (rcCertIn X x₀) rfl (by omega) (by omega)) (by omega) (by omega))
    (hcs X x₀ (V := 30 * (M + 1) ^ 2) (by omega) (by omega)) (by omega)
  -- 11. `S`
  set e10 : List Val := e9 ++ [.list ((itcqCs X).map encPerm)] with he10
  have hx11 := wt_list2_le (.list ((((1 :: gs).map itciDec).map (itciLift X)).map encPerm))
    (.list ((itcqCs X).map encPerm))
  have eS : (itcqSg X gs).map encPerm = (((1 :: gs).map itciDec).map (itciLift X)).map encPerm ++
      (itcqCs X).map encPerm := by rw [itcqSg, List.map_append]
  have d11 := StDC.call (StDC.mk2 (StDC.var' (P := P) (env := e10) (i := 9) rfl (W := W)
    (by omega)) (StDC.var' (P := P) (env := e10) (i := 10) rfl (W := W) (by omega)) (by omega)
    (by omega)) (itcq_app_det happ _ _) (by rw [← eS]; omega)
  rw [← eS] at d11
  -- 12. the overcosets
  set e11 : List Val := e10 ++ [.list ((itcqSg X gs).map encPerm)] with he11
  have d12 := StDC.call (StDC.mk3 (StDC.var' (P := P) (env := e11) (i := 8) rfl (W := W)
    (by omega)) (StDC.var' (P := P) (env := e11) (i := 11) rfl (W := W) (by omega))
    (hK e11 rfl 0 w rfl (by omega) (by omega)) (by omega) (by omega)) hO (by omega)
  have b11 := StDC.letE d11 d12 (by omega)
  have b10 := StDC.letE d10 b11 (by omega)
  have b9 := StDC.letE d9 b10 (by omega)
  have b8 := StDC.letE d8 b9 (by omega)
  have b7 := StDC.letE d7 b8 (by omega)
  have b6 := StDC.letE d6 b7 (by omega)
  have b5 := StDC.letE d5 b6 (by omega)
  have b4 := StDC.letE d4 b5 (by omega)
  have b3 := StDC.letE d3 b4 (by omega)
  have b2 := StDC.letE d2 b3 (by omega)
  have b1 := StDC.letE d1 b2 (by omega)
  refine StDC.funDet hf (P := P) b1 ?_
  clear b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12
  have hlX : (((itciFo X).map Fin.val).map Val.nat).length ≤ q := by
    simp only [List.length_map, itciFo_length]; exact Finset.card_le_univ _ |>.trans (by simp)
  have hlY : (((itciFo Y).map Fin.val).map Val.nat).length ≤ q := by
    simp only [List.length_map, itciFo_length]; exact Finset.card_le_univ _ |>.trans (by simp)
  have eX : Val.list [Val.list (((itciFl X.fiber).map Fin.val).map Val.nat),
      Val.list (((itciFo X).map Fin.val).map Val.nat)] = Val.list [itcqFV X, itcqDV X] := rfl
  have eY : Val.list [Val.list (((itciFl Y.fiber).map Fin.val).map Val.nat),
      Val.list (((itciFo Y).map Fin.val).map Val.nat)] = Val.list [itcqFV Y, itcqDV Y] := rfl
  have hlC : ((itcqCs X).map encPerm).length + 1 ≤ (M + 1) ^ 2 := by
    rw [List.length_map]
    have := Nat.mul_le_mul (show q ≤ M by omega) (show q ≤ M by omega)
    have e : (M + 1) ^ 2 = M * M + 2 * M + 1 := by ring
    omega
  have hpos : 1 ≤ M + 1 := by omega
  refine itcq_sbC_shape hq (by norm_num) hW (by rfl) (by rfl) ?_ ?_ ?_ ?_
  · rw [eX]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  · rw [eY]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  · exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega))
  · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)

end Prog

end GI.Impl
