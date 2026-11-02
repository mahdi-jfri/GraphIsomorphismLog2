import Workspace.Impl.TermJHMath
import Workspace.Impl.TermJProgYg2

/-!
# The transporter of one label: the small programs

All permutations of the pairs are on `Fin (m q)` through `finProdFinEquiv`, as in
`TermJProgPair.lean`. `lc = tmJLocCtx m q` holds `1` on `Fin m`, `1` on `Fin q`, `q` and `m`.

* `tmJHCstF`, on `[encPerm h, lc]`: the constant pair `(h; 1)` (`tmJH_cst_spec`).
* `tmJHDecF`, on `[encPerm σ, lc]` with `σ = (d, π)`: the values `[tmJDsVal d, encPerm π]`
  (`tmJH_dec_spec`). The point `i + q c` of `σ` is `π i + q (d_i⁻¹ c)`, so `d_i⁻¹ c` is a
  quotient by `q` and `π i` a remainder.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

variable {m q : ℕ}

/-! ### The constant pair `(h; 1)` -/

/-- On `[encPerm h, lc]`: invert `h`, repeat `h⁻¹` `q` times, and build the pair. -/
def tmJHCstF (iv rep pr : ℕ) : Expr :=
  .letE (.call iv (arg 0))
    (.call pr (mk4 (.call rep (mk2 (.get (arg 1) (.nat 2)) (.var 1)))
      (.get (arg 1) (.nat 1)) (.get (arg 1) (.nat 2)) (.get (arg 1) (.nat 3))))

/-- The cost of `tmJHCstF`, in `V = (m + 1) (q + 1)`. -/
def tmJHCstK (V : ℕ) : ℕ := 10 ^ 16 * V ^ 8

theorem tmJH_dsVal_const (h : Perm (Fin m)) :
    tmJDsVal (fun _ => h : Fin q → Perm (Fin m)) = .list (List.replicate q (encPerm h⁻¹)) := by
  simp [tmJDsVal, List.map_const']

theorem tmJH_cst_spec {P : Program} {f iv rep pr prg prt prte : ℕ}
    (hf : P.funs[f]? = some (tmJHCstF iv rep pr)) (hiv : P.HasAt iv (invFuns iv))
    (hrep : P.HasAt rep (replicateFuns rep)) (hpr : TmJPairAt P pr prg prt prte)
    (h : Perm (Fin m)) :
    FunDet P f (.list [encPerm h, tmJLocCtx m q])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP ((fun _ => h : Fin q → Perm (Fin m)), (1 : Perm (Fin q))))))
      (tmJHCstK ((m + 1) * (q + 1))) := by
  refine FunDet.intro hf ?_
  unfold tmJHCstF
  have c1 := Det.call (Det.arg' (P := P) (vs := [encPerm h, tmJLocCtx m q]) (rest := []) (j := 0)
    (v := encPerm h) rfl) (inv_spec hiv h)
  set env := [Val.list [encPerm h, tmJLocCtx m q], encPerm h⁻¹] with henv
  have u1 := Det.arg' (P := P) (vs := [encPerm h, tmJLocCtx m q]) (rest := [encPerm h⁻¹]) (j := 1)
    (v := tmJLocCtx m q) rfl
  have g1 := Det.get' u1 (Det.nat 1) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := encPerm (1 : Perm (Fin q))) rfl
  have g2 := Det.get' u1 (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have g3 := Det.get' u1 (Det.nat 3) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat m) rfl
  have v1 := Det.var' (P := P) (env := env) (i := 1) (v := encPerm h⁻¹) rfl
  have hR : FunDet P rep (.list [.nat q, encPerm h⁻¹]) (.list (List.replicate q (encPerm h⁻¹)))
      (loopModK * (q + 1) * ((Val.list [.nat q, encPerm h⁻¹]).wt + q +
        (Val.list (List.replicate q (encPerm h⁻¹))).wt + 1)) :=
    (replicate_spec hrep q (encPerm h⁻¹)).mono fun w c hw => ⟨hw.1, by rw [hw.1] at hw; exact hw.2⟩
  have c2 := Det.call (Det.mk2 g2 v1) hR
  rw [← tmJH_dsVal_const (q := q) h] at c2
  have c3 := Det.call (Det.mk4 c2 g1 g2 g3)
    (tmJ_pair_spec hpr (fun _ => h : Fin q → Perm (Fin m)) 1)
  refine (Det.letE c1 c3).mono ?_
  -- the cost
  generalize hV : (m + 1) * (q + 1) = V at *
  have hm1 : m + 1 ≤ V := by rw [← hV]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ V := by rw [← hV]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hV1 : 1 ≤ V := by omega
  have hV2 : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) _
  have hV28 : V ^ 2 ≤ V ^ 8 := Nat.pow_le_pow_right hV1 (by norm_num)
  have hV48 : V ^ 4 ≤ V ^ 8 := Nat.pow_le_pow_right hV1 (by norm_num)
  have hV38 : V ^ 3 ≤ V ^ 8 := Nat.pow_le_pow_right hV1 (by norm_num)
  have hm2 : (m + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hm1 2
  have hm4 : (m + 1) ^ 4 ≤ V ^ 4 := Nat.pow_le_pow_left hm1 4
  have hq2 : (q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hq1 2
  have hmq : m * q + 1 ≤ V := by rw [← hV]; nlinarith
  have hmq2 : (m * q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hmq 2
  have wds : (tmJDsVal (fun _ => h : Fin q → Perm (Fin m))).wt ≤ 9 * V ^ 2 := by
    have h1 := wt_tmJDsVal_le (fun _ => h : Fin q → Perm (Fin m))
    have : (q + 1) * (m + 1) ^ 2 ≤ V ^ 2 := by
      have e : V ^ 2 = (q + 1) ^ 2 * (m + 1) ^ 2 := by rw [← hV]; ring
      rw [e]
      exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
    have h9 : 9 * (q + 1) * (m + 1) ^ 2 = 9 * ((q + 1) * (m + 1) ^ 2) := by ring
    omega
  have wds' : (Val.list (List.replicate q (encPerm h⁻¹))).wt ≤ 9 * V ^ 2 := by
    rw [← tmJH_dsVal_const]; exact wds
  have wc := wt_tmJLocCtx_le m q
  rw [hV] at wc
  have wh := wt_encPerm_le h
  have whi := wt_encPerm_le h⁻¹
  have w1q := wt_encPerm_le (1 : Perm (Fin q))
  have wq := wt_nat_le q
  have wm := wt_nat_le m
  have win := wt_list2_le (encPerm h) (tmJLocCtx m q)
  have wr2 := wt_list2_le (.nat q) (encPerm h⁻¹)
  have wb4 := wt_list4_le (tmJDsVal (fun _ => h : Fin q → Perm (Fin m)))
    (encPerm (1 : Perm (Fin q))) (.nat q) (.nat m)
  have wout := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJP ((fun _ => h : Fin q → Perm (Fin m)), (1 : Perm (Fin q)))))
  have hX : (Val.list [tmJDsVal (fun _ => h : Fin q → Perm (Fin m)),
      encPerm (1 : Perm (Fin q)), .nat q, .nat m]).wt + m * q + 1 ≤ 50 * V ^ 2 := by omega
  have hP : tmJPairK ((Val.list [tmJDsVal (fun _ => h : Fin q → Perm (Fin m)),
      encPerm (1 : Perm (Fin q)), .nat q, .nat m]).wt + m * q) ≤ 10 ^ 6 * (50 * V ^ 2) ^ 4 := by
    unfold tmJPairK
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX 4)
  have e1 : 10 ^ 6 * (50 * V ^ 2) ^ 4 = 6250000000000 * V ^ 8 := by ring
  have hRc : loopModK * (q + 1) * ((Val.list [.nat q, encPerm h⁻¹]).wt + q +
      (tmJDsVal (fun _ => h : Fin q → Perm (Fin m))).wt + 1) ≤ 1000 * V * (40 * V ^ 2) := by
    unfold loopModK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hq1) (by omega)
  have e2 : 1000 * V * (40 * V ^ 2) = 40000 * V ^ 3 := by ring
  have hI : invK * (m + 1) ^ 4 ≤ 100000 * V ^ 4 := by unfold invK; omega
  show _ ≤ 10 ^ 16 * V ^ 8
  omega

/-! ### Reading a pair off `Fin (m q)` -/

/-- One coordinate: on `[[σ, q, i], c]`, the number `σ (i + q c) / q`. -/
def tmJHDecEF : Expr :=
  .arith .div (.get (.get (arg 0) (.nat 0))
      (.arith .add (.get (arg 0) (.nat 2)) (.arith .mul (.get (arg 0) (.nat 1)) (arg 1))))
    (.get (arg 0) (.nat 1))

/-- One row: on `[[σ, q, ids_m], i]`, tabulate `tmJHDecEF` over `c < m`. -/
def tmJHDecRF (tbE : ℕ) : Expr :=
  .call tbE (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))
    (.get (arg 0) (.nat 2)))

/-- The top: on `[[σ, q], i]`, the number `σ i % q`. -/
def tmJHDecPF : Expr :=
  .arith .mod (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1))

/-- On `[encPerm σ, lc]`: `[ds, π]`, the rows tabulated over `i < q` and the top. -/
def tmJHDecF (rg tbR tbP : ℕ) : Expr :=
  mk2 (.call tbR (mk2 (mk3 (arg 0) (.get (arg 1) (.nat 2)) (.call rg (.get (arg 1) (.nat 3))))
      (.call rg (.get (arg 1) (.nat 2)))))
    (.call tbP (mk2 (mk2 (arg 0) (.get (arg 1) (.nat 2))) (.call rg (.get (arg 1) (.nat 2)))))


theorem tmJH_encPerm_get? {n : ℕ} (σ : Perm (Fin n)) (k : ℕ) (hk : k < n) :
    ((List.finRange n).map fun i => Val.nat (σ i))[k]? = some (.nat (σ ⟨k, hk⟩)) := by
  simp [hk]

theorem tmJH_decE_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJHDecEF)
    (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)) (i : Fin q) (c : Fin m) :
    FunDet P f (.list [.list [encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP (d, π))), .nat q, .nat i], .nat c])
      (.nat ((d i)⁻¹ c)) (100 * (100 * ((m + 1) * (q + 1)) ^ 2)) := by
  refine FunDet.intro hf ?_
  set σ := toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)) with hσ
  set ctx := Val.list [encPerm σ, .nat q, .nat i] with hctx
  have hidx : (i : ℕ) + q * c < m * q := by
    have := (finProdFinEquiv (c, i) : Fin (m * q)).2
    rwa [finProdFinEquiv_apply_val] at this
  have hfe : (⟨(i : ℕ) + q * c, hidx⟩ : Fin (m * q)) = finProdFinEquiv (c, i) := by
    ext; simp [finProdFinEquiv_apply_val]
  have d0 := Det.arg' (P := P) (vs := [ctx, .nat c]) (rest := []) (j := 0) (v := ctx) rfl
  have d1 := Det.arg' (P := P) (vs := [ctx, .nat c]) (rest := []) (j := 1) (v := .nat c) rfl
  have ds := Det.get' d0 (Det.nat 0) (vs := [encPerm σ, .nat q, .nat i]) (v := encPerm σ) rfl
  have dq := Det.get' d0 (Det.nat 1) (vs := [encPerm σ, .nat q, .nat i]) (v := .nat q) rfl
  have di := Det.get' d0 (Det.nat 2) (vs := [encPerm σ, .nat q, .nat i]) (v := .nat i) rfl
  have dmul := Det.arith' (op := .mul) dq d1 (z := q * c) rfl
  have dadd := Det.arith' (op := .add) di dmul (z := i + q * c) rfl
  have dent := Det.get' ds dadd (tmJH_encPerm_get? σ _ hidx)
  have ddiv := Det.arith' (op := .div) dent dq (z := (d i)⁻¹ c) (by
    show ((σ ⟨_, hidx⟩ : Fin (m * q)) : ℕ) / q = _
    rw [hfe, hσ, tmJH_dec_div])
  refine ddiv.mono ?_
  -- the cost
  generalize hV : (m + 1) * (q + 1) = V at *
  have hmq : m * q + 1 ≤ V := by rw [← hV]; nlinarith
  have hmq2 : (m * q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hmq 2
  have hV2 : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) _
  have wσ := wt_encPerm_le σ
  have wq := wt_nat_le q
  have wi := wt_nat_le i
  have wc := wt_nat_le c
  have hi := i.2
  have hc := c.2
  have w3 := wt_list3_le (encPerm σ) (.nat q) (.nat i)
  have w2 := wt_list2_le ctx (.nat c)
  have we := wt_nat_le (σ ⟨_, hidx⟩ : ℕ)
  have he := (σ ⟨_, hidx⟩).2
  have hdc := ((d i)⁻¹ c).2
  have hqc : q * c ≤ m * q := by nlinarith
  have hqV : q ≤ V := by rw [← hV]; nlinarith
  have hmV : m ≤ V := by rw [← hV]; nlinarith
  have r3 : (Val.list [encPerm σ, .nat q, .nat i]).wt = ctx.wt := rfl
  omega

theorem tmJH_decR_spec {P : Program} {f tbE e : ℕ} (hf : P.funs[f]? = some (tmJHDecRF tbE))
    (htb : P.HasAt tbE (mapFuns tbE e)) (he : P.funs[e]? = some tmJHDecEF)
    (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)) (i : Fin q) :
    FunDet P f (.list [.list [encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP (d, π))), .nat q, encFun fun c : Fin m => (c : ℕ)], .nat i])
      (encPerm (d i)⁻¹) (10 ^ 7 * ((m + 1) * (q + 1)) ^ 3) := by
  refine FunDet.intro hf ?_
  set σ := toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)) with hσ
  set ctx := Val.list [encPerm σ, .nat q, encFun fun c : Fin m => (c : ℕ)] with hctx
  have d0 := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 0) (v := ctx) rfl
  have d1 := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 1) (v := .nat i) rfl
  have ds := Det.get' d0 (Det.nat 0) (vs := [encPerm σ, .nat q, encFun fun c : Fin m => (c : ℕ)])
    (v := encPerm σ) rfl
  have dq := Det.get' d0 (Det.nat 1) (vs := [encPerm σ, .nat q, encFun fun c : Fin m => (c : ℕ)])
    (v := .nat q) rfl
  have dids := Det.get' d0 (Det.nat 2)
    (vs := [encPerm σ, .nat q, encFun fun c : Fin m => (c : ℕ)])
    (v := encFun fun c : Fin m => (c : ℕ)) rfl
  have hT := tabulate_spec htb (c := .list [encPerm σ, .nat q, .nat i])
    (F := fun c : Fin m => Val.nat ((d i)⁻¹ c)) (fun c => tmJH_decE_spec he d π i c)
  have c1 := Det.call (Det.mk2 (Det.mk3 ds dq d1) dids) hT
  have hval : Val.list ((List.finRange m).map fun c => Val.nat ((d i)⁻¹ c)) = encPerm (d i)⁻¹ :=
    rfl
  rw [hval] at c1
  refine c1.mono ?_
  -- the cost
  generalize hV : (m + 1) * (q + 1) = V at *
  have hm1 : m + 1 ≤ V := by rw [← hV]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hmq : m * q + 1 ≤ V := by rw [← hV]; nlinarith
  have hmq2 : (m * q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hmq 2
  have hm2 : (m + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hm1 2
  have hV1 : 1 ≤ V := by omega
  have hV2 : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) _
  have hV3 : V ^ 2 ≤ V ^ 3 := Nat.pow_le_pow_right hV1 (by norm_num)
  have wσ := wt_encPerm_le σ
  have wq := wt_nat_le q
  have wi := wt_nat_le i
  have hi := i.2
  have hqV : q ≤ V := by rw [← hV]; nlinarith
  have wids := wt_ids_le m
  have wout := wt_encPerm_le (d i)⁻¹
  have w3 := wt_list3_le (encPerm σ) (.nat q) (encFun fun c : Fin m => (c : ℕ))
  have w3' := wt_list3_le (encPerm σ) (.nat q) (.nat i)
  have w2 := wt_list2_le ctx (.nat i)
  have w2' := wt_list2_le (.list [encPerm σ, .nat q, .nat i]) (encFun fun c : Fin m => (c : ℕ))
  have l1 : m * (100 * (100 * V ^ 2)) ≤ V * (10000 * V ^ 2) :=
    Nat.mul_le_mul (by omega) (le_of_eq (by ring))
  have l2 : mapK * (m + 1) * ((Val.list [Val.list [encPerm σ, .nat q, .nat i],
      encFun fun c : Fin m => (c : ℕ)]).wt + (encPerm (d i)⁻¹).wt + 1) ≤
      1000 * V * (200 * V ^ 2) := by
    unfold mapK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hm1) (by omega)
  have e1 : V * (10000 * V ^ 2) = 10000 * V ^ 3 := by ring
  have e2 : 1000 * V * (200 * V ^ 2) = 200000 * V ^ 3 := by ring
  have r3 : (Val.list [encPerm σ, .nat q, encFun fun c : Fin m => (c : ℕ)]).wt = ctx.wt := rfl
  have r4 : (Val.list ((List.finRange m).map fun c => Val.nat ((d i)⁻¹ c))).wt =
    (encPerm (d i)⁻¹).wt := rfl
  omega

theorem tmJH_decP_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJHDecPF) (hm : 0 < m)
    (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)) (i : Fin q) :
    FunDet P f (.list [.list [encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP (d, π))), .nat q], .nat i])
      (.nat (π i)) (100 * (100 * ((m + 1) * (q + 1)) ^ 2)) := by
  refine FunDet.intro hf ?_
  set σ := toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)) with hσ
  set ctx := Val.list [encPerm σ, .nat q] with hctx
  have hidx : (i : ℕ) < m * q := by
    have := (finProdFinEquiv ((⟨0, hm⟩ : Fin m), i) : Fin (m * q)).2
    rwa [finProdFinEquiv_apply_val, mul_zero, add_zero] at this
  have hfe : (⟨(i : ℕ), hidx⟩ : Fin (m * q)) = finProdFinEquiv ((⟨0, hm⟩ : Fin m), i) := by
    ext; simp [finProdFinEquiv_apply_val]
  have d0 := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 0) (v := ctx) rfl
  have d1 := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 1) (v := .nat i) rfl
  have ds := Det.get' d0 (Det.nat 0) (vs := [encPerm σ, .nat q]) (v := encPerm σ) rfl
  have dq := Det.get' d0 (Det.nat 1) (vs := [encPerm σ, .nat q]) (v := .nat q) rfl
  have dent := Det.get' ds d1 (tmJH_encPerm_get? σ _ hidx)
  have dmod := Det.arith' (op := .mod) dent dq (z := π i) (by
    show ((σ ⟨_, hidx⟩ : Fin (m * q)) : ℕ) % q = _
    rw [hfe, hσ, tmJH_dec_mod])
  refine dmod.mono ?_
  generalize hV : (m + 1) * (q + 1) = V at *
  have hmq : m * q + 1 ≤ V := by rw [← hV]; nlinarith
  have hmq2 : (m * q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hmq 2
  have hV2 : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) _
  have wσ := wt_encPerm_le σ
  have wq := wt_nat_le q
  have wi := wt_nat_le i
  have hi := i.2
  have w2 := wt_list2_le (encPerm σ) (.nat q)
  have w2' := wt_list2_le ctx (.nat i)
  have we := wt_nat_le (σ ⟨_, hidx⟩ : ℕ)
  have he := (σ ⟨_, hidx⟩).2
  have hpi := (π i).2
  have hqV : q ≤ V := by rw [← hV]; nlinarith
  have r : (Val.list [encPerm σ, .nat q]).wt = ctx.wt := rfl
  omega

/-- The cost of `tmJHDecF`, in `V = (m + 1) (q + 1)`. -/
def tmJHDecK (V : ℕ) : ℕ := 10 ^ 10 * V ^ 4

/-- **Reading a pair.** On `[encPerm σ, lc]` with `σ = (d, π)` on `Fin (m q)` and `m > 0`, the
result is `[tmJDsVal d, encPerm π]`. -/
theorem tmJH_dec_spec {P : Program} {f rg tbR rE tbE e tbP pE : ℕ}
    (hf : P.funs[f]? = some (tmJHDecF rg tbR tbP)) (hrg : P.HasAt rg (rangeFuns rg))
    (htbR : P.HasAt tbR (mapFuns tbR rE)) (hrE : P.funs[rE]? = some (tmJHDecRF tbE))
    (htbE : P.HasAt tbE (mapFuns tbE e)) (he : P.funs[e]? = some tmJHDecEF)
    (htbP : P.HasAt tbP (mapFuns tbP pE)) (hpE : P.funs[pE]? = some tmJHDecPF) (hm : 0 < m)
    (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)) :
    FunDet P f (.list [encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP (d, π))), tmJLocCtx m q])
      (.list [tmJDsVal d, encPerm π]) (tmJHDecK ((m + 1) * (q + 1))) := by
  refine FunDet.intro hf ?_
  unfold tmJHDecF
  set σ := toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)) with hσ
  have d0 := Det.arg' (P := P) (vs := [encPerm σ, tmJLocCtx m q]) (rest := []) (j := 0)
    (v := encPerm σ) rfl
  have d1 := Det.arg' (P := P) (vs := [encPerm σ, tmJLocCtx m q]) (rest := []) (j := 1)
    (v := tmJLocCtx m q) rfl
  have g2 := Det.get' d1 (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have g3 := Det.get' d1 (Det.nat 3) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat m) rfl
  have rq := Det.call g2 (tmJ_range_det hrg q)
  have rm := Det.call g3 (tmJ_range_det hrg m)
  have hT := tabulate_spec htbR (c := .list [encPerm σ, .nat q, encFun fun c : Fin m => (c : ℕ)])
    (F := fun i : Fin q => encPerm (d i)⁻¹) (fun i => tmJH_decR_spec hrE htbE he d π i)
  have c1 := Det.call (Det.mk2 (Det.mk3 d0 g2 rm) rq) hT
  have hP := tabulate_spec htbP (c := .list [encPerm σ, .nat q])
    (F := fun i : Fin q => Val.nat (π i)) (fun i => tmJH_decP_spec hpE hm d π i)
  have c2 := Det.call (Det.mk2 (Det.mk2 d0 g2) rq) hP
  have e1 : Val.list ((List.finRange q).map fun i => encPerm (d i)⁻¹) = tmJDsVal d := rfl
  have e2 : Val.list ((List.finRange q).map fun i => Val.nat (π i)) = encPerm π := rfl
  rw [e1] at c1
  rw [e2] at c2
  refine (Det.mk2 c1 c2).mono ?_
  -- the cost
  generalize hV : (m + 1) * (q + 1) = V at *
  have hm1 : m + 1 ≤ V := by rw [← hV]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ V := by rw [← hV]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hmq : m * q + 1 ≤ V := by rw [← hV]; nlinarith
  have hmq2 : (m * q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hmq 2
  have hm2 : (m + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hm1 2
  have hq2 : (q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hq1 2
  have hm3 : (m + 1) ^ 3 ≤ V ^ 3 := Nat.pow_le_pow_left hm1 3
  have hq3 : (q + 1) ^ 3 ≤ V ^ 3 := Nat.pow_le_pow_left hq1 3
  have hV1 : 1 ≤ V := by omega
  have hV2 : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) _
  have hV3 : V ^ 2 ≤ V ^ 3 := Nat.pow_le_pow_right hV1 (by norm_num)
  have hV4 : V ^ 3 ≤ V ^ 4 := Nat.pow_le_pow_right hV1 (by norm_num)
  have wσ := wt_encPerm_le σ
  have wq := wt_nat_le q
  have wm := wt_nat_le m
  have wc := wt_tmJLocCtx_le m q
  rw [hV] at wc
  have widq := wt_ids_le q
  have widm := wt_ids_le m
  have wds : (tmJDsVal d).wt ≤ 9 * V ^ 2 := by
    have h1 := wt_tmJDsVal_le d
    have : (q + 1) * (m + 1) ^ 2 ≤ V ^ 2 := by
      have e : V ^ 2 = (q + 1) ^ 2 * (m + 1) ^ 2 := by rw [← hV]; ring
      rw [e]
      exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
    have h9 : 9 * (q + 1) * (m + 1) ^ 2 = 9 * ((q + 1) * (m + 1) ^ 2) := by ring
    omega
  have wπ := wt_encPerm_le π
  have win := wt_list2_le (encPerm σ) (tmJLocCtx m q)
  have w3 := wt_list3_le (encPerm σ) (.nat q) (encFun fun c : Fin m => (c : ℕ))
  have w3' := wt_list2_le (Val.list [encPerm σ, .nat q, encFun fun c : Fin m => (c : ℕ)])
    (encFun fun i : Fin q => (i : ℕ))
  have w2 := wt_list2_le (encPerm σ) (.nat q)
  have w2' := wt_list2_le (Val.list [encPerm σ, .nat q]) (encFun fun i : Fin q => (i : ℕ))
  have wout := wt_list2_le (tmJDsVal d) (encPerm π)
  have l1 : q * (10 ^ 7 * V ^ 3) ≤ V * (10 ^ 7 * V ^ 3) := Nat.mul_le_mul (by omega) le_rfl
  have l1' : q * (100 * (100 * V ^ 2)) ≤ V * (10000 * V ^ 2) :=
    Nat.mul_le_mul (by omega) (le_of_eq (by ring))
  have l2 : mapK * (q + 1) * ((Val.list [Val.list [encPerm σ, .nat q,
      encFun fun c : Fin m => (c : ℕ)], encFun fun i : Fin q => (i : ℕ)]).wt +
      (tmJDsVal d).wt + 1) ≤ 1000 * V * (200 * V ^ 2) := by
    unfold mapK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hq1) (by omega)
  have l3 : mapK * (q + 1) * ((Val.list [Val.list [encPerm σ, .nat q],
      encFun fun i : Fin q => (i : ℕ)]).wt + (encPerm π).wt + 1) ≤ 1000 * V * (200 * V ^ 2) := by
    unfold mapK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hq1) (by omega)
  have e1 : V * (10 ^ 7 * V ^ 3) = 10 ^ 7 * V ^ 4 := by ring
  have e2 : V * (10000 * V ^ 2) = 10000 * V ^ 3 := by ring
  have e3 : 1000 * V * (200 * V ^ 2) = 200000 * V ^ 3 := by ring
  have hrq : 10000 * (q + 1) ^ 3 ≤ 10000 * V ^ 3 := Nat.mul_le_mul_left _ hq3
  have hrm : 10000 * (m + 1) ^ 3 ≤ 10000 * V ^ 3 := Nat.mul_le_mul_left _ hm3
  show _ ≤ 10 ^ 10 * V ^ 4
  omega

end GI.Impl
