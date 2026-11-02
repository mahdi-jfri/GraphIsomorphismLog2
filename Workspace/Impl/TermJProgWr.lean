import Workspace.Impl.TermJWrMath
import Workspace.Impl.TermJProgPair

/-!
# Generators of `N ≀ Sym(q)` on `Fin (m q)` (program)

On `[σN, q, m]` (`σN` a list of permutations of `Fin m`), `tmJWrF` returns the generators of
`tmJ_wreath_gens2` written on `Fin (m q)`: `(g⁻¹ at 0; 1)` for `g ∈ σN`, then `(1; rotation)`
and `(1; (0 1))` (`tmJWrList`). Pieces:

* `tmJDsEF`, `tmJDsF`: the coordinates `[g, 1, …, 1]` of `(g⁻¹ at 0; 1)` (`tmJDsVal`);
* `tmJRotEF`, `tmJSwEF`: the entries `(i + 1) % q` and `(0 1) i` of the two top permutations;
* `tmJLocF`: one local generator, by the pair program `tmJPairF`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

/-! ### Weights -/

/-- A list whose entries weigh at most `E`. -/
theorem tmJ_wt_list_le {vs : List Val} {E : ℕ} (h : ∀ v ∈ vs, v.wt ≤ E) :
    (Val.list vs).wt ≤ vs.length * (2 * E + 1) + 4 := by
  have h1 := wt_list_le vs
  have h2 : (vs.map Val.wt).sum ≤ vs.length * E := by
    have := List.sum_le_card_nsmul (vs.map Val.wt) E (by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      exact h v hv)
    simpa using this
  have : vs.length * (2 * E + 1) = 2 * (vs.length * E) + vs.length := by ring
  omega

/-- The coordinates of a pair weigh at most `9 (q + 1) (m + 1)²`. -/
theorem wt_tmJDsVal_le {m q : ℕ} (d : Fin q → Perm (Fin m)) :
    (tmJDsVal d).wt ≤ 9 * (q + 1) * (m + 1) ^ 2 := by
  have := tmJ_wt_list_le (vs := (List.finRange q).map fun i => encPerm (d i)⁻¹)
    (E := 4 * (m + 1) ^ 2) (by
      intro v hv
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
      exact wt_encPerm_le _)
  simp only [List.length_map, List.length_finRange] at this
  have h1 : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold tmJDsVal
  nlinarith

/-- `if` on a known number, with sums in place of the maxima of `Det.ite'`. -/
theorem tmJ_det_ite {P : Program} {env : List Val} {c t e : Expr} {x : ℕ} {v1 v0 : Val}
    {cc ct ce : ℕ} (hc : Det P env c (.nat x) cc) (ht : Det P env t v1 ct)
    (he : Det P env e v0 ce) :
    Det P env (.ite c t e) (if x = 0 then v0 else v1) (cc + ct + ce + v1.wt + v0.wt + 1) :=
  (Det.ite' hc ht he).mono (by
    have := max_le (Nat.le_add_right ct ce) (Nat.le_add_left ce ct)
    have := max_le (Nat.le_add_right v1.wt v0.wt) (Nat.le_add_left v0.wt v1.wt)
    omega)

/-! ### The coordinates of a local generator at `0` -/

/-- On `[[g, one], i]`: `g` if `i = 0`, else `one`. -/
def tmJDsEF : Expr :=
  .ite (.arith .eq (arg 1) (.nat 0)) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))

/-- The coordinate `i` of `(g⁻¹ at 0; 1)`, stored inverted. -/
theorem tmJ_dsE_val {m q : ℕ} (hq : 0 < q) (g : Perm (Fin m)) (i : Fin q) :
    encPerm ((Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m)) i)⁻¹ =
      if (if (i : ℕ) = 0 then 1 else 0) = 0 then encPerm (1 : Perm (Fin m)) else encPerm g := by
  by_cases hi : (i : ℕ) = 0
  · have : i = ⟨0, hq⟩ := Fin.ext hi
    subst this
    simp
  · have : i ≠ ⟨0, hq⟩ := fun h => hi (by rw [h])
    simp [hi, Pi.mulSingle_eq_of_ne this]

theorem tmJ_dsE_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJDsEF) {m q : ℕ}
    (hq : 0 < q) (g : Perm (Fin m)) (i : Fin q) :
    FunDet P f (.list [.list [encPerm g, encPerm (1 : Perm (Fin m))], .nat i])
      (encPerm ((Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m)) i)⁻¹)
      (1000 * ((m + 1) ^ 2 + q + 1)) := by
  refine FunDet.intro hf ?_
  set c := Val.list [encPerm g, encPerm (1 : Perm (Fin m))] with hc
  have d0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 0) (v := c) rfl
  have d1 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 1) (v := .nat i) rfl
  have deq := Det.arith (op := .eq) d1 (Det.nat 0)
  have dg := Det.get' d0 (Det.nat 0) (vs := [encPerm g, encPerm 1]) (v := encPerm g) rfl
  have d1' := Det.get' d0 (Det.nat 1) (vs := [encPerm g, encPerm 1]) (v := encPerm 1) rfl
  have dite := tmJ_det_ite deq dg d1'
  rw [show Machine.BinOp.eval .eq (i : ℕ) 0 = if (i : ℕ) = 0 then 1 else 0 from rfl,
    ← tmJ_dsE_val hq g i] at dite
  refine dite.mono ?_
  have w1 := wt_encPerm_le g
  have w2 := wt_encPerm_le (1 : Perm (Fin m))
  have wc := wt_list2_le (encPerm g) (encPerm (1 : Perm (Fin m)))
  have wa := wt_list2_le c (Val.nat i)
  have wi := wt_nat_le i
  have hi := i.2
  have wb : (Val.nat (if (i : ℕ) = 0 then 1 else 0)).wt ≤ 3 := by
    split_ifs <;> decide
  have wr : ∀ v ∈ [encPerm g, encPerm (1 : Perm (Fin m))], v.wt ≤ 4 * (m + 1) ^ 2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl) <;> assumption
  have wmax : max (encPerm g).wt (encPerm (1 : Perm (Fin m))).wt ≤ 4 * (m + 1) ^ 2 := by omega
  have wd := wt_encPerm_le ((Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m)) i)⁻¹
  have rc : c.wt = (Val.list [encPerm g, encPerm (1 : Perm (Fin m))]).wt := rfl
  have := wt_nat_le 1
  omega

/-- On `[g, one, q]`: the coordinates of `(g⁻¹ at 0; 1)`. -/
def tmJDsF (rg tb : ℕ) : Expr := .call tb (mk2 (mk2 (arg 0) (arg 1)) (.call rg (arg 2)))

/-- The range `0, …, n - 1` as a call, with its value `encFun id`. -/
theorem tmJ_range_det {P : Program} {rg : ℕ} (hrg : P.HasAt rg (rangeFuns rg)) (n : ℕ) :
    FunDet P rg (.nat n) (encFun fun i : Fin n => (i : ℕ)) (10000 * (n + 1) ^ 3) := by
  rw [encFun_id]
  refine FunAll.mono (range_spec hrg n) fun w c h => ?_
  obtain ⟨rfl, h2⟩ := h
  refine ⟨rfl, h2.trans ?_⟩
  have w1 := wt_nat_le n
  have w2 : (natList (List.range n)).wt ≤ 4 * (n + 1) ^ 2 := by
    rw [← encFun_id]; exact wt_ids_le n
  have : (Val.nat n).wt + n + (natList (List.range n)).wt + 1 ≤ 10 * (n + 1) ^ 2 := by
    nlinarith
  calc loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1)
      ≤ 1000 * (n + 1) * (10 * (n + 1) ^ 2) := by
        unfold loopModK; exact Nat.mul_le_mul_left _ this
    _ = 10000 * (n + 1) ^ 3 := by ring

/-- The identity as the range. -/
theorem tmJ_encFun_id_eq (n : ℕ) : encFun (fun i : Fin n => (i : ℕ)) = encPerm (1 : Perm (Fin n)) :=
  rfl

/-- The cost of the coordinates of a local generator. -/
def tmJDsK (W : ℕ) : ℕ := 10 ^ 7 * W ^ 4

theorem tmJ_ds_spec {P : Program} {f rg tb tbe : ℕ} (hf : P.funs[f]? = some (tmJDsF rg tb))
    (hrg : P.HasAt rg (rangeFuns rg)) (htb : P.HasAt tb (mapFuns tb tbe))
    (htbe : P.funs[tbe]? = some tmJDsEF) {m q : ℕ} (hq : 0 < q) (g : Perm (Fin m)) :
    FunDet P f (.list [encPerm g, encPerm (1 : Perm (Fin m)), .nat q])
      (tmJDsVal (Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m)))
      (tmJDsK ((m + 1) * (q + 1))) := by
  refine FunDet.intro hf ?_
  unfold tmJDsF
  set a := Val.list [encPerm g, encPerm (1 : Perm (Fin m)), .nat q] with ha
  set c := Val.list [encPerm g, encPerm (1 : Perm (Fin m))] with hc
  have d0 := Det.arg' (P := P) (vs := [encPerm g, encPerm (1 : Perm (Fin m)), .nat q])
    (rest := []) (j := 0) (v := encPerm g) rfl
  have d1 := Det.arg' (P := P) (vs := [encPerm g, encPerm (1 : Perm (Fin m)), .nat q])
    (rest := []) (j := 1) (v := encPerm 1) rfl
  have d2 := Det.arg' (P := P) (vs := [encPerm g, encPerm (1 : Perm (Fin m)), .nat q])
    (rest := []) (j := 2) (v := .nat q) rfl
  have dr := Det.call d2 (tmJ_range_det hrg q)
  have hT := tabulate_spec htb (c := c) (F := fun i : Fin q =>
    encPerm ((Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m)) i)⁻¹)
    (fun i => tmJ_dsE_spec htbe hq g i)
  have dall := Det.call (Det.mk2 (Det.mk2 d0 d1) dr) hT
  refine dall.mono ?_
  -- the cost
  set W := (m + 1) * (q + 1) with hW
  have hm1 : m + 1 ≤ W := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ W := Nat.le_mul_of_pos_left _ (by omega)
  have hW1 : 1 ≤ W := by omega
  have hW2 : W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW3 : W ^ 2 ≤ W ^ 3 := Nat.pow_le_pow_right hW1 (by norm_num)
  have hm2 : (m + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hm1 2
  have hq2 : (q + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hq1 2
  have hq3 : (q + 1) ^ 3 ≤ W ^ 3 := Nat.pow_le_pow_left hq1 3
  have w1 := wt_encPerm_le g
  have w2 := wt_encPerm_le (1 : Perm (Fin m))
  have wq := wt_nat_le q
  have wa := wt_list3_le (encPerm g) (encPerm (1 : Perm (Fin m))) (.nat q)
  have wc := wt_list2_le (encPerm g) (encPerm (1 : Perm (Fin m)))
  have wid := wt_ids_le q
  have wcr := wt_list2_le c (encFun fun i : Fin q => (i : ℕ))
  have wds := wt_tmJDsVal_le (Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m))
  have hds : (tmJDsVal (Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m))).wt ≤ 9 * W ^ 3 := by
    have : (q + 1) * (m + 1) ^ 2 ≤ W ^ 3 := by
      calc (q + 1) * (m + 1) ^ 2 ≤ W * W ^ 2 := Nat.mul_le_mul hq1 hm2
        _ = W ^ 3 := by ring
    nlinarith
  have e1 : Val.list ((List.finRange q).map fun i : Fin q =>
      encPerm ((Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m)) i)⁻¹) =
      tmJDsVal (Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m)) := rfl
  rw [e1]
  have P1 : q * (1000 * ((m + 1) ^ 2 + q + 1)) ≤ 3000 * W ^ 3 := by
    calc q * (1000 * ((m + 1) ^ 2 + q + 1)) ≤ W * (1000 * (3 * W ^ 2)) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 3000 * W ^ 3 := by ring
  have rc : c.wt = (Val.list [encPerm g, encPerm (1 : Perm (Fin m))]).wt := rfl
  have P2 : mapK * (q + 1) * ((Val.list [c, encFun fun i : Fin q => (i : ℕ)]).wt +
      (tmJDsVal (Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m))).wt + 1) ≤
      1000 * W * (100 * W ^ 3) := by
    unfold mapK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hq1) (by omega)
  have e2 : 1000 * W * (100 * W ^ 3) = 100000 * W ^ 4 := by ring
  have hW4 : W ^ 3 ≤ W ^ 4 := Nat.pow_le_pow_right hW1 (by norm_num)
  have r1 : (Val.list [encPerm g, encPerm (1 : Perm (Fin m))]).wt = c.wt := rfl
  have r2 : (Val.list [Val.list [encPerm g, encPerm (1 : Perm (Fin m))],
      encFun fun i : Fin q => (i : ℕ)]).wt = (Val.list [c, encFun fun i : Fin q => (i : ℕ)]).wt := rfl
  have r3 : (Val.list [encPerm g, encPerm (1 : Perm (Fin m)), Val.nat q]).wt = a.wt := rfl
  show _ ≤ 10 ^ 7 * W ^ 4
  omega

/-! ### The two top permutations -/

/-- On `[q, i]`: `(i + 1) % q`. -/
def tmJRotEF : Expr := .arith .mod (.arith .add (arg 1) (.nat 1)) (arg 0)

/-- On `[q, i]`: `1 - i` if `i < 2`, else `i`. -/
def tmJSwEF : Expr := .ite (.arith .lt (arg 1) (.nat 2)) (.arith .sub (.nat 1) (arg 1)) (arg 1)

theorem tmJ_finRotate_val {q : ℕ} (i : Fin q) : (finRotate q i : ℕ) = (i + 1) % q := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by have := i.2; omega⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one']
  simp [Nat.add_mod]

theorem tmJ_swap01_val {q : ℕ} (hq : 2 ≤ q) (i : Fin q) :
    (swap (⟨0, by omega⟩ : Fin q) ⟨1, by omega⟩ i : ℕ) = if (i : ℕ) < 2 then 1 - (i : ℕ) else i := by
  rw [swap_apply_def]
  split_ifs with h1 h2 h3 h4 <;> (simp_all [Fin.ext_iff]; try omega)

theorem tmJ_rotE_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJRotEF) {q : ℕ}
    (i : Fin q) : FunDet P f (.list [.nat q, .nat i]) (.nat (finRotate q i)) (100 * (q + 1)) := by
  refine FunDet.intro hf ?_
  have d0 := Det.arg' (P := P) (vs := [.nat q, .nat i]) (rest := []) (j := 0) (v := .nat q) rfl
  have d1 := Det.arg' (P := P) (vs := [.nat q, .nat i]) (rest := []) (j := 1) (v := .nat i) rfl
  have dadd := Det.arith' (op := .add) d1 (Det.nat 1) (z := i + 1) rfl
  have dmod := Det.arith' (op := .mod) dadd d0 (z := finRotate q i) (by
    rw [tmJ_finRotate_val]; rfl)
  refine dmod.mono ?_
  have wa := wt_list2_le (Val.nat q) (Val.nat i)
  have := wt_nat_le q
  have := wt_nat_le i
  have := i.2
  have := (finRotate q i).2
  omega

theorem tmJ_swE_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJSwEF) {q : ℕ}
    (hq : 2 ≤ q) (i : Fin q) :
    FunDet P f (.list [.nat q, .nat i]) (.nat (swap (⟨0, by omega⟩ : Fin q) ⟨1, by omega⟩ i))
      (100 * (q + 1)) := by
  refine FunDet.intro hf ?_
  have d1 := Det.arg' (P := P) (vs := [.nat q, .nat i]) (rest := []) (j := 1) (v := .nat i) rfl
  have dlt := Det.arith (op := .lt) d1 (Det.nat 2)
  have dsub := Det.arith' (op := .sub) (Det.nat 1) d1 (z := 1 - i) rfl
  have dite := tmJ_det_ite dlt dsub d1
  have hv : (if Machine.BinOp.eval .lt (i : ℕ) 2 = 0 then Val.nat i else Val.nat (1 - i)) =
      .nat (swap (⟨0, by omega⟩ : Fin q) ⟨1, by omega⟩ i) := by
    rw [tmJ_swap01_val hq]
    by_cases h : (i : ℕ) < 2 <;> simp [Machine.BinOp.eval, h]
  rw [hv] at dite
  refine dite.mono ?_
  have wa := wt_list2_le (Val.nat q) (Val.nat i)
  have := wt_nat_le q
  have := wt_nat_le i
  have := wt_nat_le (1 - i)
  have := wt_nat_le (swap (⟨0, by omega⟩ : Fin q) ⟨1, by omega⟩ i)
  have := (swap (⟨0, by omega⟩ : Fin q) ⟨1, by omega⟩ i).2
  have := i.2
  have : (Val.nat (Machine.BinOp.eval .lt (i : ℕ) 2)).wt ≤ 3 := by
    simp only [Machine.BinOp.eval]; split_ifs <;> decide
  omega

/-- A top permutation tabulated over `0, …, q - 1`. -/
theorem tmJ_top_spec {P : Program} {tb e : ℕ} (htb : P.HasAt tb (mapFuns tb e)) {q : ℕ}
    (π : Perm (Fin q)) (he : ∀ i : Fin q, FunDet P e (.list [.nat q, .nat i]) (.nat (π i))
      (100 * (q + 1))) :
    FunDet P tb (.list [.nat q, encFun fun i : Fin q => (i : ℕ)]) (encPerm π)
      (10 ^ 5 * (q + 1) ^ 3) := by
  have hT := tabulate_spec htb (c := .nat q) (F := fun i : Fin q => .nat (π i)) he
  refine hT.mono ?_
  have w1 := wt_list2_le (Val.nat q) (encFun fun i : Fin q => (i : ℕ))
  have w2 := wt_ids_le q
  have w3 := wt_encPerm_le π
  have w4 := wt_nat_le q
  have e1 : Val.list ((List.finRange q).map fun i : Fin q => Val.nat (π i)) = encPerm π := rfl
  rw [e1]
  have hq1 : 1 ≤ q + 1 := by omega
  have P1 : q * (100 * (q + 1)) ≤ 100 * (q + 1) ^ 2 := by
    calc q * (100 * (q + 1)) ≤ (q + 1) * (100 * (q + 1)) := Nat.mul_le_mul_right _ (by omega)
      _ = 100 * (q + 1) ^ 2 := by ring
  have P2 : mapK * (q + 1) * ((Val.list [.nat q, encFun fun i : Fin q => (i : ℕ)]).wt +
      (encPerm π).wt + 1) ≤ 1000 * (q + 1) * (30 * (q + 1) ^ 2) := by
    unfold mapK
    apply Nat.mul_le_mul_left
    nlinarith
  have e2 : 1000 * (q + 1) * (30 * (q + 1) ^ 2) = 30000 * (q + 1) ^ 3 := by ring
  have h23 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right hq1 (by norm_num)
  omega

/-! ### One local generator -/

/-- On `[[one_m, one_q, q, m], g]`: the local generator `(g⁻¹ at 0; 1)` on `Fin (m q)`. -/
def tmJLocF (ds pr : ℕ) : Expr :=
  .call pr (mk4 (.call ds (mk3 (arg 1) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 2))))
    (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 3)))

/-- The context of the local generators. -/
def tmJLocCtx (m q : ℕ) : Val :=
  .list [encPerm (1 : Perm (Fin m)), encPerm (1 : Perm (Fin q)), .nat q, .nat m]

theorem wt_tmJLocCtx_le (m q : ℕ) : (tmJLocCtx m q).wt ≤ 40 * ((m + 1) * (q + 1)) ^ 2 := by
  have h1 := wt_list4_le (encPerm (1 : Perm (Fin m))) (encPerm (1 : Perm (Fin q))) (.nat q) (.nat m)
  have := wt_encPerm_le (1 : Perm (Fin m))
  have := wt_encPerm_le (1 : Perm (Fin q))
  have := wt_nat_le q
  have := wt_nat_le m
  have hm : (m + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 :=
    Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by omega)) 2
  have hq : (q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 :=
    Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (by omega)) 2
  have : m + q + 2 ≤ (m + 1) ^ 2 + (q + 1) ^ 2 := by nlinarith
  have : 1 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  unfold tmJLocCtx
  omega

/-- The cost of one local generator. -/
def tmJLocK (W : ℕ) : ℕ := 10 ^ 14 * W ^ 8

/-- The local generator at `0`. -/
abbrev tmJLoc0 {m q : ℕ} (hq : 0 < q) (g : Perm (Fin m)) : Perm (Fin m × Fin q) :=
  tmJLoc (⟨0, hq⟩ : Fin q) g⁻¹

theorem tmJ_loc_spec {P : Program} {f ds rg tbd tbde pr prg prt prte : ℕ}
    (hf : P.funs[f]? = some (tmJLocF ds pr))
    (hds : P.funs[ds]? = some (tmJDsF rg tbd)) (hrg : P.HasAt rg (rangeFuns rg))
    (htbd : P.HasAt tbd (mapFuns tbd tbde)) (htbde : P.funs[tbde]? = some tmJDsEF)
    (hpr : TmJPairAt P pr prg prt prte) {m q : ℕ} (hq : 0 < q) (g : Perm (Fin m)) :
    FunDet P f (.list [tmJLocCtx m q, encPerm g])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq g)))
      (tmJLocK ((m + 1) * (q + 1))) := by
  refine FunDet.intro hf ?_
  unfold tmJLocF
  set c := tmJLocCtx m q with hc
  have d0 := Det.arg' (P := P) (vs := [c, encPerm g]) (rest := []) (j := 0) (v := c) rfl
  have d1 := Det.arg' (P := P) (vs := [c, encPerm g]) (rest := []) (j := 1) (v := encPerm g) rfl
  have g0 := Det.get' d0 (Det.nat 0) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := encPerm (1 : Perm (Fin m))) rfl
  have g1 := Det.get' d0 (Det.nat 1) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := encPerm (1 : Perm (Fin q))) rfl
  have g2 := Det.get' d0 (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have g3 := Det.get' d0 (Det.nat 3) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat m) rfl
  have cds := Det.call (Det.mk3 d1 g0 g2) (tmJ_ds_spec hds hrg htbd htbde hq g)
  have cpr := Det.call (Det.mk4 cds g1 g2 g3) (tmJ_pair_spec hpr
    (Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m)) 1)
  refine cpr.mono ?_
  -- the cost
  set W := (m + 1) * (q + 1) with hW
  have hm1 : m + 1 ≤ W := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ W := Nat.le_mul_of_pos_left _ (by omega)
  have hW1 : 1 ≤ W := by omega
  have hW2 : W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) _
  have hm2 : (m + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hm1 2
  have hq2 : (q + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hq1 2
  have hmq : m * q + 1 ≤ W := by rw [hW]; nlinarith
  set ds' := tmJDsVal (Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m)) with hds'
  have wds : ds'.wt ≤ 9 * W ^ 2 := by
    have := wt_tmJDsVal_le (Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m))
    have : (q + 1) * (m + 1) ^ 2 ≤ W ^ 2 := by
      have e : W ^ 2 = (q + 1) ^ 2 * (m + 1) ^ 2 := by rw [hW]; ring
      rw [e]
      exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
    have h9 : 9 * (q + 1) * (m + 1) ^ 2 = 9 * ((q + 1) * (m + 1) ^ 2) := by ring
    have : ds'.wt = (tmJDsVal (Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m))).wt := rfl
    omega
  have wc := wt_tmJLocCtx_le m q
  have wg := wt_encPerm_le g
  have w1m := wt_encPerm_le (1 : Perm (Fin m))
  have w1q := wt_encPerm_le (1 : Perm (Fin q))
  have wq := wt_nat_le q
  have wm := wt_nat_le m
  have wa := wt_list2_le c (encPerm g)
  have wa3 := wt_list3_le (encPerm g) (encPerm (1 : Perm (Fin m))) (.nat q)
  have wa4 := wt_list4_le ds' (encPerm (1 : Perm (Fin q))) (.nat q) (.nat m)
  have wout := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq g))
  have hout : (m * q + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hmq 2
  have rW : ((m + 1) * (q + 1)) ^ 2 = W ^ 2 := rfl
  have hX : (Val.list [ds', encPerm (1 : Perm (Fin q)), .nat q, .nat m]).wt + m * q + 1 ≤
      50 * W ^ 2 := by omega
  have hP : tmJPairK ((Val.list [ds', encPerm (1 : Perm (Fin q)), .nat q, .nat m]).wt + m * q) ≤
      10 ^ 6 * (50 * W ^ 2) ^ 4 := by
    unfold tmJPairK
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX 4)
  have e1 : 10 ^ 6 * (50 * W ^ 2) ^ 4 = 6250000000000 * W ^ 8 := by ring
  have hD : tmJDsK W ≤ 10 ^ 7 * W ^ 8 := by
    unfold tmJDsK
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW1 (by norm_num))
  have h28 : W ^ 2 ≤ W ^ 8 := Nat.pow_le_pow_right hW1 (by norm_num)
  have e2 : tmJLoc0 hq g = tmJP ((Pi.mulSingle (⟨0, hq⟩ : Fin q) g⁻¹ : Fin q → Perm (Fin m)), 1) :=
    rfl
  rw [e2] at wout
  have r1 : c.wt = (tmJLocCtx m q).wt := rfl
  show _ ≤ 10 ^ 14 * W ^ 8
  omega

/-! ### All generators -/

/-- On `[σN, q, m]`: the generators `tmJWrList` of `N ≀ Sym(q)` on `Fin (m q)`. -/
def tmJWrF (rg ds tbR tbS mp pr : ℕ) : Expr :=
  .letE (.call rg (arg 2))
  (.letE (.call rg (arg 1))
  (.letE (.call ds (mk3 (.var 1) (.var 1) (arg 1)))
  (.letE (.call tbR (mk2 (arg 1) (.var 2)))
  (.letE (.call tbS (mk2 (arg 1) (.var 2)))
  (.letE (.call mp (mk2 (mk4 (.var 1) (.var 2) (arg 1) (arg 2)) (arg 0)))
  (.snoc (.snoc (.var 6) (.call pr (mk4 (.var 3) (.var 4) (arg 1) (arg 2))))
    (.call pr (mk4 (.var 3) (.var 5) (arg 1) (arg 2)))))))))

/-- The generators of `N ≀ Sym(q)` produced by `tmJWrF`, on `Fin m × Fin q`. -/
def tmJWrList {m q : ℕ} (hq : 2 ≤ q) (σN : List (Perm (Fin m))) : List (Perm (Fin m × Fin q)) :=
  σN.map (tmJLoc0 (by omega)) ++ [tmJP ((1 : Fin q → Perm (Fin m)), finRotate q),
    tmJP ((1 : Fin q → Perm (Fin m)), swap ⟨0, by omega⟩ ⟨1, by omega⟩)]

/-- **The generators generate `N ≀ Sym(q)`.** -/
theorem tmJWrList_closure {m q : ℕ} (hq : 2 ≤ q) (σN : List (Perm (Fin m))) :
    Subgroup.closure {σ | σ ∈ tmJWrList hq σN} = tmJW (gens σN) := by
  have hinv : Subgroup.closure {s | s ∈ σN.map (·⁻¹)} = gens σN := by
    have : {s | s ∈ σN.map (·⁻¹)} = ({g | g ∈ σN} : Set (Perm (Fin m)))⁻¹ := by
      ext s; simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_inv]
      constructor
      · rintro ⟨g, hg, rfl⟩; simpa using hg
      · intro hs; exact ⟨s⁻¹, hs, inv_inv s⟩
    rw [this, Subgroup.closure_inv]; rfl
  rw [← tmJ_wreath_gens2 hq (gens σN) (σN.map (·⁻¹)) hinv]
  congr 1
  ext σ
  simp only [tmJWrList, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, tmJLoc0]
  constructor
  · rintro (⟨g, hg, rfl⟩ | rfl | rfl)
    · exact Or.inl ⟨g⁻¹, ⟨g, hg, rfl⟩, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (⟨_, ⟨g, hg, rfl⟩, rfl⟩ | rfl | rfl)
    · exact Or.inl ⟨g, hg, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- The value of a list of pairs on `Fin (m q)`. -/
def tmJPermsVal {m q : ℕ} (l : List (Perm (Fin m × Fin q))) : Val :=
  .list (l.map fun σ => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ))

/-- Where the pieces of `tmJWrF` sit. -/
structure TmJWrAt (P : Program) (f rg ds tbd tbde tbR rotE tbS swE mp loc pr prg prt prte : ℕ) :
    Prop where
  hf : P.funs[f]? = some (tmJWrF rg ds tbR tbS mp pr)
  hrg : P.HasAt rg (rangeFuns rg)
  hds : P.funs[ds]? = some (tmJDsF rg tbd)
  htbd : P.HasAt tbd (mapFuns tbd tbde)
  htbde : P.funs[tbde]? = some tmJDsEF
  htbR : P.HasAt tbR (mapFuns tbR rotE)
  hrotE : P.funs[rotE]? = some tmJRotEF
  htbS : P.HasAt tbS (mapFuns tbS swE)
  hswE : P.funs[swE]? = some tmJSwEF
  hmp : P.HasAt mp (mapFuns mp loc)
  hloc : P.funs[loc]? = some (tmJLocF ds pr)
  hpr : TmJPairAt P pr prg prt prte

/-- The cost of `tmJWrF`, in `Y = wt [σN, q, m] + (m + 1) (q + 1)`. -/
def tmJWrK (Y : ℕ) : ℕ := 10 ^ 18 * Y ^ 9

theorem tmJ_wr_spec {P : Program} {f rg ds tbd tbde tbR rotE tbS swE mp loc pr prg prt prte : ℕ}
    (hA : TmJWrAt P f rg ds tbd tbde tbR rotE tbS swE mp loc pr prg prt prte) {m q : ℕ}
    (hq : 2 ≤ q) (σN : List (Perm (Fin m))) :
    FunDet P f (.list [.list (σN.map encPerm), .nat q, .nat m]) (tmJPermsVal (tmJWrList hq σN))
      (tmJWrK ((Val.list [.list (σN.map encPerm), .nat q, .nat m]).wt + (m + 1) * (q + 1))) := by
  refine FunDet.intro hA.hf ?_
  unfold tmJWrF
  have hq0 : 0 < q := by omega
  set sw := (swap (⟨0, by omega⟩ : Fin q) ⟨1, by omega⟩) with hsw
  -- the six values
  have a2 := Det.arg' (P := P) (vs := [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]) (rest := []) (j := 2) (v := .nat m) rfl
  have c1 := Det.call a2 (tmJ_range_det hA.hrg m)
  rw [tmJ_encFun_id_eq] at c1
  have b1 := Det.arg' (P := P) (vs := [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]) (rest := [(encPerm (1 : Perm (Fin m)))]) (j := 1) (v := .nat q) rfl
  have c2 := Det.call b1 (tmJ_range_det hA.hrg q)
  have v1 := Det.var' (P := P) (env := [Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m], (encPerm (1 : Perm (Fin m))), (encFun fun i : Fin q => (i : ℕ))]) (i := 1) (v := (encPerm (1 : Perm (Fin m)))) rfl
  have b1a := Det.arg' (P := P) (vs := [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]) (rest := [(encPerm (1 : Perm (Fin m))), (encFun fun i : Fin q => (i : ℕ))]) (j := 1) (v := .nat q) rfl
  have c3 := Det.call (Det.mk3 v1 v1 b1a) (tmJ_ds_spec hA.hds hA.hrg hA.htbd hA.htbde hq0 1)
  have hones : (Pi.mulSingle (⟨0, hq0⟩ : Fin q) (1 : Perm (Fin m))⁻¹ : Fin q → Perm (Fin m)) = 1 := by
    simp
  rw [hones] at c3
  have b1b := Det.arg' (P := P) (vs := [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]) (rest := [(encPerm (1 : Perm (Fin m))), (encFun fun i : Fin q => (i : ℕ)), (tmJDsVal (1 : Fin q → Perm (Fin m)))]) (j := 1) (v := .nat q) rfl
  have v2 := Det.var' (P := P) (env := [Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m], (encPerm (1 : Perm (Fin m))), (encFun fun i : Fin q => (i : ℕ)), (tmJDsVal (1 : Fin q → Perm (Fin m)))]) (i := 2) (v := (encFun fun i : Fin q => (i : ℕ))) rfl
  have c4 := Det.call (Det.mk2 b1b v2) (tmJ_top_spec hA.htbR (finRotate q)
    (fun i => tmJ_rotE_spec hA.hrotE i))
  have b1c := Det.arg' (P := P) (vs := [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]) (rest := [(encPerm (1 : Perm (Fin m))), (encFun fun i : Fin q => (i : ℕ)), (tmJDsVal (1 : Fin q → Perm (Fin m))), encPerm (finRotate q)])
    (j := 1) (v := .nat q) rfl
  have v2b := Det.var' (P := P) (env := [Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m], (encPerm (1 : Perm (Fin m))), (encFun fun i : Fin q => (i : ℕ)), (tmJDsVal (1 : Fin q → Perm (Fin m))), encPerm (finRotate q)])
    (i := 2) (v := (encFun fun i : Fin q => (i : ℕ))) rfl
  have c5 := Det.call (Det.mk2 b1c v2b) (tmJ_top_spec hA.htbS sw (fun i => tmJ_swE_spec hA.hswE hq i))
  set rest5 := [(encPerm (1 : Perm (Fin m))), (encFun fun i : Fin q => (i : ℕ)), (tmJDsVal (1 : Fin q → Perm (Fin m))), encPerm (finRotate q), encPerm sw] with hrest5
  have u0 := Det.arg' (P := P) (vs := [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]) (rest := rest5) (j := 0) (v := (Val.list (σN.map encPerm))) rfl
  have u1 := Det.arg' (P := P) (vs := [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]) (rest := rest5) (j := 1) (v := .nat q) rfl
  have u2 := Det.arg' (P := P) (vs := [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]) (rest := rest5) (j := 2) (v := .nat m) rfl
  have w1 := Det.var' (P := P) (env := Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m] :: rest5) (i := 1) (v := (encPerm (1 : Perm (Fin m)))) rfl
  have w2 := Det.var' (P := P) (env := Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m] :: rest5) (i := 2) (v := (encFun fun i : Fin q => (i : ℕ))) rfl
  have hctx := Det.mk4 w1 w2 u1 u2
  have hM := mapList_spec hA.hmp σN encPerm
    (fun g => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g)))
    (c := tmJLocCtx m q) (fun a _ a' _ he => by rw [encPerm_injective he])
    (fun g _ => tmJ_loc_spec hA.hloc hA.hds hA.hrg hA.htbd hA.htbde hA.hpr hq0 g)
  have c6 := Det.call (Det.mk2 hctx u0) hM
  -- the two top generators and the result
  set rest6 := rest5 ++ [(Val.list (σN.map fun g => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g))))] with hrest6
  have x6 := Det.var' (P := P) (env := Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m] :: rest6) (i := 6) (v := (Val.list (σN.map fun g => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g))))) rfl
  have x3 := Det.var' (P := P) (env := Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m] :: rest6) (i := 3) (v := (tmJDsVal (1 : Fin q → Perm (Fin m)))) rfl
  have x4 := Det.var' (P := P) (env := Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m] :: rest6) (i := 4)
    (v := encPerm (finRotate q)) rfl
  have x5 := Det.var' (P := P) (env := Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m] :: rest6) (i := 5) (v := encPerm sw) rfl
  have y1 := Det.arg' (P := P) (vs := [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]) (rest := rest6) (j := 1) (v := .nat q) rfl
  have y2 := Det.arg' (P := P) (vs := [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]) (rest := rest6) (j := 2) (v := .nat m) rfl
  have p1 := Det.call (Det.mk4 x3 x4 y1 y2) (tmJ_pair_spec hA.hpr 1 (finRotate q))
  have p2 := Det.call (Det.mk4 x3 x5 y1 y2) (tmJ_pair_spec hA.hpr 1 sw)
  have dres := Det.snoc (Det.snoc x6 p1) p2
  have hval : tmJPermsVal (tmJWrList hq σN) = Val.list ((σN.map fun g =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g))) ++
      [encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP ((1 : Fin q → Perm (Fin m)), finRotate q)))] ++
      [encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP ((1 : Fin q → Perm (Fin m)), sw)))]) := by
    simp [tmJPermsVal, tmJWrList, List.map_append, Function.comp_def, hsw]
  rw [hval]
  refine (Det.letE c1 (Det.letE c2 (Det.letE c3 (Det.letE c4 (Det.letE c5
    (Det.letE c6 dres)))))).mono ?_
  -- the cost
  set W := (m + 1) * (q + 1) with hW
  set Y := (Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]).wt + W with hY
  set l := σN.length with hl
  have hm1 : m + 1 ≤ W := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ W := Nat.le_mul_of_pos_left _ (by omega)
  have hmq : m * q + 1 ≤ W := by rw [hW]; nlinarith
  have hW1 : 1 ≤ W := by omega
  have hWY : W ≤ Y := by omega
  have hY1 : 1 ≤ Y := by omega
  have hlY : l + 1 ≤ Y := by
    have h1 := length_lt_wt_list (σN.map encPerm)
    have h2 : (Val.list (σN.map encPerm)).wt < (Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]).wt := wt_le_wt_list (by simp)
    simp only [List.length_map] at h1
    have : (Val.list (σN.map encPerm)).wt = (Val.list (σN.map encPerm)).wt := rfl
    omega
  have hW2 : W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW23 : W ^ 2 ≤ W ^ 3 := Nat.pow_le_pow_right hW1 (by norm_num)
  have hW34 : W ^ 3 ≤ W ^ 4 := Nat.pow_le_pow_right hW1 (by norm_num)
  have hW48 : W ^ 4 ≤ W ^ 8 := Nat.pow_le_pow_right hW1 (by norm_num)
  have hm3 : (m + 1) ^ 3 ≤ W ^ 3 := Nat.pow_le_pow_left hm1 3
  have hq3 : (q + 1) ^ 3 ≤ W ^ 3 := Nat.pow_le_pow_left hq1 3
  have hmq2 : (m * q + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hmq 2
  have hW8Y : W ^ 8 ≤ Y ^ 8 := Nat.pow_le_pow_left hWY 8
  have hY89 : Y ^ 8 ≤ Y ^ 9 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hW2Y : W ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hWY 2
  have hY23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY39 : Y ^ 3 ≤ Y ^ 9 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY12 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  -- weights of the values
  have wone := wt_encPerm_le (1 : Perm (Fin m))
  have widq := wt_ids_le q
  have wones : (tmJDsVal (1 : Fin q → Perm (Fin m))).wt ≤ 9 * W ^ 2 := by
    have := wt_tmJDsVal_le (1 : Fin q → Perm (Fin m))
    have : (q + 1) * (m + 1) ^ 2 ≤ W ^ 2 := by
      have e : W ^ 2 = (q + 1) ^ 2 * (m + 1) ^ 2 := by rw [hW]; ring
      rw [e]
      exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
    have h9 : 9 * (q + 1) * (m + 1) ^ 2 = 9 * ((q + 1) * (m + 1) ^ 2) := by ring
    have : (tmJDsVal (1 : Fin q → Perm (Fin m))).wt = (tmJDsVal (1 : Fin q → Perm (Fin m))).wt := rfl
    omega
  have wrot := wt_encPerm_le (finRotate q)
  have wsw := wt_encPerm_le sw
  have wq := wt_nat_le q
  have wm := wt_nat_le m
  have wp1 := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJP ((1 : Fin q → Perm (Fin m)), finRotate q)))
  have wp2 := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJP ((1 : Fin q → Perm (Fin m)), sw)))
  have wlocs : (Val.list (σN.map fun g => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g)))).wt ≤ l * (8 * W ^ 2 + 9) + 4 := by
    have := tmJ_wt_list_le (vs := σN.map fun g =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g)))
      (E := 4 * (m * q + 1) ^ 2) (by
        intro v hv
        obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
        exact wt_encPerm_le _)
    simp only [List.length_map] at this
    have : σN.length * (2 * (4 * (m * q + 1) ^ 2) + 1) ≤ l * (8 * W ^ 2 + 9) :=
      Nat.mul_le_mul_left _ (by omega)
    have : (Val.list (σN.map fun g => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g)))).wt = (Val.list (σN.map fun g =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g)))).wt := rfl
    omega
  have wres : (Val.list ((σN.map fun g =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g))) ++
      [encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP ((1 : Fin q → Perm (Fin m)), finRotate q)))] ++
      [encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP ((1 : Fin q → Perm (Fin m)), sw)))])).wt ≤ (l + 2) * (8 * W ^ 2 + 9) + 4 := by
    have := tmJ_wt_list_le (vs := (σN.map fun g =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g))) ++
      [encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP ((1 : Fin q → Perm (Fin m)), finRotate q)))] ++
      [encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP ((1 : Fin q → Perm (Fin m)), sw)))])
      (E := 4 * (m * q + 1) ^ 2) (by
        intro v hv
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at hv
        rcases hv with (⟨g, -, rfl⟩ | rfl) | rfl <;> exact wt_encPerm_le _)
    simp only [List.length_append, List.length_map, List.length_singleton] at this
    have : (σN.length + 1 + 1) * (2 * (4 * (m * q + 1) ^ 2) + 1) ≤ (l + 2) * (8 * W ^ 2 + 9) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have wres1 : (Val.list ((σN.map fun g =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g))) ++
      [encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP ((1 : Fin q → Perm (Fin m)), finRotate q)))])).wt ≤ (l + 2) * (8 * W ^ 2 + 9) + 4 := by
    have := tmJ_wt_list_le (vs := (σN.map fun g =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g))) ++
      [encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJP ((1 : Fin q → Perm (Fin m)), finRotate q)))])
      (E := 4 * (m * q + 1) ^ 2) (by
        intro v hv
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at hv
        rcases hv with ⟨g, -, rfl⟩ | rfl <;> exact wt_encPerm_le _)
    simp only [List.length_append, List.length_map, List.length_singleton] at this
    have : (σN.length + 1) * (2 * (4 * (m * q + 1) ^ 2) + 1) ≤ (l + 2) * (8 * W ^ 2 + 9) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hLW : (l + 2) * (8 * W ^ 2 + 9) ≤ 34 * Y ^ 3 := by
    calc (l + 2) * (8 * W ^ 2 + 9) ≤ (2 * Y) * (17 * Y ^ 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = 34 * Y ^ 3 := by ring
  have hLW' : l * (8 * W ^ 2 + 9) ≤ (l + 2) * (8 * W ^ 2 + 9) := Nat.mul_le_mul_right _ (by omega)
  have wctx : (tmJLocCtx m q).wt ≤ 40 * W ^ 2 := wt_tmJLocCtx_le m q
  have rone : (encPerm (1 : Perm (Fin m))).wt = (encPerm (1 : Perm (Fin m))).wt := rfl
  have ridq : (encFun fun i : Fin q => (i : ℕ)).wt = (encFun fun i : Fin q => (i : ℕ)).wt := rfl
  have rctx : (Val.list [(encPerm (1 : Perm (Fin m))), (encFun fun i : Fin q => (i : ℕ)), Val.nat q, Val.nat m]).wt = (tmJLocCtx m q).wt := rfl
  have wsv : (Val.list (σN.map encPerm)).wt < (Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]).wt := wt_le_wt_list (by simp)
  have wcs := wt_list2_le (tmJLocCtx m q) (Val.list (σN.map encPerm))
  have wc3 := wt_list3_le (encPerm (1 : Perm (Fin m))) (encPerm (1 : Perm (Fin m))) (Val.nat q)
  have wc4 := wt_list2_le (Val.nat q) (encFun fun i : Fin q => (i : ℕ))
  have wc5 := wt_list2_le (Val.list [(encPerm (1 : Perm (Fin m))), (encFun fun i : Fin q => (i : ℕ)), Val.nat q, Val.nat m]) (Val.list (σN.map encPerm))
  have wq1 := wt_list4_le (tmJDsVal (1 : Fin q → Perm (Fin m))) (encPerm (finRotate q)) (Val.nat q) (Val.nat m)
  have wq2 := wt_list4_le (tmJDsVal (1 : Fin q → Perm (Fin m))) (encPerm sw) (Val.nat q) (Val.nat m)
  have PM1 : l * tmJLocK W ≤ 10 ^ 14 * Y ^ 9 := by
    unfold tmJLocK
    calc l * (10 ^ 14 * W ^ 8) ≤ Y * (10 ^ 14 * Y ^ 8) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hW8Y)
      _ = 10 ^ 14 * Y ^ 9 := by ring
  have PM2 : mapK * (l + 1) * ((Val.list [tmJLocCtx m q, (Val.list (σN.map encPerm))]).wt + (Val.list (σN.map fun g => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g)))).wt + 1) ≤
      10 ^ 6 * Y ^ 9 := by
    have h1 : (Val.list [tmJLocCtx m q, (Val.list (σN.map encPerm))]).wt + (Val.list (σN.map fun g => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g)))).wt + 1 ≤ 200 * Y ^ 3 := by omega
    calc mapK * (l + 1) * ((Val.list [tmJLocCtx m q, (Val.list (σN.map encPerm))]).wt + (Val.list (σN.map fun g => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g)))).wt + 1)
        ≤ 1000 * Y * (200 * Y ^ 3) := by
          unfold mapK; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hlY) h1
      _ = 200000 * Y ^ 4 := by ring
      _ ≤ 10 ^ 6 * Y ^ 9 := by
          have : Y ^ 4 ≤ Y ^ 9 := Nat.pow_le_pow_right hY1 (by norm_num)
          omega
  have PP : ∀ π : Perm (Fin q), (encPerm π).wt ≤ 4 * (q + 1) ^ 2 →
      tmJPairK ((Val.list [(tmJDsVal (1 : Fin q → Perm (Fin m))), encPerm π, Val.nat q, Val.nat m]).wt + m * q) ≤
        10 ^ 13 * Y ^ 9 := by
    intro π hπ
    have w4 := wt_list4_le (tmJDsVal (1 : Fin q → Perm (Fin m))) (encPerm π) (Val.nat q) (Val.nat m)
    have hq2 : (q + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hq1 2
    have hX : (Val.list [(tmJDsVal (1 : Fin q → Perm (Fin m))), encPerm π, Val.nat q, Val.nat m]).wt + m * q + 1 ≤ 50 * W ^ 2 := by
      omega
    unfold tmJPairK
    calc 10 ^ 6 * ((Val.list [(tmJDsVal (1 : Fin q → Perm (Fin m))), encPerm π, Val.nat q, Val.nat m]).wt + m * q + 1) ^ 4
        ≤ 10 ^ 6 * (50 * W ^ 2) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX 4)
      _ = 6250000000000 * W ^ 8 := by ring
      _ ≤ 10 ^ 13 * Y ^ 9 := by omega
  have PP1 := PP (finRotate q) wrot
  have PP2 := PP sw wsw
  have hD : tmJDsK W ≤ 10 ^ 7 * Y ^ 9 := by
    unfold tmJDsK
    have : W ^ 4 ≤ Y ^ 9 := (Nat.pow_le_pow_left hWY 4).trans (Nat.pow_le_pow_right hY1 (by norm_num))
    omega
  have hR1 : 10000 * (m + 1) ^ 3 ≤ 10000 * Y ^ 9 := by
    have : (m + 1) ^ 3 ≤ Y ^ 9 := (Nat.pow_le_pow_left (hm1.trans hWY) 3).trans
      (Nat.pow_le_pow_right hY1 (by norm_num))
    omega
  have hR2 : 10 ^ 5 * (q + 1) ^ 3 ≤ 10 ^ 5 * Y ^ 9 := by
    have : (q + 1) ^ 3 ≤ Y ^ 9 := (Nat.pow_le_pow_left (hq1.trans hWY) 3).trans
      (Nat.pow_le_pow_right hY1 (by norm_num))
    omega
  have rinp : (Val.list [Val.list (σN.map encPerm), Val.nat q, Val.nat m]).wt = (Val.list [(Val.list (σN.map encPerm)), Val.nat q, Val.nat m]).wt :=
    rfl
  have q1 : (tmJDsVal (1 : Fin q → Perm (Fin m))).wt = (tmJDsVal (1 : Fin q → Perm (Fin m))).wt := rfl
  have q2 : mapK * (l + 1) * ((Val.list [tmJLocCtx m q, Val.list (σN.map encPerm)]).wt +
      (Val.list (σN.map fun g => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJLoc0 hq0 g)))).wt + 1) =
      mapK * (l + 1) * ((Val.list [tmJLocCtx m q, (Val.list (σN.map encPerm))]).wt + (Val.list (σN.map fun g => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g)))).wt + 1) := rfl
  have q3 : (Val.list (σN.map fun g => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJLoc0 hq0 g)))).wt = (Val.list (σN.map fun g => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc0 hq0 g)))).wt := rfl
  have q4 : tmJPairK ((Val.list [tmJDsVal (1 : Fin q → Perm (Fin m)), encPerm (finRotate q),
      Val.nat q, Val.nat m]).wt + m * q) =
      tmJPairK ((Val.list [(tmJDsVal (1 : Fin q → Perm (Fin m))), encPerm (finRotate q), Val.nat q, Val.nat m]).wt + m * q) := rfl
  have q5 : tmJPairK ((Val.list [tmJDsVal (1 : Fin q → Perm (Fin m)), encPerm sw,
      Val.nat q, Val.nat m]).wt + m * q) =
      tmJPairK ((Val.list [(tmJDsVal (1 : Fin q → Perm (Fin m))), encPerm sw, Val.nat q, Val.nat m]).wt + m * q) := rfl
  have hm2' : (m + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hm1 2
  have hq2' : (q + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hq1 2
  show _ ≤ 10 ^ 18 * Y ^ 9
  omega

end GI.Impl
