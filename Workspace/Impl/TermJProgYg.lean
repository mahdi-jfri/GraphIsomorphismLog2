import Workspace.Impl.TermJYgMath
import Workspace.Impl.TermJProgWr
import Workspace.Impl.TermJProgFlat

/-!
# The generators of `Aut_{N ≀ Sym(q)}(X)` from the `N`-test table (program)

On `[us, q, m]`, with `us[a (2q) + a'] = tmJEntVal (O a a')` (the stored coset
`Iso_N(x_a, x_{a'})`), `tmJYgF` returns `tmJPermsVal (tmJYgList O)` (`TermJYgMath.lean`).

* `tmJDsAEF`, `tmJDsAF`: the coordinates of `(g⁻¹ at a; 1)`;
* `tmJLocAF`: one local generator; `tmJRowLocF`: the locals of one row;
* `tmJSwDEF`, `tmJSwPEF`, `tmJSwF`: one lifted transposition (or the identity);
* `tmJYgF`: the locals of all rows (flattened), then the transpositions.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

/-- The value of a stored coset. -/
def tmJEntVal {m : ℕ} : Option (Perm (Fin m) × List (Perm (Fin m))) → Val
  | none => .list []
  | some (r, gs) => .list [encPerm r, encGroup gs]

/-! ### Coordinates at a row `a` -/

/-- On `[[g, one, a], i]`: `g` if `i = a`, else `one`. -/
def tmJDsAEF : Expr :=
  .ite (.arith .eq (arg 1) (.get (arg 0) (.nat 2))) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))

theorem tmJ_dsAE_val {m q : ℕ} (a : Fin q) (g : Perm (Fin m)) (i : Fin q) :
    encPerm ((Pi.mulSingle a g⁻¹ : Fin q → Perm (Fin m)) i)⁻¹ =
      if (if (i : ℕ) = a then 1 else 0) = 0 then encPerm (1 : Perm (Fin m)) else encPerm g := by
  by_cases hi : i = a
  · subst hi; simp
  · have : (i : ℕ) ≠ a := fun h => hi (Fin.ext h)
    simp [this, Pi.mulSingle_eq_of_ne hi]

theorem tmJ_dsAE_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJDsAEF) {m q : ℕ}
    (a : Fin q) (g : Perm (Fin m)) (i : Fin q) :
    FunDet P f (.list [.list [encPerm g, encPerm (1 : Perm (Fin m)), .nat a], .nat i])
      (encPerm ((Pi.mulSingle a g⁻¹ : Fin q → Perm (Fin m)) i)⁻¹)
      (1000 * ((m + 1) ^ 2 + q + 1)) := by
  refine FunDet.intro hf ?_
  have d0 := Det.arg' (P := P) (vs := [.list [encPerm g, encPerm (1 : Perm (Fin m)), .nat a],
    .nat i]) (rest := []) (j := 0) (v := .list [encPerm g, encPerm (1 : Perm (Fin m)), .nat a]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [encPerm g, encPerm (1 : Perm (Fin m)), .nat a],
    .nat i]) (rest := []) (j := 1) (v := .nat i) rfl
  have da := Det.get' d0 (Det.nat 2) (vs := [encPerm g, encPerm 1, .nat a]) (v := .nat a) rfl
  have deq := Det.arith (op := .eq) d1 da
  have dg := Det.get' d0 (Det.nat 0) (vs := [encPerm g, encPerm 1, .nat a]) (v := encPerm g) rfl
  have d1' := Det.get' d0 (Det.nat 1) (vs := [encPerm g, encPerm 1, .nat a]) (v := encPerm 1) rfl
  have dite := tmJ_det_ite deq dg d1'
  rw [show Machine.BinOp.eval .eq (i : ℕ) a = if (i : ℕ) = a then 1 else 0 from rfl,
    ← tmJ_dsAE_val a g i] at dite
  refine dite.mono ?_
  have w1 := wt_encPerm_le g
  have w2 := wt_encPerm_le (1 : Perm (Fin m))
  have wc := wt_list3_le (encPerm g) (encPerm (1 : Perm (Fin m))) (.nat a)
  have wa := wt_list2_le (.list [encPerm g, encPerm (1 : Perm (Fin m)), .nat a]) (Val.nat i)
  have wi := wt_nat_le i
  have wa' := wt_nat_le a
  have hi := i.2
  have ha := a.2
  have wb : (Val.nat (if (i : ℕ) = a then 1 else 0)).wt ≤ 3 := by
    split_ifs <;> decide
  have wd := wt_encPerm_le ((Pi.mulSingle a g⁻¹ : Fin q → Perm (Fin m)) i)⁻¹
  omega

/-- On `[g, one, q, a]`: the coordinates of `(g⁻¹ at a; 1)`. -/
def tmJDsAF (rg tb : ℕ) : Expr :=
  .call tb (mk2 (mk3 (arg 0) (arg 1) (arg 3)) (.call rg (arg 2)))

theorem tmJ_dsA_spec {P : Program} {f rg tb tbe : ℕ} (hf : P.funs[f]? = some (tmJDsAF rg tb))
    (hrg : P.HasAt rg (rangeFuns rg)) (htb : P.HasAt tb (mapFuns tb tbe))
    (htbe : P.funs[tbe]? = some tmJDsAEF) {m q : ℕ} (a : Fin q) (g : Perm (Fin m)) :
    FunDet P f (.list [encPerm g, encPerm (1 : Perm (Fin m)), .nat q, .nat a])
      (tmJDsVal (Pi.mulSingle a g⁻¹ : Fin q → Perm (Fin m)))
      (tmJDsK ((m + 1) * (q + 1))) := by
  refine FunDet.intro hf ?_
  unfold tmJDsAF
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact a.elim0)
  have d0 := Det.arg' (P := P) (vs := [encPerm g, encPerm (1 : Perm (Fin m)), .nat q, .nat a])
    (rest := []) (j := 0) (v := encPerm g) rfl
  have d1 := Det.arg' (P := P) (vs := [encPerm g, encPerm (1 : Perm (Fin m)), .nat q, .nat a])
    (rest := []) (j := 1) (v := encPerm 1) rfl
  have d2 := Det.arg' (P := P) (vs := [encPerm g, encPerm (1 : Perm (Fin m)), .nat q, .nat a])
    (rest := []) (j := 2) (v := .nat q) rfl
  have d3 := Det.arg' (P := P) (vs := [encPerm g, encPerm (1 : Perm (Fin m)), .nat q, .nat a])
    (rest := []) (j := 3) (v := .nat a) rfl
  have dr := Det.call d2 (tmJ_range_det hrg q)
  have hT := tabulate_spec htb (c := .list [encPerm g, encPerm (1 : Perm (Fin m)), .nat a])
    (F := fun i : Fin q => encPerm ((Pi.mulSingle a g⁻¹ : Fin q → Perm (Fin m)) i)⁻¹)
    (fun i => tmJ_dsAE_spec htbe a g i)
  have dall := Det.call (Det.mk2 (Det.mk3 d0 d1 d3) dr) hT
  refine dall.mono ?_
  -- the cost
  set W := (m + 1) * (q + 1) with hW
  have hm1 : m + 1 ≤ W := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ W := Nat.le_mul_of_pos_left _ (by omega)
  have hW1 : 1 ≤ W := by omega
  have hW2 : W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW3 : W ^ 2 ≤ W ^ 3 := Nat.pow_le_pow_right hW1 (by norm_num)
  have hW4 : W ^ 3 ≤ W ^ 4 := Nat.pow_le_pow_right hW1 (by norm_num)
  have hm2 : (m + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hm1 2
  have hq2 : (q + 1) ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hq1 2
  have hq3 : (q + 1) ^ 3 ≤ W ^ 3 := Nat.pow_le_pow_left hq1 3
  have w1 := wt_encPerm_le g
  have w2 := wt_encPerm_le (1 : Perm (Fin m))
  have wq := wt_nat_le q
  have wa := wt_nat_le a
  have ha := a.2
  have wa4 := wt_list4_le (encPerm g) (encPerm (1 : Perm (Fin m))) (.nat q) (.nat a)
  have wc := wt_list3_le (encPerm g) (encPerm (1 : Perm (Fin m))) (.nat a)
  have wid := wt_ids_le q
  have wcr := wt_list2_le (.list [encPerm g, encPerm (1 : Perm (Fin m)), .nat a])
    (encFun fun i : Fin q => (i : ℕ))
  have wds := wt_tmJDsVal_le (Pi.mulSingle a g⁻¹ : Fin q → Perm (Fin m))
  have hds : (q + 1) * (m + 1) ^ 2 ≤ W ^ 2 := by
    have e : W ^ 2 = (q + 1) ^ 2 * (m + 1) ^ 2 := by rw [hW]; ring
    rw [e]
    exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
  have h9 : 9 * (q + 1) * (m + 1) ^ 2 = 9 * ((q + 1) * (m + 1) ^ 2) := by ring
  have e1 : Val.list ((List.finRange q).map fun i : Fin q =>
      encPerm ((Pi.mulSingle a g⁻¹ : Fin q → Perm (Fin m)) i)⁻¹) =
      tmJDsVal (Pi.mulSingle a g⁻¹ : Fin q → Perm (Fin m)) := rfl
  rw [e1]
  have P1 : q * (1000 * ((m + 1) ^ 2 + q + 1)) ≤ 3000 * W ^ 3 := by
    calc q * (1000 * ((m + 1) ^ 2 + q + 1)) ≤ W * (1000 * (3 * W ^ 2)) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 3000 * W ^ 3 := by ring
  have P2 : mapK * (q + 1) * ((Val.list [.list [encPerm g, encPerm (1 : Perm (Fin m)), .nat a],
      encFun fun i : Fin q => (i : ℕ)]).wt +
      (tmJDsVal (Pi.mulSingle a g⁻¹ : Fin q → Perm (Fin m))).wt + 1) ≤
      1000 * W * (100 * W ^ 3) := by
    unfold mapK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hq1) (by omega)
  have e2 : 1000 * W * (100 * W ^ 3) = 100000 * W ^ 4 := by ring
  show _ ≤ 10 ^ 7 * W ^ 4
  omega

end GI.Impl
