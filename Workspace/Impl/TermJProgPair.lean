import Workspace.Impl.TermJData
import Workspace.Impl.TermCosetRel

/-!
# A pair as a permutation of `Fin (m q)` (program)

Every permutation the `J`-step hands to a cited call is a pair `(d, π)` written on `Fin (m q)`:
the point `t = i + q c` (`finProdFinEquiv (c, i)`) goes to `π i + q · d_i⁻¹ c`. This is
`toFin finProdFinEquiv (tmJP (d, π))`.

* `tmJPairEF`: one entry, on `[[ds, π, q], t]` with `ds = [d_0⁻¹, …, d_{q-1}⁻¹]`;
* `tmJPairF rg tb`: on `[ds, π, q, m]`, the whole permutation (range of `m q`, then tabulate).

`tmJ_pair_spec`: the result is `encPerm (toFin finProdFinEquiv (tmJP (d, π)))`, at cost at most
`tmJPairK X` for `X` the weight of the input plus `m q`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv
open GI.Cited (Val encPerm encPerms encGroup gens)

/-- The value of the inverted coordinates `[d_0⁻¹, …, d_{q-1}⁻¹]`. -/
def tmJDsVal {m q : ℕ} (d : Fin q → Perm (Fin m)) : Val :=
  .list ((List.finRange q).map fun i => encPerm (d i)⁻¹)

/-- **One entry of a pair**: on `[[ds, π, q], t]`, the number `π (t % q) + q · ds[t % q][t / q]`. -/
def tmJPairEF : Expr :=
  .arith .add (.get (.get (arg 0) (.nat 1)) (.arith .mod (arg 1) (.get (arg 0) (.nat 2))))
    (.arith .mul (.get (arg 0) (.nat 2))
      (.get (.get (.get (arg 0) (.nat 0)) (.arith .mod (arg 1) (.get (arg 0) (.nat 2))))
        (.arith .div (arg 1) (.get (arg 0) (.nat 2)))))

/-- The point `t` of `Fin (m q)` is the pair `(t / q, t % q)`. -/
theorem tmJ_toFin_apply {m q : ℕ} (σ : Perm (Fin m × Fin q)) (t : Fin (m * q)) :
    ((toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ t : Fin (m * q)) : ℕ) =
      (σ (finProdFinEquiv.symm t)).2 + q * (σ (finProdFinEquiv.symm t)).1 := by
  simp [toFin, Equiv.permCongrHom, Equiv.permCongr_apply]

/-- **One entry.** -/
theorem tmJ_pairE_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJPairEF) {m q : ℕ}
    (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)) (t : Fin (m * q)) :
    FunDet P f (.list [.list [tmJDsVal d, encPerm π, .nat q], .nat t])
      (.nat (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)) t))
      (100 * ((Val.list [tmJDsVal d, encPerm π, .nat q]).wt + m * q + 10)) := by
  refine FunDet.intro hf ?_
  set ctx := Val.list [tmJDsVal d, encPerm π, .nat q] with hctx
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at t; exact t.elim0)
  have htq : (t : ℕ) / q < m := (Nat.div_lt_iff_lt_mul hq).2 t.2
  have htm : (t : ℕ) % q < q := Nat.mod_lt _ hq
  set i : Fin q := ⟨t % q, htm⟩ with hi
  set c : Fin m := ⟨t / q, htq⟩ with hc
  have hsymm : finProdFinEquiv.symm t = (c, i) := by ext <;> simp [hc, hi]
  have d0 := Det.arg' (P := P) (vs := [ctx, .nat t]) (rest := []) (j := 0) (v := ctx) rfl
  have d1 := Det.arg' (P := P) (vs := [ctx, .nat t]) (rest := []) (j := 1) (v := .nat t) rfl
  have dds := Det.get' d0 (Det.nat 0) (vs := [tmJDsVal d, encPerm π, .nat q])
    (v := tmJDsVal d) rfl
  have dpi := Det.get' d0 (Det.nat 1) (vs := [tmJDsVal d, encPerm π, .nat q])
    (v := encPerm π) rfl
  have dq := Det.get' d0 (Det.nat 2) (vs := [tmJDsVal d, encPerm π, .nat q]) (v := .nat q) rfl
  have dmod := Det.arith' (op := .mod) d1 dq (z := t % q) rfl
  have ddiv := Det.arith' (op := .div) d1 dq (z := t / q) rfl
  have hpi : ((List.finRange q).map fun j => Val.nat (π j))[(t : ℕ) % q]? =
      some (.nat (π i)) := by simp [hi, htm]
  have dpiv := Det.get' dpi dmod hpi
  have hrow : ((List.finRange q).map fun j => encPerm (d j)⁻¹)[(t : ℕ) % q]? =
      some (encPerm (d i)⁻¹) := by simp [hi, htm]
  have drow := Det.get' dds dmod hrow
  have hent : ((List.finRange m).map fun b => Val.nat ((d i)⁻¹ b))[(t : ℕ) / q]? =
      some (.nat ((d i)⁻¹ c)) := by simp [hc, htq]
  have dent := Det.get' drow ddiv hent
  have dmul := Det.arith' (op := .mul) dq dent (z := q * ((d i)⁻¹ c)) rfl
  have dres := Det.arith' (op := .add) dpiv dmul
    (z := (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)) t : ℕ)) (by
      rw [tmJ_toFin_apply, hsymm]; rfl)
  refine dres.mono ?_
  have w1 : (tmJDsVal d).wt < ctx.wt := wt_le_wt_list (by simp)
  have w2 : (encPerm π).wt < ctx.wt := wt_le_wt_list (by simp)
  have w3 : (Val.nat q).wt < ctx.wt := wt_le_wt_list (by simp)
  have w4 : (encPerm (d i)⁻¹).wt < (tmJDsVal d).wt := wt_le_wt_list (List.mem_of_getElem? hrow)
  have w5 : (Val.nat ((d i)⁻¹ c)).wt < (encPerm (d i)⁻¹).wt :=
    wt_le_wt_list (List.mem_of_getElem? hent)
  have w6 : (Val.nat (π i)).wt < (encPerm π).wt := wt_le_wt_list (List.mem_of_getElem? hpi)
  have wa := wt_list2_le ctx (Val.nat t)
  have wt := wt_nat_le t
  have h1 : (t : ℕ) % q ≤ t := Nat.mod_le _ _
  have h2 : (t : ℕ) / q ≤ t := Nat.div_le_self _ _
  have h3 := t.2
  have wr := wt_nat_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)) t : ℕ)
  have h4 := (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)) t).2
  have wm := wt_nat_le (q * ((d i)⁻¹ c))
  have h5 : q * ((d i)⁻¹ c : ℕ) ≤ m * q := by
    have := ((d i)⁻¹ c).2
    nlinarith
  omega

/-- **A pair on `Fin (m q)`**: on `[ds, π, q, m]`, tabulate the entries over `0, …, m q - 1`. -/
def tmJPairF (rg tb : ℕ) : Expr :=
  .call tb (mk2 (mk3 (arg 0) (arg 1) (arg 2)) (.call rg (.arith .mul (arg 3) (arg 2))))

/-- The cost bound of a pair, in `X = wt [ds, π, q, m] + m q`. -/
def tmJPairK (X : ℕ) : ℕ := 10 ^ 6 * (X + 1) ^ 4

/-- Where the pieces of the pair program sit. -/
structure TmJPairAt (P : Program) (f rg tb tbe : ℕ) : Prop where
  hf : P.funs[f]? = some (tmJPairF rg tb)
  hrg : P.HasAt rg (rangeFuns rg)
  htb : P.HasAt tb (mapFuns tb tbe)
  htbe : P.funs[tbe]? = some tmJPairEF

/-- **A pair on `Fin (m q)`.** -/
theorem tmJ_pair_spec {P : Program} {f rg tb tbe : ℕ} (hA : TmJPairAt P f rg tb tbe) {m q : ℕ}
    (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)) :
    FunDet P f (.list [tmJDsVal d, encPerm π, .nat q, .nat m])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π))))
      (tmJPairK ((Val.list [tmJDsVal d, encPerm π, .nat q, .nat m]).wt + m * q)) := by
  refine FunDet.intro hA.hf ?_
  unfold tmJPairF
  set a := Val.list [tmJDsVal d, encPerm π, .nat q, .nat m] with ha
  set ctx := Val.list [tmJDsVal d, encPerm π, .nat q] with hctx
  set σ := toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)) with hσ
  have d0 := Det.arg' (P := P) (vs := [tmJDsVal d, encPerm π, .nat q, .nat m]) (rest := [])
    (j := 0) (v := tmJDsVal d) rfl
  have d1 := Det.arg' (P := P) (vs := [tmJDsVal d, encPerm π, .nat q, .nat m]) (rest := [])
    (j := 1) (v := encPerm π) rfl
  have d2 := Det.arg' (P := P) (vs := [tmJDsVal d, encPerm π, .nat q, .nat m]) (rest := [])
    (j := 2) (v := .nat q) rfl
  have d3 := Det.arg' (P := P) (vs := [tmJDsVal d, encPerm π, .nat q, .nat m]) (rest := [])
    (j := 3) (v := .nat m) rfl
  have dctx := Det.mk3 d0 d1 d2
  have hmul := Det.arith' (op := .mul) d3 d2 (z := m * q) rfl
  have hR : FunDet P rg (.nat (m * q)) (encFun fun i : Fin (m * q) => (i : ℕ))
      (loopModK * (m * q + 1) * ((Val.nat (m * q)).wt + m * q +
        (natList (List.range (m * q))).wt + 1)) := by
    rw [encFun_id]
    exact FunAll.mono (range_spec hA.hrg (m * q)) fun w c h => by
      obtain ⟨rfl, h2⟩ := h; exact ⟨rfl, h2⟩
  have c5r := Det.call hmul hR
  have hT := tabulate_spec hA.htb (c := ctx) (F := fun t => .nat (σ t))
    (fun t => tmJ_pairE_spec hA.htbe d π t)
  have c5 := Det.call (Det.mk2 dctx c5r) hT
  have he : Val.list ((List.finRange (m * q)).map fun t => Val.nat (σ t)) = encPerm σ := rfl
  rw [he] at c5
  refine c5.mono ?_
  -- the cost
  set X := a.wt + m * q with hX
  set Y := X + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  have hmqY : m * q + 1 ≤ Y := by omega
  have hY12 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY34 : Y ^ 3 ≤ Y ^ 4 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hq2 : (m * q + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hmqY 2
  have wctx : ctx.wt ≤ a.wt := wt_list_mono (show [tmJDsVal d, encPerm π, .nat q] <+:
      [tmJDsVal d, encPerm π, .nat q, .nat m] from ⟨[.nat m], rfl⟩)
  have wid := wt_ids_le (m * q)
  have wrg : (natList (List.range (m * q))).wt ≤ 4 * (m * q + 1) ^ 2 := by
    rw [← encFun_id]; exact wid
  have wσ := wt_encPerm_le σ
  have wnmq := wt_nat_le (m * q)
  have wcr := wt_list2_le ctx (encFun fun i : Fin (m * q) => (i : ℕ))
  have hctxY : ctx.wt + m * q + 10 ≤ 40 * Y ^ 2 := by omega
  have P1 : m * q * (100 * (ctx.wt + m * q + 10)) ≤ 4000 * Y ^ 3 := by
    calc m * q * (100 * (ctx.wt + m * q + 10)) ≤ Y * (100 * (40 * Y ^ 2)) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 4000 * Y ^ 3 := by ring
  have P2 : mapK * (m * q + 1) * ((Val.list [ctx, encFun fun i : Fin (m * q) => (i : ℕ)]).wt +
      (encPerm σ).wt + 1) ≤ 10 ^ 5 * Y ^ 3 := by
    calc _ ≤ 1000 * Y * (100 * Y ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hmqY) (by omega)
      _ = 10 ^ 5 * Y ^ 3 := by ring
  have P3 : loopModK * (m * q + 1) * ((Val.nat (m * q)).wt + m * q +
      (natList (List.range (m * q))).wt + 1) ≤ 10 ^ 4 * Y ^ 3 := by
    calc _ ≤ 1000 * Y * (10 * Y ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hmqY) (by omega)
      _ = 10 ^ 4 * Y ^ 3 := by ring
  have r2 : (Val.list [tmJDsVal d, encPerm π, Val.nat q]).wt = ctx.wt := rfl
  have r3 : (Val.list [Val.list [tmJDsVal d, encPerm π, Val.nat q],
      encFun fun i : Fin (m * q) => (i : ℕ)]).wt =
      (Val.list [ctx, encFun fun i : Fin (m * q) => (i : ℕ)]).wt := rfl
  have r1 : (Val.list [tmJDsVal d, encPerm π, Val.nat q, Val.nat m]).wt = a.wt := rfl
  have r4 : m * q * (100 * ((Val.list [tmJDsVal d, encPerm π, Val.nat q]).wt + m * q + 10)) =
      m * q * (100 * (ctx.wt + m * q + 10)) := rfl
  show _ ≤ 10 ^ 6 * Y ^ 4
  omega

end GI.Impl
