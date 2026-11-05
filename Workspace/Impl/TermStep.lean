module

public import Workspace.Impl.TermAsm
public import Workspace.Impl.FreshColor
public import Workspace.Lang.Lib.Tabulate

@[expose] public section

/-!
# The value of one call of the row terminal, as a program (T1)

The row terminal asks `Solve` on `rowState K z w`, where `z` and `w` are two rows of the strings
(`tmTestState`, `tmCosetState`). Its canonical value is `tmRowVal gs c z w`
(`Workspace/Impl/TermCall.lean`). This file computes that value from a *context*

`ctx = [xv, yv, cv, gN, gH, ones, m, q]`,

where `xv`, `yv` are the color values of the state, `cv = coordsVal e S E` lists the positions of
each row, `gN`, `gH` are group values of `N` and `H` with at most `m²` generators, and `ones` is
the list of `m` ones (the domain of a fresh state on `Fin m`).

* `tmRowF` on `[ctx, a]`: the codes of row `a` (the rows of `x` are `0, …, q - 1`, those of `y`
  are `q, …, 2q - 1`), by one gather from `xv` or `yv` at the positions of the row;
* `tmValF` on `[g, zc, wc, ones, m]`: the value `tmRowVal`, from the codes of the two rows: the
  concatenation `L` of the codes of `w` and `z`, and the first position in `L` of each code
  (`mapPos_spec`), as for a fresh phase;
* `tmAskF` on `[ctx, sel, a, b]`: the value of the call on rows `a` and `b` under the group
  `ctx[sel]`.

The costs are polynomial in a bound `M` on the sizes and weights in the context.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

variable {Ω C : Type}

/-! ### Rows by number -/

/-- Row number `a` of the `2q` rows: the rows of `x`, then the rows of `y`. -/
def tmRowAt (q a : ℕ) (h : a < 2 * q) : Fin q ⊕ Fin q :=
  if ha : a < q then .inl ⟨a, ha⟩ else .inr ⟨a - q, by omega⟩

theorem tmRows_getElem? (q a : ℕ) (h : a < 2 * q) : (tmRows q)[a]? = some (tmRowAt q a h) := by
  unfold tmRows tmRowAt
  by_cases ha : a < q
  · rw [dif_pos ha, List.getElem?_append_left (by simpa using ha)]
    simp [ha]
  · rw [dif_neg ha, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map, List.length_finRange, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by simp; omega)]
    simp

theorem tm_product_getElem? {α β : Type} (l₁ : List α) (l₂ : List β) (j : ℕ)
    (hj : j < l₁.length * l₂.length) :
    ∃ (h1 : j / l₂.length < l₁.length) (h2 : j % l₂.length < l₂.length),
      (l₁ ×ˢ l₂)[j]? = some (l₁[j / l₂.length], l₂[j % l₂.length]) := by
  induction l₁ generalizing j with
  | nil => simp at hj
  | cons a l₁ ih =>
    have hn : 0 < l₂.length := by
      rcases Nat.eq_zero_or_pos l₂.length with h | h
      · rw [h] at hj; simp at hj
      · exact h
    rw [List.product_cons]
    by_cases hjl : j < l₂.length
    · refine ⟨by rw [Nat.div_eq_of_lt hjl]; simp, Nat.mod_lt _ hn, ?_⟩
      rw [List.getElem?_append_left (by simpa using hjl), List.getElem?_map,
        List.getElem?_eq_getElem hjl]
      simp only [Option.map_some, Nat.div_eq_of_lt hjl, Nat.mod_eq_of_lt hjl,
        List.getElem_cons_zero]
    · have hj' : j - l₂.length < l₁.length * l₂.length := by
        simp only [List.length_cons, Nat.add_mul, one_mul] at hj; omega
      obtain ⟨h1, h2, h3⟩ := ih (j - l₂.length) hj'
      have hd : j / l₂.length = (j - l₂.length) / l₂.length + 1 := by
        rw [← Nat.sub_add_cancel (not_lt.1 hjl), Nat.add_div_right _ hn, Nat.add_sub_cancel]
      have hm : j % l₂.length = (j - l₂.length) % l₂.length := by
        conv_lhs => rw [← Nat.sub_add_cancel (not_lt.1 hjl)]
        exact Nat.add_mod_right _ _
      refine ⟨by rw [hd]; simpa using h1, Nat.mod_lt _ hn, ?_⟩
      rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map]
      rw [h3]
      simp only [hd, hm, List.getElem_cons_succ]

/-- The `j`-th `N`-test of the program's order. -/
theorem tmTests_getElem? (q j : ℕ) (hj : j < 4 * q ^ 2) :
    ∃ (h1 : j / (2 * q) < 2 * q) (h2 : j % (2 * q) < 2 * q),
      (tmTests q)[j]? = some (tmRowAt q (j / (2 * q)) h1, tmRowAt q (j % (2 * q)) h2) := by
  have hl : (tmRows q).length = 2 * q := by simp [tmRows]; ring
  obtain ⟨h1, h2, h3⟩ := tm_product_getElem? (tmRows q) (tmRows q) j (by rw [hl]; nlinarith)
  rw [hl] at h1 h2
  refine ⟨h1, h2, ?_⟩
  unfold tmTests
  rw [h3]
  congr 2
  · have := tmRows_getElem? q (j / (2 * q)) h1
    rw [List.getElem?_eq_getElem (by rw [hl]; exact h1)] at this
    simp only [Option.some.injEq] at this
    convert this using 2; rw [hl]
  · have := tmRows_getElem? q (j % (2 * q)) h2
    rw [List.getElem?_eq_getElem (by rw [hl]; exact h2)] at this
    simp only [Option.some.injEq] at this
    convert this using 2; rw [hl]

/-- The `j`-th coset call of the program's order. -/
theorem tmCosets_getElem? (q j : ℕ) (hj : j < q ^ 2) :
    ∃ (h1 : j / q < q) (h2 : j % q < q), (tmCosets q)[j]? = some (⟨j / q, h1⟩, ⟨j % q, h2⟩) := by
  have hl : (List.finRange q).length = q := List.length_finRange
  obtain ⟨h1, h2, h3⟩ := tm_product_getElem? (List.finRange q) (List.finRange q) j
    (by rw [hl]; nlinarith)
  rw [hl] at h1 h2
  refine ⟨h1, h2, ?_⟩
  unfold tmCosets
  rw [h3]
  simp only [List.getElem_finRange, Option.some.injEq, Prod.mk.injEq]
  constructor <;> ext <;> simp [hl]

theorem length_tmTests (q : ℕ) : (tmTests q).length = 4 * q ^ 2 := by
  simp [tmTests, tmRows, List.length_product]; ring

theorem length_tmCosets (q : ℕ) : (tmCosets q).length = q ^ 2 := by
  simp [tmCosets, List.length_product]; ring

/-! ### The context -/

/-- The list of `m` ones: the domain value of a fresh state on `Fin m`. -/
def tmOnes (m : ℕ) : Val := .list (List.replicate m (.nat 1))

/-- **The context** of the calls. -/
def tmCtx (xv yv cv gN gH : Val) (m q : ℕ) : Val :=
  .list [xv, yv, cv, gN, gH, tmOnes m, .nat m, .nat q]

/-- The codes of a row string. -/
def tmCodes (c : C → ℕ) {m : ℕ} (z : Fin m → C) : List ℕ := (List.finRange m).map fun b => c (z b)

theorem tmCodeList_eq (c : C → ℕ) {m : ℕ} (z w : Fin m → C) :
    tmCodeList c z w = tmCodes c w ++ tmCodes c z := rfl

theorem tmCmp_eq (c : C → ℕ) {m : ℕ} (z w u : Fin m → C) :
    tmCmp c z w u = (tmCodes c u).map (posOf (tmCodeList c z w)) := by
  simp [tmCmp, tmCodes, List.map_map, Function.comp_def]

theorem wt_tmOnes_le (m : ℕ) : (tmOnes m).wt ≤ 7 * m + 4 := by
  have h := wt_natList_le (xs := List.replicate m 1) (B := 1) (by simp)
  have e : natList (List.replicate m 1) = tmOnes m := by simp [natList, tmOnes, List.map_replicate]
  rw [e] at h
  simp only [List.length_replicate] at h
  omega

theorem wt_tmCodes_le (c : C → ℕ) {m M : ℕ} (z : Fin m → C) (hm : m ≤ M)
    (hc : ∀ b, c (z b) < 2 * M) : (natList (tmCodes c z)).wt ≤ 9 * (M + 1) ^ 2 := by
  have h := wt_natList_le (xs := tmCodes c z) (B := 2 * M) (by
    intro y hy
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
    exact (hc b).le)
  have hl : (tmCodes c z).length = m := by simp [tmCodes]
  rw [hl] at h
  have : m * (2 * (2 * M) + 5) ≤ M * (4 * M + 5) := Nat.mul_le_mul hm (by omega)
  nlinarith

/-! ### `tmRowF`: the codes of one row -/

/-- The positions of row `i` in `cv`. -/
theorem coordsVal_getElem? {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) {m q : ℕ}
    (E : Fin m × Fin q ≃ S.dom) (i : Fin q) :
    (match coordsVal e S E with | .list l => l | .nat _ => [])[(i : ℕ)]? =
      some (natList ((List.finRange m).map fun β => ((e (E (β, i)).val : Fin k) : ℕ))) := by
  simp [coordsVal]

/-- The body of `tmRowF`, with the gather at `ga`. -/
def tmRowBody (ga : ℕ) : Expr :=
  .ite (.arith .lt (arg 1) (.get (arg 0) (.nat 7)))
    (.call ga (mk2 (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 2)) (arg 1))))
    (.call ga (mk2 (.get (arg 0) (.nat 1))
      (.get (.get (arg 0) (.nat 2)) (.arith .sub (arg 1) (.get (arg 0) (.nat 7))))))

/-- The cost constant of `tmRowF`. -/
def tmRowK : ℕ := 10 ^ 9

section RowF

variable {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) {m q : ℕ}
  (E : Fin m × Fin q ≃ S.dom)

/-- The gather of one row. -/
theorem tm_gather_row {P : Program} {ga : ℕ} (hga : P.HasAt ga (gatherFuns ga)) (x : Ω → C)
    (i : Fin q) :
    FunDet P ga (.list [colVal e c x,
        natList ((List.finRange m).map fun β => ((e (E (β, i)).val : Fin k) : ℕ))])
      (natList (tmCodes c fun b => x (E (b, i))))
      (gatherK * ((Val.list [colVal e c x,
        natList ((List.finRange m).map fun β => ((e (E (β, i)).val : Fin k) : ℕ))]).wt + 1) ^ 3) := by
  have hg := gather_spec hga (L := (List.finRange k).map fun j => Val.nat (c (x (e.symm j))))
    (is := (List.finRange m).map fun β => ((e (E (β, i)).val : Fin k) : ℕ)) (by
      intro j hj
      obtain ⟨β, -, rfl⟩ := List.mem_map.1 hj
      simp)
  have e1 : (Val.list (((List.finRange m).map fun β => ((e (E (β, i)).val : Fin k) : ℕ)).map
      fun j => ((List.finRange k).map fun j => Val.nat (c (x (e.symm j)))).getD j (.nat 0))) =
      natList (tmCodes c fun b => x (E (b, i))) := by
    simp only [natList, tmCodes, List.map_map]
    congr 1
    apply List.map_congr_left
    intro β _
    simp only [Function.comp_apply]
    rw [getD_finRange_map _ _ (e (E (β, i)).val).isLt]
    simp
  rw [e1] at hg
  exact hg

theorem coordsVal_eq_list :
    coordsVal e S E = .list ((List.finRange q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ))) := rfl

theorem coordsVal_get? (i : Fin q) :
    ((List.finRange q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))[(i : ℕ)]? =
      some (natList ((List.finRange m).map fun β => ((e (E (β, i)).val : Fin k) : ℕ))) := by
  simp

theorem length_lt_wt_natList (l : List ℕ) : l.length < (natList l).wt := by
  have := length_lt_wt_list (l.map Val.nat); simpa [natList] using this

/-- **The codes of row `a`.** `W` is the weight of the context. -/
theorem tmRow_spec {P : Program} {f ga : ℕ} (hf : P.funs[f]? = some (tmRowBody ga))
    (hga : P.HasAt ga (gatherFuns ga)) (gN gH : Val) (hcol : ∀ x, c (S.x x) < 2 * k ∧ c (S.y x) < 2 * k)
    (a : ℕ) (ha : a < 2 * q) :
    FunDet P f (.list [tmCtx (colVal e c S.x) (colVal e c S.y) (coordsVal e S E) gN gH m q, .nat a])
      (natList (tmCodes c (tmRowStr S E (tmRowAt q a ha))))
      (tmRowK * ((tmCtx (colVal e c S.x) (colVal e c S.y) (coordsVal e S E) gN gH m q).wt + 1) ^ 3) := by
  set xv := colVal e c S.x
  set yv := colVal e c S.y
  set cv := coordsVal e S E
  set ctx := tmCtx xv yv cv gN gH m q with hctx
  set W := ctx.wt with hW
  have hl : ∀ v ∈ [xv, yv, cv, gN, gH, tmOnes m, .nat m, .nat q], v.wt < W := fun v hv =>
    wt_le_wt_list hv
  have wx := hl xv (by simp)
  have wy := hl yv (by simp)
  have wc := hl cv (by simp)
  have wo := hl (tmOnes m) (by simp)
  have wq := hl (.nat q) (by simp)
  have hmW : m < W := by
    have := length_lt_wt_list (List.replicate m (Val.nat 1))
    simp only [List.length_replicate] at this
    have : (Val.list (List.replicate m (Val.nat 1))).wt = (tmOnes m).wt := rfl
    omega
  have hkW : k < W := by
    have := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (c (S.x (e.symm i))))
    simp only [List.length_map, List.length_finRange] at this
    have : (Val.list ((List.finRange k).map fun i => Val.nat (c (S.x (e.symm i))))).wt = xv.wt := rfl
    omega
  have hqW : q < W := by
    have := length_lt_wt_list ((List.finRange q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))
    simp only [List.length_map, List.length_finRange] at this
    have : (coordsVal e S E).wt = cv.wt := rfl
    rw [coordsVal_eq_list] at this
    omega
  have hiW : (Val.list [ctx, .nat a]).wt ≤ 2 * (W + a + 2) + 6 := by
    have := wt_list2_le ctx (.nat a); have := wt_nat_le a; omega
  have dctx := Det.arg' (P := P) (vs := [ctx, .nat a]) (rest := []) (j := 0) (v := ctx) rfl
  have da := Det.arg' (P := P) (vs := [ctx, .nat a]) (rest := []) (j := 1) (v := .nat a) rfl
  have dq := Det.get' dctx (Det.nat 7) (vs := [xv, yv, cv, gN, gH, tmOnes m, .nat m, .nat q])
    (v := .nat q) rfl
  have dcv := Det.get' dctx (Det.nat 2) (vs := [xv, yv, cv, gN, gH, tmOnes m, .nat m, .nat q])
    (v := cv) rfl
  have hcv : cv = .list ((List.finRange q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ))) :=
    coordsVal_eq_list e S E
  have hcvw := congrArg Val.wt hcv
  rw [hcv] at dcv
  -- the row of a string `x` with code value `xv'` at entry `j` of the context
  have key : ∀ (x : Ω → C) (xv' : Val), xv' = colVal e c x → xv'.wt < W →
      (∀ y, c (x y) < 2 * k) → ∀ (i : Fin q) (j : ℕ), j ≤ 1 →
      [xv, yv, cv, gN, gH, tmOnes m, .nat m, .nat q][j]? = some xv' →
      ∀ (ie : Expr) (ci : ℕ), Det P [.list [ctx, .nat a]] ie (.nat i) ci →
      Det P [.list [ctx, .nat a]] (.call ga (mk2 (.get (arg 0) (.nat j)) (.get (.get (arg 0) (.nat 2)) ie)))
        (natList (tmCodes c fun b => x (E (b, i))))
        (ci + 4 * (Val.list [ctx, .nat a]).wt + 3 * W + 40 + 2 * (4 * W + 6) + gatherK * (4 * W + 7) ^ 3 +
          9 * (W + 1) ^ 2 + 1) := by
    intro x xv' hxv' hxw hxc i j hj hget ie ci die
    have dx := Det.get' dctx (Det.nat j) hget
    have dr := Det.get' dcv die (coordsVal_get? e S E i)
    have hg := tm_gather_row e c S E hga x i
    rw [← hxv'] at hg
    set rv := natList ((List.finRange m).map fun β => ((e (E (β, i)).val : Fin k) : ℕ))
    have wr : rv.wt < cv.wt := by
      rw [hcv]
      exact wt_le_wt_list (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
    have w2 : (Val.list [xv', rv]).wt + 1 ≤ 4 * W + 7 := by
      have := wt_list2_le xv' rv; omega
    have hout := wt_tmCodes_le c (M := W) (fun b => x (E (b, i))) hmW.le
      (fun b => by have := hxc (E (b, i)); beta_reduce; omega)
    refine (Det.call (Det.mk2 dx dr) hg).mono ?_
    have := Nat.pow_le_pow_left w2 3
    have := Nat.mul_le_mul_left gatherK this
    have := wt_list2_le xv' rv
    have : j + 3 ≤ 4 := by omega
    omega
  refine FunDet.intro hf ?_
  unfold tmRowBody
  by_cases haq : a < q
  · have dlt := Det.arith' (op := .lt) da dq (z := 1) (by simp [GI.Machine.BinOp.eval, haq])
    have hrow : tmRowStr S E (tmRowAt q a ha) = fun b => S.x (E (b, ⟨a, haq⟩)) := by
      simp [tmRowAt, haq, tmRowStr]
    rw [hrow]
    have := key S.x xv rfl wx (fun y => (hcol y).1) ⟨a, haq⟩ 0 (by omega) rfl _ _ da
    refine (Det.ite_pos dlt one_ne_zero this).mono ?_
    have := wt_tmCodes_le c (M := W) (fun b => S.x (E (b, ⟨a, haq⟩))) hmW.le
      (fun b => by have := (hcol (E (b, ⟨a, haq⟩))).1; beta_reduce; omega)
    have h1 : 4 * (Val.list [ctx, .nat a]).wt + 3 * W + 40 + 2 * (4 * W + 6) ≤ 100 * (W + 1) := by omega
    have h2 : (4 * W + 7) ^ 3 ≤ 7 ^ 3 * (W + 1) ^ 3 := pow_le_mul_pow 3 (by omega)
    have h3 : (W + 1) ≤ (W + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h4 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [tmRowK, gatherK] at *
    omega
  · have dlt := Det.arith' (op := .lt) da dq (z := 0) (by simp [GI.Machine.BinOp.eval, haq])
    have hrow : tmRowStr S E (tmRowAt q a ha) =
        fun b => S.y (E (b, ⟨a - q, by omega⟩)) := by
      simp [tmRowAt, haq, tmRowStr]
    rw [hrow]
    have dsub := Det.arith' (op := .sub) da dq (z := a - q) rfl
    have := key S.y yv rfl wy (fun y => (hcol y).2) ⟨a - q, by omega⟩ 1 (by omega) rfl _ _ dsub
    refine (Det.ite_zero dlt this).mono ?_
    have := wt_tmCodes_le c (M := W) (fun b => S.y (E (b, ⟨a - q, by omega⟩))) hmW.le
      (fun b => by have := (hcol (E (b, ⟨a - q, by omega⟩))).2; beta_reduce; omega)
    have h1 : 4 * (Val.list [ctx, .nat a]).wt + 3 * W + 40 + 2 * (4 * W + 6) ≤ 100 * (W + 1) := by omega
    have h2 : (4 * W + 7) ^ 3 ≤ 7 ^ 3 * (W + 1) ^ 3 := pow_le_mul_pow 3 (by omega)
    have h3 : (W + 1) ≤ (W + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h4 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [tmRowK, gatherK] at *
    omega

end RowF

/-! ### `tmValF`: the value of a call from the codes of its rows -/

/-- The body of `tmValF` on `[g, zc, wc, ones, m]`, with `append` at `ap` and `mapPos` at
`mp`. -/
def tmValBody (ap mp : ℕ) : Expr :=
  .letE (.call ap (mk2 (arg 2) (arg 1)))
  (.letE (.call mp (mk2 (.var 1) (arg 2)))
  (.letE (.call mp (mk2 (.var 1) (arg 1)))
  (Expr.mkList [arg 4, arg 0, arg 3, .var 2, .var 3, .nil, .nil, .nat 0, .nat 2, arg 4])))

/-- The cost constant of `tmValF`. -/
def tmValK : ℕ := 10 ^ 13

theorem tmRowVal_eq {m : ℕ} (gs : List (Perm (Fin m))) (c : C → ℕ) (z w : Fin m → C) :
    tmRowVal gs c z w = .list [.nat m, encGroup gs, tmOnes m,
      natList ((tmCodes c w).map (posOf (tmCodes c w ++ tmCodes c z))),
      natList ((tmCodes c z).map (posOf (tmCodes c w ++ tmCodes c z))),
      .list [], .list [], .nat 0, .nat 2, .nat m] := by
  simp only [tmRowVal, freshVal, tmOnes, tmCmp_eq, tmCodeList_eq]

/-- **The value of a call.** `W` is the weight of the input. -/
theorem tmVal_spec {P : Program} {f d ap : ℕ} (hf : P.funs[f]? = some (tmValBody ap (d + 9)))
    (hd : DomAt P d) (hap : P.HasAt ap (appendFuns ap)) {m : ℕ} (gs : List (Perm (Fin m)))
    (c : C → ℕ) (z w : Fin m → C) :
    FunDet P f (.list [encGroup gs, natList (tmCodes c z), natList (tmCodes c w), tmOnes m, .nat m])
      (tmRowVal gs c z w)
      (tmValK * ((Val.list [encGroup gs, natList (tmCodes c z), natList (tmCodes c w), tmOnes m,
        .nat m]).wt + 1) ^ 3) := by
  set zl := tmCodes c z
  set wl := tmCodes c w
  set L := wl ++ zl with hL
  set g := encGroup gs
  set inp := Val.list [g, natList zl, natList wl, tmOnes m, .nat m] with hinp
  set W := inp.wt with hW
  have hl : ∀ v ∈ [g, natList zl, natList wl, tmOnes m, .nat m], v.wt < W := fun v hv =>
    wt_le_wt_list hv
  have wg := hl g (by simp)
  have wz := hl (natList zl) (by simp)
  have ww := hl (natList wl) (by simp)
  have wo := hl (tmOnes m) (by simp)
  have wm := hl (.nat m) (by simp)
  have hmW : m < W := by
    have := length_lt_wt_list (List.replicate m (Val.nat 1))
    simp only [List.length_replicate] at this
    have : (Val.list (List.replicate m (Val.nat 1))).wt = (tmOnes m).wt := rfl
    omega
  have lz : zl.length = m := by simp [zl, tmCodes]
  have lw : wl.length = m := by simp [wl, tmCodes]
  have wL := wt_natList_append_le wl zl
  rw [← hL] at wL
  have a0 := Det.arg' (P := P) (vs := [g, natList zl, natList wl, tmOnes m, .nat m]) (rest := [])
    (j := 0) (v := g) rfl
  have a1 := Det.arg' (P := P) (vs := [g, natList zl, natList wl, tmOnes m, .nat m]) (rest := [])
    (j := 1) (v := natList zl) rfl
  have a2 := Det.arg' (P := P) (vs := [g, natList zl, natList wl, tmOnes m, .nat m]) (rest := [])
    (j := 2) (v := natList wl) rfl
  -- the concatenation
  have happ := append_spec hap (wl.map Val.nat) (zl.map Val.nat)
  have happ' : FunDet P ap (.list [natList wl, natList zl]) (natList L)
      (loopModK * (m + 1) * (12 * W + 12)) := by
    refine FunAll.mono happ fun v cv ⟨hv, hcv⟩ => ⟨?_, ?_⟩
    · rw [hv]; simp [natList, hL]
    · have e1 : v = natList L := by rw [hv]; simp [natList, hL]
      subst e1
      have := wt_list2_le (natList wl) (natList zl)
      have e2 : (Val.list [Val.list (wl.map Val.nat), Val.list (zl.map Val.nat)]) =
        (Val.list [natList wl, natList zl]) := rfl
      rw [e2, List.length_map, lz] at hcv
      refine hcv.trans (Nat.mul_le_mul_left _ ?_)
      omega
  have d1 := Det.call (Det.mk2 a2 a1) happ'
  -- the two compressed lists
  set env1 := [inp, natList L]
  have hA1 : (natList L).wt + (natList wl).wt ≤ 8 * W + 8 := by omega
  have hA2 : (natList L).wt + (natList zl).wt ≤ 8 * W + 8 := by omega
  have b1 := Det.arg' (P := P) (vs := [g, natList zl, natList wl, tmOnes m, .nat m])
    (rest := [natList L]) (j := 2) (v := natList wl) rfl
  have d2 := Det.call (Det.mk2 (Det.var' (P := P) (env := env1) (i := 1) rfl) b1)
    (mapPos_spec hd L wl hA1)
  set xr := natList (wl.map (posOf L))
  set env2 := [inp, natList L, xr]
  have b2 := Det.arg' (P := P) (vs := [g, natList zl, natList wl, tmOnes m, .nat m])
    (rest := [natList L, xr]) (j := 1) (v := natList zl) rfl
  have d3 := Det.call (Det.mk2 (Det.var' (P := P) (env := env2) (i := 1) rfl) b2)
    (mapPos_spec hd L zl hA2)
  set yr := natList (zl.map (posOf L))
  set env3 := [inp, natList L, xr, yr]
  -- the weights of the two compressed lists
  have hLl : L.length = 2 * m := by simp [hL, lz, lw]; ring
  have wxr : xr.wt ≤ m * (2 * (2 * m) + 5) + 4 := by
    refine (wt_natList_le (B := 2 * m) fun y hy => ?_).trans ?_
    · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy; exact (posOf_le _ z).trans hLl.le
    · simp [lw]
  have wyr : yr.wt ≤ m * (2 * (2 * m) + 5) + 4 := by
    refine (wt_natList_le (B := 2 * m) fun y hy => ?_).trans ?_
    · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy; exact (posOf_le _ z).trans hLl.le
    · simp [lz]
  have hmm : m * (2 * (2 * m) + 5) ≤ 9 * (W + 1) ^ 2 := by
    have : m * (2 * (2 * m) + 5) ≤ W * (4 * W + 5) := Nat.mul_le_mul hmW.le (by omega)
    nlinarith
  -- the output list
  have hpieces : ∀ p ∈ [(arg 4, Val.nat m), (arg 0, g), (arg 3, tmOnes m), (Expr.var 2, xr),
      (Expr.var 3, yr), (Expr.nil, Val.list []), (Expr.nil, Val.list []), (Expr.nat 0, Val.nat 0),
      (Expr.nat 2, Val.nat 2), (arg 4, Val.nat m)],
      Det P env3 p.1 p.2 (2 * W + 9 * (W + 1) ^ 2 + 20) := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have c4 := Det.arg' (P := P) (vs := [g, natList zl, natList wl, tmOnes m, .nat m])
      (rest := [natList L, xr, yr]) (j := 4) (v := .nat m) rfl
    have c0 := Det.arg' (P := P) (vs := [g, natList zl, natList wl, tmOnes m, .nat m])
      (rest := [natList L, xr, yr]) (j := 0) (v := g) rfl
    have c3 := Det.arg' (P := P) (vs := [g, natList zl, natList wl, tmOnes m, .nat m])
      (rest := [natList L, xr, yr]) (j := 3) (v := tmOnes m) rfl
    have hWi : (Val.list [g, natList zl, natList wl, tmOnes m, .nat m]).wt = W := rfl
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact c4.mono (by omega)
    · exact c0.mono (by omega)
    · exact c3.mono (by omega)
    · exact (Det.var' (P := P) (env := env3) (i := 2) rfl).mono (by omega)
    · exact (Det.var' (P := P) (env := env3) (i := 3) rfl).mono (by omega)
    · exact Det.nil.mono (by omega)
    · exact Det.nil.mono (by omega)
    · exact (Det.nat 0).mono (by omega)
    · exact (Det.nat 2).mono (by omega)
    · exact c4.mono (by omega)
  have d4 := Det.mkList _ hpieces
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at d4
  rw [tmRowVal_eq]
  refine FunDet.intro hf ((Det.letE d1 (Det.letE d2 (Det.letE d3 d4))).mono ?_)
  -- the cost
  set out := Val.list [.nat m, g, tmOnes m, xr, yr, .list [], .list [], .nat 0, .nat 2, .nat m]
  have wout : out.wt ≤ 2 * (4 * W + 2 * (9 * (W + 1) ^ 2) + 20) + 24 := by
    have := wt_list_le [.nat m, g, tmOnes m, xr, yr, .list [], .list [], .nat 0, .nat 2, .nat m]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    have : (Val.list []).wt ≤ 5 := by decide
    have : (Val.nat 0).wt ≤ 3 := by decide
    have : (Val.nat 2).wt ≤ 4 := by decide
    have : out.wt = (Val.list [.nat m, g, tmOnes m, xr, yr, .list [], .list [], .nat 0, .nat 2,
      .nat m]).wt := rfl
    omega
  have w2a := wt_list2_le (natList wl) (natList zl)
  have w2b := wt_list2_le (natList L) (natList wl)
  have w2c := wt_list2_le (natList L) (natList zl)
  have hY : 1 ≤ W + 1 := by omega
  have p12 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right hY (by omega)
  have q1 : (8 * W + 8 + 1) ^ 3 ≤ 9 ^ 3 * (W + 1) ^ 3 := pow_le_mul_pow 3 (by omega)
  have q2 : loopModK * (m + 1) * (12 * W + 12) ≤ loopModK * (W + 1) * (12 * (W + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have q3 : loopModK * (W + 1) * (12 * (W + 1)) = 12000 * (W + 1) ^ 2 := by
    simp only [loopModK]; ring
  have q4 : 10 * (2 * W + 9 * (W + 1) ^ 2 + 20 + out.wt + 1) + 5 ≤ 10 ^ 4 * (W + 1) ^ 2 := by
    omega
  have hw1 : (natList L).wt ≤ 8 * W + 8 := by omega
  simp only [tmValK] at *
  nlinarith

theorem wt_tmRowVal_le {m : ℕ} (gs : List (Perm (Fin m))) (c : C → ℕ) (z w : Fin m → C) :
    (tmRowVal gs c z w).wt ≤ 2 * (encGroup gs).wt + 50 * (m + 1) ^ 2 + 100 := by
  rw [tmRowVal_eq]
  have hLl : (tmCodes c w ++ tmCodes c z).length = 2 * m := by simp [tmCodes]; ring
  have hb : ∀ u : Fin m → C, (natList ((tmCodes c u).map (posOf (tmCodes c w ++ tmCodes c z)))).wt ≤
      m * (2 * (2 * m) + 5) + 4 := by
    intro u
    refine (wt_natList_le (B := 2 * m) fun y hy => ?_).trans ?_
    · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy; exact (posOf_le _ z).trans hLl.le
    · simp [tmCodes]
  have h1 := hb w
  have h2 := hb z
  have h3 := wt_tmOnes_le m
  have h4 := wt_nat_le m
  have := wt_list_le [.nat m, encGroup gs, tmOnes m,
      natList ((tmCodes c w).map (posOf (tmCodes c w ++ tmCodes c z))),
      natList ((tmCodes c z).map (posOf (tmCodes c w ++ tmCodes c z))),
      .list [], .list [], .nat 0, .nat 2, .nat m]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at this
  have : (Val.list []).wt ≤ 5 := by decide
  have : (Val.nat 0).wt ≤ 3 := by decide
  have : (Val.nat 2).wt ≤ 4 := by decide
  have : m * (2 * (2 * m) + 5) ≤ 5 * (m + 1) ^ 2 := by nlinarith
  have : m + 1 ≤ (m + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

/-! ### `tmAskF`: the value of the call on two rows -/

theorem tm_code_lt {k : ℕ} {c : C → ℕ} {S : State Ω C} {m q : ℕ} {E : Fin m × Fin q ≃ S.dom}
    (hcol : ∀ x, c (S.x x) < 2 * k ∧ c (S.y x) < 2 * k) (a : Fin q ⊕ Fin q) (b : Fin m) :
    c (tmRowStr S E a b) < 2 * k := by
  rcases a with i | i
  · exact (hcol _).1
  · exact (hcol _).2

/-- The body of `tmAskF` on `[ctx, sel, a, b]`, with `tmRowF` at `rw` and `tmValF` at `vf`. -/
def tmAskBody (rw vf : ℕ) : Expr :=
  .call vf (Expr.mkList [.get (arg 0) (arg 1), .call rw (mk2 (arg 0) (arg 2)),
    .call rw (mk2 (arg 0) (arg 3)), .get (arg 0) (.nat 5), .get (arg 0) (.nat 6)])

/-- The cost constant of `tmAskF`. -/
def tmAskK : ℕ := 10 ^ 20

/-- **The value of the call on rows `a` and `b`** under the group stored at entry `sel` of the
context. -/
theorem tmAsk_spec {P : Program} {f rw vf ga d ap : ℕ} (hf : P.funs[f]? = some (tmAskBody rw vf))
    (hrw : P.funs[rw]? = some (tmRowBody ga)) (hga : P.HasAt ga (gatherFuns ga))
    (hvf : P.funs[vf]? = some (tmValBody ap (d + 9))) (hd : DomAt P d)
    (hap : P.HasAt ap (appendFuns ap)) {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
    {m q : ℕ} (E : Fin m × Fin q ≃ S.dom) (gN gH : Val)
    (hcol : ∀ x, c (S.x x) < 2 * k ∧ c (S.y x) < 2 * k)
    (sel : ℕ) (gs : List (Perm (Fin m)))
    (hsel : [colVal e c S.x, colVal e c S.y, coordsVal e S E, gN, gH, tmOnes m, .nat m,
      .nat q][sel]? = some (encGroup gs)) (hs : sel ≤ 4)
    (a b : ℕ) (ha : a < 2 * q) (hb : b < 2 * q) :
    FunDet P f (.list [tmCtx (colVal e c S.x) (colVal e c S.y) (coordsVal e S E) gN gH m q,
        .nat sel, .nat a, .nat b])
      (tmRowVal gs c (tmRowStr S E (tmRowAt q a ha)) (tmRowStr S E (tmRowAt q b hb)))
      (tmAskK * ((tmCtx (colVal e c S.x) (colVal e c S.y) (coordsVal e S E) gN gH m q).wt + 1) ^ 6) := by
  set xv := colVal e c S.x
  set yv := colVal e c S.y
  set cv := coordsVal e S E
  set ctx := tmCtx xv yv cv gN gH m q with hctx
  set W := ctx.wt with hW
  set z := tmRowStr S E (tmRowAt q a ha)
  set w := tmRowStr S E (tmRowAt q b hb)
  have hl : ∀ v ∈ [xv, yv, cv, gN, gH, tmOnes m, .nat m, .nat q], v.wt < W := fun v hv =>
    wt_le_wt_list hv
  have wo := hl (tmOnes m) (by simp)
  have wm := hl (.nat m) (by simp)
  have wg : (encGroup gs).wt < W := hl _ (List.mem_of_getElem? hsel)
  have hmW : m < W := by
    have := length_lt_wt_list (List.replicate m (Val.nat 1))
    simp only [List.length_replicate] at this
    have : (Val.list (List.replicate m (Val.nat 1))).wt = (tmOnes m).wt := rfl
    omega
  have hqW : q < W := by
    have := length_lt_wt_list ((List.finRange q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))
    simp only [List.length_map, List.length_finRange] at this
    have : (coordsVal e S E).wt < W := hl cv (by simp)
    rw [coordsVal_eq_list] at this
    omega
  have hkW : k < W := by
    have := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (c (S.x (e.symm i))))
    simp only [List.length_map, List.length_finRange] at this
    have : (Val.list ((List.finRange k).map fun i => Val.nat (c (S.x (e.symm i))))).wt = xv.wt := rfl
    have := hl xv (by simp)
    omega
  have hiW : (Val.list [ctx, .nat sel, .nat a, .nat b]).wt ≤ 2 * (W + sel + 2 + a + 2 + b + 2) + 8 := by
    have := wt_list4_le ctx (.nat sel) (.nat a) (.nat b)
    have := wt_nat_le sel; have := wt_nat_le a; have := wt_nat_le b
    omega
  have hI : (Val.list [ctx, .nat sel, .nat a, .nat b]).wt ≤ 12 * W + 30 := by omega
  have dctx := Det.arg' (P := P) (vs := [ctx, .nat sel, .nat a, .nat b]) (rest := []) (j := 0)
    (v := ctx) rfl
  have dsel := Det.arg' (P := P) (vs := [ctx, .nat sel, .nat a, .nat b]) (rest := []) (j := 1)
    (v := .nat sel) rfl
  have da := Det.arg' (P := P) (vs := [ctx, .nat sel, .nat a, .nat b]) (rest := []) (j := 2)
    (v := .nat a) rfl
  have db := Det.arg' (P := P) (vs := [ctx, .nat sel, .nat a, .nat b]) (rest := []) (j := 3)
    (v := .nat b) rfl
  -- the codes of the two rows
  have hrowa : FunDet P rw (.list [ctx, .nat a]) (natList (tmCodes c z)) (tmRowK * (W + 1) ^ 3) :=
    tmRow_spec e c S E hrw hga gN gH hcol a ha
  have hrowb : FunDet P rw (.list [ctx, .nat b]) (natList (tmCodes c w)) (tmRowK * (W + 1) ^ 3) :=
    tmRow_spec e c S E hrw hga gN gH hcol b hb
  have wz := wt_tmCodes_le c (M := W) z hmW.le (fun x => (tm_code_lt hcol _ x).trans (by omega))
  have ww := wt_tmCodes_le c (M := W) w hmW.le (fun x => (tm_code_lt hcol _ x).trans (by omega))
  have wza : (Val.list [ctx, .nat a]).wt ≤ 2 * (W + a + 2) + 6 := by
    have := wt_list2_le ctx (.nat a); have := wt_nat_le a; omega
  have wzb : (Val.list [ctx, .nat b]).wt ≤ 2 * (W + b + 2) + 6 := by
    have := wt_list2_le ctx (.nat b); have := wt_nat_le b; omega
  set c0 := tmRowK * (W + 1) ^ 3 + 200 * (W + 1) ^ 2 with hc0
  have hY : 1 ≤ W + 1 := by omega
  have p12 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right hY (by omega)
  have p36 : (W + 1) ^ 3 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right hY (by omega)
  have hpieces : ∀ p ∈ [(Expr.get (arg 0) (arg 1), encGroup gs),
      (Expr.call rw (mk2 (arg 0) (arg 2)), natList (tmCodes c z)),
      (Expr.call rw (mk2 (arg 0) (arg 3)), natList (tmCodes c w)),
      (Expr.get (arg 0) (.nat 5), tmOnes m), (Expr.get (arg 0) (.nat 6), Val.nat m)],
      Det P [.list [ctx, .nat sel, .nat a, .nat b]] p.1 p.2 c0 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · refine (Det.get' dctx dsel (vs := [xv, yv, cv, gN, gH, tmOnes m, .nat m, .nat q]) hsel).mono ?_
      have := wt_nat_le sel
      omega
    · refine (Det.call (Det.mk2 dctx da) hrowa).mono ?_
      have := wt_nat_le a
      omega
    · refine (Det.call (Det.mk2 dctx db) hrowb).mono ?_
      have := wt_nat_le b
      omega
    · refine (Det.get' dctx (Det.nat 5) (vs := [xv, yv, cv, gN, gH, tmOnes m, .nat m, .nat q])
        (v := tmOnes m) rfl).mono ?_
      omega
    · refine (Det.get' dctx (Det.nat 6) (vs := [xv, yv, cv, gN, gH, tmOnes m, .nat m, .nat q])
        (v := .nat m) rfl).mono ?_
      omega
  have dl := Det.mkList _ hpieces
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at dl
  have hv := tmVal_spec hvf hd hap gs c z w
  set lv := Val.list [encGroup gs, natList (tmCodes c z), natList (tmCodes c w), tmOnes m, .nat m]
  have wlv : lv.wt ≤ 50 * (W + 1) ^ 2 := by
    have := wt_list_le [encGroup gs, natList (tmCodes c z), natList (tmCodes c w), tmOnes m, .nat m]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    have : lv.wt = (Val.list [encGroup gs, natList (tmCodes c z), natList (tmCodes c w), tmOnes m,
      .nat m]).wt := rfl
    omega
  refine FunDet.intro hf ((Det.call dl hv).mono ?_)
  have wout := wt_tmRowVal_le gs c z w
  have q1 : (lv.wt + 1) ^ 3 ≤ (51 * (W + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have q2 : (51 * (W + 1) ^ 2) ^ 3 = 51 ^ 3 * (W + 1) ^ 6 := by ring
  have q3 := Nat.mul_le_mul_left tmValK q1
  have hmm : (m + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  simp only [tmAskK, tmValK, tmRowK, hc0] at *
  omega

end GI.Impl
