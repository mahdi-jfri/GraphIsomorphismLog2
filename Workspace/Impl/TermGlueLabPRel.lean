module

public import Workspace.Impl.TermGlueLabPRelM
public import Workspace.Impl.LabelLift

@[expose] public section

/-!
# Reading `N`-transporters from the stored coset table: the program

Steps 2 and 3 of the label program (Theorem A.23: "constructive factorization in
the normalized product `N Aut_H(z_a)` supplies the required local `N`-transporter"). The
mathematics is `TermGlueLabPRelM`.

The module `tmGLPRelFuns b jm jf` (22 functions) runs on `[gens N, v, w]`, with `v` a stored
coset answer for `Iso_H(x_j, y_l)` and `w ∈ H` carrying a row `Z` to `y_l`:

1. if `v = []`, return `[]`;
2. else `v = [g, gens A]`: put `X = g⁻¹ w` and test `X ∈ ⟨A, 1, N⟩` (**Membership** at `jm`);
3. if the test fails, return `[]`; else factor `X = a m` with `a ∈ ⟨A⟩`, `m ∈ N`
   (**NormalizedFactor** at `jf`) and return `[w m⁻¹ w⁻¹]`.

`tmGLPRel_spec`: the result is `[]` when no element of `N` carries `x_j` to `Z`, and `[n]` with
`n ∈ N`, `x_j^n = Z` otherwise. No string-isomorphism call is made.
-/

namespace GI.Impl

open GI.Lang Equiv
open scoped GI.Multicoset
open GI.Cited (Val encPerm encGroup gens Membership NormalizedFactor)

/-! ### The program -/

/-- Step 3, on `[gens A, gens N, [X, w]]`: factor `X = a m`, return `[w m⁻¹ w⁻¹]`. -/
def tmGLPRel2F (comp inv jf : ℕ) : Expr :=
  .letE (.prim jf (mk3 (arg 0) (arg 1) (.get (arg 2) (.nat 0))))
    (mk1 (.call comp (mk2 (.call comp (mk2 (.get (arg 2) (.nat 1))
      (.call inv (.get (.var 1) (.nat 1))))) (.call inv (.get (arg 2) (.nat 1))))))

variable {n : ℕ}

/-- The cost bound of step 3, for an input of weight `W`. -/
def tmGLPRel2C (pf : Prim) (W : ℕ) : ℕ := pf.c * (6 * W + 12) ^ pf.k + 10 ^ 8 * (W + 1) ^ 4

theorem tmGLP_n_lt_wt (σ : Perm (Fin n)) : n < (encPerm σ).wt := by
  have := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (σ i))
  simpa [encPerm] using this

set_option maxHeartbeats 1000000 in
/-- **Step 3**: the factorization and the transporter `w m⁻¹ w⁻¹`. -/
theorem tmGLPRel2_spec (hfac : NormalizedFactor) {P : Program} {f comp inv jf : ℕ}
    (hf : P.funs[f]? = some (tmGLPRel2F comp inv jf)) (hc : P.HasAt comp (composeFuns comp))
    (hi : P.HasAt inv (invFuns inv)) (hj : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {A σN : List (Perm (Fin n))} (hnA : Normalizes (gens A) (gens σN)) {X w : Perm (Fin n)}
    (hX : ∃ a ∈ gens A, ∃ m ∈ gens σN, X = a * m) :
    FunAll P f (.list [encGroup A, encGroup σN, .list [encPerm X, encPerm w]]) (fun u c =>
      (∃ a ∈ gens A, ∃ m ∈ gens σN, X = a * m ∧ u = .list [encPerm (w * m⁻¹ * w⁻¹)]) ∧
      c ≤ tmGLPRel2C (normalizedFactorPrim hfac)
        (Val.list [encGroup A, encGroup σN, .list [encPerm X, encPerm w]]).wt) := by
  set XW : Val := .list [encPerm X, encPerm w] with hXW
  set a : Val := .list [encGroup A, encGroup σN, XW] with ha
  apply FunAll.intro hf
  have g0 := Det.arg' (P := P) (vs := [encGroup A, encGroup σN, XW]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [encGroup A, encGroup σN, XW]) (rest := []) (j := 1) rfl
  have g2 := Det.arg' (P := P) (vs := [encGroup A, encGroup σN, XW]) (rest := []) (j := 2) rfl
  have dX := Det.get' g2 (Det.nat 0) (vs := [encPerm X, encPerm w]) (v := encPerm X) rfl
  have da := Det.mk3 g0 g1 dX
  have hcall := normalizedFactor_call hfac hj da (G := gens A) (N := gens σN) ⟨A, rfl, rfl⟩
    ⟨σN, rfl, rfl⟩ hnA hX
  refine EvalAll.letE hcall fun v cv hv => ?_
  obtain ⟨⟨a', ha', m, hm, hXe, rfl⟩, hcv⟩ := hv
  set fv : Val := .list [encPerm a', encPerm m] with hfv
  have e2 := Det.arg' (P := P) (vs := [encGroup A, encGroup σN, XW]) (rest := [fv]) (j := 2) rfl
  have ew := Det.get' e2 (Det.nat 1) (vs := [encPerm X, encPerm w]) (v := encPerm w) rfl
  have ev := Det.var' (P := P) (env := [a, fv]) (i := 1) (v := fv) rfl
  have em := Det.get' ev (Det.nat 1) (vs := [encPerm a', encPerm m]) (v := encPerm m) rfl
  have dmi := Det.call em (inv_spec hi m)
  have dc1 := Det.call (Det.mk2 ew dmi) (compose_spec hc w m⁻¹)
  have dwi := Det.call ew (inv_spec hi w)
  have dc2 := Det.call (Det.mk2 dc1 dwi) (compose_spec hc (w * m⁻¹) w⁻¹)
  have dres := Det.mk1 dc2
  refine dres.post fun c hc' => ⟨⟨a', ha', m, hm, hXe, rfl⟩, ?_⟩
  -- the cost
  clear dres dc2 dwi dc1 dmi em ev ew e2 hcall da dX g0 g1 g2
  have hn := tmGLP_n_lt_wt w
  have wX := wt_encPerm_le X
  have ww := wt_encPerm_le w
  have wa' := wt_encPerm_le a'
  have wm := wt_encPerm_le m
  have wmi := wt_encPerm_le m⁻¹
  have wwi := wt_encPerm_le w⁻¹
  have wc1 := wt_encPerm_le (w * m⁻¹)
  have wc2 := wt_encPerm_le (w * m⁻¹ * w⁻¹)
  have ea : a.wt = (Val.list [encGroup A, encGroup σN, XW]).wt := rfl
  have efv : fv.wt = (Val.list [encPerm a', encPerm m]).wt := rfl
  have wXW : XW.wt < a.wt := wt_le_wt_list (by simp)
  have wA : (encGroup A).wt < a.wt := wt_le_wt_list (by simp)
  have wN : (encGroup σN).wt < a.wt := wt_le_wt_list (by simp)
  have wXa : (encPerm X).wt < XW.wt := wt_le_wt_list (by simp)
  have wwa : (encPerm w).wt < XW.wt := wt_le_wt_list (by simp)
  have l3 := wt_list3_le (encGroup A) (encGroup σN) (encPerm X)
  have l2 := wt_list2_le (encPerm a') (encPerm m)
  have l2a := wt_list2_le (encPerm w) (encPerm m⁻¹)
  have l2b := wt_list2_le (encPerm (w * m⁻¹)) (encPerm w⁻¹)
  have l1 := wt_list1_le (encPerm (w * m⁻¹ * w⁻¹))
  have hW : (Val.list [encGroup A, encGroup σN, encPerm X]).wt ≤ 6 * a.wt + 10 := by omega
  have hb := prim_bound_le_wt (normalizedFactorPrim hfac) hW
  clear_value a XW fv
  rw [← ea] at hc' hcv
  have n4 : (n + 1) ^ 4 ≤ (a.wt + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have n3 : (n + 1) ^ 3 ≤ (a.wt + 1) ^ 4 :=
    (Nat.pow_le_pow_left (show n + 1 ≤ a.wt + 1 by omega) 3).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have n2 : (n + 1) ^ 2 ≤ (a.wt + 1) ^ 4 :=
    (Nat.pow_le_pow_left (show n + 1 ≤ a.wt + 1 by omega) 2).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have w1 : a.wt + 1 ≤ (a.wt + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have e12 : 6 * a.wt + 10 + 2 = 6 * a.wt + 12 := rfl
  rw [e12] at hb
  unfold tmGLPRel2C
  simp only [invK, permK] at hc'
  omega

/-! ### The test -/

/-- Step 2, on `[gens N, [g, gens A], w]`: `X = g⁻¹ w`, the test `X ∈ ⟨A, 1, N⟩`, then step 3
at `r2`. -/
def tmGLPRel1F (r2 comp inv app jm : ℕ) : Expr :=
  .letE (.call comp (mk2 (.call inv (.get (arg 1) (.nat 0))) (arg 2)))
    (.letE (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 0))
        (.call app (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 1)) (.get (arg 0) (.nat 1)))))
      (.ite (.prim jm (mk2 (.var 2) (.var 1)))
        (.call r2 (mk3 (.get (arg 1) (.nat 1)) (arg 0) (mk2 (.var 1) (arg 2))))
        .nil))

/-- The entry, on `[gens N, v, w]`: `[]` for an empty coset `v`, else step 2. -/
def tmGLPRelF (r1 : ℕ) : Expr := .ite (.length (arg 1)) (.call r1 (.var 0)) .nil

/-- **The module** (22 functions): entry at `b`, **Membership** at `jm`, **NormalizedFactor**
at `jf`. -/
def tmGLPRelFuns (b jm jf : ℕ) : List Expr :=
  [tmGLPRelF (b + 1), tmGLPRel1F (b + 2) (b + 3) (b + 7) (b + 19) jm,
    tmGLPRel2F (b + 3) (b + 7) jf] ++ composeFuns (b + 3) ++ invFuns (b + 7) ++ appendFuns (b + 19)

theorem length_tmGLPRelFuns (b jm jf : ℕ) : (tmGLPRelFuns b jm jf).length = 22 := rfl

/-- The blocks of the module. -/
structure TmGLPRelAt (P : Program) (b jm jf : ℕ) : Prop where
  entry : P.funs[b]? = some (tmGLPRelF (b + 1))
  r1 : P.funs[b + 1]? = some (tmGLPRel1F (b + 2) (b + 3) (b + 7) (b + 19) jm)
  r2 : P.funs[b + 2]? = some (tmGLPRel2F (b + 3) (b + 7) jf)
  comp : P.HasAt (b + 3) (composeFuns (b + 3))
  inv : P.HasAt (b + 7) (invFuns (b + 7))
  app : P.HasAt (b + 19) (appendFuns (b + 19))

theorem tmGLPRelAt_of {P : Program} {b jm jf : ℕ} (h : P.HasAt b (tmGLPRelFuns b jm jf)) :
    TmGLPRelAt P b jm jf where
  entry := (h.block (gs := [tmGLPRelF (b + 1)]) 0 rfl).single
  r1 := (h.block (gs := [tmGLPRel1F (b + 2) (b + 3) (b + 7) (b + 19) jm]) 1 rfl).single
  r2 := (h.block (gs := [tmGLPRel2F (b + 3) (b + 7) jf]) 2 rfl).single
  comp := h.block 3 rfl
  inv := h.block 7 rfl
  app := h.block 19 rfl

/-- The weight of a concatenation. -/
theorem tmGLP_wt_append (xs ys : List Val) :
    (Val.list (xs ++ ys)).wt ≤ 3 * ((Val.list xs).wt + (Val.list ys).wt) + 4 := by
  have h := wt_list_le (xs ++ ys)
  have hx := sum_wt_lt_wt_list xs
  have hy := sum_wt_lt_wt_list ys
  have lx := length_lt_wt_list xs
  have ly := length_lt_wt_list ys
  simp only [List.map_append, List.sum_append, List.length_append] at h
  omega

/-- The value of the product group `⟨A, 1, σN⟩`. -/
theorem tmGLP_encGroup_append (A σN : List (Perm (Fin n))) :
    encGroup (A ++ 1 :: σN) =
      .list [.nat n, .list ((1 :: A).map encPerm ++ (1 :: σN).map encPerm)] := by
  simp [encGroup, GI.Cited.encPerms]

/-- The result relation of the module. -/
def TmGLPRelOut {Ω : Type*} [GI.Multicoset.RAct (Perm (Fin n)) Ω] (N : Subgroup (Perm (Fin n)))
    (X0 Z : Ω) (u : Val) : Prop :=
  (u = .list [] ∧ ∀ x ∈ N, X0 ↼ x ≠ Z) ∨ (∃ x ∈ N, u = .list [encPerm x] ∧ X0 ↼ x = Z)

/-- The cost bound of the module, for an input of weight `W`. -/
def tmGLPRelC (pm pf : Prim) (W : ℕ) : ℕ :=
  pm.c * (100 * (W + 1) ^ 2 + 2) ^ pm.k + 5 * tmGLPRel2C pf (30 * (W + 1) ^ 2) +
    10 ^ 9 * (W + 1) ^ 4

theorem tmGLPRel2C_mono (pf : Prim) {W V : ℕ} (h : W ≤ V) : tmGLPRel2C pf W ≤ tmGLPRel2C pf V := by
  unfold tmGLPRel2C; gcongr

set_option maxHeartbeats 2000000 in
/-- **Step 2**: on a nonempty stored coset `Iso_H(x_j, y_l) = g ⟨A⟩`, the test and the
transporter. -/
theorem tmGLPRel1_spec (hm : Membership) (hfac : NormalizedFactor) {P : Program} {b jm jf : ℕ}
    (h : TmGLPRelAt P b jm jf) (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {Ω : Type*} [GI.Multicoset.RAct (Perm (Fin n)) Ω] {H : Subgroup (Perm (Fin n))}
    {σN : List (Perm (Fin n))} (hNH : gens σN ≤ H) (hn : GI.Multicoset.Normalizes H (gens σN))
    {X0 Y Z : Ω} {g w : Perm (Fin n)} {A : List (Perm (Fin n))}
    (hI : GI.Multicoset.Iso H X0 Y = (fun k => g * k) '' (gens A : Set (Perm (Fin n))))
    (hw : w ∈ H) (hZ : Z ↼ w = Y) :
    FunAll P (b + 1) (.list [encGroup σN, .list [encPerm g, encGroup A], encPerm w])
      (fun u c => TmGLPRelOut (gens σN) X0 Z u ∧
        c ≤ tmGLPRelC (membershipPrim hm) (normalizedFactorPrim hfac)
          (Val.list [encGroup σN, .list [encPerm g, encGroup A], encPerm w]).wt) := by
  set gv : Val := .list [encPerm g, encGroup A] with hgv
  set a : Val := .list [encGroup σN, gv, encPerm w] with ha
  have hAH := (tmGLP_rel_le hI).2
  have hnA : Normalizes (gens A) (gens σN) := fun k hk x hx => hn k (hAH hk) x hx
  apply FunAll.intro h.r1
  -- `X = g⁻¹ w`
  have g1 := Det.arg' (P := P) (vs := [encGroup σN, gv, encPerm w]) (rest := []) (j := 1) rfl
  have g2 := Det.arg' (P := P) (vs := [encGroup σN, gv, encPerm w]) (rest := []) (j := 2) rfl
  have dg := Det.get' g1 (Det.nat 0) (vs := [encPerm g, encGroup A]) (v := encPerm g) rfl
  have dgi := Det.call dg (inv_spec h.inv g)
  have dX := Det.call (Det.mk2 dgi g2) (compose_spec h.comp g⁻¹ w)
  refine EvalAll.letE dX fun v cv hv => ?_
  obtain ⟨rfl, hcv⟩ := hv
  -- the product group `⟨A, 1, σN⟩`
  set xs := (1 :: A).map encPerm with hxs
  set ys := (1 :: σN).map encPerm with hys
  have k0 := Det.arg' (P := P) (vs := [encGroup σN, gv, encPerm w])
    (rest := [encPerm (g⁻¹ * w)]) (j := 0) rfl
  have k1 := Det.arg' (P := P) (vs := [encGroup σN, gv, encPerm w])
    (rest := [encPerm (g⁻¹ * w)]) (j := 1) rfl
  have kA := Det.get' k1 (Det.nat 1) (vs := [encPerm g, encGroup A]) (v := encGroup A) rfl
  have kn := Det.get' kA (Det.nat 0) (vs := [.nat n, .list xs]) (v := .nat n) rfl
  have kx := Det.get' kA (Det.nat 1) (vs := [.nat n, .list xs]) (v := .list xs) rfl
  have ky := Det.get' k0 (Det.nat 1) (vs := [.nat n, .list ys]) (v := .list ys) rfl
  have happ : FunAll P (b + 19) (.list [.list xs, .list ys]) (fun w' c => w' = .list (xs ++ ys) ∧
      c ≤ loopModK * (ys.length + 1) *
        ((Val.list [.list xs, .list ys]).wt + ys.length + (Val.list (xs ++ ys)).wt + 1)) :=
    FunAll.mono (append_spec h.app xs ys) fun w' c hw' => ⟨hw'.1, hw'.1 ▸ hw'.2⟩
  have kapp := Det.call (Det.mk2 kx ky) happ
  have kG := Det.mk2 kn kapp
  have eG : Val.list [.nat n, .list (xs ++ ys)] = encGroup (A ++ 1 :: σN) :=
    (tmGLP_encGroup_append A σN).symm
  rw [eG] at kG
  refine EvalAll.letE kG fun v cG hv => ?_
  obtain ⟨rfl, hcG⟩ := hv
  -- the membership test
  set GV := encGroup (A ++ 1 :: σN) with hGV
  have mG := Det.var' (P := P) (env := [a, encPerm (g⁻¹ * w), GV]) (i := 2) (v := GV) rfl
  have mX := Det.var' (P := P) (env := [a, encPerm (g⁻¹ * w), GV]) (i := 1)
    (v := encPerm (g⁻¹ * w)) rfl
  have hmem := membership_call hm hjm (Det.mk2 mG mX) (G := gens (A ++ 1 :: σN)) ⟨_, rfl, rfl⟩
  have hiff := tmGLP_rel_iff hNH hn hI hw hZ
  have hgens := tmGLP_rel_gens hnA (g⁻¹ * w)
  -- weights
  have wa : a.wt = (Val.list [encGroup σN, gv, encPerm w]).wt := rfl
  have wgv : gv.wt < a.wt := wt_le_wt_list (by simp)
  have wN : (encGroup σN).wt < a.wt := wt_le_wt_list (by simp)
  have wwa : (encPerm w).wt < a.wt := wt_le_wt_list (by simp)
  have wA : (encGroup A).wt < gv.wt := wt_le_wt_list (by simp)
  have wg : (encPerm g).wt < gv.wt := wt_le_wt_list (by simp)
  have wxs : (Val.list xs).wt < (encGroup A).wt :=
    wt_le_wt_list (by simp [hxs, encGroup, GI.Cited.encPerms])
  have wys : (Val.list ys).wt < (encGroup σN).wt :=
    wt_le_wt_list (by simp [hys, encGroup, GI.Cited.encPerms])
  have lys := length_lt_wt_list ys
  have wapp := tmGLP_wt_append xs ys
  have wnn := wt_nat_le n
  have hn1 := tmGLP_n_lt_wt w
  have l2xy := wt_list2_le (.list xs) (.list ys)
  have l2G := wt_list2_le (.nat n) (.list (xs ++ ys))
  have wGV : GV.wt ≤ 2 * ((Val.nat n).wt + (Val.list (xs ++ ys)).wt) + 6 := by
    rw [← eG]; exact l2G
  have wX := wt_encPerm_le (g⁻¹ * w)
  have wgi := wt_encPerm_le g⁻¹
  have l2m := wt_list2_le GV (encPerm (g⁻¹ * w))
  have n2' : (n + 1) ^ 2 ≤ (a.wt + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have a12 : a.wt + 1 ≤ (a.wt + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hbm := prim_bound_le_wt (membershipPrim hm)
    (show (Val.list [GV, encPerm (g⁻¹ * w)]).wt ≤ 100 * (a.wt + 1) ^ 2 by omega)
  -- common cost facts
  have n2 : (n + 1) ^ 2 ≤ (a.wt + 1) ^ 4 :=
    (Nat.pow_le_pow_left (show n + 1 ≤ a.wt + 1 by omega) 2).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have n3 : (n + 1) ^ 3 ≤ (a.wt + 1) ^ 4 :=
    (Nat.pow_le_pow_left (show n + 1 ≤ a.wt + 1 by omega) 3).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have n4 : (n + 1) ^ 4 ≤ (a.wt + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hyl : (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
      (Val.list (xs ++ ys)).wt + 1) ≤ 100 * (a.wt + 1) ^ 2 := by
    have : (Val.list [.list xs, .list ys]).wt + ys.length + (Val.list (xs ++ ys)).wt + 1 ≤
        20 * (a.wt + 1) := by omega
    have h2 : ys.length + 1 ≤ a.wt + 1 := by omega
    calc (ys.length + 1) * _ ≤ (a.wt + 1) * (20 * (a.wt + 1)) := Nat.mul_le_mul h2 this
      _ ≤ 100 * (a.wt + 1) ^ 2 := by nlinarith
  have q24 : (a.wt + 1) ^ 2 ≤ (a.wt + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q14 : a.wt + 1 ≤ (a.wt + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hyl' : loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
      (Val.list (xs ++ ys)).wt + 1) ≤ 10 ^ 5 * (a.wt + 1) ^ 2 := by
    rw [Nat.mul_assoc]; unfold loopModK; omega
  have l2g := wt_list2_le (encPerm g⁻¹) (encPerm w)
  have BX : cv ≤ 10 ^ 6 * (a.wt + 1) ^ 4 := by
    simp only [invK, permK] at hcv; omega
  have BG : cG ≤ 10 ^ 6 * (a.wt + 1) ^ 4 := by
    clear hcv BX; omega
  refine EvalAll.ite hmem (fun vc cc hc => ?_) (fun x cc hx => ?_)
  · rcases hc.1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  obtain ⟨hout, hcc⟩ := hx
  have Bcc : cc ≤ (membershipPrim hm).c * (100 * (a.wt + 1) ^ 2 + 2) ^ (membershipPrim hm).k +
      10 ^ 4 * (a.wt + 1) ^ 4 := by
    clear hcv hcG BX BG; omega
  rcases hout with ⟨he, hXm⟩ | ⟨he, hXn⟩
  · -- the test succeeds: factor and return the transporter
    cases he
    rw [if_neg one_ne_zero]
    have hX := (hgens.1 hXm)
    have r1 := Det.arg' (P := P) (vs := [encGroup σN, gv, encPerm w])
      (rest := [encPerm (g⁻¹ * w), GV]) (j := 1) rfl
    have rA := Det.get' r1 (Det.nat 1) (vs := [encPerm g, encGroup A]) (v := encGroup A) rfl
    have r0 := Det.arg' (P := P) (vs := [encGroup σN, gv, encPerm w])
      (rest := [encPerm (g⁻¹ * w), GV]) (j := 0) rfl
    have r2 := Det.arg' (P := P) (vs := [encGroup σN, gv, encPerm w])
      (rest := [encPerm (g⁻¹ * w), GV]) (j := 2) rfl
    have rX := Det.var' (P := P) (env := [a, encPerm (g⁻¹ * w), GV]) (i := 1)
      (v := encPerm (g⁻¹ * w)) rfl
    have rargs := Det.mk3 rA r0 (Det.mk2 rX r2)
    refine EvalAll.call_funAll rargs fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine FunAll.mono (FunAll.wt_lt (tmGLPRel2_spec hfac h.r2 h.comp h.inv hjf hnA hX))
      fun u cu hu => ⟨?_, ?_⟩
    · obtain ⟨⟨⟨a', ha', m, hm', hXe, rfl⟩, -⟩, -⟩ := hu
      have := tmGLP_rel_out hn hI hw hZ ha' hm' hXe
      exact Or.inr ⟨_, this.1, rfl, this.2⟩
    · obtain ⟨⟨-, hcu⟩, hwu⟩ := hu
      have l3 := wt_list3_le (encGroup A) (encGroup σN)
        (.list [encPerm (g⁻¹ * w), encPerm w])
      have l2 := wt_list2_le (encPerm (g⁻¹ * w)) (encPerm w)
      have hmono := tmGLPRel2C_mono (normalizedFactorPrim hfac)
        (show (Val.list [encGroup A, encGroup σN, .list [encPerm (g⁻¹ * w), encPerm w]]).wt ≤
          30 * (a.wt + 1) ^ 2 by omega)
      clear hmem hiff hgens kG kapp happ ky kx kn kA k0 k1 dX dgi dg g1 g2 rargs rX r2 r0 rA r1
        mG mX
      have Bca : ca ≤ 10 ^ 4 * (a.wt + 1) ^ 4 := by
        clear hcv hcG hcc hcu BX BG Bcc hmono; omega
      have Bcu : cu ≤ tmGLPRel2C (normalizedFactorPrim hfac) (30 * (a.wt + 1) ^ 2) := hcu.trans hmono
      unfold tmGLPRelC
      clear hcv hcG hcc hca hcu hmono
      omega
  · -- the test fails: no transporter
    cases he
    rw [if_pos rfl]
    refine (Det.nil (P := P)).post fun c hc => ⟨Or.inl ⟨rfl, ?_⟩, ?_⟩
    · intro x hx hxZ
      exact hXn (hgens.2 (hiff.1 ⟨x, hx, hxZ⟩))
    · clear hmem hiff hgens kG kapp happ ky kx kn kA k0 k1 dX dgi dg g1 g2 mG mX
      unfold tmGLPRelC
      have := Nat.zero_le (tmGLPRel2C (normalizedFactorPrim hfac) (30 * (a.wt + 1) ^ 2))
      clear hcv hcG hcc
      simp only [wt_list_nil] at hc ⊢
      omega

theorem tmGLPRelC_mono (pm pf : Prim) {W V : ℕ} (h : W ≤ V) :
    tmGLPRelC pm pf W ≤ tmGLPRelC pm pf V := by
  unfold tmGLPRelC tmGLPRel2C; gcongr

/-- **The module.** On `[gens N, v, w]`, with `v` a canonical answer for `Iso_H(x_j, y_l)`,
`w ∈ H` and `Z^w = y_l`, the result is `[]` when no element of `N` carries `x_j` to `Z`, and
`[n]` with `n ∈ N`, `x_j^n = Z` otherwise. It calls **Membership** once and
**NormalizedFactor** at most once, and makes no string-isomorphism call. -/
theorem tmGLPRel_spec (hm : Membership) (hfac : NormalizedFactor) {P : Program} {b jm jf : ℕ}
    (h : TmGLPRelAt P b jm jf) (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {Ω : Type*} [GI.Multicoset.RAct (Perm (Fin n)) Ω] {H : Subgroup (Perm (Fin n))}
    {σN : List (Perm (Fin n))} (hNH : gens σN ≤ H) (hn : GI.Multicoset.Normalizes H (gens σN))
    {X0 Y Z : Ω} {v : Val} (hv : AnsC (Equiv.refl (Fin n)) v (GI.Multicoset.Iso H X0 Y))
    {w : Perm (Fin n)} (hw : w ∈ H) (hZ : Z ↼ w = Y) :
    FunAll P b (.list [encGroup σN, v, encPerm w]) (fun u c => TmGLPRelOut (gens σN) X0 Z u ∧
      c ≤ 3 * tmGLPRelC (membershipPrim hm) (normalizedFactorPrim hfac)
        (Val.list [encGroup σN, v, encPerm w]).wt + 100 * (Val.list [encGroup σN, v, encPerm w]).wt +
          100) := by
  apply FunAll.intro h.entry
  have d1 := Det.arg' (P := P) (vs := [encGroup σN, v, encPerm w]) (rest := []) (j := 1) rfl
  rcases hv with ⟨rfl, hI⟩ | ⟨g, A, rfl, -, hI⟩
  · -- the empty coset
    have dl := Det.length d1
    refine (Det.ite_zero (t := .call (b + 1) (.var 0)) dl (Det.nil (P := P))).post
      fun c hc => ⟨Or.inl ⟨rfl, tmGLP_rel_empty hNH hI hw hZ⟩, ?_⟩
    simp only [List.length_nil, wt_list_nil] at hc
    omega
  · -- a nonempty coset
    rw [tmCs_toFin_refl] at hI
    have hI' : GI.Multicoset.Iso H X0 Y = (fun k => g * k) '' (gens A : Set (Perm (Fin n))) := hI
    have dl := Det.length d1
    refine EvalAll.ite dl (fun _ _ h => ⟨2, h.1⟩) fun y cc hy => ?_
    obtain ⟨h1, h2⟩ := hy
    cases h1
    rw [if_neg (by simp)]
    refine EvalAll.call_funAll (Det.var' (P := P) (env := [_]) (i := 0) rfl) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine FunAll.mono (FunAll.wt_lt (tmGLPRel1_spec hm hfac h hjm hjf hNH hn hI' hw hZ))
      fun u cu hu => ⟨hu.1.1, ?_⟩
    have hc := hu.1.2
    have hwt := hu.2
    simp only [List.length_cons, List.length_nil] at h2
    omega

end GI.Impl
