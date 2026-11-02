import Workspace.Impl.TermCosetFirst
import Workspace.Impl.Reduce

/-!
# The objects of the rows, built from the coset table

`tmCsObjXF` builds the object of the row `x_i`; `tmCsObjYF` builds the object of the row `y_j`.
They work on `[ctx, i]` with the context `ctx = [vs, σN, m, q]` (`tmCsCtx`): `vs` is the table
of the answers `Iso_H(x_i, y_j)` at position `i q + j`, each `[]` or `[g, gens of Aut_H(y_j)]`.

* Row `x_i`: `J` = the first `j` with a nonempty entry `[g, gs]` in row `i`; the object is
  `[J, ⟨gs, σN⟩, g⁻¹]` (`y_J^{g⁻¹} = x_i`).
* Row `y_j`: `I` = the first `i` with a nonempty entry in column `j`, `J` the first nonempty entry
  `[g, gs]` of row `I`, `[g', -]` the entry `(I, j)`; the object is `[J, ⟨gs, σN⟩, g⁻¹ g']`
  (`y_J^{g⁻¹ g'} = x_I^{g'} = y_j`).

The group `⟨gs, σN⟩` is cut to at most `m²` generators by the cited **PointwiseStab** with no
points (`red_spec`). The mathematics of these objects is in `TermCosetMath.lean`
(`tmCs_obj_eq`); here only the values are computed.
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encPerm encGroup gens PointwiseStab)

/-- The context of the object functions. -/
def tmCsCtx {m : ℕ} (vs : List Val) (σN : List (Perm (Fin m))) (q : ℕ) : Val :=
  .list [.list vs, .list (σN.map encPerm), .nat m, .nat q]

/-- An entry of the table has the shape of a canonical answer. -/
def TmCsShape (m : ℕ) (v : Val) : Prop :=
  v = .list [] ∨ ∃ (x : Perm (Fin m)) (gs : List (Perm (Fin m))),
    v = .list [encPerm x, encGroup gs] ∧ gs.length ≤ m ^ 2

/-- The entry `i q + j` of the table. -/
def TmCsTab {m : ℕ} (vs : List Val) (q : ℕ) : Prop :=
  vs.length = q * q ∧ ∀ i < q, ∀ j < q, ∃ v, vs[i * q + j]? = some v ∧ TmCsShape m v

/-- The body of the object of `x_i`, on `[ctx, i]`. -/
def tmCsObjXF (first app red inv : ℕ) : Expr :=
  .letE (.call first (mk2 (mk4 (.get (arg 0) (.nat 0))
      (.arith .mul (arg 1) (.get (arg 0) (.nat 3))) (.nat 1) (.get (arg 0) (.nat 3))) (.nat 0)))
  (.letE (.get (.get (arg 0) (.nat 0))
      (.arith .add (.arith .mul (arg 1) (.get (arg 0) (.nat 3))) (.var 1)))
  (.letE (.call app (mk2 (.get (.get (.var 2) (.nat 1)) (.nat 1)) (.get (arg 0) (.nat 1))))
  (.letE (.call red (mk2 (.get (arg 0) (.nat 2)) (mk2 (.get (arg 0) (.nat 2)) (.var 3))))
  (.letE (.call inv (.get (.var 2) (.nat 0)))
  (mk3 (.var 1) (.var 4) (.var 5))))))

/-- The cost bound of an object function, in a bound `X` of the weight of the context. -/
def tmCsObjK (p : Prim) (X : ℕ) : ℕ := 10 ^ 9 * (X + 1) ^ 10 + p.boundSize (30 * X + 100)

theorem tmCs_wt_ctx {m : ℕ} {vs : List Val} {σN : List (Perm (Fin m))} {q : ℕ} :
    (Val.list vs).wt < (tmCsCtx vs σN q).wt ∧ (Val.list (σN.map encPerm)).wt < (tmCsCtx vs σN q).wt ∧
      (Val.nat m).wt < (tmCsCtx vs σN q).wt ∧ (Val.nat q).wt < (tmCsCtx vs σN q).wt :=
  ⟨wt_le_wt_list (by simp), wt_le_wt_list (by simp), wt_le_wt_list (by simp),
    wt_le_wt_list (by simp)⟩

/-- **The object of `x_i`.** -/
theorem tmCs_objX_spec (hst : PointwiseStab) {P : Program} {fx first app red inv jst : ℕ}
    (hfx : P.funs[fx]? = some (tmCsObjXF first app red inv))
    (hfirst : P.funs[first]? = some (tmCsFirstF first)) (happ : P.HasAt app (appendFuns app))
    (hred : P.HasAt red (redFuns red jst)) (hinv : P.HasAt inv (invFuns inv))
    (hjst : P.prims[jst]? = some (pointwiseStabPrim hst))
    {m q : ℕ} {vs : List Val} {σN : List (Perm (Fin m))} (htab : TmCsTab (m := m) vs q)
    {X : ℕ} (hX : (tmCsCtx vs σN q).wt ≤ X) (hmX : m ≤ X) (hqX : q ≤ X)
    {i : ℕ} (hi : i < q) (hpart : ∃ j < q, ∃ a l, vs[i * q + j]? = some (.list (a :: l))) :
    FunAll P fx (.list [tmCsCtx vs σN q, .nat i]) (fun w cost =>
      ∃ (J : ℕ) (g : Perm (Fin m)) (gs hs : List (Perm (Fin m))),
        w = tmGlObjVal (J, hs, g⁻¹) ∧ J < q ∧
        (∀ j' < J, vs[i * q + j']? = some (.list [])) ∧
        vs[i * q + J]? = some (.list [encPerm g, encGroup gs]) ∧
        gens hs = gens (gs ++ σN) ∧ hs.length ≤ m ^ 2 ∧
        cost ≤ tmCsObjK (pointwiseStabPrim hst) X) := by
  obtain ⟨hvl, hsh⟩ := htab
  set c := tmCsCtx vs σN q with hc
  obtain ⟨wvs, wσ, wm, wq⟩ := tmCs_wt_ctx (vs := vs) (σN := σN) (q := q)
  rw [← hc] at wvs wσ wm wq
  -- the search
  have hl : ∀ j < q, ∃ l : List Val, vs[i * q + 1 * j]? = some (.list l) := by
    intro j hj
    obtain ⟨v, hv, hs⟩ := hsh i hi j hj
    rw [one_mul]
    rcases hs with rfl | ⟨x, gs, rfl, -⟩
    · exact ⟨[], hv⟩
    · exact ⟨_, hv⟩
  obtain ⟨J, hJ, -, hJq, hJe, hJn⟩ := tmCs_first_spec hfirst hl q 0 (by omega) (by omega)
  have hJq' : J < q := by
    by_contra hcon
    obtain ⟨j, hj, a', l', hj'⟩ := hpart
    have := hJe j (by omega) (by omega)
    rw [one_mul, hj'] at this
    cases this
  obtain ⟨a', l', hJv⟩ := hJn hJq'
  rw [one_mul] at hJv
  obtain ⟨v, hv, hvs⟩ := hsh i hi J hJq'
  rw [hJv] at hv
  cases hv
  obtain ⟨g, gs, hgv, hgl⟩ := hvs.resolve_left (by intro h; cases h)
  rw [hgv] at hJv
  clear hvs hgv a' l'
  have hidx : i * q + J < vs.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hJv; cases hJv
  have hentw : (Val.list [encPerm g, encGroup gs]).wt < (Val.list vs).wt := by
    have := wt_getElem_lt vs (i * q + J) hidx
    obtain ⟨_, he⟩ := List.getElem_of_getElem? hJv
    rwa [he] at this
  have hiq : i * q < q * q := Nat.mul_lt_mul_of_pos_right hi (by omega)
  have hlv := length_lt_wt_list vs
  refine FunAll.intro hfx ?_
  unfold tmCsObjXF
  -- 1. the search
  set a := Val.list [c, .nat i] with ha
  have hca : c.wt < a.wt := wt_le_wt_list (by simp [ha])
  have hiw : (Val.nat i).wt < a.wt := wt_le_wt_list (by simp [ha])
  have haw : a.wt ≤ 2 * (c.wt + (Val.nat i).wt) + 6 := wt_list2_le _ _
  have hiw' : (Val.nat i).wt ≤ (Val.nat q).wt := by
    rw [wt_nat, wt_nat]; have := GI.Machine.len_mono hi.le; omega
  have d0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 0) (v := c) rfl
  have d1 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 1) (v := .nat i) rfl
  have dvs := Det.get' d0 (Det.nat 0) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .list vs) rfl
  have dq := Det.get' d0 (Det.nat 3) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .nat q) rfl
  have diq := Det.arith' (op := .mul) d1 dq (z := i * q) rfl
  have dfc := Det.mk2 (Det.mk4 dvs diq (Det.nat 1) dq) (Det.nat 0)
  have dJ := Det.call dfc hJ
  refine EvalAll.letE dJ ?_
  rintro _ cJ ⟨rfl, hcJ⟩
  -- 2. the entry `[g, gs]`
  have e0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := [.nat J]) (j := 0) (v := c) rfl
  have e1 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := [.nat J]) (j := 1) (v := .nat i) rfl
  have evs := Det.get' e0 (Det.nat 0) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .list vs) rfl
  have eq := Det.get' e0 (Det.nat 3) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .nat q) rfl
  have eJ := Det.var' (P := P) (env := [a, .nat J]) (i := 1) (v := .nat J) rfl
  have eidx := Det.arith' (op := .add) (Det.arith' (op := .mul) e1 eq (z := i * q) rfl) eJ
    (z := i * q + J) rfl
  have ev := Det.get' evs eidx hJv
  refine EvalAll.letE ev ?_
  rintro _ cv ⟨rfl, hcv⟩
  -- 3. the generators of `Aut_H(y_J)` followed by those of `N`
  set ent := Val.list [encPerm g, encGroup gs] with hent
  have f0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := [.nat J, ent]) (j := 0) (v := c) rfl
  have fv := Det.var' (P := P) (env := [a, .nat J, ent]) (i := 2) (v := ent) rfl
  have fgs := Det.get' fv (Det.nat 1) (vs := [encPerm g, encGroup gs]) (v := encGroup gs) rfl
  have fl := Det.get' fgs (Det.nat 1)
    (vs := [.nat m, .list ((1 :: gs).map encPerm)]) (v := .list ((1 :: gs).map encPerm)) rfl
  have fσ := Det.get' f0 (Det.nat 1) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .list (σN.map encPerm)) rfl
  set L0 := Val.list ((1 :: gs).map encPerm ++ σN.map encPerm) with hL0
  have happ' : FunDet P app (.list [.list ((1 :: gs).map encPerm), .list (σN.map encPerm)]) L0
      (loopModK * ((σN.map encPerm).length + 1) *
        ((Val.list [.list ((1 :: gs).map encPerm), .list (σN.map encPerm)]).wt +
          (σN.map encPerm).length + L0.wt + 1)) :=
    (append_spec happ _ _).mono fun w c' ⟨h1, h2⟩ => ⟨h1, by rw [h1] at h2; exact h2⟩
  have fapp := Det.call (Det.mk2 fl fσ) happ'
  refine EvalAll.letE fapp ?_
  rintro _ cL ⟨rfl, hcL⟩
  -- 4. cut to at most `m²` generators
  have hgv : GroupVal m (.list [.nat m, L0]) (gens (gs ++ σN)) := ⟨gs ++ σN, by
    simp [hL0, encGroup, GI.Cited.encPerms], rfl⟩
  have g0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := [.nat J, ent, L0]) (j := 0) (v := c) rfl
  have gm := Det.get' g0 (Det.nat 2) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .nat m) rfl
  have gL := Det.var' (P := P) (env := [a, .nat J, ent, L0]) (i := 3) (v := L0) rfl
  refine EvalAll.letE (EvalAll.call_spec (Det.mk2 gm (Det.mk2 gm gL))
    (red_spec hst hred hjst hgv)) ?_
  rintro _ cR ⟨cbR, ⟨hs, rfl, hgens, hlen, hcbR⟩, hcR⟩
  -- 5. the representative `g⁻¹`
  have i2 := Det.var' (P := P) (env := [a, .nat J, ent, L0, encGroup hs]) (i := 2) (v := ent) rfl
  have ig := Det.get' i2 (Det.nat 0) (vs := [encPerm g, encGroup gs]) (v := encPerm g) rfl
  have dinv := Det.call ig (inv_spec hinv g)
  refine EvalAll.letE dinv ?_
  rintro _ cI ⟨rfl, hcI⟩
  have dout := Det.mk3 (Det.var' (P := P) (env := [a, .nat J, ent, L0, encGroup hs, encPerm g⁻¹])
    (i := 1) (v := .nat J) rfl)
    (Det.var' (P := P) (env := [a, .nat J, ent, L0, encGroup hs, encPerm g⁻¹]) (i := 4) rfl)
    (Det.var' (P := P) (env := [a, .nat J, ent, L0, encGroup hs, encPerm g⁻¹]) (i := 5) rfl)
  refine dout.post fun cO hcO => ⟨J, g, gs, hs, rfl, hJq', fun j' hj' => ?_, hJv, hgens, hlen, ?_⟩
  · have := hJe j' (by omega) hj'; rwa [one_mul] at this
  · -- the cost
    have hXw : (Val.list vs).wt < X := by omega
    have hqw : (Val.nat q).wt < X := by omega
    have hiw2 : (Val.nat i).wt < X := by omega
    have hA : (Val.list [c, Val.nat i]).wt ≤ 4 * X + 6 := by
      have := wt_list2_le c (Val.nat i); omega
    have hJw : (Val.nat J).wt < X := by
      have : (Val.nat J).wt ≤ (Val.nat q).wt := by
        rw [wt_nat, wt_nat]; have := GI.Machine.len_mono hJq; omega
      omega
    have hiqX : i * q + J < X := by omega
    have hentX : ent.wt < X := by omega
    have hgsw : (encGroup gs).wt < ent.wt := wt_le_wt_list (by simp [hent])
    have hgw : (encPerm g).wt < ent.wt := wt_le_wt_list (by simp [hent])
    have hl1w : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
      wt_le_wt_list (by simp [encGroup, GI.Cited.encPerms])
    have hσl := length_lt_wt_list (σN.map encPerm)
    have hσX : (Val.list (σN.map encPerm)).wt < X := by omega
    have hW4 : (Val.list [Val.list vs, Val.nat (i * q), Val.nat 1, Val.nat q]).wt ≤ 6 * X + 14 := by
      have := wt_list4_le (Val.list vs) (Val.nat (i * q)) (Val.nat 1) (Val.nat q)
      have := wt_nat_le (i * q)
      have : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
      omega
    have hW5 := wt_list2_le (Val.list [Val.list vs, Val.nat (i * q), Val.nat 1, Val.nat q]) (Val.nat 0)
    have hn0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    have hF : (q + 1) * tmCsFirstK (tmCsFirstCtx vs (i * q) 1 q).wt ≤ 4000 * (X + 1) ^ 2 := by
      have e : (tmCsFirstCtx vs (i * q) 1 q).wt =
          (Val.list [Val.list vs, Val.nat (i * q), Val.nat 1, Val.nat q]).wt := rfl
      calc (q + 1) * tmCsFirstK (tmCsFirstCtx vs (i * q) 1 q).wt
          ≤ (X + 1) * (4000 * (X + 1)) := by
            apply Nat.mul_le_mul (by omega)
            unfold tmCsFirstK; rw [e]; omega
        _ = 4000 * (X + 1) ^ 2 := by ring
    have hL0w : L0.wt ≤ 6 * X + 4 := by
      have h1 := wt_list_le ((1 :: gs).map encPerm ++ σN.map encPerm)
      have h2 := sum_wt_lt_wt_list ((1 :: gs).map encPerm)
      have h3 := sum_wt_lt_wt_list (σN.map encPerm)
      have h4 := length_lt_wt_list ((1 :: gs).map encPerm)
      rw [List.map_append, List.sum_append, List.length_append] at h1
      rw [hL0]
      omega
    have hP2 := wt_list2_le (Val.list ((1 :: gs).map encPerm)) (Val.list (σN.map encPerm))
    have hApp : loopModK * ((List.map encPerm σN).length + 1) *
        ((Val.list [Val.list ((1 :: gs).map encPerm), Val.list (σN.map encPerm)]).wt +
          (List.map encPerm σN).length + L0.wt + 1) ≤ 20000 * (X + 1) ^ 2 := by
      calc loopModK * ((List.map encPerm σN).length + 1) *
            ((Val.list [Val.list ((1 :: gs).map encPerm), Val.list (σN.map encPerm)]).wt +
              (List.map encPerm σN).length + L0.wt + 1)
          ≤ 1000 * (X + 1) * (20 * (X + 1)) := by
            apply Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
        _ = 20000 * (X + 1) ^ 2 := by ring
    have hmL := wt_list2_le (Val.nat m) L0
    have hmmL := wt_list2_le (Val.nat m) (Val.list [Val.nat m, L0])
    have hred' : (pointwiseStabPrim hst).bound (Val.list [Val.list [Val.nat m, L0], Val.list []]) ≤
        (pointwiseStabPrim hst).boundSize (30 * X + 100) := by
      apply Prim.bound_le
      have := (Val.list [Val.list [Val.nat m, L0], Val.list []]).size_le_wt
      have := wt_list2_le (Val.list [Val.nat m, L0]) (Val.list [])
      have : (Val.list []).wt ≤ 5 := by decide
      omega
    have hm1 : m + 1 ≤ X + 1 := by omega
    have p2 : (m + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left hm1 2
    have p4 : (m + 1) ^ 4 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_left hm1 4
    have p6 : (m + 1) ^ 6 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_left hm1 6
    have p9 : (m + 1) ^ 9 ≤ (X + 1) ^ 9 := Nat.pow_le_pow_left hm1 9
    have q2 : (X + 1) ^ 2 ≤ (X + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
    have q4 : (X + 1) ^ 4 ≤ (X + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
    have q6 : (X + 1) ^ 6 ≤ (X + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
    have q9 : (X + 1) ^ 9 ≤ (X + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
    have q1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have wg1 := wt_encPerm_le g
    have wg2 := wt_encPerm_le g⁻¹
    have wh := wt_encGroup_le_sq hlen
    have wout := wt_list3_le (Val.nat J) (encGroup hs) (encPerm g⁻¹)
    have bJ : cJ ≤ 500 * X + 1000 + 4000 * (X + 1) ^ 2 := by omega
    have bv : cv ≤ 500 * X + 1000 := by omega
    have bL : cL ≤ 500 * X + 1000 + 20000 * (X + 1) ^ 2 := by omega
    have bR : cR ≤ 500 * X + 1000 + (pointwiseStabPrim hst).boundSize (30 * X + 100) +
        10 ^ 7 * (X + 1) ^ 9 + 320 * (X + 1) ^ 6 := by omega
    have bI : cI ≤ 500 * X + 1000 + invK * (X + 1) ^ 4 + 8 * (X + 1) ^ 2 := by
      have := Nat.mul_le_mul_left invK p4; omega
    have q26 : (X + 1) ^ 2 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have bO : cO ≤ 500 * X + 1000 + 5000 * (X + 1) ^ 6 := by omega
    unfold tmCsObjK
    simp only [invK] at *
    omega

/-- The body of the object of `y_j`, on `[ctx, j]`: the first row `I` linked to `y_j`, the object
`[J, L, g⁻¹]` of `x_I`, and the representative `g⁻¹ g'` with `g'` the entry `(I, j)`. -/
def tmCsObjYF (first fx comp : ℕ) : Expr :=
  .letE (.call first (mk2 (mk4 (.get (arg 0) (.nat 0)) (arg 1) (.get (arg 0) (.nat 3))
      (.get (arg 0) (.nat 3))) (.nat 0)))
  (.letE (.call fx (mk2 (arg 0) (.var 1)))
  (.letE (.get (.get (arg 0) (.nat 0))
      (.arith .add (.arith .mul (.var 1) (.get (arg 0) (.nat 3))) (arg 1)))
  (mk3 (.get (.var 2) (.nat 0)) (.get (.var 2) (.nat 1))
    (.call comp (mk2 (.get (.var 2) (.nat 2)) (.get (.var 3) (.nat 0)))))))

/-- **The object of `y_j`.** -/
theorem tmCs_objY_spec (hst : PointwiseStab) {P : Program} {fy fx first app red inv comp jst : ℕ}
    (hfy : P.funs[fy]? = some (tmCsObjYF first fx comp))
    (hfx : P.funs[fx]? = some (tmCsObjXF first app red inv))
    (hfirst : P.funs[first]? = some (tmCsFirstF first)) (happ : P.HasAt app (appendFuns app))
    (hred : P.HasAt red (redFuns red jst)) (hinv : P.HasAt inv (invFuns inv))
    (hcomp : P.HasAt comp (composeFuns comp))
    (hjst : P.prims[jst]? = some (pointwiseStabPrim hst))
    {m q : ℕ} {vs : List Val} {σN : List (Perm (Fin m))} (htab : TmCsTab (m := m) vs q)
    {X : ℕ} (hX : (tmCsCtx vs σN q).wt ≤ X) (hmX : m ≤ X) (hqX : q ≤ X)
    {j : ℕ} (hj : j < q) (hpart : ∃ i < q, ∃ a l, vs[i * q + j]? = some (.list (a :: l))) :
    FunAll P fy (.list [tmCsCtx vs σN q, .nat j]) (fun w cost =>
      ∃ (I J : ℕ) (g g' : Perm (Fin m)) (gs gs' hs : List (Perm (Fin m))),
        w = tmGlObjVal (J, hs, g⁻¹ * g') ∧ I < q ∧
        (∀ i' < I, vs[i' * q + j]? = some (.list [])) ∧
        vs[I * q + j]? = some (.list [encPerm g', encGroup gs']) ∧ J < q ∧
        (∀ j' < J, vs[I * q + j']? = some (.list [])) ∧
        vs[I * q + J]? = some (.list [encPerm g, encGroup gs]) ∧
        gens hs = gens (gs ++ σN) ∧ hs.length ≤ m ^ 2 ∧
        cost ≤ 2 * tmCsObjK (pointwiseStabPrim hst) X) := by
  have htab' := htab
  obtain ⟨hvl, hsh⟩ := htab
  set c := tmCsCtx vs σN q with hc
  obtain ⟨wvs, wσ, wm, wq⟩ := tmCs_wt_ctx (vs := vs) (σN := σN) (q := q)
  rw [← hc] at wvs wσ wm wq
  have hl : ∀ i < q, ∃ l : List Val, vs[j + q * i]? = some (.list l) := by
    intro i hi
    obtain ⟨v, hv, hs⟩ := hsh i hi j hj
    rw [show j + q * i = i * q + j by ring]
    rcases hs with rfl | ⟨x, gs, rfl, -⟩
    · exact ⟨[], hv⟩
    · exact ⟨_, hv⟩
  obtain ⟨I, hI, -, hIq, hIe, hIn⟩ := tmCs_first_spec hfirst hl q 0 (by omega) (by omega)
  have hIq' : I < q := by
    by_contra hcon
    obtain ⟨i, hi, a', l', hi'⟩ := hpart
    have := hIe i (by omega) (by omega)
    rw [show j + q * i = i * q + j by ring, hi'] at this
    cases this
  obtain ⟨a', l', hIv⟩ := hIn hIq'
  rw [show j + q * I = I * q + j by ring] at hIv
  obtain ⟨v, hv, hvs⟩ := hsh I hIq' j hj
  rw [hIv] at hv
  cases hv
  obtain ⟨g', gs', hgv, hgl⟩ := hvs.resolve_left (by intro h; cases h)
  rw [hgv] at hIv
  clear hvs hgv
  have hidx : I * q + j < vs.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hIv; cases hIv
  have hentw : (Val.list [encPerm g', encGroup gs']).wt < (Val.list vs).wt := by
    have := wt_getElem_lt vs (I * q + j) hidx
    obtain ⟨_, he⟩ := List.getElem_of_getElem? hIv
    rwa [he] at this
  have hlv := length_lt_wt_list vs
  refine FunAll.intro hfy ?_
  unfold tmCsObjYF
  -- 1. the first row linked to `y_j`
  have hA : (Val.list [c, Val.nat j]).wt ≤ 4 * X + 6 := by
    have := wt_list2_le c (Val.nat j)
    have : (Val.nat j).wt ≤ (Val.nat q).wt := by
      rw [wt_nat, wt_nat]; have := GI.Machine.len_mono hj.le; omega
    omega
  have d0 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 0) (v := c) rfl
  have d1 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 1) (v := .nat j) rfl
  have dvs := Det.get' d0 (Det.nat 0) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .list vs) rfl
  have dq := Det.get' d0 (Det.nat 3) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .nat q) rfl
  have dfc := Det.mk2 (Det.mk4 dvs d1 dq dq) (Det.nat 0)
  refine EvalAll.letE (Det.call dfc hI) ?_
  rintro _ cI ⟨rfl, hcI⟩
  -- 2. the object of `x_I`
  have hpartI : ∃ j' < q, ∃ a l, vs[I * q + j']? = some (.list (a :: l)) :=
    ⟨j, hj, _, _, hIv⟩
  have e0 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := [.nat I]) (j := 0) (v := c) rfl
  have eI := Det.var' (P := P) (env := [.list [c, .nat j], .nat I]) (i := 1) (v := .nat I) rfl
  refine EvalAll.letE (EvalAll.call_spec (Det.mk2 e0 eI)
    (tmCs_objX_spec hst hfx hfirst happ hred hinv hjst htab' hX hmX hqX hIq' hpartI)) ?_
  rintro _ cX ⟨cbX, ⟨J, g, gs, hs, rfl, hJq, hJe, hJv, hgens, hlen, hcbX⟩, hcX⟩
  -- 3. the entry `(I, j)`
  set ob := tmGlObjVal (J, hs, g⁻¹) with hob
  have f0 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := [.nat I, ob]) (j := 0) (v := c) rfl
  have f1 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := [.nat I, ob]) (j := 1) (v := .nat j) rfl
  have fvs := Det.get' f0 (Det.nat 0) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .list vs) rfl
  have fq := Det.get' f0 (Det.nat 3) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .nat q) rfl
  have fI := Det.var' (P := P) (env := [.list [c, .nat j], .nat I, ob]) (i := 1) (v := .nat I) rfl
  have fidx := Det.arith' (op := .add) (Det.arith' (op := .mul) fI fq (z := I * q) rfl) f1
    (z := I * q + j) rfl
  refine EvalAll.letE (Det.get' fvs fidx hIv) ?_
  rintro _ cv ⟨rfl, hcv⟩
  -- 4. the object
  set ent := Val.list [encPerm g', encGroup gs'] with hent
  have o2 := Det.var' (P := P) (env := [.list [c, .nat j], .nat I, ob, ent]) (i := 2) (v := ob) rfl
  have o3 := Det.var' (P := P) (env := [.list [c, .nat j], .nat I, ob, ent]) (i := 3) (v := ent) rfl
  have oJ := Det.get' o2 (Det.nat 0) (vs := [.nat J, encGroup hs, encPerm g⁻¹]) (v := .nat J) rfl
  have oL := Det.get' o2 (Det.nat 1) (vs := [.nat J, encGroup hs, encPerm g⁻¹])
    (v := encGroup hs) rfl
  have og := Det.get' o2 (Det.nat 2) (vs := [.nat J, encGroup hs, encPerm g⁻¹])
    (v := encPerm g⁻¹) rfl
  have og' := Det.get' o3 (Det.nat 0) (vs := [encPerm g', encGroup gs']) (v := encPerm g') rfl
  have dcomp := Det.call (Det.mk2 og og') (compose_spec hcomp g⁻¹ g')
  refine (Det.mk3 oJ oL dcomp).post fun cO hcO =>
    ⟨I, J, g, g', gs, gs', hs, rfl, hIq', fun i' hi' => ?_, hIv, hJq, hJe, hJv, hgens, hlen, ?_⟩
  · have := hIe i' (by omega) hi'; rwa [show j + q * i' = i' * q + j by ring] at this
  · have hXw : (Val.list vs).wt < X := by omega
    have hqw : (Val.nat q).wt < X := by omega
    have hIw : (Val.nat I).wt < X := by
      have : (Val.nat I).wt ≤ (Val.nat q).wt := by
        rw [wt_nat, wt_nat]; have := GI.Machine.len_mono hIq; omega
      omega
    have hJw : (Val.nat J).wt < X := by
      have : (Val.nat J).wt ≤ (Val.nat q).wt := by
        rw [wt_nat, wt_nat]; have := GI.Machine.len_mono hJq.le; omega
      omega
    have hjw : (Val.nat j).wt < X := by
      have : (Val.nat j).wt ≤ (Val.nat q).wt := by
        rw [wt_nat, wt_nat]; have := GI.Machine.len_mono hj.le; omega
      omega
    have hAI : (Val.list [c, Val.nat I]).wt ≤ 4 * X + 6 := by
      have := wt_list2_le c (Val.nat I); omega
    have hiqX : I * q + j < X := by omega
    have hentX : ent.wt < X := by omega
    have hgw : (encPerm g').wt < ent.wt := wt_le_wt_list (by simp [hent])
    have hW4 : (Val.list [Val.list vs, Val.nat j, Val.nat q, Val.nat q]).wt ≤ 8 * X + 14 := by
      have := wt_list4_le (Val.list vs) (Val.nat j) (Val.nat q) (Val.nat q)
      omega
    have hW5 := wt_list2_le (Val.list [Val.list vs, Val.nat j, Val.nat q, Val.nat q]) (Val.nat 0)
    have hn0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    have hF : (q + 1) * tmCsFirstK (tmCsFirstCtx vs j q q).wt ≤ 4000 * (X + 1) ^ 2 := by
      have e : (tmCsFirstCtx vs j q q).wt =
          (Val.list [Val.list vs, Val.nat j, Val.nat q, Val.nat q]).wt := rfl
      calc (q + 1) * tmCsFirstK (tmCsFirstCtx vs j q q).wt
          ≤ (X + 1) * (4000 * (X + 1)) := by
            apply Nat.mul_le_mul (by omega)
            unfold tmCsFirstK; rw [e]; omega
        _ = 4000 * (X + 1) ^ 2 := by ring
    have hm1 : m + 1 ≤ X + 1 := by omega
    have p2 : (m + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left hm1 2
    have p3 : (m + 1) ^ 3 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_left hm1 3
    have p6 : (m + 1) ^ 6 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_left hm1 6
    have q2 : (X + 1) ^ 2 ≤ (X + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
    have q3 : (X + 1) ^ 3 ≤ (X + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
    have q6 : (X + 1) ^ 6 ≤ (X + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
    have q1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have wg1 := wt_encPerm_le g⁻¹
    have wg2 := wt_encPerm_le g'
    have wg3 := wt_encPerm_le (g⁻¹ * g')
    have wh := wt_encGroup_le_sq hlen
    have wob : ob.wt ≤ 2 * ((Val.nat J).wt + (encGroup hs).wt + (encPerm g⁻¹).wt) + 7 :=
      wt_list3_le _ _ _
    have wout := wt_list3_le (Val.nat J) (encGroup hs) (encPerm (g⁻¹ * g'))
    have wp2 := wt_list2_le (encPerm g⁻¹) (encPerm g')
    have hpk := Nat.mul_le_mul_left permK p3
    have q26 : (X + 1) ^ 2 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have bI : cI ≤ 500 * X + 1000 + 4000 * (X + 1) ^ 2 := by omega
    have bX : cX ≤ 500 * X + 1000 + cbX + 2000 * (X + 1) ^ 6 := by omega
    have bv : cv ≤ 500 * X + 1000 := by omega
    have bO : cO ≤ 10000 * (X + 1) ^ 6 + permK * (X + 1) ^ 3 := by omega
    have hK := tmCsObjK (pointwiseStabPrim hst) X
    unfold tmCsObjK at hcbX ⊢
    simp only [permK] at *
    omega

end GI.Impl
