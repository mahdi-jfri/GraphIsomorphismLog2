module

public import Workspace.Impl.TermCosetObj
public import Workspace.Lang.Lib.Search

@[expose] public section

/-!
# The lists of objects of the rows

`tmCsObjsF` works on the context `ctx = [vs, σN, m, q]` of `TermCosetObj.lean`. It first checks
that every row `x_i` has a nonempty entry in its row of the table and every row `y_j` has a
nonempty entry in its column (`tmCsPxF`, `tmCsPyF` with the library `all`). If some row has no
partner, the transporter of the types is empty (`tmCs_partner_x`, `tmCs_partner_y`), and the
function returns `[]`. Otherwise it returns `[OX, OY]`, the lists of the objects of the rows of
`x` and of `y` (`tmCsObjXF`, `tmCsObjYF` with the library `map`).
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encPerm encGroup gens PointwiseStab)

/-- Some entry `base + stride j`, `j < q`, of the table is a nonempty list. -/
def TmCsHas (vs : List Val) (base stride q : ℕ) : Prop :=
  ∃ j < q, ∃ (a : Val) (l : List Val), vs[base + stride * j]? = some (.list (a :: l))

/-- The partner test on `[ctx, i]`: is the first nonempty entry found before `q`? -/
def tmCsPF (first : ℕ) (bE sE : Expr) : Expr :=
  .arith .lt (.call first (mk2 (mk4 (.get (arg 0) (.nat 0)) bE sE (.get (arg 0) (.nat 3)))
    (.nat 0))) (.get (arg 0) (.nat 3))

/-- The partner test of the row `x_i`: base `i q`, stride `1`. -/
def tmCsPxF (first : ℕ) : Expr :=
  tmCsPF first (.arith .mul (arg 1) (.get (arg 0) (.nat 3))) (.nat 1)

/-- The partner test of the row `y_j`: base `j`, stride `q`. -/
def tmCsPyF (first : ℕ) : Expr := tmCsPF first (arg 1) (.get (arg 0) (.nat 3))

/-- The cost of a partner test. -/
def tmCsPK (X : ℕ) : ℕ := 10 ^ 4 * (X + 1) ^ 2

open Classical in
theorem tmCs_p_spec {P : Program} {p first : ℕ} {bE sE : Expr}
    (hp : P.funs[p]? = some (tmCsPF first bE sE))
    (hfirst : P.funs[first]? = some (tmCsFirstF first))
    {m q : ℕ} {vs : List Val} {σN : List (Perm (Fin m))} {i base stride : ℕ}
    {X cb cs : ℕ} (hX : (tmCsCtx vs σN q).wt ≤ X) (hqX : q ≤ X) (hiq : i < q)
    (hb : Det P [.list [tmCsCtx vs σN q, .nat i]] bE (.nat base) cb)
    (hs : Det P [.list [tmCsCtx vs σN q, .nat i]] sE (.nat stride) cs)
    (hcb : cb ≤ 20 * X + 40) (hcs : cs ≤ 20 * X + 40)
    (hbase : base ≤ X) (hstride : stride ≤ X)
    (hl : ∀ j < q, ∃ l : List Val, vs[base + stride * j]? = some (.list l)) :
    FunDet P p (.list [tmCsCtx vs σN q, .nat i])
      (boolVal (decide (TmCsHas vs base stride q))) (tmCsPK X) := by
  set c := tmCsCtx vs σN q with hc
  obtain ⟨wvs, wσ, wm, wq⟩ := tmCs_wt_ctx (vs := vs) (σN := σN) (q := q)
  rw [← hc] at wvs wσ wm wq
  obtain ⟨J, hJ, -, hJq, hJe, hJn⟩ := tmCs_first_spec hfirst hl q 0 (by omega) (by omega)
  have hiff : J < q ↔ TmCsHas vs base stride q := by
    constructor
    · intro h; obtain ⟨a, l, h'⟩ := hJn h; exact ⟨J, h, a, l, h'⟩
    · rintro ⟨j, hj, a, l, h'⟩
      by_contra hcon
      have := hJe j (by omega) (by omega)
      rw [h'] at this; cases this
  refine FunDet.intro hp ?_
  unfold tmCsPF
  have d0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 0) (v := c) rfl
  have dvs := Det.get' d0 (Det.nat 0) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .list vs) rfl
  have dq := Det.get' d0 (Det.nat 3) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .nat q) rfl
  have dfc := Det.mk2 (Det.mk4 dvs hb hs dq) (Det.nat 0)
  have dJ := Det.call dfc hJ
  have dlt := Det.arith' (op := .lt) dJ dq
    (z := (decide (TmCsHas vs base stride q)).toNat) (by
      by_cases h : TmCsHas vs base stride q
      · simp [GI.Machine.BinOp.eval, hiff.2 h, h]
      · have : ¬ J < q := fun h' => h (hiff.1 h')
        simp [GI.Machine.BinOp.eval, this, h])
  refine dlt.mono ?_
  have hA : (Val.list [c, Val.nat i]).wt ≤ 4 * X + 6 := by
    have := wt_list2_le c (Val.nat i)
    have : (Val.nat i).wt ≤ (Val.nat q).wt := by
      rw [wt_nat, wt_nat]; have := GI.Machine.len_mono hiq.le; omega
    omega
  have hmono : ∀ {a b : ℕ}, a ≤ b → (Val.nat a).wt ≤ (Val.nat b).wt := fun h => by
    rw [wt_nat, wt_nat]; have := GI.Machine.len_mono h; omega
  have hX1 : (Val.nat X).wt ≤ X + 2 := wt_nat_le X
  have w1 := hmono hbase
  have w2 := hmono hstride
  have w3 := hmono (show J ≤ X by omega)
  have hlv := length_lt_wt_list vs
  have hW4 := wt_list4_le (Val.list vs) (Val.nat base) (Val.nat stride) (Val.nat q)
  have hW5 := wt_list2_le (Val.list [Val.list vs, Val.nat base, Val.nat stride, Val.nat q])
    (Val.nat 0)
  have hn0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
  have hb3 : (Val.nat (decide (TmCsHas vs base stride q)).toNat).wt ≤ 3 :=
    wt_boolVal_le _
  have hF : (q + 1) * tmCsFirstK (tmCsFirstCtx vs base stride q).wt ≤ 4000 * (X + 1) ^ 2 := by
    have e : (tmCsFirstCtx vs base stride q).wt =
        (Val.list [Val.list vs, Val.nat base, Val.nat stride, Val.nat q]).wt := rfl
    calc (q + 1) * tmCsFirstK (tmCsFirstCtx vs base stride q).wt
        ≤ (X + 1) * (4000 * (X + 1)) := by
          apply Nat.mul_le_mul (by omega)
          unfold tmCsFirstK; rw [e]; omega
      _ = 4000 * (X + 1) ^ 2 := by ring
  have q1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  unfold tmCsPK
  have := Bool.toNat_le (decide (TmCsHas vs base stride q))
  omega

/-! ### The facts about the listed objects -/

/-- The facts about the object `o` of the row `x_i`, as computed by `tmCsObjXF`. -/
def TmCsXObj {m : ℕ} (vs : List Val) (σN : List (Perm (Fin m))) (q i : ℕ)
    (o : ℕ × List (Perm (Fin m)) × Perm (Fin m)) : Prop :=
  ∃ (g : Perm (Fin m)) (gs : List (Perm (Fin m))), o.2.2 = g⁻¹ ∧ o.1 < q ∧
    (∀ j' < o.1, vs[i * q + j']? = some (.list [])) ∧
    vs[i * q + o.1]? = some (.list [encPerm g, encGroup gs]) ∧
    gens o.2.1 = gens (gs ++ σN) ∧ o.2.1.length ≤ m ^ 2

/-- The facts about the object `o` of the row `y_j`, as computed by `tmCsObjYF`. -/
def TmCsYObj {m : ℕ} (vs : List Val) (σN : List (Perm (Fin m))) (q j : ℕ)
    (o : ℕ × List (Perm (Fin m)) × Perm (Fin m)) : Prop :=
  ∃ (I : ℕ) (g g' : Perm (Fin m)) (gs gs' : List (Perm (Fin m))), o.2.2 = g⁻¹ * g' ∧ I < q ∧
    (∀ i' < I, vs[i' * q + j]? = some (.list [])) ∧
    vs[I * q + j]? = some (.list [encPerm g', encGroup gs']) ∧ o.1 < q ∧
    (∀ j' < o.1, vs[I * q + j']? = some (.list [])) ∧
    vs[I * q + o.1]? = some (.list [encPerm g, encGroup gs]) ∧
    gens o.2.1 = gens (gs ++ σN) ∧ o.2.1.length ≤ m ^ 2

/-- A list of object values computed entrywise from `0, …, n - 1` comes from a list of
objects. -/
theorem tmCs_forall₂_objs {m : ℕ} {R : ℕ → ℕ × List (Perm (Fin m)) × Perm (Fin m) → Prop} :
    ∀ (l : List ℕ) (ws : List Val),
      List.Forall₂ (fun x w => ∃ i o, x = Val.nat i ∧ w = tmGlObjVal o ∧ R i o)
        (l.map Val.nat) ws →
      ∃ OX : List (ℕ × List (Perm (Fin m)) × Perm (Fin m)),
        ws = OX.map tmGlObjVal ∧ List.Forall₂ R l OX
  | [], ws, h => by
    rw [List.map_nil, List.forall₂_nil_left_iff] at h
    exact ⟨[], by simp [h], List.Forall₂.nil⟩
  | a :: l, ws, h => by
    rw [List.map_cons, List.forall₂_cons_left_iff] at h
    obtain ⟨w, ws', ⟨i, o, hi, rfl, hR⟩, h', rfl⟩ := h
    cases hi
    obtain ⟨OX, rfl, hOX⟩ := tmCs_forall₂_objs l ws' h'
    exact ⟨o :: OX, rfl, List.Forall₂.cons hR hOX⟩

theorem tmCs_forall₂_range {α : Type*} {R : ℕ → α → Prop} {q : ℕ} {OX : List α}
    (h : List.Forall₂ R (List.range q) OX) :
    ∃ hl : OX.length = q, ∀ i (hi : i < q), R i (OX[i]'(by omega)) := by
  have hl : OX.length = q := by rw [← h.length_eq, List.length_range]
  refine ⟨hl, fun i hi => ?_⟩
  have := (List.forall₂_iff_get.1 h).2 i (by simp [hi]) (by omega)
  simpa using this

open Classical in
/-- The test of the library `all` on the rows of `x`. -/
noncomputable def tmCsQx (vs : List Val) (q : ℕ) : Val → Bool
  | .nat i => decide (TmCsHas vs (i * q) 1 q)
  | _ => false

open Classical in
/-- The test of the library `all` on the rows of `y`. -/
noncomputable def tmCsQy (vs : List Val) (q : ℕ) : Val → Bool
  | .nat j => decide (TmCsHas vs j q q)
  | _ => false

theorem tmCs_all_range {Q : ℕ → Prop} [DecidablePred Q] {qf : Val → Bool} (hq : ∀ i, qf (.nat i) = decide (Q i))
    (q : ℕ) : ((List.range q).map Val.nat).all qf = true ↔ ∀ i < q, Q i := by
  simp [List.all_eq_true, hq]

/-- The body of the lists of objects, on `ctx`. -/
def tmCsObjsF (rg ax ay mx my : ℕ) : Expr :=
  .letE (.call rg (.get (.var 0) (.nat 3)))
  (.letE (.call ax (mk2 (.var 0) (.var 1)))
  (.letE (.call ay (mk2 (.var 0) (.var 1)))
  (.ite (.arith .mul (.var 2) (.var 3))
    (.letE (.call mx (mk2 (.var 0) (.var 1)))
    (.letE (.call my (mk2 (.var 0) (.var 1)))
    (mk2 (.var 4) (.var 5))))
    .nil)))

/-- The functions of the lists of objects. -/
structure TmCsObjsAt (P : Program) (f rg ax px ay py mx fx my fy first app red inv comp jst : ℕ) :
    Prop where
  hf : P.funs[f]? = some (tmCsObjsF rg ax ay mx my)
  hrg : P.HasAt rg (rangeFuns rg)
  hax : P.HasAt ax (allFuns ax px)
  hpx : P.funs[px]? = some (tmCsPxF first)
  hay : P.HasAt ay (allFuns ay py)
  hpy : P.funs[py]? = some (tmCsPyF first)
  hmx : P.HasAt mx (mapFuns mx fx)
  hfx : P.funs[fx]? = some (tmCsObjXF first app red inv)
  hmy : P.HasAt my (mapFuns my fy)
  hfy : P.funs[fy]? = some (tmCsObjYF first fx comp)
  hfirst : P.funs[first]? = some (tmCsFirstF first)
  happ : P.HasAt app (appendFuns app)
  hred : P.HasAt red (redFuns red jst)
  hinv : P.HasAt inv (invFuns inv)
  hcomp : P.HasAt comp (composeFuns comp)

/-- The cost bound of the lists of objects. -/
def tmCsObjsK (p : Prim) (X : ℕ) : ℕ := 10 ^ 7 * (X + 1) ^ 3 * tmCsObjK p X

/-- **The lists of objects.** -/
theorem tmCs_objs_spec (hst : PointwiseStab) {P : Program}
    {f rg ax px ay py mx fx my fy first app red inv comp jst : ℕ}
    (hA : TmCsObjsAt P f rg ax px ay py mx fx my fy first app red inv comp jst)
    (hjst : P.prims[jst]? = some (pointwiseStabPrim hst))
    {m q : ℕ} {vs : List Val} {σN : List (Perm (Fin m))} (htab : TmCsTab (m := m) vs q)
    {X : ℕ} (hX : (tmCsCtx vs σN q).wt ≤ X) (hmX : m ≤ X) (hqX : q ≤ X) :
    FunAll P f (tmCsCtx vs σN q) (fun w cost =>
      ((((∀ i < q, TmCsHas vs (i * q) 1 q) ∧ (∀ j < q, TmCsHas vs j q q)) ∧
        ∃ OX OY : List (ℕ × List (Perm (Fin m)) × Perm (Fin m)),
          w = .list [tmGlObjsVal OX, tmGlObjsVal OY] ∧
          ∃ (hx : OX.length = q) (hy : OY.length = q),
          (∀ i (hi : i < q), TmCsXObj vs σN q i (OX[i]'(by omega))) ∧
          (∀ j (hj : j < q), TmCsYObj vs σN q j (OY[j]'(by omega)))) ∨
      (w = .list [] ∧ ¬((∀ i < q, TmCsHas vs (i * q) 1 q) ∧ (∀ j < q, TmCsHas vs j q q)))) ∧
      cost ≤ tmCsObjsK (pointwiseStabPrim hst) X) := by
  classical
  have htab' := htab
  obtain ⟨hvl, hsh⟩ := htab
  set c := tmCsCtx vs σN q with hc
  obtain ⟨wvs, wσ, wm, wq⟩ := tmCs_wt_ctx (vs := vs) (σN := σN) (q := q)
  rw [← hc] at wvs wσ wm wq
  have hlv := length_lt_wt_list vs
  have hqq : q * q < X := by omega
  set K := tmCsObjK (pointwiseStabPrim hst) X with hK
  have hK1 : 1 ≤ K := by
    rw [hK]; unfold tmCsObjK; have := Nat.one_le_pow 10 (X + 1) (by omega); nlinarith
  set xs := (List.range q).map Val.nat with hxs
  have hxsl : xs.length = q := by simp [hxs]
  have hxsw : (Val.list xs).wt ≤ 5 * (X + 1) ^ 2 := by
    have := wt_natList_le_sq (xs := List.range q) (B := X)
      (fun x hx => by rw [List.mem_range] at hx; omega) (by simp; omega)
    exact this.trans (Nat.mul_le_mul_left _ (by omega))
  have hcx : (Val.list [c, .list xs]).wt ≤ 2 * X + 10 * (X + 1) ^ 2 + 6 := by
    have := wt_list2_le c (.list xs); omega
  have hrow : ∀ i < q, ∀ base stride, (∀ j < q, base + stride * j = i * q + j) →
      ∀ j < q, ∃ l : List Val, vs[base + stride * j]? = some (.list l) := by
    intro i hi base stride he j hj
    obtain ⟨v, hv, hs⟩ := hsh i hi j hj
    rw [he j hj]
    rcases hs with rfl | ⟨x, gs, rfl, -⟩
    · exact ⟨[], hv⟩
    · exact ⟨_, hv⟩
  refine FunAll.intro hA.hf ?_
  unfold tmCsObjsF
  -- the list `0, …, q - 1`
  have d0 := Det.var' (P := P) (env := [c]) (i := 0) (v := c) rfl
  have dq := Det.get' d0 (Det.nat 3) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
    (v := .nat q) rfl
  refine EvalAll.letE (EvalAll.call_spec dq (range_spec hA.hrg q)) ?_
  rintro _ cR ⟨cbR, ⟨rfl, hcbR⟩, hcR⟩
  -- the partner tests
  have hpx : ∀ x ∈ xs, FunDet P px (.list [c, x]) (boolVal (tmCsQx vs q x)) (tmCsPK X) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hi
    have e0 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 0) (v := c) rfl
    have e1 := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 1) (v := .nat i) rfl
    have eq := Det.get' e0 (Det.nat 3) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
      (v := .nat q) rfl
    have hb := Det.arith' (op := .mul) e1 eq (z := i * q) rfl
    have hA2 : (Val.list [c, Val.nat i]).wt ≤ 4 * X + 6 := by
      have := wt_list2_le c (Val.nat i)
      have : (Val.nat i).wt ≤ (Val.nat q).wt := by
        rw [wt_nat, wt_nat]; have := GI.Machine.len_mono hi.le; omega
      omega
    have hiq : i * q < q * q := Nat.mul_lt_mul_of_pos_right hi (by omega)
    have := tmCs_p_spec (P := P) (p := px) (first := first) hA.hpx hA.hfirst (σN := σN)
      (i := i) (base := i * q) (stride := 1) hX hqX hi hb (Det.nat 1) (by omega)
      (by have := wt_nat_le 1; omega) (by omega) (by omega)
      (hrow i hi (i * q) 1 (fun j _ => by ring))
    simpa [tmCsQx] using this
  have hpy : ∀ x ∈ xs, FunDet P py (.list [c, x]) (boolVal (tmCsQy vs q x)) (tmCsPK X) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hj
    have e0 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 0) (v := c) rfl
    have e1 := Det.arg' (P := P) (vs := [c, .nat j]) (rest := []) (j := 1) (v := .nat j) rfl
    have eq := Det.get' e0 (Det.nat 3) (vs := [.list vs, .list (σN.map encPerm), .nat m, .nat q])
      (v := .nat q) rfl
    have hA2 : (Val.list [c, Val.nat j]).wt ≤ 4 * X + 6 := by
      have := wt_list2_le c (Val.nat j)
      have : (Val.nat j).wt ≤ (Val.nat q).wt := by
        rw [wt_nat, wt_nat]; have := GI.Machine.len_mono hj.le; omega
      omega
    have hl : ∀ i < q, ∃ l : List Val, vs[j + q * i]? = some (.list l) := by
      intro i hi
      obtain ⟨v, hv, hs⟩ := hsh i hi j hj
      rw [show j + q * i = i * q + j by ring]
      rcases hs with rfl | ⟨x, gs, rfl, -⟩
      · exact ⟨[], hv⟩
      · exact ⟨_, hv⟩
    have := tmCs_p_spec (P := P) (p := py) (first := first) hA.hpy hA.hfirst (σN := σN)
      (i := j) (base := j) (stride := q) hX hqX hj e1 eq (by omega) (by omega) (by omega)
      (by omega) hl
    simpa [tmCsQy] using this
  have hQx := tmCs_all_range (Q := fun i => TmCsHas vs (i * q) 1 q) (qf := tmCsQx vs q)
    (fun i => rfl) q
  have hQy := tmCs_all_range (Q := fun j => TmCsHas vs j q q) (qf := tmCsQy vs q)
    (fun j => rfl) q
  have a0 := Det.var' (P := P) (env := [c, .list xs]) (i := 0) (v := c) rfl
  have a1 := Det.var' (P := P) (env := [c, .list xs]) (i := 1) (v := .list xs) rfl
  refine EvalAll.letE (EvalAll.call_spec (Det.mk2 a0 a1) (all_spec hA.hax hpx)) ?_
  rintro _ cX ⟨cbX, ⟨rfl, hcbX⟩, hcX⟩
  set bx := xs.all (tmCsQx vs q) with hbx
  have b0 := Det.var' (P := P) (env := [c, .list xs, boolVal bx]) (i := 0) (v := c) rfl
  have b1 := Det.var' (P := P) (env := [c, .list xs, boolVal bx]) (i := 1) (v := .list xs) rfl
  refine EvalAll.letE (EvalAll.call_spec (Det.mk2 b0 b1) (all_spec hA.hay hpy)) ?_
  rintro _ cY ⟨cbY, ⟨rfl, hcbY⟩, hcY⟩
  set bY := xs.all (tmCsQy vs q) with hbY
  -- the costs so far
  have hsumP : ∀ (l : List Val), (l.map fun _ => tmCsPK X).sum = l.length * tmCsPK X := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  rw [hsumP, hxsl] at hcbX hcbY
  have hY1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY2 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hqP : q * tmCsPK X ≤ 10 ^ 4 * (X + 1) ^ 3 := by
    unfold tmCsPK
    calc q * (10 ^ 4 * (X + 1) ^ 2) ≤ (X + 1) * (10 ^ 4 * (X + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 4 * (X + 1) ^ 3 := by ring
  have hloop : ∀ {W : ℕ}, W ≤ 20 * (X + 1) ^ 2 → loopModK * (q + 1) * W ≤ 20000 * (X + 1) ^ 3 := by
    intro W hW
    calc loopModK * (q + 1) * W ≤ 1000 * (X + 1) * (20 * (X + 1) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) hW
      _ = 20000 * (X + 1) ^ 3 := by ring
  have hqw : (Val.nat q).wt ≤ X + 2 := (wt_nat_le q).trans (by omega)
  have hbxw := wt_boolVal_le bx
  have hbyw := wt_boolVal_le bY
  have hR1 := hloop (W := (Val.nat q).wt + q + (Val.list xs).wt + 1) (by omega)
  have hX1 := hloop (W := (Val.list [c, .list xs]).wt + xs.length + 4) (by rw [hxsl]; omega)
  have hc2 := wt_list2_le c (.list xs)
  have hcR' : cR ≤ 30 * X + 30 * (X + 1) ^ 2 + 20000 * (X + 1) ^ 3 + 100 := by
    have hs_eq : (natList (List.range q)).wt = (Val.list xs).wt := rfl
    rw [hs_eq] at hcR hcbR
    have := hcbR.trans hR1; omega
  have hcX' : cX ≤ 30 * X + 30 * (X + 1) ^ 2 + 40000 * (X + 1) ^ 3 + 100 := by
    rw [hxsl] at hX1; omega
  have hcY' : cY ≤ 30 * X + 30 * (X + 1) ^ 2 + 40000 * (X + 1) ^ 3 + 100 := by
    rw [hxsl] at hX1; omega
  -- the map cost
  have hY3K : (X + 1) ^ 3 ≤ (X + 1) ^ 3 * K := Nat.le_mul_of_pos_right _ (by omega)
  have hmapc : ∀ {W : ℕ}, W ≤ 20 * (X + 1) ^ 2 + 5 * (X + 1) * K →
      mapK * (q + 1) * W ≤ 30000 * ((X + 1) ^ 3 * K) := by
    intro W hW
    have h2 : (X + 1) * ((X + 1) * K) ≤ (X + 1) ^ 3 * K := by
      have : (X + 1) * ((X + 1) * K) = (X + 1) ^ 2 * K := by ring
      rw [this]; exact Nat.mul_le_mul_right _ hY2
    calc mapK * (q + 1) * W ≤ 1000 * (X + 1) * (20 * (X + 1) ^ 2 + 5 * (X + 1) * K) :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) hW
      _ = 20000 * (X + 1) ^ 3 + 5000 * ((X + 1) * ((X + 1) * K)) := by ring
      _ ≤ 30000 * ((X + 1) ^ 3 * K) := by omega
  have hqK : q * K ≤ (X + 1) ^ 3 * K := by
    have : q ≤ (X + 1) ^ 3 := by
      have := Nat.le_self_pow (show 3 ≠ 0 by norm_num) (X + 1); omega
    exact Nat.mul_le_mul_right _ this
  have hXK : X * (4 * K + 1) ≤ 5 * (X + 1) * K := by nlinarith
  -- the test
  have t2 := Det.var' (P := P) (env := [c, .list xs, boolVal bx, boolVal bY]) (i := 2) rfl
  have t3 := Det.var' (P := P) (env := [c, .list xs, boolVal bx, boolVal bY]) (i := 3) rfl
  have dt := Det.arith' (op := .mul) t2 t3 (z := bx.toNat * bY.toNat) rfl
  refine EvalAll.ite dt (fun _ _ h => ⟨_, h.1⟩) fun z cz ⟨hz, hcz⟩ => ?_
  cases hz
  have hiff : bx.toNat * bY.toNat ≠ 0 ↔
      ((∀ i < q, TmCsHas vs (i * q) 1 q) ∧ (∀ j < q, TmCsHas vs j q q)) := by
    rw [← hQx, ← hQy]
    cases bx <;> cases bY <;> simp
  have hbw : (boolVal bx).wt + (boolVal bY).wt ≤ 6 := by omega
  by_cases h0 : bx.toNat * bY.toNat = 0
  · -- some row has no partner
    rw [if_pos h0]
    refine Det.nil.post fun c' hc' => ⟨Or.inr ⟨rfl, fun h => (hiff.2 h) h0⟩, ?_⟩
    have : (Val.list []).wt ≤ 5 := by decide
    have hz3 : bx.toNat * bY.toNat ≤ 1 := by cases bx <;> cases bY <;> simp
    unfold tmCsObjsK
    have h7 : 10 ^ 6 * (X + 1) ^ 3 ≤ 10 ^ 7 * (X + 1) ^ 3 * K := by
      calc 10 ^ 6 * (X + 1) ^ 3 ≤ 10 ^ 6 * ((X + 1) ^ 3 * K) := Nat.mul_le_mul_left _ hY3K
        _ ≤ 10 ^ 7 * ((X + 1) ^ 3 * K) := Nat.mul_le_mul_right _ (by norm_num)
        _ = 10 ^ 7 * (X + 1) ^ 3 * K := by ring
    rw [← hK]
    omega
  rw [if_neg h0]
  obtain ⟨hallx, hally⟩ := hiff.1 h0
  -- the objects of the rows of `x`
  have hfx : ∀ x ∈ xs, FunAll P fx (.list [c, x]) (fun w cost =>
      ((∃ i o, x = Val.nat i ∧ w = tmGlObjVal o ∧ TmCsXObj vs σN q i o) ∧ w.wt ≤ K) ∧
        cost ≤ K) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hi
    obtain ⟨j, hj, a, l, hal⟩ := hallx i hi
    rw [one_mul] at hal
    refine ((tmCs_objX_spec hst hA.hfx hA.hfirst hA.happ hA.hred hA.hinv hjst htab' hX hmX hqX
      hi ⟨j, hj, a, l, hal⟩).wt_lt).mono ?_
    rintro w cost ⟨⟨J, g, gs, hs, rfl, hJ, hJe, hJv, hgens, hlen, hcost⟩, hwt⟩
    exact ⟨⟨⟨i, (J, hs, g⁻¹), rfl, rfl, g, gs, rfl, hJ, hJe, hJv, hgens, hlen⟩, by omega⟩, hcost⟩
  have hfy : ∀ x ∈ xs, FunAll P fy (.list [c, x]) (fun w cost =>
      ((∃ j o, x = Val.nat j ∧ w = tmGlObjVal o ∧ TmCsYObj vs σN q j o) ∧ w.wt ≤ 2 * K) ∧
        cost ≤ 2 * K) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hj
    obtain ⟨i, hi, a, l, hal⟩ := hally j hj
    rw [show j + q * i = i * q + j by ring] at hal
    refine ((tmCs_objY_spec hst hA.hfy hA.hfx hA.hfirst hA.happ hA.hred hA.hinv hA.hcomp hjst
      htab' hX hmX hqX hj ⟨i, hi, a, l, hal⟩).wt_lt).mono ?_
    rintro w cost ⟨⟨I, J, g, g', gs, gs', hs, rfl, hI, hIe, hIv, hJ, hJe, hJv, hgens, hlen,
      hcost⟩, hwt⟩
    exact ⟨⟨⟨j, (J, hs, g⁻¹ * g'), rfl, rfl, I, g, g', gs, gs', rfl, hI, hIe, hIv, hJ, hJe, hJv,
      hgens, hlen⟩, by omega⟩, hcost⟩
  have m0 := Det.var' (P := P) (env := [c, .list xs, boolVal bx, boolVal bY]) (i := 0) (v := c) rfl
  have m1 := Det.var' (P := P) (env := [c, .list xs, boolVal bx, boolVal bY]) (i := 1)
    (v := .list xs) rfl
  refine EvalAll.letE (EvalAll.call_spec (Det.mk2 m0 m1) (map_spec hA.hmx hfx)) ?_
  rintro _ cMx ⟨cbMx, ⟨wsX, rfl, hwsX, hcbMx⟩, hcMx⟩
  have n0 := Det.var' (P := P) (env := [c, .list xs, boolVal bx, boolVal bY, .list wsX]) (i := 0)
    (v := c) rfl
  have n1 := Det.var' (P := P) (env := [c, .list xs, boolVal bx, boolVal bY, .list wsX]) (i := 1)
    (v := .list xs) rfl
  refine EvalAll.letE (EvalAll.call_spec (Det.mk2 n0 n1) (map_spec hA.hmy hfy)) ?_
  rintro _ cMy ⟨cbMy, ⟨wsY, rfl, hwsY, hcbMy⟩, hcMy⟩
  have o4 := Det.var' (P := P) (env := [c, .list xs, boolVal bx, boolVal bY, .list wsX, .list wsY])
    (i := 4) (v := .list wsX) rfl
  have o5 := Det.var' (P := P) (env := [c, .list xs, boolVal bx, boolVal bY, .list wsX, .list wsY])
    (i := 5) (v := .list wsY) rfl
  -- the lists of objects
  obtain ⟨OX, rfl, hOX⟩ := tmCs_forall₂_objs (R := TmCsXObj vs σN q) (List.range q) wsX
    (hwsX.imp fun _ _ h => h.1)
  obtain ⟨OY, rfl, hOY⟩ := tmCs_forall₂_objs (R := TmCsYObj vs σN q) (List.range q) wsY
    (hwsY.imp fun _ _ h => h.1)
  obtain ⟨hlx, hOX'⟩ := tmCs_forall₂_range hOX
  obtain ⟨hly, hOY'⟩ := tmCs_forall₂_range hOY
  have hwX := tm_wt_forall₂ (W := K) (fun _ _ h => h.2) hwsX.flip
  have hwY := tm_wt_forall₂ (W := 2 * K) (fun _ _ h => h.2) hwsY.flip
  rw [hxsl] at hwX hwY
  refine (Det.mk2 o4 o5).post fun c' hc' => ⟨Or.inl ⟨⟨hallx, hally⟩, OX, OY, rfl, hlx, hly,
    hOX', hOY'⟩, ?_⟩
  have hsumK : ∀ (l : List Val) (k : ℕ), (l.map fun _ => k).sum = l.length * k := by
    intro l k; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  rw [hsumK, hxsl] at hcbMx hcbMy
  have hqx1 : q * (2 * K + 1) ≤ X * (4 * K + 1) := Nat.mul_le_mul hqX (by omega)
  have hqy1 : q * (2 * (2 * K) + 1) ≤ X * (4 * K + 1) := Nat.mul_le_mul hqX (by omega)
  have hMx := hmapc (W := (Val.list [c, .list xs]).wt + (Val.list (OX.map tmGlObjVal)).wt + 1)
    (by omega)
  have hMy := hmapc (W := (Val.list [c, .list xs]).wt + (Val.list (OY.map tmGlObjVal)).wt + 1)
    (by omega)
  have hq2K : q * (2 * K) ≤ 2 * ((X + 1) ^ 3 * K) := by
    rw [show q * (2 * K) = 2 * (q * K) by ring]; omega
  have hout := wt_list2_le (Val.list (OX.map tmGlObjVal)) (Val.list (OY.map tmGlObjVal))
  have hcMx' := hcbMx.trans (Nat.add_le_add hqK hMx)
  have hcMy' := hcbMy.trans (Nat.add_le_add hq2K hMy)
  have h7 : 10 ^ 6 * ((X + 1) ^ 3 * K) ≤ 10 ^ 7 * (X + 1) ^ 3 * K := by
    calc 10 ^ 6 * ((X + 1) ^ 3 * K) ≤ 10 ^ 7 * ((X + 1) ^ 3 * K) :=
          Nat.mul_le_mul_right _ (by norm_num)
      _ = 10 ^ 7 * (X + 1) ^ 3 * K := by ring
  have hz3 : bx.toNat * bY.toNat ≤ 1 := by cases bx <;> cases bY <;> simp
  have hXK2 : X * (4 * K + 1) ≤ 5 * ((X + 1) ^ 3 * K) := by
    have : (X + 1) * K ≤ (X + 1) ^ 3 * K := Nat.mul_le_mul_right _ (by
      have := Nat.le_self_pow (show 3 ≠ 0 by norm_num) (X + 1); omega)
    have e : 5 * (X + 1) * K = 5 * ((X + 1) * K) := by ring
    omega
  unfold tmCsObjsK
  rw [← hK]
  omega

end GI.Impl
