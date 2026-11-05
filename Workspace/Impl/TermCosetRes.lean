module

public import Workspace.Impl.TermCosetLink
public import Workspace.Impl.TermHyp
public import Workspace.Impl.OutbReb

@[expose] public section

/-!
# The residual transporter in one radical coset (Corollary A.22 through Lemma A.19)

`tmCsResF` works on `tmCsResIn uR σN vs q r = [uR, σN, vs, m, q, r]` (generator lists as lists
of permutations, `vs` the coset table). With `R = ⟨uR⟩ ≤ H = ⟨σH⟩`, `N = ⟨σN⟩ ≤ R`:

1. Turn `uR` and `σN` into group values (`mkGroup`), and rebase `vs` from `Iso_H(x_i, y_j)` to
   `vs'` for `Iso_R(x_i, y_j^{r⁻¹})` (`outbRebFuns`).
2. The objects of the rows (`tmCsObjsF`); if some row has no `R`-partner, the answer is `[]`.
3. The fuel `ℓ` (least with `m⁵ ≤ 3^ℓ`), and the recursion of Theorem A.20 on `(R, N)`
   (`TermRecSpec`): a canonical answer of `Iso_R(X, Y')`.
4. If it is `[x0, gs]`, the answer is `[x0 r, ⟨r⁻¹ gs r⟩]`.

`tmCs_res_spec`: the result is a canonical answer of the residual set
`{h ∈ Iso_H(types x, types y) : h ∈ R r}` (`tmCsResSet`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens PointwiseStab Membership GensOf)

/-! ### Shifting the objects -/

/-- On `[r, o]`: the object `o` with its representative multiplied by `r` on the right. -/
def tmCsShF (comp : ℕ) : Expr :=
  mk3 (.get (arg 1) (.nat 0)) (.get (arg 1) (.nat 1))
    (.call comp (mk2 (.get (arg 1) (.nat 2)) (arg 0)))

/-- The shifted object. -/
def tmCsSh {n : ℕ} (r : Perm (Fin n)) (o : ℕ × List (Perm (Fin n)) × Perm (Fin n)) :
    ℕ × List (Perm (Fin n)) × Perm (Fin n) := (o.1, o.2.1, o.2.2 * r)

theorem tmCs_sh_spec {P : Program} {sh comp : ℕ} (hsh : P.funs[sh]? = some (tmCsShF comp))
    (hcomp : P.HasAt comp (composeFuns comp)) {n : ℕ} (r : Perm (Fin n))
    (o : ℕ × List (Perm (Fin n)) × Perm (Fin n)) :
    FunDet P sh (.list [encPerm r, tmGlObjVal o]) (tmGlObjVal (tmCsSh r o))
      (20 * (Val.list [encPerm r, tmGlObjVal o]).wt + 8 * (tmGlObjVal (tmCsSh r o)).wt +
        permK * (n + 1) ^ 3 + 100) := by
  refine FunDet.intro hsh ?_
  unfold tmCsShF
  set a := Val.list [encPerm r, tmGlObjVal o] with ha
  have d0 := Det.arg' (P := P) (vs := [encPerm r, tmGlObjVal o]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [encPerm r, tmGlObjVal o]) (rest := []) (j := 1) rfl
  have e0 := Det.get' d1 (Det.nat 0) (vs := [.nat o.1, encGroup o.2.1, encPerm o.2.2])
    (v := .nat o.1) rfl
  have e1 := Det.get' d1 (Det.nat 1) (vs := [.nat o.1, encGroup o.2.1, encPerm o.2.2])
    (v := encGroup o.2.1) rfl
  have e2 := Det.get' d1 (Det.nat 2) (vs := [.nat o.1, encGroup o.2.1, encPerm o.2.2])
    (v := encPerm o.2.2) rfl
  have dc := Det.call (Det.mk2 e2 d0) (compose_spec hcomp o.2.2 r)
  refine (Det.mk3 e0 e1 dc).mono ?_
  have hob : (tmGlObjVal o).wt < a.wt := wt_le_wt_list (by simp [ha])
  have hr : (encPerm r).wt < a.wt := wt_le_wt_list (by simp [ha])
  have w0 : (Val.nat o.1).wt < (tmGlObjVal o).wt := wt_le_wt_list (by simp [tmGlObjVal])
  have w1 : (encGroup o.2.1).wt < (tmGlObjVal o).wt := wt_le_wt_list (by simp [tmGlObjVal])
  have w2 : (encPerm o.2.2).wt < (tmGlObjVal o).wt := wt_le_wt_list (by simp [tmGlObjVal])
  have w3 := wt_list2_le (encPerm o.2.2) (encPerm r)
  have w4 : (Val.list [.nat o.1, encGroup o.2.1, encPerm (o.2.2 * r)]).wt =
      (tmGlObjVal (tmCsSh r o)).wt := rfl
  have w5 : (encPerm (o.2.2 * r)).wt < (tmGlObjVal (tmCsSh r o)).wt :=
    wt_le_wt_list (by simp [tmGlObjVal, tmCsSh])
  have hak : a.wt = (Val.list [encPerm r, tmGlObjVal o]).wt := rfl
  omega

/-! ### Helper facts -/

theorem tmCs_objVal_inj {n : ℕ} {o o' : ℕ × List (Perm (Fin n)) × Perm (Fin n)}
    (h : tmGlObjVal o = tmGlObjVal o') : o = o' := by
  obtain ⟨c, L, g⟩ := o
  obtain ⟨c', L', g'⟩ := o'
  simp only [tmGlObjVal, encGroup, GI.Cited.encPerms, Val.list.injEq, List.cons.injEq,
    Val.nat.injEq, and_true, List.map_cons, true_and] at h
  obtain ⟨rfl, h2, h3⟩ := h
  rw [List.map_injective_iff.2 encPerm_injective h2, encPerm_injective h3]

theorem tmCs_map_sh {n : ℕ} (r : Perm (Fin n)) :
    ∀ (OX : List (ℕ × List (Perm (Fin n)) × Perm (Fin n))) (ws : List Val),
      List.Forall₂ (fun x w => ∀ o, x = tmGlObjVal o → w = tmGlObjVal (tmCsSh r o))
        (OX.map tmGlObjVal) ws → ws = (OX.map (tmCsSh r)).map tmGlObjVal
  | [], ws, h => by rw [List.map_nil, List.forall₂_nil_left_iff] at h; simp [h]
  | o :: OX, ws, h => by
    rw [List.map_cons, List.forall₂_cons_left_iff] at h
    obtain ⟨w, ws', hw, h', rfl⟩ := h
    rw [tmCs_map_sh r OX ws' h', hw o rfl]
    rfl

theorem tmCs_gens_nil {n : ℕ} : gens ([] : List (Perm (Fin n))) = ⊥ := by
  unfold gens; simp

theorem tmCs_pow_le (m : ℕ) : m ^ 5 ≤ 3 ^ (m ^ 2 + 4) := by
  rcases Nat.lt_or_ge m 4 with h | h
  · interval_cases m <;> norm_num
  · have h1 : m ≤ 3 ^ m := (Nat.lt_pow_self (by norm_num)).le
    calc m ^ 5 ≤ (3 ^ m) ^ 5 := Nat.pow_le_pow_left h1 5
      _ = 3 ^ (5 * m) := by ring
      _ ≤ 3 ^ (m ^ 2 + 4) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- The fuel is at most `m² + 5`. -/
theorem tmCs_ell_le_sq {m L : ℕ} (h : L = 0 ∨ 3 ^ (L - 1) < m ^ 5) : L ≤ m ^ 2 + 5 := by
  rcases h with rfl | h
  · omega
  · have := lt_of_lt_of_le h (tmCs_pow_le m)
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 this
    omega

/-- The fuel bounds Dixon's derived length. -/
theorem tmCs_ell_ge {m L : ℕ} (hm : 0 < m) (h : m ^ 5 ≤ 3 ^ L) :
    5 * Real.logb 3 m ≤ L := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h' : ((m : ℝ)) ^ 5 ≤ (3 : ℝ) ^ L := by exact_mod_cast h
  have := Real.logb_le_logb_of_le (b := 3) (by norm_num) (by positivity) h'
  rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this

/-- The fuel is at most `5 log₃ m + 1`. -/
theorem tmCs_ell_le {m L : ℕ} (hm : 0 < m) (h : L = 0 ∨ 3 ^ (L - 1) < m ^ 5) :
    (L : ℝ) ≤ 5 * Real.logb 3 m + 1 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h0 : 0 ≤ Real.logb 3 (m : ℝ) := Real.logb_nonneg (by norm_num) hm'
  rcases h with rfl | h
  · simp; linarith
  · have h' : (3 : ℝ) ^ (L - 1) < ((m : ℝ)) ^ 5 := by exact_mod_cast h
    have := Real.logb_lt_logb (b := 3) (by norm_num) (by positivity) h'
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
    have e : ((L - 1 : ℕ) : ℝ) ≥ (L : ℝ) - 1 := by
      rcases Nat.eq_zero_or_pos L with hL | hL
      · subst hL; simp
      · rw [Nat.cast_sub hL]; simp
    push_cast at this
    linarith

theorem tmCs_meas2 {l m : ℕ} (hl : l ≤ m ^ 2) : (l + 2) * (m + 1) ≤ 2 * (m + 1) ^ 3 := by
  have h1 : l + 2 ≤ 2 * (m + 1) ^ 2 := by
    have : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
    omega
  calc (l + 2) * (m + 1) ≤ (2 * (m + 1) ^ 2) * (m + 1) := Nat.mul_le_mul_right _ h1
    _ = 2 * (m + 1) ^ 3 := by ring

theorem tmCs_cast {n Q cb : ℕ} {RB : ℝ} (h : n ≤ Q + cb) (hcb : (cb : ℝ) ≤ RB) (hRB : 0 ≤ RB) :
    (n : ℝ) ≤ Q + 20 * RB := by
  have : (n : ℝ) ≤ Q + cb := by exact_mod_cast h
  linarith

/-! ### The residual program -/

/-- The input of the residual program. -/
def tmCsResIn {m : ℕ} (uR : Val) (σN : List (Perm (Fin m))) (vs : List Val) (q : ℕ)
    (r : Perm (Fin m)) : Val :=
  .list [uR, .list (σN.map encPerm), .list vs, .nat m, .nat q, encPerm r]

/-- `m⁵`, from the input. -/
def tmCsM5 : Expr :=
  .arith .mul (.get (.var 0) (.nat 3)) (.arith .mul (.get (.var 0) (.nat 3))
    (.arith .mul (.get (.var 0) (.nat 3)) (.arith .mul (.get (.var 0) (.nat 3))
      (.get (.var 0) (.nat 3)))))

/-- The tail after a nonempty answer `[x0, gs]` of the recursion (at `var 11`). -/
def tmCsResTail (comp inv mp_conj : ℕ) : Expr :=
  .letE (.call comp (mk2 (.get (.var 11) (.nat 0)) (.get (.var 0) (.nat 5))))
  (.letE (.call inv (.get (.var 0) (.nat 5)))
  (.letE (.call mp_conj (mk2 (mk2 (.var 13) (.get (.var 0) (.nat 5)))
      (.get (.get (.var 11) (.nat 1)) (.nat 1))))
  (mk2 (.var 12) (mk2 (.get (.var 0) (.nat 3)) (.var 14)))))

/-- The part after the objects (at `var 7`), when every row has a partner. -/
def tmCsResRec (ell rec comp inv red mp_conj : ℕ) : Expr :=
  .letE (.call red (mk2 (.get (.var 0) (.nat 3)) (.var 2)))
  (.letE (.get (.var 7) (.nat 0))
  (.letE (.call ell (mk3 (.nat 1) tmCsM5 (.nat 0)))
  (.letE (.call rec (.snoc (mk4 (.var 10) (.var 6) (.var 8) (.var 9)) (.get (.var 7) (.nat 1))))
  (.ite (.length (.var 11)) (tmCsResTail comp inv mp_conj) .nil))))

/-- **The residual program.** -/
def tmCsResF (mkg reb objs ell rec comp inv red mp_conj : ℕ) : Expr :=
  .letE (.call mkg (mk2 (.get (.var 0) (.nat 3)) (.get (.var 0) (.nat 0))))
  (.letE (.call mkg (mk2 (.get (.var 0) (.nat 3)) (.get (.var 0) (.nat 1))))
  (.letE (.call reb (mk4 (.var 1) (.get (.var 0) (.nat 3)) (.get (.var 0) (.nat 5))
      (.get (.var 0) (.nat 2))))
  (.letE (.var 1)
  (.letE (.var 1)
  (.letE (.var 1)
  (.letE (.call objs (mk4 (.var 3) (.get (.var 0) (.nat 1))
      (.get (.var 0) (.nat 3)) (.get (.var 0) (.nat 4))))
  (.ite (.length (.var 7)) (tmCsResRec ell rec comp inv red mp_conj) .nil)))))))

/-- The functions of the residual program. -/
structure TmCsResAt (P : Program) (hm : Membership)
    (f mkg reb objs ell rec comp app red mp_conj conj jst jm : ℕ)
    (rg ax px ay py mx fx my fy first inv : ℕ) : Prop where
  hf : P.funs[f]? = some (tmCsResF mkg reb objs ell rec comp inv red mp_conj)
  hmkg : P.HasAt mkg (mkGroupFuns mkg)
  hreb : OutbRebPlaced P hm reb comp inv rg app red mp_conj conj jst jm
  hobjs : TmCsObjsAt P objs rg ax px ay py mx fx my fy first app red inv comp jst
  hell : P.funs[ell]? = some (tmCsEllF ell)
  hcomp : P.HasAt comp (composeFuns comp)
  happ : P.HasAt app (appendFuns app)
  hred : P.HasAt red (redFuns red jst)

/-- The polynomial part of the cost of the residual program. -/
noncomputable def tmCsResQ (p : Prim) (hm : Membership) (Kr Dr X : ℕ) : ℕ :=
  10 ^ 9 * (tmCsObjsK p (10 ^ 4 * (X + 1) ^ 8) + outbRebK p hm X +
    Kr * (10 ^ 4 * (X + 1) ^ 6) ^ Dr +
    p.boundSize (10 ^ 4 * (X + 1) ^ 6) +
    10 ^ 12 * (X + 1) ^ 12) ^ 2

set_option maxHeartbeats 3200000 in
/-- **The residual program** (Corollary A.22 through Lemma A.19 and Theorem A.20). -/
theorem tmCs_res_spec (hst : PointwiseStab) (hm_mem : Membership)
    (dixon : GI.Cited.DixonDerivedLength) {P : Program}
    {f mkg reb objs ell rec comp app red mp_conj conj jst jm
      rg ax px ay py mx fx my fy first inv : ℕ}
    (hA : TmCsResAt P hm_mem f mkg reb objs ell rec comp app red mp_conj conj jst jm
      rg ax px ay py mx fx my fy first inv)
    (hjst : P.prims[jst]? = some (pointwiseStabPrim hst)) (Kr Dr : ℕ) {Kc Dc : ℕ}
    (hrec : Iface.TermRecSpec P Kc Dc rec)
    {m q : ℕ} (hm : 0 < m) {Ω : Type*} [RAct (Perm (Fin m)) Ω] {x y : Fin q → Ω}
    {σH σN : List (Perm (Fin m))} {R : Subgroup (Perm (Fin m))} {uR : Val}
    {vs : List Val} (huR : GensOf R uR)
    (hRH : R ≤ gens σH) (hNR : gens σN ≤ R)
    (hRd : ∃ ℓ, relDerived R (gens σN) ℓ ≤ gens σN)
    (hn : GI.Multicoset.Normalizes (gens σH) (gens σN))
    (hT : TmCsTabOK (gens σH) x y vs)
    {r : Perm (Fin m)} (hr : r ∈ gens σH) {X : ℕ}
    (hX : (tmCsResIn uR σN vs q r).wt + (R.subgroupOf (gens σH)).index ≤ X)
    (hmX : m ≤ X) (hqX : q ≤ X) :
    FunAll P f (tmCsResIn uR σN vs q r) (fun w cost =>
      AnsC (Equiv.refl (Fin m)) w (tmCsResSet (gens σH) (gens σN) R x y r) ∧
      ∃ ℓ : ℕ, (ℓ : ℝ) ≤ 5 * Real.logb 3 m + 1 ∧
        (cost : ℝ) ≤ (tmCsResQ (pointwiseStabPrim hst) hm_mem Kr Dr X : ℝ) +
          20 * ((5 * ((q : ℝ) + 1) ^ 3 + 1) ^ ℓ * (Kc * (((m + q : ℕ) : ℝ) + 2) ^ Dc))) := by
  set H := gens σH with hH
  set N := gens σN with hN
  obtain ⟨hsR, rfl, hlR, hgR⟩ := huR
  set a := tmCsResIn (.list (hsR.map encPerm)) σN vs q r with ha
  set y' : Fin q → Ω := fun j => y j ↼ r⁻¹ with hy'
  have hRB0 : ∀ ℓ : ℕ, (0 : ℝ) ≤ (5 * ((q : ℝ) + 1) ^ 3 + 1) ^ ℓ *
      (Kc * (((m + q : ℕ) : ℝ) + 2) ^ Dc) := fun ℓ => by positivity
  have hlog0 : ((0 : ℕ) : ℝ) ≤ 5 * Real.logb 3 m + 1 := by
    have : 0 ≤ Real.logb 3 (m : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
    simp; linarith
  refine FunAll.intro hA.hf ?_
  unfold tmCsResF
  -- 1, 2. the group values of `R` and `N`
  have d0 := Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl
  have dm := Det.get' d0 (Det.nat 3) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  have dR := Det.get' d0 (Det.nat 0) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .list (hsR.map encPerm)) rfl
  refine EvalAll.letE (Det.call (Det.mk2 dm dR) (mkGroup_spec hA.hmkg hsR)) ?_
  rintro _ c1 ⟨rfl, hc1⟩
  have e0 := Det.var' (P := P) (env := [a, encGroup hsR]) (i := 0) (v := a) rfl
  have em := Det.get' e0 (Det.nat 3) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  have eN := Det.get' e0 (Det.nat 1) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .list (σN.map encPerm)) rfl
  refine EvalAll.letE (Det.call (Det.mk2 em eN) (mkGroup_spec hA.hmkg σN)) ?_
  rintro _ c2 ⟨rfl, hc2⟩
  -- 3. rebase the coset table `vs` into `R`
  have f0 := Det.var' (P := P) (env := [a, encGroup hsR, encGroup σN]) (i := 0) (v := a) rfl
  have f1 := Det.var' (P := P) (env := [a, encGroup hsR, encGroup σN]) (i := 1)
    (v := encGroup hsR) rfl
  have fm := Det.get' f0 (Det.nat 3) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  have fr := Det.get' f0 (Det.nat 5) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := encPerm r) rfl
  have fvs := Det.get' f0 (Det.nat 2) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .list vs) rfl
  refine EvalAll.letE (EvalAll.call_spec (Det.mk4 f1 fm fr fvs)
    (outbReb_spec hst hm_mem hA.hreb hjst hRH hlR hgR hr hT hmX hqX (by omega))) ?_
  rintro _ c3 ⟨cb3, ⟨⟨vs', rfl, hT', hwvs'⟩, hcb3⟩, hc3⟩
  -- 4, 5, 6. keep `encGroup hsR`
  set env4 := [a, encGroup hsR, encGroup σN, .list vs'] with henv4
  have g1 := Det.var' (P := P) (env := env4) (i := 1) (v := encGroup hsR) rfl
  refine EvalAll.letE g1 ?_
  rintro _ c4 ⟨rfl, hc4⟩
  set env5 := env4 ++ [encGroup hsR] with henv5
  have h1 := Det.var' (P := P) (env := env5) (i := 1) (v := encGroup hsR) rfl
  refine EvalAll.letE h1 ?_
  rintro _ c5 ⟨rfl, hc5⟩
  set env6 := env5 ++ [encGroup hsR] with henv6
  have i1 := Det.var' (P := P) (env := env6) (i := 1) (v := encGroup hsR) rfl
  refine EvalAll.letE i1 ?_
  rintro _ c6 ⟨rfl, hc6⟩
  -- 7. the objects of `(x, y')` in `R`
  have hRN : GI.Multicoset.Normalizes R N := hn.mono hRH
  set env7 := env6 ++ [encGroup hsR] with henv7
  have j0 := Det.var' (P := P) (env := env7) (i := 0) (v := a) rfl
  have jvs := Det.var' (P := P) (env := env7) (i := 3) (v := .list vs') rfl
  have jN := Det.get' j0 (Det.nat 1) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .list (σN.map encPerm)) rfl
  have jm := Det.get' j0 (Det.nat 3) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  have jq := Det.get' j0 (Det.nat 4) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat q) rfl
  have hX1 : 1 ≤ X + 1 := by omega
  have hX81 : 1 ≤ (X + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hXY8 : X + 1 ≤ (X + 1) ^ 8 := Nat.le_self_pow (by norm_num) _
  have haX : a.wt ≤ X := (Nat.le_add_right _ _).trans hX
  have waN : (Val.list (σN.map encPerm)).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
  have wam : (Val.nat m).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
  have waq : (Val.nat q).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
  have wavs : (Val.list vs).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
  have war : (encPerm r).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
  have waR : (Val.list (hsR.map encPerm)).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
  have hctx : (tmCsCtx vs' σN q).wt ≤ 10 ^ 4 * (X + 1) ^ 8 := by
    have h1 := wt_list4_le (.list vs') (.list (σN.map encPerm)) (.nat m) (.nat q)
    unfold tmCsCtx; omega
  refine EvalAll.letE (EvalAll.call_spec (Det.mk4 jvs jN jm jq)
    (FunAll.wt_lt (tmCs_objs_spec hst hA.hobjs hjst (tmCs_tab_of hT') hctx (by omega)
      (by omega)))) ?_
  rintro v7 c7 ⟨cb7, ⟨⟨hob, hcb7⟩, hw7⟩, hc7⟩
  -- the cost of steps 1 to 7
  set p := pointwiseStabPrim hst with hp
  set C := tmCsObjsK p (10 ^ 4 * (X + 1) ^ 8) + outbRebK p hm_mem X +
    Kr * (10 ^ 4 * (X + 1) ^ 6) ^ Dr +
    p.boundSize (10 ^ 4 * (X + 1) ^ 6) +
    10 ^ 12 * (X + 1) ^ 12 with hC
  have hQ : tmCsResQ p hm_mem Kr Dr X = 10 ^ 9 * C ^ 2 := rfl
  have hY1 : 1 ≤ X + 1 := by omega
  have hYp : ∀ k ≤ 12, (X + 1) ^ k ≤ (X + 1) ^ 12 := fun k hk => Nat.pow_le_pow_right hY1 hk
  have hm1 : m + 1 ≤ X + 1 := by omega
  have hmp : ∀ k, (m + 1) ^ k ≤ (X + 1) ^ k := fun k => Nat.pow_le_pow_left hm1 k
  have hC12 : 10 ^ 12 * (X + 1) ^ 12 ≤ C := by rw [hC]; omega
  have hCo : tmCsObjsK p (10 ^ 4 * (X + 1) ^ 8) ≤ C := by rw [hC]; omega
  have hCreb : outbRebK p hm_mem X ≤ C := by rw [hC]; omega
  have hC1 : 1 ≤ C := by have := Nat.one_le_pow 12 (X + 1) (by omega); omega
  have hlN : σN.length < X := by
    have := length_lt_wt_list (σN.map encPerm); simp at this; omega
  have hmeas : ∀ l : ℕ, l < X → (l + 2) * (m + 1) ≤ 2 * (X + 1) ^ 2 := by
    intro l hl
    calc (l + 2) * (m + 1) ≤ (2 * (X + 1)) * (X + 1) := Nat.mul_le_mul (by omega) hm1
      _ = 2 * (X + 1) ^ 2 := by ring
  have hmeas2 : ∀ l : ℕ, l ≤ m ^ 2 → (l + 2) * (m + 1) ≤ 2 * (X + 1) ^ 3 := by
    intro l hl
    have := tmCs_meas2 hl
    have := hmp 3; omega
  have hcube : ∀ {b B : ℕ}, b ≤ B → mkGroupK * b ^ 3 ≤ mkGroupK * B ^ 3 := fun h =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 3)
  have hmkN := hcube (hmeas _ hlN)
  have hmkR := hcube (hmeas2 _ hlR)
  have e2 : (2 * (X + 1) ^ 2) ^ 3 = 8 * (X + 1) ^ 6 := by ring
  have e3 : (2 * (X + 1) ^ 3) ^ 3 = 8 * (X + 1) ^ 9 := by ring
  rw [e2] at hmkN
  rw [e3] at hmkR
  have hsq : ∀ {b B : ℕ}, b ≤ B → 40 * b ^ 2 ≤ 40 * B ^ 2 := fun h =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)
  have wgN := (wt_encGroup_le σN).trans (hsq (hmeas _ hlN))
  have e4 : (2 * (X + 1) ^ 2) ^ 2 = 4 * (X + 1) ^ 4 := by ring
  rw [e4] at wgN
  have wgR := wt_encGroup_le_sq hlR
  have wlR := wt_list_encPerms_le_sq hlR
  have hX6 := hmp 6
  have wl1 := wt_list2_le (Val.nat m) (Val.list (hsR.map encPerm))
  have wl2 := wt_list2_le (Val.nat m) (Val.list (σN.map encPerm))
  have wl4 := wt_list4_le (encGroup hsR) (Val.nat m) (encPerm r) (Val.list vs)
  have wl5 := wt_list4_le (Val.list vs') (Val.list (σN.map encPerm)) (Val.nat m) (Val.nat q)
  have h6 := hYp 6 (by norm_num)
  have h8 := hYp 8 (by norm_num)
  have h9 := hYp 9 (by norm_num)
  have hXY : X + 1 ≤ (X + 1) ^ 12 := Nat.le_self_pow (by norm_num) _
  have hmk : mkGroupK = 100000 := rfl
  have h612 := hYp 6 (by norm_num)
  have h412 := hYp 4 (by norm_num)
  have hpre : c1 + c2 + c3 + c4 + c5 + c6 + c7 ≤ 10 * C + v7.wt := by
    rw [hmk] at hmkN hmkR hc1 hc2
    omega
  have hpart_iff : ((∀ i < q, TmCsHas vs' (i * q) 1 q) ∧ (∀ j < q, TmCsHas vs' j q q)) ↔
      ((∀ i, ∃ j, (Iso R (x i) (y' j)).Nonempty) ∧
        (∀ j, ∃ i, (Iso R (x i) (y' j)).Nonempty)) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => (tmCs_has_x hT' i).1 (h1 i.1 i.2),
        fun j => (tmCs_has_y hT' j).1 (h2 j.1 j.2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i hi => (tmCs_has_x hT' ⟨i, hi⟩).2 (h1 ⟨i, hi⟩),
        fun j hj => (tmCs_has_y hT' ⟨j, hj⟩).2 (h2 ⟨j, hj⟩)⟩
  rcases hob with ⟨hall, OX, OY, rfl, hlx, hly, hOX, hOY⟩ | ⟨rfl, hnot⟩
  swap
  · -- some row has no partner in `R`
    have k7 := Det.var' (P := P) (env := env7 ++ [.list []]) (i := 7) (v := .list []) rfl
    refine (Det.ite_zero (t := tmCsResRec ell rec comp inv red mp_conj) (Det.length k7)
      Det.nil).post fun c' hc' => ⟨Or.inl ⟨rfl, ?_⟩, 0, hlog0, ?_⟩
    · exact tmCs_res_empty hRH hNR hn hr fun h => hnot (hpart_iff.2 h)
    · refine tmCs_cast (cb := 0) ?_ (by simpa using hRB0 0) (hRB0 0)
      have hw0 : (Val.list []).wt ≤ 5 := by decide
      have hCC : C ≤ C ^ 2 := Nat.le_self_pow (by norm_num) _
      rw [hQ]
      simp only [List.length_nil] at hc'
      omega
  -- every row has a partner in `R`
  obtain ⟨hpx, hpy⟩ := hpart_iff.1 hall
  set v7 := Val.list [tmGlObjsVal OX, tmGlObjsVal OY] with hv7
  have k7 := Det.var' (P := P) (env := env7 ++ [v7]) (i := 7) (v := v7) rfl
  refine EvalAll.ite (Det.length k7) (fun _ _ h => ⟨_, h.1⟩) fun z cz ⟨hz, hcz⟩ => ?_
  cases hz
  rw [if_neg (by simp [hv7])]
  unfold tmCsResRec
  -- the multisets of the objects
  have hmsX : tmGlMs OX = (types N x).map (tmCsF R N y') :=
    tmCs_ms_list hlx fun i hi => tmCs_x_obj hT' hNR hRN rfl (hOX i hi)
  have hmsY : tmGlMs OY = (types N y').map (tmCsF R N y') :=
    tmCs_ms_list hly fun j hj => tmCs_y_obj hT' hNR hRN rfl (hOY j hj)
  have hiso_objs := tmCs_iso_objs_eq hNR hRN hmsX hmsY hpx
  -- 8. cut `σN` to `m²` generators
  set env8 := env7 ++ [v7] with henv8
  have l0 := Det.var' (P := P) (env := env8) (i := 0) (v := a) rfl
  have lm := Det.get' l0 (Det.nat 3) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  have l2 := Det.var' (P := P) (env := env8) (i := 2) (v := encGroup σN) rfl
  have hgvN : GroupVal m (encGroup σN) N := ⟨σN, rfl, rfl⟩
  refine EvalAll.letE (EvalAll.call_spec (Det.mk2 lm l2) (red_spec hst hA.hred hjst hgvN)) ?_
  rintro _ c8 ⟨cb8, ⟨hsN, rfl, hgensN, hlN2, hcb8⟩, hc8⟩
  -- 9. the objects of `x`
  set env9 := env8 ++ [encGroup hsN] with henv9
  have n7 := Det.var' (P := P) (env := env9) (i := 7) (v := v7) rfl
  have nX := Det.get' n7 (Det.nat 0) (vs := [tmGlObjsVal OX, tmGlObjsVal OY])
    (v := tmGlObjsVal OX) rfl
  have hv7C : v7.wt < C := by omega
  have hxsv : (tmGlObjsVal OX).wt < v7.wt := wt_le_wt_list (by simp [hv7])
  have hr4 := wt_encPerm_le r
  have hm2 := hmp 2
  have hm3 := hmp 3
  have h2_12 := hYp 2 (by norm_num)
  have h3_12 := hYp 3 (by norm_num)
  refine EvalAll.letE nX ?_
  rintro _ c9 ⟨rfl, hc9⟩
  -- 10. the fuel
  set env10 := env9 ++ [tmGlObjsVal OX] with henv10
  have p0 := Det.var' (P := P) (env := env10) (i := 0) (v := a) rfl
  have pm := Det.get' p0 (Det.nat 3) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  set t := m * (m * (m * (m * m))) with ht
  have ht5 : t = m ^ 5 := by rw [ht]; ring
  have ht1 : 1 ≤ t := by rw [ht5]; exact Nat.one_le_pow _ _ hm
  have p5 : Det P env10 tmCsM5 (.nat t) _ :=
    Det.arith' (op := .mul) pm (Det.arith' (op := .mul) pm (Det.arith' (op := .mul) pm
      (Det.arith' (op := .mul) pm pm (z := m * m) rfl) (z := m * (m * m)) rfl)
      (z := m * (m * (m * m))) rfl) (z := t) rfl
  obtain ⟨L, hL, htL, hL2⟩ := tmCs_ell_spec hA.hell t ht1 (t - 3 ^ 0) 0 rfl (Or.inl rfl)
  rw [pow_zero] at hL
  refine EvalAll.letE (Det.call (Det.mk3 (Det.nat 1) p5 (Det.nat 0)) hL) ?_
  rintro _ c10 ⟨rfl, hc10⟩
  have hLm : (L : ℝ) ≤ 5 * Real.logb 3 m + 1 := tmCs_ell_le hm (by rw [← ht5]; exact hL2)
  -- 11. the recursion on `(R, N)`
  have hok : ∀ o ∈ OX ++ OY, o.2.1.length ≤ m ^ 2 ∧ o.2.2 ∈ R ∧ ∃ hc : o.1 < q,
      ∀ z, z ∈ gens o.2.1 ↔ ∃ a ∈ Aut R (y' ⟨o.1, hc⟩), ∃ k ∈ N, z = a * k := by
    intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ho
      have hxo := hOX i (by omega)
      obtain ⟨hc, hg⟩ := tmCs_x_gens (i := ⟨i, by omega⟩) hT' hRN rfl hxo
      obtain ⟨g, gs, hrep, hc', -, hv, -, hlen⟩ := hxo
      have hgR' := (tmCs_mem_of_cons hT' (i := ⟨i, by omega⟩) (j := ⟨(OX[i]'hi).1, hc'⟩) hv).1
      have hrepR : (OX[i]'hi).2.2 ∈ R := by
        rw [hrep]
        exact R.inv_mem hgR'
      exact ⟨hlen, hrepR, hc, hg⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ho
      have hyo := hOY j (by omega)
      obtain ⟨hc, hg⟩ := tmCs_y_gens (j := ⟨j, by omega⟩) hT' hRN rfl hyo
      obtain ⟨I, g, g', gs, gs', hrep, hI, -, hv', hc', -, hv, -, hlen⟩ := hyo
      have hgR' := (tmCs_mem_of_cons hT' (i := ⟨I, hI⟩) (j := ⟨(OY[j]'hj).1, hc'⟩) hv).1
      have hg'R := (tmCs_mem_of_cons hT' (i := ⟨I, hI⟩) (j := ⟨j, by omega⟩) hv').1
      have hrepR : (OY[j]'hj).2.2 ∈ R := by
        rw [hrep]
        exact R.mul_mem (R.inv_mem hgR') hg'R
      exact ⟨hlen, hrepR, hc, hg⟩
  have hrecok : TmRecObjOK q (OX ++ OY) := by
    intro o ho
    obtain ⟨hlo, -, hc, hgo⟩ := hok o ho
    refine ⟨hlo, by omega, fun o' ho' he => ?_⟩
    obtain ⟨-, -, hc', hgo'⟩ := hok o' ho'
    ext z
    rw [hgo z, hgo' z]
    have : (⟨o.1, hc⟩ : Fin q) = ⟨o'.1, hc'⟩ := Fin.ext he
    rw [this]
  have hnormR : ∀ o ∈ OX ++ OY,
      GI.Multicoset.Normalizes (gens (o.2.1.map fun x => o.2.2⁻¹ * x * o.2.2⁻¹⁻¹)) (gens hsR) := by
    intro o ho
    obtain ⟨-, hrepR, hc, hgo⟩ := hok o ho
    have hle : gens (o.2.1.map fun x => o.2.2⁻¹ * x * o.2.2⁻¹⁻¹) ≤ R := by
      rw [GI.Cited.gens, Subgroup.closure_le]
      intro z hz
      rw [Set.mem_setOf_eq, List.mem_map] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxR : x ∈ R := by
        have : x ∈ gens o.2.1 := Subgroup.subset_closure hx
        obtain ⟨a, ha, k, hk, rfl⟩ := (hgo x).1 this
        exact R.mul_mem ha.1 (hNR hk)
      exact R.mul_mem (R.mul_mem (R.inv_mem hrepR) hxR) (R.inv_mem (R.inv_mem hrepR))
    rw [hgR]
    intro k hk g hg
    exact R.mul_mem (R.mul_mem (hle hk) hg) (R.inv_mem (hle hk))
  have hNR'' : gens hsN ≤ gens hsR := by rw [hgensN, hgR]; exact hNR
  have hnormRN : GI.Multicoset.Normalizes (gens hsR) (gens hsN) := by
    rw [hgR, hgensN]; exact hRN
  have hrel : relDerived (gens hsR) (gens hsN) L ≤ gens hsN := by
    rw [hgR, hgensN]
    obtain ⟨hSR, hSsolv, hSsup⟩ := supplement_spec hNR hRN hRd
    have hge := tmCs_ell_ge hm (L := L) (by rw [← ht5]; exact htL)
    have hdix := dixon m (supplement R N) hSsolv L (by simpa using hge)
    exact relDerived_le_of_supplement hNR hSR hRN hSsup hdix
  have hDx : ∀ t ∈ types N x, t ∈ tmCsD R N y' := fun t ht => by
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ht
    obtain ⟨j, hj⟩ := hpx i
    exact ⟨j, (tmCs_in_iff hNR (x i) j).2 hj⟩
  have hDy : ∀ t ∈ types N y', t ∈ tmCsD R N y' := fun t ht => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 ht
    exact ⟨j, (tmCs_in_iff hNR (y' j) j).2 ⟨1, R.one_mem, act_one _⟩⟩
  have hfixM : ∀ {Z : Multiset (Set Ω)}, (∀ t ∈ Z, t ∈ tmCsD R N y') → Fixes N Z →
      Fixes N (Z.map (tmCsF R N y')) := by
    intro Z hZ hfZ k hk o ho
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 ho
    rw [← tmCsF_act hRN t (hZ t ht) k (hNR hk), hfZ k hk t ht]
  have hfixOX : Fixes (gens hsN) (tmGlMs OX) := by
    rw [hgensN, hmsX]
    exact hfixM hDx (fixes_types N x)
  have hfixOY : Fixes (gens hsN) (tmGlMs OY) := by
    rw [hgensN, hmsY]
    exact hfixM hDy (fixes_types N y')
  have hrecF := hrec q L hsR hsN OX OY hnormR hNR'' hnormRN hrel
    (tmCs_ell_le_sq (by rw [← ht5]; exact hL2)) hfixOX hfixOY hlR hlN2
    (by omega) (by omega) hrecok
  set env11 := env10 ++ [Val.nat L] with henv11
  have r10 := Det.var' (P := P) (env := env11) (i := 10) (v := .nat L) rfl
  have r6 := Det.var' (P := P) (env := env11) (i := 6) (v := encGroup hsR) rfl
  have r8 := Det.var' (P := P) (env := env11) (i := 8) (v := encGroup hsN) rfl
  have r9 := Det.var' (P := P) (env := env11) (i := 9) (v := tmGlObjsVal OX) rfl
  have r7 := Det.var' (P := P) (env := env11) (i := 7) (v := v7) rfl
  have r7Y := Det.get' r7 (Det.nat 1) (vs := [tmGlObjsVal OX, tmGlObjsVal OY])
    (v := tmGlObjsVal OY) rfl
  have darg := Det.snoc (Det.mk4 r10 r6 r8 r9) r7Y
  refine EvalAll.letE (EvalAll.call_spec darg hrecF) ?_
  rintro u c11 ⟨cb11, ⟨hans, hcb11⟩, hc11⟩
  rw [hgR] at hans
  have hans' := hans
  -- the cost of steps 8 to 11
  have hu : u.wt ≤ C := by
    rcases hans with ⟨rfl, -⟩ | ⟨x0, gs, rfl, hgl, -⟩
    · have : (Val.list []).wt ≤ 5 := by decide
      omega
    · have := wt_list2_le (encPerm x0) (encGroup gs)
      have := wt_encPerm_le x0
      have := wt_encGroup_le_sq hgl
      omega
  have hmid : cz + c8 + c9 + c10 + c11 ≤ 10 ^ 8 * C ^ 2 + cb11 := by
    have hlen2 : [tmGlObjsVal OX, tmGlObjsVal OY].length = 2 := rfl
    rw [hlen2] at hcz
    have wg0' := wt_encGroup_le_sq hlN2
    have hX61 : 1 ≤ (X + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have h4_6 : (X + 1) ^ 4 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_right hY1 (by norm_num)
    have h6_12 := hYp 6 (by norm_num)
    have w8 := wt_list2_le (Val.nat m) (encGroup σN)
    have w8b := wt_list2_le (encGroup σN) (Val.list [])
    have hl0 : (Val.list []).wt ≤ 5 := by decide
    have hbd8 : (pointwiseStabPrim hst).bound (Val.list [encGroup σN, Val.list []]) ≤
        p.boundSize (10 ^ 4 * (X + 1) ^ 6) := by
      apply Prim.bound_le
      have := (Val.list [encGroup σN, Val.list []]).size_le_wt
      omega
    have hm9 := hmp 9
    -- the fuel
    have hmm : m * m ≤ (X + 1) ^ 12 := by
      have : m * m ≤ (X + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
      omega
    have hmmm : m * (m * m) ≤ (X + 1) ^ 12 := by
      have : m * (m * m) ≤ (X + 1) ^ 3 := by
        calc m * (m * m) ≤ (X + 1) * ((X + 1) * (X + 1)) :=
              Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
          _ = (X + 1) ^ 3 := by ring
      omega
    have hm4 : m * (m * (m * m)) ≤ (X + 1) ^ 12 := by
      have : m * (m * (m * m)) ≤ (X + 1) ^ 4 := by
        calc m * (m * (m * m)) ≤ (X + 1) * ((X + 1) * ((X + 1) * (X + 1))) :=
              Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega)
                (Nat.mul_le_mul (by omega) (by omega)))
          _ = (X + 1) ^ 4 := by ring
      omega
    have ht5' : t ≤ (X + 1) ^ 5 := by rw [ht5]; exact Nat.pow_le_pow_left (by omega) 5
    have h5_12 := hYp 5 (by norm_num)
    have hell : (t - 1 + 1) * tmCsEllK (Val.nat (3 * t)).wt ≤ 1200 * (X + 1) ^ 10 := by
      have h1 : t - 1 + 1 = t := by omega
      have h2 := wt_nat_le (3 * t)
      rw [h1]
      unfold tmCsEllK
      calc t * (200 * (Val.nat (3 * t)).wt + 200) ≤ (X + 1) ^ 5 * (1200 * (X + 1) ^ 5) := by
            apply Nat.mul_le_mul ht5'
            have : 1 ≤ (X + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
            omega
        _ = 1200 * (X + 1) ^ 10 := by ring
    have h10_12 := hYp 10 (by norm_num)
    have hLw : (Val.nat L).wt ≤ (X + 1) ^ 2 + 7 := by
      have := wt_nat_le L
      have := tmCs_ell_le_sq (by rw [← ht5]; exact hL2)
      have := hmp 2
      have : m ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have wn1 : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
    have wn0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    have wt3 := wt_list3_le (Val.nat 1) (Val.nat t) (Val.nat 0)
    have wtt := wt_nat_le t
    have wgS0 := wgR
    have hOYw : (tmGlObjsVal OY).wt < v7.wt := wt_le_wt_list (by simp [hv7])
    have w11a := wt_list4_le (Val.nat L) (encGroup hsR) (encGroup hsN) (tmGlObjsVal OX)
    have w11b := wt_list_le
      ([Val.nat L, encGroup hsR, encGroup hsN, tmGlObjsVal OX] ++ [tmGlObjsVal OY])
    simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] at w11b
    have hCC : C ≤ C ^ 2 := Nat.le_self_pow (by norm_num) _
    have e11 : (Val.list ([Val.nat L, encGroup hsR, encGroup hsN, tmGlObjsVal OX] ++
        [tmGlObjsVal OY])).wt =
        (Val.list [Val.nat L, encGroup hsR, encGroup hsN, tmGlObjsVal OX,
        tmGlObjsVal OY]).wt := rfl
    rw [e11] at hc11
    omega
  have hset : tmCsResSet H N R x y r =
      (fun z => z * r) '' Iso R (tmGlMs OX) (tmGlMs OY) := by
    rw [tmCs_resSet_eq_image hRH hn hr, ← hiso_objs]
  set env12 := env11 ++ [u] with henv12
  have s11 := Det.var' (P := P) (env := env12) (i := 11) (v := u) rfl
  rcases hans with ⟨rfl, hI⟩ | ⟨x0, gs, rfl, hgl, -⟩
  · -- the transporter on `R` is empty
    refine (Det.ite_zero (t := tmCsResTail comp inv mp_conj) (Det.length s11) Det.nil).post
      fun c' hc' => ⟨Or.inl ⟨rfl, ?_⟩, L, hLm, ?_⟩
    · rw [hset, hI]; simp
    · refine tmCs_cast (cb := cb11) ?_ hcb11 (hRB0 L)
      have hw0 : (Val.list []).wt ≤ 5 := by decide
      have hCC : C ≤ C ^ 2 := Nat.le_self_pow (by norm_num) _
      simp only [List.length_nil] at hc'
      rw [hQ]
      omega
  have hI := tmCs_ansC_cons hans' rfl
  refine EvalAll.ite (Det.length s11) (fun _ _ h => ⟨_, h.1⟩) fun z' cz' ⟨hz', hcz'⟩ => ?_
  cases hz'
  rw [if_neg (by simp)]
  unfold tmCsResTail
  -- 12. the representative `x0 * r`
  have t0 := Det.var' (P := P) (env := env12) (i := 0) (v := a) rfl
  have tr := Det.get' t0 (Det.nat 5) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := encPerm r) rfl
  have tx := Det.get' s11 (Det.nat 0) (vs := [encPerm x0, encGroup gs]) (v := encPerm x0) rfl
  refine EvalAll.letE (Det.call (Det.mk2 tx tr) (compose_spec hA.hcomp x0 r)) ?_
  rintro _ c12 ⟨rfl, hc12⟩
  -- 13. `r⁻¹`
  set env13 := env12 ++ [encPerm (x0 * r)] with henv13
  have u0 := Det.var' (P := P) (env := env13) (i := 0) (v := a) rfl
  have ur := Det.get' u0 (Det.nat 5) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := encPerm r) rfl
  refine EvalAll.letE (Det.call ur (inv_spec hA.hreb.hinv r)) ?_
  rintro _ c13 ⟨rfl, hc13⟩
  -- 14. conjugate `(1 :: gs)` by `r⁻¹`
  set env14 := env13 ++ [encPerm r⁻¹] with henv14
  have v13 := Det.var' (P := P) (env := env14) (i := 13) (v := encPerm r⁻¹) rfl
  have v0 := Det.var' (P := P) (env := env14) (i := 0) (v := a) rfl
  have vr := Det.get' v0 (Det.nat 5) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := encPerm r) rfl
  have v11 := Det.var' (P := P) (env := env14) (i := 11) (v := .list [encPerm x0, encGroup gs]) rfl
  have vgs := Det.get' v11 (Det.nat 1) (vs := [encPerm x0, encGroup gs]) (v := encGroup gs) rfl
  have vl := Det.get' vgs (Det.nat 1) (vs := [.nat m, .list ((1 :: gs).map encPerm)])
    (v := .list ((1 :: gs).map encPerm)) rfl
  set pairRi := Val.list [encPerm r⁻¹, encPerm r] with hpairRi
  have hpairRi_eq : pairRi = Val.list [encPerm r⁻¹, encPerm (r⁻¹)⁻¹] := by simp [hpairRi]
  set gs' := gs.map (fun g => r⁻¹ * g * r) with hgs'
  have hgl' : gs'.length ≤ m ^ 2 := by rw [hgs', List.length_map]; exact hgl
  have hMconj := map_spec hA.hreb.hmp_conj (c := pairRi) (xs := (1 :: gs).map encPerm)
    (R := fun u_v w_v => ∀ σ : Perm (Fin m), u_v = encPerm σ → w_v = encPerm (r⁻¹ * σ * r))
    (B := fun _ => tmCsConjK m) (by
      intro u_v hu_v
      obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hu_v
      rw [hpairRi_eq]
      refine FunAll.mono (tmCs_conj_spec hA.hreb.hconj hA.hcomp r⁻¹ σ) fun w_v cost hw_v =>
        ⟨fun σ' h' => by
          have h1 := hw_v.1
          rw [inv_inv] at h1
          rw [h1, encPerm_injective h'], hw_v.2⟩)
  have hws_conj : ∀ ws', List.Forall₂ (fun u_v w_v => ∀ σ : Perm (Fin m), u_v = encPerm σ →
      w_v = encPerm (r⁻¹ * σ * r)) ((1 :: gs).map encPerm) ws' →
      ws' = (1 :: gs').map encPerm := by
    intro ws' h2
    have := forall₂_map_eq (g := fun σ => encPerm (r⁻¹ * σ * r)) (fun a _ w hw => hw a rfl) h2
    rw [this, hgs', List.map_cons, List.map_cons, List.map_map]
    simp
  have hlen_gs : (1 :: gs).length ≤ (X + 1) ^ 2 := by
    simp only [List.length_cons]
    have h1 : m ^ 2 + 1 ≤ (m + 1) ^ 2 := by
      calc m ^ 2 + 1 ≤ m ^ 2 + 2 * m + 1 := by omega
        _ = (m + 1) ^ 2 := by ring
    have h2 := hmp 2
    omega
  have wgs := (wt_encGroup_le_sq hgl).trans (Nat.mul_le_mul_left 320 (hmp 6))
  have w1gs : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (by simp [encGroup, GI.Cited.encPerms])
  have wgs' := (wt_encGroup_le_sq hgl').trans (Nat.mul_le_mul_left 320 (hmp 6))
  have w1gs' : (Val.list ((1 :: gs').map encPerm)).wt < (encGroup gs').wt :=
    wt_le_wt_list (by simp [encGroup, GI.Cited.encPerms])
  have wri := wt_encPerm_le r⁻¹
  have wpri := wt_list2_le (encPerm r⁻¹) (encPerm r)
  rw [← hpairRi] at wpri
  have h2_6 : (X + 1) ^ 2 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hconj_cost : FunDet P mp_conj (.list [pairRi, .list ((1 :: gs).map encPerm)])
      (.list ((1 :: gs').map encPerm)) (10 ^ 7 * (X + 1) ^ 8) := by
    refine FunAll.mono hMconj fun w_v cost ⟨ws', hw_v, h2, hcost⟩ => ?_
    have := hws_conj ws' h2; subst this; subst hw_v
    refine ⟨rfl, ?_⟩
    rw [tm_sum_map_const, List.length_map] at hcost
    have h1 : (1 :: gs).length * tmCsConjK m ≤ (X + 1) ^ 2 * (10 ^ 6 * (X + 1) ^ 3) := by
      unfold tmCsConjK
      exact Nat.mul_le_mul hlen_gs (Nat.mul_le_mul_left _ (hmp 3))
    have w2 := wt_list2_le pairRi (.list ((1 :: gs).map encPerm))
    have hlp : mapK * ((1 :: gs).length + 1) *
        ((Val.list [pairRi, .list ((1 :: gs).map encPerm)]).wt +
          (Val.list ((1 :: gs').map encPerm)).wt + 1) ≤
        2 * 10 ^ 3 * (X + 1) ^ 2 * (2000 * (X + 1) ^ 6) := by
      simp only [mapK]
      refine Nat.mul_le_mul (by
        have : 1 ≤ (X + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega) ?_
      omega
    have e5 : (X + 1) ^ 2 * (10 ^ 6 * (X + 1) ^ 3) = 10 ^ 6 * (X + 1) ^ 5 := by ring
    have e8 : 2 * 10 ^ 3 * (X + 1) ^ 2 * (2000 * (X + 1) ^ 6) = 4 * 10 ^ 6 * (X + 1) ^ 8 := by ring
    have h58 := Nat.pow_le_pow_right hY1 (show 5 ≤ 8 by norm_num)
    omega
  refine EvalAll.letE (Det.call (Det.mk2 (Det.mk2 v13 vr) vl) hconj_cost) ?_
  rintro _ c14 ⟨rfl, hc14⟩
  rw [← hpairRi] at hc14
  set env15 := env14 ++ [Val.list ((1 :: gs').map encPerm)] with henv15
  have o12 := Det.var' (P := P) (env := env15) (i := 12) (v := encPerm (x0 * r)) rfl
  have o0 := Det.var' (P := P) (env := env15) (i := 0) (v := a) rfl
  have om := Det.get' o0 (Det.nat 3) (vs := [.list (hsR.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  have o14 := Det.var' (P := P) (env := env15) (i := 14)
    (v := .list ((1 :: gs').map encPerm)) rfl
  refine (Det.mk2 o12 (Det.mk2 om o14)).post fun c' hc' =>
    ⟨Or.inr ⟨x0 * r, gs', rfl, hgl', ?_⟩, L, hLm, ?_⟩
  · rw [tmCs_toFin_refl, hset, hI, outbReb_right_translate]
    rfl
  · refine tmCs_cast (cb := cb11) ?_ hcb11 (hRB0 L)
    have hCC : C ≤ C ^ 2 := Nat.le_self_pow (by norm_num) _
    have hlen2 : [encPerm x0, encGroup gs].length = 2 := rfl
    rw [hlen2] at hcz'
    have hX16 : X + 1 ≤ (X + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    have hm4' := hmp 4
    have hm9 := hmp 9
    have hx0 := wt_encPerm_le x0
    have hxr := wt_encPerm_le (x0 * r)
    have hpk : permK = 30000 := rfl
    have hik : invK = 100000 := rfl
    rw [hpk] at hc12
    rw [hik] at hc13
    have wp2 := wt_list2_le (encPerm x0) (encPerm r)
    have wp3 := wt_list2_le pairRi (.list ((1 :: gs).map encPerm))
    have wp4 := wt_list2_le (.nat m) (.list ((1 :: gs').map encPerm))
    have wo := wt_list2_le (encPerm (x0 * r)) (encGroup gs')
    have e_gs' : Val.list [Val.nat m, Val.list ((1 :: gs').map encPerm)] = encGroup gs' := rfl
    rw [e_gs'] at wp4 hc' ⊢
    rw [hQ]
    omega

end GI.Impl
