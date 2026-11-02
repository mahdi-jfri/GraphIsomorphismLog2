import Workspace.Impl.TermCosetLink
import Workspace.Impl.TermHyp

/-!
# The residual transporter in one radical coset (Corollary A.22 through Lemma A.19)

`tmCsResF` works on `tmCsResIn σH σN vs m q r = [σH, σN, vs, m, q, r]` (generator lists as lists
of permutations, `vs` the coset table). With `H = ⟨σH⟩`, `N = ⟨σN⟩`:

1. `R` = the radical preimage of `H/N` (`TermRadSpec`, T2), `S` = a solvable supplement of `N`
   in `R` (`TermSupSpec`, T4).
2. The objects of the rows (`tmCsObjsF`); if some row has no partner, the answer is `[]`.
3. The objects of `x` shifted by `r` (`tmCsShF`), the fuel `ℓ` (least with `m⁵ ≤ 3^ℓ`), and the
   recursion of Theorem A.20 on `(S, 1)` (`TermRecSpec`): a canonical answer of
   `Iso_S(X^r, Y)`.
4. If it is `[x0, gs]`, the answer is `[r x0, ⟨gs, σN⟩]` (cut to `m²` generators).

`tmCs_res_spec`: the result is a canonical answer of the residual set
`{h ∈ Iso_H(types x, types y) : h ∈ R r}` (`tmCsResSet`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens PointwiseStab)

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
def tmCsResIn {m : ℕ} (σH σN : List (Perm (Fin m))) (vs : List Val) (q : ℕ) (r : Perm (Fin m)) :
    Val :=
  .list [.list (σH.map encPerm), .list (σN.map encPerm), .list vs, .nat m, .nat q, encPerm r]

/-- `m⁵`, from the input. -/
def tmCsM5 : Expr :=
  .arith .mul (.get (.var 0) (.nat 3)) (.arith .mul (.get (.var 0) (.nat 3))
    (.arith .mul (.get (.var 0) (.nat 3)) (.arith .mul (.get (.var 0) (.nat 3))
      (.get (.var 0) (.nat 3)))))

/-- The tail after a nonempty answer `[x0, gs]` of the recursion (at `var 11`). -/
def tmCsResTail (comp app red : ℕ) : Expr :=
  .letE (.call comp (mk2 (.get (.var 0) (.nat 5)) (.get (.var 11) (.nat 0))))
  (.letE (.call app (mk2 (.get (.get (.var 11) (.nat 1)) (.nat 1)) (.get (.var 0) (.nat 1))))
  (.letE (.call red (mk2 (.get (.var 0) (.nat 3)) (mk2 (.get (.var 0) (.nat 3)) (.var 13))))
  (mk2 (.var 12) (.var 14))))

/-- The part after the objects (at `var 7`), when every row has a partner. -/
def tmCsResRec (mkg msh ell rec comp app red : ℕ) : Expr :=
  .letE (.call mkg (mk2 (.get (.var 0) (.nat 3)) .nil))
  (.letE (.call msh (mk2 (.get (.var 0) (.nat 5)) (.get (.var 7) (.nat 0))))
  (.letE (.call ell (mk3 (.nat 1) tmCsM5 (.nat 0)))
  (.letE (.call rec (.snoc (mk4 (.var 10) (.var 6) (.var 8) (.var 9)) (.get (.var 7) (.nat 1))))
  (.ite (.length (.var 11)) (tmCsResTail comp app red) .nil))))

/-- **The residual program.** -/
def tmCsResF (mkg rad sup objs msh ell rec comp app red : ℕ) : Expr :=
  .letE (.call mkg (mk2 (.get (.var 0) (.nat 3)) (.get (.var 0) (.nat 0))))
  (.letE (.call mkg (mk2 (.get (.var 0) (.nat 3)) (.get (.var 0) (.nat 1))))
  (.letE (.call rad (mk2 (.var 1) (.var 2)))
  (.letE (.call mkg (mk2 (.get (.var 0) (.nat 3)) (.var 3)))
  (.letE (.call sup (mk2 (.var 4) (.var 2)))
  (.letE (.call mkg (mk2 (.get (.var 0) (.nat 3)) (.var 5)))
  (.letE (.call objs (mk4 (.get (.var 0) (.nat 2)) (.get (.var 0) (.nat 1))
      (.get (.var 0) (.nat 3)) (.get (.var 0) (.nat 4))))
  (.ite (.length (.var 7)) (tmCsResRec mkg msh ell rec comp app red) .nil)))))))

/-- The functions of the residual program. -/
structure TmCsResAt (P : Program) (f mkg rad sup objs msh sh ell rec comp app red jst : ℕ)
    (rg ax px ay py mx fx my fy first inv : ℕ) : Prop where
  hf : P.funs[f]? = some (tmCsResF mkg rad sup objs msh ell rec comp app red)
  hmkg : P.HasAt mkg (mkGroupFuns mkg)
  hobjs : TmCsObjsAt P objs rg ax px ay py mx fx my fy first app red inv comp jst
  hmsh : P.HasAt msh (mapFuns msh sh)
  hsh : P.funs[sh]? = some (tmCsShF comp)
  hell : P.funs[ell]? = some (tmCsEllF ell)
  hcomp : P.HasAt comp (composeFuns comp)
  happ : P.HasAt app (appendFuns app)
  hred : P.HasAt red (redFuns red jst)

/-- The polynomial part of the cost of the residual program. -/
def tmCsResQ (p : Prim) (Kr Dr Ks Ds X : ℕ) : ℕ :=
  10 ^ 9 * (tmCsObjsK p (20 * X + 20) + Kr * (10 ^ 4 * (X + 1) ^ 6) ^ Dr +
    Ks * (10 ^ 4 * (X + 1) ^ 6) ^ Ds + p.boundSize (10 ^ 4 * (X + 1) ^ 6) +
    10 ^ 12 * (X + 1) ^ 12) ^ 2

set_option maxHeartbeats 3200000 in
/-- **The residual program** (Corollary A.22 through Lemma A.19 and Theorem A.20). -/
theorem tmCs_res_spec (hst : PointwiseStab) (dixon : GI.Cited.DixonDerivedLength) {P : Program}
    {f mkg rad sup objs msh sh ell rec comp app red jst rg ax px ay py mx fx my fy first inv : ℕ}
    (hA : TmCsResAt P f mkg rad sup objs msh sh ell rec comp app red jst rg ax px ay py mx fx my fy
      first inv)
    (hjst : P.prims[jst]? = some (pointwiseStabPrim hst)) {Kr Dr Ks Ds Kc Dc : ℕ}
    (hrad : Iface.TermRadSpec P Kr Dr rad) (hsup : Iface.TermSupSpec P Ks Ds sup)
    (hrec : Iface.TermRecSpec P Kc Dc rec)
    {m q : ℕ} (hm : 0 < m) {Ω : Type*} [RAct (Perm (Fin m)) Ω] {x y : Fin q → Ω}
    {σH σN : List (Perm (Fin m))} {vs : List Val} (hNH : gens σN ≤ gens σH)
    (hn : GI.Multicoset.Normalizes (gens σH) (gens σN)) (hT : TmCsTabOK (gens σH) x y vs)
    {r : Perm (Fin m)} (hr : r ∈ gens σH) {X : ℕ} (hX : (tmCsResIn σH σN vs q r).wt ≤ X)
    (hmX : m ≤ X) (hqX : q ≤ X) :
    FunAll P f (tmCsResIn σH σN vs q r) (fun w cost =>
      AnsC (Equiv.refl (Fin m)) w (tmCsResSet (gens σH) (gens σN) x y r) ∧
      ∃ ℓ : ℕ, (ℓ : ℝ) ≤ 5 * Real.logb 3 m + 1 ∧
        (cost : ℝ) ≤ (tmCsResQ (pointwiseStabPrim hst) Kr Dr Ks Ds X : ℝ) +
          20 * ((5 * ((q : ℝ) + 1) ^ 3 + 1) ^ ℓ * (Kc * (((m + q : ℕ) : ℝ) + 2) ^ Dc))) := by
  set H := gens σH with hH
  set N := gens σN with hN
  set R := radicalPreimage H N with hR
  obtain ⟨hRH, hNR, hRd⟩ := radicalPreimage_spec hNH hn
  have hRn : GI.Multicoset.Normalizes H R := tmCs_rad_normalizes hn
  set a := tmCsResIn σH σN vs q r with ha
  have hRB0 : ∀ ℓ : ℕ, (0 : ℝ) ≤ (5 * ((q : ℝ) + 1) ^ 3 + 1) ^ ℓ *
      (Kc * (((m + q : ℕ) : ℝ) + 2) ^ Dc) := fun ℓ => by positivity
  have hlog0 : ((0 : ℕ) : ℝ) ≤ 5 * Real.logb 3 m + 1 := by
    have : 0 ≤ Real.logb 3 (m : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
    simp; linarith
  refine FunAll.intro hA.hf ?_
  unfold tmCsResF
  -- 1, 2. the group values of `H` and `N`
  have d0 := Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl
  have dm := Det.get' d0 (Det.nat 3) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  have dH := Det.get' d0 (Det.nat 0) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .list (σH.map encPerm)) rfl
  refine EvalAll.letE (Det.call (Det.mk2 dm dH) (mkGroup_spec hA.hmkg σH)) ?_
  rintro _ c1 ⟨rfl, hc1⟩
  have e0 := Det.var' (P := P) (env := [a, encGroup σH]) (i := 0) (v := a) rfl
  have em := Det.get' e0 (Det.nat 3) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  have eN := Det.get' e0 (Det.nat 1) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .list (σN.map encPerm)) rfl
  refine EvalAll.letE (Det.call (Det.mk2 em eN) (mkGroup_spec hA.hmkg σN)) ?_
  rintro _ c2 ⟨rfl, hc2⟩
  -- 3, 4. the radical preimage
  have f1 := Det.var' (P := P) (env := [a, encGroup σH, encGroup σN]) (i := 1) rfl
  have f2 := Det.var' (P := P) (env := [a, encGroup σH, encGroup σN]) (i := 2) rfl
  refine EvalAll.letE (EvalAll.call_spec (Det.mk2 f1 f2) (hrad σH σN hNH hn)) ?_
  rintro _ c3 ⟨cb3, ⟨⟨hsR, rfl, hlR, hgR⟩, hcb3⟩, hc3⟩
  have g0 := Det.var' (P := P) (env := [a, encGroup σH, encGroup σN, .list (hsR.map encPerm)])
    (i := 0) (v := a) rfl
  have gm := Det.get' g0 (Det.nat 3) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  have g3 := Det.var' (P := P) (env := [a, encGroup σH, encGroup σN, .list (hsR.map encPerm)])
    (i := 3) rfl
  refine EvalAll.letE (Det.call (Det.mk2 gm g3) (mkGroup_spec hA.hmkg hsR)) ?_
  rintro _ c4 ⟨rfl, hc4⟩
  -- 5, 6. the solvable supplement
  have hNR' : gens σN ≤ gens hsR := by rw [hgR]; exact hNR
  haveI : ((gens σN).subgroupOf (gens hsR)).Normal := by
    rw [hgR]; exact normal_of_normalizes (hn.mono hRH)
  have hsolvq : IsSolvable ((gens hsR) ⧸ (gens σN).subgroupOf (gens hsR)) := by
    obtain ⟨ℓ, hℓ⟩ := hRd
    rw [← hgR] at hℓ
    exact isSolvable_quot_of_relDerived hℓ
  set env5 := [a, encGroup σH, encGroup σN, .list (hsR.map encPerm), encGroup hsR] with henv5
  have h4 := Det.var' (P := P) (env := env5) (i := 4) (v := encGroup hsR) rfl
  have h2 := Det.var' (P := P) (env := env5) (i := 2) (v := encGroup σN) rfl
  refine EvalAll.letE (EvalAll.call_spec (Det.mk2 h4 h2) (hsup hsR σN hNR' hsolvq)) ?_
  rintro _ c5 ⟨cb5, ⟨S, ⟨hsS, rfl, hlS, hgS⟩, hSR, hSsolv, hSsup, hcb5⟩, hc5⟩
  rw [hgR] at hSR hSsup
  set env6 := env5 ++ [.list (hsS.map encPerm)] with henv6
  have i0 := Det.var' (P := P) (env := env6) (i := 0) (v := a) rfl
  have im := Det.get' i0 (Det.nat 3) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  have i5 := Det.var' (P := P) (env := env6) (i := 5) (v := .list (hsS.map encPerm)) rfl
  refine EvalAll.letE (Det.call (Det.mk2 im i5) (mkGroup_spec hA.hmkg hsS)) ?_
  rintro _ c6 ⟨rfl, hc6⟩
  -- 7. the objects
  have hSN : GI.Multicoset.Normalizes S N := (hn.mono hRH).mono hSR
  have hcov := tmCs_cover hSN hSsup
  set env7 := env6 ++ [encGroup hsS] with henv7
  have j0 := Det.var' (P := P) (env := env7) (i := 0) (v := a) rfl
  have jvs := Det.get' j0 (Det.nat 2) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .list vs) rfl
  have jN := Det.get' j0 (Det.nat 1) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .list (σN.map encPerm)) rfl
  have jm := Det.get' j0 (Det.nat 3) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  have jq := Det.get' j0 (Det.nat 4) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat q) rfl
  have hctx : (tmCsCtx vs σN q).wt ≤ 20 * X + 20 := by
    have h1 := wt_list4_le (.list vs) (.list (σN.map encPerm)) (.nat m) (.nat q)
    have hav : (Val.list vs).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
    have haN : (Val.list (σN.map encPerm)).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
    have ham : (Val.nat m).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
    have haq : (Val.nat q).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
    unfold tmCsCtx; omega
  refine EvalAll.letE (EvalAll.call_spec (Det.mk4 jvs jN jm jq)
    (FunAll.wt_lt (tmCs_objs_spec hst hA.hobjs hjst (tmCs_tab_of hT) hctx (by omega)
      (by omega)))) ?_
  rintro v7 c7 ⟨cb7, ⟨⟨hob, hcb7⟩, hw7⟩, hc7⟩
  -- the cost of steps 1 to 7
  set p := pointwiseStabPrim hst with hp
  set C := tmCsObjsK p (20 * X + 20) + Kr * (10 ^ 4 * (X + 1) ^ 6) ^ Dr +
    Ks * (10 ^ 4 * (X + 1) ^ 6) ^ Ds + p.boundSize (10 ^ 4 * (X + 1) ^ 6) +
    10 ^ 12 * (X + 1) ^ 12 with hC
  have hQ : tmCsResQ p Kr Dr Ks Ds X = 10 ^ 9 * C ^ 2 := rfl
  have hY1 : 1 ≤ X + 1 := by omega
  have hYp : ∀ k ≤ 12, (X + 1) ^ k ≤ (X + 1) ^ 12 := fun k hk => Nat.pow_le_pow_right hY1 hk
  have hm1 : m + 1 ≤ X + 1 := by omega
  have hmp : ∀ k, (m + 1) ^ k ≤ (X + 1) ^ k := fun k => Nat.pow_le_pow_left hm1 k
  have hC12 : 10 ^ 12 * (X + 1) ^ 12 ≤ C := by rw [hC]; omega
  have hCo : tmCsObjsK p (20 * X + 20) ≤ C := by rw [hC]; omega
  have hC1 : 1 ≤ C := by have := Nat.one_le_pow 12 (X + 1) (by omega); omega
  have haX : a.wt ≤ X := hX
  have waH : (Val.list (σH.map encPerm)).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
  have waN : (Val.list (σN.map encPerm)).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
  have wam : (Val.nat m).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
  have waq : (Val.nat q).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
  have wavs : (Val.list vs).wt < a.wt := wt_le_wt_list (by simp [ha, tmCsResIn])
  have hlH : σH.length < X := by
    have := length_lt_wt_list (σH.map encPerm); simp at this; omega
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
  have hmkH := hcube (hmeas _ hlH)
  have hmkN := hcube (hmeas _ hlN)
  have hmkR := hcube (hmeas2 _ hlR)
  have hmkS := hcube (hmeas2 _ hlS)
  have e2 : (2 * (X + 1) ^ 2) ^ 3 = 8 * (X + 1) ^ 6 := by ring
  have e3 : (2 * (X + 1) ^ 3) ^ 3 = 8 * (X + 1) ^ 9 := by ring
  rw [e2] at hmkH hmkN
  rw [e3] at hmkR hmkS
  have hsq : ∀ {b B : ℕ}, b ≤ B → 40 * b ^ 2 ≤ 40 * B ^ 2 := fun h =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)
  have wgH := (wt_encGroup_le σH).trans (hsq (hmeas _ hlH))
  have wgN := (wt_encGroup_le σN).trans (hsq (hmeas _ hlN))
  have e4 : (2 * (X + 1) ^ 2) ^ 2 = 4 * (X + 1) ^ 4 := by ring
  rw [e4] at wgH wgN
  have wgR := wt_encGroup_le_sq hlR
  have wgS := wt_encGroup_le_sq hlS
  have wlR := wt_list_encPerms_le_sq hlR
  have wlS := wt_list_encPerms_le_sq hlS
  have hX6 := hmp 6
  have hpow : ∀ {b : ℕ} (K D : ℕ), b ≤ 10 ^ 4 * (X + 1) ^ 6 → K * b ^ D ≤
      K * (10 ^ 4 * (X + 1) ^ 6) ^ D := fun K D h =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h D)
  have w3 := wt_list2_le (encGroup σH) (encGroup σN)
  have w5 := wt_list2_le (encGroup hsR) (encGroup σN)
  have h46 : (X + 1) ^ 4 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hX61 : 1 ≤ (X + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hcb3' := hcb3.trans (hpow Kr Dr (b := (Val.list [encGroup σH, encGroup σN]).wt + 1)
    (by omega))
  have hcb5' := hcb5.trans (hpow Ks Ds (b := (Val.list [encGroup hsR, encGroup σN]).wt + 1)
    (by omega))
  have wl1 := wt_list2_le (Val.nat m) (Val.list (σH.map encPerm))
  have wl2 := wt_list2_le (Val.nat m) (Val.list (σN.map encPerm))
  have wl3 := wt_list2_le (Val.nat m) (Val.list (hsR.map encPerm))
  have wl4 := wt_list2_le (Val.nat m) (Val.list (hsS.map encPerm))
  have wl5 := wt_list4_le (Val.list vs) (Val.list (σN.map encPerm)) (Val.nat m) (Val.nat q)
  have h6 := hYp 6 (by norm_num)
  have h9 := hYp 9 (by norm_num)
  have hXY : X + 1 ≤ (X + 1) ^ 12 := Nat.le_self_pow (by norm_num) _
  have hmk : mkGroupK = 100000 := rfl
  have h612 := hYp 6 (by norm_num)
  have h412 := hYp 4 (by norm_num)
  have hpre : c1 + c2 + c3 + c4 + c5 + c6 + c7 ≤ 10 * C + v7.wt := by
    rw [hmk] at hmkH hmkN hmkR hmkS hc1 hc2 hc4 hc6
    omega
  have hpart_iff : ((∀ i < q, TmCsHas vs (i * q) 1 q) ∧ (∀ j < q, TmCsHas vs j q q)) ↔
      ((∀ i, ∃ j, (Iso H (x i) (y j)).Nonempty) ∧ (∀ j, ∃ i, (Iso H (x i) (y j)).Nonempty)) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => (tmCs_has_x hT i).1 (h1 i.1 i.2), fun j => (tmCs_has_y hT j).1 (h2 j.1 j.2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i hi => (tmCs_has_x hT ⟨i, hi⟩).2 (h1 ⟨i, hi⟩),
        fun j hj => (tmCs_has_y hT ⟨j, hj⟩).2 (h2 ⟨j, hj⟩)⟩
  rcases hob with ⟨hall, OX, OY, rfl, hlx, hly, hOX, hOY⟩ | ⟨rfl, hnot⟩
  swap
  · -- some row has no partner
    have k7 := Det.var' (P := P) (env := env7 ++ [.list []]) (i := 7) (v := .list []) rfl
    refine (Det.ite_zero (t := tmCsResRec mkg msh ell rec comp app red) (Det.length k7)
      Det.nil).post fun c' hc' => ⟨Or.inl ⟨rfl, ?_⟩, 0, hlog0, ?_⟩
    · exact tmCs_res_empty hNH hn fun h => hnot (hpart_iff.2 h)
    · refine tmCs_cast (cb := 0) ?_ (by simpa using hRB0 0) (hRB0 0)
      have hw0 : (Val.list []).wt ≤ 5 := by decide
      have hCC : C ≤ C ^ 2 := Nat.le_self_pow (by norm_num) _
      rw [hQ]
      simp only [List.length_nil] at hc'
      omega
  -- every row has a partner
  obtain ⟨hpx, hpy⟩ := hpart_iff.1 hall
  set v7 := Val.list [tmGlObjsVal OX, tmGlObjsVal OY] with hv7
  have k7 := Det.var' (P := P) (env := env7 ++ [v7]) (i := 7) (v := v7) rfl
  refine EvalAll.ite (Det.length k7) (fun _ _ h => ⟨_, h.1⟩) fun z cz ⟨hz, hcz⟩ => ?_
  cases hz
  rw [if_neg (by simp [hv7])]
  unfold tmCsResRec
  -- the multisets of the objects
  have hmsX : tmGlMs OX = (types N x).map (tmCsF H N y) :=
    tmCs_ms_list hlx fun i hi => tmCs_x_obj hT hNH hn rfl (hOX i hi)
  have hmsY : tmGlMs OY = (types N y).map (tmCsF H N y) :=
    tmCs_ms_list hly fun j hj => tmCs_y_obj hT hNH hn rfl (hOY j hj)
  have hmain := tmCs_res_main hNH hn hRH hRn hSR hNR hcov hSN hmsX hmsY hpx hr
  -- 8. the trivial group
  set env8 := env7 ++ [v7] with henv8
  have l0 := Det.var' (P := P) (env := env8) (i := 0) (v := a) rfl
  have lm := Det.get' l0 (Det.nat 3) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  refine EvalAll.letE (Det.call (Det.mk2 lm Det.nil) (mkGroup_spec hA.hmkg ([] : List (Perm (Fin m)))))
    ?_
  rintro _ c8 ⟨rfl, hc8⟩
  -- 9. the shifted objects of `x`
  set env9 := env8 ++ [encGroup ([] : List (Perm (Fin m)))] with henv9
  have n0 := Det.var' (P := P) (env := env9) (i := 0) (v := a) rfl
  have nr := Det.get' n0 (Det.nat 5) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := encPerm r) rfl
  have n7 := Det.var' (P := P) (env := env9) (i := 7) (v := v7) rfl
  have nX := Det.get' n7 (Det.nat 0) (vs := [tmGlObjsVal OX, tmGlObjsVal OY])
    (v := .list (OX.map tmGlObjVal)) rfl
  have hv7C : v7.wt < C := by omega
  have hxsv : (Val.list (OX.map tmGlObjVal)).wt < v7.wt := wt_le_wt_list (by simp [hv7, tmGlObjsVal])
  have hr4 := wt_encPerm_le r
  have hm2 := hmp 2
  have hm3 := hmp 3
  have h2_12 := hYp 2 (by norm_num)
  have h3_12 := hYp 3 (by norm_num)
  have hshf : ∀ xv ∈ OX.map tmGlObjVal, FunAll P sh (.list [encPerm r, xv]) (fun w cost =>
      ((∀ o, xv = tmGlObjVal o → w = tmGlObjVal (tmCsSh r o)) ∧ w.wt < 200 * C) ∧
        cost ≤ 200 * C) := by
    intro xv hxv
    have hxw : xv.wt < (Val.list (OX.map tmGlObjVal)).wt := wt_le_wt_list hxv
    obtain ⟨o, -, rfl⟩ := List.mem_map.1 hxv
    refine (FunAll.wt_lt (tmCs_sh_spec hA.hsh hA.hcomp r o)).mono ?_
    rintro w c ⟨⟨rfl, hc⟩, hwc⟩
    suffices hcb : c ≤ 200 * C from
      ⟨⟨fun o' ho' => by rw [tmCs_objVal_inj ho'], by omega⟩, hcb⟩
    have : (tmGlObjVal (tmCsSh r o)).wt ≤ 2 * ((tmGlObjVal o).wt + 4 * (m + 1) ^ 2) + 7 := by
      have h1 := wt_encPerm_le (o.2.2 * r)
      have h2 := wt_list3_le (.nat o.1) (encGroup o.2.1) (encPerm (o.2.2 * r))
      have h3 := sum_wt_lt_wt_list [.nat o.1, encGroup o.2.1, encPerm o.2.2]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h3
      have e1 : (tmGlObjVal (tmCsSh r o)).wt =
          (Val.list [.nat o.1, encGroup o.2.1, encPerm (o.2.2 * r)]).wt := rfl
      have e2 : (tmGlObjVal o).wt = (Val.list [.nat o.1, encGroup o.2.1, encPerm o.2.2]).wt := rfl
      omega
    have := wt_list2_le (encPerm r) (tmGlObjVal o)
    have hpk : permK = 30000 := rfl
    rw [hpk] at hc
    omega
  refine EvalAll.letE (EvalAll.call_spec (Det.mk2 nr nX) (map_spec hA.hmsh hshf)) ?_
  rintro _ c9 ⟨cb9, ⟨wsX, rfl, hwsX, hcb9⟩, hc9⟩
  have hws := tmCs_map_sh r OX wsX (hwsX.imp fun _ _ h => h.1)
  set OX' := OX.map (tmCsSh r) with hOX'
  -- 10. the fuel
  set env10 := env9 ++ [Val.list wsX] with henv10
  have p0 := Det.var' (P := P) (env := env10) (i := 0) (v := a) rfl
  have pm := Det.get' p0 (Det.nat 3) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
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
  -- 11. the recursion on `(S, 1)`
  have hok : ∀ o ∈ OX' ++ OY, o.2.1.length ≤ m ^ 2 ∧ ∃ hc : o.1 < q,
      ∀ z, z ∈ gens o.2.1 ↔ ∃ a ∈ Aut H (y ⟨o.1, hc⟩), ∃ k ∈ N, z = a * k := by
    intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨o0, ho0, rfl⟩ := List.mem_map.1 ho
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ho0
      have hxo := hOX i (by omega)
      obtain ⟨hc, hg⟩ := tmCs_x_gens (i := ⟨i, by omega⟩) hT hn rfl hxo
      exact ⟨hxo.choose_spec.choose_spec.2.2.2.2.2, hc, hg⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ho
      have hyo := hOY j (by omega)
      obtain ⟨hc, hg⟩ := tmCs_y_gens (j := ⟨j, by omega⟩) hT hn rfl hyo
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlen⟩ := hyo
      exact ⟨hlen, hc, hg⟩
  have hrecok : TmRecObjOK q (OX' ++ OY) := by
    intro o ho
    obtain ⟨hlo, hc, hgo⟩ := hok o ho
    refine ⟨hlo, by omega, fun o' ho' he => ?_⟩
    obtain ⟨-, hc', hgo'⟩ := hok o' ho'
    ext z
    rw [hgo z, hgo' z]
    have : (⟨o.1, hc⟩ : Fin q) = ⟨o'.1, hc'⟩ := Fin.ext he
    rw [this]
  have hsolvS : IsSolvable (gens hsS) := by rw [hgS]; exact hSsolv
  have hnorm0 : GI.Multicoset.Normalizes (gens hsS) (gens ([] : List (Perm (Fin m)))) := by
    rw [tmCs_gens_nil]; intro g _ k hk; rw [Subgroup.mem_bot] at hk ⊢; rw [hk]; group
  have hfix0 : ∀ Z : Multiset (CObj ℕ (Perm (Fin m))),
      Fixes (gens ([] : List (Perm (Fin m)))) Z := by
    intro Z k hk z _; rw [tmCs_gens_nil, Subgroup.mem_bot] at hk; rw [hk, act_one]
  have hrel : relDerived (gens hsS) (gens ([] : List (Perm (Fin m)))) L ≤
      gens ([] : List (Perm (Fin m))) := by
    refine relDerived_le_of_solvable (by rw [tmCs_gens_nil]; exact bot_le) hnorm0 ?_
    have hge := tmCs_ell_ge hm (L := L) (by rw [← ht5]; exact htL)
    simpa using dixon m (gens hsS) hsolvS L (by simpa using hge)
  have hrecF := hrec q L hsS [] OX' OY hsolvS (by rw [tmCs_gens_nil]; exact bot_le) hnorm0 hrel
    (tmCs_ell_le_sq (by rw [← ht5]; exact hL2)) (hfix0 _) (hfix0 _) hlS (by simp)
    (by simp [hOX', hlx]) (by omega) hrecok
  set env11 := env10 ++ [Val.nat L] with henv11
  have r10 := Det.var' (P := P) (env := env11) (i := 10) (v := .nat L) rfl
  have r6 := Det.var' (P := P) (env := env11) (i := 6) (v := encGroup hsS) rfl
  have r8 := Det.var' (P := P) (env := env11) (i := 8) (v := encGroup ([] : List (Perm (Fin m))))
    rfl
  have r9 := Det.var' (P := P) (env := env11) (i := 9) (v := .list wsX) rfl
  rw [hws] at r9
  have r7 := Det.var' (P := P) (env := env11) (i := 7) (v := v7) rfl
  have r7Y := Det.get' r7 (Det.nat 1) (vs := [tmGlObjsVal OX, tmGlObjsVal OY])
    (v := tmGlObjsVal OY) rfl
  have darg := Det.snoc (Det.mk4 r10 r6 r8 r9) r7Y
  refine EvalAll.letE (EvalAll.call_spec darg hrecF) ?_
  rintro u c11 ⟨cb11, ⟨hans, hcb11⟩, hc11⟩
  have hmsX' : tmGlMs OX' = tmGlMs OX ↼ r := tmCs_ms_shift OX r
  rw [hmsX', hgS] at hans
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
    have hlen0 : ([] : List (Perm (Fin m))).length = 0 := rfl
    rw [hlen0] at hc8
    have hmk8 : 100000 * ((0 + 2) * (m + 1)) ^ 3 ≤ 8 * 10 ^ 5 * (X + 1) ^ 3 := by
      have : ((0 + 2) * (m + 1)) ^ 3 = 8 * (m + 1) ^ 3 := by ring
      rw [this]; omega
    have wg0 := wt_encGroup_le_sq (n := m) (hs := []) (by simp)
    have w8 := wt_list2_le (Val.nat m) (Val.list [])
    have hl0 : (Val.list []).wt ≤ 5 := by decide
    -- the map
    have hsumK : ∀ (l : List Val) (k : ℕ), (l.map fun _ => k).sum = l.length * k := by
      intro l k; induction l with
      | nil => simp
      | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
    rw [hsumK, List.length_map, hlx] at hcb9
    have hwsw := tm_wt_forall₂ (W := 200 * C) (fun _ _ h => h.2.le) hwsX.flip
    rw [List.length_map, hlx] at hwsw
    have hqC1 : q * (2 * (200 * C) + 1) ≤ 401 * (X * C) := by
      calc q * (2 * (200 * C) + 1) ≤ X * (401 * C) := Nat.mul_le_mul hqX (by omega)
        _ = 401 * (X * C) := by ring
    have hXC : (X + 1) * C = X * C + C := by ring
    have hY2C : (X + 1) ^ 2 ≤ C := by omega
    have w9 := wt_list2_le (encPerm r) (Val.list (OX.map tmGlObjVal))
    have hW9 : (Val.list [encPerm r, Val.list (List.map tmGlObjVal OX)]).wt + (Val.list wsX).wt + 1
        ≤ 1000 * ((X + 1) * C) := by omega
    have hmap9 : mapK * (q + 1) * ((Val.list [encPerm r, Val.list (List.map tmGlObjVal OX)]).wt +
        (Val.list wsX).wt + 1) ≤ 10 ^ 6 * C ^ 2 := by
      calc mapK * (q + 1) * ((Val.list [encPerm r, Val.list (List.map tmGlObjVal OX)]).wt +
            (Val.list wsX).wt + 1) ≤ 1000 * (X + 1) * (1000 * ((X + 1) * C)) :=
            Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) hW9
        _ = 10 ^ 6 * ((X + 1) ^ 2 * C) := by ring
        _ ≤ 10 ^ 6 * (C * C) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hY2C)
        _ = 10 ^ 6 * C ^ 2 := by ring
    have hqC : q * (200 * C) ≤ 200 * C ^ 2 := by
      calc q * (200 * C) ≤ C * (200 * C) := Nat.mul_le_mul_right _ (by omega)
        _ = 200 * C ^ 2 := by ring
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
    have wgS0 := wgS
    have hwsX' : (Val.list (List.map tmGlObjVal OX')).wt ≤ q * (2 * (200 * C) + 1) + 4 := by
      rw [← hws]; exact hwsw
    have hOYw : (tmGlObjsVal OY).wt < v7.wt := wt_le_wt_list (by simp [hv7])
    have w11a := wt_list4_le (Val.nat L) (encGroup hsS) (encGroup ([] : List (Perm (Fin m))))
      (Val.list (List.map tmGlObjVal OX'))
    have w11b := wt_list_le
      ([Val.nat L, encGroup hsS, encGroup ([] : List (Perm (Fin m))),
        Val.list (List.map tmGlObjVal OX')] ++
        [tmGlObjsVal OY])
    simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] at w11b
    have hCC : C ≤ C ^ 2 := Nat.le_self_pow (by norm_num) _
    have hXC2 : X * C ≤ C ^ 2 := by
      calc X * C ≤ C * C := Nat.mul_le_mul_right _ (by omega)
        _ = C ^ 2 := by ring
    rw [hmk] at hc8
    have e11 : (Val.list ([Val.nat L, encGroup hsS, encGroup ([] : List (Perm (Fin m))),
        Val.list (List.map tmGlObjVal OX')] ++ [tmGlObjsVal OY])).wt =
        (Val.list [Val.nat L, encGroup hsS, encGroup ([] : List (Perm (Fin m))),
        Val.list (List.map tmGlObjVal OX'), tmGlObjsVal OY]).wt := rfl
    rw [e11] at hc11
    have ews : (Val.list wsX).wt = (Val.list (List.map tmGlObjVal OX')).wt := by rw [hws]
    omega
  have hset : tmCsResSet H N x y r =
      {h | ∃ s ∈ Iso S (tmGlMs OX ↼ r) (tmGlMs OY), ∃ k ∈ N, h = r * s * k} := hmain
  set env12 := env11 ++ [u] with henv12
  have s11 := Det.var' (P := P) (env := env12) (i := 11) (v := u) rfl
  rcases hans with ⟨rfl, hI⟩ | ⟨x0, gs, rfl, hgl, -⟩
  · -- the transporter on the supplement is empty
    refine (Det.ite_zero (t := tmCsResTail comp app red) (Det.length s11) Det.nil).post
      fun c' hc' => ⟨Or.inl ⟨rfl, ?_⟩, L, hLm, ?_⟩
    · rw [hset, hI]; simp
    · refine tmCs_cast (cb := cb11) ?_ hcb11 (hRB0 L)
      have hw0 : (Val.list []).wt ≤ 5 := by decide
      have hCC : C ≤ C ^ 2 := Nat.le_self_pow (by norm_num) _
      simp only [List.length_nil] at hc'
      rw [hQ]
      omega
  have hI := tmCs_ansC_cons hans' rfl
  refine EvalAll.ite (Det.length s11) (fun _ _ h => ⟨_, h.1⟩) fun z cz ⟨hz, hcz⟩ => ?_
  cases hz
  rw [if_neg (by simp)]
  unfold tmCsResTail
  -- 12. the representative `r x0`
  have t0 := Det.var' (P := P) (env := env12) (i := 0) (v := a) rfl
  have tr := Det.get' t0 (Det.nat 5) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := encPerm r) rfl
  have tx := Det.get' s11 (Det.nat 0) (vs := [encPerm x0, encGroup gs]) (v := encPerm x0) rfl
  refine EvalAll.letE (Det.call (Det.mk2 tr tx) (compose_spec hA.hcomp r x0)) ?_
  rintro _ c12 ⟨rfl, hc12⟩
  -- 13. the generators `gs, σN`
  set env13 := env12 ++ [encPerm (r * x0)] with henv13
  have u11 := Det.var' (P := P) (env := env13) (i := 11) (v := .list [encPerm x0, encGroup gs]) rfl
  have ugs := Det.get' u11 (Det.nat 1) (vs := [encPerm x0, encGroup gs]) (v := encGroup gs) rfl
  have ul := Det.get' ugs (Det.nat 1) (vs := [.nat m, .list ((1 :: gs).map encPerm)])
    (v := .list ((1 :: gs).map encPerm)) rfl
  have u0 := Det.var' (P := P) (env := env13) (i := 0) (v := a) rfl
  have uN := Det.get' u0 (Det.nat 1) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .list (σN.map encPerm)) rfl
  set L0 := Val.list ((1 :: gs).map encPerm ++ σN.map encPerm) with hL0
  have happ' : FunDet P app (.list [.list ((1 :: gs).map encPerm), .list (σN.map encPerm)]) L0
      (loopModK * ((σN.map encPerm).length + 1) *
        ((Val.list [.list ((1 :: gs).map encPerm), .list (σN.map encPerm)]).wt +
          (σN.map encPerm).length + L0.wt + 1)) :=
    (append_spec hA.happ _ _).mono fun w c' ⟨h1, h2⟩ => ⟨h1, by rw [h1] at h2; exact h2⟩
  refine EvalAll.letE (Det.call (Det.mk2 ul uN) happ') ?_
  rintro _ c13 ⟨rfl, hc13⟩
  -- 14. cut to `m²` generators
  set env14 := env13 ++ [L0] with henv14
  have hgv : GroupVal m (.list [.nat m, L0]) (gens (gs ++ σN)) := ⟨gs ++ σN, by
    simp [hL0, encGroup, GI.Cited.encPerms], rfl⟩
  have w0 := Det.var' (P := P) (env := env14) (i := 0) (v := a) rfl
  have wm := Det.get' w0 (Det.nat 3) (vs := [.list (σH.map encPerm), .list (σN.map encPerm),
    .list vs, .nat m, .nat q, encPerm r]) (v := .nat m) rfl
  have wL := Det.var' (P := P) (env := env14) (i := 13) (v := L0) rfl
  refine EvalAll.letE (EvalAll.call_spec (Det.mk2 wm (Det.mk2 wm wL))
    (red_spec hst hA.hred hjst hgv)) ?_
  rintro _ c14 ⟨cb14, ⟨hs, rfl, hgens, hlen, hcb14⟩, hc14⟩
  have o12 := Det.var' (P := P) (env := env14 ++ [encGroup hs]) (i := 12) (v := encPerm (r * x0)) rfl
  have o14 := Det.var' (P := P) (env := env14 ++ [encGroup hs]) (i := 14) (v := encGroup hs) rfl
  refine (Det.mk2 o12 o14).post fun c' hc' => ⟨Or.inr ⟨r * x0, hs, rfl, hlen, ?_⟩, L, hLm, ?_⟩
  · have hσS : gens gs ≤ S := tmCs_gens_le (fun g hg => hg.1) hI
    rw [tmCs_toFin_refl, hset, tmCs_res_coset hσS hSN rfl hI, ← hgens]
    rfl
  · refine tmCs_cast (cb := cb11) ?_ hcb11 (hRB0 L)
    have hCC : C ≤ C ^ 2 := Nat.le_self_pow (by norm_num) _
    have hlen2 : [encPerm x0, encGroup gs].length = 2 := rfl
    rw [hlen2] at hcz
    have hX16 : X + 1 ≤ (X + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    have hm9 := hmp 9
    have hx0 := wt_encPerm_le x0
    have hrx := wt_encPerm_le (r * x0)
    have hgsw := wt_encGroup_le_sq hgl
    have hhsw := wt_encGroup_le_sq hlen
    have hl1 : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
      wt_le_wt_list (by simp [encGroup, GI.Cited.encPerms])
    have hlen1 := length_lt_wt_list ((1 :: gs).map encPerm)
    have hlenN := length_lt_wt_list (σN.map encPerm)
    have hL0w : L0.wt ≤ 960 * (X + 1) ^ 6 + 3 * X + 4 := by
      have h1 := wt_list_le ((1 :: gs).map encPerm ++ σN.map encPerm)
      have h2 := sum_wt_lt_wt_list ((1 :: gs).map encPerm)
      have h3 := sum_wt_lt_wt_list (σN.map encPerm)
      rw [List.map_append, List.sum_append, List.length_append] at h1
      rw [hL0]
      omega
    have wa := wt_list2_le (Val.nat m) L0
    have wb := wt_list2_le (Val.nat m) (Val.list [Val.nat m, L0])
    have wc := wt_list2_le (Val.list [Val.nat m, L0]) (Val.list [])
    have hl0 : (Val.list []).wt ≤ 5 := by decide
    have hbd : (pointwiseStabPrim hst).bound (Val.list [Val.list [Val.nat m, L0], Val.list []]) ≤
        p.boundSize (10 ^ 4 * (X + 1) ^ 6) := by
      apply Prim.bound_le
      have := (Val.list [Val.list [Val.nat m, L0], Val.list []]).size_le_wt
      omega
    have wd := wt_list2_le (Val.list ((1 :: gs).map encPerm)) (Val.list (σN.map encPerm))
    have hW13 : (Val.list [Val.list (List.map encPerm (1 :: gs)), Val.list (List.map encPerm σN)]).wt +
        (List.map encPerm σN).length + L0.wt + 1 ≤ 100 * C := by
      simp only [List.length_map] at hlenN ⊢
      omega
    have hloop13 : loopModK * ((List.map encPerm σN).length + 1) *
        ((Val.list [Val.list (List.map encPerm (1 :: gs)), Val.list (List.map encPerm σN)]).wt +
          (List.map encPerm σN).length + L0.wt + 1) ≤ 10 ^ 5 * C ^ 2 := by
      calc loopModK * ((List.map encPerm σN).length + 1) *
            ((Val.list [Val.list (List.map encPerm (1 :: gs)),
              Val.list (List.map encPerm σN)]).wt + (List.map encPerm σN).length + L0.wt + 1)
          ≤ 1000 * C * (100 * C) := by
            apply Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) ?_) hW13
            simp only [List.length_map]; omega
        _ = 10 ^ 5 * C ^ 2 := by ring
    have hpk : permK = 30000 := rfl
    rw [hpk] at hc12
    have wp2 := wt_list2_le (encPerm r) (encPerm x0)
    have wo := wt_list2_le (encPerm (r * x0)) (encGroup hs)
    rw [hQ]
    omega

end GI.Impl
