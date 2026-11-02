import Workspace.Impl.TermJProgLocRow

/-!
# The local transporter of a class (program)

Given a class `h` that has a matching of local tests (some `π` with an element of
`Iso_H(x_a, y_{π a})` in `h N` for every `a`), the program returns one local transporter
`z = (d; σ)` of class `h`, as a permutation of `Fin (m q)`.

The steps of `tmJLMainF`, on `[h, vs, σN, q, m]`:
1. the points `0, …, q - 1`, and the 0/1 matrix of local tests, row by row (`tmJLRowF`,
   `tmJLBitF`, in `TermJProgLocBit`, `TermJProgLocRow`);
2. a matching `σ` read off by ranks (`tmJLPiF`, `tmJMatchO`, in `TermJProgLocPi`);
3. the group value `⟨σN⟩`;
4. for every `a`, with the entry `[g, gs]` of `(a, σ a)`: NormalizedFactor of `g⁻¹ h` in
   `⟨gs⟩ ⟨σN⟩` gives `g⁻¹ h = s n`, and `d a = g s` (`tmJLDF`);
5. the pair `(d, σ)` on `Fin (m q)` (`tmJPairF`).

`tmJL_spec` is the result. `TmJLAt` lists where the pieces sit, and `TmJLAt.of_hasAt` builds it
from the seven functions `tmJLFuns` at a base `b` and the library modules.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv
open GI.Cited (Val encPerm encPerms encGroup gens)
open scoped Pointwise

variable {m q : ℕ}

/-! ### The program -/

/-- **The main function**, on `inp = [h, vs, σN, q, m]`. -/
def tmJLMainF (rg ap mR mP mD pr : ℕ) : Expr :=
  .letE (.call rg (arg 3))
  (.letE (.call mR (mk2 (.var 0) (.var 1)))
  (.letE (.call mP (mk2 (mk2 (.var 2) (.var 1)) (.var 1)))
  (.letE (mk2 (arg 4) (.call ap (mk2 (mk1 (.call rg (arg 4))) (arg 2))))
  (.letE (.call mD (mk2 (mk3 (.var 0) (.var 3) (.var 4)) (.var 1)))
  (.call pr (mk4 (.var 5) (.var 3) (arg 3) (arg 4)))))))

/-- The seven own functions, in order: main, row, test, matched column, rank test, column test,
local element. They sit at `b, …, b + 6`; the map and filter modules call them there. -/
def tmJLFuns (rg ap cp iv en mR mB mP fR fC mD pr jm jf : ℕ) : List Expr :=
  [tmJLMainF rg ap mR mP mD pr, tmJLRowF rg mB, tmJLBitF jm ap cp iv, tmJLPiF fR fC, tmJLRkF en,
    tmJLColF, tmJLDF jf cp iv]

theorem tmJLFuns_length (rg ap cp iv en mR mB mP fR fC mD pr jm jf : ℕ) :
    (tmJLFuns rg ap cp iv en mR mB mP fR fC mD pr jm jf).length = 7 := rfl

/-- Where the pieces sit: the own functions at `b, …, b + 6`, and the library modules. -/
structure TmJLAt (P : Program) (b rg ap cp iv en mR mB mP fR fC mD pr prg ptb ptbe jm jf : ℕ) :
    Prop where
  hmain : P.funs[b]? = some (tmJLMainF rg ap mR mP mD pr)
  hrow : P.funs[b + 1]? = some (tmJLRowF rg mB)
  hbit : P.funs[b + 2]? = some (tmJLBitF jm ap cp iv)
  hpi : P.funs[b + 3]? = some (tmJLPiF fR fC)
  hrk : P.funs[b + 4]? = some (tmJLRkF en)
  hcol : P.funs[b + 5]? = some tmJLColF
  hd : P.funs[b + 6]? = some (tmJLDF jf cp iv)
  hrg : P.HasAt rg (rangeFuns rg)
  hap : P.HasAt ap (appendFuns ap)
  hcp : P.HasAt cp (composeFuns cp)
  hiv : P.HasAt iv (invFuns iv)
  hen : P.HasAt en (eqNatsFuns en)
  hmR : P.HasAt mR (mapFuns mR (b + 1))
  hmB : P.HasAt mB (mapFuns mB (b + 2))
  hmP : P.HasAt mP (mapFuns mP (b + 3))
  hfR : P.HasAt fR (filterFuns fR (b + 4))
  hfC : P.HasAt fC (filterFuns fC (b + 5))
  hmD : P.HasAt mD (mapFuns mD (b + 6))
  hpair : TmJPairAt P pr prg ptb ptbe

/-- The own functions at `b` and the library modules give `TmJLAt`. -/
theorem TmJLAt.of_hasAt {P : Program} {b rg ap cp iv en mR mB mP fR fC mD pr prg ptb ptbe jm jf : ℕ}
    (h : P.HasAt b (tmJLFuns rg ap cp iv en mR mB mP fR fC mD pr jm jf))
    (hrg : P.HasAt rg (rangeFuns rg)) (hap : P.HasAt ap (appendFuns ap))
    (hcp : P.HasAt cp (composeFuns cp)) (hiv : P.HasAt iv (invFuns iv))
    (hen : P.HasAt en (eqNatsFuns en)) (hmR : P.HasAt mR (mapFuns mR (b + 1)))
    (hmB : P.HasAt mB (mapFuns mB (b + 2))) (hmP : P.HasAt mP (mapFuns mP (b + 3)))
    (hfR : P.HasAt fR (filterFuns fR (b + 4))) (hfC : P.HasAt fC (filterFuns fC (b + 5)))
    (hmD : P.HasAt mD (mapFuns mD (b + 6))) (hpair : TmJPairAt P pr prg ptb ptbe) :
    TmJLAt P b rg ap cp iv en mR mB mP fR fC mD pr prg ptb ptbe jm jf where
  hmain := by simpa using h 0 (by simp [tmJLFuns])
  hrow := h 1 (by simp [tmJLFuns])
  hbit := h 2 (by simp [tmJLFuns])
  hpi := h 3 (by simp [tmJLFuns])
  hrk := h 4 (by simp [tmJLFuns])
  hcol := h 5 (by simp [tmJLFuns])
  hd := h 6 (by simp [tmJLFuns])
  hrg := hrg
  hap := hap
  hcp := hcp
  hiv := hiv
  hen := hen
  hmR := hmR
  hmB := hmB
  hmP := hmP
  hfR := hfR
  hfC := hfC
  hmD := hmD
  hpair := hpair

/-! ### The cost bound -/

/-- The cost of the steps, in `Y = wt inp + 1`. -/
def tmJLMainC (pm pf : Prim) (Y : ℕ) : ℕ :=
  Y * tmJLRowC pm Y + Y * tmJLPiC Y + Y * tmJLDC pf Y + 2 * 10 ^ 13 * Y ^ 12

/-- The constant of the cost bound. -/
def tmJLK (pm pf : Prim) : ℕ := 10 ^ 15 * (pm.c + 1) * (pf.c + 1) * 202 ^ (pm.k + pf.k)

/-- The degree of the cost bound. -/
def tmJLD (pm pf : Prim) : ℕ := 2 * (pm.k + pf.k) + 12

theorem tmJL_mainC_le (pm pf : Prim) {Y : ℕ} (hY : 1 ≤ Y) :
    tmJLMainC pm pf Y ≤ tmJLK pm pf * Y ^ tmJLD pm pf := by
  set B := (pm.c + 1) * (pf.c + 1) * 202 ^ (pm.k + pf.k) with hB
  set D := tmJLD pm pf with hD
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hY2 : 1 ≤ Y ^ 2 := Nat.one_le_pow _ _ hY
  have p1 : (100 * Y ^ 2 + 2) ^ pm.k ≤ 202 ^ pm.k * Y ^ (2 * pm.k) :=
    calc (100 * Y ^ 2 + 2) ^ pm.k ≤ (202 * Y ^ 2) ^ pm.k := Nat.pow_le_pow_left (by omega) _
      _ = 202 ^ pm.k * Y ^ (2 * pm.k) := by rw [mul_pow, ← pow_mul]
  have p2 : (200 * Y ^ 2 + 2) ^ pf.k ≤ 202 ^ pf.k * Y ^ (2 * pf.k) :=
    calc (200 * Y ^ 2 + 2) ^ pf.k ≤ (202 * Y ^ 2) ^ pf.k := Nat.pow_le_pow_left (by omega) _
      _ = 202 ^ pf.k * Y ^ (2 * pf.k) := by rw [mul_pow, ← pow_mul]
  have c1 : pm.c * 202 ^ pm.k ≤ B :=
    Nat.mul_le_mul (le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega)))
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have c2 : pf.c * 202 ^ pf.k ≤ B := by
    rw [hB, Nat.mul_comm (pm.c + 1)]
    exact Nat.mul_le_mul (le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega)))
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have T1 : Y * (Y * (pm.c * (100 * Y ^ 2 + 2) ^ pm.k)) ≤ B * Y ^ D :=
    calc _ ≤ Y * (Y * (pm.c * (202 ^ pm.k * Y ^ (2 * pm.k)))) := by gcongr
      _ = (pm.c * 202 ^ pm.k) * Y ^ (2 * pm.k + 2) := by ring
      _ ≤ B * Y ^ D := Nat.mul_le_mul c1 (Nat.pow_le_pow_right hY (by rw [hD, tmJLD]; omega))
  have T2 : Y * (pf.c * (200 * Y ^ 2 + 2) ^ pf.k) ≤ B * Y ^ D :=
    calc _ ≤ Y * (pf.c * (202 ^ pf.k * Y ^ (2 * pf.k))) := by gcongr
      _ = (pf.c * 202 ^ pf.k) * Y ^ (2 * pf.k + 1) := by ring
      _ ≤ B * Y ^ D := Nat.mul_le_mul c2 (Nat.pow_le_pow_right hY (by rw [hD, tmJLD]; omega))
  have T3 : Y ^ 12 ≤ B * Y ^ D :=
    le_trans (Nat.pow_le_pow_right hY (by rw [hD, tmJLD]; omega)) (Nat.le_mul_of_pos_left _ hB1)
  have q4 : Y ^ 4 ≤ Y ^ 12 := Nat.pow_le_pow_right hY (by norm_num)
  have q5 : Y ^ 5 ≤ Y ^ 12 := Nat.pow_le_pow_right hY (by norm_num)
  have q6 : Y ^ 6 ≤ Y ^ 12 := Nat.pow_le_pow_right hY (by norm_num)
  have e1 : tmJLMainC pm pf Y = Y * (Y * (pm.c * (100 * Y ^ 2 + 2) ^ pm.k)) +
      Y * (pf.c * (200 * Y ^ 2 + 2) ^ pf.k) + 10 ^ 7 * Y ^ 6 + 10 ^ 6 * Y ^ 4 + 10 ^ 8 * Y ^ 4 +
        10 ^ 7 * Y ^ 5 + 2 * 10 ^ 13 * Y ^ 12 := by
    unfold tmJLMainC tmJLRowC tmJLBitC tmJLPiC tmJLDC; ring
  have e2 : tmJLK pm pf * Y ^ D = 10 ^ 15 * (B * Y ^ D) := by
    rw [tmJLK, hB]; ring
  rw [e1, e2]
  omega

/-! ### The specification -/

/-- From the entries of a list related to the points, a function that gives them. -/
theorem tmJL_choose {β : Type} {Pr : Fin q → β → Prop} {enc : β → Val} {ws : List Val}
    (h : List.Forall₂ (fun x w => ∀ a : Fin q, x = .nat a → ∃ d, Pr a d ∧ w = enc d)
      ((List.finRange q).map fun a : Fin q => Val.nat (a : ℕ)) ws) :
    ∃ d : Fin q → β, (∀ a, Pr a (d a)) ∧ ws = (List.finRange q).map fun a => enc (d a) := by
  have hl : ws.length = q := by rw [← h.length_eq]; simp
  have hR := (List.forall₂_iff_get.1 h).2
  have hx : ∀ a : Fin q, ∃ d, Pr a d ∧ ws[(a : ℕ)]'(by rw [hl]; exact a.2) = enc d := by
    intro a
    have := hR a (by simp) (by rw [hl]; exact a.2)
    simpa using this a (by simp)
  choose d hd using hx
  refine ⟨d, fun a => (hd a).1, List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_⟩
  have := (hd ⟨i, by rw [hl] at h1; exact h1⟩).2
  simpa using this

section Setting

variable {C : Type}

/-- **The local transporter of a class.** On `[h, vs, σN, q, m]`, when the class `h` has a
matching of local tests, the result is a pair `(d, π)` on `Fin (m q)` whose coordinates are local
elements of the class: `d a ∈ Iso_H(x_a, y_{π a})` and `h⁻¹ d a ∈ N`. -/
theorem tmJL_spec (hm : GI.Cited.Membership) (hfac : GI.Cited.NormalizedFactor) {P : Program}
    {b rg ap cp iv en mR mB mP fR fC mD pr prg ptb ptbe jm jf : ℕ}
    (hA : TmJLAt P b rg ap cp iv en mR mB mP fR fC mD pr prg ptb ptbe jm jf)
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    (hq : 0 < q) (H N : Subgroup (Perm (Fin m))) (hn : GI.Multicoset.Normalizes H N)
    (σN : List (Perm (Fin m))) (hσN : gens σN = N) (x y : Fin q → Fin m → C)
    (A : Fin q × Fin q → Set (Perm (Fin m)))
    (hAdef : ∀ a j, A (a, j) = {u | u ∈ H ∧ x a ∘ ⇑u = y j}) (vs : List Val)
    (hvs : List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (A ij)) vs (tmCosets q))
    (h : Perm (Fin m)) (hmatch : ∃ π : Perm (Fin q), ∀ a, ∃ u ∈ A (a, π a), h⁻¹ * u ∈ N) :
    FunAll P b (.list [encPerm h, .list vs, .list (σN.map encPerm), .nat q, .nat m])
      (fun w cost => (∃ (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)),
          (∀ a, d a ∈ A (a, π a) ∧ h⁻¹ * d a ∈ N) ∧
          w = encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)))) ∧
        cost ≤ tmJLK (membershipPrim hm) (normalizedFactorPrim hfac) *
          ((Val.list [encPerm h, .list vs, .list (σN.map encPerm), .nat q, .nat m]).wt + 1) ^
            tmJLD (membershipPrim hm) (normalizedFactorPrim hfac)) := by
  have hlen : vs.length = q * q := by rw [hvs.length_eq, length_tmCosets]; ring
  obtain ⟨wm, wqq, wq, wh, wvs, wσ, wnq, wnm⟩ := tmJL_inp_wt h σN hq hlen
  have einp : Val.list [encPerm h, .list vs, .list (σN.map encPerm), .nat q, .nat m] =
      tmJLInp h vs σN q := rfl
  rw [einp]
  set inp := tmJLInp h vs σN q with hinp
  set Y := inp.wt + 1 with hY
  set M := tmJLMat N h A with hM
  set ilist := [encPerm h, .list vs, .list (σN.map encPerm), .nat q, .nat m] with hil
  have wil : (Val.list ilist).wt = inp.wt := rfl
  obtain ⟨σ, hσ⟩ := tmJL_match h hAdef hmatch
  have hqY : q + 1 ≤ Y := by omega
  have hmY : m + 1 ≤ Y := by omega
  have hY1 : 1 ≤ Y := by omega
  have hY2 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY34 : Y ^ 3 ≤ Y ^ 4 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY412 : Y ^ 4 ≤ Y ^ 12 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hq2 : (q + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hqY 2
  have hq3 : (q + 1) ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left hqY 3
  have hm2 : (m + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hmY 2
  have hm3 : (m + 1) ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left hmY 3
  have wids : (tmJLIds q).wt ≤ 4 * (q + 1) ^ 2 := wt_ids_le q
  have wpi := wt_encPerm_le σ
  have wrows := tmJL_wt_rows M
  have wσG := tmJL_wt_σG wm wσ
  rw [← hY] at wσG
  -- step 1: the points
  have r3 : Det P [inp] (arg 3) (.nat q) (2 * inp.wt + 3 + 5) :=
    Det.arg' (P := P) (vs := ilist) (rest := []) (j := 3) (v := .nat q) rfl
  have s1 := (Det.call r3 (tmJL_range hA.hrg q)).mono (c' := 10 ^ 5 * Y ^ 3) (by
    have := tmJL_range_le q
    have := wt_nat_le q
    omega)
  refine FunAll.intro hA.hmain (EvalAll.letE s1 fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- step 2: the rows
  have hT2 := tabulate_spec hA.hmR (c := inp) (F := tmJLRowV M)
    (fun a => tmJL_row_spec hm hA.hrow hA.hrg hA.hmB hA.hbit hjm hA.hap hA.hcp hA.hiv hn hσN
      hAdef hvs h a)
  have t1 := Det.var' (P := P) (env := [inp, tmJLIds q]) (i := 1) (v := tmJLIds q) rfl
  have t0' := Det.var' (P := P) (env := [inp, tmJLIds q]) (i := 0) (v := inp) rfl
  have s2 := (Det.call (Det.mk2 t0' t1) hT2).mono
      (c' := Y * tmJLRowC (membershipPrim hm) Y + 10 ^ 6 * Y ^ 3) (by
    have l1 : q * tmJLRowC (membershipPrim hm) ((tmJLInp h vs σN q).wt + 1) ≤
        Y * tmJLRowC (membershipPrim hm) Y := Nat.mul_le_mul_right _ (by omega)
    have wl : (Val.list [inp, encFun fun i : Fin q => (i : ℕ)]).wt ≤
        2 * (inp.wt + (tmJLIds q).wt) + 6 := wt_list2_le _ _
    have wr : (Val.list ((List.finRange q).map (tmJLRowV M))).wt ≤ 20 * (q + 1) ^ 2 := wrows
    have l2 : mapK * (q + 1) * ((Val.list [inp, encFun fun i : Fin q => (i : ℕ)]).wt +
        (Val.list ((List.finRange q).map (tmJLRowV M))).wt + 1) ≤ 1000 * Y * (100 * Y ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hqY) (by omega)
    have l3 : 1000 * Y * (100 * Y ^ 2) = 10 ^ 5 * Y ^ 3 := by ring
    have eI : (Val.list [inp, tmJLIds q]).wt =
        (Val.list [inp, encFun fun i : Fin q => (i : ℕ)]).wt := rfl
    omega)
  refine EvalAll.letE s2 fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  -- step 3: the matching
  have hT3 := tabulate_spec hA.hmP (c := .list [tmJLRowsV M, tmJLIds q])
    (F := fun a => .nat (σ a))
    (fun a => tmJL_pi_spec hA.hpi hA.hfR hA.hfC hA.hrk hA.hcol hA.hen M a (σ a) (hσ a).1)
  have u1 := Det.var' (P := P) (env := [inp, tmJLIds q, tmJLRowsV M]) (i := 1) (v := tmJLIds q) rfl
  have u2 := Det.var' (P := P) (env := [inp, tmJLIds q, tmJLRowsV M]) (i := 2)
    (v := tmJLRowsV M) rfl
  have s3' := Det.call (Det.mk2 (Det.mk2 u2 u1) u1) hT3
  have e3 : Val.list ((List.finRange q).map fun a => Val.nat (σ a)) = encPerm σ := rfl
  rw [e3] at s3'
  have s3 := s3'.mono (c' := Y * tmJLPiC Y + 10 ^ 6 * Y ^ 3) (by
    have l1 : q * tmJLPiC (q + 1) ≤ Y * tmJLPiC Y :=
      Nat.mul_le_mul (by omega) (by unfold tmJLPiC; omega)
    have wl1 : (Val.list [tmJLRowsV M, tmJLIds q]).wt ≤
        2 * ((tmJLRowsV M).wt + (tmJLIds q).wt) + 6 := wt_list2_le _ _
    have wl2 : (Val.list [.list [tmJLRowsV M, tmJLIds q], encFun fun i : Fin q => (i : ℕ)]).wt ≤
        2 * ((Val.list [tmJLRowsV M, tmJLIds q]).wt + (tmJLIds q).wt) + 6 := wt_list2_le _ _
    have l2 : mapK * (q + 1) * ((Val.list [.list [tmJLRowsV M, tmJLIds q],
        encFun fun i : Fin q => (i : ℕ)]).wt + (encPerm σ).wt + 1) ≤ 1000 * Y * (200 * Y ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hqY) (by omega)
    have l3 : 1000 * Y * (200 * Y ^ 2) = 2 * 10 ^ 5 * Y ^ 3 := by ring
    have eI : (Val.list [.list [tmJLRowsV M, tmJLIds q], tmJLIds q]).wt =
        (Val.list [.list [tmJLRowsV M, tmJLIds q], encFun fun i : Fin q => (i : ℕ)]).wt := rfl
    omega)
  refine EvalAll.letE s3 fun v3 c3 h3 => ?_
  obtain ⟨rfl, hc3⟩ := h3
  -- step 4: the group `⟨σN⟩`
  have a4 : Det P [inp, tmJLIds q, tmJLRowsV M, encPerm σ] (arg 4) (.nat m) (2 * inp.wt + 4 + 5) :=
    Det.arg' (P := P) (vs := ilist) (rest := [tmJLIds q, tmJLRowsV M, encPerm σ]) (j := 4)
      (v := .nat m) rfl
  have a2 : Det P [inp, tmJLIds q, tmJLRowsV M, encPerm σ] (arg 2) (.list (σN.map encPerm))
      (2 * inp.wt + 2 + 5) :=
    Det.arg' (P := P) (vs := ilist) (rest := [tmJLIds q, tmJLRowsV M, encPerm σ]) (j := 2)
      (v := .list (σN.map encPerm)) rfl
  have crm := Det.call a4 (tmJL_range hA.hrg m)
  have e1m : tmJLIds m = encPerm (1 : Perm (Fin m)) := by
    show encFun _ = _
    rw [encFun_id, range_eq_encPerm_one]
  rw [e1m] at crm
  have hAp4 : FunDet P ap (.list [.list [encPerm (1 : Perm (Fin m))], .list (σN.map encPerm)])
      (.list ([encPerm (1 : Perm (Fin m))] ++ σN.map encPerm))
      (loopModK * ((σN.map encPerm).length + 1) *
        ((Val.list [.list [encPerm (1 : Perm (Fin m))], .list (σN.map encPerm)]).wt +
          (σN.map encPerm).length + (Val.list ([encPerm (1 : Perm (Fin m))] ++ σN.map encPerm)).wt +
            1)) :=
    (append_spec hA.hap _ _).mono fun w c hw => by obtain ⟨rfl, h2⟩ := hw; exact ⟨rfl, h2⟩
  have cap := Det.call (Det.mk2 (Det.mk1 crm) a2) hAp4
  have s4' := Det.mk2 a4 cap
  have e4 : Val.list [.nat m, .list ([encPerm (1 : Perm (Fin m))] ++ σN.map encPerm)] =
      encGroup σN := rfl
  rw [e4] at s4'
  have s4 := s4'.mono (c' := 10 ^ 6 * Y ^ 3) (by
    have l0 := tmJL_range_le m
    have w1 := wt_encPerm_le (1 : Perm (Fin m))
    have w2 := wt_list1_le (encPerm (1 : Perm (Fin m)))
    have w3 := tmJL_wt_append_le [encPerm (1 : Perm (Fin m))] (σN.map encPerm)
    have w4 := wt_list2_le (Val.list [encPerm (1 : Perm (Fin m))]) (.list (σN.map encPerm))
    have w5 := length_lt_wt_list (σN.map encPerm)
    have w6 := wt_nat_le m
    have l1 : loopModK * ((σN.map encPerm).length + 1) *
        ((Val.list [.list [encPerm (1 : Perm (Fin m))], .list (σN.map encPerm)]).wt +
          (σN.map encPerm).length + (Val.list ([encPerm (1 : Perm (Fin m))] ++ σN.map encPerm)).wt +
            1) ≤ 1000 * Y * (200 * Y ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have l3 : 1000 * Y * (200 * Y ^ 2) = 2 * 10 ^ 5 * Y ^ 3 := by ring
    have wG := wt_list2_le (Val.nat m) (.list ([encPerm (1 : Perm (Fin m))] ++ σN.map encPerm))
    rw [e4] at wG
    omega)
  refine EvalAll.letE s4 fun v4 c4 h4 => ?_
  obtain ⟨rfl, hc4⟩ := h4
  -- step 5: the local elements
  set env4 := [inp, tmJLIds q, tmJLRowsV M, encPerm σ, encGroup σN] with henv4
  set xs := (List.finRange q).map fun a : Fin q => Val.nat (a : ℕ) with hxs
  set cD := Val.list [inp, encPerm σ, encGroup σN] with hcD
  have g0 := Det.var' (P := P) (env := env4) (i := 0) (v := inp) rfl
  have g1 := Det.var' (P := P) (env := env4) (i := 1) (v := .list xs) rfl
  have g3 := Det.var' (P := P) (env := env4) (i := 3) (v := encPerm σ) rfl
  have g4 := Det.var' (P := P) (env := env4) (i := 4) (v := encGroup σN) rfl
  have harg := Det.mk2 (Det.mk3 g0 g3 g4) g1
  have hMap := map_spec hA.hmD (c := cD) (xs := xs)
    (R := fun x w => ∀ a : Fin q, x = .nat a →
      ∃ d, (d ∈ A (a, σ a) ∧ h⁻¹ * d ∈ N) ∧ w = encPerm d⁻¹)
    (B := fun _ => tmJLDC (normalizedFactorPrim hfac) Y) (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      refine (tmJL_d_spec hfac hA.hd hjf hA.hcp hA.hiv hn hσN hAdef hvs h σ a (hσ a).2).mono
        fun w c hw => ⟨fun a' ha' => ?_, hw.2⟩
      have : a' = a := Fin.ext (by simpa using ha'.symm)
      subst this
      exact hw.1)
  have hxl : xs.length = q := by simp [hxs]
  have wcD : cD.wt ≤ 2 * (inp.wt + (encPerm σ).wt + (encGroup σN).wt) + 7 := wt_list3_le _ _ _
  have s5 : EvalAll P env4 (.call mD (mk2 (mk3 (.var 0) (.var 3) (.var 4)) (.var 1)))
      (fun w c => ∃ d : Fin q → Perm (Fin m), (∀ a, d a ∈ A (a, σ a) ∧ h⁻¹ * d a ∈ N) ∧
        w = tmJDsVal d ∧ c ≤ Y * tmJLDC (normalizedFactorPrim hfac) Y + 10 ^ 6 * Y ^ 4) := by
    refine EvalAll.call_funAll harg fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine hMap.mono fun w cb hw => ?_
    obtain ⟨ws, rfl, h2, hcb⟩ := hw
    obtain ⟨d, hd, rfl⟩ := tmJL_choose
      (Pr := fun a d => d ∈ A (a, σ a) ∧ h⁻¹ * d ∈ N) (enc := fun d => encPerm d⁻¹) h2
    refine ⟨d, hd, rfl, ?_⟩
    have hs : (xs.map fun _ => tmJLDC (normalizedFactorPrim hfac) Y).sum =
        q * tmJLDC (normalizedFactorPrim hfac) Y := by
      simp [List.map_const', hxl]
    rw [hs, hxl] at hcb
    have wd : (Val.list ((List.finRange q).map fun a => encPerm (d a)⁻¹)).wt ≤ 9 * Y ^ 3 + 4 := by
      have := tmJL_wt_list_le (l := (List.finRange q).map fun a => encPerm (d a)⁻¹)
        (B := 4 * Y ^ 2) (by
          intro v hv
          obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv
          have := wt_encPerm_le (d a)⁻¹; omega)
      simp only [List.length_map, List.length_finRange] at this
      have h1 : q * (2 * (4 * Y ^ 2) + 1) ≤ Y * (2 * (4 * Y ^ 2) + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : Y * (2 * (4 * Y ^ 2) + 1) = 8 * Y ^ 3 + Y := by ring
      omega
    have wI : (Val.list xs).wt ≤ 4 * (q + 1) ^ 2 := wids
    have wa := wt_list2_le cD (.list xs)
    have l1 : q * tmJLDC (normalizedFactorPrim hfac) Y ≤ Y * tmJLDC (normalizedFactorPrim hfac) Y :=
      Nat.mul_le_mul_right _ (by omega)
    have l2 : mapK * (q + 1) * ((Val.list [cD, .list xs]).wt +
        (Val.list ((List.finRange q).map fun a => encPerm (d a)⁻¹)).wt + 1) ≤
        1000 * Y * (300 * Y ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hqY) (by omega)
    have l3 : 1000 * Y * (300 * Y ^ 3) = 3 * 10 ^ 5 * Y ^ 4 := by ring
    have wm3 := wt_list3_le inp (encPerm σ) (encGroup σN)
    have e5 : (tmJDsVal d).wt = (Val.list ((List.finRange q).map fun a => encPerm (d a)⁻¹)).wt := rfl
    have ecd : (Val.list [Val.list [inp, encPerm σ, encGroup σN], .list xs]).wt =
        (Val.list [cD, .list xs]).wt := rfl
    omega
  refine EvalAll.letE s5 fun v5 c5 h5 => ?_
  obtain ⟨d, hd, rfl, hc5⟩ := h5
  -- step 6: the pair
  set env5 := env4 ++ [tmJDsVal d] with henv5
  have k5 := Det.var' (P := P) (env := env5) (i := 5) (v := tmJDsVal d) rfl
  have k3 := Det.var' (P := P) (env := env5) (i := 3) (v := encPerm σ) rfl
  have kq : Det P env5 (arg 3) (.nat q) (2 * inp.wt + 3 + 5) :=
    Det.arg' (P := P) (vs := ilist) (rest := [tmJLIds q, tmJLRowsV M, encPerm σ, encGroup σN,
      tmJDsVal d]) (j := 3) (v := .nat q) rfl
  have km : Det P env5 (arg 4) (.nat m) (2 * inp.wt + 4 + 5) :=
    Det.arg' (P := P) (vs := ilist) (rest := [tmJLIds q, tmJLRowsV M, encPerm σ, encGroup σN,
      tmJDsVal d]) (j := 4) (v := .nat m) rfl
  have s6 := Det.call (Det.mk4 k5 k3 kq km) (tmJ_pair_spec hA.hpair d σ)
  refine s6.post fun c6 hc6 => ⟨⟨d, σ, hd, rfl⟩, ?_⟩
  -- the cost
  set z := toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, σ)) with hz
  have hmq : m * q + 1 ≤ Y ^ 2 := by
    have : m * q ≤ inp.wt * inp.wt := Nat.mul_le_mul wm.le wq.le
    have : Y ^ 2 = inp.wt * inp.wt + 2 * inp.wt + 1 := by rw [hY]; ring
    omega
  have wz : (encPerm z).wt ≤ 4 * Y ^ 4 := by
    have := wt_encPerm_le z
    have : (m * q + 1) ^ 2 ≤ (Y ^ 2) ^ 2 := Nat.pow_le_pow_left hmq 2
    have : (Y ^ 2) ^ 2 = Y ^ 4 := by ring
    omega
  have wd : (tmJDsVal d).wt ≤ 9 * Y ^ 3 + 4 := by
    have := tmJL_wt_list_le (l := (List.finRange q).map fun a => encPerm (d a)⁻¹)
      (B := 4 * Y ^ 2) (by
        intro v hv
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv
        have := wt_encPerm_le (d a)⁻¹; omega)
    simp only [List.length_map, List.length_finRange] at this
    have h1 : q * (2 * (4 * Y ^ 2) + 1) ≤ Y * (2 * (4 * Y ^ 2) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : Y * (2 * (4 * Y ^ 2) + 1) = 8 * Y ^ 3 + Y := by ring
    have e : (tmJDsVal d).wt = (Val.list ((List.finRange q).map fun a => encPerm (d a)⁻¹)).wt :=
      rfl
    omega
  have w4 := wt_list4_le (tmJDsVal d) (encPerm σ) (.nat q) (.nat m)
  have hpair : tmJPairK ((Val.list [tmJDsVal d, encPerm σ, .nat q, .nat m]).wt + m * q) ≤
      10 ^ 13 * Y ^ 12 := by
    unfold tmJPairK
    have h1 : (Val.list [tmJDsVal d, encPerm σ, .nat q, .nat m]).wt + m * q + 1 ≤ 50 * Y ^ 3 := by
      omega
    calc 10 ^ 6 * ((Val.list [tmJDsVal d, encPerm σ, .nat q, .nat m]).wt + m * q + 1) ^ 4
        ≤ 10 ^ 6 * (50 * Y ^ 3) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 4)
      _ ≤ 10 ^ 13 * Y ^ 12 := by ring_nf; omega
  have hK := tmJL_mainC_le (membershipPrim hm) (normalizedFactorPrim hfac) hY1
  unfold tmJLMainC at hK
  omega

end Setting

end GI.Impl
