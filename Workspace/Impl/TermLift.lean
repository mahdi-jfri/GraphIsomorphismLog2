module

public import Workspace.Impl.TermLiftMath
public import Workspace.Impl.Fresh
public import Workspace.Impl.TermMain

@[expose] public section

/-!
# T7: the lift of the table transport to `Ω` and the cut to `G`

Theorem A.23 ends with "the `J`-elements above each residual element, lifted to `Ω`". This file
reduces `Iface.TermAsmSpec` (the assembly of the row terminal) to a smaller hypothesis,
`Iface.TermDomSpec`: a program that returns a canonical coset description of the table
transport of the exact tables, written as permutations of the domain positions
(`tmDomSet E T`: the permutation `e(c, i) ↦ e(d_i⁻¹ c, π i)` for each pair `(d, π)` of `T`).

The function `tmLiftBody pre g lift` on the input of `TermAsmSpec`:

1. `prepF` on the state value (`prep_spec`): at most `k²` generators `gs₀` of `G`, the domain
   positions and their number `s`.
2. The function `g` of `TermDomSpec` on the whole input: a canonical answer `u'` of
   `tmDomSet E T` on the domain positions.
3. The lift (`lift_spec`) on `[[k, s, domCtx, gs₀], u']`: a canonical answer of
   `S.liftAnswer (tmDomSet E T)`, which is `S.answer` (`tm_liftAnswer_eq`). Its precondition,
   that `tmDomSet E T` lies in `G|_dom`, is `tm_domSet_le` (`K R₀ ≤ G`, Theorems A.17, A.18).

Cited tasks: **PointwiseStab** (in `prepF`), **Preimage** and **NormalizedFactor** (in the lift),
as in a fresh phase. The cost is the cost of `g` plus a polynomial in `N` (`tmLiftPoly`), so it is
at most `expLogSq (tmLiftA A) N` (`tm_termAsmSpec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens PointwiseStab Preimage NormalizedFactor)

namespace Iface

variable (Pg : Program)

/-- **The table transport on the domain positions** (T2–T6, the hypothesis left by T7): on the
input of `TermAsmSpec`, return a canonical answer, on the domain positions, of the lift
`tmDomSet E T` of the table transport `T` of the exact tables (Theorem A.23: the residual
transporter of A.22 and, above each residual element, the `J`-elements that pass the label and
parity tests), at a cost of at most `expLogSq A N`. The terminal data are those of
`RowForm.rowTerminal` (`A = N/N*`) for the row form from pure coordinates. -/
def TermDomSpec (A : ℝ) (g : ℕ) : Prop :=
  ∀ {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
    Function.Injective c →
    ∀ (sv lv : Val) (L : SuppliedLabels S), Canon e c sv S → LabValStd e S lv L →
    P₀.q₀ < L.q → Good P₀ .giant S → RowCase P₀.α S L.toGiantLabels →
    ∀ (label : Ω → Fin L.q) (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q)
      {m : ℕ} (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom)
      (hP : PureCoords S L.toGiantLabels label E)
      (σH σN σS : List (Perm (Fin m))),
      gens σH = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb →
      gens σN = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb →
      gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype →
      ∀ (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B),
      σH.length ≤ (k + L.q) ^ 2 → σN.length ≤ (k + L.q) ^ 2 → σS.length ≤ (k + L.q) ^ 2 →
      ∀ (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
        (hqα : (S.N : ℝ) ^ P₀.α < L.q),
      ∀ us vs : List Val,
      List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
        us (tmTests L.q) →
      List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (tmCosetState S E σH ij).answer)
        vs (tmCosets L.q) →
      FunAll Pg g (.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
          encFun (rowLab e L.con.blocks)], .list us, .list vs])
        (fun u cost => AnsC (domEquiv e S.dom) u
          (tmDomSet (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).e
            (tmExactT ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN
              hqα))) ∧
          (cost : ℝ) ≤ expLogSq A S.N)

end Iface

/-- **The body of T7**: `prepF` at `pre` on the state value, the function `g` of `TermDomSpec`
on the whole input, and the lift at `lift`. -/
def tmLiftBody (pre g lift : ℕ) : Expr :=
  .letE (.call pre (.get (arg 0) (.nat 0)))
  (.letE (.call g (.var 0))
  (.call lift (mk2 (mk4 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (.var 1) (.nat 2))
    (.get (.var 1) (.nat 1)) (.get (.var 1) (.nat 0))) (.var 2))))

/-- Where the modules of T7 sit in the program. -/
structure TmLiftAt (P : Program) (f pre red dom col hier ap rep lo cnt ob jst g lift jpre jfac : ℕ) :
    Prop where
  entry : P.funs[f]? = some (tmLiftBody pre g lift)
  prepAt : PrepAt P pre red dom col hier ap rep lo cnt ob jst
  liftAt : LiftAt P lift dom jpre jfac

/-- The polynomial part of the cost of T7, in `X = (weight of the input) + 1`. -/
def tmLiftPoly (pst pp pf : Prim) (X : ℕ) : ℕ :=
  prepCost pst X + liftCost pp pf X + 10 ^ 8 * X ^ 6

theorem tm_prepCost_mono (pst : Prim) {a b : ℕ} (h : a ≤ b) : prepCost pst a ≤ prepCost pst b := by
  unfold prepCost
  have h1 : a ^ 21 ≤ b ^ 21 := Nat.pow_le_pow_left h _
  have h2 : a ^ 6 ≤ b ^ 6 := Nat.pow_le_pow_left h _
  have h3 : (10 ^ 6 * a ^ 6 + 2) ^ pst.k ≤ (10 ^ 6 * b ^ 6 + 2) ^ pst.k :=
    Nat.pow_le_pow_left (by omega) _
  have := Nat.mul_le_mul_left pst.c h3
  omega

namespace Iface

variable (Pg : Program)

/-- **T7 on one input**: the cost is that of `g` plus `tmLiftPoly` of the input weight. -/
theorem tm_lift_main (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    {f pre red dom col hier ap rep lo cnt ob jst g lift jpre jfac : ℕ}
    (h : TmLiftAt Pg f pre red dom col hier ap rep lo cnt ob jst g lift jpre jfac)
    (hjs : Pg.prims[jst]? = some (pointwiseStabPrim hst))
    (hjp : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hjf : Pg.prims[jfac]? = some (normalizedFactorPrim hfac)) {A : ℝ}
    (hdom : TermDomSpec Pg A g)
    {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ)
    (hc : Function.Injective c)
    (sv lv : Val) (L : SuppliedLabels S) (hsv : Canon e c sv S) (hlv : LabValStd e S lv L)
    (hq0 : P₀.q₀ < L.q) (hgood : Good P₀ .giant S) (hrow : RowCase P₀.α S L.toGiantLabels)
    (label : Ω → Fin L.q) (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q)
    {m : ℕ} (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom)
    (hP : PureCoords S L.toGiantLabels label E)
    (σH σN σS : List (Perm (Fin m)))
    (hH : gens σH = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb)
    (hN : gens σN = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb)
    (hS : gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hlH : σH.length ≤ (k + L.q) ^ 2) (hlN : σN.length ≤ (k + L.q) ^ 2)
    (hlS : σS.length ≤ (k + L.q) ^ 2) (us vs : List Val)
    (hus : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
        us (tmTests L.q))
    (hvs : List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (tmCosetState S E σH ij).answer)
        vs (tmCosets L.q)) :
    FunAll Pg f (.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
          encFun (rowLab e L.con.blocks)], .list us, .list vs])
        (fun u cost => AnsC e u S.answer ∧ (cost : ℝ) ≤ expLogSq A S.N +
          (tmLiftPoly (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac)
            ((Val.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
              encFun (rowLab e L.con.blocks)], .list us, .list vs]).wt + 1) : ℕ)) := by
  have hgood' : Good P₀ .giant S := hgood
  obtain ⟨-, hsize, -, -, -, -⟩ := hgood
  have hcard : Fintype.card (Fin m) * L.q = S.size := by
    unfold State.size
    rw [← Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  have hsz : 0 < S.size := by
    rw [← hcard, Fintype.card_fin]; exact Nat.mul_pos h0 (by omega)
  have hNpos : 0 < S.N := by omega
  set T0 := (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsize hNpos hrow.1
    with hT0
  set tin := Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
    encFun (rowLab e L.con.blocks)] with htin
  set V := Val.list [tin, .list us, .list vs] with hV
  have hsvV := hsv.stateVal
  have hkv := StateVal.k_le_wt hsvV
  obtain ⟨gv, dv, xv, yv, hv0, rv, -, -, -, -, -, -, hsveq⟩ := hsv.val
  refine FunAll.intro h.entry ?_
  unfold tmLiftBody
  -- 1. the generators of `G` and the domain positions
  have dtin := Det.arg' (P := Pg) (vs := [tin, .list us, .list vs]) (rest := []) (j := 0)
    (v := tin) rfl
  have dsv := Det.get' dtin (Det.nat 0) (vs := [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
    encFun (rowLab e L.con.blocks)]) (v := sv) rfl
  refine EvalAll.letE (EvalAll.call_spec dsv (prep_spec hst h.prepAt hjs e c S hsz hsvV)) ?_
  rintro w1 c1 ⟨cb1, ⟨⟨gs₀, hsF, labF, a, hgs₀, hl₀, -, -, rfl, hw1⟩, hcb1⟩, hc1⟩
  -- 2. the table transport on the domain positions
  have hdcall := hdom S k e c hc sv lv L hsv hlv hq0 hgood' hrow label hnat hq h0 E hP σH σN σS
    hH hN hS htr hlH hlN hlS hcard hsize hNpos hrow.1 us vs hus hvs
  refine EvalAll.letE (EvalAll.call_spec (Det.var' (P := Pg) (env := [V, _]) (i := 0) (v := V) rfl)
    hdcall) ?_
  rintro u' c2 ⟨cb2, ⟨hu', hcb2⟩, hc2⟩
  -- 3. the lift
  have hsub := tm_domSet_le T0
  have hlift := lift_spec hpre hfac h.liftAt h.prepAt.domAt hjp hjf e S hgs₀ hl₀ hu' hsub
  set W1 := Val.list [encGroup gs₀, domCtx e S.dom, .nat (domFin e S.dom).length,
      freshVal (domFin e S.dom).length (encGroup hsF) (natList (cmpCodes e c S S.x))
        (natList (cmpCodes e c S S.y)) (fhierVal (encFun labF) (Nat.card (orb S.domGroup a)))]
    with hW1
  have dtin3 := Det.arg' (P := Pg) (vs := [tin, .list us, .list vs]) (rest := [W1, u']) (j := 0)
    (v := tin) rfl
  have dsv3 := Det.get' dtin3 (Det.nat 0) (vs := [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
    encFun (rowLab e L.con.blocks)]) (v := sv) rfl
  rw [hsveq] at dsv3
  have dk := Det.get' dsv3 (Det.nat 0) (v := .nat k) rfl
  have dW := Det.var' (P := Pg) (env := [V, W1, u']) (i := 1) (v := W1) rfl
  have d2 := Det.get' dW (Det.nat 2) (vs := [encGroup gs₀, domCtx e S.dom,
    .nat (domFin e S.dom).length, _]) rfl
  have d1 := Det.get' dW (Det.nat 1) (vs := [encGroup gs₀, domCtx e S.dom,
    .nat (domFin e S.dom).length, _]) rfl
  have d0 := Det.get' dW (Det.nat 0) (vs := [encGroup gs₀, domCtx e S.dom,
    .nat (domFin e S.dom).length, _]) rfl
  have du := Det.var' (P := Pg) (env := [V, W1, u']) (i := 2) (v := u') rfl
  refine (EvalAll.call_spec (Det.mk2 (Det.mk4 dk d2 d1 d0) du) hlift).mono ?_
  rintro w c3 ⟨cb3, ⟨hAns, hcb3⟩, hc3⟩
  refine ⟨by convert hAns using 1; exact (tm_liftAnswer_eq T0).symm, ?_⟩
  -- the cost
  have hsvw : (Val.list [Val.nat k, gv, dv, xv, yv, hv0, rv, boolVal S.floor, Val.nat S.h,
      Val.nat S.N]).wt = sv.wt := by rw [hsveq]
  have wsv : sv.wt < tin.wt := wt_le_wt_list (by simp)
  have wtin : tin.wt < V.wt := wt_le_wt_list (by simp)
  set X := V.wt + 1 with hX
  have hkX : k + 1 ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  have k6 : (k + 1) ^ 6 ≤ X ^ 6 := Nat.pow_le_pow_left hkX 6
  have p16 : X ≤ X ^ 6 := Nat.le_self_pow (by norm_num) _
  have ww := hAns.wt_le
  have ww' := ansW_le_pow k
  have wu := hu'.wt_le
  have wu' : ansW (domFin e S.dom).length ≤ 400 * (k + 1) ^ 6 :=
    (ansW_le_pow _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (by have : (domFin e S.dom).length ≤ k := length_domFin_le; omega) 6))
  have wctx := wt_liftCtx_le e S.dom hl₀
  have eL : (Val.list [Val.nat k, Val.nat (domFin e S.dom).length, domCtx e S.dom,
    encGroup gs₀]).wt = (liftCtx e S.dom gs₀).wt := rfl
  have wl2 := wt_list2_le (liftCtx e S.dom gs₀) u'
  have eL2 : (Val.list [Val.list [Val.nat k, Val.nat (domFin e S.dom).length, domCtx e S.dom,
    encGroup gs₀], u']).wt = (Val.list [liftCtx e S.dom gs₀, u']).wt := rfl
  have m1 : (encGroup gs₀).wt < W1.wt := wt_le_wt_list (by simp)
  have m2 : (domCtx e S.dom).wt < W1.wt := wt_le_wt_list (by simp)
  have m3 : (Val.nat (domFin e S.dom).length).wt < W1.wt := wt_le_wt_list (by simp)
  have wk := wt_nat_le k
  have hp1 := tm_prepCost_mono (pointwiseStabPrim hst) (show sv.wt + 1 ≤ X by omega)
  have hl1 := liftCost_mono (preimagePrim hpre) (normalizedFactorPrim hfac) (show k ≤ X by omega)
  have hnat : c1 + (c2 + c3 + w.wt + 1) + w.wt + 1 ≤ cb2 +
      tmLiftPoly (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac) X := by
    unfold tmLiftPoly
    have eV : (Val.list [tin, Val.list us, Val.list vs]).wt = V.wt := rfl
    rw [hsvw] at hc3
    omega
  have hnat' := (Nat.cast_le (α := ℝ)).2 hnat
  push_cast at hnat' ⊢
  linarith

end Iface

/-! ### The cost fits in `expLogSq` -/

/-- A list of values related to a list `l`, each of weight at most `W`. -/
theorem tm_wt_forall₂ {α : Type*} {R : Val → α → Prop} {W : ℕ} (hR : ∀ u a, R u a → u.wt ≤ W)
    {us : List Val} {l : List α} (h : List.Forall₂ R us l) :
    (Val.list us).wt ≤ l.length * (2 * W + 1) + 4 := by
  have h1 := wt_list_le us
  have hs : (us.map Val.wt).sum ≤ us.length * W := by
    clear h1
    induction h with
    | nil => simp
    | cons hab _ ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := hR _ _ hab
      nlinarith
  have hl : us.length = l.length := h.length_eq
  rw [hl] at hs
  have : l.length * (2 * W + 1) = 2 * (l.length * W) + l.length := by ring
  omega

/-- The bound of the input weight plus one, in `N`. -/
def tmVB (N : ℕ) : ℕ := 4 * 10 ^ 6 * (N + 2) ^ 8

/-- **The weight of the input of T7** is polynomial in `N`. -/
theorem tm_wtV_le {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
    {sv lv : Val} {L : SuppliedLabels S} (hsv : Canon e c sv S) (hlv : LabValStd e S lv L)
    {m : ℕ} (E : Fin m × Fin L.q ≃ S.dom) (hq : 0 < L.q)
    {σH σN σS : List (Perm (Fin m))}
    (hlH : σH.length ≤ (k + L.q) ^ 2) (hlN : σN.length ≤ (k + L.q) ^ 2)
    (hlS : σS.length ≤ (k + L.q) ^ 2) {us vs : List Val}
    (hus : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
        us (tmTests L.q))
    (hvs : List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (tmCosetState S E σH ij).answer)
        vs (tmCosets L.q)) :
    (Val.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
      encFun (rowLab e L.con.blocks)], .list us, .list vs]).wt + 1 ≤ tmVB S.N := by
  have hk : k ≤ S.N := hsv.fits
  have hqk : L.q ≤ k + 2 := GiantLabels.q_le e L.toGiantLabels
  have hmk : m ≤ k := m_le_n e E ⟨0, hq⟩
  set P := S.N + 2 with hP
  have hP1 : 1 ≤ P := by omega
  have hA : ansW m ≤ 1000 * P ^ 6 :=
    (ansW_le m).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6))
  have h1 := wt_tmIn_le hsv hlv E hq hlH hlN hlS
  have h2 := tm_wt_forall₂ (W := 1000 * P ^ 6) (fun u ac (h : AnsC (Equiv.refl (Fin m)) u
    (tmTestState S E σN ac).answer) => h.wt_le.trans hA) hus
  have h3 := tm_wt_forall₂ (W := 1000 * P ^ 6) (fun u ij (h : AnsC (Equiv.refl (Fin m)) u
    (tmCosetState S E σH ij).answer) => h.wt_le.trans hA) hvs
  have l2 : (tmTests L.q).length ≤ 4 * P ^ 2 := by
    simp only [tmTests, tmRows, List.length_product, List.length_append, List.length_map,
      List.length_finRange]
    have : L.q ≤ P := by omega
    nlinarith
  have l3 : (tmCosets L.q).length ≤ P ^ 2 := by
    simp only [tmCosets, List.length_product, List.length_finRange]
    have : L.q ≤ P := by omega
    nlinarith
  have w3 := wt_list3_le (Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
    encFun (rowLab e L.con.blocks)]) (.list us) (.list vs)
  have hIn : tmInB S.N = 10 ^ 6 * P ^ 6 := rfl
  have p68 : P ^ 6 ≤ P ^ 8 := Nat.pow_le_pow_right hP1 (by omega)
  have p1 : 1 ≤ P ^ 8 := Nat.one_le_pow _ _ hP1
  have e1 : P ^ 2 * (2 * (1000 * P ^ 6) + 1) ≤ 2001 * P ^ 8 := by
    have : P ^ 2 * P ^ 6 = P ^ 8 := by ring
    have : P ^ 2 ≤ P ^ 8 := Nat.pow_le_pow_right hP1 (by omega)
    nlinarith
  have e2 := Nat.mul_le_mul_right (2 * (1000 * P ^ 6) + 1) l2
  have e3 := Nat.mul_le_mul_right (2 * (1000 * P ^ 6) + 1) l3
  have e4 : 4 * P ^ 2 * (2 * (1000 * P ^ 6) + 1) = 4 * (P ^ 2 * (2 * (1000 * P ^ 6) + 1)) := by
    ring
  unfold tmVB
  rw [← hP]
  omega

/-- The constant of the polynomial bound of `tmLiftPoly`. -/
def tmLK (pst pp pf : Prim) : ℕ := freshConst pst pp pf + 10 ^ 8

/-- The degree of the polynomial bound of `tmLiftPoly`. -/
def tmLD (pst pp pf : Prim) : ℕ := 21 + 6 * (pst.k + pp.k + pf.k)

theorem tmLiftPoly_le (pst pp pf : Prim) {X : ℕ} (hX : 1 ≤ X) :
    tmLiftPoly pst pp pf X ≤ tmLK pst pp pf * X ^ tmLD pst pp pf := by
  have h := freshCost_le pst pp pf (d := tmLD pst pp pf) (by unfold tmLD; omega)
    (by unfold tmLD; omega) (by unfold tmLD; omega) (by unfold tmLD; omega) hX
  have h6 : X ^ 6 ≤ X ^ tmLD pst pp pf := Nat.pow_le_pow_right hX (by unfold tmLD; omega)
  unfold tmLiftPoly tmLK
  unfold freshCost at h
  rw [Nat.add_mul]
  omega

/-- The constant of `tmLiftPoly` in `N + 2`. -/
def tmLKN (pst pp pf : Prim) : ℕ := tmLK pst pp pf * (4 * 10 ^ 6) ^ tmLD pst pp pf

/-- **The constant of T7**: `expLogSq A N` for the hypothesis plus the polynomial part. -/
noncomputable def tmLiftA (pst pp pf : Prim) (A : ℝ) : ℝ :=
  A + 3 * (Real.log (tmLKN pst pp pf) + (8 * tmLD pst pp pf : ℕ)) + 3

theorem tmLiftPoly_le_exp (pst pp pf : Prim) {A : ℝ} (hA : 0 ≤ A) {N X : ℕ} (hX1 : 1 ≤ X)
    (hX : X ≤ tmVB N) :
    expLogSq A N + (tmLiftPoly pst pp pf X : ℝ) ≤ expLogSq (tmLiftA pst pp pf A) N := by
  set D := tmLD pst pp pf
  have h1 := tmLiftPoly_le pst pp pf hX1
  have h2 : X ^ D ≤ (4 * 10 ^ 6) ^ D * (N + 2) ^ (8 * D) := by
    have := Nat.pow_le_pow_left hX D
    unfold tmVB at this
    rwa [mul_pow, ← pow_mul] at this
  have h3 : tmLiftPoly pst pp pf X ≤ tmLKN pst pp pf * (N + 2) ^ (8 * D) := by
    unfold tmLKN
    calc tmLiftPoly pst pp pf X ≤ tmLK pst pp pf * X ^ D := h1
      _ ≤ tmLK pst pp pf * ((4 * 10 ^ 6) ^ D * (N + 2) ^ (8 * D)) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  have hK : (1 : ℝ) ≤ tmLKN pst pp pf := by
    have : 1 ≤ tmLKN pst pp pf := by
      unfold tmLKN tmLK
      exact Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have h4 := pow_le_expLogSq hK (8 * D) N
  have h3' : (tmLiftPoly pst pp pf X : ℝ) ≤ (tmLKN pst pp pf : ℝ) * ((N : ℝ) + 2) ^ (8 * D) := by
    have := (Nat.cast_le (α := ℝ)).2 h3
    push_cast at this ⊢
    linarith
  have h5 := expLogSq_add_le hA (by
    have := Real.log_nonneg hK
    positivity : (0 : ℝ) ≤ 3 * (Real.log (tmLKN pst pp pf) + (8 * D : ℕ))) N
  unfold tmLiftA
  push_cast at h4 h5 ⊢
  linarith

namespace Iface

variable (Pg : Program)

/-- **T7: the assembly of the row terminal from the table transport on the domain positions.**
From `TermDomSpec Pg A g` and the cited **PointwiseStab**, **Preimage** and
**NormalizedFactor**, the function `tmLiftBody` meets `TermAsmSpec` with the constant
`tmLiftA A`. -/
theorem tm_termAsmSpec (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    {f pre red dom col hier ap rep lo cnt ob jst g lift jpre jfac : ℕ}
    (h : TmLiftAt Pg f pre red dom col hier ap rep lo cnt ob jst g lift jpre jfac)
    (hjs : Pg.prims[jst]? = some (pointwiseStabPrim hst))
    (hjp : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hjf : Pg.prims[jfac]? = some (normalizedFactorPrim hfac)) {A : ℝ} (hA : 0 ≤ A)
    (hdom : TermDomSpec Pg A g) :
    TermAsmSpec Pg (tmLiftA (pointwiseStabPrim hst) (preimagePrim hpre)
      (normalizedFactorPrim hfac) A) f := by
  intro Ω C _ S k e c hc sv lv L hsv hlv hq0 hgood hrow label hnat hq m h0 E hP σH σN σS hH hN
    hS htr hlH hlN hlS us vs hus hvs
  refine (tm_lift_main Pg hst hpre hfac h hjs hjp hjf hdom S k e c hc sv lv L hsv hlv hq0 hgood
    hrow label hnat hq h0 E hP σH σN σS hH hN hS htr hlH hlN hlS us vs hus hvs).mono ?_
  rintro u cost ⟨hu, hcost⟩
  refine ⟨hu, hcost.trans ?_⟩
  exact tmLiftPoly_le_exp _ _ _ hA (by omega)
    (tm_wtV_le hsv hlv E (by omega) hlH hlN hlS hus hvs)

end Iface

end GI.Impl
