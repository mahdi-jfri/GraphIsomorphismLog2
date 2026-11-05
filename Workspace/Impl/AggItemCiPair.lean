module

public import Workspace.Impl.AggItemCiCfgD
public import Workspace.Impl.AggItemCiSojSpec
public import Workspace.Impl.AggItemStepWt
public import Workspace.Impl.AggItemSrcP
public import Workspace.Impl.GenNormPoly
public import Workspace.Impl.AggItemCfObW

@[expose] public section

/-!
# The pair part from its two branches

`cfgOutItem` on two pair configurations is `cfgItem X Y` when `q ≤ N^α` and
`sojItem … X Y x₀ y₀` otherwise. The pair part follows this split.
* The start program `itciPS` runs the exact test `itciTestE` (`N² < q⁵`, `itci_test_spec`,
  `itci_rpow_iff`) and calls the start of the matching branch.
* An item state of the pair part is `[[tag, kst], u]`: tag `0` for the configuration branch and
  tag `1` for the branch `sojItem`, with `[kst, u]` an item state of that branch. The step
  program `itciPK` reads the tag and calls the step of that branch on `[kst, u]`.
* After each call, `itciWrap t` adds the tag `t` to an ask `[1, code, arg, kst]`, which becomes
  `[1, code, arg, [t, kst]]`. A finished result passes unchanged.

Both branches share the kept relation of the branch `sojItem` (the configuration branch holds
for every kept relation, `ItciCfgSpec`). `itci_post_wrap` moves the post-condition of a branch
to the pair part. The main result is `itci_pairSpec_of`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val)
open GI.Machine (BinOp)

variable {Ω C : Type} {k : ℕ}

/-! ### Adding a tag to an ask -/

/-- Evaluate `r`; if it is an ask `[1, code, arg, kst]`, return `[1, code, arg, [t, kst]]`,
else return it unchanged. The environment has one entry, so the value of `r` is entry `1`. -/
def itciWrap (t : ℕ) (r : Expr) : Expr :=
  .letE r (.ite (.get (.var 1) (.nat 0))
    (mk4 (.nat 1) (.get (.var 1) (.nat 1)) (.get (.var 1) (.nat 2))
      (mk2 (.nat t) (.get (.var 1) (.nat 3))))
    (.var 1))

/-- `w` is a finished result with `Pst w`, or an ask whose tagged form has `Pst`. -/
def itciShape (t : ℕ) (Pst : Val → Prop) (w : Val) : Prop :=
  (∃ rest, w = .list (.nat 0 :: rest) ∧ Pst w) ∨
    ∃ a₁ a₂ a₃, w = .list [.nat 1, a₁, a₂, a₃] ∧ Pst (.list [.nat 1, a₁, a₂, .list [.nat t, a₃]])

/-- The cost bound of `itciWrap` when `r` costs at most `Bd`. -/
def itciWB (Bd : ℕ) : ℕ := Bd + 25 * (4 * Bd + 51)

theorem itci_wb_mono {a b : ℕ} (h : a ≤ b) : itciWB a ≤ itciWB b := by unfold itciWB; omega

theorem itci_wrap_spec {P : Program} {v : Val} {r : Expr} {t Bd : ℕ} {Pst : Val → Prop}
    (h : EvalAll P [v] r (fun w c => c ≤ Bd ∧ itciShape t Pst w)) (ht : t ≤ 1) :
    EvalAll P [v] (itciWrap t r) (fun w c => Pst w ∧ c ≤ itciWB Bd) := by
  refine EvalAll.letE h.wt_lt fun w ca ⟨⟨hca, hsh⟩, hwt⟩ => ?_
  have hW : w.wt ≤ 4 * Bd + 50 := by omega
  have g1 : StDC P ([v] ++ [w]) (.var 1) w 1 0 (4 * Bd + 50) := StDC.var' rfl hW
  have h0w := wt_nat_le 0
  have h1w := wt_nat_le 1
  rcases hsh with ⟨rest, rfl, hp⟩ | ⟨a₁, a₂, a₃, rfl, hp⟩
  · have h0 := StDC.get g1 (StDC.nat 0 (by omega)) (v := .nat 0) rfl (by omega)
    have hi := StDC.ite (nt := 0) (Et := 0) (t := mk4 (.nat 1) (.get (.var 1) (.nat 1))
      (.get (.var 1) (.nat 2)) (mk2 (.nat t) (.get (.var 1) (.nat 3)))) h0
      (fun h => (h rfl).elim) (fun _ => g1) hW
    refine EvalAll.mono hi fun w' cb ⟨hw', hcb⟩ => ?_
    subst hw'
    refine ⟨hp, ?_⟩
    unfold itciWB; omega
  · have hs := sum_wt_lt_wt_list [Val.nat 1, a₁, a₂, a₃]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hs
    have h0 := StDC.get g1 (StDC.nat 0 (by omega)) (v := .nat 1) rfl (by omega)
    have ga₁ := StDC.get g1 (StDC.nat 1 (by omega)) (v := a₁) rfl (by omega)
    have ga₂ := StDC.get g1 (StDC.nat 2 (by omega)) (v := a₂) rfl (by omega)
    have ga₃ := StDC.get g1 (StDC.nat 3 (by omega)) (v := a₃) rfl (by omega)
    have htw := wt_nat_le t
    have hw2 := wt_list2_le (.nat t) a₃
    have hw4 := wt_list4_le (.nat 1) a₁ a₂ (.list [.nat t, a₃])
    have inner := StDC.mk2 (StDC.nat t (by omega)) ga₃ (by omega) (by omega)
    have outer := StDC.mk4 (StDC.nat 1 (by omega)) ga₁ ga₂ inner (by omega) (by omega)
    have hi := StDC.ite (ne := 0) (Ee := 0) (e := .var 1) h0 (fun _ => outer)
      (fun h => (one_ne_zero h).elim)
      (by omega)
    refine EvalAll.mono hi fun w' cb ⟨hw', hcb⟩ => ?_
    subst hw'
    refine ⟨hp, ?_⟩
    unfold itciWB; omega

/-- A call of a function whose results have the shape `itciShape t Pst`, then `itciWrap t`. -/
theorem itci_callwrap {P : Program} {v va : Val} {a : Expr} {f t na Ea W Bs : ℕ}
    {Pst : Val → Prop} (ha : StDC P [v] a va na Ea W)
    (hf : FunAll P f va (fun w c => c ≤ Bs ∧ itciShape t Pst w)) (ht : t ≤ 1) :
    EvalAll P [v] (itciWrap t (.call f a))
      (fun w c => Pst w ∧ c ≤ itciWB (na * (W + 1) + Ea + 2 * Bs + 1)) :=
  itci_wrap_spec (EvalAll.call_funAll ha fun v' ca ⟨hv, hca⟩ => by
    subst hv
    exact hf.wt_lt.mono fun w cb ⟨⟨h1, h2⟩, h3⟩ => ⟨by omega, h2⟩) ht

/-! ### Moving the post-condition of a branch to the pair part -/

/-- **The post-condition through the tag.** If the kept relation of `R` implies that of `R'`,
and `R`-states `[kst, u]` give `R'`-states `[[t, kst], u]` (with more calls allowed), then the
post-condition of `R` gives that of `R'` for the tagged result. -/
theorem itci_post_wrap {R R' : ItCfIRel} (t : ℕ) {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
    {L : SuppliedLabels S} {K : ItSCtx k S L} {b : Fin (P₀.κ + 1) → Fin L.q}
    {oX oY : CfgOut L.q} {E : Set (ItCfCh S L.toGiantLabels)}
    {sb : ItCfCh S L.toGiantLabels → Script (Branches Ω)} {g f Bs B : ℕ} {w : Val}
    (hK : ∀ w E, R.Ki e c S L K w E → R'.Ki e c S L K w E)
    (hR : ∀ kst u E' sb' g' f', g' ≤ f' → R.Ri e c S L K b oX oY (.list [kst, u]) E' sb' g' →
      R'.Ri e c S L K b oX oY (.list [.list [.nat t, kst], u]) E' sb' f')
    (h : ItCfIPost R e c S L K b oX oY E sb g Bs w) (hg : g ≤ f) (hB : Bs ≤ B) :
    itciShape t (ItCfIPost R' e c S L K b oX oY E sb f B) w := by
  rcases h with ⟨r, pcs, os, wI, E', h1, h2, h3, h4, h5, h6⟩ | ⟨hf0, m, Ω', C', T, k', e', c',
    arg, kst, E', kk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · exact Or.inl ⟨_, h1, Or.inl ⟨r, pcs, os, wI, E', h1, h2, h3, hK _ _ h4, h5, h6.trans hB⟩⟩
  · refine Or.inr ⟨_, _, _, h5, Or.inr ⟨by omega, m, Ω', C', T, k', e', c', arg,
      .list [.nat t, kst], E', kk, h1, h2, h3, h4, rfl, h6, h7, h8, h9, fun u hu => ?_⟩⟩
    exact hR _ _ _ _ _ _ (by omega) (h10 u hu)

/-! ### The programs -/

/-- **The start program of the pair part**, with the starts `fsc` (configuration branch) and
`fss` (branch `sojItem`). Entry `0` of the input is `K.v`. -/
def itciPS (fsc fss : ℕ) : Expr :=
  .ite (itciTestE (.get (.var 0) (.nat 0))) (itciWrap 1 (.call fss (.var 0)))
    (itciWrap 0 (.call fsc (.var 0)))

/-- The input `[kst, u]` of the step of a branch, read from `[[t, kst], u]`. -/
def itciPkIn : Expr := mk2 (.get (.get (.var 0) (.nat 0)) (.nat 1)) (.get (.var 0) (.nat 1))

/-- **The step program of the pair part**, with the steps `fkc` and `fks` of the branches. -/
def itciPK (fkc fks : ℕ) : Expr :=
  .ite (.get (.get (.var 0) (.nat 0)) (.nat 0)) (itciWrap 1 (.call fks itciPkIn))
    (itciWrap 0 (.call fkc itciPkIn))

theorem itci_tag_wt {t : ℕ} (ht : t ≤ 1) (kst u : Val) :
    (Val.list [.list [.nat t, kst], u]).wt ≤ 4 * (Val.list [kst, u]).wt + 30 := by
  have hs := sum_wt_lt_wt_list [kst, u]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hs
  have h1 := wt_list2_le (.list [.nat t, kst]) u
  have h2 := wt_list2_le (.nat t) kst
  have := wt_nat_le t
  omega

theorem itci_pk_in {P : Program} {t : ℕ} {kst u : Val} {W : ℕ}
    (hI : (Val.list [.list [.nat t, kst], u]).wt ≤ W) (hs : (Val.list [kst, u]).wt ≤ W) :
    StDC P [.list [.list [.nat t, kst], u]] (.get (.get (.var 0) (.nat 0)) (.nat 0)) (.nat t) 5 0 W ∧
      StDC P [.list [.list [.nat t, kst], u]] itciPkIn (.list [kst, u]) 11 0 W := by
  have hs1 := sum_wt_lt_wt_list [Val.list [.nat t, kst], u]
  have hs2 := sum_wt_lt_wt_list [Val.nat t, kst]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hs1 hs2
  have h4 : 4 ≤ W := by have := wt_list_eq [kst, u]; omega
  have v0 := StDC.var' (P := P) (env := [.list [.list [.nat t, kst], u]]) (i := 0) rfl hI
  have a := StDC.get v0 (StDC.nat 0 (by omega)) (v := .list [.nat t, kst]) rfl (by omega)
  have tg := StDC.get a (StDC.nat 0 (by omega)) (v := .nat t) rfl (by omega)
  have ks := StDC.get a (StDC.nat 1 (by omega)) (v := kst) rfl (by omega)
  have us := StDC.get v0 (StDC.nat 1 (by omega)) (v := u) rfl (by omega)
  exact ⟨tg, StDC.mk2 ks us hs h4⟩

/-! ### The relations and the bound -/

/-- **The relations of the pair part**: the kept relation of the branch `sojItem`; an item
state `[[t, kst], u]` with `[kst, u]` an item state of the configuration branch (`t = 0`) or
of the branch `sojItem` (`t = 1`), with at most `g ≤ f` more calls. -/
def itciPR (Rcf : ItciKiT → ItciRiT) (Rs : ItCfIRel) : ItCfIRel where
  Ki := Rs.Ki
  Ri := fun e c S L K b oX oY ist E sb f => ∃ (t : ℕ) (kst u : Val) (g : ℕ),
    ist = .list [.list [.nat t, kst], u] ∧ g ≤ f ∧
      ((t = 0 ∧ Rcf Rs.Ki e c S L K b oX oY (.list [kst, u]) E sb g) ∨
        (t = 1 ∧ Rs.Ri e c S L K b oX oY (.list [kst, u]) E sb g))

/-- The weight bound inside the pair part, with the branch bound `Bp`. -/
def itciPW (W₀ Bp : ℕ) : ℕ := 10 * itSVB W₀ + 50 * (2 * W₀ + 3 + 1) ^ 2 + 30 * Bp + 100

/-- The weight bound of the objects of a branch (`itCfObjOf_wt` with `q ≤ 2 W₀ + 3`). -/
def itciOW (W₀ : ℕ) : ℕ := itCfObjB (2 * W₀ + 3) (2 * (2 * W₀ + 3) ^ 64)

/-- The kept-value and object bound given to the configuration branch. -/
def itciBk (Xs : ℕ → ℕ) (W₀ : ℕ) : ℕ := Xs W₀ + itciOW W₀

/-- The weight bound with the branch bounds `Xs` and `Xc`. -/
def itciPWX (Xc : ℕ → ℕ → ℕ) (Xs : ℕ → ℕ) (W₀ : ℕ) : ℕ :=
  itciPW W₀ (itciBk Xs W₀ + Xc W₀ (itciBk Xs W₀))

/-- **The bound of the pair part.** -/
def itciXp (Xc : ℕ → ℕ → ℕ) (Xs : ℕ → ℕ) (W₀ : ℕ) : ℕ :=
  200 * (itciPWX Xc Xs W₀ + 1) + 2 * itciWB (13 * (itciPWX Xc Xs W₀ + 1)) + 1

variable (I : Iface) (Pg : Program)

/-- **The objects of a branch weigh at most `itciOW`** (from the color bounds in
`ItCfObjOf`, `itCfObjOf_wt`). -/
theorem itci_objW {F : Funs} {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
    {sv lv : Val} {L : SuppliedLabels S} (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L}
    {b : Fin (P₀.κ + 1) → Fin L.q} {oX oY : CfgOut L.q} (h : ItCfObjOf K b oX oY) :
    (itCfOutV oX).wt ≤ itciOW (I.inW .giant S) ∧ (itCfOutV oY).wt ≤ itciOW (I.inW .giant S) := by
  obtain ⟨hkq, -, hpow, -, -, -⟩ := itS_size I Pg F hc
  have hmono : itCfObjB L.q (2 * L.q ^ P₀.κ) ≤ itciOW (I.inW .giant S) := by
    unfold itciOW itCfObjB
    have h1 : (L.q + 1) ^ 2 ≤ (2 * I.inW .giant S + 3 + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (by omega)
  have := itCfObjOf_wt h
  exact ⟨this.1.trans hmono, this.2.trans hmono⟩

set_option maxHeartbeats 1000000 in
/-- **The pair part from its two branches**: `ItciPairSpec` at the start `fs` and the step
`fk` holding `itciPS fsc fss` and `itciPK fkc fks`, from the configuration branch at
`fsc`, `fkc` and the branch `sojItem` at `fi`, `fss`, `fks`. -/
theorem itci_pairSpec_of {F : Funs} {fi fs fk fsc fkc fss fks : ℕ} {Xc : ℕ → ℕ → ℕ}
    {Xs : ℕ → ℕ} (hC : ItciCfgSpec I Pg F fsc fkc Xc) (hS : ItciSojSpec I Pg F fi fss fks Xs)
    (hfs : Pg.funs[fs]? = some (itciPS fsc fss)) (hfk : Pg.funs[fk]? = some (itciPK fkc fks)) :
    ItciPairSpec I Pg F fi fs fk (itciXp Xc Xs) := by
  classical
  obtain ⟨Rcf, hRc⟩ := hC
  obtain ⟨Rs, hRs⟩ := hS
  refine ⟨itciPR Rcf Rs, fun {Ω C k} e c S sv lv L hc K hK hcase => ?_⟩
  have sa := hRs e c S sv lv L hc K hK hcase
  have ca := hRc Rs.Ki (itciBk Xs (I.inW .giant S)) e c S sv lv L hc K hK hcase sa.ne
    (fun w E h => (sa.wtK w E h).trans (by unfold itciBk; omega))
    (fun b oX oY h => ⟨fun X x₀ _ => (itci_objW I Pg hc h).1.trans (by unfold itciBk; omega),
      fun Y y₀ _ => (itci_objW I Pg hc h).2.trans (by unfold itciBk; omega)⟩)
  have hoW : ∀ b oX oY, ItCfObjOf K b oX oY → (itCfOutV oX).wt ≤ itciOW (I.inW .giant S) ∧
      (itCfOutV oY).wt ≤ itciOW (I.inW .giant S) := fun b oX oY h => itci_objW I Pg hc h
  obtain ⟨hkq, hκ, -, -, -, -⟩ := itS_size I Pg F hc
  have hv := itS_vW I Pg F hc hK
  generalize I.inW .giant S = W₀ at sa ca hkq hκ hv hoW ⊢
  set Ws := itciPWX Xc Xs W₀ with hWs
  have hW1 : 10 * itSVB W₀ + 50 * (2 * W₀ + 3 + 1) ^ 2 +
    30 * (Xs W₀ + itciOW W₀ + Xc W₀ (itciBk Xs W₀)) + 100 = Ws := rfl
  have hXp : itciXp Xc Xs W₀ = 200 * (Ws + 1) + 2 * itciWB (13 * (Ws + 1)) + 1 := rfl
  have hwb := itci_wb_mono (le_refl (13 * (Ws + 1)))
  have hwb0 : 13 * (Ws + 1) ≤ itciWB (13 * (Ws + 1)) := by unfold itciWB; omega
  have hBs : Xs W₀ ≤ itciXp Xc Xs W₀ := by omega
  have hBc : Xc W₀ (itciBk Xs W₀) ≤ itciXp Xc Xs W₀ := by omega
  have hBo : itciOW W₀ ≤ itciXp Xc Xs W₀ := by omega
  refine ⟨sa.init.mono fun w cost ⟨E, h1, h2⟩ => ⟨E, h1, h2.trans hBs⟩, sa.ne,
    fun w E h => (sa.wtK w E h).trans hBs, ?_, ?_, ?_, fun b oX oY h =>
      ⟨fun X x₀ _ => (hoW b oX oY h).1.trans hBo,
        fun Y y₀ _ => (hoW b oX oY h).2.trans hBo⟩⟩
  · -- the start
    intro b X x₀ Y y₀ w E hob hKi
    have hw := sa.wtK w E hKi
    have hX := (hoW b _ _ hob).1
    have hY := (hoW b _ _ hob).2
    have htb : (stTv b).wt ≤ 5 * (2 * W₀ + 3 + 1) ^ 2 := it_wt_src b (by omega) hκ
    have hin : (itciIn K.v (stTv b) (itCfOutV (.pair X x₀)) (itCfOutV (.pair Y y₀)) w).wt ≤
        Ws := by
      have := wt_list_le [K.v, stTv b, itCfOutV (.pair X x₀), itCfOutV (.pair Y y₀), w]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at this
      unfold itciIn; omega
    have hkv := itci_get_in (P := Pg) hin (i := 0) (v := K.v) rfl (by omega)
    have htest := itci_test_spec hK hkv (by omega)
    refine FunAll.intro hfs ((itci_ite (Bd := itciWB (13 * (Ws + 1)))
      (Pst := ItCfIPost (itciPR Rcf Rs) e c S L K b (.pair X x₀) (.pair Y y₀) E
        (itCfSb e (.pair X x₀) (.pair Y y₀)) (itciXp Xc Xs W₀) (itciXp Xc Xs W₀))
      htest ?_).mono fun w' cost ⟨p, hc'⟩ => ⟨by omega, p⟩)
    by_cases hlt : S.N ^ 2 < L.q ^ 5
    · rw [if_pos hlt, if_neg one_ne_zero]
      have hq : ¬ (L.q : ℝ) ≤ (S.N : ℝ) ^ P₀.α := by rw [itci_rpow_iff]; omega
      have hst := sa.start b X x₀ Y y₀ w E hob hq hKi
      rw [← itcs_sb_eq e X Y x₀ y₀ hq] at hst
      refine (itci_callwrap (StDC.var' rfl hin) (hst.mono fun w' c' ⟨h1, h2⟩ =>
        ⟨h1, itci_post_wrap (R := Rs) (R' := itciPR Rcf Rs) 1 (fun _ _ h => h)
          (fun kst u E' sb' g' f' hg h => ⟨1, kst, u, g', rfl, hg, Or.inr ⟨rfl, h⟩⟩)
          h2 hBs hBs⟩) le_rfl).mono fun w' c' ⟨p, hc'⟩ =>
        ⟨p, hc'.trans (itci_wb_mono (by omega))⟩
    · rw [if_neg hlt, if_pos rfl]
      have hst := ca.start b X x₀ Y y₀ w E hob hKi (by omega)
      refine (itci_callwrap (StDC.var' rfl hin) (hst.mono fun w' c' ⟨h1, h2⟩ =>
        ⟨h1, itci_post_wrap (R := ⟨Rs.Ki, Rcf Rs.Ki⟩) (R' := itciPR Rcf Rs) 0 (fun _ _ h => h)
          (fun kst u E' sb' g' f' hg h => ⟨0, kst, u, g', rfl, hg, Or.inl ⟨rfl, h⟩⟩)
          h2 hBc hBc⟩) (by omega)).mono fun w' c' ⟨p, hc'⟩ =>
        ⟨p, hc'.trans (itci_wb_mono (by omega))⟩
  · -- the weight of item states
    rintro b oX oY ist E sb f ⟨t, kst, u, g, rfl, -, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · have := ca.wtR _ _ _ _ _ _ _ h
      have := itci_tag_wt (t := 0) (by omega) kst u
      omega
    · have := sa.wtR _ _ _ _ _ _ _ h
      have := itci_tag_wt (t := 1) le_rfl kst u
      omega
  · -- the step
    rintro b oX oY ist E sb f ⟨t, kst, u, g, rfl, hg, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · have hs := ca.wtR _ _ _ _ _ _ _ h
      have := itci_tag_wt (t := 0) (by omega) kst u
      obtain ⟨tg, sub⟩ := itci_pk_in (P := Pg) (W := Ws) (t := 0) (kst := kst) (u := u)
        (by omega) (by omega)
      refine FunAll.intro hfk ((itci_ite (Bd := itciWB (13 * (Ws + 1)))
        (Pst := ItCfIPost (itciPR Rcf Rs) e c S L K b oX oY E sb f (itciXp Xc Xs W₀))
        tg ?_).mono fun w' cost ⟨p, hc'⟩ => ⟨by omega, p⟩)
      rw [if_pos rfl]
      refine (itci_callwrap sub ((ca.step _ _ _ _ _ _ _ h).mono fun w' c' ⟨h1, h2⟩ =>
        ⟨h1, itci_post_wrap (R := ⟨Rs.Ki, Rcf Rs.Ki⟩) (R' := itciPR Rcf Rs) 0 (fun _ _ h => h)
          (fun kst u E' sb' g' f' hg h => ⟨0, kst, u, g', rfl, hg, Or.inl ⟨rfl, h⟩⟩)
          h2 hg hBc⟩) (by omega)).mono fun w' c' ⟨p, hc'⟩ =>
        ⟨p, hc'.trans (itci_wb_mono (by omega))⟩
    · have hs := sa.wtR _ _ _ _ _ _ _ h
      have := itci_tag_wt (t := 1) le_rfl kst u
      obtain ⟨tg, sub⟩ := itci_pk_in (P := Pg) (W := Ws) (t := 1) (kst := kst) (u := u)
        (by omega) (by omega)
      refine FunAll.intro hfk ((itci_ite (Bd := itciWB (13 * (Ws + 1)))
        (Pst := ItCfIPost (itciPR Rcf Rs) e c S L K b oX oY E sb f (itciXp Xc Xs W₀))
        tg ?_).mono fun w' cost ⟨p, hc'⟩ => ⟨by omega, p⟩)
      rw [if_neg one_ne_zero]
      refine (itci_callwrap sub ((sa.step _ _ _ _ _ _ _ h).mono fun w' c' ⟨h1, h2⟩ =>
        ⟨h1, itci_post_wrap (R := Rs) (R' := itciPR Rcf Rs) 1 (fun _ _ h => h)
          (fun kst u E' sb' g' f' hg h => ⟨1, kst, u, g', rfl, hg, Or.inr ⟨rfl, h⟩⟩)
          h2 hg hBs⟩) le_rfl).mono fun w' c' ⟨p, hc'⟩ =>
        ⟨p, hc'.trans (itci_wb_mono (by omega))⟩

/-- **The bound of the pair part is polynomial** when the bounds of the branches are (the
configuration bound at the kept-value and object bound `itciBk Xs W`). -/
theorem itciXp_pbu {Xc : ℕ → ℕ → ℕ} {Xs : ℕ → ℕ} (hs : PBU fun _ W _ => Xs W)
    (hc : PBU fun _ W _ => Xc W (itciBk Xs W)) : PBU fun _ W _ => itciXp Xc Xs W := by
  have hp : PBU fun _ W _ => 10 * itSVB W + 50 * (2 * W + 3 + 1) ^ 2 + 100 := by
    simp only [itSVB, cmOutB, cmPb, cmNb]
    norm_poly
  have ho : PBU fun _ W _ => itciOW W := by
    simp only [itciOW, itCfObjB]
    norm_poly
  refine PBU.mono (PBU.addc (PBU.smul 3000 (PBU.add hp (PBU.smul 30
    (PBU.add (PBU.add hs ho) hc)))) 4000) fun _ W _ => ?_
  unfold itciXp itciPWX itciPW itciWB itciBk
  omega

end GI.Impl
