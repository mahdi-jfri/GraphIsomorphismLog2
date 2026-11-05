module

public import Workspace.Impl.AggItemCiObj

@[expose] public section

/-!
# Cases 2b and 3: the item stage from its pair part

The item of a branch of Cases 2b and 3 is `cfgOutItem O ch oX oY` (`AuxCases.lean`): the overcoset
item `objItem` of two colored partitions, the configuration query or the first-rectangle item of
two pair configurations, and no item for objects of different kinds. The start program
`itciDF` reads the kinds (the first entries of the object values) and

* for two partitions, returns the overcosets of the colored-partition program (`itci_prog`) as a
  finished result, with the kept value unchanged;
* for two pair configurations, calls the start program of the pair part;
* otherwise returns the empty result, with the kept value unchanged.

`ItciPairSpec` is the contract of the pair part: the item-stage contract `ItCfItemSpec` with the
start asked only for two pair configurations, and with a bound on the values of the pair
configurations of a branch (the start program reads the kinds of both objects, so it pays for
their values). `itci_itemSpec` gives `ItCfItemSpec` from it, with the bound `itciXt`, which is
polynomial when the pair bound is (`itciXt_pbu`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)
open GI.Machine (BinOp)

variable {Ω C : Type} {k : ℕ}

/-! ### The program -/

/-- The kind of the object at entry `i` of the input. -/
def itciTag (i : ℕ) : Expr := .get (.get (.var 0) (.nat i)) (.nat 0)

/-- The empty result, with the kept value of the input. -/
def itciEmp : Expr := mk2 (.nat 0) (mk3 .nil .nil (.get (.var 0) (.nat 4)))

/-- The result of two partitions, with the colored-partition program at `fp`. -/
def itciPartE (fp : ℕ) : Expr :=
  mk2 (.nat 0) (mk3 .nil
    (.call fp (mk2 (.get (.get (.var 0) (.nat 2)) (.nat 2)) (.get (.get (.var 0) (.nat 3)) (.nat 2))))
    (.get (.var 0) (.nat 4)))

/-- **The start program** on `[K.v, b, ⟨oX⟩, ⟨oY⟩, wI]`, with the colored-partition program at
`fp` and the start of the pair part at `fq`. -/
def itciDF (fp fq : ℕ) : Expr :=
  .ite (.arith .eq (itciTag 2) (.nat 2))
    (.ite (.arith .eq (itciTag 3) (.nat 2)) (.call fq (.var 0)) itciEmp)
    (.ite (.arith .eq (itciTag 2) (.nat 1))
      (.ite (.arith .eq (itciTag 3) (.nat 1)) (itciPartE fp) itciEmp) itciEmp)

/-! ### The contract of the pair part -/

variable (I : Iface) (Pg : Program)

/-- **What the pair part must do at a context `K`**: `ItCfItemAt`, with the start asked only for
two pair configurations, and the values of the pair configurations of a branch weigh at most
`B`. -/
structure ItciPairAt (R : ItCfIRel) (fi fs fk : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
    (L : SuppliedLabels S) (K : ItSCtx k S L) (B : ℕ) : Prop where
  init : FunAll Pg fi K.v (fun w cost => ∃ E, R.Ki e c S L K w E ∧ cost ≤ B)
  ne : ∀ w E, R.Ki e c S L K w E → E.Nonempty
  wtK : ∀ w E, R.Ki e c S L K w E → w.wt ≤ B
  start : ∀ b X x₀ Y y₀ w E, ItCfObjOf K b (.pair X x₀) (.pair Y y₀) → R.Ki e c S L K w E →
    FunAll Pg fs (.list [K.v, stTv b, itCfOutV (.pair X x₀), itCfOutV (.pair Y y₀), w])
      (fun w' cost => cost ≤ B ∧ ItCfIPost R e c S L K b (.pair X x₀) (.pair Y y₀) E
        (itCfSb e (.pair X x₀) (.pair Y y₀)) B B w')
  wtR : ∀ b oX oY ist E sb f, R.Ri e c S L K b oX oY ist E sb f → ist.wt ≤ B
  step : ∀ b oX oY ist E sb f, R.Ri e c S L K b oX oY ist E sb f →
    FunAll Pg fk ist (fun w cost => cost ≤ B ∧ ItCfIPost R e c S L K b oX oY E sb f B w)
  objW : ∀ b oX oY, ItCfObjOf K b oX oY →
    (∀ X x₀, oX = .pair X x₀ → (itCfOutV oX).wt ≤ B) ∧
      ∀ Y y₀, oY = .pair Y y₀ → (itCfOutV oY).wt ≤ B

/-- **The contract of the pair part** at `fi`, `fs`, `fk` with the bound `Xp`. -/
def ItciPairSpec (F : Funs) (fi fs fk : ℕ) (Xp : ℕ → ℕ) : Prop :=
  ∃ R : ItCfIRel, ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
    (sv lv : Val) (L : SuppliedLabels S), AsCall I Pg F e c S sv lv L →
    ∀ K : ItSCtx k S L, K.OK e c → (K.case = .twoB ∨ K.case = .three) →
      ItciPairAt Pg R fi fs fk e c S L K (Xp (I.inW .giant S))

/-! ### The relations -/

/-- The relations of the item stage from those of the pair part: an item state with at most
`f'` more calls has at most `f` more calls for `f ≥ f'`. -/
def itciR (R : ItCfIRel) : ItCfIRel where
  Ki := R.Ki
  Ri := fun e c S L K b oX oY ist E sb f => ∃ f', f' ≤ f ∧ R.Ri e c S L K b oX oY ist E sb f'

theorem itci_post_mono {R : ItCfIRel} {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
    {L : SuppliedLabels S} {K : ItSCtx k S L} {b : Fin (P₀.κ + 1) → Fin L.q}
    {oX oY : CfgOut L.q} {E : Set (ItCfCh S L.toGiantLabels)}
    {sb : ItCfCh S L.toGiantLabels → Script (Branches Ω)} {f f' B B' : ℕ} {w : Val}
    (h : ItCfIPost R e c S L K b oX oY E sb f B w) (hf : f ≤ f') (hB : B ≤ B') :
    ItCfIPost (itciR R) e c S L K b oX oY E sb f' B' w := by
  rcases h with ⟨r, pcs, os, wI, E', h1, h2, h3, h4, h5, h6⟩ | ⟨hf0, m, Ω', C', T, k', e', c', arg,
    kst, E', kk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · exact Or.inl ⟨r, pcs, os, wI, E', h1, h2, h3, h4, h5, h6.trans hB⟩
  · refine Or.inr ⟨by omega, m, Ω', C', T, k', e', c', arg, kst, E', kk, h1, h2, h3, h4, h5, h6,
      h7, h8, h9, fun u hu => ⟨f - 1, by omega, h10 u hu⟩⟩

/-! ### Branches of the program -/

theorem itci_ite {P : Program} {env : List Val} {c t e : Expr} {x nc Ec W Bd : ℕ}
    {Pst : Val → Prop} (hc : StDC P env c (.nat x) nc Ec W)
    (hb : EvalAll P env (if x = 0 then e else t) (fun w cb => Pst w ∧ cb ≤ Bd)) :
    EvalAll P env (.ite c t e) (fun w c' => Pst w ∧ c' ≤ nc * (W + 1) + Ec + 2 * Bd + 1) :=
  EvalAll.ite hc (fun _ _ h => ⟨x, h.1⟩) fun y cc h => by
    obtain ⟨h1, h2⟩ := h
    cases h1
    exact hb.wt_lt.mono fun w cb ⟨⟨p, hle⟩, hw⟩ => ⟨p, by omega⟩

theorem itci_of_det {P : Program} {env : List Val} {e : Expr} {v : Val} {n E W Bd : ℕ}
    {Pst : Val → Prop} (h : StDC P env e v n E W) (hp : Pst v) (hB : n * (W + 1) + E ≤ Bd) :
    EvalAll P env e (fun w cb => Pst w ∧ cb ≤ Bd) :=
  EvalAll.mono h fun w cb ⟨hw, hc⟩ => by subst hw; exact ⟨hp, by omega⟩

/-- The input of the start program. -/
def itciIn (kv tb vX vY w : Val) : Val := .list [kv, tb, vX, vY, w]

theorem itci_get_in {P : Program} {kv tb vX vY w : Val} {W : ℕ}
    (hW : (itciIn kv tb vX vY w).wt ≤ W) {i : ℕ} {v : Val}
    (hv : ([kv, tb, vX, vY, w] : List Val)[i]? = some v) (hi : i + 2 ≤ W) :
    StDC P [itciIn kv tb vX vY w] (.get (.var 0) (.nat i)) v 3 0 W := by
  have hvw : v.wt ≤ W := by
    have := wt_le_wt_list (List.mem_of_getElem? hv)
    unfold itciIn at hW; omega
  exact StDC.get (StDC.var' rfl hW) (StDC.nat i hi) hv hvw

theorem itci_tag_spec {P : Program} {kv tb vX vY w : Val} {W : ℕ}
    (hW : (itciIn kv tb vX vY w).wt ≤ W) {i t : ℕ} {vs : List Val}
    (hv : ([kv, tb, vX, vY, w] : List Val)[i]? = some (.list (.nat t :: vs))) (hi : i + 2 ≤ W)
    (m : ℕ) (hm : m + 3 ≤ W) :
    StDC P [itciIn kv tb vX vY w] (.arith .eq (itciTag i) (.nat m))
      (.nat (if t = m then 1 else 0)) 7 0 W := by
  have g := itci_get_in (P := P) hW hv hi
  have hvw : (Val.list (.nat t :: vs)).wt ≤ W := by
    have := wt_le_wt_list (List.mem_of_getElem? hv)
    unfold itciIn at hW; omega
  have htw : (Val.nat t).wt ≤ W := by
    have := wt_le_wt_list (show Val.nat t ∈ Val.nat t :: vs from List.mem_cons_self ..); omega
  have g0 := StDC.get g (StDC.nat 0 (by omega)) (v := .nat t) rfl htw
  have := StDC.arith' g0 (StDC.nat m (by omega)) (op := .eq) (z := if t = m then 1 else 0)
    (by simp [BinOp.eval_eq]) (by split_ifs <;> omega)
  exact this.mono (by omega) (by omega)

/-- The finished result `[0, [⟨⟩, ov, w]]`. -/
def itciRes (ov w : Val) : Val := .list [.nat 0, .list [.list [], ov, w]]

theorem itci_emp_spec {P : Program} {kv tb vX vY w : Val} {W : ℕ}
    (hW : (itciIn kv tb vX vY w).wt ≤ W) (hr : (itciRes (.list []) w).wt ≤ W) (h6 : 6 ≤ W) :
    StDC P [itciIn kv tb vX vY w] itciEmp (itciRes (.list []) w) 15 0 W := by
  have g4 := itci_get_in (P := P) hW (i := 4) (v := w) rfl (by omega)
  have hin : (Val.list [.list [], .list [], w]).wt ≤ W := by
    have := wt_le_wt_list (show Val.list [.list [], .list [], w] ∈
      [Val.nat 0, .list [.list [], .list [], w]] by simp)
    unfold itciRes at hr; omega
  have := StDC.mk2 (StDC.nat 0 (by omega))
    (StDC.mk3 (StDC.nil (by omega)) (StDC.nil (by omega)) g4 hin (by omega)) hr (by omega)
  exact this.mono (by omega) (by omega)

theorem itci_part_spec {P : Program} {fp : ℕ} {kv tb vX vY w : Val} {W : ℕ}
    (hW : (itciIn kv tb vX vY w).wt ≤ W) {xs ys : List Val} {aX aY ov : Val}
    (hX : vX = .list xs) (hY : vY = .list ys) (haX : xs[2]? = some aX) (haY : ys[2]? = some aY)
    {cf : ℕ} (hf : FunDet P fp (.list [aX, aY]) ov cf)
    (ha : (Val.list [aX, aY]).wt ≤ W) (hr : (itciRes ov w).wt ≤ W) (h6 : 6 ≤ W) :
    StDC P [itciIn kv tb vX vY w] (itciPartE fp) (itciRes ov w) 40 cf W := by
  subst hX hY
  have g2 := itci_get_in (P := P) hW (i := 2) (v := .list xs) rfl (by omega)
  have g3 := itci_get_in (P := P) hW (i := 3) (v := .list ys) rfl (by omega)
  have g4 := itci_get_in (P := P) hW (i := 4) (v := w) rfl (by omega)
  have haXw : aX.wt ≤ W := by
    have := wt_le_wt_list (show aX ∈ [aX, aY] by simp); omega
  have haYw : aY.wt ≤ W := by
    have := wt_le_wt_list (show aY ∈ [aX, aY] by simp); omega
  have gX := StDC.get g2 (StDC.nat 2 (by omega)) haX haXw
  have gY := StDC.get g3 (StDC.nat 2 (by omega)) haY haYw
  have hin : (Val.list [.list [], ov, w]).wt ≤ W := by
    have := wt_le_wt_list (show Val.list [.list [], ov, w] ∈
      [Val.nat 0, .list [.list [], ov, w]] by simp)
    unfold itciRes at hr; omega
  have hov : ov.wt ≤ W := by
    have := wt_le_wt_list (show ov ∈ [.list [], ov, w] by simp); omega
  have := StDC.mk2 (StDC.nat 0 (by omega))
    (StDC.mk3 (StDC.nil (by omega)) (StDC.call (StDC.mk2 gX gY ha (by omega)) hf hov) g4 hin
      (by omega)) hr (by omega)
  exact this.mono (by omega) (by omega)

/-- **The start program, by the kinds of the objects.** -/
theorem itci_df_spec {P : Program} {fp fq : ℕ} {kv tb w : Val} {tX tY : ℕ} {xs ys : List Val}
    {W Bd : ℕ} (hW : (itciIn kv tb (.list (.nat tX :: xs)) (.list (.nat tY :: ys)) w).wt ≤ W)
    (h6 : 6 ≤ W) {Pst : Val → Prop}
    (hpr : tX = 2 → tY = 2 → EvalAll P [itciIn kv tb (.list (.nat tX :: xs))
      (.list (.nat tY :: ys)) w] (.call fq (.var 0)) (fun w cb => Pst w ∧ cb ≤ Bd))
    (hpt : tX = 1 → tY = 1 → EvalAll P [itciIn kv tb (.list (.nat tX :: xs))
      (.list (.nat tY :: ys)) w] (itciPartE fp) (fun w cb => Pst w ∧ cb ≤ Bd))
    (hem : ¬ (tX = 2 ∧ tY = 2) → ¬ (tX = 1 ∧ tY = 1) → EvalAll P [itciIn kv tb
      (.list (.nat tX :: xs)) (.list (.nat tY :: ys)) w] itciEmp (fun w cb => Pst w ∧ cb ≤ Bd)) :
    EvalAll P [itciIn kv tb (.list (.nat tX :: xs)) (.list (.nat tY :: ys)) w] (itciDF fp fq)
      (fun w c => Pst w ∧ c ≤ 50 * (W + 1) + 8 * Bd + 7) := by
  have cX2 := itci_tag_spec (P := P) hW (i := 2) rfl (by omega) 2 (by omega)
  have cY2 := itci_tag_spec (P := P) hW (i := 3) rfl (by omega) 2 (by omega)
  have cX1 := itci_tag_spec (P := P) hW (i := 2) rfl (by omega) 1 (by omega)
  have cY1 := itci_tag_spec (P := P) hW (i := 3) rfl (by omega) 1 (by omega)
  unfold itciDF
  refine EvalAll.mono (itci_ite (Bd := 21 * (W + 1) + 4 * Bd + 3) (Pst := Pst) cX2 ?_)
    fun _ _ ⟨p, hc⟩ => ⟨p, by omega⟩
  by_cases h2 : tX = 2
  · rw [if_pos h2, if_neg one_ne_zero]
    refine EvalAll.mono (itci_ite (Bd := Bd) cY2 ?_) fun _ _ ⟨p, hc⟩ => ⟨p, by omega⟩
    by_cases h3 : tY = 2
    · rw [if_pos h3, if_neg one_ne_zero]; exact hpr h2 h3
    · rw [if_neg h3, if_pos rfl]; exact hem (fun h => h3 h.2) (fun h => by omega)
  · rw [if_neg h2, if_pos rfl]
    refine EvalAll.mono (itci_ite (Bd := 7 * (W + 1) + 2 * Bd + 1) cX1 ?_)
      fun _ _ ⟨p, hc⟩ => ⟨p, by omega⟩
    by_cases h1 : tX = 1
    · rw [if_pos h1, if_neg one_ne_zero]
      refine EvalAll.mono (itci_ite (Bd := Bd) cY1 ?_) fun _ _ ⟨p, hc⟩ => ⟨p, by omega⟩
      by_cases h3 : tY = 1
      · rw [if_pos h3, if_neg one_ne_zero]; exact hpt h1 h3
      · rw [if_neg h3, if_pos rfl]; exact hem (fun h => h2 h.1) (fun h => h3 h.2)
    · rw [if_neg h1, if_pos rfl]
      exact (hem (fun h => h2 h.1) (fun h => h1 h.1)).mono fun _ _ ⟨p, hc⟩ => ⟨p, by omega⟩

end GI.Impl
