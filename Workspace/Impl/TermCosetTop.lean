import Workspace.Impl.TermCosetRes
import Workspace.Impl.TermCosetRel
import Workspace.Impl.TermStep

/-!
# The coset program of one radical coset (Theorems A.22 and A.23)

This file links the residual program `tmCsResF` (`TermCosetRes.lean`) to the terminal:
the table `vs` of the coset calls is a `TmCsTabOK` table of the rows (`tmCs_tabOK_of`), and the
residual set `tmCsResSet` is the set `tmGlRes` of `TermGlueLabSpec` (`tmCs_resSet_eq`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens)
open scoped Pointwise

variable {Ω C : Type}

attribute [local instance] stringRAct

/-- **The coset table is a table of the rows.** -/
theorem tmCs_tabOK_of (S : State Ω C) {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (σH : List (Perm (Fin m))) {vs : List Val}
    (hvs : List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (tmCosetState S E σH ij).answer)
      vs (tmCosets q)) :
    TmCsTabOK (gens σH) (fun i => tmRowStr S E (.inl i)) (fun j => tmRowStr S E (.inr j)) vs := by
  have hlen : vs.length = q * q := by rw [hvs.length_eq, length_tmCosets]; ring
  refine ⟨hlen, fun i j => ?_⟩
  have hij : i.1 * q + j.1 < q ^ 2 := by
    have : i.1 * q + j.1 < q * q := by nlinarith [i.2, j.2]
    nlinarith
  obtain ⟨h1, h2, hc⟩ := tmCosets_getElem? q (i.1 * q + j.1) hij
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0)
  have e1 : (⟨(i.1 * q + j.1) / q, h1⟩ : Fin q) = i := by
    ext; simp only; rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt j.2]; simp
  have e2 : (⟨(i.1 * q + j.1) % q, h2⟩ : Fin q) = j := by
    ext; simp only; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]
  rw [e1, e2] at hc
  have hlt : i.1 * q + j.1 < vs.length := by rw [hlen]; nlinarith
  refine ⟨vs[i.1 * q + j.1], List.getElem?_eq_getElem hlt, ?_⟩
  have hR := List.forall₂_iff_get.1 hvs
  have := hR.2 (i.1 * q + j.1) hlt (by rw [← hR.1]; exact hlt)
  have hget : (tmCosets q).get ⟨i.1 * q + j.1, by rw [← hR.1]; exact hlt⟩ = (i, j) := by
    have := List.getElem?_eq_getElem (l := tmCosets q) (i := i.1 * q + j.1)
      (by rw [← hR.1]; exact hlt)
    rw [hc] at this
    exact (Option.some.inj this).symm
  rw [hget] at this
  simp only [List.get_eq_getElem] at this
  convert this using 1
  unfold tmCosetState
  rw [rowState_answer]
  rfl

/-- **The residual set is the set of `TermGlueLabSpec`.** -/
theorem tmCs_resSet_eq {S : State Ω C} {L : SuppliedLabels S} {label : Ω → Fin L.q}
    (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
    (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L.toGiantLabels label E)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
    (hqα : (S.N : ℝ) ^ P₀.α < L.q) (σH σN : List (Perm (Fin m)))
    (hH : gens σH = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb)
    (hNg : gens σN = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb) (r : Perm (Fin m)) :
    tmCsResSet (gens σH) (gens σN) (fun i => tmRowStr S E (.inl i))
        (fun j => tmRowStr S E (.inr j)) r =
      tmGlRes ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα) r := by
  unfold tmCsResSet tmGlRes
  rw [hH, hNg]
  rfl

/-! ### The program -/

/-- **The coset program** on `[V, encPerm r]`, `V = [[sv, lv, cv, a18, rl], us, vs]`: read
`σH, σN, m, q`; the residual answer (`res`); the label coset (`lab`, `TermGlueLabSpec`); the
`J`-answer (`jj`, `TermJSpec`); the table of the numbering (`tab`); the relabeled answer
(`rel`). -/
def tmCsTopF (res lab jj tab rel : ℕ) : Expr :=
  .letE (.get (arg 0) (.nat 0))
  (.letE (.get (.var 1) (.nat 2))
  (.letE (.get (.var 1) (.nat 3))
  (.letE (.length (.var 2))
  (.letE (.length (.get (.var 2) (.nat 0)))
  (.letE (.call res (Expr.mkList [.get (.var 3) (.nat 0), .get (.var 3) (.nat 1),
      .get (arg 0) (.nat 2), .var 5, .var 4, arg 1]))
  (.letE (.call lab (mk3 (arg 0) (arg 1) (.var 6)))
  (.letE (.call jj (mk3 (arg 0) (arg 1) (.var 7)))
  (.letE (.call tab (mk2 (.get (.var 1) (.nat 0)) (.var 2)))
  (.call rel (mk2 (.var 9) (.var 8)))))))))))

/-- The weight of a canonical answer on `Fin n`. -/
theorem tmCs_wt_ansC {n : ℕ} {Ω' : Type} {e : Ω' ≃ Fin n} {u : Val} {A : Set (Perm Ω')}
    (h : AnsC e u A) : u.wt ≤ 1000 * (n + 1) ^ 6 := by
  have h6 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  rcases h with ⟨rfl, -⟩ | ⟨x, gs, rfl, hgl, -⟩
  · have : (Val.list []).wt ≤ 5 := by decide
    omega
  · have := wt_list2_le (encPerm x) (encGroup gs)
    have := wt_encPerm_le x
    have := wt_encGroup_le_sq hgl
    have : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- Where the pieces of the coset program sit (the residual program, the table and the
relabeling; `lab` and `jj` enter through their specifications). -/
structure TmCsTopAt (P : Program) (f res lab jj tab rel : ℕ)
    (mkg rad sup objs msh sh ell rec comp app red jst rg ax px ay py mx fx my fy first inv : ℕ)
    (dom rg' tb tbe inv' conj mp : ℕ) : Prop where
  hf : P.funs[f]? = some (tmCsTopF res lab jj tab rel)
  hres : TmCsResAt P res mkg rad sup objs msh sh ell rec comp app red jst rg ax px ay py mx fx
    my fy first inv
  htab : TmCsTabAt P tab dom rg' tb tbe inv'
  hrel : P.funs[rel]? = some (tmCsRelF conj mp)
  hconj : P.funs[conj]? = some (tmCsConjF comp)
  hmp : P.HasAt mp (mapFuns mp conj)

/-- The polynomial part of the cost of the coset program, in `X = 100 (wt [V, r] + 1)`. -/
def tmCsTopQ (p : Prim) (Kr Dr Ks Ds Kl Dl Kj Dj X : ℕ) : ℕ :=
  tmCsResQ p Kr Dr Ks Ds X + Kl * (10 ^ 4 * (X + 1) ^ 6) ^ Dl +
    Kj * (10 ^ 4 * (X + 1) ^ 6) ^ Dj + tmCsTabK X + tmCsRelK X + 10 ^ 7 * (X + 1) ^ 6

theorem tmCs_cast2 {n A cb Q : ℕ} {B RB : ℝ} (h : n ≤ A + cb) (hcb : (cb : ℝ) ≤ B + RB)
    (hAB : (A : ℝ) + B ≤ Q) : (n : ℝ) ≤ Q + RB := by
  have : (n : ℝ) ≤ A + cb := by exact_mod_cast h
  linarith

attribute [local instance] stringRAct in
/-- **The coset program**, with its cost before the comparison with `expLogSq`. -/
theorem tmCs_top_spec (hst : GI.Cited.PointwiseStab) (dixon : GI.Cited.DixonDerivedLength) {P : Program}
    {f res lab jj tab rel : ℕ}
    {mkg rad sup objs msh sh ell rec comp app red jst rg ax px ay py mx fx my fy first inv : ℕ}
    {dom rg' tb tbe inv' conj mp : ℕ}
    (hA : TmCsTopAt P f res lab jj tab rel mkg rad sup objs msh sh ell rec comp app red jst rg ax
      px ay py mx fx my fy first inv dom rg' tb tbe inv' conj mp)
    (hjst : P.prims[jst]? = some (pointwiseStabPrim hst)) {Kr Dr Ks Ds Kc Dc Kl Dl Kj Dj : ℕ}
    (hrad : Iface.TermRadSpec P Kr Dr rad) (hsup : Iface.TermSupSpec P Ks Ds sup)
    (hrec : Iface.TermRecSpec P Kc Dc rec) (hlab : Iface.TermGlueLabSpec P Kl Dl lab)
    (hjj : Iface.TermJSpec P Kj Dj jj)
    {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ)
    (hc : Function.Injective c)
    (sv lv : Val) (L : SuppliedLabels S) (hsv : Canon e c sv S) (hlv : LabValStd e S lv L)
    (hq0 : P₀.q₀ < L.q) (hgood : Good P₀ .giant S) (hrow : RowCase P₀.α S L.toGiantLabels)
    (label : Ω → Fin L.q) (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q)
    {m : ℕ} (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom)
    (hP : PureCoords S L.toGiantLabels label E)
    (σH σN σS : List (Perm (Fin m)))
    (hH : gens σH = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb)
    (hNg : gens σN = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb)
    (hSg : gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hlH : σH.length ≤ (k + L.q) ^ 2) (hlN : σN.length ≤ (k + L.q) ^ 2)
    (hlS : σS.length ≤ (k + L.q) ^ 2)
    (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
    (hqα : (S.N : ℝ) ^ P₀.α < L.q) (us vs : List Val)
    (hus : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
        us (tmTests L.q))
    (hvs : List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (tmCosetState S E σH ij).answer)
        vs (tmCosets L.q))
    (r : Perm (Fin m))
    (hr : r ∈ ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα).Hb) :
    FunAll P f (.list [(.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
          encFun (rowLab e L.con.blocks)], .list us, .list vs]), encPerm r])
      (fun u cost => AnsC (domEquiv e S.dom) u
          (tmDomSet ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα).e
            (tmCosetT ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα)
              r)) ∧
        ∃ ℓ : ℕ, (ℓ : ℝ) ≤ 5 * Real.logb 3 m + 1 ∧
          (cost : ℝ) ≤ (tmCsTopQ (pointwiseStabPrim hst) Kr Dr Ks Ds Kl Dl Kj Dj
            (100 * ((Val.list [(.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
              encFun (rowLab e L.con.blocks)], .list us, .list vs]), encPerm r]).wt + 1)) : ℝ) +
            20 * ((5 * ((L.q : ℝ) + 1) ^ 3 + 1) ^ ℓ * (Kc * (((m + L.q : ℕ) : ℝ) + 2) ^ Dc))) := by
  set F := RowForm.ofPure hnat hq E hP ⟨0, h0⟩ with hF
  set T := F.rowTerminal P₀ htr hcard hsN hN hqα with hT
  set cv := coordsVal e S E with hcv
  set a18 := a18Out σH σN σS 0 with ha18
  set V0 := Val.list [sv, lv, cv, a18, encFun (rowLab e L.con.blocks)] with hV0
  set V := Val.list [V0, .list us, .list vs] with hV
  set a := Val.list [V, encPerm r] with ha
  set X := 100 * (a.wt + 1) with hX
  have hNH : gens σN ≤ gens σH := by rw [hH, hNg]; exact F.Nb_le
  have hnorm : GI.Multicoset.Normalizes (gens σH) (gens σN) := by
    rw [hH, hNg]; exact F.normalizes
  have hrH : r ∈ gens σH := by rw [hH]; exact hr
  have hq1 : 0 < L.q := by omega
  have hTab := tmCs_tabOK_of S E σH hvs
  have hs : (domFin e S.dom).length = m * L.q := by
    have h1 := Nat.card_congr (domEquiv e S.dom)
    rw [Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h1
    rw [← h1, ← Fintype.card_fin m, hcard]; rfl
  refine FunAll.intro hA.hf ?_
  unfold tmCsTopF
  set rows := (List.finRange L.q).map fun j => natList ((List.finRange m).map
      fun β => ((e (E (β, j)).val : Fin k) : ℕ)) with hrows
  have hcvl : cv = .list rows := rfl
  set a18l := [Val.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm),
    Val.nat 0] with ha18l
  set V0l := [sv, lv, cv, a18, encFun (rowLab e L.con.blocks)] with hV0l
  -- weights
  have wV : V.wt < a.wt := wt_le_wt_list (by simp [ha])
  have wr : (encPerm r).wt < a.wt := wt_le_wt_list (by simp [ha])
  have wV0 : V0.wt < V.wt := wt_le_wt_list (by simp [hV])
  have wvs : (Val.list vs).wt < V.wt := wt_le_wt_list (by simp [hV])
  have wcv : cv.wt < V0.wt := wt_le_wt_list (by simp [hV0])
  have wsv : sv.wt < V0.wt := wt_le_wt_list (by simp [hV0])
  have wa18 : a18.wt < V0.wt := wt_le_wt_list (by simp [hV0])
  have wσH : (Val.list (σH.map encPerm)).wt < a18.wt := wt_le_wt_list (by simp [ha18, a18Out])
  have wσN : (Val.list (σN.map encPerm)).wt < a18.wt := wt_le_wt_list (by simp [ha18, a18Out])
  have wq : L.q < cv.wt := by
    have := length_lt_wt_list rows
    rw [hcvl]; simpa [hrows] using this
  have hr0 : rows[0]? = some (.list ((List.finRange m).map fun β =>
      Val.nat ((e (E (β, ⟨0, hq1⟩)).val : Fin k) : ℕ))) := by
    simp [hrows, natList, hq1, Function.comp_def]
  have wr0 : (Val.list ((List.finRange m).map fun β =>
      Val.nat ((e (E (β, ⟨0, hq1⟩)).val : Fin k) : ℕ))).wt < cv.wt := by
    rw [hcvl]; exact wt_le_wt_list (List.mem_of_getElem? hr0)
  have wm : m < (Val.list ((List.finRange m).map fun β =>
      Val.nat ((e (E (β, ⟨0, hq1⟩)).val : Fin k) : ℕ))).wt := by
    have := length_lt_wt_list ((List.finRange m).map fun β =>
      Val.nat ((e (E (β, ⟨0, hq1⟩)).val : Fin k) : ℕ))
    simpa using this
  -- 1-5. reading the input
  have d0 := Det.arg' (P := P) (vs := [V, encPerm r]) (rest := []) (j := 0)
    (v := .list [V0, .list us, .list vs]) rfl
  have c1 := Det.get' d0 (Det.nat 0) (vs := [V0, .list us, .list vs]) (v := V0) rfl
  refine EvalAll.letE c1 ?_
  rintro _ c1' ⟨rfl, hc1⟩
  have e1 := Det.var' (P := P) (env := [a, V0]) (i := 1) (v := .list V0l) rfl
  have c2 := Det.get' e1 (Det.nat 2) (vs := V0l) (v := cv) rfl
  refine EvalAll.letE c2 ?_
  rintro _ c2' ⟨rfl, hc2⟩
  have f1 := Det.var' (P := P) (env := [a, V0, cv]) (i := 1) (v := .list V0l) rfl
  have c3 := Det.get' f1 (Det.nat 3) (vs := V0l) (v := .list a18l) rfl
  refine EvalAll.letE c3 ?_
  rintro _ c3' ⟨rfl, hc3⟩
  have g2 := Det.var' (P := P) (env := [a, V0, cv, .list a18l]) (i := 2) (v := .list rows) rfl
  have c4 := Det.length g2
  rw [show rows.length = L.q by simp [hrows]] at c4
  refine EvalAll.letE c4 ?_
  rintro _ c4' ⟨rfl, hc4⟩
  have h2 := Det.var' (P := P) (env := [a, V0, cv, .list a18l, .nat L.q]) (i := 2)
    (v := .list rows) rfl
  have c5 := Det.length (Det.get' h2 (Det.nat 0) hr0)
  rw [show ((List.finRange m).map fun β => Val.nat ((e (E (β, ⟨0, hq1⟩)).val : Fin k) : ℕ)).length
    = m by simp] at c5
  refine EvalAll.letE c5 ?_
  rintro _ c5' ⟨rfl, hc5⟩
  -- 6. the residual answer
  set env6 := [a, V0, cv, .list a18l, .nat L.q, .nat m] with henv6
  set Cm := 3 * a.wt + 20 with hCm
  have wnq := wt_nat_le L.q
  have wnm := wt_nat_le m
  have hpieces : ∀ p ∈ [(Expr.get (.var 3) (.nat 0), Val.list (σH.map encPerm)),
      (Expr.get (.var 3) (.nat 1), Val.list (σN.map encPerm)),
      (Expr.get (arg 0) (.nat 2), Val.list vs), (Expr.var 5, Val.nat m), (Expr.var 4, Val.nat L.q),
      (arg 1, encPerm r)], Det P env6 p.1 p.2 Cm := by
    have k3 := Det.var' (P := P) (env := env6) (i := 3) (v := .list a18l) rfl
    have k0 := Det.arg' (P := P) (vs := [V, encPerm r]) (rest := [V0, cv, .list a18l, .nat L.q,
      .nat m]) (j := 0) (v := .list [V0, .list us, .list vs]) rfl
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (Det.get' k3 (Det.nat 0) (vs := a18l) (v := .list (σH.map encPerm)) rfl).mono
        (by have : a18.wt = (Val.list a18l).wt := rfl; omega)
    · exact (Det.get' k3 (Det.nat 1) (vs := a18l) (v := .list (σN.map encPerm)) rfl).mono
        (by have : a18.wt = (Val.list a18l).wt := rfl; omega)
    · exact (Det.get' k0 (Det.nat 2) (vs := [V0, .list us, .list vs]) (v := .list vs) rfl).mono
        (by
          have : (Val.list [V, encPerm r]).wt = a.wt := rfl
          have : V.wt = (Val.list [V0, .list us, .list vs]).wt := rfl
          omega)
    · exact (Det.var' (P := P) (env := env6) (i := 5) (v := .nat m) rfl).mono (by omega)
    · exact (Det.var' (P := P) (env := env6) (i := 4) (v := .nat L.q) rfl).mono (by omega)
    · exact (Det.arg' (P := P) (vs := [V, encPerm r]) (rest := [V0, cv, .list a18l, .nat L.q,
        .nat m]) (j := 1) (v := encPerm r) rfl).mono
        (by have : (Val.list [V, encPerm r]).wt = a.wt := rfl; omega)
  have dres := Det.mkList _ hpieces
  have hresIn : (Val.list ([(Expr.get (.var 3) (.nat 0), Val.list (σH.map encPerm)),
      (Expr.get (.var 3) (.nat 1), Val.list (σN.map encPerm)),
      (Expr.get (arg 0) (.nat 2), Val.list vs), (Expr.var 5, Val.nat m), (Expr.var 4, Val.nat L.q),
      (arg 1, encPerm r)].map Prod.snd)) = tmCsResIn σH σN vs L.q r := rfl
  rw [hresIn] at dres
  have wIn : (tmCsResIn σH σN vs L.q r).wt ≤ X := by
    have := wt_list_le [Val.list (σH.map encPerm), Val.list (σN.map encPerm), Val.list vs,
      Val.nat m, Val.nat L.q, encPerm r]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    have e : (tmCsResIn σH σN vs L.q r).wt = (Val.list [Val.list (σH.map encPerm),
      Val.list (σN.map encPerm), Val.list vs, Val.nat m, Val.nat L.q, encPerm r]).wt := rfl
    omega
  have hRes := tmCs_res_spec hst dixon hA.hres hjst hrad hsup hrec h0
    (x := fun i => tmRowStr S E (.inl i)) (y := fun j => tmRowStr S E (.inr j))
    hNH hnorm hTab hrH wIn (by omega) (by omega)
  refine EvalAll.letE (EvalAll.call_spec dres (FunAll.wt_lt hRes)) ?_
  rintro w1 c6 ⟨cb6, ⟨⟨hw1, ℓ, hℓ, hcb6⟩, hw1c⟩, hc6⟩
  rw [tmCs_resSet_eq hnat hq h0 E hP htr hcard hsN hN hqα σH σN hH hNg r] at hw1
  -- 7. the label coset
  set env7 := env6 ++ [w1] with henv7
  have l0 := Det.arg' (P := P) (vs := [V, encPerm r]) (rest := [V0, cv, .list a18l, .nat L.q,
    .nat m, w1]) (j := 0) (v := V) rfl
  have l1 := Det.arg' (P := P) (vs := [V, encPerm r]) (rest := [V0, cv, .list a18l, .nat L.q,
    .nat m, w1]) (j := 1) (v := encPerm r) rfl
  have l6 := Det.var' (P := P) (env := env7) (i := 6) (v := w1) rfl
  have hLab := hlab S k e c hc sv lv L hsv hlv hq0 hgood hrow label hnat hq h0 E hP σH σN σS hH hNg
    hSg htr hlH hlN hlS hcard hsN hN hqα us vs hus hvs r hr w1 hw1
  refine EvalAll.letE (EvalAll.call_spec (Det.mk3 l0 l1 l6) hLab) ?_
  rintro w2 c7 ⟨cb7, ⟨hw2, hcb7⟩, hc7⟩
  -- 8. the `J`-answer
  set env8 := env7 ++ [w2] with henv8
  have j0 := Det.arg' (P := P) (vs := [V, encPerm r]) (rest := [V0, cv, .list a18l, .nat L.q,
    .nat m, w1, w2]) (j := 0) (v := V) rfl
  have j1 := Det.arg' (P := P) (vs := [V, encPerm r]) (rest := [V0, cv, .list a18l, .nat L.q,
    .nat m, w1, w2]) (j := 1) (v := encPerm r) rfl
  have j7 := Det.var' (P := P) (env := env8) (i := 7) (v := w2) rfl
  have hJ := hjj S k e c hc sv lv L hsv hlv hq0 hgood hrow label hnat hq h0 E hP σH σN σS hH hNg
    hSg htr hlH hlN hlS hcard hsN hN hqα us vs hus hvs r hr w2 hw2
  refine EvalAll.letE (EvalAll.call_spec (Det.mk3 j0 j1 j7) hJ) ?_
  rintro u c8 ⟨cb8, ⟨hu, hcb8⟩, hc8⟩
  -- 9. the table
  set env9 := env8 ++ [u] with henv9
  have t1 := Det.var' (P := P) (env := env9) (i := 1) (v := .list V0l) rfl
  have tsv := Det.get' t1 (Det.nat 0) (vs := V0l) (v := sv) rfl
  have t2 := Det.var' (P := P) (env := env9) (i := 2) (v := cv) rfl
  have c9 := Det.call (Det.mk2 tsv t2) (tmCs_tab_spec hA.htab e c hsv E hs hq1)
  refine EvalAll.letE c9 ?_
  rintro _ c9' ⟨rfl, hc9⟩
  -- 10. the relabeling
  set env10 := env9 ++ [.list [encPerm (tmCsRhoP e E hs), encPerm (tmCsRhoP e E hs)⁻¹]]
    with henv10
  have r9 := Det.var' (P := P) (env := env10) (i := 9)
    (v := .list [encPerm (tmCsRhoP e E hs), encPerm (tmCsRhoP e E hs)⁻¹]) rfl
  have r8 := Det.var' (P := P) (env := env10) (i := 8) (v := u) rfl
  have hmq0 : 0 < m * L.q := Nat.mul_pos h0 hq1
  have hRel := tmCs_rel_spec hA.hrel hA.hconj hA.hres.hcomp hA.hmp e E hs hmq0 hu
  refine (EvalAll.call_spec (Det.mk2 r9 r8) hRel).mono ?_
  rintro w c10 ⟨cb10, ⟨hw, hcb10⟩, hc10⟩
  refine ⟨hw, ℓ, hℓ, ?_⟩
  -- the cost
  have hX1 : 1 ≤ X + 1 := by omega
  have hP6 : ∀ {b : ℕ}, b ≤ X → (b + 1) ^ 6 ≤ (X + 1) ^ 6 := fun h => Nat.pow_le_pow_left (by omega) 6
  have hsumrows : L.q * m ≤ (rows.map Val.wt).sum := by
    have hrow : ∀ v ∈ rows, m ≤ v.wt := by
      intro v hv
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hv
      have := length_lt_wt_list (((List.finRange m).map fun β =>
        ((e (E (β, j)).val : Fin k) : ℕ)).map Val.nat)
      simp only [List.length_map, List.length_finRange] at this
      exact this.le
    have key : ∀ l : List Val, (∀ v ∈ l, m ≤ v.wt) → l.length * m ≤ (l.map Val.wt).sum := by
      intro l hl
      induction l with
      | nil => simp
      | cons x l ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
        have := hl x (by simp)
        have := ih fun v hv => hl v (by simp [hv])
        omega
    have := key rows hrow
    simpa [hrows] using this
  have hmq : m * L.q ≤ X := by
    have := sum_wt_lt_wt_list rows
    have e1 : cv.wt = (Val.list rows).wt := rfl
    rw [Nat.mul_comm]; omega
  have hkX : k < sv.wt := by
    obtain ⟨gv, dv, xv, yv, hv, rv, -, hd, -, -, -, -, hsv'⟩ := hsv.val
    have hd' : dv = indVal e S.dom := DomVal.eq_indVal hd
    have hk1 : k < (indVal e S.dom).wt := by
      have := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (indF e S.dom i))
      simpa [indVal, encFun] using this
    have hk2 : (indVal e S.dom).wt < sv.wt := by
      rw [hsv', ← hd']; exact wt_le_wt_list (by simp)
    omega
  have ww1 := tmCs_wt_ansC hw1
  have ww2 := tmCs_wt_ansC hw2
  have wu := tmCs_wt_ansC hu
  have ww := tmCs_wt_ansC hw
  rw [hs] at ww
  have hm6 := hP6 (b := m) (by omega)
  have hmq6 := hP6 (b := m * L.q) hmq
  -- the label and `J` calls
  have hlabw : (Val.list [V, encPerm r, w1]).wt + 1 ≤ 10 ^ 4 * (X + 1) ^ 6 := by
    have := wt_list3_le V (encPerm r) w1
    have : X ≤ (X + 1) ^ 6 := by
      have := Nat.le_self_pow (n := 6) (by norm_num) (X + 1); omega
    omega
  have hjw : (Val.list [V, encPerm r, w2]).wt + 1 ≤ 10 ^ 4 * (X + 1) ^ 6 := by
    have := wt_list3_le V (encPerm r) w2
    have : X ≤ (X + 1) ^ 6 := by
      have := Nat.le_self_pow (n := 6) (by norm_num) (X + 1); omega
    omega
  have hcb7' : cb7 ≤ Kl * (10 ^ 4 * (X + 1) ^ 6) ^ Dl :=
    hcb7.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlabw _))
  have hcb8' : cb8 ≤ Kj * (10 ^ 4 * (X + 1) ^ 6) ^ Dj :=
    hcb8.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hjw _))
  -- the table and the relabeling
  have htabX : (Val.list [sv, cv]).wt + k ≤ X := by
    have := wt_list2_le sv cv
    omega
  have hc9' : tmCsTabK ((Val.list [sv, cv]).wt + k) ≤ tmCsTabK X :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hcb10' : cb10 ≤ tmCsRelK X :=
    hcb10.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have wρ := wt_encPerm_le (tmCsRhoP e E hs)
  have wρi := wt_encPerm_le (tmCsRhoP e E hs)⁻¹
  have wtt := wt_list2_le (encPerm (tmCsRhoP e E hs)) (encPerm (tmCsRhoP e E hs)⁻¹)
  have hq2 : (m * L.q + 1) ^ 2 ≤ (m * L.q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hX6 : X ≤ (X + 1) ^ 6 := by
    have := Nat.le_self_pow (n := 6) (by norm_num) (X + 1); omega
  set Anat := Kl * (10 ^ 4 * (X + 1) ^ 6) ^ Dl + Kj * (10 ^ 4 * (X + 1) ^ 6) ^ Dj +
    tmCsTabK X + tmCsRelK X + 10 ^ 7 * (X + 1) ^ 6 with hAnat
  refine tmCs_cast2 (A := Anat) (cb := cb6) ?_ hcb6 ?_
  · have hlen6 : [((Expr.var 3).get (Expr.nat 0), Val.list (List.map encPerm σH)),
        ((Expr.var 3).get (Expr.nat 1), Val.list (List.map encPerm σN)),
        ((arg 0).get (Expr.nat 2), Val.list vs), (Expr.var 5, Val.nat m),
        (Expr.var 4, Val.nat L.q), (arg 1, encPerm r)].length = 6 := rfl
    rw [hlen6] at hc6
    have e1 : (Val.list [V, encPerm r]).wt = a.wt := rfl
    have e2 : (Val.list V0l).wt = V0.wt := rfl
    have e3 : (Val.list a18l).wt = a18.wt := rfl
    have e4 : (Val.list rows).wt = cv.wt := rfl
    have e5 : (Val.list ([((Expr.var 3).get (Expr.nat 0), Val.list (List.map encPerm σH)),
        ((Expr.var 3).get (Expr.nat 1), Val.list (List.map encPerm σN)),
        ((arg 0).get (Expr.nat 2), Val.list vs), (Expr.var 5, Val.nat m),
        (Expr.var 4, Val.nat L.q), (arg 1, encPerm r)].map Prod.snd)).wt =
        (tmCsResIn σH σN vs L.q r).wt := rfl
    have w3a := wt_list3_le V (encPerm r) w1
    have w3b := wt_list3_le V (encPerm r) w2
    have w2a := wt_list2_le sv cv
    have w2b := wt_list2_le (Val.list [encPerm (tmCsRhoP e E hs), encPerm (tmCsRhoP e E hs)⁻¹]) u
    have e6 : tmCsTabK ((Val.list [sv, coordsVal e S E]).wt + k) =
        tmCsTabK ((Val.list [sv, cv]).wt + k) := rfl
    have wtt' := FunDet.wt_lt (tmCs_tab_spec hA.htab e c hsv E hs hq1)
    omega
  · rw [show tmCsTopQ (pointwiseStabPrim hst) Kr Dr Ks Ds Kl Dl Kj Dj X =
      tmCsResQ (pointwiseStabPrim hst) Kr Dr Ks Ds X + Anat by unfold tmCsTopQ; rw [hAnat]; ring]
    push_cast; linarith

end GI.Impl
