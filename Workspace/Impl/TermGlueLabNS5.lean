module

public import Workspace.Impl.TermGlueLabNDist
public import Workspace.Impl.TermGlueLabN6
public import Workspace.Impl.TermGlueLabPS5O
public import Workspace.Impl.TermGlueLabPEx
public import Workspace.Impl.TermGlueLabPAlign

@[expose] public section

/-!
# The label driver: step 5 with the choice of the orientation case

Proof of Theorem A.23, step 5. The paper adds the orientation coordinate (the
modulus `2` in front) exactly when all types of `x` are distinct. The step-5 function of the
driver first runs the test `tmGLNDistFuns` on the labels of `x` (entry 3 of the second part of
the step-5 input). If the flag is `1`, it runs the orientation variant `tmGLPStep5OF`;
otherwise it runs the plain step 5 `tmGLPStep5F`.

* `tmGLNS5F dist s5o s5p` and `tmGLNS5_spec`: the dispatch, for any results of the two
  variants.
* `tmGLN_s5At_plain`, `tmGLN_s5At_or`: the results of the two variants at the row terminal
  give `TmGLNS5Res`, the form step 6 and the vector program read (`TermGlueLabNDef.lean`).
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Lang GI.Paper Equiv
open GI.Cited (Val encPerm encGroup encIntMatrix gens)
open scoped Pointwise

attribute [local instance] stringRAct
set_option backward.isDefEq.respectTransparency false

/-- **The step-5 function of the driver**: the test on the labels of `x`, then the
orientation variant `s5o` (flag `1`) or the plain step 5 `s5p` (flag `0`). -/
def tmGLNS5F (dist s5o s5p : ℕ) : Expr :=
  .ite (.call dist (.get (arg 1) (.nat 3))) (.call s5o (.var 0)) (.call s5p (.var 0))

/-- The cost bound of the dispatch, for bounds `CO`, `CP` of the two variants. -/
def tmGLNS5C (W CO CP : ℕ) : ℕ := 4000 * (W + 1) ^ 2 + 4 * (CO + CP) + 100

/-- An `if` whose condition is a nonzero number and whose `then` branch has a specification. -/
theorem tmGLN_ite_pos {P : Program} {env : List Val} {c t e : Expr} {x cc : ℕ}
    (hc : Det P env c (.nat x) cc) (hx : x ≠ 0) {R : Val → ℕ → Prop} (ht : EvalAll P env t R) :
    EvalAll P env (.ite c t e) (fun w c' => ∃ ct, R w ct ∧ c' ≤ cc + ct + w.wt + 1) :=
  EvalAll.ite hc (fun _ _ h => ⟨x, h.1⟩) fun y cc' h => by
    obtain ⟨h1, h2⟩ := h
    cases h1
    rw [if_neg hx]
    exact ht.mono fun w ct hw => ⟨ct, hw, by omega⟩

/-- A trampoline call `.call f (.var 0)` on the input. -/
private theorem tmGLN_call0 {P : Program} {f : ℕ} {a : Val} {R : Val → Prop} {C : ℕ}
    (h : FunAll P f a (fun w c => R w ∧ c ≤ C)) :
    EvalAll P [a] (.call f (.var 0)) (fun w c => R w ∧ c ≤ a.wt + 2 * C + 2) :=
  EvalAll.call_funAll (Det.var' (P := P) (env := [a]) (i := 0) rfl) fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    exact (FunAll.wt_lt h).mono fun w c ⟨⟨hR, hc⟩, hw⟩ => ⟨hR, by omega⟩

private theorem tmGLN_s5_ar {W L X cc ct w C : ℕ} (hL : L < X) (hX : X < W)
    (hcc : cc ≤ 2 * W + 1 + 5 + (3 + 3) + X + 1 + loopModK * (L + 1) * (X + L + 4) + 3 + 1)
    (hct : ct ≤ W + 2 * C + 2) (hw : w < C) :
    cc + ct + w + 1 ≤ 4000 * (W + 1) ^ 2 + 4 * C + 100 := by
  have h1 : loopModK * (L + 1) * (X + L + 4) ≤ 1000 * (W + 1) * (3 * (W + 1)) := by
    unfold loopModK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have h2 : 1000 * (W + 1) * (3 * (W + 1)) = 3000 * (W + 1) ^ 2 := by ring
  have h3 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

set_option maxHeartbeats 1000000 in
/-- **The dispatch of step 5.** On the step-5 input, with the labels `xl` of `x`, the function
returns a result of the orientation variant when all types of `x` are distinct, and a result
of the plain step 5 otherwise. -/
theorem tmGLNS5_spec {P : Program} {f dist s5o s5p : ℕ}
    (hf : P.funs[f]? = some (tmGLNS5F dist s5o s5p)) (hd : P.HasAt dist (tmGLNDistFuns dist))
    {m : ℕ} (σS σN bs : List (Perm (Fin m))) (vs : List Val) (q : ℕ) (xl : List Val) (lc : Val)
    (gs : List (Perm (Fin m))) {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]
    {N : Subgroup (Perm (Fin n))} {X : Fin q → Ω} (hxl : TmGLPXOut N X (.list xl))
    {RO RP : Val → Prop} {CO CP : ℕ}
    (hO : (types N X).Nodup →
      FunAll P s5o (tmGLPStep5In σS σN bs vs q xl lc gs) (fun w c => RO w ∧ c ≤ CO))
    (hP : ¬ (types N X).Nodup →
      FunAll P s5p (tmGLPStep5In σS σN bs vs q xl lc gs) (fun w c => RP w ∧ c ≤ CP)) :
    FunAll P f (tmGLPStep5In σS σN bs vs q xl lc gs) (fun w c =>
      ((types N X).Nodup ∧ RO w ∨ ¬ (types N X).Nodup ∧ RP w) ∧
        c ≤ tmGLNS5C (tmGLPStep5In σS σN bs vs q xl lc gs).wt CO CP) := by
  set s0 : Val := .list [encGroup σS, encGroup σN, .list (bs.map encPerm)] with hs0
  set oc : Val := .list [encGroup σN, .list vs, .nat q, .list xl] with hoc
  set gl : Val := .list (gs.map encPerm) with hgl
  set a : Val := tmGLPStep5In σS σN bs vs q xl lc gs with ha
  set W := a.wt with hW
  have w1 : oc.wt < W := by
    have : oc.wt < (Val.list [s0, oc, lc, gl]).wt := wt_le_wt_list (by simp)
    exact this
  have wx : (Val.list xl).wt < oc.wt := wt_le_wt_list (by simp)
  have hlx := length_lt_wt_list xl
  have d1 : Det P [a] (arg 1) oc (2 * W + 1 + 5) := Det.arg' (vs := [s0, oc, lc, gl]) rfl
  have dx := Det.get' d1 (Det.nat 3) (vs := [encGroup σN, .list vs, .nat q, .list xl])
    (v := .list xl) (x := 3) rfl
  have dt := Det.call dx (tmGLNDist_types hd hxl)
  have hb := wt_boolVal_le (decide (types N X).Nodup)
  clear_value s0 oc gl
  apply FunAll.intro hf
  by_cases hT : (types N X).Nodup
  · have dt' : Det P [a] (.call dist (.get (arg 1) (.nat 3))) (.nat 1)
        (2 * W + 1 + 5 + (3 + 3) + (Val.list xl).wt + 1 +
          loopModK * (xl.length + 1) * ((Val.list xl).wt + xl.length + 4) + (Val.nat 1).wt + 1) := by
      rw [show decide (types N X).Nodup = true from decide_eq_true hT] at dt; exact dt
    have h' : FunAll P _ a (fun w c => (RO w ∧ w.wt < CO + CP) ∧ c ≤ CO + CP) :=
      FunAll.mono (FunAll.wt_lt (hO hT)) fun w c h => ⟨⟨h.1.1, by omega⟩, by omega⟩
    refine (tmGLN_ite_pos dt' one_ne_zero (tmGLN_call0 h')).mono fun w c h => ?_
    obtain ⟨ct, ⟨⟨hR, hw⟩, hct⟩, hc⟩ := h
    refine ⟨Or.inl ⟨hT, hR⟩, hc.trans ?_⟩
    unfold tmGLNS5C
    have := tmGLN_s5_ar (C := CO + CP) (L := xl.length) (X := (Val.list xl).wt) (W := W)
      (cc := 2 * W + 1 + 5 + (3 + 3) + (Val.list xl).wt + 1 +
        loopModK * (xl.length + 1) * ((Val.list xl).wt + xl.length + 4) + (Val.nat 1).wt + 1)
      (ct := ct) (w := w.wt) hlx (wx.trans w1) (by have := wt_nat_le 1; omega) (by omega)
      (by omega)
    omega
  · have dt' : Det P [a] (.call dist (.get (arg 1) (.nat 3))) (.nat 0)
        (2 * W + 1 + 5 + (3 + 3) + (Val.list xl).wt + 1 +
          loopModK * (xl.length + 1) * ((Val.list xl).wt + xl.length + 4) + (Val.nat 0).wt + 1) := by
      rw [show decide (types N X).Nodup = false from decide_eq_false hT] at dt; exact dt
    have h' : FunAll P _ a (fun w c => (RP w ∧ w.wt < CO + CP) ∧ c ≤ CO + CP) :=
      FunAll.mono (FunAll.wt_lt (hP hT)) fun w c h => ⟨⟨h.1.1, by omega⟩, by omega⟩
    refine (EvalAll.ite_zero' dt' (tmGLN_call0 h')).mono fun w c h => ?_
    obtain ⟨ct, ⟨⟨hR, hw⟩, hct⟩, hc⟩ := h
    refine ⟨Or.inr ⟨hT, hR⟩, hc.trans ?_⟩
    unfold tmGLNS5C
    have := tmGLN_s5_ar (C := CO + CP) (L := xl.length) (X := (Val.list xl).wt) (W := W)
      (cc := 2 * W + 1 + 5 + (3 + 3) + (Val.list xl).wt + 1 +
        loopModK * (xl.length + 1) * ((Val.list xl).wt + xl.length + 4) + (Val.nat 0).wt + 1)
      (ct := ct) (w := w.wt) hlx (wx.trans w1) (by have := wt_nat_le 0; omega) (by omega)
      (by omega)
    omega

/-! ### The results of the two variants in the form step 6 reads -/

section Adapt

variable {Ω C : Type} {Pp : Params} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}
  (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
  (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
  (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
    (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
  (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
  (hqα : (S.N : ℝ) ^ Pp.α < L.q)

local notation "𝕀" => tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα
set_option quotPrecheck false in
local notation "𝕩" => @id (Fin L.q → Fin m → C) (rowTuple (𝕀).e S.x)
set_option quotPrecheck false in
local notation "ℕb" => @id (Subgroup (Perm (Fin m))) (𝕀).Nb
set_option quotPrecheck false in
local notation "ℍb" => @id (Subgroup (Perm (Fin m))) (𝕀).Hb

/-- The kernel of `φ` is `N*`, read through its generators `σS`. -/
theorem tmGLN_ker {σS : List (Perm (Fin m))}
    (hσS : gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype) :
    ∀ g (hg : g ∈ (𝕀).Nb), (𝕀).φ ⟨g, hg⟩ = 1 ↔ g ∈ gens σS := fun g hg => by
  rw [hσS]; exact (𝕀).φ_ker ⟨g, hg⟩

/-- Two blockwise lifts of `h` differ by a zero-sum tuple (`tmGLP_lift_zero`), in the form of
the step-5 adapters. -/
theorem tmGLN_hyk : ∀ h ∈ (𝕀).Hb, ∀ y : Fin L.q → Perm (Fin m), cleanRowPerm E y ∈ S.domGroup →
    y ⟨0, by omega⟩ = h → ∃ ν, TmGLZero (𝕀).Nb (𝕀).φ ν ∧
      ∀ i, y i = rowLift (𝕀).e (𝕀).i0 h i * ν i :=
  fun _ hh _ hy hy0 => ⟨_, tmGLP_lift_zero (I := 𝕀) hh hy hy0⟩

/-- **Some type repeats: the plain step 5 gives `TmGLNS5Res`** (`tmGLP_step5_s5`). -/
theorem tmGLN_s5At_plain {σS σN bs gs : List (Perm (Fin m))} (hσN : gens σN = (𝕀).Nb)
    (hσS : gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype)
    (hbs : TmGLPBsOut (gens σN) (fun i => tmRowStr S E (.inl i)) bs)
    (hgs : gens gs ≤ Aut ℍb (types ℕb (𝕩))) (hT : ¬ (types ℕb (𝕩)).Nodup) {w : Val}
    (hw : TmGLPStep5Out E ⟨0, by omega⟩ σS σN bs (𝕩) gs w) :
    TmGLNS5Res hnat hq h0 E hP htr hcard hsN hN hqα σN gs w := by
  rw [hσN] at hbs
  obtain ⟨U, V, D, E', hpos, -, -, hE', ⟨ws, hws⟩, c0, c1, c2, hw5⟩ :=
    tmGLP_step5_s5 (𝕀).normalizes (tmGL_kerI 𝕀) (𝕀).Nb_le (tmGL_liftI 𝕀) E ⟨0, by omega⟩
      (𝕀).i0 (tmGLN_hyk hnat hq h0 E hP htr hcard hsN hN hqα) hσN
      (tmGLN_ker hnat hq h0 E hP htr hcard hsN hN hqα hσS) hbs hgs hw
  have e := hws.symm.trans hw5
  simp only [Val.list.injEq, List.cons.injEq] at e
  exact ⟨hgs, U, V, D, ws, hpos, Or.inl ⟨hT, hws, E', hE', e.2.1⟩⟩

/-- **All types distinct: the orientation variant gives `TmGLNS5Res`** (as
`tmGLP_step5O_s5`, keeping the context `[t, U, V, (2, d)]`). -/
theorem tmGLN_s5At_or {σS σN bs gs : List (Perm (Fin m))} (hσN : gens σN = (𝕀).Nb)
    (hσS : gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype)
    (hbs : TmGLPBsOut (gens σN) (fun i => tmRowStr S E (.inl i)) bs)
    (hgs : gens gs ≤ Aut ℍb (types ℕb (𝕩))) (hT : (types ℕb (𝕩)).Nodup) {w : Val}
    (hw : TmGLPStep5OOut σS σN bs (TmGLPGenOOut E ⟨0, by omega⟩ σN (𝕩)) gs w) :
    TmGLNS5Res hnat hq h0 E hP htr hcard hsN hN hqα σN gs w := by
  rw [hσN] at hbs
  obtain ⟨M, Z, U, V, D, ws, rfl, hMp, hZ, hV, hpos, hrel, hUV, hVU, hws⟩ := hw
  obtain ⟨E', hE'⟩ := tmGLP_set_E (x := 𝕩) (𝕀).φ hσN
    (tmGLN_ker hnat hq h0 E hP htr hcard hsN hN hqα hσS) hbs hMp hZ hV hpos hrel
  have hitems := tmGLP_items_eq (F := fun g => tmGLAffItem gs
      (Fin.cons 2 (tmGLQMod D) : Fin (σN.length + 1) → ℕ)
      (tmGLρE (tmGLPEoOf E') (tmGLlamO (𝕀).normalizes (tmGL_kerI 𝕀) hgs (𝕀).Nb_le))
      (tmGLcE (tmGLPEoOf E') (tmGLoO (tmGLPRep ℕb (𝕩) (𝕀).i0) (rowLift (𝕀).e (𝕀).i0))) g)
    (fun g hg w hgw => tmGLP_genO_item (𝕀).normalizes (tmGL_kerI 𝕀) (𝕀).Nb_le (tmGL_liftI 𝕀) E
      ⟨0, by omega⟩ (𝕀).i0 (tmGLN_hyk hnat hq h0 E hP htr hcard hsN hN hqα) hσN hpos hUV E' hE'
      hgs ⟨g, Subgroup.subset_closure hg⟩ hgw) hws
  refine ⟨hgs, U, V, D, ws, hpos, Or.inr ⟨hT, ?_, E', tmGLPEoOf E', hE', fun p => rfl, hitems⟩⟩
  rw [tmGLNOCtx, tmGLN_modV_cons hpos]

end Adapt

end GI.Impl
