module

public import Workspace.Impl.TermGlueLabNPev
public import Workspace.Impl.TermGlueLabNIn
public import Workspace.Impl.TermGlueLabN6

@[expose] public section

/-!
# The label driver: the last three stages

Proof of Theorem A.23, the composition of the label driver `tmGLNeF`. After the
first eight stages the environment holds the input, `gens N`, `gens N*`, the lift context, the
lift `y` of `τ`, the labels of `x` and of `y'`, the generators of the supplement `S` and the
`b_j`. The last three stages run step 5, the vector wrapper and step 6. `tmGLN_tail` proves
that they return a canonical answer of the label coset, from the contracts `TmGLNS5OK`,
`TmGLNVecOK`, `TmGLNS6OK` of the three callees.

The step-5 result fixes `U`, `V`, `D` (step 5 is not deterministic). The vector wrapper and
step 6 are then called with this one choice, which is why their contracts take `U V D` as data.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Lang GI.Paper Equiv
open GI.Cited (Val encPerm encGroup encIntMatrix gens GensOf)

attribute [local instance] stringRAct

/-! ### The arguments of the driver -/

/-- The argument of the first `mkGroup` call: `[m, gens N]`. -/
def tmGLNA1 : Expr := mk2 tmGLNM (.get tmGLNA18 (.nat 1))
/-- The argument of the second `mkGroup` call: `[m, gens N*]`. -/
def tmGLNA2 : Expr := mk2 tmGLNM (.get tmGLNA18 (.nat 2))
/-- The argument of the lift context. -/
def tmGLNA3 : Expr := mk3 (mk2 (.get (.get tmGLNV0 (.nat 0)) (.nat 0)) tmGLNQ)
  (.get tmGLNLv (.nat 1)) (.get tmGLNCo (.nat 0))
/-- The argument of the lift of `τ`. -/
def tmGLNA4 : Expr := mk2 (mk2 (.var 3) tmGLNCo) tmGLNTau
/-- The argument of the labels of `x`. -/
def tmGLNA5 : Expr := mk2 (.get (arg 0) (.nat 1)) tmGLNQ
/-- The argument of the labels of `y'`. -/
def tmGLNA6 : Expr := mk4 (.var 1) (.get (arg 0) (.nat 2)) tmGLNQ (.var 4)
/-- The argument of step 4. -/
def tmGLNA7 : Expr := mk2 (.var 1) (arg 2)
/-- The argument of the stabilizer generators. -/
def tmGLNA8 : Expr := mk2 (.get (arg 0) (.nat 1)) tmGLNQ
/-- The argument of step 5. -/
def tmGLNA9 : Expr := mk4 (mk3 (.var 2) (.var 1) (.var 8))
  (mk4 (.var 1) (.get (arg 0) (.nat 2)) tmGLNQ (.var 5)) (mk2 (.var 3) tmGLNCo) (.var 7)
/-- The argument of the vector wrapper. -/
def tmGLNA10 : Expr := mk4 (.var 9) (.var 1) (.var 5) (.var 6)
/-- The argument of step 6. -/
def tmGLNA11 : Expr := Expr.mkList [.var 1, tmGLNTau, .var 7, .var 9, .get (.var 10) (.nat 0),
  .get (.var 10) (.nat 1)]

theorem tmGLNeF_eq (mg lc xlab ylab sup bsb s5 vec s6 : ℕ) :
    tmGLNeF mg lc xlab ylab sup bsb s5 vec s6 =
      .letE (.call mg tmGLNA1) (.letE (.call mg tmGLNA2) (.letE (.call lc tmGLNA3)
      (.letE (.call (lc + 1) tmGLNA4) (.letE (.call xlab tmGLNA5) (.letE (.call ylab tmGLNA6)
      (.letE (.call sup tmGLNA7) (.letE (.call bsb tmGLNA8) (.letE (.call s5 tmGLNA9)
      (.letE (.call vec tmGLNA10) (.call s6 tmGLNA11)))))))))) := rfl

/-- The cost of the last three stages, for an environment of weight `W`. -/
def tmGLNTailC (F : ℕ → ℕ) : ℕ → ℕ :=
  tmGLNStC (tmGLNSz tmGLNA9) F (tmGLNStC (tmGLNSz tmGLNA10) F (tmGLNLastC (tmGLNSz tmGLNA11) F))

theorem tmGLNTailC_mono {F : ℕ → ℕ} (hF : Monotone F) : Monotone (tmGLNTailC F) :=
  tmGLN_stC_mono _ hF (tmGLN_stC_mono _ hF (tmGLN_lastC_mono _ hF))

theorem tmGLNTailC_poly {F : ℕ → ℕ} (hF : TmGLNPoly F) : TmGLNPoly (tmGLNTailC F) :=
  tmGLN_stC_poly _ hF (tmGLN_stC_poly _ hF (tmGLN_lastC_poly _ hF))

section Tail

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}
  (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
  (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
  (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
    (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
  (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
  (hqα : (S.N : ℝ) ^ P₀.α < L.q)

local notation "𝕀" => tmGLSI P₀ hnat hq h0 E hP htr hcard hsN hN hqα

/-- **The last three stages of the driver**: step 5, the vectors and step 6. -/
theorem tmGLN_tail {P : Program} {s5 vec s6 : ℕ} {F Fs5 Fvec Fs6 : ℕ → ℕ} (hF : Monotone F)
    (h5F : ∀ B, Fs5 B ≤ F B) (hvF : ∀ B, Fvec B ≤ F B) (h6F : ∀ B, Fs6 B ≤ F B)
    (hs5 : Iface.TmGLNS5OK P s5 Fs5) (hvec : Iface.TmGLNVecOK P vec Fvec)
    (hs6 : Iface.TmGLNS6OK P s6 Fs6)
    {R' : Subgroup (Perm (Fin m))}
    (hRH : R' ≤ (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb)
    (hNR : (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb ≤ R')
    (hsolv : ∃ ℓ, GI.Multicoset.relDerived R' (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb ℓ ≤
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb)
    {k : ℕ} (e : Ω ≃ Fin k) {sv lv rl : Val} {lvr : List Val} (hlv0 : lv = .list (.nat L.q :: lvr))
    {σH σN σS bs gs U : List (Perm (Fin m))} {us vs xl : List Val} {yl : Val}
    {ps' : List (Perm (Fin k) × Perm (Fin m))} {r τ : Perm (Fin m)} {y : Fin L.q → Perm (Fin m)}
    (hσN : gens σN = (𝕀).Nb)
    (hσS : gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype)
    (hbs : TmGLPBsOut (gens σN) (fun i => tmRowStr S E (.inl i)) bs)
    (hT : TmCsTabOK (𝕀).Hb (fun i => tmRowStr S E (.inl i)) (fun j => tmRowStr S E (.inr j)) vs)
    (hiso : ∀ j : Fin L.q, ∃ l : Fin L.q, (GI.Multicoset.Iso
      (@id (Subgroup (Perm (Fin m))) (𝕀).Hb)
      (tmRowStr S E (.inl j)) (tmRowStr S E (.inr l))).Nonempty)
    (hxl : TmGLPXOut (gens σN) (fun i => tmRowStr S E (.inl i)) (.list xl))
    (hcl : Subgroup.closure {p | p ∈ ps'} =
      (tmGLPχ e E hnat (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).e_label ⟨0, by omega⟩).range)
    (hgsl : gs.length ≤ m ^ 2)
    (hgl : gens gs ≤ Aut (@id (Subgroup (Perm (Fin m))) (𝕀).Hb)
      (types (@id (Subgroup (Perm (Fin m))) (𝕀).Nb) (@id (Fin L.q → Fin m → C)
        (rowTuple (𝕀).e S.x))))
    (hτ : τ ∈ tmGlRes (tmGLSIWith P₀ hnat hq h0 E hP htr hcard hsN hN hqα R' hRH hNR hsolv) r)
    (hy : cleanRowPerm E y ∈ S.domGroup) (hy0 : y ⟨0, by omega⟩ = τ)
    (hyl : TmGLPYOut (gens σN) (fun i => tmRowStr S E (.inl i))
      (fun i => tmRowStr S E (.inr i) ↼ (y i)⁻¹) yl)
    (hw : AnsC (Equiv.refl (Fin m)) (.list [encPerm τ, encGroup U])
      (tmGlRes (tmGLSIWith P₀ hnat hq h0 E hP htr hcard hsN hN hqα R' hRH hNR hsolv) r))
    (hgl6 : gens gs ⊔ gens σN = gens (U.map fun x => τ * x * τ⁻¹))
    (hsol : ∃ _ : ((gens σN).subgroupOf (gens gs)).Normal,
      Group.IsSolvable ((gens gs) ⧸ (gens σN).subgroupOf (gens gs))) :
    EvalAll P [.list [.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl], .list us,
        .list vs], encPerm r, .list [encPerm τ, encGroup U]],
      encGroup σN, encGroup σS, liftLabCtx k m ps',
      .list ((List.finRange L.q).map fun i => encPerm (y i)), .list xl, yl,
      .list (gs.map encPerm), .list (bs.map encPerm)]
      (.letE (.call s5 tmGLNA9) (.letE (.call vec tmGLNA10) (.call s6 tmGLNA11)))
      (fun u c => AnsC (Equiv.refl (Fin m)) u
        (tmGlLab (tmGLSIWith P₀ hnat hq h0 E hP htr hcard hsN hN hqα R' hRH hNR hsolv) r) ∧
        c ≤ tmGLNTailC F (Val.list [.list [.list [.list [sv, lv, coordsVal e S E,
          a18Out σH σN σS 0, rl], .list us, .list vs], encPerm r,
          .list [encPerm τ, encGroup U]], encGroup σN, encGroup σS, liftLabCtx k m ps',
          .list ((List.finRange L.q).map fun i => encPerm (y i)), .list xl, yl,
          .list (gs.map encPerm), .list (bs.map encPerm)]).wt) := by
  subst hlv0
  -- step 5
  have h9 : tmGLNPev [.list [.list [.list [sv, .list (.nat L.q :: lvr), coordsVal e S E,
      a18Out σH σN σS 0, rl], .list us, .list vs], encPerm r, .list [encPerm τ, encGroup U]],
      encGroup σN, encGroup σS, liftLabCtx k m ps',
      .list ((List.finRange L.q).map fun i => encPerm (y i)), .list xl, yl,
      .list (gs.map encPerm), .list (bs.map encPerm)] tmGLNA9 =
      some (tmGLPStep5In σS σN bs vs L.q xl (.list [liftLabCtx k m ps', coordsVal e S E]) gs) :=
    rfl
  refine tmGLN_stage (tmGLN_stC_mono _ hF (tmGLN_lastC_mono _ hF)) h9
    ((hs5 hnat hq h0 E hP htr hcard hsN hN hqα e σS σN bs gs vs xl ps' hσN hσS hbs hT hiso hxl
      hcl hgsl hgl _ (tmGLN_pev_wt h9)).mono fun o c ⟨ho, hc⟩ => ⟨ho, hc.trans (h5F _)⟩) ?_
  intro o5 ho5
  obtain ⟨hgs, U5, V, D, ws, hAt⟩ := ho5
  -- the vectors
  have hτ0 : τ ∈ tmGlRes 𝕀 τ := ⟨hτ.1, 1, (tmRad 𝕀).one_mem, (one_mul τ).symm⟩
  have h10 : tmGLNPev ([.list [.list [.list [sv, .list (.nat L.q :: lvr), coordsVal e S E,
      a18Out σH σN σS 0, rl], .list us, .list vs], encPerm r, .list [encPerm τ, encGroup U]],
      encGroup σN, encGroup σS, liftLabCtx k m ps',
      .list ((List.finRange L.q).map fun i => encPerm (y i)), .list xl, yl,
      .list (gs.map encPerm), .list (bs.map encPerm)] ++ [o5]) tmGLNA10 =
      some (.list [o5, encGroup σN, .list xl, yl]) := rfl
  refine tmGLN_stage (R := fun u => ∃ vv ww : Val, u = .list [vv, ww] ∧
      TmGLNVecRes hnat hq h0 E hP htr hcard hsN hN hqα σN τ V D vv ww)
    (tmGLN_lastC_mono _ hF) h10
    ((hvec hnat hq h0 E hP htr hcard hsN hN hqα σN gs τ τ y U5 V D o5 (.list xl) yl hσN hτ0 hy hy0
      ⟨hgs, ws, hAt⟩ hxl hyl _ (tmGLN_pev_wt h10)).mono fun u c ⟨vv, ww, hu, hr, hc⟩ =>
        ⟨⟨vv, ww, hu, hr⟩, hc.trans (hvF _)⟩) ?_
  intro u10 hu10
  obtain ⟨vv, ww, rfl, hvr⟩ := hu10
  -- step 6
  have h11 : tmGLNPev ([.list [.list [.list [sv, .list (.nat L.q :: lvr), coordsVal e S E,
      a18Out σH σN σS 0, rl], .list us, .list vs], encPerm r, .list [encPerm τ, encGroup U]],
      encGroup σN, encGroup σS, liftLabCtx k m ps',
      .list ((List.finRange L.q).map fun i => encPerm (y i)), .list xl, yl,
      .list (gs.map encPerm), .list (bs.map encPerm)] ++ [o5] ++ [.list [vv, ww]]) tmGLNA11 =
      some (.list [encGroup σN, encPerm τ, .list (gs.map encPerm), o5, vv, ww]) := rfl
  exact tmGLN_last h11
    ((hs6 hnat hq h0 E hP htr hcard hsN hN hqα hRH hNR hsolv hσN hw hgl6 hsol hgsl U5 V D o5 vv ww
      ⟨hgs, ws, hAt⟩ hvr _ (tmGLN_pev_wt h11)).mono fun u c ⟨hu, hc⟩ => ⟨hu, hc.trans (h6F _)⟩)

end Tail

end GI.Impl
