import Workspace.Impl.TermGlueLabNTail
import Workspace.Impl.TermGlueLabST4

/-!
# The label driver: stages 5 to 8

Proof of Theorem A.23, the composition of the label driver `tmGLNeF`. After the
group values and the lift of `τ`, the driver computes the labels of `x` (from the `N`-test
table), the labels of `y'` (from the coset table and the lift `y`), the supplement `S` of step 4,
and the stabilizer generators `b_j`. `tmGLN_mid` checks the hypotheses of these four callees
and of the last three stages (`tmGLN_tail`):

* the test table is a `TmGLPTestOK` table of the rows of `x` (`tmGLP_testOK_of`);
* the lift `y` has all rows in `H` (`row_mem_Hb`), and `y'_i = y_i^{(y i)⁻¹}` gives back `y_i`
  under `y i`;
* step 4 is called on `N ≤ τ⟨U⟩τ⁻¹` with solvable quotient (`tmGLS_t4_gens`, Lemma A.21), and
  its output `S` gives `⟨gs⟩ ⊔ N = Aut_H(types) ⊓ R`, the hypothesis of step 5.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Lang GI.Paper Equiv
open GI.Cited (Val encPerm encGroup encIntMatrix gens GensOf)

attribute [local instance] stringRAct

/-- The cost of stages 5 to 11, for an environment of weight `W`. -/
def tmGLNMidC (F : ℕ → ℕ) : ℕ → ℕ :=
  tmGLNStC (tmGLNSz tmGLNA5) F (tmGLNStC (tmGLNSz tmGLNA6) F (tmGLNStC (tmGLNSz tmGLNA7) F
    (tmGLNStC (tmGLNSz tmGLNA8) F (tmGLNTailC F))))

theorem tmGLNMidC_mono {F : ℕ → ℕ} (hF : Monotone F) : Monotone (tmGLNMidC F) :=
  tmGLN_stC_mono _ hF (tmGLN_stC_mono _ hF (tmGLN_stC_mono _ hF
    (tmGLN_stC_mono _ hF (tmGLNTailC_mono hF))))

theorem tmGLNMidC_poly {F : ℕ → ℕ} (hF : TmGLNPoly F) : TmGLNPoly (tmGLNMidC F) :=
  tmGLN_stC_poly _ hF (tmGLN_stC_poly _ hF (tmGLN_stC_poly _ hF
    (tmGLN_stC_poly _ hF (tmGLNTailC_poly hF))))

section Mid

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}
  (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
  (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
  (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
    (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
  (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
  (hqα : (S.N : ℝ) ^ P₀.α < L.q)

local notation "𝕀" => tmGLSI P₀ hnat hq h0 E hP htr hcard hsN hN hqα

/-- **Stages 5 to 11 of the driver.** -/
theorem tmGLN_mid {P : Program} {xlab ylab sup bsb s5 vec s6 : ℕ}
    {F Fx Fy Fsup Fbs Fs5 Fvec Fs6 : ℕ → ℕ} (hF : Monotone F)
    (hxF : ∀ B, Fx B ≤ F B) (hyF : ∀ B, Fy B ≤ F B) (hsF : ∀ B, Fsup B ≤ F B)
    (hbF : ∀ B, Fbs B ≤ F B) (h5F : ∀ B, Fs5 B ≤ F B) (hvF : ∀ B, Fvec B ≤ F B)
    (h6F : ∀ B, Fs6 B ≤ F B)
    (hxo : Iface.TmGLNXOK P xlab Fx) (hyo : Iface.TmGLNYOK P ylab Fy)
    (hsupo : Iface.TmGLNSupOK P sup Fsup) (hbso : Iface.TmGLNBsOK P bsb Fbs)
    (hs5 : Iface.TmGLNS5OK P s5 Fs5) (hvec : Iface.TmGLNVecOK P vec Fvec)
    (hs6 : Iface.TmGLNS6OK P s6 Fs6)
    {k : ℕ} (e : Ω ≃ Fin k) {sv lv rl : Val} {lvr : List Val} (hlv0 : lv = .list (.nat L.q :: lvr))
    {σH σN σS U : List (Perm (Fin m))} {us vs : List Val}
    {ps' : List (Perm (Fin k) × Perm (Fin m))} {r τ : Perm (Fin m)} {y : Fin L.q → Perm (Fin m)}
    (hσN : gens σN = (𝕀).Nb)
    (hσS : gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype)
    (hus : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
      us (tmTests L.q))
    (hT : TmCsTabOK (𝕀).Hb (fun i => tmRowStr S E (.inl i)) (fun j => tmRowStr S E (.inr j)) vs)
    (hiso : ∀ j : Fin L.q, ∃ l : Fin L.q, (GI.Multicoset.Iso
      (@id (Subgroup (Perm (Fin m))) (𝕀).Hb)
      (tmRowStr S E (.inl j)) (tmRowStr S E (.inr l))).Nonempty)
    (hcl : Subgroup.closure {p | p ∈ ps'} =
      (tmGLPχ e E hnat (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).e_label ⟨0, by omega⟩).range)
    (hτ : τ ∈ tmGlRes 𝕀 r) (hy : cleanRowPerm E y ∈ S.domGroup) (hy0 : y ⟨0, by omega⟩ = τ)
    (hw : AnsC (Equiv.refl (Fin m)) (.list [encPerm τ, encGroup U]) (tmGlRes 𝕀 r))
    (hUl : U.length ≤ m ^ 2) :
    EvalAll P [.list [.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl], .list us,
        .list vs], encPerm r, .list [encPerm τ, encGroup U]],
      encGroup σN, encGroup σS, liftLabCtx k m ps',
      .list ((List.finRange L.q).map fun i => encPerm (y i))]
      (.letE (.call xlab tmGLNA5) (.letE (.call ylab tmGLNA6) (.letE (.call sup tmGLNA7)
        (.letE (.call bsb tmGLNA8) (.letE (.call s5 tmGLNA9) (.letE (.call vec tmGLNA10)
          (.call s6 tmGLNA11)))))))
      (fun u c => AnsC (Equiv.refl (Fin m)) u (tmGlLab 𝕀 r) ∧
        c ≤ tmGLNMidC F (Val.list [.list [.list [.list [sv, lv, coordsVal e S E,
          a18Out σH σN σS 0, rl], .list us, .list vs], encPerm r,
          .list [encPerm τ, encGroup U]], encGroup σN, encGroup σS, liftLabCtx k m ps',
          .list ((List.finRange L.q).map fun i => encPerm (y i))]).wt) := by
  have hmono := tmGLNTailC_mono hF
  have hTest := tmGLP_testOK_of S E σN hus
  have hlv := hlv0
  subst hlv
  -- the labels of `x`
  have h5 : tmGLNPev [.list [.list [.list [sv, .list (.nat L.q :: lvr), coordsVal e S E,
      a18Out σH σN σS 0, rl], .list us, .list vs], encPerm r, .list [encPerm τ, encGroup U]],
      encGroup σN, encGroup σS, liftLabCtx k m ps',
      .list ((List.finRange L.q).map fun i => encPerm (y i))] tmGLNA5 =
      some (.list [.list us, .nat L.q]) := rfl
  refine tmGLN_stage (tmGLN_stC_mono _ hF (tmGLN_stC_mono _ hF (tmGLN_stC_mono _ hF hmono))) h5
    ((hxo (gens σN) (fun i => tmRowStr S E (.inl i)) hTest _ (tmGLN_pev_wt h5)).mono
      fun u c ⟨hu, hc⟩ => ⟨hu, hc.trans (hxF _)⟩) ?_
  intro v5 hv5
  have hv5' := hv5
  obtain ⟨xl, rfl, -⟩ := hv5'
  -- the labels of `y'`
  have h6 : tmGLNPev ([.list [.list [.list [sv, .list (.nat L.q :: lvr), coordsVal e S E,
      a18Out σH σN σS 0, rl], .list us, .list vs], encPerm r, .list [encPerm τ, encGroup U]],
      encGroup σN, encGroup σS, liftLabCtx k m ps',
      .list ((List.finRange L.q).map fun i => encPerm (y i))] ++ [.list xl]) tmGLNA6 =
      some (tmGLPYIn σN vs y) := rfl
  have hle : gens σN ≤ (𝕀).Hb := hσN ▸ (𝕀).Nb_le
  have hnorm : GI.Multicoset.Normalizes (𝕀).Hb (gens σN) := hσN ▸ (𝕀).normalizes
  have hks : ∀ i, y i ∈ (𝕀).Hb := row_mem_Hb hnat hq E hP ⟨0, h0⟩ y hy
  have hZ : ∀ i, tmRowStr S E (.inr i) ↼ (y i)⁻¹ ↼ y i = tmRowStr S E (.inr i) :=
    fun i => act_inv_act _ _
  refine tmGLN_stage (tmGLN_stC_mono _ hF (tmGLN_stC_mono _ hF hmono)) h6
    ((hyo hle hnorm hT hks hZ _ (tmGLN_pev_wt h6)).mono
      fun u c ⟨hu, hc⟩ => ⟨hu, hc.trans (hyF _)⟩) ?_
  intro yl hyl
  -- step 4
  obtain ⟨ht4, hle4, hnorm4, hsol4⟩ :=
    tmGLS_t4_gens hnat hq h0 E hP htr hcard hsN hN hqα hσN hw
  haveI := hnorm4
  have h7 : tmGLNPev ([.list [.list [.list [sv, .list (.nat L.q :: lvr), coordsVal e S E,
      a18Out σH σN σS 0, rl], .list us, .list vs], encPerm r, .list [encPerm τ, encGroup U]],
      encGroup σN, encGroup σS, liftLabCtx k m ps',
      .list ((List.finRange L.q).map fun i => encPerm (y i))] ++ [.list xl] ++ [yl]) tmGLNA7 =
      some (.list [encGroup σN, .list [encPerm τ, encGroup U]]) := rfl
  refine tmGLN_stage (R := fun u => ∃ S' : Subgroup (Perm (Fin m)), GensOf S' u ∧
      S' ≤ gens (U.map fun x => τ * x * τ⁻¹) ∧ IsSolvable S' ∧
      S' ⊔ gens σN = gens (U.map fun x => τ * x * τ⁻¹))
    (tmGLN_stC_mono _ hF hmono) h7
    ((hsupo hUl τ hle4 hsol4 _ (tmGLN_pev_wt h7)).mono
      fun u c ⟨S', h1, h2, h3, h4, hc⟩ => ⟨⟨S', h1, h2, h3, h4⟩, hc.trans (hsF _)⟩) ?_
  intro v7 hv7
  obtain ⟨S', ⟨gs, rfl, hgsl, hgsS⟩, -, hsolS, hjoin⟩ := hv7
  have hgl6 : gens gs ⊔ gens σN = gens (U.map fun x => τ * x * τ⁻¹) := by rw [hgsS]; exact hjoin
  have hsol : IsSolvable (gens gs) := by rw [hgsS]; exact hsolS
  -- the stabilizer generators
  have h8 : tmGLNPev ([.list [.list [.list [sv, .list (.nat L.q :: lvr), coordsVal e S E,
      a18Out σH σN σS 0, rl], .list us, .list vs], encPerm r, .list [encPerm τ, encGroup U]],
      encGroup σN, encGroup σS, liftLabCtx k m ps',
      .list ((List.finRange L.q).map fun i => encPerm (y i))] ++ [.list xl] ++ [yl] ++
      [.list (gs.map encPerm)]) tmGLNA8 = some (.list [.list us, .nat L.q]) := rfl
  refine tmGLN_stage (R := fun u => ∃ bs : List (Perm (Fin m)), u = .list (bs.map encPerm) ∧
      TmGLPBsOut (gens σN) (fun i => tmRowStr S E (.inl i)) bs) hmono h8
    ((hbso (gens σN) (fun i => tmRowStr S E (.inl i)) hTest _ (tmGLN_pev_wt h8)).mono
      fun u c ⟨bs, h1, h2, hc⟩ => ⟨⟨bs, h1, h2⟩, hc.trans (hbF _)⟩) ?_
  intro v8 hv8
  obtain ⟨bs, rfl, hbs⟩ := hv8
  have hgl : gens gs ⊔ gens σN = Aut (@id (Subgroup (Perm (Fin m))) (𝕀).Hb)
      (types (@id (Subgroup (Perm (Fin m))) (𝕀).Nb) (@id (Fin L.q → Fin m → C)
        (rowTuple (𝕀).e S.x))) ⊓ tmRad 𝕀 := hgl6.trans ht4
  exact tmGLN_tail hnat hq h0 E hP htr hcard hsN hN hqα hF h5F hvF h6F hs5 hvec hs6 e rfl hσN
    hσS hbs hT hiso hv5 hcl hgsl hgl hτ hy hy0 hyl hw hgl6 hsol

end Mid

end GI.Impl
