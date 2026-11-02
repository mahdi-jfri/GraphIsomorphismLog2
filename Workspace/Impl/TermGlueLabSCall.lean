import Workspace.Impl.TermGlueLabS6
import Workspace.Impl.TermGlueLabPCall

/-!
# The affine call of step 6 at the row terminal, and the label answer

Proof of Theorem A.23: "The finite abelian affine transporter procedure in the
proof of Theorem A.20 now imposes both labels in polynomial time within this radical coset.
With the possible orientation factor included, the characteristic bound is `p ≤ max{b, 2}`."

* `tmGLS_call` (every type distinct, orientation coordinate) and `tmGLS_call'` (some type
  repeats) are `tmGLP_aff_call(')` at the row terminal `I` of the label step, with the lifts
  `rowLift` of Theorem A.18, `v = E(p_{y'})` and `w = E(p_x)`. Their transporter set is
  `tmGLSTrans I rep τ ⟨gs⟩`. The four preconditions of `Iface.TmGLAffineSpec` are checked inside
  `tmGLP_aff_call(')`: solvability is the hypothesis `hsol` (T4 output), positive moduli `hm`,
  the prime bound by `tmGL_prime_le(')`, and the cocycle identity by `tmGLρE_cocycle` with
  `tmGLoO_cocycle` / `tmGLo_cocycle`. The generator bound `gs.length ≤ n²` is passed.
* `tmGLS6_lab`: step 6 returns a canonical answer of the label coset `tmGlLab I r`, from
  `tmGLS6_spec` and `tmGLS_lab_ans`.
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Lang Equiv
open GI.Cited (Val encPerm encGroup gens PointwiseStab)
open scoped Pointwise

variable {Ω C : Type}

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}
  (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
  (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
  (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
    (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
  (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
  (hqα : (S.N : ℝ) ^ P.α < L.q)

local notation "𝕀" => tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα
set_option quotPrecheck false in
local notation "𝕩" => @id (Fin L.q → Fin m → C) (rowTuple (𝕀).e S.x)
set_option quotPrecheck false in
local notation "ℕb" => @id (Subgroup (Perm (Fin m))) (𝕀).Nb
set_option quotPrecheck false in
local notation "ℍb" => @id (Subgroup (Perm (Fin m))) (𝕀).Hb

/-- **The affine call, every type distinct** (with the orientation coordinate). -/
theorem tmGLS_call {Pg : Program} {Ka Da ja : ℕ} (hA : Iface.TmGLAffineSpec Pg Ka Da ja)
    {gs : List (Perm (Fin m))}
    (hgs : gens gs ≤ Aut ℍb (types ℕb 𝕩))
    (hsol : IsSolvable (gens gs)) (hgl : gs.length ≤ m ^ 2)
    {d : ℕ} {md : Fin d → ℕ} (hm : ∀ i, 0 < md i)
    (Ev : Additive (tmGLV ℕb (𝕀).φ 𝕩 × ℤˣ) ≃+ tmGLVec md)
    {rep : Set (Fin m → C) → (Fin m → C)}
    (hrep : TmGLRep ℕb 𝕩 rep) (τ : Perm (Fin m)) :
    FunAll Pg ja (tmGLAffIn gs md (tmGLρE Ev (tmGLlamO ((𝕀).normalizes : GI.Multicoset.Normalizes ℍb ℕb) (tmGL_kerI 𝕀) hgs (𝕀).Nb_le))
        (tmGLcE Ev (tmGLoO rep (rowLift (𝕀).e (𝕀).i0)))
        (Ev (Additive.ofMul (tmGLPt ℕb (𝕀).φ 𝕩 rep ((@id (Fin L.q → Fin m → C) (tmGLAlign 𝕀 τ))))))
        (Ev (Additive.ofMul (tmGLPt ℕb (𝕀).φ 𝕩 rep 𝕩))))
      (fun u c => TmGLAffOut m u (tmGLSTrans 𝕀 rep τ (gens gs)) ∧
        c ≤ Ka * ((tmGLAffIn gs md (tmGLρE Ev (tmGLlamO ((𝕀).normalizes : GI.Multicoset.Normalizes ℍb ℕb) (tmGL_kerI 𝕀) hgs (𝕀).Nb_le))
          (tmGLcE Ev (tmGLoO rep (rowLift (𝕀).e (𝕀).i0)))
          (Ev (Additive.ofMul (tmGLPt ℕb (𝕀).φ 𝕩 rep ((@id (Fin L.q → Fin m → C) (tmGLAlign 𝕀 τ))))))
          (Ev (Additive.ofMul (tmGLPt ℕb (𝕀).φ 𝕩 rep
            𝕩)))).wt + 1) ^ Da) :=
  tmGLP_aff_call hA ((𝕀).normalizes : GI.Multicoset.Normalizes ℍb ℕb) (tmGL_kerI 𝕀) (𝕀).Nb_le hgs hsol hgl hm Ev (tmGL_liftI 𝕀)
    hrep _ _

/-- **The affine call, some type repeats** (no orientation coordinate: the orientation is `1`). -/
theorem tmGLS_call' {Pg : Program} {Ka Da ja : ℕ} (hA : Iface.TmGLAffineSpec Pg Ka Da ja)
    {gs : List (Perm (Fin m))}
    (hgs : gens gs ≤ Aut ℍb (types ℕb 𝕩))
    (hsol : IsSolvable (gens gs)) (hgl : gs.length ≤ m ^ 2)
    (hT : ¬ (types ℕb 𝕩).Nodup)
    {d : ℕ} {md : Fin d → ℕ} (hm : ∀ i, 0 < md i)
    (Ev : Additive (tmGLV ℕb (𝕀).φ 𝕩) ≃+ tmGLVec md)
    {rep : Set (Fin m → C) → (Fin m → C)}
    (hrep : TmGLRep ℕb 𝕩 rep) (τ : Perm (Fin m)) :
    FunAll Pg ja (tmGLAffIn gs md (tmGLρE Ev (tmGLlam ((𝕀).normalizes : GI.Multicoset.Normalizes ℍb ℕb) (tmGL_kerI 𝕀) hgs (𝕀).Nb_le))
        (tmGLcE Ev (tmGLo rep (rowLift (𝕀).e (𝕀).i0)))
        (Ev (Additive.ofMul (tmGLLab ℕb (𝕀).φ 𝕩 rep ((@id (Fin L.q → Fin m → C) (tmGLAlign 𝕀 τ))))))
        (Ev (Additive.ofMul (tmGLLab ℕb (𝕀).φ 𝕩 rep 𝕩))))
      (fun u c => TmGLAffOut m u (tmGLSTrans 𝕀 rep τ (gens gs)) ∧
        c ≤ Ka * ((tmGLAffIn gs md (tmGLρE Ev (tmGLlam ((𝕀).normalizes : GI.Multicoset.Normalizes ℍb ℕb) (tmGL_kerI 𝕀) hgs (𝕀).Nb_le))
          (tmGLcE Ev (tmGLo rep (rowLift (𝕀).e (𝕀).i0)))
          (Ev (Additive.ofMul (tmGLLab ℕb (𝕀).φ 𝕩 rep ((@id (Fin L.q → Fin m → C) (tmGLAlign 𝕀 τ))))))
          (Ev (Additive.ofMul (tmGLLab ℕb (𝕀).φ 𝕩 rep
            𝕩)))).wt + 1) ^ Da) := by
  have h := tmGLP_aff_call' hA ((𝕀).normalizes : GI.Multicoset.Normalizes ℍb ℕb) (tmGL_kerI 𝕀) (𝕀).Nb_le hgs hsol hgl hT hm Ev
    (tmGL_liftI 𝕀) hrep (tmGLLab ℕb (𝕀).φ 𝕩 rep 𝕩)
    (tmGLLab ℕb (𝕀).φ 𝕩 rep ((@id (Fin L.q → Fin m → C) (tmGLAlign 𝕀 τ))))
  -- both label points have orientation `1`
  refine h.mono fun u c hu => ⟨?_, hu.2⟩
  have e1 : tmGLOr (𝕀).Nb (rowTuple (𝕀).e S.x) (rowTuple (𝕀).e S.x) = 1 :=
    tmGLOr_of_not_nodup hT _
  have e2 : tmGLOr (𝕀).Nb (rowTuple (𝕀).e S.x) (tmGLAlign 𝕀 τ) = 1 :=
    tmGLOr_of_not_nodup hT _
  unfold tmGLSTrans tmGLPt
  rw [e1, e2]
  exact hu.1

/-- **The supplement lies in `D`.** A subgroup of `τ ⟨U⟩ τ⁻¹ = D ∩ R` lies in `D` (this is the
hypothesis `hgs` of the call lemmas). -/
theorem tmGLS_supp_D {σN U gs : List (Perm (Fin m))} (hσN : gens σN = (𝕀).Nb) {r τ : Perm (Fin m)}
    (hw : AnsC (Equiv.refl (Fin m)) (.list [encPerm τ, encGroup U]) (tmGlRes 𝕀 r))
    (hSR : gens gs ≤ gens (U.map fun x => τ * x * τ⁻¹)) :
    gens gs ≤ Aut (𝕀).Hb (types (𝕀).Nb (rowTuple (𝕀).e S.x)) := by
  have h := (tmGLS_t4_gens hnat hq h0 E hP htr hcard hsN hN hqα hσN hw).1
  rw [h] at hSR
  exact hSR.trans inf_le_left

/-- **Step 6 returns the label coset.** With the residual answer `[τ, U]`, the T4 output
`gs` (`gens gs ⊔ N = τ ⟨U⟩ τ⁻¹`, at most `m²` generators), step 5 at `s5` and the affine call
at `ja` with the label transporter set (`tmGLS_call` or `tmGLS_call'`), the program
`tmGLS6F` returns a canonical answer of `tmGlLab I r`. -/
theorem tmGLS6_lab (hps : PointwiseStab) {Pg : Program}
    {f mg s5 ja out red app jp inv cp cj mc Ka Da : ℕ}
    (hf : Pg.funs[f]? = some (tmGLS6F mg s5 ja out))
    (hmg : Pg.HasAt mg (mkGroupFuns mg))
    (hout : Pg.funs[out]? = some (tmGLSOutF red inv cp mc))
    (hred : Pg.funs[red]? = some (tmGLSRedF app mg jp)) (happ : Pg.HasAt app (appendFuns app))
    (hj : Pg.prims[jp]? = some (pointwiseStabPrim hps))
    (hinv : Pg.HasAt inv (invFuns inv)) (hcp : Pg.HasAt cp (composeFuns cp))
    (hcj : Pg.funs[cj]? = some (supConjF cp)) (hmc : Pg.HasAt mc (mapFuns mc cj))
    {σN U gs : List (Perm (Fin m))} (hσN : gens σN = (𝕀).Nb) {r τ : Perm (Fin m)}
    (hw : AnsC (Equiv.refl (Fin m)) (.list [encPerm τ, encGroup U]) (tmGlRes 𝕀 r))
    (hSN : gens gs ⊔ gens σN = gens (U.map fun x => τ * x * τ⁻¹)) (hgl : gs.length ≤ m ^ 2)
    {rep : Set (Fin m → C) → (Fin m → C)}
    (hrep : TmGLRep (𝕀).Nb (rowTuple (𝕀).e S.x) rep)
    (in5 vv ww modV : Val) (items : List Val) (C5 : ℕ)
    (h5 : FunAll Pg s5 in5 (fun w c => TmGLS5Out modV items w ∧ c ≤ C5))
    (hcall : FunAll Pg ja (.list [encGroup gs, modV, .list items, vv, ww]) (fun u c =>
      TmGLAffOut m u (tmGLSTrans 𝕀 rep τ (gens gs)) ∧
        c ≤ Ka * ((Val.list [encGroup gs, modV, .list items, vv, ww]).wt + 1) ^ Da)) :
    FunAll Pg f (.list [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww]) (fun w c =>
      AnsC (Equiv.refl (Fin m)) w (tmGlLab 𝕀 r) ∧
        c ≤ tmGLS6C Ka Da (pointwiseStabPrim hps).c (pointwiseStabPrim hps).k C5
          (Val.list [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww]).wt) := by
  have hres : tmGlRes 𝕀 r = τ • ((gens U : Subgroup (Perm (Fin m))) : Set (Perm (Fin m))) :=
    tmCs_ansC_cons hw rfl
  have hτ : τ ∈ tmGlRes 𝕀 r := by
    rw [hres]; exact ⟨1, (gens U).one_mem, mul_one τ⟩
  have hR := (tmGLS_t4_gens hnat hq h0 E hP htr hcard hsN hN hqα hσN hw).1
  have hSN' : gens gs ⊔ (𝕀).Nb = Aut (𝕀).Hb (types (𝕀).Nb (rowTuple (𝕀).e S.x)) ⊓ tmRad 𝕀 := by
    rw [show gens gs ⊔ (𝕀).Nb = gens gs ⊔ gens σN by rw [hσN], hSN, hR]
  refine (tmGLS6_spec hps hf hmg hout hred happ hj hinv hcp hcj hmc σN gs hgl τ in5 vv ww modV
    items C5 h5 hcall).mono fun w c ⟨u, hu, hwr, hc⟩ => ⟨?_, hc⟩
  exact tmGLS_lab_ans hnat hq h0 E hP htr hcard hsN hN hqα hσN hτ hSN' hrep hu hwr

end GI.Impl
