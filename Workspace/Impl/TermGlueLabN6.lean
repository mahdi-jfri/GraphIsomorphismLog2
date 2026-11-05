module

public import Workspace.Impl.TermGlueLabNProg
public import Workspace.Impl.TermGlueLabPS5Ad

@[expose] public section

/-!
# The driver of the label program: step 6 on the precomputed step-5 output

Proof of Theorem A.23: "The finite abelian affine transporter procedure in the
proof of Theorem A.20 now imposes both labels in polynomial time within this radical coset."

The driver runs step 5 itself and passes its output `o5` to step 6 (`tmGLS6F mg idx ja out`),
whose step-5 index `idx` holds the trampoline `tmGLNIdF`. `tmGLN_s6_ok` proves the contract
`Iface.TmGLNS6OK` of this step 6 from `tmGLS6_lab`: the trampoline gives the
hypothesis `h5` of `tmGLS6_lab` with `o5` itself, and the affine call `hcall` is `tmGLS_call'`
(some type repeats) or `tmGLS_call` (all types distinct) with the coordinates `Ev` of
`TmGLNS5Res` and the vectors of `TmGLNVecRes`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Lang GI.Paper Equiv
open GI.Cited (Val encPerm encGroup encIntMatrix gens GensOf PointwiseStab)
open scoped Pointwise

attribute [local instance] stringRAct

namespace Iface

/-- **Step 6** at `s6`, on `[gens N, τ, gens S, step 5, E(p_{y'}), E(p_x)]`. -/
def TmGLNS6OK (P : Program) (s6 : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ {Ω C : Type} {Pp : Params} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}
    (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
    (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
    (hqα : (S.N : ℝ) ^ Pp.α < L.q)
    {R' : Subgroup (Perm (Fin m))}
    (hRH : R' ≤ (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb)
    (hNR : (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb ≤ R')
    (hsolv : ∃ ℓ, GI.Multicoset.relDerived R' (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb ℓ ≤
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb)
    {σN U gs : List (Perm (Fin m))} {r τ : Perm (Fin m)},
    gens σN = (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Nb →
    AnsC (Equiv.refl (Fin m)) (.list [encPerm τ, encGroup U])
      (tmGlRes (tmGLSIWith Pp hnat hq h0 E hP htr hcard hsN hN hqα R' hRH hNR hsolv) r) →
    gens gs ⊔ gens σN = gens (U.map fun x => τ * x * τ⁻¹) →
    (∃ _ : ((gens σN).subgroupOf (gens gs)).Normal,
      Group.IsSolvable ((gens gs) ⧸ (gens σN).subgroupOf (gens gs))) →
    gs.length ≤ m ^ 2 → ∀ (U5 V D : Matrix (Fin σN.length) (Fin σN.length) ℤ) (o5 vv ww : Val),
    (∃ hgs ws, TmGLNS5At hnat hq h0 E hP htr hcard hsN hN hqα σN gs hgs U5 V D ws o5) →
    TmGLNVecRes hnat hq h0 E hP htr hcard hsN hN hqα σN τ V D vv ww →
    ∀ B : ℕ, (Val.list [encGroup σN, encPerm τ, .list (gs.map encPerm), o5, vv, ww]).wt ≤ B →
    FunAll P s6 (.list [encGroup σN, encPerm τ, .list (gs.map encPerm), o5, vv, ww])
      (fun w c => AnsC (Equiv.refl (Fin m)) w
        (tmGlLab (tmGLSIWith Pp hnat hq h0 E hP htr hcard hsN hN hqα R' hRH hNR hsolv) r) ∧ c ≤ F B)

end Iface

theorem tmGLS6A_mono {C W C' W' : ℕ} (hC : C ≤ C') (hW : W ≤ W') :
    tmGLS6A C W ≤ tmGLS6A C' W' := by
  unfold tmGLS6A; gcongr

theorem tmGLS6KA_mono (Ka Da : ℕ) {C W C' W' : ℕ} (hC : C ≤ C') (hW : W ≤ W') :
    tmGLS6KA Ka Da C W ≤ tmGLS6KA Ka Da C' W' := by
  unfold tmGLS6KA
  have := tmGLS6A_mono hC hW
  gcongr

theorem tmGLS6C_mono (Ka Da c k : ℕ) {C W C' W' : ℕ} (hC : C ≤ C') (hW : W ≤ W') :
    tmGLS6C Ka Da c k C W ≤ tmGLS6C Ka Da c k C' W' := by
  unfold tmGLS6C
  have h1 := tmGLS6A_mono hC hW
  have h2 := tmGLS6KA_mono Ka Da hC hW
  have h3 := tmGLSOutC_mono c k (show 4 * W + 2 * tmGLS6KA Ka Da C W + 10 ≤
    4 * W' + 2 * tmGLS6KA Ka Da C' W' + 10 by omega)
  have h4 : (W + 1) ^ 9 ≤ (W' + 1) ^ 9 := Nat.pow_le_pow_left (by omega) 9
  omega

/-- The moduli value of the orientation context is that of `Fin.cons 2 (tmGLQMod D)`. -/
theorem tmGLN_modV_cons {t : ℕ} {D : Matrix (Fin t) (Fin t) ℤ} (hpos : ∀ i, 0 < D i i) :
    linVecVal (Fin.cons 2 (fun i => D i i) : Fin (t + 1) → ℤ) =
      linVecVal (tmGLModZ (Fin.cons 2 (tmGLQMod D) : Fin (t + 1) → ℕ)) := by
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [tmGLModZ]
  · simp only [tmGLModZ, Fin.cons_succ, tmGLQMod]
    exact (Int.toNat_of_nonneg (hpos j).le).symm

/-- **Step 6 meets its contract**, with the trampoline at `idx` in place of step 5. -/
theorem tmGLN_s6_ok (hps : PointwiseStab) {Pg : Program}
    {s6 mg idx ja out red app jp inv cp cj mc Ka Da : ℕ}
    (hf : Pg.funs[s6]? = some (tmGLS6F mg idx ja out)) (hid : Pg.funs[idx]? = some tmGLNIdF)
    (hmg : Pg.HasAt mg (mkGroupFuns mg))
    (hout : Pg.funs[out]? = some (tmGLSOutF red inv cp mc))
    (hred : Pg.funs[red]? = some (tmGLSRedF app mg jp)) (happ : Pg.HasAt app (appendFuns app))
    (hj : Pg.prims[jp]? = some (pointwiseStabPrim hps))
    (hinv : Pg.HasAt inv (invFuns inv)) (hcp : Pg.HasAt cp (composeFuns cp))
    (hcj : Pg.funs[cj]? = some (supConjF cp)) (hmc : Pg.HasAt mc (mapFuns mc cj))
    (hA : Iface.TmGLAffineSpec Pg Ka Da ja) :
    Iface.TmGLNS6OK Pg s6 (fun B => tmGLS6C Ka Da (pointwiseStabPrim hps).c
      (pointwiseStabPrim hps).k (B + 1) B) := by
  intro Ω C Pp S L label hnat hq m h0 E hP htr hcard hsN hN hqα R' hRH hNR hsolv σN U gs r τ hσN
    hw hSN hsol hgl U' V D o5 vv ww h5 hv B hB
  have hsol'' : ∃ _ : ((@id (Subgroup (Perm (Fin m)))
      (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Nb).subgroupOf (gens gs)).Normal,
      Group.IsSolvable ((gens gs) ⧸ (@id (Subgroup (Perm (Fin m)))
        (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Nb).subgroupOf (gens gs)) :=
    hσN ▸ hsol
  have hrep := tmGLP_rep_ok (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Nb
    (@id (Fin L.q → Fin m → C)
      (rowTuple (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).e S.x))
    (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).i0
  have hT5 : FunAll Pg idx o5 (fun w c => w = o5 ∧ c ≤ o5.wt + 1) := tmGLN_id_spec hid o5
  have ho5 : o5.wt ≤ B := by
    have : o5.wt < (Val.list [encGroup σN, encPerm τ, .list (gs.map encPerm), o5, vv, ww]).wt :=
      wt_le_wt_list (by simp)
    omega
  have hcost : ∀ c, c ≤ tmGLS6C Ka Da (pointwiseStabPrim hps).c (pointwiseStabPrim hps).k
      (o5.wt + 1) (Val.list [encGroup σN, encPerm τ, .list (gs.map encPerm), o5, vv, ww]).wt →
      c ≤ tmGLS6C Ka Da (pointwiseStabPrim hps).c (pointwiseStabPrim hps).k (B + 1) B :=
    fun c h => h.trans (tmGLS6C_mono _ _ _ _ (by omega) hB)
  obtain ⟨hgs, ws, hpos, hc⟩ := h5
  rcases hc with ⟨hT, rfl, Ev, hE, rfl⟩ | ⟨hT, rfl, E', Ev, hE, hEv, rfl⟩
  · -- some type repeats
    obtain ⟨rfl, rfl⟩ := hv.1 hT Ev hE
    have h5' : FunAll Pg idx (.list [tmGLPMCtx U' V (fun i => D i i), .list _])
        (fun w c => TmGLS5Out (linVecVal (fun i => D i i)) _ w ∧ c ≤ _) :=
      FunAll.mono hT5 fun w c ⟨hw', hc'⟩ => ⟨⟨_, _, _, hw'⟩, hc'⟩
    have hcall := tmGLS_call' hnat hq h0 E hP htr hcard hsN hN hqα hA hgs hsol'' hgl hT
      (tmGLQMod_pos hpos) Ev hrep τ
    rw [← tmGLS_affIn_eq, ← tmGLP_modV hpos] at hcall
    exact FunAll.mono (tmGLS6_lab hnat hq h0 E hP htr hcard hsN hN hqα hps hf hmg hout hred happ hj hinv hcp hcj hmc hRH hNR hsolv hσN hw hSN hgl
      hrep _ _ _ _ _ _ h5' hcall) fun w c h => ⟨h.1, hcost c h.2⟩
  · -- all types distinct: the orientation coordinate
    obtain ⟨rfl, rfl⟩ := hv.2 hT E' Ev hE hEv
    have h5' : FunAll Pg idx (.list [tmGLNOCtx U' V (fun i => D i i), .list _])
        (fun w c => TmGLS5Out (linVecVal (Fin.cons 2 (fun i => D i i) : Fin (σN.length + 1) → ℤ))
          _ w ∧ c ≤ _) :=
      FunAll.mono hT5 fun w c ⟨hw', hc'⟩ => ⟨⟨_, _, _, hw'⟩, hc'⟩
    have hcall := tmGLS_call hnat hq h0 E hP htr hcard hsN hN hqα hA hgs hsol'' hgl
      (tmGLQMod_cons_pos hpos) Ev hrep τ
    rw [← tmGLS_affIn_eq, ← tmGLN_modV_cons hpos] at hcall
    exact FunAll.mono (tmGLS6_lab hnat hq h0 E hP htr hcard hsN hN hqα hps hf hmg hout hred happ hj hinv hcp hcj hmc hRH hNR hsolv hσN hw hSN hgl
      hrep _ _ _ _ _ _ h5' hcall) fun w c h => ⟨h.1, hcost c h.2⟩

end GI.Impl
