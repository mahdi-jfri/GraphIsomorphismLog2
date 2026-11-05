module

public import Workspace.Impl.TermGlueLabPOGen
public import Workspace.Impl.TermGlueLabPEx

@[expose] public section

/-!
# Step 5 with the orientation coordinate, and its adapter to step 6

Step 5 of the label program, the case where all types are distinct. Step 5 is
run with the per-generator program `tmGLPGenOF` (items with the orientation coordinate,
`tmGLPGenO_spec`). Its context `[t, U, V, d]` gets the modulus `2` of the orientation in front
of `d` (`tmGLPStep5OF`), so that step 6 reads the moduli `(2, D)`.

* `tmGLPStep5O_spec`: on the input of step 5, the result is `[[t, U, V, (2, d)], items]` with
  the facts of the setup and, for every generator, an item related to it by `R`
  (`TmGLPStep5OOut`);
* `tmGLP_step5O_s5`: with `R = TmGLPGenOOut`, this is the hypothesis `h5` of step 6
  (`TmGLS5Out`) for the moduli `Fin.cons 2 (tmGLQMod D)` and the items of `tmGLAffItem` with
  `E_o = tmGLPEoOf E'`, `tmGLlamO` and `tmGLoO` (the form of `tmGLS_call`).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Algorithm (State)
open GI.Cited (Val encInt encPerm encGroup encIntMatrix gens)

/-- The expression of `encInt 2`. -/
def tmGLPTwoE : Expr := mk2 (.nat 0) (mk2 (.nat 0) (.nat 1))

theorem tmGLP_encInt2 : encInt 2 = .list [.nat 0, .list [.nat 0, .nat 1]] := by
  simp [encInt, Nat.bits, Nat.binaryRec]

theorem tmGLP_twoE {P : Program} {env : List Val} : Det P env tmGLPTwoE (encInt 2) 200 := by
  rw [tmGLP_encInt2]
  exact (Det.mk2 (Det.nat 0) (Det.mk2 (Det.nat 0) (Det.nat 1))).mono (by decide)

theorem tmGLP_encInt2_wt : (encInt 2).wt ≤ 100 := by rw [tmGLP_encInt2]; decide

/-- **Step 5 with the modulus of the orientation in front**, on the input of step 5. -/
def tmGLPStep5OF (s5 cons : ℕ) : Expr :=
  .letE (.call s5 (.var 0))
    (mk2 (mk4 (.get (.get (.var 1) (.nat 0)) (.nat 0)) (.get (.get (.var 1) (.nat 0)) (.nat 1))
        (.get (.get (.var 1) (.nat 0)) (.nat 2))
        (.call cons (mk2 tmGLPTwoE (.get (.get (.var 1) (.nat 0)) (.nat 3)))))
      (.get (.var 1) (.nat 1)))

/-- **The output**: `[[t, U, V, (2, d)], items]` with the setup facts and items related by `R`. -/
def TmGLPStep5OOut {m : ℕ} (σS σN bs : List (Perm (Fin m)))
    (R : Matrix (Fin σN.length) (Fin σN.length) ℤ → Matrix (Fin σN.length) (Fin σN.length) ℤ →
      (Fin σN.length → ℤ) → Perm (Fin m) → Val → Prop)
    (gs : List (Perm (Fin m))) (w : Val) : Prop :=
  ∃ (M : Matrix (Fin σN.length) (Fin σN.length) ℤ) (Z : Matrix (Fin bs.length) (Fin σN.length) ℤ)
    (U V D : Matrix (Fin σN.length) (Fin σN.length) ℤ) (ws : List Val),
    w = .list [.list [.nat σN.length, encIntMatrix U, encIntMatrix V,
      linVecVal (tmGLModZ (Fin.cons 2 (tmGLQMod D) : Fin (σN.length + 1) → ℕ))], .list ws] ∧
    linPermPresentation σS σN M ∧
    (∀ j : Fin bs.length, TmGLPCoordOf σN (bs[j.val]'j.isLt) (Z j)) ∧ IsUnit V.det ∧
    (∀ i, 0 < D i i) ∧
    (∀ w, (∃ y, Matrix.vecMul y (tmGLQStack M Z) = w) ↔ ∀ i, D i i ∣ (Matrix.vecMul w V) i) ∧
    U * V = 1 ∧ V * U = 1 ∧
    List.Forall₂ (fun g w => R U V (fun i => D i i) g w) gs ws

/-- The moduli value `(2, D)`. -/
theorem tmGLP_modV_cons {t : ℕ} {D : Matrix (Fin t) (Fin t) ℤ} (hpos : ∀ i, 0 < D i i) :
    linVecVal (tmGLModZ (Fin.cons 2 (tmGLQMod D) : Fin (t + 1) → ℕ)) =
      tmGLPConsV (encInt 2) (linVecVal (fun i => D i i)) := by
  have h : tmGLModZ (Fin.cons 2 (tmGLQMod D) : Fin (t + 1) → ℕ) =
      Fin.cons 2 (tmGLModZ (tmGLQMod D)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [tmGLModZ]
    · simp [tmGLModZ]
  rw [h, tmGLP_linVec_cons, tmGLP_modV hpos]

def tmGLPStep5OC (C5 W : ℕ) : ℕ := 100 * (W + 1) + 1000 * (C5 + 10) + 10 * tmGLPConsC (2 * C5 + 206)

set_option maxHeartbeats 1000000 in
/-- **Step 5 with the orientation modulus.** -/
theorem tmGLPStep5O_spec {P : Program} {f s5 cons app : ℕ}
    (hf : P.funs[f]? = some (tmGLPStep5OF s5 cons)) (hcons : P.funs[cons]? = some (tmGLPConsF app))
    (happ : P.HasAt app (appendFuns app)) {m : ℕ} (σS σN bs : List (Perm (Fin m)))
    (R : Matrix (Fin σN.length) (Fin σN.length) ℤ → Matrix (Fin σN.length) (Fin σN.length) ℤ →
      (Fin σN.length → ℤ) → Perm (Fin m) → Val → Prop)
    (gs : List (Perm (Fin m))) (a : Val) {C5 : ℕ}
    (h5 : FunAll P s5 a (fun w c => TmGLPStep5OutR σS σN bs R gs w ∧ c ≤ C5)) :
    FunAll P f a (fun w c => TmGLPStep5OOut σS σN bs R gs w ∧ c ≤ tmGLPStep5OC C5 a.wt) := by
  apply FunAll.intro hf
  have dv := Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl
  refine EvalAll.letE (EvalAll.call_funAll dv (Q := fun w c => TmGLPStep5OutR σS σN bs R gs w ∧
      c ≤ a.wt + 1 + C5 + C5 + 1 ∧ w.wt < C5) fun v ca hv => ?_) fun r cr hr => ?_
  · obtain ⟨rfl, hca⟩ := hv
    exact (FunAll.wt_lt h5).mono fun w c ⟨⟨hR, hc⟩, hw⟩ => ⟨hR, by omega, by omega⟩
  obtain ⟨hR, hcr, hwr⟩ := hr
  have hR' := hR
  obtain ⟨M, Z, U, V, D, ws, rfl, hMp, hZ, hV, hpos, hrel, hUV, hVU, hws⟩ := hR'
  set dv' : List Val := (List.finRange σN.length).map fun i => encInt (D i i) with hdv
  have hd : linVecVal (fun i => D i i) = .list dv' := rfl
  set ctx : Val := .list [.nat σN.length, encIntMatrix U, encIntMatrix V, .list dv'] with hctx
  have ectx : tmGLPMCtx U V (fun i => D i i) = ctx := rfl
  rw [ectx]
  set r : Val := .list [ctx, .list ws] with hr
  set env : List Val := [a, r] with henv
  have d1 : Det P env (.var 1) r (r.wt + 1) := Det.var' rfl
  have dc := Det.get' d1 (Det.nat 0) (x := 0) (vs := [ctx, .list ws]) rfl
  have dc' : Det P env _ (.list [.nat σN.length, encIntMatrix U, encIntMatrix V, .list dv']) _ := dc
  have e0 := Det.get' dc' (Det.nat 0) (x := 0) (vs := [.nat σN.length, encIntMatrix U,
    encIntMatrix V, .list dv']) rfl
  have e1 := Det.get' dc' (Det.nat 1) (x := 1) (vs := [.nat σN.length, encIntMatrix U,
    encIntMatrix V, .list dv']) rfl
  have e2 := Det.get' dc' (Det.nat 2) (x := 2) (vs := [.nat σN.length, encIntMatrix U,
    encIntMatrix V, .list dv']) rfl
  have e3 := Det.get' dc' (Det.nat 3) (x := 3) (vs := [.nat σN.length, encIntMatrix U,
    encIntMatrix V, .list dv']) rfl
  have dk := Det.call (Det.mk2 (tmGLP_twoE (P := P) (env := env)) e3)
    (tmGLPCons_spec hcons happ (encInt 2) dv')
  have dw := Det.get' d1 (Det.nat 1) (x := 1) (vs := [ctx, .list ws]) rfl
  have dm := Det.mk2 (Det.mk4 e0 e1 e2 dk) dw
  refine dm.post fun c hc => ⟨⟨M, Z, U, V, D, ws, ?_, hMp, hZ, hV, hpos, hrel, hUV, hVU, hws⟩, ?_⟩
  · rw [tmGLP_modV_cons hpos, hd]; rfl
  · -- the cost
    have er : r.wt = (Val.list [tmGLPMCtx U V (fun i => D i i), .list ws]).wt := rfl
    have wctx : ctx.wt < r.wt := wt_le_wt_list (by simp)
    have wws : (Val.list ws).wt < r.wt := wt_le_wt_list (by simp)
    have wd : (Val.list dv').wt < ctx.wt := wt_le_wt_list (by simp)
    have wU : (encIntMatrix U).wt < ctx.wt := wt_le_wt_list (by simp)
    have wV : (encIntMatrix V).wt < ctx.wt := wt_le_wt_list (by simp)
    have wt0 : (Val.nat σN.length).wt < ctx.wt := wt_le_wt_list (by simp)
    have w2 := tmGLP_encInt2_wt
    have wk := wt_list2_le (encInt 2) (.list dv')
    have hk := tmGLPConsC_mono (show (Val.list [encInt 2, .list dv']).wt ≤ 2 * C5 + 206 by omega)
    have wk' := wt_list_cons_le (encInt 2) dv'
    have w4 := wt_list4_le (.nat σN.length) (encIntMatrix U) (encIntMatrix V)
      (.list (encInt 2 :: dv'))
    have wf := wt_list2_le (.list [.nat σN.length, encIntMatrix U, encIntMatrix V,
      .list (encInt 2 :: dv')]) (.list ws)
    have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    have : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
    have : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
    have : (Val.nat 3).wt ≤ 5 := wt_nat_le 3
    have ec : ctx.wt = (Val.list [.nat σN.length, encIntMatrix U, encIntMatrix V, .list dv']).wt :=
      rfl
    have hCw : tmGLPConsC (Val.list [encInt 2, .list dv']).wt ≥ (Val.list (encInt 2 :: dv')).wt :=
      (tmGLP_fundet_wt (tmGLPCons_spec hcons happ (encInt 2) dv')).le
    unfold tmGLPStep5OC
    generalize tmGLPConsC (2 * C5 + 206) = K at *
    omega

/-! ### The adapter to step 6 -/

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]
variable {N H : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] {φ : N →* A}
variable {Ω₀ C₀ : Type} {S : State Ω₀ C₀} {L : GI.Algorithm.GiantLabels S}

/-- **The step-5 result in the form step 6 reads, all types distinct.** For the `b_j` of
`tmGLPBs_spec` and `φ` with kernel `⟨σS⟩`, the result of `tmGLPStep5O_spec` with the items of
`tmGLPGenO_spec` gives the coordinates `E'` of `A/B(x)` with `E'(class of z) = z V mod D` and
the hypothesis `h5` of step 6 for the moduli `(2, D)` and the items of `E_o = tmGLPEoOf E'`. -/
theorem tmGLP_step5O_s5 (hn : GI.Multicoset.Normalizes H N) (hker : TmGLKer N H φ) (hNH : N ≤ H)
    {k : Perm (Fin n) → Fin L.q → Perm (Fin n)} (hk : TmGLLift N H φ k)
    (E : Fin n × Fin L.q ≃ S.dom) (i0 j0 : Fin L.q) {x : Fin L.q → Ω}
    (hyk : ∀ h ∈ H, ∀ y : Fin L.q → Perm (Fin n), GI.Paper.cleanRowPerm E y ∈ S.domGroup →
      y i0 = h → ∃ ν, TmGLZero N φ ν ∧ ∀ i, y i = k h i * ν i)
    {σS σN bs : List (Perm (Fin n))} (hN : gens σN = N)
    (hK : ∀ g (hg : g ∈ N), φ ⟨g, hg⟩ = 1 ↔ g ∈ gens σS) (hbs : TmGLPBsOut N x bs)
    {gs : List (Perm (Fin n))} (hgs : gens gs ≤ Aut H (types N x)) {w : Val}
    (hw : TmGLPStep5OOut σS σN bs (TmGLPGenOOut E i0 σN x) gs w) :
    ∃ (U V D : Matrix (Fin σN.length) (Fin σN.length) ℤ)
      (E' : Additive (tmGLV N φ x) ≃+ tmGLVec (tmGLQMod D)),
      (∀ i, 0 < D i i) ∧ U * V = 1 ∧ V * U = 1 ∧
      (∀ z, E' (tmGLPg N φ x (fun i => σN[i.val]) z) = tmGLQMap V D z) ∧
      TmGLS5Out (linVecVal (tmGLModZ (Fin.cons 2 (tmGLQMod D) : Fin (σN.length + 1) → ℕ)))
        (gs.attach.map fun g => tmGLAffItem gs (Fin.cons 2 (tmGLQMod D) : Fin (σN.length + 1) → ℕ)
          (tmGLρE (tmGLPEoOf E') (tmGLlamO hn hker hgs hNH))
          (tmGLcE (tmGLPEoOf E') (tmGLoO (tmGLPRep N x j0) k)) ⟨g.1, Subgroup.subset_closure g.2⟩)
        w := by
  obtain ⟨M, Z, U, V, D, ws, rfl, hMp, hZ, hV, hpos, hrel, hUV, hVU, hws⟩ := hw
  obtain ⟨E', hE'⟩ := tmGLP_set_E (x := x) φ hN hK hbs hMp hZ hV hpos hrel
  refine ⟨U, V, D, E', hpos, hUV, hVU, hE', .nat σN.length, encIntMatrix U, encIntMatrix V, ?_⟩
  have hitems := tmGLP_items_eq (F := fun g => tmGLAffItem gs
      (Fin.cons 2 (tmGLQMod D) : Fin (σN.length + 1) → ℕ)
      (tmGLρE (tmGLPEoOf E') (tmGLlamO hn hker hgs hNH))
      (tmGLcE (tmGLPEoOf E') (tmGLoO (tmGLPRep N x j0) k)) g)
    (fun g hg w hgw => tmGLP_genO_item hn hker hNH hk E i0 j0 hyk hN hpos hUV E' hE' hgs
      ⟨g, Subgroup.subset_closure hg⟩ hgw) hws
  rw [← hitems]

end GI.Impl
