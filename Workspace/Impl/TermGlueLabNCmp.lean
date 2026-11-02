import Workspace.Impl.TermGlueLabNMid
import Workspace.Impl.RowSpecProg

/-!
# The label driver meets the contract of the nonempty label part

Proof of Theorem A.23, the label step in the case `w ≠ []`. `tmGLN_ne_spec`
proves `Iface.TmGLPNeSpec` for the driver `tmGLNeF` from the contracts of its callees.

The first four stages compute `gens N`, `gens N*` (`mkGroup`), the lift context and the lift
`y` of `τ`. Their hypotheses come from the input:
* the answer `w` is `[τ, U]` with `τ` in the residual set (`tmGLN_w_cons`);
* the pairs of the label value generate the graph of the label map (`rsPairGens`);
* `τ ∈ H`, so some blockwise element of `G|_dom` acts as `τ` on row `0` (`mem_Hb_ofPure`);
* the sizes `k`, `q`, `m` are below the input weight (`tmGLN_k_lt`, `tmGLN_q_lt`,
  `tmGLN_m_lt`).
The row isomorphisms that step 5 needs follow from `tmGLN_row_iso`. Stages 5 to 11 are
`tmGLN_mid`.

The cost is `tmGLNTotC F` of the weight of `[input]`, with `F` a common monotone bound of the
callee costs. When it is at most `K (W + 1) ^ D`, the driver meets `TmGLPNeSpec` with
`K · 6 ^ D` and `D`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Lang GI.Paper Equiv
open GI.Cited (Val encPerm encGroup encIntMatrix gens GensOf)

attribute [local instance] stringRAct

/-! ### Direct evaluation of the pieces -/

theorem tmGLN_pev_get {env : List Val} {a : Expr} {vs : List Val} {j : ℕ} {v : Val}
    (ha : tmGLNPev env a = some (.list vs)) (hj : vs[j]? = some v) :
    tmGLNPev env (.get a (.nat j)) = some v := by
  simp [tmGLNPev, ha, hj]

theorem tmGLN_pev_mk2 {env : List Val} {a b : Expr} {va vb : Val}
    (ha : tmGLNPev env a = some va) (hb : tmGLNPev env b = some vb) :
    tmGLNPev env (mk2 a b) = some (.list [va, vb]) := by
  simp [tmGLNPev, mk2, mk1, ha, hb]

theorem tmGLN_pev_mk3 {env : List Val} {a b c : Expr} {va vb vc : Val}
    (ha : tmGLNPev env a = some va) (hb : tmGLNPev env b = some vb)
    (hc : tmGLNPev env c = some vc) :
    tmGLNPev env (mk3 a b c) = some (.list [va, vb, vc]) := by
  simp [tmGLNPev, mk3, mk2, mk1, ha, hb, hc]

/-- The first row of the coordinates. -/
theorem tmGLN_coords0 {Ω C : Type} {n m : ℕ} (e : Ω ≃ Fin n) (S : State Ω C)
    {L : GiantLabels S} (E : Fin m × Fin L.q ≃ S.dom) (hq : 0 < L.q) :
    ((List.finRange L.q).map fun j =>
        natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin n) : ℕ)))[0]? =
      some (natList ((rowList e E ⟨0, hq⟩).map Fin.val)) := by
  simp [rowList, List.getElem?_map, List.map_map, Function.comp_def, hq]

/-! ### The cost -/

/-- The cost of the driver, for an environment of weight `W`. -/
def tmGLNTotC (F : ℕ → ℕ) : ℕ → ℕ :=
  tmGLNStC (tmGLNSz tmGLNA1) F (tmGLNStC (tmGLNSz tmGLNA2) F (tmGLNStC (tmGLNSz tmGLNA3) F
    (tmGLNStC (tmGLNSz tmGLNA4) F (tmGLNMidC F))))

theorem tmGLNTotC_mono {F : ℕ → ℕ} (hF : Monotone F) : Monotone (tmGLNTotC F) :=
  tmGLN_stC_mono _ hF (tmGLN_stC_mono _ hF (tmGLN_stC_mono _ hF
    (tmGLN_stC_mono _ hF (tmGLNMidC_mono hF))))

theorem tmGLNTotC_poly {F : ℕ → ℕ} (hF : TmGLNPoly F) : TmGLNPoly (tmGLNTotC F) :=
  tmGLN_stC_poly _ hF (tmGLN_stC_poly _ hF (tmGLN_stC_poly _ hF
    (tmGLN_stC_poly _ hF (tmGLNMidC_poly hF))))

private theorem tmGLN_top_ar {K D x c W : ℕ} (hc : c ≤ K * (W + 1) ^ D) (hW : W ≤ 2 * x + 5) :
    c ≤ K * 6 ^ D * (x + 1) ^ D := by
  have h1 : (W + 1) ^ D ≤ (6 * (x + 1)) ^ D := Nat.pow_le_pow_left (by omega) D
  calc c ≤ K * (W + 1) ^ D := hc
    _ ≤ K * (6 * (x + 1)) ^ D := Nat.mul_le_mul_left K h1
    _ = K * 6 ^ D * (x + 1) ^ D := by rw [mul_pow]; ring

private theorem tmGLN_lt_argB {x W : ℕ} (s : ℕ) (h : x < W) : x ≤ tmGLNArgB s W := by
  have : W ≤ 4 ^ s * (W + 1) := by
    have := Nat.one_le_pow s 4 (by omega)
    nlinarith
  unfold tmGLNArgB; omega

private theorem tmGLN_head_lt (v : Val) (rest : List Val) : v.wt < (Val.list (v :: rest)).wt :=
  wt_le_wt_list (List.mem_cons_self ..)

/-! ### The composition -/

/-- **The label driver meets `TmGLPNeSpec`** (Theorem A.23, the case `w ≠ []`). -/
theorem tmGLN_ne_spec {P : Program} {g mg lc xlab ylab sup bsb s5 vec s6 : ℕ}
    (hg : P.funs[g]? = some (tmGLNeF mg lc xlab ylab sup bsb s5 vec s6))
    {F Fmk Flc Fl1 Fx Fy Fsup Fbs Fs5 Fvec Fs6 : ℕ → ℕ} (hF : Monotone F)
    (hmF : ∀ B, Fmk B ≤ F B) (hcF : ∀ B, Flc B ≤ F B) (h1F : ∀ B, Fl1 B ≤ F B)
    (hxF : ∀ B, Fx B ≤ F B) (hyF : ∀ B, Fy B ≤ F B) (hsF : ∀ B, Fsup B ≤ F B)
    (hbF : ∀ B, Fbs B ≤ F B) (h5F : ∀ B, Fs5 B ≤ F B) (hvF : ∀ B, Fvec B ≤ F B)
    (h6F : ∀ B, Fs6 B ≤ F B)
    (hmk : Iface.TmGLNMkOK P mg Fmk) (hlc : Iface.TmGLNLcOK P lc Flc)
    (hl1 : Iface.TmGLNL1OK P (lc + 1) Fl1)
    (hxo : Iface.TmGLNXOK P xlab Fx) (hyo : Iface.TmGLNYOK P ylab Fy)
    (hsupo : Iface.TmGLNSupOK P sup Fsup) (hbso : Iface.TmGLNBsOK P bsb Fbs)
    (hs5 : Iface.TmGLNS5OK P s5 Fs5) (hvec : Iface.TmGLNVecOK P vec Fvec)
    (hs6 : Iface.TmGLNS6OK P s6 Fs6)
    {K D : ℕ} (hK : ∀ W, tmGLNTotC F W ≤ K * (W + 1) ^ D) :
    Iface.TmGLPNeSpec P (K * 6 ^ D) D g := by
  intro Ω C _ S k e c _ sv lv L hsv hlv _ _ _ label hnat hq m h0 E hP σH σN σS hσH hσN hσS htr
    _ _ _ hcard hsN hN hqα us vs hus hvs r _ w hw hne
  obtain ⟨τ, U, rfl, hUl, hτ⟩ := tmGLN_w_cons hw hne
  obtain ⟨ps, hlvE, -, hgen, hπ⟩ := hlv
  have hps : PairGens e L.toGiantLabels S.G ps := rsPairGens hgen hπ
  obtain ⟨gv, dv, xv, yv, hv, rv, -, -, -, -, -, -, hsv'⟩ := hsv.val
  have hk : k < sv.wt := tmGLN_k_lt hsv
  have hqc : L.q < (coordsVal e S E).wt := tmGLN_q_lt e S E
  have hmU : m < (encGroup U).wt := tmGLN_m_lt U
  set I := tmGLSI P₀ hnat hq h0 E hP htr hcard hsN hN hqα with hI
  set inp : Val := .list [.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
    encFun (rowLab e L.con.blocks)], .list us, .list vs], encPerm r,
    .list [encPerm τ, encGroup U]] with hinp
  -- the sizes are below the weight of the input
  have m1 : (Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
      encFun (rowLab e L.con.blocks)]) ∈ [Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
      encFun (rowLab e L.con.blocks)], .list us, .list vs] := by simp
  have m2 : (Val.list [Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
      encFun (rowLab e L.con.blocks)], .list us, .list vs]) ∈ [Val.list [Val.list [sv, lv,
      coordsVal e S E, a18Out σH σN σS 0, encFun (rowLab e L.con.blocks)], .list us, .list vs],
      encPerm r, .list [encPerm τ, encGroup U]] := by simp
  have m3 : sv ∈ [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
      encFun (rowLab e L.con.blocks)] := by simp
  have m4 : coordsVal e S E ∈ [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
      encFun (rowLab e L.con.blocks)] := by simp
  have m5 : encGroup U ∈ [encPerm τ, encGroup U] := by simp
  have m6 : Val.list [encPerm τ, encGroup U] ∈ [Val.list [Val.list [sv, lv,
      coordsVal e S E, a18Out σH σN σS 0, encFun (rowLab e L.con.blocks)], .list us, .list vs],
      encPerm r, .list [encPerm τ, encGroup U]] := by simp
  have hV0 : (Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
      encFun (rowLab e L.con.blocks)]).wt < inp.wt :=
    lt_trans (wt_le_wt_list m1) (wt_le_wt_list m2)
  have hkI : k < inp.wt := lt_trans (lt_trans hk (wt_le_wt_list m3)) hV0
  have hqI : L.q < inp.wt := lt_trans (lt_trans hqc (wt_le_wt_list m4)) hV0
  have hmI : m < inp.wt := lt_trans (lt_trans hmU (wt_le_wt_list m5)) (wt_le_wt_list m6)
  refine FunAll.intro hg ?_
  rw [tmGLNeF_eq]
  refine EvalAll.mono (Q := fun u c => AnsC (Equiv.refl (Fin m)) u (tmGlLab I r) ∧
    c ≤ tmGLNTotC F (Val.list [inp]).wt) ?_ fun u c ⟨hu, hc⟩ =>
      ⟨hu, tmGLN_top_ar ((hc.trans (le_refl _)).trans (hK _)) (wt_list1_le inp)⟩
  have hmono := tmGLNMidC_mono hF
  -- `gens N`
  have h1 : tmGLNPev [inp] tmGLNA1 = some (.list [.nat m, .list (σN.map encPerm)]) := rfl
  refine tmGLN_stage (tmGLN_stC_mono _ hF (tmGLN_stC_mono _ hF (tmGLN_stC_mono _ hF hmono))) h1
    ((hmk σN _ (tmGLN_pev_wt h1) (tmGLN_lt_argB _ (lt_trans hmI (tmGLN_head_lt inp [])))).mono
      fun u c ⟨hu, hc⟩ => ⟨hu, hc.trans (hmF _)⟩) ?_
  rintro _ rfl
  -- `gens N*`
  have h2 : tmGLNPev ([inp] ++ [encGroup σN]) tmGLNA2 =
      some (.list [.nat m, .list (σS.map encPerm)]) := rfl
  refine tmGLN_stage (tmGLN_stC_mono _ hF (tmGLN_stC_mono _ hF hmono)) h2
    ((hmk σS _ (tmGLN_pev_wt h2) (tmGLN_lt_argB _ (lt_trans hmI (tmGLN_head_lt inp _)))).mono
      fun u c ⟨hu, hc⟩ => ⟨hu, hc.trans (hmF _)⟩) ?_
  rintro _ rfl
  -- the lift context
  have hE := (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).e_label
  have hq0 : 0 < L.q := by omega
  have hV : tmGLNPev ([inp] ++ [encGroup σN] ++ [encGroup σS]) tmGLNV0 =
      some (.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, encFun (rowLab e L.con.blocks)]) :=
    rfl
  have hLv : tmGLNPev ([inp] ++ [encGroup σN] ++ [encGroup σS]) tmGLNLv =
      some (.list [.nat L.q, .list (ps.map pairV), .nat L.sel, .nat L.con.blocks.h,
        .nat L.con.blocks.f, blkMapVal e L.con.blocks]) := by
    exact tmGLN_pev_get hV (by rw [hlvE]; rfl)
  have h3 : tmGLNPev ([inp] ++ [encGroup σN] ++ [encGroup σS]) tmGLNA3 =
      some (.list [.list [.nat k, .nat L.q], .list (ps.map pairV),
        natList ((rowList e E ⟨0, hq0⟩).map Fin.val)]) := by
    refine tmGLN_pev_mk3 (tmGLN_pev_mk2 ?_ (tmGLN_pev_get hLv rfl)) (tmGLN_pev_get hLv rfl) ?_
    · have hs0 : tmGLNPev ([inp] ++ [encGroup σN] ++ [encGroup σS]) (.get tmGLNV0 (.nat 0)) =
          some (.list [.nat k, gv, dv, xv, yv, hv, rv, boolVal S.floor, .nat S.h, .nat S.N]) :=
        tmGLN_pev_get hV (by rw [hsv']; rfl)
      exact tmGLN_pev_get hs0 rfl
    · have hCo : tmGLNPev ([inp] ++ [encGroup σN] ++ [encGroup σS]) tmGLNCo =
          some (.list ((List.finRange L.q).map fun j =>
            natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))) :=
        tmGLN_pev_get hV rfl
      exact tmGLN_pev_get hCo (tmGLN_coords0 e S E hq0)
  refine tmGLN_stage (R := fun u => ∃ ps' : List (Perm (Fin k) × Perm (Fin m)),
      u = liftLabCtx k m ps' ∧
      Subgroup.closure {p | p ∈ ps'} = (tmGLPχ e E hnat hE ⟨0, hq0⟩).range ∧
      ps'.length ≤ (k + L.q) ^ 2)
    (tmGLN_stC_mono _ hF hmono) h3
    ((hlc e E hnat hE ⟨0, hq0⟩ hps _ (tmGLN_pev_wt h3)
      (tmGLN_lt_argB _ (lt_trans hkI (tmGLN_head_lt inp _)))
      (tmGLN_lt_argB _ (lt_trans hqI (tmGLN_head_lt inp _)))).mono
      fun u c ⟨ps', h1, h2, h3, hc⟩ => ⟨⟨ps', h1, h2, h3⟩, hc.trans (hcF _)⟩) ?_
  rintro _ ⟨ps', rfl, hcl, -⟩
  -- the lift of `τ`
  have hτH : τ ∈ (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb := hτ.1.1
  have hex := (mem_Hb_ofPure hnat hq E hP ⟨0, h0⟩ τ).1 hτH
  have h4 : tmGLNPev ([inp] ++ [encGroup σN] ++ [encGroup σS] ++ [liftLabCtx k m ps'])
      tmGLNA4 = some (.list [.list [liftLabCtx k m ps', coordsVal e S E], encPerm τ]) := rfl
  refine tmGLN_stage (R := fun u => ∃ y : Fin L.q → Perm (Fin m),
      u = .list ((List.finRange L.q).map fun i => encPerm (y i)) ∧
      cleanRowPerm E y ∈ S.domGroup ∧ y ⟨0, hq0⟩ = τ) hmono h4
    ((hl1 e E hnat hE ⟨0, hq0⟩ hcl hex _ (tmGLN_pev_wt h4)
      (tmGLN_lt_argB _ (lt_trans hkI (tmGLN_head_lt inp _)))
      (tmGLN_lt_argB _ (lt_trans hqI (tmGLN_head_lt inp _)))).mono
      fun u c ⟨y, h1, h2, h3, hc⟩ => ⟨⟨y, h1, h2, h3⟩, hc.trans (h1F _)⟩) ?_
  rintro _ ⟨y, rfl, hy, hy0⟩
  -- stages 5 to 11
  have hT : TmCsTabOK I.Hb (fun i => tmRowStr S E (.inl i)) (fun j => tmRowStr S E (.inr j))
      vs := by
    have := tmCs_tabOK_of S E σH hvs
    rw [hσH] at this
    exact this
  have hyH : ∀ i, y i ∈ I.Hb := row_mem_Hb hnat hq E hP ⟨0, h0⟩ y hy
  have hiso : ∀ j : Fin L.q, ∃ l : Fin L.q, (GI.Multicoset.Iso
      (@id (Subgroup (Perm (Fin m))) I.Hb)
      (tmRowStr S E (.inl j)) (tmRowStr S E (.inr l))).Nonempty :=
    tmGLN_row_iso (I := I) hτ hy hy0 hyH
  exact tmGLN_mid hnat hq h0 E hP htr hcard hsN hN hqα hF hxF hyF hsF hbF h5F hvF h6F hxo hyo
    hsupo hbso hs5 hvec hs6 e hlvE hσN hσS hus hT hiso hcl hτ hy hy0 hw hUl

end GI.Impl
