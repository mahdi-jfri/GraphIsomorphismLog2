import Workspace.Impl.AggLiftHier
import Workspace.Impl.AggPre
import Workspace.Impl.LabelLift
import Workspace.Impl.GenEnum

/-!
# `LiftAndContinue` on one overcoset, as a program

On an overcoset `(ρ(σ), π⁻¹(E₀))` of the round (given by `σ` and generators `ms` of `E₀`),
`lcChildF` computes, in order:

1. the graph form of `π⁻¹(E₀)` (`graphPre_spec`, one **Preimage** call on the graph group);
2. its first parts, cut to at most `k²` generators (the module at `bkr`; its contract is `LcKrOK`,
   met by the reduction module of the certificate phase);
3. a lift `a` of `σ`, `(a, σ)` in the graph group (`liftLab_spec`, one **NormalizedFactor**
   call), so `τ = e⁻¹ a` lies in the overcoset (`lc_tau_mem`);
4. the colors `y ∘ τ` (`gather`);
5. the hierarchy with the cap of `sel` lowered (`lcHier_spec`);
6. one `Continue` call on the child value, which is canonical (`canon_lcChild`).

It returns the piece `[encPerm a, u]`. `lcChild_spec` is the result. The cost of the call is not
tied to the representative `τ` that this evaluation found: `lcChild_spec` gives a run of the child
on *some* representative of the overcoset, and the translated answer does not depend on the
representative (`lc_smul_answer`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Preimage NormalizedFactor preimageSet)
open scoped Pointwise

variable {Ω C : Type} {k q : ℕ}

/-! ### The translated answer does not depend on the representative -/

/-- **`τ · Iso(H; x, y ∘ τ)` depends only on the coset `τ H`.** -/
theorem lc_smul_answer {H : Subgroup (Perm Ω)} {D : Set Ω} {x y : Ω → C} {τ τ' : Perm Ω}
    (h : τ⁻¹ * τ' ∈ H) :
    τ • GI.Algorithm.answer H D x (y ∘ τ) = τ' • GI.Algorithm.answer H D x (y ∘ τ') := by
  have key : ∀ {τ τ' : Perm Ω}, τ⁻¹ * τ' ∈ H →
      τ' • GI.Algorithm.answer H D x (y ∘ τ') ⊆ τ • GI.Algorithm.answer H D x (y ∘ τ) := by
    intro τ τ' h g hg
    obtain ⟨g', ⟨hg'H, hg'⟩, rfl⟩ := hg
    refine ⟨τ⁻¹ * τ' * g', ⟨H.mul_mem h hg'H, fun v hv => ?_⟩, ?_⟩
    · have := hg' v hv
      simp only [Function.comp_apply, Perm.mul_apply, Perm.apply_inv_self] at this ⊢
      exact this
    · simp only [smul_eq_mul]; group
  refine le_antisymm (key ?_) (key h)
  have := H.inv_mem h
  simpa [mul_inv_rev] using this

/-- Two elements of an overcoset differ by an element of its group. -/
theorem lc_inv_mul_mem {ρ : Perm Ω} {H : Subgroup (Perm Ω)} {τ τ' : Perm Ω}
    (h : τ ∈ ρ • (H : Set (Perm Ω))) (h' : τ' ∈ ρ • (H : Set (Perm Ω))) : τ⁻¹ * τ' ∈ H := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  simp only [smul_eq_mul, mul_inv_rev]
  have : a⁻¹ * ρ⁻¹ * (ρ * b) = a⁻¹ * b := by group
  rw [this]
  exact H.mul_mem (H.inv_mem ha) hb

/-- **The translated answer of a continuation** does not depend on the representative. -/
theorem lcChild_smul_answer (S : State Ω C) {L : GiantLabels S}
    (σ : alternatingGroup (Fin L.q)) (E₀ : Subgroup (alternatingGroup (Fin L.q))) {τ τ' : Perm Ω}
    (h : τ ∈ L.rep σ • (L.lift E₀ : Set (Perm Ω))) (h' : τ' ∈ L.rep σ • (L.lift E₀ : Set (Perm Ω)))
    (i cap : ℕ) :
    τ • (lcChild S E₀ τ i cap).answer = τ' • (lcChild S E₀ τ' i cap).answer := by
  rw [State.answer_of_inst (lcChild_inst S E₀ τ i cap), State.answer_of_inst (lcChild_inst S E₀ τ' i cap)]
  exact lc_smul_answer (lc_inv_mul_mem h h')

/-! ### Sizes -/

/-- The weight of the preimage instance of a graph group. -/
theorem lcPreEnc_wt (ps : List (Perm (Fin k) × Perm (Fin q))) (ms : List (Perm (Fin q)))
    (hms : ∀ m ∈ ms, ∃ p ∈ Subgroup.closure {p | p ∈ ps}, MonoidHom.snd _ _ p = m) :
    (GI.Lang.preimageEnc (pairInst (MonoidHom.snd _ _) ps ms hms)).wt ≤
      1000 * preM k q ps ms ^ 4 := by
  set M := preM k q ps ms with hM
  have hMd : k + q + ps.length + ms.length + 2 = M := rfl
  have h1 := wt_encGroup_le ((pairInst (MonoidHom.snd _ _) ps ms hms).ds.map GI.Cited.sumToFin)
  have h2 := wt_encGroup_le ms
  have h3 := wt_list3_le (.nat (k + q))
    (encGroup ((pairInst (MonoidHom.snd _ _) ps ms hms).ds.map GI.Cited.sumToFin)) (encGroup ms)
  have h4 := wt_nat_le (k + q)
  have el : ((pairInst (MonoidHom.snd _ _) ps ms hms).ds.map GI.Cited.sumToFin).length =
      ps.length := by simp [pairInst]
  rw [el] at h1
  change _ ≤ 40 * ((ps.length + 2) * (k + q + q + 1)) ^ 2 at h1
  have a1 : (ps.length + 2) * (k + q + q + 1) ≤ M * (3 * M) :=
    Nat.mul_le_mul (by omega) (by omega)
  have a2 : (ms.length + 2) * (q + 1) ≤ M * M := Nat.mul_le_mul (by omega) (by omega)
  have b1 := Nat.pow_le_pow_left a1 2
  have b2 := Nat.pow_le_pow_left a2 2
  have e1 : (M * (3 * M)) ^ 2 = 9 * M ^ 4 := by ring
  have e2 : (M * M) ^ 2 = M ^ 4 := by ring
  have m4 : M ≤ M ^ 4 := Nat.le_self_pow (by norm_num) _
  show (Val.list [.nat (k + q), encGroup _, encGroup ms]).wt ≤ _
  omega

theorem lc_liftLabCost_mono (pf : Prim) {M M' : ℕ} (h : M ≤ M') :
    liftLabCost pf M ≤ liftLabCost pf M' := by
  unfold liftLabCost
  have h1 : (2000 * M ^ 4 + 2) ^ pf.k ≤ (2000 * M' ^ 4 + 2) ^ pf.k :=
    Nat.pow_le_pow_left (by have := Nat.pow_le_pow_left h 4; omega) _
  have h2 := Nat.pow_le_pow_left h 6
  exact Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)

/-! ### The program -/

/-- **The contract of the module at `bkr`**: on `[k, pairs]` it returns a generating list of the
group of the first parts with at most `k²` entries, at cost at most `krC (pM k q ps)`. -/
def LcKrOK (Pg : Program) (bkr : ℕ) (krC : ℕ → ℕ) : Prop :=
  ∀ (k q : ℕ) (ps : List (Perm (Fin k) × Perm (Fin q))),
    FunAll Pg bkr (.list [.nat k, .list (ps.map pairV)]) (fun w c => ∃ hs : List (Perm (Fin k)),
      w = encGroup hs ∧ gens hs = gens (ps.map Prod.fst) ∧ hs.length ≤ k ^ 2 ∧ c ≤ krC (pM k q ps))

/-- The context of the continuations: the state value, `[k, q]`, the graph pairs, the context of
the label lift, the selected interval and the new cap. -/
def lcCtx (v : Val) (k q : ℕ) (ps : List (Perm (Fin k) × Perm (Fin q))) (sel cap : ℕ) : Val :=
  .list [v, .list [.nat k, .nat q], .list (ps.map pairV), liftLabCtx k q ps, .nat sel, .nat cap]

/-- The value of an overcoset: `[σ, generators of E₀]`. -/
def lcOv (σ : Perm (Fin q)) (ms : List (Perm (Fin q))) : Val :=
  .list [encPerm σ, .list (ms.map encPerm)]

/-- Entry `j` of the context. -/
def lcC (j : ℕ) : Expr := .get (arg 0) (.nat j)
/-- Entry `j` of the state value. -/
def lcV (j : ℕ) : Expr := .get (lcC 0) (.nat j)
/-- Entry `j` of the overcoset. -/
def lcO (j : ℕ) : Expr := .get (arg 1) (.nat j)

/-- **`LiftAndContinue` on one overcoset**, on `[ctx, ov]` (see the module docstring). The
environment grows as `[a, pre, K, τ, y', h']`. -/
def lcChildF (F : Funs) (bpre bkr blift bg bh : ℕ) : Expr :=
  .letE (.call bpre (mk3 (lcC 1) (lcC 2) (lcO 1)))
  (.letE (.call bkr (mk2 (lcV 0) (.var 1)))
  (.letE (.call blift (mk2 (lcC 3) (lcO 0)))
  (.letE (.call bg (mk2 (lcV 4) (.var 3)))
  (.letE (.call bh (mk3 (lcV 5) (lcC 4) (lcC 5)))
    (mk2 (.var 3) (.call F.cont (Expr.mkList [lcV 0, .var 2, lcV 2, lcV 3, .var 4, .var 5, lcV 6,
      lcV 7, lcV 8, lcV 9])))))))

/-- The size parameter of a call with input weight `M`. -/
def lcX (M : ℕ) : ℕ := 8 * (M + 2) ^ 2

theorem lcX_ge (M : ℕ) : 8 * M + 8 ≤ lcX M := by
  unfold lcX; nlinarith

theorem lcX_sq {M a b : ℕ} (ha : a + 1 ≤ M) (hb : b + 1 ≤ M) : (a + b) ^ 2 + a + b + 2 ≤ lcX M := by
  have : (a + b) ^ 2 ≤ (M + M) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  unfold lcX; nlinarith

theorem lc_col_le (k : ℕ) : k * (2 * (2 * k) + 5) + 4 ≤ 5 * (k + 1) ^ 2 := by nlinarith

/-- The constant of the overhead. -/
def lcK : ℕ := 10 ^ 9

/-- **The own cost bound of one continuation**, for an input of weight `M`. -/
noncomputable def lcB (pre fac : Prim) (krC : ℕ → ℕ) (M : ℕ) : ℕ :=
  pre.boundSize (1000 * lcX M ^ 4) + graphPreK * lcX M ^ 8 + krC (lcX M) + liftLabCost fac (lcX M) +
    gatherK * (40 * lcX M ^ 2) ^ 3 + lcHierK * (7 * M + 20) ^ 2 + lcK * lcX M ^ 8

end GI.Impl

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Preimage NormalizedFactor preimageSet)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

set_option maxHeartbeats 1000000 in
/-- **`LiftAndContinue` on one overcoset meets its specification.** The output is the piece
`[encPerm a, u]` of a representative `e⁻¹ a` of the overcoset and a canonical answer `u` of its
child; the cost is at most `lcB` of the input weight plus the total cost of a run of the child on
some representative of the overcoset. -/
theorem lcChild_spec (I : Iface) (hpre : Preimage) (hfac : NormalizedFactor) {Pg : Program}
    {F : Funs} {f bpre jpre bkr blift sb sp jfac bg bh bset : ℕ} {krC : ℕ → ℕ}
    (hf : Pg.funs[f]? = some (lcChildF F bpre bkr blift bg bh))
    (hbpre : Pg.HasAt bpre (graphPreFuns bpre jpre))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hkr : LcKrOK Pg bkr krC) (hkrm : Monotone krC)
    (hlift : Pg.funs[blift]? = some (liftLabF sb sp jfac)) (hsb : ShiftAt Pg sb)
    (hsp : Pg.HasAt sp (pSplitFuns sp))
    (hjfac : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (hga : Pg.HasAt bg (gatherFuns bg))
    (hbh : Pg.funs[bh]? = some (lcHierF bset)) (hset : Pg.HasAt bset (setFuns bset))
    {e : Ω ≃ Fin k} {c : C → ℕ} {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C}
    (hcan : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    {L : GiantLabels S} (con : L.Constituent)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {sel : ℕ} (hsel : sel < S.hier.length) (cap : ℕ)
    (σ : alternatingGroup (Fin L.q)) (E₀ : Subgroup (alternatingGroup (Fin L.q)))
    (ms : List (Perm (Fin L.q))) (hms : gens ms = E₀.map (alternatingGroup (Fin L.q)).subtype)
    (hcall : ∀ τ : Perm Ω, ∀ val, Canon e c val (lcChild S E₀ τ sel cap) →
      FunAll Pg F.cont val (I.Post .cont (lcChild S E₀ τ sel cap) e val)) :
    FunAll Pg f (.list [lcCtx (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) k L.q ps
        sel cap, lcOv (σ : Perm (Fin L.q)) ms])
      (fun w cost => (∃ a u, w = .list [encPerm a, u] ∧
          (toFin e).symm a ∈ L.rep σ • (L.lift E₀ : Set (Perm Ω)) ∧
          AnsC e u (lcChild S E₀ ((toFin e).symm a) sel cap).answer) ∧
        ∃ cb : ℕ, (∃ τ ∈ L.rep σ • (L.lift E₀ : Set (Perm Ω)), ∃ (A : Set (Perm Ω))
          (r : Run P₀ .cont (lcChild S E₀ τ sel cap) none A), (cb : ℝ) ≤ r.total I.work) ∧
        cost ≤ lcB (preimagePrim hpre) (normalizedFactorPrim hfac) krC
          (Val.list [lcCtx (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) k L.q ps
            sel cap, lcOv (σ : Perm (Fin L.q)) ms]).wt + cb) := by
  have hk := StateVal.k_le_wt hcan.stateVal
  obtain ⟨gv0, dv0, xv0, yv0, hv0, rv0, -, -, -, hyv, hhv, -, heq⟩ := hcan.val
  simp only [Val.list.injEq, List.cons.injEq] at heq
  obtain ⟨-, -, -, -, rfl, rfl, -, -, -, -, -⟩ := heq
  have hhv' := hhv
  obtain ⟨vs, rfl, -⟩ := hhv'
  set vl : List Val := [.nat k, gv, dv, xv, yv, .list vs, rv, fv, hh, .nat N] with hvl
  set v := Val.list vl with hv
  set ctxl : List Val := [v, .list [.nat k, .nat L.q], .list (ps.map pairV), liftLabCtx k L.q ps,
    .nat sel, .nat cap] with hctxl
  set ctx := Val.list ctxl with hctx
  set ovl : List Val := [encPerm (σ : Perm (Fin L.q)), .list (ms.map encPerm)] with hovl
  set ov := Val.list ovl with hov
  set a := Val.list [ctx, ov] with ha
  set M := a.wt with hM
  have ectx : lcCtx v k L.q ps sel cap = ctx := rfl
  have eov : lcOv (σ : Perm (Fin L.q)) ms = ov := rfl
  rw [ectx, eov]
  -- sizes
  have wctx : ctx.wt < M := wt_le_wt_list (by simp)
  have wov : ov.wt < M := wt_le_wt_list (by simp)
  have wv : v.wt < ctx.wt := wt_le_wt_list (by simp [hctxl])
  have wctxs := sum_wt_lt_wt_list ctxl
  have wvs := sum_wt_lt_wt_list vl
  have wovs := sum_wt_lt_wt_list ovl
  simp only [hctxl, hvl, hovl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at wctxs wvs wovs
  have hq : L.q < (encPerm (σ : Perm (Fin L.q))).wt := by
    rw [encPerm_eq_natList]
    have := length_lt_wt_list ((List.finRange L.q).map fun i => Val.nat ((σ : Perm (Fin L.q)) i))
    simpa [natList] using this
  have hpsl : ps.length < (Val.list (ps.map pairV)).wt := by
    have := length_lt_wt_list (ps.map pairV); simpa using this
  have hmsl : ms.length < (Val.list (ms.map encPerm)).wt := by
    have := length_lt_wt_list (ms.map encPerm); simpa using this
  set X := lcX M with hX
  have hMX : 8 * M + 8 ≤ X := lcX_ge M
  have eM : (Val.list [ctx, ov]).wt = M := rfl
  have ectx2 : (Val.list [v, .list [.nat k, .nat L.q], .list (ps.map pairV), liftLabCtx k L.q ps,
    .nat sel, .nat cap]).wt = ctx.wt := rfl
  have eov2 : (Val.list [encPerm (σ : Perm (Fin L.q)), .list (ms.map encPerm)]).wt = ov.wt := rfl
  have ev2 : (Val.list [.nat k, gv, dv, xv, yv, .list vs, rv, fv, hh, .nat N]).wt = v.wt := rfl
  have ectxw : (Val.list ctxl).wt = ctx.wt := rfl
  have eovw : (Val.list ovl).wt = ov.wt := rfl
  have evw : (Val.list vl).wt = v.wt := rfl
  -- the reads
  have dC0 : ∀ rest, Det Pg (a :: rest) (lcC 0) v (3 * M + 20) := fun rest =>
    (Det.get' (Det.arg' (vs := [ctx, ov]) (rest := rest) (j := 0) rfl) (Det.nat 0)
      (v := v) rfl).mono (by have := wt_nat_le 0; omega)
  have dV : ∀ rest j (hj : j < 10), Det Pg (a :: rest) (lcV j) vl[j] (5 * M + 40) :=
    fun rest j hj => by
      have := wt_getElem_lt vl j (by simpa [hvl] using hj)
      exact (Det.get' (dC0 rest) (Det.nat j)
        (List.getElem?_eq_getElem (by simpa [hvl] using hj))).mono (by
          have := wt_nat_le j; omega)
  have dCj : ∀ rest (j : ℕ) (u : Val), ctxl[j]? = some u →
      Det Pg (a :: rest) (lcC j) u (3 * M + 20 + j) := fun rest j u hu => by
    have hj : j < ctxl.length := (List.getElem?_eq_some_iff.mp hu).1
    have hu' : ctxl[j] = u := (List.getElem?_eq_some_iff.mp hu).2
    have := wt_getElem_lt ctxl j hj
    rw [hu'] at this
    exact (Det.get' (Det.arg' (vs := [ctx, ov]) (rest := rest) (j := 0) rfl) (Det.nat j)
      hu).mono (by have := wt_nat_le j; omega)
  have dOj : ∀ rest (j : ℕ) (u : Val), ovl[j]? = some u →
      Det Pg (a :: rest) (lcO j) u (3 * M + 20 + j) := fun rest j u hu => by
    have hj : j < ovl.length := (List.getElem?_eq_some_iff.mp hu).1
    have hu' : ovl[j] = u := (List.getElem?_eq_some_iff.mp hu).2
    have := wt_getElem_lt ovl j hj
    rw [hu'] at this
    exact (Det.get' (Det.arg' (vs := [ctx, ov]) (rest := rest) (j := 1) rfl) (Det.nat j)
      hu).mono (by have := wt_nat_le j; omega)
  have dVj : ∀ rest (j : ℕ) (u : Val), vl[j]? = some u →
      Det Pg (a :: rest) (lcV j) u (5 * M + 40 + j) := fun rest j u hu => by
    have hj : j < vl.length := (List.getElem?_eq_some_iff.mp hu).1
    have hu' : vl[j] = u := (List.getElem?_eq_some_iff.mp hu).2
    have := wt_getElem_lt vl j hj
    rw [hu'] at this
    exact (Det.get' (dC0 rest) (Det.nat j) hu).mono (by have := wt_nat_le j; omega)
  -- powers of the size parameter
  have hkM : k + 1 ≤ M := by omega
  have hqM : L.q + 1 ≤ M := by omega
  have hpsM : ps.length + 1 ≤ M := by omega
  have hmsM : ms.length + 1 ≤ M := by omega
  have hX1 : 1 ≤ X := by omega
  have x12 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) _
  have x23 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX1 (by omega)
  have x34 : X ^ 3 ≤ X ^ 4 := Nat.pow_le_pow_right hX1 (by omega)
  have x46 : X ^ 4 ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by omega)
  have x68 : X ^ 6 ≤ X ^ 8 := Nat.pow_le_pow_right hX1 (by omega)
  have hkX : k + 1 ≤ X := by omega
  have hqX : L.q + 1 ≤ X := by omega
  have hkq2 : (k + L.q) ^ 2 + k + L.q + 2 ≤ X := lcX_sq hkM hqM
  -- step 1: the preimage of `E₀` in graph form
  have hmsα : ∀ m ∈ ms, ∃ p ∈ Subgroup.closure {p | p ∈ ps}, MonoidHom.snd _ _ p = m := by
    intro m hm
    have hm' : m ∈ gens ms := Subgroup.subset_closure hm
    rw [hms] at hm'
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hm'
    exact lc_hms hps x.2
  have d1 := Det.mk3 (dCj [] 1 (.list [.nat k, .nat L.q]) rfl) (dCj [] 2 _ rfl)
    (dOj [] 1 (.list (ms.map encPerm)) rfl)
  set C1 := 30 * M + (preimagePrim hpre).boundSize (1000 * X ^ 4) + graphPreK * X ^ 8 +
    50 * X ^ 3 + 200 with hC1
  refine FunAll.intro hf (EvalAll.letE (Ra := fun w cw => ∃ qs : List (Perm (Fin k) × Perm (Fin L.q)),
      w = .list (qs.map pairV) ∧ qs.length ≤ (k + L.q) ^ 2 ∧
      Subgroup.closure {p | p ∈ qs} =
        Subgroup.closure {p | p ∈ ps} ⊓ (gens ms).comap (MonoidHom.snd _ _) ∧ cw ≤ C1)
    (EvalAll.call_funAll d1 fun v0 ca h0 => ?_) fun preV cpre hpre1 => ?_)
  · obtain ⟨rfl, hca⟩ := h0
    refine (graphPre_spec hpre hbpre hjpre ps ms hmsα).mono fun w cw hw => ?_
    obtain ⟨qs, rfl, hl, hqs, hc⟩ := hw
    refine ⟨qs, rfl, hl, hqs, ?_⟩
    have hpM : preM k L.q ps ms ≤ X := by unfold preM; omega
    have hb := (preimagePrim hpre).bound_le
      ((GI.Lang.preimageEnc (pairInst (MonoidHom.snd _ _) ps ms hmsα)).size_le_wt.trans
        ((lcPreEnc_wt ps ms hmsα).trans (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hpM 4))))
    have h8 := Nat.mul_le_mul_left graphPreK (Nat.pow_le_pow_left hpM 8)
    have hwq := wt_pairList_le qs
    have hpq : pM k L.q qs ≤ X := by unfold pM; omega
    have h3 := Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left hpq 3)
    have w3 := wt_list3_le (.list [.nat k, .nat L.q]) (.list (ps.map pairV)) (.list (ms.map encPerm))
    omega
  obtain ⟨qs, rfl, hql, hqs, hcpre⟩ := hpre1
  have hpqX : pM k L.q qs ≤ X := by unfold pM; omega
  have wpre : (Val.list (qs.map pairV)).wt ≤ 50 * X ^ 3 := by
    have := wt_pairList_le qs
    have := Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left hpqX 3)
    omega
  -- step 2: the group `π⁻¹(E₀)` on positions, with at most `k²` generators
  have d2 := Det.mk2 (dVj [.list (qs.map pairV)] 0 (.nat k) rfl)
    (Det.var' (P := Pg) (env := [a, .list (qs.map pairV)]) (i := 1) rfl)
  set C2 := 20 * M + 300 * X ^ 3 + krC X + 320 * X ^ 6 + 100 with hC2
  refine EvalAll.letE (Ra := fun w cw => ∃ hs : List (Perm (Fin k)), w = encGroup hs ∧
      gens hs = gens (qs.map Prod.fst) ∧ hs.length ≤ k ^ 2 ∧ cw ≤ C2)
    (EvalAll.call_funAll d2 fun v0 ca h0 => ?_) fun Kv cK hK2 => ?_
  · obtain ⟨rfl, hca⟩ := h0
    refine (hkr k L.q qs).mono fun w cw hw => ?_
    obtain ⟨hs, rfl, hgs, hl, hc⟩ := hw
    refine ⟨hs, rfl, hgs, hl, ?_⟩
    have := hkrm hpqX
    have wg := wt_encGroup_le_sq hl
    have := Nat.mul_le_mul_left 320 (Nat.pow_le_pow_left hkX 6)
    have w2 := wt_list2_le (.nat k) (.list (qs.map pairV))
    have := wt_nat_le k
    omega
  obtain ⟨hs, rfl, hgs, hsl, hcK⟩ := hK2
  have hgK : GroupValC k (encGroup hs) (groupFin e (L.lift E₀)) :=
    ⟨hs, rfl, hgs.trans (lc_groupFin hps hms hqs), hsl⟩
  have wK : (encGroup hs).wt ≤ 320 * X ^ 6 := by
    have wg := wt_encGroup_le_sq hsl
    have := Nat.mul_le_mul_left 320 (Nat.pow_le_pow_left hkX 6)
    omega
  -- step 3: a lift of `σ`
  have hσ : ∃ a', (a', (σ : Perm (Fin L.q))) ∈ Subgroup.closure {p | p ∈ ps} := by
    obtain ⟨p, hp, hp2⟩ := lc_hms hps σ.2
    exact ⟨p.1, by rw [← hp2]; exact hp⟩
  have d3 := Det.mk2 (dCj [.list (qs.map pairV), encGroup hs] 3 (liftLabCtx k L.q ps) rfl)
    (dOj [.list (qs.map pairV), encGroup hs] 0 (encPerm (σ : Perm (Fin L.q))) rfl)
  set C3 := 20 * M + liftLabCost (normalizedFactorPrim hfac) X + 4 * X ^ 2 + 100 with hC3
  refine EvalAll.letE (Ra := fun w cw => ∃ a', w = encPerm a' ∧
      (a', (σ : Perm (Fin L.q))) ∈ Subgroup.closure {p | p ∈ ps} ∧ cw ≤ C3)
    (EvalAll.call_funAll d3 fun v0 ca h0 => ?_) fun τV cτ hτ3 => ?_
  · obtain ⟨rfl, hca⟩ := h0
    refine (liftLab_spec hfac hlift hsb hsp hjfac ps hσ).mono fun w cw hw => ?_
    obtain ⟨a', rfl, ha', hc⟩ := hw
    refine ⟨a', rfl, ha', ?_⟩
    have := lc_liftLabCost_mono (normalizedFactorPrim hfac) (show ps.length + k + L.q + 2 ≤ X by omega)
    have wa := wt_encPerm_le a'
    have := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hkX 2)
    have w2 := wt_list2_le (liftLabCtx k L.q ps) (encPerm (σ : Perm (Fin L.q)))
    omega
  obtain ⟨a', rfl, ha', hcτ⟩ := hτ3
  set τ := (toFin e).symm a' with hτd
  have htτ : toFin e τ = a' := MulEquiv.apply_symm_apply _ _
  have hτmem : τ ∈ L.rep σ • (L.lift E₀ : Set (Perm Ω)) := lc_tau_mem hps σ E₀ ha'
  -- step 4: the colors `y ∘ τ`
  have hyv0 : yv = .list ((List.finRange k).map fun i => Val.nat (c (S.y (e.symm i)))) := hyv
  have hgt := gather_spec hga (L := (List.finRange k).map fun i => Val.nat (c (S.y (e.symm i))))
    (is := (List.finRange k).map fun i => (a' i : ℕ)) (by simp)
  have hgy : (((List.finRange k).map fun i => (a' i : ℕ)).map fun j =>
      ((List.finRange k).map fun i => Val.nat (c (S.y (e.symm i)))).getD j (.nat 0)) =
      (List.finRange k).map fun i => Val.nat (c ((S.y ∘ τ) (e.symm i))) := by
    rw [← htτ]; exact gather_colors e c S.y τ
  rw [hgy] at hgt
  obtain ⟨yv', hyv'⟩ : ∃ y, y = encFun fun i => c ((S.y ∘ τ) (e.symm i)) := ⟨_, rfl⟩
  have hy' : ColorVal e c yv' (S.y ∘ τ) := hyv'
  have hyc : ∀ b, c ((S.y ∘ τ) b) < 2 * k := fun b => (hcan.colors (τ b)).2
  have wy' : yv'.wt ≤ 5 * X ^ 2 := by
    have h1 := ColorVal.wt_le hy' hyc
    have h2 := lc_col_le k
    have := Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left hkX 2)
    omega
  have d4a := Det.mk2 (dVj [.list (qs.map pairV), encGroup hs, encPerm a'] 4 yv rfl)
    (Det.var' (P := Pg) (env := [a, .list (qs.map pairV), encGroup hs, encPerm a']) (i := 3) rfl)
  have d4 := Det.call d4a (by rw [hyv0, encPerm_eq_natList]; exact hgt)
  refine EvalAll.letE d4 fun yw cy hyw => ?_
  obtain ⟨hyw, hcy⟩ := hyw
  have eyw : Val.list ((List.finRange k).map fun i => Val.nat (c ((S.y ∘ τ) (e.symm i)))) = yv' :=
    hyv'.symm
  rw [eyw] at hyw
  have hyw' := hyw.symm
  subst hyw'
  have hgw : (Val.list [Val.list ((List.finRange k).map fun i => Val.nat (c (S.y (e.symm i)))),
      natList ((List.finRange k).map fun i => (a' i : ℕ))]).wt = (Val.list [yv, encPerm a']).wt := by
    rw [hyv0, encPerm_eq_natList]
  have eyt : (Val.list ((List.finRange k).map fun i => Val.nat (c ((S.y ∘ τ) (e.symm i))))).wt =
      yv'.wt := by rw [eyw]
  rw [hgw] at hcy
  set C4 := 20 * M + gatherK * (40 * X ^ 2) ^ 3 + 30 * X ^ 2 + 100 with hC4
  have hcy' : cy ≤ C4 := by
    have w2 := wt_list2_le yv (encPerm a')
    have wa := wt_encPerm_le a'
    have := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hkX 2)
    have hW : (Val.list [yv, encPerm a']).wt + 1 ≤ 40 * X ^ 2 := by omega
    have := Nat.mul_le_mul_left gatherK (Nat.pow_le_pow_left hW 3)
    have := wt_nat_le 4
    omega
  clear hcy d4 d4a hgw hgt hgy
  -- step 5: the hierarchy
  have d5a := Det.mk3 (dVj [.list (qs.map pairV), encGroup hs, encPerm a', yv'] 5 (.list vs) rfl)
    (dCj [.list (qs.map pairV), encGroup hs, encPerm a', yv'] 4 (.nat sel) rfl)
    (dCj [.list (qs.map pairV), encGroup hs, encPerm a', yv'] 5 (.nat cap) rfl)
  set C5 := 40 * M + lcHierK * (7 * M + 20) ^ 2 + 300 with hC5
  refine EvalAll.letE (Ra := fun w cw => (HierValC e w (lcHier S sel cap) ∧
      w.wt ≤ 16 * M + 90) ∧ cw ≤ C5)
    (EvalAll.call_funAll d5a fun v0 ca h0 => ?_) fun hV' ch h5 => ?_
  · obtain ⟨rfl, hca⟩ := h0
    refine (lcHier_spec hbh hset hhv hsel cap).mono fun w cw hw => ?_
    have h1 := hw.1.1
    have h2 := hw.1.2
    have h3 := hw.2
    have w3 := wt_list3_le (.list vs) (.nat sel) (.nat cap)
    have hW : (Val.list [.list vs, .nat sel, .nat cap]).wt + 10 ≤ 7 * M + 20 := by omega
    have := Nat.mul_le_mul_left lcHierK (Nat.pow_le_pow_left hW 2)
    exact ⟨⟨h1, by omega⟩, by omega⟩
  obtain ⟨⟨hhV, whV⟩, hch⟩ := h5
  -- step 6: the child value and the call of `Continue`
  set env6 : List Val := [a, .list (qs.map pairV), encGroup hs, encPerm a', yv', hV'] with henv6
  have hvlw : ∀ j (h : j < vl.length), vl[j].wt < M := fun j h =>
    (wt_getElem_lt vl j h).trans (by omega)
  set Z := 330 * X ^ 6 + 16 * M + 90 with hZ
  have dvv : ∀ j (h : j < 10), Det Pg env6 (lcV j) (vl[j]'(by simpa [hvl] using h))
      Z := fun j h => (dVj _ j _ (List.getElem?_eq_getElem _)).mono (by omega)
  have hval := Det.mkList (P := Pg) (env := env6) (c := Z)
    [(lcV 0, .nat k), (.var 2, encGroup hs), (lcV 2, dv), (lcV 3, xv), (.var 4, yv'),
      (.var 5, hV'), (lcV 6, rv), (lcV 7, fv), (lcV 8, hh), (lcV 9, .nat N)]
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact dvv 0 (by omega)
      · exact (Det.var' (i := 2) rfl).mono (by dsimp only; omega)
      · exact dvv 2 (by omega)
      · exact dvv 3 (by omega)
      · exact (Det.var' (i := 4) rfl).mono (by dsimp only; omega)
      · exact (Det.var' (i := 5) rfl).mono (by dsimp only; omega)
      · exact dvv 6 (by omega)
      · exact dvv 7 (by omega)
      · exact dvv 8 (by omega)
      · exact dvv 9 (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hval
  have hcanT := canon_lcChild hcan con E₀ τ sel cap hgK hy' hhV
  have hcl := call_child I hval (hcall τ _ hcanT)
  have hfin := EvalAll.snoc_det (Det.mk1 (Det.var' (P := Pg) (env := env6) (i := 3) rfl)) hcl
  refine hfin.mono ?_
  rintro w cw ⟨u, cu, ⟨A, r, cb, hA, hcb, hcu⟩, rfl, hcw⟩
  have hAT := r.exact
  subst hAT
  refine ⟨⟨a', u, rfl, hτmem, hA⟩, cb, ⟨τ, hτmem, _, r, hcb⟩, ?_⟩
  have wcv : (Val.list [Val.nat k, encGroup hs, dv, xv, yv', hV', rv, fv, hh, Val.nat N]).wt ≤
      10 * (2 * Z + 1) + 4 := by
    refine (wt_list_le_of _ (c := Z) ?_).trans (by simp)
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    have h0 := hvlw 0 (by simp [hvl]); have h2 := hvlw 2 (by simp [hvl])
    have h3 := hvlw 3 (by simp [hvl]); have h6 := hvlw 6 (by simp [hvl])
    have h7 := hvlw 7 (by simp [hvl]); have h8 := hvlw 8 (by simp [hvl])
    have h9 := hvlw 9 (by simp [hvl])
    simp only [hvl, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h2 h3 h6 h7 h8 h9
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have wu : u.wt ≤ 1000 * X ^ 6 := by
    have h1 := hA.wt_le
    have h2 := ansW_le k
    have := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hkX 6)
    omega
  have wa := wt_encPerm_le a'
  have := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hkX 2)
  have wo : (Val.list ([encPerm a'] ++ [u])).wt ≤ 2 * (4 * X ^ 2 + 1000 * X ^ 6) + 6 := by
    have := wt_list2_le (encPerm a') u
    simp only [List.cons_append, List.nil_append]
    omega
  have wo1 : (Val.list [encPerm a']).wt ≤ 2 * (4 * X ^ 2) + 5 := by
    have := wt_list_le [encPerm a']
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    omega
  have x8 : 100000 * X ^ 6 + 10000 * X ^ 3 + 10000 * X ^ 2 + 1000 * M + 10000 ≤ lcK * X ^ 8 := by
    have : 1000 * M + 10000 ≤ 10000 * X := by omega
    have : 10000 * X ^ 8 ≤ lcK * X ^ 8 - 1000000 * X ^ 8 := by
      simp only [lcK]; omega
    omega
  simp only [hC1, hC2, hC3, hC4, hC5] at hcpre hcK hcτ hcy' hch
  rw [lcB, ← hX]
  have eM2 : lcHierK * (7 * (Val.list [ctx, ov]).wt + 20) ^ 2 = lcHierK * (7 * M + 20) ^ 2 := rfl
  rw [eM2]
  omega

end GI.Impl
