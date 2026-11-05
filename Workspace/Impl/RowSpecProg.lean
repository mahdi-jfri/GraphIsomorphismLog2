module

public import Workspace.Impl.ColBrSpec
public import Workspace.Impl.GenCls
public import Workspace.Impl.AggPairs

@[expose] public section

/-!
# The row step as a program

The row step (`Iface.RowSpec`) on `[sv, lv]`:

1. computes the row labels `rl` of the positions (`rowPartE`, `rowPart_det`);
2. builds the context `winCtx k q rl ps` of the coordinate program from `sv`, `lv` and `rl`
   (`rsCtxE`, `rsCtx_det`);
3. computes pure coordinates `E` of Theorem A.17 (`coords_spec_good`), as `coordsVal e S E`;
4. computes generators of `H`, `N`, `N*` and the number `t` of Theorem A.18 (`a18_spec`);
5. if `t ≠ 0` (`N` is not transitive on a row) calls the column branch (`colBr_spec`), and
   otherwise the terminal function (`RowTermSpec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms)

/-! ### The context of the coordinate program -/

/-- The context `winCtx k q rl ps`, in the environment `[[sv, lv], rl]`; the range functions
sit at `rng`. -/
def rsCtxE (rng : ℕ) : Expr :=
  Expr.mkList [.get (.get (.var 0) (.nat 0)) (.nat 0), .get (.get (.var 0) (.nat 1)) (.nat 0),
    .var 1, .get (.get (.var 0) (.nat 1)) (.nat 1),
    mk2 (.get (.get (.var 0) (.nat 0)) (.nat 0))
      (mk2 (.call rng (.get (.get (.var 0) (.nat 0)) (.nat 0)))
        (.call rng (.get (.get (.var 0) (.nat 1)) (.nat 0)))),
    .call rng (.get (.get (.var 0) (.nat 1)) (.nat 0)),
    .call rng (.get (.get (.var 0) (.nat 0)) (.nat 0))]

theorem rsCtx_det {P : Program} {rng : ℕ} (hrng : P.HasAt rng (rangeFuns rng)) {k q : ℕ}
    {svs lvs : List Val} (ps : List (Perm (Fin k) × Perm (Fin q))) (rl : List ℕ)
    (hsv : svs[0]? = some (.nat k)) (hq : lvs[0]? = some (.nat q))
    (hps : lvs[1]? = some (.list (ps.map pairV))) {B : ℕ}
    (hB : (Val.list [.list svs, .list lvs]).wt + (natList rl).wt + k + q ≤ B) :
    Det P [.list [.list svs, .list lvs], natList rl] (rsCtxE rng) (winCtx k q rl ps)
      (10 ^ 8 * (B + 1) ^ 3) := by
  set env := [Val.list [.list svs, .list lvs], natList rl] with henv
  have wA : (Val.list [.list svs, .list lvs]).wt + 1 ≤ B + 1 := by omega
  have d0 : Det P env (.var 0) (.list [.list svs, .list lvs]) (B + 1) := colVar rfl wA
  have dsv : Det P env (.get (.var 0) (.nat 0)) (.list svs) (2 * (B + 1) + 3 + 1) :=
    colGet d0 (Det.nat 0) rfl
  have dlv : Det P env (.get (.var 0) (.nat 1)) (.list lvs) (2 * (B + 1) + 4 + 1) :=
    colGet d0 (Det.nat 1) rfl
  have dk : Det P env (.get (.get (.var 0) (.nat 0)) (.nat 0)) (.nat k) (10 * B + 30) :=
    (colGet dsv (Det.nat 0) hsv).mono (by omega)
  have dq : Det P env (.get (.get (.var 0) (.nat 1)) (.nat 0)) (.nat q) (10 * B + 30) :=
    (colGet dlv (Det.nat 0) hq).mono (by omega)
  have dps : Det P env (.get (.get (.var 0) (.nat 1)) (.nat 1)) (.list (ps.map pairV))
      (10 * B + 30) := (colGet dlv (Det.nat 1) hps).mono (by omega)
  have drl : Det P env (.var 1) (natList rl) (B + 1) := colVar rfl (by omega)
  have p3 : (B + 1) ≤ (B + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hk3 : 7000 * (k + 1) ^ 3 ≤ 7000 * (B + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have hq3 : 7000 * (q + 1) ^ 3 ≤ 7000 * (B + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have drk : Det P env (.call rng (.get (.get (.var 0) (.nat 0)) (.nat 0)))
      (encPerm (1 : Perm (Fin k))) (15000 * (B + 1) ^ 3 + 40 * B + 40) := by
    have := colCall dk (range_det hrng k)
    rw [range_eq_encPerm_one] at this
    exact this.mono (by omega)
  have drq : Det P env (.call rng (.get (.get (.var 0) (.nat 1)) (.nat 0)))
      (encPerm (1 : Perm (Fin q))) (15000 * (B + 1) ^ 3 + 40 * B + 40) := by
    have := colCall dq (range_det hrng q)
    rw [range_eq_encPerm_one] at this
    exact this.mono (by omega)
  have dsp := colMk2 dk (colMk2 drk drq)
  set c := 1000000 * (B + 1) ^ 3 with hc
  have hps := Det.mkList (P := P) (env := env) (c := c)
    [(.get (.get (.var 0) (.nat 0)) (.nat 0), .nat k), (.get (.get (.var 0) (.nat 1)) (.nat 0), .nat q),
      (.var 1, natList rl), (.get (.get (.var 0) (.nat 1)) (.nat 1), .list (ps.map pairV)),
      (mk2 (.get (.get (.var 0) (.nat 0)) (.nat 0))
        (mk2 (.call rng (.get (.get (.var 0) (.nat 0)) (.nat 0)))
          (.call rng (.get (.get (.var 0) (.nat 1)) (.nat 0)))), pSplitCtx k q),
      (.call rng (.get (.get (.var 0) (.nat 1)) (.nat 0)), encPerm (1 : Perm (Fin q))),
      (.call rng (.get (.get (.var 0) (.nat 0)) (.nat 0)), encPerm (1 : Perm (Fin k)))] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact dk.mono (by omega)
      · exact dq.mono (by omega)
      · exact drl.mono (by omega)
      · exact dps.mono (by omega)
      · exact dsp.mono (by omega)
      · exact drq.mono (by omega)
      · exact drk.mono (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hps
  refine hps.mono ?_
  have w1 := dk.wt_lt; have w2 := dq.wt_lt; have w3 := drl.wt_lt; have w4 := dps.wt_lt
  have w5 : (pSplitCtx k q).wt < _ := dsp.wt_lt; have w6 := drq.wt_lt; have w7 := drk.wt_lt
  have hw := wt_list_le [.nat k, .nat q, natList rl, .list (ps.map pairV), pSplitCtx k q,
    encPerm (1 : Perm (Fin q)), encPerm (1 : Perm (Fin k))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at hw
  show _ ≤ 10 ^ 8 * (B + 1) ^ 3
  have : (10 : ℕ) ^ 8 = 100000000 := by norm_num
  rw [this]
  generalize (B + 1) ^ 3 = t at *
  omega

/-! ### The pairs of a label value generate the graph of `G` -/

theorem rsPairGens {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}
    {ps : List (Perm (Fin k) × Perm (Fin L.q))}
    (hgen : GI.Cited.gens (ps.map Prod.fst) = groupFin e S.G)
    (hπ : ∀ p ∈ ps, ∀ hg : (toFin e).symm p.1 ∈ S.G,
      ((L.π ⟨(toFin e).symm p.1, hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) = p.2) :
    PairGens e L S.G ps := by
  have hmem : ∀ p ∈ ps, (toFin e).symm p.1 ∈ S.G := by
    intro p hp
    have h1 : p.1 ∈ GI.Cited.gens (ps.map Prod.fst) :=
      Subgroup.subset_closure (List.mem_map_of_mem hp)
    rw [hgen] at h1
    obtain ⟨g, hg, hgp⟩ := Subgroup.mem_map.1 h1
    have : (toFin e).symm p.1 = g := by
      rw [← hgp]; exact (toFin e).symm_apply_apply g
    rw [this]; exact hg
  have hp : ∀ p (hp : p ∈ ps), gpair e L ⟨_, hmem p hp⟩ = p := by
    intro p hp'
    refine Prod.ext ?_ (hπ p hp' _)
    show toFin e ((toFin e).symm p.1) = p.1
    exact (toFin e).apply_symm_apply p.1
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 fun p hp' => ?_
    rw [← hp p hp']
    exact Subgroup.mem_map_of_mem _ (by simp)
  · intro x hx
    obtain ⟨⟨g, hg⟩, -, rfl⟩ := Subgroup.mem_map.1 hx
    set K : Subgroup (Perm Ω) :=
      ((Subgroup.closure {p : Perm (Fin k) × Perm (Fin L.q) | p ∈ ps}).comap (gpair e L)).map
        S.G.subtype with hK
    have hle : GI.Cited.gens (ps.map Prod.fst) ≤ K.map (toFin e).toMonoidHom := by
      refine (Subgroup.closure_le _).2 fun a ha => ?_
      obtain ⟨p, hp', rfl⟩ := List.mem_map.1 ha
      refine ⟨(toFin e).symm p.1, ⟨⟨_, hmem p hp'⟩, ?_, rfl⟩, (toFin e).apply_symm_apply p.1⟩
      show gpair e L ⟨_, hmem p hp'⟩ ∈ Subgroup.closure {p : Perm (Fin k) × Perm (Fin L.q) | p ∈ ps}
      rw [hp p hp']
      exact Subgroup.subset_closure hp'
    have h1 : toFin e g ∈ K.map (toFin e).toMonoidHom := by
      apply hle; rw [hgen]; exact Subgroup.mem_map_of_mem _ hg
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 h1
    have hyg' : y = g := (toFin e).injective hyg
    subst hyg'
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    exact hz


/-- The entries of the context weigh less than the context. -/
theorem rs_ctx_entries (k q : ℕ) (rl : List ℕ) (ps : List (Perm (Fin k) × Perm (Fin q))) :
    (Val.nat k).wt + (Val.nat q).wt + (natList rl).wt + (Val.list (ps.map pairV)).wt +
      (pSplitCtx k q).wt < (winCtx k q rl ps).wt := by
  have := sum_wt_lt_wt_list [Val.nat k, .nat q, natList rl, .list (ps.map pairV), pSplitCtx k q,
    encPerm (1 : Perm (Fin q)), encPerm (1 : Perm (Fin k))]
  simp only [List.map, List.sum_cons, List.sum_nil] at this
  unfold winCtx; omega

/-- **The input of the A.18 program**, built from the environment of the row step. -/
theorem rs_a18In_det {P : Program} (A cv : Val) {k q : ℕ} (rl : List ℕ)
    (ps : List (Perm (Fin k) × Perm (Fin q))) :
    ∃ c0, Det P [A, natList rl, winCtx k q rl ps, cv]
      (mk4 (mk2 (.get (.var 2) (.nat 0)) (.get (.var 2) (.nat 1))) (.get (.var 2) (.nat 3))
        (.var 3) (.var 1)) (a18In k q ps cv rl) c0 ∧
      c0 ≤ 100 * ((winCtx k q rl ps).wt + cv.wt) + 100 := by
  have gc : ∀ (j : ℕ) (u : Val), [Val.nat k, .nat q, natList rl, .list (ps.map pairV),
      pSplitCtx k q, encPerm (1 : Perm (Fin q)), encPerm (1 : Perm (Fin k))][j]? = some u →
      Det P [A, natList rl, winCtx k q rl ps, cv] (.get (.var 2) (.nat j)) u
        (2 * ((winCtx k q rl ps).wt + 1) + (j + 3) + 1) := fun j u hu =>
    colGet (colVar (P := P) (env := [A, natList rl, winCtx k q rl ps, cv]) (i := 2) rfl le_rfl)
      (Det.nat j) hu
  refine ⟨_, Det.mk4 (Det.mk2 (gc 0 _ rfl) (gc 1 _ rfl)) (gc 3 _ rfl)
    (Det.var' (P := P) (env := [A, natList rl, winCtx k q rl ps, cv]) (i := 3) rfl)
    (Det.var' (P := P) (env := [A, natList rl, winCtx k q rl ps, cv]) (i := 1) rfl), ?_⟩
  have h1 := rs_ctx_entries k q rl ps
  have h2 := wt_list2_le (Val.nat k) (Val.nat q)
  have h3 := wt_list_le [Val.list [.nat k, .nat q], .list (ps.map pairV), cv, natList rl]
  simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at h3
  have h4 : (a18In k q ps cv rl).wt = (Val.list [Val.list [.nat k, .nat q],
    .list (ps.map pairV), cv, natList rl]).wt := rfl
  omega

/-- A list of five expressions, each evaluating at cost at most `c`. -/
theorem rs_mk5 {P : Program} {env : List Val} {a₁ a₂ a₃ a₄ a₅ : Expr} {v₁ v₂ v₃ v₄ v₅ : Val}
    {c : ℕ} (h₁ : Det P env a₁ v₁ c) (h₂ : Det P env a₂ v₂ c) (h₃ : Det P env a₃ v₃ c)
    (h₄ : Det P env a₄ v₄ c) (h₅ : Det P env a₅ v₅ c) :
    ∃ c', Det P env (Expr.mkList [a₁, a₂, a₃, a₄, a₅]) (.list [v₁, v₂, v₃, v₄, v₅]) c' ∧
      c' ≤ 5 * c + 10 * (v₁.wt + v₂.wt + v₃.wt + v₄.wt + v₅.wt) + 60 := by
  have h := Det.mkList [(a₁, v₁), (a₂, v₂), (a₃, v₃), (a₄, v₄), (a₅, v₅)] (c := c)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl) <;> assumption)
  have hw := wt_list_le [v₁, v₂, v₃, v₄, v₅]
  simp only [List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at h hw
  exact ⟨_, h, by omega⟩

/-- The `j`-th entry of a list value in the environment. -/
theorem rs_get {P : Program} {env : List Val} {i j : ℕ} {vs : List Val} {u : Val}
    (h : env[i]? = some (.list vs)) (hu : vs[j]? = some u) :
    Det P env (.get (.var i) (.nat j)) u (2 * ((Val.list vs).wt + 1) + (j + 3) + 1) :=
  colGet (colVar h le_rfl) (Det.nat j) hu

/-- **The input of the column branch**, built from the environment of the row step. -/
theorem rs_colIn_det {P : Program} {sv lv rv cv x y : Val} {Cs Fs : List Val}
    (hx : Cs[1]? = some x) (hy : Fs[1]? = some y) :
    ∃ c', Det P [.list [sv, lv], rv, .list Cs, cv, .list Fs]
      (Expr.mkList [.get (.var 0) (.nat 0), .get (.var 2) (.nat 1), .var 3,
        .get (.var 4) (.nat 1), .var 1]) (.list [sv, x, cv, y, rv]) c' ∧
      c' ≤ 30 * ((Val.list [sv, lv]).wt + rv.wt + (Val.list Cs).wt + cv.wt + (Val.list Fs).wt)
        + 300 := by
  set K := 2 * ((Val.list [sv, lv]).wt + rv.wt + (Val.list Cs).wt + cv.wt + (Val.list Fs).wt)
    + 20 with hK
  have w1 : sv.wt < (Val.list [sv, lv]).wt := wt_le_wt_list (by simp)
  have w2 : x.wt < (Val.list Cs).wt := wt_le_wt_list (List.mem_of_getElem? hx)
  have w4 : y.wt < (Val.list Fs).wt := wt_le_wt_list (List.mem_of_getElem? hy)
  obtain ⟨c', h, hc'⟩ := rs_mk5 (c := K)
    ((rs_get (P := P) (env := [.list [sv, lv], rv, .list Cs, cv, .list Fs]) (i := 0) (j := 0)
      rfl rfl).mono (by omega))
    ((rs_get (P := P) (env := [.list [sv, lv], rv, .list Cs, cv, .list Fs]) (i := 2) (j := 1)
      rfl hx).mono (by omega))
    (colVar (P := P) (env := [.list [sv, lv], rv, .list Cs, cv, .list Fs]) (i := 3) rfl
      (by omega))
    ((rs_get (P := P) (env := [.list [sv, lv], rv, .list Cs, cv, .list Fs]) (i := 4) (j := 1)
      rfl hy).mono (by omega))
    (colVar (P := P) (env := [.list [sv, lv], rv, .list Cs, cv, .list Fs]) (i := 1) rfl
      (by omega))
  exact ⟨c', h, by omega⟩

/-- **The input of the terminal function**, built from the environment of the row step. -/
theorem rs_termIn_det {P : Program} {sv lv rv cv : Val} {Cs : List Val} (Fv : Val) :
    ∃ c', Det P [.list [sv, lv], rv, .list Cs, cv, Fv]
      (Expr.mkList [.get (.var 0) (.nat 0), .get (.var 0) (.nat 1), .var 3, .var 4, .var 1])
        (.list [sv, lv, cv, Fv, rv]) c' ∧
      c' ≤ 30 * ((Val.list [sv, lv]).wt + rv.wt + cv.wt + Fv.wt) + 300 := by
  set K := 2 * ((Val.list [sv, lv]).wt + rv.wt + cv.wt + Fv.wt) + 20 with hK
  have w1 : sv.wt < (Val.list [sv, lv]).wt := wt_le_wt_list (by simp)
  have w2 : lv.wt < (Val.list [sv, lv]).wt := wt_le_wt_list (by simp)
  obtain ⟨c', h, hc'⟩ := rs_mk5 (c := K)
    ((rs_get (P := P) (env := [.list [sv, lv], rv, .list Cs, cv, Fv]) (i := 0) (j := 0)
      rfl rfl).mono (by omega))
    ((rs_get (P := P) (env := [.list [sv, lv], rv, .list Cs, cv, Fv]) (i := 0) (j := 1)
      rfl rfl).mono (by omega))
    (colVar (P := P) (env := [.list [sv, lv], rv, .list Cs, cv, Fv]) (i := 3) rfl (by omega))
    (colVar (P := P) (env := [.list [sv, lv], rv, .list Cs, cv, Fv]) (i := 4) rfl (by omega))
    (colVar (P := P) (env := [.list [sv, lv], rv, .list Cs, cv, Fv]) (i := 1) rfl (by omega))
  exact ⟨c', h, by omega⟩

/-- The arithmetic of the cost of the row step. -/
theorem rs_arith {c1 c2 c3 c4 cc ca cb uw ctxw cvw v4w Aw rlw ca4 V B CCm CC ACm AC : ℕ}
    (h1 : c1 ≤ V) (h2 : c2 ≤ V) (hctx : ctxw ≤ V) (hB : B ≤ V) (hcv : cvw ≤ B)
    (hAw : Aw + rlw ≤ B) (hu : uw ≤ B) (h3 : c3 ≤ 4 * ctxw + 20 + CCm + cvw) (hCC : CCm ≤ CC)
    (h4 : c4 ≤ ca4 + 2 * ACm + 1) (hca4 : ca4 ≤ 100 * (ctxw + cvw) + 100) (hAC : ACm ≤ AC)
    (hv4 : v4w < ACm) (hcc : cc ≤ 2 * (v4w + 1) + (3 + 3) + 1)
    (hca : ca ≤ 30 * (Aw + rlw + ctxw + cvw + v4w) + 300) (hV : 1 ≤ V) :
    c1 + (c2 + (c3 + (c4 + (cc + (ca + cb + uw + 1) + uw + 1) + uw + 1) + uw + 1) + uw + 1) + uw + 1 ≤
      10000 * (V + CC + AC) + cb := by
  omega

theorem rs_ca_term {ca a b c d x : ℕ} (h : ca ≤ 30 * (a + b + c + d) + 300) :
    ca ≤ 30 * (a + b + x + c + d) + 300 := by omega

/-- Closing the cost bound of a branch of the row step. -/
theorem rs_close {X pre cb : ℕ} {own Wb ch : ℝ} (hX : X ≤ pre + cb) (hcb : (cb : ℝ) ≤ Wb + ch)
    (hW : Wb + pre ≤ own) : (X : ℝ) ≤ max 0 own + ch := by
  have h : (X : ℝ) ≤ pre + cb := by exact_mod_cast hX
  have := le_max_right 0 own
  linarith

/-! ### The row step -/

/-- **The body of the row step** on `[sv, lv]`: the row labels (`rowPartE`, natural-label
module at `bN`, map at `r`), the context (`rsCtxE`, ranges at `rng`), the coordinates (module
`cB`), the A.18 program (module `aB`), and the branch on `t`: the column branch (function
`colB`) when `t ≠ 0`, the terminal function `tB` when `t = 0`. -/
def rsBodyE (bN r rng cB aB colB tB : ℕ) : Expr :=
  .letE (rowPartE bN r)
  (.letE (rsCtxE rng)
  (.letE (.call cB (mk1 (.var 2)))
  (.letE (.call aB (mk4 (mk2 (.get (.var 2) (.nat 0)) (.get (.var 2) (.nat 1)))
      (.get (.var 2) (.nat 3)) (.var 3) (.var 1)))
  (.ite (.get (.var 4) (.nat 3))
    (.call colB (Expr.mkList [.get (.var 0) (.nat 0), .get (.var 2) (.nat 1), .var 3,
      .get (.var 4) (.nat 1), .var 1]))
    (.call tB (Expr.mkList [.get (.var 0) (.nat 0), .get (.var 0) (.nat 1), .var 3, .var 4,
      .var 1]))))))

/-- **Where the row step and its modules sit.** -/
structure RsAt (P : Program) (F : Funs) (hst : GI.Cited.PointwiseStab)
    (hfac : GI.Cited.NormalizedFactor) (f bN jpre r rng cB jp jf aB colB tB : ℕ) : Prop where
  main : P.funs[f]? = some (rsBodyE bN r rng cB aB colB tB)
  nat : NatAt P bN jpre
  part : P.HasAt r (rowPartFuns r)
  rng : P.HasAt rng (rangeFuns rng)
  coord : P.HasAt cB (coordFuns cB jp jf)
  pst : P.prims[jp]? = some (pointwiseStabPrim hst)
  fac : P.prims[jf]? = some (normalizedFactorPrim hfac)
  a18 : P.HasAt aB (a18Funs aB jp)
  col : ColBrAt P colB F.cont

/-- The bound on the weights of the input and of the row labels, in the phase size `N`. -/
def rsB (N : ℕ) : ℕ := 10 ^ 5 * (N + 2) ^ 6

/-- The bound on the cost of the simple steps. -/
def rsV (N : ℕ) : ℕ := 10 ^ 15 * (rsB N + 2) ^ 4

/-- **The cost of the row step before the branch call**, in the phase size `N`: the simple
steps, the coordinates and the A.18 program. -/
noncomputable def rsPre (hst : GI.Cited.PointwiseStab) (hfac : GI.Cited.NormalizedFactor)
    (N : ℕ) : ℕ :=
  10 ^ 4 * (rsV N + coordCost hst hfac (rsB N) + a18Cost hst (rsB N))

theorem rsB_le_rsV (N : ℕ) : rsB N ≤ rsV N ∧ 10 ^ 8 * (rsB N + 1) ^ 3 ≤ rsV N ∧
    2 * rowPartK * (rsB N + 2) ^ 4 ≤ rsV N := by
  unfold rsV rowPartK
  have h1 : rsB N + 1 ≤ (rsB N + 2) ^ 4 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by norm_num) _)
  have h2 : (rsB N + 1) ^ 3 ≤ (rsB N + 2) ^ 4 :=
    (Nat.pow_le_pow_left (Nat.le_succ _) 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
  generalize (rsB N + 2) ^ 4 = x at *
  generalize (rsB N + 1) ^ 3 = y at *
  omega

theorem rs_coordCost_mono (hst : GI.Cited.PointwiseStab) (hfac : GI.Cited.NormalizedFactor)
    {a b : ℕ} (h : a ≤ b) : coordCost hst hfac a ≤ coordCost hst hfac b := by
  unfold coordCost rowStepCost liftWinCost
  have := liftLabCost_mono (normalizedFactorPrim hfac)
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h 2))
  gcongr

theorem rs_a18Cost_mono (hst : GI.Cited.PointwiseStab) {a b : ℕ} (h : a ≤ b) :
    a18Cost hst a ≤ a18Cost hst b := by
  unfold a18Cost rowKerCost
  gcongr

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

/-- **The work that the row step needs**: at a `rowTerminal` node the terminal work `Wt` plus
`rsPre`, at a `rowColumns` node `colBrPoly + rsPre`. -/
def RowW (hst : GI.Cited.PointwiseStab) (hfac : GI.Cited.NormalizedFactor)
    (Wt : Node P₀ → ℝ) : Prop :=
  ∀ nd : Node P₀, (nd.run.kind = .rowTerminal → Wt nd + rsPre hst hfac nd.S.N ≤ I.W nd) ∧
    (nd.run.kind = .rowColumns → ((colBrPoly nd.S.N + rsPre hst hfac nd.S.N : ℕ) : ℝ) ≤ I.W nd)

set_option maxHeartbeats 4000000 in
/-- **The row step meets its specification** (`Iface.RowSpec`), given the specification of the
terminal function (`RowTermSpec`) and the work bound `RowW`. Cited:
`PointwiseStab` and `NormalizedFactor` (primitives at `jp`, `jf`),
`Preimage` (through the natural-label module `NatAt`). -/
theorem rowSpec (hst : GI.Cited.PointwiseStab)
    (hfac : GI.Cited.NormalizedFactor)
    (hLab : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (lv : Val)
      (L : SuppliedLabels S), I.LabVal e S lv L → LabValStd e S lv L)
    {f bN jpre r rng cB jp jf aB colB tB : ℕ}
    (hA : RsAt Pg F hst hfac f bN jpre r rng cB jp jf aB colB tB) {Wt : Node P₀ → ℝ}
    (hT : I.RowTermSpec Pg F Wt tB) (hW : I.RowW hst hfac Wt) : I.RowSpec Pg F f := by
  intro Ω C S k e c hc v hv hg hcase ih
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨sv, lv, L, rfl, hsv, hL, hq0, -⟩ := hv
  obtain ⟨sv', lv', L', hv', hL', hrow⟩ := hcase
  simp only [Val.list.injEq, List.cons.injEq, and_true] at hv'
  obtain ⟨rfl, rfl⟩ := hv'
  have hlv := hLab e S lv L hL
  cases LabValStd.unique (hLab e S lv L' hL') hlv
  have hlv0 := hlv
  obtain ⟨ps, hlvE, hpsl, hgen, hπ⟩ := hlv0
  have hps : PairGens e L.toGiantLabels S.G ps := rsPairGens hgen hπ
  obtain ⟨label, hnat⟩ := hrow.2.1
  have hq : 5 ≤ L.q := by
    have h : P₀.q₀ = 2064 := rfl
    omega
  have hgood := hg
  obtain ⟨hN0, hsN, htr, hth, hhi, -⟩ := hg
  have hsmall := hsv.small'
  have hkN : k ≤ S.N := hsv.fits
  have hqk : L.q ≤ k + 2 := GiantLabels.q_le e L.toGiantLabels
  -- the row labels as a list
  set rlL := (List.finRange k).map (rowLab e L.con.blocks) with hrlL
  have hrlE : encFun (rowLab e L.con.blocks) = natList rlL := GI.Lang.encFun_eq_natList _
  have hRL : RowLabs e S label rlL := by
    refine ⟨by simp [hrlL], fun i => ?_⟩
    rw [List.getD_eq_getElem _ _ (by simp [hrlL])]
    simp only [hrlL, List.getElem_map, List.getElem_finRange]
    split_ifs with hi
    · exact colRowLab_dom e L.con.blocks hq hnat _ hi
    · exact rowLab_off e L.con.blocks hi
  -- weights
  set P := S.N + 2 with hPdef
  have p26 : P ^ 2 ≤ P ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p46 : P ^ 4 ≤ P ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p16 : P ≤ P ^ 6 := Nat.le_self_pow (by norm_num) _
  have wsv : sv.wt ≤ 10 ^ 4 * P ^ 6 := hsv.wt_le_poly
  have wlv : lv.wt ≤ labWStd k S.N := hlv.wt_le hsmall.1
  have wlv' : lv.wt ≤ 2200 * P ^ 6 := by
    have := Nat.pow_le_pow_left (show k + 1 ≤ P by omega) 4
    unfold labWStd at wlv
    omega
  have wA := wt_list2_le sv lv
  have wrl : (natList rlL).wt ≤ 20 * P ^ 6 := by
    rw [← hrlE]
    have h1 : (encFun (rowLab e L.con.blocks)).wt ≤ 5 * (k + L.q + 1) ^ 2 :=
      wt_encFun_le' _ (fun i => (colRowLab_le e _ i).trans (by omega)) (by omega)
    have h2 := Nat.pow_le_pow_left (show k + L.q + 1 ≤ 2 * P by omega) 2
    have h3 : (2 * P) ^ 2 = 4 * P ^ 2 := by ring
    omega
  have hB : (Val.list [sv, lv]).wt + (natList rlL).wt + k + L.q ≤ rsB S.N := by
    unfold rsB; rw [← hPdef]; omega
  -- the value forms
  obtain ⟨gv, dv, xv, yv, hv, rv, -, -, -, -, -, -, hsvE⟩ := hsv.val
  have hlvE' : lv = .list [.nat L.q, .list (ps.map pairV), .nat L.sel,
      .nat L.con.blocks.h, .nat L.con.blocks.f, blkMapVal e L.con.blocks] := hlvE
  -- step 1: the row labels
  have d1 := rowPart_det (sv := sv) hA.nat hA.part e L hlv (by omega) []
  rw [hrlE] at d1
  refine FunAll.intro hA.main (EvalAll.letE d1 fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- step 2: the context
  have d2 := rsCtx_det (P := Pg) hA.rng ps rlL (svs := [.nat k, gv, dv, xv, yv, hv, rv,
    boolVal S.floor, .nat S.h, .nat S.N]) (lvs := [.nat L.q, .list (ps.map pairV), .nat L.sel,
      .nat L.con.blocks.h, .nat L.con.blocks.f, blkMapVal e L.con.blocks]) rfl rfl rfl
    (B := rsB S.N) (by rw [← hsvE, ← hlvE']; exact hB)
  rw [← hsvE, ← hlvE'] at d2
  refine EvalAll.letE d2 fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  have wctx := d2.wt_lt
  -- step 3: the coordinates
  have hco := coords_spec_good hst hfac hgood hrow hA.coord hA.pst hA.fac hps hRL hnat
  have dm := Det.mk1 (Det.var' (P := Pg) (env := [Val.list [sv, lv], natList rlL, winCtx k L.q rlL ps]) (i := 2) (v := winCtx k L.q rlL ps) rfl)
  have wm := wt_list1_le (winCtx k L.q rlL ps)
  have e3 : EvalAll Pg [Val.list [sv, lv], natList rlL, winCtx k L.q rlL ps] (.call cB (mk1 (.var 2)))
      (fun w c => ∃ E : Fin (zeroPts rlL k).length × Fin L.q ≃ S.dom,
        PureCoords S L.toGiantLabels label E ∧ w = coordsVal e S E ∧
        c ≤ 4 * (winCtx k L.q rlL ps).wt + 20 + coordCost hst hfac (k + L.q + ps.length + 2) + w.wt) :=
    EvalAll.call_funAll dm fun v ca h => by
      obtain ⟨rfl, hca⟩ := h
      exact hco.mono fun w cb ⟨E, hP, hw, hcb⟩ => ⟨E, hP, hw, by omega⟩
  refine EvalAll.letE e3 fun v3 c3 h3 => ?_
  obtain ⟨E, hP, rfl, hc3⟩ := h3
  have hq1 : 0 < L.q := by omega
  have hsize : S.size = (zeroPts rlL k).length * L.q := by
    unfold State.size
    rw [← Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  have h0 : 0 < (zeroPts rlL k).length := by
    have := size_pos_of_large hth
    rcases Nat.eq_zero_or_pos (zeroPts rlL k).length with h | h
    · rw [h] at hsize; omega
    · exact h
  have wco : (coordsVal e S E).wt ≤ 15 * (k + L.q + 2) ^ 3 + 4 := wt_coordsVal_le E
  -- step 4: the A.18 program
  have ha := a18_spec hst E hnat hq hP ⟨0, h0⟩ hA.a18 hA.pst hps hRL
  obtain ⟨ca4, da, hca4⟩ := rs_a18In_det (P := Pg) (Val.list [sv, lv]) (coordsVal e S E) rlL ps
  have e4 : EvalAll Pg [Val.list [sv, lv], natList rlL, winCtx k L.q rlL ps, coordsVal e S E]
      (.call aB (mk4 (mk2 (.get (.var 2) (.nat 0)) (.get (.var 2) (.nat 1)))
        (.get (.var 2) (.nat 3)) (.var 3) (.var 1)))
      (fun w c => ∃ (σH σN σS : List (Perm (Fin (zeroPts rlL k).length))) (t : ℕ), w = a18Out σH σN σS t ∧
        σH.length ≤ (k + L.q) ^ 2 ∧ σN.length ≤ (k + L.q) ^ 2 ∧ σS.length ≤ (k + L.q) ^ 2 ∧
        Subgroup.closure {σ | σ ∈ σH} = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb ∧
        Subgroup.closure {σ | σ ∈ σN} = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb ∧
        Subgroup.closure {σ | σ ∈ σS} = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
          (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype ∧
        (t = 0 ↔ MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
          (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B) ∧
        w.wt < a18Cost hst (pM k L.q ps) ∧ c ≤ ca4 + 2 * a18Cost hst (pM k L.q ps) + 1) :=
    EvalAll.call_funAll da fun v ca h => by
      obtain ⟨rfl, hca⟩ := h
      exact ha.wt_lt.mono fun w cb ⟨⟨σH, σN, σS, t, hw, l1, l2, l3, g1, g2, g3, gt, hcb⟩, hwt⟩ =>
        ⟨σH, σN, σS, t, hw, l1, l2, l3, g1, g2, g3, gt, by omega, by omega⟩
  refine EvalAll.letE e4 fun v4 c4 h4 => ?_
  obtain ⟨σH, σN, σS, t, rfl, l1, l2, l3, g1, g2, g3, gt, wv4, hc4⟩ := h4
  -- step 5: the branch on `t`
  have dc := rs_get (P := Pg) (env := [Val.list [sv, lv], natList rlL, winCtx k L.q rlL ps,
    coordsVal e S E, a18Out σH σN σS t]) (i := 4) (j := 3)
    (vs := [.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm), .nat t])
    rfl rfl
  refine EvalAll.ite dc (fun _ _ h => ⟨t, h.1⟩) fun x cc hx => ?_
  obtain ⟨hx1, hcc⟩ := hx
  cases hx1
  -- bounds shared by both branches
  have hBV := rsB_le_rsV S.N
  have hc1' : c1 ≤ rsV S.N := by
    refine hc1.trans (le_trans ?_ hBV.2.2)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have hc2' : c2 ≤ rsV S.N := by
    refine hc2.trans (le_trans ?_ hBV.2.1)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have hctx' : (winCtx k L.q rlL ps).wt ≤ rsV S.N := by
    have := hBV.2.1; have := d2.wt_lt; omega
  have hM : k + L.q + ps.length + 2 ≤ rsB S.N := by
    have := Nat.pow_le_pow_left hkN 2
    have := Nat.pow_le_pow_left (show S.N ≤ P by omega) 2
    unfold rsB; rw [← hPdef]; omega
  have hCC := rs_coordCost_mono hst hfac hM
  have hAC := rs_a18Cost_mono hst (show pM k L.q ps ≤ rsB S.N from hM)
  have hcv : (coordsVal e S E).wt ≤ rsB S.N := by
    have := Nat.pow_le_pow_left (show k + L.q + 2 ≤ 2 * P by omega) 3
    have h3 : (2 * P) ^ 3 = 8 * P ^ 3 := by ring
    have : P ^ 3 ≤ P ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    unfold rsB; rw [← hPdef]; omega
  have hAw : (Val.list [sv, lv]).wt + (natList rlL).wt ≤ rsB S.N := by omega
  have hV1 : 1 ≤ rsV S.N := le_trans (Nat.one_le_pow _ _ (by omega))
    (le_trans (Nat.le_mul_of_pos_left _ (by unfold rowPartK; norm_num)) hBV.2.2)
  have hpre : rsPre hst hfac S.N = 10000 * (rsV S.N + coordCost hst hfac (rsB S.N) +
      a18Cost hst (rsB S.N)) := by unfold rsPre; norm_num
  have hcc' : cc ≤ 2 * ((a18Out σH σN σS t).wt + 1) + (3 + 3) + 1 := hcc
  have hu6 : 1000 * (S.N + 2) ^ 6 ≤ rsB S.N := by unfold rsB; omega
  simp only [List.cons_append, List.nil_append]
  by_cases ht : t = 0
  · -- the terminal branch
    rw [if_pos ht]
    obtain ⟨ca5, d5, hca5⟩ := rs_termIn_det (P := Pg) (sv := sv) (lv := lv) (rv := natList rlL)
      (cv := coordsVal e S E) (Cs := [Val.nat k, .nat L.q, natList rlL, .list (ps.map pairV),
        pSplitCtx k L.q, encPerm (1 : Perm (Fin L.q)), encPerm (1 : Perm (Fin k))])
      (a18Out σH σN σS t)
    have hT' := hT S k e c hc sv lv L hsv hlv hq0 hgood hrow ih label hnat hq h0 E hP σH σN σS t
      g1 g2 g3 ht (gt.mp ht) l1 l2 l3
    rw [hrlE] at hT'
    refine EvalAll.call_funAll d5 fun v ca h => ?_
    obtain ⟨rfl, hca⟩ := h
    refine hT'.mono fun u cb ⟨Aset, rr, hk, hans, hcb⟩ => ?_
    refine ⟨Aset, some L, rr, ⟨sv, lv, L, rfl, hL, rfl⟩, by rw [hk]; simp, hans, ?_⟩
    have hu : u.wt ≤ 1000 * (S.N + 2) ^ 6 := hans.wt_le.trans (ansW_le_N hkN)
    have hX := rs_arith (cb := cb) (uw := u.wt) hc1' hc2' hctx' hBV.1 hcv hAw (hu.trans hu6) hc3
      hCC hc4 hca4 hAC wv4 hcc' (show ca ≤ 30 * ((Val.list [sv, lv]).wt + (natList rlL).wt +
        (winCtx k L.q rlL ps).wt + (coordsVal e S E).wt + (a18Out σH σN σS t).wt) + 300 from
        rs_ca_term (hca.trans hca5))
      hV1
    rw [← hpre] at hX
    have hWn := (hW rr.node).1 hk
    simp only [Iface.own, reduceCtorEq, if_false]
    exact rs_close hX hcb hWn
  · -- the column branch
    rw [if_neg ht]
    obtain ⟨ca5, d5, hca5⟩ := rs_colIn_det (P := Pg) (sv := sv) (lv := lv) (rv := natList rlL)
      (cv := coordsVal e S E) (Cs := [Val.nat k, .nat L.q, natList rlL, .list (ps.map pairV),
        pSplitCtx k L.q, encPerm (1 : Perm (Fin L.q)), encPerm (1 : Perm (Fin k))])
      (Fs := [.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm), .nat t])
      rfl rfl
    have hC := colBr_spec I Pg F hA.col S k e c hc sv L hsv hgood hrow ih label hnat hq h0 E hP σN
      g2 (fun h => ht (gt.mpr h)) l2
    have hin : colBrIn sv L.q (colRowsR e S E) σN (rowLab e L.con.blocks) =
        .list [sv, .nat L.q, coordsVal e S E, .list (σN.map encPerm), natList rlL] := by
      rw [colCoordsVal_eq, ← hrlE]; rfl
    rw [hin] at hC
    refine EvalAll.call_funAll d5 fun v ca h => ?_
    obtain ⟨rfl, hca⟩ := h
    refine hC.mono fun u cb ⟨Aset, rr, hk, hans, hcb⟩ => ?_
    refine ⟨Aset, some L, rr, ⟨sv, lv, L, rfl, hL, rfl⟩, by rw [hk]; simp, hans, ?_⟩
    have hu : u.wt ≤ 1000 * (S.N + 2) ^ 6 := hans.wt_le.trans (ansW_le_N hkN)
    have hX := rs_arith (cb := cb) (uw := u.wt) hc1' hc2' hctx' hBV.1 hcv hAw (hu.trans hu6) hc3
      hCC hc4 hca4 hAC wv4 hcc' (show ca ≤ 30 * ((Val.list [sv, lv]).wt + (natList rlL).wt +
        (winCtx k L.q rlL ps).wt + (coordsVal e S E).wt + (a18Out σH σN σS t).wt) + 300 from
        hca.trans hca5)
      hV1
    rw [← hpre] at hX
    have hWn := (hW rr.node).2 hk
    simp only [Iface.own, reduceCtorEq, if_false]
    refine rs_close hX hcb ?_
    have : ((colBrPoly S.N + rsPre hst hfac S.N : ℕ) : ℝ) ≤ I.W rr.node := hWn
    push_cast at this
    exact this

end Iface

end GI.Impl
