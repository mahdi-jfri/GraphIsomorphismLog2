import Workspace.Impl.TermGlueLabNDef
import Workspace.Impl.TermGlueLabPLiftS
import Workspace.Impl.TermGlueLabPXLab
import Workspace.Impl.TermGlueLabPYLab
import Workspace.Impl.TermGlueLabPSup
import Workspace.Impl.TermGlueLabPTop
import Workspace.Impl.TermGlueLabPBs

/-!
# The driver of the label program: the program and the contracts of its callees

Proof of Theorem A.23, the nonempty case of the label step. The driver
`tmGLNeF` runs on the input of `Iface.TmGLPNeSpec`,
`[[[sv, lv, rows, a18Out σH σN σS 0, rowLab], us, vs], r, [τ, U]]`, and chains the steps of
the paper's label program:

1. the group values `gens N` and `gens N*` (`mkGroup`);
2. the lift context (`tmGLPLc_spec`, the label kernel in graph form) and one lift of `τ`
   (`tmGLPL1_spec`), a blockwise `y` with `y i0 = τ`;
3. the labels of `x` from the `N`-test table (`tmGLPXLab_spec`) and of `y' = y^{k(τ)⁻¹}` from
   the coset table (`tmGLPYLab_spec`, with the lift of `τ`);
4. step 4: the supplement `S` of `N` in `D ⊓ R` (`tmGLPSup_spec`, T4);
5. the stabilizer generators `b_j` (from the `us` table) and step 5 (the context
   `[t, U, V, d]` and the items `[M(ρ g), c g, M(ρ g⁻¹), c g⁻¹]`);
6. the two vectors `E(p_{y'})`, `E(p_x)` and step 6 (the affine call and the answer).

Every callee sits at an index given as a parameter. Its contract is a `Prop` below
(`TmGLN…OK`), stated with a cost bound `F B` for inputs of weight at most `B`. The contracts
of the finished pieces have the result forms of their specs; the contracts of the pieces in
progress (`TmGLNBsOK`, `TmGLNS5OK`, `TmGLNVecOK`) have the forms that step 6 reads
(`TermGlueLabNDef.lean`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Lang GI.Paper Equiv
open GI.Cited (Val encPerm encGroup encIntMatrix gens GensOf)
open scoped Pointwise

attribute [local instance] stringRAct

/-! ### The program -/

/-- The entry `[sv, lv, rows, a18, rowLab]` of the input. -/
def tmGLNV0 : Expr := .get (arg 0) (.nat 0)
/-- The label value `lv`. -/
def tmGLNLv : Expr := .get tmGLNV0 (.nat 1)
/-- The number `q` of rows. -/
def tmGLNQ : Expr := .get tmGLNLv (.nat 0)
/-- The coordinates `rows`. -/
def tmGLNCo : Expr := .get tmGLNV0 (.nat 2)
/-- The output of Theorem A.18. -/
def tmGLNA18 : Expr := .get tmGLNV0 (.nat 3)
/-- The residual element `τ`. -/
def tmGLNTau : Expr := .get (arg 2) (.nat 0)
/-- The block size `m`, read from `encGroup U`. -/
def tmGLNM : Expr := .get (.get (arg 2) (.nat 1)) (.nat 0)

/-- **The driver** of the nonempty label part. The environment after the `j`-th `letE` holds
`v_j` at `.var j`: `v1 = gens N`, `v2 = gens N*`, `v3` the lift context, `v4` the lift of
`τ`, `v5` the labels of `x`, `v6` the labels of `y'`, `v7` the generators of `S`, `v8` the
`b_j`, `v9` the step-5 output, `v10 = [E(p_{y'}), E(p_x)]`. Step 6 (at `s6`) gets
`[gens N, τ, gens S, step 5, E(p_{y'}), E(p_x)]`. -/
def tmGLNeF (mg lc xlab ylab sup bsb s5 vec s6 : ℕ) : Expr :=
  .letE (.call mg (mk2 tmGLNM (.get tmGLNA18 (.nat 1))))
  (.letE (.call mg (mk2 tmGLNM (.get tmGLNA18 (.nat 2))))
  (.letE (.call lc (mk3 (mk2 (.get (.get tmGLNV0 (.nat 0)) (.nat 0)) tmGLNQ)
      (.get tmGLNLv (.nat 1)) (.get tmGLNCo (.nat 0))))
  (.letE (.call (lc + 1) (mk2 (mk2 (.var 3) tmGLNCo) tmGLNTau))
  (.letE (.call xlab (mk2 (.get (arg 0) (.nat 1)) tmGLNQ))
  (.letE (.call ylab (mk4 (.var 1) (.get (arg 0) (.nat 2)) tmGLNQ (.var 4)))
  (.letE (.call sup (mk2 (.var 1) (arg 2)))
  (.letE (.call bsb (mk2 (.get (arg 0) (.nat 1)) tmGLNQ))
  (.letE (.call s5 (mk4 (mk3 (.var 2) (.var 1) (.var 8))
      (mk4 (.var 1) (.get (arg 0) (.nat 2)) tmGLNQ (.var 5)) (mk2 (.var 3) tmGLNCo) (.var 7)))
  (.letE (.call vec (mk4 (.var 9) (.var 1) (.var 5) (.var 6)))
    (.call s6 (Expr.mkList [.var 1, tmGLNTau, .var 7, .var 9, .get (.var 10) (.nat 0),
      .get (.var 10) (.nat 1)])))))))))))

/-! ### Contracts of the finished callees -/

namespace Iface

/-- `mkGroup` at `mg`. -/
def TmGLNMkOK (P : Program) (mg : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} (hs : List (Perm (Fin n))) (B : ℕ),
    (Val.list [.nat n, .list (hs.map encPerm)]).wt ≤ B → n ≤ B →
    FunAll P mg (.list [.nat n, .list (hs.map encPerm)]) (fun w c => w = encGroup hs ∧ c ≤ F B)

/-- The lift context at `lc` (`tmGLPLc_spec`). -/
def TmGLNLcOK (P : Program) (lc : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ {Ω C : Type} {n : ℕ} (e : Ω ≃ Fin n) {S : State Ω C} {L : GiantLabels S}
    {label : Ω → Fin L.q} {m : ℕ} (E : Fin m × Fin L.q ≃ S.dom) (hnat : NaturalRows S L label)
    (hE : ∀ b i, label (E (b, i)) = i) (i0 : Fin L.q)
    {ps : List (Perm (Fin n) × Perm (Fin L.q))}, PairGens e L S.G ps → ∀ B : ℕ,
    (Val.list [.list [.nat n, .nat L.q], .list (ps.map pairV),
      natList ((rowList e E i0).map Fin.val)]).wt ≤ B → n ≤ B → L.q ≤ B →
    FunAll P lc (.list [.list [.nat n, .nat L.q], .list (ps.map pairV),
        natList ((rowList e E i0).map Fin.val)])
      (fun w c => ∃ ps' : List (Perm (Fin n) × Perm (Fin m)), w = liftLabCtx n m ps' ∧
        Subgroup.closure {p | p ∈ ps'} = (tmGLPχ e E hnat hE i0).range ∧
        ps'.length ≤ (n + L.q) ^ 2 ∧ c ≤ F B)

/-- One lift at `l1` (`tmGLPL1_spec`). -/
def TmGLNL1OK (P : Program) (l1 : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ {Ω C : Type} {n : ℕ} (e : Ω ≃ Fin n) {S : State Ω C} {L : GiantLabels S}
    {label : Ω → Fin L.q} {m : ℕ} (E : Fin m × Fin L.q ≃ S.dom) (hnat : NaturalRows S L label)
    (hE : ∀ b i, label (E (b, i)) = i) (i0 : Fin L.q)
    {ps' : List (Perm (Fin n) × Perm (Fin m))},
    Subgroup.closure {p | p ∈ ps'} = (tmGLPχ e E hnat hE i0).range →
    ∀ {s : Perm (Fin m)}, (∃ y : Fin L.q → Perm (Fin m), cleanRowPerm E y ∈ S.domGroup ∧ y i0 = s) →
    ∀ B : ℕ, (Val.list [.list [liftLabCtx n m ps', coordsVal e S E], encPerm s]).wt ≤ B →
    n ≤ B → L.q ≤ B →
    FunAll P l1 (.list [.list [liftLabCtx n m ps', coordsVal e S E], encPerm s])
      (fun w c => ∃ y : Fin L.q → Perm (Fin m),
        w = .list ((List.finRange L.q).map fun i => encPerm (y i)) ∧
        cleanRowPerm E y ∈ S.domGroup ∧ y i0 = s ∧ c ≤ F B)

/-- The labels of `x` at `xl` (`tmGLPXLab_spec`). -/
def TmGLNXOK (P : Program) (xl : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] (N : Subgroup (Perm (Fin n))) {q : ℕ}
    (X : Fin q → Ω) {us : List Val}, TmGLPTestOK N X us → ∀ B : ℕ,
    (Val.list [.list us, .nat q]).wt ≤ B →
    FunAll P xl (.list [.list us, .nat q]) (fun u c => TmGLPXOut N X u ∧ c ≤ F B)

/-- The labels of `y'` at `yl` (`tmGLPYLab_spec`). -/
def TmGLNYOK (P : Program) (yl : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {H : Subgroup (Perm (Fin n))}
    {σN : List (Perm (Fin n))}, gens σN ≤ H → GI.Multicoset.Normalizes H (gens σN) →
    ∀ {q : ℕ} {X Y : Fin q → Ω} {vs : List Val}, TmCsTabOK H X Y vs →
    ∀ {ks : Fin q → Perm (Fin n)}, (∀ i, ks i ∈ H) →
    ∀ {Z : Fin q → Ω}, (∀ i, Z i ↼ ks i = Y i) → ∀ B : ℕ, (tmGLPYIn σN vs ks).wt ≤ B →
    FunAll P yl (tmGLPYIn σN vs ks) (fun u c => TmGLPYOut (gens σN) X Z u ∧ c ≤ F B)

/-- Step 4 at `sup` (`tmGLPSup_spec`). -/
def TmGLNSupOK (P : Program) (sup : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} {σN U : List (Perm (Fin n))}, U.length ≤ n ^ 2 → ∀ τ : Perm (Fin n),
    gens σN ≤ gens (U.map fun x => τ * x * τ⁻¹) →
    ∀ [((gens σN).subgroupOf (gens (U.map fun x => τ * x * τ⁻¹))).Normal],
    IsSolvable ((gens (U.map fun x => τ * x * τ⁻¹)) ⧸
      (gens σN).subgroupOf (gens (U.map fun x => τ * x * τ⁻¹))) →
    ∀ B : ℕ, (Val.list [encGroup σN, .list [encPerm τ, encGroup U]]).wt ≤ B →
    FunAll P sup (.list [encGroup σN, .list [encPerm τ, encGroup U]]) (fun u c =>
      ∃ S : Subgroup (Perm (Fin n)), GensOf S u ∧
        S ≤ gens (U.map fun x => τ * x * τ⁻¹) ∧ IsSolvable S ∧
        S ⊔ gens σN = gens (U.map fun x => τ * x * τ⁻¹) ∧ c ≤ F B)

/-! ### Contracts of the callees in progress -/

/-- **The stabilizer generators** at `bsb`, on `[us, q]` (`tmGLPBs_spec`: entry
`i + 2qi` of the `N`-test table is `Aut_N(x_i)`; take its generators for all `i`). The result
`TmGLPBsOut` is the hypothesis `hbs` of `tmGLP_step5_s5`. -/
def TmGLNBsOK (P : Program) (bsb : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] (N : Subgroup (Perm (Fin n))) {q : ℕ}
    (X : Fin q → Ω) {us : List Val}, TmGLPTestOK N X us → ∀ B : ℕ,
    (Val.list [.list us, .nat q]).wt ≤ B →
    FunAll P bsb (.list [.list us, .nat q]) (fun u c =>
      ∃ bs : List (Perm (Fin n)), u = .list (bs.map encPerm) ∧ TmGLPBsOut N X bs ∧ c ≤ F B)

/-- **Step 5** at `s5` (`tmGLPStep5_spec` when some type repeats, its orientation
variant when all types are distinct, and the case `t = 0`). The input is `tmGLPStep5In`
with the lift context, the labels of `x` and the generators of the supplement. -/
def TmGLNS5OK (P : Program) (s5 : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ {Ω C : Type} {Pp : Params} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}
    (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
    (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
    (hqα : (S.N : ℝ) ^ Pp.α < L.q) {k : ℕ} (e : Ω ≃ Fin k)
    (σS σN bs gs : List (Perm (Fin m))) (vs xl : List Val)
    (ps' : List (Perm (Fin k) × Perm (Fin m))),
    gens σN = (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Nb →
    gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype →
    TmGLPBsOut (gens σN) (fun i => tmRowStr S E (.inl i)) bs →
    TmCsTabOK (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Hb
      (fun i => tmRowStr S E (.inl i)) (fun j => tmRowStr S E (.inr j)) vs →
    (∀ j : Fin L.q, ∃ l : Fin L.q, (GI.Multicoset.Iso
      (@id (Subgroup (Perm (Fin m))) (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Hb)
      (tmRowStr S E (.inl j)) (tmRowStr S E (.inr l))).Nonempty) →
    TmGLPXOut (gens σN) (fun i => tmRowStr S E (.inl i)) (.list xl) →
    Subgroup.closure {p | p ∈ ps'} =
      (tmGLPχ e E hnat (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).e_label ⟨0, by omega⟩).range →
    gs.length ≤ m ^ 2 →
    gens gs ⊔ gens σN = Aut (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Hb
      (types (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Nb
        (rowTuple (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).e S.x)) ⊓
      tmRad (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα) →
    ∀ B : ℕ, (tmGLPStep5In σS σN bs vs L.q xl (.list [liftLabCtx k m ps', coordsVal e S E])
      gs).wt ≤ B →
    FunAll P s5 (tmGLPStep5In σS σN bs vs L.q xl (.list [liftLabCtx k m ps', coordsVal e S E]) gs)
      (fun o c => TmGLNS5Res hnat hq h0 E hP htr hcard hsN hN hqα σN gs o ∧ c ≤ F B)

/-- **The vector program** at `vec`, on `[step 5, gens N, labels of x, labels of y']`
(`tmGLS_lab_vec`, `tmGLS_pt_vec`). `y` is the lift of `τ` that the labels of `y'` used:
row `i` of `y'` is `y_i^{(y i)⁻¹}`. -/
def TmGLNVecOK (P : Program) (vec : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ {Ω C : Type} {Pp : Params} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}
    (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
    (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
    (hqα : (S.N : ℝ) ^ Pp.α < L.q) (σN gs : List (Perm (Fin m))) (r τ : Perm (Fin m))
    (y : Fin L.q → Perm (Fin m)) (U V D : Matrix (Fin σN.length) (Fin σN.length) ℤ)
    (o5 xl yl : Val),
    gens σN = (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Nb →
    τ ∈ tmGlRes (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα) r →
    cleanRowPerm E y ∈ S.domGroup → y ⟨0, by omega⟩ = τ →
    (∃ hgs ws, TmGLNS5At hnat hq h0 E hP htr hcard hsN hN hqα σN gs hgs U V D ws o5) →
    TmGLPXOut (gens σN) (fun i => tmRowStr S E (.inl i)) xl →
    TmGLPYOut (gens σN) (fun i => tmRowStr S E (.inl i))
      (fun i => tmRowStr S E (.inr i) ↼ (y i)⁻¹) yl →
    ∀ B : ℕ, (Val.list [o5, encGroup σN, xl, yl]).wt ≤ B →
    FunAll P vec (.list [o5, encGroup σN, xl, yl]) (fun u c => ∃ vv ww : Val,
      u = .list [vv, ww] ∧ TmGLNVecRes hnat hq h0 E hP htr hcard hsN hN hqα σN τ V D vv ww ∧
      c ≤ F B)

end Iface

/-- **The stabilizer generators meet their contract** (`tmGLPBs_spec`). -/
theorem tmGLN_bs_ok {P : Program} {b : ℕ} (h : P.HasAt b (tmGLPBsFuns b)) :
    Iface.TmGLNBsOK P b tmGLPBsC := by
  intro n Ω _ N q X us hT B hB
  refine (tmGLPBs_spec h hT).mono fun w c ⟨bs, hw, hbs, hc⟩ => ⟨bs, hw, hbs, ?_⟩
  exact hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))

end GI.Impl
