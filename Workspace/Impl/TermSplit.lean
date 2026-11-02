import Workspace.Impl.TermSplitMath
import Workspace.Impl.TermSplitCost
import Workspace.RadicalIndex

/-!
# T7 from the radical cosets: the split of `TermDomSpec`

Corollary A.22: "enumerate the radical cosets, solve each by Theorem A.20". Theorem A.23 then
keeps above each residual element the `J`-elements that pass the label test, and returns the
union. This file reduces `Iface.TermDomSpec` (the table transport on the domain positions, as
one coset) to two hypotheses that follow the paper's steps:

* `Iface.TermRepsSpec` (T2, T3): a list of right coset representatives of the radical preimage
  `R` in `H`, one per coset (`[H : R]` of them);
* `Iface.TermCosetSpec` (T4–T6): for a representative `r ∈ H`, a canonical answer on the domain
  positions of the piece `tmCosetT ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα) r` of the table transport above `R r`.

The function `tmSplitBody`: the representatives; the identity on the `s` domain positions
(`range`); the map of `tmPieceF` (the piece `[1, answer of r]`) over the representatives; and
`CombineExact` (`ce_spec`, cited **Membership**), which turns the union of the pieces into one
canonical coset (T7's "compressed to generators and one representative"). The union is the
whole table transport (`tm_exactT_eq_iUnion`) and is empty or a coset
(`tm_domSet_cosetOrEmpty`).

Cost: `[H : R] ≤ b^{2 log₂ b}` calls of the piece function ([GMP, Theorem 1.4] and Lemma A.21,
`radical_index_le`, cited `GMPAbelianFactors`, `GMPOutBound`, `GMPTransitiveNonabelian`) and a
polynomial in the weight of the pieces, all within `expLogSq`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Membership)
open scoped Pointwise

namespace Iface

variable (Pg : Program)

/-- **The radical coset representatives** (T2, T3; Corollary A.22: "enumerate the radical
cosets"): on the input of `TermAsmSpec`, a list of right coset representatives `r ∈ H` of the
radical preimage `R`, one for each coset (so `[H : R]` of them), at cost at most `expLogSq A N`. -/
def TermRepsSpec (A : ℝ) (g : ℕ) : Prop :=
  ∀ {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
    Function.Injective c →
    ∀ (sv lv : Val) (L : SuppliedLabels S), Canon e c sv S → LabValStd e S lv L →
    P₀.q₀ < L.q → Good P₀ .giant S → RowCase P₀.α S L.toGiantLabels →
    ∀ (label : Ω → Fin L.q) (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q)
      {m : ℕ} (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom)
      (hP : PureCoords S L.toGiantLabels label E)
      (σH σN σS : List (Perm (Fin m))),
      gens σH = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb →
      gens σN = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb →
      gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype →
      ∀ (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B),
      σH.length ≤ (k + L.q) ^ 2 → σN.length ≤ (k + L.q) ^ 2 → σS.length ≤ (k + L.q) ^ 2 →
      ∀ (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
        (hqα : (S.N : ℝ) ^ P₀.α < L.q),
      ∀ us vs : List Val,
      List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
        us (tmTests L.q) →
      List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (tmCosetState S E σH ij).answer)
        vs (tmCosets L.q) →
      FunAll Pg g (.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
          encFun (rowLab e L.con.blocks)], .list us, .list vs])
        (fun u cost => ∃ reps : List (Perm (Fin m)), u = .list (reps.map encPerm) ∧
          (∀ r ∈ reps, r ∈ ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα).Hb) ∧
          (∀ h : Perm (Fin m), h ∈ ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα).Hb → ∃ r ∈ reps, ∃ x : Perm (Fin m), x ∈ tmRad ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα) ∧ h = x * r) ∧
          reps.length = ((tmRad ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα)).subgroupOf ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα).Hb).index ∧
          (cost : ℝ) ≤ expLogSq A S.N)

/-- **One radical coset** (T4–T6; Theorem A.20 in `R r`, then the labels of A.23): on the input
of `TermAsmSpec` and a representative `r ∈ H`, a canonical answer on the domain positions of the
piece `tmCosetT ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα) r` of the table transport, at cost at most `expLogSq A N`. -/
def TermCosetSpec (A : ℝ) (g : ℕ) : Prop :=
  ∀ {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
    Function.Injective c →
    ∀ (sv lv : Val) (L : SuppliedLabels S), Canon e c sv S → LabValStd e S lv L →
    P₀.q₀ < L.q → Good P₀ .giant S → RowCase P₀.α S L.toGiantLabels →
    ∀ (label : Ω → Fin L.q) (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q)
      {m : ℕ} (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom)
      (hP : PureCoords S L.toGiantLabels label E)
      (σH σN σS : List (Perm (Fin m))),
      gens σH = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb →
      gens σN = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb →
      gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype →
      ∀ (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B),
      σH.length ≤ (k + L.q) ^ 2 → σN.length ≤ (k + L.q) ^ 2 → σS.length ≤ (k + L.q) ^ 2 →
      ∀ (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
        (hqα : (S.N : ℝ) ^ P₀.α < L.q),
      ∀ us vs : List Val,
      List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
        us (tmTests L.q) →
      List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (tmCosetState S E σH ij).answer)
        vs (tmCosets L.q) →
      ∀ r : Perm (Fin m), r ∈ ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα).Hb →
      FunAll Pg g (.list [(.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
          encFun (rowLab e L.con.blocks)], .list us, .list vs]), encPerm r])
        (fun u cost => AnsC (domEquiv e S.dom) u (tmDomSet ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα).e (tmCosetT ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα) r)) ∧
          (cost : ℝ) ≤ expLogSq A S.N)

end Iface

/-- The piece of one representative, on `[[V, 1], encPerm r]`: `[1, answer of r]`. -/
def tmPieceF (g2 : ℕ) : Expr :=
  .letE (.call g2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)))
    (mk2 (.get (arg 0) (.nat 1)) (.var 1))

/-- The number `m * q` of domain positions, read off the coordinates. -/
def tmSExpr : Expr :=
  .arith .mul (.length (.get (.get (arg 0) (.nat 2)) (.nat 0))) (.length (.get (arg 0) (.nat 2)))

/-- **The body of the split**: representatives (`g1`), the identity on the domain positions
(`range` at `rg`), the pieces (`map` at `mp`) and `CombineExact` (at `ce`). -/
def tmSplitBody (g1 rg mp ce : ℕ) : Expr :=
  .letE (.call g1 (.var 0))
  (.letE (.call rg tmSExpr)
  (.letE (.call mp (mk2 (mk2 (.var 0) (.var 2)) (.var 1)))
  (.call ce (mk2 .nil (.var 3)))))

/-- Where the modules of the split sit in the program. -/
structure TmSplitAt (P : Program) (f g1 g2 rg mp pf ce bapp bc gc comp inv app bn jm : ℕ) :
    Prop where
  entry : P.funs[f]? = some (tmSplitBody g1 rg mp ce)
  piece : P.funs[pf]? = some (tmPieceF g2)
  range : P.HasAt rg (rangeFuns rg)
  map : P.HasAt mp (mapFuns mp pf)
  ce : P.funs[ce]? = some (ceF bapp bc bn)
  ap : P.HasAt bapp (appendFuns bapp)
  fold : P.HasAt bc (foldlFuns bc gc)
  step : P.funs[gc]? = some (combStep comp inv app)
  comp : P.HasAt comp (composeFuns comp)
  inv : P.HasAt inv (invFuns inv)
  app : P.HasAt app (appendFuns app)
  nf : P.HasAt bn (cosetNFFuns bn jm)

/-- **The pieces as values of `CombineExact`.** A list of pieces `[1, u_r]`, with `u_r` a canonical
answer of `A_r`, is the list of piece values of some `cps` whose union is `⋃ e(A_r)`. -/
theorem tm_pieces {Ω' : Type} {s : ℕ} (e' : Ω' ≃ Fin s) {ι : Type} (A : ι → Set (Perm Ω')) :
    ∀ {reps : List ι} {ws : List Val}, List.Forall₂ (fun r w => ∃ u,
      w = .list [encPerm (1 : Perm (Fin s)), u] ∧ AnsC e' u (A r)) reps ws →
    ∃ cps : List (Perm (Fin s) × Acc s), ws = cps.map encPiece ∧
      unionSet cps = ⋃ r ∈ reps, toFin e' '' A r
  | [], [], .nil => ⟨[], rfl, by ext g; simp [unionSet]⟩
  | r :: reps, w :: ws, .cons ⟨u, hw, hu⟩ htl => by
    obtain ⟨cps, hcps, hU⟩ := tm_pieces e' A htl
    obtain ⟨a, rfl, ha⟩ := hu.acc
    refine ⟨(1, a) :: cps, by rw [hw, hcps]; rfl, ?_⟩
    ext g
    have hU' := congrArg (g ∈ ·) hU
    simp only [unionSet, Set.mem_setOf_eq, List.mem_cons, Set.mem_iUnion, exists_prop] at hU' ⊢
    rw [eq_iff_iff] at hU'
    constructor
    · rintro ⟨q, rfl | hq, hg⟩
      · exact ⟨r, Or.inl rfl, by rw [← ha]; simpa using hg⟩
      · obtain ⟨r', hr', hg'⟩ := hU'.1 ⟨q, hq, hg⟩
        exact ⟨r', Or.inr hr', hg'⟩
    · rintro ⟨r', rfl | hr', hg⟩
      · exact ⟨(1, a), Or.inl rfl, by rw [← ha] at hg; simpa using hg⟩
      · obtain ⟨q, hq, hg'⟩ := hU'.2 ⟨r', hr', hg⟩
        exact ⟨q, Or.inr hq, hg'⟩

theorem tm_sum_map_const {α : Type*} (l : List α) (b : ℕ) :
    (l.map fun _ => b).sum = l.length * b := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- The polynomial part of the cost of the split, in `Z`. -/
noncomputable def tmSplitPoly (hm : Membership) (Z : ℕ) : ℕ :=
  tmCeK hm * Z ^ tmCeD hm + 10 ^ 9 * Z ^ 3

/-- The weight bound `Z` of the split, for `n` representatives and inputs of weight below
`Y = tmVB N`. -/
def tmSplitZ (n Y : ℕ) : ℕ := 10 ^ 6 * (n + 1) * Y

namespace Iface

variable (Pg : Program)

/-- **The split on one input.** -/
theorem tm_split_main (hm : Membership)
    {f g1 g2 rg mp pf ce bapp bc gc comp inv app bn jm : ℕ}
    (h : TmSplitAt Pg f g1 g2 rg mp pf ce bapp bc gc comp inv app bn jm)
    (hjm : Pg.prims[jm]? = some (membershipPrim hm)) {A : ℝ}
    (hreps : TermRepsSpec Pg A g1) (hcos : TermCosetSpec Pg A g2)
    {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ)
    (hc : Function.Injective c)
    (sv lv : Val) (L : SuppliedLabels S) (hsv : Canon e c sv S) (hlv : LabValStd e S lv L)
    (hq0 : P₀.q₀ < L.q) (hgood : Good P₀ .giant S) (hrow : RowCase P₀.α S L.toGiantLabels)
    (label : Ω → Fin L.q) (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q)
    {m : ℕ} (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom)
    (hP : PureCoords S L.toGiantLabels label E)
    (σH σN σS : List (Perm (Fin m)))
    (hH : gens σH = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb)
    (hNg : gens σN = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb)
    (hS : gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hlH : σH.length ≤ (k + L.q) ^ 2) (hlN : σN.length ≤ (k + L.q) ^ 2)
    (hlS : σS.length ≤ (k + L.q) ^ 2)
    (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hNpos : 0 < S.N)
    (hqα : (S.N : ℝ) ^ P₀.α < L.q) (us vs : List Val)
    (hus : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
        us (tmTests L.q))
    (hvs : List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (tmCosetState S E σH ij).answer)
        vs (tmCosets L.q)) :
    FunAll Pg f (.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
          encFun (rowLab e L.con.blocks)], .list us, .list vs])
      (fun u cost => AnsC (domEquiv e S.dom) u (tmDomSet ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hNpos hqα).e (tmExactT ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hNpos hqα))) ∧
        (cost : ℝ) ≤ expLogSq A S.N + (((tmRad ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hNpos hqα)).subgroupOf ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hNpos hqα).Hb).index : ℝ) *
          (expLogSq A S.N + 1 + (10 ^ 4 * tmVB S.N : ℕ)) +
          (tmSplitPoly hm (tmSplitZ ((tmRad ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hNpos hqα)).subgroupOf ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hNpos hqα).Hb).index (tmVB S.N)) : ℕ)) := by
  set T := ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hNpos hqα) with hT
  set tin := Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
    encFun (rowLab e L.con.blocks)] with htin
  set V := Val.list [tin, .list us, .list vs] with hV
  set s := (domFin e S.dom).length with hs
  have hms : m * L.q = s := by
    rw [hs, ← card_dom_eq e S.dom, ← Nat.card_congr E, Nat.card_eq_fintype_card,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  refine FunAll.intro h.entry ?_
  unfold tmSplitBody
  -- 1. the representatives
  refine EvalAll.letE (EvalAll.call_spec (Det.var' (P := Pg) (env := [V]) (i := 0) (v := V) rfl)
    (hreps S k e c hc sv lv L hsv hlv hq0 hgood hrow label hnat hq h0 E hP σH σN σS hH hNg hS htr
      hlH hlN hlS hcard hsN hNpos hqα us vs hus hvs)) ?_
  rintro w1 c1 ⟨cb1, ⟨reps, rfl, hrH, hcov, hlen, hcb1⟩, hc1⟩
  -- 2. the identity on the domain positions
  have dtin := Det.arg' (P := Pg) (vs := [tin, .list us, .list vs])
    (rest := [.list (reps.map encPerm)]) (j := 0) (v := tin) rfl
  have dco := Det.get' dtin (Det.nat 2) (vs := [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
    encFun (rowLab e L.con.blocks)]) (v := coordsVal e S E) rfl
  rw [coordsVal_eq_list] at dco
  have dr0 := Det.get' dco (Det.nat 0) (coordsVal_get? e S E ⟨0, by omega⟩)
  have dmm := Det.length dr0
  have dqq := Det.length dco
  simp only [natList, List.length_map, List.length_finRange] at dmm dqq
  have dS := Det.arith' (op := .mul) dmm dqq (z := s) (by rw [← hms]; rfl)
  -- a linear bound of the cost of `s`
  have wtin : tin.wt < V.wt := wt_le_wt_list (by simp)
  have wco : (coordsVal e S E).wt < tin.wt := wt_le_wt_list (by simp)
  have wrow : (natList ((List.finRange m).map fun β => ((e (E (β, ⟨0, by omega⟩)).val : Fin k) : ℕ))).wt <
      (coordsVal e S E).wt := by
    rw [coordsVal_eq_list]
    exact wt_le_wt_list (List.mem_map.2 ⟨⟨0, by omega⟩, List.mem_finRange _, rfl⟩)
  have hsk : s ≤ k := length_domFin_le
  have hkv := StateVal.k_le_wt hsv.stateVal
  have wsv : sv.wt < tin.wt := wt_le_wt_list (by simp)
  have wm := wt_nat_le m
  have wq := wt_nat_le L.q
  have hmW : m < V.wt := by
    have := length_lt_wt_natList ((List.finRange m).map fun β =>
      ((e (E (β, ⟨0, by omega⟩)).val : Fin k) : ℕ))
    simp only [List.length_map, List.length_finRange] at this
    omega
  have hqW : L.q < V.wt := by
    have := length_lt_wt_list ((List.finRange L.q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))
    simp only [List.length_map, List.length_finRange] at this
    have e1 : (coordsVal e S E).wt = (Val.list ((List.finRange L.q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))).wt := by
      rw [coordsVal_eq_list]
    omega
  have eV : (Val.list [tin, Val.list us, Val.list vs]).wt = V.wt := rfl
  have e2 : (Val.list ((List.finRange L.q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))).wt =
      (coordsVal e S E).wt := by rw [coordsVal_eq_list]
  have dS' : Det Pg [V, .list (reps.map encPerm)] tmSExpr (.nat s) (20 * V.wt + 40) :=
    dS.mono (by
      have r1 : (Val.list (List.map Val.nat (List.map (fun β => ((e (E (β, ⟨0, by omega⟩)).val : Fin k) : ℕ))
        (List.finRange m)))).wt = (natList ((List.finRange m).map fun β =>
          ((e (E (β, ⟨0, by omega⟩)).val : Fin k) : ℕ))).wt := rfl
      have r2 : (Val.list (List.map (fun j => Val.list (List.map Val.nat (List.map
        (fun β => ((e (E (β, j)).val : Fin k) : ℕ)) (List.finRange m)))) (List.finRange L.q))).wt =
          (coordsVal e S E).wt := rfl
      rw [r1, r2]
      omega)
  refine EvalAll.letE (EvalAll.call_spec dS' (range_spec h.range s)) ?_
  rintro w2 c2 ⟨cb2, ⟨rfl, hcb2⟩, hc2⟩
  rw [range_eq_encPerm_one] at hc2 ⊢
  -- weights
  set Y := tmVB S.N with hYdef
  have hY : V.wt + 1 ≤ Y := tm_wtV_le hsv hlv E (by omega) hlH hlN hlS hus hvs
  have hkN : k ≤ S.N := hsv.fits
  have hP6 : (S.N + 1) ^ 6 ≤ (S.N + 2) ^ 8 :=
    (Nat.pow_le_pow_left (by omega) 6).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hP2 : (S.N + 1) ^ 2 ≤ (S.N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hYP : Y = 4 * 10 ^ 6 * (S.N + 2) ^ 8 := rfl
  have hsY : 4 * (s + 1) ^ 2 ≤ Y := by
    have := Nat.pow_le_pow_left (show s + 1 ≤ S.N + 1 by omega) 2; omega
  have hmk : m ≤ k := m_le_n e E ⟨0, by omega⟩
  have hmY : 4 * (m + 1) ^ 2 ≤ Y := by
    have := Nat.pow_le_pow_left (show m + 1 ≤ S.N + 1 by omega) 2; omega
  have hAY : ansW s ≤ Y := by
    have h1 := ansW_le s
    have := Nat.pow_le_pow_left (show s + 1 ≤ S.N + 1 by omega) 6; omega
  have w1 := wt_encPerm_le (1 : Perm (Fin s))
  -- 3. the pieces
  set one := encPerm (1 : Perm (Fin s)) with hone
  set E0 := expLogSq A S.N with hE0
  set Bp := ⌈E0⌉₊ + 10 ^ 4 * Y with hBp
  have hpiece : ∀ x ∈ reps.map encPerm, FunAll Pg pf (.list [.list [V, one], x]) (fun w cost =>
      (∃ r, x = encPerm r ∧ ∃ u, w = .list [one, u] ∧
        AnsC (domEquiv e S.dom) u (tmDomSet T.e (tmCosetT T r))) ∧ cost ≤ Bp) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    refine FunAll.intro h.piece ?_
    unfold tmPieceF
    have dV := Det.get' (Det.arg' (P := Pg) (vs := [.list [V, one], encPerm r]) (rest := []) (j := 0)
      rfl) (Det.nat 0) (vs := [V, one]) (v := V) rfl
    have dr := Det.arg' (P := Pg) (vs := [.list [V, one], encPerm r]) (rest := []) (j := 1)
      (v := encPerm r) rfl
    refine EvalAll.letE (EvalAll.call_spec (Det.mk2 dV dr) (hcos S k e c hc sv lv L hsv hlv hq0
      hgood hrow label hnat hq h0 E hP σH σN σS hH hNg hS htr hlH hlN hlS hcard hsN hNpos hqα us vs
      hus hvs r (hrH r hr))) ?_
    rintro u cu ⟨cb, ⟨hu, hcb⟩, hcu⟩
    have d1 := Det.get' (Det.arg' (P := Pg) (vs := [.list [V, one], encPerm r]) (rest := [u]) (j := 0)
      rfl) (Det.nat 1) (vs := [V, one]) (v := one) rfl
    have d2 := Det.var' (P := Pg) (env := [.list [.list [V, one], encPerm r], u]) (i := 1) (v := u) rfl
    refine (Det.mk2 d1 d2).post fun cw hcw => ⟨⟨r, rfl, u, rfl, hu⟩, ?_⟩
    have hcb' : cb ≤ ⌈E0⌉₊ := by exact_mod_cast hcb.trans (Nat.le_ceil E0)
    have wu := hu.wt_le
    have wr := wt_encPerm_le r
    have a1 := wt_list2_le V one
    have a2 := wt_list2_le (.list [V, one]) (encPerm r)
    have a3 := wt_list2_le V (encPerm r)
    have a4 := wt_list2_le one u
    have a5 := wt_list2_le (.list [.list [V, one], encPerm r]) u
    have wu' : u.wt ≤ Y := wu.trans hAY
    omega
  have hmap := map_spec h.map (c := .list [V, one]) (xs := reps.map encPerm) (B := fun _ => Bp)
    hpiece
  have dc := Det.mk2 (P := Pg) (env := [V, .list (reps.map encPerm), one])
    (Det.mk2 (Det.var' (i := 0) (v := V) rfl) (Det.var' (i := 2) (v := one) rfl))
    (Det.var' (i := 1) (v := .list (reps.map encPerm)) rfl)
  refine EvalAll.letE (EvalAll.call_spec dc hmap) ?_
  rintro w3 c3 ⟨cb3, ⟨ws, rfl, hws, hcb3⟩, hc3⟩
  -- the pieces as values of `CombineExact`
  have hws' : List.Forall₂ (fun r w => ∃ u, w = .list [encPerm (1 : Perm (Fin s)), u] ∧
      AnsC (domEquiv e S.dom) u (tmDomSet T.e (tmCosetT T r))) reps ws := by
    rw [List.forall₂_map_left_iff] at hws
    refine hws.imp fun r w hrw => ?_
    obtain ⟨r', hr', u, hw, hu⟩ := hrw
    have := encPerm_injective hr'
    subst this
    exact ⟨u, hw, hu⟩
  obtain ⟨cps, hcps, hU⟩ := tm_pieces (domEquiv e S.dom)
    (fun r : Perm (Fin m) => tmDomSet T.e (tmCosetT T r)) hws'
  have hUnion : unionSet ([] ++ cps) = toFin (domEquiv e S.dom) '' tmDomSet T.e (tmExactT T) := by
    rw [List.nil_append, hU, tm_exactT_eq_iUnion T (reps := reps) hcov, tmDomSet_iUnion,
      Set.image_iUnion₂]
    rfl
  have hce := ce_spec hm h.ce h.ap h.fold h.step h.comp h.inv h.app h.nf hjm [] cps
    (by rw [hUnion]; exact tm_domSet_cosetOrEmpty e T)
  have da := Det.mk2 (P := Pg) (env := [V, .list (reps.map encPerm), one, .list ws]) Det.nil
    (Det.var' (i := 3) (v := .list ws) rfl)
  subst hcps
  refine (EvalAll.call_spec da hce).mono ?_
  rintro u c4 ⟨cb4, ⟨hC, hcb4⟩, hc4⟩
  have hAns : AnsC (domEquiv e S.dom) u (tmDomSet T.e (tmExactT T)) :=
    CosetC.ansC (by rw [← hUnion]; exact hC)
  refine ⟨hAns, ?_⟩
  -- the cost
  set n := reps.length with hn
  have hn' : ((tmRad T).subgroupOf T.Hb).index = n := hlen.symm
  rw [hn']
  have wu : u.wt ≤ Y := hAns.wt_le.trans hAY
  have hone1 : one.wt ≤ Y := w1.trans (by omega)
  have Y1 : 1 ≤ Y := by omega
  have wR : (Val.list (reps.map encPerm)).wt ≤ n * (2 * Y + 1) + 4 :=
    wt_list_map_le reps encPerm (W := Y) fun r _ => (wt_encPerm_le r).trans (by omega)
  have wC : (Val.list (cps.map encPiece)).wt ≤ n * (2 * (5 * Y) + 1) + 4 := by
    have := tm_wt_forall₂ (W := 5 * Y) (R := fun w r => ∃ u, w = .list [one, u] ∧
      AnsC (domEquiv e S.dom) u (tmDomSet T.e (tmCosetT T r))) (fun w r ⟨u', hw, hu'⟩ => by
        rw [hw]
        have := wt_list2_le one u'
        have := hu'.wt_le.trans hAY
        omega) hws'.flip
    exact this
  rw [range_eq_encPerm_one] at hcb2
  set P := n * Y with hPdef
  set T1 := P + Y with hT1
  have r1 : n * (2 * Y + 1) = 2 * P + n := by rw [hPdef]; ring
  have r2 : n * (2 * (5 * Y) + 1) = 10 * P + n := by rw [hPdef]; ring
  have hnT : n ≤ P := Nat.le_mul_of_pos_right _ Y1
  have hs1 : s + 1 ≤ Y := by
    have : s + 1 ≤ (s + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have l1 := wt_list2_le V one
  have l2 := wt_list2_le (.list [V, one]) (.list (reps.map encPerm))
  have l3 := wt_list2_le (.list []) (.list (cps.map encPiece))
  have l0 : (Val.list []).wt ≤ 5 := by decide
  have hsum : (List.map (fun _ => Bp) (List.map encPerm reps)).sum = n * Bp := by
    rw [List.map_map, hn]
    exact tm_sum_map_const reps Bp
  rw [hsum] at hcb3
  simp only [List.length_map] at hcb3
  rw [← hn] at hcb3
  set W2 := (Val.list [Val.list [V, one], Val.list (List.map encPerm reps)]).wt with hW2
  set W3 := (Val.list (List.map encPiece cps)).wt with hW3
  have hW23 : W2 + W3 + 1 ≤ 50 * T1 := by omega
  have hm3 : mapK * (n + 1) * (W2 + W3 + 1) ≤ 50000 * (T1 * T1) := by
    have := Nat.mul_le_mul (show n + 1 ≤ T1 by omega) hW23
    have e : mapK * (n + 1) * (W2 + W3 + 1) = 1000 * ((n + 1) * (W2 + W3 + 1)) := by
      unfold mapK; ring
    have e2 : T1 * (50 * T1) = 50 * (T1 * T1) := by ring
    omega
  have hc2' : loopModK * (s + 1) * ((Val.nat s).wt + s + one.wt + 1) ≤ 4000 * (T1 * T1) := by
    have ws := wt_nat_le s
    have := Nat.mul_le_mul (show s + 1 ≤ T1 by omega)
      (show (Val.nat s).wt + s + one.wt + 1 ≤ 4 * T1 by omega)
    have e : loopModK * (s + 1) * ((Val.nat s).wt + s + one.wt + 1) =
      1000 * ((s + 1) * ((Val.nat s).wt + s + one.wt + 1)) := by unfold loopModK; ring
    have e2 : T1 * (4 * T1) = 4 * (T1 * T1) := by ring
    omega
  have hZ : tmSplitZ n Y = 10 ^ 6 * T1 := by unfold tmSplitZ; rw [hT1, hPdef]; ring
  have hT1p : 1 ≤ T1 := by omega
  have hZ1 : 1 ≤ tmSplitZ n Y := by rw [hZ]; omega
  have e3 : (Val.list [Val.list (List.map encPiece ([] : List (Perm (Fin s) × Acc s))),
      Val.list (List.map encPiece cps)]).wt = (Val.list [.list [], .list (cps.map encPiece)]).wt := rfl
  have hce' := tm_ceCost_le hm hZ1 (n := s) (W := (Val.list [Val.list (List.map encPiece []),
    Val.list (List.map encPiece cps)]).wt) (by rw [hZ]; omega) (by rw [hZ, e3]; omega)
  have hTT : T1 * T1 ≤ tmSplitZ n Y ^ 3 := by
    rw [hZ]
    have h3 : (10 ^ 6 * T1) ^ 3 = (10 ^ 6 * T1) * (10 ^ 6 * T1) * (10 ^ 6 * T1) := by ring
    rw [h3]
    calc T1 * T1 ≤ (10 ^ 6 * T1) * (10 ^ 6 * T1) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ (10 ^ 6 * T1) * (10 ^ 6 * T1) * (10 ^ 6 * T1) := Nat.le_mul_of_pos_right _ (by omega)
  have hBp' : n * Bp = n * ⌈E0⌉₊ + n * (10 ^ 4 * Y) := by rw [hBp]; ring
  have hnat : c1 + (c2 + (c3 + c4 + u.wt + 1) + u.wt + 1) + u.wt + 1 ≤
      cb1 + n * ⌈E0⌉₊ + n * (10 ^ 4 * Y) + tmSplitPoly hm (tmSplitZ n Y) := by
    unfold tmSplitPoly
    have : n * (10 ^ 4 * Y) = 10 ^ 4 * P := by rw [hPdef]; ring
    have hTT1 : T1 ≤ T1 * T1 := Nat.le_mul_of_pos_right _ hT1p
    have hcb4' : cb4 ≤ tmCeK hm * tmSplitZ n Y ^ tmCeD hm := hcb4.trans hce'
    rw [← hone] at hcb2
    clear_value W2 W3 T1 P Bp
    omega
  have hE0 : 0 ≤ E0 := expLogSq_nonneg _ _
  have hceil : (⌈E0⌉₊ : ℝ) ≤ E0 + 1 := (Nat.ceil_lt_add_one hE0).le
  have : (n : ℝ) * ⌈E0⌉₊ ≤ n * (E0 + 1) := mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg _)
  have hcast : ((c1 + (c2 + (c3 + c4 + u.wt + 1) + u.wt + 1) + u.wt + 1 : ℕ) : ℝ) ≤
      (cb1 : ℝ) + n * ⌈E0⌉₊ + (n * (10 ^ 4 * Y) : ℕ) + (tmSplitPoly hm (tmSplitZ n Y) : ℕ) := by
    exact_mod_cast hnat
  have e4 : ((n * (10 ^ 4 * Y) : ℕ) : ℝ) = n * ((10 ^ 4 * Y : ℕ) : ℝ) := by push_cast; ring
  rw [e4] at hcast
  have e5 : (n : ℝ) * (E0 + 1 + ((10 ^ 4 * Y : ℕ) : ℝ)) =
    n * (E0 + 1) + n * ((10 ^ 4 * Y : ℕ) : ℝ) := by ring
  rw [e5]
  linarith

end Iface

/-- `N` is normal in `H` and transitive on `B`, in the form of `radical_index_le`. -/
theorem tm_index_le (hAb : GI.Cited.GMPAbelianFactors) (hOut : GI.Cited.GMPOutBound)
    (hTr : GI.Cited.GMPTransitiveNonabelian) {Ω C : Type} {P : Params} {S : State Ω C}
    {L : GiantLabels S} (I : RowTerminal P S L) :
    (((tmRad I).subgroupOf I.Hb).index : ℝ) ≤
      (Fintype.card I.B : ℝ) ^ (2 * Real.logb 2 (Fintype.card I.B)) := by
  haveI : (I.Nb.subgroupOf I.Hb).Normal := by
    change ((I.Nl.map I.Hb.subtype).comap I.Hb.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective I.Hb.subtype_injective]
    infer_instance
  have htr : MulAction.IsPretransitive I.Nb I.B := by
    refine ⟨fun b b' => ?_⟩
    obtain ⟨n, hn⟩ := I.transitive.exists_smul_eq b b'
    exact ⟨⟨((n : I.Hb) : Perm I.B), n, n.2, rfl⟩, hn⟩
  exact GI.RadicalIndex.radical_index_le hAb hOut hTr I.Nb_le htr

/-- The constant of the weights in `tmSplitPoly`. -/
noncomputable def tmSplitKP (hm : Membership) : ℕ :=
  (tmCeK hm + 10 ^ 9) * (8 * 10 ^ 12) ^ tmCeD hm

/-- The exponent constant of the split: the four terms of `tm_split_main` each lie below
`expLogSq (tmSplitM hm A)`. -/
noncomputable def tmSplitM (hm : Membership) (A : ℝ) : ℝ :=
  A + 3 + 3 * (Real.log (5 * 10 ^ 10) + 8) +
    (3 * (Real.log (tmSplitKP hm) + 8 * tmCeD hm) + 3 * tmCeD hm)

/-- **The exponent of the split.** -/
noncomputable def tmSplitA (hm : Membership) (A : ℝ) : ℝ := 4 * tmSplitM hm A + 9

theorem tm_expLogSq_pow (a : ℝ) (D N : ℕ) : expLogSq a N ^ D = expLogSq (D * a) N := by
  unfold expLogSq
  rw [← Real.exp_nat_mul]
  ring_nf

/-- **The cost of the split is within `expLogSq`.** -/
theorem tm_split_cost_le (hm : Membership) {A : ℝ} (hA : 0 ≤ A) {N n : ℕ}
    (hn : (n : ℝ) ≤ expLogSq 3 N) :
    expLogSq A N + (n : ℝ) * (expLogSq A N + 1 + (10 ^ 4 * tmVB N : ℕ)) +
      (tmSplitPoly hm (tmSplitZ n (tmVB N)) : ℕ) ≤ expLogSq (tmSplitA hm A) N := by
  set X := expLogSq 3 N with hX
  set D := tmCeD hm with hD
  set M := tmSplitM hm A with hM
  have hX1 : 1 ≤ X := tm_one_le_expLogSq (by norm_num) N
  have hN2 : (1 : ℝ) ≤ (N : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hKP1 : (1 : ℝ) ≤ tmSplitKP hm := by
    have : 1 ≤ tmSplitKP hm := Nat.one_le_iff_ne_zero.2 (by unfold tmSplitKP; positivity)
    exact_mod_cast this
  have hlogKP : 0 ≤ Real.log (tmSplitKP hm) := Real.log_nonneg hKP1
  have hlog5 : 0 ≤ Real.log (5 * 10 ^ 10) := Real.log_nonneg (by norm_num)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  set cQ : ℝ := 3 * (Real.log (5 * 10 ^ 10) + 8) with hcQ
  set cP : ℝ := 3 * (Real.log (tmSplitKP hm) + 8 * D) + 3 * D with hcP
  have hcQ0 : 0 ≤ cQ := by positivity
  have hcP0 : 0 ≤ cP := by positivity
  have hMdef : M = A + 3 + cQ + cP := rfl
  -- 1. the first call
  have t1 : expLogSq A N ≤ expLogSq M N := tm_expLogSq_mono (by linarith) N
  -- 2. the representatives' calls
  have hE0 := expLogSq_nonneg A N
  have t2 : (n : ℝ) * expLogSq A N ≤ expLogSq M N := by
    calc (n : ℝ) * expLogSq A N ≤ X * expLogSq A N := mul_le_mul_of_nonneg_right hn hE0
      _ = expLogSq (3 + A) N := tm_expLogSq_mul _ _ _
      _ ≤ expLogSq M N := tm_expLogSq_mono (by linarith) N
  -- 3. the weights of the calls
  have hQ : ((1 : ℝ) + ((10 ^ 4 * tmVB N : ℕ) : ℝ)) ≤ expLogSq cQ N := by
    have h := pow_le_expLogSq (A := 5 * 10 ^ 10) (by norm_num) 8 N
    have hp : (1 : ℝ) ≤ ((N : ℝ) + 2) ^ 8 := one_le_pow₀ hN2
    have : ((10 ^ 4 * tmVB N : ℕ) : ℝ) = 4 * 10 ^ 10 * ((N : ℝ) + 2) ^ 8 := by
      unfold tmVB; push_cast; ring
    rw [this]
    have h8 : ((8 : ℕ) : ℝ) = 8 := by norm_num
    rw [h8] at h
    linarith
  have t3 : (n : ℝ) * (1 + ((10 ^ 4 * tmVB N : ℕ) : ℝ)) ≤ expLogSq M N := by
    calc (n : ℝ) * (1 + ((10 ^ 4 * tmVB N : ℕ) : ℝ)) ≤ X * expLogSq cQ N :=
          mul_le_mul hn hQ (by positivity) (by positivity)
      _ = expLogSq (3 + cQ) N := tm_expLogSq_mul _ _ _
      _ ≤ expLogSq M N := tm_expLogSq_mono (by linarith) N
  -- 4. the polynomial part
  have t4 : ((tmSplitPoly hm (tmSplitZ n (tmVB N)) : ℕ) : ℝ) ≤ expLogSq M N := by
    set Z := tmSplitZ n (tmVB N) with hZ
    have hZ1 : 1 ≤ Z := by
      rw [hZ]; unfold tmSplitZ tmVB; exact Nat.one_le_iff_ne_zero.2 (by positivity)
    have hD3 : 3 ≤ D := by rw [hD]; unfold tmCeD; omega
    have hP : tmSplitPoly hm Z ≤ (tmCeK hm + 10 ^ 9) * Z ^ D := by
      unfold tmSplitPoly
      have : Z ^ 3 ≤ Z ^ D := Nat.pow_le_pow_right hZ1 hD3
      rw [← hD, Nat.add_mul]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ this) _
    have hZr : (Z : ℝ) ≤ 8 * 10 ^ 12 * X * ((N : ℝ) + 2) ^ 8 := by
      have : (n : ℝ) + 1 ≤ 2 * X := by linarith
      have h8 : (0 : ℝ) ≤ ((N : ℝ) + 2) ^ 8 := by positivity
      have eZ : (Z : ℝ) = 4 * 10 ^ 12 * ((N : ℝ) + 2) ^ 8 * ((n : ℝ) + 1) := by
        rw [hZ]; unfold tmSplitZ tmVB; push_cast; ring
      rw [eZ]
      calc 4 * 10 ^ 12 * ((N : ℝ) + 2) ^ 8 * ((n : ℝ) + 1)
          ≤ 4 * 10 ^ 12 * ((N : ℝ) + 2) ^ 8 * (2 * X) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = 8 * 10 ^ 12 * X * ((N : ℝ) + 2) ^ 8 := by ring
    have hZD : (Z : ℝ) ^ D ≤ (8 * 10 ^ 12 : ℝ) ^ D * ((N : ℝ) + 2) ^ (8 * D) * X ^ D := by
      calc (Z : ℝ) ^ D ≤ (8 * 10 ^ 12 * X * ((N : ℝ) + 2) ^ 8) ^ D :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hZr D
        _ = _ := by rw [mul_pow, mul_pow, ← pow_mul]; ring
    have hPr : ((tmSplitPoly hm Z : ℕ) : ℝ) ≤
        (tmSplitKP hm : ℝ) * ((N : ℝ) + 2) ^ (8 * D) * X ^ D := by
      have this : ((tmSplitPoly hm Z : ℕ) : ℝ) ≤ ((tmCeK hm + 10 ^ 9 : ℕ) : ℝ) * (Z : ℝ) ^ D := by
        exact_mod_cast hP
      have hK : (0 : ℝ) ≤ ((tmCeK hm + 10 ^ 9 : ℕ) : ℝ) := Nat.cast_nonneg _
      have eK : (tmSplitKP hm : ℝ) = ((tmCeK hm + 10 ^ 9 : ℕ) : ℝ) * (8 * 10 ^ 12 : ℝ) ^ D := by
        unfold tmSplitKP; rw [← hD, Nat.cast_mul, Nat.cast_pow]; norm_num
      calc ((tmSplitPoly hm Z : ℕ) : ℝ) ≤ ((tmCeK hm + 10 ^ 9 : ℕ) : ℝ) * (Z : ℝ) ^ D := this
        _ ≤ ((tmCeK hm + 10 ^ 9 : ℕ) : ℝ) * ((8 * 10 ^ 12 : ℝ) ^ D * ((N : ℝ) + 2) ^ (8 * D) * X ^ D) :=
          mul_le_mul_of_nonneg_left hZD hK
        _ = _ := by rw [eK]; ring
    have hpe := pow_le_expLogSq hKP1 (8 * D) N
    have hXD : X ^ D = expLogSq (D * 3) N := tm_expLogSq_pow _ _ _
    calc ((tmSplitPoly hm Z : ℕ) : ℝ) ≤ (tmSplitKP hm : ℝ) * ((N : ℝ) + 2) ^ (8 * D) * X ^ D := hPr
      _ ≤ expLogSq (3 * (Real.log (tmSplitKP hm) + ((8 * D : ℕ) : ℝ))) N * expLogSq (D * 3) N := by
          rw [hXD]; exact mul_le_mul_of_nonneg_right hpe (expLogSq_nonneg _ _)
      _ = expLogSq cP N := by rw [tm_expLogSq_mul]; congr 1; rw [hcP]; push_cast; ring
      _ ≤ expLogSq M N := tm_expLogSq_mono (by linarith) N
  -- the sum of four terms
  have hM0 : 0 ≤ M := by linarith
  have s2 := expLogSq_add_le hM0 hM0 N
  have s4 := expLogSq_add_le (by linarith : 0 ≤ M + M + 3) (by linarith : 0 ≤ M + M + 3) N
  have e : tmSplitA hm A = M + M + 3 + (M + M + 3) + 3 := by
    unfold tmSplitA; rw [← hM]; ring
  rw [e]
  have : expLogSq A N + (n : ℝ) * (expLogSq A N + 1 + ((10 ^ 4 * tmVB N : ℕ) : ℝ)) +
      ((tmSplitPoly hm (tmSplitZ n (tmVB N)) : ℕ) : ℝ) =
      expLogSq A N + (n : ℝ) * expLogSq A N + ((n : ℝ) * (1 + ((10 ^ 4 * tmVB N : ℕ) : ℝ)) +
        ((tmSplitPoly hm (tmSplitZ n (tmVB N)) : ℕ) : ℝ)) := by ring
  rw [this]
  linarith

namespace Iface

variable (Pg : Program)

/-- **T7 from the radical cosets.** The split meets `TermDomSpec`, from the representatives
(`TermRepsSpec`) and the pieces (`TermCosetSpec`), with cited Membership (`CombineExact`) and the
cited bounds of [GMP] for the number of radical cosets. -/
theorem tm_termDomSpec (hm : Membership) (hAb : GI.Cited.GMPAbelianFactors)
    (hOut : GI.Cited.GMPOutBound) (hTr : GI.Cited.GMPTransitiveNonabelian)
    {f g1 g2 rg mp pf ce bapp bc gc comp inv app bn jm : ℕ}
    (h : TmSplitAt Pg f g1 g2 rg mp pf ce bapp bc gc comp inv app bn jm)
    (hjm : Pg.prims[jm]? = some (membershipPrim hm)) {A : ℝ} (hA : 0 ≤ A)
    (hreps : TermRepsSpec Pg A g1) (hcos : TermCosetSpec Pg A g2) :
    TermDomSpec Pg (tmSplitA hm A) f := by
  intro Ω C _ S k e c hc sv lv L hsv hlv hq0 hgood hrow label hnat hq m h0 E hP σH σN σS hH hNg hS
    htr hlH hlN hlS hcard hsN hN hqα us vs hus hvs
  refine (tm_split_main Pg hm h hjm hreps hcos S k e c hc sv lv L hsv hlv hq0 hgood hrow label hnat
    hq h0 E hP σH σN σS hH hNg hS htr hlH hlN hlS hcard hsN hN hqα us vs hus hvs).mono ?_
  rintro u cost ⟨hu, hcost⟩
  refine ⟨hu, hcost.trans (tm_split_cost_le hm hA ?_)⟩
  refine (tm_index_le hAb hOut hTr ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα)).trans ?_
  have hB : Fintype.card ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα).B ≤ S.N := by
    have h1 : Fintype.card ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsN hN hqα).B = m := by
      change Fintype.card (Fin m) = m
      exact Fintype.card_fin m
    have h2 : m ≤ m * L.q := Nat.le_mul_of_pos_right _ (by omega)
    rw [Fintype.card_fin] at hcard
    omega
  exact tm_rpow_le_expLogSq hB

end Iface

end GI.Impl
