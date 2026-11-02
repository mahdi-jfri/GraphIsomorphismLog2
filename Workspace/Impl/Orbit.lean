import Workspace.Impl.LargestOrbit
import Workspace.Impl.Floor
import Workspace.Impl.ColsSplit

/-!
# The orbit chain of `Continue`

Algorithm 5: "if `G` is intransitive then return the inherited orbit-chain answer". Section 3.2
says how: take a largest orbit `D₁` first and solve it with `Continue`. If its answer is empty,
so is the whole answer (`Run.orbitStop`). Otherwise it is a coset `t H₁` with
`H₁ = Aut_G(x on D₁)`; the rest `D \ D₁` continues under `H₁` with target `y ∘ t`, and the answer
is `t A₂` (`Run.orbitChain`).

The step function:

1. finds a largest orbit, as the indicators of `D₁` and `D \ D₁` (`loFuns`,
   `Workspace/Impl/LargestOrbit.lean`);
2. calls `Continue` on the first state: the same group, colorings, hierarchy and phase size, the
   domain `D₁`, and the bookkeeping reset (no row record, floor mode off, `h = 2`);
3. if the answer is `[]`, returns `[]`; otherwise it reads `[t, H₁]` from it, computes `y ∘ t`
   (`gatherFuns`) and calls `Continue` on the second state: group `H₁`, domain `D \ D₁`,
   colorings `x` and `y ∘ t`, the same hierarchy and phase size, the bookkeeping reset;
4. if the second answer is `[]`, returns `[]`; otherwise it returns `[t t₂, H₂]` (`composeFuns`).

The children reset the bookkeeping, which the constructors allow (they fix only the core, the
hierarchy and the phase size). The reset needs no test of the row invariant on the new core.

The group part of the first answer is the group value of `H₁`: the first child has an exact
answer (`Run.exact`), and a nonempty exact answer is `t · Aut` (`answer_eq_smul_aut`). So the
second state value is canonical without any group computation (`first_answer`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-! ### The children -/

/-- The value of a child: entries `1, 2, 4` of the input replaced, the bookkeeping reset. -/
def childVal (k : ℕ) (gv dv xv yv hv : Val) (N : ℕ) : Val :=
  .list [.nat k, gv, dv, xv, yv, hv, .list [], boolVal false, .nat 2, .nat N]

theorem stateW_resetChild (S : State Ω C) (G' : Subgroup (Perm Ω)) (D' : Set Ω)
    (hD' : Invariant G' D') (x' y' : Ω → C) :
    stateW k (S.resetChild G' D' hD' x' y') ≤ stateW k S + 4 := by
  have h1 : rowsW k (S.resetChild G' D' hD' x' y').rows ≤ rowsW k S.rows := by
    show rowsW k none ≤ _
    cases S.rows <;> simp [rowsW]
  simp only [stateW]
  have : hierW k (S.resetChild G' D' hD' x' y').hier = hierW k S.hier := rfl
  have : (S.resetChild G' D' hD' x' y').N = S.N := rfl
  have : (S.resetChild G' D' hD' x' y').h = 2 := rfl
  omega

/-- A child is smaller in the measure when its domain is smaller. -/
theorem mlt_resetChild {S : State Ω C} {G' : Subgroup (Perm Ω)} {D' : Set Ω}
    {hD' : Invariant G' D'} {x' y' : Ω → C}
    (hsz : (S.resetChild G' D' hD' x' y').size < S.size) :
    MLt (measure P₀ .cont (S.resetChild G' D' hD' x' y')) (measure P₀ .cont S) := by
  have hN : (S.resetChild G' D' hD' x' y').N = S.N := rfl
  rw [mlt_iff]
  simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false,
    false_or]
  omega

theorem canon_resetChild {e : Ω ≃ Fin k} {c : C → ℕ} {gv dv xv yv hv rv fv hh : Val} {N : ℕ}
    {S : State Ω C} (hcan : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    {G' : Subgroup (Perm Ω)} {D' : Set Ω} {hD' : Invariant G' D'}
    {y' : Ω → C} {gv' yv' : Val} (hg : GroupValC k gv' (groupFin e G'))
    (hy : ColorVal e c yv' y') (hyc : ∀ a, c (y' a) < 2 * k) :
    Canon e c (childVal k gv' (indVal e D') xv yv' hv S.N) (S.resetChild G' D' hD' S.x y') := by
  obtain ⟨gv0, dv0, xv0, yv0, hv0, rv0, -, -, hx, -, hh0, -, heq⟩ := hcan.val
  simp only [Val.list.injEq, List.cons.injEq] at heq
  obtain ⟨-, -, -, rfl, -, rfl, -⟩ := heq
  exact ⟨⟨gv', indVal e D', xv, yv', hv, .list [], hg, domVal_indVal e D', hx, hy, hh0, rfl,
    rfl⟩, fun a => ⟨(hcan.colors a).1, hyc a⟩, hcan.fits, hcan.small.reset rfl rfl rfl⟩

/-! ### The first child -/

/-- The value of the first child: entry `2` replaced by `ind D₁`; the bookkeeping kept when the
row test `sp` is nonzero, and reset otherwise. -/
def firstVal (k : ℕ) (gv dv xv yv hv rv fv hh : Val) (N sp : ℕ) : Val :=
  .list [.nat k, gv, dv, xv, yv, hv, if sp = 0 then .list [] else rv,
    if sp = 0 then .nat 0 else fv, if sp = 0 then .nat 2 else hh, .nat N]

/-- The bookkeeping of the first child (`State.inherit` on the largest orbit). -/
theorem first_book (S : State Ω C) {D₁ : Set Ω} (hD₁ : S.LargestOrbit D₁) :
    (S.inherit S.G D₁ hD₁.invariant S.x S.y).book = S.orbitBook D₁ :=
  S.inherit_book hD₁.invariant hD₁.subset hD₁.nonempty S.x S.y

theorem first_parts (S : State Ω C) {D₁ : Set Ω} (hD₁ : S.LargestOrbit D₁) :
    let T := S.inherit S.G D₁ hD₁.invariant S.x S.y
    (S.ColsSplit D₁ → T.rows = S.rows ∧ T.floor = S.floor ∧ T.h = S.h) ∧
    (¬ S.ColsSplit D₁ → T.rows = none ∧ T.floor = false ∧ T.h = 2) := by
  classical
  have hb := first_book S hD₁
  simp only [State.orbitBook, State.book, State.resetBook] at hb
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [if_pos h] at hb
    simp only [Prod.mk.injEq] at hb
    exact hb
  · rw [if_neg h] at hb
    simp only [Prod.mk.injEq] at hb
    exact hb

theorem stateW_first (S : State Ω C) {D₁ : Set Ω} (hD₁ : S.LargestOrbit D₁) :
    stateW k (S.inherit S.G D₁ hD₁.invariant S.x S.y) ≤ stateW k S + 4 := by
  obtain ⟨h1, h2⟩ := first_parts S hD₁
  simp only [stateW, State.inherit_hier, State.inherit_N]
  by_cases h : S.ColsSplit D₁
  · obtain ⟨hr, -, hh⟩ := h1 h
    rw [hr, hh]; omega
  · obtain ⟨hr, -, hh⟩ := h2 h
    rw [hr, hh]
    have : rowsW k (none : Option (RowRecord Ω)) ≤ rowsW k S.rows := by
      cases S.rows <;> simp [rowsW]
    omega

/-- A child with the same phase size and a smaller domain is smaller in the measure. -/
theorem mlt_of_size {S T : State Ω C} (hN : T.N = S.N) (hsz : T.size < S.size) :
    MLt (measure P₀ .cont T) (measure P₀ .cont S) := by
  rw [mlt_iff]
  simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false,
    false_or]
  omega

open Classical in
theorem canon_first {e : Ω ≃ Fin k} {c : C → ℕ} {gv dv xv yv hv rv fv hh : Val} {N : ℕ}
    {S : State Ω C} (hcan : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    {D₁ : Set Ω} (hD₁ : S.LargestOrbit D₁) :
    Canon e c (firstVal k gv (indVal e D₁) xv yv hv rv fv hh S.N
      (if S.ColsSplit D₁ then 1 else 0)) (S.inherit S.G D₁ hD₁.invariant S.x S.y) := by
  obtain ⟨gv0, dv0, xv0, yv0, hv0, rv0, hg, -, hx, hy, hh0, hr0, heq⟩ := hcan.val
  simp only [Val.list.injEq, List.cons.injEq] at heq
  obtain ⟨-, rfl, -, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := heq
  obtain ⟨h1, h2⟩ := first_parts S hD₁
  have hsm : SmallInv (S.inherit S.G D₁ hD₁.invariant S.x S.y) := by
    have hT := S.inherit_hier S.G D₁ hD₁.invariant S.x S.y
    have hN := S.inherit_N S.G D₁ hD₁.invariant S.x S.y
    by_cases h : S.ColsSplit D₁
    · have hr := (h1 h).1
      refine hcan.small.of_hier_eq hT hN fun R hR => ?_
      rw [hr] at hR
      exact hN ▸ hcan.small.2.2 R hR
    · exact SmallInv.reset hcan.small hT hN (h2 h).1
  refine ⟨?_, fun a => by simpa using hcan.colors a, by simpa using hcan.fits, hsm⟩
  by_cases h : S.ColsSplit D₁
  · obtain ⟨hr, hf, hhh⟩ := h1 h
    refine ⟨gv, indVal e D₁, xv, yv, hv, rv, by simpa using hg, by simp [domVal_indVal],
      by simpa using hx, by simpa using hy, by simpa using hh0, by rw [hr]; exact hr0, ?_⟩
    simp [firstVal, h, hf, hhh]
  · obtain ⟨hr, hf, hhh⟩ := h2 h
    refine ⟨gv, indVal e D₁, xv, yv, hv, .list [], by simpa using hg, by simp [domVal_indVal],
      by simpa using hx, by simpa using hy, by simpa using hh0, by rw [hr]; rfl, ?_⟩
    simp [firstVal, h, hf, hhh]

/-! ### The answers -/

theorem toFin_symm_apply_mem {e : Ω ≃ Fin k} {A : Set (Perm Ω)} {x : Perm (Fin k)}
    {H : Subgroup (Perm (Fin k))} (hA : toFin e '' A = x • (H : Set (Perm (Fin k)))) :
    (toFin e).symm x ∈ A := by
  have hx : x ∈ x • (H : Set (Perm (Fin k))) := ⟨1, H.one_mem, mul_one x⟩
  rw [← hA] at hx
  obtain ⟨t, ht, htx⟩ := hx
  rw [← htx, MulEquiv.symm_apply_apply]
  exact ht

/-- **The answer of the first child.** A canonical nonempty answer `[t, H₁]` of a run on a
state with core `(G, D₁, x, y)` has `t` in the answer and `H₁` generating the image of
`Aut_G(x on D₁)`. The run gives the exact answer (`Run.exact`), and a nonempty exact answer is
`t · Aut` (`answer_eq_smul_aut`). Two equal left cosets `x K = x H` have `K = H`. -/
theorem first_answer {S₁ : State Ω C} {G : Subgroup (Perm Ω)} {D₁ : Set Ω}
    (hD₁ : Invariant G D₁) {x y : Ω → C} (h₁ : S₁.Inst G D₁ x y) {A₁ : Set (Perm Ω)}
    (r : Run P₀ .cont S₁ none A₁) {e : Ω ≃ Fin k} {x₁ : Perm (Fin k)} {gs : List (Perm (Fin k))}
    (hA : toFin e '' A₁ = x₁ • (gens gs : Set (Perm (Fin k)))) :
    (toFin e).symm x₁ ∈ A₁ ∧ gens gs = groupFin e (autGroup G D₁ hD₁ x) := by
  have ht := toFin_symm_apply_mem hA
  refine ⟨ht, ?_⟩
  have hex : A₁ = answer G D₁ x y := (r.exact).trans (State.answer_of_inst h₁)
  rw [hex] at ht hA
  rw [answer_eq_smul_aut hD₁ ht, toFin_image_coset, MulEquiv.apply_symm_apply] at hA
  have h2 := congrArg (fun X : Set (Perm (Fin k)) => x₁⁻¹ • X) hA
  simp only [inv_smul_smul] at h2
  exact SetLike.coe_injective h2.symm

/-- The answer of the chain from the second answer. -/
theorem chain_answer {e : Ω ≃ Fin k} {t : Perm Ω} {A₂ : Set (Perm Ω)} {x₂ : Perm (Fin k)}
    {gs : List (Perm (Fin k))} (hA : toFin e '' A₂ = x₂ • (gens gs : Set (Perm (Fin k)))) :
    toFin e '' (t • A₂) = (toFin e t * x₂) • (gens gs : Set (Perm (Fin k))) := by
  rw [← smul_smul, ← hA]
  ext g
  simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨toFin e a, ⟨a, ha, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨t * a, ⟨a, ha, rfl⟩, by simp⟩

/-- The colors of `y ∘ t` from those of `y` and the image of `t`. -/
theorem gather_colors (e : Ω ≃ Fin k) (c : C → ℕ) (y : Ω → C) (t : Perm Ω) :
    ((List.finRange k).map fun i => ((toFin e t) i : ℕ)).map
        (fun j => ((List.finRange k).map fun i => Val.nat (c (y (e.symm i)))).getD j (.nat 0)) =
      (List.finRange k).map fun i => Val.nat (c ((y ∘ t) (e.symm i))) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp [toFin, Equiv.permCongrHom, Equiv.permCongr_apply]

theorem encPerm_eq_natList (σ : Perm (Fin k)) :
    encPerm σ = natList ((List.finRange k).map fun i => (σ i : ℕ)) := by
  rw [encPerm_eq_encFun, encFun_eq_natList]

/-! ### The program -/

/-- The value of a child, from the input: entries `1, 2, 4` given by `eG, eD, eY`, the
bookkeeping reset. -/
def childArg (eG eD eY : Expr) : Expr :=
  Expr.mkList [arg 0, eG, eD, arg 3, eY, arg 5, .nil, .nat 0, .nat 2, arg 9]

/-- The value of the first child, from the input: entry `2` given by `eD`, the bookkeeping kept
when `eS` is nonzero and reset otherwise. -/
def firstArg (eS eD : Expr) : Expr :=
  Expr.mkList [arg 0, arg 1, eD, arg 3, arg 4, arg 5, .ite eS (arg 6) .nil,
    .ite eS (arg 7) (.nat 0), .ite eS (arg 8) (.nat 2), arg 9]

/-- The body of the orbit chain. `bl`, `bs`, `bg`, `bc` are the bases of the largest-orbit,
row-test, gather and compose modules. The environment grows as
`[v, [d₁, d₂], d₁, d₂, sp, u₁, t, H₁, y∘t, u₂]`. -/
def orbitBody (F : Funs) (bl bs bg bc : ℕ) : Expr :=
  .letE (.call bl (mk2 (arg 1) (arg 2)))
  (.letE (.get (.var 1) (.nat 0))
  (.letE (.get (.var 1) (.nat 1))
  (.letE (.call bs (mk2 (arg 6) (.var 2)))
  (.letE (.call F.cont (firstArg (.var 4) (.var 2)))
  (.ite (.length (.var 5))
    (.letE (.get (.var 5) (.nat 0))
    (.letE (.get (.var 5) (.nat 1))
    (.letE (.call bg (mk2 (arg 4) (.var 6)))
    (.letE (.call F.cont (childArg (.var 7) (.var 3) (.var 8)))
    (.ite (.length (.var 9))
      (mk2 (.call bc (mk2 (.var 6) (.get (.var 9) (.nat 0)))) (.get (.var 9) (.nat 1)))
      (.var 9))))))
    (.var 5))))))

theorem firstArg_det {P : Program} {k N : ℕ} {gv dv xv yv hv rv fv hh : Val} {rest : List Val}
    {eS eD : Expr} {sp : ℕ} {D' : Val} {c : ℕ}
    (hS : Det P (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] :: rest) eS (.nat sp) c)
    (hD : Det P (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] :: rest) eD D' c)
    (hc : 6 * (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt + 40 ≤ c) :
    Det P (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] :: rest) (firstArg eS eD)
      (firstVal k gv D' xv yv hv rv fv hh N sp) (10 * (3 * c + (firstVal k gv D' xv yv hv rv fv hh N sp).wt + 1) + 5) := by
  have ha : ∀ j (hj : j < 10), Det P (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] ::
      rest) (arg j) [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N][j] c := fun j hj =>
    (Det.arg (P := P) (rest := rest) (j := j) (by simp; omega)).mono (by omega)
  have hwv : ∀ j (hj : j < 10), ([.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] : List Val)[j].wt <
      (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt :=
    fun j hj => wt_getElem_lt _ j (by simp; omega)
  have hite : ∀ (j : ℕ) (hj : j < 10) (e0 : Expr) (v0 : Val), Det P (.list [.nat k, gv, dv, xv, yv,
      hv, rv, fv, hh, .nat N] :: rest) e0 v0 c → v0.wt ≤ 5 →
      Det P (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] :: rest) (.ite eS (arg j) e0)
        (if sp = 0 then v0 else [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N][j]) (3 * c) := by
    intro j hj e0 v0 h0 hw0
    refine (Det.ite' hS (ha j hj) h0).mono ?_
    have := hwv j hj
    have : max c c = c := max_self c
    have : max ([Val.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] : List Val)[j].wt v0.wt ≤
        (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt + 5 := max_le (by omega) (by omega)
    omega
  have h2 : (Val.list []).wt ≤ 5 := by simp [GI.Lang.wt_list_nil]
  have h3 : (Val.nat 0).wt ≤ 5 := by simp [wt_nat, GI.Machine.len_zero]
  have h4 : (Val.nat 2).wt ≤ 5 := by have := wt_nat_le 2; omega
  have hps := Det.mkList (P := P) (env := .list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] ::
    rest) (c := 3 * c)
    [(arg 0, .nat k), (arg 1, gv), (eD, D'), (arg 3, xv), (arg 4, yv), (arg 5, hv),
      (.ite eS (arg 6) .nil, if sp = 0 then .list [] else rv),
      (.ite eS (arg 7) (.nat 0), if sp = 0 then .nat 0 else fv),
      (.ite eS (arg 8) (.nat 2), if sp = 0 then .nat 2 else hh), (arg 9, .nat N)] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (ha 0 (by omega)).mono (by omega)
      · exact (ha 1 (by omega)).mono (by omega)
      · exact hD.mono (by omega)
      · exact (ha 3 (by omega)).mono (by omega)
      · exact (ha 4 (by omega)).mono (by omega)
      · exact (ha 5 (by omega)).mono (by omega)
      · exact hite 6 (by omega) _ _ (Det.nil.mono (by omega)) h2
      · exact hite 7 (by omega) _ _ ((Det.nat 0).mono (by omega)) h3
      · exact hite 8 (by omega) _ _ ((Det.nat 2).mono (by omega)) h4
      · exact (ha 9 (by omega)).mono (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hps
  exact hps

theorem childArg_det {P : Program} {k N : ℕ} {gv dv xv yv hv rv fv hh : Val} {rest : List Val}
    {eG eD eY : Expr} {G' D' Y' : Val} {c : ℕ}
    (hG : Det P (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] :: rest) eG G' c)
    (hD : Det P (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] :: rest) eD D' c)
    (hY : Det P (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] :: rest) eY Y' c)
    (hc : 2 * (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt + 14 ≤ c) :
    Det P (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] :: rest) (childArg eG eD eY)
      (childVal k G' D' xv Y' hv N) (10 * (c + (childVal k G' D' xv Y' hv N).wt + 1) + 5) := by
  have ha : ∀ j (hj : j < 10), Det P (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] ::
      rest) (arg j) [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N][j] c := fun j hj =>
    (Det.arg (P := P) (rest := rest) (j := j) (by simp; omega)).mono (by omega)
  have hps := Det.mkList (P := P) (env := .list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] ::
    rest) (c := c)
    [(arg 0, .nat k), (eG, G'), (eD, D'), (arg 3, xv), (eY, Y'), (arg 5, hv),
      (.nil, .list []), (.nat 0, .nat 0), (.nat 2, .nat 2), (arg 9, .nat N)] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ha 0 (by omega)
      · exact hG
      · exact hD
      · exact ha 3 (by omega)
      · exact hY
      · exact ha 5 (by omega)
      · exact Det.nil.mono (by omega)
      · exact (Det.nat 0).mono (by omega)
      · exact (Det.nat 2).mono (by omega)
      · exact ha 9 (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hps
  exact hps

/-- A call of `Continue` on a child value: its answer is a canonical answer of a run on the
child, at the cost of building the value plus the total cost of the run. -/
theorem call_child (I : Iface) {Pg : Program} {F : Funs} {env : List Val} {a : Expr}
    {val : Val} {cArg : ℕ} {T : State Ω C} {e : Ω ≃ Fin k} (ha : Det Pg env a val cArg)
    (hcall : FunAll Pg F.cont val (I.Post .cont T e val)) :
    EvalAll Pg env (.call F.cont a) (fun u cu => ∃ (A : Set (Perm Ω)) (r : Run P₀ .cont T none A)
      (cb : ℕ), AnsC e u A ∧ (cb : ℝ) ≤ r.total I.work ∧ cu ≤ cArg + cb + u.wt + 1) :=
  EvalAll.call_funAll ha fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine hcall.mono fun u cb ⟨A, L, r, hL, hA, hcb⟩ => ?_
    have hL' : L = none := hL
    subst hL'
    exact ⟨A, r, cb, hA, by simpa [Iface.excess] using hcb, by omega⟩

/-- The cost constant of the orbit chain. -/
def orbK : ℕ := 10 ^ 14

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

/-- The work bound that the orbit chain needs at its nodes: a polynomial in the weights of the
state value and of an answer. -/
def OrbitW : Prop :=
  ∀ nd : Node P₀, nd.run.kind = .orbitStop ∨ nd.run.kind = .orbitChain →
    ((orbK * (stateW (Nat.card nd.Ω) nd.S + ansW (Nat.card nd.Ω) + 1) ^ 15 : ℕ) : ℝ) ≤ I.W nd

/-- **The orbit chain meets its specification.** -/
theorem orbitSpec {f bl bs bg bc : ℕ} (hf : Pg.funs[f]? = some (orbitBody F bl bs bg bc))
    (hlo : Pg.HasAt bl (loFuns bl)) (hsp : Pg.HasAt bs (splitFuns bs))
    (hga : Pg.HasAt bg (gatherFuns bg))
    (hco : Pg.HasAt bc (composeFuns bc)) (hW : I.OrbitW) : I.OrbitSpec Pg F f := by
  intro Ω C S k e c hc v hv hg hP ih
  have hv' : Canon e c v S := hv
  obtain ⟨hN, hsN, hhi⟩ := hg
  obtain ⟨hs, hint⟩ := hP
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  have hwv := hv'.wt_le
  obtain ⟨gv, dv, xv, yv, hv0, rv, hgv, hdv, hxv, hyv, hhv, hrv, hvv⟩ := hv'.val
  obtain ⟨gs, rfl, hgens, hl⟩ := hgv
  have hdv' : dv = indVal e S.dom := hdv
  subst hdv' hvv
  -- The largest orbit.
  obtain ⟨D₁, hsub, horb, hlarge, hloD⟩ :=
    lo_spec hlo e S.dom_inv (dom_nonempty_of_large hs) hgens hl
  have hD₁ : S.LargestOrbit D₁ := ⟨hsub, horb, hlarge⟩
  set T₁ := S.inherit S.G D₁ hD₁.invariant S.x S.y with hT₁
  have hT₁N : T₁.N = S.N := State.inherit_N _ _ _ _ _ _
  have hsz₁ := LargestOrbit.size_lt (S₁ := T₁) hint hD₁ (State.inherit_dom _ _ _ _ _ _)
  have hgood₁ : Good P₀ .cont T₁ := by
    refine ⟨hT₁N ▸ hN, by rw [hT₁N]; omega, ?_⟩
    show HierInv T₁.G T₁.dom T₁.hier
    rw [hT₁, State.inherit_G, State.inherit_dom, State.inherit_hier]
    exact HierInv.mono hhi le_rfl hD₁.subset
  have hcan₁ := canon_first hv' hD₁
  have hcall₁ := ih .cont _ hgood₁ (mlt_of_size hT₁N hsz₁) k e c hc _ hcan₁
  have hk := card_eq e
  refine FunAll.intro hf ?_
  -- Step 1: the largest orbit.
  have d1 := Det.call (Det.mk2 (Det.arg' (P := Pg) (vs := [.nat k, encGroup gs, indVal e S.dom, xv,
    yv, hv0, rv, boolVal S.floor, .nat S.h, .nat S.N]) (rest := []) (j := 1) rfl)
    (Det.arg' (j := 2) rfl)) hloD
  refine EvalAll.letE d1 fun pv cp hp => ?_
  obtain ⟨rfl, hcp⟩ := hp
  refine EvalAll.letE (Det.get' (Det.var' (i := 1)
    (v := .list [indVal e D₁, indVal e (S.dom \ D₁)]) rfl) (Det.nat 0) (v := indVal e D₁) rfl)
    fun d1v cd1 hd1 => ?_
  obtain ⟨rfl, hcd1⟩ := hd1
  refine EvalAll.letE (Det.get' (Det.var' (i := 1)
    (v := .list [indVal e D₁, indVal e (S.dom \ D₁)]) rfl) (Det.nat 1)
    (v := indVal e (S.dom \ D₁)) rfl) fun d2v cd2 hd2 => ?_
  obtain ⟨rfl, hcd2⟩ := hd2
  -- Weights.
  have wD : ∀ D' : Set Ω, (indVal e D').wt ≤ k * 7 + 4 := fun D' => DomVal.wt_le (domVal_indVal e D')
  have wG : (encGroup gs).wt < stateW k S := (wt_le_wt_list (by simp)).trans_le hwv
  have wY : yv.wt < stateW k S := (wt_le_wt_list (by simp)).trans_le hwv
  have wAW : 8 * (k + 1) ^ 2 ≤ ansW k := by unfold ansW; omega
  have wkk : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have wC₁ := (Canon.wt_le hcan₁).trans (stateW_first (k := k) S hD₁)
  have wL := wt_list2_le (encGroup gs) (indVal e S.dom)
  have wP := wt_list2_le (indVal e D₁) (indVal e (S.dom \ D₁))
  have wD₁ := wD D₁
  have wD₂ := wD (S.dom \ D₁)
  have wD₀ := wD S.dom
  -- The bound `Z¹⁵`.
  have hZ1 : 1 ≤ (stateW k S + ansW k + 1) ^ 15 := Nat.one_le_pow _ _ (by omega)
  have hZZ : stateW k S + ansW k + 1 ≤ (stateW k S + ansW k + 1) ^ 15 :=
    Nat.le_self_pow (by norm_num) _
  have hkZ : (k + 1) ^ 15 ≤ (stateW k S + ansW k + 1) ^ 15 :=
    Nat.pow_le_pow_left (by have : k + 1 ≤ stateW k S := (by unfold stateW; omega); omega) _
  -- Step 1b: the row test of the first child.
  classical
  have hspl := split_spec hsp e S hrv hD₁.nonempty
  have wRV : rv.wt < stateW k S := (wt_le_wt_list (by simp)).trans_le hwv
  have wSP := wt_list2_le rv (indVal e D₁)
  refine EvalAll.letE (Det.call (Det.mk2 (Det.arg' (j := 6) (v := rv) rfl)
    (Det.var' (i := 2) (v := indVal e D₁) rfl)) hspl) fun spv csp hspv => ?_
  obtain ⟨rfl, hcsp⟩ := hspv
  have wsp : (Val.nat (if S.ColsSplit D₁ then 1 else 0)).wt ≤ 3 := by
    split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
  have hspZ : splitK * ((Val.list [rv, indVal e D₁]).wt + 1) ^ 3 ≤
      splitK * 125 * (stateW k S + ansW k + 1) ^ 15 := by
    have h1 : (Val.list [rv, indVal e D₁]).wt + 1 ≤ 5 * (stateW k S + ansW k + 1) := by
      have := wD D₁; have : k * 7 + 4 ≤ stateW k S := by unfold stateW; omega
      omega
    have h2 : (stateW k S + ansW k + 1) ^ 3 ≤ (stateW k S + ansW k + 1) ^ 15 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    calc splitK * ((Val.list [rv, indVal e D₁]).wt + 1) ^ 3
        ≤ splitK * (5 * (stateW k S + ansW k + 1)) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 3)
      _ = splitK * 125 * (stateW k S + ansW k + 1) ^ 3 := by ring
      _ ≤ splitK * 125 * (stateW k S + ansW k + 1) ^ 15 := Nat.mul_le_mul_left _ h2
  -- Step 2: `Continue` on the first orbit.
  refine EvalAll.letE (call_child I (firstArg_det (eS := .var 4) (eD := .var 2)
    (c := 6 * stateW k S + 2 * ansW k + 60) ((Det.var' (i := 4) rfl).mono (by omega))
    ((Det.var' (i := 2) rfl).mono (by have := wD D₁; omega)) (by omega)) hcall₁)
    fun u₁ cu₁ hu₁ => ?_
  obtain ⟨A₁, r₁, cb₁, hA₁, hcb₁, hcu₁⟩ := hu₁
  have wu₁ := hA₁.wt_le
  rcases hA₁ with ⟨rfl, rfl⟩ | ⟨x₁, gs₁, rfl, hl₁, hA₁⟩
  · -- The first answer is empty: so is the answer (`Run.orbitStop`).
    refine EvalAll.ite (Det.length (Det.var' (i := 5) (v := .list []) rfl)) (fun _ _ h => ⟨_, h.1⟩)
      fun x cc hx => ?_
    obtain ⟨hx, hcc⟩ := hx
    cases hx
    simp only [List.length_nil, if_true]
    refine (Det.var' (i := 5) (v := .list []) rfl).post fun c' hc' => ?_
    let r := Run.orbitStop hs hint hD₁ (S₁ := T₁) (S.inherit_inst _ _ _ _ _) hT₁N
      (State.inherit_hier _ _ _ _ _ _) (first_book S hD₁) r₁
    refine ⟨∅, none, r, rfl, by simp [r, Run.kind], Or.inl ⟨rfl, rfl⟩, ?_⟩
    have hWn := hW r.node (Or.inl rfl)
    simp only [Run.node] at hWn
    rw [hk] at hWn
    have hown : ∀ v', ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) ≤ I.own .cont r v' := by
      intro v'
      simp only [own, reduceCtorEq, if_false]
      exact hWn.trans (le_max_right _ _)
    have hch : I.childCost r = r₁.total I.work := by
      simp only [r, childCost, Run.children, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, charge, reduceCtorEq, if_false]
    rw [hch]
    have key : ∀ n : ℕ, n ≤ orbK * (stateW k S + ansW k + 1) ^ 15 + cb₁ →
        (n : ℝ) ≤ I.own .cont r (.list [.nat k, encGroup gs, indVal e S.dom, xv, yv, hv0, rv,
          boolVal S.floor, .nat S.h, .nat S.N]) + r₁.total I.work := by
      intro n hn
      have hn' : (n : ℝ) ≤ ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) + cb₁ := by
        exact_mod_cast hn
      linarith [hown (.list [.nat k, encGroup gs, indVal e S.dom, xv, yv, hv0, rv,
        boolVal S.floor, .nat S.h, .nat S.N])]
    apply key
    simp only [List.length_nil] at hcc
    simp only [orbK, loK, splitK] at hcp hcsp hspZ ⊢
    omega
  · -- The first answer is `[t, H₁]`.
    obtain ⟨ht, hgens₁⟩ := first_answer hD₁.invariant
      (S₁ := T₁) (S.inherit_inst _ _ _ _ _) r₁ hA₁
    have htx : toFin e ((toFin e).symm x₁) = x₁ := MulEquiv.apply_symm_apply _ _
    generalize (toFin e).symm x₁ = t at ht htx
    refine EvalAll.ite (Det.length (Det.var' (i := 5) (v := .list [encPerm x₁, encGroup gs₁]) rfl))
      (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
    obtain ⟨hx, hcc⟩ := hx
    cases hx
    rw [if_neg (show [encPerm x₁, encGroup gs₁].length ≠ 0 by simp)]
    refine EvalAll.letE (Det.get' (Det.var' (i := 5) (v := .list [encPerm x₁, encGroup gs₁]) rfl)
      (Det.nat 0) (v := encPerm x₁) rfl) fun xv₁ cx₁ hx₁ => ?_
    obtain ⟨rfl, hcx₁⟩ := hx₁
    refine EvalAll.letE (Det.get' (Det.var' (i := 5) (v := .list [encPerm x₁, encGroup gs₁]) rfl)
      (Det.nat 1) (v := encGroup gs₁) rfl) fun gv₁ cg₁ hg₁ => ?_
    obtain ⟨rfl, hcg₁⟩ := hg₁
    -- Step 3: the colors `y ∘ t`.
    have hyv' : yv = .list ((List.finRange k).map fun i => Val.nat (c (S.y (e.symm i)))) := hyv
    have hgat := gather_spec hga (L := (List.finRange k).map fun i => Val.nat (c (S.y (e.symm i))))
      (is := (List.finRange k).map fun i => (x₁ i : ℕ)) (by simp)
    rw [← htx, gather_colors e c S.y t, ← encPerm_eq_natList, htx, ← hyv'] at hgat
    refine EvalAll.letE (Det.call (Det.mk2 (Det.arg' (j := 4) (v := yv) rfl)
      (Det.var' (i := 6) (v := encPerm x₁) rfl)) hgat) fun y₂ cy₂ hy₂ => ?_
    obtain ⟨rfl, hcy₂⟩ := hy₂
    -- Step 4: `Continue` on the rest.
    have hinv : Invariant (autGroup S.G D₁ hD₁.invariant S.x) (S.dom \ D₁) :=
      (S.dom_inv.diff hD₁.invariant).mono (autGroup_le S.G D₁ hD₁.invariant S.x)
    have hsz := orbitChain_sizes (S₁ := T₁)
      (S₂ := S.resetChild _ _ hinv S.x (S.y ∘ t)) hint hD₁ (State.inherit_dom _ _ _ _ _ _) rfl
    have hgood₂ : Good P₀ .cont (S.resetChild _ _ hinv S.x (S.y ∘ t)) :=
      ⟨hN, show _ ≤ S.N by omega, HierInv.mono hhi (autGroup_le S.G D₁ hD₁.invariant S.x) Set.diff_subset⟩
    have hcan₂ := canon_resetChild hv' (D' := S.dom \ D₁) (hD' := hinv) (y' := S.y ∘ t)
      (gv' := encGroup gs₁) (yv' := encFun fun i => c ((S.y ∘ t) (e.symm i)))
      ⟨gs₁, rfl, hgens₁, hl₁⟩ rfl (fun a => (hv'.colors (t a)).2)
    have hcall₂ := ih .cont _ hgood₂ (mlt_resetChild (by omega)) k e c hc _ hcan₂
    have wC₂ := (Canon.wt_le hcan₂).trans (stateW_resetChild (k := k) S _ _ hinv S.x (S.y ∘ t))
    have wY₂ : (encFun fun i => c ((S.y ∘ t) (e.symm i))).wt <
        (childVal k (encGroup gs₁) (indVal e (S.dom \ D₁)) xv
          (encFun fun i => c ((S.y ∘ t) (e.symm i))) hv0 S.N).wt := wt_le_wt_list (by simp)
    have wG₁ : (encGroup gs₁).wt < (Val.list [encPerm x₁, encGroup gs₁]).wt :=
      wt_le_wt_list (by simp)
    have wX₁ : (encPerm x₁).wt < (Val.list [encPerm x₁, encGroup gs₁]).wt :=
      wt_le_wt_list (by simp)
    have wYX := wt_list2_le yv (encPerm x₁)
    have wpx₁ := wt_encPerm_le x₁
    have hZ3 : (stateW k S + ansW k + 1) ^ 3 ≤ (stateW k S + ansW k + 1) ^ 15 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    have hg3 : ((Val.list [yv, encPerm x₁]).wt + 1) ^ 3 ≤ 343 * (stateW k S + ansW k + 1) ^ 15 := by
      have h1 : (Val.list [yv, encPerm x₁]).wt + 1 ≤ 7 * (stateW k S + ansW k + 1) := by omega
      calc ((Val.list [yv, encPerm x₁]).wt + 1) ^ 3 ≤ (7 * (stateW k S + ansW k + 1)) ^ 3 :=
            Nat.pow_le_pow_left h1 3
        _ = 343 * (stateW k S + ansW k + 1) ^ 3 := by ring
        _ ≤ 343 * (stateW k S + ansW k + 1) ^ 15 := Nat.mul_le_mul_left _ hZ3
    have ey₂ : (Val.list ((List.finRange k).map fun i => Val.nat (c ((S.y ∘ t) (e.symm i))))).wt =
        (encFun fun i => c ((S.y ∘ t) (e.symm i))).wt := rfl
    have hk3 : (k + 1) ^ 3 ≤ (stateW k S + ansW k + 1) ^ 15 :=
      (Nat.pow_le_pow_right (by omega) (by norm_num : 3 ≤ 15)).trans hkZ
    refine EvalAll.letE (call_child I (childArg_det (eG := .var 7) (eD := .var 3) (eY := .var 8)
      (c := 2 * stateW k S + 2 * ansW k + 20) ((Det.var' (i := 7) rfl).mono (by omega))
      ((Det.var' (i := 3) rfl).mono (by omega))
      ((Det.var' (i := 8) rfl).mono (by omega)) (by omega)) hcall₂) fun u₂ cu₂ hu₂ => ?_
    obtain ⟨A₂, r₂, cb₂, hA₂, hcb₂, hcu₂⟩ := hu₂
    have wu₂ := hA₂.wt_le
    rcases hA₂ with ⟨rfl, rfl⟩ | ⟨x₂, gs₂, rfl, hl₂, hA₂⟩
    · -- The second answer is empty: so is the answer.
      refine EvalAll.ite (Det.length (Det.var' (i := 9) (v := .list []) rfl))
        (fun _ _ h => ⟨_, h.1⟩) fun x cc' hx => ?_
      obtain ⟨hx, hcc'⟩ := hx
      cases hx
      simp only [List.length_nil, if_true]
      refine (Det.var' (i := 9) (v := .list []) rfl).post fun c' hc' => ?_
      let r := Run.orbitChain hs hint hD₁ (S₁ := T₁)
        (S₂ := S.resetChild _ _ hinv S.x (S.y ∘ t)) (S.inherit_inst _ _ _ _ _) hT₁N
        (State.inherit_hier _ _ _ _ _ _) (first_book S hD₁) r₁ t ht
        ⟨rfl, rfl, rfl, rfl⟩ rfl rfl rfl r₂
      refine ⟨_, none, r, rfl, by simp [r, Run.kind], Or.inl ⟨rfl, Set.smul_set_empty⟩, ?_⟩
      have hWn := hW r.node (Or.inr rfl)
      simp only [Run.node] at hWn
      rw [hk] at hWn
      have hown : ∀ v', ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) ≤ I.own .cont r v' := by
        intro v'
        simp only [own, reduceCtorEq, if_false]
        exact hWn.trans (le_max_right _ _)
      have hch : I.childCost r = r₁.total I.work + r₂.total I.work := by
        simp only [r, childCost, Run.children, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, charge, reduceCtorEq, if_false]
      rw [hch]
      have key : ∀ n : ℕ, n ≤ orbK * (stateW k S + ansW k + 1) ^ 15 + cb₁ + cb₂ →
          (n : ℝ) ≤ I.own .cont r (.list [.nat k, encGroup gs, indVal e S.dom, xv, yv, hv0, rv,
            boolVal S.floor, .nat S.h, .nat S.N]) + (r₁.total I.work + r₂.total I.work) := by
        intro n hn
        have hn' : (n : ℝ) ≤ ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) + cb₁ + cb₂ := by
          exact_mod_cast hn
        linarith [hown (.list [.nat k, encGroup gs, indVal e S.dom, xv, yv, hv0, rv,
          boolVal S.floor, .nat S.h, .nat S.N])]
      apply key
      simp only [List.length_nil, List.length_cons] at hcc hcc'
      simp only [orbK, loK, gatherK, splitK] at hcp hcy₂ hc' hcsp hspZ ⊢
      omega
    · -- The answer `[t t₂, H₂]`.
      refine EvalAll.ite (Det.length (Det.var' (i := 9)
        (v := .list [encPerm x₂, encGroup gs₂]) rfl)) (fun _ _ h => ⟨_, h.1⟩) fun x cc' hx => ?_
      obtain ⟨hx, hcc'⟩ := hx
      cases hx
      rw [if_neg (show [encPerm x₂, encGroup gs₂].length ≠ 0 by simp)]
      refine (Det.mk2 (Det.call (Det.mk2 (Det.var' (i := 6) rfl)
        (Det.get' (Det.var' (i := 9) (v := .list [encPerm x₂, encGroup gs₂]) rfl) (Det.nat 0)
          (v := encPerm x₂) rfl)) (compose_spec hco x₁ x₂))
        (Det.get' (Det.var' (i := 9) (v := .list [encPerm x₂, encGroup gs₂]) rfl) (Det.nat 1)
          (v := encGroup gs₂) rfl)).post fun c' hc' => ?_
      let r := Run.orbitChain hs hint hD₁ (S₁ := T₁)
        (S₂ := S.resetChild _ _ hinv S.x (S.y ∘ t)) (S.inherit_inst _ _ _ _ _) hT₁N
        (State.inherit_hier _ _ _ _ _ _) (first_book S hD₁) r₁ t ht
        ⟨rfl, rfl, rfl, rfl⟩ rfl rfl rfl r₂
      refine ⟨_, none, r, rfl, by simp [r, Run.kind], Or.inr ⟨x₁ * x₂, gs₂, rfl, hl₂, ?_⟩, ?_⟩
      · rw [chain_answer hA₂, htx]
      have hWn := hW r.node (Or.inr rfl)
      simp only [Run.node] at hWn
      rw [hk] at hWn
      have hown : ∀ v', ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) ≤ I.own .cont r v' := by
        intro v'
        simp only [own, reduceCtorEq, if_false]
        exact hWn.trans (le_max_right _ _)
      have hch : I.childCost r = r₁.total I.work + r₂.total I.work := by
        simp only [r, childCost, Run.children, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, charge, reduceCtorEq, if_false]
      rw [hch]
      have key : ∀ n : ℕ, n ≤ orbK * (stateW k S + ansW k + 1) ^ 15 + cb₁ + cb₂ →
          (n : ℝ) ≤ I.own .cont r (.list [.nat k, encGroup gs, indVal e S.dom, xv, yv, hv0, rv,
            boolVal S.floor, .nat S.h, .nat S.N]) + (r₁.total I.work + r₂.total I.work) := by
        intro n hn
        have hn' : (n : ℝ) ≤ ((orbK * (stateW k S + ansW k + 1) ^ 15 : ℕ) : ℝ) + cb₁ + cb₂ := by
          exact_mod_cast hn
        linarith [hown (.list [.nat k, encGroup gs, indVal e S.dom, xv, yv, hv0, rv,
          boolVal S.floor, .nat S.h, .nat S.N])]
      have := wt_encPerm_le x₂
      have := wt_encPerm_le (x₁ * x₂)
      have := wt_list2_le (encPerm x₁) (encPerm x₂)
      have := wt_list2_le (encPerm (x₁ * x₂)) (encGroup gs₂)
      have : (encGroup gs₂).wt < (Val.list [encPerm x₂, encGroup gs₂]).wt := wt_le_wt_list (by simp)
      apply key
      simp only [List.length_nil, List.length_cons] at hcc hcc'
      simp only [orbK, loK, gatherK, permK, splitK] at hcp hcy₂ hc' hcsp hspZ ⊢
      omega

end Iface

end GI.Impl
