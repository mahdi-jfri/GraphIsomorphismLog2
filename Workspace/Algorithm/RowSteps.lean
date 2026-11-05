module

public import Workspace.Algorithm.RowTerminalOf
public import Workspace.Algorithm.ColumnStepOf
public import Workspace.Algorithm.HierInv
public import Workspace.Algorithm.ColumnDrop

@[expose] public section

/-!
# The row step: the row terminal and the column step (Algorithm 4)

`RowStep(S, Γ)` (Algorithm 4) is used when the physical kernel orbits have a natural action
on `q > λ` labels. It constructs the independent-row normal form (Theorems A.17 and A.18) and
its within-row variation `L` (the group `N` of the normal form). If `L` is transitive on a
row, it returns the row terminal (Theorem A.23). Otherwise it retains the columns of
Lemma A.14 and continues.

Both branches carry the same structural data, `RowForm S L`:

* the natural row labels `label : Ω → Γ` of the giant labels `L` (`NaturalRows`);
* the identification `e : B × Γ ≃ dom` with `label (e (b, i)) = i` (Theorem A.17);
* the clean complement `s : Alt(Γ) → G|_dom`, pure (`s(p)` moves `e(b, i)` to `e(b, p i)`),
  and a complement of the block kernel (Theorem A.17);
* the row normal form `N* ◁ N ◁ H = K[B_{i0}]` (`GI.Paper.IsRowNormalForm`, Theorem A.18).

The data are stated for the faithful image `G|_dom` of the state on its domain (Section 3:
"Every fresh call uses the faithful permutation image on its own active domain").

## The row terminal

`RowTerminal P S L` adds the map `φ : N → A` with kernel `N*` (so `A = N/N*`), the
transitivity of `N` on `B` (Theorem A.23: "assume additionally that `N` is transitive on
`B`"), and the row size bound of Section 6.2 ("The row size is at most `N^{1-α}`").
Its script is *defined* from these data by the procedure of Theorem A.23
(`RowTerminal.script`):

1. ask `Solve` on every pair of rows under `N` ("classify the local strings into
   `N`-orbits");
2. ask `Solve` on every pair of an `x`-row and a `y`-row under `H` ("store every needed coset
   `Iso_H(z_a, z_c)`");
3. from these tables, choose a representative of each type, form the two type multisets,
   compute the residual transporter by Corollary A.22 (`radicalTransport`) and, above each
   residual element `h`, keep the `J`-elements `μ` whose corrected local maps `k_i(h) μ_i`
   lie in the stored cosets.

`RowTerminal.exact` proves from Theorem A.23 (`GI.Multicoset.terminalTransport_eq`) that,
when the calls are exact, the result is the exact answer of the state. The inclusion of the
group in `K R₀` that A.23 assumes is derived from A.17 and A.18 (`actsAs_inG`).

## The column step

`ColumnStep S L` adds the intransitivity of `N` (`t ≥ 2` orbits) and the retained tower
(Section 3.3, "We keep a hierarchy of such partitions down to singletons"; Lemma A.14, "write a
local block tower as a point-stabilizer chain `P = L_0 < ⋯ < L_s = H`"): the hierarchy is the
local tower inside a row followed by the row interval of ratio `q` ("The currently acted
natural row-block level is included in the inherited tower before this refactoring"). The
subgroups `L_j` are the stabilizers in `H` of the blocks of a base point (`localTower`); the
stored ratios are their indices.

Everything the recursion uses is then defined from these data:

* the row partition (`ColumnStep.rowPart`): the label fibers;
* the column partition (`ColumnStep.cols`): `[m] × Δ_j` for the `N`-orbits `Δ_j`
  (Lemma A.14);
* the new hierarchy (`ColumnStep.hier'`): the lower pieces of the tower split
  (`towerSplit`, eq. `modular-index-split`), then the row interval with the columns as its
  coarse end, then the upper pieces ("the clean product interchanges the ratio sequence
  `r_1, …, r_s, m` with `m, r_1, …, r_s`").

So neither branch can be met by data that do not come from these theorems: the row terminal's
script is a fixed function of its data, and the column step's partitions and hierarchy are.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Multicoset GI.Paper GI.NormalTranspose
open scoped Pointwise

variable {Ω C : Type}

/-! ### Tables of calls -/

namespace Script

variable {α β : Type}

/-- Ask `Solve` on `st i` for each `i` of a list, and return the table of the answers. -/
def table {ι : Type} [DecidableEq ι] {Ω' C' : Type} (st : ι → State Ω' C') :
    List ι → Script (ι → Set (Perm Ω'))
  | [] => done fun _ => ∅
  | i :: l => ask .solve (st i) fun A => (table st l).bind fun f => done (Function.update f i A)

theorem evalExact_table {ι : Type} [DecidableEq ι] {Ω' C' : Type} (st : ι → State Ω' C') :
    ∀ (l : List ι), ∀ i ∈ l, (table st l).evalExact i = (st i).answer
  | [], _, h => absurd h List.not_mem_nil
  | j :: l, i, hi => by
    simp only [table, evalExact, evalExact_bind]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Function.update_of_ne hij]
      exact evalExact_table st l i ((List.mem_cons.1 hi).resolve_left hij)

theorem callsExact_table {ι : Type} [DecidableEq ι] {Ω' C' : Type} (st : ι → State Ω' C')
    (p : ∀ {Ω'' C'' : Type}, Mode → State Ω'' C'' → Prop) (hp : ∀ i, p .solve (st i)) :
    ∀ l : List ι, (table st l).CallsExact p
  | [] => trivial
  | i :: l => by
    refine ⟨hp i, ?_⟩
    exact callsExact_bind _ _ (callsExact_table st p hp l) trivial

end Script

/-! ### The structural data of the row step -/

/-- **The data of the row normal form** (Theorems A.17 and A.18), on the faithful image of the
state on its domain, for the natural row labels of the giant labels `L`. -/
structure RowForm (S : State Ω C) (L : GiantLabels S) where
  /-- The within-row coordinate set, `|B| = b`. -/
  B : Type
  [fin : Fintype B]
  [dec : DecidableEq B]
  /-- The natural row labels (Algorithm 5: "Recover the one-label or two-label map for the
  physical kernel orbits"; "this map is natural"). -/
  label : Ω → Fin L.q
  natural : NaturalRows S L label
  /-- The identification `Ω = B × [m]` of Theorem A.17: block `i` is `B × {i}`. -/
  e : B × Fin L.q ≃ S.dom
  e_label : ∀ b i, label (e (b, i)) = i
  /-- Lemma A.14 uses `m ≥ 4`; Theorem A.18 is applied under (LG1), which gives `m ≥ 17`. -/
  four_le : 4 ≤ L.q
  /-- The clean complement `R = s(Alt(m))` of Theorem A.17: pure, and a complement of the
  block kernel. -/
  s : alternatingGroup (Fin L.q) →* S.domGroup
  pure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)
  complement : (blockKernel e).IsComplement' s.range
  /-- The row normal form of Theorem A.18, for the block `i0`. -/
  i0 : Fin L.q
  Nl : Subgroup (cleanLocalGroup S.domGroup e i0)
  Nstar : Subgroup (cleanLocalGroup S.domGroup e i0)
  [Nl_normal : Nl.Normal]
  [Nstar_normal : Nstar.Normal]
  rnf : IsRowNormalForm S.domGroup (blockKernel e) e i0 s Nl Nstar

attribute [instance] RowForm.fin RowForm.dec RowForm.Nl_normal RowForm.Nstar_normal

namespace RowForm

variable {S : State Ω C} {L : GiantLabels S} (F : RowForm S L)

/-- `H = K[B_{i0}] ≤ Sym(B)`. -/
abbrev Hb : Subgroup (Perm F.B) := cleanLocalGroup S.domGroup F.e F.i0

/-- `N ≤ Sym(B)`. -/
abbrev Nb : Subgroup (Perm F.B) := F.Nl.map F.Hb.subtype

theorem Nb_le : F.Nb ≤ F.Hb := by
  rintro _ ⟨n, -, rfl⟩
  exact n.2

theorem normalizes : Normalizes F.Hb F.Nb := by
  rintro h hh _ ⟨n, hn, rfl⟩
  refine ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, F.Nl_normal.conj_mem n hn ⟨h, hh⟩, rfl⟩

theorem three_le (F : RowForm S L) : 3 ≤ L.q := by have := F.four_le; omega

/-- The lifts of Theorem A.18 satisfy `h⁻¹ k_i(h) ∈ N`. -/
theorem lift_mem {h : Perm F.B} (hh : h ∈ F.Hb) (i : Fin L.q) :
    h⁻¹ * rowLift F.e F.i0 h i ∈ F.Nb :=
  rowLift_mem F.e F.i0 F.pure F.three_le F.rnf hh i

theorem lift_mem_H {h : Perm F.B} (hh : h ∈ F.Hb) (i : Fin L.q) : rowLift F.e F.i0 h i ∈ F.Hb := by
  have := F.Hb.mul_mem hh (F.Nb_le (F.lift_mem hh i))
  rwa [mul_inv_cancel_left] at this

end RowForm

/-! ### The row terminal -/

attribute [local instance] stringRAct

/-- A call on one row: `Solve` under `K ≤ Sym(B)` on all of `B`, for the strings `z` and `w`.
Its answer is `{g ∈ K | z^g = w}`. It is a fresh call: a new phase on `|B|` positions with no
row record. -/
def rowState {B C' : Type} [Fintype B] (K : Subgroup (Perm B)) (z w : B → C') : State B C' :=
  ⟨K, Set.univ, fun _ _ _ => Iff.rfl, w, z, [], none, false, 2, le_rfl, Fintype.card B,
    CounterInv.reset _ _ _ _,
    CarrierOK.none _ _ _⟩

theorem rowState_answer {B C' : Type} [Fintype B] (K : Subgroup (Perm B)) (z w : B → C') :
    (rowState K z w).answer = {g | g ∈ K ∧ z ↼ g = w} := by
  ext g
  simp only [State.answer, GI.Algorithm.answer, rowState, Set.mem_univ, true_implies,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hg, h⟩; exact ⟨hg, funext h⟩
  · rintro ⟨hg, h⟩; exact ⟨hg, fun v => congrFun h v⟩

theorem rowState_size {B C' : Type} [Fintype B] (K : Subgroup (Perm B)) (z w : B → C') :
    (rowState K z w).size = Fintype.card B := by
  simp [State.size, rowState, Nat.card_eq_fintype_card]

/-- **The row terminal** (Theorem A.23, `thm:transitive-gat-terminal`; Algorithm 4: "if `L` is
transitive on a row then compute all needed row types and local isomorphism cosets using
`Solve`; return the full row-terminal answer from these tables and the normal form"). The
data of the row normal form, the map `φ : N → A = N/N*`, the transitivity of `N` on `B`,
and the row size bound. -/
structure RowTerminal (P : Params) (S : State Ω C) (L : GiantLabels S) extends RowForm S L where
  /-- `A = N/N*`, given by a map `φ : N → A` with kernel `N*`. -/
  A : Type
  [commA : CommGroup A]
  φ : (Nl.map (cleanLocalGroup S.domGroup e i0).subtype) →* A
  φ_ker : ∀ n, φ n = 1 ↔ n.val ∈ Nstar.map (cleanLocalGroup S.domGroup e i0).subtype
  /-- Theorem A.23: "assume additionally that `N` is transitive on `B`" (Algorithm 4: "if `L`
  is transitive on a row"). -/
  transitive : MulAction.IsPretransitive Nl B
  /-- Section 6.2: "The row size is at most `N^{1-α}`" (`GI.Paper.cases_row_size`: from
  `q > λ = N^α` and `qb = s ≤ N`). -/
  row_size : (Fintype.card B : ℝ) ≤ (S.N : ℝ) ^ (1 - P.α)
  /-- The order of the `N`-tests: every ordered pair of the `2q` rows exactly once (the paper
  fixes no order; the default is `Finset.toList`). -/
  tests : List ((Fin L.q ⊕ Fin L.q) × (Fin L.q ⊕ Fin L.q))
  tests_nodup : tests.Nodup
  mem_tests : ∀ ac, ac ∈ tests
  /-- The order of the coset calls: every pair of a row of `x` and a row of `y` exactly once. -/
  cosets : List (Fin L.q × Fin L.q)
  cosets_nodup : cosets.Nodup
  mem_cosets : ∀ ij, ij ∈ cosets
  /-- A solvable-quotient subgroup `R' ≤ H` with `N ≤ R'` and `R'/N` solvable (by default,
  `radicalSubgroup Hb Nb` of Lemma A.21). -/
  rad : Subgroup (Perm B)
  rad_le : rad ≤ toRowForm.Hb
  Nb_le_rad : toRowForm.Nb ≤ rad
  rad_solv : ∃ ℓ, GI.Multicoset.relDerived rad toRowForm.Nb ℓ ≤ toRowForm.Nb

attribute [instance] RowTerminal.commA

namespace RowTerminal

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

/-- The `2m` rows: the rows of `x`, then the rows of `y`. -/
def rows : Fin L.q ⊕ Fin L.q → I.B → C :=
  Sum.elim (rowTuple I.e S.x) (rowTuple I.e S.y)

/-- The `N`-test on two rows (a degree-`b` string call under `N`). -/
def typeCall (ac : (Fin L.q ⊕ Fin L.q) × (Fin L.q ⊕ Fin L.q)) : State I.B C :=
  rowState I.Nb (I.rows ac.1) (I.rows ac.2)

/-- The coset call `Iso_H(x_i, y_j)` (a degree-`b` string call under `H`). -/
def cosetCall (ij : Fin L.q × Fin L.q) : State I.B C :=
  rowState I.Hb (rowTuple I.e S.x ij.1) (rowTuple I.e S.y ij.2)

open Classical in
/-- The representative of the type of a row, from the `N`-test table: a row of the same
`N`-type ("For each occurring type `a`, choose a representative `z_a`"). -/
noncomputable def rep (TN : (Fin L.q ⊕ Fin L.q) × (Fin L.q ⊕ Fin L.q) → Set (Perm I.B))
    (a : Fin L.q ⊕ Fin L.q) : Fin L.q ⊕ Fin L.q :=
  if h : ∃ c, (TN (a, c)).Nonempty then Classical.choose h else a

/-- The type multiset of one side, from the `N`-test table. -/
noncomputable def typesOf (TN : (Fin L.q ⊕ Fin L.q) × (Fin L.q ⊕ Fin L.q) → Set (Perm I.B))
    (side : Fin L.q → Fin L.q ⊕ Fin L.q) : Multiset (Set (I.B → C)) :=
  Finset.univ.val.map fun i => orbitN I.Nb (I.rows (I.rep TN (side i)))

/-- The transporter assembled from the tables (the procedure of Theorem A.23): residual
elements `h` of the type multisets by Corollary A.22, and above each the `J`-elements `μ`
(zero-sum labels, even matching) whose corrected local maps `k_i(h) μ_i` lie in the stored
cosets `Iso_H(x_i, y_{π i})`. -/
noncomputable def tableTransport
    (TN : (Fin L.q ⊕ Fin L.q) × (Fin L.q ⊕ Fin L.q) → Set (Perm I.B))
    (TH : Fin L.q × Fin L.q → Set (Perm I.B)) :
    Set ((Fin L.q → Perm I.B) × Perm (Fin L.q)) :=
  {p | ∃ h ∈ (radicalTransport I.Hb I.Nb (I.typesOf TN Sum.inl) (I.typesOf TN Sum.inr)).set,
    ∃ μ, InJ I.Nb I.φ μ p.2 ∧ p.1 = rowLift I.e I.i0 h * μ ∧
      ∀ i, rowLift I.e I.i0 h i * μ i ∈ TH (i, p.2 i)}

/-- The answer returned, lifted to `Ω`: the elements of the state's group whose action on
the domain is in the assembled transporter. -/
noncomputable def assemble (TN : (Fin L.q ⊕ Fin L.q) × (Fin L.q ⊕ Fin L.q) → Set (Perm I.B))
    (TH : Fin L.q × Fin L.q → Set (Perm I.B)) : Set (Perm Ω) :=
  {g | g ∈ S.G ∧ ∃ p ∈ I.tableTransport TN TH, ActsAs I.e g p.1 p.2}

/-- **The script of the row terminal** (Theorem A.23): the `N`-tests on all pairs of rows, the
cosets `Iso_H(x_i, y_j)`, then the assembly. Every call is a `Solve` call on `b` points. -/
noncomputable def script : Script (Set (Perm Ω)) :=
  (Script.table I.typeCall I.tests).bind fun TN =>
    (Script.table I.cosetCall I.cosets).bind fun TH => Script.done (I.assemble TN TH)

/-- Every call of the script is a fresh `Solve` call on a row, of size at most `N^{1-α}`. -/
theorem calls : I.script.CallsExact fun m T => m = .solve ∧ (T.size : ℝ) ≤ (S.N : ℝ) ^ (1 - P.α) := by
  have hrow : ∀ {C' : Type} (K : Subgroup (Perm I.B)) (z w : I.B → C'),
      ((rowState K z w).size : ℝ) ≤ (S.N : ℝ) ^ (1 - P.α) := fun K z w => by
    rw [rowState_size]; exact I.row_size
  refine Script.callsExact_bind _ _ (Script.callsExact_table _ _ (fun ac => ⟨rfl, hrow _ _ _⟩) _) ?_
  exact Script.callsExact_bind _ _ (Script.callsExact_table _ _ (fun ij => ⟨rfl, hrow _ _ _⟩) _)
    trivial

/-- The calls of the script are on finite position sets. -/
theorem calls_finite : I.script.CallsExact fun {Ω' _} _ _ => Finite Ω' := by
  refine Script.callsExact_bind _ _ (Script.callsExact_table _ _ (fun _ => Finite.of_fintype _) _) ?_
  exact Script.callsExact_bind _ _ (Script.callsExact_table _ _ (fun _ => Finite.of_fintype _) _)
    trivial

/-- With exact `N`-tests, the representative has the same type. -/
theorem orbitN_rep (a : Fin L.q ⊕ Fin L.q) :
    orbitN I.Nb (I.rows (I.rep (fun ac => (I.typeCall ac).answer) a)) = orbitN I.Nb (I.rows a) := by
  classical
  unfold rep
  split_ifs with h
  · obtain ⟨n, hn⟩ := Classical.choose_spec h
    have hn' : n ∈ (rowState I.Nb (I.rows a) (I.rows (Classical.choose h))).answer := hn
    rw [rowState_answer] at hn'
    rw [← hn'.2, orbitN_kernel hn'.1]
  · rfl

theorem typesOf_exact (side : Fin L.q → Fin L.q ⊕ Fin L.q) :
    I.typesOf (fun ac => (I.typeCall ac).answer) side =
      Finset.univ.val.map fun i => orbitN I.Nb (I.rows (side i)) := by
  unfold typesOf
  congr 1
  funext i
  exact I.orbitN_rep _

/-- **The table transport is the terminal transport** of Theorem A.23 when the tables are
exact. -/
theorem tableTransport_exact :
    I.tableTransport (fun ac => (I.typeCall ac).answer) (fun ij => (I.cosetCall ij).answer) =
      terminalTransport I.Hb I.Nb I.φ (rowLift I.e I.i0) (rowTuple I.e S.x) (rowTuple I.e S.y) := by
  have hX : I.typesOf (fun ac => (I.typeCall ac).answer) Sum.inl = types I.Nb (rowTuple I.e S.x) :=
    I.typesOf_exact _
  have hY : I.typesOf (fun ac => (I.typeCall ac).answer) Sum.inr = types I.Nb (rowTuple I.e S.y) :=
    I.typesOf_exact _
  ext ⟨d, π⟩
  simp only [tableTransport, terminalTransport, Set.mem_setOf_eq, hX, hY]
  rw [radicalTransport_set I.Nb_le I.normalizes (fixes_types _ _) (fixes_types _ _)]
  refine exists_congr fun h => and_congr_right fun hh => exists_congr fun μ =>
    and_congr_right fun hJ => and_congr_right fun _ => ?_
  have hH : ∀ i, rowLift I.e I.i0 h i * μ i ∈ I.Hb := fun i =>
    I.Hb.mul_mem (I.lift_mem_H hh.1 i) (I.Nb_le (hJ.1 i))
  rw [rowAct_eq_iff]
  simp only [cosetCall, rowState_answer, Set.mem_setOf_eq, rowAct, Perm.one_symm, Perm.one_apply,
    act_act]
  exact forall_congr' fun i => and_iff_right (hH i)

/-- **The row terminal is exact** (Theorem A.23, `GI.Multicoset.terminalTransport_eq`): when the
row calls return their exact answers, the script returns the exact answer of the state. The
inclusion of the state's group in `G = K R₀` comes from Theorems A.17 and A.18
(`actsAs_inG`). -/
theorem exact : I.script.evalExact = S.answer := by
  classical
  simp only [script, Script.evalExact_bind, Script.evalExact]
  have hTN : (Script.table I.typeCall I.tests).evalExact =
      fun ac => (I.typeCall ac).answer :=
    funext fun ac => Script.evalExact_table _ _ ac (I.mem_tests ac)
  have hTH : (Script.table I.cosetCall I.cosets).evalExact =
      fun ij => (I.cosetCall ij).answer :=
    funext fun ij => Script.evalExact_table _ _ ij (I.mem_cosets ij)
  rw [hTN, hTH]
  -- Theorem A.23: the procedure returns the full transporter `Iso_G(x, y)`.
  have hA23 := terminalTransport_eq (φ := I.φ) I.Nb_le I.normalizes
    (fun h hh i => I.lift_mem hh i) (rowTuple I.e S.x) (rowTuple I.e S.y)
  have hG := actsAs_inG I.e I.i0 I.pure I.three_le I.rnf I.complement I.φ I.φ_ker
  ext g
  change g ∈ S.G ∧ (∃ p ∈ I.tableTransport _ _, ActsAs I.e g p.1 p.2) ↔
    g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v
  rw [I.tableTransport_exact, hA23]
  constructor
  · rintro ⟨hgG, p, ⟨-, hp⟩, hact⟩
    exact ⟨hgG, (colors_iff_rowAct I.e hact S.x S.y).2 hp⟩
  · rintro ⟨hgG, hcol⟩
    obtain ⟨d, π, hInG, hact⟩ := hG g hgG
    exact ⟨hgG, (d, π), ⟨hInG, (colors_iff_rowAct I.e hact S.x S.y).1 hcol⟩, hact⟩

end RowTerminal

/-! ### The column step -/

namespace RowForm

variable {S : State Ω C} {L : GiantLabels S}

/-- The level-`j` partition of a row: the blocks of the `j`-th stored interval inside row
`i0`, read in the coordinates `e`. -/
def lvl {B : Type} (e : B × Fin L.q ≃ S.dom) (i0 : Fin L.q) (loc : List (Interval Ω)) (j : ℕ) : Setoid B :=
  if h : j < loc.length then Setoid.comap (fun c => (e (c, i0) : Ω)) loc[j].part else ⊤

/-- **The local tower** (Lemma A.14: "write a local block tower as a point-stabilizer chain
`P = L_0 < ⋯ < L_s = H`"): `L_0` is the stabilizer in `H` of a base point `b₀`, and `L_{j+1}`
the stabilizer of the level-`j` block of `b₀`. -/
def localTower {B : Type} (e : B × Fin L.q ≃ S.dom) (i0 : Fin L.q) (loc : List (Interval Ω))
    (b₀ : B) : ℕ → Subgroup (cleanLocalGroup S.domGroup e i0)
  | 0 => MulAction.stabilizer _ ({b₀} : Set B)
  | j + 1 => MulAction.stabilizer _ {c | (lvl e i0 loc j) b₀ c}

end RowForm

/-- **The column step** (Lemma A.14, `lem:normal-transpose`, applied to the row normal form of
Theorem A.18; Algorithm 4: "Let `D_1, …, D_t` be the within-row orbits of `L`. Make column `j`
the union of the copies of `D_j` in all rows. Refactor the old hierarchy by splitting and
reordering its interval factors. Inherit every interval bound, clamped by its new interval
ratio"). The data of the row normal form, the intransitivity of `N`, and the retained tower:
the local tower inside a row followed by the row interval (Section 6.2: "the row partition is
already an interval of the retained hierarchy"), and the stored ratios of the local tower are
the indices of its block stabilizers.

The retained tower `loc ++ [rowI]` is the stored hierarchy with the row level exposed at the
column step: its local levels are
invariant, nested, and the last one holds each row; it does not increase `ρ` or `Q`
(`exp_rho`, `exp_Q`). It is built from the stored hierarchy in
`Workspace/Algorithm/RowExpose.lean`. -/
structure ColumnPre (S : State Ω C) (L : GiantLabels S) extends RowForm S L where
  /-- Algorithm 4: `L` is not transitive on a row; it has `t ≥ 2` orbits. -/
  intransitive : 2 ≤ Nat.card (Quotient (MulAction.orbitRel Nl B))
  /-- The retained tower: the local intervals inside a row, then the row interval. -/
  loc : List (Interval Ω)
  rowI : Interval Ω
  /-- Section 6.2: "the row partition is already an interval of the retained hierarchy". -/
  rowI_ratio : rowI.ratio = L.q
  rowI_cap : rowI.cap ≤ rowI.ratio
  /-- The local levels are block systems of the domain, nested, and the last one holds each
  row (Section 3.3: "We keep a hierarchy of such partitions down to singletons"). -/
  loc_inv : ∀ (j : ℕ) (hj : j < loc.length), ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom,
    loc[j].part.r (g v) (g w) ↔ loc[j].part.r v w
  loc_mono : ∀ (j : ℕ) (hj : j + 1 < loc.length), ∀ v ∈ S.dom, ∀ w ∈ S.dom,
    loc[j].part.r v w → loc[j + 1].part.r v w
  loc_pos : 0 < loc.length
  loc_top : ∀ v ∈ S.dom, ∀ w ∈ S.dom, label v = label w →
    (loc[loc.length - 1]'(by omega)).part.r v w
  /-- The local levels refine the rows. -/
  loc_low : ∀ (j : ℕ) (hj : j < loc.length), ∀ v ∈ S.dom, ∀ w ∈ S.dom,
    loc[j].part.r v w → label v = label w
  /-- **The local intervals carry valid bounds** (Section 3.3, the cap invariant; Algorithm 4:
  "Inherit every interval bound"). -/
  loc_caps : ∀ (j : ℕ) (hj : j < loc.length),
    CapOK S.G S.dom (fineEnd ⊥ (loc.take j)) loc[j].part loc[j].cap
  /-- **The row interval keeps the full bound `q`** when `q ≥ 5` (Section 7.2: "The old cap is at
  least `q` because the selected alternating section belongs to that whole constituent"). -/
  rowI_cap_eq : 5 ≤ L.q → rowI.cap = L.q
  /-- The base point of the local tower. -/
  b₀ : B

/-- **The column step**: the data of `ColumnPre`, the retained tower refines the stored
hierarchy without raising `ρ` or `Q` (Section 7.1: "Splitting or restricting intervals also
cannot increase `Q`"), and the stored local ratios are the indices of the block stabilizers. -/
structure ColumnStep (S : State Ω C) (L : GiantLabels S) extends ColumnPre S L where
  exp_rho : State.hierRho (loc ++ [rowI]) ≤ State.hierRho S.hier
  exp_Q : State.hierQ (loc ++ [rowI]) ≤ State.hierQ S.hier
  tower_mono : ∀ j, RowForm.localTower e i0 loc b₀ j ≤ RowForm.localTower e i0 loc b₀ (j + 1)
  /-- The stored ratio of the `j`-th local interval is the index `[L_{j+1} : L_j]`. -/
  tower_ratio : ∀ (j : ℕ) (hj : j < loc.length),
    loc[j].ratio = (RowForm.localTower e i0 loc b₀ j).relIndex (RowForm.localTower e i0 loc b₀ (j + 1))

namespace ColumnPre

variable {S : State Ω C} {L : GiantLabels S} (I : ColumnPre S L)

/-- The row partition: the fibers of the natural row labels. -/
noncomputable def rowPart : Setoid Ω := S.domKer fun v => I.label v

/-- **The column partition of Lemma A.14**: `[m] × Δ_j` for the `N`-orbits `Δ_j`. -/
noncomputable def cols : Setoid Ω := S.domKer (colOf I.e I.Nl)

/-- The partition of the `j`-th local level, `⊤` beyond the local tower. -/
def lvlPart (j : ℕ) : Setoid Ω := if h : j < I.loc.length then I.loc[j].part else ⊤

/-- The `j`-th local level inside the rows: two points of the domain are related when they
lie in one row and in one class of the `j`-th local level. -/
noncomputable def locRow (j : ℕ) : Setoid Ω :=
  S.domKer fun v => (I.label v, (Quotient.mk (I.lvlPart j) (v : Ω) : Quotient (I.lvlPart j)))

/-- The coarse end of the lower piece of interval `j`: the level-`j` blocks inside one cell
`{i} × Δ` (the subgroup `B_j = L_j ∩ NP` of the proof of A.14). -/
noncomputable def lowerPart (j : ℕ) : Setoid Ω := I.locRow j ⊓ I.cols

/-- The coarse end of the upper piece of interval `j`: the unions `N·(block)` over all rows
(the subgroup `N L_j` of the proof of A.14, on the column quotient). Two points of the domain
are related when a chain of level-`j` steps inside rows and column steps joins them. -/
noncomputable def upperPart (j : ℕ) : Setoid Ω := I.locRow j ⊔ I.cols

/-- The split of the local intervals by eq. `modular-index-split`. -/
noncomputable def split : List (Interval Ω × Interval Ω) :=
  towerSplit (RowForm.localTower I.e I.i0 I.loc I.b₀) I.Nl I.lowerPart I.upperPart 0 I.loc

/-- **The refactored hierarchy** (Lemma A.14): the lower pieces, then the row interval with
the columns as its coarse end, then the upper pieces. Every piece keeps its origin label and
its old bound, clamped by its new ratio. -/
noncomputable def hier' : List (Interval Ω) :=
  I.split.map Prod.fst ++ [{ I.rowI with part := I.cols }] ++ I.split.map Prod.snd

theorem rowPart_inv : ∀ g ∈ S.G, ∀ v w, I.rowPart.r (g v) (g w) ↔ I.rowPart.r v w :=
  State.domKer_inv _ fun g v w h => by
    have h1 := I.natural.equivariant g v v.2
    have h2 := I.natural.equivariant g w w.2
    change I.label (S.domHom g v) = I.label (S.domHom g w)
    rw [State.domHom_apply, State.domHom_apply, h1, h2]
    exact congrArg _ h

theorem cols_inv : ∀ g ∈ S.G, ∀ v w, I.cols.r (g v) (g w) ↔ I.cols.r v w :=
  haveI : Finite S.dom := Finite.of_equiv _ I.e
  State.domKer_inv _ fun g v w h =>
    (lem_normal_transpose I.pure I.rnf (by simpa using I.four_le)).2.2.1
      ⟨S.domHom g, ⟨g, rfl⟩⟩ v w h

/-- The column partition is proper on the domain: `N` has `t ≥ 2` orbits. -/
theorem proper : ∃ v ∈ S.dom, ∃ w ∈ S.dom, ¬ I.cols.r v w := by
  haveI : Nontrivial (Quotient (MulAction.orbitRel I.Nl I.B)) :=
    Finite.one_lt_card_iff_nontrivial.1 (by have := I.intransitive; omega)
  obtain ⟨q₁, q₂, hq⟩ := exists_pair_ne (Quotient (MulAction.orbitRel I.Nl I.B))
  refine ⟨_, (I.e (q₁.out, I.i0)).2, _, (I.e (q₂.out, I.i0)).2, ?_⟩
  rw [cols, State.domKer_r_of_mem _ (I.e (q₁.out, I.i0)).2 (I.e (q₂.out, I.i0)).2]
  simp only [Subtype.coe_eta, colOf_apply, Quotient.out_eq]
  exact hq

end ColumnPre

namespace ColumnStep

variable {S : State Ω C} {L : GiantLabels S} (I : ColumnStep S L)

theorem split_ok : List.Forall₂ SplitOK I.loc I.split :=
  towerSplit_ok _ _ _ _ I.tower_mono 0 I.loc fun i hi => by
    rw [I.tower_ratio i hi, zero_add]

/-- Section 7.3: "Row and column refactoring splits and permutes old interval factors. It
preserves their origin labels and does not increase `ρ`, `Q`, or `σ`." Lemma A.14
(`GI.Paper.lem_normal_transpose_rho`) is the paper's proof for `ρ`. -/
theorem rho_le : State.hierRho I.hier' ≤ State.hierRho S.hier := by
  have h := splitHier_rho_le I.split_ok
  rw [splitHier, hierRho_append] at h
  have he := I.exp_rho
  rw [hierRho_append] at he
  rw [ColumnPre.hier', hierRho_append, hierRho_append]
  have : State.hierRho [{ I.rowI with part := I.cols }] = State.hierRho [I.rowI] := rfl
  linarith

/-- Section 7.3, as for `rho_le`, for `Q`. -/
theorem Q_le : State.hierQ I.hier' ≤ State.hierQ S.hier := by
  have h := splitHier_Q_le I.split_ok
  rw [splitHier, hierQ_append] at h
  have he := I.exp_Q
  rw [hierQ_append] at he
  rw [ColumnPre.hier', hierQ_append, hierQ_append]
  have : State.hierQ [{ I.rowI with part := I.cols }] = State.hierQ [I.rowI] := rfl
  linarith

end ColumnStep

end GI.Algorithm
