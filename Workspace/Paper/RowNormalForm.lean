import Workspace.CleanComplementPaper
import Workspace.CleanRowNormalForm
import Workspace.Paper.RowNormalFormDefs
import Workspace.Cited.TransitiveAffected

/-!
# Paper statements: Theorems A.17 and A.18

Faithful statements of `thm:logarithmic-clean-complement` (A.17) and
`thm:logarithmic-gat-normal-form` (A.18).

A group `G ≤ Sym(V)` is a subgroup of `Equiv.Perm V`. The supplied block
system is a labelling `label : V → I` of the points by the `m = |I|` blocks,
every block of size `f`. The supplied block action is a homomorphism
`φ : G → Sym(I)` with `label (g x) = φ g (label x)`; "the block action is
`Alt(m)`" says its image is `alternatingGroup I`. Its kernel `K = ker φ` is
the block kernel.

The clauses "can be constructed in polynomial time" (A.17) and "the groups,
quotient maps, and lifts are polynomial-time computable" (A.18) are
statements about algorithms on the machine model; they are left to
the machine-level programs of `Workspace/Impl/`. Here we prove the mathematical content.
-/

namespace GI.Paper

open Equiv

section
variable {V : Type} [Fintype V] {I : Type} [Fintype I] [DecidableEq I]

/-- The common first part of the proofs of A.17 and A.18: the paper's data
form a `CleanBlockAction`, and (LG2) with the odd and even completions give a
clean complement for it. -/
theorem exists_clean_complement (hcite : GI.Cited.TransitiveAffected)
    (G : Subgroup (Perm V)) (label : V → I) (f : ℕ)
    (hsize : ∀ i, Fintype.card {x : V // label x = i} = f) (hf : 0 < f)
    (φ : G →* Perm I) (hφ : ∀ (g : G) (x : V), label (g.val x) = φ g (label x))
    (hAlt : φ.range = alternatingGroup I)
    (htrans : ∀ x y : V, label x = label y → ∃ g : G, g ∈ φ.ker ∧ g.val x = y)
    (k : ℕ) (hodd : Odd k) (hLG1 : max 8 (2 + Real.logb 2 f) < (k : ℝ))
    (hm : 2 * k - 1 ≤ Fintype.card I) :
    ∃ (A : CleanBlockAction G I), A.label = label ∧ A.top.ker = φ.ker ∧
      Nonempty (PureComplement A) := by
  classical
  -- Blocks are nonempty, since they have size `f > 0`.
  have hlabel : Function.Surjective label := by
    intro i
    have hpos : 0 < Fintype.card {x : V // label x = i} := by rw [hsize i]; exact hf
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨x.val, x.property⟩
  let A := cleanBlockActionOf G label hlabel φ hφ hAlt
  have hkerA : A.top.ker = φ.ker := cleanBlockActionOf_ker G label hlabel φ hφ hAlt
  have hker : A.KernelTransitive := by
    intro x y hxy
    obtain ⟨g, hg, hgxy⟩ := htrans x y hxy
    refine ⟨g, ?_, hgxy⟩
    have hg' : g ∈ A.top.ker := by rw [hkerA]; exact hg
    exact hg'
  have hthr : A.BelowLogThreshold k := by
    intro i
    change max 8 (2 + Real.logb 2 (Fintype.card {x : V // label x = i})) < (k : ℝ)
    rw [hsize i]
    exact hLG1
  -- The odd and even completions of the paper, after (LG2) from Lemma A.15.
  exact ⟨A, rfl, hkerA, pureComplement_nonempty_log hcite A hker hthr hodd hm⟩

/-- **Theorem A.17** (Logarithmic-threshold clean complement).

Let `G ≤ Sym(V)` have a block system of `m = |I|` blocks, each of size `f`.
Suppose the block action `φ` has image `Alt(m)` and its kernel `K` is
transitive on each block. Let `k` be odd with
`k > max {8, 2 + log₂ f}` and `2k - 1 ≤ m` (LG1). Then there is an
identification `e : B × I ≃ V` with `|B| = f` (block `i` is `B × {i}`) and an
injective homomorphism `s : Alt(m) → G` such that `s p` acts only on the
block index, `(b, i) ↦ (b, p i)`. Its image `R = s(Alt(m)) ≅ Alt(m)` is a
complement to `K` in `G`: `G = KR` and `K ∩ R = 1`.

The paper's `R` is `s.range`; `IsComplement'` says that every element of
`G` is uniquely a product of an element of `K` and an element of `R`.
The cited input `hcite` is Lemma 4.3(a) of [H], used through Lemma A.15. -/
theorem thm_logarithmic_clean_complement (hcite : GI.Cited.TransitiveAffected)
    (G : Subgroup (Perm V)) (label : V → I) (f : ℕ)
    (hsize : ∀ i, Fintype.card {x : V // label x = i} = f) (hf : 0 < f)
    (φ : G →* Perm I) (hφ : ∀ (g : G) (x : V), label (g.val x) = φ g (label x))
    (hAlt : φ.range = alternatingGroup I)
    (htrans : ∀ x y : V, label x = label y → ∃ g : G, g ∈ φ.ker ∧ g.val x = y)
    (k : ℕ) (hodd : Odd k) (hLG1 : max 8 (2 + Real.logb 2 f) < (k : ℝ))
    (hm : 2 * k - 1 ≤ Fintype.card I) :
    ∃ (B : Type) (_ : Fintype B) (e : B × I ≃ V) (s : alternatingGroup I →* G),
      Fintype.card B = f ∧ (∀ b i, label (e (b, i)) = i) ∧
      Function.Injective s ∧ (∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) ∧
      φ.ker.IsComplement' s.range := by
  classical
  obtain ⟨A, hAl, hkerA, ⟨c⟩⟩ := exists_clean_complement hcite G label f hsize hf φ hφ hAlt
    htrans k hodd hLG1 hm
  subst hAl
  obtain ⟨i0⟩ : Nonempty I := Fintype.card_pos_iff.mp (by have := hodd.pos; omega)
  letI : Fintype c.Fiber := Fintype.ofEquiv _ (c.fiberEquivBlock i0).symm
  refine ⟨c.Fiber, inferInstance, c.coordinates, c.sectionHom, ?_, c.label_coordinates,
    c.sectionHom_injective, c.pure, ?_⟩
  · rw [Fintype.card_congr (c.fiberEquivBlock i0)]
    exact hsize i0
  · rw [← hkerA]
    exact c.isComplement

/-- The remark after Theorem A.17: "a threshold `m = O(log(f+2))` suffices".
If `m ≥ 2 max {8, 2 + log₂ f} + 3`, an odd `k` satisfying (LG1) exists. -/
theorem thm_logarithmic_clean_complement_threshold (f m : ℕ)
    (hm : 2 * max 8 (2 + Real.logb 2 f) + 3 ≤ (m : ℝ)) :
    ∃ k : ℕ, Odd k ∧ max 8 (2 + Real.logb 2 f) < (k : ℝ) ∧ 2 * k - 1 ≤ m := by
  set x : ℝ := max 8 (2 + Real.logb 2 f)
  have hx8 : (8 : ℝ) ≤ x := le_max_left _ _
  set k0 : ℕ := ⌊x⌋₊ + 1
  have hk0 : x < k0 := by
    have := Nat.lt_floor_add_one x
    push_cast [k0]
    exact this
  have hk0le : (k0 : ℝ) ≤ x + 1 := by
    have := Nat.floor_le (show 0 ≤ x by linarith)
    push_cast [k0]
    linarith
  rcases Nat.even_or_odd k0 with heven | hodd
  · refine ⟨k0 + 1, heven.add_one, by push_cast; linarith, ?_⟩
    have hreal : ((2 * (k0 + 1) - 1 : ℕ) : ℝ) ≤ m := by
      have h1 : 1 ≤ 2 * (k0 + 1) := by omega
      push_cast [Nat.cast_sub h1]
      linarith
    exact_mod_cast hreal
  · refine ⟨k0, hodd, hk0, ?_⟩
    have hreal : ((2 * k0 - 1 : ℕ) : ℝ) ≤ m := by
      have h1 : 1 ≤ 2 * k0 := by have := hodd.pos; omega
      push_cast [Nat.cast_sub h1]
      linarith
    exact_mod_cast hreal

/-- **Theorem A.18** (Full normal form under the logarithmic threshold).

Under the hypotheses of Theorem A.17, there are clean coordinates `e` and a
clean complement `R = s(Alt(m))` as in A.17 such that, for every block `i0`
and `H = K[B_{i0}] ≤ Sym(B)` (`cleanLocalGroup G e i0`), there exist
`N* ◁ N ◁ H` satisfying the row normal form `IsRowNormalForm`
(`Workspace/Paper/RowNormalFormDefs.lean`): `N/N*` is abelian, `M* = (N*)^m`
and `M = K ∩ N^m` satisfy `M* ◁ M ◁ G` and `M ≤ K`, `M/M*` is the zero-sum
subgroup of `(N/N*)^m`, `K/M` is the diagonal `H/N`, `MR ◁ G`, and
`G/(MR) ≅ H/N` (by `θ`, onto with kernel `MR`).

The proof is the paper's: (LG3) by the commutator computation
(`GI.row_transfer_of_five`), `[N, N] ≤ N*` from commuting transfers on two
pairs of rows, the diagonal property from a pure 3-cycle conjugate, and the
zero-sum description from concentrating the total in one coordinate.
It uses `m ≥ 5`, which (LG1) supplies: `m ≥ 2k - 1 ≥ 17`. -/
theorem thm_logarithmic_gat_normal_form (hcite : GI.Cited.TransitiveAffected)
    (G : Subgroup (Perm V)) (label : V → I) (f : ℕ)
    (hsize : ∀ i, Fintype.card {x : V // label x = i} = f) (hf : 0 < f)
    (φ : G →* Perm I) (hφ : ∀ (g : G) (x : V), label (g.val x) = φ g (label x))
    (hAlt : φ.range = alternatingGroup I)
    (htrans : ∀ x y : V, label x = label y → ∃ g : G, g ∈ φ.ker ∧ g.val x = y)
    (k : ℕ) (hodd : Odd k) (hLG1 : max 8 (2 + Real.logb 2 f) < (k : ℝ))
    (hm : 2 * k - 1 ≤ Fintype.card I) :
    ∃ (B : Type) (_ : Fintype B) (e : B × I ≃ V) (s : alternatingGroup I →* G),
      Fintype.card B = f ∧ (∀ b i, label (e (b, i)) = i) ∧
      Function.Injective s ∧ (∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) ∧
      φ.ker.IsComplement' s.range ∧
      ∀ i0 : I, ∃ (N Nstar : Subgroup (cleanLocalGroup G e i0)) (_ : N.Normal)
        (_ : Nstar.Normal), IsRowNormalForm G φ.ker e i0 s N Nstar := by
  classical
  obtain ⟨A, hAl, hkerA, ⟨c⟩⟩ := exists_clean_complement hcite G label f hsize hf φ hφ hAlt
    htrans k hodd hLG1 hm
  subst hAl
  -- (LG1) gives `m ≥ 2k - 1 ≥ 17`, in particular `m ≥ 5`.
  have hk9 : 9 ≤ k := by
    have h8 : (8 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hLG1
    have : 8 < k := by exact_mod_cast h8
    omega
  have h5 : 5 ≤ Fintype.card I := by omega
  obtain ⟨j0⟩ : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  letI : Fintype c.Fiber := Fintype.ofEquiv _ (c.fiberEquivBlock j0).symm
  refine ⟨c.Fiber, inferInstance, c.coordinates, c.sectionHom, ?_, c.label_coordinates,
    c.sectionHom_injective, c.pure, ?_, ?_⟩
  · rw [Fintype.card_congr (c.fiberEquivBlock j0)]
    exact hsize j0
  · rw [← hkerA]
    exact c.isComplement
  · intro i0
    -- `N` is defined from a second row `i ≠ i0`.
    obtain ⟨i, hi⟩ : ∃ i : I, i ≠ i0 := by
      have h1 : 1 < Fintype.card I := by omega
      obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h1
      by_cases ha : a = i0
      · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
      · exact ⟨a, ha⟩
    refine ⟨c.rowN h5 i0 (i := i), c.rowNstar h5 i0, inferInstance, inferInstance, ?_⟩
    rw [← hkerA]
    exact c.isRowNormalForm h5 i0 hi

end

end GI.Paper
