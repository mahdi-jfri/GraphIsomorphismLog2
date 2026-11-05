module

public import Workspace.NormalTranspose
public import Workspace.NormalTransposeColumns
public import Workspace.CarrierInheritance
public import Workspace.NormalTransposeOrbits
public import Workspace.NormalTransposeConcrete
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

@[expose] public section

/-!
# Paper statements: Lemma A.14, the carrier inheritance, and Section 6

* `lem:normal-transpose` (A.14): the column partition
  (`lem_normal_transpose`), eq. `modular-index-split`
  (`eq_modular_index_split`), the lower and upper actions
  (`lem_normal_transpose_lower_action`, `lem_normal_transpose_upper_action`),
  `ρ` does not increase (`lem_normal_transpose_rho`), and the interchange of
  the ratio sequence (`lem_normal_transpose_interchange`), and its form for the
  concrete clean product `G/M ≅ Alt(m) × H/N` of Theorem A.18
  (`lem_normal_transpose_clean_product`); the equal column width `u = b/t` from
  the transitivity of `G` (`lem_normal_transpose_equal_orbits`,
  `lem_normal_transpose_equal_orbits_of_normal_form`).
* `subsec:carrier-inheritance`, the faithful-image assertion
  (`carrier_inheritance_faithful_image`).
* Section 6, "Why a row action is enlarged at most once": eq.
  `promotion-product` (`eq_promotion_product`); its structural claim is the
  faithful-image assertion above.

The clause "This is a polynomial operation" of A.14 is about algorithms on
the machine model and is left to the machine level. The bookkeeping
instructions in the proof of A.14 and in `subsec:carrier-inheritance`
("Keep their origin labels", "dispatch above it uses its quotient action",
"switch in place to the general inherited dispatcher", the
largest-orbit-first rule) describe the algorithm and are not formalized here.
-/

namespace GI.Paper

open Equiv GI.NormalTranspose

/-- **Lemma A.14** (Retained normal-column transpose), the column partition.

Let a clean row normal form as in Theorem A.18 be supplied: clean coordinates
`e : B × I ≃ V`, the clean complement `R = s(Alt(m))` acting by
`(b, i) ↦ (b, p i)`, and `N* ◁ N ◁ H` with `IsRowNormalForm`. The column of a
point `e (b, i)` is the `N`-orbit `Δ` of `b` (`colOf e N`). Then:

1. the `M`-orbits are the cells `{i} × Δ`;
2. the orbits of `J = M R` are the columns `[m] × Δ`;
3. `G` permutes the columns, so the column action is a quotient of degree
   `t`, the number of `N`-orbits;
4. the old `Alt(m)` acts inside the columns;
5. a column `[m] × Δ` has `m |Δ|` points (`mu` when `|Δ| = u`);
6. `t ≤ b`.

The paper's setting has `m ≥ 5` (A.18 is under (LG1)); `4 ≤ m` is what is used. -/
theorem lem_normal_transpose {V B I : Type*} [Fintype I] [DecidableEq I] [Finite B] [Finite V]
    {G : Subgroup (Perm V)} {K : Subgroup G} {e : B × I ≃ V} {s : alternatingGroup I →* G}
    (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i)) {i0 : I}
    {N Nstar : Subgroup (cleanLocalGroup G e i0)} [N.Normal] [Nstar.Normal]
    (hRNF : IsRowNormalForm G K e i0 s N Nstar) (hm : 4 ≤ Fintype.card I) :
    (∀ (b b' : B) (i i' : I), (∃ g ∈ rowNormalM G K e i0 N, g.val (e (b, i)) = e (b', i')) ↔
      i = i' ∧ ∃ n : N, n • b = b') ∧
    (∀ v w : V, (∃ g ∈ rowNormalM G K e i0 N ⊔ s.range, g.val v = w) ↔
      colOf e N v = colOf e N w) ∧
    (∀ (g : G) (v w : V), colOf e N v = colOf e N w →
      colOf e N (g.val v) = colOf e N (g.val w)) ∧
    (∀ (p : alternatingGroup I) (v : V), colOf e N ((s p).val v) = colOf e N v) ∧
    (∀ C : Quotient (MulAction.orbitRel N B), Nat.card {v : V // colOf e N v = C} =
      Fintype.card I * Nat.card {b : B // Quotient.mk _ b = C}) ∧
    Nat.card (Quotient (MulAction.orbitRel N B)) ≤ Nat.card B := by
  classical
  haveI : Fintype B := Fintype.ofFinite B
  haveI : Fintype V := Fintype.ofFinite V
  refine ⟨fun b b' i i' => m_orbit_iff hRNF b b' i i' (by omega),
    j_orbit_iff hRNF hpure hm, columns_invariant hRNF hpure hm,
    complement_in_columns hpure, fun C => ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, column_card C]
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact column_count_le

/-- **Eq. `modular-index-split`** (proof of Lemma A.14). For `N ◁ H` and a
step `L_{i-1} ≤ L_i` of a local tower,
`[L_i : L_{i-1}] = [L_i ∩ N : L_{i-1} ∩ N] [N L_i : N L_{i-1}]`. -/
theorem eq_modular_index_split {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    {L' L : Subgroup H} (hle : L' ≤ L) :
    L'.relIndex L = (L' ⊓ N).relIndex (L ⊓ N) * (N ⊔ L').relIndex (N ⊔ L) :=
  modular_index_split N hle

/-- The lower action in the proof of Lemma A.14. With `P ≤ L_{i-1} ≤ L_i` and
`B_i = L_i ∩ NP`: "`B_i = L_i ∩ NP = (L_i ∩ N)P`. Then
`B_i ∩ L_{i-1} = B_{i-1}`, so the action on the cosets `B_{i-1}\B_i` is exactly
the orbit of the base coset under `B_i` in the old action on `L_{i-1}\L_i`."
The index of that action is the lower factor `[L_i ∩ N : L_{i-1} ∩ N]`. -/
theorem lem_normal_transpose_lower_action {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] {P L' L : Subgroup H} (hPL' : P ≤ L') (hle : L' ≤ L) :
    L ⊓ (N ⊔ P) = (L ⊓ N) ⊔ P ∧
    (L ⊓ (N ⊔ P)) ⊓ L' = L' ⊓ (N ⊔ P) ∧
    (∀ x : L, x.val ∈ N ⊔ P →
      (x • ((1 : L) : L ⧸ L'.subgroupOf L) = ((1 : L) : L ⧸ L'.subgroupOf L) ↔
        x.val ∈ L' ⊓ (N ⊔ P))) ∧
    (L' ⊓ (N ⊔ P)).relIndex (L ⊓ (N ⊔ P)) = (L' ⊓ N).relIndex (L ⊓ N) :=
  ⟨inf_sup_eq_of_le N (hPL'.trans hle), lower_inf N hle, fun x hx => lower_stabilizer N x hx,
    lower_index N hPL' hle⟩

/-- The upper action in the proof of Lemma A.14: "The upper action on
`NL_{i-1}\NL_i` is equivalent to the action of `L_i` on the cosets of
`L_i ∩ NL_{i-1}`. Since `L_{i-1} ≤ L_i ∩ NL_{i-1} ≤ L_i`, it is a block quotient
of the old constituent." Here: `L_i` meets every coset of `NL_{i-1}` in `NL_i`
(transitivity), `N` acts trivially on those cosets, and the degree is
`[L_i : L_i ∩ NL_{i-1}]`. -/
theorem lem_normal_transpose_upper_action {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] {L' L : Subgroup H} (hle : L' ≤ L) :
    (∀ y ∈ N ⊔ L, ∃ x ∈ L, y⁻¹ * x ∈ N ⊔ L') ∧
    (∀ n ∈ N, ∀ y : H, (n * y)⁻¹ * y ∈ N ⊔ L') ∧
    L' ≤ L ⊓ (N ⊔ L') ∧ L ⊓ (N ⊔ L') ≤ L ∧
    (N ⊔ L').relIndex (N ⊔ L) = (L ⊓ (N ⊔ L')).relIndex L :=
  ⟨fun y hy => upper_transitive N y hy, fun n hn y => upper_normal_trivial N n y hn,
    (upper_index N hle).1, inf_le_left, (upper_index N hle).2⟩

/-- "The inequality `f(a) + f(b) ≤ f(ab)`, for `f(r) = 2⌊log₂ r⌋ - 1` and
`f(1) = 0`, shows that `ρ` does not increase" (proof of Lemma A.14): splitting
each ratio `d_i = a_i b_i` into its lower and upper factors gives
`ρ(a) + ρ(b) ≤ ρ(d)`. -/
theorem lem_normal_transpose_rho (l : List (ℕ × ℕ)) (hpos : ∀ p ∈ l, 0 < p.1 ∧ 0 < p.2) :
    rho (l.map Prod.fst) + rho (l.map Prod.snd) ≤ rho (l.map fun p => p.1 * p.2) :=
  rho_split_le l hpos

/-- The interchange in the proof of Lemma A.14. "Modulo `𝓜`, write the clean
product as `Alt(m) × Q`. ... Each intermediate subgroup contains
`Alt(m-1) × 1` and is therefore exactly `Alt(m-1) × V` for some
`U ≤ V ≤ Q`. Replace these groups by `Alt(m) × V`, after the initial step
`Alt(m-1) × U < Alt(m) × U` of index `m`. This preserves all local indices.
Thus the clean product interchanges the ratio sequence `r_1, …, r_s, m` with
`m, r_1, …, r_s`." Here `A` stands for `Alt(m)` and `A₁` for `Alt(m-1)`. -/
theorem lem_normal_transpose_interchange {A Q : Type*} [Group A] [Group Q] [Finite A]
    [Finite Q] (A₁ : Subgroup A) :
    (∀ X : Subgroup (A × Q), A₁.prod ⊥ ≤ X → X ≤ A₁.prod ⊤ →
      X = A₁.prod (X.map (MonoidHom.snd A Q))) ∧
    (∀ V₀ V₁ : Subgroup Q, V₀ ≤ V₁ →
      (A₁.prod V₀).relIndex (A₁.prod V₁) = V₀.relIndex V₁ ∧
      ((⊤ : Subgroup A).prod V₀).relIndex ((⊤ : Subgroup A).prod V₁) = V₀.relIndex V₁ ∧
      (A₁.prod V₀).relIndex ((⊤ : Subgroup A).prod V₀) = A₁.index) :=
  ⟨fun X hlow hhigh => prod_intermediate A₁ X hlow hhigh,
    fun _ _ hV => ratio_interchange A₁ hV⟩

/-- **Lemma A.14**, "if the local variation group `N` is intransitive with `t` orbits
of size `u = b/t`": the `N`-orbits have one size `u`, derived from the transitivity of
`G`. With the outputs of Theorem A.18 (clean coordinates `e`, the pure complement
`s(Alt(m))`, a kernel `K` complemented by `s(Alt(m))` whose elements keep every
block), the local group `H` is transitive on `B`, so the orbits of `N ◁ H` have one
size `u`. Then every column class has `u` points, `t u = b`, and every column
`[m] × Δ` has `m u` points ("normal columns of degree `mu = n/t`"). -/
theorem lem_normal_transpose_equal_orbits {V B I : Type*} [Fintype I] [DecidableEq I]
    [Finite B] {G : Subgroup (Perm V)} {K : Subgroup G} {e : B × I ≃ V}
    {s : alternatingGroup I →* G} (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i))
    (hK : ∀ k ∈ K, ∀ b i, (e.symm (k.val (e (b, i)))).2 = i) (hcompl : K.IsComplement' s.range)
    (htrans : ∀ v w : V, ∃ g : G, g.val v = w) {i0 : I}
    (N : Subgroup (cleanLocalGroup G e i0)) [N.Normal] [Nonempty B] :
    ∃ u : ℕ, (∀ C : Quotient (MulAction.orbitRel N B), Nat.card {b : B // Quotient.mk _ b = C} = u) ∧
      Nat.card (Quotient (MulAction.orbitRel N B)) * u = Nat.card B ∧
      (∀ C : Quotient (MulAction.orbitRel N B),
        Nat.card {v : V // colOf e N v = C} = Fintype.card I * u) := by
  classical
  haveI : Fintype B := Fintype.ofFinite B
  haveI : Finite V := Finite.of_equiv _ e
  haveI : Fintype V := Fintype.ofFinite V
  obtain ⟨b₀⟩ := ‹Nonempty B›
  have hloc := local_transitive i0 hpure hK hcompl htrans
  obtain ⟨hfib, hcount⟩ := orbit_count_mul N hloc b₀
  refine ⟨_, hfib, hcount, fun C => ?_⟩
  rw [Nat.card_eq_fintype_card, column_card C, ← hfib C, Nat.card_eq_fintype_card]

/-- `lem_normal_transpose_equal_orbits` with the hypotheses in the form that Theorem
A.18 (`thm_logarithmic_gat_normal_form`) supplies: the top action `φ` on the rows
`label`, clean coordinates with `label (e (b, i)) = i`, the pure complement `s`, and
`ker φ` complemented by `s(Alt(m))`. The only further hypothesis is the transitivity
of `G`, as in the statement of Lemma A.14. -/
theorem lem_normal_transpose_equal_orbits_of_normal_form {V B I : Type*} [Fintype I]
    [DecidableEq I] [Finite B] [Nonempty B] {G : Subgroup (Perm V)} (label : V → I)
    (φ : G →* Perm I) (hφ : ∀ (g : G) (x : V), label (g.val x) = φ g (label x))
    {e : B × I ≃ V} (hlabel : ∀ b i, label (e (b, i)) = i)
    {s : alternatingGroup I →* G} (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i))
    (hcompl : φ.ker.IsComplement' s.range) (htrans : ∀ v w : V, ∃ g : G, g.val v = w) {i0 : I}
    (N : Subgroup (cleanLocalGroup G e i0)) [N.Normal] :
    ∃ u : ℕ, (∀ C : Quotient (MulAction.orbitRel N B), Nat.card {b : B // Quotient.mk _ b = C} = u) ∧
      Nat.card (Quotient (MulAction.orbitRel N B)) * u = Nat.card B ∧
      (∀ C : Quotient (MulAction.orbitRel N B),
        Nat.card {v : V // colOf e N v = C} = Fintype.card I * u) := by
  refine lem_normal_transpose_equal_orbits hpure (fun k hk b i => ?_) hcompl htrans N
  have h1 := hφ k (e (b, i))
  rw [hlabel, (MonoidHom.mem_ker).mp hk, Perm.one_apply] at h1
  have h2 : label (k.val (e (b, i))) = (e.symm (k.val (e (b, i)))).2 := by
    simpa using hlabel (e.symm (k.val (e (b, i)))).1 (e.symm (k.val (e (b, i)))).2
  rw [← h2, h1]

/-- **Lemma A.14**, the interchange for the concrete clean product of Theorem A.18.
The data are the outputs of Theorem A.18 (`thm_logarithmic_gat_normal_form`): the top
action `φ : G → Alt(m)` on the rows (`label`), clean coordinates `e` with
`label (e (b, i)) = i`, the pure complement `s`, and a clean row normal form with
`K = ker φ`. Then "modulo `𝓜`, write the clean product as `Alt(m) × Q`": there is
`π : G → Alt(m) × H/N`, whose first component is `φ` and whose second is the
diagonal map `θ` of the normal form, with
1. `π` onto and `ker π = M`, so `G/M ≅ Alt(m) × H/N`;
2. "The cell and row stabilizers are `Alt(m-1) × U` and `Alt(m-1) × Q`": `M` fixes
   every cell, the cell stabilizer lies in the row stabilizer, and the row stabilizer
   is `π⁻¹(Alt(m-1) × Q)`;
3. "Each intermediate subgroup ... is therefore exactly `Alt(m-1) × V`": every
   subgroup between the cell and the row stabilizer (the cell stabilizer itself
   included) is `π⁻¹(Alt(m-1) × V)`;
4. "Replace these groups by `Alt(m) × V` ... This preserves all local indices": the
   preimages of `Alt(m-1) × V_l` and of `Alt(m) × V_l` have the same successive
   indices `[V_l : V_{l-1}]`, and the new initial step has index `m`. -/
theorem lem_normal_transpose_clean_product {V B I : Type*} [Fintype I] [DecidableEq I]
    [Finite B] [Nonempty B] {G : Subgroup (Perm V)} (label : V → I) (φ : G →* Perm I)
    (hφA : ∀ g, φ g ∈ alternatingGroup I)
    (hφ : ∀ (g : G) (x : V), label (g.val x) = φ g (label x))
    {e : B × I ≃ V} (hlabel : ∀ b i, label (e (b, i)) = i)
    {s : alternatingGroup I →* G} (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i))
    {i0 : I} {N Nstar : Subgroup (cleanLocalGroup G e i0)} [N.Normal] [Nstar.Normal]
    (hRNF : IsRowNormalForm G φ.ker e i0 s N Nstar) (hm : 4 ≤ Fintype.card I) :
    ∃ π : G →* alternatingGroup I × (cleanLocalGroup G e i0 ⧸ N),
      (∀ g, ((π g).1 : Perm I) = φ g) ∧
      (∀ (g : G) (x : I → cleanLocalGroup G e i0) (r : I),
        cleanLift e _ x = g.val → (π g).2 = (x r : cleanLocalGroup G e i0 ⧸ N)) ∧
      Function.Surjective π ∧ π.ker = rowNormalM G φ.ker e i0 N ∧
      (∀ (i : I) (Δ : Quotient (MulAction.orbitRel N B)),
        rowNormalM G φ.ker e i0 N ≤ cellStab e N i Δ ∧
        cellStab e N i Δ ≤ rowStab e i ∧
        rowStab e i = ((rowFix i).prod ⊤).comap π) ∧
      (∀ (i : I) (Δ : Quotient (MulAction.orbitRel N B)) (X : Subgroup G),
        cellStab e N i Δ ≤ X → X ≤ rowStab e i →
          ∃ W : Subgroup (cleanLocalGroup G e i0 ⧸ N), X = ((rowFix i).prod W).comap π) ∧
      (∀ (i : I) (V₀ V₁ : Subgroup (cleanLocalGroup G e i0 ⧸ N)), V₀ ≤ V₁ →
        (((rowFix i).prod V₀).comap π).relIndex (((rowFix i).prod V₁).comap π) =
            V₀.relIndex V₁ ∧
        ((((⊤ : Subgroup (alternatingGroup I)).prod V₀).comap π).relIndex
            (((⊤ : Subgroup (alternatingGroup I)).prod V₁).comap π)) = V₀.relIndex V₁ ∧
        (((rowFix i).prod V₀).comap π).relIndex
            (((⊤ : Subgroup (alternatingGroup I)).prod V₀).comap π) = Fintype.card I) := by
  classical
  haveI : Finite (cleanLocalGroup G e i0) := Subgroup.instFiniteSubtypeMem _
  obtain ⟨b₀⟩ := ‹Nonempty B›
  let top : G →* alternatingGroup I := φ.codRestrict (alternatingGroup I) hφA
  have htop : ∀ (g : G) b i, (e.symm (g.val (e (b, i)))).2 = (top g : Perm I) i := by
    intro g b i
    have h1 := hφ g (e (b, i))
    rw [hlabel] at h1
    have h2 : label (g.val (e (b, i))) = (e.symm (g.val (e (b, i)))).2 := by
      simpa using hlabel (e.symm (g.val (e (b, i)))).1 (e.symm (g.val (e (b, i)))).2
    change (e.symm (g.val (e (b, i)))).2 = φ g i
    rw [← h1, h2]
  have htopK : top.ker = φ.ker := by
    ext g
    simp only [MonoidHom.mem_ker, top]
    exact Subtype.ext_iff
  have htops : ∀ p, top (s p) = p := by
    intro p
    apply Subtype.ext
    ext i
    have := htop (s p) b₀ i
    rw [hpure, e.symm_apply_apply] at this
    exact this.symm
  obtain ⟨θ, hθ, hθK, -, hθker⟩ := hRNF.diagonal
  have hsurj := cleanProduct_surjective top htopK htops θ hθK hθker
  have hker := cleanProduct_ker top hRNF htopK htops θ hθker
  have hm2 : 2 ≤ Fintype.card I := by omega
  have hrow : ∀ i, rowStab e i = ((rowFix i).prod ⊤).comap (cleanProduct top θ) := by
    intro i
    rw [comap_rowFix_top, rowStab_eq top htop]
  refine ⟨cleanProduct top θ, fun g => rfl, fun g x r hx => hθ g x r hx, hsurj, hker,
    fun i Δ => ⟨?_, ?_, hrow i⟩, fun i Δ X hlow hhigh => ?_, fun i V₀ V₁ hV => ?_⟩
  · -- `M = ker π` fixes every cell.
    rw [← hker]
    refine le_trans ?_ (cellStab_lower top hRNF htopK htops θ hθker hm2 i Δ hpure)
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    change cleanProduct top θ g ∈ (rowFix i).prod ⊥
    rw [hg]
    exact Subgroup.one_mem _
  · rw [rowStab_eq top htop]
    exact cellStab_le_rowStab top htop i Δ
  · rw [rowStab_eq top htop] at hhigh
    exact ⟨_, intermediate_eq top hRNF htopK htops θ hθK hθker hm2 i Δ hpure X hlow hhigh⟩
  · obtain ⟨h1, h2, h3⟩ := ratio_interchange (rowFix i) hV
    refine ⟨?_, ?_, ?_⟩
    · rw [relIndex_comap_cleanProduct top htopK htops θ hθK hθker, h1]
    · rw [relIndex_comap_cleanProduct top htopK htops θ hθK hθker, h2]
    · rw [relIndex_comap_cleanProduct top htopK htops θ hθK hθker, h3]
      haveI := alternatingGroup.isPretransitive_of_three_le_card (α := I)
        (by rw [Nat.card_eq_fintype_card]; omega)
      rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card]

/-- **Inheritance of the retained row action**, the faithful-image assertion
(`subsec:carrier-inheritance`). Write the covering group as
`H/M = Alt(m) × Q'` (a surjection `π` with kernel `M`) and let `T` be the kernel
of the physical action on the first orbit `Ω'`. If `Ω'` meets every row, every
element of `T` fixes every row label, so its `Alt(m)`-component is trivial
(`hrow` says the `Alt(m)`-component of `π` is the action on rows). Consequently
`TM/M = 1 × Z` for a normal `Z ◁ Q'`, and
`(H/T)/(TM/T) ≅ Alt(m) × (Q'/Z)`. -/
theorem carrier_inheritance_faithful_image {H A Q X I : Type*} [Group H] [Group A] [Group Q]
    [MulAction H X] (M T : Subgroup H) [T.Normal] (π : H →* A × Q)
    (hπ : Function.Surjective π) (hker : π.ker = M)
    (φ : H →* Perm I) (label : X → I) (hlabel : ∀ (h : H) (x : X), label (h • x) = φ h (label x))
    (hrow : ∀ h : H, φ h = 1 → (π h).1 = 1)
    (Ω' : Set X) (hrows : ∀ i, ∃ x ∈ Ω', label x = i) (hT : ∀ t ∈ T, ∀ x ∈ Ω', t • x = x) :
    ∃ (Z : Subgroup Q) (_ : Z.Normal), (T ⊔ M).map π = (⊥ : Subgroup A).prod Z ∧
      ∃ (_ : ((T ⊔ M).map (QuotientGroup.mk' T)).Normal),
        Nonempty ((H ⧸ T) ⧸ ((T ⊔ M).map (QuotientGroup.mk' T)) ≃* A × (Q ⧸ Z)) :=
  GI.CarrierInheritance.faithful_image M T π hπ hker (fun t ht =>
    hrow t (GI.CarrierInheritance.row_action_trivial_of_fixes φ label hlabel Ω' hrows t
      (hT t ht)))

/-- **Eq. `promotion-product`** (Section 6, "Why a row action is enlarged at
most once"). With `1/3 < α`, `λ = N^α`, and the exposed ratios `m, q > λ`,
`N/(mq) < N^{1-2α} < N^α = λ`. -/
theorem eq_promotion_product {N α m q : ℝ} (hN : 1 < N) (hα : 1 / 3 < α)
    (hm : N ^ α < m) (hq : N ^ α < q) :
    N / (m * q) < N ^ (1 - 2 * α) ∧ N ^ (1 - 2 * α) < N ^ α :=
  GI.CarrierInheritance.promotion_product hN hα hm hq

end GI.Paper
