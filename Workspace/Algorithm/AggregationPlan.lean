module

public import Workspace.Algorithm.AggregationItems
public import Workspace.Algorithm.LabelOrbits

@[expose] public section

/-!
# The plan of an aggregation round: the paper's case analysis

For each branch of an aggregation round, the item is computed from the two canonical structures
of the branch, `X` (of `(x, src)`) and `Y` (of `(y, b)`), by the case analysis of [H,
Section 6.2] as re-proved in Section A.3 of the paper. The case is read off the ideal
certificate group `π(F_x)` of `X` (`aggCase`, `Workspace/Algorithm/LabelOrbits.lean`):

* **Case 1** (Section A.3, "Case 1 and balanced colored partitions"): the canonical colored
  partition into orbits, colored by orbit length. "The structure is equivariant, so aligning the
  two colored partitions and lifting their full allowed coset loses no parent isomorphism.
  Impose alternating parity by the sign homomorphism, rejecting an empty parity coset." The item
  is the overcoset of the even stabilizer of the partition of `X`, through an even permutation
  that maps it to the partition of `Y`, or no item if there is none (`invItem`, `caseOneItem`).
  Its cap is at most `q/2` (`labelOrbitPart_cap`).
* **Case 2a** (Lemma A.11): the halving item. The dominant orbits of `X` and `Y` are aligned by a
  lift `τ₀` ("choose an even ideal permutation aligning their dominant orbits, lift it through
  `π`"), the parity twist is an even paired transposition, and `A` consists of the lifts of the
  certificate automorphisms in `H₀ = π⁻¹(Alt(Φ) × Alt(C))` (`halvingItem`). The facts of Lemma
  A.11 hold (`halvingItem_valid`): the kernel orbits are small by the Johnson block map
  (`JohnsonBlocks`), and `A` meets every coset of the kernel because `π(F_x)` contains the pure
  `Alt(Φ) × 1` (`GI.Paper.lem_large_symmetry_constant_cert_pure`).
* **Cases 2b and 3**: these produce a nontrivial homogeneous coherent configuration (Case 2b
  through anchors and an orbital, Case 3 through the Design Lemma), which Algorithm
  `alg:auxiliary` turns into a configuration query, a balanced partition, or a rectangle query.
  They are the interface `cfg` of the plan.

`plan` is this procedure; `plan_valid` proves that the item of every branch satisfies
`AuxItem.Valid` for the parent isomorphisms of the branch, in Cases 1 and 2a, and takes the
validity of `cfg` in Cases 2b and 3 as its hypothesis.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Rectangle GI.Paper GI.ExactConfiguration GI.PairRefinement
open scoped Pointwise

variable {Ω C : Type} {P : Params} {S : State Ω C} {L : GiantLabels S}

/-! ### Items from an equivariant invariant -/

section Invariant

variable {Z : Type*} [MulAction (Perm (Fin L.q)) Z] {ℓ : ℕ}

open Classical in
/-- **The overcoset item of an invariant**: if an even permutation `σ` maps the invariant of `X`
to that of `Y`, the overcoset `σ E₀` of the even stabilizer `E₀` of the invariant of `X`;
otherwise no item ("rejecting an empty parity coset"). -/
noncomputable def invItem (F : Canon L.q P.κ ℓ → Z) (X Y : Canon L.q P.κ ℓ) : AuxItem P S L :=
  if h : ∃ σ : alternatingGroup (Fin L.q), (σ : Perm (Fin L.q)) • F X = F Y then
    .overcoset h.choose (evenStab (q := L.q) (F X))
  else .none

/-- **The overcoset item of an invariant is valid** when the invariant commutes with relabeling
and its even stabilizer has `aw ≤ βq`. -/
theorem invItem_valid {F : Canon L.q P.κ ℓ → Z} (hF : AuxItem.Equivariant F)
    {X Y : Canon L.q P.κ ℓ} {B : Set (Perm Ω)}
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • X = Y)
    (hcap : (aw (evenStab (q := L.q) (F X)) : ℝ) ≤ P.β * L.q) :
    (invItem (P := P) (S := S) F X Y).Valid B := by
  classical
  unfold invItem
  split_ifs with h
  · exact AuxItem.valid_overcoset_of_invariant hF hB _ h.choose_spec hcap fun e he => he
  · push Not at h
    exact AuxItem.valid_none_of_invariant hF hB h

end Invariant

/-! ### Case 1 -/

section CaseOne

variable {ℓ : ℕ}

/-- The orbit partition of the ideal certificate group commutes with relabeling. -/
theorem labelOrbitPart_equivariant :
    AuxItem.Equivariant (fun X : Canon L.q P.κ ℓ => labelOrbitPart X.grp) := fun σ X => by
  simp only [Canon.smul_grp, labelOrbitPart_conj]

/-- **The item of Case 1**: the overcoset of the colored orbit partition. -/
noncomputable def caseOneItem (X Y : Canon L.q P.κ ℓ) : AuxItem P S L :=
  invItem (fun Z : Canon L.q P.κ ℓ => labelOrbitPart Z.grp) X Y

/-- **The item of Case 1 is valid** (Section A.3, "Case 1 and balanced colored partitions"),
for `β ≥ 1/2`: the cap of the orbit partition is at most `q/2 ≤ βq` (`labelOrbitPart_cap`). -/
theorem caseOneItem_valid (hβ : 1 / 2 ≤ P.β) {X Y : Canon L.q P.κ ℓ} {B : Set (Perm Ω)}
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • X = Y)
    (hcase : aggCase X.grp = .one) :
    (caseOneItem (P := P) (S := S) X Y).Valid B := by
  classical
  refine invItem_valid labelOrbitPart_equivariant hB ?_
  have hdom : domSet X.grp = ∅ := by
    unfold aggCase at hcase
    by_contra hne
    rw [if_pos (Finset.nonempty_iff_ne_empty.2 hne)] at hcase
    split_ifs at hcase
  have hsupp : L.q ≤ 2 * (suppSet X.grp).card := by
    unfold aggCase at hcase
    rw [if_neg (by rw [hdom]; simp)] at hcase
    split_ifs at hcase with h
    exact h
  have hcap := labelOrbitPart_cap X.grp hdom hsupp
  have haw : aw (evenStab (q := L.q) (labelOrbitPart X.grp)) ≤ L.q / 2 := (aw_le_iff _).2 hcap
  have h1 : ((L.q / 2 : ℕ) : ℝ) ≤ (L.q : ℝ) / 2 := Nat.cast_div_le
  have h2 : (L.q : ℝ) / 2 ≤ P.β * L.q := by
    have : (0 : ℝ) ≤ L.q := Nat.cast_nonneg _
    nlinarith
  calc (aw (evenStab (q := L.q) (labelOrbitPart X.grp)) : ℝ) ≤ ((L.q / 2 : ℕ) : ℝ) := by
        exact_mod_cast haw
    _ ≤ P.β * L.q := h1.trans h2

end CaseOne

/-! ### Case 2a: the pure alternating group of the dominant orbit -/

section Pure

variable {q : ℕ}

/-- `m! < n!/2` for `m < n` and `n ≥ 3`, in the form `m! < |Alt(n)|`. -/
theorem factorial_lt_card_alt {Φ : Finset (Fin q)} {m : ℕ} (hm : m < Φ.card) (h3 : 3 ≤ Φ.card) :
    m.factorial < Nat.card (alternatingGroup Φ) := by
  haveI : Nontrivial Φ := Fintype.one_lt_card_iff_nontrivial.1 (by rw [Fintype.card_coe]; omega)
  have h2 := two_mul_nat_card_alternatingGroup (α := Φ)
  have hΦ : Nat.card Φ = Φ.card := by simp
  rw [Nat.card_perm, hΦ] at h2
  have hle : m.factorial ≤ (Φ.card - 1).factorial := Nat.factorial_le (by omega)
  have hsucc : Φ.card.factorial = Φ.card * (Φ.card - 1).factorial := by
    conv_lhs => rw [show Φ.card = (Φ.card - 1) + 1 by omega]
    rw [Nat.factorial_succ]
    congr 1
    omega
  have hpos : 0 < (Φ.card - 1).factorial := Nat.factorial_pos _
  nlinarith

/-- **The pure alternating group** (Lemma A.11: "Consequently `L` contains the pure supported
`Alt(Φ) × 1_C`", `GI.Paper.lem_large_symmetry_constant_cert_pure`). Let `F ≤ Alt(Γ)` preserve
`Φ`, with `|Φ| ≥ 5` and `|Γ \ Φ| < |Φ|`. If the restriction of `F` to `Φ` contains `Alt(Φ)`, then
`F` contains every even permutation that fixes `Γ \ Φ` pointwise. -/
theorem pure_of_giantOn {F : Subgroup (Perm (Fin q))}
    (hF : F ≤ alternatingGroup (Fin q)) {Φ : Finset (Fin q)}
    (hpres : ∀ h ∈ F, ∀ a ∈ Φ, h a ∈ Φ) (hg : GiantOn F Φ) (h5 : 5 ≤ Φ.card)
    (hlt : Φᶜ.card < Φ.card) :
    ∀ σ : Perm (Fin q), σ ∈ alternatingGroup (Fin q) → (∀ a, a ∉ Φ → σ a = a) → σ ∈ F := by
  classical
  -- elements of `F` are permitted permutations of `Φ` and its complement
  have hpresc : ∀ h ∈ F, ∀ a, a ∉ Φ → h a ∉ Φ := by
    intro h hh a ha hha
    have := hpres h⁻¹ (F.inv_mem hh) _ hha
    rw [Perm.inv_apply_self] at this
    exact ha this
  have hperm : ∀ h (hh : h ∈ F), (⟨h, hF hh⟩ : alternatingGroup (Fin q)) ∈ permitted Φ Φᶜ :=
    fun h hh => mem_sides_of_maps h (hpres h hh) (fun a ha => by
      rw [Finset.mem_compl] at ha ⊢; exact hpresc h hh a ha)
  let Fp : Subgroup (permitted Φ Φᶜ) :=
    F.comap ((alternatingGroup (Fin q)).subtype.comp (permitted Φ Φᶜ).subtype)
  let Lsub : Subgroup (Perm Φ × Perm (Φᶜ : Finset (Fin q))) := Fp.map sideAction
  have honto : ∀ σ ∈ alternatingGroup Φ, ∃ l ∈ Lsub, l.1 = σ := by
    intro σ hσ
    have hτ : ofSubtype σ ∈ alternatingGroup (Fin q) := by
      rw [Perm.mem_alternatingGroup, sign_ofSubtype]; exact hσ
    obtain ⟨h, hh, hha⟩ := hg (ofSubtype σ) hτ (fun a ha => ofSubtype_apply_of_not_mem σ ha)
    refine ⟨sideAction ⟨⟨h, hF hh⟩, hperm h hh⟩, ⟨_, hh, rfl⟩, ?_⟩
    refine Equiv.ext fun x => Subtype.ext ?_
    exact (hha x x.2).trans (ofSubtype_apply_coe σ x)
  have hsmall : (Fintype.card (Φᶜ : Finset (Fin q))).factorial <
      Nat.card (alternatingGroup Φ) := by
    rw [Fintype.card_coe]
    exact factorial_lt_card_alt hlt (by omega)
  have h5' : 5 ≤ Fintype.card Φ := by rw [Fintype.card_coe]; exact h5
  have hpure := lem_large_symmetry_constant_cert_pure Lsub h5' honto hsmall
  intro σ hσ hfix
  have hmaps : ∀ x, x ∈ Φ ↔ σ x ∈ Φ := by
    intro x
    constructor
    · intro hx
      by_contra hσx
      have h1 := σ.injective (hfix _ hσx)
      rw [h1] at hσx
      exact hσx hx
    · intro hσx
      by_contra hx
      rw [hfix x hx] at hσx
      exact hx hσx
  let σ' : Perm Φ := subtypePerm σ (fun x => (hmaps x).symm)
  have hσ' : σ' ∈ alternatingGroup Φ := by
    rw [Perm.mem_alternatingGroup]
    have := sign_subtypePerm σ (p := fun x => x ∈ Φ) (fun x => (hmaps x).symm)
      (fun x hx => by by_contra h; exact hx (hfix x h))
    convert this.trans hσ using 3
  obtain ⟨g, hg, hgl⟩ := hpure σ' hσ'
  have heq : ((g : alternatingGroup (Fin q)) : Perm (Fin q)) = σ := by
    refine Equiv.ext fun a => ?_
    by_cases ha : a ∈ Φ
    · have := congrArg (fun p : Perm Φ × Perm (Φᶜ : Finset (Fin q)) => ((p.1 ⟨a, ha⟩ : Φ) : Fin q))
        hgl
      exact this
    · have hac : a ∈ (Φᶜ : Finset (Fin q)) := Finset.mem_compl.2 ha
      have := congrArg (fun p : Perm Φ × Perm (Φᶜ : Finset (Fin q)) =>
        ((p.2 ⟨a, hac⟩ : (Φᶜ : Finset (Fin q))) : Fin q)) hgl
      change ((g : alternatingGroup (Fin q)) : Perm (Fin q)) a = a at this
      rw [this, hfix a ha]
  rw [← heq]
  exact hg

end Pure

/-! ### Case 2a: the Johnson block map and the halving item -/

/-- **The Johnson block map of the selected constituent** (Lemma A.11: "Assume its actual
equivariant block map is `p : Ω → binom(Γ, h)`, `1 ≤ h ≤ q/2`"; "Transitivity of `G` makes the
fibers of `p` equal"). In the recursion it comes from the kernel-orbit map of Corollary A.25:
one label (`h = 1`) or a pair of labels (`h = 2`). -/
structure JohnsonBlocks {Ω C : Type} (S : State Ω C) (L : GiantLabels S) where
  h : ℕ
  f : ℕ
  p : S.dom → Finset (Fin L.q)
  equivariant : ∀ (g : S.G) v, p (S.domHom g v) =
    (p v).map ((L.π g : alternatingGroup (Fin L.q)) : Perm (Fin L.q)).toEmbedding
  card : ∀ v, (p v).card = h
  fibers : ∀ Bl : Finset (Fin L.q), Bl.card = h → Nat.card {v : S.dom // p v = Bl} = f
  one_le : 1 ≤ h
  half : 2 * h ≤ L.q

section Halving

variable (fin : Finite Ω) (S) (L) (πd : S.domGroup →* alternatingGroup (Fin L.q)) (κ : ℕ)

/-- **The certificate automorphisms in `G`**: the elements of `G` whose restriction to the
domain lies in the certificate group `F_x` (the lifts of its elements). -/
noncomputable def certLift : Subgroup (Perm Ω) :=
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  S.liftGroup (certGroup S πd κ (dstr S S.x))

variable {S L}

open Classical in
/-- **The parity twist** (Lemma A.11: "When a second coset exists, an even paired
transposition, one transposition in each of `Φ` and `C`, supplies its representative"): a lift
of `(a b)(c d)` with `a ≠ b` in `Φ` and `c ≠ d` outside `Φ`, or `1` when there is no such pair
outside `Φ`. -/
noncomputable def twist (Φ : Finset (Fin L.q)) : Perm Ω :=
  if h : ∃ a b c d : Fin L.q, a ∈ Φ ∧ b ∈ Φ ∧ a ≠ b ∧ c ∉ Φ ∧ d ∉ Φ ∧ c ≠ d then
    L.rep ⟨swap h.choose h.choose_spec.choose * swap h.choose_spec.choose_spec.choose
      h.choose_spec.choose_spec.choose_spec.choose, by
        obtain ⟨-, -, hab, -, -, hcd⟩ := h.choose_spec.choose_spec.choose_spec.choose_spec
        rw [Perm.mem_alternatingGroup, Perm.sign_mul, sign_swap hab, sign_swap hcd]; rfl⟩
  else 1

variable {fin πd κ}

/-- **The choices of the halving item** (Lemma A.11), with the properties its proof uses.
* `align Φ Φ'`: for dominant orbits of the same size at least two, an element of `G` whose label
  image maps `Φ` onto `Φ'` and every such element lies in its coset of
  `π⁻¹((Sym(Φ) × Sym(C)) ∩ Alt(Γ))` ("choose an even ideal permutation aligning their dominant
  orbits, lift it through `π`"; `GI.Paper.lem_large_symmetry_constant_cert_align`);
* `twist Φ`: an element of `H = π⁻¹((Sym(Φ) × Sym(C)) ∩ Alt(Γ))` that represents the second coset
  of `H₀ = π⁻¹(Alt(Φ) × Alt(C))` when there is one ("an even paired transposition … supplies its
  representative").
The paper fixes neither element; `HalvingChoice.default` takes classical choices. -/
structure HalvingChoice {Ω C : Type} (S : State Ω C) (L : GiantLabels S) where
  align : Finset (Fin L.q) → Finset (Fin L.q) → Perm Ω
  align_spec : ∀ Φ Φ' : Finset (Fin L.q), Φ.card = Φ'.card → 2 ≤ Φ.card →
    ∃ t : S.G, (t : Perm Ω) = align Φ Φ' ∧ ((L.π t : Perm (Fin L.q)) '' (Φ : Set (Fin L.q)) = Φ') ∧
      ∀ g : S.G, (L.π g : Perm (Fin L.q)) '' (Φ : Set (Fin L.q)) = Φ' →
        t⁻¹ * g ∈ (permitted Φ Φᶜ).comap L.π
  twist : Finset (Fin L.q) → Perm Ω
  twist_spec : ∀ Φ : Finset (Fin L.q), 2 ≤ Φ.card →
    twist Φ ∈ L.lift (permitted Φ Φᶜ) ∧ ∀ g ∈ L.lift (permitted Φ Φᶜ),
      g ∈ L.lift (evenSides Φ Φᶜ) ∨ (twist Φ)⁻¹ * g ∈ L.lift (evenSides Φ Φᶜ)

open Classical in
/-- **The halving item of Case 2a** (Lemma A.11). `Φ`, `Φ'` are the dominant orbits of the ideal
certificate groups of `X` and `Y`. If they have the same size, `τ₀` is a lift of an even
permutation aligning them ("choose an even ideal permutation aligning their dominant orbits, lift
it through `π`, and absorb it into the target string"); otherwise the branch is empty ("differing
cases or dominant-orbit sizes certify nonisomorphism"). The group `A` is the group of lifts of
the certificate automorphisms that lie in `H₀ = π⁻¹(Alt(Φ) × Alt(C))`. The alignment and the
twist are those of `hv`. -/
noncomputable def halvingItem (fin : Finite Ω) (πd : S.domGroup →* alternatingGroup (Fin L.q))
    (hv : HalvingChoice S L) {ℓ : ℕ} (X Y : Canon L.q P.κ ℓ) : AuxItem P S L :=
  if (domSet X.grp).card = (domSet Y.grp).card ∧ 2 ≤ (domSet X.grp).card then
    .halving
      { Φ := domSet X.grp
        τ₀ := hv.align (domSet X.grp) (domSet Y.grp)
        t := hv.twist (domSet X.grp)
        A := certLift S L fin πd P.κ ⊓ L.lift (evenSides (domSet X.grp) (domSet X.grp)ᶜ) }
  else .none

/-- The parity twist of Lemma A.11 splits `H` into `H₀` and `t H₀`
(`Halving.twist_facts`, `Halving.no_twist_facts`). -/
theorem twist_facts' (H : Halving S L) (ht : H.t = twist (L := L) H.Φ) (h2 : 2 ≤ H.Φ.card) :
    H.t ∈ H.big ∧ ∀ g ∈ H.big, g ∈ H.even ∨ H.t⁻¹ * g ∈ H.even := by
  classical
  by_cases hx : ∃ a b c d : Fin L.q, a ∈ H.Φ ∧ b ∈ H.Φ ∧ a ≠ b ∧ c ∉ H.Φ ∧ d ∉ H.Φ ∧ c ≠ d
  · obtain ⟨ha, hb, hab, hc, hd, hcd⟩ :=
      hx.choose_spec.choose_spec.choose_spec.choose_spec
    have htw : H.t = L.rep ⟨swap hx.choose hx.choose_spec.choose *
        swap hx.choose_spec.choose_spec.choose hx.choose_spec.choose_spec.choose_spec.choose,
        by rw [Perm.mem_alternatingGroup, Perm.sign_mul, sign_swap hab, sign_swap hcd]; rfl⟩ := by
      rw [ht, twist, dif_pos hx]
    have htG : H.t ∈ S.G := htw ▸ L.rep_mem _
    refine H.twist_facts ha hb hab hc hd hcd htG ?_
    have := L.π_rep ⟨swap hx.choose hx.choose_spec.choose *
        swap hx.choose_spec.choose_spec.choose hx.choose_spec.choose_spec.choose_spec.choose,
        by rw [Perm.mem_alternatingGroup, Perm.sign_mul, sign_swap hab, sign_swap hcd]; rfl⟩
    have e : (⟨H.t, htG⟩ : S.G) = ⟨L.rep _, L.rep_mem _⟩ := Subtype.ext htw
    rw [e, this]
  · have h1 : H.t = 1 := by rw [ht, twist, dif_neg hx]
    refine H.no_twist_facts ?_ h1
    by_contra hC
    push Not at hC
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < H.Φ.card)
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.1 (by omega : 1 < H.Φᶜ.card)
    exact hx ⟨a, b, c, d, ha, hb, hab, Finset.mem_compl.1 hc, Finset.mem_compl.1 hd, hcd⟩
open Classical in
/-- **The default choices of the halving item**: the classical choice of
`lem_large_symmetry_constant_cert_align` and the lift of a fixed paired transposition (`twist`). -/
noncomputable def HalvingChoice.default (S : State Ω C) (L : GiantLabels S) : HalvingChoice S L where
  align Φ Φ' := if h : Φ.card = Φ'.card ∧ 2 ≤ Φ.card then
    ((lem_large_symmetry_constant_cert_align L.π L.π_surj h.1 h.2).choose : Perm Ω) else 1
  align_spec Φ Φ' h1 h2 := ⟨_, by rw [dif_pos ⟨h1, h2⟩],
    (lem_large_symmetry_constant_cert_align L.π L.π_surj h1 h2).choose_spec⟩
  twist Φ := GI.Algorithm.twist (L := L) Φ
  twist_spec Φ h2 := twist_facts' ⟨Φ, 1, GI.Algorithm.twist (L := L) Φ, ⊥⟩ rfl h2

/-- The dominant orbit of a relabeled structure. -/
theorem domSet_smul {ℓ : ℕ} (σ : Perm (Fin L.q)) (X : Canon L.q P.κ ℓ) :
    domSet (σ • X).grp = (domSet X.grp).map σ.toEmbedding := by
  rw [Canon.smul_grp, domSet_conj]

/-- The case of a relabeled structure. -/
theorem aggCase_smul {ℓ : ℕ} (σ : Perm (Fin L.q)) (X : Canon L.q P.κ ℓ) :
    aggCase (σ • X).grp = aggCase X.grp := by
  rw [Canon.smul_grp, aggCase_conj]

/-- The image of a finset under a permutation, as a set. -/
theorem image_coe_finset (σ : Perm (Fin L.q)) (Φ : Finset (Fin L.q)) :
    σ '' (Φ : Set (Fin L.q)) = ((Φ.map σ.toEmbedding : Finset (Fin L.q)) : Set (Fin L.q)) := by
  rw [Finset.coe_map]; rfl

/-- **The halving item of Case 2a is valid** (Lemma A.11). The hypotheses: `π_d` agrees with
`π` (`hπ`), `θ ≥ 1/2` (Lemma A.11: "every physical `K`-orbit has size at most `n/2`"),
`q ≥ 10` (the fixed base degree: `|Φ| ≥ 5`), and the Johnson block map `J`. -/
theorem halvingItem_valid (fin : Finite Ω) (πd : S.domGroup →* alternatingGroup (Fin L.q))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) (hK : JointFn)
    (nm : ClassNum S P.κ L.q)
    (hθ : 1 / 2 ≤ P.θ) (hq : 10 ≤ L.q) (J : JohnsonBlocks S L) (hv : HalvingChoice S L) {ℓ : ℕ}
    (src b : Fin ℓ → Fin L.q)
    (hcase : aggCase (structX fin S L πd hK P.κ nm src).grp = .twoA) :
    (halvingItem (P := P) fin πd hv (structX fin S L πd hK P.κ nm src)
      (structY fin S L πd hK P.κ nm b)).Valid (isoSetOf fin S L πd hK P.κ nm src b) := by
  classical
  have hBdef : ∀ g, g ∈ isoSetOf fin S L πd hK P.κ nm src b ↔ ∃ hg : g ∈ S.G,
      (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • structX fin S L πd hK P.κ nm src =
        structY fin S L πd hK P.κ nm b := fun g => Iff.rfl
  generalize isoSetOf fin S L πd hK P.κ nm src b = B at *
  have hcert : (structX fin S L πd hK P.κ nm src).grp =
      (haveI := fin
       letI : Fintype S.dom := Fintype.ofFinite _
       letI : DecidableEq S.dom := Classical.decEq _
       idealGrp S πd P.κ (dstr S S.x)) := rfl
  generalize structX fin S L πd hK P.κ nm src = X at *
  generalize structY fin S L πd hK P.κ nm b = Y at *
  unfold halvingItem
  set Φ := domSet X.grp with hΦdef
  -- the case
  have hne : Φ.Nonempty := by
    unfold aggCase at hcase
    by_contra h
    rw [if_neg h] at hcase
    split_ifs at hcase
  have hgiant : GiantOn X.grp Φ := by
    unfold aggCase at hcase
    rw [if_pos hne] at hcase
    split_ifs at hcase with h
    exact h
  have hdomq : L.q < 2 * Φ.card := domSet_card_lt hne
  have hΦ5 : 5 ≤ Φ.card := by omega
  have hΦc : Φᶜ.card + Φ.card = L.q := by
    rw [Finset.card_compl, Fintype.card_fin]
    have : Φ.card ≤ L.q := by simpa using Finset.card_le_univ Φ
    omega
  -- the parent isomorphisms of the branch map `Φ` onto the dominant orbit of `Y`
  have hbr : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G,
      domSet Y.grp = Φ.map (L.π ⟨g, hg⟩ : Perm (Fin L.q)).toEmbedding := by
    rintro g ⟨-, hgB⟩
    obtain ⟨hg, hgB⟩ := (hBdef g).1 hgB
    refine ⟨hg, ?_⟩
    rw [← hgB, domSet_smul]
  split_ifs with hc
  swap
  · -- differing sizes: the branch is empty
    show S.answer ∩ B = ∅
    refine Set.eq_empty_iff_forall_notMem.2 fun g hg => hc ⟨?_, show 2 ≤ Φ.card by omega⟩
    obtain ⟨hgG, he⟩ := hbr g hg
    rw [he, Finset.card_map]
  obtain ⟨τ, hτeq, hτspec⟩ := hv.align_spec Φ (domSet Y.grp) hc.1 hc.2
  rw [← hτeq]
  set H : Halving S L :=
    { Φ := Φ
      τ₀ := (τ : Perm Ω)
      t := hv.twist Φ
      A := certLift S L fin πd P.κ ⊓ L.lift (evenSides Φ Φᶜ) } with hHdef
  refine ⟨⟨τ.2, (hv.twist_spec Φ hc.2).1, (hv.twist_spec Φ hc.2).2, inf_le_right, ?_, ?_,
    ?_, hdomq⟩, ?_⟩
  · -- `A` preserves `x`
    intro a ha v hv
    haveI := fin
    letI : Fintype S.dom := Fintype.ofFinite _
    letI : DecidableEq S.dom := Classical.decEq _
    obtain ⟨haG, hac⟩ := State.mem_liftGroup.1 ha.1
    have := (certGroup_le_automorphisms S πd P.κ (dstr S S.x) hac).2 ⟨v, hv⟩
    exact this
  · -- `A` meets every coset of the kernel (the pure alternating group)
    refine H.onto_of_agree inf_le_right fun h hh => ?_
    obtain ⟨hhG, hhE⟩ := (L.mem_lift).1 hh
    have hF : X.grp ≤ alternatingGroup (Fin L.q) := by
      intro f hf
      rw [hcert] at hf
      obtain ⟨e, -, rfl⟩ := hf
      exact e.2
    have hpure := pure_of_giantOn hF (fun f hf a ha => apply_mem_domSet hf ha) hgiant hΦ5
      (show Φᶜ.card < Φ.card by omega)
    set e := evenLeft Φ Φᶜ ⟨L.π ⟨h, hhG⟩, hhE⟩ with hedef
    have hσe : ofSubtype (e : Perm Φ) ∈ alternatingGroup (Fin L.q) := by
      rw [Perm.mem_alternatingGroup, sign_ofSubtype]; exact e.2
    have hσF := hpure _ hσe (fun a ha => ofSubtype_apply_of_not_mem _ ha)
    -- `ofSubtype e = π_d(k)` for an element `k` of the certificate group
    haveI := fin
    letI : Fintype S.dom := Fintype.ofFinite _
    letI : DecidableEq S.dom := Classical.decEq _
    rw [hcert] at hσF
    obtain ⟨_, ⟨k, hk, rfl⟩, hke⟩ := hσF
    obtain ⟨g, hg⟩ := k.2
    have hkg : (⟨S.domHom g, g, rfl⟩ : S.domGroup) = k := Subtype.ext hg
    have hπg : (L.π g : Perm (Fin L.q)) = ofSubtype (e : Perm Φ) := by
      rw [← hπ g, hkg]; exact hke
    have hgP : L.π g ∈ permitted Φ Φᶜ := by
      refine mem_sides_of_maps _ (fun a ha => ?_) (fun a ha => ?_)
      · show (L.π g : Perm (Fin L.q)) a ∈ Φ
        rw [hπg, ofSubtype_apply_of_mem _ ha]; exact (e.1 ⟨a, ha⟩).2
      · rw [Finset.mem_compl] at ha
        show (L.π g : Perm (Fin L.q)) a ∈ Φᶜ
        rw [hπg, ofSubtype_apply_of_not_mem _ ha]; exact Finset.mem_compl.2 ha
    have hgE : L.π g ∈ evenSides Φ Φᶜ := by
      refine (mem_evenSides_compl_iff Φ ⟨_, hgP⟩).2 ?_
      have : (sideAction (⟨L.π g, hgP⟩ : permitted Φ Φᶜ)).1 = (e : Perm Φ) := by
        refine Equiv.ext fun x => Subtype.ext ?_
        change (L.π g : Perm (Fin L.q)) x = _
        rw [hπg, ofSubtype_apply_coe]
      rw [this]; exact e.2
    refine ⟨(g : Perm Ω), ⟨State.mem_liftGroup.2 ⟨g.2, by rw [hg]; exact hk⟩,
      (L.mem_lift).2 ⟨g.2, hgE⟩⟩, hhG, g.2, fun a ha => ?_⟩
    have h1 : (L.π ⟨(g : Perm Ω), g.2⟩ : Perm (Fin L.q)) a = ((e : Perm Φ) ⟨a, ha⟩ : Fin L.q) := by
      change (L.π g : Perm (Fin L.q)) a = _
      rw [hπg, ofSubtype_apply_of_mem _ ha]
    rw [h1, hedef, evenLeft_apply]
  · -- the kernel orbits are small (the Johnson block map)
    haveI := fin
    refine H.orb_small_of_blocks J.p (f := J.f) J.equivariant J.card (fun Bl hBl => ?_) J.one_le
      J.half hdomq hθ
    letI : Fintype S.dom := Fintype.ofFinite _
    rw [← J.fibers Bl hBl, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · -- every parent isomorphism of the branch lies in `τ₀ H`
    intro g hg
    obtain ⟨hgG, he⟩ := hbr g hg
    have himg : (L.π ⟨g, hgG⟩ : Perm (Fin L.q)) '' (Φ : Set (Fin L.q)) = domSet Y.grp := by
      rw [he, image_coe_finset]
    have hm := hτspec.2 ⟨g, hgG⟩ himg
    refine ⟨(τ : Perm Ω)⁻¹ * g, (L.mem_lift).2 ⟨S.G.mul_mem (S.G.inv_mem τ.2) hgG, hm⟩, ?_⟩
    show (τ : Perm Ω) * ((τ : Perm Ω)⁻¹ * g) = g
    group
end Halving

/-! ### Completeness of the queries -/

namespace AuxQuery

/-- **A query is exact on a set of label permutations** `T`: as soon as `T` has an element, a
representative is read off the answer of the query. This is what an exact recursive call on the
configuration or on the rectangle provides: the call returns all isomorphisms of the colored
structure it is asked about, so the label image of each parent isomorphism of the branch (an
element of `T`) gives an element of the answer, and the answer yields a representative. -/
def Covers (Q : AuxQuery P S L) (T : Set (Perm (Fin L.q))) : Prop :=
  ∀ σ ∈ T, ∃ τ, Q.read Q.T.answer = some τ

/-- **Completeness from exactness**: if the label image of every parent isomorphism of the
branch lies in a set `T` on which some query is exact, then that query answers whenever the
branch is nonempty. -/
theorem comp_of_covers {B : Set (Perm Ω)} {Qs : List (AuxQuery P S L)} {Q : AuxQuery P S L}
    (hQ : Q ∈ Qs) {T : Set (Perm (Fin L.q))} (hcov : Q.Covers T)
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G,
      ((L.π ⟨g, hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) ∈ T) :
    (S.answer ∩ B).Nonempty → ∃ Q ∈ Qs, ∃ τ, Q.read Q.T.answer = some τ := by
  rintro ⟨g, hg⟩
  obtain ⟨hgG, hgT⟩ := hB g hg
  obtain ⟨τ, hτ⟩ := hcov _ hgT
  exact ⟨Q, hQ, τ, hτ⟩

end AuxQuery

namespace AuxItem

/-- **A configuration query item, with completeness derived** (Lemma A.12). The same as
`valid_query_config`, but the completeness hypothesis is replaced by exactness of one query on
the configuration transporter: by Lemma A.12 (`hB`), every parent isomorphism of the branch maps
into that transporter, so the query answers. -/
theorem valid_query_config_of_covers {δ : ℝ} (hβ : max (1 - δ) (1 / 2) < P.β) :
    ∃ q₀ : ℕ, ∀ {Ω C : Type} {S : State Ω C} (L : GiantLabels S) {B : Set (Perm Ω)} (n : ℕ)
      (c : Coloring n) (side target : Bool) (ι : Fin n ↪ Fin L.q), Coherent c →
      Homogeneous c side → NontrivialOffDiagonal c side → δ * L.q ≤ n → q₀ ≤ L.q →
      ∀ Qs : List (AuxQuery P S L), Qs.length ≤ 2 → (∀ Q ∈ Qs, AggCall P S Q.mode Q.T) →
      (∀ Q ∈ Qs, ∀ σ, Q.read Q.T.answer = some σ →
        ((σ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) ∈
          configTransporter ι c side target) →
      (∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G,
        ((L.π ⟨g, hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) ∈
          configTransporter ι c side target) →
      (∃ Q ∈ Qs, Q.Covers (configTransporter ι c side target)) →
      (query Qs ((configGroup ι c side).comap (alternatingGroup (Fin L.q)).subtype) :
        AuxItem P S L).Valid B := by
  obtain ⟨q₀, hq₀⟩ := valid_query_config (P := P) hβ
  refine ⟨q₀, fun L B n c side target ι hc hh hn hδ hq Qs hlen hcalls hrep hB hex => ?_⟩
  obtain ⟨Q, hQ, hcov⟩ := hex
  exact hq₀ L n c side target ι hc hh hn hδ hq Qs hlen hcalls hrep hB
    (AuxQuery.comp_of_covers hQ hcov hB)

/-- **A rectangle query item, with completeness derived** (Lemma 5.1; Lemmas A.27 and A.30).
The same as `valid_query_rectangle`, but the completeness hypothesis is replaced by exactness
of one query on the aligned left transporters `a₀ · leftOvercoset M N`. -/
theorem valid_query_rectangle_of_covers {B : Set (Perm Ω)} {W R : Finset (Fin L.q)}
    (M N : W → R → Bool) (a₀ : alternatingGroup (Fin L.q))
    (Qs : List (AuxQuery P S L)) (hcap : (aw (leftGroup M) : ℝ) ≤ P.β * L.q)
    (hlen : Qs.length ≤ 2) (hcalls : ∀ Q ∈ Qs, AggCall P S Q.mode Q.T)
    (hrep : ∀ Q ∈ Qs, ∀ σ, Q.read Q.T.answer = some σ → a₀⁻¹ * σ ∈ leftOvercoset M N)
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, a₀⁻¹ * L.π ⟨g, hg⟩ ∈ leftOvercoset M N)
    (hex : ∃ Q ∈ Qs, Q.Covers
      {σ | ∃ e : alternatingGroup (Fin L.q), (e : Perm (Fin L.q)) = σ ∧
        a₀⁻¹ * e ∈ leftOvercoset M N}) :
    (query Qs (leftGroup M) : AuxItem P S L).Valid B := by
  obtain ⟨Q, hQ, hcov⟩ := hex
  refine valid_query_rectangle M N a₀ Qs hcap hlen hcalls hrep hB
    (AuxQuery.comp_of_covers hQ hcov fun g hg => ?_)
  obtain ⟨hgG, hgM⟩ := hB g hg
  exact ⟨hgG, _, rfl, hgM⟩

end AuxItem

/-! ### The plan -/

/-- **The plan of an aggregation round** (Section A.3; Lemma A.11; Algorithm `alg:auxiliary`):
the item of a branch from the canonical structures `X` of `(x, src)` and `Y` of `(y, b)`, by the
case of the ideal certificate group of `X`. Case 1 gives the colored orbit partition
(`caseOneItem`), Case 2a the halving item (`halvingItem`), and Cases 2b and 3 the item `cfg`
of the configuration branch. -/
noncomputable def plan (fin : Finite Ω) (πd : S.domGroup →* alternatingGroup (Fin L.q))
    (hv : HalvingChoice S L) {ℓ : ℕ}
    (cfg : Canon L.q P.κ ℓ → Canon L.q P.κ ℓ → AuxItem P S L)
    (X Y : Canon L.q P.κ ℓ) : AuxItem P S L :=
  match aggCase X.grp with
  | .one => caseOneItem X Y
  | .twoA => halvingItem fin πd hv X Y
  | .twoB => cfg X Y
  | .three => cfg X Y

/-- **The plan is valid** for every branch: in Case 1 by `caseOneItem_valid`, in Case 2a by
`halvingItem_valid`, and in Cases 2b and 3 by the hypothesis `hcfg` on the configuration
branch. -/
theorem plan_valid (fin : Finite Ω) (πd : S.domGroup →* alternatingGroup (Fin L.q))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) (hK : JointFn)
    (nm : ClassNum S P.κ L.q)
    (hβ : 1 / 2 ≤ P.β) (hθ : 1 / 2 ≤ P.θ) (hq : 10 ≤ L.q) (J : JohnsonBlocks S L)
    (hv : HalvingChoice S L) {ℓ : ℕ}
    (cfg : Canon L.q P.κ ℓ → Canon L.q P.κ ℓ → AuxItem P S L)
    (src b : Fin ℓ → Fin L.q)
    (hcfg : aggCase (structX fin S L πd hK P.κ nm src).grp = .twoB ∨
        aggCase (structX fin S L πd hK P.κ nm src).grp = .three →
      (cfg (structX fin S L πd hK P.κ nm src) (structY fin S L πd hK P.κ nm b)).Valid
        (isoSetOf fin S L πd hK P.κ nm src b)) :
    (plan (P := P) fin πd hv cfg (structX fin S L πd hK P.κ nm src)
      (structY fin S L πd hK P.κ nm b)).Valid (isoSetOf fin S L πd hK P.κ nm src b) := by
  have hB : ∀ g ∈ S.answer ∩ isoSetOf fin S L πd hK P.κ nm src b, ∃ hg : g ∈ S.G,
      (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • structX fin S L πd hK P.κ nm src =
        structY fin S L πd hK P.κ nm b := fun g hg => hg.2
  unfold plan
  split
  · next h => exact caseOneItem_valid hβ hB h
  · next h => exact halvingItem_valid fin πd hπ hK nm hθ hq J hv src b h
  · next h => exact hcfg (Or.inl h)
  · next h => exact hcfg (Or.inr h)

end GI.Algorithm
