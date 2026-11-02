import Workspace.Algorithm.AuxRectQuery
import Workspace.Algorithm.AuxBlocks

/-!
# The rectangle on the cross-pair orbit (Lemma A.27)

Section 5.2: "Suppose the kernel orbits of the current action are indexed by ordered or unordered
pairs of distinct labels of `Γ`. … The positions above `W × R` form one orbit of an appropriate
subgroup of the allowed relabelings. … Pull the color of a matrix entry back to every position
above it. An allowed relabeling preserves these pulled-back colors exactly when its action on the
rectangle preserves the matrix. A complete answer on `Δ` therefore projects to the complete
permitted matrix answer."

This file builds the representation `RectRep` of a rectangle from a kernel-orbit quotient
`f : dom → Ξ` of the domain action (Lemma A.26, `GI.Paper.lem_support_two_orbit_quotient`) and an
embedding `e : W × R ↪ Ξ` of the rectangle into the pairs:

* the group is `H = π⁻¹(P)`, `P = (Sym W × Sym R × Sym Y) ∩ Alt Γ` (Lemma A.27);
* a position `v` lies above the matrix entry `c` when `f(v) = e(c)`;
* every permitted label permutation lifts to `H`, since `π` is onto, so no twist is needed;
* the size of `Δ = f⁻¹(e(W × R))` is (IR2): `|Δ| q(q-1) = |W||R| s` for ordered pairs and
  `2 |W||R| s` for unordered pairs (`GI.Paper.lem_inherited_support_two_rectangle_ordered`,
  `_unordered`). With `|W||R| ≤ η(1-η)q² = 3q²/16` (Lemma A.28) and `q ≥ 4` this gives
  `|Δ| ≤ 3qs/(8(q-1)) ≤ s/2 ≤ θ s` ("the unordered case is the larger one, with ratio at most
  `2η(1-η)m/(m-1)`"; Section 7.5 (iii): "Choose `θ < 1` above `1/2`").

At the end, `rectRepOf` chooses the representation from the support classification (Corollary
A.25, `SupportCases`): the cross-pair orbit for ordered or unordered pairs, and a supplied
representation (Lemma A.30, the diagonal carrier) for natural labels.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Rectangle GI.StabilizerQuotient

variable {P : Params} {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-! ### The kernel-orbit quotient on the domain -/

section Quotient

variable {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
  {Ξ : Type} [MulAction (alternatingGroup (Fin L.q)) Ξ] (f : KernelQuotient πd S.dom Ξ)

include hπ in
/-- The quotient map is equivariant under the parent action, through `π`. -/
theorem kq_map_apply (g : S.G) {v : Ω} (hv : v ∈ S.dom) :
    f.map ⟨(g : Perm Ω) v, (S.dom_inv g.1 g.2 v).2 hv⟩ = L.π g • f.map ⟨v, hv⟩ := by
  have e := f.equivariant ⟨S.domHom g, g, rfl⟩ ⟨v, hv⟩
  rw [hπ] at e
  have e2 : ((⟨S.domHom g, g, rfl⟩ : S.domGroup) • (⟨v, hv⟩ : S.dom)) =
      ⟨(g : Perm Ω) v, (S.dom_inv g.1 g.2 v).2 hv⟩ := Subtype.ext rfl
  rw [e2] at e
  exact e

variable {W R : Finset (Fin L.q)} (e : W × R ↪ Ξ)

open Classical in
/-- The matrix entry above a position: `c` when `f(v) = e(c)`. -/
noncomputable def pairCell (v : Ω) : Option (W × R) :=
  if hv : v ∈ S.dom then
    if h : f.map ⟨v, hv⟩ ∈ Set.range e then
      some (GI.EmbeddedQuotient.map f e ⟨⟨v, hv⟩, h⟩)
    else none
  else none

theorem pairCell_eq_some {v : Ω} (hv : v ∈ S.dom) (c : W × R) :
    pairCell f e v = some c ↔ f.map ⟨v, hv⟩ = e c := by
  classical
  unfold pairCell
  rw [dif_pos hv]
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact (GI.EmbeddedQuotient.embed_map f e ⟨⟨v, hv⟩, h⟩).symm
    · intro hc
      apply e.injective
      rw [GI.EmbeddedQuotient.embed_map]
      exact hc
  · simp only [false_iff]
    intro hc
    exact h ⟨c, hc.symm⟩

theorem pairCell_eq_none {v : Ω} (hv : v ∈ S.dom) :
    pairCell f e v = none ↔ f.map ⟨v, hv⟩ ∉ Set.range e := by
  classical
  unfold pairCell
  rw [dif_pos hv]
  split_ifs with h <;> simp [h]

/-- The group of the query: `H = π⁻¹(P)`. -/
def pairH (W R : Finset (Fin L.q)) : Subgroup (Perm Ω) := L.lift (permitted W R)

theorem pairH_image {h : Perm Ω} (hh : h ∈ pairH (L := L) W R) :
    L.π ⟨h, L.lift_le _ hh⟩ ∈ permitted W R :=
  (L.mem_lift.1 hh).2

variable (he : ∀ (g : permitted W R) (p : W × R),
  e (movePoint g p) = (g : alternatingGroup (Fin L.q)) • e p)

include hπ he in
theorem pairCell_equivariant {h : Perm Ω} (hh : h ∈ pairH (L := L) W R) {v : Ω}
    (hv : v ∈ S.dom) :
    pairCell f e (h v) = (pairCell f e v).map (movePoint ⟨_, pairH_image hh⟩) := by
  set g : permitted W R := ⟨_, pairH_image hh⟩
  have hv' : h v ∈ S.dom := (S.dom_inv h (L.lift_le _ hh) v).2 hv
  have hk := kq_map_apply hπ f ⟨h, L.lift_le _ hh⟩ hv
  cases hc : pairCell f e v with
  | some c =>
    rw [Option.map_some, pairCell_eq_some f e hv', he]
    rw [pairCell_eq_some f e hv] at hc
    rw [← hc]
    exact hk
  | none =>
    rw [Option.map_none, pairCell_eq_none f e hv']
    rw [pairCell_eq_none f e hv] at hc
    rintro ⟨c', hc'⟩
    apply hc
    refine ⟨movePoint g⁻¹ c', ?_⟩
    rw [he, hc']
    rw [show f.map ⟨h v, hv'⟩ = L.π ⟨h, L.lift_le _ hh⟩ • f.map ⟨v, hv⟩ from hk]
    rw [← mul_smul]
    change ((L.π ⟨h, L.lift_le _ hh⟩)⁻¹ * L.π ⟨h, L.lift_le _ hh⟩) • _ = _
    rw [inv_mul_cancel, one_smul]

/-- The positions above the rectangle are the points of the domain whose quotient lies in
`e(W × R)`. -/
noncomputable def pairCellEquiv :
    {v // v ∈ S.dom ∧ pairCell f e v ≠ none} ≃ {x : S.dom // f.map x ∈ Set.range e} where
  toFun v := ⟨⟨v.1, v.2.1⟩, by
    by_contra h
    exact v.2.2 ((pairCell_eq_none f e v.2.1).2 h)⟩
  invFun x := ⟨x.1.1, x.1.2, fun h => (pairCell_eq_none f e x.1.2).1 h x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hπ he in
/-- **The representation of a rectangle on the cross-pair orbit** (Lemma A.27), given the size
bound of its orbit. -/
noncomputable def RectRep.ofQuotient
    (hcount : (Nat.card {x : S.dom // f.map x ∈ Set.range e} : ℝ) ≤ P.θ * S.size) :
    RectRep P S L W R where
  H := pairH W R
  le := L.lift_le _
  image _ hh := pairH_image hh
  cell := pairCell f e
  equivariant _ hh _ hv := pairCell_equivariant hπ f e he hh hv
  onto c := by
    obtain ⟨x, hx⟩ := f.onto (e c)
    exact ⟨x.1, x.2, (pairCell_eq_some f e x.2 c).2 hx⟩
  twist := none
  -- "Every permitted pair permutation has a lift in `H`"
  lifts p := by
    left
    obtain ⟨g, hg⟩ := L.π_surj p
    exact ⟨g.1, L.mem_lift.2 ⟨g.2, by rw [hg]; exact p.2⟩, hg⟩
  small := by rw [Nat.card_congr (pairCellEquiv f e)]; exact hcount

end Quotient

/-! ### The size of the orbit (IR2) -/

/-- **The orbit has at most `θ s` points**: from `|Δ| q(q-1) ≤ 2|W||R| s`,
`|W||R| ≤ 3q²/16`, `q ≥ 4` and `θ ≥ 1/2`. -/
theorem rect_count_le {c q w r s : ℕ} {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hq : 4 ≤ q)
    (hcount : c * (q * (q - 1)) ≤ 2 * (w * r * s))
    (harea : (w : ℝ) * r ≤ etaB * (1 - etaB) * (q : ℝ) ^ 2) :
    (c : ℝ) ≤ θ * s := by
  have hq' : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hcast : ((c * (q * (q - 1)) : ℕ) : ℝ) = (c : ℝ) * ((q : ℝ) * ((q : ℝ) - 1)) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  have h1 : (c : ℝ) * ((q : ℝ) * ((q : ℝ) - 1)) ≤ 2 * ((w : ℝ) * r * s) := by
    rw [← hcast]; exact_mod_cast hcount
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have h2 : 2 * ((w : ℝ) * r * s) ≤ 3 / 8 * (q : ℝ) ^ 2 * s := by
    have : (w : ℝ) * r ≤ 3 / 16 * (q : ℝ) ^ 2 := by
      have e : etaB * (1 - etaB) = 3 / 16 := by norm_num [etaB]
      rw [e] at harea; exact harea
    nlinarith
  -- `c (q - 1) ≤ 3 q s / 8`, and `3q/8 ≤ (q-1)/2` for `q ≥ 4`
  have h3 : (c : ℝ) * ((q : ℝ) - 1) ≤ 3 / 8 * (q : ℝ) * s := by
    have hqpos : (0 : ℝ) < q := by linarith
    have := h1.trans h2
    nlinarith
  have h4 : (c : ℝ) ≤ s / 2 := by
    by_contra hlt
    push Not at hlt
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    nlinarith
  nlinarith

/-- `|W ∪ R| ≤ q`, so a rectangle with `|W| ≥ 3` and `R` nonempty needs `q ≥ 4`. -/
theorem four_le_of_rect {q : ℕ} {W R : Finset (Fin q)} (hd : Disjoint W R) (hW : 3 ≤ W.card)
    (hR : R.Nonempty) : 4 ≤ q := by
  have h1 := Finset.card_union_of_disjoint hd
  have h2 : (W ∪ R).card ≤ q := by simpa using Finset.card_le_univ (W ∪ R)
  have h3 := hR.card_pos
  omega

/-! ### The two pair cases -/

section Pairs

variable [Finite Ω] {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) {W R : Finset (Fin L.q)}

include hπ in
/-- **Lemma A.27, ordered pairs**: the representation on `Δ = f⁻¹(W × R)`. -/
noncomputable def RectRep.ordered (hθ : 1 / 2 ≤ P.θ)
    (f : KernelQuotient πd S.dom (GI.Pairs.OrderedPair (Fin L.q))) (hc : RectConds P S L W R) :
    RectRep P S L W R :=
  RectRep.ofQuotient hπ f (orderedEmbedding hc.2.1) (orderedEmbedding_move hc.2.1) (by
    classical
    obtain ⟨-, hd, hW, hR, harea⟩ := hc
    letI : Fintype S.dom := Fintype.ofFinite _
    have h := (GI.Paper.lem_inherited_support_two_rectangle_ordered.{0, 0, 0, 0} S.domGroup πd
      (πd_surjective hπ) f W R hd hW hR).2.2.1
    rw [Fintype.card_fin] at h
    have hs : Fintype.card S.dom = S.size := by rw [State.size, Nat.card_eq_fintype_card]
    rw [hs] at h
    refine rect_count_le hθ (four_le_of_rect hd hW hR) (le_of_eq_of_le h ?_) harea
    omega)

include hπ in
/-- **Lemma A.27, unordered pairs**: the representation on `Δ = f⁻¹(W × R)`. -/
noncomputable def RectRep.unordered (hθ : 1 / 2 ≤ P.θ)
    (f : KernelQuotient πd S.dom (GI.Johnson.SubsetVertex (Fin L.q) 2))
    (hc : RectConds P S L W R) : RectRep P S L W R :=
  RectRep.ofQuotient hπ f (unorderedEmbedding hc.2.1) (unorderedEmbedding_move hc.2.1) (by
    classical
    obtain ⟨-, hd, hW, hR, harea⟩ := hc
    letI : Fintype S.dom := Fintype.ofFinite _
    have h := (GI.Paper.lem_inherited_support_two_rectangle_unordered.{0, 0, 0, 0} S.domGroup πd
      (πd_surjective hπ) f W R hd hW hR).2.2.1
    rw [Fintype.card_fin] at h
    have hs : Fintype.card S.dom = S.size := by rw [State.size, Nat.card_eq_fintype_card]
    rw [hs] at h
    exact rect_count_le hθ (four_le_of_rect hd hW hR) h.le harea)

end Pairs

/-! ### Natural labels from the one-label quotient -/

/-- A one-label kernel-orbit quotient of the domain action gives natural rows
(`NaturalRows`). -/
theorem naturalRows_of {πd : S.domGroup →* alternatingGroup (Fin L.q)}
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) (hq : 0 < L.q)
    (f : KernelQuotient πd S.dom (Fin L.q)) : ∃ label, NaturalRows S L label := by
  classical
  refine ⟨fun v => if hv : v ∈ S.dom then f.map ⟨v, hv⟩ else ⟨0, hq⟩, ?_, ?_, ?_⟩
  · intro g v hv
    have hv' : (g : Perm Ω) v ∈ S.dom := (S.dom_inv g.1 g.2 v).2 hv
    simp only [dif_pos hv, dif_pos hv']
    exact kq_map_apply hπ f g hv
  · intro i
    obtain ⟨x, hx⟩ := f.onto i
    exact ⟨x.1, x.2, by simp only [dif_pos x.2]; exact hx⟩
  · intro v hv w hw
    simp only [dif_pos hv, dif_pos hw]
    rw [f.kernel_fibers]
    constructor
    · rintro ⟨k, hk1, hkv⟩
      obtain ⟨g, hg⟩ := k.2
      have hk : k = ⟨S.domHom g, g, rfl⟩ := Subtype.ext hg.symm
      subst hk
      refine ⟨g, by rw [← hπ]; exact hk1, ?_⟩
      exact congrArg Subtype.val hkv
    · rintro ⟨g, hg1, hgv⟩
      refine ⟨⟨S.domHom g, g, rfl⟩, by rw [hπ]; exact hg1, Subtype.ext ?_⟩
      exact hgv

/-! ### The representation chosen by the support classification -/

open Classical in
/-- **The rectangle representation of a branch `q > λ`** (Algorithm `alg:auxiliary`: "For a
large configuration, the inherited representation is either the cross-pair orbit or the
row--column diagonal orbit described above"). By the support classification (`SupportCases`,
Corollary A.25) the kernel orbits are indexed by ordered pairs, by unordered pairs, or by single
labels. For pairs it is the cross-pair orbit (Lemma A.27); for single labels it is the supplied
representation `nat` (the diagonal carrier of Lemma A.30). -/
noncomputable def rectRepOf [Finite Ω] {πd : S.domGroup →* alternatingGroup (Fin L.q)}
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) (hθ : 1 / 2 ≤ P.θ)
    (nat : (S.N : ℝ) ^ P.α < L.q → (∃ label, NaturalRows S L label) →
      ∀ W R, RectConds P S L W R → RectRep P S L W R)
    (hcases : (S.N : ℝ) ^ P.α < L.q →
      Nonempty (KernelQuotient πd S.dom (Fin L.q)) ∨
      Nonempty (KernelQuotient πd S.dom (GI.Pairs.OrderedPair (Fin L.q))) ∨
      Nonempty (KernelQuotient πd S.dom (GI.Johnson.SubsetVertex (Fin L.q) 2)))
    (W R : Finset (Fin L.q)) (hc : RectConds P S L W R) : RectRep P S L W R :=
  if ho : Nonempty (KernelQuotient πd S.dom (GI.Pairs.OrderedPair (Fin L.q))) then
    RectRep.ordered hπ hθ ho.some hc
  else if hu : Nonempty (KernelQuotient πd S.dom (GI.Johnson.SubsetVertex (Fin L.q) 2)) then
    RectRep.unordered hπ hθ hu.some hc
  else
    nat hc.1 (by
      rcases hcases hc.1 with hn | h | h
      · exact naturalRows_of hπ (by have := four_le_of_rect hc.2.1 hc.2.2.1 hc.2.2.2.1; omega)
          hn.some
      · exact absurd h ho
      · exact absurd h hu) W R hc

end GI.Algorithm
