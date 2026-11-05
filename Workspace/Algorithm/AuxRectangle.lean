module

public import Workspace.Algorithm.AuxPartitions

@[expose] public section

/-!
# The first rectangle of a configuration branch (Lemma 5.1)

Algorithm `alg:auxiliary`, the branch `q > λ`: "**for each** source--target choice in the
first-rectangle construction **do**: **if** it gives a balanced partition **then** append its
full-`Γ` overcoset to `ℰ`; **continue**. Align the two rectangles; **skip** this choice if side
sizes differ. Represent the rectangle on an actual inherited orbit `Δ`. Pull matrix-entry colors
back to `Δ` in both instances. Use `Continue` to obtain its complete permitted rectangle answer.
**if** this answer is empty **then continue**. Project to the left side; extend over `Γ \ W` and
impose parity. Append the resulting full-`Γ` overcoset to `ℰ`."

This file builds the item of one source--target choice: the source vertex `x₀` of the source
configuration `X` and its target image `y₀` in the target configuration `Y`
(`sojItem`). It follows Lemma 5.1 (`GI.Paper.lem_main_rectangle`) and Lemma A.28:

* if the configuration of `X` is imprimitive, the overcoset of the canonical equal-block
  partition (`PairCfg.impPart`);
* if it is primitive and every color class at `x₀` has at most `η|C|` points, the overcoset of
  the balanced partition at `x₀` (`PairCfg.balPart`);
* otherwise the first rectangle `W, R` at `x₀` with its matrix `M`: the target sides `W', R'` at
  `y₀` and the target matrix are read with the same colors; if the side sizes differ the branch
  is empty; otherwise an even alignment `a₀` (`GI.Paper.par_parity_alignment`) and the rectangle
  queries of a `RectOracle`, with the group `leftGroup M`.

`RectOracle` is the step "Represent the rectangle on an actual inherited orbit `Δ` … Use
`Continue` …": at most two charged `Continue` calls whose answers give representatives in
`a₀ · leftOvercoset M N`, and that answer as soon as a permitted matrix transporter exists. It
is built from a representation of the rectangle on an inherited orbit (`RectRep`,
`Workspace/Algorithm/AuxRectQuery.lean`): for pair labels from the support-two orbit quotient of
Lemma A.26 (Lemma A.27, `Workspace/Algorithm/AuxPairRect.lean`); for natural labels it is
Lemma A.30.

The parameters are `η = 3/4` (Section 5.1: "Choose an absolute balance parameter `η > 2/3`") and
`δ = 1/4` (Section A.3, "Balance parameters": "Thus `|C| ≥ δq` for `0 < δ ≤ 1/4`"). The cap
needs `β ≥ max{1/2, 1-δ, 1-ηδ, η} = 13/16`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.PairRefinement GI.CoherentEntrance GI.Rectangle GI.Paper

/-- The balance parameter `η = 3/4` of Section 5.1 ("Choose an absolute balance parameter
`η > 2/3`"). -/
noncomputable def etaB : ℝ := 3 / 4

/-- The fraction `δ = 1/4` of Section A.3, "Balance parameters" ("Thus `|C| ≥ δq` for
`0 < δ ≤ 1/4`"). -/
noncomputable def deltaB : ℝ := 1 / 4

namespace PairCfg

variable {q : ℕ}

/-! ### From the configuration on `Γ` to its coloring on `Fin |C|` -/

theorem vals_of_mem {P : PairCfg q} {a b : Fin q} (ha : a ∈ P.fiber) (hb : b ∈ P.fiber) :
    P.col a b ∈ P.vals := by
  obtain ⟨i, rfl⟩ := P.exists_emb rfl ha
  obtain ⟨k, rfl⟩ := P.exists_emb rfl hb
  exact P.col_mem_vals i k

theorem coloring_apply (P : PairCfg q) (s : Bool) (i k : Fin P.fiber.card) :
    P.coloring (s, i, k) = P.enc (P.col (P.emb rfl i) (P.emb rfl k)) := rfl

/-- The coloring has the code of `v` exactly where the configuration has the color `v`. -/
theorem coloring_eq_enc {P : PairCfg q} {v : ℕ} (hv : v ∈ P.vals) (s : Bool)
    (i k : Fin P.fiber.card) :
    P.coloring (s, i, k) = P.enc v ↔ P.col (P.emb rfl i) (P.emb rfl k) = v := by
  rw [coloring_apply]
  exact ⟨P.enc_inj (P.col_mem_vals i k) hv, fun h => by rw [h]⟩

/-- The color classes at a vertex of the fiber are the color classes of the coloring. -/
theorem filter_col_eq_map {P : PairCfg q} {v : ℕ} (hv : v ∈ P.vals) (i : Fin P.fiber.card) :
    P.fiber.filter (fun a => P.col (P.emb rfl i) a = v) =
      (colorClass P.coloring false i (P.enc v)).map (P.emb rfl) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_map, mem_colorClass]
  constructor
  · rintro ⟨ha, hav⟩
    obtain ⟨k, rfl⟩ := P.exists_emb rfl ha
    exact ⟨k, (coloring_eq_enc hv false i k).2 hav, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨P.emb_mem rfl k, (coloring_eq_enc hv false i k).1 hk⟩

/-- The edges of color `v` are the edges of the code of `v`. -/
theorem edge_emb_iff {P : PairCfg q} {v : ℕ} (hv : v ∈ P.vals) (s : Bool) (i k : Fin P.fiber.card) :
    P.edge v (P.emb rfl i) (P.emb rfl k) ↔ colorEdge P.coloring s (P.enc v) i k := by
  simp only [edge, colorEdge, coloring_eq_enc hv]
  exact ⟨fun h => h.2.2, fun h => ⟨P.emb_mem rfl i, P.emb_mem rfl k, h⟩⟩

/-- The components of the color `v` are the components of the code of `v`. -/
theorem comp_emb {P : PairCfg q} {v : ℕ} (hv : v ∈ P.vals) (s : Bool) (i : Fin P.fiber.card) :
    P.comp v (P.emb rfl i) = (colorComponent P.coloring s (P.enc v) i).map (P.emb rfl) := by
  ext b
  rw [mem_comp, Finset.mem_map]
  constructor
  · intro h
    -- every point reached lies in the fiber; pull the path back to `Fin |C|`
    have key : ∀ b, P.reach v (P.emb rfl i) b →
        ∃ k, colorReach P.coloring s (P.enc v) i k ∧ P.emb rfl k = b := by
      intro b hb
      induction hb with
      | refl => exact ⟨i, Relation.ReflTransGen.refl, rfl⟩
      | tail _ he ih =>
        obtain ⟨k, hk, rfl⟩ := ih
        obtain ⟨k', rfl⟩ := P.exists_emb rfl he.2.1
        exact ⟨k', Relation.ReflTransGen.tail hk ((edge_emb_iff hv s k k').1 he), rfl⟩
    obtain ⟨k, hk, rfl⟩ := key b h
    exact ⟨k, (mem_colorComponent _ _ _ _ _).2 hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have hk := (mem_colorComponent _ _ _ _ _).1 hk
    exact Relation.ReflTransGen.lift (P.emb rfl) (fun a b hab => (edge_emb_iff hv s a b).2 hab) _ _ hk

end PairCfg

/-! ### The facts of a rectangle certificate (Lemma 5.1) -/

section Certificate

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {n : ℕ}

/-- **The facts of any first-entrance certificate** (the proof of Lemma 5.1,
`GI.Paper.lem_main_rectangle`, for a given certificate): disjoint sides, `|W| > η|C|`,
`|R| ≤ |C| - |W|`, `|W||R| ≤ η(1-η)q²`, left twin classes of at most `|W|/2` points, and the
cap `aw(leftGroup M) ≤ βq`. -/
theorem cert_facts (c : Coloring n) (side : Bool) (ι : Fin n ↪ Γ) {x : Fin n} {η δ β : ℝ}
    (cert : RectangleCertificate c side x η) (hη : 2 / 3 < η) (hη1 : η < 1)
    (hC : δ * Fintype.card Γ ≤ n) (hβ : max (1 / 2) (1 - η * δ) ≤ β) :
    Disjoint (idealSide ι c side x cert.leftColor) (idealSide ι c side x cert.rightColor) ∧
    η * n < ((idealSide ι c side x cert.leftColor).card : ℝ) ∧
    (idealSide ι c side x cert.rightColor).card ≤ n - (idealSide ι c side x cert.leftColor).card ∧
    ((idealSide ι c side x cert.leftColor).card : ℝ) *
        (idealSide ι c side x cert.rightColor).card ≤ η * (1 - η) * (Fintype.card Γ : ℝ) ^ 2 ∧
    SectionCaps.Cap (leftGroup (idealMatrix ι c side x cert.leftColor cert.rightColor
      cert.edgeColor)) ⌊β * Fintype.card Γ⌋₊ := by
  have hnq : n ≤ Fintype.card Γ := by
    simpa using Fintype.card_le_of_injective ι ι.injective
  have hdom := cert.dominant
  have hR : (colorClass c side x cert.rightColor).card ≤
      n - (colorClass c side x cert.leftColor).card := by
    have := cert.sideSum
    rw [colorClass_card, colorClass_card]
    omega
  have harea : ((colorClass c side x cert.leftColor).card : ℝ) *
      (colorClass c side x cert.rightColor).card ≤ η * (1 - η) * (Fintype.card Γ : ℝ) ^ 2 := by
    have h := cert.area
    rw [colorClass_card, colorClass_card]
    have hnq' : (n : ℝ) ≤ Fintype.card Γ := by exact_mod_cast hnq
    have hsq : (n : ℝ) ^ 2 ≤ (Fintype.card Γ : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hnq' 2
    have hcoef : 0 ≤ η * (1 - η) := mul_nonneg (by linarith) (by linarith)
    exact h.trans (mul_le_mul_of_nonneg_left hsq hcoef)
  have htw' : ∀ u, 2 * (Semiregular.twins (idealMatrix ι c side x cert.leftColor
      cert.rightColor cert.edgeColor) u).card ≤ (colorClass c side x cert.leftColor).card := by
    intro u
    have e := twins_card_transfer (idealSideEquiv ι c side x cert.leftColor)
      (idealSideEquiv ι c side x cert.rightColor)
      (fiberMatrix c side x cert.leftColor cert.rightColor cert.edgeColor) u
    exact (congrArg (2 * ·) e).trans_le (cert.twinBound _)
  have hWC : idealSide ι c side x cert.leftColor ⊆ Finset.univ.map ι :=
    Finset.map_subset_map.mpr (Finset.subset_univ _)
  have hCcard : (Finset.univ.map ι).card = n := by simp
  have hcap := par_returned_parent_cap hWC (by linarith : (0 : ℝ) ≤ η)
    (C := Finset.univ.map ι) (δ := δ) (β := β) (by rw [hCcard]; exact hC)
    (by rw [hCcard, card_idealSide]; exact hdom)
    (by rw [hCcard, card_idealSide, card_idealSide]; exact hR) hβ
    (idealMatrix ι c side x cert.leftColor cert.rightColor cert.edgeColor)
    (by intro u; rw [card_idealSide]; exact htw' u)
  simp only [card_idealSide]
  exact ⟨Finset.disjoint_map ι |>.mpr cert.disjoint, hdom, hR, harea, hcap.2.2⟩

end Certificate

/-! ### Rectangle oracles -/

/-- **A rectangle oracle** for the state `S` (Algorithm `alg:auxiliary`: "Represent the rectangle
on an actual inherited orbit `Δ`. Pull matrix-entry colors back to `Δ` in both instances. Use
`Continue` to obtain its complete permitted rectangle answer"; "If the diagonal action supplies
only one parity class of rectangle maps, query both classes by twisting the target matrix … This
uses at most two inherited calls"). The oracle is asked only in the branch `q > λ` of the
algorithm. For disjoint sides `W, R` with `|W| ≥ 3`, `R` nonempty and
`|W||R| ≤ η(1-η)q²`, a source matrix `M`, an aligned target matrix `N` and the alignment `a₀`,
it gives at most two charged calls; every representative read off their answers lies in
`a₀ · leftOvercoset M N` ("Project to the left side; extend over `Γ \ W` and impose parity"), and
some query answers as soon as a permitted matrix transporter from `M` to `N` exists (the calls
are exact). -/
structure RectOracle (P : Params) {Ω C : Type} (S : State Ω C) (L : GiantLabels S) : Type 1 where
  queries : (W R : Finset (Fin L.q)) → (W → R → Bool) → (W → R → Bool) →
    alternatingGroup (Fin L.q) → List (AuxQuery P S L)
  valid : ∀ (W R : Finset (Fin L.q)) (M N : W → R → Bool) (a₀ : alternatingGroup (Fin L.q)),
    (S.N : ℝ) ^ P.α < L.q → Disjoint W R → 3 ≤ W.card → R.Nonempty →
    (W.card : ℝ) * R.card ≤ etaB * (1 - etaB) * (L.q : ℝ) ^ 2 →
    (queries W R M N a₀).length ≤ 2 ∧ (∀ Q ∈ queries W R M N a₀, AggCall P S Q.mode Q.T) ∧
    (∀ Q ∈ queries W R M N a₀, ∀ σ, Q.read Q.T.answer = some σ →
      a₀⁻¹ * σ ∈ leftOvercoset M N) ∧
    ((∃ h : permitted W R, MatrixTransports M N h) →
      ∃ Q ∈ queries W R M N a₀, ∃ σ, Q.read Q.T.answer = some σ)

/-! ### The choices of the first-rectangle construction -/

/-- The predicate "imprimitive with equal blocks" of a pair `a ≠ b` of fiber indices: every
component of the color graph of `(a, b)` has at least two and at most `|C|/2` points (Lemma 5.1,
the imprimitive alternative; Lemma A.28). -/
def ImpPair {q : ℕ} (X : PairCfg q) (a b : Fin X.fiber.card) : Prop :=
  a ≠ b ∧ (∀ x, 2 ≤ (colorComponent X.coloring false (X.coloring (false, a, b)) x).card ∧
    2 * (colorComponent X.coloring false (X.coloring (false, a, b)) x).card ≤ X.fiber.card)

/-- The predicate of an even alignment of two rectangles (`GI.Paper.par_parity_alignment`):
`g₀` maps `W` onto `W'`, `R` onto `R'`, the rest onto the rest, and the even permutations that
map the sides are exactly `g₀ · permitted W R`. -/
def IsAlign {q : ℕ} (W R W' R' : Finset (Fin q)) (g₀ : alternatingGroup (Fin q)) : Prop :=
  (g₀ : Perm (Fin q)) '' (W : Set (Fin q)) = W' ∧
    (g₀ : Perm (Fin q)) '' (R : Set (Fin q)) = R' ∧
    (g₀ : Perm (Fin q)) '' (((W ∪ R)ᶜ : Finset (Fin q)) : Set (Fin q)) =
      (((W' ∪ R')ᶜ : Finset (Fin q)) : Set (Fin q)) ∧
    ∀ g : alternatingGroup (Fin q),
      ((g : Perm (Fin q)) '' (W : Set (Fin q)) = W' ∧ (g : Perm (Fin q)) '' (R : Set (Fin q)) = R') ↔
        g₀⁻¹ * g ∈ permitted W R

/-- **The choices of the first-rectangle construction** (Lemma 5.1, Lemma A.28, Algorithm
`alg:auxiliary`), each with the property the paper asks of it.
* `cert X i₀`: a first-entrance rectangle certificate at the vertex `i₀` when one exists
  (Lemma 5.1: "a rectangle certificate exists"); any certificate works.
* `align`: an even alignment of two rectangles with equal side sizes ("Align the two
  rectangles"; `GI.Paper.par_parity_alignment`).
* `imp X`: a pair of fiber indices whose color has equal-size blocks, when one exists (the
  imprimitive alternative of Lemma 5.1).
The paper fixes none of them; `SojChoice.default` takes classical choices. -/
structure SojChoice where
  cert : ∀ {q : ℕ} (X : PairCfg q) (i₀ : Fin X.fiber.card),
    Nonempty (RectangleCertificate X.coloring false i₀ etaB) →
    RectangleCertificate X.coloring false i₀ etaB
  align : ∀ {q : ℕ} (W R W' R' : Finset (Fin q)), Disjoint W R → Disjoint W' R' →
    W.card = W'.card → R.card = R'.card → 3 ≤ W.card →
    {g₀ : alternatingGroup (Fin q) // IsAlign W R W' R' g₀}
  imp : ∀ {q : ℕ} (X : PairCfg q), (∃ a b, ImpPair X a b) →
    {p : Fin X.fiber.card × Fin X.fiber.card // ImpPair X p.1 p.2}

/-- **The default choices**: classical choices of a certificate, an alignment
(`GI.Paper.par_parity_alignment`) and an imprimitive pair. -/
noncomputable def SojChoice.default : SojChoice where
  cert _ _ h := h.some
  align _ _ _ _ hd hd' hW hR h3 :=
    ⟨((par_parity_alignment hd hd').2 hW hR h3).choose,
      ((par_parity_alignment hd hd').2 hW hR h3).choose_spec⟩
  imp _ h := ⟨(h.choose, h.choose_spec.choose), h.choose_spec.choose_spec⟩

/-! ### The item of one source--target choice -/

section Item

variable {P : Params} {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- The sides of the source rectangle. -/
noncomputable def rectW {q : ℕ} (X : PairCfg q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) : Finset (Fin q) :=
  idealSide (X.emb rfl) X.coloring false i₀ cert.leftColor

noncomputable def rectR {q : ℕ} (X : PairCfg q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) : Finset (Fin q) :=
  idealSide (X.emb rfl) X.coloring false i₀ cert.rightColor

/-- The matrix of the source rectangle. -/
noncomputable def rectM {q : ℕ} (X : PairCfg q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) :
    rectW X i₀ cert → rectR X i₀ cert → Bool :=
  idealMatrix (X.emb rfl) X.coloring false i₀ cert.leftColor cert.rightColor cert.edgeColor

/-- The pair colors of the certificate: of the left side, the right side, and the edges. -/
noncomputable def certVals {q : ℕ} (X : PairCfg q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) : ℕ × ℕ × ℕ :=
  (X.col (X.emb rfl i₀) (X.emb rfl cert.leftPoint),
    X.col (X.emb rfl i₀) (X.emb rfl cert.rightPoint),
    X.col (X.emb rfl cert.mixed.choose) (X.emb rfl cert.rightPoint))

open Classical in
/-- **The rectangle item** of a source--target choice. The target sides are read at `y₀` with the
colors of the source certificate; if the side sizes differ, the branch is empty ("**skip** this
choice if side sizes differ"); otherwise `a₀` is the even alignment of `ch`
(`GI.Paper.par_parity_alignment`), the aligned target matrix is `N(w, r) = [Y(a₀ w, a₀ r) = v_E]`,
and the item is the rectangle query of the oracle with the group `leftGroup M`. -/
noncomputable def rectItem (O : RectOracle P S L) (ch : SojChoice) (X Y : PairCfg L.q) (y₀ : Fin L.q)
    (i₀ : Fin X.fiber.card) (cert : RectangleCertificate X.coloring false i₀ etaB) :
    AuxItem P S L :=
  let W' := Y.fiber.filter fun a => Y.col y₀ a = (certVals X i₀ cert).1
  let R' := Y.fiber.filter fun a => Y.col y₀ a = (certVals X i₀ cert).2.1
  if hs : (rectW X i₀ cert).card = W'.card ∧ (rectR X i₀ cert).card = R'.card ∧
      3 ≤ (rectW X i₀ cert).card ∧ Disjoint (rectW X i₀ cert) (rectR X i₀ cert) ∧
      Disjoint W' R' then
    let a₀ := (ch.align _ _ _ _ hs.2.2.2.1 hs.2.2.2.2 hs.1 hs.2.1 hs.2.2.1).1
    .query (O.queries (rectW X i₀ cert) (rectR X i₀ cert) (rectM X i₀ cert)
        (fun w r => decide (Y.col ((a₀ : Perm (Fin L.q)) w) ((a₀ : Perm (Fin L.q)) r) =
          (certVals X i₀ cert).2.2)) a₀)
      (leftGroup (rectM X i₀ cert))
  else .none

open Classical in
/-- **The item of one source--target choice** of the first-rectangle construction (Lemma 5.1,
Lemma A.28): the source vertex `x₀` of `X` and its target `y₀`. -/
noncomputable def sojItem (O : RectOracle P S L) (ch : SojChoice) (X Y : PairCfg L.q)
    (x₀ y₀ : Fin L.q) :
    AuxItem P S L :=
  if hx : x₀ ∈ X.fiber then
    if PrimitiveColorCuts X.coloring false then
      if ∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤ etaB * X.fiber.card then
        objItem (X.balPart x₀) (Y.balPart y₀)
      else if hcert : Nonempty (RectangleCertificate X.coloring false (X.idx hx) etaB) then
        rectItem O ch X Y y₀ (X.idx hx) (ch.cert X (X.idx hx) hcert)
      else .none
    else
      if himp : ∃ a b, ImpPair X a b then
        objItem (X.impPart (X.col (X.emb rfl (ch.imp X himp).1.1) (X.emb rfl (ch.imp X himp).1.2)))
          (Y.impPart (X.col (X.emb rfl (ch.imp X himp).1.1) (X.emb rfl (ch.imp X himp).1.2)))
      else .none
  else .none

end Item

/-! ### Validity -/

namespace PairCfg

variable {q : ℕ}

/-- The color class at a vertex moves with the relabeling. -/
theorem filter_smul (σ : Perm (Fin q)) (X : PairCfg q) (x₀ : Fin q) (v : ℕ) :
    (σ • X).fiber.filter (fun a => (σ • X).col (σ x₀) a = v) =
      (X.fiber.filter fun a => X.col x₀ a = v).map σ.toEmbedding := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_map_equiv, mem_fiber_smul, smul_col,
    Perm.inv_apply_self]
  rfl

/-- A side of the ideal rectangle is a color class of the configuration at the source vertex. -/
theorem idealSide_eq (X : PairCfg q) (i₀ k : Fin X.fiber.card) (I : Color X.fiber.card)
    (hI : X.coloring (false, i₀, k) = I) :
    idealSide (X.emb rfl) X.coloring false i₀ I =
      X.fiber.filter (fun a => X.col (X.emb rfl i₀) a = X.col (X.emb rfl i₀) (X.emb rfl k)) := by
  subst hI
  rw [filter_col_eq_map (X.col_mem_vals i₀ k)]
  rfl

theorem idealSideEquiv_symm {Γ : Type*} {n : ℕ} (ι : Fin n ↪ Γ) (c : Coloring n) (s : Bool)
    (x : Fin n) (i : Color n) (a : idealSide ι c s x i) :
    ι ((idealSideEquiv ι c s x i).symm a).val = a.val := by
  have h := congrArg Subtype.val ((idealSideEquiv ι c s x i).apply_symm_apply a)
  exact h

end PairCfg

open PairCfg

theorem rectW_eq {q : ℕ} (X : PairCfg q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) :
    rectW X i₀ cert = X.fiber.filter (fun a => X.col (X.emb rfl i₀) a = (certVals X i₀ cert).1) :=
  X.idealSide_eq i₀ _ _ cert.leftPoint.property

theorem rectR_eq {q : ℕ} (X : PairCfg q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) :
    rectR X i₀ cert =
      X.fiber.filter (fun a => X.col (X.emb rfl i₀) a = (certVals X i₀ cert).2.1) :=
  X.idealSide_eq i₀ _ _ cert.rightPoint.property

/-- **The edge value does not depend on the mixed witness**: for every pair `(u, r)` of the edge
color, the third certificate value is the pair color of `(u, r)`. The definition of `certVals`
reads it at the witness `cert.mixed.choose`; a program may read it at any pair of the edge
color, since the code `enc` is injective on the occurring colors (`enc_inj`). -/
theorem certVals_edge {q : ℕ} (X : PairCfg q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) {u r : Fin X.fiber.card}
    (hu : X.coloring (false, u, r) = cert.edgeColor) :
    (certVals X i₀ cert).2.2 = X.col (X.emb rfl u) (X.emb rfl r) := by
  have hE : X.coloring (false, cert.mixed.choose.val, cert.rightPoint.val) = cert.edgeColor := by
    have h := cert.mixed.choose_spec.choose_spec.1
    simpa [fiberMatrix] using h
  have h := hE.trans hu.symm
  rw [coloring_apply, coloring_apply] at h
  exact X.enc_inj (X.col_mem_vals _ _) (X.col_mem_vals _ _) h

/-- The source matrix marks the pairs of the edge color. -/
theorem rectM_apply {q : ℕ} (X : PairCfg q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) (a : rectW X i₀ cert)
    (b : rectR X i₀ cert) :
    rectM X i₀ cert a b = decide (X.col a.val b.val = (certVals X i₀ cert).2.2) := by
  have hE : X.coloring (false, cert.mixed.choose.val, cert.rightPoint.val) = cert.edgeColor := by
    have h := cert.mixed.choose_spec.choose_spec.1
    simpa [fiberMatrix] using h
  have ha := idealSideEquiv_symm (X.emb rfl) X.coloring false i₀ cert.leftColor a
  have hb := idealSideEquiv_symm (X.emb rfl) X.coloring false i₀ cert.rightColor b
  unfold rectM idealMatrix fiberMatrix
  rw [← hE, coloring_apply, coloring_apply, ha, hb]
  have hva : X.col a.val b.val ∈ X.vals := by
    rw [← ha, ← hb]; exact X.col_mem_vals _ _
  exact decide_eq_decide.2 ⟨X.enc_inj hva (X.col_mem_vals _ _), fun h => by rw [h]; rfl⟩

section Valid

variable {P : Params} {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- **The rectangle item is valid** when every parent isomorphism of the branch maps `X` to `Y`
and `x₀` to `y₀` (Lemma A.28 with Lemma A.27 or A.30 for the oracle). -/
theorem rectItem_valid (O : RectOracle P S L) (ch : SojChoice) {X Y : PairCfg L.q} {x₀ y₀ : Fin L.q}
    {B : Set (Perm Ω)} (hX : X.Good deltaB) (hx : x₀ ∈ X.fiber)
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB)
    (hβ : 13 / 16 ≤ P.β) (hq : 16 ≤ L.q) (hlam : (S.N : ℝ) ^ P.α < L.q)
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G,
      (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • X = Y ∧ (L.π ⟨g, hg⟩ : Perm (Fin L.q)) x₀ = y₀) :
    (rectItem O ch X Y y₀ (X.idx hx) cert).Valid B := by
  classical
  have hi₀ := X.emb_idx hx
  have hW := rectW_eq X (X.idx hx) cert
  have hR := rectR_eq X (X.idx hx) cert
  rw [hi₀] at hW hR
  have hC : deltaB * (Fintype.card (Fin L.q) : ℝ) ≤ X.fiber.card := by
    rw [Fintype.card_fin]; exact hX.large
  obtain ⟨hdis, hdom, -, harea, hcap⟩ := cert_facts (β := P.β) X.coloring false (X.emb rfl) cert
    (by norm_num [etaB]) (by norm_num [etaB]) hC
    (max_le (by linarith) (by norm_num [etaB, deltaB]; linarith))
  rw [Fintype.card_fin] at harea hcap
  have h3 : 3 ≤ (rectW X (X.idx hx) cert).card := by
    have hq' : (16 : ℝ) ≤ L.q := by exact_mod_cast hq
    have h4 : (4 : ℝ) ≤ X.fiber.card := by
      have := hX.large; unfold deltaB at this; linarith
    have : (3 : ℝ) < (rectW X (X.idx hx) cert).card := by
      have := hdom; unfold etaB at this
      change (3 : ℝ) < (idealSide (X.emb rfl) X.coloring false (X.idx hx) cert.leftColor).card
      linarith
    exact_mod_cast this.le
  have hRne : (rectR X (X.idx hx) cert).Nonempty :=
    ⟨_, Finset.mem_map_of_mem _ ((mem_colorClass _ _ _ _ _).2 cert.rightPoint.property)⟩
  -- the target sides are the images of the source sides
  have himage : ∀ σ : Perm (Fin L.q), σ • X = Y → σ x₀ = y₀ →
      (Y.fiber.filter fun a => Y.col y₀ a = (certVals X (X.idx hx) cert).1) =
        (rectW X (X.idx hx) cert).map σ.toEmbedding ∧
      (Y.fiber.filter fun a => Y.col y₀ a = (certVals X (X.idx hx) cert).2.1) =
        (rectR X (X.idx hx) cert).map σ.toEmbedding := by
    rintro σ rfl rfl
    rw [hW, hR, filter_smul, filter_smul]
    exact ⟨rfl, rfl⟩
  unfold rectItem
  dsimp only
  split_ifs with hs
  · obtain ⟨haW, haR, -, hiff⟩ := (ch.align _ _ _ _ hs.2.2.2.1 hs.2.2.2.2 hs.1 hs.2.1 hs.2.2.1).2
    set a₀ := (ch.align _ _ _ _ hs.2.2.2.1 hs.2.2.2.2 hs.1 hs.2.1 hs.2.2.1).1
    set N : rectW X (X.idx hx) cert → rectR X (X.idx hx) cert → Bool :=
      fun w r => decide (Y.col ((a₀ : Perm (Fin L.q)) w) ((a₀ : Perm (Fin L.q)) r) =
        (certVals X (X.idx hx) cert).2.2) with hN
    obtain ⟨hlen, hcall, hsound, hcomp⟩ :=
      O.valid _ _ (rectM X (X.idx hx) cert) N a₀ hlam hdis h3 hRne
        (by simpa only [etaB, rectW, rectR] using harea)
    -- every parent isomorphism gives a permitted matrix transporter
    have htrans : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G,
        a₀⁻¹ * L.π ⟨g, hg⟩ ∈ leftOvercoset (rectM X (X.idx hx) cert) N := by
      intro g hg
      obtain ⟨hgG, hXY, hxy⟩ := hB g hg
      refine ⟨hgG, ?_⟩
      obtain ⟨hW', hR'⟩ := himage _ hXY hxy
      have hmem : a₀⁻¹ * L.π ⟨g, hgG⟩ ∈ permitted (rectW X (X.idx hx) cert)
          (rectR X (X.idx hx) cert) := by
        refine (hiff _).1 ⟨?_, ?_⟩
        · rw [hW', Finset.coe_map]; rfl
        · rw [hR', Finset.coe_map]; rfl
      refine mem_leftOvercoset (h := ⟨_, hmem⟩) fun a b => ?_
      have hmaps := maps_of_smul hXY
      have ha : a.val ∈ X.fiber := by
        exact (Finset.mem_filter.1 ((Finset.ext_iff.1 hW a.val).1 a.property)).1
      have hb : b.val ∈ X.fiber := by
        exact (Finset.mem_filter.1 ((Finset.ext_iff.1 hR b.val).1 b.property)).1
      rw [rectM_apply, hN]
      have e : ∀ z : Fin L.q, (a₀ : Perm (Fin L.q))
          (((a₀⁻¹ * L.π ⟨g, hgG⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) z) =
            (L.π ⟨g, hgG⟩ : Perm (Fin L.q)) z := by
        intro z
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, Perm.apply_inv_self]
      change decide (Y.col ((a₀ : Perm (Fin L.q)) (((a₀⁻¹ * L.π ⟨g, hgG⟩ :
        alternatingGroup (Fin L.q)) : Perm (Fin L.q)) a.val)) ((a₀ : Perm (Fin L.q))
          (((a₀⁻¹ * L.π ⟨g, hgG⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) b.val)) =
            (certVals X (X.idx hx) cert).2.2) = _
      rw [e, e, hmaps.2.1 _ ha _ hb]
    refine ⟨?_, hlen, hcall, fun Q hQ τ hτ g hg => ?_, fun ⟨g, hg⟩ => ?_⟩
    · exact hcap
    · obtain ⟨hgG, hσ⟩ := htrans g hg
      refine ⟨hgG, ?_⟩
      have := (leftOvercoset_coset (hsound Q hQ τ hτ) _).1 hσ
      simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using this
    · obtain ⟨hgG, h, hh, -⟩ := htrans g hg
      exact hcomp ⟨h, hh⟩
  · refine Set.eq_empty_iff_forall_notMem.2 fun g hg => hs ?_
    obtain ⟨hgG, hXY, hxy⟩ := hB g hg
    obtain ⟨hW', hR'⟩ := himage _ hXY hxy
    rw [hW', hR', Finset.card_map, Finset.card_map]
    exact ⟨rfl, rfl, h3, hdis, Finset.disjoint_map _ |>.2 hdis⟩

/-- **The item of one source--target choice is valid** (Lemma 5.1 and Lemma A.28): for a good
configuration `X` on at least `q/4` labels, a source vertex `x₀` in its fiber, `β ≥ 13/16`,
`βq ≥ 1` and `q ≥ 16`, if every parent isomorphism of the branch maps `X` to `Y` and `x₀` to
`y₀`, in the branch `q > λ`. The alternatives "no certificate" and "imprimitive without equal blocks" do not occur:
Lemma 5.1 (`primitive_entrance_alternative`) and the component lemma
(`nonprimitive_balanced_components`) rule them out. -/
theorem sojItem_valid (O : RectOracle P S L) (ch : SojChoice) {X Y : PairCfg L.q} {x₀ y₀ : Fin L.q}
    {B : Set (Perm Ω)} (hX : X.Good deltaB) (hx : x₀ ∈ X.fiber)
    (hβ : 13 / 16 ≤ P.β) (h1 : 1 ≤ P.β * L.q) (hq : 16 ≤ L.q) (hlam : (S.N : ℝ) ^ P.α < L.q)
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G,
      (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • X = Y ∧ (L.π ⟨g, hg⟩ : Perm (Fin L.q)) x₀ = y₀) :
    (sojItem O ch X Y x₀ y₀).Valid B := by
  classical
  have hδ : deltaB * L.q ≤ X.fiber.card := hX.large
  have hcoh := coloring_coherent hX
  have hhom := X.coloring_homogeneous false
  have hnon := coloring_nontrivial hX false
  have hi₀ := X.emb_idx hx
  unfold sojItem
  rw [dif_pos hx]
  split_ifs with hp hbal hcert himp
  · refine objItem_valid (fun g hg => ?_) ?_
    · obtain ⟨hgG, hXY, hxy⟩ := hB g hg
      exact ⟨hgG, by rw [balPart_smul, hXY, hxy]⟩
    · refine balPart_cap (δ := deltaB) (η := etaB) (fun v => ?_) hδ ?_ ?_ ?_ h1
      · by_cases hv : v ∈ X.vals
        · rw [← hi₀, filter_col_eq_map hv, Finset.card_map]
          exact hbal _
        · have e : X.fiber.filter (fun a => X.col x₀ a = v) = ∅ := by
            refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
            obtain ⟨ha, hav⟩ := Finset.mem_filter.1 ha
            exact hv (hav ▸ vals_of_mem hx ha)
          rw [e, Finset.card_empty, Nat.cast_zero]
          exact mul_nonneg (by norm_num [etaB]) (Nat.cast_nonneg _)
      · norm_num [etaB]; linarith
      · norm_num [deltaB]; linarith
      · norm_num [etaB]
  · exact rectItem_valid O ch hX hx _ hβ hq hlam hB
  · exfalso
    rcases primitive_entrance_alternative X.coloring hcoh false hhom hnon hp (X.idx hx) etaB
      (by norm_num [etaB]) with h | h
    · exact hbal fun i => by simpa only [colorClass_card] using h i
    · exact hcert h
  · refine objItem_valid (fun g hg => ?_) ?_
    · obtain ⟨hgG, hXY, -⟩ := hB g hg
      exact ⟨hgG, by rw [impPart_smul, hXY]⟩
    · refine impPart_cap (δ := deltaB) (fun a ha => ?_) hδ (by linarith)
        (by norm_num [deltaB]; linarith) h1
      obtain ⟨i, rfl⟩ := X.exists_emb rfl ha
      rw [comp_emb (X.col_mem_vals _ _) false i, Finset.card_map]
      exact (ch.imp X himp).2.2 i
  · exfalso
    obtain ⟨a, b, hab, -, hsz⟩ := nonprimitive_balanced_components X.coloring hcoh false hhom hp
    exact himp ⟨a, b, hab, hsz⟩

end Valid

end GI.Algorithm
