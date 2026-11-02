import Workspace.Algorithm.SingleFactor
import Workspace.Algorithm.LabelData
import Workspace.Algorithm.CarrierKeep

/-!
# The labels of the single-factor normalization carry their constituent data

The normalization of a single alternating factor (`PrimitiveQuotient.normalization`,
`Workspace/Algorithm/SingleFactor.lean`) gives the labels of the giant step: the normalized group
`G'` maps onto `Alt(m)`, where the primitive quotient acts on the `k`-subsets of `[m]`. This file
proves that these labels carry the data that the paper attaches to them
(`GiantLabels.Constituent`, `Workspace/Algorithm/LabelData.lean`):

* **they are read on the domain** (`GiantLabels.OnDomain`). An element of `G'` that fixes every
  point of the domain fixes every block, because every block meets the domain
  (`PrimitiveQuotient.onto`); so its action on the blocks is trivial, and so is its permutation
  of `[m]`.
* **the Johnson block map of the Cameron constituent** (`JohnsonBlocks`; Lemma A.11: "Assume its
  actual equivariant block map is `p : Ω → binom(Γ, h)`, `1 ≤ h ≤ q/2`"). A position `v` lies in
  a block, the block is a `k`-subset of `[m]`, and `p(v)` is that subset when `2k ≤ m` and its
  complement otherwise (the Johnson scheme `J(m,k)` is `J(m,m-k)`). The map is equivariant
  because `G'` acts on the `k`-subsets through its permutation of `[m]`. The fiber of `p` over a
  set is one block, and all blocks have the same size because the parent group is transitive on
  the domain and permutes the blocks.

* **they lie above the retained columns** (`GiantLabels.Constituent.kills`), and the normalized
  group keeps the carrier of the retained rows (`NormAbove.keeps`), when the blocks lie above the
  retained columns (`PrimitiveQuotient.KillsCols`, true of the exposed quotient,
  `State.expose_killsCols`): an element that fixes every column fixes every block.

`PrimitiveQuotient.normAbove` is the normalization with this data and with its degree above `q₀`
(`NormAbove`), given its degree. No cited result is used.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

namespace PrimitiveQuotient

variable {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S)

/-- An element of `G` that fixes every point of the domain acts trivially on the blocks: every
block meets the domain. -/
theorem ρ_eq_one_of_fix (g : S.G) (hg : ∀ v ∈ S.dom, (g : Perm Ω) v = v) : Q.ρ g = 1 := by
  ext i
  obtain ⟨v, hv, rfl⟩ := Q.onto i
  rw [← Q.equivariant g v hv, hg v hv]
  rfl

/-- **All blocks have the same number of domain points** when `G` is transitive on the domain:
an element of `G` that moves a point of block `i` to a point of block `j` maps block `i` onto
block `j`. -/
theorem card_block_eq (htr : S.Transitive) (i j : Fin Q.d) :
    Nat.card {v : S.dom // Q.blk v.1 = i} = Nat.card {v : S.dom // Q.blk v.1 = j} := by
  obtain ⟨v, hv, rfl⟩ := Q.onto i
  obtain ⟨w, hw, rfl⟩ := Q.onto j
  obtain ⟨g, hg, hgv⟩ := htr v hv w hw
  have hρ : Q.ρ ⟨g, hg⟩ (Q.blk v) = Q.blk w := by rw [← Q.equivariant ⟨g, hg⟩ v hv, hgv]
  have hinv := S.dom_inv g hg
  refine Nat.card_congr
    { toFun := fun u => ⟨⟨g u.1.1, (hinv u.1.1).2 u.1.2⟩, ?_⟩
      invFun := fun u => ⟨⟨g⁻¹ u.1.1, (hinv (g⁻¹ u.1.1)).1 (by simp)⟩, ?_⟩
      left_inv := fun u => by ext; simp
      right_inv := fun u => by ext; simp }
  · show Q.blk (((⟨g, hg⟩ : S.G) : Perm Ω) u.1.1) = Q.blk w
    rw [Q.equivariant ⟨g, hg⟩ _ u.1.2, u.2, hρ]
  · have hu : (g⁻¹ u.1.1) ∈ S.dom := (hinv (g⁻¹ u.1.1)).1 (by simp)
    have e1 := Q.equivariant ⟨g, hg⟩ (g⁻¹ u.1.1) hu
    have e2 : ((⟨g, hg⟩ : S.G) : Perm Ω) (g⁻¹ u.1.1) = u.1.1 := by simp
    have hu2 : Q.blk u.1.1 = Q.blk w := u.2
    rw [e2, hu2] at e1
    exact (Q.ρ ⟨g, hg⟩).injective (e1.symm.trans hρ.symm)

section OneCoordinate

variable {m k : ℕ} (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)

/-- The `k`-subset of `[m]` of the block of a position. -/
def kset (v : Ω) : Finset (Fin m) := (e (Q.blk v) 0).1

theorem card_kset (v : Ω) : (Q.kset e v).card = k := (e (Q.blk v) 0).2

include hS in
/-- `G` acts on the `k`-subsets through its permutation of `[m]`. -/
theorem kset_equivariant (g : S.G) {v : Ω} (hv : v ∈ S.dom) :
    Q.kset e ((g : Perm Ω) v) =
      (Q.kset e v).map (Q.permOf e hS (Q.ρ.rangeRestrict g)).toEmbedding := by
  have h := Q.permOf_spec e hS (Q.ρ.rangeRestrict g) (Q.blk v)
  unfold kset
  rw [Q.equivariant g v hv]
  exact congrArg Subtype.val (congrFun h 0)

/-- A position has the `k`-set `A` exactly when its block is `e⁻¹(A)`. -/
theorem kset_eq_iff (v : Ω) (A : Product.KSet m k) :
    Q.kset e v = A.1 ↔ Q.blk v = e.symm fun _ => A := by
  rw [Equiv.eq_symm_apply]
  constructor
  · intro h
    funext i
    rw [Subsingleton.elim i 0]
    exact Subtype.ext h
  · intro h
    unfold kset
    rw [h]

include e in
/-- `0 < k < m`: there are at least two blocks. -/
theorem k_bounds : 0 < k ∧ k < m := by
  have hb := Q.two_le_choose e
  have hk0 : k ≠ 0 := by rintro rfl; simp at hb
  refine ⟨Nat.pos_of_ne_zero hk0, ?_⟩
  by_contra hkm
  rcases Nat.lt_or_ge m k with hlt | hge
  · rw [Nat.choose_eq_zero_of_lt hlt] at hb; omega
  · have : k = m := by omega
    subst this
    simp at hb

/-! #### The block map, up to the complement -/

/-- The block map is the `k`-set or its complement: `c` is the identity or the complement. -/
structure Flip (m k h : ℕ) where
  c : Finset (Fin m) → Finset (Fin m)
  invol : ∀ A, c (c A) = A
  map : ∀ (σ : Perm (Fin m)) A, c (A.map σ.toEmbedding) = (c A).map σ.toEmbedding
  card : ∀ A, A.card = k → (c A).card = h
  card' : ∀ A, A.card = h → (c A).card = k

/-- The identity, with `h = k`. -/
def Flip.id (m k : ℕ) : Flip m k k :=
  ⟨fun A => A, fun _ => rfl, fun _ _ => rfl, fun _ h => h, fun _ h => h⟩

theorem compl_map {m : ℕ} (σ : Perm (Fin m)) (A : Finset (Fin m)) :
    (A.map σ.toEmbedding)ᶜ = (Aᶜ).map σ.toEmbedding := by
  ext b
  simp [Finset.mem_map_equiv]

/-- The complement, with `h = m - k`. -/
def Flip.compl {m k : ℕ} (hkm : k ≤ m) : Flip m k (m - k) where
  c A := Aᶜ
  invol A := compl_compl A
  map σ A := compl_map σ A
  card A h := by rw [Finset.card_compl, Fintype.card_fin, h]
  card' A h := by
    rw [Finset.card_compl, Fintype.card_fin, h]
    omega

/-- **The permutation of `[m]` determines the element of `ρ(G)`**: the action on `k`-subsets
is the action on the blocks. -/
theorem permHom_eq_one {x : Q.ρ.range} (h : Q.permHom e hS x = 1) : x = 1 := by
  have hx := Q.permOf_spec e hS x
  change Q.permOf e hS x = 1 at h
  rw [h] at hx
  apply Subtype.ext
  ext y
  have h1 := (hx y).trans (Product.isProd_one e y).symm
  exact congrArg Fin.val (by simpa using e.injective h1)

/-- **The labels of the normalization are the action on the blocks**: an element of `G'` has
trivial label image exactly when it keeps every block of every point of the domain. -/
theorem normPi_eq_one_iff (g : Q.normGroup e hS) :
    Q.normPi e hS g = 1 ↔ ∀ w ∈ S.dom, Q.blk ((g : Perm Ω) w) = Q.blk w := by
  have key : Q.normPi e hS g = 1 ↔ Q.ρ ⟨g.1, Q.normGroup_le e hS g.2⟩ = 1 := by
    constructor
    · intro h1
      have h2 : Q.permHom e hS (Q.ρ.rangeRestrict ⟨g.1, Q.normGroup_le e hS g.2⟩) = 1 :=
        congrArg Subtype.val h1
      exact congrArg Subtype.val (Q.permHom_eq_one e hS h2)
    · intro h1
      have h2 : Q.ρ.rangeRestrict ⟨g.1, Q.normGroup_le e hS g.2⟩ = 1 := Subtype.ext h1
      apply Subtype.ext
      show Q.permHom e hS (Q.ρ.rangeRestrict ⟨g.1, Q.normGroup_le e hS g.2⟩) = 1
      rw [h2, map_one]
  rw [key]
  constructor
  · intro h1 w hw
    rw [Q.equivariant ⟨g.1, Q.normGroup_le e hS g.2⟩ w hw, h1]
    rfl
  · intro h1
    ext i
    obtain ⟨v, hv, rfl⟩ := Q.onto i
    rw [← Q.equivariant ⟨g.1, Q.normGroup_le e hS g.2⟩ v hv]
    exact congrArg Fin.val (h1 v hv)

variable [Finite Ω]

/-- **The Johnson block map of the normalized labels**, on any child state with group `G'` and
the parent domain. -/
noncomputable def johnsonBlocks (htr : S.Transitive) {h : ℕ} (F : Flip m k h) (h1 : 1 ≤ h)
    (h2 : 2 * h ≤ m) (x y : Ω → C) (hier : List (Interval Ω)) :
    JohnsonBlocks (S.restrict (Q.normGroup e hS) (Q.normGroup_le e hS) x y hier)
      ⟨m, Q.normPi e hS, Q.normPi_surjective e hS⟩ where
  h := h
  f := Nat.card {v : S.dom // Q.blk v.1 = ⟨0, by have := Q.two_le; omega⟩}
  p v := F.c (Q.kset e v.1)
  equivariant g v := by
    show F.c (Q.kset e ((g : Perm Ω) v.1)) = _
    rw [Q.kset_equivariant e hS ⟨g.1, Q.normGroup_le e hS g.2⟩ v.2, F.map]
    rfl
  card v := F.card _ (Q.card_kset e v.1)
  fibers Bl hBl := by
    let A : Product.KSet m k := ⟨F.c Bl, F.card' Bl hBl⟩
    have hfib : ∀ v : S.dom, F.c (Q.kset e v.1) = Bl ↔ Q.blk v.1 = e.symm fun _ => A := by
      intro v
      rw [← Q.kset_eq_iff e v.1 A]
      constructor
      · intro hv; show Q.kset e v.1 = F.c Bl; rw [← hv, F.invol]
      · intro hv; rw [show Q.kset e v.1 = F.c Bl from hv, F.invol]
    have : Nat.card {v : (S.restrict (Q.normGroup e hS) (Q.normGroup_le e hS) x y hier).dom //
        F.c (Q.kset e v.1) = Bl} = Nat.card {v : S.dom // Q.blk v.1 = e.symm fun _ => A} :=
      Nat.card_congr (Equiv.subtypeEquivRight hfib)
    exact this.trans (Q.card_block_eq htr _ _)
  one_le := h1
  half := h2

omit [Finite Ω] in
/-- **The labels of the normalized group are read on the domain.** -/
theorem normPi_onDomain (x y : Ω → C) (hier : List (Interval Ω)) :
    (⟨m, Q.normPi e hS, Q.normPi_surjective e hS⟩ :
      GiantLabels (S.restrict (Q.normGroup e hS) (Q.normGroup_le e hS) x y hier)).OnDomain := by
  intro g hg
  have hfix : ∀ v ∈ S.dom, (g : Perm Ω) v = v := fun v hv => by
    have := congrArg Subtype.val (Equiv.Perm.ext_iff.1 hg ⟨v, hv⟩)
    simpa using this
  have hρ := Q.ρ_eq_one_of_fix ⟨g.1, Q.normGroup_le e hS g.2⟩ hfix
  apply Subtype.ext
  show Q.permHom e hS (Q.ρ.rangeRestrict ⟨g.1, Q.normGroup_le e hS g.2⟩) = 1
  have : Q.ρ.rangeRestrict ⟨g.1, Q.normGroup_le e hS g.2⟩ = 1 := Subtype.ext hρ
  rw [this, map_one]

omit [Finite Ω] in
/-- **The labels of the normalized group lie above the retained columns**, when the blocks
do: an element that fixes every retained column fixes every block. -/
theorem normPi_kills (hkc : Q.KillsCols) (x y : Ω → C) (hier : List (Interval Ω)) :
    ∀ R c, (S.restrict (Q.normGroup e hS) (Q.normGroup_le e hS) x y hier).rows = some R →
      R.cols = some c →
      ∀ g : (S.restrict (Q.normGroup e hS) (Q.normGroup_le e hS) x y hier).G,
        FixesCols c S.dom g → Q.normPi e hS g = 1 := by
  intro R c hR hc g hg
  have hρ := hkc R c (State.restrict_rows_eq _ _ _ _ _ _ hR) hc ⟨g.1, Q.normGroup_le e hS g.2⟩ hg
  apply Subtype.ext
  show Q.permHom e hS (Q.ρ.rangeRestrict ⟨g.1, Q.normGroup_le e hS g.2⟩) = 1
  have : Q.ρ.rangeRestrict ⟨g.1, Q.normGroup_le e hS g.2⟩ = 1 := Subtype.ext hρ
  rw [this, map_one]

omit [Finite Ω] in
/-- **The normalized group keeps the carrier**: it contains every element that fixes every
retained column, since such an element fixes every block (Section A.4: "use full preimages of
all quotient restrictions. This keeps the entire kernel `J`"). -/
theorem normGroup_keeps (hkc : Q.KillsCols) (hkl : Q.KeepsLevels) :
    CarrierOK (Q.normGroup e hS) S.dom S.rows (Q.pre ++ Q.top :: Q.post) :=
  S.carrier.mono (Q.normGroup_le e hS) (fun R c hR hc g hg hf => by
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    have hρ : Q.ρ.rangeRestrict ⟨g, hg⟩ = 1 := Subtype.ext (hkc R c hR hc ⟨g, hg⟩ hf)
    change Perm.sign ((Q.permHom e hS) (Q.ρ.rangeRestrict ⟨g, hg⟩)) = 1
    rw [hρ, map_one, map_one]) hkl

/-- **The constituent data of the normalized labels** on any child state. -/
noncomputable def constituent (htr : S.Transitive) (hkc : Q.KillsCols) (x y : Ω → C)
    (hier : List (Interval Ω)) :
    (⟨m, Q.normPi e hS, Q.normPi_surjective e hS⟩ :
      GiantLabels (S.restrict (Q.normGroup e hS) (Q.normGroup_le e hS) x y hier)).Constituent :=
  have hk := Q.k_bounds e
  { onDomain := Q.normPi_onDomain e hS x y hier
    blocks :=
      if h2 : 2 * k ≤ m then Q.johnsonBlocks e hS htr (Flip.id m k) hk.1 h2 x y hier
      else Q.johnsonBlocks e hS htr (Flip.compl hk.2.le) (by omega) (by omega) x y hier
    kills := Q.normPi_kills e hS hkc x y hier }

end OneCoordinate

/-- **The single-factor normalization of a choice with its constituent data**: the
normalization of a single factor, its degree above `q₀`, and on every child state the labels
read on the domain with the Johnson block map of the Cameron constituent. -/
noncomputable def normAboveOf [Finite Ω] {P : Params} (c : Q.NormChoice) (htr : S.Transitive)
    (hq : P.q₀ < (Q.normalizationOf c).q) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels) :
    NormAbove P S where
  I := Q.normalizationOf c
  q_large := hq
  con x y hier := Q.constituent c.e c.hS htr hkc x y hier
  tower := Q.tower.mono (Q.normalizationOf c).le subset_rfl
  sel := ⟨Q.pre.length, by simp [normalizationOf]⟩
  sel_univ v hv w hw := by
    show ((Q.pre ++ Q.top :: Q.post)[Q.pre.length]'(by simp)).part.r v w
    rw [List.getElem_of_append rfl rfl]
    exact Q.top_univ v hv w hw
  sel_ker g := by
    have hpre : (Q.pre ++ Q.top :: Q.post).take Q.pre.length = Q.pre := by simp
    show (Q.normalizationOf c).π g = 1 ↔ ∀ w ∈ S.dom,
      (fineEnd ⊥ ((Q.pre ++ Q.top :: Q.post).take Q.pre.length)).r ((g : Perm Ω) w) w
    rw [hpre]
    refine (Q.normPi_eq_one_iff c.e c.hS g).trans ?_
    refine forall₂_congr fun w hw => ?_
    have hgw : (g : Perm Ω) w ∈ S.dom := (S.dom_inv g ((Q.normalizationOf c).le g.2) w).2 hw
    exact (Q.fine_eq _ hgw w hw).symm
  keeps := Q.normGroup_keeps c.e c.hS hkc hkl

/-- The single-factor normalization with its constituent data, for the default choice. -/
noncomputable def normAbove [Finite Ω] {P : Params} (h : Q.SingleFactor) (htr : S.Transitive)
    (hq : P.q₀ < (Q.normalization h).q) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels) :
    NormAbove P S :=
  Q.normAboveOf (Q.defaultChoice h) htr hq hkc hkl

end PrimitiveQuotient

end GI.Algorithm
