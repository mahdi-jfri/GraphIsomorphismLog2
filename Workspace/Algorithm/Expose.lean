import Workspace.Algorithm.Dispatch

/-!
# Exposing the primitive quotient

Algorithm 5, `Continue`: "Expose the next primitive quotient above any retained column
partition". Section A.5, "Selection of the quotient and its cap": "Ordinary Cameron dispatch
uses the coarsest available primitive quotient of the whole current group". Section 3.3: "The
old hierarchy is retained; new invariant partitions only refine it."

On a transitive state whose hierarchy satisfies the invariant `HierInv`
(`Workspace/Algorithm/HierInv.lean`), with at least two positions, this file builds a
`PrimitiveQuotient` (`exists_primitiveQuotient`, `State.expose`):

1. Find the interval `J` of the stored hierarchy whose fine end `f` splits the domain and whose
   coarse end holds it (`exists_split`). The intervals above `J` are trivial on the domain.
2. Choose a coarsest `G`-invariant partition `M` of the domain that is coarser than `f` and
   does not hold the whole domain (`exists_maxCand_of`). If some such partition is coarser than
   the retained column partition (`State.retainedCols`), choose `M` among those. The action of
   `G` on the classes of `M` is primitive (`State.blockPrimitive`): a nontrivial block would
   give a coarser candidate, which is still above the columns. So when the column partition
   splits the domain and is comparable with the stored levels, the exposed blocks are unions of
   columns (`State.expose_aboveCols`).
3. Split `J` at `M`: the interval `mid` from `f` to `M`, with ratio the number `c₁` of
   `f`-classes in one `M`-class, and the interval `top` from `M` to the domain, with ratio the
   number `d` of `M`-classes. Both inherit the bound of `J`, clamped by their new ratios
   (Section 3.3: "When an interval of new ratio `d'` inherits a bound `c`, we store
   `min{c, d'}`").

The new ratios are exact on the domain, and `c₁ d` is the number of `f`-classes on the domain
(`classCount_mul`), which is at most the stored ratio of `J`. So `ρ` and `Q` do not increase
(Section 7.1: "Splitting a ratio into at least two nontrivial factors decreases `ρ`. … Splitting
or restricting intervals also cannot increase `Q`"), and the exposed hierarchy satisfies the
invariant.

No cited result is used.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm
open scoped Pointwise

variable {Ω : Type}

/-- `f` holds all of `D` in one class. -/
def UnivOn (D : Set Ω) (f : Setoid Ω) : Prop := ∀ v ∈ D, ∀ w ∈ D, f.r v w

/-! ### The interval to split -/

/-- On a transitive domain that `f` splits, some interval of a hierarchy with the top condition
has a fine end that splits the domain and a coarse end that holds it. -/
theorem exists_split {G : Subgroup (Perm Ω)} {D : Set Ω}
    (htr : ∀ v ∈ D, ∀ w ∈ D, w ∈ orb G v) :
    ∀ (f : Setoid Ω) (l : List (Interval Ω)), TopOn G D (fineEnd f l) → ¬ UnivOn D f →
      ∃ pre J post, l = pre ++ J :: post ∧ ¬ UnivOn D (fineEnd f pre) ∧ UnivOn D J.part
  | _, [], htop, hf => absurd (fun v hv w hw => htop v hv w hw (htr v hv w hw)) hf
  | f, I :: l, htop, hf => by
    by_cases hI : UnivOn D I.part
    · exact ⟨[], I, l, rfl, hf, hI⟩
    · obtain ⟨pre, J, post, rfl, h1, h2⟩ := exists_split htr I.part l htop hI
      exact ⟨I :: pre, J, post, rfl, h1, h2⟩

/-! ### A coarsest invariant partition above `f` -/

/-- A candidate for the primitive quotient above `f`: a `G`-invariant partition of `D`, coarser
than `f`, that does not hold all of `D`. -/
structure IsCand (G : Subgroup (Perm Ω)) (D : Set Ω) (f M : Setoid Ω) : Prop where
  inv : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, M.r (g v) (g w) ↔ M.r v w
  le : ∀ v ∈ D, ∀ w ∈ D, f.r v w → M.r v w
  proper : ¬ UnivOn D M

/-- The number of related pairs of points of `D`. A coarser partition relates more pairs. -/
noncomputable def pairCount (D : Set Ω) (M : Setoid Ω) : ℕ :=
  Set.ncard {p : Ω × Ω | p.1 ∈ D ∧ p.2 ∈ D ∧ M.r p.1 p.2}

theorem finite_setoid [Finite Ω] : Finite (Setoid Ω) :=
  Finite.of_injective (fun s : Setoid Ω => s.r) fun s t h => by
    obtain ⟨r, hr⟩ := s
    obtain ⟨r', hr'⟩ := t
    simp only at h
    subst h
    rfl

/-- **A coarsest candidate exists** among those with a property `p` that coarser partitions
keep: one with the most related pairs. -/
theorem exists_maxCand_of [Finite Ω] {G : Subgroup (Perm Ω)} {D : Set Ω} {f M₀ : Setoid Ω}
    (p : Setoid Ω → Prop) (h₀ : IsCand G D f M₀) (hp₀ : p M₀) :
    ∃ M, IsCand G D f M ∧ p M ∧
      ∀ M', IsCand G D f M' → p M' → pairCount D M' ≤ pairCount D M := by
  haveI := finite_setoid (Ω := Ω)
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image {M | IsCand G D f M ∧ p M} (pairCount D)
    (Set.toFinite _) ⟨M₀, h₀, hp₀⟩
  exact ⟨M, hM.1, hM.2, fun M' h1 h2 => hmax M' ⟨h1, h2⟩⟩

/-- **A coarsest candidate exists**: one with the most related pairs. -/
theorem exists_maxCand [Finite Ω] {G : Subgroup (Perm Ω)} {D : Set Ω} {f : Setoid Ω}
    (hf : IsCand G D f f) :
    ∃ M, IsCand G D f M ∧ ∀ M', IsCand G D f M' → pairCount D M' ≤ pairCount D M := by
  haveI := finite_setoid (Ω := Ω)
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image {M | IsCand G D f M} (pairCount D)
    (Set.toFinite _) ⟨f, hf⟩
  exact ⟨M, hM, fun M' hM' => hmax M' hM'⟩

/-! ### Counting classes in a transitive action -/

/-- On a transitive domain, every coarse class of an invariant partition contains the same
number of classes of an invariant fine partition. -/
theorem classCount_classIn_eq [Finite Ω] {G : Subgroup (Perm Ω)} {D : Set Ω}
    (hD : Invariant G D) (htr : ∀ v ∈ D, ∀ w ∈ D, ∃ g ∈ G, g v = w) {f M : Setoid Ω}
    (hf : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, f.r (g v) (g w) ↔ f.r v w)
    (hM : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, M.r (g v) (g w) ↔ M.r v w) {a b : Ω} (ha : a ∈ D)
    (hb : b ∈ D) : classCount f (classIn G D M b) = classCount f (classIn G D M a) := by
  obtain ⟨g, hg, rfl⟩ := htr a ha b hb
  have himg : g '' classIn G D M a = classIn G D M (g a) := by
    ext y
    constructor
    · rintro ⟨w, ⟨hw, -, hMw⟩, rfl⟩
      have hgw := (hD g hg w).2 hw
      obtain ⟨k, hk, hkw⟩ := htr (g a) hb (g w) hgw
      exact ⟨hgw, ⟨k, hk, hkw⟩, (hM g hg a ha w hw).2 hMw⟩
    · rintro ⟨hy, -, hMy⟩
      have hy' := hD.inv_mem hg hy
      obtain ⟨k, hk, hkw⟩ := htr a ha (g⁻¹ y) hy'
      refine ⟨g⁻¹ y, ⟨hy', ⟨k, hk, hkw⟩, ?_⟩, by simp⟩
      exact (hM g hg a ha (g⁻¹ y) hy').1 (by simpa using hMy)
  rw [← himg, classCount_image]
  intro v hv w hw
  exact hf g hg v hv.1 w hw.1

/-- **The classes multiply** (Section 3.3: "In a transitive action all blocks have the same
size … `d_1 ⋯ d_t = s`"): on a transitive domain, for invariant partitions `f ≤ M`, the number
of `f`-classes is the number of `M`-classes times the number of `f`-classes in one `M`-class. -/
theorem classCount_mul [Finite Ω] {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D)
    (htr : ∀ v ∈ D, ∀ w ∈ D, ∃ g ∈ G, g v = w) {f M : Setoid Ω}
    (hf : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, f.r (g v) (g w) ↔ f.r v w)
    (hM : ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, M.r (g v) (g w) ↔ M.r v w)
    (hle : ∀ v ∈ D, ∀ w ∈ D, f.r v w → M.r v w) {a : Ω} (ha : a ∈ D) :
    classCount f D = classCount M D * classCount f (classIn G D M a) := by
  classical
  let π : Quotient (Setoid.comap (Subtype.val : D → Ω) f) →
      Quotient (Setoid.comap (Subtype.val : D → Ω) M) :=
    Quotient.map id fun v w h => hle v.1 v.2 w.1 w.2 h
  haveI : Fintype (Quotient (Setoid.comap (Subtype.val : D → Ω) M)) := Fintype.ofFinite _
  have hfib : ∀ b, Nat.card {x // π x = b} = classCount f (classIn G D M a) := by
    intro b
    induction b using Quotient.inductionOn with
    | h v =>
    rw [← classCount_classIn_eq hD htr hf hM ha v.2]
    unfold classCount
    symm
    refine Nat.card_eq_of_bijective (fun q => ⟨Quotient.map (fun w => ⟨w.1, w.2.1⟩)
      (fun _ _ h => h) q, ?_⟩) ⟨?_, ?_⟩
    · induction q using Quotient.inductionOn with
      | h w =>
      exact Quotient.sound (M.symm w.2.2.2)
    · intro q₁ q₂ h
      induction q₁ using Quotient.inductionOn
      induction q₂ using Quotient.inductionOn
      have h' := congrArg Subtype.val h
      simp only [Quotient.map_mk] at h'
      have hr := Quotient.exact h'
      exact Quotient.sound hr
    · rintro ⟨x, hx⟩
      induction x using Quotient.inductionOn with
      | h w =>
      have hr : (Setoid.comap (Subtype.val : D → Ω) M).r w v := Quotient.exact hx
      refine ⟨Quotient.mk _ ⟨w.1, w.2, (htr v.1 v.2 w.1 w.2), M.symm hr⟩, ?_⟩
      rfl
  unfold classCount
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv π).symm, Nat.card_sigma]
  rw [Finset.sum_congr rfl (fun b _ => hfib b), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card]
  rfl

/-! ### The block action of a state -/

section Blocks

variable {C : Type} (S : State Ω C) (M : Setoid Ω)
  (hM : ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom, M.r (g v) (g w) ↔ M.r v w)

/-- The classes of `M` on the domain. -/
abbrev BlockT : Type := Quotient (Setoid.comap (Subtype.val : S.dom → Ω) M)

/-- `g` moves the classes of `M` on the domain. -/
def blockAct (g : Perm Ω) (hg : g ∈ S.G) : BlockT S M → BlockT S M :=
  Quotient.map (fun v : S.dom => (⟨g v.1, (S.dom_inv g hg v.1).2 v.2⟩ : S.dom))
    (fun v w h => (hM g hg v.1 v.2 w.1 w.2).2 h)

theorem blockAct_mk (g : Perm Ω) (hg : g ∈ S.G) (v : S.dom) :
    blockAct S M hM g hg (Quotient.mk _ v) =
      Quotient.mk _ ⟨g v.1, (S.dom_inv g hg v.1).2 v.2⟩ := rfl

/-- The action of `G` on the classes of `M`. -/
def stateBlockHom : S.G →* Perm (BlockT S M) where
  toFun g :=
    { toFun := blockAct S M hM g.1 g.2
      invFun := blockAct S M hM g.1⁻¹ (S.G.inv_mem g.2)
      left_inv := fun q => by
        induction q using Quotient.inductionOn with
        | h v =>
        rw [blockAct_mk, blockAct_mk]
        exact congrArg _ (Subtype.ext (by simp))
      right_inv := fun q => by
        induction q using Quotient.inductionOn with
        | h v =>
        rw [blockAct_mk, blockAct_mk]
        exact congrArg _ (Subtype.ext (by simp)) }
  map_one' := by
    ext q
    induction q using Quotient.inductionOn with
    | h v =>
    exact congrArg _ (Subtype.ext rfl)
  map_mul' g k := by
    ext q
    induction q using Quotient.inductionOn with
    | h v =>
    exact congrArg _ (Subtype.ext rfl)

theorem stateBlockHom_mk (g : S.G) (v : S.dom) :
    stateBlockHom S M hM g (Quotient.mk _ v) = Quotient.mk _ ⟨g.1 v.1, (S.dom_inv g.1 g.2 v.1).2 v.2⟩ :=
  rfl

variable [Finite Ω]

/-- The number of classes of `M` on the domain. -/
noncomputable abbrev blockNum : ℕ := Nat.card (BlockT S M)

/-- The classes of `M`, numbered. -/
noncomputable def blockEquiv : BlockT S M ≃ Fin (blockNum S M) := Finite.equivFin _

/-- The block action on `Fin d`. -/
noncomputable def blockRho : S.G →* Perm (Fin (blockNum S M)) :=
  (blockEquiv S M).permCongrHom.toMonoidHom.comp (stateBlockHom S M hM)

open Classical in
/-- The block map: a point of the domain goes to the number of its class. -/
noncomputable def blockMap (hd : 0 < blockNum S M) (v : Ω) : Fin (blockNum S M) :=
  if hv : v ∈ S.dom then blockEquiv S M (Quotient.mk _ ⟨v, hv⟩) else ⟨0, hd⟩

theorem blockMap_of_mem (hd : 0 < blockNum S M) {v : Ω} (hv : v ∈ S.dom) :
    blockMap S M hd v = blockEquiv S M (Quotient.mk _ ⟨v, hv⟩) := by
  unfold blockMap
  exact dif_pos hv

theorem blockMap_eq_iff (hd : 0 < blockNum S M) {v w : Ω} (hv : v ∈ S.dom) (hw : w ∈ S.dom) :
    blockMap S M hd v = blockMap S M hd w ↔ M.r v w := by
  rw [blockMap_of_mem S M hd hv, blockMap_of_mem S M hd hw, (blockEquiv S M).apply_eq_iff_eq]
  exact Quotient.eq

theorem blockMap_equivariant (hd : 0 < blockNum S M) (g : S.G) {v : Ω} (hv : v ∈ S.dom) :
    blockMap S M hd ((g : Perm Ω) v) = blockRho S M hM g (blockMap S M hd v) := by
  rw [blockMap_of_mem S M hd hv, blockMap_of_mem S M hd ((S.dom_inv g.1 g.2 v).2 hv)]
  show _ = blockEquiv S M (stateBlockHom S M hM g ((blockEquiv S M).symm (blockEquiv S M _)))
  rw [Equiv.symm_apply_apply]
  rfl

theorem blockMap_onto (hd : 0 < blockNum S M) (i : Fin (blockNum S M)) :
    ∃ v ∈ S.dom, blockMap S M hd v = i := by
  obtain ⟨⟨v, hv⟩, hq⟩ := Quotient.mk_surjective ((blockEquiv S M).symm i)
  refine ⟨v, hv, ?_⟩
  rw [blockMap_of_mem S M hd hv, hq, Equiv.apply_symm_apply]

/-- The block action is transitive on the blocks. -/
theorem blockRho_transitive (hd : 0 < blockNum S M) (htr : S.Transitive) (i j : Fin (blockNum S M)) :
    ∃ g : (blockRho S M hM).range, g • i = j := by
  obtain ⟨v, hv, rfl⟩ := blockMap_onto S M hd i
  obtain ⟨w, hw, rfl⟩ := blockMap_onto S M hd j
  obtain ⟨g, hg, rfl⟩ := htr v hv w hw
  refine ⟨⟨blockRho S M hM ⟨g, hg⟩, ⟨g, hg⟩, rfl⟩, ?_⟩
  exact (blockMap_equivariant S M hM hd ⟨g, hg⟩ hv).symm

/-- **The block action of a coarsest candidate is primitive.** A block `B` with two points and
a point outside would give the invariant partition "the blocks lie in one translate of `B`",
which is coarser than `M`, still a candidate, and relates more pairs. -/
theorem blockPrimitive (hd : 0 < blockNum S M) (htr : S.Transitive) {f : Setoid Ω}
    (hMc : IsCand S.G S.dom f M)
    (hmax : ∀ M', IsCand S.G S.dom f M' → (∀ v ∈ S.dom, ∀ w ∈ S.dom, M.r v w → M'.r v w) →
      pairCount S.dom M' ≤ pairCount S.dom M) :
    MulAction.IsPreprimitive (blockRho S M hM).range (Fin (blockNum S M)) := by
  classical
  set ρ := blockRho S M hM
  set blk := blockMap S M hd
  have hpt : MulAction.IsPretransitive ρ.range (Fin (blockNum S M)) :=
    ⟨blockRho_transitive S M hM hd htr⟩
  refine { toIsPretransitive := hpt, isTrivialBlock_of_isBlock := ?_ }
  intro B hB
  by_contra hnt
  simp only [MulAction.IsTrivialBlock, not_or] at hnt
  obtain ⟨hns, hnu⟩ := hnt
  obtain ⟨b₁, hb₁, b₂, hb₂, hb12⟩ := Set.not_subsingleton_iff.1 hns
  obtain ⟨c, hc⟩ := (Set.ne_univ_iff_exists_notMem B).1 hnu
  -- The relation "in one translate of `B`".
  let R : Fin (blockNum S M) → Fin (blockNum S M) → Prop := fun i j =>
    ∃ y : ρ.range, i ∈ y • B ∧ j ∈ y • B
  have hRrefl : ∀ i, R i i := by
    intro i
    obtain ⟨y, hy⟩ := hpt.exists_smul_eq b₁ i
    exact ⟨y, hy ▸ Set.smul_mem_smul_set hb₁, hy ▸ Set.smul_mem_smul_set hb₁⟩
  have hRtrans : ∀ i j k, R i j → R j k → R i k := by
    rintro i j k ⟨y, hi, hj⟩ ⟨y', hj', hk⟩
    by_cases he : y • B = y' • B
    · exact ⟨y, hi, he ▸ hk⟩
    · exact absurd (Set.disjoint_left.1 (hB he) hj) (not_not.2 hj')
  have hRmove : ∀ (z : ρ.range) i j, R (z • i) (z • j) ↔ R i j := by
    intro z i j
    constructor
    · rintro ⟨y, hi, hj⟩
      refine ⟨z⁻¹ * y, ?_, ?_⟩
      · have := Set.smul_mem_smul_set (a := z⁻¹) hi
        rwa [inv_smul_smul, smul_smul] at this
      · have := Set.smul_mem_smul_set (a := z⁻¹) hj
        rwa [inv_smul_smul, smul_smul] at this
    · rintro ⟨y, hi, hj⟩
      refine ⟨z * y, ?_, ?_⟩
      · have := Set.smul_mem_smul_set (a := z) hi
        rwa [smul_smul] at this
      · have := Set.smul_mem_smul_set (a := z) hj
        rwa [smul_smul] at this
  -- The coarser partition.
  let M' : Setoid Ω :=
    { r := fun v w => (v ∈ S.dom ∧ w ∈ S.dom ∧ R (blk v) (blk w)) ∨ (v ∉ S.dom ∧ w ∉ S.dom)
      iseqv := ⟨fun v => by
          by_cases hv : v ∈ S.dom
          exacts [Or.inl ⟨hv, hv, hRrefl _⟩, Or.inr ⟨hv, hv⟩],
        fun h => by
          rcases h with ⟨a, b, ⟨y, h1, h2⟩⟩ | ⟨a, b⟩
          exacts [Or.inl ⟨b, a, ⟨y, h2, h1⟩⟩, Or.inr ⟨b, a⟩],
        fun h1 h2 => by
          rcases h1 with ⟨a, b, c⟩ | ⟨a, b⟩ <;> rcases h2 with ⟨a', b', c'⟩ | ⟨a', b'⟩
          · exact Or.inl ⟨a, b', hRtrans _ _ _ c c'⟩
          · exact absurd b a'
          · exact absurd a' b
          · exact Or.inr ⟨a, b'⟩⟩ }
  have hM'r : ∀ v ∈ S.dom, ∀ w ∈ S.dom, M'.r v w ↔ R (blk v) (blk w) := by
    intro v hv w hw
    constructor
    · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
      exacts [h, absurd hv h]
    · exact fun h => Or.inl ⟨hv, hw, h⟩
  have hMM' : ∀ v ∈ S.dom, ∀ w ∈ S.dom, M.r v w → M'.r v w := by
    intro v hv w hw h
    have he : blk v = blk w := (blockMap_eq_iff S M hd hv hw).2 h
    rw [hM'r v hv w hw, he]
    exact hRrefl _
  have hcand : IsCand S.G S.dom f M' := by
    refine ⟨fun g hg v hv w hw => ?_, fun v hv w hw h => hMM' v hv w hw (hMc.le v hv w hw h), ?_⟩
    · have hgv := (S.dom_inv g hg v).2 hv
      have hgw := (S.dom_inv g hg w).2 hw
      rw [hM'r _ hgv _ hgw, hM'r v hv w hw]
      have e1 := blockMap_equivariant S M hM hd ⟨g, hg⟩ hv
      have e2 := blockMap_equivariant S M hM hd ⟨g, hg⟩ hw
      change blk (g v) = ρ ⟨g, hg⟩ (blk v) at e1
      change blk (g w) = ρ ⟨g, hg⟩ (blk w) at e2
      rw [e1, e2]
      exact hRmove ⟨ρ ⟨g, hg⟩, ⟨g, hg⟩, rfl⟩ (blk v) (blk w)
    · intro hall
      obtain ⟨v, hv, hvb⟩ := blockMap_onto S M hd b₁
      obtain ⟨w, hw, hwc⟩ := blockMap_onto S M hd c
      have h := (hM'r v hv w hw).1 (hall v hv w hw)
      change R (blk v) (blk w) at h
      rw [show blk v = b₁ from hvb, show blk w = c from hwc] at h
      obtain ⟨y, hy1, hyc⟩ := h
      by_cases he : y • B = (1 : ρ.range) • B
      · rw [he, one_smul] at hyc
        exact hc hyc
      · exact Set.disjoint_left.1 (hB he) hy1 (by rw [one_smul]; exact hb₁)
  -- `M'` relates more pairs than `M`.
  have hlt : pairCount S.dom M < pairCount S.dom M' := by
    apply Set.ncard_lt_ncard _ (Set.toFinite _)
    obtain ⟨v, hv, hvb⟩ := blockMap_onto S M hd b₁
    obtain ⟨w, hw, hwb⟩ := blockMap_onto S M hd b₂
    refine ⟨fun p ⟨h1, h2, h3⟩ => ⟨h1, h2, hMM' _ h1 _ h2 h3⟩, fun hsub => ?_⟩
    have hR : M'.r v w := by
      rw [hM'r v hv w hw]
      refine ⟨1, ?_, ?_⟩
      · rw [one_smul]; exact (show blk v = b₁ from hvb) ▸ hb₁
      · rw [one_smul]; exact (show blk w = b₂ from hwb) ▸ hb₂
    obtain ⟨-, -, hMvw⟩ := hsub (show (v, w) ∈ {p : Ω × Ω | p.1 ∈ S.dom ∧ p.2 ∈ S.dom ∧
      M'.r p.1 p.2} from ⟨hv, hw, hR⟩)
    have := (blockMap_eq_iff S M hd hv hw).2 hMvw
    exact hb12 ((show blk v = b₁ from hvb).symm.trans (this.trans hwb))
  exact absurd (hmax M' hcand hMM') (not_le.2 hlt)

end Blocks

/-! ### The exposed quotient -/

theorem towerRank_split_le {c d e : ℕ} (hc : 1 ≤ c) (hd : 2 ≤ d) (hcde : c * d ≤ e) :
    GI.towerRank c + GI.towerRank d ≤ GI.towerRank e := by
  rcases Nat.lt_or_ge c 2 with h | h
  · have : c = 1 := by omega
    subst this
    simp only [GI.towerRank, le_refl, if_true, zero_add]
    exact GI.tower_rank_mono (by omega)
  · have h1 := GI.tower_rank_split h hd
    have h2 := GI.tower_rank_mono hcde
    linarith

theorem log_split_le {c d e cap : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) (hcde : c * d ≤ e) :
    Real.log c * Real.log (max (min cap c) 2 : ℕ) + Real.log d * Real.log (max (min cap d) 2 : ℕ) ≤
      Real.log e * Real.log (max cap 2 : ℕ) := by
  have hL : ∀ x : ℕ, Real.log (max (min cap x) 2 : ℕ) ≤ Real.log (max cap 2 : ℕ) := by
    intro x
    apply Real.log_le_log (by positivity)
    exact_mod_cast max_le_max (min_le_left _ _) le_rfl
  have hL0 : ∀ x : ℕ, 0 ≤ Real.log (max x 2 : ℕ) := fun x => Real.log_natCast_nonneg _
  have hc0 := Real.log_natCast_nonneg c
  have hd0 := Real.log_natCast_nonneg d
  have hsum : Real.log c + Real.log d ≤ Real.log e := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hcde
  have h1 := mul_le_mul_of_nonneg_left (hL c) hc0
  have h2 := mul_le_mul_of_nonneg_left (hL d) hd0
  have h3 := mul_le_mul_of_nonneg_right hsum (hL0 cap)
  nlinarith

/-- The retained column partition of a state, if any (`State.rows`, Section 6.2). -/
def State.retainedCols {C : Type} (S : State Ω C) : Option (Setoid Ω) :=
  S.rows.bind RowRecord.cols

/-- `M` is coarser on the domain than the retained column partition. -/
def AboveCols {C : Type} (S : State Ω C) (M : Setoid Ω) : Prop :=
  ∀ c, S.retainedCols = some c → ∀ v ∈ S.dom, ∀ w ∈ S.dom, c.r v w → M.r v w

/-- `c` is a block system of the domain that splits it and is comparable on the domain with
every level of the stored hierarchy. Then "the next primitive quotient above" `c` exists. -/
structure ColsComparable {C : Type} (S : State Ω C) (c : Setoid Ω) : Prop where
  inv : ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom, c.r (g v) (g w) ↔ c.r v w
  proper : ¬ UnivOn S.dom c
  comparable : ∀ pre post, S.hier = pre ++ post →
    (∀ v ∈ S.dom, ∀ w ∈ S.dom, (fineEnd ⊥ pre).r v w → c.r v w) ∨
      (∀ v ∈ S.dom, ∀ w ∈ S.dom, c.r v w → (fineEnd ⊥ pre).r v w)

/-- The blocks of an exposed quotient are coarser than the retained column partition, when it
is comparable with the stored levels. -/
def PrimitiveQuotient.AboveCols {C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) : Prop :=
  ∀ c, S.retainedCols = some c → ColsComparable S c →
    ∀ v ∈ S.dom, ∀ w ∈ S.dom, c.r v w → Q.blk v = Q.blk w

/-- **The exposed hierarchy keeps the old levels**: every partition that is the fine end of a
prefix of the old hierarchy on the domain is the fine end of a prefix of the exposed one. The
exposure only splits one interval `J` into the levels `f ≤ M ≤ J.part`. -/
def PrimitiveQuotient.KeepsLevels {C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) : Prop :=
  ∀ c, ColsLevel S.dom S.hier c → ColsLevel S.dom (Q.pre ++ Q.top :: Q.post) c

/-- The level after a prefix is the partition of its last interval. -/
theorem hierLevel_append_cons (l a : List (Interval Ω)) (I : Interval Ω) :
    hierLevel (l ++ I :: a) = a.foldl (fun _ I => I.part) I.part := by
  simp [hierLevel, List.foldl_append, List.foldl_cons]

/-- A candidate with no strictly coarser candidate has the most related pairs among the
candidates coarser than it. -/
theorem pairCount_le_of_maximal [Finite Ω] {G : Subgroup (Perm Ω)} {D : Set Ω} {f M : Setoid Ω}
    (hmax : ∀ M', IsCand G D f M' → (∀ v ∈ D, ∀ w ∈ D, M.r v w → M'.r v w) →
      ∀ v ∈ D, ∀ w ∈ D, M'.r v w → M.r v w) :
    ∀ M', IsCand G D f M' → (∀ v ∈ D, ∀ w ∈ D, M.r v w → M'.r v w) →
      pairCount D M' ≤ pairCount D M := by
  intro M' h1 h2
  have h3 := hmax M' h1 h2
  have : {p : Ω × Ω | p.1 ∈ D ∧ p.2 ∈ D ∧ M'.r p.1 p.2} =
      {p : Ω × Ω | p.1 ∈ D ∧ p.2 ∈ D ∧ M.r p.1 p.2} := by
    ext ⟨v, w⟩
    exact ⟨fun ⟨hv, hw, h⟩ => ⟨hv, hw, h3 v hv w hw h⟩, fun ⟨hv, hw, h⟩ => ⟨hv, hw, h2 v hv w hw h⟩⟩
  unfold pairCount
  rw [this]

/-- **A primitive quotient from a maximal candidate** (the form a program can reach: Algorithm 5,
"Expose the next primitive quotient above any retained column partition"). Let the stored
hierarchy be `pre ++ J :: post`, where the coarse end of `J` holds the domain, and let `M` be a
candidate above the fine end `f` of `pre` (`G`-invariant on the domain, coarser than `f`, not
holding the whole domain) such that no candidate is strictly coarser than `M` on the domain,
and such that `M` is coarser than every retained column partition that is comparable with the
stored levels and coarser than `f`. Then the exposed hierarchy that splits `J` at `M` gives a
primitive quotient above the retained columns that keeps the old levels, and its blocks are the
classes of `M` on the domain. -/
theorem exists_primitiveQuotient_of_cand [Finite Ω] {C : Type} (S : State Ω C)
    (htr : S.Transitive) (hinv : S.HierInv) (pre : List (Interval Ω)) (J : Interval Ω)
    (post : List (Interval Ω)) (hl : S.hier = pre ++ J :: post) (hJ : UnivOn S.dom J.part)
    (M : Setoid Ω) (hMc : IsCand S.G S.dom (fineEnd ⊥ pre) M)
    (hmaxM : ∀ M', IsCand S.G S.dom (fineEnd ⊥ pre) M' →
      (∀ v ∈ S.dom, ∀ w ∈ S.dom, M.r v w → M'.r v w) →
      ∀ v ∈ S.dom, ∀ w ∈ S.dom, M'.r v w → M.r v w)
    (hcols : ∀ c, S.retainedCols = some c → ColsComparable S c →
      (∀ v ∈ S.dom, ∀ w ∈ S.dom, (fineEnd ⊥ pre).r v w → c.r v w) →
      ∀ v ∈ S.dom, ∀ w ∈ S.dom, c.r v w → M.r v w) :
    ∃ Q : PrimitiveQuotient S, (∀ v ∈ S.dom, ∀ w ∈ S.dom, Q.blk v = Q.blk w ↔ M.r v w) ∧
      Q.AboveCols ∧ Q.KeepsLevels ∧
      ∃ c₁ : ℕ, c₁ * Q.d = classCount (fineEnd ⊥ pre) S.dom ∧
        Q.pre = (if c₁ = 1 then pre else pre ++ [⟨M, c₁, min J.cap c₁, J.origin⟩]) ∧
        Q.top = ⟨J.part, Q.d, min J.cap Q.d, J.origin⟩ ∧ Q.post = post := by
  classical
  have htr' : ∀ v ∈ S.dom, ∀ w ∈ S.dom, w ∈ orb S.G v := fun v hv w hw => htr v hv w hw
  set f := fineEnd ⊥ pre with hfdef
  have hch := hinv.chain
  unfold State.HierInv at hinv
  rw [hl] at hch hinv
  obtain ⟨hchpre, hJinv, hfJ, hJcount, hJcap, hpost⟩ := chain_append.1 hch
  have hfinv := Chain.fineEnd_inv hchpre (bot_inv _ _)
  have hmax := pairCount_le_of_maximal hmaxM
  obtain ⟨a₀, ha₀⟩ : S.dom.Nonempty := by
    by_contra hne
    exact hMc.proper fun v hv => absurd ⟨v, hv⟩ hne
  -- The numbers of blocks.
  have hd2 : 2 ≤ blockNum S M := by
    obtain ⟨v, hv, w, hw, hvw⟩ : ∃ v ∈ S.dom, ∃ w ∈ S.dom, ¬ M.r v w := by
      by_contra h
      push Not at h
      exact hMc.proper h
    haveI : Nontrivial (BlockT S M) :=
      ⟨⟨Quotient.mk _ ⟨v, hv⟩, Quotient.mk _ ⟨w, hw⟩, fun h => hvw (by have := Quotient.exact h; exact this)⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.2 this
  have hd0 : 0 < blockNum S M := by omega
  have hdM : blockNum S M = classCount M S.dom := rfl
  set c₁ := classCount f (classIn S.G S.dom M a₀) with hc₁
  have hind : ∀ a ∈ S.dom, classCount f (classIn S.G S.dom M a) = c₁ := fun a ha =>
    classCount_classIn_eq S.dom_inv htr hfinv hMc.inv ha₀ ha
  have hc₁1 : 1 ≤ c₁ := one_le_classCount f ⟨a₀, ha₀, htr' a₀ ha₀ a₀ ha₀, M.refl a₀⟩
  have hmul := classCount_mul S.dom_inv htr hfinv hMc.inv hMc.le ha₀
  have hJall : classIn S.G S.dom J.part a₀ = S.dom := by
    ext w
    exact ⟨fun h => h.1, fun hw => ⟨hw, htr' a₀ ha₀ w hw, hJ a₀ ha₀ w hw⟩⟩
  have hcd : c₁ * blockNum S M ≤ J.ratio := by
    have := hJcount a₀ ha₀
    rw [hJall, hmul, ← hdM] at this
    rw [mul_comm]
    exact this
  let mid : Interval Ω := ⟨M, c₁, min J.cap c₁, J.origin⟩
  let top : Interval Ω := ⟨J.part, blockNum S M, min J.cap (blockNum S M), J.origin⟩
  -- A trivial interval (`c₁ = 1`: the fine end already is the block partition on the domain) is
  -- not stored.
  obtain ⟨pre', hpre'⟩ : ∃ l : List (Interval Ω), l = if c₁ = 1 then pre else pre ++ [mid] :=
    ⟨_, rfl⟩
  have hfM : ∀ v ∈ S.dom, ∀ w ∈ S.dom, (fineEnd ⊥ pre').r v w ↔ M.r v w := by
    intro v hv w hw
    by_cases h1 : c₁ = 1
    · rw [hpre', if_pos h1]
      refine ⟨hMc.le v hv w hw, fun hvw => ?_⟩
      have hcnt : classCount f (classIn S.G S.dom M v) = 1 := (hind v hv).trans h1
      have hvX : v ∈ classIn S.G S.dom M v := classIn_mem_self M hv
      have hwX : w ∈ classIn S.G S.dom M v := ⟨hw, htr' v hv w hw, hvw⟩
      unfold classCount at hcnt
      haveI := (Nat.card_eq_one_iff_unique.1 hcnt).1
      have := Subsingleton.elim
        (Quotient.mk (Setoid.comap (Subtype.val : classIn S.G S.dom M v → Ω) f) ⟨v, hvX⟩)
        (Quotient.mk _ ⟨w, hwX⟩)
      exact Quotient.exact (s := Setoid.comap (Subtype.val : classIn S.G S.dom M v → Ω) f) this
    · rw [hpre', if_neg h1]
      rw [fineEnd_append]
      exact Iff.rfl
  have hfinv' : ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom,
      (fineEnd ⊥ pre').r (g v) (g w) ↔ (fineEnd ⊥ pre').r v w := by
    intro g hg v hv w hw
    rw [hfM _ ((S.dom_inv g hg v).2 hv) _ ((S.dom_inv g hg w).2 hw), hfM v hv w hw]
    exact hMc.inv g hg v hv w hw
  have hcaps := hinv.caps
  obtain ⟨hcpre, hcJ, hcpost⟩ := caps_append.1 hcaps
  have hJcls : ∀ a ∈ S.dom, ∀ w ∈ S.dom, w ∈ classIn S.G S.dom J.part a :=
    fun a ha w hw => ⟨hw, htr' a ha w hw, hJ a ha w hw⟩
  -- The bound of `mid`: a sub-interval of `J`, clamped by its ratio.
  have hcmid : CapOK S.G S.dom f M (min J.cap c₁) := fun a ha =>
    capAt_min_count ((hcJ a ha).sub le_rfl (fun _ _ h => hJcls a ha _ h.1)
        (fun _ _ _ hfix w hw => hfix w (hJcls a ha w hw.1)))
      S.dom_inv hfinv hMc.inv (hind a ha).le
  -- The bound of `top`: a block quotient of `J`, clamped by its ratio.
  have hctop : CapOK S.G S.dom (fineEnd ⊥ pre') J.part (min J.cap (blockNum S M)) := by
    intro a ha
    refine capAt_min_count ((hcJ a ha).sub le_rfl (fun _ _ h => h) fun u hu _ hfix w hw => ?_)
      S.dom_inv hfinv' hJinv ?_
    · have huw : u w ∈ S.dom := (S.dom_inv u hu w).2 hw.1
      exact (hfM _ huw w hw.1).2 (hMc.le _ huw w hw.1 (hfix w hw))
    · rw [classCount_congr (f' := M) fun v hv w hw => hfM v hv.1 w hw.1]
      exact (classCount_mono M (fun w hw => hw.1)).trans hdM.symm.le
  have hlist : pre ++ [mid] ++ top :: post = pre ++ [mid, top] ++ post := by simp
  have hlist' : pre ++ J :: post = pre ++ [J] ++ post := by simp
  have hlist1 : pre ++ top :: post = pre ++ [top] ++ post := by simp
  have hrank1 : GI.towerRank (blockNum S M) ≤ GI.towerRank J.ratio :=
    GI.tower_rank_mono (le_trans (by nlinarith) hcd)
  -- Every new interval is nontrivial, with numbers at most those of `J`.
  have hfrom : ∀ I ∈ pre' ++ top :: post, I ∈ S.hier ∨ ∃ J' ∈ S.hier, 2 ≤ I.ratio ∧
      I.ratio ≤ J'.ratio ∧ I.cap ≤ J'.cap ∧ I.origin = J'.origin := by
    have hJmem : J ∈ S.hier := by rw [hl]; simp
    have htopok : 2 ≤ top.ratio ∧ top.ratio ≤ J.ratio ∧ top.cap ≤ J.cap ∧ top.origin = J.origin :=
      ⟨hd2, le_trans (by nlinarith) hcd, min_le_left _ _, rfl⟩
    intro I hI
    simp only [List.mem_append, List.mem_cons] at hI
    rcases hI with hI | rfl | hI
    · by_cases h1 : c₁ = 1
      · rw [hpre', if_pos h1] at hI
        exact Or.inl (by rw [hl]; simp [hI])
      · rw [hpre', if_neg h1] at hI
        simp only [List.mem_append, List.mem_singleton] at hI
        rcases hI with hI | rfl
        · exact Or.inl (by rw [hl]; simp [hI])
        · refine Or.inr ⟨J, hJmem, show 2 ≤ c₁ by omega, show c₁ ≤ J.ratio from
            le_trans (by nlinarith) hcd, min_le_left _ _, rfl⟩
    · exact Or.inr ⟨J, hJmem, htopok⟩
    · exact Or.inl (by rw [hl]; simp [hI])
  refine ⟨{ d := blockNum S M
            blk := blockMap S M hd0
            ρ := blockRho S M hMc.inv
            equivariant := fun g v hv => blockMap_equivariant S M hMc.inv hd0 g hv
            onto := blockMap_onto S M hd0
            primitive := blockPrimitive S M hMc.inv hd0 htr hMc hmax
            two_le := hd2
            pre := pre'
            top := top
            post := post
            rho_le := ?_
            Q_le := ?_
            drop := ?_
            ratio_eq := rfl
            fine_eq := fun v hv w hw =>
              (hfM v hv w hw).trans (blockMap_eq_iff S M hd0 hv hw).symm
            top_univ := hJ
            tower := ?_
            from_old := hfrom }, fun v hv w hw => (blockMap_eq_iff S M hd0 hv hw), ?_, ?_,
            c₁, show c₁ * blockNum S M = _ by rw [hmul, ← hdM, mul_comm], hpre', rfl, rfl⟩
  · rw [hl]
    by_cases h1 : c₁ = 1
    · rw [hpre', if_pos h1]
      rw [hlist1, hlist', CitedInstances.hierRho_append, CitedInstances.hierRho_append,
        CitedInstances.hierRho_append, CitedInstances.hierRho_append]
      have h' : State.hierRho [top] ≤ State.hierRho [J] := by
        simp only [State.hierRho, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero]
        exact_mod_cast hrank1
      linarith
    · rw [hpre', if_neg h1]
      rw [hlist, hlist', CitedInstances.hierRho_append, CitedInstances.hierRho_append,
        CitedInstances.hierRho_append, CitedInstances.hierRho_append]
      have h := towerRank_split_le hc₁1 hd2 hcd
      have h' : State.hierRho [mid, top] ≤ State.hierRho [J] := by
        simp only [State.hierRho, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero]
        exact_mod_cast h
      linarith
  · rw [hl]
    have hsplit := log_split_le (cap := J.cap) hc₁1 (show 1 ≤ blockNum S M by omega) hcd
    by_cases h1 : c₁ = 1
    · rw [hpre', if_pos h1]
      rw [hlist1, hlist', CitedInstances.hierQ_append, CitedInstances.hierQ_append,
        CitedInstances.hierQ_append, CitedInstances.hierQ_append]
      have h' : State.hierQ [top] ≤ State.hierQ [J] := by
        simp only [State.hierQ, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero]
        rw [h1] at hsplit
        simpa [top] using hsplit
      linarith
    · rw [hpre', if_neg h1]
      rw [hlist, hlist', CitedInstances.hierQ_append, CitedInstances.hierQ_append,
        CitedInstances.hierQ_append, CitedInstances.hierQ_append]
      have h' : State.hierQ [mid, top] ≤ State.hierQ [J] := by
        simp only [State.hierQ, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero]
        exact hsplit
      linarith
  · rw [hl]
    by_cases h1 : c₁ = 1
    · -- No new level: the sum of the bounds does not increase.
      right
      rw [hpre', if_pos h1]
      simp only [List.map_append, List.map_cons, List.sum_append,
        List.sum_cons]
      have : top.cap ≤ J.cap := min_le_left _ _
      omega
    · -- A nontrivial split: `ρ` drops.
      left
      rw [hpre', if_neg h1]
      rw [hlist, hlist', CitedInstances.hierRho_append, CitedInstances.hierRho_append,
        CitedInstances.hierRho_append, CitedInstances.hierRho_append]
      have h := GI.tower_rank_split (show 2 ≤ c₁ by omega) hd2
      have h2 := GI.tower_rank_mono hcd
      have h' : State.hierRho [mid, top] + 1 ≤ State.hierRho [J] := by
        simp only [State.hierRho, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero]
        exact_mod_cast (by linarith : GI.towerRank c₁ + GI.towerRank (blockNum S M) + 1 ≤
          GI.towerRank J.ratio)
      linarith
  · refine ⟨?_, ?_, ?_⟩
    · rw [chain_append]
      refine ⟨?_, (chain_congr hfM).2 ⟨hJinv, fun v hv w hw _ => hJ v hv w hw, fun a _ => ?_,
        min_le_right _ _, hpost⟩⟩
      · by_cases h1 : c₁ = 1
        · rw [hpre', if_pos h1]; exact hchpre
        · rw [hpre', if_neg h1]
          exact chain_append.2 ⟨hchpre, hMc.inv, hMc.le, fun a ha => (hind a ha).le,
            min_le_right _ _, trivial⟩
      · exact (classCount_mono M (fun w hw => hw.1)).trans hdM.symm.le
    · have htop := hinv.top
      rw [fineEnd_append] at htop ⊢
      exact htop
    · refine caps_append.2 ⟨?_, hctop, hcpost⟩
      by_cases h1 : c₁ = 1
      · rw [hpre', if_pos h1]; exact hcpre
      · rw [hpre', if_neg h1]
        exact caps_append.2 ⟨hcpre, hcmid, trivial⟩
  · -- The blocks are above a comparable retained column partition.
    intro c hc hcc v hv w hw hvw
    change blockMap S M hd0 v = blockMap S M hd0 w
    rw [blockMap_eq_iff S M hd0 hv hw]
    rcases hcc.comparable pre (J :: post) hl with hfc' | hcf
    · -- `f ≤ c`: `M` is above the columns by hypothesis.
      exact hcols c hc hcc hfc' v hv w hw hvw
    · -- `c ≤ f ≤ M`.
      exact hMc.le v hv w hw (hcf v hv w hw hvw)
  · -- The old levels are levels of the exposed hierarchy: `pre'` extends `pre`, and `top` has
    -- the coarse end of `J`.
    obtain ⟨e, he⟩ : ∃ e, pre' = pre ++ e := by
      by_cases h1 : c₁ = 1
      · exact ⟨[], by rw [hpre', if_pos h1, List.append_nil]⟩
      · exact ⟨[mid], by rw [hpre', if_neg h1]⟩
    intro c ⟨p0, p1, h0, hc⟩
    change ColsLevel S.dom (pre' ++ top :: post) c
    -- A prefix of `pre` stays a prefix.
    have hpre_case : ∀ a', pre = p0 ++ a' → ColsLevel S.dom (pre' ++ top :: post) c :=
      fun a' ha' => ⟨p0, a' ++ e ++ top :: post, by rw [he, ha']; simp, hc⟩
    rcases List.append_eq_append_iff.1 (h0.symm.trans hl) with ⟨a', h1, -⟩ | ⟨c', h1, h2⟩
    · exact hpre_case a' h1
    · cases c' with
      | nil => exact hpre_case [] (by rw [h1, List.append_nil, List.append_nil])
      | cons K c'' =>
        obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 h2
        refine ⟨pre' ++ top :: c'', p1, by simp, fun v hv w hw => ?_⟩
        rw [hierLevel_append_cons]
        rw [h1, hierLevel_append_cons] at hc
        exact hc v hv w hw

/-- **The exposed primitive quotient exists** on a transitive state with the hierarchy invariant
and two points (Algorithm 5: "Expose the next primitive quotient above any retained column
partition"). Among the candidates, the coarsest is taken among those above the retained column
partition when there is one. -/
theorem exists_primitiveQuotient [Finite Ω] {C : Type} (S : State Ω C) (htr : S.Transitive)
    (hinv : S.HierInv) (h2 : ¬ UnivOn S.dom ⊥) :
    ∃ Q : PrimitiveQuotient S, Q.AboveCols ∧ Q.KeepsLevels := by
  classical
  have htr' : ∀ v ∈ S.dom, ∀ w ∈ S.dom, w ∈ orb S.G v := fun v hv w hw => htr v hv w hw
  obtain ⟨pre, J, post, hl, hpre, hJ⟩ := exists_split htr' ⊥ S.hier hinv.top h2
  set f := fineEnd ⊥ pre with hfdef
  have hch := hinv.chain
  unfold State.HierInv at hinv
  rw [hl] at hch
  obtain ⟨hchpre, -, -, -, -, -⟩ := chain_append.1 hch
  have hfinv := Chain.fineEnd_inv hchpre (bot_inv _ _)
  have hfc : IsCand S.G S.dom f f := ⟨hfinv, fun _ _ _ _ h => h, hpre⟩
  -- The candidates above the retained columns, if there is one; else all candidates.
  let p : Setoid Ω → Prop := fun M =>
    (∃ M₀, IsCand S.G S.dom f M₀ ∧ AboveCols S M₀) → AboveCols S M
  have hp_mono : ∀ M M', p M → (∀ v ∈ S.dom, ∀ w ∈ S.dom, M.r v w → M'.r v w) → p M' :=
    fun M M' hM hle hex c hc v hv w hw h => hle v hv w hw (hM hex c hc v hv w hw h)
  obtain ⟨M, hMc, hpM, hmax⟩ : ∃ M, IsCand S.G S.dom f M ∧ p M ∧
      ∀ M', IsCand S.G S.dom f M' → p M' → pairCount S.dom M' ≤ pairCount S.dom M := by
    by_cases hex : ∃ M₀, IsCand S.G S.dom f M₀ ∧ AboveCols S M₀
    · obtain ⟨M₀, h₀, hA⟩ := hex
      exact exists_maxCand_of p h₀ fun _ => hA
    · exact exists_maxCand_of p hfc fun h => absurd h hex
  -- No candidate is strictly coarser than `M`: it would relate more pairs.
  have hmaxM : ∀ M', IsCand S.G S.dom f M' → (∀ v ∈ S.dom, ∀ w ∈ S.dom, M.r v w → M'.r v w) →
      ∀ v ∈ S.dom, ∀ w ∈ S.dom, M'.r v w → M.r v w := by
    intro M' h1 h2
    have hle := hmax M' h1 (hp_mono M M' hpM h2)
    have hsub : {q : Ω × Ω | q.1 ∈ S.dom ∧ q.2 ∈ S.dom ∧ M.r q.1 q.2} ⊆
        {q : Ω × Ω | q.1 ∈ S.dom ∧ q.2 ∈ S.dom ∧ M'.r q.1 q.2} :=
      fun q ⟨hv, hw, h⟩ => ⟨hv, hw, h2 _ hv _ hw h⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
    intro v hv w hw h
    have : (v, w) ∈ {q : Ω × Ω | q.1 ∈ S.dom ∧ q.2 ∈ S.dom ∧ M.r q.1 q.2} := by
      rw [heq]; exact ⟨hv, hw, h⟩
    exact this.2.2
  -- `M` is above every comparable column partition coarser than `f`: such a partition is a
  -- candidate above the columns.
  have hcols : ∀ c, S.retainedCols = some c → ColsComparable S c →
      (∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r v w → c.r v w) →
      ∀ v ∈ S.dom, ∀ w ∈ S.dom, c.r v w → M.r v w := by
    intro c hc hcc hfc' v hv w hw hvw
    have hcand : IsCand S.G S.dom f c := ⟨hcc.inv, hfc', hcc.proper⟩
    have hA : AboveCols S c := fun c' hc' => by
      rw [hc] at hc'
      cases hc'
      exact fun _ _ _ _ h => h
    exact hpM ⟨c, hcand, hA⟩ c hc v hv w hw hvw
  obtain ⟨Q, -, h1, h2, -⟩ :=
    exists_primitiveQuotient_of_cand S htr hinv pre J post hl hJ M hMc hmaxM hcols
  exact ⟨Q, h1, h2⟩

/-- **The exposed primitive quotient** of a transitive state with the hierarchy invariant and
at least two positions, above the retained column partition (`State.expose_aboveCols`). -/
noncomputable def State.expose [Finite Ω] {C : Type} (S : State Ω C) (htr : S.Transitive)
    (hinv : S.HierInv) (h2 : ¬ UnivOn S.dom ⊥) : PrimitiveQuotient S :=
  Classical.choose (exists_primitiveQuotient S htr hinv h2)

/-- **The exposed quotient lies above the retained column partition** (Algorithm 5: "Expose
the next primitive quotient above any retained column partition"), when that partition is a
block system that splits the domain and is comparable with the stored levels. -/
theorem State.expose_aboveCols [Finite Ω] {C : Type} (S : State Ω C) (htr : S.Transitive)
    (hinv : S.HierInv) (h2 : ¬ UnivOn S.dom ⊥) : (S.expose htr hinv h2).AboveCols :=
  (Classical.choose_spec (exists_primitiveQuotient S htr hinv h2)).1

/-- **The exposed hierarchy keeps the old levels.** -/
theorem State.expose_keepsLevels [Finite Ω] {C : Type} (S : State Ω C) (htr : S.Transitive)
    (hinv : S.HierInv) (h2 : ¬ UnivOn S.dom ⊥) : (S.expose htr hinv h2).KeepsLevels :=
  (Classical.choose_spec (exists_primitiveQuotient S htr hinv h2)).2

end GI.Algorithm
