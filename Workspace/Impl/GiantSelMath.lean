import Workspace.Impl.Weights
import Workspace.Lang.Prims.BlockMath

/-!
# The mathematics of the row test of `GiantStep`

`GiantStep` first decides the row case `RowCase α S L` for its supplied labels `L` (Algorithm 5:
"if `q > λ` … if this map is natural and (no rows are retained, or `q` exceeds their degree)").
The three parts of the test are decided as follows.

* `q > N^α` with `α = 2/5` holds exactly when `N² < q⁵` (`rpow_α_lt_iff`), a test on numbers.
* The row degree is read from the state value.
* A natural kernel-orbit map exists exactly when the Johnson block map of the supplied
  constituent has blocks of size one and the kernel `K = ker π` is transitive on each block fiber
  (`natural_iff`). The block map is part of the supplied labels, so a program reads it.

The proof of `natural_iff`. If a natural map `label` exists, every block `p v` is invariant under
the even permutations fixing `label v` (they are label images of elements that move `v` inside
its kernel orbit), and a nonempty block of at most `q/2` labels with this property is `{label v}`
(`eq_singleton_of_inv`: a 3-cycle fixing `label v` moves any other label of the block to any
third label). So the blocks have size one and equal blocks mean equal labels, which means one
kernel orbit. Conversely, blocks of size one give the map `v ↦` the label in `p v`: it is
equivariant because `p` is, onto because all blocks of the same size have fibers of the same
size, and its fibers are kernel orbits by the transitivity hypothesis.

The kernel is computed as a preimage of the trivial group in the graph group
`{g ⊕ π g}` (`mem_graphKer`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens sumToFin)

variable {Ω C : Type} {k : ℕ}

/-! ### The threshold `q > N^α` -/

theorem P₀_α_eq : P₀.α = 2 / 5 := by norm_num [P₀]

/-- `N^{2/5} < q` exactly when `N² < q⁵`. -/
theorem rpow_α_lt_iff (N q : ℕ) : (N : ℝ) ^ P₀.α < q ↔ N ^ 2 < q ^ 5 := by
  rw [P₀_α_eq]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : ((N : ℝ) ^ (2 / 5 : ℝ)) ^ (5 : ℕ) = (N : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
    norm_num
  have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (2 / 5 : ℝ) := Real.rpow_nonneg hN _
  rw [← pow_lt_pow_iff_left₀ h2 (Nat.cast_nonneg q) (by norm_num : (5 : ℕ) ≠ 0), h1]
  exact_mod_cast Iff.rfl

/-! ### Blocks invariant under a point stabilizer -/

/-- **A block fixed by the even permutations fixing `a`** is `{a}`, if it is nonempty, has at most
`q/2` labels, and `q ≥ 5`. -/
theorem eq_singleton_of_inv {q : ℕ} (hq : 5 ≤ q) (a : Fin q) (B : Finset (Fin q))
    (hinv : ∀ σ : Perm (Fin q), σ ∈ alternatingGroup (Fin q) → σ a = a → ∀ b ∈ B, σ b ∈ B)
    (h1 : 1 ≤ B.card) (h2 : 2 * B.card ≤ q) : B = {a} := by
  classical
  have hsub : ∀ b ∈ B, b = a := by
    intro b hb
    by_contra hba
    -- every label other than `a` lies in `B`
    have hall : ∀ c : Fin q, c ≠ a → c ∈ B := by
      intro c hca
      by_cases hcb : c = b
      · rw [hcb]; exact hb
      · -- a fourth label `d`
        have hcard : ({a, b, c} : Finset (Fin q)).card < (Finset.univ : Finset (Fin q)).card := by
          have := (Finset.card_le_three : ({a, b, c} : Finset (Fin q)).card ≤ 3)
          simp only [Finset.card_univ, Fintype.card_fin]; omega
        obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
        obtain ⟨hda, hdb, hdc⟩ := hd
        have hmem : swap b d * swap b c ∈ alternatingGroup (Fin q) := by
          rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
            Equiv.Perm.sign_swap (Ne.symm hdb), Equiv.Perm.sign_swap (Ne.symm hcb)]
          decide
        have hfix : (swap b d * swap b c) a = a := by
          rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hba) (Ne.symm hca),
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hba) (Ne.symm hda)]
        have hbc : (swap b d * swap b c) b = c := by
          rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
            Equiv.swap_apply_of_ne_of_ne hcb (Ne.symm hdc)]
        have := hinv _ hmem hfix b hb
        rwa [hbc] at this
    have hsub' : Finset.univ.erase a ⊆ B := fun c hc => hall c (Finset.ne_of_mem_erase hc)
    have := Finset.card_le_card hsub'
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
  rw [Finset.eq_singleton_iff_unique_mem]
  exact ⟨hsub b hb ▸ hb, hsub⟩

/-! ### Natural kernel-orbit maps and the block map -/

variable {S : State Ω C}

/-- The kernel relation: `w` lies in the kernel orbit of `v`. -/
def KerRel (S : State Ω C) (L : GiantLabels S) (v w : Ω) : Prop :=
  ∃ g : S.G, L.π g = 1 ∧ (g : Perm Ω) v = w

/-- Under a natural map, every block is the singleton of the label. -/
theorem blocks_eq_label {L : GiantLabels S} (J : JohnsonBlocks S L) (hq : 5 ≤ L.q)
    {label : Ω → Fin L.q} (hn : NaturalRows S L label) (v : S.dom) : J.p v = {label v} := by
  classical
  refine eq_singleton_of_inv hq _ _ ?_ (by rw [J.card]; exact J.one_le) (by rw [J.card]; exact J.half)
  intro σ hσ hfix b hb
  obtain ⟨g, hg⟩ := L.π_surj ⟨σ, hσ⟩
  have hgv : label ((g : Perm Ω) v) = label v := by
    rw [hn.equivariant g v v.2, hg]; exact hfix
  obtain ⟨k', hk1, hkv⟩ := (hn.fibers v v.2 _ ((S.dom_inv g g.2 v).mpr v.2)).mp hgv.symm
  have hkeq : S.domHom k' v = S.domHom g v := Subtype.ext (by simpa using hkv)
  have h1 := J.equivariant k' v
  rw [hk1] at h1
  have h2 := J.equivariant g v
  rw [hkeq] at h1
  rw [h1] at h2
  have hbm : σ b ∈ (J.p v).map ((L.π g : alternatingGroup (Fin L.q)) : Perm (Fin L.q)).toEmbedding := by
    rw [Finset.mem_map]
    exact ⟨b, hb, by simp [hg]⟩
  rw [← h2] at hbm
  simpa using hbm

/-- **A natural kernel-orbit map exists exactly when the blocks have size one and the kernel is
transitive on each block fiber.** -/
theorem natural_iff [Finite Ω] {L : GiantLabels S} (J : JohnsonBlocks S L) (hq : 5 ≤ L.q)
    (hne : S.dom.Nonempty) :
    (∃ label, NaturalRows S L label) ↔
      J.h = 1 ∧ ∀ v w : S.dom, J.p v = J.p w → KerRel S L v w := by
  classical
  constructor
  · rintro ⟨label, hn⟩
    obtain ⟨v₀, hv₀⟩ := hne
    refine ⟨?_, fun v w hvw => ?_⟩
    · rw [← J.card ⟨v₀, hv₀⟩, blocks_eq_label J hq hn]; rfl
    · rw [blocks_eq_label J hq hn, blocks_eq_label J hq hn, Finset.singleton_inj] at hvw
      exact (hn.fibers v v.2 w w.2).mp hvw
  · rintro ⟨hh, hK⟩
    have hone : ∀ v : S.dom, ∃ a, J.p v = {a} := fun v =>
      Finset.card_eq_one.mp ((J.card v).trans hh)
    let lab : S.dom → Fin L.q := fun v => (hone v).choose
    have hlab : ∀ v, J.p v = {lab v} := fun v => (hone v).choose_spec
    have hq0 : 0 < L.q := by omega
    let label : Ω → Fin L.q := fun x => if hx : x ∈ S.dom then lab ⟨x, hx⟩ else ⟨0, hq0⟩
    have hlabel : ∀ v : S.dom, label v = lab v := fun v => by simp [label, v.2]
    have heqv : ∀ (g : S.G) (v : S.dom),
        lab (S.domHom g v) = (L.π g : alternatingGroup (Fin L.q)).val (lab v) := by
      intro g v
      have := J.equivariant g v
      rw [hlab, hlab, Finset.map_singleton, Finset.singleton_inj] at this
      exact this
    refine ⟨label, ⟨fun g v hv => ?_, fun i => ?_, fun v hv w hw => ?_⟩⟩
    · have := heqv g ⟨v, hv⟩
      rw [← hlabel, ← hlabel] at this
      exact this
    · -- onto: the fibers of all singletons have the same size `f ≥ 1`
      obtain ⟨v₀, hv₀⟩ := hne
      have hf : 1 ≤ J.f := by
        rw [← J.fibers {lab ⟨v₀, hv₀⟩} (by simp [hh])]
        have : Nonempty {v : S.dom // J.p v = {lab ⟨v₀, hv₀⟩}} := ⟨⟨⟨v₀, hv₀⟩, hlab _⟩⟩
        exact Nat.card_pos
      have hpos : 0 < Nat.card {v : S.dom // J.p v = {i}} := by
        rw [J.fibers {i} (by simp [hh])]; omega
      obtain ⟨⟨v, hv⟩⟩ := (Nat.card_pos_iff.mp hpos).1
      refine ⟨v, v.2, ?_⟩
      rw [hlabel]
      rw [hlab] at hv
      exact Finset.singleton_inj.mp hv
    · rw [show label v = lab ⟨v, hv⟩ from hlabel ⟨v, hv⟩,
        show label w = lab ⟨w, hw⟩ from hlabel ⟨w, hw⟩]
      constructor
      · intro h
        exact hK ⟨v, hv⟩ ⟨w, hw⟩ (by rw [hlab, hlab, h])
      · rintro ⟨g, hg1, hgv⟩
        have := heqv g ⟨v, hv⟩
        rw [hg1] at this
        have he : S.domHom g ⟨v, hv⟩ = ⟨w, hw⟩ := Subtype.ext (by simpa using hgv)
        rw [he] at this
        exact this.symm

/-! ### The kernel as a preimage in the graph group -/

open Classical in
/-- The graph map `g ↦ g ⊕ π g` on the permutations of `Fin k` that come from `G`. -/
noncomputable def graphMap (e : Ω ≃ Fin k) (L : GiantLabels S) (g : Perm (Fin k)) :
    Perm (Fin k ⊕ Fin L.q) :=
  if h : (toFin e).symm g ∈ S.G then
    Perm.sumCongr g ((L.π ⟨_, h⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q))
  else 1

theorem mem_groupFin_iff (e : Ω ≃ Fin k) (G : Subgroup (Perm Ω)) (g : Perm (Fin k)) :
    g ∈ groupFin e G ↔ (toFin e).symm g ∈ G :=
  Subgroup.mem_map_equiv

theorem graphMap_of_mem (e : Ω ≃ Fin k) (L : GiantLabels S) {g : Perm (Fin k)}
    (h : (toFin e).symm g ∈ S.G) :
    graphMap e L g = Perm.sumCongr g ((L.π ⟨_, h⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) := by
  classical
  unfold graphMap
  rw [dif_pos h]

theorem graphMap_mul (e : Ω ≃ Fin k) (L : GiantLabels S) :
    ∀ a ∈ groupFin e S.G, ∀ b ∈ groupFin e S.G,
      graphMap e L (a * b) = graphMap e L a * graphMap e L b := by
  intro a ha b hb
  rw [mem_groupFin_iff] at ha hb
  have hab : (toFin e).symm (a * b) ∈ S.G := by rw [map_mul]; exact S.G.mul_mem ha hb
  rw [graphMap_of_mem e L ha, graphMap_of_mem e L hb, graphMap_of_mem e L hab,
    Perm.sumCongr_mul]
  congr 1
  have : (⟨_, hab⟩ : S.G) = ⟨_, ha⟩ * ⟨_, hb⟩ := Subtype.ext (map_mul _ _ _)
  rw [this, map_mul]
  rfl

theorem sumCongr_inj' {n n' : ℕ} {a c : Perm (Fin n)} {b d : Perm (Fin n')}
    (h : Perm.sumCongr a b = Perm.sumCongr c d) : a = c ∧ b = d := by
  constructor
  · refine Equiv.ext fun i => ?_
    have := congrArg (fun σ : Perm (Fin n ⊕ Fin n') => σ (Sum.inl i)) h
    simpa using this
  · refine Equiv.ext fun i => ?_
    have := congrArg (fun σ : Perm (Fin n ⊕ Fin n') => σ (Sum.inr i)) h
    simpa using this

open GI.Cited (PreimageInst) in
/-- **The preimage instance of the kernel**: the graph generators `g ⊕ π g` and no generators of
the image subgroup. -/
def kerInst {q : ℕ} (ps : List (Perm (Fin k) × Perm (Fin q))) : PreimageInst where
  n := k
  n' := q
  ds := ps.map fun p => Perm.sumCongr p.1 p.2
  ms := []
  preserves := fun d hd i => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hd
    exact ⟨p.1 i, by simp⟩
  ms_le := fun m hm => by simp at hm

/-- **The preimage of the trivial group in the graph group is the kernel of `π`.** -/
theorem mem_kerInst (e : Ω ≃ Fin k) (L : GiantLabels S)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hgen : gens (ps.map Prod.fst) = groupFin e S.G)
    (hπ : ∀ p ∈ ps, ∀ hg : (toFin e).symm p.1 ∈ S.G,
      ((L.π ⟨(toFin e).symm p.1, hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) = p.2)
    (g : Perm (Fin k)) :
    g ∈ GI.CitedChecks.preimageSubgroup (kerInst ps) ↔
      ∃ h : (toFin e).symm g ∈ S.G, L.π ⟨_, h⟩ = 1 := by
  have hmem1 : ∀ p ∈ ps, (toFin e).symm p.1 ∈ S.G := fun p hp => by
    rw [← mem_groupFin_iff, ← hgen]
    exact Subgroup.subset_closure (List.mem_map_of_mem hp)
  have hds : {d | d ∈ (kerInst ps).ds} =
      {y | ∃ g ∈ ps.map Prod.fst, graphMap e L g = y} := by
    ext d
    show d ∈ ps.map (fun p => Perm.sumCongr p.1 p.2) ↔ ∃ g ∈ ps.map Prod.fst, graphMap e L g = d
    rw [List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, List.mem_map_of_mem hp, by rw [graphMap_of_mem e L (hmem1 _ hp), hπ _ hp]; rfl⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact ⟨p, hp, by rw [graphMap_of_mem e L (hmem1 _ hp), hπ _ hp]; rfl⟩
  show (∃ h ∈ Subgroup.closure {m | m ∈ ([] : List (Perm (Fin L.q)))},
    Perm.sumCongr g h ∈ Subgroup.closure {d | d ∈ (kerInst ps).ds}) ↔ _
  simp only [List.not_mem_nil, Set.setOf_false, Subgroup.closure_empty, Subgroup.mem_bot,
    exists_eq_left]
  have key := mem_closure_image_of_mul (groupFin e S.G) (graphMap e L) (graphMap_mul e L)
    (gs := ps.map Prod.fst) (fun g hg => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      rw [mem_groupFin_iff]; exact hmem1 p hp) (Perm.sumCongr g 1)
  rw [hds]
  refine key.trans ?_
  rw [hgen]
  constructor
  · rintro ⟨g', hg', he⟩
    rw [mem_groupFin_iff] at hg'
    rw [graphMap_of_mem e L hg'] at he
    obtain ⟨rfl, h1⟩ := sumCongr_inj' he
    refine ⟨hg', Subtype.ext ?_⟩
    exact h1
  · rintro ⟨hg, h1⟩
    refine ⟨g, (mem_groupFin_iff e S.G g).mpr hg, ?_⟩
    rw [graphMap_of_mem e L hg, h1]
    rfl

/-- **Kernel orbits as orbits of the computed generators.** -/
theorem kerRel_iff_orbit (e : Ω ≃ Fin k) (L : GiantLabels S) {hs : List (Perm (Fin k))}
    (hK : ∀ g, g ∈ gens hs ↔ ∃ h : (toFin e).symm g ∈ S.G, L.π ⟨_, h⟩ = 1) (v w : Ω) :
    KerRel S L v w ↔ e w ∈ genOrbit hs (e v) := by
  rw [mem_genOrbit]
  constructor
  · rintro ⟨g, hg1, rfl⟩
    refine ⟨toFin e g, ?_, ?_⟩
    · show toFin e g ∈ gens hs
      rw [hK]
      have hg2 : (toFin e).symm (toFin e g) ∈ S.G := by
        rw [MulEquiv.symm_apply_apply]; exact g.2
      refine ⟨hg2, ?_⟩
      have : (⟨(toFin e).symm (toFin e g), hg2⟩ : S.G) = g :=
        Subtype.ext (MulEquiv.symm_apply_apply _ _)
      rw [this, hg1]
    · simp [toFin, Equiv.permCongrHom, Equiv.permCongr_apply]
  · rintro ⟨g, hg, hgv⟩
    obtain ⟨h, h1⟩ := (hK g).mp hg
    refine ⟨⟨_, h⟩, h1, ?_⟩
    apply e.injective
    rw [← hgv]
    simp [toFin, Equiv.permCongrHom, Equiv.permCongr_apply]

end GI.Impl
