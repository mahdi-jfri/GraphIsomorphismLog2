import Workspace.Algorithm.AuxConfig

/-!
# Balanced colored partitions of a configuration branch

Lemma 5.1 and Lemma A.28 (`GI.Paper.lem_main_rectangle`, `GI.Paper.lem_first_soj_rectangle`) give
a fixed-fraction restriction before any rectangle appears, in two ways:

* the configuration is imprimitive: the components of one color form "the canonical partition
  into equal blocks of sizes between `2` and `n/2`" (first paragraph of [H, Section 5.2]);
* at the individualized source vertex `x₀`, "every resulting color class has size at most
  `η|C|`, the coloring already gives a balanced restriction".

Section A.3, "Case 1 and balanced colored partitions": "an admissible colored partition on
`C₀ ⊆ Γ`, `|C₀| ≥ δq`, with block sizes at most `η|C₀|`, has block counts at most `|C₀|/2` …
Extending over the omitted points adds width at most `q - |C₀| ≤ (1-δ)q`. Thus this branch has
full ideal cap at most `max{η, 1-δ}q`." "No index of a colored-partition stabilizer is enumerated:
its full overcoset is lifted."

This file defines the two colored partitions of `Γ` from a pair configuration (`impPart`,
`balPart`), shows that they commute with relabeling, bounds the caps of their stabilizers
(`impPart_cap`, `balPart_cap`), and gives the overcoset item of an equivariant object
(`objItem`, `objItem_valid`). The points outside the fiber form one more color class.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.PairRefinement GI.CoherentEntrance

/-! ### The overcoset item of an object -/

section Overcoset

variable {P : Params} {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {Z : Type*} [MulAction (Perm (Fin L.q)) Z]

open Classical in
/-- **The overcoset item of an object**: if an even permutation `σ` maps the object `z_X` of the
source to the object `z_Y` of the target, the overcoset `σ E₀` of the even stabilizer `E₀` of
`z_X`; otherwise no item ("rejecting an empty parity coset"). -/
noncomputable def objItem (zX zY : Z) : AuxItem P S L :=
  if h : ∃ σ : alternatingGroup (Fin L.q), (σ : Perm (Fin L.q)) • zX = zY then
    .overcoset h.choose (evenStab (q := L.q) zX)
  else .none

/-- **The overcoset item of an object is valid** when every parent isomorphism of the branch maps
`z_X` to `z_Y` and the even stabilizer of `z_X` has the cap `⌊βq⌋`. -/
theorem objItem_valid {zX zY : Z} {B : Set (Perm Ω)}
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • zX = zY)
    (hcap : GI.SectionCaps.Cap (evenStab (q := L.q) zX) ⌊P.β * L.q⌋₊) :
    (objItem (P := P) zX zY : AuxItem P S L).Valid B := by
  classical
  unfold objItem
  split_ifs with h
  · refine ⟨hcap, fun g hg => ?_⟩
    obtain ⟨hgG, he⟩ := hB g hg
    refine ⟨hgG, ?_⟩
    show ((h.choose⁻¹ * L.π ⟨g, hgG⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) • zX = zX
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, he]
    exact inv_smul_eq_iff.2 h.choose_spec.symm
  · show S.answer ∩ B = ∅
    refine Set.eq_empty_iff_forall_notMem.2 fun g hg => h ?_
    obtain ⟨hgG, he⟩ := hB g hg
    exact ⟨_, he⟩

end Overcoset

namespace PairCfg

variable {q : ℕ}

/-! ### Components of one color -/

/-- An edge of color `v` between two points of the fiber, in either direction. -/
def edge (P : PairCfg q) (v : ℕ) (a b : Fin q) : Prop :=
  a ∈ P.fiber ∧ b ∈ P.fiber ∧ (P.col a b = v ∨ P.col b a = v)

/-- Reachability by edges of color `v`. -/
def reach (P : PairCfg q) (v : ℕ) : Fin q → Fin q → Prop := Relation.ReflTransGen (P.edge v)

theorem reach_symm {P : PairCfg q} {v : ℕ} {a b : Fin q} (h : P.reach v a b) : P.reach v b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ he ih => exact Relation.ReflTransGen.head ⟨he.2.1, he.1, he.2.2.symm⟩ ih

theorem reach_mem {P : PairCfg q} {v : ℕ} {a b : Fin q} (h : P.reach v a b) (ha : a ∈ P.fiber) :
    b ∈ P.fiber := by
  induction h with
  | refl => exact ha
  | tail _ he _ => exact he.2.1

theorem edge_smul (σ : Perm (Fin q)) (P : PairCfg q) (v : ℕ) (a b : Fin q) :
    (σ • P).edge v a b ↔ P.edge v (σ⁻¹ a) (σ⁻¹ b) := by
  simp only [edge, mem_fiber_smul, smul_col]

theorem reach_smul (σ : Perm (Fin q)) (P : PairCfg q) (v : ℕ) (a b : Fin q) :
    (σ • P).reach v a b ↔ P.reach v (σ⁻¹ a) (σ⁻¹ b) := by
  constructor
  · intro h
    exact Relation.ReflTransGen.lift (fun x => σ⁻¹ x) (fun x y hxy => (edge_smul σ P v x y).1 hxy) h
  · intro h
    have h' := Relation.ReflTransGen.lift (fun x => σ x)
      (fun x y hxy => (edge_smul σ P v (σ x) (σ y)).2 (by simpa using hxy)) h
    simpa using h'

open Classical in
/-- The component of `a` for the color `v`. -/
noncomputable def comp (P : PairCfg q) (v : ℕ) (a : Fin q) : Finset (Fin q) :=
  Finset.univ.filter (P.reach v a)

theorem mem_comp {P : PairCfg q} {v : ℕ} {a b : Fin q} : b ∈ P.comp v a ↔ P.reach v a b := by
  classical
  simp [comp]

theorem comp_eq_of_mem {P : PairCfg q} {v : ℕ} {a b : Fin q} (hb : b ∈ P.comp v a) :
    P.comp v b = P.comp v a := by
  ext z
  rw [mem_comp, mem_comp]
  have hab := mem_comp.1 hb
  exact ⟨fun h => hab.trans h, fun h => (reach_symm hab).trans h⟩

theorem comp_smul (σ : Perm (Fin q)) (P : PairCfg q) (v : ℕ) (a : Fin q) :
    (σ • P).comp v a = (P.comp v (σ⁻¹ a)).map σ.toEmbedding := by
  ext b
  rw [mem_comp, Finset.mem_map_equiv, mem_comp, reach_smul]
  rfl

/-! ### The two colored partitions -/

open Classical in
/-- **The imprimitive partition**: the components of the color `v` on the fiber, and the points
outside the fiber as singletons of a second color. -/
noncomputable def impPart (P : PairCfg q) (v : ℕ) : ColPart (Fin q) :=
  ⟨fun a => if a ∈ P.fiber then P.comp v a else {a}, fun a => if a ∈ P.fiber then 1 else 0⟩

open Classical in
/-- **The balanced partition at a source vertex** `x₀`: the points of the fiber colored by their
pair color from `x₀`, and the points outside the fiber in one more color; all blocks are
singletons. -/
noncomputable def balPart (P : PairCfg q) (x₀ : Fin q) : ColPart (Fin q) :=
  ⟨fun a => {a}, fun a => if a ∈ P.fiber then 2 * P.col x₀ a + 1 else 0⟩

theorem impPart_smul (σ : Perm (Fin q)) (P : PairCfg q) (v : ℕ) :
    σ • P.impPart v = (σ • P).impPart v := by
  classical
  ext a b
  · simp only [ColPart.smul_blk, impPart, mem_fiber_smul]
    split_ifs with h
    · rw [comp_smul]
    · simp only [Finset.map_singleton, Finset.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro rfl; simp
  · simp only [ColPart.smul_col, impPart, mem_fiber_smul]

theorem balPart_smul (σ : Perm (Fin q)) (P : PairCfg q) (x₀ : Fin q) :
    σ • P.balPart x₀ = (σ • P).balPart (σ x₀) := by
  classical
  ext a b
  · simp only [ColPart.smul_blk, balPart, Finset.map_singleton, Finset.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  · simp only [ColPart.smul_col, balPart, mem_fiber_smul, smul_col, Perm.inv_apply_self]

/-! ### Their caps -/

/-- Pairwise disjoint subsets of `T`, each with at least two points, number at most `|T|/2`. -/
theorem two_mul_card_le {T : Finset (Fin q)} (F : Finset (Finset (Fin q)))
    (hdis : ∀ B ∈ F, ∀ B' ∈ F, B ≠ B' → Disjoint B B') (hsub : ∀ B ∈ F, B ⊆ T)
    (h2 : ∀ B ∈ F, 2 ≤ B.card) : 2 * F.card ≤ T.card := by
  classical
  have h := Finset.card_biUnion (s := F) (t := id) (fun B hB B' hB' hne => hdis B hB B' hB' hne)
  have hsum : 2 * F.card ≤ ∑ B ∈ F, (id B).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun B hB => h2 B hB
  have hle : (F.biUnion id).card ≤ T.card :=
    Finset.card_le_card (Finset.biUnion_subset.2 fun B hB => hsub B hB)
  omega

/-- The points outside the fiber number at most `(1 - δ) q`. -/
theorem card_compl_le {P : PairCfg q} {δ β : ℝ} (hδ : δ * q ≤ P.fiber.card) (hβ : 1 - δ ≤ β) :
    (((Finset.univ.filter fun a : Fin q => a ∉ P.fiber).card : ℕ) : ℝ) ≤ β * q := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin q)))
    (p := fun a => a ∈ P.fiber)
  have e : Finset.univ.filter (fun a : Fin q => a ∈ P.fiber) = P.fiber := by ext; simp
  rw [e, Finset.card_univ, Fintype.card_fin] at h
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have : ((Finset.univ.filter fun a : Fin q => a ∉ P.fiber).card : ℝ) = q - P.fiber.card := by
    have h' : (Finset.univ.filter fun a : Fin q => a ∉ P.fiber).card = q - P.fiber.card := by omega
    rw [h', Nat.cast_sub (by omega)]
  rw [this]
  nlinarith

/-- **The cap of the balanced partition** (Section A.3: "Balanced colored partitions give width
at most `max{η, 1-δ}q`"). If every color class at `x₀` has at most `η|C|` points, `|C| ≥ δq`,
`β ≥ max{η, 1-δ}` and `βq ≥ 1`, the even stabilizer of `balPart P x₀` has the cap `⌊βq⌋`. -/
theorem balPart_cap {P : PairCfg q} {x₀ : Fin q} {δ η β : ℝ}
    (hbal : ∀ v, ((P.fiber.filter fun a => P.col x₀ a = v).card : ℝ) ≤ η * P.fiber.card)
    (hδ : δ * q ≤ P.fiber.card) (hηβ : η ≤ β) (hδβ : 1 - δ ≤ β) (hη : 0 ≤ η) (h1 : 1 ≤ β * q) :
    GI.SectionCaps.Cap (evenStab (q := q) (P.balPart x₀)) ⌊β * q⌋₊ := by
  classical
  apply evenStab_cap_of
  have hfq : (P.fiber.card : ℝ) ≤ q := by exact_mod_cast (by simpa using Finset.card_le_univ P.fiber)
  refine colPart_cap (P.balPart x₀) (fun a => Finset.mem_singleton_self a)
    (fun a b hb => by rw [Finset.mem_singleton.1 hb]) (fun a => ?_) (fun c => ?_) _ (fun σ hσ => hσ)
  · simp only [balPart, Finset.card_singleton]
    exact Nat.le_floor (by exact_mod_cast h1)
  · refine Finset.card_image_le.trans (Nat.le_floor ?_)
    by_cases hc : c = 0
    · subst hc
      have e : (Finset.univ.filter fun a => (P.balPart x₀).col a = 0) =
          Finset.univ.filter fun a : Fin q => a ∉ P.fiber := by
        ext a
        simp only [balPart, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with h <;> simp [h]
      rw [e]
      exact card_compl_le hδ hδβ
    · have e : (Finset.univ.filter fun a => (P.balPart x₀).col a = c) ⊆
          P.fiber.filter fun a => P.col x₀ a = (c - 1) / 2 := by
        intro a ha
        simp only [balPart, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        split_ifs at ha with h
        · exact Finset.mem_filter.2 ⟨h, by omega⟩
        · exact absurd ha.symm hc
      have hle : ((Finset.univ.filter fun a => (P.balPart x₀).col a = c).card : ℝ) ≤
          ((P.fiber.filter fun a => P.col x₀ a = (c - 1) / 2).card : ℝ) := by
        exact_mod_cast Finset.card_le_card e
      calc _ ≤ _ := hle
        _ ≤ η * P.fiber.card := hbal _
        _ ≤ η * q := mul_le_mul_of_nonneg_left hfq hη
        _ ≤ β * q := mul_le_mul_of_nonneg_right hηβ (Nat.cast_nonneg _)

/-- **The cap of the imprimitive partition** (Lemma A.28, first alternative: "the canonical
partition into equal blocks of sizes between `2` and `n/2`"). If every component of the color `v`
on the fiber has between `2` and `|C|/2` points, `|C| ≥ δq`, `β ≥ max{1/2, 1-δ}` and `βq ≥ 1`,
the even stabilizer of `impPart P v` has the cap `⌊βq⌋`: blocks have at most `|C|/2` points,
there are at most `|C|/2` of them, and at most `(1-δ)q` points lie outside the fiber. -/
theorem impPart_cap {P : PairCfg q} {v : ℕ} {δ β : ℝ}
    (hsz : ∀ a ∈ P.fiber, 2 ≤ (P.comp v a).card ∧ 2 * (P.comp v a).card ≤ P.fiber.card)
    (hδ : δ * q ≤ P.fiber.card) (hβ : 1 / 2 ≤ β) (hδβ : 1 - δ ≤ β) (h1 : 1 ≤ β * q) :
    GI.SectionCaps.Cap (evenStab (q := q) (P.impPart v)) ⌊β * q⌋₊ := by
  classical
  apply evenStab_cap_of
  have hfq : (P.fiber.card : ℝ) ≤ q := by exact_mod_cast (by simpa using Finset.card_le_univ P.fiber)
  have hhalf : ∀ m : ℕ, 2 * m ≤ P.fiber.card → m ≤ ⌊β * q⌋₊ := by
    intro m hm
    apply Nat.le_floor
    have : (2 * m : ℝ) ≤ P.fiber.card := by exact_mod_cast hm
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith
  refine colPart_cap (P.impPart v) (fun a => ?_) (fun a b hb => ?_) (fun a => ?_) (fun c => ?_) _
    (fun σ hσ => hσ)
  · simp only [impPart]
    split_ifs
    · exact mem_comp.2 Relation.ReflTransGen.refl
    · exact Finset.mem_singleton_self a
  · simp only [impPart] at hb ⊢
    split_ifs at hb with ha
    · rw [if_pos (reach_mem (mem_comp.1 hb) ha), if_pos ha]
    · rw [Finset.mem_singleton.1 hb]
  · simp only [impPart]
    split_ifs with ha
    · exact hhalf _ (hsz a ha).2
    · rw [Finset.card_singleton]; exact Nat.le_floor (by exact_mod_cast h1)
  · by_cases hc1 : c = 1
    · subst hc1
      apply hhalf
      refine two_mul_card_le _ (fun B hB B' hB' hne => ?_) (fun B hB => ?_) (fun B hB => ?_)
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hB
        obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hB'
        simp only [impPart, Finset.mem_filter, Finset.mem_univ, true_and] at ha ha' hne ⊢
        split_ifs at ha ha' hne ⊢ with h h' <;> simp at ha ha'
        rw [Finset.disjoint_left]
        intro z hz hz'
        exact hne ((comp_eq_of_mem hz).symm.trans (comp_eq_of_mem hz'))
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hB
        simp only [impPart, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        split_ifs at ha ⊢ with h
        intro z hz; exact reach_mem (mem_comp.1 hz) h
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hB
        simp only [impPart, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        split_ifs at ha ⊢ with h
        exact (hsz a h).1
    · refine Finset.card_image_le.trans (Nat.le_floor ?_)
      by_cases hc0 : c = 0
      · subst hc0
        have e : (Finset.univ.filter fun a => (P.impPart v).col a = 0) =
            Finset.univ.filter fun a : Fin q => a ∉ P.fiber := by
          ext a
          simp only [impPart, Finset.mem_filter, Finset.mem_univ, true_and]
          split_ifs with h <;> simp [h]
        rw [e]
        exact card_compl_le hδ hδβ
      · have e : (Finset.univ.filter fun a => (P.impPart v).col a = c) = ∅ := by
          ext a
          simp only [impPart, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.notMem_empty, iff_false]
          split_ifs <;> omega
        rw [e]
        simp only [Finset.card_empty, Nat.cast_zero]
        nlinarith

end PairCfg

end GI.Algorithm
