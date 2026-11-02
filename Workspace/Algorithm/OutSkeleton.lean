import Workspace.Algorithm.AuxCases
import Workspace.Cited.DesignLemma

/-!
# Skeletons of a coherent configuration on the labels

Cases 2b and 3 of the aggregation (Section A.3) end with one of two objects read off a `k`-ary
coherent configuration `c` on the labels `Γ = [q]` and an individualized tuple `x` of `ℓ`
labels:

* the vertex coloring `z ↦ c(x, z, …, z)` ([H, Section 5]: `X_x^{(1)}`), as a colored partition
  into its color classes (`classPart`); if every class has at most `s` points, the even
  stabilizer has width at most `s` (`classPart_cap`);
* the pair coloring `(z₁, z₂) ↦ c(x, z₁, z₂, …, z₂)` (`(X_x)^{(2)}`) on a vertex class `C`
  (`skelCfg`). When `ℓ + 1 < k`, it is a coherent configuration on `C` (`skelCfg_coherent`):
  equal colors have the same equality pattern, the same converse color, and the same
  intersection numbers inside `C`. The intersection numbers inside `C` are sums of the
  intersection numbers of `c` (axiom (b) of a configuration recovers the colors of
  `(x, a, z, …, z)`, `(x, z, b, …, b)` and `(x, z, …, z)` from the colors of single-coordinate
  updates of `(x, a, b, …, b)`), so they are the same for two pairs of the same color
  (`card_filter_eq_of_coherent`).

Both are used in Case 2b with `k = 2`, `ℓ = 0` (the refined orbital graph) and in Case 3 with
the Design Lemma's tuple.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Cited

/-! ### Counting with equal fiber sizes -/

section Count

/-- Two maps with the same fiber sizes differ by a permutation of the domain. -/
theorem exists_equiv_of_fiber_card {α β : Type*} [Fintype α] [DecidableEq β] (f f' : α → β)
    (h : ∀ v, (Finset.univ.filter fun z => f z = v).card =
      (Finset.univ.filter fun z => f' z = v).card) :
    ∃ e : α ≃ α, ∀ z, f' (e z) = f z := by
  classical
  have hv : ∀ v, Nonempty ({z // f z = v} ≃ {z // f' z = v}) := fun v =>
    ⟨Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact h v)⟩
  let e : α ≃ α := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun v => (hv v).some).trans (Equiv.sigmaFiberEquiv f'))
  exact ⟨e, fun z => ((hv (f z)).some ⟨z, rfl⟩).2⟩

/-- **Counting through a vector of colors**: if `f` and `f'` have the same fiber sizes and the
predicates `p`, `p'` depend only on the values of `f`, `f'`, they hold equally often. -/
theorem card_filter_eq_of_fibers {α β : Type*} [Fintype α] [DecidableEq β] (f f' : α → β)
    (h : ∀ v, (Finset.univ.filter fun z => f z = v).card =
      (Finset.univ.filter fun z => f' z = v).card)
    (p p' : α → Prop) [DecidablePred p] [DecidablePred p']
    (hp : ∀ z z', f z = f' z' → (p z ↔ p' z')) :
    (Finset.univ.filter p).card = (Finset.univ.filter p').card := by
  obtain ⟨e, he⟩ := exists_equiv_of_fiber_card f f' h
  refine Finset.card_equiv e fun z => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hp z (e z) (he z).symm

variable {q k : ℕ}

/-- The colors of the single-coordinate updates of a tuple. -/
def updVec (c : (Fin k → Fin q) → ℕ) (y : Fin k → Fin q) (z : Fin q) : Fin k → ℕ :=
  fun i => c (Function.update y i z)

/-- **Coherence as equal fiber sizes** of the update colors. -/
theorem updVec_fibers {c : (Fin k → Fin q) → ℕ} (hco : IsCoherent c) {y y' : Fin k → Fin q}
    (h : c y = c y') (v : Fin k → ℕ) :
    (Finset.univ.filter fun z => updVec c y z = v).card =
      (Finset.univ.filter fun z => updVec c y' z = v).card := by
  have e : ∀ w : Fin k → Fin q, (Finset.univ.filter fun z => updVec c w z = v) =
      Finset.univ.filter fun z => ∀ i, c (Function.update w i z) = v i := by
    intro w
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, updVec, funext_iff]
  rw [e, e]
  exact hco y y' h v

/-- **Counts through the update colors**: for two tuples of the same color, every predicate of
the update colors holds for equally many points. -/
theorem card_filter_eq_of_coherent {c : (Fin k → Fin q) → ℕ} (hco : IsCoherent c)
    {y y' : Fin k → Fin q} (h : c y = c y') (p p' : Fin q → Prop) [DecidablePred p]
    [DecidablePred p'] (hp : ∀ z z', updVec c y z = updVec c y' z' → (p z ↔ p' z')) :
    (Finset.univ.filter p).card = (Finset.univ.filter p').card :=
  card_filter_eq_of_fibers _ _ (updVec_fibers hco h) p p' hp

end Count

/-! ### Tuple identities -/

section Tuples

variable {q k ℓ : ℕ}

theorem padTuple₂_self (x : Fin ℓ → Fin q) (a : Fin q) :
    (padTuple₂ x a a : Fin k → Fin q) = padTuple x a := by
  funext i
  simp only [padTuple₂, padTuple]
  split_ifs <;> rfl

/-- The map of positions that swaps the last two coordinates of `(x, a, b, …, b)`. -/
def swapPos (hk : ℓ + 1 < k) : Fin k → Fin k :=
  fun i => if i.val < ℓ then i else if i.val = ℓ then ⟨ℓ + 1, hk⟩ else ⟨ℓ, by omega⟩

theorem padTuple₂_swap (hk : ℓ + 1 < k) (x : Fin ℓ → Fin q) (a b : Fin q) :
    (padTuple₂ x a b : Fin k → Fin q) ∘ swapPos hk = padTuple₂ x b a := by
  funext i
  simp only [Function.comp, swapPos, padTuple₂]
  by_cases h1 : i.val < ℓ
  · simp [h1]
  · by_cases h2 : i.val = ℓ
    · simp [h2]
    · simp [h1, h2]

/-- Positions `> ℓ` go to `ℓ + 1`. -/
def tailPos (hk : ℓ + 1 < k) : Fin k → Fin k :=
  fun i => if i.val ≤ ℓ then i else ⟨ℓ + 1, hk⟩

/-- Positions `≥ ℓ` go to `ℓ`. -/
def headPos (hk : ℓ + 1 < k) : Fin k → Fin k :=
  fun i => if i.val < ℓ then i else ⟨ℓ, by omega⟩

theorem padTuple₂_upd_head (hk : ℓ + 1 < k) (x : Fin ℓ → Fin q) (a b z : Fin q) :
    Function.update (padTuple₂ x a b : Fin k → Fin q) ⟨ℓ, by omega⟩ z = padTuple₂ x z b := by
  funext i
  by_cases hi : i = ⟨ℓ, by omega⟩
  · subst hi; simp [padTuple₂]
  · rw [Function.update_of_ne hi]
    have hi' : i.val ≠ ℓ := fun h => hi (Fin.ext h)
    simp [padTuple₂, hi']

theorem padTuple₂_upd_tail (hk : ℓ + 1 < k) (x : Fin ℓ → Fin q) (a b z : Fin q) :
    Function.update (padTuple₂ x a b : Fin k → Fin q) ⟨ℓ + 1, hk⟩ z ∘ tailPos hk =
      padTuple₂ x a z := by
  funext i
  simp only [Function.comp, tailPos]
  by_cases h1 : i.val ≤ ℓ
  · rw [if_pos h1, Function.update_of_ne (fun h => by rw [h] at h1; simp at h1)]
    simp only [padTuple₂]
    by_cases h2 : i.val < ℓ
    · simp [h2]
    · have : i.val = ℓ := by omega
      simp [this]
  · rw [if_neg h1, Function.update_self]
    simp only [padTuple₂]
    have h2 : ¬ i.val < ℓ := by omega
    have h3 : i.val ≠ ℓ := by omega
    simp [h2, h3]

theorem padTuple₂_upd_diag (hk : ℓ + 1 < k) (x : Fin ℓ → Fin q) (a b z : Fin q) :
    Function.update (padTuple₂ x a b : Fin k → Fin q) ⟨ℓ, by omega⟩ z ∘ headPos hk =
      padTuple₂ x z z := by
  rw [padTuple₂_upd_head hk]
  funext i
  simp only [Function.comp, headPos, padTuple₂]
  by_cases h1 : i.val < ℓ
  · simp [h1]
  · simp [h1]

end Tuples

/-! ### The vertex coloring as a colored partition -/

section ClassPart

variable {q : ℕ}

/-- The color class of `a` under a vertex coloring `f`. -/
noncomputable def classOf (f : Fin q → ℕ) (a : Fin q) : Finset (Fin q) :=
  Finset.univ.filter fun b => f b = f a

/-- **The colored partition of a vertex coloring**: each label lies in its color class, colored
by its color. -/
noncomputable def classPart (f : Fin q → ℕ) : ColPart (Fin q) := ⟨classOf f, f⟩

theorem classPart_smul (σ : Perm (Fin q)) (f : Fin q → ℕ) :
    σ • classPart f = classPart (fun a => f (σ⁻¹ a)) := by
  ext a b
  · simp only [ColPart.smul_blk, classPart, classOf, Finset.mem_map_equiv, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rfl
  · rfl

/-- **The cap of a vertex coloring** (Section A.3: "The analogous balanced-coloring outcome of
Design has all its color classes bounded by a fixed fraction of `q`, and has the same cap
conclusion"): if every color class has at most `s ≥ 1` points, the even stabilizer of the
colored partition has width at most `s`. -/
theorem classPart_cap (f : Fin q → ℕ) {s : ℕ} (hs : 1 ≤ s) (h : ∀ a, (classOf f a).card ≤ s) :
    GI.SectionCaps.Cap (evenStab (q := q) (classPart f)) s := by
  classical
  apply evenStab_cap_of
  refine colPart_cap (classPart f) (fun a => ?_) (fun a b hb => ?_) h (fun c => ?_) _
    (fun σ hσ => hσ)
  · simp [classPart, classOf]
  · simpa [classPart, classOf] using hb
  · refine le_trans (Finset.card_le_one.2 fun B hB B' hB' => ?_) hs
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hB'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, classPart] at ha ha'
    simp only [classPart, classOf, ha, ha']

end ClassPart

/-! ### The pair skeleton -/

section Skeleton

variable {q k ℓ : ℕ}

/-- **The pair skeleton** `(z₁, z₂) ↦ c(x, z₁, z₂, …, z₂)` with the diagonal color `j`: its
fiber is the vertex class `{z | c(x, z, …, z) = j}`. -/
def skelCfg (c : (Fin k → Fin q) → ℕ) (x : Fin ℓ → Fin q) (j : ℕ) : PairCfg q :=
  ⟨fun a b => skel₂ c x a b, j⟩

theorem mem_skelCfg_fiber {c : (Fin k → Fin q) → ℕ} {x : Fin ℓ → Fin q} {j : ℕ} {a : Fin q} :
    a ∈ (skelCfg c x j).fiber ↔ skel₁ c x a = j := by
  rw [PairCfg.mem_fiber]
  change c (padTuple₂ x a a) = j ↔ c (padTuple x a) = j
  rw [padTuple₂_self]

/-- **The pair skeleton is coherent on its fiber** when `ℓ + 1 < k` ([H, Section 5]: the pair
coloring `(X_x)^{(2)}` of a `k`-ary coherent configuration is coherent): equal colors have the
same equality pattern, the same converse color, and the same intersection numbers inside the
fiber. -/
theorem skelCfg_coherent {c : (Fin k → Fin q) → ℕ} (hc : IsConfiguration c)
    (hco : IsCoherent c) (hk : ℓ + 1 < k) (x : Fin ℓ → Fin q) (j : ℕ) :
    ∀ a ∈ (skelCfg c x j).fiber, ∀ b ∈ (skelCfg c x j).fiber,
      ∀ a' ∈ (skelCfg c x j).fiber, ∀ b' ∈ (skelCfg c x j).fiber,
      (skelCfg c x j).col a b = (skelCfg c x j).col a' b' →
      (a = b ↔ a' = b') ∧ (skelCfg c x j).col b a = (skelCfg c x j).col b' a' ∧
        ∀ i i', (skelCfg c x j).inter a b i i' = (skelCfg c x j).inter a' b' i i' := by
  classical
  intro a _ b _ a' _ b' _ hab
  set y : Fin k → Fin q := padTuple₂ x a b with hy
  set y' : Fin k → Fin q := padTuple₂ x a' b' with hy'
  have hcy : c y = c y' := hab
  let pℓ : Fin k := ⟨ℓ, by omega⟩
  let pℓ1 : Fin k := ⟨ℓ + 1, hk⟩
  refine ⟨?_, ?_, fun i i' => ?_⟩
  · -- the equality pattern at the two last coordinates
    have := hc.1 y y' hcy pℓ pℓ1
    have e1 : y pℓ = a := by simp [hy, pℓ, padTuple₂]
    have e2 : y pℓ1 = b := by simp [hy, pℓ1, padTuple₂]
    have e1' : y' pℓ = a' := by simp [hy', pℓ, padTuple₂]
    have e2' : y' pℓ1 = b' := by simp [hy', pℓ1, padTuple₂]
    rwa [e1, e2, e1', e2'] at this
  · -- the converse color
    have := hc.2 y y' hcy (swapPos hk)
    change c (padTuple₂ x b a) = c (padTuple₂ x b' a')
    rwa [← padTuple₂_swap hk x a b, ← padTuple₂_swap hk x a' b']
  · -- the intersection numbers inside the fiber
    have key : ∀ (w : Fin k → Fin q) (u v : Fin q), w = padTuple₂ x u v →
        (skelCfg c x j).inter u v i i' = (Finset.univ.filter fun z =>
          c (Function.update w pℓ z ∘ headPos hk) = j ∧
          c (Function.update w pℓ1 z ∘ tailPos hk) = i ∧ c (Function.update w pℓ z) = i').card := by
      intro w u v hw
      unfold PairCfg.inter PairCfg.fiber
      rw [Finset.filter_filter]
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hw]
      rw [padTuple₂_upd_diag hk, padTuple₂_upd_tail hk, padTuple₂_upd_head hk]
      rfl
    rw [key y a b hy, key y' a' b' hy']
    refine card_filter_eq_of_coherent hco hcy _ _ fun z z' hz => ?_
    have h1 : c (Function.update y pℓ z) = c (Function.update y' pℓ z') := congrFun hz pℓ
    have h2 : c (Function.update y pℓ1 z) = c (Function.update y' pℓ1 z') := congrFun hz pℓ1
    rw [hc.2 _ _ h1 (headPos hk), hc.2 _ _ h2 (tailPos hk), h1]

/-- **A good pair skeleton**: if `ℓ + 1 < k`, the fiber has at least `δq` points, and two pairs
of distinct fiber points have different colors, the skeleton is good. -/
theorem skelCfg_good {c : (Fin k → Fin q) → ℕ} (hc : IsConfiguration c) (hco : IsCoherent c)
    (hk : ℓ + 1 < k) (x : Fin ℓ → Fin q) (j : ℕ) {δ : ℝ}
    (hlarge : δ * q ≤ (skelCfg c x j).fiber.card)
    (hnt : ∃ a ∈ (skelCfg c x j).fiber, ∃ b ∈ (skelCfg c x j).fiber,
      ∃ a' ∈ (skelCfg c x j).fiber, ∃ b' ∈ (skelCfg c x j).fiber,
      a ≠ b ∧ a' ≠ b' ∧ skel₂ c x a b ≠ skel₂ c x a' b') :
    (skelCfg c x j).Good δ :=
  ⟨skelCfg_coherent hc hco hk x j, hnt, hlarge⟩

end Skeleton

end GI.Algorithm
