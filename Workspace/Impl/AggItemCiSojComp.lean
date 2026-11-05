module

public import Workspace.Impl.AggItemCiSojMath

@[expose] public section

/-!
# Labeling the imprimitive blocks by components

The blocks in the imprimitive alternative are components of one undirected color
relation, with singleton blocks outside the fiber. We label a point by the least
point of its component. This gives the same block representation used by Case 1.
When every component in each fiber has at least two points, block sizes also tell
which points have the interior color. Thus the size-colored partition and the
model's two-colored partition have the same transporters and stabilizers.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (gens)

variable {q : ℕ}

/-- Every point belongs to its own component, including omitted points. -/
theorem itcs_comp_self (X : PairCfg q) (v : ℕ) (a : Fin q) : a ∈ X.comp v a :=
  PairCfg.mem_comp.2 Relation.ReflTransGen.refl

/-- An omitted point has no incident color edge, so its component is a singleton. -/
theorem itcs_comp_out {X : PairCfg q} {v : ℕ} {a : Fin q} (ha : a ∉ X.fiber) :
    X.comp v a = {a} := by
  have hreach : ∀ b, X.reach v a b → b = a := by
    intro b hb
    induction hb with
    | refl => rfl
    | tail _ he ih => exact False.elim (ha (ih ▸ he.1))
  ext b
  rw [PairCfg.mem_comp, mem_singleton]
  exact ⟨hreach b, fun h => h ▸ Relation.ReflTransGen.refl⟩

/-- The imprimitive blocks are the components on all labels. -/
theorem itcs_imp_blk (X : PairCfg q) (v : ℕ) (a : Fin q) :
    (X.impPart v).blk a = X.comp v a := by
  classical
  by_cases ha : a ∈ X.fiber
  · simp only [PairCfg.impPart, if_pos ha]
  · simp only [PairCfg.impPart, if_neg ha, itcs_comp_out ha]

/-- The component center. -/
noncomputable def itcsCenter (X : PairCfg q) (v : ℕ) (a : Fin q) : Fin q :=
  (X.comp v a).min' ⟨a, itcs_comp_self X v a⟩

/-- The component label is the number of its least point. -/
noncomputable def itcsLab (X : PairCfg q) (v : ℕ) (a : Fin q) : ℕ := itcsCenter X v a

/-- The center belongs to its component. -/
theorem itcs_center_mem (X : PairCfg q) (v : ℕ) (a : Fin q) :
    itcsCenter X v a ∈ X.comp v a := min'_mem _ _

/-- Two labels agree exactly when the points are connected. -/
theorem itcs_lab_eq (X : PairCfg q) (v : ℕ) (a b : Fin q) :
    itcsLab X v a = itcsLab X v b ↔ X.reach v a b := by
  constructor
  · intro h
    have he : itcsCenter X v a = itcsCenter X v b := Fin.ext h
    have ha := PairCfg.mem_comp.1 (itcs_center_mem X v a)
    have hb := PairCfg.mem_comp.1 (itcs_center_mem X v b)
    rw [he] at ha
    exact ha.trans (PairCfg.reach_symm hb)
  · intro hab
    have he := PairCfg.comp_eq_of_mem (PairCfg.mem_comp.2 hab)
    have hc : itcsCenter X v a = itcsCenter X v b :=
      le_antisymm (min'_le _ _ (he ▸ itcs_center_mem X v b))
        (min'_le _ _ (he.symm ▸ itcs_center_mem X v a))
    exact congrArg Fin.val hc

/-- Label classes are exactly the model's components. -/
theorem itcs_lab_blk (X : PairCfg q) (v : ℕ) (a : Fin q) :
    itpBlk (itcsLab X v) a = X.comp v a := by
  ext b
  rw [itp_mem_blk, itcs_lab_eq, PairCfg.mem_comp]
  exact ⟨PairCfg.reach_symm, PairCfg.reach_symm⟩

/-- The center is a point with its own component's label. -/
theorem itcs_center_lab (X : PairCfg q) (v : ℕ) (a : Fin q) :
    itcsLab X v (itcsCenter X v a) = itcsLab X v a :=
  (itcs_lab_eq X v _ _).2 (PairCfg.reach_symm
    (PairCfg.mem_comp.1 (itcs_center_mem X v a)))

/-- The center precedes every point in the same label class. -/
theorem itcs_center_le {X : PairCfg q} {v : ℕ} {a b : Fin q}
    (h : itcsLab X v a = itcsLab X v b) : itcsCenter X v a ≤ b :=
  min'_le _ _ (PairCfg.mem_comp.2 ((itcs_lab_eq X v a b).1 h))

/-- A component label is a valid point number. -/
theorem itcs_lab_lt (X : PairCfg q) (v : ℕ) (a : Fin q) : itcsLab X v a < q :=
  (itcsCenter X v a).isLt

/-- The interior color is detected by the size of the component. -/
theorem itcs_fiber_iff_size {X : PairCfg q} {v : ℕ}
    (h : ∀ a ∈ X.fiber, 2 ≤ (X.comp v a).card) (a : Fin q) :
    a ∈ X.fiber ↔ 2 ≤ (X.comp v a).card := by
  constructor
  · exact h a
  · intro hs
    by_contra ha
    rw [itcs_comp_out ha, card_singleton] at hs
    omega

/-- Size-colored component partitions and the imprimitive objects have the same
transporters when all interior blocks have at least two points. -/
theorem itcs_imp_iff (X Y : PairCfg q) (v : ℕ)
    (hX : ∀ a ∈ X.fiber, 2 ≤ (X.comp v a).card)
    (hY : ∀ a ∈ Y.fiber, 2 ≤ (Y.comp v a).card) (σ : Perm (Fin q)) :
    σ • X.impPart v = Y.impPart v ↔
      σ • itpPart (itcsLab X v) = itpPart (itcsLab Y v) := by
  constructor
  · intro he
    have hm (a : Fin q) : (X.comp v (σ⁻¹ a)).map σ.toEmbedding = Y.comp v a := by
      have := congrArg (fun z : ColPart (Fin q) => z.blk a) he
      simpa only [ColPart.smul_blk, itcs_imp_blk] using this
    apply ColPart.ext
    · funext a
      simp only [ColPart.smul_blk, itpPart, itcs_lab_blk, hm]
    · funext a
      simp only [ColPart.smul_col, itpPart, itcs_lab_blk]
      rw [← hm a, card_map]
  · intro he
    have hm (a : Fin q) : (X.comp v (σ⁻¹ a)).map σ.toEmbedding = Y.comp v a := by
      have := congrArg (fun z : ColPart (Fin q) => z.blk a) he
      simpa only [ColPart.smul_blk, itpPart, itcs_lab_blk] using this
    have hf (a : Fin q) : σ⁻¹ a ∈ X.fiber ↔ a ∈ Y.fiber := by
      rw [itcs_fiber_iff_size hX, itcs_fiber_iff_size hY, ← hm a, card_map]
    apply ColPart.ext
    · funext a
      simp only [ColPart.smul_blk, itcs_imp_blk, hm]
    · funext a
      simp only [ColPart.smul_col, PairCfg.impPart, hf]

/-- The component labeling meets Case 1's labeling contract. The auxiliary star
transpositions only witness the orbit representation of the blocks. -/
theorem itcs_component_labels (X : PairCfg q) (v : ℕ) :
    ItcLab (itciT (itcsLab X v)) (itcsLab X v) := by
  have horb (a b : Fin q) : itcsLab X v a = itcsLab X v b ↔
      b ∈ genOrbit (itciT (itcsLab X v)) a := by
    rw [mem_genOrbit]
    constructor
    · intro h
      exact ⟨Equiv.swap a b, itci_mem_closure (itp_swap_lab h), Equiv.swap_apply_left a b⟩
    · rintro ⟨g, hg, rfl⟩
      exact (itci_keep_of_mem hg a).symm
  refine ⟨horb, fun a => ⟨itcs_lab_lt X v a, ?_, ?_⟩⟩
  · exact (horb a _).1 (itcs_center_lab X v a).symm
  · intro b hb
    exact Fin.le_def.1 (itcs_center_le ((horb a b).2 hb))

/-- A component with at least two points supplies the odd transposition used by Case 1. -/
theorem itcs_component_odd {X : PairCfg q} {v : ℕ} {a : Fin q}
    (ha : 2 ≤ (X.comp v a).card) : ∃ b : Fin q, itcsLab X v b ≠ b := by
  obtain ⟨b, hb, hne⟩ := Finset.exists_mem_ne (by omega : 1 < (X.comp v a).card)
    (itcsCenter X v a)
  refine ⟨b, fun h => hne ?_⟩
  apply Fin.ext
  have he := (itcs_lab_eq X v a b).2 (PairCfg.mem_comp.1 hb)
  exact h.symm.trans he.symm

/-- The existing Case 1 program applies directly to component labels, including
its bound `10¹⁰(q+1)⁶`. -/
theorem itcs_component_prog {Pg : Program} {Ii : ItC1Idx} (h : ItC1Ok Pg Ii)
    (X Y : PairCfg q) (v : ℕ) (ha : ∃ a, 2 ≤ (X.comp v a).card)
    (E₀ : Subgroup (alternatingGroup (Fin q))) :
    ∃ (a : Fin q) (hne : itcsLab X v a ≠ a),
      FunDet Pg Ii.f (.list [encFun (itcsLab X v), encFun (itcsLab Y v)])
        (.list ((itcOsM (itcs_component_labels X v) (itcsLab Y v) hne E₀
          (itcMs (itcsLab X v) a)).map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2))
        (itC1C q) := by
  obtain ⟨a, ha⟩ := ha
  exact it_c1_prog h (itcs_component_labels X v) (itcs_component_labels Y v)
    (itcs_component_odd ha) E₀

end GI.Impl
