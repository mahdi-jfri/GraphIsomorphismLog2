import Workspace.SubdirectNormalizerStep
import Mathlib.Data.Fin.Tuple.Basic

namespace GI.PrimitiveProducts

variable {S I J : Type*} [Group S]

/-- Every actual coordinate projection of the subgroup is onto. -/
def Subdirect (H : Subgroup (I → S)) : Prop :=
  ∀ i : I, Function.Surjective (fun h : H => h.val i)

def tupleSplit (S : Type*) [Group S] (n : ℕ) :
    (Fin (n + 1) → S) ≃* S × (Fin n → S) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by cases p; rfl
  map_mul' _ _ := rfl

/-- Scott's self-normalizer lemma for subdirect subgroups of a finite
power of a nonabelian simple group, proved by actual coordinate induction. -/
theorem subdirect_normalizer_fin [IsSimpleGroup S]
    (nonabelian : ∃ x y : S, x * y ≠ y * x) :
    ∀ n : ℕ, ∀ H : Subgroup (Fin n → S), Subdirect H → (Subgroup.normalizer H) = H := by
  intro n
  induction n with
  | zero =>
    intro H _
    have htop : H = ⊤ := by
      apply top_le_iff.mp
      intro f _
      have hf : f = 1 := Subsingleton.elim _ _
      rw [hf]
      exact H.one_mem
    rw [htop, Subgroup.normalizer_eq_top]
  | succ n ih =>
    intro H hsub
    let e := tupleSplit S n
    let K := H.map e.toMonoidHom
    let L := K.map (MonoidHom.snd S (Fin n → S))
    have hhead : Function.Surjective (Prod.fst ∘ K.subtype) := by
      intro s
      obtain ⟨h, hh⟩ := hsub 0 s
      exact ⟨⟨e h.val, ⟨h.val, h.property, rfl⟩⟩, hh⟩
    have htail : Subdirect L := by
      intro i s
      obtain ⟨h, hh⟩ := hsub i.succ s
      exact ⟨⟨(e h.val).2, ⟨e h.val, ⟨h.val, h.property, rfl⟩, rfl⟩⟩, hh⟩
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_equiv_normalizer_eq]
    exact normalizer_eq_self_of_simple_first K hhead nonabelian (ih L htail)

def coordinateRelabel (S : Type*) [Group S] (e : I ≃ J) : (I → S) ≃* (J → S) where
  toFun f := f ∘ e.symm
  invFun f := f ∘ e
  left_inv f := by funext i; simp
  right_inv f := by funext j; simp
  map_mul' _ _ := rfl

/-- The finite-index version works with the actual factor index set;
reindexing to a finite tuple is constructed and then transported back. -/
theorem subdirect_normalizer [Fintype I] [IsSimpleGroup S]
    (nonabelian : ∃ x y : S, x * y ≠ y * x)
    (H : Subgroup (I → S)) (hsub : Subdirect H) : (Subgroup.normalizer H) = H := by
  let e := coordinateRelabel S (Fintype.equivFin I)
  let K := H.map e.toMonoidHom
  have hK : Subdirect K := by
    intro i s
    obtain ⟨h, hh⟩ := hsub ((Fintype.equivFin I).symm i) s
    exact ⟨⟨e h.val, ⟨h.val, h.property, rfl⟩⟩, hh⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_equiv_normalizer_eq]
  exact subdirect_normalizer_fin nonabelian _ K hK

end GI.PrimitiveProducts

#print axioms GI.PrimitiveProducts.subdirect_normalizer_fin
#print axioms GI.PrimitiveProducts.subdirect_normalizer
