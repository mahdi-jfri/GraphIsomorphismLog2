import Workspace.SubdirectNormalizer

namespace GI.PrimitiveProducts

variable {S I J : Type*} [Group S] [DecidableEq I] [DecidableEq J]

def HasFullFactor (H : Subgroup (I → S)) (i : I) : Prop :=
  ∀ s : S, Pi.mulSingle i s ∈ H

def NoFullFactors (H : Subgroup (I → S)) : Prop := ∀ i, ¬ HasFullFactor H i

def factorInclusion (H : Subgroup (I → S)) (i : I) (hi : HasFullFactor H i) : S →* H :=
  (MonoidHom.mulSingle (fun _ : I => S) i).codRestrict H hi

theorem factorInclusion_injective (H : Subgroup (I → S)) (i : I)
    (hi : HasFullFactor H i) : Function.Injective (factorInclusion H i hi) := by
  intro s t he
  have h := congrArg (fun z : H => z.val i) he
  simpa only [factorInclusion, MonoidHom.codRestrict_apply,
    MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same] using h

theorem factorInclusion_commute (H : Subgroup (I → S)) (i j : I)
    (hi : HasFullFactor H i) (hj : HasFullFactor H j) (hne : i ≠ j) (s t : S) :
    Commute (factorInclusion H i hi s) (factorInclusion H j hj t) := by
  apply Subtype.ext
  exact Pi.mulSingle_commute (f := fun _ : I => S) hne s t

theorem coordinateRelabel_single (e : I ≃ J) (i : I) (s : S) :
    coordinateRelabel S e (Pi.mulSingle i s) = Pi.mulSingle (e i) s := by
  funext j
  by_cases hj : j = e i
  · subst j
    rw [Pi.mulSingle_eq_same]
    change Pi.mulSingle (M := fun _ : I => S) i s (e.symm (e i)) = s
    rw [e.symm_apply_apply, Pi.mulSingle_eq_same]
  · have hi : e.symm j ≠ i := fun h => hj (by rw [← h, e.apply_symm_apply])
    simp only [coordinateRelabel, MulEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply,
      Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hj]

theorem hasFullFactor_relabel (H : Subgroup (I → S)) (e : I ≃ J) (i : I) :
    HasFullFactor (H.map (coordinateRelabel S e).toMonoidHom) (e i) ↔ HasFullFactor H i := by
  constructor
  · intro h s
    obtain ⟨x, hx, he⟩ := h s
    have hxeq : x = Pi.mulSingle i s := by
      apply (coordinateRelabel S e).injective
      rw [coordinateRelabel_single]
      exact he
    exact hxeq ▸ hx
  · intro h s
    exact ⟨Pi.mulSingle i s, h s, coordinateRelabel_single e i s⟩

theorem noFullFactors_relabel (H : Subgroup (I → S)) (e : I ≃ J)
    (hH : NoFullFactors H) : NoFullFactors (H.map (coordinateRelabel S e).toMonoidHom) := by
  intro j hj
  obtain ⟨i, rfl⟩ := e.surjective j
  exact hH i ((hasFullFactor_relabel H e i).mp hj)

omit [DecidableEq I] [DecidableEq J] in
theorem subdirect_relabel (H : Subgroup (I → S)) (e : I ≃ J) (hH : Subdirect H) :
    Subdirect (H.map (coordinateRelabel S e).toMonoidHom) := by
  intro j s
  obtain ⟨h, hh⟩ := hH (e.symm j) s
  exact ⟨⟨coordinateRelabel S e h.val, ⟨h.val, h.property, rfl⟩⟩, hh⟩

theorem tupleSplit_single_zero (n : ℕ) (s : S) :
    tupleSplit S n (Pi.mulSingle 0 s) = (s, 1) := by
  apply Prod.ext
  · simp [tupleSplit]
  · funext i
    simp [tupleSplit, Pi.mulSingle_apply]

theorem tupleSplit_single_succ (n : ℕ) (i : Fin n) (s : S) :
    tupleSplit S n (Pi.mulSingle i.succ s) = (1, Pi.mulSingle i s) := by
  apply Prod.ext
  · simp [tupleSplit, Pi.mulSingle_apply]
  · funext j
    simp [tupleSplit, Pi.mulSingle_apply]

end GI.PrimitiveProducts

#print axioms GI.PrimitiveProducts.HasFullFactor
#print axioms GI.PrimitiveProducts.NoFullFactors
#print axioms GI.PrimitiveProducts.factorInclusion
#print axioms GI.PrimitiveProducts.factorInclusion_injective
#print axioms GI.PrimitiveProducts.factorInclusion_commute
#print axioms GI.PrimitiveProducts.coordinateRelabel_single
#print axioms GI.PrimitiveProducts.hasFullFactor_relabel
#print axioms GI.PrimitiveProducts.noFullFactors_relabel
#print axioms GI.PrimitiveProducts.subdirect_relabel
#print axioms GI.PrimitiveProducts.tupleSplit_single_zero
#print axioms GI.PrimitiveProducts.tupleSplit_single_succ
