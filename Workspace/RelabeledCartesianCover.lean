import Workspace.CartesianFiberCover

namespace GI.CartesianCover

variable {V I D : Type*}

/-- An actual coordinate equivalence and actual position homomorphism
produce the CartesianCover on the conjugated permutation subgroup. -/
noncomputable def ofRelabeledFiberInvariance (H : Subgroup (Equiv.Perm V))
    (e : V ≃ (I → D)) (p : H →* Equiv.Perm I)
    (fibers : ∀ (h : H) i x y, e x i = e y i →
      e ((h : Equiv.Perm V) x) (p h i) = e ((h : Equiv.Perm V) y) (p h i)) :
    CartesianCover (H.map (relabelPerm e).toMonoidHom) := by
  let q := (relabelPerm e).subgroupMap H
  let p' := p.comp q.symm.toMonoidHom
  apply ofFiberInvariance p'
  intro k i x y hxy
  let h := q.symm k
  have hk : q h = k := q.apply_symm_apply k
  have hval : (k : Equiv.Perm (I → D)) = relabelPerm e (h : Equiv.Perm V) :=
    congrArg (fun z : H.map (relabelPerm e).toMonoidHom => (z : Equiv.Perm (I → D))) hk.symm
  change ((k : Equiv.Perm (I → D)) x) (p h i) = ((k : Equiv.Perm (I → D)) y) (p h i)
  rw [hval]
  change e ((h : Equiv.Perm V) (e.symm x)) (p h i) =
    e ((h : Equiv.Perm V) (e.symm y)) (p h i)
  apply fibers h i (e.symm x) (e.symm y)
  simpa only [e.apply_symm_apply] using hxy

end GI.CartesianCover

#print axioms GI.CartesianCover.ofRelabeledFiberInvariance
