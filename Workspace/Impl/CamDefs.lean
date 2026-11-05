module

public import Workspace.Impl.CamTransport

@[expose] public section

/-!
# The socle and its factors, read through a Maróti identification

For an identification `e` of the points with `r`-tuples of `k`-subsets of `Fin m`, `camHom e`
sends a tuple `h` of permutations of `Fin m` to the permutation of the points that acts by `h i`
in coordinate `i`. `camProd e S` is the image of `Alt(m)` in the coordinates of `S` (identity in
the others). So `camProd e univ` is the socle `Alt(m)^r`, `camProd e {i}` is its `i`-th simple
factor, and `camProd e {i}ᶜ` is the product of the other factors.
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n m k r : ℕ}

/-- The coordinatewise action of a tuple of permutations of `Fin m`, read through `e`. -/
def camHom (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) :
    (Fin r → Perm (Fin m)) →* Perm (Fin n) where
  toFun h := e.trans ((Equiv.piCongrRight fun i => kSetPerm (h i)).trans e.symm)
  map_one' := by
    refine Equiv.ext fun x => ?_
    change e.symm (fun i => kSetPerm (1 : Perm (Fin m)) (e x i)) = x
    simp [cam_kSetPerm_one]
  map_mul' a b := by
    ext x
    simp only [Equiv.trans_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
    congr 2
    funext i
    simp [cam_kSetPerm_mul]

theorem camHom_apply (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}))
    (h : Fin r → Perm (Fin m)) (x : Fin n) :
    e (camHom e h x) = fun i => kSetPerm (h i) (e x i) := by
  change e (e.symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The product of the factors `Alt(m)` in the coordinates of `S`. -/
def camProd (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) (S : Finset (Fin r)) :
    Subgroup (Perm (Fin n)) :=
  (Subgroup.pi Set.univ fun i => if i ∈ S then alternatingGroup (Fin m) else ⊥).map (camHom e)

end GI.Impl
