module

public import Workspace.Impl.LinObjectOffsetsCost
public import Workspace.Impl.LinObjectLiftAnswer

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

def linObjectOffsetsOut {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (refs : List (List (TmRiO n))) (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n)))) (out : Val) : Prop :=
  ∃ w : Fin (as.length * refs.length) → ℤ, out = linVecVal w ∧
    ∀ i : Fin refs.length, ∃ a : gens as,
      tmGlMs (refs.get i) ↼ a.val = partAt (gens as) Z (tmGlMs (refs.get i)) ∧
      linObjectLiftCoord as π (linObjectUnflatten refs.length as.length w i) = Additive.ofMul (π a)

def linMatrixCastRows {r s d : ℕ} (h : r = s) (M : Matrix (Fin r) (Fin d) ℤ) :
    Matrix (Fin s) (Fin d) ℤ := fun i => M (i.cast h.symm)

theorem linMatrixCastRows_encoding {r s d : ℕ} (h : r = s) (M : Matrix (Fin r) (Fin d) ℤ) :
    encIntMatrix (linMatrixCastRows h M) = encIntMatrix M := by
  subst s
  rfl

theorem linObjectOffsetsOut_of_rows {n : ℕ} {Q : Type*} [CommGroup Q]
    (as gs : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (refs : List (List (TmRiO n))) (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n))))
    (hgs : List.Forall₂ (fun S a => a ∈ gens as ∧ tmGlMs S ↼ a = partAt (gens as) Z (tmGlMs S)) refs gs)
    (M : Matrix (Fin gs.length) (Fin as.length) ℤ)
    (hM : ∀ i : Fin gs.length,
      linCoordHom (fun j : Fin as.length => π (linIntoSubgroup (gens as) as[j.val]))
        (Multiplicative.ofAdd (M i)) = π (linIntoSubgroup (gens as) gs[i.val])) :
    let C := linMatrixCastRows hgs.length_eq.symm M
    linObjectOffsetsOut as π refs Z (linVecVal ((linObjectUnflatten refs.length as.length).symm C)) := by
  let C := linMatrixCastRows hgs.length_eq.symm M
  refine ⟨(linObjectUnflatten refs.length as.length).symm C, rfl, ?_⟩
  intro i
  let j : Fin gs.length := i.cast hgs.length_eq
  have hh := hgs.get i.isLt j.isLt
  let a : gens as := ⟨gs.get j, hh.1⟩
  refine ⟨a, hh.2, ?_⟩
  set_option backward.isDefEq.respectTransparency false in
    rw [(linObjectUnflatten refs.length as.length).apply_symm_apply]
  have hm := congrArg Additive.ofMul (hM j)
  change linObjectLiftCoord as π (M j) = Additive.ofMul (π a)
  change linObjectLiftCoord as π (M j) = Additive.ofMul (π (linIntoSubgroup (gens as) (gs.get j))) at hm
  have ha : linIntoSubgroup (gens as) (gs.get j) = a := Subtype.ext
    (linIntoSubgroup_val (gens as) _ hh.1)
  exact hm.trans (congrArg (fun x => Additive.ofMul (π x)) ha)

end GI.Impl
