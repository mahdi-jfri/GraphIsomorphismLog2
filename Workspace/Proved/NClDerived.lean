module

public import Workspace.Impl.NClDerProg
public import Workspace.Proved.NClNormal

@[expose] public section

/-!
# The derived subgroup from the normal closure

`derivedSubgroup_of`: the normal closure algorithm gives a polynomial-time algorithm for
`DerivedSubgroupTask`. For `G = ⟨gs⟩` the program forms the commutators `[a, b]`,
`a, b ∈ 1 :: gs`, and returns the normal closure of their group in `G` (Luks 1993, DIMACS 11,
item (3.12), p. 145). This is `[G, G]` by `derived_eq_ncl` (`Impl/NClDerMath.lean`).

`GI.Proved.derivedSubgroup` applies it to `GI.Proved.normalClosure`.
-/

namespace GI.Impl

open GI.Cited GI.Lang Equiv

/-- The constant of the cost. -/
noncomputable def derK (h : NormalClosure) : ℕ :=
  10 ^ 8 + (normalClosurePrim h).c * 200 ^ (normalClosurePrim h).k

/-- The degree of the cost. -/
noncomputable def derD (h : NormalClosure) : ℕ := 4 * (normalClosurePrim h).k + 6

theorem der_cost_poly (h : NormalClosure) {Y : ℕ} (hY : 1 ≤ Y) :
    10 ^ 8 * Y ^ 6 + (normalClosurePrim h).c * (200 * Y ^ 4) ^ (normalClosurePrim h).k ≤
      derK h * Y ^ derD h := by
  set c := (normalClosurePrim h).c
  set k := (normalClosurePrim h).k
  have e : c * (200 * Y ^ 4) ^ k = c * 200 ^ k * Y ^ (4 * k) := by rw [mul_pow, ← pow_mul]; ring
  have h1 : Y ^ (4 * k) ≤ Y ^ derD h := Nat.pow_le_pow_right hY (by unfold derD; omega)
  have h2 : Y ^ 6 ≤ Y ^ derD h := Nat.pow_le_pow_right hY (by unfold derD; omega)
  have h3 := Nat.mul_le_mul_left (c * 200 ^ k) h1
  have e2 : derK h * Y ^ derD h = 10 ^ 8 * Y ^ derD h + c * 200 ^ k * Y ^ derD h := by
    unfold derK; ring
  rw [e, e2]
  omega

/-- **The program.** -/
noncomputable def derProgram (h : NormalClosure) : Program :=
  ⟨derFuns 0 0, [normalClosurePrim h]⟩

theorem derProgram_at (h : NormalClosure) : DerAt (derProgram h) 0 0 h := by
  refine derAt_of ?_ rfl
  have hA := Program.hasAt_append [] (derFuns 0 0) [] [normalClosurePrim h]
  simpa [derProgram] using hA

/-- **The derived subgroup from the normal closure.** -/
theorem derivedSubgroup_of (h : NormalClosure) : DerivedSubgroup := by
  refine polyTimeAt_ofVal_of_lang_cells (derProgram h) 0 (derK h) (derD h) 1 1
    (fun I => cam_encGroup_cells I.gs) fun I => ?_
  exact FunAll.mono (derEntry_spec (derProgram_at h) I.gs) fun v c hv =>
    ⟨hv.1, hv.2.trans (der_cost_poly h (by omega))⟩

end GI.Impl

namespace GI.Proved

/-- **Derived subgroup** (`GI.Cited.DerivedSubgroup`), proved from the normal closure, which is
proved from membership. -/
theorem derivedSubgroup : GI.Cited.DerivedSubgroup :=
  GI.Impl.derivedSubgroup_of GI.Proved.normalClosure

end GI.Proved
