module

public import Workspace.Impl.GenNormGraph

@[expose] public section

/-!
# Computing the alternating generators needed by the normalized preimage
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

/-- On `m`, construct the all-one indicator and run the existing three-cycle generator. -/
def normAltF (rep cyc : ℕ) : Expr :=
  .letE (.call rep (mk2 (.var 0) (.nat 1))) (.call cyc (mk2 (.var 0) (.var 1)))

/-- Its own cost is polynomial in `m`. -/
def normAltCost (m : ℕ) : ℕ := 10 * cycGensCost m + 10 ^ 9 * (m + 1) ^ 4

/-- The whole alternating-generator list is computed with no cited call. -/
theorem normAlt_spec {Pg : Program} {f rep cyc m : ℕ}
    (hf : Pg.funs[f]? = some (normAltF rep cyc))
    (hrep : Pg.HasAt rep (replicateFuns rep)) (hcyc : Pg.HasAt cyc (cycGensFuns cyc)) :
    FunDet Pg f (.nat m) (.list ((normAltGens m).map encPerm)) (normAltCost m) := by
  have hones : (Val.list (List.replicate m (.nat 1))) = indT (Finset.univ : Finset (Fin m)) := by
    simp [indT, encFun, List.map_const', List.length_finRange]
  have wone := wt_nat_le 1
  have wm := wt_nat_le m
  have wrep := wt_list_le (List.replicate m (.nat 1))
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul, List.length_replicate] at wrep
  have wrep' : (Val.list (List.replicate m (.nat 1))).wt ≤ 7 * m + 4 := by
    have hmul := Nat.mul_le_mul_left m wone
    omega
  have warg := wt_list2_le (.nat m) (.nat 1)
  have hrep' : FunDet Pg rep (.list [.nat m, .nat 1]) (.list (List.replicate m (.nat 1)))
      (10 ^ 6 * (m + 1) ^ 3) := by
    refine FunAll.mono (replicate_spec hrep m (.nat 1)) fun w c hw => ⟨hw.1, ?_⟩
    have hc := hw.2
    rw [hw.1] at hc
    have h1 : loopModK * (m + 1) *
        ((Val.list [.nat m, .nat 1]).wt + m + (Val.list (List.replicate m (.nat 1))).wt + 1) ≤
        1000 * (m + 1) * (30 * (m + 1)) := by
      apply Nat.mul_le_mul_left
      omega
    have heq : 1000 * (m + 1) * (30 * (m + 1)) = 30000 * (m + 1) ^ 2 := by ring
    have h23 : (m + 1) ^ 2 ≤ (m + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [heq] at h1
    omega
  rw [hones] at hrep'
  have hcyc' := cycGens_spec hcyc (Finset.univ : Finset (Fin m))
  have hout : (Val.list ((List.range (m ^ 3)).map fun t => encPerm (genOf (Finset.univ : Finset (Fin m)) t))) =
      .list ((normAltGens m).map encPerm) := by simp only [normAltGens, List.map_map, Function.comp_def]
  rw [hout] at hcyc'
  have wo := hcyc'.wt_lt
  have d0 := Det.var' (P := Pg) (env := [Val.nat m]) (i := 0) rfl
  have drep := Det.call (Det.mk2 d0 (Det.nat 1)) hrep'
  have dcyc := Det.call (Det.mk2
    (Det.var' (P := Pg) (env := [.nat m, indT (Finset.univ : Finset (Fin m))]) (i := 0) rfl)
    (Det.var' (P := Pg) (env := [.nat m, indT (Finset.univ : Finset (Fin m))]) (i := 1) rfl)) hcyc'
  refine FunDet.intro hf ((Det.letE drep dcyc).mono ?_)
  rw [← hones] at *
  have warg2 := wt_list2_le (.nat m) (.list (List.replicate m (.nat 1)))
  have h34 : (m + 1) ^ 3 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h14 : m + 1 ≤ (m + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  unfold normAltCost
  omega

end GI.Impl
