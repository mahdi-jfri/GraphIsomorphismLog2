import Workspace.Impl.TermJProgTab
import Workspace.Impl.TermJVecList

/-!
# The coordinate vectors of the local generators (program)

The solve step needs, for every local generator `g_k` in the list `lg`, its coordinate vector
`β_k` in `A = ⟨σN⟩ / ⟨σS⟩`. The program reads the permutations off `tmJLgVal lg` and calls the
list version of the coordinate program (`tmJV_vecs_spec`).

`tmJ_beta_spec`: on `[encGroup ns, encGroup as, tmJLgVal lg]` the program returns
`.list (zs.map linVecVal)` with `zs` entrywise the coordinates of the `g_k`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens ConstructiveMembership)
open scoped IsMulCommutative

/-- On `[c, [a, g]]`: `g`. -/
def tmJLgPEF : Expr := .get (arg 1) (.nat 1)

theorem tmJ_lgPE_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJLgPEF) (c v : Val)
    (a : ℕ) :
    FunDet P f (.list [c, .list [.nat a, v]]) v
      (10 * ((Val.list [c, .list [.nat a, v]]).wt + 5)) := by
  refine FunDet.intro hf ?_
  have d1 := Det.arg' (P := P) (vs := [c, .list [.nat a, v]]) (rest := []) (j := 1)
    (v := .list [.nat a, v]) rfl
  refine (Det.get' d1 (Det.nat 1) (vs := [.nat a, v]) (v := v) rfl).mono ?_
  have h1 : (Val.list [.nat a, v]).wt < (Val.list [c, .list [.nat a, v]]).wt :=
    wt_le_wt_list (by simp)
  have h2 : v.wt < (Val.list [.nat a, v]).wt := wt_le_wt_list (by simp)
  omega

/-- On `[ns, as, lg]`: the coordinate vectors of the permutations of `lg`. -/
def tmJBetaF (mp vv : ℕ) : Expr :=
  .call vv (mk3 (arg 0) (arg 1) (.call mp (mk2 (arg 2) (arg 2))))

/-- The permutations of `lg` weigh at most about three times the list. -/
theorem tmJ_lgPerms_wt {m q : ℕ} (lg : List (Fin q × Perm (Fin m))) :
    (Val.list ((lg.map Prod.snd).map encPerm)).wt ≤ 3 * (tmJLgVal lg).wt + 4 := by
  have e : tmJLgVal lg = Val.list (lg.map fun p => Val.list [.nat p.1, encPerm p.2]) := rfl
  rw [e]
  have h1 := wt_list_le ((lg.map Prod.snd).map encPerm)
  have h2 := List.sum_le_sum (l := lg) (f := fun p => (encPerm p.2).wt)
    (g := fun p => (Val.list [.nat p.1, encPerm p.2]).wt)
    (fun p _ => (wt_le_wt_list (by simp)).le)
  have h3 := sum_wt_lt_wt_list (lg.map fun p => Val.list [.nat p.1, encPerm p.2])
  have h4 := length_lt_wt_list (lg.map fun p => Val.list [.nat p.1, encPerm p.2])
  simp only [List.map_map, Function.comp_def, List.length_map] at h1 h2 h3 h4 ⊢
  omega

/-- **The coordinate vectors of the local generators.** -/
theorem tmJ_beta_spec (hm : ConstructiveMembership) :
    ∃ K D : ℕ, ∀ {P : Program} {f mp e vv jm n q : ℕ},
      P.funs[f]? = some (tmJBetaF mp vv) → P.HasAt mp (mapFuns mp e) →
      P.funs[e]? = some tmJLgPEF →
      P.HasAt vv (tmJVVecsFuns vv jm) → P.prims[jm]? = some (linMembershipPrim hm) →
      ∀ (ns as : List (Equiv.Perm (Fin n))), gens ns ≤ gens as →
      ∀ [((gens ns).subgroupOf (gens as)).Normal]
        [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]
        (lg : List (Fin q × Perm (Fin n))), (∀ p ∈ lg, p.2 ∈ gens as) →
        FunAll P f (.list [encGroup ns, encGroup as, tmJLgVal lg]) (fun out cost =>
          (∃ zs : List (Fin as.length → ℤ), out = .list (zs.map linVecVal) ∧
            List.Forall₂ (fun u z =>
              Additive.ofMul (QuotientGroup.mk' ((gens ns).subgroupOf (gens as))
                (linIntoSubgroup (gens as) u)) =
              linCoordMap (fun i : Fin as.length =>
                QuotientGroup.mk' ((gens ns).subgroupOf (gens as))
                  (linIntoSubgroup (gens as) as[i.val])) z) (lg.map Prod.snd) zs) ∧
          cost ≤ K * ((Val.list [encGroup ns, encGroup as, tmJLgVal lg]).wt + 1) ^ D) := by
  obtain ⟨K0, D0, hv⟩ := tmJV_vecs_spec hm
  refine ⟨10 ^ 6 + 3 * K0 * 21 ^ D0, D0 + 3,
    fun {P f mp e vv jm n q} hf hmp he hvv hj ns as hle _ _ lg hlg => ?_⟩
  set W := (Val.list [encGroup ns, encGroup as, tmJLgVal lg]).wt with hW
  set L := tmJLgVal lg
  have wS : (encGroup ns).wt < W := wt_le_wt_list (by simp)
  have wA : (encGroup as).wt < W := wt_le_wt_list (by simp)
  have wL : L.wt < W := wt_le_wt_list (by simp; exact Or.inr (Or.inr rfl))
  have d0 := Det.arg' (P := P) (vs := [encGroup ns, encGroup as, L]) (rest := []) (j := 0)
    (v := encGroup ns) rfl
  have d1 := Det.arg' (P := P) (vs := [encGroup ns, encGroup as, L]) (rest := []) (j := 1)
    (v := encGroup as) rfl
  have d2 := Det.arg' (P := P) (vs := [encGroup ns, encGroup as, L]) (rest := []) (j := 2)
    (v := L) rfl
  have hB : ∀ p ∈ lg, 10 * ((Val.list [L, .list [.nat p.1, encPerm p.2]]).wt + 5) ≤
      10 * (2 * (W + W) + 11) := by
    intro p hp
    have := wt_list2_le L (.list [.nat p.1, encPerm p.2])
    have : (Val.list [.nat p.1, encPerm p.2]).wt < L.wt :=
      wt_le_wt_list (List.mem_map.2 ⟨p, hp, rfl⟩)
    omega
  have hM := mapList_spec hmp lg (fun p => .list [.nat p.1, encPerm p.2]) (fun p => encPerm p.2)
    (c := L) (fun p _ p' _ hpp => by
      have : encPerm p.2 = encPerm p'.2 := by simp_all
      exact this)
    (fun p hp => (tmJ_lgPE_spec he L (encPerm p.2) p.1).mono (hB p hp))
  have dmap := Det.call (Det.mk2 d2 d2) hM
  have hLv : Val.list (lg.map fun p => encPerm p.2) = Val.list ((lg.map Prod.snd).map encPerm) := by
    simp only [List.map_map]; rfl
  rw [hLv] at dmap
  have dargs := Det.mk3 d0 d1 dmap
  apply FunAll.intro hf
  apply EvalAll.call_funAll dargs
  rintro v ca ⟨rfl, hca⟩
  have eLL : Val.list [L, Val.list (lg.map fun p => Val.list [.nat p.1, encPerm p.2])] =
      Val.list [L, L] := rfl
  rw [eLL] at hca
  refine (hv hvv hj ns as hle (lg.map Prod.snd) (fun u hu => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hu
    exact hlg p hp)).wt_lt.mono fun out cost ho => ?_
  obtain ⟨⟨hz, hcost⟩, hwt⟩ := ho
  refine ⟨hz, ?_⟩
  -- the cost
  have wP := tmJ_lgPerms_wt lg
  have eL : (tmJLgVal lg).wt = L.wt := rfl
  have hlen := length_lt_wt_list (lg.map fun p => Val.list [.nat p.1, encPerm p.2])
  simp only [List.length_map] at hlen
  have hlen' : lg.length < L.wt := hlen
  have w3 := wt_list3_le (encGroup ns) (encGroup as) (.list ((lg.map Prod.snd).map encPerm))
  have w2 := wt_list2_le L L
  have hW1 : 1 ≤ W + 1 := by omega
  have hpow : ∀ i j, i ≤ j → (W + 1) ^ i ≤ (W + 1) ^ j := fun i j h =>
    Nat.pow_le_pow_right hW1 h
  -- the map
  have hmapc : lg.length * (10 * (2 * (W + W) + 11)) + mapK * (lg.length + 1) *
      ((Val.list [L, L]).wt + (Val.list ((lg.map Prod.snd).map encPerm)).wt + 1) ≤
      10 ^ 5 * (W + 1) ^ 2 := by
    have a1 : lg.length * (10 * (2 * (W + W) + 11)) ≤ (W + 1) * (110 * (W + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have a2 : mapK * (lg.length + 1) *
        ((Val.list [L, L]).wt + (Val.list ((lg.map Prod.snd).map encPerm)).wt + 1) ≤
        1000 * (W + 1) * (20 * (W + 1)) := by
      unfold mapK
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e1 : (W + 1) * (110 * (W + 1)) = 110 * (W + 1) ^ 2 := by ring
    have e2 : 1000 * (W + 1) * (20 * (W + 1)) = 20000 * (W + 1) ^ 2 := by ring
    omega
  -- the coordinate call
  have hW' : (Val.list [encGroup ns, encGroup as,
      .list ((lg.map Prod.snd).map encPerm)]).wt + 1 ≤ 21 * (W + 1) := by omega
  have hK : K0 * ((Val.list [encGroup ns, encGroup as,
      .list ((lg.map Prod.snd).map encPerm)]).wt + 1) ^ D0 ≤ K0 * 21 ^ D0 * (W + 1) ^ D0 := by
    rw [mul_assoc, ← mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW' _)
  have hD : (W + 1) ^ D0 ≤ (W + 1) ^ (D0 + 3) := hpow _ _ (by omega)
  have hD2 : (W + 1) ^ 2 ≤ (W + 1) ^ (D0 + 3) := hpow _ _ (by omega)
  have hD0 : (W + 1) ^ 0 ≤ (W + 1) ^ (D0 + 3) := hpow _ _ (by omega)
  simp only [pow_zero] at hD0
  have hKD := Nat.mul_le_mul_left (K0 * 21 ^ D0) hD
  have e3 : (10 ^ 6 + 3 * K0 * 21 ^ D0) * (W + 1) ^ (D0 + 3) =
      10 ^ 6 * (W + 1) ^ (D0 + 3) + 3 * (K0 * 21 ^ D0 * (W + 1) ^ (D0 + 3)) := by ring
  have hdm : 10 * (W + 1) ^ 2 ≤ 10 ^ 6 * (W + 1) ^ (D0 + 3) := by omega
  rw [e3]
  have hca' : ca ≤ 10 ^ 5 * (W + 1) ^ 2 + 200 * (W + 1) ^ 2 := by
    have h1 : (Val.list [encGroup ns, encGroup as,
        .list ((lg.map Prod.snd).map encPerm)]).wt ≤ 21 * (W + 1) := by omega
    have : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have : 10 ^ 5 * (W + 1) ^ 2 + 200 * (W + 1) ^ 2 + 1 ≤ 10 ^ 6 * (W + 1) ^ (D0 + 3) := by omega
  omega

end GI.Impl
