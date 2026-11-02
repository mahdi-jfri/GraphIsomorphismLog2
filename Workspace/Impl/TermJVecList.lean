import Workspace.Impl.TermJVec

/-!
# Coordinate vectors of a list of elements of `A = N / N*` (programs)

Two programs built on `tmJVVecF` (`TermJVec.lean`). Both take
`[encGroup ns, encGroup as, .list (us.map encPerm)]` with every `u ∈ us` in `⟨as⟩`.

* `tmJVVecsF` maps `tmJVVecF` over `us`: one coordinate vector per element
  (`tmJV_vecs_spec`).
* `tmJVSumF` first multiplies the permutations of `us` (a `foldl` of `compose`, starting from
  the identity), then computes one coordinate vector of the product. Since the coordinate map
  is a homomorphism, this vector represents the sum of the classes (`tmJV_sum_spec`).

Both costs are polynomial in the input weight. The only primitive used is constructive
membership, at index `jm`.
-/

namespace GI.Impl
open GI.Cited GI.Lang
open scoped IsMulCommutative

/-! ### Two list facts -/

/-- Read off the vectors from a list of results related entrywise to `us.map encPerm`. -/
theorem tmJV_extract {n t E : ℕ} (rel : Equiv.Perm (Fin n) → (Fin t → ℤ) → Prop)
    (us : List (Equiv.Perm (Fin n))) (ws : List Val)
    (h : List.Forall₂ (fun x w => ∃ z : Fin t → ℤ, w = linVecVal z ∧
      (∀ u, x = encPerm u → rel u z) ∧ w.wt ≤ E) (us.map encPerm) ws) :
    ∃ zs : List (Fin t → ℤ), ws = zs.map linVecVal ∧ List.Forall₂ rel us zs ∧
      ∀ w ∈ ws, w.wt ≤ E := by
  induction us generalizing ws with
  | nil =>
    obtain rfl := List.forall₂_nil_left_iff.mp h
    exact ⟨[], rfl, .nil, by simp⟩
  | cons u us ih =>
    rw [List.map_cons] at h
    obtain ⟨w, ws', ⟨z, rfl, hz, hw⟩, hws', rfl⟩ := List.forall₂_cons_left_iff.mp h
    obtain ⟨zs, rfl, hzs, hb⟩ := ih ws' hws'
    refine ⟨z :: zs, rfl, .cons (hz u rfl) hzs, ?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hw
    · exact hb v hv

/-- `linIntoSubgroup` is multiplicative on lists of members. -/
theorem tmJV_into_prod {G : Type*} [Group G] (A : Subgroup G) (us : List G)
    (hus : ∀ u ∈ us, u ∈ A) :
    (us.map (linIntoSubgroup A)).prod = linIntoSubgroup A us.prod := by
  apply A.subtype_injective
  rw [map_list_prod, linIntoSubgroup_map A us hus,
    linIntoSubgroup_val A _ (A.list_prod_mem hus)]

theorem tmJV_into_eq {G : Type*} [Group G] (A : Subgroup G) (x : G) (hx : x ∈ A) :
    linIntoSubgroup A x = ⟨x, hx⟩ :=
  A.subtype_injective (linIntoSubgroup_val A x hx)

/-! ### One vector per element -/

/-- The mapped function: on `[[encGroup ns, encGroup as], encPerm u]`, the vector of `u`. -/
def tmJVVecsElemF (vec : ℕ) : Expr :=
  .call vec (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))

/-- The main function: map `tmJVVecsElemF` over the list. -/
def tmJVVecsF (mp : ℕ) : Expr := .call mp (mk2 (mk2 (arg 0) (arg 1)) (arg 2))

/-- The functions, in order: main, the mapped function, the `map` module, and the vector block.
They sit at `b, …, b + 56`. -/
def tmJVVecsFuns (b jm : ℕ) : List Expr :=
  [tmJVVecsF (b + 2), tmJVVecsElemF (b + 5)] ++ mapFuns (b + 2) (b + 1) ++ tmJVVecFuns (b + 5) jm

theorem tmJVVecsFuns_length (b jm : ℕ) : (tmJVVecsFuns b jm).length = 57 := rfl

/-- Where the pieces sit. -/
structure TmJVVecsAt (P : Program) (b jm : ℕ) : Prop where
  main : P.funs[b]? = some (tmJVVecsF (b + 2))
  elem : P.funs[b + 1]? = some (tmJVVecsElemF (b + 5))
  map : P.HasAt (b + 2) (mapFuns (b + 2) (b + 1))
  vec : P.HasAt (b + 5) (tmJVVecFuns (b + 5) jm)

theorem TmJVVecsAt.of_hasAt {P : Program} {b jm : ℕ} (h : P.HasAt b (tmJVVecsFuns b jm)) :
    TmJVVecsAt P b jm where
  main := (h.block (gs := [tmJVVecsF (b + 2)]) 0 rfl).single
  elem := (h.block (gs := [tmJVVecsElemF (b + 5)]) 1 rfl).single
  map := h.block 2 rfl
  vec := h.block 5 rfl

/-- The cost bound of one call of the mapped function, given the constants `K0, D0` of
`tmJV_vec_spec_poly`. -/
def tmJVVecsElem (K0 D0 W : ℕ) : ℕ := 1000 * (W + 1) + 2 * (K0 * (6 * W + 8) ^ D0)

/-- The cost bound of `tmJVVecsF`. -/
def tmJVVecsBound (K0 D0 W : ℕ) : ℕ :=
  1000 * (W + 1) + 10 * (W * tmJVVecsElem K0 D0 W) +
    mapK * (W + 1) * (100 * (W + 1) + 10 * (W * tmJVVecsElem K0 D0 W))

theorem tmJVVecsBound_poly (K0 D0 : ℕ) : PBU (fun _ W _ => tmJVVecsBound K0 D0 W) := by
  have hE : PBU (fun _ W _ => tmJVVecsElem K0 D0 W) :=
    PBU.add (PBU.smul 1000 (PBU.addc PBU.W 1))
      (PBU.smul 2 (PBU.smul K0 (PBU.pow (PBU.addc (PBU.smul 6 PBU.W) 8) D0)))
  have hWE := PBU.smul 10 (PBU.mul PBU.W hE)
  exact PBU.add (PBU.add (PBU.smul 1000 (PBU.addc PBU.W 1)) hWE)
    (PBU.mul (PBU.smul mapK (PBU.addc PBU.W 1)) (PBU.add (PBU.smul 100 (PBU.addc PBU.W 1)) hWE))

/-- The weight of the input of one call of `tmJVVecF`, from the weight of the list input. -/
theorem tmJV_wt_elem {n : ℕ} (ns as : List (Equiv.Perm (Fin n))) (us : List (Equiv.Perm (Fin n)))
    (u : Equiv.Perm (Fin n)) (hu : u ∈ us) :
    (Val.list [encGroup ns, encGroup as, encPerm u]).wt + 1 ≤
      6 * (Val.list [encGroup ns, encGroup as, .list (us.map encPerm)]).wt + 8 := by
  have h3 := wt_list3_le (encGroup ns) (encGroup as) (encPerm u)
  have wS : (encGroup ns).wt < (Val.list [encGroup ns, encGroup as, .list (us.map encPerm)]).wt :=
    wt_le_wt_list (by simp)
  have wN : (encGroup as).wt < (Val.list [encGroup ns, encGroup as, .list (us.map encPerm)]).wt :=
    wt_le_wt_list (by simp)
  have wL : (Val.list (us.map encPerm)).wt <
      (Val.list [encGroup ns, encGroup as, .list (us.map encPerm)]).wt := wt_le_wt_list (by simp)
  have wu : (encPerm u).wt < (Val.list (us.map encPerm)).wt :=
    wt_le_wt_list (List.mem_map.mpr ⟨u, hu, rfl⟩)
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **One coordinate vector per element.** On `[encGroup ns, encGroup as, .list (us.map encPerm)]`
with every `u ∈ us` in `⟨as⟩`, every run returns `.list (zs.map linVecVal)` where `zs` matches
`us` entrywise: the image of `zs[i]` under the coordinate map is the class of `us[i]`. -/
theorem tmJV_vecs_spec (hm : ConstructiveMembership) :
    ∃ K D : ℕ, ∀ {P : Program} {b jm n : ℕ},
      P.HasAt b (tmJVVecsFuns b jm) → P.prims[jm]? = some (linMembershipPrim hm) →
      ∀ (ns as : List (Equiv.Perm (Fin n))), gens ns ≤ gens as →
      ∀ [((gens ns).subgroupOf (gens as)).Normal]
        [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]
        (us : List (Equiv.Perm (Fin n))), (∀ u ∈ us, u ∈ gens as) →
        FunAll P b (.list [encGroup ns, encGroup as, .list (us.map encPerm)]) (fun out cost =>
          (∃ zs : List (Fin as.length → ℤ), out = .list (zs.map linVecVal) ∧
            List.Forall₂ (fun u z =>
              Additive.ofMul (QuotientGroup.mk' ((gens ns).subgroupOf (gens as))
                (linIntoSubgroup (gens as) u)) =
              linCoordMap (fun i : Fin as.length =>
                QuotientGroup.mk' ((gens ns).subgroupOf (gens as))
                  (linIntoSubgroup (gens as) as[i.val])) z) us zs) ∧
          cost ≤ K * ((Val.list [encGroup ns, encGroup as, .list (us.map encPerm)]).wt + 1) ^ D) := by
  obtain ⟨K0, D0, hv⟩ := tmJV_vec_spec_poly hm
  obtain ⟨K, D, hb⟩ := tmJV_pbu_bound (tmJVVecsBound_poly K0 D0)
  refine ⟨K, D, fun {P b jm n} hl hj ns as hle _ _ us hus => ?_⟩
  have h := TmJVVecsAt.of_hasAt hl
  let L := Val.list (us.map encPerm)
  let c := Val.list [encGroup ns, encGroup as]
  let a := Val.list [encGroup ns, encGroup as, L]
  let W := a.wt
  let E := tmJVVecsElem K0 D0 W
  let rel : Equiv.Perm (Fin n) → (Fin as.length → ℤ) → Prop := fun u z =>
    Additive.ofMul (QuotientGroup.mk' ((gens ns).subgroupOf (gens as))
      (linIntoSubgroup (gens as) u)) =
    linCoordMap (fun i : Fin as.length => QuotientGroup.mk' ((gens ns).subgroupOf (gens as))
      (linIntoSubgroup (gens as) as[i.val])) z
  let R : Val → Val → Prop := fun x w => ∃ z : Fin as.length → ℤ, w = linVecVal z ∧
    (∀ u, x = encPerm u → rel u z) ∧ w.wt ≤ E
  have wS : (encGroup ns).wt < W := wt_le_wt_list (by simp)
  have wN : (encGroup as).wt < W := wt_le_wt_list (by simp)
  have wL : L.wt < W := wt_le_wt_list (by simp)
  have wc := wt_list2_le (encGroup ns) (encGroup as)
  -- one call of the mapped function
  have hf : ∀ x ∈ us.map encPerm, FunAll P (b + 1) (.list [c, x]) (fun w cost => R x w ∧ cost ≤ E) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    have hvu' := hv (h.vec) hj ns as hle u (hus u hu)
    have wu := tmJV_wt_elem ns as us u hu
    have wcx := wt_list2_le c (encPerm u)
    have wxl : (encPerm u).wt < L.wt := wt_le_wt_list (List.mem_map.mpr ⟨u, hu, rfl⟩)
    have hpow := Nat.mul_le_mul_left K0 (Nat.pow_le_pow_left wu D0)
    have d0 := Det.arg' (P := P) (vs := [c, encPerm u]) (rest := []) (j := 0) rfl
    have dargs := Det.mk3 (Det.get' d0 (Det.nat 0) (show [encGroup ns, encGroup as][0]? = _ from rfl))
      (Det.get' d0 (Det.nat 1) (show [encGroup ns, encGroup as][1]? = _ from rfl))
      (Det.arg' (P := P) (vs := [c, encPerm u]) (rest := []) (j := 1) rfl)
    have w3 := wt_list3_le (encGroup ns) (encGroup as) (encPerm u)
    apply FunAll.intro h.elem
    apply EvalAll.call_funAll dargs
    rintro v ca ⟨rfl, hca⟩
    refine hvu'.wt_lt.mono fun w cost ho => ?_
    obtain ⟨⟨⟨z, rfl, hz⟩, hcost⟩, hwt⟩ := ho
    have hrel : ∀ u', encPerm u = encPerm u' → rel u' z := by
      intro u' he
      obtain rfl := encPerm_injective he
      change _ = _
      rw [tmJV_into_eq (gens as) u (hus u hu)]
      exact hz
    refine ⟨⟨z, rfl, hrel, ?_⟩, ?_⟩
    · dsimp only [E, tmJVVecsElem]
      dsimp only [W, a, L, c] at *
      omega
    · dsimp only [E, tmJVVecsElem]
      dsimp only [W, a, L, c] at *
      omega
  have hmap := map_spec h.map hf
  have dargs := Det.mk2 (Det.mk2 (Det.arg' (P := P) (vs := [encGroup ns, encGroup as, L])
      (rest := []) (j := 0) rfl) (Det.arg' (P := P) (vs := [encGroup ns, encGroup as, L])
      (rest := []) (j := 1) rfl)) (Det.arg' (P := P) (vs := [encGroup ns, encGroup as, L])
      (rest := []) (j := 2) rfl)
  apply FunAll.intro h.main
  apply EvalAll.call_funAll dargs
  rintro v ca ⟨rfl, hca⟩
  refine hmap.mono fun w cost ho => ?_
  obtain ⟨ws, rfl, hws, hcost⟩ := ho
  obtain ⟨zs, rfl, hzs, hwb⟩ := tmJV_extract rel us _ hws
  refine ⟨⟨zs, rfl, hzs⟩, le_trans ?_ (hb W)⟩
  -- the cost
  have hlen : us.length ≤ W := by
    have := length_lt_wt_list (us.map encPerm)
    simp only [List.length_map] at this
    dsimp only [W, a, L] at *
    omega
  have hsum : ((us.map encPerm).map fun _ => E).sum = us.length * E := by
    simp only [List.map_map, Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul]
  have hwt := linWtList hwb
  have hzl : zs.length = us.length := hzs.length_eq.symm
  simp only [List.length_map, hzl] at hwt hcost
  rw [hsum] at hcost
  have hcL := wt_list2_le c L
  have h1 : us.length * E ≤ W * E := Nat.mul_le_mul_right E hlen
  have h2 : mapK * (us.length + 1) * ((Val.list [c, L]).wt +
      (Val.list ((zs.map linVecVal))).wt + 1) ≤
      mapK * (W + 1) * (100 * (W + 1) + 10 * (W * E)) := by
    apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
    dsimp only [W, a, L, c] at *
    omega
  have hwa := wt_list2_le c L
  unfold tmJVVecsBound
  change _ ≤ 1000 * (W + 1) + 10 * (W * E) + mapK * (W + 1) * (100 * (W + 1) + 10 * (W * E))
  dsimp only [W, a, L, c, E] at *
  omega

/-! ### One vector for the product -/

/-- The fold step: on `[c, acc, encPerm u]`, the product `acc * u`. -/
def tmJVSumStepF (comp : ℕ) : Expr := .call comp (mk2 (arg 1) (arg 2))

/-- The main function: fold the product from the identity (entry 0 of `encGroup as`), then
compute the vector of the product. -/
def tmJVSumF (fl vec : ℕ) : Expr :=
  .letE (.call fl (mk3 .nil (arg 2) (.get (.get (arg 1) (.nat 1)) (.nat 0))))
    (.call vec (mk3 (arg 0) (arg 1) (.var 1)))

/-- The functions, in order: main, the `foldl` module and its step, `compose`, and the vector
block. They sit at `b, …, b + 60`. -/
def tmJVSumFuns (b jm : ℕ) : List Expr :=
  [tmJVSumF (b + 1) (b + 9)] ++ foldlFuns (b + 1) (b + 4) ++ [tmJVSumStepF (b + 5)] ++
    composeFuns (b + 5) ++ tmJVVecFuns (b + 9) jm

theorem tmJVSumFuns_length (b jm : ℕ) : (tmJVSumFuns b jm).length = 61 := rfl

/-- Where the pieces sit. -/
structure TmJVSumAt (P : Program) (b jm : ℕ) : Prop where
  main : P.funs[b]? = some (tmJVSumF (b + 1) (b + 9))
  fold : P.HasAt (b + 1) (foldlFuns (b + 1) (b + 4))
  step : P.funs[b + 4]? = some (tmJVSumStepF (b + 5))
  comp : P.HasAt (b + 5) (composeFuns (b + 5))
  vec : P.HasAt (b + 9) (tmJVVecFuns (b + 9) jm)

theorem TmJVSumAt.of_hasAt {P : Program} {b jm : ℕ} (h : P.HasAt b (tmJVSumFuns b jm)) :
    TmJVSumAt P b jm where
  main := (h.block (gs := [tmJVSumF (b + 1) (b + 9)]) 0 rfl).single
  fold := h.block 1 rfl
  step := (h.block (gs := [tmJVSumStepF (b + 5)]) 4 rfl).single
  comp := h.block 5 rfl
  vec := h.block 9 rfl

/-- The cost bound of one fold step. -/
def tmJVSumStep (W : ℕ) : ℕ := 300 * (W + 1) ^ 2 + 100 + permK * (W + 1) ^ 3

/-- The cost bound of `tmJVSumF`, given the constants `K0, D0` of `tmJV_vec_spec_poly`. -/
def tmJVSumBound (K0 D0 W : ℕ) : ℕ :=
  1000 * (W + 1) ^ 2 + W * tmJVSumStep W + loopModK * (W + 1) * (100 * (W + 1) ^ 2) +
    3 * (K0 * (12 * (W + 1) ^ 2) ^ D0)

theorem tmJVSumBound_poly (K0 D0 : ℕ) : PBU (fun _ W _ => tmJVSumBound K0 D0 W) := by
  have hX : PBU (fun _ W _ => W + 1) := PBU.addc PBU.W 1
  have hS : PBU (fun _ W _ => tmJVSumStep W) :=
    PBU.add (PBU.addc (PBU.smul 300 (PBU.pow hX 2)) 100) (PBU.smul permK (PBU.pow hX 3))
  exact PBU.add (PBU.add (PBU.add (PBU.smul 1000 (PBU.pow hX 2)) (PBU.mul PBU.W hS))
    (PBU.mul (PBU.smul loopModK hX) (PBU.smul 100 (PBU.pow hX 2))))
    (PBU.smul 3 (PBU.smul K0 (PBU.pow (PBU.smul 12 (PBU.pow hX 2)) D0)))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **One coordinate vector for the whole list.** On
`[encGroup ns, encGroup as, .list (us.map encPerm)]` with every `u ∈ us` in `⟨as⟩`, every run
returns `linVecVal s` whose image under the coordinate map is the product of the classes of the
elements of `us`, that is, the sum of their coordinate images. -/
theorem tmJV_sum_spec (hm : ConstructiveMembership) :
    ∃ K D : ℕ, ∀ {P : Program} {b jm n : ℕ},
      P.HasAt b (tmJVSumFuns b jm) → P.prims[jm]? = some (linMembershipPrim hm) →
      ∀ (ns as : List (Equiv.Perm (Fin n))), gens ns ≤ gens as →
      ∀ [((gens ns).subgroupOf (gens as)).Normal]
        [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]
        (us : List (Equiv.Perm (Fin n))), (∀ u ∈ us, u ∈ gens as) →
        FunAll P b (.list [encGroup ns, encGroup as, .list (us.map encPerm)]) (fun out cost =>
          (∃ s : Fin as.length → ℤ, out = linVecVal s ∧
            Additive.ofMul ((us.map fun u => QuotientGroup.mk' ((gens ns).subgroupOf (gens as))
                (linIntoSubgroup (gens as) u)).prod) =
              linCoordMap (fun i : Fin as.length =>
                QuotientGroup.mk' ((gens ns).subgroupOf (gens as))
                  (linIntoSubgroup (gens as) as[i.val])) s) ∧
          cost ≤ K * ((Val.list [encGroup ns, encGroup as, .list (us.map encPerm)]).wt + 1) ^ D) := by
  obtain ⟨K0, D0, hv⟩ := tmJV_vec_spec_poly hm
  obtain ⟨K, D, hb⟩ := tmJV_pbu_bound (tmJVSumBound_poly K0 D0)
  refine ⟨K, D, fun {P b jm n} hl hj ns as hle _ _ us hus => ?_⟩
  have h := TmJVSumAt.of_hasAt hl
  let L := Val.list (us.map encPerm)
  let vs := [encGroup ns, encGroup as, L]
  let a := Val.list vs
  let W := a.wt
  let F := tmJVSumStep W
  have wS : (encGroup ns).wt < W := wt_le_wt_list (by simp [vs])
  have wN : (encGroup as).wt < W := wt_le_wt_list (by simp [vs])
  have wL : L.wt < W := wt_le_wt_list (by simp [vs])
  obtain ⟨hn, -, -⟩ := tmJV_source_bounds ns as (1 : Equiv.Perm (Fin n))
  have wn := S_le_wt_encGroup as
  have hnW : n + 1 ≤ W := by nlinarith
  have hW2 : 2 ≤ W := by
    have := (encGroup as).two_le_size.trans (encGroup as).size_le_wt
    omega
  have hsq : n + 1 ≤ W + 1 := by omega
  have p2 := Nat.pow_le_pow_left hsq 2
  have p3 := Nat.pow_le_pow_left hsq 3
  have hWsq : 4 * W + 8 ≤ 4 * (W + 1) ^ 2 := by nlinarith
  have hWsq' : W + 1 ≤ (W + 1) ^ 2 := by nlinarith
  have hp : us.prod ∈ gens as := (gens as).list_prod_mem hus
  -- the fold
  have hfold := foldl_spec h.fold (c := .list []) (xs := us.map encPerm)
    (acc0 := encPerm (1 : Equiv.Perm (Fin n)))
    (Inv := fun i acc => acc = encPerm (us.take i).prod) (M := 4 * (n + 1) ^ 2)
    (B := fun _ => F) (by simp) (by rintro i acc - rfl; exact wt_encPerm_le _) (by
      rintro i acc hi rfl
      have hi' : i < us.length := by simpa using hi
      have hx : (us.map encPerm)[i] = encPerm us[i] := by simp
      rw [hx]
      have wa := wt_encPerm_le (us.take i).prod
      have wx := wt_encPerm_le us[i]
      have wo := wt_encPerm_le ((us.take i).prod * us[i])
      have w3 := wt_list3_le (.list []) (encPerm (us.take i).prod) (encPerm us[i])
      have w2 := wt_list2_le (encPerm (us.take i).prod) (encPerm us[i])
      have wnil : (Val.list []).wt = 4 := rfl
      apply FunAll.intro h.step
      apply EvalAll.call_funAll (Det.mk2
        (Det.arg' (P := P) (vs := [.list [], encPerm (us.take i).prod, encPerm us[i]])
          (rest := []) (j := 1) rfl)
        (Det.arg' (P := P) (vs := [.list [], encPerm (us.take i).prod, encPerm us[i]])
          (rest := []) (j := 2) rfl))
      rintro v ca ⟨rfl, hca⟩
      refine FunAll.mono (compose_spec h.comp (us.take i).prod us[i]) fun w cost ho => ?_
      obtain ⟨rfl, hc⟩ := ho
      refine ⟨?_, ?_⟩
      · show encPerm ((us.take i).prod * us[i]) = encPerm (us.take (i + 1)).prod
        rw [List.prod_take_succ us i hi']
      · have hk := Nat.mul_le_mul_left permK p3
        dsimp only [F, tmJVSumStep]
        omega)
  have dfa := Det.mk3 (P := P) (env := [a]) Det.nil
    (Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl)
    (Det.get' (Det.get' (Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl) (Det.nat 1)
      (show [Val.nat n, .list ((1 :: as).map encPerm)][1]? = some (.list ((1 :: as).map encPerm))
        from rfl)) (Det.nat 0) (show ((1 :: as).map encPerm)[0]? = some (encPerm 1) from rfl))
  have hlen : us.length ≤ W := by
    have := length_lt_wt_list (us.map encPerm)
    simp only [List.length_map] at this
    change us.length < L.wt at this
    omega
  have wf := wt_list3_le (.list []) L (encPerm (1 : Equiv.Perm (Fin n)))
  have wg1 : (Val.list ((1 :: as).map encPerm)).wt < (encGroup as).wt := wt_le_wt_list (by simp)
  have we1 := wt_encPerm_le (1 : Equiv.Perm (Fin n))
  have wnil : (Val.list []).wt = 4 := rfl
  have hLF : us.length * F ≤ W * F := Nat.mul_le_mul_right F hlen
  have hloop : loopModK * ((us.map encPerm).length + 1) *
      ((Val.list [.list [], L, encPerm (1 : Equiv.Perm (Fin n))]).wt + (us.map encPerm).length +
        4 * (n + 1) ^ 2 + 1) ≤ loopModK * (W + 1) * (100 * (W + 1) ^ 2) := by
    simp only [List.length_map]
    apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
    omega
  apply FunAll.intro h.main
  apply EvalAll.letE (EvalAll.call_funAll dfa (Q := fun pv cp =>
      pv = encPerm us.prod ∧ cp ≤ 100 * (W + 1) ^ 2 + W * F +
        loopModK * (W + 1) * (100 * (W + 1) ^ 2)) (fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine hfold.mono fun w cost ho => ?_
    obtain ⟨hw, hc⟩ := ho
    simp only [List.length_map, List.take_length] at hw
    subst hw
    refine ⟨rfl, ?_⟩
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map] at hc hloop
    have wo := wt_encPerm_le us.prod
    dsimp only [W, a, vs, L] at *
    omega))
  rintro pv cp ⟨rfl, hcp⟩
  have dva := Det.mk3 (Det.arg' (P := P) (vs := vs) (rest := [encPerm us.prod]) (j := 0) rfl)
    (Det.arg' (P := P) (vs := vs) (rest := [encPerm us.prod]) (j := 1) rfl)
    (Det.var' (P := P) (env := [a, encPerm us.prod]) (i := 1) rfl)
  apply EvalAll.call_funAll dva
  rintro v ca ⟨rfl, hca⟩
  refine (hv h.vec hj ns as hle us.prod hp).wt_lt.mono fun w cost ho => ?_
  obtain ⟨⟨⟨z, rfl, hz⟩, hcost⟩, hwt⟩ := ho
  refine ⟨⟨z, rfl, ?_⟩, ?_⟩
  · rw [← hz]
    congr 1
    calc (us.map fun u => QuotientGroup.mk' ((gens ns).subgroupOf (gens as))
            (linIntoSubgroup (gens as) u)).prod
        = ((us.map (linIntoSubgroup (gens as))).map
            (QuotientGroup.mk' ((gens ns).subgroupOf (gens as)))).prod := by rw [List.map_map]; rfl
      _ = QuotientGroup.mk' ((gens ns).subgroupOf (gens as))
            (us.map (linIntoSubgroup (gens as))).prod := (map_list_prod _ _).symm
      _ = _ := by rw [tmJV_into_prod _ _ hus, tmJV_into_eq _ _ hp]
  · refine le_trans ?_ (hb W)
    have w3 := wt_list3_le (encGroup ns) (encGroup as) (encPerm us.prod)
    have wp := wt_encPerm_le us.prod
    have hpw : (Val.list [encGroup ns, encGroup as, encPerm us.prod]).wt + 1 ≤ 12 * (W + 1) ^ 2 := by
      dsimp only [W, a, vs, L] at *
      omega
    have hpow := Nat.mul_le_mul_left K0 (Nat.pow_le_pow_left hpw D0)
    unfold tmJVSumBound
    dsimp only [F, W, a, vs, L] at *
    omega

end GI.Impl
