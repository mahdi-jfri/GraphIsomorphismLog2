/-
**The permutation-group algorithms of `Workspace.Cited.AlgoPermGroups` as primitives.**

For each task `X` the hypothesis `h : GI.Cited.X` gives the primitive `xPrim h` (by
`Prim.ofHyp`). Two lemmas describe it:
* `xPrim_spec`: on the value of an instance, written with the predicates of
  `Workspace.Lang.Prims.Repr` (for example `GroupVal n gv G`), the primitive may be called and
  every result encodes a correct output, stated about the objects (for example
  `GensVal n w (pointwiseStab G S)`);
* `x_call`: the same for a call `.prim j a` in a program holding the primitive at index `j`, in
  `EvalAll` form, with the cost `ca + (xPrim h).bound v + W + 1`, where `ca` bounds the cost
  of the argument, `(xPrim h).bound v = c * (v.size + 2) ^ k` for the constants of `h`, and `W`
  is a polynomial in `n` that bounds the weight of every correct result.

*Size of the results.* The tasks bound their outputs (`GI.Cited.GensOf`, `SeriesOf`,
`LabelsOf`), so every result has weight polynomial in the degree `n`: a generator list at most
`13 (n + 1)⁶` (`GensVal.wt_le`), a labeling at most `7 (n + 1)²` (`labels_wt_le`), a series at
most `100 (n + 1)⁸` (`SeriesVal.wt_le`), an order at most `n² + 3` (`wt_card_le`). The specs
whose result format does not carry the bound state it (`w.wt ≤ …`).

The proofs are the same for every task: the encoding of the instances is injective (the degree
is stored in every group encoding, `encGroup_deg`), so `Prim.ofHyp_spec` applies.
-/
module

public import Workspace.Lang.Prims.Basic

@[expose] public section

namespace GI.Lang

open GI.Cited
open Equiv

variable {n : ℕ}

/-! ### Membership -/

/-- **Membership** as a primitive. -/
noncomputable def membershipPrim (h : Membership) : Prim := Prim.ofHyp _ _ h

/-- The result of membership: `1` if `x ∈ G`, else `0`. -/
def MemberOut (G : Subgroup (Perm (Fin n))) (x : Perm (Fin n)) (w : Val) : Prop :=
  (w = .nat 1 ∧ x ∈ G) ∨ (w = .nat 0 ∧ x ∉ G)

theorem membershipPrim_spec (h : Membership) {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hG : GroupVal n gv G) (x : Perm (Fin n)) :
    PrimSpec (membershipPrim h) (.list [gv, encPerm x]) (MemberOut G x) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  exact Prim.ofHyp_spec h (⟨n, gs, x⟩ : MemberInst) (by
    rintro ⟨n', gs', x'⟩ hy
    simp only [Val.list.injEq, List.cons.injEq, and_true] at hy
    obtain rfl := encGroup_deg hy.1
    obtain rfl := encGroup_injective hy.1
    obtain rfl := encPerm_injective hy.2
    rfl)

theorem membership_call (h : Membership) {P : Program} {env : List Val} {j : ℕ} {a : Expr}
    {ca : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))} {x : Perm (Fin n)}
    (hj : P.prims[j]? = some (membershipPrim h)) (ha : Det P env a (.list [gv, encPerm x]) ca)
    (hG : GroupVal n gv G) :
    EvalAll P env (.prim j a) (fun w c => MemberOut G x w ∧
      c ≤ ca + (membershipPrim h).bound (.list [gv, encPerm x]) + 3 + 1) :=
  EvalAll.prim_spec_le hj ha (membershipPrim_spec h hG x) fun w hw => by
    rcases hw with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

/-! ### Order -/

/-- The injectivity of `encGroup` as an encoding of `GroupInst`. -/
theorem groupInst_inj (gs : List (Perm (Fin n))) :
    ∀ y : GroupInst, encGroup y.gs = encGroup gs → y = ⟨n, gs⟩ := by
  rintro ⟨n', gs'⟩ hy
  obtain rfl := encGroup_deg hy
  obtain rfl := encGroup_injective hy
  rfl

/-- **The order of a subgroup of `Sym(n)` as a value weighs at most `n² + 3`**: it is below
`2^(n² + 1)` (`GI.CitedChecks.card_lt_two_pow`), so it has at most `n² + 1` bits. -/
theorem wt_card_le (G : Subgroup (Perm (Fin n))) : (Val.nat (Nat.card G)).wt ≤ n ^ 2 + 3 := by
  rw [wt_nat]
  have := GI.Machine.len_le_iff.mpr (GI.CitedChecks.card_lt_two_pow G)
  omega

/-- **Order** as a primitive. -/
noncomputable def groupOrderPrim (h : GroupOrder) : Prim := Prim.ofHyp _ _ h

theorem groupOrderPrim_spec (h : GroupOrder) {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hG : GroupVal n gv G) : PrimSpec (groupOrderPrim h) gv (· = .nat (Nat.card G)) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  exact Prim.ofHyp_spec h (⟨n, gs⟩ : GroupInst) (groupInst_inj gs)

theorem groupOrder_call (h : GroupOrder) {P : Program} {env : List Val} {j : ℕ} {a : Expr}
    {ca : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hj : P.prims[j]? = some (groupOrderPrim h)) (ha : Det P env a gv ca) (hG : GroupVal n gv G) :
    Det P env (.prim j a) (.nat (Nat.card G)) (ca + (groupOrderPrim h).bound gv + n ^ 2 + 4) :=
  (Det.prim_spec hj ha (groupOrderPrim_spec h hG)).mono (by have := wt_card_le G; omega)

/-! ### Pointwise stabilizers -/

/-- **Pointwise stabilizer** as a primitive. -/
noncomputable def pointwiseStabPrim (h : PointwiseStab) : Prim := Prim.ofHyp _ _ h

theorem pointwiseStabPrim_spec (h : PointwiseStab) {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hG : GroupVal n gv G) (S : List (Fin n)) :
    PrimSpec (pointwiseStabPrim h) (.list [gv, encPts S])
      (fun w => GensVal n w (pointwiseStab G S)) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  exact Prim.ofHyp_spec h (⟨n, gs, S⟩ : PointsInst) (by
    rintro ⟨n', gs', S'⟩ hy
    simp only [Val.list.injEq, List.cons.injEq, and_true] at hy
    obtain rfl := encGroup_deg hy.1
    obtain rfl := encGroup_injective hy.1
    obtain rfl := encPts_injective hy.2
    rfl)

theorem pointwiseStab_call (h : PointwiseStab) {P : Program} {env : List Val} {j : ℕ}
    {a : Expr} {ca : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))} {S : List (Fin n)}
    (hj : P.prims[j]? = some (pointwiseStabPrim h)) (ha : Det P env a (.list [gv, encPts S]) ca)
    (hG : GroupVal n gv G) :
    EvalAll P env (.prim j a) (fun w c => GensVal n w (pointwiseStab G S) ∧
      c ≤ ca + (pointwiseStabPrim h).bound (.list [gv, encPts S]) + 13 * (n + 1) ^ 6 + 1) :=
  EvalAll.prim_spec_le hj ha (pointwiseStabPrim_spec h hG S)
    fun w hw => GensVal.wt_le hw

/-! ### Preimages -/

theorem sumToFin_injective {n' : ℕ} : Function.Injective (sumToFin (n := n) (n' := n')) := by
  intro a b hab
  ext x
  have := congrArg (fun σ : Perm (Fin (n + n')) => σ (finSumFinEquiv x)) hab
  simp only [sumToFin, Equiv.trans_apply, Equiv.symm_apply_apply] at this
  rw [finSumFinEquiv.injective this]

/-- The value of a preimage instance. -/
def preimageEnc (I : PreimageInst) : Val :=
  .list [.nat I.n, encGroup (I.ds.map sumToFin), encGroup I.ms]

/-- **Preimage** as a primitive. -/
noncomputable def preimagePrim (h : Preimage) : Prim := Prim.ofHyp _ _ h

theorem preimagePrim_spec (h : Preimage) (I : PreimageInst) :
    PrimSpec (preimagePrim h) (preimageEnc I)
      (fun w => GensVal I.n w (GI.CitedChecks.preimageSubgroup I)) := by
  refine (Prim.ofHyp_spec h I ?_).mono fun w hw => ?_
  · obtain ⟨n, n', ds, ms, p, q⟩ := I
    rintro ⟨n₂, n₂', ds₂, ms₂, p₂, q₂⟩ hy
    simp only [Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at hy
    obtain ⟨rfl, h2, h3⟩ := hy
    have e := encGroup_deg h2
    obtain rfl : n₂' = n' := by omega
    obtain rfl := (List.map_injective_iff.mpr sumToFin_injective) (encGroup_injective h2)
    obtain rfl := encGroup_injective h3
    rfl
  · obtain ⟨hs, rfl, hl, he⟩ := hw
    exact ⟨hs, rfl, hl, SetLike.coe_injective he⟩

theorem preimage_call (h : Preimage) {P : Program} {env : List Val} {j : ℕ} {a : Expr}
    {ca : ℕ} (I : PreimageInst) (hj : P.prims[j]? = some (preimagePrim h))
    (ha : Det P env a (preimageEnc I) ca) :
    EvalAll P env (.prim j a) (fun w c => GensVal I.n w (GI.CitedChecks.preimageSubgroup I) ∧
      c ≤ ca + (preimagePrim h).bound (preimageEnc I) + 13 * (I.n + 1) ^ 6 + 1) :=
  EvalAll.prim_spec_le hj ha (preimagePrim_spec h I)
    fun w hw => GensVal.wt_le hw

/-! ### Orbits and blocks -/

/-- **Orbits** as a primitive. -/
noncomputable def orbitsPrim (h : Orbits) : Prim := Prim.ofHyp _ _ h

theorem orbitsPrim_spec (h : Orbits) {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hG : GroupVal n gv G) :
    PrimSpec (orbitsPrim h) gv (fun w => OrbitVal n w G ∧ w.wt ≤ 7 * (n + 1) ^ 2) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  refine (Prim.ofHyp_spec h (⟨n, gs⟩ : GroupInst) (groupInst_inj gs)).mono fun w hw => ?_
  obtain ⟨lab, rfl, hlt, hlab⟩ := hw
  exact ⟨⟨lab, rfl, hlab⟩, labels_wt_le hlt⟩

theorem orbits_call (h : Orbits) {P : Program} {env : List Val} {j : ℕ} {a : Expr}
    {ca : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hj : P.prims[j]? = some (orbitsPrim h)) (ha : Det P env a gv ca) (hG : GroupVal n gv G) :
    EvalAll P env (.prim j a) (fun w c => (OrbitVal n w G ∧ w.wt ≤ 7 * (n + 1) ^ 2) ∧
      c ≤ ca + (orbitsPrim h).bound gv + 7 * (n + 1) ^ 2 + 1) :=
  EvalAll.prim_spec_le hj ha (orbitsPrim_spec h hG)
    fun w hw => hw.2

/-- **Minimal blocks** as a primitive. -/
noncomputable def minimalBlocksPrim (h : MinimalBlocks) : Prim := Prim.ofHyp _ _ h

/-- The result of minimal blocks: the labels of a minimal block system. -/
def BlocksOut (G : Subgroup (Perm (Fin n))) (w : Val) : Prop :=
  ∃ lab : Fin n → ℕ, w = encFun lab ∧ (∀ i, lab i < n) ∧ IsMinimalBlocks G lab

theorem BlocksOut.wt_le {G : Subgroup (Perm (Fin n))} {w : Val} (h : BlocksOut G w) :
    w.wt ≤ 7 * (n + 1) ^ 2 := by
  obtain ⟨lab, rfl, hlt, -⟩ := h
  exact labels_wt_le hlt

theorem minimalBlocksPrim_spec (h : MinimalBlocks) {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hG : GroupVal n gv G) (h2 : 2 ≤ n) (htr : ∀ i j : Fin n, ∃ g ∈ G, g i = j) :
    PrimSpec (minimalBlocksPrim h) gv (BlocksOut G) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  exact Prim.ofHyp_spec h (⟨n, gs, h2, htr⟩ : TransitiveInst) (by
    rintro ⟨n', gs', _, _⟩ hy
    obtain rfl := encGroup_deg hy
    obtain rfl := encGroup_injective hy
    rfl)

theorem minimalBlocks_call (h : MinimalBlocks) {P : Program} {env : List Val} {j : ℕ}
    {a : Expr} {ca : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hj : P.prims[j]? = some (minimalBlocksPrim h)) (ha : Det P env a gv ca)
    (hG : GroupVal n gv G) (h2 : 2 ≤ n) (htr : ∀ i j : Fin n, ∃ g ∈ G, g i = j) :
    EvalAll P env (.prim j a) (fun w c => BlocksOut G w ∧
      c ≤ ca + (minimalBlocksPrim h).bound gv + 7 * (n + 1) ^ 2 + 1) :=
  EvalAll.prim_spec_le hj ha (minimalBlocksPrim_spec h hG h2 htr)
    fun w hw => BlocksOut.wt_le hw

/-! ### Normal closures, derived subgroups and series -/

/-- **Normal closure** as a primitive. -/
noncomputable def normalClosurePrim (h : NormalClosure) : Prim := Prim.ofHyp _ _ h

theorem normalClosurePrim_spec (h : NormalClosure) {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hG : GroupVal n gv G) (hs : List (Perm (Fin n))) :
    PrimSpec (normalClosurePrim h) (.list [gv, encGroup hs]) (fun w => GensVal n w
      (Subgroup.closure {x | ∃ g ∈ G ⊔ gens hs, ∃ y ∈ hs, x = g * y * g⁻¹})) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  have e : gens (gs ++ hs) = gens gs ⊔ gens hs := by
    unfold gens
    rw [← Subgroup.closure_union]
    congr 1; ext g; simp
  refine (Prim.ofHyp_spec h (⟨n, gs, hs⟩ : TwoListInst) ?_).mono fun w hw => ?_
  · rintro ⟨n', gs', hs'⟩ hy
    simp only [Val.list.injEq, List.cons.injEq, and_true] at hy
    obtain rfl := encGroup_deg hy.1
    obtain rfl := encGroup_injective hy.1
    obtain rfl := encGroup_injective hy.2
    rfl
  · simpa only [GensVal, e] using hw

theorem normalClosure_call (h : NormalClosure) {P : Program} {env : List Val} {j : ℕ}
    {a : Expr} {ca : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))} {hs : List (Perm (Fin n))}
    (hj : P.prims[j]? = some (normalClosurePrim h)) (ha : Det P env a (.list [gv, encGroup hs]) ca)
    (hG : GroupVal n gv G) :
    EvalAll P env (.prim j a) (fun w c => GensVal n w
      (Subgroup.closure {x | ∃ g ∈ G ⊔ gens hs, ∃ y ∈ hs, x = g * y * g⁻¹}) ∧
      c ≤ ca + (normalClosurePrim h).bound (.list [gv, encGroup hs]) + 13 * (n + 1) ^ 6 + 1) :=
  EvalAll.prim_spec_le hj ha (normalClosurePrim_spec h hG hs)
    fun w hw => GensVal.wt_le hw

/-- **Derived subgroup** as a primitive. -/
noncomputable def derivedSubgroupPrim (h : DerivedSubgroup) : Prim := Prim.ofHyp _ _ h

theorem derivedSubgroupPrim_spec (h : DerivedSubgroup) {gv : Val}
    {G : Subgroup (Perm (Fin n))} (hG : GroupVal n gv G) :
    PrimSpec (derivedSubgroupPrim h) gv (fun w => GensVal n w ⁅G, G⁆) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  exact Prim.ofHyp_spec h (⟨n, gs⟩ : GroupInst) (groupInst_inj gs)

theorem derivedSubgroup_call (h : DerivedSubgroup) {P : Program} {env : List Val} {j : ℕ}
    {a : Expr} {ca : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hj : P.prims[j]? = some (derivedSubgroupPrim h)) (ha : Det P env a gv ca)
    (hG : GroupVal n gv G) :
    EvalAll P env (.prim j a) (fun w c => GensVal n w ⁅G, G⁆ ∧
      c ≤ ca + (derivedSubgroupPrim h).bound gv + 13 * (n + 1) ^ 6 + 1) :=
  EvalAll.prim_spec_le hj ha (derivedSubgroupPrim_spec h hG)
    fun w hw => GensVal.wt_le hw

theorem seriesOf_iff {P : List (Subgroup (Perm (Fin n))) → Prop} {w : Val} :
    SeriesOf P w ↔ ∃ Hs, SeriesVal n w Hs ∧ P Hs := by
  constructor
  · rintro ⟨L, rfl, h1, h2, hP⟩
    exact ⟨_, ⟨L, rfl, h1, h2, rfl⟩, hP⟩
  · rintro ⟨_, ⟨L, rfl, h1, h2, rfl⟩, hP⟩
    exact ⟨L, rfl, h1, h2, hP⟩

/-- **Composition series** as a primitive. -/
noncomputable def compositionSeriesPrim (h : CompositionSeriesAlgo) : Prim := Prim.ofHyp _ _ h

theorem compositionSeriesPrim_spec (h : CompositionSeriesAlgo) {gv : Val}
    {G : Subgroup (Perm (Fin n))} (hG : GroupVal n gv G) :
    PrimSpec (compositionSeriesPrim h) gv
      (fun w => ∃ Hs, SeriesVal n w Hs ∧ IsCompositionSeries G Hs) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  exact (Prim.ofHyp_spec h (⟨n, gs⟩ : GroupInst) (groupInst_inj gs)).mono
    fun w hw => seriesOf_iff.mp hw

theorem compositionSeries_call (h : CompositionSeriesAlgo) {P : Program} {env : List Val}
    {j : ℕ} {a : Expr} {ca : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hj : P.prims[j]? = some (compositionSeriesPrim h)) (ha : Det P env a gv ca)
    (hG : GroupVal n gv G) :
    EvalAll P env (.prim j a) (fun w c => (∃ Hs, SeriesVal n w Hs ∧ IsCompositionSeries G Hs) ∧
      c ≤ ca + (compositionSeriesPrim h).bound gv + 100 * (n + 1) ^ 8 + 1) :=
  EvalAll.prim_spec_le hj ha (compositionSeriesPrim_spec h hG)
    fun w hw => by obtain ⟨_, hs, -⟩ := hw; exact SeriesVal.wt_le hs

/-! ### Normalized subgroups -/

/-- `G` normalizes `N`. -/
def Normalizes (G N : Subgroup (Perm (Fin n))) : Prop := ∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N

/-- **Intersection with a normalized subgroup** as a primitive. -/
noncomputable def normalizedIntersectionPrim (h : NormalizedIntersection) : Prim :=
  Prim.ofHyp _ _ h

theorem normalizedIntersectionPrim_spec (h : NormalizedIntersection) {gv nv : Val}
    {G N : Subgroup (Perm (Fin n))} (hG : GroupVal n gv G) (hN : GroupVal n nv N)
    (hnorm : Normalizes G N) :
    PrimSpec (normalizedIntersectionPrim h) (.list [gv, nv]) (fun w => GensVal n w (G ⊓ N)) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  obtain ⟨ns, rfl, rfl⟩ := hN
  exact Prim.ofHyp_spec h (⟨n, gs, ns, fun g hg => hnorm g (Subgroup.subset_closure hg)⟩ :
    NormalizedInst) (by
      rintro ⟨n', gs', ns', _⟩ hy
      simp only [Val.list.injEq, List.cons.injEq, and_true] at hy
      obtain rfl := encGroup_deg hy.1
      obtain rfl := encGroup_injective hy.1
      obtain rfl := encGroup_injective hy.2
      rfl)

theorem normalizedIntersection_call (h : NormalizedIntersection) {P : Program} {env : List Val}
    {j : ℕ} {a : Expr} {ca : ℕ} {gv nv : Val} {G N : Subgroup (Perm (Fin n))}
    (hj : P.prims[j]? = some (normalizedIntersectionPrim h)) (ha : Det P env a (.list [gv, nv]) ca)
    (hG : GroupVal n gv G) (hN : GroupVal n nv N) (hnorm : Normalizes G N) :
    EvalAll P env (.prim j a) (fun w c => GensVal n w (G ⊓ N) ∧
      c ≤ ca + (normalizedIntersectionPrim h).bound (.list [gv, nv]) + 13 * (n + 1) ^ 6 + 1) :=
  EvalAll.prim_spec_le hj ha (normalizedIntersectionPrim_spec h hG hN hnorm)
    fun w hw => GensVal.wt_le hw

/-- **Factorization in a normalized product** as a primitive. -/
noncomputable def normalizedFactorPrim (h : NormalizedFactor) : Prim := Prim.ofHyp _ _ h

/-- The result of a factorization `x = g m`. -/
def FactorOut (G N : Subgroup (Perm (Fin n))) (x : Perm (Fin n)) (w : Val) : Prop :=
  ∃ g ∈ G, ∃ m ∈ N, x = g * m ∧ w = .list [encPerm g, encPerm m]

theorem FactorOut.wt_le {G N : Subgroup (Perm (Fin n))} {x : Perm (Fin n)} {w : Val}
    (h : FactorOut G N x w) : w.wt ≤ 22 * (n + 1) ^ 2 := by
  obtain ⟨g, -, m, -, -, rfl⟩ := h
  have := wt_list2_le (encPerm g) (encPerm m)
  have := wt_encPerm_le g
  have := wt_encPerm_le m
  have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem normalizedFactorPrim_spec (h : NormalizedFactor) {gv nv : Val}
    {G N : Subgroup (Perm (Fin n))} (hG : GroupVal n gv G) (hN : GroupVal n nv N)
    (hnorm : Normalizes G N) {x : Perm (Fin n)} (hx : ∃ g ∈ G, ∃ m ∈ N, x = g * m) :
    PrimSpec (normalizedFactorPrim h) (.list [gv, nv, encPerm x]) (FactorOut G N x) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  obtain ⟨ns, rfl, rfl⟩ := hN
  exact Prim.ofHyp_spec h (⟨n, gs, ns, fun g hg => hnorm g (Subgroup.subset_closure hg), x, hx⟩ :
    FactorInst) (by
      rintro ⟨n', gs', ns', _, x', _⟩ hy
      simp only [Val.list.injEq, List.cons.injEq, and_true] at hy
      obtain rfl := encGroup_deg hy.1
      obtain rfl := encGroup_injective hy.1
      obtain rfl := encGroup_injective hy.2.1
      obtain rfl := encPerm_injective hy.2.2
      rfl)

theorem normalizedFactor_call (h : NormalizedFactor) {P : Program} {env : List Val} {j : ℕ}
    {a : Expr} {ca : ℕ} {gv nv : Val} {G N : Subgroup (Perm (Fin n))} {x : Perm (Fin n)}
    (hj : P.prims[j]? = some (normalizedFactorPrim h))
    (ha : Det P env a (.list [gv, nv, encPerm x]) ca)
    (hG : GroupVal n gv G) (hN : GroupVal n nv N) (hnorm : Normalizes G N)
    (hx : ∃ g ∈ G, ∃ m ∈ N, x = g * m) :
    EvalAll P env (.prim j a) (fun w c => FactorOut G N x w ∧
      c ≤ ca + (normalizedFactorPrim h).bound (.list [gv, nv, encPerm x]) + 22 * (n + 1) ^ 2 + 1) :=
  EvalAll.prim_spec_le hj ha (normalizedFactorPrim_spec h hG hN hnorm hx)
    fun w hw => FactorOut.wt_le hw

/-! ### Coset intersections -/

/-- The result: `0` if `G x ∩ H` is empty, otherwise `[y, L]` with `y ∈ G x ∩ H` and `L`
generators of `G ∩ H`, so that `G x ∩ H = (G ∩ H) y`. -/
def CosetIntOut (G H : Subgroup (Perm (Fin n))) (x : Perm (Fin n)) (w : Val) : Prop :=
  (w = .nat 0 ∧ ∀ g ∈ G, g * x ∉ H) ∨
  ∃ y : Perm (Fin n), (∃ g ∈ G, y = g * x) ∧ y ∈ H ∧
    ∃ L, w = .list [encPerm y, L] ∧ GensVal n L (G ⊓ H)

theorem CosetIntOut.wt_le {G H : Subgroup (Perm (Fin n))} {x : Perm (Fin n)} {w : Val}
    (h : CosetIntOut G H x w) : w.wt ≤ 40 * (n + 1) ^ 6 := by
  have h1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  rcases h with ⟨rfl, -⟩ | ⟨y, -, -, L, rfl, hL⟩
  · have : (Val.nat 0).wt = 2 := by decide
    omega
  · have := wt_list2_le (encPerm y) L
    have := wt_encPerm_le y
    have := GensVal.wt_le hL
    have : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega

end GI.Lang
