module

public import Workspace.Proved.GMPLuksCentralizer
public import Workspace.Proved.NIntMath
public import Workspace.Lang.Prims.PermGroups

@[expose] public section

/-!
# Normal-subgroup centralizer task and two-stage kernel mathematics

For `I : NormalizedInst`, `gmpNormalCentralizerSubgroup I` is the centralizer of `gens I.ns` in
`gens I.gs`, and `GMPNormalCentralizerTask` / `GMPNormalCentralizer` are its polynomial-time task
specification.

We also connect Luks's two-stage centralizer construction (`GMPLuksStabilizers`, `GMPLuksAction`,
`GMPLuksCentralizer`) to the concrete `Subgroup (Perm (Fin n))` operations used by `pstabFuns`,
`kerFuns`, and `gmpFactorKernelFuns`:
* Stage 1 (`gmpFirstStageKer_normalizes_stab`): the kernel `K₁` of the action of `H` on the equality
  classes of `pointwiseStab N [i]` normalizes `pointwiseStab N [i]` for every `i : Fin n`, and
  contains `C_H(N)`.
* Stage 2 (`gmpPointwiseStab_index_le`, `gmpSecondStage_mem_iff`): each `pointwiseStab N [i]` has
  index at most `n` in `N`, and intersecting `{h ∈ K₁ : ∀ u ∈ N, h * u * h⁻¹ * u⁻¹ ∈ pointwiseStab N [i]}`
  over all `i : Fin n` yields `{h ∈ H : ∀ u ∈ N, h * u * h⁻¹ * u⁻¹ = 1}`.
-/

namespace GI.Proved

open GI.Algorithm GI.Cited GI.Lang Equiv

variable {n : ℕ}

/-- If `Normalizes H N` (`∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N`), then `H` lies in the normalizer
of `N`. -/
theorem gmp_normalizes_iff {H N : Subgroup (Perm (Fin n))} (hHN : Normalizes H N)
    {h : Perm (Fin n)} (hh : h ∈ H) (x : Perm (Fin n)) :
    h * x * h⁻¹ ∈ N ↔ x ∈ N := by
  have hmem : h ∈ Subgroup.normalizer (N : Set (Perm (Fin n))) :=
    nint_mem_normalizer (hHN h hh)
  exact (Subgroup.mem_normalizer_iff.mp hmem x).symm

/-- The centralizer of `gens I.ns` in `gens I.gs` for a `NormalizedInst`. -/
def gmpNormalCentralizerSubgroup (I : NormalizedInst) : Subgroup (Perm (Fin I.n)) where
  carrier := {h | h ∈ gens I.gs ∧ ∀ x ∈ gens I.ns, h * x * h⁻¹ * x⁻¹ = 1}
  one_mem' := ⟨(gens I.gs).one_mem, fun x _ => by group⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(gens I.gs).mul_mem ha hb, fun x hx => ?_⟩
    have h1 := ha' x hx
    have h2 := hb' x hx
    have hbx : b * x * b⁻¹ = x := by
      calc b * x * b⁻¹ = (b * x * b⁻¹ * x⁻¹) * x := by group
        _ = 1 * x := by rw [h2]
        _ = x := one_mul x
    calc (a * b) * x * (a * b)⁻¹ * x⁻¹
        = a * (b * x * b⁻¹) * a⁻¹ * x⁻¹ := by group
      _ = a * x * a⁻¹ * x⁻¹ := by rw [hbx]
      _ = 1 := h1
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(gens I.gs).inv_mem ha, fun x hx => ?_⟩
    have hnorm := nint_normalizer I.normalizes
    have ha_norm : a⁻¹ ∈ Subgroup.normalizer ((gens I.ns : Subgroup (Perm (Fin I.n))) : Set _) :=
      hnorm ((gens I.gs).inv_mem ha)
    have hy : a⁻¹ * x * a ∈ gens I.ns := by
      have h := (Subgroup.mem_normalizer_iff.mp ha_norm x).mp hx
      simpa using h
    have h1 := ha' (a⁻¹ * x * a) hy
    calc a⁻¹ * x * a⁻¹⁻¹ * x⁻¹
        = (a * (a⁻¹ * x * a) * a⁻¹ * (a⁻¹ * x * a)⁻¹)⁻¹ := by group
      _ = 1⁻¹ := by rw [h1]
      _ = 1 := inv_one

/-- **Normal-subgroup centralizer** (Luks 1993, Proposition 7.3; [LM, Theorem 3.1(viii)(a)]):
given `G` normalizing `N`, find `C_G(N)`. -/
def GMPNormalCentralizerTask : GI.Cited.Task NormalizedInst :=
  GI.Cited.Task.ofVal (fun I => .list [encGroup I.gs, encGroup I.ns])
    (fun I v => GensOf (gmpNormalCentralizerSubgroup I) v)

/-- Polynomial-time solvability of `GMPNormalCentralizerTask`. -/
def GMPNormalCentralizer : Prop := ∃ p, PolyTimeAt GMPNormalCentralizerTask p

/-- **Normal-subgroup centralizer** as a primitive. -/
noncomputable def gmpNormalCentralizerPrim (h : GMPNormalCentralizer) : Prim := Prim.ofHyp _ _ h

/-- The result of `gmpNormalCentralizerPrim`: generators of `C_H(N)` in `H`. -/
def GMPNormCentOut (H N : Subgroup (Perm (Fin n))) (w : Val) : Prop :=
  ∃ C, GensVal n w C ∧
    ∀ y, y ∈ C ↔ y ∈ H ∧ ∀ x ∈ N, y * x * y⁻¹ * x⁻¹ ∈ (⊥ : Subgroup (Perm (Fin n)))

theorem gmpNormalCentralizerPrim_spec (h : GMPNormalCentralizer) {hv nv : Val}
    {H N : Subgroup (Perm (Fin n))} (hH : GroupVal n hv H) (hN : GroupVal n nv N)
    (hHN : Normalizes H N) :
    PrimSpec (gmpNormalCentralizerPrim h) (.list [hv, nv]) (GMPNormCentOut H N) := by
  obtain ⟨gs, rfl, rfl⟩ := hH
  obtain ⟨ns, rfl, rfl⟩ := hN
  refine (Prim.ofHyp_spec h
    (⟨n, gs, ns, fun g hg => hHN g (Subgroup.subset_closure hg)⟩ : NormalizedInst) ?_).mono
    fun w hw => ⟨gmpNormalCentralizerSubgroup ⟨n, gs, ns, fun g hg => hHN g (Subgroup.subset_closure hg)⟩,
      hw, fun y => ?_⟩
  · rintro ⟨n', gs', ns', _⟩ hy
    simp only [Val.list.injEq, List.cons.injEq, and_true] at hy
    obtain rfl := encGroup_deg hy.1
    obtain rfl := encGroup_injective hy.1
    obtain rfl := encGroup_injective hy.2
    rfl
  · simp only [Subgroup.mem_bot]
    rfl

theorem gmpNormalCentralizer_call (h : GMPNormalCentralizer) {P : Program} {env : List Val}
    {j : ℕ} {a : Expr} {ca : ℕ} {hv nv : Val} {H N : Subgroup (Perm (Fin n))}
    (hj : P.prims[j]? = some (gmpNormalCentralizerPrim h))
    (ha : Det P env a (.list [hv, nv]) ca)
    (hH : GroupVal n hv H) (hN : GroupVal n nv N) (hHN : Normalizes H N) :
    EvalAll P env (.prim j a) (fun w c => GMPNormCentOut H N w ∧
      c ≤ ca + (gmpNormalCentralizerPrim h).bound (.list [hv, nv]) + 13 * (n + 1) ^ 6 + 1) :=
  EvalAll.prim_spec_le hj ha (gmpNormalCentralizerPrim_spec h hH hN hHN)
    fun w hw => by obtain ⟨_, hs, -⟩ := hw; exact GensVal.wt_le hs

/-- Membership in `pointwiseStab N [i]`. -/
theorem gmp_mem_pointwiseStab_singleton {N : Subgroup (Perm (Fin n))} {i : Fin n}
    {g : Perm (Fin n)} :
    g ∈ pointwiseStab N [i] ↔ g ∈ N ∧ g i = i := by
  simp [pointwiseStab]

/-- Equivalence of points having the same `N`-point stabilizer. -/
def gmpStabRel (N : Subgroup (Perm (Fin n))) (i j : Fin n) : Prop :=
  pointwiseStab N [i] = pointwiseStab N [j]

theorem gmpStabRel_equiv (N : Subgroup (Perm (Fin n))) : Equivalence (gmpStabRel N) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- Conjugating `pointwiseStab N [i]` by `h ∈ H` (when `Normalizes H N`) shifts the stabilized
point to `h i`. -/
theorem gmp_conj_mem_pointwiseStab_singleton {H N : Subgroup (Perm (Fin n))}
    (hHN : Normalizes H N) {h : Perm (Fin n)} (hh : h ∈ H) (i : Fin n) (g : Perm (Fin n)) :
    h * g * h⁻¹ ∈ pointwiseStab N [h i] ↔ g ∈ pointwiseStab N [i] := by
  rw [gmp_mem_pointwiseStab_singleton, gmp_mem_pointwiseStab_singleton,
    gmp_normalizes_iff hHN hh g]
  refine and_congr_right fun _ => ?_
  simp only [Perm.mul_apply, Perm.inv_apply_self, EmbeddingLike.apply_eq_iff_eq]

/-- Any normalizing subgroup `H` preserves the equality relation `gmpStabRel N` on point
stabilizers. -/
theorem gmpStabRel_pres {H N : Subgroup (Perm (Fin n))} (hHN : Normalizes H N) :
    ∀ g ∈ H, ∀ i j : Fin n, gmpStabRel N (g i) (g j) ↔ gmpStabRel N i j := by
  intro g hg i j
  unfold gmpStabRel
  constructor
  · intro h
    ext x
    rw [← gmp_conj_mem_pointwiseStab_singleton hHN hg i x, h,
      gmp_conj_mem_pointwiseStab_singleton hHN hg j x]
  · intro h
    ext y
    have hy : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [hy, gmp_conj_mem_pointwiseStab_singleton hHN hg i (g⁻¹ * y * g), h,
      ← gmp_conj_mem_pointwiseStab_singleton hHN hg j (g⁻¹ * y * g)]

/-- Any element `h ∈ H` with `pointwiseStab N [h i] = pointwiseStab N [i]` normalizes
`pointwiseStab N [i]`. -/
theorem gmpFirstStageKer_normalizes_stab {H N K₁ A : Subgroup (Perm (Fin n))}
    (hHN : Normalizes H N) (hK₁H : K₁ ≤ H)
    (hK₁ : ∀ h ∈ K₁, ∀ i : Fin n, pointwiseStab N [h i] = pointwiseStab N [i])
    (hAK₁ : A ≤ K₁) (i : Fin n) :
    Normalizes A (pointwiseStab N [i]) := by
  intro h hh g hg
  have hhK₁ : h ∈ K₁ := hAK₁ hh
  have hhH : h ∈ H := hK₁H hhK₁
  rw [← hK₁ h hhK₁ i]
  exact (gmp_conj_mem_pointwiseStab_singleton hHN hhH i g).mpr hg

/-- Every element that centralizes `N` lies in the first-stage kernel `K₁`. -/
theorem gmp_cent_mem_firstStageKer {N : Subgroup (Perm (Fin n))}
    {h : Perm (Fin n)} (hcent : ∀ u ∈ N, h * u * h⁻¹ * u⁻¹ = 1) (i : Fin n) :
    pointwiseStab N [h i] = pointwiseStab N [i] := by
  have hcomm : ∀ u ∈ N, h * u * h⁻¹ = u := by
    intro u hu
    calc h * u * h⁻¹ = (h * u * h⁻¹ * u⁻¹) * u := by group
      _ = 1 * u := by rw [hcent u hu]
      _ = u := one_mul u
  ext g
  rw [gmp_mem_pointwiseStab_singleton, gmp_mem_pointwiseStab_singleton]
  refine and_congr_right fun hgN => ?_
  have hgh : g (h i) = h (g i) := by
    have hc := hcomm g hgN
    have happ := congrArg (fun p : Perm (Fin n) => p (h i)) hc
    simpa [Perm.mul_apply] using happ.symm
  rw [hgh, EmbeddingLike.apply_eq_iff_eq]

/-- The subgroup `(pointwiseStab N [i]).subgroupOf N` equals `MulAction.stabilizer N i`. -/
theorem gmpPointwiseStab_subgroupOf_eq_stabilizer (N : Subgroup (Perm (Fin n))) (i : Fin n) :
    (pointwiseStab N [i]).subgroupOf N = MulAction.stabilizer N i := by
  ext x
  simp [Subgroup.mem_subgroupOf, gmp_mem_pointwiseStab_singleton, MulAction.mem_stabilizer_iff,
    Subgroup.smul_def]

/-- The index of `pointwiseStab N [i]` in `N` is at most `n`. -/
theorem gmpPointwiseStab_index_le (N : Subgroup (Perm (Fin n))) (i : Fin n) :
    ((pointwiseStab N [i]).subgroupOf N).index ≤ n := by
  rw [gmpPointwiseStab_subgroupOf_eq_stabilizer, Subgroup.index_eq_card,
    ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer N i)]
  have hle : Nat.card (MulAction.orbit N i) ≤ Nat.card (Fin n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  simpa using hle

/-- Characterizing the intersection of `{h ∈ K₁ : ∀ u ∈ N, h * u * h⁻¹ * u⁻¹ ∈ pointwiseStab N [j]}`
over all points `j : Fin n`. -/
theorem gmpSecondStage_mem_iff {H N K₁ A : Subgroup (Perm (Fin n))}
    (hK₁ : ∀ h, h ∈ K₁ ↔ h ∈ H ∧ ∀ i : Fin n, pointwiseStab N [h i] = pointwiseStab N [i])
    (hA : ∀ h, h ∈ A ↔ h ∈ K₁ ∧ ∀ j : Fin n, ∀ u ∈ N, h * u * h⁻¹ * u⁻¹ ∈ pointwiseStab N [j]) :
    ∀ h, h ∈ A ↔ h ∈ H ∧ ∀ u ∈ N, h * u * h⁻¹ * u⁻¹ = 1 := by
  intro h
  rw [hA, hK₁]
  constructor
  · rintro ⟨⟨hhH, _⟩, hpt⟩
    refine ⟨hhH, fun u hu => ?_⟩
    exact Equiv.ext fun j => (gmp_mem_pointwiseStab_singleton.mp (hpt j u hu)).2
  · rintro ⟨hhH, hcent⟩
    refine ⟨⟨hhH, gmp_cent_mem_firstStageKer hcent⟩, fun j u hu => ?_⟩
    rw [hcent u hu]
    exact (pointwiseStab N [j]).one_mem

end GI.Proved
