import Workspace.Impl.LargestOrbit

/-!
# The faithful image on the domain, and lifting answers back

Algorithm 5, `Solve`: "Use the faithful action and jointly compressed colors on `Ω`", and
Section 3: "Every fresh call uses the faithful permutation image on its own active domain … Its
caller retains the homomorphism used to lift the returned generators and representative."

Both steps of `Solve` (`Run.direct` and `Run.fresh`) work on the active domain `D`. A program
sees the positions `0, …, k - 1` of `Ω` (through `e : Ω ≃ Fin k`); the domain is the list of
positions `p₀ < p₁ < … < p_{s-1}` whose indicator is `1` (`domFin`), and the point `p_j` of the
domain becomes the position `j` of the domain (`domEquiv`). This file is the mathematics of the
two programs (`Workspace/Impl/DomRestrict.lean`, `Workspace/Impl/Lift.lean`):

* `domEquiv e D : D ≃ Fin s`, with `s` the length of `domFin e D`; the position of a point of
  the domain is found by searching the list (`posOf`).
* `restrK e G D hD : groupFin e G →* Perm (Fin s)`: the restriction to the domain, read on the
  positions; `restrK_apply` says how a program computes it (two table lookups), and `restrP` is
  the same map on all permutations (`1` outside the group).
* `closure_map_list`: generators are mapped to generators of the image.
* **Lifting.** The answer of the restricted instance is a coset `x' K'` of permutations of the
  domain. Its preimage under the restriction is computed with the cited preimage algorithm on
  the graph group `{g ⊕ g|_D}` (`liftInst`, `preimageSet_liftInst`), and a preimage `a` of `x'`
  with the cited factorization in the product of the graph group and `G ⊕ 1`, which it
  normalizes (`normalizes_graph`, `factor_lift`). `image_liftAnswer_coset` says that the result
  `a · ⟨preimage⟩` is the image of the lifted answer.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens sumToFin PreimageInst preimageSet)
open scoped Pointwise

variable {Ω : Type} {k : ℕ}

/-! ### Positions in a list -/

/-- The position of `j` in the list `l`: the index of its first occurrence (the length of `l` if
it does not occur). This is what the library function `findEq` returns. -/
def posOf (l : List ℕ) (j : ℕ) : ℕ := l.findIdx fun x => decide (x = j)

theorem posOf_lt {l : List ℕ} {j : ℕ} (h : j ∈ l) : posOf l j < l.length :=
  List.findIdx_lt_length_of_exists ⟨j, h, by simp⟩

theorem getElem_posOf {l : List ℕ} {j : ℕ} (h : j ∈ l) : l[posOf l j]'(posOf_lt h) = j := by
  have := List.findIdx_getElem (p := fun x => decide (x = j)) (xs := l) (w := posOf_lt h)
  simpa using this

theorem posOf_getElem {l : List ℕ} (hl : l.Nodup) (i : ℕ) (hi : i < l.length) :
    posOf l l[i] = i := by
  have hp : posOf l l[i] < l.length := posOf_lt (List.getElem_mem hi)
  have := getElem_posOf (List.getElem_mem hi)
  exact (hl.getElem_inj_iff).1 this

theorem posOf_le (l : List ℕ) (j : ℕ) : posOf l j ≤ l.length := List.findIdx_le_length

/-! ### The positions of the domain -/

section Dom

variable (e : Ω ≃ Fin k) (D : Set Ω)

open Classical in
/-- The positions of the domain, in increasing order. -/
noncomputable def domFin : List (Fin k) :=
  (List.finRange k).filter fun i => decide (e.symm i ∈ D)

/-- The positions of the domain, as numbers. -/
noncomputable def domNat : List ℕ := (domFin e D).map Fin.val

variable {e D}

open Classical in
theorem mem_domFin {i : Fin k} : i ∈ domFin e D ↔ e.symm i ∈ D := by
  classical
  simp [domFin]

theorem nodup_domFin : (domFin e D).Nodup := (List.nodup_finRange k).filter _

theorem nodup_domNat : (domNat e D).Nodup :=
  (nodup_domFin).map Fin.val_injective

theorem length_domNat : (domNat e D).length = (domFin e D).length := by simp [domNat]

theorem domNat_getElem (j : ℕ) (hj : j < (domNat e D).length) :
    (domNat e D)[j] = ((domFin e D)[j]'(by simpa [domNat] using hj) : ℕ) := by
  simp [domNat]

theorem val_mem_domNat {a : Ω} (ha : a ∈ D) : ((e a : Fin k) : ℕ) ∈ domNat e D :=
  List.mem_map.2 ⟨e a, mem_domFin.2 (by simpa using ha), rfl⟩

theorem domNat_lt {i : ℕ} (hi : i ∈ domNat e D) : i < k := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
  exact j.isLt

theorem length_domFin_le : (domFin e D).length ≤ k := by
  classical
  have := List.length_filter_le (fun i => decide (e.symm i ∈ D)) (List.finRange k)
  simpa [domFin] using this

variable (e D)

/-- **The positions of the domain**: the point `a` of the domain is at position
`posOf (domNat e D) (e a)`; position `j` is the point `e⁻¹ (domFin e D)[j]`. -/
noncomputable def domEquiv : D ≃ Fin (domFin e D).length where
  toFun a := ⟨posOf (domNat e D) (e a), by
    have := posOf_lt (val_mem_domNat (e := e) a.2)
    rwa [length_domNat] at this⟩
  invFun j := ⟨e.symm (domFin e D)[j], mem_domFin.1 (List.getElem_mem _)⟩
  left_inv a := by
    apply Subtype.ext
    simp only
    have h := getElem_posOf (val_mem_domNat (e := e) a.2)
    rw [domNat_getElem] at h
    rw [Fin.getElem_fin]
    rw [show (domFin e D)[posOf (domNat e D) (e a)]'(by
        have := posOf_lt (val_mem_domNat (e := e) a.2); rwa [length_domNat] at this) = e a from
      Fin.ext h, Equiv.symm_apply_apply]
  right_inv j := by
    apply Fin.ext
    simp only [Equiv.apply_symm_apply]
    have := posOf_getElem (nodup_domNat (e := e) (D := D)) j (by rw [length_domNat]; exact j.2)
    rw [domNat_getElem] at this
    exact this

theorem domEquiv_apply (a : D) : (domEquiv e D a : ℕ) = posOf (domNat e D) (e a) := rfl

theorem domEquiv_symm_apply (j : Fin (domFin e D).length) :
    ((domEquiv e D).symm j : Ω) = e.symm (domFin e D)[j] := rfl

/-- The domain has `s` points. -/
theorem card_dom_eq : Nat.card D = (domFin e D).length := by
  rw [Nat.card_congr (domEquiv e D), Nat.card_eq_fintype_card, Fintype.card_fin]

end Dom

/-! ### Generators of an image -/

/-- **Generators are mapped to generators of the image.** If the list `gs` generates `H` and
`ψ` agrees with a homomorphism `φ` on `H`, then `ψ` of the generators generates the image of
`φ`. -/
theorem closure_map_list {M N : Type*} [Group M] [Group N] {H : Subgroup M} {gs : List M}
    (hH : Subgroup.closure {g | g ∈ gs} = H) (φ : H →* N) (ψ : M → N)
    (hψ : ∀ g (hg : g ∈ H), ψ g = φ ⟨g, hg⟩) :
    Subgroup.closure {x | x ∈ gs.map ψ} = φ.range := by
  subst hH
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := {g | g ∈ gs}),
    MonoidHom.map_closure]
  congr 1
  ext x
  simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, Subgroup.subset_closure hg⟩, hg, (hψ g _).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, hψ g g.2⟩

/-! ### The restriction on positions -/

section Restrict

variable (e : Ω ≃ Fin k) (G : Subgroup (Perm Ω)) (D : Set Ω) (hD : Invariant G D)

/-- The isomorphism of `G` with its image on the positions. -/
noncomputable def finIso : G ≃* groupFin e G :=
  G.equivMapOfInjective (toFin e).toMonoidHom (toFin e).injective

theorem finIso_symm_apply (g : groupFin e G) :
    ((finIso e G).symm g : Perm Ω) = (toFin e).symm g := by
  have h : (finIso e G) ((finIso e G).symm g) = g := MulEquiv.apply_symm_apply _ _
  have h2 : ((finIso e G ((finIso e G).symm g) : groupFin e G) : Perm (Fin k)) =
      toFin e ((finIso e G).symm g : Perm Ω) := rfl
  rw [h] at h2
  rw [h2, MulEquiv.symm_apply_apply]

/-- **The restriction to the domain, on positions**: `G` (as permutations of `Fin k`) to the
permutations of the `s` positions of the domain. -/
noncomputable def restrK : groupFin e G →* Perm (Fin (domFin e D).length) :=
  (toFin (domEquiv e D)).toMonoidHom.comp
    ((restrictHom G D hD).comp (finIso e G).symm.toMonoidHom)

/-- **How to compute the restriction**: entry `j` is the position of `g p_j`. -/
theorem restrK_apply (g : Perm (Fin k)) (hg : g ∈ groupFin e G) (j : Fin (domFin e D).length) :
    (restrK e G D hD ⟨g, hg⟩ j : ℕ) = posOf (domNat e D) (g (domFin e D)[j]) := by
  simp only [restrK, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [toFin_apply, domEquiv_apply]
  congr 2
  rw [restrictHom_apply, finIso_symm_apply, domEquiv_symm_apply]
  simp

open Classical in
/-- The restriction on all permutations of `Fin k` (`1` outside the image of `G`). -/
noncomputable def restrP (g : Perm (Fin k)) : Perm (Fin (domFin e D).length) :=
  if h : g ∈ groupFin e G then restrK e G D hD ⟨g, h⟩ else 1

theorem restrP_of_mem {g : Perm (Fin k)} (hg : g ∈ groupFin e G) :
    restrP e G D hD g = restrK e G D hD ⟨g, hg⟩ := by
  simp [restrP, hg]

/-- The restriction of the image of an element of `G` is the image of its restriction. -/
theorem restrK_toFin (g : Perm Ω) (hg : g ∈ G) :
    restrK e G D hD ⟨toFin e g, mem_groupFin.2 ⟨g, hg, rfl⟩⟩ =
      toFin (domEquiv e D) (restrictHom G D hD ⟨g, hg⟩) := by
  simp only [restrK, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
  congr 2
  apply Subtype.ext
  rw [finIso_symm_apply]
  ext x
  simp

/-- The image of the restriction is the faithful image `G|_D` on positions. -/
theorem range_restrK :
    (restrK e G D hD).range = groupFin (domEquiv e D) (restrictHom G D hD).range := by
  ext σ
  simp only [MonoidHom.mem_range, mem_groupFin]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨h, hh, rfl⟩ := mem_groupFin.1 hg
    exact ⟨_, ⟨⟨h, hh⟩, rfl⟩, (restrK_toFin e G D hD h hh).symm⟩
  · rintro ⟨_, ⟨⟨h, hh⟩, rfl⟩, rfl⟩
    exact ⟨_, restrK_toFin e G D hD h hh⟩

/-- **The restricted generators generate the faithful image.** -/
theorem gens_restrP {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e G) :
    gens (gs.map (restrP e G D hD)) = groupFin (domEquiv e D) (restrictHom G D hD).range := by
  rw [← range_restrK]
  exact closure_map_list hgs _ _ fun g hg => restrP_of_mem e G D hD hg

/-! ### The graph group and the lift -/

/-- The graph `g ↦ g ⊕ g|_D` of the restriction. -/
noncomputable def graphHom :
    groupFin e G →* Perm (Fin k ⊕ Fin (domFin e D).length) :=
  (sumCongrHom _ _).comp ((groupFin e G).subtype.prod (restrK e G D hD))

theorem graphHom_apply (g : groupFin e G) :
    graphHom e G D hD g = Perm.sumCongr (g : Perm (Fin k)) (restrK e G D hD g) := rfl

/-- The graph generators of a generating list. -/
noncomputable def graphGens (gs : List (Perm (Fin k))) :
    List (Perm (Fin k ⊕ Fin (domFin e D).length)) :=
  gs.map fun g => Perm.sumCongr g (restrP e G D hD g)

theorem closure_graphGens {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e G) :
    Subgroup.closure {d | d ∈ graphGens e G D hD gs} = (graphHom e G D hD).range :=
  closure_map_list hgs _ _ fun g hg => by
    rw [graphHom_apply, restrP_of_mem e G D hD hg]

theorem sumCongr_inj {α β : Type*} {a a' : Perm α} {b b' : Perm β}
    (h : Perm.sumCongr a b = Perm.sumCongr a' b') : a = a' ∧ b = b' := by
  constructor
  · ext x
    have := congrArg (fun σ : Perm (α ⊕ β) => σ (Sum.inl x)) h
    simpa using this
  · ext x
    have := congrArg (fun σ : Perm (α ⊕ β) => σ (Sum.inr x)) h
    simpa using this

/-- **The preimage instance.** The graph group of the generators, and generators `ms` of a
subgroup of the image `G|_D`. -/
noncomputable def liftInst {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e G)
    (ms : List (Perm (Fin (domFin e D).length)))
    (hms : gens ms ≤ (restrK e G D hD).range) : PreimageInst where
  n := k
  n' := (domFin e D).length
  ds := graphGens e G D hD gs
  ms := ms
  preserves := by
    intro d hd i
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hd
    exact ⟨g i, by simp⟩
  ms_le := by
    intro m hm
    obtain ⟨a, ha⟩ := hms (Subgroup.subset_closure hm)
    refine ⟨a, ?_⟩
    rw [closure_graphGens e G D hD hgs]
    exact ⟨a, by rw [graphHom_apply, ha]⟩

/-- **The preimage set** is the set of `b ∈ G` (on positions) whose restriction lies in
`⟨ms⟩`. -/
theorem preimageSet_liftInst {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e G)
    (ms : List (Perm (Fin (domFin e D).length))) (hms : gens ms ≤ (restrK e G D hD).range) :
    preimageSet (liftInst e G D hD hgs ms hms) =
      {b | ∃ hb : b ∈ groupFin e G, restrK e G D hD ⟨b, hb⟩ ∈ gens ms} := by
  ext b
  change b ∈ {g : Perm (Fin k) | ∃ h ∈ Subgroup.closure {m | m ∈ ms},
    Equiv.sumCongr g h ∈ Subgroup.closure {d | d ∈ graphGens e G D hD gs}} ↔ _
  rw [closure_graphGens e G D hD hgs]
  constructor
  · rintro ⟨h, hh, ⟨a, ha⟩⟩
    rw [graphHom_apply] at ha
    obtain ⟨h1, h2⟩ := sumCongr_inj ha
    subst h1
    refine ⟨a.2, ?_⟩
    rw [h2]
    exact hh
  · rintro ⟨hb, hr⟩
    exact ⟨_, hr, ⟨⟨b, hb⟩, rfl⟩⟩

/-! ### The representative: a factorization -/

/-- `sumToFin` as a homomorphism. -/
theorem sumToFin_eq {n n' : ℕ} (g : Perm (Fin n ⊕ Fin n')) :
    sumToFin g = (finSumFinEquiv.permCongrHom : Perm (Fin n ⊕ Fin n') ≃* Perm (Fin (n + n'))) g :=
  rfl

/-- The graph group on `Fin (k + s)`. -/
noncomputable def graphHomF : groupFin e G →* Perm (Fin (k + (domFin e D).length)) :=
  finSumFinEquiv.permCongrHom.toMonoidHom.comp (graphHom e G D hD)

/-- The group `G ⊕ 1` on `Fin (k + s)`. -/
noncomputable def leftHomF : groupFin e G →* Perm (Fin (k + (domFin e D).length)) :=
  finSumFinEquiv.permCongrHom.toMonoidHom.comp
    ((sumCongrHom _ _).comp ((groupFin e G).subtype.prod 1))

theorem graphHomF_apply (g : groupFin e G) :
    graphHomF e G D hD g = sumToFin (Perm.sumCongr (g : Perm (Fin k)) (restrK e G D hD g)) := rfl

theorem leftHomF_apply (g : groupFin e G) :
    leftHomF e G D g = sumToFin (Perm.sumCongr (g : Perm (Fin k)) 1) := rfl

/-- The graph generators on `Fin (k + s)`. -/
noncomputable def graphGensF (gs : List (Perm (Fin k))) : List (Perm (Fin (k + (domFin e D).length))) :=
  (graphGens e G D hD gs).map sumToFin

/-- The generators `g ⊕ 1` on `Fin (k + s)`. -/
noncomputable def leftGensF (gs : List (Perm (Fin k))) : List (Perm (Fin (k + (domFin e D).length))) :=
  gs.map fun g => sumToFin (Perm.sumCongr g 1)

theorem gens_graphGensF {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e G) :
    gens (graphGensF e G D hD gs) = (graphHomF e G D hD).range := by
  unfold graphGensF graphGens
  rw [List.map_map]
  exact closure_map_list hgs _ _ fun g hg => by
    simp only [Function.comp_apply, graphHomF_apply, restrP_of_mem e G D hD hg]

theorem gens_leftGensF {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e G) :
    gens (leftGensF e D gs) = (leftHomF e G D).range :=
  closure_map_list hgs _ _ fun _ _ => rfl

/-- **The graph group normalizes `G ⊕ 1`.** -/
theorem normalizes_graph {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e G) :
    Normalizes (gens (graphGensF e G D hD gs)) (gens (leftGensF e D gs)) := by
  rw [gens_graphGensF e G D hD hgs, gens_leftGensF e G D hgs]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨a * b * a⁻¹, ?_⟩
  simp only [graphHomF_apply, leftHomF_apply, sumToFin_eq, ← map_inv, ← map_mul,
    Perm.sumCongr_inv, Perm.sumCongr_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_one,
    mul_inv_cancel, map_one]

/-- `1 ⊕ x'` lies in the product of the graph group and `G ⊕ 1` when `x'` is in the image. -/
theorem mem_graph_mul_left {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e G)
    {x' : Perm (Fin (domFin e D).length)} (hx : x' ∈ (restrK e G D hD).range) :
    ∃ g ∈ gens (graphGensF e G D hD gs), ∃ m ∈ gens (leftGensF e D gs),
      sumToFin (Perm.sumCongr (1 : Perm (Fin k)) x') = g * m := by
  obtain ⟨a, rfl⟩ := hx
  rw [gens_graphGensF e G D hD hgs, gens_leftGensF e G D hgs]
  refine ⟨_, ⟨a, rfl⟩, _, ⟨a⁻¹, rfl⟩, ?_⟩
  simp only [graphHomF_apply, leftHomF_apply, sumToFin_eq, ← map_mul, Perm.sumCongr_mul,
    Subgroup.coe_inv, mul_inv_cancel, mul_one]

/-- **A factorization gives a preimage.** If `1 ⊕ x' = g m` with `g` in the graph group and `m`
in `G ⊕ 1`, then `g = a ⊕ a|_D` with `a|_D = x'`. -/
theorem factor_lift {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e G)
    {x' : Perm (Fin (domFin e D).length)} {g m : Perm (Fin (k + (domFin e D).length))}
    (hg : g ∈ gens (graphGensF e G D hD gs)) (hm : m ∈ gens (leftGensF e D gs))
    (hx : sumToFin (Perm.sumCongr (1 : Perm (Fin k)) x') = g * m) :
    ∃ a : groupFin e G, restrK e G D hD a = x' ∧ g = graphHomF e G D hD a := by
  rw [gens_graphGensF e G D hD hgs] at hg
  rw [gens_leftGensF e G D hgs] at hm
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, rfl⟩ := hm
  refine ⟨a, ?_, rfl⟩
  simp only [graphHomF_apply, leftHomF_apply, sumToFin_eq, ← map_mul, Perm.sumCongr_mul,
    mul_one] at hx
  exact (sumCongr_inj ((MulEquiv.injective _) hx)).2.symm

/-- The first `k` entries of `sumToFin (a ⊕ b)` are those of `a`. -/
theorem sumToFin_sumCongr_castAdd {n n' : ℕ} (a : Perm (Fin n)) (b : Perm (Fin n'))
    (i : Fin n) : (sumToFin (Perm.sumCongr a b) (Fin.castAdd n' i) : ℕ) = a i := by
  simp [sumToFin]

/-- The entries `k + j` of `sumToFin (a ⊕ b)` are `k + b j`. -/
theorem sumToFin_sumCongr_natAdd {n n' : ℕ} (a : Perm (Fin n)) (b : Perm (Fin n'))
    (j : Fin n') : (sumToFin (Perm.sumCongr a b) (Fin.natAdd n j) : ℕ) = n + b j := by
  simp [sumToFin]

/-! ### The lifted answer -/

/-- **The image of a lifted answer**: the `b ∈ G` (on positions) whose restriction lies in the
image of `A`. -/
theorem image_liftAnswer {C : Type} (S : State Ω C) (A : Set (Perm S.dom)) :
    toFin e '' S.liftAnswer A = {b | ∃ hb : b ∈ groupFin e S.G,
      restrK e S.G S.dom S.dom_inv ⟨b, hb⟩ ∈ toFin (domEquiv e S.dom) '' A} := by
  ext b
  simp only [Set.mem_image, State.liftAnswer, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, ⟨hg, hA⟩, rfl⟩
    refine ⟨mem_groupFin.2 ⟨g, hg, rfl⟩, _, hA, ?_⟩
    rw [restrK_toFin]
    rfl
  · rintro ⟨hb, a, ha, hab⟩
    obtain ⟨g, hg, rfl⟩ := mem_groupFin.1 hb
    refine ⟨g, ⟨hg, ?_⟩, rfl⟩
    rw [restrK_toFin e S.G S.dom S.dom_inv g hg] at hab
    have : a = restrictHom S.G S.dom S.dom_inv ⟨g, hg⟩ := (toFin _).injective hab
    rw [this] at ha
    exact ha

/-- **The lift of a coset.** If the image of `A` is `x' K'` and `a|_D = x'`, the image of the
lifted answer is `a · {b ∈ G | b|_D ∈ K'}`. -/
theorem image_liftAnswer_coset {C : Type} (S : State Ω C) (A : Set (Perm S.dom))
    {x' : Perm (Fin (domFin e S.dom).length)} {K' : Subgroup (Perm (Fin (domFin e S.dom).length))}
    (hA : toFin (domEquiv e S.dom) '' A = x' • (K' : Set _)) (a : groupFin e S.G)
    (ha : restrK e S.G S.dom S.dom_inv a = x') :
    toFin e '' S.liftAnswer A = (a : Perm (Fin k)) •
      {b | ∃ hb : b ∈ groupFin e S.G, restrK e S.G S.dom S.dom_inv ⟨b, hb⟩ ∈ K'} := by
  rw [image_liftAnswer, hA]
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨hb, c, hc, hcb⟩
    refine ⟨(a : Perm (Fin k))⁻¹ * b, ⟨(groupFin e S.G).mul_mem ((groupFin e S.G).inv_mem a.2) hb,
      ?_⟩, by group⟩
    have : restrK e S.G S.dom S.dom_inv ⟨(a : Perm (Fin k))⁻¹ * b,
        (groupFin e S.G).mul_mem ((groupFin e S.G).inv_mem a.2) hb⟩ =
        (restrK e S.G S.dom S.dom_inv a)⁻¹ * restrK e S.G S.dom S.dom_inv ⟨b, hb⟩ := by
      rw [← map_inv, ← map_mul]; rfl
    rw [this, ha, ← hcb]
    simpa using hc
  · rintro ⟨c, ⟨hc, hK⟩, rfl⟩
    refine ⟨(groupFin e S.G).mul_mem a.2 hc, _, hK, ?_⟩
    have : restrK e S.G S.dom S.dom_inv ⟨(a : Perm (Fin k)) * c, (groupFin e S.G).mul_mem a.2 hc⟩ =
        restrK e S.G S.dom S.dom_inv a * restrK e S.G S.dom S.dom_inv ⟨c, hc⟩ := by
      rw [← map_mul]; rfl
    rw [this, ha]

end Restrict

end GI.Impl
