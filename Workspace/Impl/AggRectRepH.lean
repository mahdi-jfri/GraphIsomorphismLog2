import Workspace.Impl.AggRectRepTab

/-!
# The group of the query in graph form

The program computes generators of the query group `H` in three steps.

1. **Preimage** on a graph group. For pairs, the graph group of `G` with the generators of
   `P = permitted W R` (`rcR_pairGens_H`). For single labels (Lemma A.30), the group of the pairs
   `(g, ρ(g) ⊕ π(g))` (`rcRPhi`) with the generators `embed(a) ⊕ a` of `{(embed a, a) : a ∈ P}`;
   an element `g` lands there exactly when `π(g) ∈ P` and `ρ(g) = embed(π(g))`, which is
   `g ∈ H` (`rcR_car_fst`). The precondition of the call holds because the diagonal preimage maps
   onto `Alt(q)` (`rcR_car_lift`).
2. The first parts, cut to at most `k²` generators (**PointwiseStab**, `kr_spec`).
3. The label part of each generator, read from the orbit table (`rcR_piN`). The pairs generate the
   graph of `H` (`rcR_hs_pairs`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Lang
open GI.Cited (gens)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S} {k : ℕ} (e : Ω ≃ Fin k)

theorem rcR_gpair_injective : Function.Injective (gpair e L) := by
  intro x y h
  have := congrArg Prod.fst h
  exact Subtype.ext ((toFin e).injective this)

/-- The positions part of `gpair`. -/
noncomputable abbrev rcRPos : S.G →* Perm (Fin k) := (toFin e).toMonoidHom.comp S.G.subtype

/-! ### Generators of the image of a homomorphism on `G` -/

/-- **The images of graph-form generators generate the image.** If each pair `p` of `ps` is
`gpair (pre p)`, the elements `Φ (pre p)` generate `Φ(G)`. -/
theorem rcR_closure_phi {Y : Type} [Group Y] {ps : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L S.G ps) (Φ : S.G →* Y) (pre : Perm (Fin k) × Perm (Fin L.q) → S.G)
    (hpre : ∀ p ∈ ps, gpair e L (pre p) = p) :
    Subgroup.closure {y | y ∈ ps.map (fun p => Φ (pre p))} = Φ.range := by
  have hset : {y | y ∈ ps.map (fun p => Φ (pre p))} = Φ '' {g | ∃ p ∈ ps, pre p = g} := by
    ext y
    simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨pre p, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨g, ⟨p, hp, rfl⟩, rfl⟩; exact ⟨p, hp, rfl⟩
  have htop : Subgroup.closure {g | ∃ p ∈ ps, pre p = g} = ⊤ := by
    apply Subgroup.map_injective (rcR_gpair_injective e (L := L))
    rw [MonoidHom.map_closure]
    have h1 : gpair e L '' {g | ∃ p ∈ ps, pre p = g} = {p | p ∈ ps} := by
      ext p
      constructor
      · rintro ⟨g, ⟨p', hp', rfl⟩, rfl⟩
        rw [hpre p' hp']; exact hp'
      · intro hp
        exact ⟨pre p, ⟨p, hp, rfl⟩, hpre p hp⟩
    rw [h1, hps]
    show (S.G.subgroupOf S.G).map (gpair e L) = _
    rw [Subgroup.subgroupOf_self]
  rw [hset, ← MonoidHom.map_closure, htop, MonoidHom.range_eq_map]

/-- The first parts of a preimage in the image of `Φ`. -/
theorem rcR_fst_pre {Y : Type} [Group Y] (Φ : S.G →* Perm (Fin k) × Y) (U : Subgroup Y) :
    (Φ.range ⊓ U.comap (MonoidHom.snd _ _)).map (MonoidHom.fst _ _) =
      (U.comap ((MonoidHom.snd _ _).comp Φ)).map ((MonoidHom.fst _ _).comp Φ) := by
  ext a
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_comap,
    MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨_, ⟨⟨g, rfl⟩, hU⟩, rfl⟩
    exact ⟨g, hU, rfl⟩
  · rintro ⟨g, hU, rfl⟩
    exact ⟨_, ⟨⟨g, rfl⟩, hU⟩, rfl⟩

/-- The first parts of graph pairs of a subgroup `A`. -/
theorem rcR_fst_graph {A : Subgroup (Perm Ω)} {qs : List (Perm (Fin k) × Perm (Fin L.q))}
    (hqs : PairGens e L A qs) :
    gens (qs.map Prod.fst) = (A.subgroupOf S.G).map (rcRPos e) := by
  have h1 : gens (qs.map Prod.fst) = (Subgroup.closure {p | p ∈ qs}).map (MonoidHom.fst _ _) := by
    unfold gens
    rw [MonoidHom.map_closure]
    congr 1
    ext σ
    simp
  rw [h1, hqs, graphOf, Subgroup.map_map]
  rfl

/-! ### From generators on positions to graph pairs -/

/-- **Graph pairs from generators on positions.** If `hs` generates `A` on positions and `πN`
gives the label part of every element of `A`, the pairs `(h, πN h)` generate the graph of `A`. -/
theorem rcR_hs_pairs {A : Subgroup (Perm Ω)} (hA : A ≤ S.G) {hs : List (Perm (Fin k))}
    (hg : gens hs = (A.subgroupOf S.G).map (rcRPos e))
    (πN : Perm (Fin k) → Perm (Fin L.q))
    (hπN : ∀ g : S.G, g.1 ∈ A → πN (rcRPos e g) = rcRPi L g) :
    PairGens e L A (hs.map fun h => (h, πN h)) := by
  classical
  have hmem : ∀ h ∈ hs, ∃ g : S.G, g.1 ∈ A ∧ rcRPos e g = h := by
    intro h hh
    have : h ∈ gens hs := Subgroup.subset_closure hh
    rw [hg] at this
    obtain ⟨g, hgA, rfl⟩ := Subgroup.mem_map.1 this
    exact ⟨g, hgA, rfl⟩
  choose! pre hpreA hpre using hmem
  have hset : {p | p ∈ hs.map fun h => (h, πN h)} = gpair e L '' {g | ∃ h ∈ hs, pre h = g} := by
    ext p
    simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨pre h, ⟨h, hh, rfl⟩, ?_⟩
      refine Prod.ext (hpre h hh) ?_
      show rcRPi L (pre h) = πN h
      rw [← hπN _ (hpreA h hh), hpre h hh]
    · rintro ⟨g, ⟨h, hh, rfl⟩, rfl⟩
      refine ⟨h, hh, Prod.ext (hpre h hh).symm ?_⟩
      show πN h = rcRPi L (pre h)
      rw [← hπN _ (hpreA h hh), hpre h hh]
  have hcl : Subgroup.closure {g | ∃ h ∈ hs, pre h = g} = A.subgroupOf S.G := by
    apply Subgroup.map_injective (f := rcRPos e) (fun a b hab =>
      Subtype.ext ((toFin e).injective hab))
    rw [MonoidHom.map_closure, ← hg]
    unfold gens
    congr 1
    ext h
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, ⟨h', hh', rfl⟩, rfl⟩
      rw [hpre h' hh']; exact hh'
    · intro hh
      exact ⟨pre h, ⟨h, hh, rfl⟩, hpre h hh⟩
  unfold PairGens
  rw [hset, ← MonoidHom.map_closure, hcl]
  rfl

end GI.Impl

/-! ### The carrier case -/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Lang
open GI.Cited (gens)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

section Car

variable [Finite Ω] {k : ℕ} (e : Ω ≃ Fin k) (I : AggregationData P₀ S L)
  (hlam : (S.N : ℝ) ^ P₀.α < L.q) (f : KernelQuotient I.πd S.dom (Fin L.q))

/-- On the diagonal preimage, `ρ(g) = embed(π(g))`. -/
theorem rcR_liftD_rho {h : Perm Ω} (h1 : h ∈ (rcRCarD e I hlam f).liftD) (hg : h ∈ S.G) :
    rcRRhoN e I hlam f ⟨h, hg⟩ = (rcRCarD e I hlam f).d.embedAlt (L.π ⟨h, hg⟩) := by
  have hmem : h ∈ (rcRCarD e I hlam f).H (∅ : Finset (Fin L.q)) ∅ ↔ _ := rcR_car_memH e I hlam f
  set D := rcRCarD e I hlam f
  obtain ⟨hg', hl⟩ := D.mem_liftD.1 h1
  obtain ⟨z, hz⟩ := (D.d.mem_lift_iff _).1 hl
  replace hz := (CarrierOfState.piD_spec (rcR_specN e I hlam f) ⟨h, hg⟩).symm.trans hz
  have h3 := congrArg Prod.fst hz
  have h4 := congrArg Prod.snd hz
  simp only at h3 h4
  rw [h3]
  congr 1
  show CarrierOfState.psi0 (rcR_specN e I hlam f)
    (I.con.kills _ _ (rcR_rec_spec I hlam f).1 (rcR_cols_spec I hlam f).1) z.1 = _
  rw [← h4, CarrierOfState.psi0_spec]

/-- **Every label permutation has a lift on the diagonal**: `π(g) = a` and `ρ(g) = embed(a)`
(Lemma A.30: the diagonal preimage maps onto `Alt(q)`). -/
theorem rcR_car_lift (a : alternatingGroup (Fin L.q)) :
    ∃ g : S.G, L.π g = a ∧
      rcRRhoN e I hlam f g = (rcRCarD e I hlam f).d.embedAlt a := by
  set D := rcRCarD e I hlam f
  obtain ⟨l, hl⟩ := D.d.ideal_onto a
  obtain ⟨g, hg⟩ := State.domGroup_elim l.1
  have hmem : (⟨S.domHom g, g, rfl⟩ : S.domGroup) ∈ D.d.lift := hg ▸ l.2
  have hπ : L.π g = a := by
    rw [← D.link g hmem, ← hl]
    congr 1
    exact Subtype.ext hg.symm
  refine ⟨g, hπ, ?_⟩
  have h1 : g.1 ∈ D.liftD := D.mem_liftD.2 ⟨g.2, hmem⟩
  have := rcR_liftD_rho e I hlam f h1 g.2
  rw [← hπ]
  exact this

/-- The pair map of the carrier case: `g ↦ (g, ρ(g) ⊕ π(g))`. -/
noncomputable def rcRPhi : S.G →* Perm (Fin k) × Perm (Fin ((rcRCarD e I hlam f).m + L.q)) :=
  MonoidHom.prod (rcRPos e) ((encPairHom _ L.q).comp (MonoidHom.prod
    ((alternatingGroup _).subtype.comp (rcRRhoN e I hlam f))
    ((alternatingGroup _).subtype.comp L.π)))

/-- The label permutations `embed(a) ⊕ a`. -/
noncomputable def rcREmb : alternatingGroup (Fin L.q) →*
    Perm (Fin ((rcRCarD e I hlam f).m + L.q)) :=
  (encPairHom _ L.q).comp (MonoidHom.prod
    ((alternatingGroup _).subtype.comp (rcRCarD e I hlam f).d.embedAlt)
    (alternatingGroup _).subtype)

/-- **The first parts of the carrier preimage generate `H` on positions.** -/
theorem rcR_car_fst {W R : Finset (Fin L.q)} :
    (((permitted W R).map (rcREmb e I hlam f)).comap
      ((MonoidHom.snd _ _).comp (rcRPhi e I hlam f))).map
      ((MonoidHom.fst _ _).comp (rcRPhi e I hlam f)) =
      (((rcRCarD e I hlam f).H W R).subgroupOf S.G).map (rcRPos e) := by
  have hiff : ∀ g : S.G, (MonoidHom.snd _ _).comp (rcRPhi e I hlam f) g ∈
      (permitted W R).map (rcREmb e I hlam f) ↔ g.1 ∈ (rcRCarD e I hlam f).H W R := by
    intro g
    rw [rcR_car_memH, Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, he⟩
      have he' := encPairHom_injective he
      have he1 := congrArg Prod.fst he'
      have he2 := congrArg Prod.snd he'
      simp only [MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype] at he1 he2
      have h2 : L.π g = a := Subtype.ext he2.symm
      replace he' := he1
      refine ⟨g.2, by rw [show (⟨g.1, g.2⟩ : S.G) = g from rfl, h2]; exact ha, ?_⟩
      rw [show (⟨g.1, g.2⟩ : S.G) = g from rfl, h2]
      exact Subtype.ext he'.symm
    · rintro ⟨hg, hp, hρ⟩
      refine ⟨L.π g, hp, ?_⟩
      show encPairHom _ L.q _ = encPairHom _ L.q _
      congr 1
      refine Prod.ext ?_ rfl
      show ((rcRCarD e I hlam f).d.embedAlt (L.π g)).1 = (rcRRhoN e I hlam f g).1
      rw [← hρ]
  ext a
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (hiff g).1 hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (hiff g).2 hg, rfl⟩

end Car

end GI.Impl
