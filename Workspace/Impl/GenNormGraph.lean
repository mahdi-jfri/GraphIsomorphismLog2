module

public import Workspace.Impl.GenNormRecover
public import Workspace.Impl.GenNormChoice
public import Workspace.Impl.AggMTProg
public import Workspace.Impl.AggPre
public import Workspace.Impl.AggKerRed
public import Workspace.Impl.LabelLift

@[expose] public section

/-!
# The normalized graph group

The parent graph keeps a position permutation together with its recovered Cameron point
permutation. Taking the preimage of `Alt(m)` in this graph keeps the full block kernel.
The existing three-cycle program supplies the generators of `Alt(m)` by taking its side
set to be the whole point set. Thus normalization needs no separate sign program.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val gens encPerm Preimage)

private theorem normSideAlt_le {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    sideAlt p ≤ alternatingGroup (Fin m) := by
  intro σ hσ
  obtain ⟨τ, hτ, rfl⟩ := mem_sideAlt.mp hσ
  exact mem_alternatingGroup.mpr ((sign_ofSubtype τ).trans hτ)

/-- Taking the side set to be the whole set gives the alternating group. -/
theorem normMT_univ (m : ℕ) : MT (Finset.univ : Finset (Fin m)) = alternatingGroup (Fin m) := by
  apply le_antisymm
  · exact sup_le (normSideAlt_le _) (normSideAlt_le _)
  · intro σ hσ
    apply (le_sup_left : sideAlt (fun i : Fin m => i ∈ (Finset.univ : Finset (Fin m))) ≤
      MT (Finset.univ : Finset (Fin m)))
    apply mem_sideAlt.mpr
    letI : Fintype {i : Fin m // i ∈ (Finset.univ : Finset (Fin m))} := Subtype.fintype _
    let τ := σ.subtypePerm (p := fun i => i ∈ (Finset.univ : Finset (Fin m))) (fun i => by simp)
    have hτ : ofSubtype τ = σ := by
      apply Equiv.ext
      intro i
      rw [ofSubtype_apply_of_mem τ (Finset.mem_univ i)]
      rfl
    refine ⟨τ, ?_, hτ⟩
    have hh : sign (ofSubtype τ) = 1 := hτ ▸ mem_alternatingGroup.mp hσ
    exact (sign_ofSubtype τ).symm.trans hh

/-- A polynomial list of generators of `Alt(m)`, already computed by `cycGens_spec`. -/
def normAltGens (m : ℕ) : List (Perm (Fin m)) :=
  (List.range (m ^ 3)).map (genOf (Finset.univ : Finset (Fin m)))

/-- The three-cycle list generates exactly `Alt(m)`. -/
theorem normAltGens_gens (m : ℕ) : gens (normAltGens m) = alternatingGroup (Fin m) := by
  have hset : {σ | σ ∈ normAltGens m} =
      {σ | ∃ t ∈ List.range (m ^ 3), genOf (Finset.univ : Finset (Fin m)) t = σ} := by
    ext σ
    simp only [normAltGens, List.mem_map, Set.mem_setOf_eq]
  rw [gens, hset, closure_genOf, normMT_univ]

variable {Ω C : Type} {S : State Ω C} {n m k : ℕ}
variable (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S)
variable (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)

/-- The parent graph homomorphism, before restriction to even point actions. -/
noncomputable def normParentPair : S.G →* Perm (Fin n) × Perm (Fin m) :=
  MonoidHom.prod ((toFin en).toMonoidHom.comp S.G.subtype)
    ((Q.permHom e hS).comp Q.ρ.rangeRestrict)

/-- The first component makes the parent graph homomorphism injective. -/
theorem normParentPair_injective : Function.Injective (normParentPair en Q e hS) := by
  intro g h heq
  apply Subtype.ext
  apply (toFin en).injective
  exact congrArg Prod.fst heq

/-- A graph generating list of the parent group, with point images recovered from `E`. -/
def normParentGens (ps : List (Perm (Fin n) × Perm (Fin m))) : Prop :=
  Subgroup.closure {p | p ∈ ps} = (normParentPair en Q e hS).range

/-- Correct labels on a position generating list generate the entire parent graph. -/
theorem normParentGens_of (ps : List (Perm (Fin n) × Perm (Fin m)))
    (hgen : gens (ps.map Prod.fst) = groupFin en S.G)
    (hps : ∀ p ∈ ps, ∃ g : S.G, normParentPair en Q e hS g = p) :
    normParentGens en Q e hS ps := by
  let H := Subgroup.closure {p | p ∈ ps}
  have hle : H ≤ (normParentPair en Q e hS).range := by
    change Subgroup.closure {p | p ∈ ps} ≤ _
    rw [Subgroup.closure_le]
    exact hps
  apply le_antisymm hle
  rintro p ⟨g, rfl⟩
  have hg : toFin en g.1 ∈ gens (ps.map Prod.fst) := by
    rw [hgen]
    exact ⟨g.1, g.2, rfl⟩
  rw [gens_fst] at hg
  obtain ⟨p, hp, heq⟩ := hg
  obtain ⟨g', hg'⟩ := hle hp
  have hgg : g' = g := by
    apply Subtype.ext
    apply (toFin en).injective
    exact (congrArg Prod.fst hg').trans heq
  rw [hgg] at hg'
  exact hg' ▸ hp

/-- The normalized graph contains exactly the pairs whose point action is even. -/
noncomputable def normGraph : Subgroup (Perm (Fin n) × Perm (Fin m)) :=
  ((Q.normGroup e hS).subgroupOf S.G).map (normParentPair en Q e hS)

/-- Its description as the preimage requested from the cited graph primitive. -/
theorem normGraph_eq_inf : normGraph en Q e hS = (normParentPair en Q e hS).range ⊓
    (alternatingGroup (Fin m)).comap (MonoidHom.snd _ _) := by
  ext p
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, ?_⟩
    exact mem_alternatingGroup.mpr ((normMem_iff Q e hS g).mp hg)
  · rintro ⟨⟨g, rfl⟩, hg⟩
    refine ⟨g, ?_, rfl⟩
    exact (normMem_iff Q e hS g).mpr (mem_alternatingGroup.mp hg)

/-- Every alternating generator is in the point projection of the parent graph. This is the
precondition of `graphPre_spec`, and uses the lower inclusion of the Cameron structure. -/
theorem normAltGens_lift {ps : List (Perm (Fin n) × Perm (Fin m))}
    (hps : normParentGens en Q e hS ps) :
    ∀ a ∈ normAltGens m, ∃ p ∈ Subgroup.closure {p | p ∈ ps}, MonoidHom.snd _ _ p = a := by
  intro a ha
  have hmem : a ∈ alternatingGroup (Fin m) := by
    rw [← normAltGens_gens]
    exact Subgroup.subset_closure ha
  obtain ⟨g, hg⟩ := Q.normPi_surjective e hS ⟨a, hmem⟩
  let g' : S.G := ⟨g.1, Q.normGroup_le e hS g.2⟩
  refine ⟨normParentPair en Q e hS g', ?_, ?_⟩
  · rw [hps]
    exact ⟨g', rfl⟩
  · exact congrArg Subtype.val hg

/-- The output graph of the alternating preimage is exactly the normalized graph. -/
theorem normGraph_of_preimage {ps qs : List (Perm (Fin n) × Perm (Fin m))}
    (hps : normParentGens en Q e hS ps)
    (hqs : Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓
      (gens (normAltGens m)).comap (MonoidHom.snd _ _)) :
    Subgroup.closure {p | p ∈ qs} = normGraph en Q e hS := by
  rw [hqs, hps, normAltGens_gens, normGraph_eq_inf]

/-- The position projection of the normalized graph is the full normalized group. -/
theorem normGraph_fst {ps : List (Perm (Fin n) × Perm (Fin m))}
    (hps : Subgroup.closure {p | p ∈ ps} = normGraph en Q e hS) :
    gens (ps.map Prod.fst) = groupFin en (Q.normGroup e hS) := by
  rw [gens_fst, hps]
  ext a
  constructor
  · rintro ⟨p, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g.1, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    let g' : S.G := ⟨g, Q.normGroup_le e hS hg⟩
    exact ⟨normParentPair en Q e hS g', ⟨g', hg, rfl⟩, rfl⟩

/-- The second part of a normalized pair is exactly the model's supplied label image. -/
theorem normGraph_labels {ps : List (Perm (Fin n) × Perm (Fin m))}
    (hps : Subgroup.closure {p | p ∈ ps} = normGraph en Q e hS)
    {p : Perm (Fin n) × Perm (Fin m)} (hp : p ∈ ps)
    (hg : (toFin en).symm p.1 ∈ Q.normGroup e hS) :
    ((Q.normPi e hS ⟨(toFin en).symm p.1, hg⟩ : alternatingGroup (Fin m)) : Perm (Fin m)) = p.2 := by
  have hm : p ∈ normGraph en Q e hS := hps ▸ Subgroup.subset_closure hp
  obtain ⟨g, hg', heq⟩ := hm
  have hfirst : g.1 = (toFin en).symm p.1 := by
    apply (toFin en).injective
    exact (congrArg Prod.fst heq).trans (MulEquiv.apply_symm_apply _ _).symm
  have hsecond := congrArg Prod.snd heq
  have hgg : g = ⟨(toFin en).symm p.1, Q.normGroup_le e hS hg⟩ := Subtype.ext hfirst
  rw [hgg] at hsecond
  exact hsecond

/-- The cited graph preimage program computes exactly the normalized graph. -/
theorem normGraphPre_spec (hp : Preimage) {Pg : Program} {b jpre : ℕ}
    (hb : Pg.HasAt b (graphPreFuns b jpre)) (hj : Pg.prims[jpre]? = some (preimagePrim hp))
    (ps : List (Perm (Fin n) × Perm (Fin m))) (hps : normParentGens en Q e hS ps) :
    FunAll Pg b (.list [.list [.nat n, .nat m], .list (ps.map pairV),
      .list ((normAltGens m).map encPerm)]) (fun w cost =>
        ∃ qs : List (Perm (Fin n) × Perm (Fin m)), w = .list (qs.map pairV) ∧
          qs.length ≤ (n + m) ^ 2 ∧ Subgroup.closure {p | p ∈ qs} = normGraph en Q e hS ∧
          cost ≤ (preimagePrim hp).bound (preimageEnc (pairInst (MonoidHom.snd _ _) ps
            (normAltGens m) (normAltGens_lift en Q e hS hps))) +
              graphPreK * preM n m ps (normAltGens m) ^ 8) := by
  refine (graphPre_spec hp hb hj ps (normAltGens m)
    (normAltGens_lift en Q e hS hps)).mono ?_
  rintro w cost ⟨qs, hw, hlen, hgen, hc⟩
  exact ⟨qs, hw, hlen, normGraph_of_preimage en Q e hS hps hgen, hc⟩

/-- Cutting the first projection of the normalized graph gives a canonical group value of
the normalized position group, including the entire block kernel. -/
theorem normGraphReduce_spec (hst : GI.Cited.PointwiseStab) {Pg : Program} {b j : ℕ}
    (hb : Pg.HasAt b (krFuns b j)) (hj : Pg.prims[j]? = some (pointwiseStabPrim hst))
    (ps : List (Perm (Fin n) × Perm (Fin m)))
    (hps : Subgroup.closure {p | p ∈ ps} = normGraph en Q e hS) :
    FunAll Pg b (.list [.nat n, .list (ps.map pairV)]) (fun w cost =>
      GroupValC n w (groupFin en (Q.normGroup e hS)) ∧
        cost ≤ (pointwiseStabPrim hst).boundSize (100 * pM n m ps ^ 4) +
          krK * pM n m ps ^ 9) := by
  refine (kr_spec hst hb hj ps).mono ?_
  rintro w cost ⟨gs, hw, hgen, hlen, hc⟩
  exact ⟨⟨gs, hw, hgen.trans (normGraph_fst en Q e hS hps), hlen⟩, hc⟩

end GI.Impl
