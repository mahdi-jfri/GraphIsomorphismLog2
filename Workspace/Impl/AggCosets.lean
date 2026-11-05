module

public import Workspace.Impl.AggKer
public import Workspace.Impl.AggChoice

@[expose] public section

/-!
# Coset representatives of `ker(φ_T|_A)` in `A` from the orbit of the test tuple

Section 4: `CheckNewWindow` "enumerates the constantly many cosets of `ker(φ_T|_A)` in `A`".
The orbit program on the test tuple (`graphTup_spec`) returns pairs `(y, t)`: the points `y` are
the orbit of the label points of `T` under the graph of `A`, without repeats, and `t = a ⊕ π a`
maps the label points of `T` to `y`. Two elements of `A` lie in the same coset of the kernel
exactly when their label permutations agree on `T`, that is, when they move the tuple to the same
point. So the first parts `a` of the transversal, restricted to the domain, are one
representative for each coset (`repsOK_of_orbit`): this is what `CosetRepFn` asks of the
representatives of one pair of subgroups (`RepsOK`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm GI.LocalGroups GI.Endpoint
open GI.Cited (Val encPerm gens)

variable {k : ℕ} {Ω C : Type} (e : Ω ≃ Fin k) (S : State Ω C)

/-- The restriction to the domain of a permutation of the positions: `g|_dom` for the
permutation `g` of `Ω` that `a` stands for, when `g ∈ G`, and `1` otherwise. -/
noncomputable def domOfPos (a : Perm (Fin k)) : Perm S.dom := by
  classical
  exact if h : (toFin e).symm a ∈ S.G then S.domHom ⟨_, h⟩ else 1

theorem domOfPos_toFin {g : Perm Ω} (hg : g ∈ S.G) :
    domOfPos e S (toFin e g) = S.domHom ⟨g, hg⟩ := by
  unfold domOfPos
  have e0 : (toFin e).symm (toFin e g) = g := (toFin e).symm_apply_apply g
  have h : (toFin e).symm (toFin e g) ∈ S.G := by rw [e0]; exact hg
  rw [dif_pos h]
  congr 1
  exact Subtype.ext e0

/-- The quotient of `A` by the kernel of `φ` in `A` has the order of the image `φ(A)`. -/
theorem card_quot_kernelIn {V Q : Type} [Group Q] {P : Subgroup (Perm V)} (phi : P →* Q)
    {A : Subgroup (Perm V)} (hA : A ≤ P) :
    Nat.card (A ⧸ (kernelIn phi A).subgroupOf A) = Nat.card (img phi A) := by
  let f : A →* Q := phi.comp (Subgroup.inclusion hA)
  have hker : f.ker = (kernelIn phi A).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_kernelIn]
    exact ⟨fun h => ⟨a.2, hA a.2, h⟩, fun ⟨_, _, h⟩ => h⟩
  have hrange : f.range = img phi A := by
    ext x
    rw [MonoidHom.mem_range, mem_img]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a, hA a.2⟩, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange]

variable {e S} {L : GiantLabels S} (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- **The transversal of the orbit of the test tuple gives coset representatives** of the
kernel `ker(φ_T|_A)` in `A`, one for each coset. Here `L'` is the output of the orbit program
on the label points of `T` (`graphTup_spec`), and `qs` are the pairs of its transversal. -/
theorem repsOK_of_orbit (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
    {T : Finset (Fin L.q)} {A : Subgroup (Perm S.dom)} (hA : A ≤ Pgrp S.domGroup πd T)
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L (S.liftGroup A) ps)
    {L' : List (List (Fin (k + L.q)) × Perm (Fin (k + L.q)))}
    (hnd : (L'.map Prod.fst).Nodup)
    (hmem : ∀ y, y ∈ L'.map Prod.fst ↔ y ∈ actOrbit (fun g (xs : List (Fin (k + L.q))) =>
      xs.map g) (ps.map encPair) (labPts k (tlist T)))
    (htr : ∀ p ∈ L', p.2 ∈ gens (ps.map encPair) ∧ (labPts k (tlist T)).map p.2 = p.1)
    {qs : List (Perm (Fin k) × Perm (Fin L.q))} (hqs : L'.map Prod.snd = qs.map encPair) :
    RepsOK (A, kernelIn (phiT S.domGroup πd T) A) (qs.map fun p => domOfPos e S p.1) := by
  -- every pair of `qs` is a pair `(a, π a)` of the graph of the lift of `A`
  have hgr : ∀ p ∈ qs, ∃ g, ∃ hg : g ∈ S.G, g ∈ S.liftGroup A ∧ toFin e g = p.1 ∧
      ((L.π ⟨g, hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) = p.2 := by
    intro p hp
    have hp' : encPair p ∈ L'.map Prod.snd := by rw [hqs]; exact List.mem_map_of_mem hp
    obtain ⟨⟨y, t⟩, hyt, ht⟩ := List.mem_map.1 hp'
    have hg := (htr _ hyt).1
    simp only at ht hg
    subst ht
    obtain ⟨p', hp'', he⟩ := mem_gens_encPair.1 hg
    have := encPair_injective he
    subst this
    rw [hps] at hp''
    exact (mem_graphOf e L).1 hp''
  refine ⟨?_, ?_, ?_⟩
  · -- the representatives lie in `A`
    intro τ hτ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hτ
    obtain ⟨g, hg, hgA, h1, -⟩ := hgr p hp
    rw [← h1, domOfPos_toFin e S hg]
    exact (State.mem_liftGroup.1 hgA).2
  · -- the cosets cover `A`
    intro a ha
    have haP : a ∈ Pgrp S.domGroup πd T := hA ha
    have hdom : a ∈ S.domGroup := Pgrp_le (G := S.domGroup) haP
    obtain ⟨⟨g, hg⟩, rfl⟩ := hdom
    have hgA : g ∈ S.liftGroup A := State.mem_liftGroup.2 ⟨hg, ha⟩
    -- the image of the test tuple under `π g` is a point of the orbit
    have hy : labPts k ((tlist T).map (L.π ⟨g, hg⟩ : Perm (Fin L.q))) ∈ L'.map Prod.fst :=
      (hmem _).2 (mem_tupOrbit.2 ⟨_, (mem_gens_snd hps _).2 ⟨g, hg, hgA, rfl⟩, rfl⟩)
    obtain ⟨⟨y, t⟩, hyt, rfl⟩ := List.mem_map.1 hy
    have ht : t ∈ L'.map Prod.snd := List.mem_map_of_mem (f := Prod.snd) hyt
    rw [hqs] at ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
    obtain ⟨g', hg', hgA', h1, h2⟩ := hgr p hp
    have hmap := (htr _ hyt).2
    simp only at hmap
    rw [map_encPair_labPts] at hmap
    have hagree : ∀ c ∈ T, p.2 c = (L.π ⟨g, hg⟩ : Perm (Fin L.q)) c := by
      intro c hc
      have := List.map_inj_left.1 (labPts_injective hmap) c (mem_tlist.2 hc)
      exact this
    simp only [Set.mem_iUnion]
    refine ⟨domOfPos e S p.1, List.mem_map_of_mem hp, ?_⟩
    rw [← h1, domOfPos_toFin e S hg']
    refine ⟨S.domHom ⟨g', hg'⟩⁻¹ * S.domHom ⟨g, hg⟩, ?_, by simp [smul_eq_mul]⟩
    have hA' : S.domHom ⟨g', hg'⟩ ∈ A := (State.mem_liftGroup.1 hgA').2
    have hm : S.domHom ⟨g', hg'⟩⁻¹ * S.domHom ⟨g, hg⟩ ∈ A := A.mul_mem (A.inv_mem hA') ha
    rw [SetLike.mem_coe, mem_kernelIn]
    refine ⟨hm, hA hm, Subtype.ext (Equiv.ext fun ⟨c, hc⟩ => Subtype.ext ?_)⟩
    have hdm : S.domHom ⟨g', hg'⟩⁻¹ * S.domHom ⟨g, hg⟩ ∈ S.domGroup :=
      ⟨⟨g', hg'⟩⁻¹ * ⟨g, hg⟩, by rw [map_mul, map_inv]⟩
    rw [phiT_apply, lab_of_mem hdm]
    have e0 : S.domHom ⟨g', hg'⟩⁻¹ * S.domHom ⟨g, hg⟩ =
        S.domHom ((⟨g', hg'⟩ : S.G)⁻¹ * ⟨g, hg⟩) := by rw [map_mul, map_inv]
    have key : ((πd ⟨_, hdm⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) =
        (L.π ((⟨g', hg'⟩ : S.G)⁻¹ * ⟨g, hg⟩) : Perm (Fin L.q)) := by
      rw [← hπ]; congr 2
    rw [key, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, OneMemClass.coe_one,
      Perm.one_apply]
    rw [← hagree c hc, ← h2, Perm.inv_apply_self]
  · -- one representative for each coset
    have hlen1 : (qs.map fun p => domOfPos e S p.1).length = L'.length := by
      rw [List.length_map, ← List.length_map (f := encPair) (as := qs), ← hqs, List.length_map]
    have hlen2 : L'.length = (actOrbit (fun g (xs : List (Fin (k + L.q))) => xs.map g)
        (ps.map encPair) (labPts k (tlist T))).ncard := by
      rw [← List.length_map (f := Prod.fst), ← List.toFinset_card_of_nodup hnd,
        ← Set.ncard_coe_finset]
      congr 1
      ext y
      simp [hmem]
    show _ ≤ Nat.card (A ⧸ (kernelIn (phiT S.domGroup πd T) A).subgroupOf A)
    rw [hlen1, hlen2, ncard_tupOrbit πd hπ hA hps, card_quot_kernelIn _ hA]

end GI.Impl
