import Workspace.Impl.AggRectRepRf
import Workspace.Impl.AggTup

/-!
# What the program reads in the pair cases

The program computes, at the base point `x`:

1. the small points `D` of `P = π(G_x)` (`rcRSmall`), from generators of `P`;
2. when `D = [d₁, d₂]`, the flag `uno`: whether `d₂` lies in the `P`-orbit of `d₁`;
3. the orbit of the tuple `(x, d₁, d₂)` under the graph group of `G` on `Fin (k + q)`, whose
   entries are the tuples `(g x, π g d₁, π g d₂)` for `g ∈ G` (`rcR_tup_entry`); every position of
   the domain is the head of an entry (`rcR_tup_head`).

`rcR_pair_cells`: when `D` has two points, the representation `rcRRep` is that of a pair case
(Lemma A.27), its group is `H = π⁻¹(P)`, and the cell code of the position `g x` is
`rcRCode W R uno (π g d₁) (π g d₂)`. This is Lemma A.26 ("choose one ordering of `D` at the base
point and transport it using `φ`") read through the cells. When `D` has one point, the labels
are natural (`rcR_nat_of_small`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Lang
open GI.Cited (gens)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-! ### The orbit of the base tuple -/

section Tuple

variable {k : ℕ} (e : Ω ≃ Fin k)

/-- The base tuple `(x, d₁, d₂)` as points of `Fin (k + q)`. -/
def rcRTup {q : ℕ} (i : Fin k) (ds : List (Fin q)) : List (Fin (k + q)) :=
  Fin.castAdd q i :: ds.map (Fin.natAdd k)

theorem rcR_encPair_castAdd {q : ℕ} (p : Perm (Fin k) × Perm (Fin q)) (i : Fin k) :
    encPair p (Fin.castAdd q i) = Fin.castAdd q (p.1 i) :=
  Fin.ext (by rw [encPair_eq, sumToFin_sumCongr_castAdd]; rfl)

theorem rcR_map_tup {q : ℕ} (p : Perm (Fin k) × Perm (Fin q)) (i : Fin k) (ds : List (Fin q)) :
    (rcRTup i ds).map (encPair p) = rcRTup (p.1 i) (ds.map p.2) := by
  simp [rcRTup, rcR_encPair_castAdd, encPair_natAdd, Function.comp_def]

/-- **The entries of the orbit** of the base tuple are `(g x, π g d)` for `g ∈ G`. -/
theorem rcR_tup_entry {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {x : Ω} {ds : List (Fin L.q)} {y : List (Fin (k + L.q))}
    (hy : y ∈ actOrbit (fun g (xs : List (Fin (k + L.q))) => xs.map g) (ps.map encPair)
      (rcRTup (e x) ds)) :
    ∃ g : S.G, y = rcRTup (e ((g : Perm Ω) x)) (ds.map (L.π g : Perm (Fin L.q))) := by
  obtain ⟨t, ht, rfl⟩ := hy
  obtain ⟨p, hp, rfl⟩ := mem_gens_encPair.1 ht
  rw [hps, mem_graphOf] at hp
  obtain ⟨g, hg, -, h1, h2⟩ := hp
  refine ⟨⟨g, hg⟩, ?_⟩
  show (rcRTup (e x) ds).map (encPair p) = _
  rw [rcR_map_tup, ← h1, ← h2]
  simp [toFin_apply]

/-- **Every position of the orbit of `x` heads an entry.** -/
theorem rcR_tup_head {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {x : Ω} (ds : List (Fin L.q)) (g : S.G) :
    rcRTup (e ((g : Perm Ω) x)) (ds.map (L.π g : Perm (Fin L.q))) ∈
      actOrbit (fun g (xs : List (Fin (k + L.q))) => xs.map g) (ps.map encPair)
        (rcRTup (e x) ds) := by
  refine ⟨encPair (gpair e L g), mem_gens_encPair.2 ⟨gpair e L g, ?_, rfl⟩, ?_⟩
  · rw [hps, mem_graphOf]; exact ⟨g.1, g.2, g.2, rfl, rfl⟩
  · show (rcRTup (e x) ds).map (encPair (gpair e L g)) = _
    rw [rcR_map_tup]
    simp [gpair, toFin_apply]

end Tuple

/-! ### The cells in the pair cases -/

section Cells

variable [Finite Ω] (I : AggregationData P₀ S L) {x : Ω} (hx : x ∈ S.dom)
  (nat : ∀ W R : Finset (Fin L.q), RectConds P₀ S L W R → RectRep P₀ S L W R)

include I in
theorem rcR_q8 : 8 ≤ L.q := by have := I.q_ten; omega

theorem rcR_pt_comm {q : ℕ} (a b : Fin q) : rcRPt a b = rcRPt b a := by
  ext σ; rw [rcR_mem_pt, rcR_mem_pt]; tauto

theorem rcR_set_comm {q : ℕ} (a b : Fin q) : rcRSet a b = rcRSet b a := by
  ext σ; rw [rcR_mem_set, rcR_mem_set]; tauto

theorem rcR_pair_mem {q : ℕ} {a b d₁ d₂ : Fin q} (h : rcRPair a b = [d₁, d₂]) :
    (d₁ = a ∧ d₂ = b) ∨ (d₁ = b ∧ d₂ = a) := by
  unfold rcRPair at h
  split_ifs at h <;> simp only [List.cons.injEq, and_true] at h <;> tauto

/-- **The pair cases, read by the program.** If the small points of `π(G_x)` are `d₁, d₂`, the
representation is a pair representation with group `H = π⁻¹(P)`, and the cell code of `g x` is
`rcRCode W R uno (π g d₁) (π g d₂)`, where `uno` says whether `d₂` lies in the orbit of `d₁`. -/
theorem rcR_pair_cells {W R : Finset (Fin L.q)} (hc : RectConds P₀ S L W R) {d₁ d₂ : Fin L.q}
    (hsm : rcRSmall (rcRStab S L x) = [d₁, d₂]) :
    (rcRRep I hx nat W R hc).H = L.lift (permitted W R) ∧
    (∀ v, v ∉ S.dom → rcCellCode ((rcRRep I hx nat W R hc).cell v) = 0) ∧
    ∀ g : S.G, rcCellCode ((rcRRep I hx nat W R hc).cell ((g : Perm Ω) x)) =
      rcRCode W R (decide (d₂ ∈ rcROrb (rcRStab S L x) d₁)) ((L.π g : Perm (Fin L.q)) d₁)
        ((L.π g : Perm (Fin L.q)) d₂) := by
  classical
  haveI := I.fin
  have hq8 := rcR_q8 I
  have hgx : ∀ g : S.G, (g : Perm Ω) x ∈ S.dom := fun g => (S.dom_inv g.1 g.2 x).2 hx
  by_cases ho : Nonempty (KernelQuotient I.πd S.dom (GI.Pairs.OrderedPair (Fin L.q)))
  · have hrep : rcRRep I hx nat W R hc = RectRep.ordered I.πd_spec I.θ_half (rcRQo I hx ho) hc :=
      dif_pos ho
    set p := ho.some.map ⟨x, hx⟩ with hp
    have hP := rcR_stab_pt I.πd_spec ho.some hx
    rw [← hp] at hP
    have hsm' := hsm
    rw [hP, rcR_small_pt p.2 hq8, rcR_pair_ord] at hsm'
    simp only [List.cons.injEq, and_true] at hsm'
    obtain ⟨e1, e2⟩ := hsm'
    -- the flag: `d₁` is fixed by `P`
    have huno : d₂ ∉ rcROrb (rcRStab S L x) d₁ := by
      have hfix : ∀ σ ∈ rcRStab S L x, σ d₁ = d₁ := by
        intro σ hσ
        rw [hP, rcR_mem_pt] at hσ
        rw [← e1]
        unfold rcROrd
        split_ifs
        · exact hσ.2.1
        · exact hσ.2.2
      rw [rcR_orb_fixed hfix, Finset.mem_singleton]
      intro h
      have hne := (rcROrd p).2
      rw [e1, e2] at hne
      exact hne h.symm
    rw [hrep, decide_eq_false huno]
    refine ⟨rfl, fun v hv => rcR_code_off _ _ hv, fun g => ?_⟩
    have hmap := rcR_kqO_map I.πd_spec I.htr (by omega) ho.some hx g (hgx g)
    rw [← hp, e1, e2] at hmap
    have hd12 : d₁ ≠ d₂ := by have := (rcROrd p).2; rwa [e1, e2] at this
    exact rcR_code_ord hc.2.1 (rcRQo I hx ho) (hgx g) ((L.π g).1.injective.ne hd12)
      (Subtype.ext hmap)
  by_cases hu : Nonempty (KernelQuotient I.πd S.dom (GI.Johnson.SubsetVertex (Fin L.q) 2))
  · have hrep : rcRRep I hx nat W R hc = RectRep.unordered I.πd_spec I.θ_half hu.some hc := by
      unfold rcRRep; rw [dif_neg ho, dif_pos hu]
    obtain ⟨⟨⟨a, b⟩, hab⟩, hab'⟩ := GI.Pairs.unorderedOfOrdered_surjective (hu.some.map ⟨x, hx⟩)
    have hP := rcR_stab_set I.πd_spec hu.some hx hab hab'.symm
    have hsm' := hsm
    rw [hP, rcR_small_set hab hq8] at hsm'
    have hd := rcR_pair_mem hsm'
    have hd12 : d₁ ≠ d₂ := by rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hab; exact hab.symm]
    have huno : d₂ ∈ rcROrb (rcRStab S L x) d₁ := by
      rw [hP]
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact rcR_set_mem hab (by omega)
      · rw [rcR_set_comm]; exact rcR_set_mem hab.symm (by omega)
    -- `f(x) = {d₁, d₂}`
    have hfx : hu.some.map ⟨x, hx⟩ = GI.Pairs.unorderedOfOrdered ⟨(d₁, d₂), hd12⟩ := by
      rw [← hab']
      apply Subtype.ext
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · simp [GI.Pairs.unorderedOfOrdered, Finset.pair_comm]
    rw [hrep, decide_eq_true huno]
    refine ⟨rfl, fun v hv => rcR_code_off _ _ hv, fun g => ?_⟩
    have hmap := rcR_kq_map I.πd_spec hu.some hx g (hgx g)
    rw [hfx, ← GI.Pairs.unorderedOfOrdered_equivariant] at hmap
    exact rcR_code_uno hc.2.1 hu.some (hgx g) ((L.π g).1.injective.ne hd12) hmap
  · exfalso
    rcases I.kq_cases hc.1 with hn | h | h
    · have hP := rcR_stab_one I.πd_spec hn.some hx
      rw [hP, rcR_small_one hq8] at hsm
      simp at hsm
    · exact ho h
    · exact hu h

/-- When the small points of `π(G_x)` form one label, the labels are natural (no pair quotient
exists), so `rcRRep` is the supplied representation. -/
theorem rcR_nat_of_small {W R : Finset (Fin L.q)} (hc : RectConds P₀ S L W R) {a : Fin L.q}
    (hsm : rcRSmall (rcRStab S L x) = [a]) : rcRRep I hx nat W R hc = nat W R hc := by
  classical
  haveI := I.fin
  have hq8 := rcR_q8 I
  have ho : ¬ Nonempty (KernelQuotient I.πd S.dom (GI.Pairs.OrderedPair (Fin L.q))) := by
    rintro ⟨f⟩
    rw [rcR_stab_pt I.πd_spec f hx, rcR_small_pt (f.map ⟨x, hx⟩).2 hq8] at hsm
    unfold rcRPair at hsm; split_ifs at hsm <;> simp at hsm
  have hu : ¬ Nonempty (KernelQuotient I.πd S.dom (GI.Johnson.SubsetVertex (Fin L.q) 2)) := by
    rintro ⟨f⟩
    obtain ⟨⟨⟨a', b'⟩, hab⟩, hab'⟩ := GI.Pairs.unorderedOfOrdered_surjective (f.map ⟨x, hx⟩)
    rw [rcR_stab_set I.πd_spec f hx hab hab'.symm, rcR_small_set hab hq8] at hsm
    unfold rcRPair at hsm; split_ifs at hsm <;> simp at hsm
  unfold rcRRep
  rw [dif_neg ho, dif_neg hu]

end Cells

end GI.Impl
