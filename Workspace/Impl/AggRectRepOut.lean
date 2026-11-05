module

public import Workspace.Impl.AggRectRepCar
public import Workspace.Impl.AggKer

@[expose] public section

/-!
# What the program reads at the base point

The program finds the support of `π(G_x)` at the first domain position `x` (Corollary A.25)
from blocks it already has:

* the graph pairs of `G_x` (**PointwiseStab** on the graph group, `graphStabP_spec`); their
  second parts generate `π(G_x)` (`rcR_stab_gens`);
* the orbit labels of `π(G_x)` on `[q]` (`orbitFuns_spec`); the orbit of `c` has as many points
  as there are labels equal to the label of `c` (`rcR_count_orb`);
* the labels with orbit size at most `2`, in increasing order: this is `rcRSmall` (`rcR_small_nat`).

By the support classification the small list is `[a]` (single labels; then `a = f(x)` for a
one-label quotient `f`, `rcR_one_of_small`) or `[d₁, d₂]` with `d₁ < d₂` (pairs)
(`rcR_small_cases`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Lang
open GI.Cited (gens)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-! ### The second parts of the stabilizer pairs -/

section Stab

variable {k : ℕ} (e : Ω ≃ Fin k)

/-- **The second parts of graph pairs of `G_x` generate `π(G_x)`.** -/
theorem rcR_stab_gens {ps qs : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {x : Ω} (hqs : Subgroup.closure {p | p ∈ qs} =
      Subgroup.closure {p | p ∈ ps} ⊓ fixPts k L.q [Fin.castAdd L.q (e x)]) :
    gens (qs.map Prod.snd) = rcRStab S L x := by
  have h1 : gens (qs.map Prod.snd) = (Subgroup.closure {p | p ∈ qs}).map (MonoidHom.snd _ _) := by
    unfold gens
    rw [MonoidHom.map_closure]
    congr 1
    ext σ
    simp
  rw [h1, hqs, hps]
  ext σ
  rw [rcR_mem_stab, Subgroup.mem_map]
  constructor
  · rintro ⟨p, ⟨hp, hfix⟩, rfl⟩
    obtain ⟨g, hg, -, h1, h2⟩ := (mem_graphOf e L).1 hp
    refine ⟨⟨g, hg⟩, ?_, h2⟩
    have hf : encPair p (Fin.castAdd L.q (e x)) = Fin.castAdd L.q (e x) := hfix _ (by simp)
    rw [rcR_encPair_castAdd, ← h1, toFin_apply] at hf
    have := Fin.castAdd_injective _ _ hf
    simpa using this
  · rintro ⟨g, hgx, rfl⟩
    refine ⟨gpair e L g, ⟨(mem_graphOf e L).2 ⟨g.1, g.2, g.2, rfl, rfl⟩, ?_⟩, rfl⟩
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    rw [rcR_encPair_castAdd]
    congr 1
    show toFin e g.1 (e x) = e x
    rw [toFin_apply]
    simp [hgx]

end Stab

/-! ### Orbit sizes from orbit labels -/

section Count

variable {q : ℕ}

/-- The number of labels equal to the label of `c` is the size of the orbit of `c`. -/
theorem rcR_count_orb (gs : List (Perm (Fin q))) (c : Fin q) :
    ((List.finRange q).map (orbitLabels gs)).count (orbitLabels gs c) =
      (rcROrb (gens gs) c).card := by
  classical
  simp only [List.count, List.countP_eq_length_filter, List.filter_map, List.length_map, Function.comp_def]
  have hs : rcROrb (gens gs) c =
      ((List.finRange q).filter fun y => orbitLabels gs y == orbitLabels gs c).toFinset := by
    ext d
    rw [rcR_mem_orb, List.mem_toFinset, List.mem_filter]
    simp only [List.mem_finRange, true_and, beq_iff_eq]
    rw [eq_comm, (orbitLabels_spec gs).1 c d, mem_genOrbit]
    rfl
  rw [hs, List.toFinset_card_of_nodup ((List.nodup_finRange q).filter _)]

/-- **The small list as numbers**: the labels `c < q` with at most two labels equal to the label of
`c` are the values of `rcRSmall`. -/
theorem rcR_small_nat (gs : List (Perm (Fin q))) :
    (List.range q).filter (fun c => decide
      ((((List.finRange q).map (orbitLabels gs)).count
        ((((List.finRange q).map (orbitLabels gs))).getD c 0)) ≤ 2)) =
      (rcRSmall (gens gs)).map Fin.val := by
  classical
  have hfr : (List.finRange q).map Fin.val = List.range q := List.ext_getElem (by simp) (by simp)
  rw [← hfr, List.filter_map, rcRSmall]
  congr 1
  apply List.filter_congr
  intro c _
  have hc : ((List.finRange q).map (orbitLabels gs)).getD c 0 = orbitLabels gs c := by
    simp [List.getD_eq_getElem?_getD]
  simp only [Function.comp_apply, hc, rcR_count_orb]

end Count

/-! ### The two shapes of the small list -/

section Cases

variable [Finite Ω] (I : AggregationData P₀ S L) {x : Ω} (hx : x ∈ S.dom)

include I hx in
/-- **The small list is `[a]` or `[d₁, d₂]` with `d₁ < d₂`** (support classification). -/
theorem rcR_small_cases (hlam : (S.N : ℝ) ^ P₀.α < L.q) :
    (∃ a, rcRSmall (rcRStab S L x) = [a]) ∨
      ∃ d₁ d₂, d₁ < d₂ ∧ rcRSmall (rcRStab S L x) = [d₁, d₂] := by
  have hq8 := rcR_q8 I
  have hpair : ∀ a b : Fin L.q, a ≠ b → ∃ d₁ d₂, d₁ < d₂ ∧ rcRPair a b = [d₁, d₂] := by
    intro a b hab
    unfold rcRPair
    split_ifs with h
    · exact ⟨a, b, h, rfl⟩
    · exact ⟨b, a, lt_of_le_of_ne (not_lt.1 h) (Ne.symm hab), rfl⟩
  rcases I.kq_cases hlam with hf | hf | hf <;> obtain ⟨f⟩ := hf
  · exact Or.inl ⟨_, by rw [rcR_stab_one I.πd_spec f hx, rcR_small_one hq8]⟩
  · right
    rw [rcR_stab_pt I.πd_spec f hx, rcR_small_pt (f.map ⟨x, hx⟩).2 hq8]
    exact hpair _ _ (f.map ⟨x, hx⟩).2
  · right
    obtain ⟨⟨⟨a, b⟩, hab⟩, hab'⟩ := GI.Pairs.unorderedOfOrdered_surjective (f.map ⟨x, hx⟩)
    rw [rcR_stab_set I.πd_spec f hx hab hab'.symm, rcR_small_set hab hq8]
    exact hpair a b hab

include I in
/-- **A one-element small list comes from single labels**: there is a one-label quotient `f`
with `f(x) = a`. -/
theorem rcR_one_of_small (hlam : (S.N : ℝ) ^ P₀.α < L.q) {a : Fin L.q}
    (hsm : rcRSmall (rcRStab S L x) = [a]) :
    ∃ f : KernelQuotient I.πd S.dom (Fin L.q), f.map ⟨x, hx⟩ = a := by
  have hq8 := rcR_q8 I
  rcases I.kq_cases hlam with hf | hf | hf <;> obtain ⟨f⟩ := hf
  · refine ⟨f, ?_⟩
    rw [rcR_stab_one I.πd_spec f hx, rcR_small_one hq8] at hsm
    simpa using hsm
  · rw [rcR_stab_pt I.πd_spec f hx, rcR_small_pt (f.map ⟨x, hx⟩).2 hq8] at hsm
    unfold rcRPair at hsm; split_ifs at hsm <;> simp at hsm
  · obtain ⟨⟨⟨a', b'⟩, hab⟩, hab'⟩ := GI.Pairs.unorderedOfOrdered_surjective (f.map ⟨x, hx⟩)
    rw [rcR_stab_set I.πd_spec f hx hab hab'.symm, rcR_small_set hab hq8] at hsm
    unfold rcRPair at hsm; split_ifs at hsm <;> simp at hsm

end Cases

end GI.Impl
