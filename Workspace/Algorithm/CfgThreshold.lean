module

public import Workspace.Algorithm.AuxCases
public import Workspace.Paper.CapsExplicit

@[expose] public section

/-!
# The configuration item with the explicit label threshold of Lemma A.12

`cfgOutItem_valid` (`Workspace/Algorithm/AuxCases.lean`) proves the item of the configuration
branch valid for all labels above some threshold, taken from the existential of Lemma A.12
(`GI.Paper.lem_exact_configuration`). Its value is hidden, so the parameters could not be checked
against it. This file repeats the chain with the explicit threshold
`GI.Paper.a12Threshold = 2(4·4⁴ + 8) = 2064` of `GI.Paper.lem_exact_configuration_2064`, valid for
`β ≥ 3/4`:

* `AuxItem.config_cap_explicit`: the cap `aw(E₀) ≤ βq` of a group preserving a nontrivial
  homogeneous coherent configuration on at least `δq` labels;
* `PairCfg.autE_cap_explicit`: the cap of the automorphism group of a good configuration;
* `cfgItem_valid_explicit`: the configuration query item of Algorithm `alg:auxiliary` (`q ≤ λ`);
* `cfgOutItem_valid_explicit`: the item of the configuration branch, for `β ≥ 13/16`.

The proofs are those of `config_cap`, `PairCfg.autE_cap`, `cfgItem_valid` and `cfgOutItem_valid`,
with the explicit threshold in place of the existential one.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.PairRefinement GI.ExactConfiguration GI.Paper

/-- **The cap of a configuration item with the explicit threshold** (Lemma A.12,
`lem_exact_configuration_2064`). -/
theorem AuxItem.config_cap_explicit {P : Params} {δ : ℝ} (hβ : max (1 - δ) (1 / 2) < P.β)
    (h34 : 3 / 4 ≤ P.β) {Ω C : Type} {S : State Ω C} (L : GiantLabels S) (n : ℕ)
    (c : Coloring n) (side : Bool) (ι : Fin n ↪ Fin L.q) (hc : Coherent c)
    (hh : Homogeneous c side) (hn : NontrivialOffDiagonal c side) (hδ : δ * L.q ≤ n)
    (hq : a12Threshold ≤ L.q) (E₀ : Subgroup (alternatingGroup (Fin L.q)))
    (hE : E₀.map (alternatingGroup (Fin L.q)).subtype ≤ configGroup ι c side) :
    GI.SectionCaps.Cap E₀ ⌊P.β * L.q⌋₊ := by
  have hδ' : δ * Fintype.card (Fin L.q) ≤ n := by simpa using hδ
  have hq' : a12Threshold ≤ Fintype.card (Fin L.q) := by simpa using hq
  have h := (lem_exact_configuration_2064 hβ h34 (Fin L.q) n c side ι hc hh hn hδ' hq').2.2 _ hE
  rw [Fintype.card_fin] at h
  have hK : GI.SectionCaps.Cap (E₀.map (alternatingGroup (Fin L.q)).subtype)
      ⌊P.β * L.q⌋₊ := (aw_le_iff _).1 (Nat.le_floor h)
  let e := E₀.equivMapOfInjective (alternatingGroup (Fin L.q)).subtype
    (alternatingGroup (Fin L.q)).subtype_injective
  exact GI.SectionCaps.of_injective e.toMonoidHom e.injective hK

/-- **The cap of a configuration branch with the explicit threshold**: the automorphism group of
a good configuration on `q ≥ 2064` labels has `aw ≤ βq`. -/
theorem PairCfg.autE_cap_explicit {P : Params} {δ : ℝ} (hβ : max (1 - δ) (1 / 2) < P.β)
    (h34 : 3 / 4 ≤ P.β) {Ω C : Type} {S : State Ω C} (L : GiantLabels S) (X : PairCfg L.q)
    (hX : X.Good δ) (hq : a12Threshold ≤ L.q) : GI.SectionCaps.Cap X.autE ⌊P.β * L.q⌋₊ :=
  AuxItem.config_cap_explicit hβ h34 L X.fiber.card X.coloring false (X.emb rfl)
    (PairCfg.coloring_coherent hX) (X.coloring_homogeneous false)
    (PairCfg.coloring_nontrivial hX false) hX.large hq X.autE (X.autE_le_configGroup false)

section Query

variable {P : Params}

/-- **The configuration item is valid, with the explicit threshold** (`cfgItem_valid` with
`q ≥ 2064` in place of the existential threshold). -/
theorem cfgItem_valid_explicit {δ : ℝ} (hβ : max (1 - δ) (1 / 2) < P.β) (h34 : 3 / 4 ≤ P.β)
    {Ω C : Type} {S : State Ω C} (L : GiantLabels S) {B : Set (Perm Ω)}
    (X Y : PairCfg L.q) (hX : X.Good δ) (hq : a12Threshold ≤ L.q)
    (hlam : (L.q : ℝ) ≤ (S.N : ℝ) ^ P.α)
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • X = Y) :
    (cfgItem (P := P) X Y : AuxItem P S L).Valid B := by
  classical
  unfold cfgItem
  split_ifs with hc
  swap
  · -- different fiber sizes: the branch is empty
    show S.answer ∩ B = ∅
    refine Set.eq_empty_iff_forall_notMem.2 fun g hg => hc ?_
    obtain ⟨hgG, he⟩ := hB g hg
    rw [← he]
    refine Finset.card_bij (fun a _ => (L.π ⟨g, hgG⟩ : Perm (Fin L.q)) a) (fun a ha => ?_)
      (fun a _ b _ h => (L.π ⟨g, hgG⟩ : Perm (Fin L.q)).injective h) (fun b hb => ?_)
    · rw [PairCfg.mem_fiber_smul, Perm.inv_apply_self]; exact ha
    · rw [PairCfg.mem_fiber_smul] at hb
      exact ⟨_, hb, Perm.apply_inv_self _ _⟩
  refine ⟨PairCfg.autE_cap_explicit hβ h34 L X hX hq, by simp, fun Q hQ => ?_,
    fun Q hQ σ hσ g hg => ?_, fun hne => ?_⟩
  · -- a fresh `Solve` call on `n² ≤ N^{2α}` positions
    rw [List.mem_singleton] at hQ
    subst hQ
    left
    refine ⟨rfl, ?_⟩
    change ((pairState (C' := ℕ) _ _ _).size : ℝ) ≤ _
    rw [pairState_size]
    exact sq_le_rpow (by simpa using Finset.card_le_univ X.fiber) hlam
  · -- soundness: two maps from `X` to `Y` differ by an automorphism of `X`
    rw [List.mem_singleton] at hQ
    subst hQ
    obtain ⟨hgG, he⟩ := hB g hg
    refine ⟨hgG, ?_⟩
    have h1 := cfgQuery_read_maps hc hσ
    have h2 := PairCfg.maps_of_smul he
    exact PairCfg.Maps.coset h1 h2
  · -- completeness: the call is exact
    refine AuxQuery.comp_of_covers (List.mem_singleton_self _) (cfgQuery_covers hc)
      (fun g hg => ?_) hne
    obtain ⟨hgG, he⟩ := hB g hg
    exact ⟨hgG, _, rfl, PairCfg.maps_of_smul he⟩

end Query

/-- **The item of the configuration branch is valid, with the explicit threshold** (Lemma A.12,
Lemma 5.1, Lemma A.28): for `β ≥ 13/16`, `q ≥ 2064`, a good source object and a branch whose
parent isomorphisms map the source object to the target object, the item is valid. The proof is
that of `cfgOutItem_valid`. -/
theorem cfgOutItem_valid_explicit {P : Params} (hβ : 13 / 16 ≤ P.β) {Ω C : Type}
    {S : State Ω C} (L : GiantLabels S) (O : RectOracle P S L) (ch : SojChoice)
    {B : Set (Perm Ω)}
    (oX oY : CfgOut L.q) (hgood : oX.Good P.β) (hq : a12Threshold ≤ L.q)
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • oX = oY) :
    (cfgOutItem O ch oX oY).Valid B := by
  classical
  have hq16 : 16 ≤ L.q := le_trans (by norm_num [a12Threshold]) hq
  have h1 : 1 ≤ P.β * L.q := by
    have : (16 : ℝ) ≤ L.q := by exact_mod_cast hq16
    nlinarith
  have hβδ : max (1 - deltaB) (1 / 2) < P.β := by
    rw [max_lt_iff]; norm_num [deltaB]; constructor <;> linarith
  -- objects of different kinds: the branch is empty
  have hempty : ∀ (hne : ∀ σ : Perm (Fin L.q), σ • oX ≠ oY), S.answer ∩ B = ∅ := by
    intro hne
    refine Set.eq_empty_iff_forall_notMem.2 fun g hg => ?_
    obtain ⟨hgG, he⟩ := hB g hg
    exact hne _ he
  cases oX with
  | none => exact absurd hgood id
  | part zX =>
    cases oY with
    | part zY =>
      refine objItem_valid (fun g hg => ?_) hgood
      obtain ⟨hgG, he⟩ := hB g hg
      exact ⟨hgG, by simpa using he⟩
    | pair Y y₀ => exact hempty fun σ h => by simp at h
    | none => exact hempty fun σ h => by simp at h
  | pair X x₀ =>
    cases oY with
    | part zY => exact hempty fun σ h => by simp at h
    | none => exact hempty fun σ h => by simp at h
    | pair Y y₀ =>
      have hB' : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G,
          (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • X = Y ∧ (L.π ⟨g, hg⟩ : Perm (Fin L.q)) x₀ = y₀ := by
        intro g hg
        obtain ⟨hgG, he⟩ := hB g hg
        simp only [CfgOut.smul_pair, CfgOut.pair.injEq] at he
        exact ⟨hgG, he⟩
      show (if (L.q : ℝ) ≤ (S.N : ℝ) ^ P.α then cfgItem X Y else sojItem O ch X Y x₀ y₀).Valid B
      split_ifs with hlam
      · exact cfgItem_valid_explicit hβδ (by linarith) L X Y hgood.1 hq hlam fun g hg =>
          (hB' g hg).imp fun _ h => h.1
      · exact sojItem_valid O ch hgood.1 hgood.2 hβ h1 hq16 (lt_of_not_ge hlam) hB'

end GI.Algorithm
